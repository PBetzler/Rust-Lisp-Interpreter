use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::num::ParseFloatError;
use std::rc::Rc;
use std::fs::File;
use std::io::{BufReader, BufRead, Read, Write};
use std::path::Path;

pub enum InputSource {
    StdIn,
    File(String),
}

pub fn run(src: InputSource, input: &mut (impl Read + BufRead), output: &mut impl Write, err_out: &mut impl Write) {
    let env = &mut default_env();

    match src {
        InputSource::StdIn => {
            loop {
                match output.write_all("lisp >\n".as_bytes()) {
                    Ok(_) => {},
                    Err(_) => match err_out.write_all("Error, can not write to given output stream!".as_bytes()) {
                        Ok(_) => {}
                        Err(_) => panic!("Fatal error, could not write to error stream!"),
                    }
                };
                let exp = slurp_exp(input);

                if exp.contains("exit") {
                    break;
                }

                match parse_eval(exp, env) {
                    Ok(result) => match output.write_all(format!("{}\n", result).as_bytes()) {
                        Ok(_) => {},
                        Err(_) => match err_out.write_all("Error, can not write to given output stream!".as_bytes()) {
                            Ok(_) => {}
                            Err(_) => panic!("Fatal error, could not write to error stream!"),
                        },
                    },
                    Err(e) => match err_out.write_all(format!("{}\n", e).as_bytes()){
                        Ok(_) => {}
                        Err(_) => panic!("Fatal error, could not write to error stream!"),
                    },
                };
            }
        }
        InputSource::File(filename) => {
            let path = Path::new(&filename);
            let display = path.display();
            let file = match File::open(path) {
                Ok(file) => file,
                Err(err) => {
                    eprintln!("Error opening file {}: {}", display, err);
                    return;
                }
            };


            let reader = BufReader::new(file);

            for (index, line) in reader.lines().enumerate() {
                match line {
                    Ok(line) => {
                        println!("Line {}: {}", index+1, line);
                        match parse_eval(line, env) {
                            Ok(result) => println!("Line {}: {}", index+1, result),
                            Err(e) => eprintln!("Line: {} Error: {}", index +1, e.to_string()),
                        }
                    }
                    Err(_) => eprintln!("Error reading line: {} from file: {}", index +1, filename.to_string())
                }

            }
        }
    }


}

#[derive(Clone)]
enum LispExp {
    Bool(bool),
    Symbol(String),
    Number(f64),
    List(Vec<LispExp>),
    Func(fn(&[LispExp]) -> Result<LispExp, LispErr>),
    Nil,
    Lambda(LispLambda),
    Quote(Vec<LispExp>),
}

#[derive(Clone)]
struct LispLambda {
    params_exp: Rc<LispExp>,
    body_exp: Rc<LispExp>,
}

impl LispExp {
    fn exp_to_string(&self) -> String {
        match self {
            LispExp::Bool(_) => "bool".to_string(),
            LispExp::Symbol(_) => "symbol".to_string(),
            LispExp::Number(_) => "number".to_string(),
            LispExp::List(_) => "list".to_string(),
            LispExp::Func(_) => "function".to_string(),
            LispExp::Nil => "nil".to_string(),
            LispExp::Lambda(_) => "lambda".to_string(),
            LispExp::Quote(_) => "quote".to_string(),
        }
    }
}

impl Display for LispExp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let display_string = match self {
            LispExp::Bool(b) => b.to_string(),
            LispExp::Symbol(s) => s.clone(),
            LispExp::Number(n) => n.to_string(),
            LispExp::List(list) => {
                let xs: Vec<String> = list.iter().map(|x| x.to_string()).collect();
                format!("({})", xs.join(","))
            },
            LispExp::Func(_) => "Function {}".to_string(),
            LispExp::Nil => "nil".to_string(),
            LispExp::Lambda(_) => "Lambda {}".to_string(),
            LispExp::Quote(list) => {
                let xs: Vec<String> = list.iter().map(|x| x.to_string()).collect();
                format!("{}", xs.join(" "))
            },
        };

        write!(f, "{}", display_string)
    }
}

enum SyntaxErr {
    WrongExpExpected(LispExp),
    WrongExpDidNotExpect(LispExp),
    WrongExpNumber,
    DidExpectFormSyntax(String),
    WrongFormNum(usize),
    WrongFormExp(usize, LispExp),
    NoFormSyntaxExpected,

}

impl Display for SyntaxErr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let preamble: String = String::from("Syntax error!");
        let message = match self {
            SyntaxErr::WrongExpExpected(exp) => format!("Needed a {} expression, but got something else!", exp.exp_to_string()),
            SyntaxErr::WrongExpNumber => format!("Got the wrong number of expressions!"),
            SyntaxErr::WrongExpDidNotExpect(exp) => format!("Got a {} expression, but needed something else!", exp.exp_to_string()),
            SyntaxErr::DidExpectFormSyntax(s) => format!("Did expect symbol {} here!", s),
            SyntaxErr::WrongFormNum(n) => format!("Wrong number of form expressions! Needed: {}", n),
            SyntaxErr::WrongFormExp(n, exp) => format!("Expected form number: {} to be a {}", n, exp.exp_to_string()),
            SyntaxErr::NoFormSyntaxExpected => format!("Did not expect form syntax here!"),
        };

        write!(f, "{} {}", preamble, message)
    }
}

enum LispErr {
    SyntaxError(SyntaxErr),
    UnbalancedParens,
    UnknownSymbol(String),
}

impl Display for LispErr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let message: String = match self {
            LispErr::SyntaxError(err) => err.to_string(),
            LispErr::UnbalancedParens => "Unbalanced parens!".to_string(),
            LispErr::UnknownSymbol(k) => format!("Unknown symbol {}!", k),
        };

        write!(f, "{}",message)
    }
}

pub struct LispEnv<'a> {
    data: HashMap<String, LispExp>,
    outer: Option<&'a LispEnv<'a>>,
}

fn tokenize(expr: String) ->Vec<String> {
    expr
        .replace("(", " ( ")
        .replace(")", " ) ")
        .split_whitespace()
        .map(|x| x.to_string())
        .collect()
}

fn parse(tokens: &[String]) -> Result<(LispExp, &[String]), LispErr> {
    let (token, rest) = tokens.split_first().ok_or(
        LispErr::SyntaxError(SyntaxErr::WrongExpNumber)
    )?;

    match &token[..] {
        "(" => read_seq(rest),
        ")" => Err(LispErr::UnbalancedParens),
        _ => Ok((parse_atom(token), rest)),
    }
}

fn read_seq(tokens: &[String]) -> Result<(LispExp, &[String]), LispErr> {
    let mut result: Vec<LispExp> = Vec::new();
    let mut rest_tokens = tokens;

    loop {
        let (next_token, rest) = rest_tokens
            .split_first()
            .ok_or(LispErr::UnbalancedParens)?;

        if next_token == ")" {
            return Ok((LispExp::List(result), rest));
        }

        let (exp, rest_tokens_minus_first) = parse(&rest_tokens)?;
        result.push(exp);
        rest_tokens = rest_tokens_minus_first;
    }
}

fn parse_atom(token: &str) -> LispExp {

    match token.as_ref() {
        "true" => LispExp::Bool(true),
        "false" => LispExp::Bool(false),
        "nil" => LispExp::Nil,
        _ => {
            let potential_float: Result<f64, ParseFloatError> = token.parse();

            match potential_float {
                Ok(v) => LispExp::Number(v),
                Err(_) => LispExp::Symbol(token.to_string().clone())
            }
        }
    }
}

fn default_env<'a>() -> LispEnv<'a> {
    let mut data: HashMap<String, LispExp> = HashMap::new();

    data.insert(
        "+".to_string(),
        LispExp::Func(
            |args: &[LispExp]| -> Result<LispExp, LispErr> {
                let sum = parse_list_of_floats(args)?.iter().fold(0.0, |sum, a| sum + a);

                Ok(LispExp::Number(sum))
            }
        )
    );

    data.insert(
        "-".to_string(),
        LispExp::Func(
            |args: &[LispExp]| -> Result<LispExp, LispErr> {
                let floats = parse_list_of_floats(args)?;
                let first = *floats.first().ok_or(LispErr::SyntaxError(SyntaxErr::WrongExpNumber))?;
                let sum_rest = floats[1..].iter().fold(0.0, |sum, a| sum + a);

                Ok(LispExp::Number(first - sum_rest))
            }
        )
    );

    data.insert(
        "*".to_string(),
        LispExp::Func(
            |args: &[LispExp]| -> Result<LispExp, LispErr> {
                let sum = parse_list_of_floats(args)?.iter().fold(1.0, |sum, a| sum * a);

                Ok(LispExp::Number(sum))
            }
        )
    );

    data.insert(
        "/".to_string(),
        LispExp::Func(
            |args: &[LispExp]| -> Result<LispExp, LispErr> {
                let floats = parse_list_of_floats(args)?;
                let first = *floats.first().ok_or(LispErr::SyntaxError(SyntaxErr::WrongExpNumber))?;
                let sum_rest = floats[1..].iter().fold(0.0, |sum, a| sum + a);

                Ok(LispExp::Number(first / sum_rest))
            }
        )
    );

    data.insert(
        "mod".to_string(),
        LispExp::Func(
            |args: &[LispExp]| -> Result<LispExp, LispErr> {
                let floats = parse_list_of_floats(args)?;
                if floats.len() != 2 {
                    return Err(LispErr::SyntaxError(SyntaxErr::WrongExpNumber));
                }
                let first = *floats.first().ok_or(LispErr::SyntaxError(SyntaxErr::WrongExpNumber))?;
                let second = floats[1];

                Ok(LispExp::Number(first % second))
            }
        )
    );

    data.insert(
        "=".to_string(),
        LispExp::Func(ensure_tonicity!(|a, b| a == b))
    );
    data.insert(
        ">".to_string(),
        LispExp::Func(ensure_tonicity!(|a, b| a > b))
    );
    data.insert(
        ">=".to_string(),
        LispExp::Func(ensure_tonicity!(|a, b| a >= b))
    );
    data.insert(
        "<".to_string(),
        LispExp::Func(ensure_tonicity!(|a, b| a < b))
    );
    data.insert(
        "<=".to_string(),
        LispExp::Func(ensure_tonicity!(|a, b| a <= b))
    );

    LispEnv {data, outer: None}
}

fn parse_single_float(exp: &LispExp) -> Result<f64, LispErr> {
    match exp {
        LispExp::Number(num) => Ok(*num),
        _ => Err(LispErr::SyntaxError(SyntaxErr::WrongExpExpected(LispExp::Number(0 as f64))))
    }
}

fn parse_list_of_floats(args: &[LispExp]) -> Result<Vec<f64>, LispErr> {
    args
        .iter()
        .map(|x| parse_single_float(x))
        .collect()
}

fn eval (exp: &LispExp, env: &mut LispEnv) -> Result<LispExp, LispErr> {
    match exp {
        LispExp::Bool(_b) => Ok(exp.clone()),
        LispExp::Symbol(k) => env_get(k, env).ok_or(LispErr::UnknownSymbol(k.clone())).map(|x| x.clone()),
        LispExp::Number(_a) => Ok(exp.clone()),
        LispExp::List(list) => {
            let first_form: Option<&LispExp> = list.first();

            let first_form = match first_form {
                None => return Ok(LispExp::Nil),
                Some(v) => v,
            };
            let arg_forms = &list[1..];

            match eval_built_in_form(first_form, arg_forms, env) {
                Some(result) => result,
                None => {
                    let first_eval = eval(first_form, env)?;

                    match first_eval {
                        LispExp::Func(f) => {
                            let args_eval = eval_forms(arg_forms, env);
                            f(&args_eval?)
                        },
                        LispExp::Lambda(lambda) => {
                            let new_env = &mut env_for_lambda(lambda.params_exp, arg_forms, env)?;
                            eval(&lambda.body_exp, new_env)
                        }
                        _ => Err(LispErr::SyntaxError(SyntaxErr::WrongExpExpected(LispExp::Func(|_args: &[LispExp]| -> Result<LispExp, LispErr>{Ok(LispExp::Number(1 as f64))}))))
                    }
                }
            }
        },
        LispExp::Func(f) => Err(LispErr::SyntaxError(SyntaxErr::WrongExpDidNotExpect(LispExp::Func(*f)))),
        LispExp::Nil => Ok(LispExp::Nil),
        LispExp::Lambda(_) => Err(LispErr::SyntaxError(SyntaxErr::NoFormSyntaxExpected)),
        LispExp::Quote(_) => Err(LispErr::SyntaxError(SyntaxErr::WrongExpDidNotExpect(LispExp::Quote(vec![])))),
    }
}

fn eval_forms(arg_forms: &[LispExp], env: &mut LispEnv) -> Result<Vec<LispExp>, LispErr> {
    arg_forms
        .iter()
        .map(|x| {eval(x, env)})
        .collect()
}

fn eval_built_in_form(exp: &LispExp, arg_forms: &[LispExp], env: &mut LispEnv) -> Option<Result<LispExp, LispErr>>{
    match exp {
        LispExp::Symbol(s) => {
            match s.as_ref() {
                "if" => Some(eval_if_args(arg_forms, env)),
                "def" => Some(eval_def_args(arg_forms, env)),
                "fn" => Some(eval_lambda_args(arg_forms)),
                "quote" => Some(dont_eval_quote(arg_forms)),
                _ => None,
            }
        },
        _ => None,
    }
}

fn dont_eval_quote(arg_forms: &[LispExp]) -> Result<LispExp, LispErr> {
    Ok(LispExp::Quote(arg_forms.to_vec()))
}

fn eval_if_args(arg_forms: &[LispExp], env: &mut LispEnv) -> Result<LispExp, LispErr> {
    let if_form = arg_forms.first().ok_or(LispErr::SyntaxError(SyntaxErr::DidExpectFormSyntax("if".to_string())))?;
    let if_eval = eval(if_form, env)?;

    match if_eval {
        LispExp::Bool(b) => {
            let form_idx = if b { 1 } else { 2 };
            let result_form = arg_forms.get(form_idx).ok_or(LispErr::SyntaxError(SyntaxErr::WrongFormNum(form_idx)))?;
            let result_eval = eval(result_form, env);

            result_eval
        },
        _ => Err(LispErr::SyntaxError(SyntaxErr::WrongExpDidNotExpect(if_eval))),
    }
}

fn eval_def_args(arg_forms: &[LispExp], env: &mut LispEnv) -> Result<LispExp, LispErr> {

    if arg_forms.len() > 2 {
        return Err(LispErr::SyntaxError(SyntaxErr::WrongFormNum(2)));
    }

    let first_form = arg_forms.first().ok_or(LispErr::SyntaxError(SyntaxErr::DidExpectFormSyntax("def".to_string())))?;
    let first_str = match first_form {
        LispExp::Symbol(s) => {Ok(s.clone())}
        _ => Err(LispErr::SyntaxError(SyntaxErr::WrongFormExp(0, LispExp::Symbol("a".to_string()))))
    }?;

    let second_form = arg_forms.get(1).ok_or(LispErr::SyntaxError(SyntaxErr::WrongFormNum(2)))?;

    let second_eval = eval(second_form, env)?;
    env.data.insert(first_str, second_eval);

    Ok(first_form.clone())

}

fn eval_lambda_args(arg_forms: &[LispExp]) -> Result<LispExp, LispErr> {
    if arg_forms.len() != 2 {
        return Err(LispErr::SyntaxError(SyntaxErr::WrongFormNum(2)));
    }
    let params_exp = arg_forms.first().ok_or(LispErr::SyntaxError(SyntaxErr::WrongFormNum(2)))?;

    let body_exp = arg_forms.get(1).ok_or(LispErr::SyntaxError(SyntaxErr::WrongFormNum(2)))?;
    
    Ok(LispExp::Lambda(LispLambda {
        params_exp: Rc::new(params_exp.clone()),
        body_exp: Rc::new(body_exp.clone()),
    }))
}

fn env_get(k: &str, env: &LispEnv) -> Option<LispExp> {
    match env.data.get(k) {
        Some(exp) => Some(exp.clone()),
        None => {
            match &env.outer {
                None => None,
                Some(outer_env) => env_get(k, outer_env),
            }
        }
    }
}

fn env_for_lambda<'a> (params: Rc<LispExp>, arg_forms: &[LispExp], outer_env: &'a mut LispEnv) -> Result<LispEnv<'a>, LispErr> {
    let ks = parse_list_of_symbol_strings(params)?;
    if ks.len() != arg_forms.len() {
        return Err(LispErr::SyntaxError(SyntaxErr::WrongExpNumber));
    }
    
    let vs = eval_forms(arg_forms, outer_env)?;
    let mut data: HashMap<String, LispExp> = HashMap::new();
    
    for (k,v) in ks.iter().zip(vs.iter()) {
        data.insert(k.clone(), v.clone());
    }
    
    Ok(LispEnv {
        data,
        outer: Some(outer_env),
    })
}

fn parse_list_of_symbol_strings(from: Rc<LispExp>) -> Result<Vec<String>, LispErr> {
    let list = match from.as_ref() {
        LispExp::List(s) => Ok(s.clone()),
        _ => Err(LispErr::SyntaxError(SyntaxErr::WrongExpExpected(LispExp::List(vec![])))),
    }?;

    list.iter().map(|x| {
        match x {
            LispExp::Symbol(s) => Ok(s.clone()),
            _ => Err(LispErr::SyntaxError(SyntaxErr::WrongExpExpected(LispExp::Symbol("s".to_string())))),
        }
    }).collect()
}

fn parse_eval(exp: String, env: &mut LispEnv) -> Result<LispExp, LispErr> {
    if parse(&tokenize(exp.clone()))?.1.is_empty() == false {
        return Err(LispErr::UnbalancedParens);
    } else {
        let (parsed_exp, _) = parse(&tokenize(exp.clone()))?;
        let evaluated_exp = eval(&parsed_exp, env)?;

        Ok(evaluated_exp)
    }

}

fn slurp_exp(input: &mut (impl Read  + BufRead)) -> String {
    let mut exp = String::new();
    input.read_line(&mut exp).expect("Failed to read input line!");

    exp
}

#[macro_export]
macro_rules! ensure_tonicity {
  ($check_fn:expr) => {{
    |args: &[LispExp]| -> Result<LispExp, LispErr> {
      let floats = parse_list_of_floats(args)?;
      let first = floats.first().ok_or(LispErr::SyntaxError(SyntaxErr::WrongExpNumber))?;
      let rest = &floats[1..];
      fn f (prev: &f64, xs: &[f64]) -> bool {
        match xs.first() {
          Some(x) => $check_fn(prev, x) && f(x, &xs[1..]),
          None => true,
        }
      }
      Ok(LispExp::Bool(f(first, rest)))
    }
  }};
}



#[cfg(test)]
mod tests {
    use super::*;
    static EXIT_PHRASE: &str = "\nexit";
    static RESULT_PART: &str = "lisp >\n";

    #[test]
    fn add_test() {
        let input: Vec<u8> = format!("(+ 1 2){}", EXIT_PHRASE).as_bytes().to_vec();
        let mut output: Vec<u8> = vec![];
        let mut err_output: Vec<u8> = vec![];
        let result: Vec<u8> = format!("{}3\n{}", RESULT_PART, RESULT_PART).as_bytes().to_vec();

        run(InputSource::StdIn, &mut BufReader::new(input.as_slice()), &mut output, &mut err_output);

        assert_eq!(std::str::from_utf8(&output), std::str::from_utf8(&result));
    }

    #[test]
    fn failing_add_test() {
        let input: Vec<u8> = format!("(+ 1 2){}", EXIT_PHRASE).as_bytes().to_vec();
        let mut output: Vec<u8> = vec![];
        let mut err_output: Vec<u8> = vec![];
        let result: Vec<u8> = format!("{}1\n{}", RESULT_PART, RESULT_PART).as_bytes().to_vec();

        run(InputSource::StdIn, &mut BufReader::new(input.as_slice()), &mut output, &mut err_output);

        assert_ne!(std::str::from_utf8(&output), std::str::from_utf8(&result));
    }

    #[test]
    fn sub_test() {
        let input: Vec<u8> = format!("(- 2 1){}", EXIT_PHRASE).as_bytes().to_vec();
        let mut output: Vec<u8> = vec![];
        let mut err_output: Vec<u8> = vec![];
        let result: Vec<u8> = format!("{}1\n{}", RESULT_PART, RESULT_PART).as_bytes().to_vec();

        run(InputSource::StdIn, &mut BufReader::new(input.as_slice()), &mut output, &mut err_output);
        assert_eq!(std::str::from_utf8(&output), std::str::from_utf8(&result));
    }

    #[test]
    fn failing_sub_test() {
        let input: Vec<u8> = format!("(- 2 1){}", EXIT_PHRASE).as_bytes().to_vec();
        let mut output: Vec<u8> = vec![];
        let mut err_output: Vec<u8> = vec![];
        let result: Vec<u8> = format!("{}3\n{}", RESULT_PART, RESULT_PART).as_bytes().to_vec();

        run(InputSource::StdIn, &mut BufReader::new(input.as_slice()), &mut output, &mut err_output);
        assert_ne!(std::str::from_utf8(&output), std::str::from_utf8(&result));
    }

    #[test]
    fn mul_test() {
        let input: Vec<u8> = format!("(* 1 2){}", EXIT_PHRASE).as_bytes().to_vec();
        let mut output: Vec<u8> = vec![];
        let mut err_output: Vec<u8> = vec![];
        let result: Vec<u8> = format!("{}2\n{}", RESULT_PART, RESULT_PART).as_bytes().to_vec();

        run(InputSource::StdIn, &mut BufReader::new(input.as_slice()), &mut output, &mut err_output);
        assert_eq!(std::str::from_utf8(&output), std::str::from_utf8(&result));
    }

    #[test]
    fn failing_mul_test() {
        let input: Vec<u8> = format!("(* 1 2){}", EXIT_PHRASE).as_bytes().to_vec();
        let mut output: Vec<u8> = vec![];
        let mut err_output: Vec<u8> = vec![];
        let result: Vec<u8> = format!("{}5\n{}", RESULT_PART, RESULT_PART).as_bytes().to_vec();

        run(InputSource::StdIn, &mut BufReader::new(input.as_slice()), &mut output, &mut err_output);
        assert_ne!(std::str::from_utf8(&output), std::str::from_utf8(&result));
    }

    #[test]
    fn div_test() {
        let input: Vec<u8> = format!("(/ 4 2){}", EXIT_PHRASE).as_bytes().to_vec();
        let mut output: Vec<u8> = vec![];
        let mut err_output: Vec<u8> = vec![];
        let result: Vec<u8> = format!("{}2\n{}", RESULT_PART, RESULT_PART).as_bytes().to_vec();

        run(InputSource::StdIn, &mut BufReader::new(input.as_slice()), &mut output, &mut err_output);
        assert_eq!(std::str::from_utf8(&output), std::str::from_utf8(&result));
    }

    #[test]
    fn failing_div_test() {
        let input: Vec<u8> = format!("(/ 4 2){}", EXIT_PHRASE).as_bytes().to_vec();
        let mut output: Vec<u8> = vec![];
        let mut err_output: Vec<u8> = vec![];
        let result: Vec<u8> = format!("{}5\n{}", RESULT_PART, RESULT_PART).as_bytes().to_vec();

        run(InputSource::StdIn, &mut BufReader::new(input.as_slice()), &mut output, &mut err_output);
        assert_ne!(std::str::from_utf8(&output), std::str::from_utf8(&result));
    }

    #[test]
    fn mod_test() {
        let input: Vec<u8> = format!("(mod 3 2){}", EXIT_PHRASE).as_bytes().to_vec();
        let mut output: Vec<u8> = vec![];
        let mut err_output: Vec<u8> = vec![];
        let result: Vec<u8> = format!("{}1\n{}", RESULT_PART, RESULT_PART).as_bytes().to_vec();

        run(InputSource::StdIn, &mut BufReader::new(input.as_slice()), &mut output, &mut err_output);
        assert_eq!(std::str::from_utf8(&output), std::str::from_utf8(&result));
    }

    #[test]
    fn failing_mod_test() {
        let input: Vec<u8> = format!("(mod 3 2){}", EXIT_PHRASE).as_bytes().to_vec();
        let mut output: Vec<u8> = vec![];
        let mut err_output: Vec<u8> = vec![];
        let result: Vec<u8> = format!("{}3\n{}", RESULT_PART, RESULT_PART).as_bytes().to_vec();

        run(InputSource::StdIn, &mut BufReader::new(input.as_slice()), &mut output, &mut err_output);
        assert_ne!(std::str::from_utf8(&output), std::str::from_utf8(&result));
    }

    #[test]
    fn def_test() {
        let input: Vec<u8> = format!("(def a 2){}", EXIT_PHRASE).as_bytes().to_vec();
        let mut output: Vec<u8> = vec![];
        let mut err_output: Vec<u8> = vec![];
        let result: Vec<u8> = format!("{}a\n{}", RESULT_PART, RESULT_PART).as_bytes().to_vec();

        run(InputSource::StdIn, &mut BufReader::new(input.as_slice()), &mut output, &mut err_output);
        assert_eq!(std::str::from_utf8(&output), std::str::from_utf8(&result));
    }

    #[test]
    fn def_2_test() {
        let input: Vec<u8> = format!("(def a 2)\na{}", EXIT_PHRASE).as_bytes().to_vec();
        let mut output: Vec<u8> = vec![];
        let mut err_output: Vec<u8> = vec![];
        let result: Vec<u8> = format!("{}a\n{}2\n{}", RESULT_PART, RESULT_PART, RESULT_PART).as_bytes().to_vec();

        run(InputSource::StdIn, &mut BufReader::new(input.as_slice()), &mut output, &mut err_output);
        assert_eq!(std::str::from_utf8(&output), std::str::from_utf8(&result));
    }

    #[test]
    fn failing_def_test() {
        let input: Vec<u8> = format!("(def a 2){}", EXIT_PHRASE).as_bytes().to_vec();
        let mut output: Vec<u8> = vec![];
        let mut err_output: Vec<u8> = vec![];
        let result: Vec<u8> = format!("{}2\n{}", RESULT_PART, RESULT_PART).as_bytes().to_vec();

        run(InputSource::StdIn, &mut BufReader::new(input.as_slice()), &mut output, &mut err_output);
        assert_ne!(std::str::from_utf8(&output), std::str::from_utf8(&result));
    }

    #[test]
    fn if_test() {
        let input: Vec<u8> = format!("(if true 2 3){}", EXIT_PHRASE).as_bytes().to_vec();
        let mut output: Vec<u8> = vec![];
        let mut err_output: Vec<u8> = vec![];
        let result: Vec<u8> = format!("{}2\n{}", RESULT_PART, RESULT_PART).as_bytes().to_vec();

        run(InputSource::StdIn, &mut BufReader::new(input.as_slice()), &mut output, &mut err_output);
        assert_eq!(std::str::from_utf8(&output), std::str::from_utf8(&result));
    }

    #[test]
    fn failing_if_test() {
        let input: Vec<u8> = format!("(if false 2 3){}", EXIT_PHRASE).as_bytes().to_vec();
        let mut output: Vec<u8> = vec![];
        let mut err_output: Vec<u8> = vec![];
        let result: Vec<u8> = format!("{}2\n{}", RESULT_PART, RESULT_PART).as_bytes().to_vec();

        run(InputSource::StdIn, &mut BufReader::new(input.as_slice()), &mut output, &mut err_output);
        assert_ne!(std::str::from_utf8(&output), std::str::from_utf8(&result));
    }

    #[test]
    fn lambda_test() {
        let input: Vec<u8> = format!("(def add-one (fn (a) (+ a 1)))\n(add-one 2){}", EXIT_PHRASE).as_bytes().to_vec();
        let mut output: Vec<u8> = vec![];
        let mut err_output: Vec<u8> = vec![];
        let result: Vec<u8> = format!("{}add-one\n{}3\n{}", RESULT_PART, RESULT_PART, RESULT_PART).as_bytes().to_vec();

        run(InputSource::StdIn, &mut BufReader::new(input.as_slice()), &mut output, &mut err_output);
        assert_eq!(std::str::from_utf8(&output), std::str::from_utf8(&result));
    }

    #[test]
    fn failing_lambda_test() {
        let input: Vec<u8> = format!("(def add-one (fn (a) (+ a 1)))\n(add-one 2){}", EXIT_PHRASE).as_bytes().to_vec();
        let mut output: Vec<u8> = vec![];
        let mut err_output: Vec<u8> = vec![];
        let result: Vec<u8> = format!("{}add-one\n{}1\n{}", RESULT_PART, RESULT_PART, RESULT_PART).as_bytes().to_vec();

        run(InputSource::StdIn, &mut BufReader::new(input.as_slice()), &mut output, &mut err_output);
        assert_ne!(std::str::from_utf8(&output), std::str::from_utf8(&result));
    }

    #[test]
    fn quote_test() {
        let input: Vec<u8> = format!("(quote a){}", EXIT_PHRASE).as_bytes().to_vec();
        let mut output: Vec<u8> = vec![];
        let mut err_output: Vec<u8> = vec![];
        let result: Vec<u8> = format!("{}a\n{}", RESULT_PART, RESULT_PART).as_bytes().to_vec();

        run(InputSource::StdIn, &mut BufReader::new(input.as_slice()), &mut output, &mut err_output);
        assert_eq!(std::str::from_utf8(&output), std::str::from_utf8(&result));
    }

    #[test]
    fn quote_2_test() {
        let input: Vec<u8> = format!("(quote a b c){}", EXIT_PHRASE).as_bytes().to_vec();
        let mut output: Vec<u8> = vec![];
        let mut err_output: Vec<u8> = vec![];
        let result: Vec<u8> = format!("{}a b c\n{}", RESULT_PART, RESULT_PART).as_bytes().to_vec();

        run(InputSource::StdIn, &mut BufReader::new(input.as_slice()), &mut output, &mut err_output);
        assert_eq!(std::str::from_utf8(&output), std::str::from_utf8(&result));
    }

    #[test]
    fn quote_3_test() {
        let input: Vec<u8> = format!("(quote a b c (a b)){}", EXIT_PHRASE).as_bytes().to_vec();
        let mut output: Vec<u8> = vec![];
        let mut err_output: Vec<u8> = vec![];
        let result: Vec<u8> = format!("{}a b c (a,b)\n{}", RESULT_PART, RESULT_PART).as_bytes().to_vec();

        run(InputSource::StdIn, &mut BufReader::new(input.as_slice()), &mut output, &mut err_output);
        assert_eq!(std::str::from_utf8(&output), std::str::from_utf8(&result));
    }
}

