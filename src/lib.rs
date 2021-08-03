use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::num::ParseFloatError;
use std::io;

pub fn run() {
    let env = &mut default_env();

    loop {
        println!("lisp >");
        let exp = slurp_exp();
        match parse_eval(exp, env) {
            Ok(result) => println!("{}", result),
            Err(e) => println!("{}", e.to_string()),
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
        };

        write!(f, "{}", display_string)
    }
}

enum SyntaxErr {
    WrongExpExpected(LispExp),
    WrongExpDidNotExpect(LispExp),
    WrongExpNumber,
}

impl Display for SyntaxErr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let preamble: String = String::from("Syntax error!");
        let message = match self {
            SyntaxErr::WrongExpExpected(exp) => format!("Needed a {} expression, but got something else!", exp.exp_to_string()),
            SyntaxErr::WrongExpNumber => format!("Got the wrong number of expressions!"),
            SyntaxErr::WrongExpDidNotExpect(exp) => format!("Got a {} expression, but needed something else!", exp.exp_to_string()),
        };

        write!(f, "{} {}", preamble, message)
    }
}

enum LispErr {
    SyntaxErr(SyntaxErr),
    UnbalancedParens,
    UnknownSymbol(String),
}

impl Display for LispErr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let message: String = match self {
            LispErr::SyntaxErr(err) => err.to_string(),
            LispErr::UnbalancedParens => "Unbalanced parens!".to_string(),
            LispErr::UnknownSymbol(k) => format!("Unknown symbol {}!", k),
        };

        write!(f, "{}",message)
    }
}

pub struct LispEnv {
    data: HashMap<String, LispExp>,
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
        LispErr::SyntaxErr(SyntaxErr::WrongExpNumber)
    )?;

    match &token[..] {
        "(" => read_seq(rest),
        ")" => Err(LispErr::UnbalancedParens),
        _ => Ok((parse_atom(token), rest)),
    }
}

fn read_seq(tokens: &[String]) -> Result<(LispExp, &[String]), LispErr> {
    let mut result: Vec<LispExp> = Vec::new();
    let mut xs = tokens;

    loop {
        let (next_token, rest) = xs
            .split_first()
            .ok_or(LispErr::UnbalancedParens)?;

        if next_token == ")" {
            return Ok((LispExp::List(result), rest));
        }

        let (exp, new_xs) = parse(&xs)?;
        result.push(exp);
        xs = new_xs;
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


fn default_env() -> LispEnv {
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
                let first = *floats.first().ok_or(LispErr::SyntaxErr(SyntaxErr::WrongExpNumber))?;
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
                let first = *floats.first().ok_or(LispErr::SyntaxErr(SyntaxErr::WrongExpNumber))?;
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
                    return Err(LispErr::SyntaxErr(SyntaxErr::WrongExpNumber));
                }
                let first = *floats.first().ok_or(LispErr::SyntaxErr(SyntaxErr::WrongExpNumber))?;
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

    LispEnv {data}
}

fn parse_single_float(exp: &LispExp) -> Result<f64, LispErr> {
    match exp {
        LispExp::Number(num) => Ok(*num),
        _ => Err(LispErr::SyntaxErr(SyntaxErr::WrongExpExpected(LispExp::Number(0 as f64))))
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
        LispExp::Symbol(k) => env.data.get(k).ok_or(LispErr::UnknownSymbol(k.clone())).map(|x| x.clone()),
        LispExp::Number(_a) => Ok(exp.clone()),
        LispExp::List(list) => {
            let first_form: Option<&LispExp> = list.first();

            let first_form = match first_form {
                None => return Ok(LispExp::Nil),
                Some(v) => v,
            };
            let arg_forms = &list[1..];
            let first_eval = eval(first_form, env)?;

            match first_eval {
                LispExp::Func(f) => {
                    let args_eval = arg_forms.iter().map(|x| eval(x, env)).collect::<Result<Vec<LispExp>, LispErr>>();
                    f(&args_eval?)
                },
                _ => Err(LispErr::SyntaxErr(SyntaxErr::WrongExpExpected(LispExp::Func(|_args: &[LispExp]| -> Result<LispExp, LispErr>{Ok(LispExp::Number(1 as f64))}))))
            }
        }
        LispExp::Func(f) => Err(LispErr::SyntaxErr(SyntaxErr::WrongExpDidNotExpect(LispExp::Func(*f)))),
        LispExp::Nil => Ok(LispExp::Nil),

    }
}

fn parse_eval(exp: String, env: &mut LispEnv) -> Result<LispExp, LispErr> {
    let (parsed_exp, _) = parse(&tokenize(exp))?;
    let evaluated_exp = eval(&parsed_exp, env)?;

    Ok(evaluated_exp)
}

fn slurp_exp() -> String {
    let mut exp = String::new();
    io::stdin().read_line(&mut exp).expect("Failed to read input line!");

    exp
}

#[macro_export]
macro_rules! ensure_tonicity {
  ($check_fn:expr) => {{
    |args: &[LispExp]| -> Result<LispExp, LispErr> {
      let floats = parse_list_of_floats(args)?;
      let first = floats.first().ok_or(LispErr::SyntaxErr(SyntaxErr::WrongExpNumber))?;
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