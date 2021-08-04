use lisp_interpreter::{run, InputSource};
use std::env;

fn main() {

    if env::args().len() >= 3 {
        let args_list: Vec<String> = env::args().collect();
        let args_list: Vec<&str> = args_list.iter().map(|x| {x.as_str()}).collect();

        match args_list.get(1) {
            None => run(InputSource::StdIn),
            Some(s) => {
                match s{
                    &"-f" => run(InputSource::File(args_list[2].to_string())),
                    &"-s" => run(InputSource::StdIn),
                    _ => {
                        eprintln!("Error! Unknown argument at position 1!");
                        eprintln!("Expected '-f' and 'filepath' for file interpretation, or '-s' for console line interpretation!");
                    },
                }
            }
        }
    } else {
        run(InputSource::StdIn);
    }


}
