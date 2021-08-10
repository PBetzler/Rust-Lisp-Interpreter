# Rust Lisp Interpreter

This is a learning project for both rust and lisp.
It's core mechanics are based on the tutorial [Risp](https://dev.to/stopachka/risp-in-rust-lisp-5cle).
There have been many modifications regarding the error handling, nil values, the functions provided 
and a file interpretation has been added.

By now, the interpreter supports:

- Booleans
- Symbols
- Numbers
- Lists
- Functions
- Lambdas
- Nil
- Quote
- Cons
- Car
- Cdr
 
- \+
- \-
- \*
- \/
- %
- \>
- \>=
- <
- <=
- =

Rust takes care of the memory management and thus a garbage collector is not needed.

To read from stdin skip the args or add '-s',
to read and interpret a file add '-f' and 'filepath'.