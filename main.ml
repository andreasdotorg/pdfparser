open Batteries_uni
open Print
open Allparser

match parse_hex_string ('<'::'4'::'5'::'4'::'1'::'>'::[]) with
| SomeE s   -> printf p"{%{char list}}" (fst s)
| NoneE err -> printf p"{%{char list}}" err
