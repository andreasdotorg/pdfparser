open Batteries_uni
open Print
open String
open File
open IO

open Allparser

let list_of_string s =
  let rec list_of_string_aux acc s i =
    if i = 0 then
      s.[i]::acc
    else
      list_of_string_aux (s.[i]::acc) s (pred i)
  in
    list_of_string_aux [] s (pred (length s));;

let string_of_list l =
  let s = create (List.length l) in
  let rec string_of_list_aux ll i =
    match ll with
    | head::tail -> begin s.[i] <- head; string_of_list_aux tail (succ i) end
    | [] -> s
  in
    string_of_list_aux l 0;;

parse_integer (list_of_string "1234567890123456789012345678901234567890")

(*
let infile = open_in "foo.input" in
let data = read_all infile in
begin
  close_in infile;
  match parse_hex_string (list_of_string data) with
  | SomeE s   -> let outfile = open_out "foo.output" in
                 begin
                   nwrite outfile (string_of_list (fst s));
                   close_out outfile
                 end
  | NoneE err -> Print.printf p"%s\n" (string_of_list err)
end
*)