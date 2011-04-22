(** * Internals *)

Require Import SfLib.

Require Import String.
Require Import Ascii.
Require Import ZArith.
Require Import QArith.

Require Import Recdef.

Require Import pdftype.
Require Import sublist.
Require Import parser.

Open Scope list_scope.



(* ####################################################### *)
(** ** Lexical Analysis *)

Open Scope nat_scope.
Open Scope char_scope.

(* character class helpers *)

Definition never : ascii -> bool :=
  fun _ => false.

Definition check_aux (to : ascii) (continuation : ascii -> bool) : ascii -> bool :=
  fun c =>
    (orb (eq_ascii c to) (continuation c)).

Notation "{{ a , .. , b }}" := (check_aux a .. (check_aux b never)  .. ) (at level 0).

Notation "a 'isin' f" := (f a) (at level 1, only parsing).

Definition ascii_sequence (from to : ascii) : ascii -> bool :=
  let (a,c) := (nat_of_ascii from, nat_of_ascii to) in
  fun chr =>
    let b := nat_of_ascii chr in
    (a <=? b) && (b <=? c).

Notation "{[ a '--' b ]}" := (ascii_sequence a b) (at level 42).

Example ascii_sequence_decimal_works :
  let num := {["0"--"9"]} in
    ("0" isin num) && ("4" isin num) && ("9" isin num)
    && (negb (("a" isin num) || ("}" isin num) )) = true.
Proof.  reflexivity.  Qed.

(* some character classes *)

Definition isWhite (c : ascii) : bool :=
  {{"000", "009", "010", "012", "013", "032"}} c.
  (* NUL TAB LF formfeed CR space *)

Definition isDelimiter (c : ascii) : bool :=
  {{"(", ")", "<", ">", "[", "]", "{", "}", "/", "%"}} c.

Definition isAscii (c : ascii) : bool :=
  let n := nat_of_ascii c in
    (n <=? 127).

Definition isRegularCharacter (c : ascii) : bool :=
  (andb (isAscii c) (negb (orb (isWhite c) (isDelimiter c)))).

Definition isDigit (c : ascii) : bool :=
  {["0"--"9"]} c.

Definition isHexDigit (c : ascii) : bool :=
  (isDigit c) || (c isin {["a"--"f"]}) || (c isin {["A"--"F"]}).

Definition match_digit := match_one_char_with_predicate isDigit.

Definition match_integer := many match_digit.

Definition match_white := match_one_char_with_predicate isWhite.

Definition match_hex_digit := match_one_char_with_predicate isHexDigit.

Definition Z_of_ascii (d : ascii) := Z_of_nat (nat_of_ascii d).

Definition Z_of_digit (d : ascii) := ((Z_of_ascii d) - 48)%Z.

Definition match_sign :=
  match_one_char_with_predicate (fun x => x isin {{"-", "+"}})%char.

Definition parse_boolean : parser PDF.PDFObject :=
  fun xs =>
    match alternative (match_string "true") (match_string "false") xs with
      | SomeE ("true"%string, xs') => SomeE (PDF.PDFBoolean true, xs')
      | SomeE ("false"%string, xs') => SomeE (PDF.PDFBoolean false, xs')
      | SomeE (_, xs') => NoneE "das kann eh nicht passieren, aber unsere Typen sind zu schwach"
      | NoneE err => NoneE err
    end.

Example parse_boolean1 :
  exists e,
    parse_boolean (list_of_string "true"%string) = SomeE (PDF.PDFBoolean true, e).
Proof.  cbv; eexists; reflexivity.  Qed.

Example parse_boolean2 :
  exists e,
    parse_boolean (list_of_string "false"%string) = SomeE (PDF.PDFBoolean false, e).
Proof.  cbv; eexists; reflexivity.  Qed.

Example parse_boolean3 :
  exists e,
    parse_boolean (list_of_string "unsinn"%string) = NoneE e.
Proof.  cbv; eexists; reflexivity.  Qed.

Definition parse_unsigned_integer : parser Z :=
  fun xs =>
    match match_integer xs with
      | NoneE e => NoneE "No digits found while parsing integer"
      | SomeE (digits, xs')
        => SomeE (fold_left
                    (fun a b => a * 10 + b)
                    (map Z_of_digit digits)
                    0,
                  xs')%Z
    end.

Definition parse_integer : parser Z :=
  fun xs =>
    match sequential_leftopt match_sign parse_unsigned_integer xs with
      | SomeE ((SomeE("+"%char), val), xs') => SomeE(val, xs')
      | SomeE ((SomeE("-"%char), val), xs') => SomeE((val * -1)%Z, xs')
      | SomeE ((SomeE(_), val), xs') => NoneE "das kann eh nicht passieren, aber unsere Typen sind zu schwach"
      | SomeE ((NoneE _, val), xs') => SomeE(val, xs')
      | NoneE err => NoneE err
    end.

Example parse_integer1 :
  exists e,
    parse_integer (list_of_string("123")) = SomeE (123%Z, e).
Proof. cbv; eexists; reflexivity. Qed.

Example parse_integer2 :
  exists e,
    parse_integer (list_of_string("123foo")) = SomeE (123%Z, e).
Proof. cbv; eexists; reflexivity. Qed.

Example parse_integer3 :
  exists e,
    parse_integer (list_of_string("foo")) = NoneE e.
Proof. cbv; eexists; reflexivity. Qed.

Example parse_integer4 :
  exists e,
    parse_integer (list_of_string("-123")) = SomeE ((-123)%Z, e).
Proof. cbv; eexists; reflexivity. Qed.

Example parse_integer5 :
  exists e,
    parse_integer (list_of_string("+123")) = SomeE ((123)%Z, e).
Proof. cbv; eexists; reflexivity. Qed.

Example parse_integer6 :
  exists e,
    parse_integer (list_of_string("K123")) = NoneE e.
Proof. cbv; eexists; reflexivity. Qed.

Definition Z_of_hex_digit (c : ascii) :=
  (if c isin {["0"--"9"]} then
    Z_of_ascii(c) - Z_of_ascii("0")
  else if c isin {["a"--"f"]} then
    Z_of_ascii(c) - Z_of_ascii("a") + 10
    else if c isin {["A"--"F"]} then
      Z_of_ascii(c) - Z_of_ascii("A") + 10
      else -1)%Z.

Definition ascii_of_Z (z : Z) :=
  ascii_of_nat (Zabs_nat z).

Program Definition match_hex : parser ascii :=
  fix f xs :=
    match xs with
      | []        => NoneE "end of stream while parsing hex"
      | c1::l0 =>
           if isWhite c1 then
             @pf_skipped_one_character c1 l0 (f l0)
           else
             match l0 with
             | [] => NoneE "end of stream while parsing hex"
             | c2::l => if isHexDigit c1 then
               if isHexDigit c2 then
                 SomeE (ascii_of_Z (Z_of_hex_digit(c1) * 16 + Z_of_hex_digit(c2)),
                        exist _ l _)
               else
                 SomeE (ascii_of_Z (Z_of_hex_digit(c1) * 16),
                        exist _ (c2::l) _)
             else
               NoneE "no hex digits found"
             end
    end.

Example whitespace_regression :
  exists e,
    match_hex (list_of_string " 23"%string) =
      SomeE("#", e).
Proof.
  cbv. eexists. reflexivity.
Qed.


Definition parse_hex_string : parser string :=
  fun xs =>
    match
      sequential3 (match_exactly "<") (many match_hex) (match_exactly ">") xs
    with
      | SomeE ((_, l, _), xs') => SomeE (string_of_list l, xs')
      | NoneE err => NoneE err
    end.

Example parse_hex_string1 :
  exists e,
    parse_hex_string (list_of_string "<48454c4C4f>"%string)
      = SomeE("HELLO"%string, e).
Proof.
  cbv. eexists. reflexivity.
Qed.

Example parse_hex_string2_trailing_zero :
  exists e,
    parse_hex_string (list_of_string "<48454c4C5>"%string)
      = SomeE("HELLP"%string, e).
Proof.
  cbv. eexists. reflexivity.
Qed.

Example parse_hex_string3_whitespace :
  exists e,
    parse_hex_string (list_of_string "<48 454c4C4f>"%string)
      = SomeE("HELLO"%string, e).
Proof.
  cbv. eexists. reflexivity.
Qed.



(*
boolean,
integer,
float,
string,
name,
array,
dictionary,
stream,
null
indirect object
*)

Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlZInt.
Require Import ExtrOcamlString.

Extraction "parser.ml" parse_hex_string parse_integer.