(** * Internals *)

Require Import SfLib.

Require Import String.
Require Import Ascii.
Require Import ZArith.
Require Import QArith.

Require Import Recdef.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.

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

Definition CR := "013".
Definition LF := "010".

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

Definition isNotParen (c : ascii) : bool :=
  andb (negb (eq_ascii c "(")) (negb (eq_ascii c ")")).

Definition match_digit := match_one_char_with_predicate isDigit.

Definition match_integer := many match_digit.

Definition match_white := match_one_char_with_predicate isWhite.

Definition match_hex_digit := match_one_char_with_predicate isHexDigit.

Definition Z_of_ascii (d : ascii) := Z_of_nat (nat_of_ascii d).

(* Performance hack... *)
Definition C48 := 48.
Definition C48Z := 48%Z.

Definition C10 := 10.
Definition C10Z := 10%Z.

Definition Z_of_digit (d : ascii) := ((Z_of_ascii d) - C48Z)%Z.

Definition nat_of_digit (d : ascii) := (nat_of_ascii d) - C48.

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

Definition parse_nat : parser nat :=
  fun xs =>
    match match_integer xs with
      | NoneE e => NoneE "No digits found while parsing integer"
      | SomeE (digits, xs')
        => SomeE (fold_left
                    (fun a b => a * C10 + b)
                    (map nat_of_digit digits)
                    0,
                  xs')
    end.

Definition parse_unsigned_integer : parser Z :=
  fun xs =>
    match match_integer xs with
      | NoneE e => NoneE "No digits found while parsing integer"
      | SomeE (digits, xs')
        => SomeE (fold_left
                    (fun a b => a * C10Z + b)
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

Ltac xref_solver :=
  try program_simpl;
  try (repeat (split; unfold not; intros; (try inversion H)));
  try (split; unfold not; intros; (try inversion H); split; unfold not; intros; inversion H; fail);
  try (split; unfold not; intro H'; inversion H'; fail);
  try (split; unfold not; intro; intro H'; inversion H'; fail);
  try (eauto; fail).

Local Obligation Tactic := xref_solver.

(* \ has already been parsed away *)
Program Definition parse_char_string_escape : parser ascii :=
  fun xs =>
    match xs with
      | []       => NoneE "end of string reached during escape parsing"%string
      | "n"::xs' => SomeE ("010", exist _ xs' _)
      | "r"::xs' => SomeE ("013", exist _ xs' _)
      | "t"::xs' => SomeE ("009", exist _ xs' _)
      | "b"::xs' => SomeE ("008", exist _ xs' _)
      | "f"::xs' => SomeE ("012", exist _ xs' _)
      | "("::xs' => SomeE ("(", exist _ xs' _)
      | ")"::xs' => SomeE (")", exist _ xs' _)
      | "\"::xs' => SomeE ("\", exist _ xs' _)
      | _        => NoneE "Illegal escape character"
        (* oh yeah, need to do octal
      | "000"::xs' => SomeE (LF, xs') *)
    end.

(*
Definition parse_string : parser string :=
  fun xs =>
    match
      sequential3 (match_exactly "(") (many parse_char_string_escape) (match_exactly ")") xs
    with
      | SomeE ((_, l, _), xs') => SomeE (string_of_list l, xs')
      | NoneE err => NoneE err
    end.
*)

Definition parse_nonparen_string := many (match_one_char_with_predicate isNotParen).

Definition lift_base {A : Type} {P : A -> Prop} (s : sig P) := 
  match s with | exist a b => a end.

Require Import Coq.Program.Wf.

Program Fixpoint match_with_level l acc xs {measure (List.length xs)} : 
  optionE ((list ascii) * {xs' : list ascii | sublist xs' xs}) :=
  match xs with
    | [] => NoneE "end of string reached"

    | "("::xs' => match xs' with
                    | [] => NoneE "too many open parentheses"
                    | _  =>
                      match match_with_level (S l) ("("::acc) xs' with
                        | SomeE (res, exist xs'' H) => SomeE (res, exist _ xs'' _)
                        | NoneE err => NoneE err
                      end
                  end
    | ")"::xs' => match l with
                    | 0      => NoneE "too many closing parentheses"
                    | (S l') => 
                      match xs' with
                        | [] => match l' with
                                  | 0 => SomeE (rev (")"::acc), exist _ [] _)
                                  | _ => NoneE "too many open parentheses"
                                end
                        | _ => match match_with_level l' (")"::acc) xs' with
                                 | SomeE (res, exist xs'' H) => SomeE (res, exist _ xs'' _)
                                 | NoneE err => NoneE err
                               end
                      end
                  end
    | "013"::xs'   => match xs' with
                        | [] => match l with
                                  | 0 => SomeE (rev ("010"::acc), exist _ [] _)
                                  | _ => NoneE "too many open parentheses"
                                end
                        | "010"::xs''  =>
                          match xs'' with
                            | [] => match l with
                                      | 0 => SomeE (rev ("010"::acc), exist _ [] _)
                                      | _ => NoneE "too many open parentheses"
                                    end
                            | _  =>                        
                              match match_with_level l ("010"::acc) xs'' with
                                | SomeE (res, exist xs''' H) => SomeE (res, exist _ xs''' _)
                                | NoneE err => NoneE err
                              end
                          end
                        | _ =>  
                          match match_with_level l ("010"::acc) xs' with
                            | SomeE (res, exist xs'' H) => SomeE (res, exist _ xs'' _)
                            | NoneE err => NoneE err
                          end
                      end
    | "\"::xs'   => match parse_char_string_escape xs' with
                      | NoneE err => NoneE err
                      | SomeE (x, exist xs'' H) =>
                        match xs'' with
                          | [] => match l with
                                    | 0 => SomeE (rev (x::acc), exist _ [] _)
                                    | _ => NoneE "too many open parentheses"
                                  end
                          | _  => 
                            match match_with_level l (x::acc) xs'' with
                              | SomeE (res, exist xs''' H') => SomeE (res, exist _ xs''' _)
                              | NoneE err => NoneE err
                            end
                        end
                    end
    | x::xs'   => match xs' with
                    | [] => match l with
                              | 0 => SomeE (rev (x::acc), exist _ [] _)
                              | _ => NoneE "too many open parentheses"
                            end
                    | _  => 
                      match match_with_level l (x::acc) xs' with
                        | SomeE (res, exist xs'' H) => SomeE (res, exist _ xs'' _)
                        | NoneE err => NoneE err
                      end
                  end
  end.
Next Obligation.
  simpl. auto. 
Qed.
Next Obligation.
  simpl. clear Heq_anonymous. apply sublist__lt_length in H. auto.  
Qed.


Eval compute in match_with_level 0 [] (list_of_string "foo(bar)"%string).
Eval compute in match_with_level 0 [] (list_of_string "foo((bar)"%string).
Eval compute in match_with_level 0 [] (list_of_string "foo(bar))"%string).
Eval compute in match_with_level 0 [] (list_of_string "fo\to(bar)"%string).
Eval compute in match_with_level 0 [] (list_of_string "fo\ro(bar)"%string).
Eval compute in match_with_level 0 [] (list_of_string "foo(bar)\)"%string).
Eval compute in match_with_level 0 [] (list_of_string "foo\d(bar)"%string).
Eval compute in match_with_level 0 [] (CR::(list_of_string "foo(bar)"%string)).
Eval compute in match_with_level 0 [] (LF::(list_of_string "foo(bar)"%string)).
Eval compute in match_with_level 0 [] (CR::LF::(list_of_string "foo(bar)"%string)).
  

Program Definition parse_string : parser string :=
  fun xs =>
    DO (_, xs')       <== (match_exactly "(") xs ;;
    DO (result, xs'') <== match_with_level 0 []  (lift_base xs') ;;
    DO (_, xs''')     <== (match_exactly ")") (lift_base xs'') ;;
    SomeE (string_of_list result, exist _ (lift_base xs''') _).

Fixpoint skip_to_offset {T} (s : list T) (i : nat) :=
  match i with
    | 0 => SomeE s
    | (S n) => match s with
                 | []   => NoneE "Illegal offset"
                 | h::t => skip_to_offset t n
               end
  end.

Definition list_last_n {T} (xs : list T) (i : nat) :=
  (fix walker xs ys i :=
    match xs with
      | []     => ys
      | x::xs' => match i with
                    | 0      => walker xs' (tail ys) 0
                    | (S i') => walker xs' ys i'
                  end
    end) xs xs i.

Definition rev_string (s : string) :=
  string_of_list (rev (list_of_string s)).

Definition opt_ws {T:Set} (p : parser T) : parser (T) :=
  fun xs =>
    DO (val, xs') <== sequential_leftopt (many match_white) p xs ;; SomeE ((snd val), xs').

Definition find_xref_offset (xs : list ascii) :=
  let rxs := rev (list_last_n xs 100) in
    DO (_, rxs')    <== opt_ws (match_string (rev_string "%%EOF"%string)) rxs ;;
    DO (val, rxs'') <== opt_ws (many match_digit) (lift_base rxs') ;;
    DO (_, _)       <== opt_ws (match_string (rev_string "startxref"%string)) (lift_base rxs'') ;;
    DO (val',_)     <== parse_nat (rev val) ;;
    SomeE val'.

(*
Example find_xref_offset_ex1 :
  find_xref_offset (list_of_string "foobar  blabla  startxref  23  %%EOF  "%string)
    = SomeE(list_of_string "23"%string).
Proof.
  cbv. reflexivity.
Qed.
*)

Inductive Xref_entry : Set :=
  | InUse : nat -> nat -> Xref_entry
  | Free : nat -> nat -> Xref_entry.

Program Definition parse_xref_entry : parser Xref_entry :=
  fun xs =>
  DO (offset, xs')      <== opt_ws (some 10 match_digit) xs ;;
  DO (generation, xs'') <== opt_ws (some 5 match_digit) (lift_base xs') ;;
  DO (type, xs''')      <== opt_ws match_any (lift_base xs'') ;;
  DO (offset', _)       <== parse_nat offset ;;
  DO (generation', _)   <== parse_nat generation ;;
  match type with
    | "n" => SomeE (InUse offset' generation', exist _ (lift_base xs''') _)
    | "f" => SomeE (Free offset' generation', exist _ (lift_base xs''') _)
    | _   => NoneE "Invalid xref entry type"
  end.

Program Definition parse_xref_table_section : parser (nat*list Xref_entry) :=
  fun xs =>
  DO (startoffset, xs') <== opt_ws parse_nat xs ;;
  DO (entrynum, xs'')   <== opt_ws parse_nat (lift_base xs') ;;
  DO (entries, xs''')   <== some entrynum parse_xref_entry (lift_base xs'') ;;
  SomeE ((startoffset, entries), xs''').

Inductive Xref_table_entry : Set :=
  | table_entry : nat -> Xref_entry -> Xref_table_entry.

(*
Inductive Xref_table : Set :=
  | empty_table : Xref_table
  | next_entry : Xref_table_entry -> Xref_table -> Xref_table.
*)

Fixpoint build_xref_table_aux base entries table :=
  match entries with
    | []   => table
    | h::t => build_xref_table_aux (S base) t ((table_entry base h)::table)
  end.

Fixpoint build_xref_table sections table :=
  match sections with
    | []                    => table
    | (base, entries)::rest => build_xref_table rest (build_xref_table_aux base entries table)
  end.

Definition parse_xref_table (xs : list ascii) :=
  DO (_, xs')         <== opt_ws (match_string "xref"%string) xs ;;
  DO (sections, xs'') <== opt_ws (many parse_xref_table_section) (lift_base xs') ;;
  SomeE (build_xref_table sections []).

(* Eval compute in parse_xref_table (list_of_string "xref 23 2 0000000005 00002 f 0000000003 00001 n 42 1 0000000003 00001 n "%string). *)

Definition find_and_parse_xref_table (xs : list ascii) :=
  match find_xref_offset xs with
    | NoneE err => NoneE err
    | SomeE offset
      => match skip_to_offset xs offset with
           | NoneE err => NoneE err
           | SomeE xs' => parse_xref_table xs'
         end
  end.

Fixpoint remove_free_from_xref x : list Xref_table_entry :=
  match x with
    | [] => []
    | ((table_entry _ (InUse _ _)) as e)::x'
      => e::(remove_free_from_xref x')
    | (table_entry _ (Free _ _))::x'
      => remove_free_from_xref x'
  end.

Require Import Coq.Sorting.Sorting.
Require Import Orders.
Require Import Arith.

Open Scope bool_scope.

Local Coercion is_true : bool >-> Sortclass.

Module TableEntryOrder <: TotalLeBool.
  Definition t := Xref_table_entry.
  
  Definition leb x y :=
    match x, y with
    | (table_entry x' _),(table_entry y' _) 
      => x' <=? y'
    end.
  Check leb.
(*  Infix "<=?" := leb (at level 35). *)
  Theorem leb_total : forall a1 a2, leb a1 a2 \/ leb a2 a1.
    intros. destruct a1; destruct a2. unfold leb. 
    generalize dependent n0.
    induction n; destruct n0; simpl; auto.
  Qed.
End TableEntryOrder.

Module Import TableEntrySort := Sort TableEntryOrder.

Definition read_xref_table xs :=
  match find_and_parse_xref_table xs with 
    | NoneE e => NoneE ("Error parsing xref table: " ++ e)%string 
    | SomeE table => SomeE (sort (remove_free_from_xref table)) 
  end.

Require Import NPeano.

Check Nat.div_lt.

Definition digit_of_nat n := ascii_of_nat (n + C48).

Require Import Recdef.

Function string_of_nat_aux n acc {measure (fun x => x) n} :=
  match n with
    | 0 => acc
    | _ => string_of_nat_aux (n / C10) ((digit_of_nat (n mod C10))::acc)
  end.
Proof.
  intros. unfold C10. apply Nat.div_lt; auto with arith.
Defined.

Definition string_of_nat n := 
  match n with
    | 0 => "0"%string
    | _ => string_of_list (string_of_nat_aux n [])
  end.

Definition crlf := string_of_list ["010","013"].

Definition print_xref_entry e :=
  match e with
    | (InUse x y) => ((string_of_nat x) ++ " " ++ (string_of_nat y))%string
    | (Free _ _)  => "unused"%string
  end.

Definition print_xref_table_entry e :=
  match e with
    | (table_entry n e) => ((string_of_nat n) ++ " " ++ (print_xref_entry e))%string
  end.

Fixpoint print_xref_table l :=
  match l with
    | []    => ""%string
    | e::l' => ((print_xref_table_entry e) ++ crlf ++ (print_xref_table l'))%string
  end.

(*
Eval compute in parse_xref_entry (list_of_string "0000000005 00002 f "%string).

Definition find_xref_offset (xs : list ascii) :=
  let rxs := rev (list_last_n xs 100) in
    match opt_ws (match_string "FOE%%"%string) rxs with
      | NoneE err => NoneE ("Trailing %%EOF not found: "%string ++ err)
      | SomeE (_, exist rxs' _) 
        => match opt_ws (many match_digit) rxs' with
          | NoneE err => NoneE ("Invalid format for xref offset: "%string ++ err)
          | SomeE (val, exist rxs'' _) 
            => match opt_ws (match_string "ferxtrats"%string) rxs'' with
              | NoneE err    => NoneE ("startxref keyword not found: "%string ++ err)
              | SomeE (_, _) => SomeE (rev val)
               end
           end
    end.

*)

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

Definition main (xs : list ascii) :=
  match read_xref_table xs with
    | NoneE err   => NoneE ("Error: "%string ++ err)
    | SomeE table => SomeE (print_xref_table table)
  end.


Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlZInt.
Require Import ExtrOcamlString.

Extract Constant div => "(/)".
Extract Constant modulo => "(mod)".
Extract Constant nat_of_ascii => "Char.code".
Extract Constant ascii_of_nat => "Char.chr".

Extraction "parser.ml" main.