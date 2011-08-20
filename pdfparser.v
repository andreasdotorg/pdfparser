(** * Internals *)

Require Import SfLib.

Require Import String.
Require Import Ascii.
Require Import ZArith.
Require Import QArith.

Require Import Recdef.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.

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

Definition isOctal (c : ascii) : bool :=
  {["0"--"7"]} c.

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

Definition parse_number : parser string :=
  fun xs =>
    match sequential3 (sequential_leftopt match_sign match_integer) (match_exactly ".") match_integer xs with
      | NoneE err => NoneE "not a fractional number"
      | SomeE (NoneE _, integral, period, fractional, xs')
        => SomeE (string_of_list (integral++(period::fractional)), xs')
      | SomeE ((SomeE sign, integral, period, fractional), xs')
        => SomeE (string_of_list ((sign::integral)++(period::fractional)), xs')
    end.

Eval compute in parse_number (list_of_string "+30.5").


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
  try (simpl; auto);
  try (repeat (split; unfold not; intros; (try inversion H)));
  try (split; unfold not; intros; (try inversion H); split; unfold not; intros; inversion H; fail);
  try (split; unfold not; intro H'; inversion H'; fail);
  try (split; unfold not; intro; intro H'; inversion H'; fail);
  try (eauto; fail);
  fail.

Local Obligation Tactic := xref_solver.

(* \ has already been parsed away *)
Program Definition parse_char_string_escape_oct : parser ascii :=
  fun xs =>
    match xs with
      | d1::d2::d3::xs' => 
        if andb (andb (isOctal d1) (isOctal d2)) (isOctal d3) then 
          SomeE (ascii_of_nat(nat_of_digit(d1) * 64 + nat_of_digit(d2) * 8 + nat_of_digit(d3)), exist _ xs' _)
          else
            NoneE "Illegal escape character"
      | _  => NoneE "Illegal escape character"
    end.

Program Definition parse_char_string_escape : parser ascii :=
  fun xs =>
    match xs with
      | []              => NoneE "end of string reached during escape parsing"%string
      | "n"::xs'        => SomeE ("010", exist _ xs' _)
      | "r"::xs'        => SomeE ("013", exist _ xs' _)
      | "t"::xs'        => SomeE ("009", exist _ xs' _)
      | "b"::xs'        => SomeE ("008", exist _ xs' _)
      | "f"::xs'        => SomeE ("012", exist _ xs' _)
      | "("::xs'        => SomeE ("(", exist _ xs' _)
      | ")"::xs'        => SomeE (")", exist _ xs' _)
      | "\"::xs'        => SomeE ("\", exist _ xs' _)
      | xs0             => parse_char_string_escape_oct xs0
    end.

Local Obligation Tactic := program_simpl.

Local Notation "'fixExist' '(' t ')'" :=
  match t with
  | SomeE result =>
    match result with
    | (resultFix, exist xFix HFix) => SomeE (resultFix, exist _ xFix _)
    end
  | NoneE err => NoneE err
  end.

(* match balanced construct, using f to parse the inner content
   the opening 'from' char is expected to be already consumed
   enter and exit may transform the state *)
Program Fixpoint matchBalancedWithST {ST : Type}
    (from until : ascii)
    (f : ST -> forall xs0 : list ascii,
        optionE (ST * {xs' : list ascii | sublist xs' xs0}))
    (enter exit : (ST -> ST))
    (st : ST)
    (xs0 : list ascii)
    {measure (List.length xs0)}
    : optionE (ST * {xs' : list ascii | sublist xs' xs0})
    :=
  match xs0 with
  | nil     => NoneE "matchBalancedWith: unbalanced (got nil)"
  | (x::xs) =>
    match ascii_dec from x with
    | left  _ =>
      (* run next level *)
      match matchBalancedWithST from until f enter exit (enter st) xs with
      | SomeE ret =>
        (* insert closing *)
        match ret with
        | (st', exist xs' H) =>
          (* run rest *)
          match matchBalancedWithST from until f enter exit (exit st') xs' with
          | SomeE ret' =>
            match ret' with
            | (st'', exist xs'' H') => SomeE (st'', exist _ xs'' _)
            end
          | NoneE err  => NoneE err
          end
        end
      | NoneE err => NoneE err
      end
    | right _ =>
      match ascii_dec until x with
      | left  _ => SomeE (st, exist _ xs _)
      | right _ => (* sub-parser *)
        (* run sub-parser *)
        match f st (x::xs) with
        | SomeE ret =>
          match ret with
          | (st', exist xs' H) =>
            (* run rest *)
            match matchBalancedWithST from until f enter exit st' xs' with
            | SomeE ret' =>
              match ret' with
              | (st'', exist xs'' H) => SomeE (st'', exist _ xs'' _)
              end
            | NoneE err  => NoneE err
            end
          end
        | NoneE err => NoneE err
        end
      end
    end
  end.
Next Obligation.
  apply (sublist__lt_length (sublist_trans H (sl_tail x _))).
Defined.
Next Obligation.
  apply (sublist_trans H0 (sublist_trans H (sl_tail x _))).
Defined.
Next Obligation.
  apply (sublist__lt_length H).
Defined.
Next Obligation.
  apply (sublist_trans H0 H).
Defined.

Program Definition matchBalancedWith
    (from until : ascii)
    (f : list ascii -> forall xs0 : list ascii,
        optionE (list ascii * {xs' : list ascii | sublist xs' xs0}))
    (st : list ascii)
    (xs : list ascii)
    : optionE (list ascii * {xs' : list ascii | sublist xs' xs})
    :=
  matchBalancedWithST from until f
    (cons from) (cons until) st xs.

Local Obligation Tactic :=
  program_simpl;
  simpl;
    try (repeat split; intros;
        let C := fresh in intro C; inversion C; auto; fail);
  auto.

Program Definition parse_string_inner
    (acc xs : list ascii)
    : optionE (list ascii * {xs' : list ascii | sublist xs' xs})
    :=
  match xs with
  | nil      => NoneE "empty string while parsing string"
  (* newlines *)
  | "013"::"010"::xs' => SomeE ("010"::acc, exist _ xs' _)
  | "013"::xs'        => SomeE ("010"::acc, exist _ xs' _)
  (* escapes *)
  | "\"::"013"::"010"::xs' => SomeE (acc, exist _ xs' _)
  | "\"::"013"::xs'        => SomeE (acc, exist _ xs' _)
  | "\"::"010"::xs'        => SomeE (acc, exist _ xs' _)
  | "\"::xs' =>
    match parse_char_string_escape xs' with
    | SomeE ret =>
      match ret with
        (esc, exist xs'' H) => SomeE (esc::acc, exist _ xs'' _)
      end
    | NoneE err => NoneE err
    end
  (* default *)
  | x::xs' => SomeE (x::acc, exist _ xs' _)
  end.

Program Definition parse_string : parser string :=
  fun xs0 =>
    match xs0 with
    | ("("::xs) =>
      match matchBalancedWith "(" ")" parse_string_inner nil xs with
      | SomeE ret =>
        match ret with
        | (acc, exist xs' H) => SomeE (string_of_list (rev acc), exist _ xs' _)
        end
      | NoneE err => NoneE err
      end
    | _         => NoneE "parse_string: expected '('"
    end.

(* testing *)

Definition testStringParser (inp out rest : string) : optionE bool :=
  match parse_string (list_of_string inp) with
  | SomeE ret =>
    match ret with
    | (out', exist rest' _) =>
      match string_dec out out' with
      | left  _ =>
        match string_dec rest (string_of_list rest') with
        | left  _ => SomeE true
        | right _ => NoneE "rest differs"
        end
      | right _ => NoneE "output differs"
      end
    end
  | NoneE err =>
    match out with
    | ""%string => SomeE true
    | _  => NoneE err
    end
  end.

Definition cr  (s : string) : string := String "013" s.
Definition lf  (s : string) : string := String "010" s.
Definition tab (s : string) : string := String "009" s.

Eval compute in testStringParser "(foo(bar))" "foo(bar)" "".
Eval compute in testStringParser "(foo((bar))" "" "". (* unclosed *)
Eval compute in testStringParser "(foo(bar)))" "foo(bar)" ")".
Eval compute in testStringParser "(fo\to(bar))" ("fo" ++ tab "o(bar)") "".
Eval compute in testStringParser "(fo\ro(bar))" ("fo" ++ cr "o(bar)") "".
Eval compute in testStringParser "(foo(bar)\()" "foo(bar)(" "".
Eval compute in testStringParser "(foo\d(bar))" "" "". (* bad esc *)
Eval compute in testStringParser "(foo\011(bar))" ("foo" ++ tab "(bar)") "".
Eval compute in testStringParser ("("%string ++ cr "foo(bar))") (lf "foo(bar)") "". 
Eval compute in testStringParser ("(" ++ lf "foo(bar))") (lf "foo(bar)") "".
Eval compute in testStringParser ("(" ++ cr (lf "foo(bar))")) (lf "foo(bar)") "". (* XXX intended? XXX *)
Eval compute in testStringParser ("(\" ++ cr "foo(bar))") "foo(bar)" "".
Eval compute in testStringParser ("(\" ++ lf "foo(bar))") "foo(bar)" "".
Eval compute in testStringParser ("(\" ++ cr (lf "foo(bar))")) "foo(bar)" "".



Program Definition parse_name_char : parser ascii :=
  fun xs =>
    match xs with
      | "#"::c1::c2::xs' => 
        if andb (isHexDigit c1) (isHexDigit c2) then
          SomeE (ascii_of_Z (Z_of_hex_digit(c1) * 16 + Z_of_hex_digit(c2)),
                        exist _ xs' _)
        else
          NoneE "Illegal # encoding in name"
      | "000"::xs' => NoneE "Illegal null char in name"
      | c::xs' =>
        if isRegularCharacter c
          then SomeE (c, exist _ xs' _)
          else NoneE "not a name character"
      | [] => NoneE "End of string while parsing name char"
    end.

Program Definition parse_name : parser string :=
  fun xs =>
    DO (_, xs')       <== (match_exactly "/") xs ;;
    DO (result, xs'') <== (many parse_name_char) xs' ;;
    SomeE (string_of_list result, exist _ (proj1_sig xs'') _).
Next Obligation.
  apply (sublist_trans H H0).
Defined.

Definition parse_null : parser PDF.PDFObject :=
  fun xs =>
    match match_string "null" xs with
      | SomeE (_, xs') => SomeE (PDF.PDFNull, xs')
      | NoneE err => NoneE err
    end.

Definition opt_ws {T:Set} (p : parser T) : parser (T) :=
  fun xs =>
    DO (val, xs') <== sequential_leftopt (many match_white) p xs ;; SomeE ((snd val), xs').

Program Definition parse_indirect_ref : parser PDF.PDFObject :=
  fun xs =>
    DO (number, xs') <== parse_nat xs ;;
    DO (gen, xs'')   <== opt_ws parse_nat xs' ;;
    DO (_, xs''')    <== opt_ws (match_exactly "R") xs'' ;;
    SomeE (PDF.PDFReference number gen, xs''').
Next Obligation.
  apply (sublist_trans H (sublist_trans H0 H1)).  
Defined.

Local Obligation Tactic :=
  program_simpl;
  simpl; intros;
    try (repeat split; intros; intro C; inversion C; fail).

Program Definition parse_simple_object : parser PDF.PDFObject :=
  fun xs =>
    DO (x, xs')    <-- parse_boolean xs ;; SomeE (x, xs')
    OR DO (x, xs') <-- parse_null xs ;; SomeE (x, xs')
    OR DO (x, xs') <-- parse_name xs ;; SomeE (PDF.PDFName x, xs')
    OR DO (x, xs') <-- parse_hex_string xs ;; SomeE (PDF.PDFString x, xs')
    OR DO (x, xs') <-- parse_string xs ;; SomeE (PDF.PDFString x, xs')
    OR DO (x, xs') <-- parse_indirect_ref xs ;; SomeE (x, xs')
    OR DO (x, xs') <-- parse_number xs ;; SomeE (PDF.PDFNumber (PDF.Float x), xs')
    OR DO (x, xs') <-- parse_integer xs ;; SomeE (PDF.PDFNumber (PDF.Integer x), xs')
    OR NoneE "internal: not a simple PDFObject".

Program Definition dictionary_of_list
    (l : list (string * PDF.PDFObject))
    : optionE PDF.PDFObject
    :=
  match PDF.list2dict l PDF.DictEmpty with
  | Some d => SomeE (PDF.PDFDictionary d)
  | None   => NoneE "bad dictionary (duplicate or non-name key)"
  end.

(* still broken, FIXME *)
Program Definition parse_stream_contents dict : parser string :=
  fun xs =>
    match PDF.dictFindEntry dict "Length" with
      | None => NoneE "error parsing stream: no length in stream dict"
      | Some (PDF.PDFNumber (PDF.Integer length)) =>
        DO (_, xs1)  <== match_string "stream" xs ;;
        DO (_, xs2) <== alternative 
                          (match_string (lf "")) 
                          (match_string (cr (lf "")))
                          xs1 ;;
        DO (data, xs3) <== some (Zabs_nat length) match_any xs2 ;;
        DO (_, xs4) <== sequential_leftopt
                          (alternative 
                            (match_string (lf "")) 
                            (match_string (cr (lf ""))))
                          (match_string "endstream")
                          xs3 ;;
        SomeE (string_of_list data, xs4)
      | _ => NoneE "I don't understand the length spec!"
    end.
Next Obligation.
  eauto.
Defined.  

Definition parse_stream_contents_aux obj : parser string :=
  fun xs =>
    match obj with
      | PDF.PDFDictionary dic => parse_stream_contents dic xs
      | _ => NoneE "no stream dictionary found"
    end.



(*
Eval compute in parse_stream_contents 
  (PDF.NextEntry "length"%string (PDF.PDFNumber (PDF.Integer 1)) PDF.DictEmpty)
  ("stream"++lf++"1"++lf++"endstream")%string.
*)

(* When defining a Program Fixpoint, the current function cannot be
    passed as a callback.  Doing this results in a more or less empty
    context from which the sublist proof cannot be done.

    Thus, we inline array and dictionary parsing.

    Many must be re-implemented locally as well... TODO
*)

Program Fixpoint parse_pdf_object
    (xs : list ascii)
    {measure (List.length xs)}
    : optionE (PDF.PDFObject * {xs' : list ascii | sublist xs' xs})
    :=
    DO (x, xs')    <-- parse_simple_object xs ;; SomeE (x, xs')
    OR
      match xs with
      | "["::xs'      => (* array code *)
        match many (fun l => parse_pdf_object l) xs' with
        | SomeE ret =>
          match ret with
          | (arr, exist xs'' H) =>
            match opt_ws (match_exactly "]") xs'' with
            | SomeE (_, exist xs''' H') => SomeE (PDF.PDFArray arr, exist _ xs''' _)
            | NoneE err => NoneE err
            end
          end
        | NoneE err =>
          match opt_ws (match_exactly "]") xs' with
          | SomeE ret =>
            match ret with
            | (_, exist xs'' H) => SomeE (PDF.PDFArray nil, exist _ xs'' _)
            end
          | NoneE err => NoneE err
          end
        end
      | "<"::"<"::xs' =>
        match many (opt_ws (
            fun xs0 =>
            match parse_name xs0 with
            | SomeE (name, exist xs0' H) =>
              match parse_pdf_object xs0' with
              | SomeE (val, exist xs0'' H') => SomeE ((name, val), exist _ xs0'' _)
              | NoneE err => NoneE err
              end
            | NoneE err => NoneE err
            end
            (* name; object ... *)
            )) xs'
        with
        | SomeE (dic, exist xs'' H) =>
          match opt_ws (match_list [">",">"]) xs'' with
          | SomeE (_, exist xs''' H') =>
            match dictionary_of_list (rev dic) with
            | SomeE dic' => (* insert stream parser here? no... *) SomeE (dic', exist _ xs''' _)
            | NoneE err => NoneE err
            end
          | NoneE err => NoneE err
          end
        | NoneE err =>
          match opt_ws (match_list [">",">"]) xs' with
          | SomeE (_, exist xs'' H) => SomeE (PDF.PDFDictionary PDF.DictEmpty, exist _ xs'' _)
          | NoneE err => NoneE err
          end
        end
      | x::xs'        =>
        if isWhite x (* skip whitespace *)
          then fixExist(parse_pdf_object xs')
          else NoneE "PDFObject: no parse"
      | _   => NoneE "PDFObject: no parse (got nil)"
      end.
Next Obligation.
  admit.
Defined.
Next Obligation.
  apply (sublist_trans H' (sublist_trans H (sl_tail "[" _))).
Defined.
Next Obligation.
  admit.
Defined.
Next Obligation.
  admit.
Defined.
Next Obligation.
  apply (sublist_trans H' (sublist_trans H (sublist_trans (sl_tail "<" _) (sl_tail "<" _)))).
Defined.

(* tests *)

Definition runTest {A} (p : parser A) (inp : string) : (optionE A) :=
  match p (list_of_string inp) with
  | SomeE (a,e) => SomeE a
  | NoneE err   => NoneE err
  end.

Eval compute in runTest parse_pdf_object "true".
Eval compute in runTest parse_pdf_object "false".
Eval compute in runTest parse_pdf_object "null".
Eval compute in runTest parse_pdf_object "/foo".
Eval compute in runTest parse_pdf_object "23".
Eval compute in runTest parse_pdf_object "<454647>".
Eval compute in runTest parse_pdf_object "(abc)".

Eval compute in runTest parse_pdf_object "[(bar) 23 (baz) <414243>]".
Eval compute in runTest parse_pdf_object "[]".
Eval compute in runTest parse_pdf_object "[ /foo ]".

Eval compute in runTest parse_pdf_object "<< /foo (bar) /baz << >> /quux [ 5 ] >>".
Eval compute in runTest parse_pdf_object "<< /foo (bar) /foo << >> >>".
Eval compute in runTest parse_pdf_object "<< /foo 23 5 R >>".

Definition parse_fail {T : Set} : parser T :=
  fun xs =>
    NoneE "always fail".

Program Definition parse_indirect_object : parser PDF.PDFObject :=
  fun xs =>
    DO (number, xs1) <== parse_nat xs ;;
    DO (gen, xs2)    <== opt_ws parse_nat xs1 ;;
    DO (_, xs3)      <== opt_ws (match_string "obj") xs2 ;;
    DO (obj, xs4)    <== opt_ws parse_pdf_object xs3 ;;
    DO (_, xs5)      <-- opt_ws (match_string "endobj") xs4 ;; SomeE (PDF.PDFIndirect number gen obj, xs5)
    OR DO (stream, xs5) <== opt_ws (parse_stream_contents_aux obj) xs4 ;;
      DO (_, xs6)       <== opt_ws (match_string "endobj") xs5 ;; 
      SomeE (PDF.PDFIndirect number gen obj, xs6).
Next Obligation.
  eauto.
Defined.
Next Obligation.
  eauto 6.
Defined.

Eval compute in runTest parse_indirect_object "1 0 obj
 <<  /Type /Catalog
      /Outlines 2 0 R
      /Pages 3 0 R
  >>
endobj
".

Fixpoint skip_to_offset {T} (s : list T) (i : nat) :=
  match i with
    | 0 => SomeE s
    | (S n) => match s with
                 | []   => NoneE "Illegal offset"
                 | h::t => skip_to_offset t n
               end
  end.

Definition parse_object_at xs offset :=
  match skip_to_offset xs offset with
    | NoneE err => NoneE err
    | SomeE xs' => 
      match parse_indirect_object xs' with
        | NoneE err         => NoneE err
        | SomeE (PDF.PDFIndirect id gen obj, xs'') => SomeE obj
        | _ => NoneE "not an indirect object specification"
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

Definition find_xref_offset (xs : list ascii) :=
  let rxs := rev (list_last_n xs 100) in
    DO (_, rxs')    <== opt_ws (match_string (rev_string "%%EOF"%string)) rxs ;;
    DO (val, rxs'') <== opt_ws (many match_digit) (proj1_sig rxs') ;;
    DO (_, _)       <== opt_ws (match_string (rev_string "startxref"%string)) (proj1_sig rxs'') ;;
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

Ltac xref_solver' :=
  try program_simpl;
  try (split; unfold not; intros; (try inversion H); split; unfold not; intros; inversion H; fail);
  try (split; unfold not; intro H'; inversion H'; fail);
  try (split; unfold not; intro; intro H'; inversion H'; fail);
  try (eauto; fail).

Local Obligation Tactic := xref_solver'.



Program Definition parse_xref_entry : parser Xref_entry :=
  fun xs =>
  DO (offset, xs')      <== opt_ws (some 10 match_digit) xs ;;
  DO (generation, xs'') <== opt_ws (some 5 match_digit) (proj1_sig xs') ;;
  DO (type, xs''')      <== opt_ws match_any (proj1_sig xs'') ;;
  DO (offset', _)       <== parse_nat offset ;;
  DO (generation', _)   <== parse_nat generation ;;
  match type with
    | "n" => SomeE (InUse offset' generation', exist _ (proj1_sig xs''') _)
    | "f" => SomeE (Free offset' generation', exist _ (proj1_sig xs''') _)
    | _   => NoneE "Invalid xref entry type"
  end.

Program Definition parse_xref_table_section : parser (nat*list Xref_entry) :=
  fun xs =>
  DO (startoffset, xs') <== opt_ws parse_nat xs ;;
  DO (entrynum, xs'')   <== opt_ws parse_nat (proj1_sig xs') ;;
  DO (entries, xs''')   <== some entrynum parse_xref_entry (proj1_sig xs'') ;;
  SomeE ((startoffset, entries), xs''').

Inductive Xref_table_entry : Set :=
  | table_entry : nat -> Xref_entry -> Xref_table_entry.

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
  DO (_, xs1)        <== opt_ws (match_string "xref"%string) xs ;;
  DO (sections, xs2) <== opt_ws (many parse_xref_table_section) (proj1_sig xs1) ;;
  DO (_, xs3)        <== opt_ws (match_string "trailer"%string) (proj1_sig xs2) ;;
  DO (trailer , xs4) <== opt_ws parse_pdf_object (proj1_sig xs3) ;;
  SomeE (build_xref_table sections [], trailer).

(* Eval compute in parse_xref_table (list_of_string "xref 23 2 0000000005 00002 f 0000000003 00001 n 42 1 0000000003 00001 n "%string). *)

Local Obligation Tactic :=
  program_simpl;
  simpl; intros;
    try (repeat split; intros; intro C; inversion C; fail).

Require Import unilist.

Program Fixpoint parse_xref_table_at 
  (xs : list ascii)
  (offset : nat)
  (checked_offsets : list nat) 
  {measure ((List.length xs) - (List.length checked_offsets))}
  :=

  match @lucons (List.length xs) offset checked_offsets with
    | None => NoneE "Error: xref table loop or illegal offset"
    | Some checked_offsets' =>
      match skip_to_offset xs offset with
        | NoneE err => NoneE err
        | SomeE xs' => 
          match parse_xref_table xs' with
            | NoneE err => NoneE err
            | SomeE (table, (PDF.PDFDictionary trailer)) =>
              match PDF.dictFindEntry trailer "Prev" with
                | None => SomeE (table, trailer)
                | Some (PDF.PDFNumber (PDF.Integer offset')) =>
                   (* really need to concatenate tables here *)
                  parse_xref_table_at xs (Zabs_nat offset') checked_offsets' 
                | _ => NoneE "Invalid Prev reference in trailer"
              end
            | SomeE (table, _) => NoneE "trailer is not a dictionary"
          end
      end
  end.
Next Obligation.
  admit.
Defined.


Program Definition find_and_parse_xref_table (xs : list ascii) :=
  match find_xref_offset xs with
    | NoneE err => NoneE err
    | SomeE offset => parse_xref_table_at xs offset (exist (fun _ => True) [] _)
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
    | SomeE (table, trailer) => SomeE (sort (remove_free_from_xref table)) 
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

Fixpoint get_object id gen table xs :=
  match table with
    | []        => NoneE "object not in table"
    | e::table' => match e with
                     | (table_entry id' e) =>
                       match e with
                         | (InUse offset gen') =>
                           if andb (beq_nat id id') (beq_nat gen gen') then
                             parse_object_at xs offset
                             else get_object id gen table' xs
                         | (Free _ _ ) => get_object id gen table' xs
                       end
                   end
  end.

Definition entry_get_id table_entry :=
  match table_entry with
    | (table_entry id e) => id
  end.

(* assuming InUse entry always, FIXME *)
Definition entry_get_offset table_entry :=
  match table_entry with
    | (table_entry id e) =>
      match e with
        | (InUse offset gen) => offset
        | (Free offset gen)  => offset
      end
  end.

Definition entry_get_gen table_entry :=
  match table_entry with
    | (table_entry id e) =>
      match e with
        | (InUse offset gen) => gen
        | (Free offset gen)  => gen
      end
  end.

Definition get_obj_from_table_entry xs table_entry :=
  parse_object_at xs (entry_get_offset table_entry).

Definition is_evil obj :=
  match obj with
    | (PDF.PDFDictionary dict) =>
      match PDF.dictFindRec dict "JavaScript" with
        | nil => 
          match PDF.dictFindRec dict "S" with
            | nil  => false
            | l =>
              list_rec _ (fun _ => bool) false
              (fun x c rec =>
                match x with
                | PDF.PDFName "JavaScript" => true
                | PDF.PDFName "Rendition"  => true
                | _ => rec
                end) l
            end
        | cons _ _ => true
      end
    | _ => false
  end.

Eval compute in let obj := (runTest parse_pdf_object "1 0 obj << /S /JavaScript >> endobj") in
  match obj with
    | NoneE err => false
    | SomeE obj => is_evil obj
  end.



Definition check_obj_from_entry xs table_entry :=
  let obj := get_obj_from_table_entry xs table_entry in
    match obj with
      | NoneE err => ("bad (parse error): " ++ err ++ (lf ""))%string
      | SomeE obj => if is_evil obj then
          ("evil" ++ (lf ""))%string
        else
          ("good" ++ (lf ""))%string
    end.

Fixpoint check_table xs table :=
  match table with
    | []        => ""%string
    | e::table' => ((check_obj_from_entry xs e) ++ (check_table xs table'))%string
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
    | SomeE table => SomeE (check_table xs table)
  end.


Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlZInt.
Require Import ExtrOcamlString.

Extract Constant div => "(/)".
Extract Constant modulo => "(mod)".
Extract Constant nat_of_ascii => "Char.code".
Extract Constant ascii_of_nat => "Char.chr".

Extraction "parser.ml" main.
