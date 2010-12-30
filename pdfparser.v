(** * ImpParser: Lexing and Parsing in Coq *)
(* Version of 6/19/2010 *)

(** * Internals *)

Require Import SfLib.

Require Import String.
Require Import Ascii.
Require Import ZArith.
Require Import QArith.

Require Import Recdef.

Open Scope list_scope.



(* ####################################################### *)
(** ** Helpers *)

Check tail.

Theorem list_loop : forall {A : Set} {x : A} {l : list A}, (x::l) <> l.
  intros; generalize dependent x.
  induction l; intros x C.
    inversion C.
    set (f:= @tail A); pose proof (f_equal f C) as H; simpl in H.
    apply (IHl _ H).
Qed.





(* ####################################################### *)
(** ** Lexical Analysis *)

Open Scope nat_scope.
Open Scope char_scope.



(* comparisons *)

Definition eq_ascii (c d : ascii) : bool :=
  if ascii_dec c d then true else false.

Notation "x '<=?' y" := (ble_nat x y)
  (at level 70, no associativity) : nat_scope.



(* character class helpers *)

Definition never : ascii -> bool :=
  fun _ => false.



Definition check_aux (to : ascii) (continuation : ascii -> bool) : ascii -> bool :=
  fun c =>
    (orb (eq_ascii c to) (continuation c)).

Eval compute in (check_aux "a" (check_aux "b" (check_aux "c" never))) "c".



Notation "{{ a , .. , b }}" := (check_aux a .. (check_aux b never)  .. ) (at level 0). 

Notation "a 'isin' f" := (f a) (at level 1, only parsing).

Eval compute in {{ "a", "b", "c"}} "b".



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

(* ####################################################### *)
(** ** PDF base type *)

Module PDF.

Parameter Zpos0 : Set.


Inductive Numeric : Set :=
  | Integer : Z -> Numeric
  | Float : Q -> Numeric.

Inductive PDFObject : Set :=
  | PDFBoolean : bool -> PDFObject
  | PDFNumber : Numeric -> PDFObject
  | PDFString : string -> PDFObject
  | PDFName : string -> PDFObject
  | PDFArray : list PDFObject -> PDFObject
  | PDFDictionary : (string -> PDFObject) -> PDFObject
  | PDFStream : string -> PDFObject
  | PDFNull : PDFObject
  | PDFIndirect : positive -> Zpos0 -> PDFObject -> PDFObject
  | PDFReference : positive -> Zpos0 -> PDFObject.

End PDF.





(* ####################################################### *)
(** ** option type *)

(* An option with error messages. *)
Inductive optionE (X:Type) : Type :=
  | SomeE : X -> optionE X
  | NoneE : string -> optionE X.

Implicit Arguments SomeE [[X]].
Implicit Arguments NoneE [[X]].





(* ####################################################### *)
(** ** string <--> list *)

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: (list_of_string s)
  end.

Definition string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.





(* ####################################################### *)
(** ** length measure for lists *)

Section length_measure.

  Definition lt_length {A : Set} (l1 l2 : list A) :=
    List.length l1 < List.length l2.

  Theorem lt_length_wf {A : Set} : well_founded (@lt_length A).
  Proof. intro. apply well_founded_ltof.  Qed.

  Set Implicit Arguments.
  Section lt_length_order.

    Variable A : Set.

    Variables c d : A.
    Variables l l' l'' : list A.

    Theorem lt_length_irrefl : ~ lt_length l l.
    Proof.  apply lt_irrefl.  Qed.

    Theorem lt_length_asym : lt_length l l' -> ~ lt_length l' l.
    Proof.  apply lt_asym.  Qed.

    Theorem lt_length_trans : lt_length l l' -> lt_length l' l'' -> lt_length l l''.
    Proof.  apply lt_trans.  Qed.

    Theorem lt_length_not_nil : lt_length l l' -> l' <> nil.
    Proof.  induction l'; [ inversion 1 | intros _ C; inversion C].  Qed.

    Theorem lt_length_tail : lt_length l (c::l).
    Proof.  cbv; intros; apply le_n.  Qed.

    Theorem lt_length_tails : lt_length (c::l) (d::l') -> lt_length l l'.
    Proof.  cbv; auto with arith.  Qed.

    Theorem lt_length_cons : lt_length l l' -> lt_length l (c::l').
    Proof.  cbv; auto with arith.  Qed.

    Theorem lt_length_cons_cons : lt_length l l' -> lt_length (c::l) (d::l').
    Proof.  cbv; auto with arith.  Qed.

    Hint Unfold lt_length.
    Hint Resolve lt_length_trans lt_length_tail lt_length_tails lt_length_cons
                    lt_length_cons_cons : pdfparser.

  End lt_length_order.
  Unset Implicit Arguments.

End length_measure.





(* ####################################################### *)
(** ** truer sublist *)

Section true_sublist.
  Set Implicit Arguments.

  Variable (A : Set).

  Inductive sublist : list A -> list A -> Prop :=
  | sl_tail : forall (c : A) l, sublist l (c::l)
  | sl_cons : forall (c : A) l' l, sublist l' l -> sublist l' (c::l).

  Hint Constructors sublist.

  Section sublist_order.

    Theorem sublist__lt_length : forall l l', sublist l' l -> lt_length l' l.
    Proof.
      intros l l' H. induction H.
        apply lt_length_tail.
        apply lt_length_cons; assumption.
    Qed.

    Lemma sublist_longer : forall l l', List.length l' > List.length l -> ~ sublist l' l.
    Proof.
      intros l l' H C.
      apply sublist__lt_length in C.
      unfold lt_length in *; omega.
    Qed.

    Theorem sublist_not_nil : forall l l', sublist l l' -> l' <> nil.
    Proof.  induction l'; [ inversion 1 | intros _ C; inversion C].  Qed.

    Theorem sublist_nil : forall c l, sublist [] (c::l).
    Proof.
      intros c l; generalize dependent c.
      induction l; intros.
        constructor.
        constructor; apply IHl.
    Qed.

    Theorem sublist_tails : forall c d l l', sublist (c::l) (d::l') -> sublist l l'.
    Proof.
      intros c d l l'; generalize dependent l;
      generalize dependent d; generalize dependent c.
      induction l'; intros.
        inversion H; inversion H2.
        inversion H; subst.
          constructor.
          constructor; apply (IHl' _ _ _ H2).
    Qed.

    Theorem sublist_irrefl : forall l, ~ sublist l l.
    Proof.
      induction l; intro C; inversion C.
        apply (list_loop H2).
        subst. apply sublist__lt_length in H1.
        cbv in H1; omega.
    Qed.

    Theorem sublist_asym : forall l l', sublist l l' -> ~ sublist l' l.
    Proof.
      intros l l' H; induction H.
        intro C. apply sublist__lt_length in C. cbv in C; omega.

        intro C. apply sublist__lt_length in C. apply sublist__lt_length in H.
        cbv in H; cbv in C; omega.
    Qed.

    Theorem sublist_trans : forall l l' l'',
      sublist l l' -> sublist l' l'' -> sublist l l''.
    Proof.
      intros l l' l'' H0 H; generalize dependent l.
      induction H; intros.
        constructor; assumption.
        constructor; apply (IHsublist _ H0).
    Qed.

    Theorem sublist_sublisteq_trans : forall l l' l'',
      sublist l l' -> (sublist l' l'' \/ l' = l'') -> sublist l l''.
    Proof.
      intros l l' l''; generalize dependent l'; generalize dependent l.
      induction l''; intros.
        inversion H0.
          inversion H1.
          subst; inversion H.
        inversion H0.
          apply sublist_trans with l'; assumption.
          subst; assumption.
    Qed.

    Lemma sublist_Acc_nil : Acc sublist [].
    Proof.  constructor. intros l H; inversion H.  Qed.

    Lemma list_emptyset_nil : ~ inhabited A -> forall l : list A, l = [].
    Proof.
      intros C l.
      induction l.
        reflexivity.
        elimtype False. apply C. constructor. assumption.
    Qed.

    Theorem sublist_wf_empty : ~ inhabited A -> well_founded sublist.
    Proof.
      intro CI. pose proof (list_emptyset_nil CI).
      unfold well_founded.
      intro a; rewrite (H a).
      constructor. intros b C; inversion C.
    Qed.

    Theorem sublist_wf_inhabited : inhabited A -> well_founded sublist.
    Proof.
      intro HI. inversion HI as [x].
      unfold well_founded.
      cut (forall l' l, sublist l' l -> Acc sublist l').
        intros H l.
        refine (H l (x::l) _). apply sl_tail.

        intros l' l; generalize dependent l'.
        induction l; intros.
          inversion H.

          constructor; intros l'' H0.
          apply IHl. clear - H H0.
          inversion H; subst.
            assumption.
            apply sublist_trans with l'; assumption.
    Qed.

    Hint Resolve sublist__lt_length sublist_tails sublist_trans : sublist pdfparser.

  End sublist_order.

  (* additional pseudo-constructor *)
  Theorem sl_minus : forall (c : A) {l' l}, sublist (c::l') l -> sublist l' l.
  Proof.
    intros; destruct l.
      inversion H.
      apply sublist_tails in H. constructor; assumption.
  Qed.

  Hint Resolve sl_minus : core.

  Unset Implicit Arguments.
End true_sublist.





(* ####################################################### *)
(** ** parser *)

Definition parser (T : Type) :=
  forall l : list ascii,
    optionE (T * {l' : list ascii | sublist l' l}).


Lemma parser_nil_none : forall t (p : parser t), exists err, p [] = NoneE err.
Proof.
  intros.
  remember (p []) as H.
  destruct H.
    inversion p0. inversion H. inversion H0.
    exists s. reflexivity.
Qed.

Hint Resolve parser_nil_none : pdfparser.

Definition parse_one_character {T : Set} (f : ascii*(list ascii) -> optionE T) : parser T :=
  fun xs => match xs with
    | [] => NoneE "End of token stream"
    | (c::t) => match f (c,t) with
                | NoneE err => NoneE err
                | SomeE result => SomeE (result, exist _ t (sl_tail c t))
                end
    end.



Definition match_any : parser ascii := parse_one_character (fun t => SomeE (fst t)).

Theorem match_any_works :
  forall c : ascii,
    forall l : list ascii,
      match_any (c::l) = SomeE (c, exist _ l (sl_tail c l)).
Proof.
  intros. unfold match_any. unfold parse_one_character. simpl. reflexivity.
Qed.



Function many_helper (T:Set) (p : parser T) (acc : list T) (xs : list ascii)
    {measure List.length xs } :
        optionE (list T * {l'' : list ascii | sublist l'' xs}) :=
match p xs with
| NoneE err        => NoneE err
| SomeE (t, exist xs' H) => 
  match many_helper _ p (t::acc) xs' with
    | NoneE _ => SomeE (rev (t::acc), exist _ xs' H)
    | SomeE (acc', exist xs'' H') 
      => SomeE (acc', exist _ xs'' (sublist_trans H' H))
  end
end.
Proof.
  intros; clear - H.
  apply sublist__lt_length in H; unfold lt_length in H.
  assumption.
Defined.

Hint Rewrite many_helper_equation : pdfparser.

Definition many {T:Set} (p : parser T) : parser (list T) :=
  fun xs => many_helper T p [] xs.



Theorem many_helper_works :
  forall l acc : list ascii,
  (l =  [] -> exists e, many_helper _ match_any acc l = NoneE e) /\
  (l <> [] -> exists e, many_helper _ match_any acc l = SomeE ((rev acc)++l,e)).
Proof.
  intro l; induction l; intros;
  split; intro C; try (inversion C || elim C; reflexivity || fail); clear C.
    cbv; eexists; reflexivity.
    pose proof (IHl acc) as IH.
    inversion IH; clear IH. destruct l.
      (* case 1: last character *)
      clear - a. rewrite many_helper_equation. simpl.
      eexists; reflexivity.
      (* case 2: more characters *)
      clear H; assert (a0 :: l <> []) as H by (intro C; inversion C); pose proof H as H';
      apply H0 in H; clear H0.
      inversion H. inversion x as [l'].
      subst; rewrite many_helper_equation. simpl.
      pose proof (IHl (a::acc)). inversion H2; clear H2; clear H3.
      apply H4 in H'; clear H4.
      inversion H'. rewrite H2.
      destruct x0.
      simpl. rewrite app_ass. simpl.
      eexists; reflexivity.
Qed.

Theorem many_works :
  forall l : list ascii,
  (l =  [] -> exists e, many match_any l = NoneE e) /\
  (l <> [] -> exists e, many match_any l = SomeE (l,e)).
Proof.  unfold many; intros. apply many_helper_works.  Qed.



Definition match_one_char_with_predicate (p : ascii -> bool) : parser ascii :=
  parse_one_character (fun t => if p (fst t) then SomeE (fst t) else NoneE "predicate false").

Definition match_digit := match_one_char_with_predicate isDigit.

Definition match_integer := many match_digit.

Definition exist_left_projection {A : Set} {B : A -> Prop} (e : sig B) := 
  match e with | exist a b => a end.

Definition Z_of_ascii (d : ascii) := Z_of_nat (nat_of_ascii d).

Definition Z_of_digit (d : ascii) := ((Z_of_ascii d) - 48)%Z. 

Definition match_sign := 
  match_one_char_with_predicate (fun x => x isin {{"-", "+"}})%char.

Definition match_exactly (c : ascii) :=
  match_one_char_with_predicate (fun x => eq_ascii x c).

Definition sequential 
  {A B : Set} (a : parser A) (b : parser B) : parser (A*B) :=
  fun xs =>
    match a xs with
      | SomeE (val_a, exist xs' H) =>
        match b xs' with
          | SomeE (val_b, exist xs'' H') => SomeE ((val_a, val_b), 
                                                   exist _ xs'' (sublist_trans H' H))
          | NoneE err => NoneE err
        end
      | NoneE err => NoneE err
    end.
    
Definition sequential3 
  {A B C : Set} (a : parser A) (b : parser B) (c : parser C) : parser (A*B*C) :=
  fun xs =>
    match sequential a b xs with
      | SomeE (val_a, exist xs' H) =>
        match c xs' with
          | SomeE (val_b, exist xs'' H') => SomeE ((val_a, val_b), 
                                                   exist _ xs'' (sublist_trans H' H))
          | NoneE err => NoneE err
        end
      | NoneE err => NoneE err
    end.

Definition sequential_leftopt
  {A B : Set} (a : parser A) (b : parser B) : parser (optionE(A)*B) :=
  fun xs =>
    match a xs with
      | SomeE (val_a, exist xs' H) =>
        match b xs' with
          | SomeE (val_b, exist xs'' H') => SomeE ((SomeE val_a, val_b), 
                                                   exist _ xs'' (sublist_trans H' H))
          | NoneE err => NoneE err
        end
      | NoneE err =>
        match b xs with 
          | SomeE (val_b, xs') => SomeE ((NoneE err, val_b), xs')
          | NoneE err => NoneE err
        end
    end.

Definition sequential_rightopt
  {A B : Set} (a : parser A) (b : parser B) : parser (A*optionE(B)) :=
  fun xs =>
    match a xs with
      | SomeE (val_a, exist xs' H) =>
        match b xs' with
          | SomeE (val_b, exist xs'' H') => SomeE ((val_a, SomeE val_b), 
                                                   exist _ xs'' (sublist_trans H' H))
          | NoneE err => SomeE ((val_a, NoneE err), exist _ xs' H)
        end
      | NoneE err => NoneE err
    end.

Definition alternative 
  {A : Set} (a b : parser A) : parser (A) :=
  fun xs =>
    match a xs with
      | SomeE (val_a, xs') => 
        match b xs with
          | SomeE (val_b, xs'') => 
            if List.length (exist_left_projection xs') <=?
              List.length (exist_left_projection xs'')
            then
              SomeE (val_a, xs')
            else
              SomeE (val_b, xs'')
          | NoneE err => SomeE (val_a, xs')
        end
      | NoneE err => b xs
    end.

Definition collapse_product
  {l : Type}
  (e : optionE((ascii*string) * l)) :
    optionE(string * l) :=
      match e with
        | SomeE ((c,s), H) => SomeE ((String c s), H)
        | NoneE err => NoneE err
      end.

Definition lift_ascii
  {l : Type}
  (e : optionE(ascii * l)) :
    optionE(string * l) :=
      match e with
        | SomeE (c, H) => SomeE ((String c EmptyString), H)
        | NoneE err => NoneE err
      end.

Fixpoint match_string_helper (l : list ascii) : parser string :=
  fun xs =>
    match l with
      | []       => NoneE "empty pattern not allowed"
      | c::l'    => 
        match l' with
          | [] => lift_ascii (match_exactly c xs)
          | c'::l'' 
            => collapse_product (sequential (match_exactly c) 
              (match_string_helper l') xs)
        end
    end.

Definition match_string (s : string) : parser string :=
  fun xs => match_string_helper (list_of_string s) xs.

Example match_string1 :
  exists e,
    match_string "foo"%string (list_of_string "foobar"%string) = SomeE ("foo"%string, e).
Proof.  cbv; eexists; reflexivity.  Qed.

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
  fun xs =>
    match xs with
      | []        => NoneE "end of stream while parsing hex"
      | c::[]     => NoneE "end of stream while parsing hex"
      | c1::c2::l 
        => if isHexDigit c1 then
             if isHexDigit c2 then
               SomeE (ascii_of_Z (Z_of_hex_digit(c1) * 16 + Z_of_hex_digit(c2)),
                      exist _ l _)
             else
               SomeE (ascii_of_Z (Z_of_hex_digit(c1) * 16),
                      exist _ (c2::l) _)
           else
             NoneE "no hex digits found"
    end.
Next Obligation.
  apply sl_cons. apply sl_tail.
Qed.
Next Obligation.
  apply sl_tail.
Qed.

Definition parse_hex_string : parser string :=
  fun xs =>
    match
      sequential3 (match_exactly "<") (many match_hex) (match_exactly ">") xs
    with
      | SomeE ((_, l, _), xs') => SomeE (string_of_list l, xs')
      | NoneE err => NoneE err
    end.


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

Definition isLowerAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    andb (97 <=? n) (n <=? 122).

Definition isAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    orb (andb (65 <=? n) (n <=? 90))
        (andb (97 <=? n) (n <=? 122)).

Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in 
     andb (48 <=? n) (n <=? 57).

Inductive chartype := white | alpha | digit | other.

Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then 
    white
  else if isAlpha c then
    alpha
  else if isDigit c then
    digit
  else
    other.

Definition token := string.

Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii) 
                       : list (list ascii) :=
  let tk := match acc with [] => [] | _::_ => [rev acc] end in
  match xs with
  | [] => tk
  | (x::xs') =>
    match cls, classifyChar x, x with
    | _, _, "("      => tk ++ ["("]::(tokenize_helper other [] xs') 
    | _, _, ")"      => tk ++ [")"]::(tokenize_helper other [] xs') 
    | _, white, _    => tk ++ (tokenize_helper white [] xs')
    | alpha,alpha,x  => tokenize_helper alpha (x::acc) xs'
    | digit,digit,x  => tokenize_helper digit (x::acc) xs'
    | other,other,x  => tokenize_helper other (x::acc) xs'
    | _,tp,x         => tk ++ (tokenize_helper tp [x] xs')
    end
  end %char.

Definition tokenize (s : string) : list string :=
  map string_of_list (tokenize_helper white [] (list_of_string s)).

Example tokenize_ex1 : 
    tokenize "abc12==3  223*(3+(a+c))" %string
  = ["abc", "12", "==", "3", "223",
       "*", "(", "3", "+", "(",
       "a", "+", "c", ")", ")"]%string.
Proof. reflexivity. Qed.

(* ####################################################### *)
(** ** Parsing *)

(* ####################################################### *)
(** *** Options with Errors *)


(* Some syntactic sugar to make writing nested match-expressions on
   optionE more convenient. *)

Notation "'DO' ( x , y ) <== e1 ;; e2" 
   := (match e1 with
         | SomeE (x,y) => e2
         | NoneE err => NoneE err
       end)
   (right associativity, at level 60).

Notation "'DO' ( x , y ) <-- e1 ;; e2 'OR' e3" 
   := (match e1 with
         | SomeE (x,y) => e2
         | NoneE err => e3
       end)
   (right associativity, at level 60, e2 at next level). 

(* ####################################################### *)
(** *** Symbol Table *)

(* Build a mapping from [tokens] to [nats].  A real parser would do
   this incrementally as it encountered new symbols, but passing
   around the symbol table inside the parsing functions is a bit
   inconvenient, so instead we do it as a first pass. *)
Fixpoint build_symtable (xs : list token) (n : nat) : (token -> nat) :=
  match xs with
  | [] => (fun s => n)
  | x::xs =>
    if (forallb isLowerAlpha (list_of_string x))
     then (fun s => if string_dec s x then n else (build_symtable xs (S n) s))
     else build_symtable xs n
  end.

(* ####################################################### *)
(** *** Generic Combinators for Building Parsers *)

Open Scope string_scope.

Definition parser (T : Type) := 
  list token -> optionE (T * list token).

Fixpoint many_helper {T} (p : parser T) acc steps xs :=
match steps, p xs with
| 0, _ => NoneE "Too many recursive calls"
| _, NoneE _ => SomeE ((rev acc), xs)
| S steps', SomeE (t, xs') => many_helper p (t::acc) steps' xs'
end.

(* A (step-indexed) parser which expects zero or more [p]s *)
Fixpoint many {T} (p : parser T) (steps : nat) : parser (list T) :=
  many_helper p [] steps.

(* A parser which expects a given token, followed by p *)
Definition firstExpect {T} (t : token) (p : parser T) : parser T :=
  fun xs => match xs with
              | x::xs' => if string_dec x t 
                           then p xs' 
                          else NoneE ("expected '" ++ t ++ "'.")
              | [] =>  NoneE ("expected '" ++ t ++ "'.")
            end. 

(* A parser which expects a particular token *)
Definition expect (t : token) : parser unit :=
  firstExpect t (fun xs => SomeE(tt, xs)).

(* ####################################################### *)
(** *** A Recursive-Descent Parser for Imp *)

(* Identifiers *)
Definition parseIdentifier (symtable :string->nat) (xs : list token) 
                         : optionE (id * list token) :=
match xs with
| [] => NoneE "Expected identifier"
| x::xs' => 
    if forallb isLowerAlpha (list_of_string x) then
      SomeE (Id (symtable x), xs')
    else
      NoneE ("Illegal identifier:'" ++ x ++ "'")
end.

(* Numbers *)
Definition parseNumber (xs : list token) : optionE (nat * list token) :=
match xs with 
| [] => NoneE "Expected number"
| x::xs' => 
    if forallb isDigit (list_of_string x) then
      SomeE (fold_left (fun n d =>
                        10 * n + (nat_of_ascii d - nat_of_ascii "0"%char))
                (list_of_string x)
                0,
              xs')
    else 
      NoneE "Expected number"
end.

(* Parse arithmetic expressions *)
Fixpoint parsePrimaryExp (steps:nat) symtable (xs : list token) 
   : optionE (aexp * list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
      DO (i, rest) <-- parseIdentifier symtable xs ;;
          SomeE (AId i, rest)
      OR DO (n, rest) <-- parseNumber xs ;;
          SomeE (ANum n, rest)
      OR (DO (e, rest)  <== firstExpect "(" (parseSumExp steps' symtable) xs;;
          DO (u, rest') <== expect ")" rest ;;
          SomeE(e,rest'))
  end
with parseProductExp (steps:nat) symtable (xs : list token)  :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' => 
    DO (e, rest) <== 
      parsePrimaryExp steps' symtable xs ;;
    DO (es, rest') <== 
      many (firstExpect "*" (parsePrimaryExp steps' symtable)) steps' rest;;
    SomeE (fold_left AMult es e, rest')
  end
with parseSumExp (steps:nat) symtable (xs : list token)  :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' => 
    DO (e, rest) <== 
      parseProductExp steps' symtable xs ;;
    DO (es, rest') <== 
      many (fun xs =>
             DO (e,rest') <-- 
               firstExpect "+" (parseProductExp steps' symtable) xs;;
                                 SomeE ( (true, e), rest')
             OR DO (e,rest') <== 
               firstExpect "-" (parseProductExp steps' symtable) xs;;
                                 SomeE ( (false, e), rest'))
                            steps' rest;;
      SomeE (fold_left (fun e0 term => 
                          match term with 
                            (true,  e) => APlus e0 e
                          | (false, e) => AMinus e0 e
                          end)
                       es e, 
             rest')         
  end.

Definition parseAExp := parseSumExp.

(* Parsing boolean expressions. *)
Fixpoint parseAtomicExp (steps:nat) (symtable : string->nat) (xs : list token)  :=
match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
     DO    (u,rest) <-- expect "true" xs;;
         SomeE (BTrue,rest)
     OR DO (u,rest) <-- expect "false" xs;;
         SomeE (BFalse,rest)
     OR DO (e,rest) <-- firstExpect "not" (parseAtomicExp steps' symtable) xs;;
         SomeE (BNot e, rest)
     OR DO (e,rest) <-- firstExpect "(" (parseConjunctionExp steps' symtable) xs;;
          (DO (u,rest') <== expect ")" rest;; SomeE (e, rest'))
     OR DO (e, rest) <== parseProductExp steps' symtable xs ;;
            (DO (e', rest') <-- 
              firstExpect "==" (parseAExp steps' symtable) rest ;;
              SomeE (BEq e e', rest')
             OR DO (e', rest') <-- 
               firstExpect "<=" (parseAExp steps' symtable) rest ;;
               SomeE (BLe e e', rest')
             OR
               NoneE "Expected '==' or '<=' after arithmetic expression")
end
with parseConjunctionExp (steps:nat) (symtable : string->nat) (xs : list token)   :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    DO (e, rest) <== 
      parseAtomicExp steps' symtable xs ;;
    DO (es, rest') <== 
      many (firstExpect "&&" (parseAtomicExp steps' symtable)) steps' rest;;
    SomeE (fold_left BAnd es e, rest')
  end.

Definition parseBExp := parseConjunctionExp.

(* 
Eval compute in 
  (parseProductExp 100 (tokenize "x*y*(x*x)*x")).

Eval compute in 
  (parseDisjunctionExp 100 (tokenize "not((x==x||x*x<=(x*x)*x)&&x==x)")). 
*)

(* Parsing commands *)
Fixpoint parseSimpleCommand (steps:nat) (symtable:string->nat) (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' => 
    DO (u, rest) <-- expect "SKIP" xs;;
      SomeE (SKIP, rest)
    OR DO (e,rest) <-- 
         firstExpect "IF" (parseBExp steps' symtable) xs;;
       DO (c,rest')  <== 
         firstExpect "THEN" (parseSequencedCommand steps' symtable) rest;;
       DO (c',rest'') <== 
         firstExpect "ELSE" (parseSequencedCommand steps' symtable) rest';;
       DO (u,rest''') <== 
         expect "END" rest'';;
       SomeE(IFB e THEN c ELSE c' FI, rest''')
    OR DO (e,rest) <-- 
         firstExpect "WHILE" (parseBExp steps' symtable) xs;;
       DO (c,rest') <== 
         firstExpect "DO" (parseSequencedCommand steps' symtable) rest;;
       DO (u,rest'') <== 
         expect "END" rest';;
       SomeE(WHILE e DO c END, rest'')
    OR DO (i, rest) <== 
         parseIdentifier symtable xs;;
       DO (e, rest') <== 
         firstExpect ":=" (parseAExp steps' symtable) rest;;
       SomeE(i ::= e, rest')
  end

with parseSequencedCommand (steps:nat) (symtable:string->nat) (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' => 
      DO (c, rest) <== 
        parseSimpleCommand steps' symtable xs;;
      DO (c', rest') <-- 
        firstExpect ";" (parseSequencedCommand steps' symtable) rest;;
        SomeE(c ; c', rest')
      OR
        SomeE(c, rest)
  end.

Definition parse (str : string) : optionE (com * list token) :=
  let tokens := tokenize str in
  parseSequencedCommand 1000 (build_symtable tokens 0) tokens.

(* ####################################################### *)
(** * Examples *)

(*
Eval compute in parse "
    IF x == y + 1 + 2 - y * 6 + 3 THEN
      x := x * 1;
      y := 0
    ELSE
      SKIP
    END  ".
====>
    SomeE
       (IFB BEq (AId (Id 0))
                (APlus
                   (AMinus (APlus (APlus (AId (Id 1)) (ANum 1)) (ANum 2))
                      (AMult (AId (Id 1)) (ANum 6))) 
                   (ANum 3))
        THEN Id 0 ::= AMult (AId (Id 0)) (ANum 1); Id 1 ::= ANum 0
        ELSE SKIP FI, [])
*)

(*
Eval compute in parse "
    SKIP;
    z:=x*y*(x*x);
    WHILE x==x DO
      IF z <= z*z && not x == 2 THEN
        x := z;
        y := z
      ELSE
        SKIP
      END;
      SKIP
    END;
    x:=z  ".
====> 
     SomeE
        (SKIP;
         Id 0 ::= AMult (AMult (AId (Id 1)) (AId (Id 2)))
                        (AMult (AId (Id 1)) (AId (Id 1)));
         WHILE BEq (AId (Id 1)) (AId (Id 1)) DO 
           IFB BAnd (BLe (AId (Id 0)) (AMult (AId (Id 0)) (AId (Id 0))))
                     (BNot (BEq (AId (Id 1)) (ANum 2)))
              THEN Id 1 ::= AId (Id 0); Id 2 ::= AId (Id 0) 
              ELSE SKIP FI; 
           SKIP 
         END; 
         Id 1 ::= AId (Id 0), 
        []) 
*)

(*
Eval compute in parse "
   SKIP;
   z:=x*y*(x*x);
   WHILE x==x DO
     IF z <= z*z && not x == 2 THEN
       x := z;
       y := z
     ELSE
       SKIP
     END;
     SKIP
   END;
   x:=z  ".
=====> 
      SomeE
         (SKIP;
          Id 0 ::= AMult (AMult (AId (Id 1)) (AId (Id 2)))
                (AMult (AId (Id 1)) (AId (Id 1)));
          WHILE BEq (AId (Id 1)) (AId (Id 1)) DO 
            IFB BAnd (BLe (AId (Id 0)) (AMult (AId (Id 0)) (AId (Id 0))))
                     (BNot (BEq (AId (Id 1)) (ANum 2)))
              THEN Id 1 ::= AId (Id 0); 
                   Id 2 ::= AId (Id 0) 
              ELSE SKIP 
            FI; 
            SKIP 
          END; 
          Id 1 ::= AId (Id 0), 
         []).
*)
