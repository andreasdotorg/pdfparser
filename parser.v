Require Import SfLib.

Require Import String.
Require Import Ascii.
Require Import Recdef.

Require Import sublist.

(* comparisons *)

Definition eq_ascii (c d : ascii) : bool :=
  if ascii_dec c d then true else false.

Notation "x '<=?' y" := (ble_nat x y)
  (at level 70, no associativity) : nat_scope.

(* ####################################################### *)
(** ** option type *)

(* An option with error messages. *)
Inductive optionE (X:Type) : Type :=
  | SomeE : X -> optionE X
  | NoneE : string -> optionE X.

Implicit Arguments SomeE [[X]].
Implicit Arguments NoneE [[X]].

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
(** ** string <--> list *)

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: (list_of_string s)
  end.

Definition string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

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

Hint Resolve parser_nil_none. (* : pdfparser. *)

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

Hint Rewrite many_helper_equation. (* : pdfparser. *)

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

Fixpoint some_helper {T:Set} (n : nat) (acc : list T) (p : parser T) (xs : list ascii):
  optionE (list T * {xs' : list ascii | sublist xs' xs}) :=
  match n with
    | 0   => NoneE "Empty some match"
(*
    | 1   => match p xs with
               | NoneE err              => NoneE err
               | SomeE (t, exist xs' H) => SomeE ((rev (t::acc)), exist _ xs' H)
             end *)
    | (S n') => match p xs with
                  | NoneE err                => NoneE err
                  | SomeE (t, exist xs' H)   =>
                    match n with
                      | 1 => SomeE ((rev (t::acc)), exist _ xs' H)
                      | _ 
                        => match some_helper n' (t::acc) p xs' with
                             | NoneE err => NoneE err
                             | SomeE (acc', exist xs'' H') => SomeE (acc', exist _ xs'' (sublist_trans H' H))
                           end
                    end
                end
  end.

Definition some {T:Set} (n : nat) (p : parser T) : parser (list T) :=
  fun xs => some_helper n [] p xs.

Example some_ex1 :
  exists e,
    some 3 match_any (list_of_string "foobar"%string) = SomeE ((list_of_string "foo"%string), e).
Proof.  cbv; eexists; reflexivity.  Qed.


Definition match_one_char_with_predicate (p : ascii -> bool) : parser ascii :=
  parse_one_character (fun t => if p (fst t) then SomeE (fst t) else NoneE "predicate false").

Definition exist_left_projection {A : Set} {B : A -> Prop} (e : sig B) := 
  match e with | exist a b => a end.

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

(* Hilfsbeweis(funktionen) *)

Program Definition pf_skipped_one_character {c1 : ascii} {l0 : list ascii}
    (pf : optionE (ascii * {l' : list ascii | sublist l' l0}))
    : optionE (ascii * {l' : list ascii | sublist l' (c1 :: l0)}) := 
  match pf with
    | SomeE ((c,exist l _)) => SomeE (c,exist _ l _)
    | NoneE err => NoneE err
  end.



(* bis hier *)

