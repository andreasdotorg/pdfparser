(* unilist -- unique element list *)

Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.

Require Import Coq.Bool.Bool.

Require Import Coq.Arith.Arith.

Require Import Omega.

Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.PermutEq.

Require Import Coq.Program.Program.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.

Open Scope bool_scope.
Open Scope nat_scope.

(** * limited_unique_list

  This is an inductive predicate for lists containing every number up
  to `max` at most once.

**)

Inductive limited_unique_list (max : nat) : list nat -> Prop :=
  | LUNil  : limited_unique_list max nil
  | LUCons : forall x xs, limited_unique_list max xs
             -> x <= max
             -> ~ (In x xs)
             -> limited_unique_list max (x :: xs).

(** ** Permutability **)

(**
  Inversion of a `In` hypothesis sometimes yields an unfolded definition.
  This folds it back.
**)

Theorem In_pretty_please : forall {A : Type} {x : A} {l},
    (fix In (a : A) (l : list A) {struct l} : Prop :=
       match l with
       | nil => False
       | b :: m => b = a \/ In a m
       end) x l
    -> In x l.
Proof.
  intros; induction l.
    inversion H.
    inversion H; subst.
      constructor; reflexivity.
      pose proof (IHl H0); constructor 2; assumption.
Defined.

(**
  `In` and `~ In` are preserved under `Permutation`.
**)

Theorem Permutation_In : forall {A : Type} (a:A) {xs ys}, Permutation xs ys ->
    (In a xs <-> In a ys).
Proof.
  intros; generalize dependent a; induction H; simpl; intros.
    split; intro; assumption.
    split; intro H0; inversion H0; subst; try (left; reflexivity); right;
      [ rewrite <- IHPermutation | rewrite IHPermutation ]; assumption.
    split; intro; inversion H as [H1|H1]; subst; try (right; left; reflexivity);
      inversion H1 as [H2|H2]; subst; try (left; reflexivity); right; right; assumption.
    rewrite IHPermutation1; apply IHPermutation2.
Defined.

Theorem Permutation_not_In : forall {A : Type} (a:A) {xs ys}, Permutation xs ys ->
    (~ In a xs <-> ~ In a ys).
Proof.
  intros; split; intros; intro C; apply H0.
    rewrite <- (Permutation_In _ H) in C; assumption.
    rewrite -> (Permutation_In _ H) in C; assumption.
Defined.

(**
  Permutation preserves `limited_unique_list` and `~ limited_unique_list`
**)

Theorem Permutation_limited_unique_list : forall max {xs ys}, Permutation xs ys ->
    (limited_unique_list max xs <-> limited_unique_list max ys).
Proof.
  intros; induction H; simpl in *; intros.
    split; intros; assumption.
    split; intro; inversion H0; subst.
      rewrite (Permutation_not_In x H) in H5; constructor; try assumption;
          rewrite <- IHPermutation; assumption.
      rewrite <- (Permutation_not_In x H) in H5; constructor; try assumption;
          rewrite IHPermutation; assumption.
    split; intros; inversion H; subst;
      inversion H2; subst; repeat constructor; try assumption;
        try (intro C; apply H4; constructor 2; assumption);
        intro C; inversion C; subst;
          try (apply H4; constructor; reflexivity);
          pose proof (In_pretty_please H0); clear H0; apply (H7 H1).
    rewrite IHPermutation1; assumption.
Defined.

Theorem Permutation_not_limited_unique_list : forall max {xs ys}, Permutation xs ys ->
    (~ limited_unique_list max xs <-> ~ limited_unique_list max ys).
Proof.
  intros; split; intros; intro C; apply H0.
    rewrite (Permutation_limited_unique_list _ H); assumption.
    rewrite <- (Permutation_limited_unique_list _ H); assumption.
Defined.

(** *** Some Useful Permutations **)

(* Permutation_rev : Permutation xs (rev xs) *)

Definition sort := Mergesort.NatSort.sort.

Definition Permutation_sort : forall l, Permutation l (sort l) :=
  Mergesort.NatSort.Permuted_sort.

Definition rev_sort x := rev (sort x).

Theorem Permutation_rev_sort : forall l, Permutation l (rev_sort l).
Proof.
  intro l; unfold rev_sort.
  eapply Permutation_trans.
    apply Permutation_sort.
    apply Permutation_rev.
Qed.

(** *** Properties of `rev_sort`ed Lists **)

(**
  No matter how you permute a list, sort will produce the same result.
**)

Theorem sort_Permutation__sort : forall {l l'}, Permutation l l' ->
  sort l = sort l'.
Proof.  (* XXX TODO XXX *)  Admitted.

(**
  For a sorted `limited_unique_list`, the head is bigger than any element of the rest.
**)

Theorem rev_sort__max_hd : forall {max y} {xs ys}, limited_unique_list max xs ->
    rev_sort xs = (y :: ys) -> forall x, In x ys -> x < y.
Proof. (* XXX TODO XXX *) Admitted.
(* rev_sort puts the biggest element first |- rest is smaller or equal
   limited_unique_list |- every element is contained at most once
   ... |- rest is strictly smaller
   ... |- every element in rest is smaller than y
*)

(**
  For a sorted list, the tail is also sorted.
**)

Theorem rev_sort__rev_sort_tl : forall {xs},
    rev_sort xs = xs -> rev_sort (tl xs) = (tl xs).
Proof. (* XXX TODO XXX *) Admitted.

(** *** Reducing `max` in limited_unique_list **)

(**
  `max` can be reduced if the biggest element is at most `pred max`.
**)

Theorem limited_unique_list_pred : forall {max xs},
    limited_unique_list max xs -> ~ In max xs ->
    limited_unique_list (pred max) xs.
Proof.
  intros max xs H; induction H; simpl; intros.
    constructor.
    apply Decidable.not_or in H2; inversion H2; clear H2;
        apply IHlimited_unique_list in H4; constructor; try assumption.
    destruct max; simpl; inversion H0; subst; try assumption; elim (H3 eq_refl).
Qed.

(**
  ensuring reducibility of `max` by dropping the first element of the sorted list
  if necessary.
**)

Definition drop_hd_if_max (max : nat) (xs0 : list nat) :=
  match xs0 with
  | nil     => nil
  | (x::xs) => match beq_nat max x with
               | true => xs
               | false => (x::xs)
               end
  end.

Theorem limited_unique_list_drop_hd_if_max : forall {max y} {xs ys},
    limited_unique_list max xs -> rev_sort xs = (y :: ys) ->
    limited_unique_list (pred max) (drop_hd_if_max max (y :: ys)).
Proof.
  intros max y xs ys H H0.
  pose proof (Permutation_rev_sort xs); rewrite H0 in H1.
  pose proof (Permutation_limited_unique_list max H1).
  pose proof H; rewrite H2 in H3; clear H2.
  inversion H3; subst; simpl.
  pose proof (rev_sort__max_hd H H0).
  pose proof (eq_nat_dec max y); destruct H4; subst.
    rewrite <- beq_nat_refl; apply limited_unique_list_pred; assumption.
    inversion H6; try (elimtype False; omega); subst.
    rewrite <- beq_nat_false_iff in n; rewrite n.
    apply limited_unique_list_pred; try assumption.
    clear - H2 H4; intro C; induction C.
      omega.
      pose proof (H2 (S m) H); omega.
Qed.

Theorem limited_unique_list_drop_hd_any : forall max y xs ys,
    limited_unique_list max xs -> rev_sort xs = (y :: ys) ->
    limited_unique_list (pred max) ys.
Proof.
  intros; pose proof (limited_unique_list_drop_hd_if_max H H0).
  unfold drop_hd_if_max in H1; destruct (beq_nat max y).
    assumption.
    inversion H1; assumption.
Qed.

(**
  `max` can always be increased.
**)

Theorem limited_unique_list_increasemax : forall max xs,
  limited_unique_list max xs -> limited_unique_list (S max) xs.
Proof.
  intros; induction H; subst; constructor; try assumption; omega.
Qed.

(** ** Filling the limited_unique_list **)

(**
  If an element is bigger than `max` it cannot be inserted.
**)

Theorem limited_unique_list_toobig : forall max x xs, max < x -> ~ limited_unique_list max (x::xs).
Proof.
  intros; intro C; inversion C; subst; omega.
Qed.

(**
  A `limited_unique_list` that contains all elements and is sorted.
  (List is equivalent to [max..0].)
**)

Definition limited_unique_list_full_sorted max l :=
  limited_unique_list max l /\ length l = S max /\ rev_sort l = l.

(**
  Induction principle preserving full-ness of the list.
**)

Theorem limited_unique_list_full_sorted_ind : forall (P : nat -> list nat -> Prop),
    P 0 [0]
    -> (forall (max : nat) (x : nat) (xs : list nat),
        limited_unique_list_full_sorted max xs ->
        P max xs -> x <= (S max) -> ~ In x xs -> P (S max) (x :: xs))
    -> forall max l, limited_unique_list_full_sorted max l
    -> P max l.
Proof.
  intros P H0 HI max; induction max; simpl; intros; inversion H; inversion H2;
          clear H H2; destruct l; inversion H3; rewrite H2 in *.
    destruct l; inversion H2; inversion H1; inversion H7; subst; assumption.
    pose proof (limited_unique_list_drop_hd_if_max H1 H4).
    pose proof (rev_sort__rev_sort_tl H4); simpl in H5.    
    assert (limited_unique_list max l). clear - H H1 H4.
      inversion H1; subst; inversion H5; subst.
        simpl in H; rewrite <- beq_nat_refl in H; assumption.
        unfold drop_hd_if_max in H; assert ((S max) <> n) by omega.
        rewrite <- beq_nat_false_iff in H0; rewrite H0 in *; simpl in H;
        inversion H; assumption.
    assert (limited_unique_list_full_sorted max l) by
            (repeat split; try assumption; apply H5).
    inversion H1; refine (HI _ _ _ H7 (IHmax _ H7) _ _); assumption.
Qed.

(**
  No element can be inserted into a full `limited_unique_list`.
**)

Theorem limited_unique_list_full_all : forall {max} {xs},
    limited_unique_list_full_sorted max xs
    -> forall x, max < x \/ In x xs.
Proof.
  intros max xs H; induction H using limited_unique_list_full_sorted_ind.
    intros; destruct x; [ right; constructor; reflexivity | left; omega ].
    rename IHlimited_unique_list_full_sorted into IH; intro y.
    pose proof (le_lt_dec y max) as E; destruct E.
      pose proof (IH y); destruct H2.
        elimtype False; omega.
        right; right; assumption.
      pose proof (eq_nat_dec (S max) y) as E; destruct E; subst.
        Focus 2.  assert (S max < y) by omega; left; assumption.
        right; inversion H0; subst.
          left; reflexivity.
          pose proof (IH x); inversion H2; elimtype False; try omega.
            apply (H1 H4).
Qed.

Theorem limited_unique_list_full_noinsert : forall {max} {xs},
    limited_unique_list_full_sorted max xs ->
    forall x, ~ limited_unique_list max (x::xs).
Proof.
  intros.
  pose proof (limited_unique_list_full_all H).
  intro C; inversion C; subst.
  pose proof (H0 x); inversion H1; try omega. apply (H5 H2).
Qed.

Theorem limited_unique_list__maxlength : forall {max} {xs},
  limited_unique_list max xs ->
  length xs <= S max.
Proof.
  intros max xs; generalize dependent max; induction xs.
    intros; simpl; omega.
    intros; inversion H; subst; simpl; pose proof (IHxs max H2); inversion H0.
      pose proof (Permutation_rev_sort xs).
      assert (limited_unique_list_full_sorted max (rev_sort xs)).
        repeat split.
          rewrite <- (Permutation_limited_unique_list max H1); assumption.
          rewrite <- (Permutation_length H1); assumption.
          SearchAbout "sort".
          unfold rev_sort at 1; rewrite <- (sort_Permutation__sort H1); reflexivity.
      pose proof (limited_unique_list_full_noinsert H6 a).
      assert (Permutation (a::xs) (a :: rev_sort xs)) by (constructor 2; assumption).
      rewrite (Permutation_limited_unique_list max H8) in H.
      elim (H7 H).
      omega.
Qed.

(** * Computational Equivalent to `limited_unique_list` **)

Fixpoint is_lulist (max : nat) (xs0 : list nat) : bool :=
  match xs0 with
  | nil     => true
  | (x::xs) => if (existsb (beq_nat x) xs) || negb (leb x max)
                 then false
                 else is_lulist max xs
  end.

Theorem is_lulist_iff_limited_unique_list : forall (max : nat) (xs0 : list nat),
    true = is_lulist max xs0 <-> limited_unique_list max xs0.
Proof.
  intros max xs0.
  induction xs0.
    split.
      intros; constructor.
      intros; reflexivity.
    inversion IHxs0 as [ IH0 IH1 ]; clear IHxs0; split; intro H.
      inversion H.
        remember (existsb (beq_nat a) xs0) as bU;
        remember (negb (leb a max)) as bL.
        destruct bU; destruct bL;
          simpl in *; inversion H1.
        clear H2; pose proof (IH0 H1).
        apply negb_sym in HeqbL; simpl in HeqbL; apply leb_complete in HeqbL.
        constructor; try assumption.
        clear - HeqbU.
        intro C.
        assert (exists x : nat, In x xs0 /\ beq_nat a x = true).
          exists a; split; try assumption; rewrite <- beq_nat_refl; reflexivity.
        rewrite <- existsb_exists in H.
        rewrite H in HeqbU; inversion HeqbU.
      inversion H; simpl.
        remember (existsb (beq_nat a) xs0) as bU;
        remember (negb (leb a max)) as bL.
        destruct bU; destruct bL; simpl in *;
          try (apply leb_correct in H3; rewrite <- H3 in HeqbL;
               symmetry in HeqbL; elimtype False; apply (no_fixpoint_negb _ HeqbL));
          try (apply IH1; assumption).
        elimtype False; apply H4; subst.
        symmetry in HeqbU; rewrite existsb_exists in HeqbU.
        inversion HeqbU as [ x0 Hn ]; inversion Hn; clear HeqbU Hn.
        symmetry in H1; apply beq_nat_eq in H1; subst; assumption.
Qed.

(**
  The safe insertion function.
**)

Definition lucons (max : nat) (x : nat) (xs : list nat) : option (list nat) :=
  if is_lulist max (x::xs)
    then Some (x :: xs)
    else None.

Theorem lucons_iff_LUCons : forall max x xs, limited_unique_list max xs ->
    (@lucons max x xs = Some (x :: xs) <-> limited_unique_list max (x::xs)).
Proof.
  intros; split; intro.
    unfold lucons in H0;
      remember (is_lulist max (x :: xs)) as b; destruct b; inversion H0;
      rewrite is_lulist_iff_limited_unique_list in Heqb; assumption.
    rewrite <- is_lulist_iff_limited_unique_list in H0;
      unfold lucons; rewrite <- H0; reflexivity.
Qed.

(**
  Proof helper, unfolding one level of the list.
**)

Theorem lucons_step : forall max x xs v, @lucons max x xs = v ->
  (v = Some (x :: xs) /\ x <= max /\ ~ In x xs) \/ (v = None).
Proof.
  intros.
  destruct v; [ left | right; reflexivity ].
  unfold lucons in H; remember (is_lulist max (x :: xs)) as b; destruct b.
    repeat split; try congruence; clear - Heqb.
      unfold is_lulist in Heqb; fold (@is_lulist max) in Heqb.
      remember (leb x max) as b; destruct b.
        symmetry in Heqb0; apply (leb_complete _ _ Heqb0).
        rewrite orb_true_r in Heqb; inversion Heqb.
      rewrite is_lulist_iff_limited_unique_list in Heqb; inversion Heqb; assumption.
    inversion H.
Qed.
