(* unilist -- unique element list *)

Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.

Require Import Coq.Bool.Bool.

Require Import Coq.Arith.Arith.

Require Import Omega.

Require Import Coq.Program.Program.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.

Open Scope bool_scope.
Open Scope nat_scope.

Inductive limited_unique_list (max : nat) : list nat -> Prop :=
  | LUNil  : limited_unique_list max nil
  | LUCons : forall x xs, limited_unique_list max xs
             -> x <= max
             -> ~ (In x xs)
             -> limited_unique_list max (x :: xs).

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

Definition lucons {max : nat} (x : nat) (xs : list nat) : option (list nat) :=
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

Theorem lucons_step : forall max x xs v, @lucons max x xs = v ->
  (v = Some (x :: xs) /\ x <= max /\ length xs < length (x::xs)) \/ (v = None).
Proof.
  intros.
  destruct v; [ left | right; reflexivity ].
  unfold lucons in H; remember (is_lulist max (x :: xs)) as b; destruct b.
    repeat split; try congruence; clear - Heqb.
      unfold is_lulist in Heqb; fold (@is_lulist max) in Heqb.
      remember (leb x max) as b; destruct b.
        symmetry in Heqb0; apply (leb_complete _ _ Heqb0).
        rewrite orb_true_r in Heqb; inversion Heqb.
      simpl; constructor.
    inversion H.
Qed.

Theorem lucons_toobig : forall max x xs, max < x -> @lucons max x xs = None.
Proof.
  intros; unfold lucons; unfold is_lulist; fold is_lulist.
  unfold lt in H. apply leb_correct in H.
  remember (leb x max) as b; destruct b.
    apply leb_complete in H; symmetry in Heqb; apply leb_complete in Heqb; elimtype False; omega.
    simpl; rewrite orb_true_r; reflexivity.
Qed.

Theorem limited_unique_list_increasemax : forall max xs,
  limited_unique_list max xs -> limited_unique_list (S max) xs.
Proof.
  intros; induction H; subst; constructor; try assumption; omega.
Qed.

