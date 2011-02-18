(** * Internals *)

Require Import SfLib.

Open Scope list_scope.

(* ####################################################### *)
(** ** Helpers *)

Theorem list_loop : forall {A : Set} {x : A} {l : list A}, (x::l) <> l.
  intros; generalize dependent x.
  induction l; intros x C.
    inversion C.
    set (f:= @tail A); pose proof (f_equal f C) as H; simpl in H.
    apply (IHl _ H).
Qed.

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
                    lt_length_cons_cons. (* : pdfparser. *)

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

  End sublist_order.

  (* additional pseudo-constructor *)
  Theorem sl_minus : forall (c : A) {l' l}, sublist (c::l') l -> sublist l' l.
  Proof.
    intros; destruct l.
      inversion H.
      apply sublist_tails in H. constructor; assumption.
  Qed.

  Unset Implicit Arguments.
End true_sublist.

Hint Constructors sublist.
Hint Resolve sublist__lt_length sublist_tails sublist_trans. (* : sublist pdfparser. *)
Hint Resolve sl_minus.
