Require Import Arith.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S n => match n with
           | O => false
           | S n => evenb n
           end
  end.

Inductive optionE (X:Type) : Type :=
  | SomeE : X -> optionE X
  | NoneE : optionE X.
Implicit Arguments SomeE [[X]].
Implicit Arguments NoneE [[X]].


Definition decreasing_nat := forall l : nat, optionE {l' : nat | l' < l}.

Definition skip_step : forall xs (pf_ys : optionE { ys | ys < xs }),
                                          optionE { ys | ys < S xs }.
  intros; destruct pf_ys; [ | exact NoneE ];
    destruct s as [x ys]; constructor; exists x; auto.
Defined.

(*****

## Problem ##

Solving the obligations automatically, a working function is defined.
When solving manually, an exception is thrown by the kernel at Qed.

*****)

Program Definition skip_many_even : decreasing_nat :=
  fix f xs :=
    match xs with
    | O    => NoneE
    | S ys => if evenb ys then
             _ ys (f ys)  (* generating obligation and solving manually triggers bug *)
             (*skip_step ys (f ys) *)  (* replace above line with this to make it work *)
           else
             match ys with
             | O    => NoneE
             | S zs => SomeE (exist _ zs _)
             end
    end.

Next Obligation.
  apply skip_step. assumption.
Qed.

Eval compute in match_hex 23.
Eval compute in match_hex 22.

(*

## OUTPUT ##

    Error: Anomaly: Uncaught exception Type_errors.TypeError(_, _).
           Please report.

*)
                        

