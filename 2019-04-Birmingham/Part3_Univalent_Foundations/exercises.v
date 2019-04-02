Require Import UniMath.Foundations.PartD.

Definition pred : nat → nat := nat_rect (λ _, nat) 0 (λ n _, n).

(* Exercise, p. 17 *)

Definition nat_ge : nat → nat → UU :=
  nat_rect
    (λ _, nat → UU)
    (λ _, empty)
    (λ m IHm, nat_rect
                (λ _, UU)
                unit
                (λ n _, IHm n)).

Notation "a > b" := (nat_ge a b).
