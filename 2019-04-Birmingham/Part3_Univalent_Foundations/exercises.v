Require Import UniMath.Foundations.PartD.

Definition triv_id := λ(x: empty), x.

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

(* Exercise, p. 21 *)

Definition paths_inv {A : UU} {a b : A} (p : a = b) :=
  paths_rect A a (λ y _, y = a) (idpath a) b p.

Definition paths_comp {A : UU} {x y z : A} (p : x = y) (q : y = z) : x = z.
Proof. induction p; induction q; reflexivity. Defined.

Definition paths_ap {A B : UU} {x y : A} (f : A → B) (p : x = y) : (f x = f y).
Proof. induction p; reflexivity. Defined.

Definition transport {A : UU} {B : A → UU} {x y : A} (p : x = y) : B x → B y.
Proof. induction p; exact (idfun (B x)). Qed.

(* Theorem, p. 29 *)

Theorem iscontr_star {A : UU} : ∏(y : A), iscontr(∑(x: A), x = y).
Proof.
  intros y.
  unfold iscontr.
  use tpair.
  - exact (y,,idpath y).
  - cbn.
    intros [x p].
    induction p; reflexivity.
Qed.
