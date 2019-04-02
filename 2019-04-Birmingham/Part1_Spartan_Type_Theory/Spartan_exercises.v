Require Import UniMath.Foundations.PartD.

(** The following axiom allows us to inhabit any type.
    It is a way of indicating where you need to fill in
    your own solutions. Remove it once you're done with
    all the exercises. *)
Axiom fill_me : forall {X : UU}, X.

(** Exercise 1.1. A × (B + C) → A × B + A × C, given types A, B, C *)

Definition exercise_1_1 (A B C : UU)
  : A × (B ⨿ C) → (A × B) ⨿ (A × C) :=
  λ p, coprod_rect
         (λ _, (A × B) ⨿ (A × C))
         (λ x, ii1 (pr1 p ,, x))
         (λ y, ii2 (pr1 p ,, y))
         (pr2 p).

(** Exercise 1.2. (A → A) → (A → A), given type A

    for extra credit, write down *five* elements of this type *)

Definition exercise_1_2 (A : UU)
  : (A → A) → (A → A)
  := λ f x, f(f x).

(** Exercise 1.3. Id_nat (0, succ 0) → empty *)

Check transportf.
Check nat_rect.
Check (nat_rect (λ _, UU) unit (λ _ _, empty)).
Check (λ n, (nat_rect (λ _, UU) unit (λ _ _, empty) n)).
Check λ p: 0 = 1, transportf (nat_rect (λ _, UU) unit (λ _ _, empty)) p.
Check nat_rect (λ _ : nat, UU) unit (λ (_ : nat) (_ : UU), ∅) 0.

Theorem exercise_1_3 : (0 = 1) → empty.
Proof.
  exact (λ p, transportf (nat_rect (λ _, UU) unit (λ _ _, empty)) p tt).
Qed.

(** Exercise 1.4. ∑ (A : Universe) (A → empty) *)

Theorem exercise_1_4 : ∑ A:UU, (A → empty).
Proof.
  exact (empty ,, λ x, x).
Qed.

(** Exercise 1.6. (∑ (x : A) B × P x) → B × ∑ (x : A) P x,
                  given types A, B, and P : A → Universe *)

Theorem exercise_1_6 (A B:UU) (P:A → UU) : (∑ x:A, B × P x) → B × ∑ x:A, P x.
Proof.
  exact (λ p, (pr1(pr2 p) ,, (pr1 p ,, pr2(pr2 p)))).
Qed.

(** Exercise 1.7. B → (B → A) → A, given types A and B *)

Theorem exercise_1_7 (A B : UU) : B → (B → A) → A.
Proof. exact (λ b f, f b). Qed.

(** Exercise 1.8. B → ∏ (A : Universe) (B → A) → A, given type B *)

Theorem exercise_1_8 (B : UU) : B → ∏ A:UU, (B → A) → A.
Proof. exact (λ b _ f, f b). Qed.

(** Exercise 1.9. (∏ (A : Universe) (B → A) → A) → B, given type B *)

Theorem exercise_1_9 (B : UU) : (∏ A:UU, (B → A) → A) → B.
Proof. exact (λ f, f B (λ x, x)). Qed.

(** Exercise 2.1. Using the basic rules, construct addition on natural numbers. *)

Definition nat_plus : nat → nat → nat := λ m n, (nat_rect (λ _, nat → nat) (λ n, n) (λ _ f k, S(f k)) m) n.

(** Exercise 2.2. State associativity and commutativity of addition in a type-theoretic way. *)

Definition exercise_2_2_assoc : UU := ∏(m n k : nat), nat_plus (nat_plus m n) k = nat_plus m (nat_plus n k).

Definition exercise_2_2_comm : UU := ∏(m n : nat), nat_plus m n = nat_plus n m.

(** Exercise 2.3. Establish associativity and commutativity of addition. What does this mean in type theory? *)

Theorem zero_n_k_assoc: ∏(n k : nat), nat_plus (nat_plus 0 n) k = nat_plus 0 (nat_plus n k).
Proof.
  exact (λ n k, idpath(nat_plus n k)).
Qed.

Theorem nat_plus_is_assoc : exercise_2_2_assoc.
Proof.
  exact (nat_rect
           (λ m, ∏(n k : nat), nat_plus (nat_plus m n) k = nat_plus m (nat_plus n k))
           zero_n_k_assoc
           (λ m IH n k, maponpaths S (IH n k))).
Qed.

Lemma nat_plus_l_zero: ∏(n : nat), n = nat_plus n 0.
Proof.
  induction n.
  exact (idpath 0).
  exact (maponpaths S IHn).
Qed.

Lemma nat_plus_l_S: ∏(n k : nat), S(nat_plus n k) = nat_plus k (S n).
Proof.
  induction n.
  exact (λ k, idpath (S k)).
  exact (λ k, maponpaths S (IHn k)).
Qed.

Print exercise_2_2_comm.

Theorem nat_plus_is_comm : exercise_2_2_comm.
Proof.
  unfold exercise_2_2_comm; intros; induction m.
  exact (nat_plus_l_zero n).
  exact (nat_plus_l_S m n).
Qed.

(** Exercise 3. Write down the following types:

    1. even natural numbers *)

Definition exercise_3_1 : UU := fill_me.

(** 2. prime numbers *)

Definition nat_mult : nat → nat → nat := fill_me.

Definition exercise_3_2 : UU := fill_me.

(** 3. functions A → nat which attain zero *)

Definition exercise_3_3 (A : UU) : UU := fill_me.

(** 4. the "less than" relation on natural numbers *)

Definition exercise_3_4 (n m : nat) : UU := fill_me.
