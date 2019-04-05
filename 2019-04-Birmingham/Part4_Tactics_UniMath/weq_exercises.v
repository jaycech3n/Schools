(** *** Advanced exercise sheet for lecture 4: Tactics in Coq. *)

(** Some exercises about equivalences - recall from the course that associativity
    for products of types is not available "on the nose", i.e., just with equality.

    Exercises originally suggested by Benedikt Ahrens and Anders Mörtberg
    (for UniMath school 2017) and elaborated by Ralph Matthes (CNRS, IRIT,
    Univ. Toulouse, France)
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Locate "≃". (** written in Agda mode as [\simeq] *)
Print weq.
Print isweq.
Print hfiber.

Section weqdef.

Variables X Y: UU.
Eval compute in (X ≃ Y).
(** there is a function [f] so that for given image [y] on can find the preimage [x] uniquely, but not only as element of [X] but even the pair consisting of the preimage and the proof that it is the preimage is unique. *)
End weqdef.

(** Prove that the identity function is an equivalence *)
Lemma idisweq (X : UU) : isweq (idfun X).
Proof.
  exact (iscontrcoconustot X).
Qed.

Print weq.

(** Package this up as an equivalence *)
Definition idweq (X : UU) : X ≃ X.
Proof.
  unfold weq.
  exists (idfun X).
  exact (idisweq X).
Qed.

(** consider finding an alternative proof with [isweq_iso] that is extremely useful in the UniMath library *)

Print isweq_iso.

Lemma idisweq' (X : UU) : isweq (idfun X).
Proof.
  apply (isweq_iso (idfun X) (idfun X)).
  intro; compute; reflexivity.
  intro; compute; reflexivity.
Qed.

(** Prove that any map to empty is an equivalence *)
Lemma isweqtoempty {X : UU} (f : X -> ∅) : isweq f.
Proof.
  unfold isweq; intro y; induction y.
Qed.

(** Package this up as an equivalence *)
Definition weqtoempty {X : UU} (f : X -> ∅) : X ≃ ∅.
Proof. unfold weq. exact (f,,isweqtoempty f). Qed.

(** Prove that the composition of equivalences is an equivalence.

This is rather difficult to do directly from the definition. Important lemmas
to reason on equality of pairs in a sigma type are given by [base_paths] and
[fiber_paths] that are elimination rules (that use given equality of pairs)
and [total2_paths2_f] that is an introduction rule allowing to establish an
equation between pairs. There, transport arises, but transport along the
identity path is always the identity, and this already computationally, which
means that [cbn] gets rid of it. *)

Lemma isweq_imp_linv {X Y : UU} (f : X → Y) : isweq f → ∑ g, ∏ x, g(f x) = x.
Proof.
  intro isweq_f; unfold isweq in isweq_f.
  use tpair.
  - exact (λ y, pr11 (isweq_f y)).
  - cbn.

Theorem compisweq {X Y Z : UU} (f : X -> Y) (g : Y -> Z)
        (isf : isweq f) (isg : isweq g) : isweq (g ∘ f).
Proof.
  (* Fix z : Z, and construct a basepoint xx for the homotopy fiber of (g ∘ f) over z. *)
  intro z; assert (vv : hfiber (g ∘ f) z).

  - (* First we have a canonical basepoint of (hfiber g z). *)
    assert (yy : hfiber g z).
    {
      use tpair.
      exact (pr1 (pr1 (isg z))).
      cbn; exact (pr2 (pr1 (isg z))).
    }

    (* From this we get a canonical y : Y and py : g y = z. *)
    destruct yy as [y py].

    (* Then we have a canonical xx : hfiber f y, which splits into x : X and px : f x = y. *)
    assert (xx : hfiber f y).
    {
      use tpair.
      exact (pr1 (pr1 (isf y))).
      cbn; exact (pr2 (pr1 (isf y))).
    }
    destruct xx as [x px].

    (* Then x, together with a suitable equality constructed from px and py,
       is a basepoint for (hfiber (g ∘ f) z). *)
    exact (x ,, pathscomp0 (maponpaths g px) py).

  - (* Now we show contractibility, claiming that all (uu : hfiber (g ∘ f) z) are equal to vv. *)
    exists vv.
    intro uu; destruct vv as [x px]; destruct uu as [u pu].

    (* To show equality of pairs it suffices to show the relevant equalities on their components: *)
    Print hfiber.

    About total2_paths2_f.
    Search (isweq _ → _).

(** Package this up as an equivalence *)
Definition weqcomp {X Y Z : UU} (w1 : X ≃ Y) (w2 : Y ≃ Z) : X ≃ Z.
Abort.
