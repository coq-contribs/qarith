Require Export QArith_base.
Require Import Ring.
Require Export Setoid_ring.

Definition Qeq_bool (x y : Q) :=
  if Qeq_dec x y then fun _ => true else fun _ => false.

Lemma Qeq_bool_correct : forall x y : Q, Qeq_bool x y = true -> Qeq x y.
intros x y; unfold Qeq_bool in |- *; case (Qeq_dec x y); simpl in |- *; auto.
intros _ H; inversion H.
Qed.

Definition Qsrt : Setoid_Ring_Theory Qeq Qplus Qmult Qone Qzero Qopp Qeq_bool.
Proof.
constructor.
exact Qplus_sym.
exact Qplus_assoc.
exact Qmult_sym.
exact Qmult_assoc.
intro; setoid_rewrite (Qplus_sym Qzero n); apply Qzero_right.
intro; setoid_rewrite (Qmult_sym Qone n); apply Qmult_n_1.
exact Qplus_inverse_r.
intros; setoid_rewrite (Qmult_sym (Qplus n m) p);
 setoid_rewrite (Qmult_sym n p); setoid_rewrite (Qmult_sym m p);
 apply Qmult_plus_distr_r; auto.
unfold Is_true in |- *; intros x y; generalize (Qeq_bool_correct x y);
 case (Qeq_bool x y); auto.
Qed.

Add Setoid Ring Q Qeq Q_Setoid Qplus Qmult Qone Qzero Qopp Qeq_bool
 Qplus_comp Qmult_comp Qopp_comp Qsrt
 [ Qmake (*inject_Z*)  Zpos 0%Z Zneg xI xO 1%positive ].

(* Exemple of use: *)

Goal
forall x y z : Q, Qeq (Qmult (Qplus x y) z) (Qplus (Qmult x z) (Qmult y z)).
intros.
ring.
Abort.

Goal forall x y : Q, Qeq (Qplus x y) (Qplus y x).
intros. 
ring.
Abort.

Goal forall x y z : Q, Qeq (Qplus (Qplus x y) z) (Qplus x (Qplus y z)).
intros.
ring.
Abort.

Goal Qeq (Qplus (inject_Z 1) (inject_Z 1)) (inject_Z 2).
ring.
Abort.

Goal Qeq (Qplus Qone Qone) (Qmake 2 1).
ring.
Abort.

Goal forall x : Q, Qeq (Qminus x x) Qzero.
intro.
ring.
Abort.
