Require Import Ring.
Require Export Setoid_ring.
Require Export QArith_base.

Definition Qeq_bool (x y : Q) :=
  if Qeq_dec x y then true else false.

Lemma Qeq_bool_correct : forall x y : Q, Qeq_bool x y = true -> x==y.
intros x y; unfold Qeq_bool in |- *; case (Qeq_dec x y); simpl in |- *; auto.
intros _ H; inversion H.
Qed.

Definition Qone := 1#1.
Definition Qzero := 0#1.

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

Lemma Qring_example1 : 
 forall x y z : Q, (x+y)*z ==  (x*z)+(y*z).
intros.
ring.
Qed.

Lemma Qring_example2 : forall x y : Q, x+y == y+x.
intros. 
ring.
Qed.

Lemma Qring_example3 : forall x y z : Q, (x+y)+z == x+(y+z).
intros.
ring.
Qed.

Lemma Qring_example4 : (inject_Z 1)+(inject_Z 1)==(inject_Z 2).
ring.
Qed.

Lemma Qring_example5 : Qone+Qone ==2#1.
ring.
Qed.

Lemma Qring_example6 : 1#1+1#1 == 2#1.
ring.
Qed.

Lemma Qring_example7 : forall x : Q, x-x== 0#1.
intro.
ring.
Qed.
