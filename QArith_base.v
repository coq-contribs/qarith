
(** Summary:
   Definition of Q -set of rationals- as pair of <p,n> with p:Z and n:positive.
*)

Require Export ZArith.
Require Export ZArithRing.
Require Export Setoid.

(** The definition of Q. *)

Record Q : Set := Qmake {Qnum : Z; Qden : positive}.

Delimit Scope Q_scope with Q.
Bind Scope Q_scope with Q.
Arguments Scope Qmake [Z_scope positive_scope].
Open Scope Q_scope.

Notation "a # b" := (Qmake a b) (at level 20, no associativity) : Q_scope.

Definition inject_Z (x : Z) := Qmake x 1. 

Notation QDen := (fun q => Zpos (Qden q)).
(* Notation Qzero := (Qmake 0 1). *)
(* Notation Qone := (Qmake 1 1). *)

Definition Qeq (p q : Q) := (Qnum p * QDen q)%Z = (Qnum q * QDen p)%Z.
Definition Qle (x y : Q) := (Qnum x * QDen y <= Qnum y * QDen x)%Z.
Definition Qlt (x y : Q) := (Qnum x * QDen y < Qnum y * QDen x)%Z.
Notation Qgt := (fun x y : Q => Qlt y x).
Notation Qge := (fun x y : Q => Qle y x).

Infix "==" := Qeq (at level 70, no associativity) : Q_scope. 
Infix "<" := Qlt : Q_scope.
Infix "<=" := Qle : Q_scope.
Infix ">" := Qgt : Q_scope. 
Infix ">=" := Qge : Q_scope. 
Notation "x <= y <= z" := (x<=y/\y<=z) : Q_scope.


Hint Unfold Qeq Qle Qlt: qarith.

(* Properties of equality. *)

Theorem Qeq_refl : forall x, x == x.
Proof.
 auto with qarith.
Qed.

Theorem Qeq_sym : forall x y, x == y -> y == x. 
Proof.
 auto with qarith.
Qed.

Hint Extern 5 (?X1 <> ?X2) => intro; discriminate: qarith.

Theorem Qeq_trans : forall x y z, x == y -> y == z -> x == z.
Proof.
unfold Qeq in |- *; intros.
apply Zmult_reg_l with (QDen y). 
auto with qarith.
ring; rewrite H; ring.
rewrite Zmult_assoc; rewrite H0; ring.
Qed.

(* Furthermore, this equality is decidable: *)

Theorem Qeq_dec : forall x y, {x==y} + {~ x==y}.
Proof.
 intros; case (Z_eq_dec (Qnum x * QDen y) (Qnum y * QDen x)); auto.
Defined.

(* We now consider Q seen as a setoid. *)

Definition Q_Setoid : Setoid_Theory Q Qeq.
Proof.
 split; unfold Qeq in |- *; auto; apply Qeq_trans.
Qed.

Add Setoid Q Qeq Q_Setoid as Qsetoid.

Hint Resolve (Seq_refl Q Qeq Q_Setoid): qarith.
Hint Resolve (Seq_sym Q Qeq Q_Setoid): qarith.
Hint Resolve (Seq_trans Q Qeq Q_Setoid): qarith.

(* The addition, multiplication and opposite are defined 
   in the straightforward way: *)

Definition Qplus (x y : Q) :=
  (Qnum x * QDen y + Qnum y * QDen x) # (Qden x * Qden y).

Definition Qmult (x y : Q) := (Qnum x * Qnum y) # (Qden x * Qden y). 

Definition Qopp (x : Q) := (- Qnum x) # (Qden x).

Definition Qminus (x y : Q) := Qplus x (Qopp y).

Definition Qinv (x : Q) :=
  match Qnum x with
  | Z0 => 0#1
  | Zpos p => (QDen x)#p
  | Zneg p => (Zneg (Qden x))#p
  end.

Definition Qdiv (x y : Q) := Qmult x (Qinv y).

Infix "+" := Qplus : Q_scope.
Notation "- x" := (Qopp x) : Q_scope.
Infix "-" := Qminus : Q_scope.
Infix "*" := Qmult : Q_scope.
Notation "/ x" := (Qinv x) : Q_scope. 
Infix "/" := Qdiv : Q_scope. 

Lemma times2mult : forall p q : positive, Zpos (p * q) = (Zpos p * Zpos q)%Z.
Proof.
 auto with zarith.
Qed.

Ltac Kill_times := repeat rewrite times2mult.

Add Morphism Qplus : Qplus_comp. 
unfold Qeq, Qplus in |- *; simpl in |- *.
intros (p1, p2) (q1, q2) H (r1, r2) (s1, s2) H0; simpl in H, H0 |- *.
Kill_times; ring.
assert (E1 : (p1 * (Zpos s2 * Zpos q2))%Z = (p1 * Zpos q2 * Zpos s2)%Z);
 [ ring | rewrite E1; rewrite H ].
assert (E2 : (Zpos s2 * (Zpos q2 * r1))%Z = (r1 * Zpos s2 * Zpos q2)%Z);
 [ ring | rewrite E2; rewrite H0 ].
ring.
Qed.

Add Morphism Qopp : Qopp_comp.
unfold Qeq, Qopp in |- *; simpl in |- *.
intros; ring; rewrite H; ring.
Qed.

Add Morphism Qminus : Qminus_comp.
intros.
unfold Qminus in |- *. 
setoid_rewrite H; setoid_rewrite H0; auto with qarith.
Qed.

Add Morphism Qmult : Qmult_comp.
unfold Qeq in |- *; simpl in |- *.
intros (p1, p2) (q1, q2) H (r1, r2) (s1, s2) H0; simpl in H, H0 |- *.
intros; Kill_times; ring.
assert (E1 : (Zpos p2 * (q1 * s1))%Z = (q1 * Zpos p2 * s1)%Z);
 [ ring | rewrite E1; rewrite <- H ].
assert (E2 : (Zpos s2 * (Zpos q2 * r1))%Z = (r1 * Zpos s2 * Zpos q2)%Z);
 [ ring | rewrite E2; rewrite H0 ].
ring.
Qed.

Add Morphism Qinv : Qinv_comp.
unfold Qeq, Qinv in |- *; simpl in |- *.
intros (p1, p2) (q1, q2); simpl in |- *.
case p1; simpl in |- *.
intros. 
assert (q1 = 0%Z).
 elim (Zmult_integral q1 (Zpos p2)); auto with zarith.
 intros; discriminate.
subst; auto. 
case q1; simpl in |- *; intros; try discriminate.
rewrite (Pmult_comm p2 p); rewrite (Pmult_comm q2 p0); auto.
case q1; simpl in |- *; intros; try discriminate.
rewrite (Pmult_comm p2 p); rewrite (Pmult_comm q2 p0); auto.
Qed.

Add Morphism Qdiv : Qdiv_comp.
intros; unfold Qdiv in |- *.
setoid_rewrite H; setoid_rewrite H0; auto with qarith.
Qed.

Add Morphism Qle : Qle_comp.
cut (forall x1 x2: Q, Qeq x1 x2 -> forall x3 x4: Q, Qeq x3 x4 -> Qle x1 x3 -> Qle x2 x4).
split; apply H; assumption || (apply Qeq_sym ; assumption).

unfold Qeq, Qle in |- *; simpl in |- *.
intros (p1, p2) (q1, q2) H (r1, r2) (s1, s2) H0; simpl in H, H0 |- *.
intros.
apply Zmult_le_reg_r with (Zpos p2).
unfold Zgt in |- *; auto.
assert (E1 : (q1 * Zpos s2 * Zpos p2)%Z = (q1 * Zpos p2 * Zpos s2)%Z);
 [ ring | rewrite E1; rewrite <- H ].
apply Zmult_le_reg_r with (Zpos r2).
unfold Zgt in |- *; auto.
assert
 (E2 :
  (s1 * Zpos q2 * Zpos p2 * Zpos r2)%Z = (s1 * Zpos r2 * Zpos q2 * Zpos p2)%Z);
 [ ring | rewrite E2; rewrite <- H0 ].
assert
 (E3 :
  (p1 * Zpos q2 * Zpos s2 * Zpos r2)%Z =
  (Zpos q2 * Zpos s2 * (p1 * Zpos r2))%Z); [ ring | rewrite E3 ].
assert
 (E4 :
  (r1 * Zpos s2 * Zpos q2 * Zpos p2)%Z =
  (Zpos q2 * Zpos s2 * (r1 * Zpos p2))%Z); [ ring | rewrite E4 ].
auto with zarith.
Qed.

Add Morphism Qlt : Qlt_comp.
cut (forall x1 x2: Q, Qeq x1 x2 -> forall x3 x4: Q, Qeq x3 x4 -> Qlt x1 x3 -> Qlt x2 x4).
split; apply H; assumption || (apply Qeq_sym ; assumption).

unfold Qeq, Qlt in |- *; simpl in |- *.
intros (p1, p2) (q1, q2) H (r1, r2) (s1, s2) H0; simpl in H,H0 |- *.
intros.
apply Zgt_lt.
generalize (Zlt_gt _ _ H1); clear H1; intro H1.
apply Zmult_gt_reg_r with (Zpos p2); auto with zarith.
assert (E1 : (q1 * Zpos s2 * Zpos p2)%Z = (q1 * Zpos p2 * Zpos s2)%Z);
 [ ring | rewrite E1; rewrite <- H ].
apply Zmult_gt_reg_r with (Zpos r2); auto with zarith.
assert
 (E2 :
  (s1 * Zpos q2 * Zpos p2 * Zpos r2)%Z = (s1 * Zpos r2 * Zpos q2 * Zpos p2)%Z);
 [ ring | rewrite E2; rewrite <- H0 ].
assert
 (E3 :
  (p1 * Zpos q2 * Zpos s2 * Zpos r2)%Z =
  (Zpos q2 * Zpos s2 * (p1 * Zpos r2))%Z); [ ring | rewrite E3 ].
assert
 (E4 :
  (r1 * Zpos s2 * Zpos q2 * Zpos p2)%Z =
  (Zpos q2 * Zpos s2 * (r1 * Zpos p2))%Z); [ ring | rewrite E4 ].
apply Zlt_gt.
apply Zmult_gt_0_lt_compat_l; auto with zarith.
Qed.

(* More properties of addition. *)

Theorem Qplus_simpl : forall n m p q, n == m -> p == q -> n+p == m+q. 
Proof.
 intros; setoid_rewrite H; setoid_rewrite H0; auto with qarith.
Qed.

(* Addition is associative: *)

Theorem Qplus_assoc : forall x y z, x+(y+z)==(x+y)+z.
Proof.
 intros (x1, x2) (y1, y2) (z1, z2).
 unfold Qeq, Qplus in |- *; simpl in |- *; repeat rewrite times2mult; ring.
Qed.

(* [Qzero] is a neutral element for addition: *)

Theorem Qzero_right : forall x, (x+ 0#1)==x.
Proof.
 intros (x1, x2); unfold Qeq, Qplus in |- *; simpl in |- *.
 rewrite Pmult_comm; simpl in |- *; ring.
Qed. 

(* Commutativity of addition: *)

Theorem Qplus_sym : forall x y, x+y == y+x.
Proof.
 intros (x1, x2); unfold Qeq, Qplus in |- *; simpl in |- *.
 intros; rewrite Pmult_comm; ring.
Qed.

(*  Qopp is a well defined unary operation: *)

Lemma Qopp_simpl : forall x y, x==y -> -x == -y.
Proof.
 intros; setoid_rewrite H; auto with qarith.
Qed.

(* The group equation for Qopp *)

Theorem Qplus_inverse_r : forall q, q+(-q) == 0#1.
Proof.
 red in |- *; simpl in |- *; intro; ring.
Qed.

(** Multiplication. *)

Theorem Qmult_simpl :  forall n m p q, n==m -> p==q -> n*p==m*q. 
Proof.
 intros; setoid_rewrite H; setoid_rewrite H0; auto with qarith.
Qed.


(* Qmult is associative: *)

Theorem Qmult_assoc : forall n m p, n*(m*p)==(n*m)*p.
Proof.
 intros; red in |- *; simpl in |- *; rewrite Pmult_assoc; ring.
Qed.

(* Qone is a neutral element for multiplication: *)

Theorem Qmult_n_1 : forall n, n*(1#1)==n.
Proof.
 intro; red in |- *; simpl in |- *.
 rewrite Zmult_1_r with (n := Qnum n).
 rewrite Pmult_comm; simpl in |- *; trivial. 
Qed.

(* The commutativity for Qmult: *)

Theorem Qmult_sym : forall x y, x*y==y*x.
Proof.
 intros; red in |- *; simpl in |- *; rewrite Pmult_comm; ring.
Qed.

Theorem Qmult_plus_distr_r : forall x y z, x*(y+z)==(x*y)+(x*z).
Proof.
intros (x1, x2) (y1, y2) (z1, z2).
unfold Qeq, Qmult, Qplus in |- *; simpl in |- *; Kill_times; ring.
Qed.

(* Here we prove that Qone is not equal to Qzero: *)

Theorem Qone_neq_Qzero : ~ 1#1 == 0#1.
Proof.
 unfold Qeq in |- *; auto with qarith.
Qed.

(* A property of multiplication which says if [x<>0] and [x*y=0] then [y=0]: *)

Theorem Qmult_eq : forall x y, ~ x == 0#1 -> x*y == 0#1 -> y == 0#1.
Proof.
 intros (x1, x2) (y1, y2).
 unfold Qeq, Qmult in |- *; simpl in |- *; intros.
 apply Zmult_integral_l with x1; auto with zarith.
 rewrite <- H0.
 ring.
Qed.

(** Inverse and division. *) 

Theorem Qinv_Qmult : forall x, ~ x == 0#1 -> x*(/x) == 1#1.
Proof.
 intros (x1, x2); unfold Qeq, Qdiv, Qmult in |- *; case x1; simpl in |- *;
  intros; Kill_times; try ring.
 elim H; auto. 
Qed.

Theorem Qmult_Qdiv : forall x y, ~ y == 0#1 -> (x*y)/y == x.
Proof.
 intros; unfold Qdiv in |- *.
 setoid_rewrite <- (Qmult_assoc x y (Qinv y)).
 setoid_rewrite (Qinv_Qmult y H).
 apply Qmult_n_1.
Qed.

Theorem Qdiv_Qmult : forall x y, ~ y == 0#1 -> y*(x/y) == x.
Proof.
 intros; unfold Qdiv in |- *.
 setoid_rewrite (Qmult_assoc y x (Qinv y)).
 setoid_rewrite (Qmult_sym y x).
 fold (Qdiv (Qmult x y) y) in |- *.
 apply Qmult_Qdiv; auto.
Qed.

(** Properties of order upon Q. *)

Lemma Qle_refl : forall x, x<=x.
Proof.
unfold Qle in |- *; auto with zarith.
Qed.

Lemma Qle_antisym : forall x y, x<=y -> y<=x -> x==y.
Proof.
unfold Qle, Qeq in |- *; auto with zarith.
Qed.

Lemma Qle_trans : forall x y z, x<=y -> y<=z -> x<=z.
Proof.
unfold Qle in |- *; intros (x1, x2) (y1, y2) (z1, z2); simpl in |- *; intros.
apply Zmult_le_reg_r with (Zpos y2).
red in |- *; trivial.
apply Zle_trans with (y1 * Zpos x2 * Zpos z2)%Z.
replace (x1 * Zpos z2 * Zpos y2)%Z with (x1 * Zpos y2 * Zpos z2)%Z;
 [ idtac | ring ].
apply Zmult_le_compat_r; auto with zarith. 
replace (y1 * Zpos x2 * Zpos z2)%Z with (y1 * Zpos z2 * Zpos x2)%Z;
 [ idtac | ring ].
replace (z1 * Zpos x2 * Zpos y2)%Z with (z1 * Zpos y2 * Zpos x2)%Z;
 [ idtac | ring ].
apply Zmult_le_compat_r; auto with zarith. 
Qed.

Lemma Qlt_not_eq : forall x y, x<y -> ~ x==y.
Proof.
unfold Qlt, Qeq in |- *; auto with zarith.
Qed.

Lemma Qlt_trans : forall x y z, x<y -> y<z -> x<z.
Proof.
unfold Qlt in |- *; intros (x1, x2) (y1, y2) (z1, z2); simpl in |- *; intros.
apply Zgt_lt.
apply Zmult_gt_reg_r with (Zpos y2).
red in |- *; trivial.
apply Zgt_trans with (y1 * Zpos x2 * Zpos z2)%Z.
replace (y1 * Zpos x2 * Zpos z2)%Z with (y1 * Zpos z2 * Zpos x2)%Z;
 [ idtac | ring ].
replace (z1 * Zpos x2 * Zpos y2)%Z with (z1 * Zpos y2 * Zpos x2)%Z;
 [ idtac | ring ].
apply Zmult_gt_compat_r; auto with zarith. 
replace (x1 * Zpos z2 * Zpos y2)%Z with (x1 * Zpos y2 * Zpos z2)%Z;
 [ idtac | ring ].
apply Zmult_gt_compat_r; auto with zarith. 
Qed.

(** [x<y] iff [~(y<=x)] *)

Lemma not_Qlt : forall x y, ~ x<y -> y<=x.
Proof.
unfold Qle, Qlt in |- *; auto with zarith.
Qed.

Lemma not_Qle : forall x y, ~ x<=y -> y<x.
Proof.
unfold Qle, Qlt in |- *; auto with zarith.
Qed.

Lemma Qlt_not_le : forall x y, x<y -> ~ y<=x.
Proof.
unfold Qle, Qlt in |- *; auto with zarith.
Qed.

Lemma Qle_not_lt : forall x y, x<=y -> ~ y<x.
Proof.
unfold Qle, Qlt in |- *; auto with zarith.
Qed.

(** Large = strict or equal *)

Lemma Qlt_le_weak : forall x y, x<y -> x<=y.
Proof.
unfold Qle, Qlt in |- *; auto with zarith.
Qed.

Lemma Qle_lt_or_eq : forall x y, x<=y -> x<y \/ x==y.
Proof.
unfold Qle, Qlt, Qeq in |- *; intros; apply Zle_lt_or_eq; auto.
Qed.

(** Some decidability results about orders. *)

Lemma Q_dec : forall x y, {x<y} + {y<x} + {x==y}.
Proof.
unfold Qlt, Qle, Qeq in |- *; intros.
exact (Z_dec' (Qnum x * Zpos (Qden y)) (Qnum y * Zpos (Qden x))).
Defined.

Lemma Qlt_le_dec : forall x y, {x<y} + {y<=x}.
Proof.
unfold Qlt, Qle in |- *; intros.
exact (Z_lt_le_dec (Qnum x * QDen y) (Qnum y * QDen x)).
Defined.

(** Compatibility of operations with respect to order. *)

Lemma Qle_plus_compat :
 forall x y z t, x<=y -> z<=t -> x+z <= y+t.
Proof.
unfold Qplus, Qle in |- *; intros (x1, x2) (y1, y2) (z1, z2) (t1, t2);
 simpl in |- *; Kill_times.
intros.
ring ((x1 * Zpos z2 + z1 * Zpos x2) * (Zpos y2 * Zpos t2))%Z.
ring ((y1 * Zpos t2 + t1 * Zpos y2) * (Zpos x2 * Zpos z2))%Z.
apply Zplus_le_compat.
replace (Zpos t2 * (Zpos y2 * (z1 * Zpos x2)))%Z with
 (z1 * Zpos t2 * (Zpos y2 * Zpos x2))%Z.
replace (Zpos z2 * (Zpos x2 * (t1 * Zpos y2)))%Z with
 (t1 * Zpos z2 * (Zpos y2 * Zpos x2))%Z.
apply Zmult_le_compat_r; auto with zarith.
ring.
ring.
replace (Zpos t2 * (Zpos y2 * (Zpos z2 * x1)))%Z with
 (x1 * Zpos y2 * (Zpos z2 * Zpos t2))%Z.
replace (Zpos z2 * (Zpos x2 * (Zpos t2 * y1)))%Z with
 (y1 * Zpos x2 * (Zpos z2 * Zpos t2))%Z.
apply Zmult_le_compat_r; auto with zarith.
ring.
ring.
Qed.

Lemma Qle_mult_compat : forall x y z, 0#1 <  z  -> x <= y -> x*z <= y*z.
intros (a1,a2) (b1,b2) (c1,c2); unfold Qle, Qlt; simpl.
replace (Zpos (b2*c2)) with (Zpos b2*Zpos c2)%Z; auto with zarith.
replace (Zpos (a2*c2)) with (Zpos a2*Zpos c2)%Z; auto with zarith.
replace (a1*c1*(Zpos b2*Zpos c2))%Z with ((a1*Zpos b2)*(c1*Zpos c2))%Z.
replace (b1*c1*(Zpos a2*Zpos c2))%Z with ((b1*Zpos a2)*(c1*Zpos c2))%Z.
intros; apply Zmult_le_compat_r; auto with zarith.
ring.
ring.
Qed.

Lemma Qle_mult_compat2 : forall x y z, 0#1 <  z  -> x*z <= y*z -> x <= y.
intros (a1,a2) (b1,b2) (c1,c2); unfold Qle, Qlt; simpl.
replace (Zpos (b2*c2)) with (Zpos b2*Zpos c2)%Z; auto with zarith.
replace (Zpos (a2*c2)) with (Zpos a2*Zpos c2)%Z; auto with zarith.
replace (a1*c1*(Zpos b2*Zpos c2))%Z with ((a1*Zpos b2)*(c1*Zpos c2))%Z.
replace (b1*c1*(Zpos a2*Zpos c2))%Z with ((b1*Zpos a2)*(c1*Zpos c2))%Z.
intros; apply Zmult_le_reg_r with (c1*Zpos c2)%Z; auto with zarith.
ring.
ring.
Qed.
