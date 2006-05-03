(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)



(** Summary:
   Definition of Q -set of rationals- as pair of <p,n> with p:Z and n:positive.
*)

Require Export ZArith.
Require Export ZArithRing.
Require Export Setoid.

(** A notation for [Zpos] *)

Notation " ' x " := (Zpos x) (at level 20, no associativity).

(** The definition of Q. *)

Record Q : Set := Qmake {Qnum : Z; Qden : positive}.

Delimit Scope Q_scope with Q.
Bind Scope Q_scope with Q.
Arguments Scope Qmake [Z_scope positive_scope].
Open Scope Q_scope.

Notation "a # b" := (Qmake a b) (at level 55, no associativity) : Q_scope.

Definition inject_Z (x : Z) := Qmake x 1. 

Notation QDen := (fun q => '(Qden q)).
Notation " 0 " := (0#1) : Q_scope.
Notation " 1 " := (1#1) : Q_scope.

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
  | Z0 => 0
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

Lemma times2mult : forall p q : positive, '(p * q) = ('p * 'q)%Z.
Proof.
 auto with zarith.
Qed.
 
Ltac kill_times := repeat rewrite times2mult.

Add Morphism Qplus : Qplus_comp. 
Proof.
unfold Qeq, Qplus; simpl.
Open Scope Z_scope.
intros (p1, p2) (q1, q2) H (r1, r2) (s1, s2) H0; simpl in *.
kill_times; ring.
replace (p1 * ('s2 * 'q2)) with (p1 * 'q2 * 's2) by ring.
rewrite H.
replace ('s2 * ('q2 * r1)) with (r1 * 's2 * 'q2) by ring.
rewrite H0.
ring.
Open Scope Q_scope.
Qed.

Add Morphism Qopp : Qopp_comp.
Proof.
unfold Qeq, Qopp; simpl.
intros; ring; rewrite H; ring.
Qed.

Add Morphism Qminus : Qminus_comp.
Proof.
intros.
unfold Qminus. 
rewrite H; rewrite H0; auto with qarith.
Qed.

Add Morphism Qmult : Qmult_comp.
Proof.
unfold Qeq; simpl.
Open Scope Z_scope.
intros (p1, p2) (q1, q2) H (r1, r2) (s1, s2) H0; simpl in *.
intros; kill_times; ring.
replace ('p2 * (q1 * s1)) with (q1 * 'p2 * s1) by ring.
rewrite <- H.
replace ('s2 * ('q2 * r1)) with (r1 * 's2 * 'q2) by ring.
rewrite H0.
ring.
Open Scope Q_scope.
Qed.

Add Morphism Qinv : Qinv_comp.
Proof.
unfold Qeq, Qinv; simpl.
Open Scope Z_scope.
intros (p1, p2) (q1, q2); simpl.
case p1; simpl.
intros. 
assert (q1 = 0).
 elim (Zmult_integral q1 ('p2)); auto with zarith.
 intros; discriminate.
subst; auto. 
case q1; simpl; intros; try discriminate.
rewrite (Pmult_comm p2 p); rewrite (Pmult_comm q2 p0); auto.
case q1; simpl; intros; try discriminate.
rewrite (Pmult_comm p2 p); rewrite (Pmult_comm q2 p0); auto.
Open Scope Q_scope.
Qed.


Add Morphism Qdiv : Qdiv_comp.
Proof.
intros; unfold Qdiv.
rewrite H; rewrite H0; auto with qarith.
Qed.

Add Morphism Qle with signature Qeq ==> Qeq ==> iff as Qle_comp.
Proof.
cut (forall x1 x2, x1==x2 -> forall x3 x4, x3==x4 -> x1<=x3 -> x2<=x4).
split; apply H; assumption || (apply Qeq_sym ; assumption).

unfold Qeq, Qle; simpl.
Open Scope Z_scope.
intros (p1, p2) (q1, q2) H (r1, r2) (s1, s2) H0 H1; simpl in *.
apply Zmult_le_reg_r with ('p2).
unfold Zgt; auto.
replace (q1 * 's2 * 'p2) with (q1 * 'p2 * 's2) by ring.
rewrite <- H.
apply Zmult_le_reg_r with ('r2).
unfold Zgt; auto.
replace (s1 * 'q2 * 'p2 * 'r2) with (s1 * 'r2 * 'q2 * 'p2) by ring.
rewrite <- H0.
replace (p1 * 'q2 * 's2 * 'r2) with ('q2 * 's2 * (p1 * 'r2)) by ring.
replace (r1 * 's2 * 'q2 * 'p2) with ('q2 * 's2 * (r1 * 'p2)) by ring.
auto with zarith.
Open Scope Q_scope.
Qed.

Add Morphism Qlt with signature Qeq ==> Qeq ==> iff as  Qlt_comp.
Proof.
cut (forall x1 x2, x1==x2 -> forall x3 x4, x3==x4 -> x1<x3 -> x2<x4).
split; apply H; assumption || (apply Qeq_sym ; assumption).

unfold Qeq, Qlt; simpl.
Open Scope Z_scope.
intros (p1, p2) (q1, q2) H (r1, r2) (s1, s2) H0 H1; simpl in *.
apply Zgt_lt.
generalize (Zlt_gt _ _ H1); clear H1; intro H1.
apply Zmult_gt_reg_r with ('p2); auto with zarith.
replace (q1 * 's2 * 'p2) with (q1 * 'p2 * 's2) by ring.
rewrite <- H.
apply Zmult_gt_reg_r with ('r2); auto with zarith.
replace (s1 * 'q2 * 'p2 * 'r2) with (s1 * 'r2 * 'q2 * 'p2) by ring.
rewrite <- H0.
replace (p1 * 'q2 * 's2 * 'r2) with ('q2 * 's2 * (p1 * 'r2)) by ring.
replace (r1 * 's2 * 'q2 * 'p2) with ('q2 * 's2 * (r1 * 'p2)) by ring. 
apply Zlt_gt.
apply Zmult_gt_0_lt_compat_l; auto with zarith.
Open Scope Q_scope.
Qed.

(* More properties of addition. *)

Theorem Qplus_simpl : forall n m p q, n == m -> p == q -> n+p == m+q. 
Proof.
 intros; rewrite H; rewrite H0; auto with qarith.
Qed.

(* Addition is associative: *)

Theorem Qplus_assoc : forall x y z, x+(y+z)==(x+y)+z.
Proof.
 intros (x1, x2) (y1, y2) (z1, z2).
 unfold Qeq, Qplus; simpl; repeat rewrite times2mult; ring.
Qed.

(* [Qzero] is a neutral element for addition: *)

Theorem Qzero_right : forall x, x+ 0 == x.
Proof.
 intros (x1, x2); unfold Qeq, Qplus; simpl.
 rewrite Pmult_comm; simpl; ring.
Qed. 

(* Commutativity of addition: *)

Theorem Qplus_sym : forall x y, x+y == y+x.
Proof.
 intros (x1, x2); unfold Qeq, Qplus; simpl.
 intros; rewrite Pmult_comm; ring.
Qed.

(*  Qopp is a well defined unary operation: *)

Lemma Qopp_simpl : forall x y, x==y -> -x == -y.
Proof.
 intros; rewrite H; auto with qarith.
Qed.

(* The group equation for Qopp *)

Theorem Qplus_inverse_r : forall q, q+(-q) == 0.
Proof.
 red; simpl; intro; ring.
Qed.

(** Multiplication. *)

Theorem Qmult_simpl :  forall n m p q, n==m -> p==q -> n*p==m*q. 
Proof.
 intros; rewrite H; rewrite H0; auto with qarith.
Qed.


(* Qmult is associative: *)

Theorem Qmult_assoc : forall n m p, n*(m*p)==(n*m)*p.
Proof.
 intros; red; simpl; rewrite Pmult_assoc; ring.
Qed.

(* Qone is a neutral element for multiplication: *)

Theorem Qmult_n_1 : forall n, n*1==n.
Proof.
 intro; red; simpl.
 rewrite Zmult_1_r with (n := Qnum n).
 rewrite Pmult_comm; simpl; trivial. 
Qed.

(* The commutativity for Qmult: *)

Theorem Qmult_sym : forall x y, x*y==y*x.
Proof.
 intros; red; simpl; rewrite Pmult_comm; ring.
Qed.

Theorem Qmult_plus_distr_r : forall x y z, x*(y+z)==(x*y)+(x*z).
Proof.
intros (x1, x2) (y1, y2) (z1, z2).
unfold Qeq, Qmult, Qplus; simpl; kill_times; ring.
Qed.

(* Here we prove that Qone is not equal to Qzero: *)

Theorem Qone_neq_Qzero : ~ 1 == 0.
Proof.
 unfold Qeq; auto with qarith.
Qed.

(* A property of multiplication which says if [x<>0] and [x*y=0] then [y=0]: *)

Theorem Qmult_eq : forall x y, ~ x == 0 -> x*y == 0 -> y == 0.
Proof.
 intros (x1, x2) (y1, y2).
 unfold Qeq, Qmult; simpl; intros.
 apply Zmult_integral_l with x1; auto with zarith.
 rewrite <- H0.
 ring.
Qed.

(** Inverse and division. *) 

Theorem Qinv_Qmult : forall x, ~ x == 0 -> x*(/x) == 1.
Proof.
 intros (x1, x2); unfold Qeq, Qdiv, Qmult; case x1; simpl;
  intros; kill_times; try ring.
 elim H; auto. 
Qed.

Theorem Qmult_Qdiv : forall x y, ~ y == 0 -> (x*y)/y == x.
Proof.
 intros; unfold Qdiv.
 rewrite <- (Qmult_assoc x y (Qinv y)).
 rewrite (Qinv_Qmult y H).
 apply Qmult_n_1.
Qed.

Theorem Qdiv_Qmult : forall x y, ~ y == 0 -> y*(x/y) == x.
Proof.
 intros; unfold Qdiv.
 rewrite (Qmult_assoc y x (Qinv y)).
 rewrite (Qmult_sym y x).
 fold (Qdiv (Qmult x y) y).
 apply Qmult_Qdiv; auto.
Qed.

(** Properties of order upon Q. *)

Lemma Qle_refl : forall x, x<=x.
Proof.
unfold Qle; auto with zarith.
Qed.

Lemma Qle_antisym : forall x y, x<=y -> y<=x -> x==y.
Proof.
unfold Qle, Qeq; auto with zarith.
Qed.

Lemma Qle_trans : forall x y z, x<=y -> y<=z -> x<=z.
Proof.
unfold Qle; intros (x1, x2) (y1, y2) (z1, z2); simpl; intros.
Open Scope Z_scope.
apply Zmult_le_reg_r with ('y2).
red; trivial.
apply Zle_trans with (y1 * 'x2 * 'z2).
replace (x1 * 'z2 * 'y2) with (x1 * 'y2 * 'z2) by ring.
apply Zmult_le_compat_r; auto with zarith. 
replace (y1 * 'x2 * 'z2) with (y1 * 'z2 * 'x2) by ring.
replace (z1 * 'x2 * 'y2) with (z1 * 'y2 * 'x2) by ring.
apply Zmult_le_compat_r; auto with zarith. 
Open Scope Q_scope.
Qed.

Lemma Qlt_not_eq : forall x y, x<y -> ~ x==y.
Proof.
unfold Qlt, Qeq; auto with zarith.
Qed.

Lemma Qlt_trans : forall x y z, x<y -> y<z -> x<z.
Proof.
unfold Qlt; intros (x1, x2) (y1, y2) (z1, z2); simpl; intros.
Open Scope Z_scope.
apply Zgt_lt.
apply Zmult_gt_reg_r with ('y2).
red; trivial.
apply Zgt_trans with (y1 * 'x2 * 'z2).
replace (y1 * 'x2 * 'z2) with (y1 * 'z2 * 'x2) by ring.
replace (z1 * 'x2 * 'y2) with (z1 * 'y2 * 'x2) by ring.
apply Zmult_gt_compat_r; auto with zarith. 
replace (x1 * 'z2 * 'y2) with (x1 * 'y2 * 'z2) by ring.
apply Zmult_gt_compat_r; auto with zarith. 
Open Scope Q_scope.
Qed.

(** [x<y] iff [~(y<=x)] *)

Lemma not_Qlt : forall x y, ~ x<y -> y<=x.
Proof.
unfold Qle, Qlt; auto with zarith.
Qed.

Lemma not_Qle : forall x y, ~ x<=y -> y<x.
Proof.
unfold Qle, Qlt; auto with zarith.
Qed.

Lemma Qlt_not_le : forall x y, x<y -> ~ y<=x.
Proof.
unfold Qle, Qlt; auto with zarith.
Qed.

Lemma Qle_not_lt : forall x y, x<=y -> ~ y<x.
Proof.
unfold Qle, Qlt; auto with zarith.
Qed.

(** Large = strict or equal *)

Lemma Qlt_le_weak : forall x y, x<y -> x<=y.
Proof.
unfold Qle, Qlt; auto with zarith.
Qed.

Lemma Qle_lt_or_eq : forall x y, x<=y -> x<y \/ x==y.
Proof.
unfold Qle, Qlt, Qeq; intros; apply Zle_lt_or_eq; auto.
Qed.

(** Some decidability results about orders. *)

Lemma Q_dec : forall x y, {x<y} + {y<x} + {x==y}.
Proof.
unfold Qlt, Qle, Qeq; intros.
exact (Z_dec' (Qnum x * '(Qden y)) (Qnum y * '(Qden x))).
Defined.

Lemma Qlt_le_dec : forall x y, {x<y} + {y<=x}.
Proof.
unfold Qlt, Qle; intros.
exact (Z_lt_le_dec (Qnum x * QDen y) (Qnum y * QDen x)).
Defined.

(** Compatibility of operations with respect to order. *)

Lemma Qle_plus_compat :
 forall x y z t, x<=y -> z<=t -> x+z <= y+t.
Proof.
unfold Qplus, Qle; intros (x1, x2) (y1, y2) (z1, z2) (t1, t2);
 simpl; kill_times.
Open Scope Z_scope.
intros.
match goal with |- ?a <= ?b => ring a; ring b end.
apply Zplus_le_compat.
replace ('t2 * ('y2 * (z1 * 'x2))) with (z1 * 't2 * ('y2 * 'x2)) by ring.
replace ('z2 * ('x2 * (t1 * 'y2))) with (t1 * 'z2 * ('y2 * 'x2)) by ring.
apply Zmult_le_compat_r; auto with zarith.
replace ('t2 * ('y2 * ('z2 * x1))) with (x1 * 'y2 * ('z2 * 't2)) by ring.
replace ('z2 * ('x2 * ('t2 * y1))) with (y1 * 'x2 * ('z2 * 't2)) by ring.
apply Zmult_le_compat_r; auto with zarith.
Open Scope Q_scope.
Qed.

Lemma Qle_mult_compat : forall x y z, 0 <=  z  -> x <= y -> x*z <= y*z.
Proof.
intros (a1,a2) (b1,b2) (c1,c2); unfold Qle, Qlt; simpl.
Open Scope Z_scope.
intros; kill_times.
replace (a1*c1*('b2*'c2)) with ((a1*'b2)*(c1*'c2)) by ring.
replace (b1*c1*('a2*'c2)) with ((b1*'a2)*(c1*'c2)) by ring.
apply Zmult_le_compat_r; auto with zarith.
Open Scope Q_scope.
Qed.

Lemma Qle_mult_compat2 : forall x y z, 0 <  z  -> x*z <= y*z -> x <= y.
Proof.
intros (a1,a2) (b1,b2) (c1,c2); unfold Qle, Qlt; simpl.
Open Scope Z_scope.
kill_times.
replace (a1*c1*('b2*'c2)) with ((a1*'b2)*(c1*'c2)) by ring.
replace (b1*c1*('a2*'c2)) with ((b1*'a2)*(c1*'c2)) by ring.
intros; apply Zmult_le_reg_r with (c1*'c2); auto with zarith.
Open Scope Q_scope.
Qed.


