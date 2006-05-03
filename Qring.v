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
intro; rewrite Qplus_sym; apply Qzero_right.
intro; rewrite Qmult_sym; apply Qmult_n_1.
exact Qplus_inverse_r.
intros; rewrite Qmult_sym;
 rewrite (Qmult_sym n p); rewrite (Qmult_sym m p);
 apply Qmult_plus_distr_r; auto.
unfold Is_true; intros x y; generalize (Qeq_bool_correct x y);
 case (Qeq_bool x y); auto.
Qed.

Add Setoid Ring Q Qeq Q_Setoid Qplus Qmult Qone Qzero Qopp Qeq_bool
 Qplus_comp Qmult_comp Qopp_comp Qsrt
 [ Qmake (*inject_Z*)  Zpos 0%Z Zneg xI xO 1%positive ].

(* Exemple of use: *)

Section Examples. 

Let ex1 : forall x y z : Q, (x+y)*z ==  (x*z)+(y*z).
intros.
ring.
Qed.

Let ex2 : forall x y : Q, x+y == y+x.
intros. 
ring.
Qed.

Let ex3 : forall x y z : Q, (x+y)+z == x+(y+z).
intros.
ring.
Qed.

Let ex4 : (inject_Z 1)+(inject_Z 1)==(inject_Z 2).
ring.
Qed.

Let ex5 : Qone+Qone ==2#1.
ring.
Qed.

Let ex6 : 1#1+1#1 == 2#1.
ring.
Qed.

Let ex7 : forall x : Q, x-x== 0#1.
intro.
ring.
Qed.

End Examples.
