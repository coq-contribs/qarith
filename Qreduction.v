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


Require Export QArith_base.
Require Export Znumtheory.

(* First, a function that (tries to) build a positive back from a Z. *)

Definition Z2P (z : Z) :=
  match z with
  | Z0 => 1%positive
  | Zpos p => p
  | Zneg p => p
  end.

Lemma Z2P_correct : forall z : Z, (0 < z)%Z -> Zpos (Z2P z) = z.
Proof.
 simple destruct z; simpl in |- *; auto; intros; discriminate.
Qed.

Lemma Z2P_correct2 : forall z : Z, 0%Z <> z -> Zpos (Z2P z) = Zabs z.
Proof.
 simple destruct z; simpl in |- *; auto; intros; elim H; auto.
Qed.

(* Simplification of fractions using the Zgcd. *)

Definition Qred (q : Q) :=
  let (q1, q2) := q in
  let (r1,r2) := snd (Zgcd_gen q1 (Zpos q2)) in r1#(Z2P r2).

Lemma Qred_correct : forall q, (Qred q) == q.
Proof.
intros (n, d); unfold Qred, Qeq in |- *; simpl in |- *.
unfold Zgcd_gen in |- *.
destruct (Zgcd_gen_spec n (Zpos d)) as ((g,(nn,dd)),(_,(H1,(H2,H3)))).
simpl.
rewrite H2.
rewrite H3.
assert (0%Z <> g).
  intro. 
  elim H1; intros.
  rewrite <- H in H3.
  simpl in H3; inversion H3.

assert (0 < dd)%Z.
  apply Zmult_gt_0_lt_0_reg_r with g.
  omega.
  rewrite Zmult_comm.
  rewrite <- H3; compute; auto.
rewrite Z2P_correct; auto.
ring.
Qed.

Lemma Qred_complete : forall p q,  p==q -> Qred p = Qred q.
Proof.
intros (a, b) (c, d); unfold Qeq in |- *; simpl in |- *.
Open Scope Z_scope.
unfold Zgcd_gen in |- *.
destruct (Zgcd_gen_spec a (Zpos b)) as ((g,(aa,bb)),(Hg1,(Hg2,(Hg3,Hg4)))).
destruct (Zgcd_gen_spec c (Zpos d)) as ((g',(cc,dd)),(Hg'1,(Hg'2,(Hg'3,Hg'4)))).
simpl; intros.
assert (g <> 0).
  intro. 
  elim Hg2; intros.
  subst g.
  simpl in Hg4; inversion Hg4.
assert (g' <> 0).
  intro. 
  elim Hg'2; intros.
  subst g'.
  simpl in Hg'4; inversion Hg'4.
elim (rel_prime_cross_prod aa bb cc dd).
congruence.
unfold rel_prime in |- *.
(*rel_prime*)
constructor.
exists aa; auto with zarith.
exists bb; auto with zarith.
intros.
inversion Hg1.
destruct (H6 (g*x)).
rewrite Hg3.
destruct H2 as (xa,Hxa); exists xa; rewrite Hxa; ring.
rewrite Hg4.
destruct H3 as (xb,Hxb); exists xb; rewrite Hxb; ring.
exists q.
apply Zmult_reg_l with g; auto.
pattern g at 1; rewrite H7; ring.
(* /rel_prime *)
unfold rel_prime in |- *.
(* rel_prime *)
constructor.
exists cc; auto with zarith.
exists dd; auto with zarith.
intros.
inversion Hg'1.
destruct (H6 (g'*x)).
rewrite Hg'3.
destruct H2 as (xc,Hxc); exists xc; rewrite Hxc; ring.
rewrite Hg'4.
destruct H3 as (xd,Hxd); exists xd; rewrite Hxd; ring.
exists q.
apply Zmult_reg_l with g'; auto.
pattern g' at 1; rewrite H7; ring.
(* /rel_prime *)
assert (0<bb); [|auto with zarith].
  apply Zmult_gt_0_lt_0_reg_r with g.
  omega.
  rewrite Zmult_comm.
  rewrite <- Hg4; compute; auto.
assert (0<dd); [|auto with zarith].
  apply Zmult_gt_0_lt_0_reg_r with g'.
  omega.
  rewrite Zmult_comm.
  rewrite <- Hg'4; compute; auto.
apply Zmult_reg_l with (g'*g).
intro H2; elim (Zmult_integral _ _ H2); auto.
replace (g'*g*(aa*dd)) with ((g*aa)*(g'*dd)); [|ring].
replace (g'*g*(bb*cc)) with ((g'*cc)*(g*bb)); [|ring].
rewrite <- Hg3; rewrite <- Hg4; rewrite <- Hg'3; rewrite <- Hg'4; auto.
Open Scope Q_scope.
Qed.

Add Morphism Qred : Qred_comp. 
Proof.
intros q q' H.
rewrite (Qred_correct q); auto.
rewrite (Qred_correct q'); auto.
Qed.

Definition Qplus' (p q : Q) := Qred (Qplus p q).
Definition Qmult' (p q : Q) := Qred (Qmult p q). 

Lemma Qplus'_correct : forall p q : Q, Qeq (Qplus' p q) (Qplus p q).
Proof.
intros; unfold Qplus' in |- *; apply Qred_correct; auto.
Qed.

Lemma Qmult'_correct : forall p q : Q, Qeq (Qmult' p q) (Qmult p q).
Proof.
intros; unfold Qmult' in |- *; apply Qred_correct; auto.
Qed.

Add Morphism Qplus' : Qplus'_comp.
Proof.
intros; unfold Qplus' in |- *.
rewrite H; rewrite H0; auto with qarith.
Qed.

Add Morphism Qmult' : Qmult'_comp.
intros; unfold Qmult' in |- *.
rewrite H; rewrite H0; auto with qarith.
Qed.
