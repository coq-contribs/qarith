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
  let g := Zgcd (Zpos q2) q1 in Qmake (q1 / g) (Z2P (Zpos q2 / g)).

Lemma Qred_correct : forall q : Q, Qeq (Qred q) q.
intros (n, d); unfold Qred, Qeq in |- *; simpl in |- *.
unfold Zgcd in |- *; case (Zgcd_spec (Zpos d) n); intros g.
intuition.
elim H; intros.
assert (0%Z <> g).
  intro. 
  elim H1; intros.
  rewrite <- H4 in H5.
  rewrite Zmult_comm in H5; inversion H5.

assert (0 < Zpos d / g)%Z.
  apply Zmult_gt_0_lt_0_reg_r with g.
  omega.
  rewrite Zmult_comm.
  rewrite <- Z_div_exact_2; auto with zarith.
  compute in |- *; auto.
  apply Zdivide_mod; auto with zarith.
rewrite Z2P_correct; auto.
pattern n at 2 in |- *.
rewrite (Z_div_exact_2 n g); try apply Zdivide_mod; auto with zarith.
pattern d at 2 in |- *.
rewrite (Z_div_exact_2 (Zpos d) g); try apply Zdivide_mod; auto with zarith.
ring.
Qed.

Lemma Qred_complete : forall p q : Q, Qeq p q -> Qred p = Qred q.
intros (a, b) (c, d); unfold Qeq in |- *; simpl in |- *.
unfold Zgcd in |- *; case (Zgcd_spec (Zpos b) a); intros g (Hg1, Hg2).
unfold Zgcd in |- *; case (Zgcd_spec (Zpos d) c); intros g' (Hg'1, Hg'2).
intros.
inversion Hg1.
inversion Hg'1.
assert (g <> 0%Z).
  intro. 
  elim H0; intros.
  subst g.
  rewrite Zmult_comm in H7; inversion H7.
assert (g' <> 0%Z).
  intro. 
  elim H3; intros.
  subst g'.
  rewrite Zmult_comm in H8; inversion H8.
rewrite (Z_div_exact_2 a g) in H; try apply Zdivide_mod; auto with zarith.
rewrite (Z_div_exact_2 (Zpos d) g') in H; try apply Zdivide_mod;
 auto with zarith.
rewrite (Z_div_exact_2 (Zpos b) g) in H; try apply Zdivide_mod;
 auto with zarith.
rewrite (Z_div_exact_2 c g') in H; try apply Zdivide_mod; auto with zarith.
elim (rel_prime_cross_prod (a / g) (Zpos b / g) (c / g') (Zpos d / g')).
intros.
rewrite H8; rewrite H9; auto.
unfold rel_prime in |- *; apply Zis_gcd_rel_prime; auto with zarith.
unfold rel_prime in |- *; apply Zis_gcd_rel_prime; auto with zarith.
apply Zmult_gt_0_reg_l with g.
omega.
rewrite <- Z_div_exact_2; try apply Zdivide_mod; auto with zarith.
apply Zmult_gt_0_reg_l with g'.
omega.
rewrite <- Z_div_exact_2; try apply Zdivide_mod; auto with zarith.
apply Zmult_reg_l with (g * g')%Z.
intro; elim (Zmult_integral _ _ H8); auto.
replace (g * g' * (a / g * (Zpos d / g')))%Z with
 (g * (a / g) * (g' * (Zpos d / g')))%Z.
rewrite H.
ring.
ring.
Qed.

Add Morphism Qred : Qred_comp. 
intros q q' H.
setoid_rewrite (Qred_correct q); auto.
setoid_rewrite (Qred_correct q'); auto.
Qed.

Definition Qplus' (p q : Q) := Qred (Qplus p q).
Definition Qmult' (p q : Q) := Qred (Qmult p q). 

Definition Qplus'_correct : forall p q : Q, Qeq (Qplus' p q) (Qplus p q).
intros; unfold Qplus' in |- *; apply Qred_correct; auto.
Qed.

Definition Qmult'_correct : forall p q : Q, Qeq (Qmult' p q) (Qmult p q).
intros; unfold Qmult' in |- *; apply Qred_correct; auto.
Qed.

Add Morphism Qplus' : Qplus'_comp.
intros; unfold Qplus' in |- *.
setoid_rewrite H; setoid_rewrite H0; auto with qarith.
Qed.

Add Morphism Qmult' : Qmult'_comp.
intros; unfold Qmult' in |- *.
setoid_rewrite H; setoid_rewrite H0; auto with qarith.
Qed.
