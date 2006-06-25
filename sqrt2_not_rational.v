Require Import QArith.

Ltac mysimpl := simplify_eq; repeat rewrite Pmult_xO_permute_r. 

Theorem main_thm: forall p q: positive, (p*p <> 2*(q*q))%positive.
Proof.
induction p; simpl; intro; mysimpl.
destruct q; mysimpl; firstorder.
Qed.

Coercion inject_Z : Z >-> Q.

Theorem sqrt2_not_rational : forall q:Q, ~ q^2 == 2.
Proof.
intros (a,b).
unfold Qeq, Qpower, Qmult; simpl.
repeat rewrite Zmult_1_r; rewrite Pmult_1_r.
destruct a as [|a|a]; simpl; simplify_eq; exact (main_thm a b).
Qed.