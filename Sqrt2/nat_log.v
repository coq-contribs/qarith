Require Import ZArith.
Require Import Zlogarithm.

Fixpoint nat_log_inf (p : positive) : nat :=
  match p with
  | xH => 0 (* 1 *)
  | xO q => S (nat_log_inf q) (* 2n *)
  | xI q => S (nat_log_inf q) (* 2n+1 *)
  end.

Fixpoint nat_log_sup (p : positive) : nat :=
  match p with
  | xH => 0 (* 1 *)
  | xO n => S (nat_log_sup n) (* 2n *)
  | xI n => S (S (nat_log_inf n)) (* 2n+1 *)
  end.

Lemma log_inf_log_inf :
 forall p : positive, Z_of_nat (nat_log_inf p) = log_inf p.
simple induction p; auto.
intros; simpl (nat_log_inf (xI p0)) in |- *; simpl (log_inf (xI p0)) in |- *.
rewrite <- H; apply Znat.inj_S.
intros; simpl (nat_log_inf (xO p0)) in |- *; simpl (log_inf (xO p0)) in |- *.
rewrite <- H; apply Znat.inj_S.
Qed.

Lemma log_sup_log_sup :
 forall p : positive, Z_of_nat (nat_log_sup p) = log_sup p.
simple induction p; auto.
intros; simpl (nat_log_sup (xI p0)) in |- *; simpl (log_sup (xI p0)) in |- *.
rewrite <- log_inf_log_inf; do 2 rewrite Znat.inj_S; auto.
intros; simpl (nat_log_sup (xO p0)) in |- *; simpl (log_sup (xO p0)) in |- *.
rewrite <- H; apply Znat.inj_S.
Qed.
