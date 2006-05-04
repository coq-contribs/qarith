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


Require Export Max.
Require Export Zpower.
Require Export Zlogarithm.
Require Export QArith.

Coercion inject_Z : Z >-> Q.

(**** A quick & dirty implementation of constructive reals. ****)
(****      Based on Pr. Schwichtenberg lecture notes.        ****)
(****      Main objective: sqrt(2) as root of X^2 -2  in [1;2]   ****) 

(* First, the Cauchy property. *)

Definition Is_Cauchy (f : nat -> Q) (mo : nat -> nat) :=
  forall k m n,  (mo k <= m)%nat -> (mo k <= n)%nat ->
  -(1#2)^k <= f m - f n <= (1#2)^k.

(* A real is given by a cauchy sequence, a modulus sequence *)
(* and a proof of the Cauchy property of these sequences. *)

Record R : Set := {
  cauchy : nat -> Q; 
  modulus : nat -> nat; 
  is_cauchy : Is_Cauchy cauchy modulus }.

(* Recursive Extraction R. *)

(* A rational is injected into R via a constant cauchy sequence. *)

Definition inject_Q : Q -> R.
Proof.
intros q.
apply (Build_R (fun _ => q) (fun _ => O)).
red; intros.
assert (H1: q-q == 0) by ring.
rewrite H1; clear H1.
assert (0 <= (1#2)^k).
 apply Qpower_le_0. 
 compute; intro; discriminate.
split; auto.
replace 0 with (-0) by auto.
apply Qle_opp; auto.
Defined.

(* Extraction inject_Q. *)

(* The non-computational equality upon R. *)

Definition Req : R -> R -> Prop:= 
    fun x y : R => 
      forall k, let M := modulus x (S k) in 
            let N := modulus y (S k) in 
            -(1#2)^k <= cauchy x M - cauchy y N <= (1#2)^k.         

(* The informative positivity upon R. *)

Definition Rpos_k : nat -> R -> Prop :=
  fun k x => (1#2)^k <= cauchy x (modulus x (S k)).

Definition Rpos : R -> Set := fun x => { k:nat | Rpos_k k x }.

(* The logical non-negativity upon R. *)

Definition Rnonneg : R -> Prop := 
 fun x => forall k:nat, -(1#2)^k <= cauchy x (modulus x k).

(* The Dirty Part: *)

(**** Beware! Use with caution! Not for kids! ****)
Axiom Falsum: False.
Ltac fedup := elim Falsum.
(*****************************************************)

Definition test : R -> R -> R.
fedup.
Qed.
(* Extraction test. *)

(* Addition on R. *)
(* Only the informative parts are provided. 
    The logical statement is skipped. *)

(*
Lemma two_power_S : forall k, !2^(S k) = (2 *(!2^k))%Z.
intros. 
rewrite <- two_power_nat_S; auto with zarith.
Qed.
*)

Lemma max_le : forall a b c, le (max a b) c -> le a c /\ le b c.
Proof.
eauto with arith.
Qed.

Definition Rplus : R -> R -> R.
Proof.
intros x y.
apply (Build_R (fun n => cauchy x n + cauchy y n)
                          (fun k => max (modulus x (S k)) (modulus y (S k)))).
unfold Is_Cauchy; intros.
set (N := modulus x (S k)) in *.
set (M := modulus y (S k)) in *.
elim (max_le N M m H); elim (max_le N M n H0); intros.
assert (H5 := is_cauchy x (S k) m n H3 H1).
assert (H6 := is_cauchy y (S k) m n H4 H2).
clear N M H H0 H1 H2 H3 H4.
set (Xn := cauchy x n) in *; set (Xm := cauchy x m) in *; 
set (Yn := cauchy y n) in *; set (Ym := cauchy y m) in *.
destruct H5; destruct H6.
assert ((Xm+Ym-(Xn+Yn)) == ((Xm-Xn) +(Ym-Yn))) by ring.
rewrite H3; clear H3.
assert ((1#2)^(S k) + (1#2)^(S k) == (1#2)^k) by simpl; ring.
split.

apply Qle_trans with (- (1#2)^(S k)+ -(1#2)^(S k)).
rewrite <- Qopp_plus.
apply Qle_opp.
rewrite H3; clear H3; apply Qle_refl.
apply Qle_plus_compat; auto.

apply Qle_trans with ((1#2)^(S k) + (1#2)^(S k)).
apply Qle_plus_compat; auto.
rewrite H3; clear H3; apply Qle_refl.
Defined.

(* Extraction Rplus. *)

Definition Ropp : R -> R.
intros x.
apply (Build_R (fun n => -(cauchy x n)) (fun k => modulus x k)).
unfold Is_Cauchy; intros.
unfold Qminus.
rewrite (Qopp_opp (cauchy x n)).
rewrite (Qplus_sym (-(cauchy x m)) (cauchy x n)).
apply (is_cauchy x k n m); auto.
Defined.

Definition Rminus : R -> R -> R := fun x y => Rplus x (Ropp y).

Definition Rlt : R -> R -> Set := fun x y => Rpos (Rminus y x). 

Definition Rle : R -> R -> Prop := fun x y => Rnonneg (Rminus y x).

(* An alternative characterization of positivity upon R. *)

Definition Rpos_alt (x:R) := 
 {l:nat & { p:nat | forall n, (p<=n)%nat -> (1#2)^l <= cauchy x n}}.

Lemma Rpos_alt_1 : forall x:R, Rpos x -> Rpos_alt x.
Proof.
unfold Rpos, Rpos_k, Rpos_alt.
intros.
elim H; intros k Hk; clear H.
exists (S k).
exists (modulus x (S k)).
intros.
(*fedup.*)
destruct (x.(is_cauchy) (S k) n (modulus x (S k))) as (Hx,_); auto.
assert (H0:=Qle_plus_compat _ _ _ _ Hk Hx).
assert (H1 : cauchy x (modulus x (S k)) + (cauchy x n - cauchy x (modulus x (S k)))
            == cauchy x n) by ring. 
revert H0; rewrite H1; clear H1; intros. (* BUG rewrite in *)
assert ((1 # 2) ^ k + - (1 # 2) ^ S k == (1#2)^(S k)) by simpl; ring.
revert H0; rewrite H1; clear H1; intros. (* BUG rewrite in *)
auto.
Defined.

Lemma Rpos_alt_2 : forall x, Rpos_alt x -> Rpos x.
unfold Rpos, Rpos_k, Rpos_alt.
intros.
elim H; intros l Hl; elim Hl; intros p Hp; clear H Hl.
exists (S l).
(*fedup.*)
set (M:=modulus x (S (S l))).
set (N:=max p M).
destruct (x.(is_cauchy) (S (S l)) M N) as (Hx,_); auto. 
unfold N, M; auto with arith.
apply Qle_trans with ((1#2)^l+(-(1#2)^(S (S l)))).
setoid_replace ((1#2)^l + (- (1 # 2) ^(S (S l)))) with ((3#4)*(1#2)^l); [|simpl; ring].
simpl; apply Qle_mult_compat.
apply Qpower_le_0; compute; intro; discriminate.
compute; intro; discriminate.
setoid_replace (cauchy x M) with (cauchy x N +(cauchy x M - cauchy x N)); [|ring].
apply Qle_plus_compat; auto.
apply Hp; unfold N; auto with arith.
Defined.




(* The Key Lemma: comparison between three reals. *)

Definition Rcompare : forall x y, Rlt x y -> forall z, Rlt x z + Rlt z y.
unfold Rlt; intros.
destruct (Rpos_alt_1 _ H) as (k,(p,Hp)); clear H.
set (k' := S (S k)).
set (k'' := S (S k')).
set (q := max (modulus x k'') (max (modulus y k'') (max (modulus z k'') p))).
destruct (Qlt_le_dec (cauchy z q - cauchy x q)  ((1#2)^(S k))); 
 [right|left]; exists k'.
(*fedup.*)
red; simpl cauchy; simpl cauchy in Hp.
set (q' := max (modulus y (S (S k'))) (modulus z (S (S k')))).
destruct (z.(is_cauchy) k'' q q') as (Hz,_); auto. 
unfold q, k''; eauto with arith.
unfold q', k''; auto with arith.
destruct (y.(is_cauchy) k'' q' q) as (Hy,_); auto. 
unfold q', k''; auto with arith.
unfold q, k''; eauto with arith.
assert (p <= q)%nat by unfold q; eauto with arith.
assert (H0:=Hp q H); clear Hp H. 
assert (H1:=Qle_opp _ _ (Qlt_le_weak _ _ q0)); clear q0.
set (Yq' := cauchy y q') in *; set (Yq := cauchy y q) in *; 
 set (Zq' := cauchy z q') in *; set (Zq := cauchy z q) in *; 
 set (Xq := cauchy x q) in *; clearbody q q' Yq Yq' Zq Zq' Xq.
generalize (Qle_plus_compat _ _ _ _ Hy
                   (Qle_plus_compat _ _ _ _ H0 
                       (Qle_plus_compat _ _ _ _ H1 Hz))).
assert ((1#2)^k' == (1#4)*(1#2)^k) by simpl; ring.
rewrite H; clear H.
assert ((1#2)^k'' == (1#16)*(1#2)^k) by simpl; ring.
rewrite H; clear H.
simpl.
match goal with |- ?a <= ?b -> _ => 
 setoid_replace b with (Yq'+-Zq'); [|ring];
 setoid_replace a with ((-(1#16)+1-(1#2)+-(1#16))*(1#2)^k); [|ring]; 
 setoid_replace (-(1#16)+1-(1#2)+-(1#16)) with (3#8); [|compute; auto]
end. (* Pourquoi ring ne marche sur le dernier bout ? *)
intros.
apply Qle_trans with ((3#8)*(1#2)^k); auto.
apply Qle_mult_compat.
apply Qpower_le_0; compute; intro; discriminate.
compute; intro; discriminate.
(*fedup.*)
red; simpl cauchy; simpl cauchy in Hp.
set (q' := max (modulus z (S (S k'))) (modulus x (S (S k')))).
destruct (z.(is_cauchy) k'' q' q) as (Hz,_); auto. 
unfold q', k''; auto with arith.
unfold q, k''; eauto with arith.
destruct (x.(is_cauchy) k'' q q') as (Hx,_); auto. 
unfold q, k''; eauto with arith.
unfold q', k''; auto with arith.
clear Hp.
set (Xq' := cauchy x q') in *; set (Xq := cauchy x q) in *; 
 set (Zq' := cauchy z q') in *; set (Zq := cauchy z q) in *; 
 clearbody q q' Xq Xq' Zq Zq'.
generalize (Qle_plus_compat _ _ _ _ Hz
                   (Qle_plus_compat _ _ _ _ q0 Hx)).
assert ((1#2)^k' == (1#4)*(1#2)^k) by simpl; ring.
rewrite H; clear H.
assert ((1#2)^k'' == (1#16)*(1#2)^k) by simpl; ring.
rewrite H; clear H.
simpl.
match goal with |- ?a <= ?b -> _ => 
 setoid_replace b with (Zq'+-Xq'); [|ring];
 setoid_replace a with ((-(1#16)+(1#2)+-(1#16))*(1#2)^k); [|ring]; 
 setoid_replace (-(1#16)+(1#2)+-(1#16)) with (3#8); [|compute; auto]
end. (* Pourquoi ring ne marche sur le dernier bout ? *)
intros.
apply Qle_trans with ((3#8)*(1#2)^k); auto.
apply Qle_mult_compat.
apply Qpower_le_0; compute; intro; discriminate.
compute; intro; discriminate.
Defined.

(* Specialized continuity components for sqr2 = X^2-2 *)

Definition sqr2 := fun a => (a * a)+(-2).
Definition sqr2_h := fun a (_:nat) => sqr2 a.
Definition sqr2_alpha := fun (_:nat) => O.
Definition sqr2_w := fun k => S (S (S k)).

(* Specialized application of sqr2 to a real. *)

Definition sqr2_apply : R -> R. 
intros x. 
apply (Build_R (fun n => sqr2_h (cauchy x n) n) 
                       (fun k => max (sqr2_alpha (S (S k))) 
                                        (modulus x (pred (sqr2_w (S k)))))).
unfold Is_Cauchy, sqr2_h, sqr2_alpha, sqr2_w; simpl; intros.
fedup.  
Defined.

(* sqr2 is strictly increasing at least on interval [1;infinity] *)

Definition sqr2_incr : forall x y, Rle (inject_Q 1) x -> Rle (inject_Q 1) y -> 
  Rlt x y -> Rlt (sqr2_apply x) (sqr2_apply y).
unfold Rlt; intros.
apply Rpos_alt_2.
generalize (Rpos_alt_1 _ H1); clear H1.
unfold Rpos_alt, Rminus, Ropp, Rplus; simpl; unfold sqr2_h; simpl.
intro H1; elim H1; intros k Hk; elim Hk; intros p Hp; clear H Hk.
exists (pred k).
exists p.
intros.
generalize (Hp _ H); clear Hp H; intros.
fedup.
Qed.

Lemma One_lt_Two : Rlt (inject_Q 1) (inject_Q 2).
exists O.
unfold Rpos_k.
unfold inject_Q; simpl; auto.
unfold Qle; simpl; auto with zarith.
Qed.

Require Import nat_log.

Lemma two_p_correct : forall n, 2^n = two_p (Z_of_nat n).
Proof.
induction n.
simpl; auto.
simpl.
rewrite IHn; clear IHn.
unfold Z_of_nat, two_p.
destruct n.
simpl; auto.
simpl.
set (p:=P_of_succ_nat n).
unfold two_power_pos.
do 2 rewrite shift_pos_nat; unfold shift_nat.
rewrite nat_of_P_succ_morphism; simpl; auto.
Qed.

(** a enlever apres debug de rewrite et ring. *)
Lemma Qhalf_power_n : forall n, (1#2)^n == 1/2^n.
Proof.
induction n.
compute; auto.
simpl.
(* unfold Qdiv in IHn; rewrite Qmult_1_n in IHn.*) (*BUUG*)
rewrite IHn; clear IHn.
unfold Qdiv; rewrite Qmult_Qinv.
do 2 rewrite Qmult_1_n; ring. (* ring seul devrait gagner ... *)
Qed.

(* The strict order is conserved when injecting Q in R. *)

Lemma Qlt_Rlt : forall a b, a<b -> Rlt (inject_Q a) (inject_Q b).
intros a b; exists (nat_log_sup ((Qden b)*(Qden a))).
unfold Rpos_k.
unfold inject_Q; simpl; auto.
rewrite Qinv_power_n.
rewrite  two_p_correct.
rewrite log_sup_log_sup.
set (ab := (Qden b * Qden a)%positive) in *.
assert ('ab <= two_p (log_sup ab)).
 red; simpl; kill_times; destruct (log_sup_correct2 ab) as (_,H0); omega.
apply Qle_mult_compat2 with (two_p (log_sup ab)).
apply Qlt_le_trans with ('ab); [compute|]; auto.
rewrite Qmult_sym.
rewrite Qinv_Qmult.
intro; rewrite H1 in H0; compute in H0; auto.
rewrite Qmult_sym.
apply Qle_trans with ('ab*(b+-a)); [|
 apply Qle_mult_compat; auto; 
 rewrite <- Qle_minus; apply Qlt_le_weak; auto].
unfold ab; red; simpl.
set (baab := ((Qnum b)*'(Qden a)+-(Qnum a)*'(Qden b))%Z).
assert (1 <= baab)%Z.
 unfold baab; rewrite <- Zopp_mult_distr_l; red in H; omega.
destruct baab.
(*baab = 0*)
elim H1; auto.
(*baab>0*)
kill_times.
rewrite Zmult_1_r.
assert (H2:=Zmult_le_compat (' Qden b * ' Qden a) 1 (' Qden b * ' Qden a) ('p)).
rewrite Zmult_1_r in H2.
apply H2; auto.
apply Zle_refl.
compute; intro; discriminate.
compute; intro; discriminate.
(*baab<0*)
elim H1; auto.
Qed.

(* Main part: we now build a sequence of nested intervals 
   containing sqrt(2). *)

Record itvl : Set := { lft : Q ; rht : Q ; lft_rht : lft<rht}.
(*Print itvl. *)
(*Check itvl.*)

Definition two_three: itvl.
apply (Build_itvl 2 3).
unfold Qlt; simpl; auto with zarith.
Qed.

(*Check two_three.*)
(*Check (lft two_three).*)
(*Check lft_rht.*)
(*Check (lft_rht two_three).*)

Record itvl2: Set:= {lft1:Q; rht1:Q; lft2:Q; rht2:Q; lft1_rht1: lft1<rht1; lft2_rht2: lft2<rht2}.

Definition in_itvl := fun i x => lft i <= x <= rht i.
Definition in_itvl2 := fun i x =>  lft1 i<=x<=rht1 i /\ lft2 i<=x<=rht2 i.
 
Record continuous (i:itvl) : Set := {
   cont_h : Q -> nat -> Q; 
   cont_alpha : nat -> nat;
   cont_w : nat -> nat; 
   cont_cauchy: forall a, Is_Cauchy (cont_h a) cont_alpha;    
   cont_unif : forall a b n k, le n (cont_alpha k) -> in_itvl i a -> in_itvl i b ->   
       -(1#2)^(pred (cont_w k)) <= a-b <= (1#2)^(pred (cont_w k)) -> 
       -(1#2)^k <= cont_h a n - cont_h b n <= (1#2)^k
}.

Definition one_two : itvl. 
apply (Build_itvl 1 2).
unfold Qlt; simpl; auto with zarith.
Qed.

Definition sqr2_cont : continuous one_two.
apply (Build_continuous one_two sqr2_h sqr2_alpha sqr2_w).
fedup. 
fedup.
Qed.

Require Zcomplements.

(* Coercion Zpos : positive >-> Z. *)

Definition sqrt2_approx : nat -> itvl.
induction 1. 
apply (Build_itvl 1 2); unfold Qlt; simpl; omega.
elim IHnat; intros a b ab.
set (c:= (Qred ((2#3)*a+(1#3)*b))).
set (d:= (Qred ((1#3)*a+(2#3)*b))).
assert (cd : c<d).
   unfold c, d.
   rewrite Qlt_minus in ab |- *.
   rewrite (Qred_correct ((2#3)*a+(1#3)*b)). 
   rewrite (Qred_correct  ((1#3)*a+(2#3)*b)).
   setoid_replace ((1 # 3) * a + (2 # 3) * b + - ((2 # 3) * a + (1 # 3) * b))
   with ((b+-a)*((2#3)-(1#3))); [|ring].
   setoid_replace ((2#3)-(1#3)) with (1#3); [|compute; auto].
   setoid_replace 0 with (0*(1#3)); [|compute;auto].
   apply Qlt_mult_compat; [compute|]; auto.
set (fc := sqr2_apply (inject_Q c)).
set (fd := sqr2_apply (inject_Q d)).
assert (fcfd : Rlt fc fd).
  unfold fc, fd; apply sqr2_incr.
  fedup.
  fedup.
 apply Qlt_Rlt; auto.
case (Rcompare fc fd fcfd (inject_Q 0)); intros.
apply (Build_itvl c b).
  fedup.
apply (Build_itvl a d).
  fedup.
Qed.

(* The cauchy sequence giving sqrt(2) is finally obtained 
    by the left borders of these intervals. *)

Definition sqrt2: R. 
apply (Build_R (fun n => lft (sqrt2_approx n)) (fun k => plus k k)).
fedup.
Qed.

Extraction Inline Zcompare_rec Z_lt_rec.
Extraction "sqrt2.ml" sqrt2.

