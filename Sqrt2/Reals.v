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

Notation " !2^ y" := (two_power_nat y) (at level 30).
Coercion inject_Z : Z >-> Q.

(**** A quick & dirty implementation of constructive reals. ****)
(****      Based on Pr. Schwichtenberg lecture notes.        ****)
(****      Main objective: sqrt(2) as root of X^2 -2  in [1;2]   ****) 

(* First, the Cauchy property. *)

Definition Is_Cauchy (f : nat -> Q) (mo : nat -> nat) :=
  forall k m n,  (mo k <= m)%nat -> (mo k <= n)%nat ->
  let e:=(f m - f n)*!2^k in  -1 <= e <= 1.

(* A real is given by a cauchy sequence, a modulus sequence *)
(* and a proof of the Cauchy property of these sequences. *)

Record R : Set := {
  cauchy : nat -> Q; 
  modulus : nat -> nat; 
  is_cauchy : Is_Cauchy cauchy modulus }.

(* Recursive Extraction R. *)

(* A rational is injected into R via a constant cauchy sequence. *)

Definition inject_Q : Q -> R.
intros q.
apply (Build_R (fun _ => q) (fun _ => O)).
red; intros.
assert ((q-q)*!2^k==0#1).
ring.
setoid_rewrite H1.
unfold Qle, Zle; simpl; intuition; inversion H2.
Defined.

(* Extraction inject_Q. *)

(* The non-computational equality upon R. *)

Definition Req : R -> R -> Prop:= 
    fun x y : R => 
      forall k, let M := modulus x (S k) in 
            let N := modulus y (S k) in 
            let e := (cauchy x M - cauchy y N)*!2^k in 
            -1 <= e <= 1.         

(* The informative positivity upon R. *)

Definition Rpos_k : nat -> R -> Prop :=
  fun k x => -1 <= (cauchy x (modulus x (S k)))*!2^k.

Definition Rpos : R -> Set := fun x => { k:nat | Rpos_k k x }.

(* The logical non-negativity upon R. *)

Definition Rnonneg : R -> Prop := 
 fun x => forall k:nat, -1 <= (cauchy x (modulus x k))*!2^k.

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

Lemma two_power_S : forall k, !2^(S k) = (2 *(!2^k))%Z.
intros. 
rewrite <- two_power_nat_S; auto with zarith.
Qed.

Lemma max_le : forall a b c, le (max a b) c -> le a c /\ le b c.
eauto with arith.
Qed.

Definition Rplus : R -> R -> R.
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
rewrite two_power_S in H5; rewrite two_power_S in H6.
destruct H5; destruct H6.

assert (((Xm+Ym-(Xn+Yn)) * !2^k) * 2%Z == 
                ((Xm-Xn) * (2%Z*!2^k))+((Ym-Yn) * (2%Z*!2^k))).
ring.

split.

apply Qle_mult_compat2 with 2%Z.
unfold Qlt; simpl; omega.
replace (-1 * 2%Z) with (-1 + -1); simpl; auto.
setoid_rewrite H3.
apply Qle_plus_compat; auto.

apply Qle_mult_compat2 with 2%Z.
unfold Qlt; simpl; omega.
replace (1 * 2%Z) with (1+1); simpl; auto.
setoid_rewrite H3.
apply Qle_plus_compat; auto.
Defined.

(* Extraction Rplus. *)

Definition Ropp : R -> R.
intros x.
apply (Build_R (fun n => -(cauchy x n)) (fun k => modulus x k)).
unfold Is_Cauchy; intros.
unfold Qminus.
setoid_rewrite (Qopp_opp (cauchy x n)).
setoid_rewrite (Qplus_sym (-(cauchy x m)) (cauchy x n)).
apply (is_cauchy x k n m); auto.
Defined.

Definition Rminus : R -> R -> R := fun x y => Rplus x (Ropp y).

Definition Rlt : R -> R -> Set := fun x y => Rpos (Rminus y x). 

Definition Rle : R -> R -> Prop := fun x y => Rnonneg (Rminus y x).

(* An alternative characterization of positivity upon R. *)

Definition Rpos_alt (x:R) := 
 {l:nat & { p:nat | forall n, le p n -> 1 <= (cauchy x n)*!2^l}}.

Lemma Rpos_alt_1 : forall x:R, Rpos x -> Rpos_alt x.
unfold Rpos, Rpos_k, Rpos_alt.
intros.
elim H; intros k Hk; clear H.
exists (S k).
exists (modulus x (S k)).
intros.
fedup.
Defined.

Lemma Rpos_alt_2 : forall x, Rpos_alt x -> Rpos x.
unfold Rpos, Rpos_k, Rpos_alt.
intros.
elim H; intros l Hl; elim Hl; intros p Hp; clear H Hl.
exists (S l).
fedup.
Defined.


(* The Key Lemma: comparison between three reals. *)

Definition Rcompare : forall x y, Rlt x y -> forall z, Rlt x z + Rlt z y.
unfold Rlt; intros.
generalize (Rpos_alt_1 _ H); clear H; intros H.
elim H; intros k Hk; elim Hk; intros p Hp; clear H Hk.
set (k' := S (S k)).
set (k'' := S (S k)).
set (q := (max (modulus x k'') (max (modulus y k'') (max (modulus z k'') p)))).
elim (Qlt_le_dec ((cauchy z q - cauchy x q)*!2^k') 2); intros.
right.
exists k'.
fedup.
left.
exists k'.
fedup.
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

Lemma two_p_correct : forall n, !2^n = two_p (Z_of_nat n).
destruct n.
simpl; auto.
unfold Z_of_nat, two_p.
rewrite two_power_pos_nat.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ; auto.
Qed.

(* The strict order is conserved when injecting Q in R. *)

Lemma Qlt_Rlt : forall a b, a<b -> Rlt (inject_Q a) (inject_Q b).
intros a b; exists (nat_log_sup ((Qden b)*(Qden a))).
unfold Rpos_k.
unfold inject_Q; simpl; auto.
generalize H; unfold Qle, Qlt; simpl; auto with zarith.
intros.
rewrite two_p_correct.
rewrite log_sup_log_sup.
set (ab := (Qden b * Qden a)%positive) in *.
set (baab := ((Qnum b)*(Zpos (Qden a))+(-(Qnum a))*(Zpos (Qden b)))%Z) in *.
elim (log_sup_correct2 ab); intros; clear H1.
assert (1 <= baab)%Z.
unfold baab; rewrite <- Zopp_mult_distr_l; omega.
rewrite Zmult_1_r.
apply Zle_trans with (1*Zpos ab)%Z.
compute; intro h; inversion h.
apply Zmult_le_compat; auto with zarith.
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
       -1 <= (a-b)*(!2^(pred (cont_w k))) <= 1 -> 
       -1 <= (cont_h a n - cont_h b n)*!2^k <= 1
}.

Definition one_two : itvl. 
apply (Build_itvl 1 2 ).
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
   unfold c, d; setoid_rewrite (Qred_correct ((2#3)*a+(1#3)*b)). 
   setoid_rewrite (Qred_correct  ((1#3)*a+(2#3)*b)).
   generalize ab; unfold c, d, Qlt, Qmult, Qplus, Qnum, Qden.
   case a; intros a1 a2; case b; intros b1 b2.
   kill_times; set (A2 := Zpos a2) in *; set (B2 := Zpos b2) in *.
   intros.
   apply Zlt_left_rev.
   match goal with |- ( ?e1 < ?e2)%Z => ring e1; ring e2 end.
   replace (-27*(B2*(B2*(A2*a1))) + 27*(B2*(A2*(A2*b1))))%Z
   with ((27*B2*A2)*(b1*A2) + - ((27*B2*A2)*(a1*B2)))%Z.
   apply Zlt_left_lt.
   apply Zmult_lt_compat_l; auto.
   kill_times; unfold Zlt; auto with zarith.
   ring.  
set (fc := sqr2_apply (inject_Q c)).
set (fd := sqr2_apply (inject_Q d)).
assert (fcfd : Rlt fc fd).
  unfold fc, fd; apply sqr2_incr.
  fedup.
  fedup.
 apply Qlt_Rlt; auto.
case (Rcompare fc fd fcfd (inject_Q (0))); intros.
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

