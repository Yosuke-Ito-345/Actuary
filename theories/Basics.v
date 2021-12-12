Require Import Logic.Description Classical_sets Reals Lra Lia.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(****************************************************************************************)

Lemma S_addn : forall n:nat, n.+1 = (n+1)%N.
Proof.
    by rewrite /addn /addn_rec; lia.
Qed.      

Lemma iota_rcons : forall (m n : nat), rcons (iota m n) (m+n) = iota m (n+1).
Proof.
 by move => m n; rewrite -(cats0 (rcons _ _)) cat_rcons iotaD.
Qed.

Lemma iota_pttn : forall (n m : nat),
 [seq k | j <- iota 0 n, k <- iota (j*m) m] = iota 0 (n*m).
Proof.
 move => n; elim n => [// | p IHp].
 move => m.
 rewrite mulSn addnC iotaD add0n.
 rewrite -IHp.
 rewrite -flatten_rcons -(map_id (iota (p*m) m)) -map_rcons.
 by rewrite iota_rcons addn1.
Qed.

Lemma pairmap_pair1 : forall (T:Type) (n:nat) (f : nat -> T),
  pairmap (fun u v : T => (v,u)) (head (f 0) (mkseq f n.+1)) (behead (mkseq f n.+1))
    = [ seq (f i.+1, f i) | i <- seq.iota 0 n].
Proof.
  move => T; case => // p f.
  apply eq_from_nth with (x0 := (f 0, f 0));
    [ rewrite size_pairmap size_behead size_mkseq size_map size_iota; lia| ].
  case => //.
  case => [| j].
  - rewrite size_pairmap size_behead size_mkseq Nat.pred_succ => /ltP Hp.
    have Hp' : (0 < p)%coq_nat by lia.
    rewrite /=.
    rewrite (nth_pairmap (f 0)); [| by rewrite size_map size_iota; apply /ltP].
    rewrite !(nth_map 0); [| by rewrite size_iota; apply /ltP ..].
      by rewrite !nth_iota; [| by apply /ltP ..].
  - rewrite size_pairmap size_behead size_mkseq Nat.pred_succ => /ltP Hp.
    have Hj' : (j.+1 < p)%coq_nat by lia.
    rewrite /=.
    rewrite (nth_pairmap (f 0)) /=; [| by rewrite size_map size_iota; apply /ltP].
    rewrite !(nth_map 0); [| rewrite size_iota; apply /ltP; lia ..].
      by rewrite !nth_iota; [| apply /ltP; lia ..].
Qed.

Lemma pairmap_pair2 : forall (T:Type) (n:nat) (f : nat -> T),
  pairmap (fun u v : T => (v,v)) (head (f 0) (mkseq f n.+1)) (behead (mkseq f n.+1))
    = [ seq (f i.+1, f i.+1) | i <- seq.iota 0 n].
Proof.
  move => T; case => // p f.
  apply eq_from_nth with (x0 := (f 0, f 0));
    [ rewrite size_pairmap size_behead size_mkseq size_map size_iota; lia| ].
  case => //.
  case => [| j].
  - rewrite size_pairmap size_behead size_mkseq Nat.pred_succ => /ltP Hp.
    have Hp' : (0 < p)%coq_nat by lia.
    rewrite /=.
    rewrite (nth_pairmap (f 0)); [| by rewrite size_map size_iota; apply /ltP].
    rewrite !(nth_map 0); [| by rewrite size_iota; apply /ltP ..].
      by rewrite !nth_iota; [| by apply /ltP ..].
  - rewrite size_pairmap size_behead size_mkseq Nat.pred_succ => /ltP Hp.
    have Hj' : (j.+1 < p)%coq_nat by lia.
    rewrite /=.
    rewrite (nth_pairmap (f 0)) /=; [| by rewrite size_map size_iota; apply /ltP].
    rewrite !(nth_map 0); [| rewrite size_iota; apply /ltP; lia ..].
      by rewrite !nth_iota; [| apply /ltP; lia ..].
Qed.

Lemma INR_Ztonat_IZR : forall m:Z, (0 <= m)%Z -> INR (Z.to_nat m) = IZR m.
Proof.
  move => m Hm.
  rewrite INR_IZR_INZ.
  rewrite Z2Nat.id //.
Qed.

(****************************************************************************************)

From Coquelicot Require Import Coquelicot.

Coercion INR : nat >-> R.
Coercion IZR : Z >-> R.

Open Scope R_scope.

Infix ".^" := pow (at level 30, right associativity).
Infix "^" := Rpower : R_scope.

Reserved Notation "\Rsum_ ( m <= k < n | P ) F"
  (at level 41, F at level 41, k, m, n at level 50,
           format "'[' \Rsum_ ( m <= k < n | P ) '/  '  F ']'").
Reserved Notation "\Rsum_ ( m <= k < n ) F"
  (at level 41, F at level 41, k, m, n at level 50,
           format "'[' \Rsum_ ( m <= k < n ) '/  '  F ']'").
Notation "\Rsum_ ( m <= k < n | P ) F" :=
  (\big[Rplus/0]_(m <= k < n | P%B) F%R) : R_scope.
Notation "\Rsum_ ( m <= k < n ) F" :=
  (\big[Rplus/0]_(m <= k < n) F%R) : R_scope.

(* basic arithmetic *)

Lemma leastN : forall P : Ensemble nat,
  (exists n, P n) -> { m:nat | P m /\ forall n:nat, P n -> (m <= n)%coq_nat }.
Proof.
  move => P HPinh.
  case: (LPO P).
  - move => n; apply classic.
  - move => HPn.
    apply constructive_definite_description.
    apply dec_inh_nat_subset_has_unique_least_element; [move => n; apply classic | done].
  - move => HnotPn.
    exists 0%N.
    destruct HPinh as [n HPn].
      by contradict HPn.
Qed.

Lemma Rplus_assoc' : forall r1 r2 r3 : R, r1 + (r2 + r3) = r1 + r2 + r3.
Proof.
 by move=> r1 r2 r3; rewrite Rplus_assoc.
Qed.

Canonical Rplus_monoid := Monoid.Law Rplus_assoc' Rplus_0_l Rplus_0_r.
Canonical Rplus_monoid_RplusComm := Monoid.ComLaw Rplus_comm.
Canonical Rplus_monoid_Rmult := Monoid.MulLaw Rmult_0_l Rmult_0_r.
Canonical Rplus_monoid_RDistr := Monoid.AddLaw Rmult_plus_distr_r Rmult_plus_distr_l.

Lemma pos_neq0 : forall x:R, 0 < x -> x <> 0.
Proof.
 move => x; apply (Rgt_not_eq x 0).
Qed.

Hint Resolve pos_neq0 : core.

Lemma neg_neq0 : forall x:R, x < 0 -> x <> 0.
Proof.
 move => x; apply (Rlt_not_eq x 0).
Qed.

Hint Resolve neg_neq0 : core.

Lemma Sn_pos : forall n:nat, 0 < INR (n + 1).
Proof.
 move => n; rewrite plus_INR; apply INRp1_pos.
Qed.

Hint Resolve Sn_pos : core.

Lemma INR1_pos : 0 < INR 1.
Proof.
 by rewrite -(add0n 1%N).
Qed.

Hint Resolve INR1_pos : core.

Lemma Sn_neq0 : forall n:nat, INR (n + 1) <> 0.
Proof.
 move => n; auto.
Qed.

Hint Resolve Sn_neq0 : core.

Lemma one_pow : forall r:R, 1^r = 1.
Proof.
 move => r.
 rewrite /Rpower.
 rewrite ln_1 Rmult_0_r; apply exp_0.
Qed.

Lemma Rpower_2 : forall r:R, 0 < r -> r^2 = r*r.
Proof.
 move => r Hrpos.
 by rewrite -{-1}(Rpower_1 r) // -Rpower_plus.
Qed.

Lemma Ropp_r_simpl_l: forall r1 r2 : R, r2 + r1 - r1 = r2.
Proof.
 move => r1 r2.
 by rewrite /Rminus Rplus_assoc -/(Rminus _ r1) Rminus_eq_0 Rplus_0_r.
Qed.

Lemma Rmult_div_assoc : forall (r1 r2 r3 : R), r1 * r2 / r3 = r1 * (r2 / r3).
Proof.
  move => r1 r2 r3; lra.
Qed.

Lemma Finite_Rplus : forall r1 r2 : R, Finite (r1 + r2) = Rbar_plus (Finite r1) (Finite r2).
Proof.
  by move => r1 r2.
Qed.

Lemma Finite_Rminus : forall r1 r2 : R, Finite (r1 - r2) = Rbar_minus (Finite r1) (Finite r2).
Proof.
    by move => r1 r2.
Qed.

Lemma Finite_Rmult : forall r1 r2 : R, Finite (r1 * r2) = Rbar_mult (Finite r1) (Finite r2).
Proof.
  by move => r1 r2.
Qed.

Lemma Finite_Rinv : forall r:R, r <> 0 -> Finite (/r) = Rbar_inv r.
Proof.
    by move => r Hr.
Qed.

Lemma Rmult_opp1_l : forall r:R, (-1)*r = -r.
Proof.
  move => r; lra.
Qed.

Lemma Rmult_opp1_r : forall r:R, r*(-1) = -r.
Proof.
  move => r; lra.
Qed.

Lemma iter_Rplus : forall (n:nat) (a b : R), iter n (Rplus a) b = n*a + b.
Proof.
  induction n => a b;
    [rewrite /=; lra | rewrite [in LHS]/= IHn -Nat.add_1_r plus_INR /=; lra].
Qed.

Lemma Rabs_div : forall x y : R, y <> 0 -> Rabs (x / y) = Rabs x / Rabs y.
Proof.
  move => x y Hy.
  rewrite /Rdiv.
  rewrite Rabs_mult.
  rewrite Rabs_Rinv //.
Qed.

Lemma Rbar_mult_1_r : forall x : Rbar, Rbar_mult x 1 = x.
Proof.
 case.
   rewrite /= => r; by rewrite Rmult_1_r.
  rewrite /=; case Rle_dec; try lra => case Rle_dec; try lra;
  move=> Hle01; case Rle_lt_or_eq_dec => //; lra.
 rewrite /=; case Rle_dec; try lra => case Rle_dec; try lra;
 move=> Hle01; case Rle_lt_or_eq_dec => //; lra.
Qed.

Lemma Rbar_mult_1_l : forall x : Rbar, Rbar_mult 1 x = x.
Proof.
 case.
   rewrite /= => r; by rewrite Rmult_1_l.
  rewrite /=; case Rle_dec; try lra => case Rle_dec; try lra;
  move=> Hle01; case Rle_lt_or_eq_dec => //; lra.
 rewrite /=; case Rle_dec; try lra => case Rle_dec; try lra;
 move=> Hle01; case Rle_lt_or_eq_dec => //; lra.
Qed.

Lemma Rmult_lt_gt_compat_neg_r : forall r r1 r2 : R, r < 0 -> r1 < r2 -> r1 * r > r2 * r.
Proof.
  move => r r1 r2 Hr Hr1r2.
  rewrite (Rmult_comm r1) (Rmult_comm r2).
    by apply Rmult_lt_gt_compat_neg_l.
Qed.

Lemma Rpower_Ropp' : forall x y : R, 0 < x -> x ^ (-y) = (/x) ^ y.
Proof.
 move => x y Hxpos.
 rewrite -{2}(Rpower_1 x) //; rewrite -Rpower_Ropp.
 rewrite Rpower_mult.
 by rewrite -Ropp_mult_distr_l Rmult_1_l.
Qed.

Lemma Rpower_Ropp1 : forall x : R, 0 < x -> x ^ (-1) = / x.
Proof.
 by move => x Hxpos; rewrite (Rpower_Ropp _ 1) Rpower_1.
Qed.

Lemma Rpower_lt' : forall x y z : R, 0 < x < 1 -> y < z -> x ^ z < x ^ y.
Proof.
 move => x y z Hx Hyz.
 rewrite -(Rinv_involutive x); [| apply pos_neq0; apply Hx].
 rewrite -!(Rpower_Ropp' (x:=/x)); try apply Rinv_0_lt_compat; try apply Hx.
 apply (Rpower_lt (/x) (-z) (-y)).
  rewrite -Rinv_1; apply (Rinv_lt_contravar x 1); lra.
 lra.
Qed.

Lemma Rmax_same : forall x:R, Rmax x x = x.
Proof.
  move => x.
  rewrite /Rmax; case Rle_dec; lra.
Qed.

Lemma Rmin_same : forall x:R, Rmin x x = x.
Proof.
  move => x.
  rewrite /Rmin; case Rle_dec; lra.
Qed.

Lemma Rsum_le_compat : forall (m n : nat) (F G : nat -> R), (forall k:nat, (m <= k < n)%N -> (F k <= G k)) ->
  \big[Rplus/0]_(m <= k < n) F k <= \big[Rplus/0]_(m <= k < n) G k.
Proof.
  move => m n F G HFG.
  induction n.
  - rewrite !big_geq; try apply /leP; try lia; lra.
  - case (le_lt_dec m n) => [Hlemn | Hltnm].
    + rewrite !big_nat_recr; try apply /leP => //.
      apply Rplus_le_compat.
      * apply IHn.
        move => k /andP; case => /leP Hmk /leP Hkn.
        apply /HFG /andP; split; apply /leP; lia.
      * apply /HFG /andP; split; apply /leP; lia.
    + rewrite !big_geq; try apply /leP; try lia; lra.
Qed.

Lemma Rsum_nonneg : forall (m n : nat) (F : nat->R),
  (forall k:nat, (m <= k < n)%N -> 0 <= F k) -> 0 <= \Rsum_(m <= k < n) F k.
Proof.
  move => m n F H.
  rewrite {1}(_ : 0 = \big[Rplus/0]_(m <= k < n) (fun _:nat => 0) k); [| rewrite big1_eq //].
    by apply Rsum_le_compat.
Qed.

Lemma Rsum_Rabs : forall (m n : nat) (F : nat -> R),
    Rabs (\Rsum_(m <= i < n) F i) <= \Rsum_(m <= i < n) Rabs (F i).
Proof.
  move => m.
  wlog: m / (m = 0)%N.
  - move => H0 n F.
    rewrite -(add0n m) !big_addn /=.
      by apply H0.
  - move ->; clear.
    induction n => F; [rewrite !big_geq ?Rabs_R0 //; lra |].
    rewrite !big_nat_recr //=.
    eapply Rle_trans; [apply Rabs_triang |].
    apply Rplus_le_compat_r.
    eapply Rle_trans; [apply IHn |]; lra.
Qed.

(* geometric series *)

Lemma sum_geom : forall (n:nat)(r:R), 0 < r -> r <> 1 ->
 \Rsum_(0 <= k < n) r^k = (1 - r^n) / (1 - r).
Proof.
 induction n.
  move=> r Hrpos Hrnot1.
  by rewrite big_geq //= (Rpower_O r Hrpos) Rminus_eq_0 /Rdiv Rmult_0_l.
 move=> r Hrpos Hrnot1.
 rewrite big_nat_recr //.
 rewrite IHn //.
 rewrite -{2}(Rinv_r_simpl_l (1-r) (r^n)); [ |lra]; 
 rewrite [Rplus_monoid _ _] /= -(Rdiv_plus_distr _ _ (1-r)).
 rewrite Rmult_minus_distr_l Rmult_1_r -Rplus_assoc (Rmult_comm _ r) -{3}(Rpower_1 r) //
 -Rpower_plus {1}/Rminus (Rplus_assoc _ (-r^n)) Rplus_opp_l Rplus_0_r.
 by rewrite (Rplus_comm 1 n) S_INR.
Qed.

Lemma sum_geom_incr_aux : forall (n:nat)(r:R), 0 < r ->
 (1-r).^2 * (\Rsum_(0 <= k < n) (k+1)*r^k) = 1 - (n+1) * r^n + n * r^(n+1).
Proof.
 move => n r Hrpos; elim n => [| p IHp].
  rewrite big_nil.
  by rewrite Rmult_0_l Rmult_0_r Rplus_0_l Rplus_0_r Rpower_O // Rmult_1_r Rminus_eq_0.
 rewrite big_nat_recr //.
 rewrite Rmult_plus_distr_l.
 rewrite IHp.
 rewrite (_ : (1-r).^2 = 1 - 2*r + r.^2); [| lra].
 rewrite (Rmult_plus_distr_r _ (r.^2)) Rmult_minus_distr_r Rmult_1_l.
 rewrite -!Rmult_assoc 2!(Rmult_comm _ (p+1)) 3!Rmult_assoc -Rpower_pow //
 -{4}(Rpower_1 r) // -!Rpower_plus 2!(Rplus_comm _ p).
 rewrite (S_INR p) (_ : INR p +1 + 1 = p + 2); [| lra]; rewrite (_ : p + 2%N = p + 2) => //.
 lra.
Qed.

Lemma sum_geom_incr : forall (n:nat)(r:R), 0 < r < 1 ->
 \Rsum_(0 <= k < n) (k+1)*r^k = (1 - (n+1) * r^n + n * r^(n+1)) / (1-r)^2.
Proof.
 move => n r Hr.
 rewrite -(Rinv_r_simpl_m ((1-r)^2) (\Rsum_(0<=k<n) _ )); [| apply /pos_neq0 /exp_pos].
 rewrite {1}(Rpower_pow 2); [| lra].
 rewrite sum_geom_incr_aux //; apply Hr.
Qed.

(* ceil function *)

Definition ceil (x:R) : Z := ((floor1 x) + 1)%Z.

Lemma ceil_correct : forall x:R, (ceil x) - 1 < x <= ceil x.
Proof.
 move => x.
 rewrite /ceil.
 rewrite plus_IZR Ropp_r_simpl_l.
 rewrite /floor1; case floor1_ex => //.
Qed.

Lemma ceil_n : forall n:Z, ceil n = n.
Proof.
 move => n.
 rewrite /ceil /floor1.
 case floor1_ex => m Hn /=.
 apply Z.le_antisymm.
  rewrite Z.add_1_r; apply Zlt_le_succ.
  apply lt_IZR; apply Hn.
 apply le_IZR; rewrite plus_IZR; apply Hn.
Qed.

Lemma ceil_unique : forall (n:Z)(x:R), n - 1 < x <= n -> n = ceil x.
Proof.
 move => n x [Hgtx Hlex].
 apply Z.le_antisymm.
  rewrite -Z.lt_pred_le -Z.sub_1_r.
  apply lt_IZR; rewrite minus_IZR; eapply Rlt_le_trans.
   apply Hgtx.
  apply ceil_correct.
 case: (Rle_lt_or_eq_dec _ _ Hlex) => [Hltx | Heqx].
  apply Zlt_succ_le; rewrite -Z.add_1_r.
  apply lt_IZR; rewrite plus_IZR; apply (Rlt_trans _ (x+1)).
   rewrite -(Ropp_r_simpl_l (-1) (ceil x)) /Rminus Ropp_involutive; apply Rplus_lt_compat_r.
   apply ceil_correct.
  by apply Rplus_lt_compat_r.
 rewrite Heqx ceil_n; lia.
Qed.

(* elementary calculus *)

Lemma mulnl_eventually : forall n:nat, (0 < n)%coq_nat -> filterlim (muln n) eventually eventually.
Proof.
  move => n Hn.
  rewrite /filterlim /filter_le /filtermap !/eventually => P.
  case => N HNspec.
  exists N => m Hm.
  apply HNspec.
  have Hn' : (1 <= n)%N by [apply /leP; lia].
  rewrite -(mul1n N); apply /leP.
    by apply leq_mul; [| apply /leP].
Qed.

Lemma mulnr_eventually : forall n:nat, (0 < n)%coq_nat -> filterlim (muln^~ n) eventually eventually.
Proof.
  move => n Hn.
  rewrite /filterlim /filter_le /filtermap !/eventually => P.
  case => N HNspec.
  exists N => m Hm.
  apply HNspec.
  have Hn' : (1 <= n)%N by [apply /leP; lia].
  rewrite -(muln1 N); apply /leP.
    by apply leq_mul; [apply /leP |].
Qed.

Definition is_lower_bound (E : R -> Prop) (m:R) := forall x:R, E x -> m <= x.

Definition Eopp (E : R -> Prop) := fun x:R => E (-x).

Lemma low_up_bound (E : R -> Prop) (m:R) :
  is_upper_bound E m <-> is_lower_bound (Eopp E) (-m).
Proof.
  split.
  - intro Hub.
    rewrite /is_lower_bound.
    intros x HEopp.
    rewrite /Eopp in HEopp; rewrite /is_upper_bound in Hub.
    rewrite -(Ropp_involutive x).
    apply /Ropp_ge_le_contravar /Rle_ge /Hub => //.
  - intro Hlb.
    rewrite /is_upper_bound.
    intros x HE.
    rewrite -(Ropp_involutive x) -(Ropp_involutive m).
    apply Ropp_ge_le_contravar.
    rewrite /is_lower_bound in Hlb.
    apply /Rle_ge /Hlb.
    rewrite /Eopp Ropp_involutive //.
Qed.  

Definition bound' (E : R -> Prop) := exists m:R, is_lower_bound E m.

Lemma bound_up_low : forall (E : R -> Prop) (m : R),
    is_upper_bound E m <-> is_lower_bound (Eopp E) (-m).
Proof.
  intros E m.
  split.
  - intro Hub.
    rewrite /is_lower_bound.
    intros x HEopp.
    rewrite -(Ropp_involutive x).
    apply Ropp_ge_le_contravar.
    rewrite /is_upper_bound in Hub.
    apply /Rle_ge /Hub /HEopp.
  - intro Hlb.
    rewrite /is_upper_bound.
    intros x HE.
    rewrite -(Ropp_involutive x) -(Ropp_involutive m).
    apply Ropp_ge_le_contravar.
    rewrite /is_lower_bound in Hlb.
    apply /Rle_ge /(Hlb (-x)).
    rewrite /Eopp Ropp_involutive //.
Qed.

Definition is_glb (E : R -> Prop) (m:R) :=
  is_lower_bound E m /\ (forall b:R, is_lower_bound E b -> b <= m).

Lemma lub_glb : forall (E : R -> Prop) (m:R), is_lub E m <-> is_glb (Eopp E) (-m).
Proof.
  intros E m.
  split.
  - intro Hlub.
    rewrite /is_glb.
    split.
    + apply bound_up_low.
      apply Hlub.
    + intros b Hlb.
      rewrite -(Ropp_involutive b).
      apply Ropp_ge_le_contravar.
      apply Rle_ge.
      apply Hlub.
      apply low_up_bound.
      rewrite Ropp_involutive //.      
  - intro Hglb.
    rewrite /is_lub.
    split.
    + apply bound_up_low.
      apply Hglb.
    + intros b Hlb.
      rewrite -(Ropp_involutive b) -(Ropp_involutive m).
      apply Ropp_ge_le_contravar.
      apply Rle_ge.
      apply Hglb.
      by apply bound_up_low.
Qed.

Lemma completeness':
  forall E : R -> Prop, bound' E -> (exists x:R, E x) -> {m:R | is_glb E m}.
Proof.
  intros E HEb HEex.
  case: (completeness (Eopp E)).
  - case: HEb => [x Hlb].
    exists (-x).
    apply bound_up_low.
    rewrite Ropp_involutive /is_lower_bound.
    intros y HEopp2.
    apply Hlb.
    rewrite /Eopp in HEopp2.
    by rewrite -(Ropp_involutive y).
  - case: HEex => [x HEex].
    exists (-x).
    rewrite /Eopp.
    by rewrite (Ropp_involutive x).
  - intros b Hlub.
    exists (-b).
    apply lub_glb in Hlub.
    rewrite /is_glb in Hlub *.
    destruct Hlub as [Hlb Hmax].
    split.
    + rewrite /is_lower_bound in Hlb *.
      intros x HEx.
      apply Hlb.
      rewrite /Eopp.
      by rewrite Ropp_involutive.
    + intros a Hlb'.
      apply Hmax.
      rewrite /is_lower_bound in Hlb' *.
      intros x HEx.
      apply Hlb'.
        by rewrite -(Ropp_involutive x).
Qed.

Lemma glb_Empty_p_infty : forall E : Ensemble R, (Empty E) -> is_glb_Rbar E p_infty.
Proof.
  move => E HEemp.
  rewrite /is_glb_Rbar.
  split.
  - rewrite /is_lb_Rbar.
    move => x Hx.
    apply False_ind.
    by apply (Empty_correct_1 E HEemp x).
  - move => b Hblb.
    case b; by try move => _.
Qed.

Lemma Glb_Empty_p_infty : forall E : Ensemble R, (Empty E) -> Glb_Rbar E = p_infty.
Proof.
  move => E HEemp.
  apply is_glb_Rbar_unique.
    by apply glb_Empty_p_infty.
Qed.

Lemma complement_image_rec : forall f : R -> R, forall D : Ensemble R,
      complementary (image_rec f D) =_D image_rec f (complementary D).
Proof.
  move => f D.
  split; rewrite /included => x Hx; rewrite /image_rec /complementary; apply Hx.
Qed.    

Lemma Rsingleton_closed : forall a:R, closed_set (fun x:R => x = a).
Proof.
  move => a.
  rewrite /closed_set.
  apply open_set_P1.
  split; [| apply interior_P1].
  rewrite /included => x Hx.
  rewrite /interior /neighbourhood.
  set (r := Rabs ((x-a)/2)).
  have Hrpos : 0 < r.
  { rewrite /r.
    rewrite /complementary in Hx.
    apply Rabs_pos_lt; lra. }
  exists (mkposreal r Hrpos).
  rewrite /included => y Hy.
  rewrite /complementary.
  move => Hya.
  rewrite /disc in Hy.
  apply (Rle_not_lt (Rabs (a-x)) 0); [apply Rabs_pos |].
  move: Hy; rewrite /r Hya /Rdiv /=.
  rewrite Rabs_mult {3}/Rabs; case Rcase_abs; [lra | move => _].
  rewrite Rabs_minus_sym; lra.
Qed.

Lemma is_lim_seq_abs_minus_0 : forall (u : nat -> R) (l:R),
  is_lim_seq u l <-> is_lim_seq (fun n:nat => Rabs (u n - l)) 0.
Proof.
  move => u l.
  rewrite !is_lim_seq_Reals !/Un_cv !/R_dist.
  split.
  - move => Hul.
    move => eps Heps.
    case: (Hul eps Heps) => N HN.
    exists N => n Hn.
    rewrite Rminus_0_r Rabs_Rabsolu.
      by apply HN.
  - move => Hul0.
    move => eps Heps.
    case: (Hul0 eps Heps) => N HN.
    exists N => n Hn.
    rewrite -(Rabs_Rabsolu (u n - l)) -(Rminus_0_r (Rabs (u n - l))).
      by apply HN.
Qed.

Lemma is_lim_seq_diff_0 : forall (u v : nat -> R) (l:R),
  is_lim_seq u l -> is_lim_seq (fun n:nat => u n - v n) 0 -> is_lim_seq v l.
Proof.
  move => u v l.
  move /is_lim_seq_abs_minus_0 => Hul.
  move /is_lim_seq_abs_minus_0 => Huv0.
  apply is_lim_seq_abs_minus_0.
  apply (is_lim_seq_le_le (fun _ => 0) _ (fun n:nat => Rabs (u n - v n) + Rabs (u n - l))).
  - move => n.
    split; [apply Rabs_pos |].
    rewrite (_ : v n - l = (v n - u n) + (u n - l)); [| lra].
    rewrite -(Rabs_Ropp (u n - v n)) Ropp_minus_distr.
    apply Rabs_triang.
  - apply is_lim_seq_const.
  - rewrite -(Rplus_0_r 0).
    apply (is_lim_seq_plus _ _ 0 0); auto.
    + apply (is_lim_seq_ext (fun n:nat => Rabs (u n - v n - 0))); auto.
        by move => n; rewrite Rminus_0_r.
    + rewrite /is_Rbar_plus //=.
Qed.    

Lemma Rle_lim_decr : forall (b:R) (f : R -> R),
    (decreasing f) -> is_lim f p_infty b -> forall x:R, b <= f x.
Proof.
  move => b f Hdecr Hlim x.
  apply Rnot_lt_le.
  move => Hlt.
  apply (Rlt_irrefl (f x)).
  apply is_lim_spec in Hlim.
  rewrite /is_lim' in Hlim.
  assert (Hpos : 0 < b - (f x)) by lra.
  move: (Hlim (mkposreal (b - (f x)) Hpos)).
  rewrite /Rbar_locally'.
  case => a Hbnd.
  set a' := Rmax x a + 1.
  assert (Haa' : a < a').
  { rewrite /a'.
    apply /(Rle_lt_trans a (Rmax x a) _); [apply Rmax_r | apply Rlt_plus_1]. }
  assert (Hxa' : x < a').
  { rewrite /a'.
    apply /(Rle_lt_trans x (Rmax x a) _); [apply Rmax_l | apply Rlt_plus_1]. }
  assert (Hfa'fx : f a' <= f x) by (apply Hdecr; lra).      
  apply (Rlt_le_trans (f x) (f a') (f x)).
  - rewrite -(Ropp_involutive (f x)) -(Ropp_involutive (f a'));
      apply /Ropp_gt_contravar /(Rplus_gt_reg_l b); rewrite -2!/(Rminus b _).
    move: (Hbnd a' Haa') => Hfa'b.
    rewrite (Rabs_left (f a' - b)) in Hfa'b; [| apply Rlt_minus; lra].
    rewrite Ropp_minus_distr in Hfa'b; done.
  - done.
Qed.

Lemma continuity_pt_continuous : forall (x:R) (f : R -> R), continuity_pt f x <-> continuous f x.
Proof.
  move => x f; apply continuity_pt_filterlim.
Qed.

Lemma eq_R_continuous : forall (f : R -> R), continuity f <-> forall x:R, continuous f x.
Proof.
  move => f.
  rewrite /continuity.
    by split; move => H x; apply continuity_pt_continuous.
Qed.

Definition continuity_open := open_set_P3.

Lemma continuity_closed : forall f : R -> R,
    continuity f <-> (forall D : Ensemble R, closed_set D -> closed_set (image_rec f D)).
Proof.
  move => f.
  move: (continuity_P3 f) => [Hfopen Hopenf].
  split.
  - move => HfC0 D HD.
    rewrite /closed_set.
    apply (open_set_P6 (image_rec f (complementary D))).
    + apply Hfopen; auto.
    + apply complement_image_rec.
  - move => Hclosed.
    apply Hopenf => D HD.
    rewrite -(Complement_Complement R D).
    rewrite (_ : Complement R = complementary) //.
    apply (open_set_P6 (complementary (image_rec f (complementary D))));
      [| apply complement_image_rec].
    apply Hclosed.
    rewrite /closed_set.
    rewrite (_ : complementary = Complement R) //.
    rewrite Complement_Complement //.
Qed.

Lemma continuous_Rplus_snd : forall (a x : R), continuous (Rplus a) x.
Proof.
  move => a x.
  apply (continuous_plus (fun => a) id); [apply continuous_const | apply continuous_id].
Qed.

Lemma continuous_Rplus_fst : forall (b x : R), continuous (Rplus ^~ b) x.
Proof.
  move => b x.
  apply (continuous_plus id (fun => b)); [apply continuous_id | apply continuous_const].
Qed.

Lemma continuous_Rminus_snd : forall (a x : R), continuous (Rminus a) x.
Proof.
  move => a x.
  rewrite /Rminus.
  apply (continuous_minus (fun => a) id); [apply continuous_const | apply continuous_id].
Qed.    

Lemma continuous_Rminus_fst : forall (b x : R), continuous (Rminus ^~ b) x.
Proof.
  move => b x.
  rewrite /Rminus; apply continuous_Rplus_fst.
Qed.

Lemma continuous_Rmult_fst : forall x y : R, continuous (Rmult ^~ y) x.
Proof.
  move => x y.
  apply (continuous_mult id (fun => y)); [apply continuous_id | apply continuous_const].
Qed.  

Lemma continuous_Rmult_snd : forall x y : R, continuous (Rmult x) y.
  move => x y.
  apply (continuous_mult (fun => x) id); [apply continuous_const | apply continuous_id].
Qed.

Lemma continuous_Rpower_fst : forall x y : R, 0 < x -> continuous (Rpower ^~ y) x.
Proof.
  move => x y Hx.
  rewrite /Rpower /=.
  apply continuous_comp => /=.
  - apply (continuous_mult (fun => y)); [apply continuous_const | by apply continuous_ln].
  - apply continuous_exp.
Qed.

Lemma continuous_Rpower_snd : forall x y : R, continuous (Rpower x) y.
Proof.
  move => x y.
  rewrite /Rpower.
  apply continuous_comp.
  - apply continuous_Rmult_fst.
  - apply continuous_exp.
Qed.

Lemma lim_pow_0 : forall r:R, 0 < r < 1 -> is_lim_seq (fun n:nat => r^n) 0.
Proof.
 move => r Hr01.
 rewrite /Rpower.
 apply (is_lim_comp_seq _ _ m_infty).
   apply is_lim_exp_m.
  exists 0%N.
  move => n Hn0 HFM; inversion HFM.
 rewrite -(is_Rbar_mult_unique p_infty (ln r) m_infty);
 [| apply is_Rbar_mult_p_infty_neg => /=; rewrite -ln_1; apply ln_increasing; lra].
 apply is_lim_seq_scal_r.
 apply is_lim_seq_INR.
Qed.

Lemma lim_mult_pow_0 : forall r s : R, 0 < r < 1 -> is_lim_seq (fun n:nat => n^s * r^n) 0.
Proof.
  move => r s Hr01.
  assert (H_lnr_neg : ln r < 0) by (rewrite -ln_1; apply ln_increasing; apply Hr01).
  apply (is_lim_comp_seq (fun x:R => x^s * r^x) _ p_infty 0).
  - apply (is_lim_ext_loc (fun x:R => exp (x * (s * (ln x / x) + ln r)))) => /=.
    + exists 0 => x Hxpos.
      rewrite Rmult_plus_distr_l /Rdiv -!Rmult_assoc (Rmult_assoc x) Rinv_r_simpl_m;
        [by rewrite exp_plus -/(Rpower x s) -/(Rpower r x) | apply pos_neq0 => //].
    + apply (is_lim_comp exp (fun x:R => x * (s * (ln x / x) + ln r)) _ _ m_infty).
      * apply is_lim_exp_m.
      * rewrite (_ : m_infty = Rbar_mult p_infty (ln r));
          [| apply /esym /is_Rbar_mult_unique /is_Rbar_mult_p_infty_neg;
             rewrite /Rbar_lt; apply H_lnr_neg].
        apply is_lim_mult => //; [| rewrite /ex_Rbar_mult; apply /neg_neq0 /H_lnr_neg].
        rewrite -{2}(Rplus_0_l (ln r)).
        apply (is_lim_plus _ _ _ 0 (ln r));
          [| apply is_lim_const |  by rewrite /is_Rbar_plus /=].
        rewrite (_ : 0 = Rbar_mult s 0); [| by rewrite /= Rmult_0_r].
        apply (is_lim_scal_l _ s p_infty 0).
        apply is_lim_div_ln_p.
      * rewrite /Rbar_locally'.
        exists 0.
        move => x Hxpos Heq; inversion Heq.
  - rewrite /eventually.
    exists 0%N.
    move => n Hle0n Heq; inversion Heq.
  - apply is_lim_seq_INR.
Qed.

Lemma lim_mult1_pow_0 : forall r:R, 0 < r < 1 -> is_lim_seq (fun n:nat => n * r^n) 0.
Proof.
  move => r Hr01.
  apply (is_lim_seq_ext_loc (fun n:nat => n^1 * r^n)).
  - exists 1%N.
    move => n Hnpos.
    by rewrite -{3}(Rpower_1 n); [| apply lt_0_INR; lia].
  - apply lim_mult_pow_0 => //.
Qed.

Lemma Derive_ln : forall x:R, 0 < x -> Derive ln x = 1 / x.
Proof.
  move => x Hx.
  apply is_derive_unique; try auto_derive => //.
Qed.

Lemma Derive_incr : forall (f : R -> R) (a b : R), ex_derive f (a+b) ->
  Derive (fun x:R => f (a+x)) b = Derive f (a+b).
Proof.
  move => f a b Hf.
  rewrite (Derive_comp f); last (by auto_derive); auto.
  rewrite Derive_plus; try auto_derive; auto.
  rewrite Derive_const Derive_id.
  rewrite Rplus_0_l Rmult_1_l //.
Qed.

Lemma is_derive_Rpower_fst : forall x y : R, 0 < x -> is_derive (fun x:R => x^y) x (y * x^(y-1)).
Proof.
  move => x y Hx.
  rewrite /Rpower.
  auto_derive; auto.
  rewrite Rmult_minus_distr_r /Rminus.
  rewrite exp_plus.
  rewrite !Rmult_1_l.
  rewrite exp_Ropp exp_ln; lra.
Qed.

Lemma ex_derive_Rpower_fst : forall x y : R, 0 < x -> ex_derive (fun x:R => x^y) x.
Proof.
  move => x y Hx.
  exists (y * x^(y-1)).
    by apply is_derive_Rpower_fst.
Qed.

Lemma is_derive_Rpower_snd : forall x y : R, is_derive (fun y:R => x^y) y ((ln x) * x^y).
Proof.
  move => x y.
  rewrite /Rpower.
  auto_derive; lra.
Qed.

Lemma ex_derive_Rpower_snd : forall x y : R, ex_derive (fun y:R => x^y) y.
Proof.
  move => x y.
  exists ((ln x) * x^y).
    by apply is_derive_Rpower_snd.
Qed.

Lemma RInt_comp_plus : forall {V : CompleteNormedModule R_AbsRing} (f : R -> V) (v a b : R),
  ex_RInt f (a + v) (b + v) -> RInt (fun y : R => f (y + v)) a b = RInt f (a + v) (b + v).
Proof.
  move => V f v a b HexRInt.
  rewrite -{2}(Rmult_1_l a) -{2}(Rmult_1_l b).
  rewrite (RInt_ext (fun y:R => f (y+v)) (fun y:R => scal 1 (f (1*y+v)))).
  - apply RInt_comp_lin.
      by rewrite !Rmult_1_l.
  - move => x Hx.
      by rewrite Rmult_1_l scal_one.
Qed.

Lemma MVT' : forall (f : R -> R) (a b : R) (df : R -> R), a <= b ->
  (forall x:R, a < x < b -> is_derive f x (df x)) ->
  (forall x:R, a <= x <= b -> continuity_pt f x) ->
  exists c:R, a <= c <= b /\ f b - f a = df c * (b - a).
Proof.
  move => f a b df Hab Hdiff Hcont.
  have Ha : Rmin a b = a by rewrite Rmin_left; lra.
  have Hb : Rmax a b = b by rewrite Rmax_right; lra.
  move: (MVT_gen f a b df).
  rewrite Ha Hb; auto.
Qed.

Lemma RInt_scal_Derive_l : forall (f : R -> R) (g : R -> R) (a b : R),
  (forall t : R, Rmin a b <= t <= Rmax a b -> ex_derive f t) ->
  (forall t : R, Rmin a b <= t <= Rmax a b -> ex_derive g t) ->
  (forall t : R, Rmin a b <= t <= Rmax a b -> continuous (Derive f) t) ->
  (forall t : R, Rmin a b <= t <= Rmax a b -> continuous (Derive g) t) ->
  RInt (fun t:R => scal ((Derive f) t) (g t)) a b =
  minus (minus (scal (f b) (g b)) (scal (f a) (g a)))
        (RInt (fun t:R => scal (f t) ((Derive g) t)) a b).
Proof.
  move => f g a b HfD HgD HfCD HgCD.
  apply is_RInt_unique.
  apply (is_RInt_scal_derive_l _ _ (Derive f) (Derive g)); auto; 
    try (move => t Ht; auto_derive; auto; by rewrite Rmult_1_l).
  apply RInt_correct.
  apply ex_RInt_continuous => t Ht.
  apply continuous_mult; auto.
  apply (ex_derive_continuous f); auto.
Qed.

(* quadrature *)

Definition pr1 (T U : Type) (t:T) (u:U) := t.
Definition pr2 (T U : Type) (t:T) (u:U) := u.

Definition unif_div_l (a b : R) (n:nat) := SF_seq_f2 (pr1 (U:=R)) (unif_part a b n).
Definition unif_div_r (a b : R) (n:nat) := SF_seq_f2 (pr2 (U:=R)) (unif_part a b n).

Lemma filterlim_ext_loc_equiv : forall (T U : Type) (F : (T -> Prop) -> Prop) (G : (U -> Prop) -> Prop),
  Filter F -> forall f g : T -> U, F (fun x:T => f x = g x) -> filterlim f F G <-> filterlim g F G.
Proof.
  move => T U F G HFF f g Hfg.
  split; [by apply filterlim_ext_loc |].
  apply filterlim_ext_loc.
  apply (filter_imp (fun x:T => f x = g x)); auto.
Qed.

Lemma filter_le_Rloc_Rbarloc : forall r:R, filter_le (locally r) (Rbar_locally r).
Proof.
  move => r.
  rewrite /filter_le => P.
    by rewrite /Rbar_locally.
Qed.

Lemma Riemann_sum_calc : forall (n:nat) (a:R) (f : R -> R) (x y : nat -> R),
  Riemann_sum f (mkSF_seq a [ seq (x i, y i) | i <- seq.iota 0%N n.+1]) =
    (x 0%N - a) * f (y 0%N) + \Rsum_(0 <= i < n) (x i.+1 - x i) * f (y i.+1).
Proof.
  move => n a f x y.
  rewrite /Riemann_sum /= /plus /scal /= /mult /=.
  have Hpm : pairmap (fun x0 y0 : R * R => (y0.1 - x0.1) * f y0.2)
                     (x 0%N, y 0%N) [seq (x i, y i) | i <- seq.iota 1 n] =
             [ seq (x i.+1 - x i) * f (y i.+1) | i <- seq.iota 0 n].
  { apply eq_from_nth with (x0 := 0); [ by rewrite /= size_pairmap !size_map !size_iota |].
    move => i.
    rewrite size_pairmap size_map size_iota => Hi.
    rewrite (nth_pairmap (0,0)); [| by rewrite size_map size_iota].
    rewrite !(nth_map 0%N); [| by rewrite size_iota ..].
    rewrite !nth_iota //= add0n.
    move: Hi; case i => //= j Hj.
    rewrite (nth_map 0%N); [| rewrite size_iota; auto].
    rewrite nth_iota; auto. }
  rewrite Hpm.
  rewrite foldrE.
  rewrite big_map.
    by rewrite /index_iota subn0.
Qed.

Lemma is_RInt_regular : forall (V : NormedModule R_AbsRing) (f : R -> V) (a b : R) (If : V),
  a <= b -> is_RInt f a b If <-> filterlim (Riemann_sum f) (Riemann_fine a b) (locally If).
Proof.
  move => V f a b If Hab.
  rewrite /is_RInt.
  apply filterlim_ext_loc_equiv; [apply Riemann_fine_filter |].
  rewrite /Riemann_fine /within /locally_dist.
  have H1pos : 0 < 1 by lra.
  exists (mkposreal 1 H1pos) => /=.
  move => ptd _; case => Hpt.
  rewrite Rmin_left ?Rmax_right; [| lra ..].
  case => Ha Hb.
  rewrite /sign.
  case total_order_T; [case |].
  - by rewrite scal_one.
  - move => Heqab.
    rewrite scal_zero_l.
    rewrite Riemann_sum_zero; by [| apply ptd_sort | rewrite /SF_lx /=; lra].
  - lra.
Qed.    
  
Lemma quadr_left : forall (f : R -> R) (a b : R), a <= b -> ex_RInt f a b ->
  is_lim_seq (fun n:nat => (b-a)/(n+1) * \Rsum_(0 <= k < n+1) f (a + k*(b-a)/(n+1))) (RInt f a b).
Proof.
  move => f a b Hab Hexint.
  set (Qdr := fun n:nat => (b-a)/(n+1) * \Rsum_(0 <= k < n+1) f (a + k*(b-a)/(n+1))).
  set (unif_div_l := fun n:nat => SF_seq_f2 (@pr1 R R) (unif_part a b n)).
  have HQdr : forall n:nat, Riemann_sum f (unif_div_l n) = Qdr n.
  { move => n.
    rewrite /unif_div_l /SF_seq_f2 /pr1.
    rewrite pairmap_pair1.
    rewrite [head _ _]/=.
    rewrite Riemann_sum_calc.
    rewrite -(big_nat_recl _ _
      (fun i:nat => (a+i.+1*(b-a)/(n+1)-(a+i*(b-a)/(n+1))) * f (a+i*(b-a)/(n+1)))); auto.
    rewrite /Qdr.
    under eq_big_nat => i Hi do (rewrite -Nat.add_1_r plus_INR /=
      (_ : a + (i+1)*(b-a)/(n+1) - (a + i*(b-a)/(n+1)) = (b-a)/(n+1)); [| lra]).
    by rewrite -big_distrr -Nat.add_1_r. }
  rewrite /is_lim_seq.
  eapply filterlim_filter_le_2; [apply filter_le_Rloc_Rbarloc |].
  eapply filterlim_ext; [apply HQdr |].
  apply (filterlim_comp _ _ _ unif_div_l (Riemann_sum f) _ (Riemann_fine a b)).
  - rewrite /filterlim /filter_le => P.
    rewrite /Riemann_fine /within /locally_dist.
    case => delta Hsubdiv.
    destruct delta as [delta Hdeltapos].
    rewrite /filtermap /eventually.
    exists (Z.to_nat (ceil ((b-a)/delta))).
    move => n Hn.
    have Hn1 : 0 < n+1 by rewrite (_ : 1 = 1%N) // -plus_INR; apply lt_0_INR; lia.
    have Hab' : 0 <= (b-a)/(n+1) by apply Rdiv_le_0_compat; lra.
    apply Hsubdiv.
    + rewrite /unif_div_l.
      rewrite SF_lx_f2; [| rewrite /unif_part size_mkseq; lia].
      rewrite seq_step_unif_part.
      rewrite /Rabs; case Rcase_abs; [lra |] => _.
      apply Rlt_div_l; auto.
      rewrite Rmult_comm.
      apply Rlt_div_l => //=.
      apply (Rle_lt_trans _ n); [| lra].
      apply (Rle_trans _ (ceil ((b-a)/delta))); [apply ceil_correct |].
      move: Hn => /le_INR.
      rewrite INR_Ztonat_IZR //.
      apply le_IZR.
      apply (Rle_trans _ ((b-a)/delta));
        [apply Rdiv_le_0_compat; lra | apply ceil_correct].
    + rewrite /Rmin /Rmax; case Rle_dec; [| lra] => _.
      split; [| split].
      * rewrite /unif_div_l.
        apply ptd_f2; [by apply unif_part_sort |].
        move => x y Hxy; rewrite /pr1; lra.
      * rewrite /unif_div_l /=; lra.
      * rewrite {2}/unif_div_l.
        rewrite SF_lx_f2; [| rewrite /unif_part size_mkseq; lia].
          by rewrite last_unif_part.      
  - apply is_RInt_regular; auto.
      by apply (RInt_correct f a b).
Qed.

Lemma quadr_right : forall (f : R -> R) (a b : R), a <= b -> ex_RInt f a b ->
  is_lim_seq (fun n:nat => (b-a)/(n+1) * \Rsum_(0 <= k < n+1) f (a + k.+1*(b-a)/(n+1)))
             (RInt f a b).
Proof.
  move => f a b Hab Hexint.
  set (Qdr := fun n:nat => (b-a)/(n+1) * \Rsum_(0 <= k < n+1) f (a + k.+1*(b-a)/(n+1))).
  set (unif_div_l := fun n:nat => SF_seq_f2 (@pr2 R R) (unif_part a b n)).
  have HQdr : forall n:nat, Riemann_sum f (unif_div_l n) = Qdr n.
  { move => n.
    rewrite /unif_div_l /SF_seq_f2 /pr2.
    rewrite pairmap_pair2.
    rewrite [head _ _]/=.
    rewrite Riemann_sum_calc.
    rewrite -(big_nat_recl _ _
      (fun i:nat => (a+i.+1*(b-a)/(n+1)-(a+i*(b-a)/(n+1))) * f (a+i.+1*(b-a)/(n+1)))); auto.
    rewrite /Qdr.
    under eq_big_nat => i Hi do (
      rewrite -Nat.add_1_r plus_INR
        (_ : a + (i+1)*(b-a)/(n+1) - (a + i*(b-a)/(n+1)) = (b-a)/(n+1))
        -?plus_INR ?Nat.add_1_r; [| lra] ).
    by rewrite -big_distrr -Nat.add_1_r. }
  rewrite /is_lim_seq.
  eapply filterlim_filter_le_2; [apply filter_le_Rloc_Rbarloc |].
  eapply filterlim_ext; [apply HQdr |].
  apply (filterlim_comp _ _ _ unif_div_l (Riemann_sum f) _ (Riemann_fine a b)).
  - rewrite /filterlim /filter_le => P.
    rewrite /Riemann_fine /within /locally_dist.
    case => delta Hsubdiv.
    destruct delta as [delta Hdeltapos].
    rewrite /filtermap /eventually.
    exists (Z.to_nat (ceil ((b-a)/delta))).
    move => n Hn.
    have Hn1 : 0 < n+1 by rewrite (_ : 1 = 1%N) // -plus_INR; apply lt_0_INR; lia.
    have Hab' : 0 <= (b-a)/(n+1) by apply Rdiv_le_0_compat; lra.
    apply Hsubdiv.
    + rewrite /unif_div_l.
      rewrite SF_lx_f2; [| rewrite /unif_part size_mkseq; lia].
      rewrite seq_step_unif_part.
      rewrite /Rabs; case Rcase_abs; [lra |] => _.
      apply Rlt_div_l; auto.
      rewrite Rmult_comm.
      apply Rlt_div_l => //=.
      apply (Rle_lt_trans _ n); [| lra].
      apply (Rle_trans _ (ceil ((b-a)/delta))); [apply ceil_correct |].
      move: Hn => /le_INR.
      rewrite INR_Ztonat_IZR //.
      apply le_IZR.
      apply (Rle_trans _ ((b-a)/delta));
        [apply Rdiv_le_0_compat; lra | apply ceil_correct].
    + rewrite /Rmin /Rmax; case Rle_dec; [| lra] => _.
      split; [| split].
      * rewrite /unif_div_l.
        apply ptd_f2; [by apply unif_part_sort |].
        move => x y Hxy; rewrite /pr2; lra.
      * rewrite /unif_div_l /=; lra.
      * rewrite {2}/unif_div_l.
        rewrite SF_lx_f2; [| rewrite /unif_part size_mkseq; lia].
          by rewrite last_unif_part.
  - apply is_RInt_regular; auto.
      by apply (RInt_correct f a b).
Qed.
