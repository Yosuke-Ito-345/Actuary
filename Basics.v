Require Import Logic.Description Classical_sets Reals Lra Lia.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(****************************************************************************************)

Lemma iota_rcons : forall (m n : nat), rcons (iota m n) (m+n) = iota m (n+1).
Proof.
 by move => m n; rewrite -(cats0 (rcons _ _)) cat_rcons iota_add.
Qed.

Lemma iota_pttn : forall (n m : nat),
 [seq k | j <- iota 0 n, k <- iota (j*m) m] = iota 0 (n*m).
Proof.
 move => n; elim n => [// | p IHp].
 move => m.
 rewrite mulSn addnC iota_add add0n.
 rewrite -IHp.
 rewrite -flatten_rcons -(map_id (iota (p*m) m)) -map_rcons.
 by rewrite iota_rcons addn1.
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

Lemma Rplus_assoc' : forall r1 r2 r3 : R, r1 + (r2 + r3) = r1 + r2 + r3.
Proof.
 by move=> r1 r2 r3; rewrite Rplus_assoc.
Qed.

Canonical Rplus_monoid := Monoid.Law Rplus_assoc' Rplus_0_l Rplus_0_r.
Canonical Rplus_monoid_RplusComm := Monoid.ComLaw Rplus_comm.
Canonical Rplus_monoid_Rmult := Monoid.MulLaw Rmult_0_l Rmult_0_r.
Canonical Rplus_monoid_RDistr := Monoid.AddLaw Rmult_plus_distr_r Rmult_plus_distr_l.

Lemma pos_neq0 : forall x:R, x > 0 -> x <> 0.
Proof.
 move => x; apply (Rgt_not_eq x 0).
Qed.

Lemma neg_neq0 : forall x:R, x < 0 -> x <> 0.
Proof.
 move => x; apply (Rlt_not_eq x 0).
Qed.

Lemma Sn_pos : forall n:nat, INR (n + 1) > 0.
Proof.
 move => n; rewrite plus_INR; apply INRp1_pos.
Qed.

Lemma INR1_pos : INR 1 > 0.
Proof.
 rewrite -(add0n 1%N); apply Sn_pos.
Qed.

Lemma Sn_neq0 : forall n:nat, INR (n + 1) <> 0.
Proof.
 move => n; apply pos_neq0; apply Sn_pos.
Qed.

Lemma one_pow : forall r:R, 1^r = 1.
Proof.
 move => r.
 rewrite /Rpower.
 rewrite ln_1 Rmult_0_r; apply exp_0.
Qed.

Lemma Rpower_2 : forall r:R, r > 0 -> r^2 = r*r.
Proof.
 move => r Hrpos.
 by rewrite -{-1}(Rpower_1 r) // -Rpower_plus.
Qed.

Lemma Ropp_r_simpl_l: forall r1 r2 : R, r2 + r1 - r1 = r2.
Proof.
 move => r1 r2.
 by rewrite /Rminus Rplus_assoc -/(Rminus _ r1) Rminus_eq_0 Rplus_0_r.
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

Lemma Rpower_Ropp' : forall x y : R, x > 0 -> x ^ (-y) = (/x) ^ y.
Proof.
 move => x y Hxpos.
 rewrite -{2}(Rpower_1 x) //; rewrite -Rpower_Ropp.
 rewrite Rpower_mult.
 by rewrite -Ropp_mult_distr_l Rmult_1_l.
Qed.

Lemma Rpower_Ropp1 : forall x : R, x > 0 -> x ^ (-1) = / x.
Proof.
 by move => x Hxpos; rewrite (Rpower_Ropp _ 1) Rpower_1.
Qed.

Lemma Rpower_lt' : forall x y z : R, 0 < x < 1 -> y < z -> x ^ y > x ^ z.
Proof.
 move => x y z Hx Hyz.
 rewrite -(Rinv_involutive x); [| apply pos_neq0; apply Hx].
 rewrite -!(Rpower_Ropp' (x:=/x)); try apply Rinv_0_lt_compat; try apply Hx.
 apply (Rpower_lt (/x) (-z) (-y)).
  rewrite -Rinv_1; apply (Rinv_lt_contravar x 1); lra.
 lra.
Qed.

(* geometric series *)

Lemma sum_geom : forall (n:nat)(r:R), r > 0 -> r <> 1 ->
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

Lemma sum_geom_incr_aux : forall (n:nat)(r:R), r > 0 ->
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

Lemma Rge_lim_decr : forall (b:R) (f : R -> R),
    (decreasing f) -> is_lim f p_infty b -> forall x:R, f x >= b.
Proof.
  move => b f Hdecr Hlim x.
  apply Rnot_lt_ge.
  move => Hlt.
  apply (Rlt_irrefl (f x)).
  apply is_lim_spec in Hlim.
  rewrite /is_lim' in Hlim.
  assert (Hpos : b - (f x) > 0) by lra.
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

Lemma Rsum_ge_compat : forall (m n : nat) (F G : nat -> R), (forall k:nat, (m <= k < n)%N -> (F k >= G k)) ->
  \big[Rplus/0]_(m <= k < n) F k >= \big[Rplus/0]_(m <= k < n) G k.
Proof.
  move => m n F G HFG.
  induction n.
  - rewrite !big_geq; try apply /leP; try lia; lra.
  - case (le_lt_dec m n) => [Hlemn | Hltnm].
    + rewrite !big_nat_recr; try apply /leP => //.
      apply Rplus_ge_compat.
      * apply IHn.
        move => k /andP; case => /leP Hmk /leP Hkn.
        apply /HFG /andP; split; apply /leP; lia.
      * apply /HFG /andP; split; apply /leP; lia.
    + rewrite !big_geq; try apply /leP; try lia; lra.
Qed.

Lemma Rsum_nonneg : forall (m n : nat) (F : nat->R),
  (forall k:nat, (m <= k < n)%N -> F k >= 0) -> \Rsum_(m <= k < n) F k >= 0.
Proof.
  move => m n F H.
  rewrite {2}(_ : 0 = \big[Rplus/0]_(m <= k < n) (fun _:nat => 0) k); [| rewrite big1_eq //].
    by apply Rsum_ge_compat.
Qed.
