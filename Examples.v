Require Import Reals Lra Lia.
From mathcomp Require Import all_ssreflect.
From Actuary Require Export Basics Interest LifeTable Premium Reserve.
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(****************************************************************************************)

Section Example1.

Variable l:life.
Hypothesis l_fin : (l_finite l).

Notation "\p_{ t & u }" := (\p[l]_{t&u}) (at level 9).
Notation "'ω'" := (ω[l,l_fin]) (at level 8).

Notation "\a''[ i ]_{ x : n }" := (\a''[i,l]_{x:n}) (at level 9, x at level 9).

Lemma ann_due_decr_i : forall (i i' : R) (x n : nat), i > 0 -> i' > 0 -> x < ω ->
  i <= i' -> \a''[i]_{x:n} >= \a''[i']_{x:n}.
Proof.
  move => i i' x n Hipos Hi'pos Hx Hleii'.
  assert (Hvpos : 0 < \v[i]) by (apply /v_pos /Hipos).
  assert (Hv'pos : 0 < \v[i']) by (apply /v_pos /Hi'pos).
  rewrite /life_ann_due.
  apply Rsum_ge_compat => k /andP; case => /leP Hmk /ltP Hkn.
  apply Rmult_ge_compat_r; [by apply (p_nonneg _ l_fin) |].
  case: (zerop k) => [Hk0 | Hkpos].
  - rewrite Hk0 !Rpower_O //; lra.
  - case: (Rle_lt_or_eq_dec i i') => // [Hlt | Heq].
    + rewrite /Rpower.
      apply /Rgt_ge /exp_increasing.
      apply Rmult_lt_compat_l; [rewrite (_ : 0 = INR 0%N) //; apply lt_INR => // |].
      apply ln_increasing => //.
      rewrite /v_pres.
      apply Rinv_1_lt_contravar; lra.
    + rewrite Heq; lra.
Qed.

End Example1.

(****************************************************************************************)

Section Example2.

Variable i:R.
Hypothesis i_pos : i > 0.

Variable l:life.
Hypothesis l_fin : (l_finite l).

Notation "'ω'" := (ω[l,l_fin]) (at level 8).
Notation "\A_{ x `1: n }" := (\A[i,l]_{x`1:n}) (at level 9, x at level 9).
Notation "\A_{ x : n `1}" := (\A[i,l]_{x:n`1}) (at level 9, x at level 9).
Notation "\A_{ x : n }" := (\A[i,l]_{x:n}) (at level 9, x at level 9).
Notation "\a''_{ x : n }" := (\a''[i,l]_{x:n}) (at level 9, x at level 9).
Notation "\s''_{ x : n }" := (\s''[i,l]_{x:n}) (at level 9, x at level 9).
Notation "\P_{ x : n }" := (\P[i,l]_{x:n}) (at level 9, x at level 9).
Notation "\V_{ t & x : n }" := (\V[i,l]_{t&x:n}) (at level 9, x at level 9).

Theorem res_eq_pros_retro : forall (t x n : nat), x+t < ω -> t <= n -> n > 0 ->
  \V_{t & x:n} = \P_{x:n} * \s''_{x:t} - \A_{x`1:t} / \A_{x:t`1}.
Proof.
  move => t x n Hxt Htn Hn.
  assert (Hx : x < ω) by (apply lt_INR; move: Hxt; rewrite -plus_INR => /INR_lt; lia).
  assert (Ha'' : \a''_{ x : n} <> 0) by
    (apply /pos_neq0 /(Rge_gt_trans _ 1); [| lra]; by apply (ann_due_ge1 _ i_pos _ l_fin)).
  rewrite (_ : \s''_{x:t} = (\a''_{x:n} / \A_{x:t`1} - \a''_{(x+t):(n-t)})).
  2:{ rewrite -(acc_due_plus_ann_due _ _ _ t) //.
      rewrite /Rdiv (Rmult_assoc _ \A_{x:t`1}) Rinv_r;
        [| apply /pos_neq0 /(ins_pure_endow_pos _ _ l_fin) => //]; lra. }
  rewrite Rmult_plus_distr_l.
  rewrite {1}/prem_endow_life.
  rewrite /Rdiv -Rmult_assoc (Rmult_assoc \A_{_:_}) Rinv_l // Rmult_1_r.
  rewrite /Rminus Rplus_assoc (Rplus_comm _ (-_)) -Rplus_assoc
    -/(Rminus (_*_) (_*_)) -Rmult_minus_distr_r.
  rewrite (_ : (\A_{ x : n} - \A_{ x `1: t}) */ \A_{ x : t`1} = \A_{(x+t):(n-t)}).
  2:{ rewrite (ins_endow_pure_endow _ _ _ t) //.
      rewrite Rplus_comm Ropp_r_simpl_l Rmult_comm -Rmult_assoc Rinv_l;
        [| by apply /pos_neq0 /(ins_pure_endow_pos _ _ l_fin)]; lra. }
  rewrite /res_endow_life; lra.
Qed.

End Example2.
