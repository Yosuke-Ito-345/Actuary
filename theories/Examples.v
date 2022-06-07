Require Import Reals Lra Lia.
From mathcomp Require Import all_ssreflect.
From Coquelicot Require Import Coquelicot.
From Actuary Require Import all_Actuary.
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(****************************************************************************************)

Section Example1.

Variable l:life.
Hypothesis l_fin : (l_finite l).

Notation "\p_{ t & u }" := (\p[l]_{t&u}) (at level 9).
Notation "\ω" := (\ω[l,l_fin]) (at level 8).

Notation "\a''[ i ]_{ x : n }" := (\a''[i,l]_{x:n}) (at level 9, x at level 9).

Lemma ann_due_decr_i : forall (i i' : R) (x n : nat), 0 < i -> 0 < i' -> x < \ω ->
  i <= i' -> \a''[i']_{x:n} <= \a''[i]_{x:n}.
Proof.
  move => i i' x n Hipos Hi'pos Hx Hleii'.
  have Hvpos : 0 < \v[i] by apply /v_pos /Hipos.
  have Hv'pos : 0 < \v[i'] by apply /v_pos /Hi'pos.
  rewrite !ann_due_annual.
  apply Rsum_le_compat => k /andP; case => /leP Hmk /ltP Hkn.
  apply Rmult_le_compat_r; [by apply (p_nonneg _ l_fin) |].
  case: (zerop k) => [Hk0 | Hkpos].
  - rewrite Hk0 !Rpower_O //; lra.
  - case: (Rle_lt_or_eq_dec i i') => // [Hlt | Heq].
    + rewrite /Rpower.
      apply /Rlt_le /exp_increasing.
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
Hypothesis i_pos : 0 < i.

Variable l:life.
Hypothesis l_fin : (l_finite l).

Notation "\ω" := (\ω[l,l_fin]) (at level 8).
Notation "\A_{ x `1: n }" := (\A[i,l]_{x`1:n}) (at level 9, x at level 9).
Notation "\A_{ x : n `1}" := (\A[i,l]_{x:n`1}) (at level 9, x at level 9).
Notation "\A_{ x : n }" := (\A[i,l]_{x:n}) (at level 9, x at level 9).
Notation "\a''_{ x : n }" := (\a''[i,l]_{x:n}) (at level 9, x at level 9).
Notation "\s''_{ x : n }" := (\s''[i,l]_{x:n}) (at level 9, x at level 9).
Notation "\P_{ x : n }" := (\P[i,l]_{x:n}) (at level 9, x at level 9).
Notation "\V_{ t & x : n }" := (\V[i,l]_{t&x:n}) (at level 9, x at level 9).

Theorem res_eq_pros_retro : forall (t x n : nat), x+t < \ω -> t <= n -> 0 < n ->
  \V_{t & x:n} = \P_{x:n} * \s''_{x:t} - \A_{x`1:t} / \A_{x:t`1}.
Proof.
  move => t x n Hxt Htn Hn.
  have Hx : x < \ω by apply lt_INR; move: Hxt; rewrite -plus_INR => /INR_lt; lia.
  have Ha'' : \a''_{ x : n} <> 0.
  { apply /pos_neq0.
    eapply Rlt_le_trans; [| apply (ann_due_lb _ i_pos _ l_fin) => //].
      by apply Rinv_0_lt_compat. }
  rewrite (_ : \s''_{x:t} = (\a''_{x:n} / \A_{x:t`1} - \a''_{(x+t):(n-t)})).
  2:{ rewrite -(acc_due_plus_ann_due _ _ _ _ t) //.
      rewrite /Rdiv (Rmult_assoc _ \A_{x:t`1}) Rinv_r;
        [| apply /pos_neq0 /(ins_pure_endow_pos _ _ l_fin) => //]; lra. }
  rewrite Rmult_plus_distr_l.
  rewrite {1}/prem_endow_life.
  rewrite /Rdiv -Rmult_assoc (Rmult_assoc \A_{_:_}) Rinv_l // Rmult_1_r.
  rewrite /Rminus Rplus_assoc (Rplus_comm _ (-_)) -Rplus_assoc
    -/(Rminus (_*_) (_*_)) -Rmult_minus_distr_r.
  rewrite (_ : (\A_{x:n} - \A_{x `1:t}) */ \A_{x:t`1} = \A_{(x+t):(n-t)}).
  2:{ rewrite (ins_endow_pure_endow _ _ _ _ t) //.
      rewrite Rplus_comm Ropp_r_simpl_l Rmult_comm -Rmult_assoc Rinv_l;
        [| by apply /pos_neq0 /(ins_pure_endow_pos _ _ l_fin)]; lra. }
  rewrite /res_endow_life; lra.
Qed.

End Example2.

(****************************************************************************************)

Section Example3.

Variable i:R.
Hypothesis i_pos : 0 < i.

Variable l:life.
Hypothesis l_fin : (l_finite l).
Hypothesis l_C1 : forall u:R, ex_derive l u /\ continuous (Derive l) u.

Notation "\δ" := (\δ[i]) (at level 9).
Notation "\v" := (\v[i]) (at level 9).
Notation "\l_ u" := (\l[l]_u) (at level 9). 
Notation "\ψ" := (\ψ[l]) (at level 8).
Notation "\μ_ u" := (\μ[l]_u) (at level 9).
Notation "\A_{ u : n `1}" := (\A[i,l]_{u:n`1}) (at level 9, u at level 9).
Notation "\Abar_{ u `1: n }" := (\Abar[i,l]_{u`1:n}) (at level 9, u at level 9).
Notation "\Abar_{ u : n }" := (\Abar[i,l]_{u:n}) (at level 9, u at level 9).
Notation "\abar_{ u : n }" := (\abar[i,l]_{u:n}) (at level 9, u at level 9).
Notation "\Pbar^{p_infty}_{ u : n }" :=
  (\Pbar[i,l]^{p_infty}_{u:n}) (at level 9, u at level 9).
Notation "\Vbar^{p_infty}_{ t & u : n }" :=
  (\Vbar[i,l]^{p_infty}_{t&u:n}) (at level 9, u at level 9).

Theorem Thiele_ODE : forall t u n : R, u+t < \ψ ->
  is_derive (fun t:R => \Vbar^{p_infty}_{t & u:n}) t
    (\Pbar^{p_infty}_{u:n} - \μ_(u+t) + (\δ + \μ_(u+t)) * \Vbar^{p_infty}_{t & u:n}).
Proof.
  move => t u n Hut.
  set (eps := \ψ - (u+t)).
  have Heps : 0 < eps by rewrite /eps; lra.
  set (Reps := mkposreal eps Heps).
  have HexDpowv : ex_derive [eta Rpower \v] t by apply ex_derive_Rpower_snd.
  have Hut'Rbar : forall t':R, u+t' < \ψ -> Rbar_lt (u+t') \ψ
      by move => t' Ht'; rewrite -psi_finite //.
  have Hvneq0 : forall t':R, u+t' < \ψ -> \v^t' <> 0 by move => t' Ht'; apply /pos_neq0 /exp_pos.
  have Hlneq0 : forall t':R, u+t' < \ψ -> \l_(u+t') <> 0
      by move => t' Ht'; apply /pos_neq0 /l_u_pos; auto.
  have HC0vl : forall r:R, continuous (fun r:R => \v^r * \l_(u+r)) r.
  { move => r.
    apply (continuous_mult (Rpower \v)); [apply continuous_Rpower_snd |].
    apply continuous_comp;
      [apply continuous_Rplus_snd | apply (ex_derive_continuous l); apply l_C1]. }
  have HC0vDl : forall r:R, continuous (fun r:R => \v^r * Derive l (u+r)) r.
  { move => r.
    apply (continuous_mult (Rpower \v)); [apply continuous_Rpower_snd |].
    apply continuous_comp; [apply continuous_Rplus_snd | apply l_C1]. }
  have Hterm : forall t':R, u+t' < \ψ ->
    \Abar_{(u+t')`1:(n-t')} =
    - / (\v^t' * \l_(u+t')) * RInt (fun r:R => \v^r * Derive l (u+r)) t' n.
  { move => t' Hut'.
    rewrite /ins_term_life_cont.
    under RInt_ext => s Hs.
    { rewrite Derive_incr; [| apply l_C1].
      rewrite Rplus_assoc (Rplus_comm t' s).
      rewrite {1}(_ : s = s + t' - t'); [| lra].
      rewrite /Rminus Rpower_plus Rpower_Ropp (Rmult_comm _ (/ \v^t')).
      rewrite Rmult_assoc {1}(_ : Rmult = scal) //.
      over. }
    rewrite RInt_scal /scal /= /mult /=.
    2:{ apply ex_RInt_continuous => r _.
          by apply (continuous_comp _ (fun r:R => \v^r * Derive l (u+r)));
            [apply continuous_Rplus_fst |]. }
    rewrite (@RInt_comp_plus _ (fun r:R => \v^r * Derive l (u+r)));
      [| by apply ex_RInt_continuous => r _].
    rewrite Rplus_0_l (_ : n - t' + t' = n); [| lra].
    field; auto. }
  have Hpureendow : forall t':R, u+t' < \ψ ->
    \A_{(u+t'):(n-t')`1} = (\v^n * \l_(u+n)) / (\v^t' * \l_(u+t')).
  { move => t' Ht'.
    rewrite /ins_pure_endow_life /survive.
    rewrite (_ : u+t'+(n-t') = u+n); [| lra].
    rewrite /Rminus Rpower_plus Rpower_Ropp.
    field; auto. }
  have Hann : forall t':R, u+t' < \ψ ->
    \abar_{(u+t'):(n-t')} = / (\v^t' * \l_(u+t')) * RInt (fun r:R => \v^r * \l_(u+r)) t' n.
  { move => t' Hut'.
    rewrite /life_ann_cont /survive.
    under RInt_ext => s Hs.
    { rewrite Rplus_assoc (Rplus_comm t' s).
      rewrite {1}(_ : s = s + t' - t'); [| lra].
      rewrite (_ : \v^(s+t'-t') * (\l_(u+(s+t')) / \l_(u+t')) =
                   / (\v^t' * \l_(u+t')) * (\v^(s+t') * \l_(u+(s+t'))));
        [| rewrite /Rminus Rpower_plus Rpower_Ropp; field; auto].
      over. }
    rewrite {1}(_ : Rmult = scal) // RInt_scal /scal /= /mult /=.
    - rewrite (@RInt_comp_plus _ (fun r:R => \v^r * \l_(u+r)));
        [| by apply ex_RInt_continuous => r _].
      by rewrite Rplus_0_l (_ : n-t'+t' = n); [| lra].
    - apply ex_RInt_continuous => r _.
        by apply (continuous_comp _ (fun r:R => \v^r * \l_(u+r)));
          [apply continuous_Rplus_fst |]. }
  rewrite /res_cont_endow_life_cont /ins_endow_life_cont.
  rewrite Hterm //.
  rewrite Hpureendow //.
  rewrite Hann //.
  apply (is_derive_ext_loc (fun t':R =>
    - /(\v^t'*\l_(u+t')) * RInt (fun r:R => \v^r * Derive l (u+r)) t' n
    + \v^n * \l_(u+n) / (\v^t'*\l_(u+t'))
    - \Pbar^{p_infty}_{u:n} * /(\v^t'*\l_(u+t')) * RInt (fun r:R => \v^r * \l_(u+r)) t' n
  )).
  { exists Reps => t' Ht'.
    have Ht'' : u+t' < \ψ
      by move: Ht'; rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /= /eps;
      case /Rabs_def2; lra.
    rewrite Hterm //.
    rewrite Hpureendow //.
    rewrite Hann //.
    lra. }
  auto_derive; try repeat split; auto; try apply l_C1.
  1,3 : by apply @ex_RInt_continuous.
  1,2 : by exists Reps => t' Ht'; apply continuity_pt_continuous.
  rewrite (is_derive_unique _ _ _ (is_derive_vpow i_pos t)).
  rewrite /d_force (_ : Derive [eta l] (u+t) = Derive l (u+t)) //.
  field; auto.
Qed.

End Example3.

Section Example4.

(* In this section, we consider verifying a problem of life insurance mathematics. *)

(* Problem 1 (3). *)
(* (Translated from the examination of Life Insurance Mathematics, 2019, *)
(* the Institute of Actuaries of Japan.) *)
(* Suppose \A_x = 0.8499, \A_(x+1) = 0.8573, \i = 0.015. *)
(* Then select the value closest to \p_x among the alternatives. *)
(* (A) 0.9610  (B) 0.9613  (C) 0.9616  (D) 0.9619  (E) 0.9622 *)
(* (F) 0.9625  (G) 0.9628  (H) 0.9631  (I) 0.9634  (J) 0.9637 *)
(* Solution. *)
(* (F) *)
  
Variable i:R.
Hypothesis i_pos : 0 < i.

Variable l:life.
Hypothesis l_fin : (l_finite l).

Notation "\i" := (\i[i]) (at level 9).
Notation "\v" := (\v[i]) (at level 9).
Notation "\l_ u" := (\l[l]_u) (at level 9). 
Notation "\p_ u" := (\p[l]_{1&u}) (at level 9).
Notation "\q_{ f | t & u }" := (\q[l]_{f|t&u}) (at level 9).
Notation "\q_ u" := (\q_{0|1 & u}) (at level 9).
Notation "\ω" := (\ω[l,l_fin]) (at level 8).
Notation "\A_ x" := (\A[i,l,l_fin]_x) (at level 9).

Theorem Exam_2019_1_3 : forall x:nat, x+1 < \ω ->
  \A_x = 0.8499 -> \A_(x+1) = 0.8573 -> \i = 0.015 -> 0.96235 < \p_x < 0.96265.
Proof.
  move => x Hx HAx HAx1 Hi.
  have Hpx : \p_x = (1 - (1+\i)*\A_x) / (1 - \A_(x+1)).
  { move: (ins_whole_rec \i i_pos l l_fin x Hx).
    rewrite (_ : \q_{0|1&x} = 1 - \p_x);
      [| rewrite -{2}(p_q_1 l 1 x); [lra | apply /pos_neq0 /l_x_pos; lra]].
    rewrite /v_pres => ->; field; lra. }
  rewrite Hpx HAx HAx1 Hi; lra.
Qed.

End Example4.

Section Example5.

(* In this section, we consider verifying the formula of a gross premium. *)

Variable i:R.
Hypothesis i_pos : 0 < i.

Variable l:life.
Hypothesis l_fin : (l_finite l).

Notation "\i" := (\i[i]) (at level 9).
Notation "\v" := (\v[i]) (at level 9).
Notation "\ω" := (\ω[l,l_fin]) (at level 8).
Notation "\A_{ x : n }" := (\A[i,l]_{x:n}) (at level 9, x at level 9).
Notation "\a''_{ x : n }" := (\a''[i,l]_{x:n}) (at level 9, x at level 9).

(* initial expense *)
(* The expense α per unit insurance amount is paid at the beginning of the first year. *)
Variable α:R.
Hypothesis alpha_pos : 0 < α.

(* collection expense *)
(* The expense β per unit premium is paid at the beginning of each year. *)
Variable β:R.
Hypothesis beta_in_0_1 : 0 < β < 1.

(* maintenance expense *)
(* The expense γ per unit insurance amount is paid at the beginning of each year. *)
Variable γ:R.
Hypothesis gamma_pos : 0 < γ.

(* annual gross premium of an endowment life insurance *)
Definition gross_prem_endow_life_annual (x n : nat) :=
  (\A_{x:n} + α + γ * \a''_{x:n}) / ((1-β) * \a''_{x:n}).
Notation "\Pstar_{ x : n }" := (gross_prem_endow_life_annual x n) (at level 9, x at level 9).

(* Verify that the gross premium satisfies the equivalence principle. *)
Theorem gross_prem_endow_life_annual_correct : forall x n : nat, x < \ω -> 0 < n ->
  \Pstar_{x:n} * \a''_{x:n} = \A_{x:n} + α + (\Pstar_{x:n}*β + γ) * \a''_{x:n}.
Proof.
  move => x n Hx Hn.
  rewrite /gross_prem_endow_life_annual.
  field; split; [| lra].
  apply pos_neq0; eapply Rlt_le_trans;
    [| apply (ann_due_lb _ i_pos _ l_fin)]; first apply Rinv_0_lt_compat; auto.
Qed.

End Example5.
