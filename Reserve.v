Require Export Reals Lra Lia.
From mathcomp Require Import all_ssreflect.
From Coquelicot Require Import Coquelicot.
From Actuary Require Export Basics Interest LifeTable Premium.
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope nat_scope with N.

(****************************************************************************************)

(* the reserve for a term life insurance *)
Definition res_term_life (i:R) (l:life) (m t x n : nat) :=
  \A[i,l]^{m}_{(x+t)`1:(n-t)} - \P[i,l]^{m}_{x`1:n} * \a''[i,l]^{m}_{(x+t):(n-t)}.
Notation "\V[ i , l ]^{ m }_{ t & x `1: n }" :=
  (res_term_life i l m t x n) (at level 9, x at level 9).
Notation "\V[ i , l ]_{ t & x `1: n }" :=
  (\V[i,l]^{1}_{t & x`1:n}) (at level 9, x at level 9).
Definition res_term_life_cont (i:R) (l:life) (m t x n : nat) :=
  \Abar[i,l]_{(x+t)`1:(n-t)} - \Pbar[i,l]^{m}_{x`1:n} * \a''[i,l]^{m}_{(x+t):(n-t)}.
Notation "\Vbar[ i , l ]^{ m }_{ t & x `1: n }" :=
  (res_term_life_cont i l m t x n) (at level 9, x at level 9).
Notation "\Vbar[ i , l ]_{ t & x `1: n }" :=
  (\Vbar[i,l]^{1}_{t & x`1:n}) (at level 9, x at level 9).
Definition res_cont_term_life_cont (i:R) (l:life) (t u n : R) :=
  \Abar[i,l]_{(u+t)`1:(n-t)} - \Pbar[i,l]^{p_infty}_{u`1:n} * \abar[i,l]_{(u+t):(n-t)}.
Notation "\Vbar[ i , l ]^{p_infty}_{ t & u `1: n }" :=
  (res_cont_term_life_cont i l t u n) (at level 9, u at level 9).

(* the reserve for a whole life insurance *)
Definition res_whole_life (i:R) (l:life) (l_fin : l_finite l) (m t x : nat) :=
  \A[i,l,l_fin]^{m}_(x+t) - \P[i,l,l_fin]^{m}_x * \a''[i,l,l_fin]^{m}_(x+t).
Notation "\V[ i , l , l_fin ]^{ m }_{ t & x }" :=
  (res_whole_life i l l_fin m t x) (at level 9, x at level 9).
Notation "\V[ i , l , l_fin ]_{ t & x }" :=
  (\V[i,l,l_fin]^{1}_{t&x}) (at level 9, x at level 9).
Definition res_whole_life_cont (i:R) (l:life) (l_fin : l_finite l) (m t x : nat) :=
  \Abar[i,l,l_fin]_(x+t) - \Pbar[i,l,l_fin]^{m}_x * \a''[i,l,l_fin]^{m}_(x+t).
Notation "\Vbar[ i , l , l_fin ]^{ m }_{ t & x }" :=
  (res_whole_life_cont i l l_fin m t x) (at level 9, x at level 9).
Notation "\Vbar[ i , l , l_fin ]_{ t & x }" :=
  (\Vbar[i,l,l_fin]^{1}_{t&x}) (at level 9, x at level 9).
Definition res_cont_whole_life_cont (i:R) (l:life) (l_fin : l_finite l) (t u : R) :=
  \Abar[i,l,l_fin]_(u+t) - \Pbar[i,l,l_fin]^{p_infty}_u * \abar[i,l,l_fin]_(u+t).
Notation "\Vbar[ i , l , l_fin ]^{p_infty}_{ t & u }" :=
  (res_cont_whole_life_cont i l l_fin t u) (at level 9, u at level 9).

(* the reserve for an endowment life insurance *)
Definition res_endow_life (i:R) (l:life) (m t x n : nat) :=
  \A[i,l]^{m}_{(x+t):(n-t)} - \P[i,l]^{m}_{x:n} * \a''[i,l]^{m}_{(x+t):(n-t)}.
Notation "\V[ i , l ]^{ m }_{ t & x : n }" :=
  (res_endow_life i l m t x n) (at level 9, x at level 9).
Notation "\V[ i , l ]_{ t & x : n }" := (\V[i,l]^{1}_{t & x:n}) (at level 9, x at level 9).
Definition res_endow_life_cont (i:R) (l:life) (m t x n : nat) :=
  \Abar[i,l]_{(x+t):(n-t)} - \Pbar[i,l]^{m}_{x:n} * \a''[i,l]^{m}_{(x+t):(n-t)}.
Notation "\Vbar[ i , l ]^{ m }_{ t & x : n }" :=
  (res_endow_life_cont i l m t x n) (at level 9, x at level 9).
Notation "\Vbar[ i , l ]_{ t & x : n }" :=
  (\Vbar[i,l]^{1}_{t & x:n}) (at level 9, x at level 9).
Definition res_cont_endow_life_cont (i:R) (l:life) (t u n : R) :=
  \Abar[i,l]_{(u+t):(n-t)} - \Pbar[i,l]^{p_infty}_{u:n} * \abar[i,l]_{(u+t):(n-t)}.
Notation "\Vbar[ i , l ]^{p_infty}_{ t & u : n }" :=
  (res_cont_endow_life_cont i l t u n) (at level 9, u at level 9).

(****************************************************************************************)

Section Reserve.

Variable i:R.
Hypothesis i_pos : 0 < i.

Variable l:life.
Hypothesis l_fin : (l_finite l).

Notation "\i" := (\i[i]) (at level 9).
Notation "\i^{ m }" := (\i[i]^{m}) (at level 9).
Notation "\d^{ m }" := (\d[i]^{m}) (at level 9).
Notation "\d" := (\d^{1}) (at level 9).
Notation "\δ" := (\δ[i]) (at level 9).
Notation "\v" := (\v[i]) (at level 9).
Notation "\a^{ m }_: n" := (\a[i]^{m}_:n) (at level 9).
Notation "\a_: n" := (\a[i]_:n) (at level 9).
Notation "\s^{ m }_: n" := (\s[i]^{m}_:n) (at level 9).
Notation "\s_: n" := (\s[i]_:n) (at level 9).
Notation "\a''^{ m }_: n" := (\a''[i]^{m}_:n) (at level 9).
Notation "\a''_: n" := (\a''[i]_:n) (at level 9).
Notation "\s''^{ m }_: n" := (\s''[i]^{m}_:n) (at level 9).
Notation "\s''_: n" := (\s''[i]_:n) (at level 9).
Notation "\abar_: n" := (\abar[i]_:n) (at level 9).
Notation "\sbar_: n" := (\sbar[i]_:n) (at level 9).
Notation "\a^{ m }_:(p_infty)" := (\a[i]^{m}_:(p_infty)) (at level 9).
Notation "\a_:(p_infty)" := (\a[i]_:(p_infty)) (at level 9).
Notation "\a''^{ m }_:(p_infty)" := (\a''[i]^{m}_:(p_infty)) (at level 9).
Notation "\a''_:(p_infty)" := (\a''[i]_:(p_infty)) (at level 9).
Notation "\(I^{ l }a)^{ m }_: n" := (\(I^{l}a)[i]^{m}_:n) (at level 9).
Notation "\(Ia)^{ m }_: n" := (\(Ia)[i]^{m}_:n) (at level 9).
Notation "\(Ia)_: n" := (\(Ia)[i]_:n) (at level 9).
Notation "\(I^{ l }s)^{ m }_: n" := (\(I^{l}s)[i]^{m}_:n) (at level 9).
Notation "\(Is)^{ m }_: n" := (\(Is)[i]^{m}_:n) (at level 9).
Notation "\(Is)_: n" := (\(Is)[i]_:n) (at level 9).
Notation "\(I^{ l }a'')^{ m }_: n" := (\(I^{l}a'')[i]^{m}_:n) (at level 9).
Notation "\(Ia'')^{ m }_: n" := (\(Ia'')[i]^{m}_:n) (at level 9).
Notation "\(Ia'')_: n" := (\(Ia'')[i]_:n) (at level 9).
Notation "\(I^{ l }s'')^{ m }_: n" := (\(I^{l}s'')[i]^{m}_:n) (at level 9).
Notation "\(Is'')^{ m }_: n" := (\(Is'')[i]^{m}_:n) (at level 9).
Notation "\(Is'')_: n" := (\(Is'')[i]_:n) (at level 9).
Notation "\(I^{ l }a)^{ m }_:(p_infty)" := (\(I^{l}a)[i]^{m}_:(p_infty)) (at level 9).
Notation "\(I^{ l }a'')^{ m }_:(p_infty)" := (\(I^{l}a'')[i]^{m}_:(p_infty)) (at level 9).
Notation "\(Ia)_:(p_infty)" := (\(Ia)[i]_:(p_infty)) (at level 9).
Notation "\(Ia'')_:(p_infty)" := (\(Ia'')[i]_:(p_infty)) (at level 9).

Notation "\l_ u" := (\l[l]_u) (at level 9). 
Notation "\ψ" := (\ψ[l]) (at level 8).
Notation "\d_ u" := (\d[l]_u) (at level 9).
Notation "\p_{ t & u }" := (\p[l]_{t&u}) (at level 9).
Notation "\p_ u" := (\p[l]_{1&u}) (at level 9).
Notation "\q_{ f | t & u }" := (\q[l]_{f|t&u}) (at level 9).
Notation "\q_{ t & u }" := (\q_{0|t & u}) (at level 9).
Notation "\q_{ f | & u }" := (\q_{f|1 & u}) (at level 9).
Notation "\q_ u" := (\q_{0|1 & u}) (at level 9).
Notation "\μ_ u" := (\μ[l]_u) (at level 9).
Notation "\e_{ x : n }" := (\e[l]_{x:n}) (at level 9, x at level 9).
Notation "\ω" := (\ω[l,l_fin]) (at level 8).
Notation "\e_ x" := (\e[l,l_fin]_ x) (at level 9).
Notation "\e`o_{ u : t }" := (\e`o[l,l_fin]_{u:t}) (at level 9, u at level 9).
Notation "\e`o_ u" := (\e`o[l,l_fin]_u) (at level 9).

Notation "\A_{ u : n `1}" := (\A[i,l]_{u:n`1}) (at level 9, u at level 9).
Notation "\A^{ m }_{ x `1: n }" := (\A[i,l]^{m}_{x`1:n}) (at level 9, x at level 9).
Notation "\A_{ x `1: n }" := (\A[i,l]_{x`1:n}) (at level 9, x at level 9).
Notation "\Abar_{ u `1: n }" := (\Abar[i,l]_{u`1:n}) (at level 9, u at level 9).
Notation "\A^{ m }_ x" := (\A[i,l,l_fin]^{m}_x) (at level 9).
Notation "\A_ x" := (\A[i,l,l_fin]_x) (at level 9).
Notation "\Abar_ u" := (\Abar[i,l,l_fin]_ u) (at level 9).
Notation "\A^{ m }_{ x : n }" := (\A[i,l]^{m}_{x:n}) (at level 9, x at level 9).
Notation "\A_{ x : n }" := (\A[i,l]_{x:n}) (at level 9, x at level 9).
Notation "\Abar_{ u : n }" := (\Abar[i,l]_{u:n}) (at level 9, u at level 9).

Notation "\a^{ m }_{ x : n }" := (\a[i,l]^{m}_{x:n}) (at level 9, x at level 9).
Notation "\a_{ x : n }" := (\a[i,l]_{x:n}) (at level 9, x at level 9).
Notation "\abar_{ u : n }" := (\abar[i,l]_{u:n}) (at level 9, u at level 9).
Notation "\s^{ m }_{ x : n }" := (\s[i,l]^{m}_{x:n}) (at level 9, x at level 9).
Notation "\s_{ x : n }" := (\s[i,l]_{x:n}) (at level 9, x at level 9).
Notation "\sbar_{ u : n }" := (\sbar[i,l]_{u:n}) (at level 9, u at level 9).

Notation "\a''^{ m }_{ x : n }" := (\a''[i,l]^{m}_{x:n}) (at level 9, x at level 9).
Notation "\a''_{ x : n }" := (\a''[i,l]_{x:n}) (at level 9, x at level 9).
Notation "\s''^{ m }_{ x : n }" := (\s''[i,l]^{m}_{x:n}) (at level 9, x at level 9).
Notation "\s''_{ x : n }" := (\s''[i,l]_{x:n}) (at level 9, x at level 9).
Notation "\a^{ m }_ x" := (\a[i,l,l_fin]^{m}_x) (at level 9).
Notation "\a_ x" := (\a[i,l,l_fin]_x) (at level 9).
Notation "\a''^{ m }_ x" := (\a''[i,l,l_fin]^{m}_x) (at level 9).
Notation "\a''_ x" := (\a''[i,l,l_fin]_x) (at level 9).
Notation "\abar_ u" := (\abar[i,l,l_fin]_ u) (at level 9, u at level 9).

Notation "\P^{ m }_{ x `1: n }" := (\P[i,l]^{m}_{x`1:n}) (at level 9, x at level 9).
Notation "\P_{ x `1: n }" := (\P[i,l]_{x`1:n}) (at level 9, x at level 9).
Notation "\Pbar^{ m }_{ x `1: n }" := (\Pbar[i,l]^{m}_{x`1:n}) (at level 9, x at level 9).
Notation "\Pbar_{ x `1: n }" := (\Pbar[i,l]_{x`1:n}) (at level 9, x at level 9).
Notation "\Pbar^{p_infty}_{ u `1: n }" :=
  (\Pbar[i,l]^{p_infty}_{u`1:n}) (at level 9, u at level 9).
Notation "\P^{ m }_ x" := (\P[i,l,l_fin]^{m}_x) (at level 9).
Notation "\P_ x" := (\P[i,l,l_fin]_x) (at level 9).
Notation "\Pbar^{ m }_ x" := (\Pbar[i,l,l_fin]^{m}_x) (at level 9).
Notation "\Pbar_ x" := (\Pbar[i,l,l_fin]_x) (at level 9).
Notation "\Pbar^{p_infty}_ u" := (\Pbar[i,l,l_fin]^{p_infty}_u) (at level 9).
Notation "\P^{ m }_{ x : n `1}" := (\P[i,l]^{m}_{x:n`1}) (at level 9, x at level 9).
Notation "\P_{ x : n `1}" := (\P[i,l]_{x:n`1}) (at level 9, x at level 9).
Notation "\P^{p_infty}_{ u : n `1}" :=
  (\P[i,l]^{p_infty}_{u:n`1}) (at level 9, u at level 9).
Notation "\P^{ m }_{ x : n }" := (\P[i,l]^{m}_{x:n}) (at level 9, x at level 9).
Notation "\P_{ x : n }" := (\P[i,l]^{1}_{x:n}) (at level 9, x at level 9).
Notation "\Pbar^{ m }_{ x : n }" := (\Pbar[i,l]^{m}_{x:n}) (at level 9, x at level 9).
Notation "\Pbar_{ x : n }" := (\Pbar[i,l]_{x:n}) (at level 9, x at level 9).
Notation "\Pbar^{p_infty}_{ u : n }" :=
  (\Pbar[i,l]^{p_infty}_{u:n}) (at level 9, u at level 9).

Notation "\V^{ m }_{ t & x `1: n }" := (\V[i,l]^{m}_{t&x`1:n}) (at level 9, x at level 9).
Notation "\V_{ t & x `1: n }" := (\V[i,l]_{t&x`1:n}) (at level 9, x at level 9).
Notation "\Vbar^{ m }_{ t & x `1: n }" :=
  (\Vbar[i,l]^{m}_{t&x`1:n}) (at level 9, x at level 9).
Notation "\Vbar_{ t & x `1: n }" := (\Vbar[i,l]_{t&x`1:n}) (at level 9, x at level 9).
Notation "\Vbar^{p_infty}_{ t & u `1: n }" :=
  (\Vbar[i,l]^{p_infty}_{t&u`1:n}) (at level 9, u at level 9).
Notation "\V^{ m }_{ t & x }" := (\V[i,l,l_fin]^{m}_{t&x}) (at level 9, x at level 9).
Notation "\V_{ t & x }" := (\V[i,l,l_fin]_{t&x}) (at level 9, x at level 9).
Notation "\Vbar^{ m }_{ t & x }" := (\Vbar[i,l,l_fin]^{m}_{t&x}) (at level 9, x at level 9).
Notation "\Vbar_{ t & x }" := (\Vbar[i,l,l_fin]_{t&x}) (at level 9, x at level 9).
Notation "\Vbar^{p_infty}_{ t & u }" :=
  (\Vbar[i,l,l_fin]^{p_infty}_{t&u}) (at level 9, u at level 9).
Notation "\V^{ m }_{ t & x : n }" := (\V[i,l]^{m}_{t&x:n}) (at level 9, x at level 9).
Notation "\V_{ t & x : n }" := (\V[i,l]_{t&x:n}) (at level 9, x at level 9).
Notation "\Vbar^{ m }_{ t & x : n }" := (\Vbar[i,l]^{m}_{t&x:n}) (at level 9, x at level 9).
Notation "\Vbar_{ t & x : n }" := (\Vbar[i,l]_{t&x:n}) (at level 9, x at level 9).
Notation "\Vbar^{p_infty}_{ t & u : n }" :=
  (\Vbar[i,l]^{p_infty}_{t&u:n}) (at level 9, u at level 9).

Hint Resolve i_nom_pos i_nom_add_pos delta_pos d_nom_pos v_pos lt_v_1 v_in_0_1 : core.
Hint Resolve l_0_pos l_neg_nil l_infty_0 l_decr l_nonneg psi_nonneg l_u_pos : core.
Hint Resolve psi_finite omega_pos l_x_pos : core.

Lemma res_term_life_0_0 : forall m x n : nat, 0 < m -> x < \ω -> 0 < n -> \V^{m}_{0 & x`1:n} = 0.
Proof.
  move => m x n Hm Hx Hn.
  rewrite /res_term_life /prem_term_life.
  rewrite addn0 subn0.
  rewrite /Rdiv Rmult_assoc Rinv_l;
    [| apply pos_neq0; eapply Rlt_le_trans;
       [| apply (ann_due_lb _ i_pos _ l_fin); auto]; by apply Rinv_0_lt_compat].
  lra.
Qed.

Lemma res_whole_life_0_0 : forall m x : nat, 0 < m -> x < \ω -> \V^{m}_{0 & x} = 0.
Proof.
  move => m x Hm Hx.
  have Hx' : (x < \ω)%coq_nat by apply INR_lt; lra.
  have Hx'' :  0 < (\ω - x)%N by apply (lt_INR 0); rewrite SSR_minus; lia.
  rewrite /res_whole_life /prem_whole_life.
  rewrite addn0.
  rewrite /Rdiv Rmult_assoc Rinv_l; [lra |].
  apply pos_neq0; eapply Rlt_le_trans;
    [| apply (ann_due_lb _ i_pos _ l_fin); auto]; by apply Rinv_0_lt_compat.
Qed.

Lemma res_endow_life_0_0 : forall m x n : nat, 0 < m -> x < \ω -> 0 < n -> \V^{m}_{0 & x:n} = 0.
Proof.
  move => m x n Hm Hx Hn.
  rewrite /res_endow_life /prem_endow_life.
  rewrite addn0 subn0.
  rewrite /Rdiv Rmult_assoc Rinv_l; [lra |].
  apply pos_neq0; eapply Rlt_le_trans;
    [| apply (ann_due_lb _ i_pos _ l_fin); auto]; by apply Rinv_0_lt_compat.
Qed.

Lemma res_term_life_n_0 : forall m x n : nat, 0 < m -> x < \ω -> \V^{m}_{n & x`1:n} = 0.
Proof.
  move => m x n Hm Hx.
  rewrite /res_term_life.
  rewrite subnn.
  rewrite ins_term_0_0 // ann_due_0_0; lra.
Qed.

Lemma res_endow_life_n_1 : forall m x n : nat, 0 < m -> x+n < \ω -> \V^{m}_{n & x:n} = 1.
Proof.
  move => m x n Hm Hx.
  rewrite /res_endow_life.
  rewrite subnn.
  rewrite ins_endow_0_1 //; [| rewrite plus_INR //].
  rewrite ann_due_0_0; lra.
Qed.

Lemma res_term_whole : forall m t x : nat, 0 < m -> x+t < \ω ->
  \V^{m}_{t & x`1:(\ω-x)} = \V^{m}_{t & x}.
Proof.
  move => m t x Hm Hxt.
  have Hx : x < \ω
    by apply (Rle_lt_trans _ (x+t)); [rewrite -plus_INR; apply le_INR; lia | done].
  have Hxt' : (x+t)%N < \ω by rewrite plus_INR //.
  have Hxt'' : \ω - (x + t)%N <= (\ω - x - t)%N
    by rewrite -subnDA SSR_minus minus_INR; [lra | apply INR_le; lra].
  rewrite /res_whole_life /res_term_life.
  rewrite ins_term_whole //.
  rewrite prem_term_whole //; [| rewrite SSR_minus minus_INR; [| apply INR_le]; lra].
  rewrite ann_due_temp_whole //.
Qed.

Lemma res_endow_whole : forall m t x : nat, 0 < m -> x+t < \ω ->
  \V^{m}_{t & x:(\ω-x)} = \V^{m}_{t & x}.
Proof.
  move => m t x Hm Hxt.
  have Hx : x < \ω
    by apply (Rle_lt_trans _ (x+t)); [rewrite -plus_INR; apply le_INR; lia | done].
  have Hxt' : (x+t)%N < \ω by rewrite plus_INR //.
  have Hxt'' : \ω - (x + t)%N <= (\ω - x - t)%N
    by rewrite -subnDA SSR_minus minus_INR; [lra | apply INR_le; lra].
  rewrite -res_term_whole //.
  rewrite /res_endow_life /res_term_life.
  rewrite ins_endow_whole //.
  rewrite ins_term_whole //.
  rewrite prem_endow_whole //; rewrite SSR_minus minus_INR; [| apply INR_le]; lra.
Qed.  

Lemma res_endow_prem_ann_due : forall m t x n : nat, 0 < m -> x+t < \ω ->
  \V^{m}_{t & x:n} = 1 - (\P^{m}_{x:n} + \d^{m}) * \a''^{m}_{(x+t):(n-t)}.
Proof.
  move => m t x n Hm Hx.
  have Hx' : (x+t)%N < \ω by rewrite plus_INR //.
  rewrite /res_endow_life.
  rewrite ins_endow_ann_due; lra.
Qed.

Lemma res_endow_ann_due : forall m t x n : nat, 0 < m -> x+t < \ω -> 0 < n ->
  \V^{m}_{t & x:n} = 1 - \a''^{m}_{(x+t):(n-t)} / \a''^{m}_{x:n}.
Proof.
  move => m t x n Hm Hx Hn.
  have Hx' : (x+t)%N < \ω by rewrite plus_INR //.
  rewrite res_endow_prem_ann_due //.
  rewrite (_ : \P^{m}_{x:n} + \d^{m} = /(\a''^{m}_{x:n})); [lra |].
  rewrite prem_endow_ann_due_d //; [lra |].
  apply lt_INR; move: Hx' => /INR_lt; apply le_lt_trans.
  rewrite -{1}(addn0 x); apply plus_le_compat_l; lia.
Qed.
  
Lemma res_endow_ins_endow : forall m t x n : nat, 0 < m -> x+t < \ω -> 0 < n ->
  \V^{m}_{t & x:n} = (\A^{m}_{(x+t):(n-t)} - \A^{m}_{x:n}) / (1 - \A^{m}_{x:n}).
Proof.
  move => m t x n Hm Hxt Hn.
  have Hxt' : (x+t)%N < \ω by rewrite plus_INR //.
  have Hx : x < \ω.
  { apply lt_INR; move: Hxt' => /INR_lt; apply le_lt_trans.
    rewrite -{1}(addn0 x); apply plus_le_compat_l; lia. }
  have Hd : \d^{m} <> 0 by apply /pos_neq0 /d_nom_pos => //=; lra.
  have Ha'' : \a''^{m}_{x:n} <> 0
    by  apply pos_neq0; eapply Rlt_le_trans;
    [| apply (ann_due_lb _ i_pos _ l_fin); auto]; by apply Rinv_0_lt_compat.
  rewrite res_endow_ann_due // !ins_endow_ann_due //.
  rewrite /Rminus Ropp_plus_distr -!Rplus_assoc.
  rewrite (Rplus_assoc _ (-(\d^{m} * _))) (Rplus_comm (-(\d^{m} * _))) -Rplus_assoc.
  rewrite Rplus_opp_r !Rplus_0_l.
  rewrite Ropp_involutive Ropp_mult_distr_r.
  rewrite -Rmult_plus_distr_l.
  rewrite /Rdiv Rinv_mult_distr // -Rmult_assoc Rinv_r_simpl_m //.
  rewrite Rmult_plus_distr_r Rinv_r //; lra.
Qed.

Lemma res_endow_prem : forall m t x n : nat, 0 < m -> t < n -> x+t < \ω -> 0 < n ->
  \V^{m}_{t & x:n} = (\P^{m}_{(x+t):(n-t)} - \P^{m}_{x:n}) / (\P^{m}_{(x+t):(n-t)} + \d^{m}).
Proof.
  move => m t x n Hm Htn Hxt Hn.
  have Hxt' : (x+t)%N < \ω by rewrite plus_INR //.
  have Hx : x < \ω.
  { apply lt_INR; move: Hxt' => /INR_lt; apply le_lt_trans.
    rewrite -{1}(addn0 x); apply plus_le_compat_l; lia. }
  have Htn' :  0 < (n - t)%N
    by rewrite SSR_minus minus_INR; [lra | apply INR_le; lra].
  have Ha'' : \a''^{m}_{ (x + t) : n - t} <> 0
    by  apply pos_neq0; eapply Rlt_le_trans;
    [| apply (ann_due_lb _ i_pos _ l_fin); auto]; by apply Rinv_0_lt_compat.
  rewrite res_endow_ann_due // !prem_endow_ann_due_d //.
  rewrite /Rminus Ropp_plus_distr (Rplus_comm _ (--_))
    -Rplus_assoc !(Rplus_assoc _ (-\d^{m})) Rplus_opp_l Rplus_opp_r Rplus_0_r.
  rewrite Rdiv_plus_distr.
  rewrite /Rdiv Rinv_r; [| apply Rinv_neq_0_compat => //]; rewrite Rinv_involutive //; lra.
Qed.

Lemma res_whole_prem_ann_due : forall m t x : nat, 0 < m -> x+t < \ω ->
  \V^{m}_{t & x} = 1 - (\P^{m}_x + \d^{m}) * \a''^{m}_(x+t).
Proof.
  move => m t x Hm Hxt.
  have Hx : x < \ω
    by (apply (Rle_lt_trans _ (x+t)); [rewrite -plus_INR; apply le_INR; lia | done]).
  have Hxt' : (x+t)%N < \ω by rewrite plus_INR //.
  have Hxt'' : \ω - (x + t)%N <= (\ω - x - t)%N
    by (rewrite -subnDA SSR_minus minus_INR; [lra | apply INR_le; lra]).
  rewrite -res_endow_whole //.
  rewrite res_endow_prem_ann_due //.
  rewrite prem_endow_whole //; [| rewrite SSR_minus minus_INR; [lra | apply INR_le; lra]].
  rewrite ann_due_temp_whole //.
Qed.

Lemma res_whole_ann_due : forall m t x : nat, 0 < m -> x+t < \ω ->
  \V^{m}_{t & x} = 1 - \a''^{m}_(x+t) / \a''^{m}_x.
Proof.
  move => m t x Hm Hxt.
  have Hx : x < \ω
    by apply (Rle_lt_trans _ (x+t)); [rewrite -plus_INR; apply le_INR; lia | done].
  have Hxt' : (x+t)%N < \ω by rewrite plus_INR //.
  have Hxt'' : \ω - (x + t)%N <= (\ω - x - t)%N
    by rewrite -subnDA SSR_minus minus_INR; [lra | apply INR_le; lra].
  rewrite -res_endow_whole //.
  rewrite res_endow_ann_due //; [| rewrite SSR_minus minus_INR; [lra | apply INR_le; lra]].
  rewrite ann_due_temp_whole //.
Qed.

Lemma res_whole_ins_whole : forall m t x : nat, 0 < m -> x+t < \ω ->
  \V^{m}_{t & x} = (\A^{m}_(x+t) - \A^{m}_x) / (1 - \A^{m}_x).
Proof.
  move => m t x Hm Hxt.
  have Hx : x < \ω
    by apply (Rle_lt_trans _ (x+t)); [rewrite -plus_INR; apply le_INR; lia | done].
  have Hxt' : (x+t)%N < \ω by rewrite plus_INR //.
  have Hxt'' : \ω - (x + t)%N <= (\ω - x - t)%N
    by rewrite -subnDA SSR_minus minus_INR; [lra | apply INR_le; lra].
  rewrite -res_endow_whole //.
  rewrite res_endow_ins_endow //;
          [| rewrite SSR_minus minus_INR; [lra | apply INR_le; lra]].
  rewrite !ins_endow_whole //;
          rewrite SSR_minus minus_INR; [lra | apply INR_le; lra].
Qed.

Lemma res_whole_prem : forall m t x : nat, 0 < m -> x+t < \ω ->
  \V^{m}_{t & x} = (\P^{m}_(x+t) - \P^{m}_x) / (\P^{m}_(x+t) + \d^{m}).
Proof.
  move => m t x Hm Hxt.
  have Hx : x < \ω
    by apply (Rle_lt_trans _ (x+t)); [rewrite -plus_INR; apply le_INR; lia | done].
  have Htx : t < (\ω - x)%N
    by rewrite SSR_minus minus_INR; [lra | apply INR_le; lra].
  have Hxt' : (x+t)%N < \ω by rewrite plus_INR //.
  have Hxt'' : \ω - (x + t)%N <= (\ω - x - t)%N
    by (rewrite -subnDA SSR_minus minus_INR; [lra | apply INR_le; lra]).
  rewrite -res_endow_whole //.
  rewrite res_endow_prem //;
          [| rewrite SSR_minus minus_INR; [lra | apply INR_le; lra]].
  rewrite !prem_endow_whole //;
          rewrite SSR_minus minus_INR; [lra | apply INR_le; lra].
Qed.

Lemma res_term_rec : forall t x n : nat, 0 < t <= n -> x+t < \ω ->
  \V_{(t-1) & x`1:n} + \P_{x`1:n} - \v * \q_(x+t-1) = \v * \p_(x+t-1) * \V_{t & x`1:n}.
Proof.
  move => t x n [H0t Htn] Hxt.
  have H0t' : (0 < t)%N by apply /ltP /INR_lt => //.
  have Htn' : (t <= n)%N by apply /leP /INR_le => //.
  have H1t : (1 <= t)%coq_nat
   by rewrite (_ : 0 = 0%N) in H0t => //; apply INR_lt in H0t; lia.
  have Ht1n : ((t - 1)%coq_nat <= n)%coq_nat by apply INR_le in Htn; lia.
  have Hx : x < \ω
    by apply (Rle_lt_trans _ (x+t)); [rewrite -plus_INR; apply le_INR; lia | done].
  have Hxt' : (x+t)%N < \ω by rewrite plus_INR //.
  have Hxt'' : (x + (t - 1))%N + 1 < \ω by rewrite plus_INR SSR_minus minus_INR //=; lra.
  have Hnt : 0 < (n - (t - 1))%N by rewrite !SSR_minus !minus_INR //=; lra.
  rewrite /res_term_life.
  rewrite ins_term_rec //.
  rewrite ann_due_rec //.
  rewrite (_ : (x + (t - 1) + 1)%N = (x + t)%N);
    [| rewrite addnBA // subnK // addn_gt0 // H0t'; apply /orP; auto].
  rewrite (_ : (n - (t - 1) - 1)%N = (n - t)%N); [| rewrite subnA // addnK //].
  rewrite (_ : INR (x + (t - 1))%N = x + t -1);
    [| rewrite plus_INR SSR_minus minus_INR // (_ : INR 1%N = 1) //; lra].
  lra.
Qed.

Lemma res_endow_rec : forall t x n : nat, 0 < t <= n -> x+t < \ω ->
  \V_{(t-1) & x:n} + \P_{x:n} - \v * \q_(x+t-1) = \v * \p_(x+t-1) * \V_{t & x:n}.
Proof.
  move => t x n [H0t Htn] Hxt.
  have H0t' : (0 < t)%N by apply /ltP /INR_lt => //.
  have Htn' : (t <= n)%N by apply /leP /INR_le => //.
  have H1t : (1 <= t)%coq_nat
   by rewrite (_ : 0 = 0%N) in H0t => //; apply INR_lt in H0t; lia.
  have Ht1n : ((t - 1)%coq_nat <= n)%coq_nat by apply INR_le in Htn; lia.
  have Hx : x < \ω
    by apply (Rle_lt_trans _ (x+t)); [rewrite -plus_INR; apply le_INR; lia | done].
  have Hxt' : (x+t)%N < \ω by rewrite plus_INR //.
  have Hxt'' : (x + (t - 1))%N < \ω by rewrite plus_INR SSR_minus minus_INR //= //; lra.
  have Hnt : 0 < (n - (t - 1))%N by rewrite !SSR_minus !minus_INR //= //; lra.
  rewrite /res_endow_life.
  rewrite ins_endow_rec //; [| rewrite plus_INR SSR_minus minus_INR //= //; lra].
  rewrite ann_due_rec //; [| rewrite plus_INR SSR_minus minus_INR //=; lra].
  rewrite (_ : (x + (t - 1) + 1)%N = (x + t)%N);
    [| rewrite addnBA // subnK // addn_gt0 // H0t'; apply /orP; auto].
  rewrite (_ : (n - (t - 1) - 1)%N = (n - t)%N); [| rewrite subnA // addnK //].
  rewrite (_ : INR (x + (t - 1))%N = x + t -1);
    [| rewrite plus_INR SSR_minus minus_INR //=; lra].
  lra.
Qed.

Lemma res_whole_rec : forall t x : nat, 0 < t -> x+t < \ω ->
  \V_{(t-1) & x} + \P_x - \v * \q_(x+t-1) = \v * \p_(x+t-1) * \V_{t & x}.
Proof.
  move => t x Ht Hxt.
  have H1t : (1 <= t)%coq_nat
   by rewrite (_ : 0 = 0%N) in Ht => //; apply INR_lt in Ht; lia.
  have Htx : t < (\ω - x)%N
    by rewrite SSR_minus minus_INR; [lra | apply INR_le; lra].
  have Hxt' : x + (t - 1)%N < \ω by rewrite SSR_minus minus_INR //=; lra.
  have Hx : x < \ω
    by apply (Rle_lt_trans _ (x+t)); [rewrite -plus_INR; apply le_INR; lia | done].
  rewrite -!res_endow_whole //.
  rewrite -(prem_endow_whole _ _ l_fin _ _ (\ω-x)) //;
    [| rewrite SSR_minus minus_INR; [lra | apply INR_le; lra]].
  rewrite res_endow_rec //; split; lra.
Qed.

(******************************************************************************)

Hypothesis l_C1 : forall u:R, ex_derive l u /\ continuous (Derive l) u.

Hint Resolve ex_derive_l continuous_l continuous_Derive_l : core.
Hint Resolve l_omega_0 psi_finite omega_pos le_psi_omega l_old_0 : core.

Lemma res_term_life_cont_0_0 : forall m x n : nat, 0 < m -> x < \ω -> 0 < n ->
  \Vbar^{m}_{0 & x`1:n} = 0.
Proof.
  move => m x n Hm Hx Hn.
  rewrite /res_term_life_cont.
  rewrite /prem_term_life_cont.
  rewrite Rplus_0_r Rminus_0_r addn0 subn0.
  field.
  apply pos_neq0.
  eapply Rlt_le_trans; [| apply (ann_due_lb _ i_pos _ l_fin) => //].
    by apply Rinv_0_lt_compat.
Qed.

Lemma res_cont_term_life_cont_0_0 : forall u n : R, u < \ψ -> 0 < n ->
  \Vbar^{p_infty}_{0 & u`1:n} = 0.
Proof.
  move => u n Hu Hn.
  rewrite /res_cont_term_life_cont.
  rewrite /prem_cont_term_life_cont.
  rewrite Rplus_0_r Rminus_0_r.
  field.
    by apply /pos_neq0 /(ann_cont_pos _ i_pos _ l_fin).
Qed.

Lemma res_term_whole_cont : forall m t x : nat, 0 < m -> x+t < \ω ->
  \Vbar^{m}_{t & x`1:(\ω-x)} = \Vbar^{m}_{t & x}.
Proof.
  move => m t x Hm Hxt.
  have Ht' : 0 <= t by apply (le_INR 0); lia.
  have Hxt' : (x + t)%N < \ω by rewrite plus_INR.
  have Hx' : (x <= \ω)%coq_nat by apply INR_le; lra.
  have Ht'' : (t <= \ω - x)%coq_nat by apply INR_le; rewrite minus_INR //; lra.
  have Homegaxt : \ω - (x + t)%N <= (\ω - x - t)%N by rewrite plus_INR !minus_INR //; lra.
  have Hx'' : x < \ω by eapply Rle_lt_trans; [| apply Hxt]; lra.
  have Homegax : \ω - x <= (\ω - x)%N by rewrite minus_INR //; lra.
  have Hxtpsi : x + t < \ψ by rewrite -plus_INR; apply (lt_omega_lt_psi _ l_fin) => //.
  have Hpsixt : \ψ - (x+t) <= (\ω-x)%N - t
    by rewrite minus_INR //; move: (le_psi_omega l l_fin); rewrite -psi_finite //=; lra.
  rewrite /res_term_life_cont /res_whole_life_cont.
  rewrite ins_term_cont_whole_cont //.
  rewrite prem_term_whole_cont //.
  rewrite ann_due_temp_whole //.
Qed.

Lemma res_cont_term_whole : forall t u : R, u+t < \ψ -> 0 <= t ->
  \Vbar^{p_infty}_{t & u`1:(\ψ-u)} = \Vbar^{p_infty}_{t & u}.
Proof.
  move => t u Hut Ht.
  have Hupsi : u < \ψ by eapply Rle_lt_trans; [| apply Hut]; lra.
  rewrite /res_cont_term_life_cont /res_cont_whole_life_cont.
  rewrite ins_term_cont_whole_cont //; [| lra].
  rewrite prem_cont_term_whole //; [| lra].
  rewrite ann_cont_temp_whole //; lra.
Qed.

Lemma res_endow_whole_cont : forall m t x : nat, 0 < m -> x + t < \ω ->
  \Vbar^{m}_{t & x:(\ω-x)} = \Vbar^{m}_{t&x}.
Proof.
  move => m t x Hm Hxt.
  have Ht' : 0 <= t by apply (le_INR 0); lia.
  have Hxt' : (x + t)%N < \ω by rewrite plus_INR. 
  have Hx' : (x <= \ω)%coq_nat by apply INR_le; lra.
  have Ht'' : (t <= \ω - x)%coq_nat by apply INR_le; rewrite minus_INR //; lra.
  have Homegaxt : \ω - (x + t)%N <= (\ω - x - t)%N by rewrite plus_INR !minus_INR //; lra.
  have Hx'' : x < \ω by eapply Rle_lt_trans; [| apply Hxt]; lra.
  have Homegax : \ω - x <= (\ω - x)%N by rewrite minus_INR //; lra.
  have Hxtpsi : x + t < \ψ by rewrite -plus_INR; apply (lt_omega_lt_psi _ l_fin) => //.
  have Hpsixt : \ψ - (x+t) <= (\ω-x)%N - t
    by rewrite minus_INR //; move: (le_psi_omega l l_fin); rewrite -psi_finite //=; lra.
  rewrite /res_endow_life_cont /res_whole_life_cont.
  rewrite ins_endow_cont_whole_cont //.
  rewrite prem_endow_whole_cont //.
  rewrite ann_due_temp_whole //.
Qed.

Lemma res_cont_endow_whole : forall t u : R, u+t < \ψ -> 0 <= t ->
  \Vbar^{p_infty}_{t & u:(\ψ-u)} = \Vbar^{p_infty}_{t & u}.
Proof.
  move => t u Hut Ht.
  have Hupsi : u < \ψ by eapply Rle_lt_trans; [| apply Hut]; lra.
  rewrite /res_cont_endow_life_cont /res_cont_whole_life_cont.
  rewrite ins_endow_cont_whole_cont //; [| lra].
  rewrite prem_cont_endow_whole //; [| lra].
  rewrite ann_cont_temp_whole //; lra.
Qed.

Lemma res_whole_life_cont_0_0 : forall m x : nat, 0 < m -> x < \ω -> \Vbar^{m}_{0 & x} = 0.
Proof.
  move => m x Hm Hx.
  rewrite -res_term_whole_cont //; [| by rewrite Rplus_0_r].
  apply res_term_life_cont_0_0 => //.
  rewrite minus_INR; [| apply INR_le]; lra.
Qed.

Lemma res_cont_whole_life_cont_0_0 : forall u:R, u < \ψ -> \Vbar^{p_infty}_{0 & u} = 0.
Proof.
  move => u Hu.
  rewrite -res_cont_term_whole; [| lra ..].
  apply res_cont_term_life_cont_0_0; lra.
Qed.

Lemma res_endow_life_cont_0_0 : forall m x n : nat, 0 < m -> x < \ω -> 0 < n ->
  \Vbar^{m}_{0 & x:n} = 0.
Proof.
  move => m x n Hm Hx Hn.
  rewrite /res_endow_life_cont.
  rewrite /prem_endow_life_cont.
  rewrite Rplus_0_r Rminus_0_r addn0 subn0.
  field.
  apply pos_neq0.
  eapply Rlt_le_trans; [| apply (ann_due_lb _ i_pos _ l_fin) => //].
    by apply Rinv_0_lt_compat.
Qed.

Lemma res_cont_endow_life_cont_0_0 : forall u n : R, u < \ψ -> 0 < n ->
  \Vbar^{p_infty}_{0 & u:n} = 0.
Proof.
  move => u n Hu Hn.
  rewrite /res_cont_endow_life_cont.
  rewrite /prem_cont_endow_life_cont.
  rewrite Rplus_0_r Rminus_0_r.
  field.
    by apply /pos_neq0 /(ann_cont_pos _ i_pos _ l_fin).
Qed.

Lemma res_term_life_cont_n_0 : forall m x n : nat, 0 < m -> x < \ω -> \Vbar^{m}_{n & x`1:n} = 0.
Proof.
  move => m x n Hm Hx.
  rewrite /res_term_life_cont.
  rewrite Rminus_eq_0 subnn.
  rewrite ins_term_cont_0_0 ann_due_0_0 //.
  lra.
Qed.

Lemma res_cont_term_life_cont_n_0 : forall u n : R, u < \ψ -> \Vbar^{p_infty}_{n & u`1:n} = 0.
Proof.
  move => u n Hu.
  rewrite /res_cont_term_life_cont.
  rewrite Rminus_eq_0 /=.
  rewrite ins_term_cont_0_0 ann_cont_0_0.
  lra.
Qed.

Lemma res_endow_life_cont_n_1 : forall m x n : nat, 0 < m -> x + n < \ω -> \Vbar^{m}_{n & x:n} = 1.
Proof.
  move => m x n Hm Hxn.
  rewrite /res_endow_life_cont.
  rewrite Rminus_eq_0 subnn.
  rewrite ins_endow_cont_0_1 ?ann_due_0_0 //; [lra |].
    by rewrite -plus_INR; apply (lt_omega_lt_psi _ l_fin); rewrite ?plus_INR.
Qed.

Lemma res_cont_endow_life_cont_n_1 : forall u n : R, u + n < \ψ -> \Vbar^{p_infty}_{n & u:n} = 1.
Proof.
  move => u n Hun.
  rewrite /res_cont_endow_life_cont.
  rewrite Rminus_eq_0.
  rewrite ins_endow_cont_0_1 ?ann_cont_0_0 //; lra.
Qed.

Lemma lim_res_term_cont : forall t x n : nat, t <= n -> x+t < \ω -> 0 < n ->
  is_lim_seq (fun m:nat => \V^{m}_{t & x`1:n}) \Vbar^{p_infty}_{t & x`1:n}.
Proof.
  move => t x n Htn Hxt Hn.
  have Ht' : 0 <= t by apply (le_INR 0); lia.
  have Htn' : (t <= n)%coq_nat by apply INR_le.
  have Hx' : x < \ω by eapply Rle_lt_trans; [| apply Hxt]; lra.
  have Hxt' : (x + t)%N < \ω by rewrite plus_INR.
  rewrite /res_term_life /res_cont_term_life_cont.
  apply is_lim_seq_minus'.
  - rewrite -plus_INR -minus_INR //.
    apply lim_ins_term_cont => //.
  - apply is_lim_seq_mult'.
    + apply (lim_prem_term_cont _ i_pos _ l_fin) => //.
    + rewrite -plus_INR -minus_INR //.
      apply (lim_ann_due_cont _ _ l_fin) => //.
Qed.

Lemma Lim_res_term_cont : forall t x n : nat, t <= n -> x+t < \ω -> 0 < n ->
  Lim_seq (fun m:nat => \V^{m}_{t & x`1:n}) = \Vbar^{p_infty}_{t & x`1:n}.
Proof.
  move => t x n Htn Hxt Hn.
  apply /is_lim_seq_unique /lim_res_term_cont => //.
Qed.

Lemma lim_res_whole_cont : forall t x : nat, x+t < \ω ->
  is_lim_seq (fun m:nat => \V^{m}_{t & x}) \Vbar^{p_infty}_{t & x}.
Proof.
  move => t x Hxt.
  have Ht : 0 <= t by apply (le_INR 0); lia.
  have Hx : x < \ω by eapply Rle_lt_trans; [| apply Hxt]; lra.
  have Hx' : (x <= \ω)%coq_nat by apply INR_le; lra.
  have Hxt' : (x + t)%N < \ω by rewrite plus_INR.
  have Hxt'' : (x + t <= \ω)%coq_nat by apply INR_le; rewrite plus_INR; lra.
  have Hxt''' :  (x + t)%coq_nat < \ψ by apply (lt_omega_lt_psi _ l_fin).
  have Hpsixt : \ψ - (x + t)%coq_nat <= (\ω - (x + t))%N
    by rewrite minus_INR // plus_INR;
    move: (le_psi_omega _  l_fin); rewrite -psi_finite //=; lra.
  rewrite /res_whole_life /res_cont_whole_life_cont.
  apply is_lim_seq_minus'.
  - rewrite -plus_INR.
    apply lim_ins_whole_cont => //.
  - apply is_lim_seq_mult'.
    + apply (lim_prem_whole_cont _ i_pos _ l_fin) => //.
    + rewrite -plus_INR.
      rewrite -(ann_cont_temp_whole _ _ _ _ (x+t)%coq_nat (\ω-(x+t))%N) //.
      apply (lim_ann_due_cont _ _ l_fin) => //.
Qed.

Lemma Lim_res_whole_cont : forall t x : nat, x+t < \ω ->
  Lim_seq (fun m:nat => \V^{m}_{t & x}) = \Vbar^{p_infty}_{t & x}.
Proof.
  move => t x Hxt.
  apply /is_lim_seq_unique /lim_res_whole_cont => //.
Qed.

Lemma lim_res_endow_cont : forall t x n : nat, t <= n -> x+t < \ω -> 0 < n ->
  is_lim_seq (fun m:nat => \V^{m}_{t & x:n}) \Vbar^{p_infty}_{t & x:n}.
Proof.
  move => t x n Ht Hxt Hn.
  have Ht' : 0 <= t by apply (le_INR 0); lia.
  have Ht'' : (t <= n)%coq_nat by apply INR_le.
  have Hx' : x < \ω by eapply Rle_lt_trans; [| apply Hxt]; lra.
  have Hxt' : (x + t)%N < \ω by rewrite plus_INR.
  rewrite /res_endow_life /res_cont_endow_life_cont.
  apply is_lim_seq_minus'.
  - rewrite -plus_INR -minus_INR //.
    apply lim_ins_endow_cont => //.
  - apply is_lim_seq_mult'.
    + apply (lim_prem_endow_cont _ i_pos _ l_fin) => //.
    + rewrite -plus_INR -minus_INR //.
      apply (lim_ann_due_cont _ _ l_fin) => //.
Qed.

Lemma Lim_res_endow_cont : forall t x n : nat, t <= n -> x+t < \ω -> 0 < n ->
  Lim_seq (fun m:nat => \V^{m}_{t & x:n}) = \Vbar^{p_infty}_{t & x:n}.
Proof.
  move => t x n Ht Hxt Hn.
  apply /is_lim_seq_unique /lim_res_endow_cont => //.
Qed.

Lemma res_endow_prem_ann_cont : forall t u n : R, 0 <= t -> u + t < \ψ -> 0 < n ->
  \Vbar^{p_infty}_{t & u:n} = 1 - (\Pbar^{p_infty}_{u:n} + \δ) * \abar_{(u+t):n-t}.
Proof.
  move => t u n Ht Hut Hn.
  rewrite /res_cont_endow_life_cont.
  rewrite ins_endow_cont_ann_cont //.
  lra.
Qed.

Lemma res_endow_ann_cont : forall t u n : R, 0 <= t -> u + t < \ψ -> 0 < n ->
  \Vbar^{p_infty}_{t & u:n} = 1 - \abar_{(u+t):n-t} / \abar_{u:n}.
Proof.
  move => t u n Ht Hut Hn.
  have Hu' : u < \ψ by eapply Rle_lt_trans; [| apply Hut]; lra.
  rewrite /res_cont_endow_life_cont.
  rewrite /prem_cont_endow_life_cont.
  rewrite !ins_endow_cont_ann_cont //.
    by field; apply /pos_neq0 /ann_cont_pos.
Qed.

Lemma res_endow_ins_endow_cont : forall t u n : R, 0 <= t -> u + t < \ψ -> 0 < n ->
  \Vbar^{p_infty}_{t & u:n} = (\Abar_{(u+t):n-t} - \Abar_{u:n}) / (1 - \Abar_{u:n}).
Proof.
  move => t u n Ht Hut Hn.
  have Hu' : u < \ψ by eapply Rle_lt_trans; [| apply Hut]; lra.
  have Habar : 0 < \abar_{ u : n} by apply ann_cont_pos.
  rewrite /res_endow_ann_cont /res_cont_endow_life_cont /prem_cont_endow_life_cont.
  rewrite !ins_endow_cont_ann_cont //.
  field; split; apply pos_neq0 => //.
  move: (delta_pos i_pos); nra.
Qed.

Lemma res_whole_prem_ann_cont : forall t u : R, 0 <= t -> u + t < \ψ ->
  \Vbar^{p_infty}_{t & u} = 1 - (\Pbar^{p_infty}_u + \δ) * \abar_(u+t).
Proof.
  move => t u Ht Hut.
  have Hu' : u < \ψ by eapply Rle_lt_trans; [| apply Hut]; lra.
  rewrite -res_cont_endow_whole //.
  rewrite -(prem_cont_endow_whole _ _ _ l_C1 _ (\ψ-u)) //; [| lra].
  rewrite /whole_life_ann_cont.
  rewrite (_ : \ψ-(u+t) = \ψ-u-t); [| lra].
  apply res_endow_prem_ann_cont => //.
  eapply Rle_lt_trans; [apply Ht |]; lra.
Qed.

Lemma res_whole_ann_cont : forall t u : R, 0 <= t -> u + t < \ψ ->
  \Vbar^{p_infty}_{t & u} = 1 - \abar_(u+t) / \abar_u.
Proof.
  move => t u Ht Hut.
  rewrite -res_cont_endow_whole //.
  rewrite /whole_life_ann_cont.
  rewrite (_ : \ψ-(u+t) = \ψ-u-t); [| lra].
  apply res_endow_ann_cont => //.
  eapply Rle_lt_trans; [apply Ht |]; lra.
Qed.

Lemma res_whole_ins_whole_cont : forall t u : R, 0 <= t -> u + t < \ψ ->
  \Vbar^{p_infty}_{t & u} = (\Abar_(u+t) - \Abar_u) / (1 - \Abar_u).
Proof.
  move => t u Ht Hut.
  rewrite -res_cont_endow_whole //.
  rewrite -(ins_endow_cont_whole_cont _ _ _ l_C1 _ (\ψ-u-t)); [| lra ..].
  rewrite -(ins_endow_cont_whole_cont _ _ _ l_C1 _ (\ψ-u)); [| lra ..].
  apply res_endow_ins_endow_cont => //.
  eapply Rle_lt_trans; [apply Ht |]; lra.
Qed.

End Reserve.
