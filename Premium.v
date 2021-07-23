Require Export Logic.ClassicalChoice Reals Lra Lia.
From mathcomp Require Import all_ssreflect.
From Coquelicot Require Import Coquelicot.
From Actuary Require Export Basics Interest LifeTable.
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(****************************************************************************************)

(* present value of a pure endowment life insurance *)
Definition ins_pure_endow_life (i:R) (l:life) (u:R) (n:R) := \v[i]^n * \p[l]_{n&u}.
Notation "\A[ i , l ]_{ u : n `1}" :=
  (ins_pure_endow_life i l u n) (at level 9, u at level 9).

(* present value of a term life insurance *)
Definition ins_term_life (i:R) (l:life) (m:nat) (x:nat) (n:nat) :=
  \Rsum_(0 <= k < m*n) (\v[i])^((k+1)/m) * (\q[l]_{k/m | 1/m & x}).
Notation "\A[ i , l ]^{ m }_{ x `1: n }" :=
  (ins_term_life i l m x n) (at level 9, x at level 9).
Notation "\A[ i , l ]_{ x `1: n }" := (\A[i,l]^{1}_{x`1:n}) (at level 9, x at level 9).
Definition ins_term_life_cont (i:R) (l:life) (u:R) (n:R) :=
  -/(\l[l]_u) * RInt (fun s:R => \v[i]^s * (Derive (fun r:R => \l[l]_(u+r)) s)) 0 n.
Notation "\Abar[ i , l ]_{ u `1: n }" :=
  (ins_term_life_cont i l u n) (at level 9, u at level 9).

(* present value of a whole life insurance *)
Definition ins_whole_life (i:R) (l:life) (l_fin : l_finite l) (m:nat) (x:nat) :=
  \A[i,l]^{m}_{x`1:\ω[l,l_fin]-x}.
Notation "\A[ i , l , l_fin ]^{ m }_ x" := (ins_whole_life i l l_fin m x) (at level 9).
Notation "\A[ i , l , l_fin ]_ x" := (\A[i,l,l_fin]^{1}_x) (at level 9).
Definition ins_whole_life_cont (i:R) (l:life) (l_fin : l_finite l) (u:R) :=
  \Abar[i,l]_{u`1:\ψ[l]-u}.
Notation "\Abar[ i , l , l_fin ]_ u" := (ins_whole_life_cont i l l_fin u) (at level 9).

(* present value of an endowment life insurance *)
Definition ins_endow_life (i:R) (l:life) (m:nat) (x:nat) (n:nat) :=
  \A[i,l]^{m}_{x`1:n} + \A[i,l]_{x:n`1}.
Notation "\A[ i , l ]^{ m }_{ x : n }" :=
  (ins_endow_life i l m x n) (at level 9, x at level 9).
Notation "\A[ i , l ]_{ x : n }" := (\A[i,l]^{1}_{x:n}) (at level 9, x at level 9).
Definition ins_endow_life_cont (i:R) (l:life) (u:R) (n:R) :=
  \Abar[i,l]_{u`1:n} + \A[i,l]_{u:n`1}.
Notation "\Abar[ i , l ]_{ u : n }" :=
  (ins_endow_life_cont i l u n) (at level 9, u at level 9).

(* present value of a temporary life annuity immediate *)
Definition life_ann (i:R) (l:life) (m:nat) (x:nat) (n:nat) :=
  /m * \Rsum_(0 <= k < m*n) (\v[i])^((k+1)/m) * (\p[l]_{(k+1)/m & x}).
Notation "\a[ i , l ]^{ m }_{ x : n }" := (life_ann i l m x n) (at level 9, x at level 9).
Notation "\a[ i , l ]_{ x : n }" := (\a[i,l]^{1}_{x:n}) (at level 9, x at level 9).
Definition life_ann_cont (i:R) (l:life) (u:R) (n:R) :=
  RInt (fun t:R => \v[i]^t * \p[l]_{t&u}) 0 n.
Notation "\abar[ i , l ]_{ u : n }" := (life_ann_cont i l u n) (at level 9, u at level 9).

(* future value of a temporary life annuity immediate *)
Definition life_acc (i:R) (l:life) (m:nat) (x:nat) (n:nat) :=
  /m * \Rsum_(0 <= k < m*n) /(\v[i]^(k/m) * \p[l]_{k/m & x + n - k/m}).
Notation "\s[ i , l ]^{ m }_{ x : n }" := (life_acc i l m x n) (at level 9, x at level 9).
Notation "\s[ i , l ]_{ x : n }" := (\s[i,l]^{1}_{x:n}) (at level 9, x at level 9).
Definition life_acc_cont (i:R) (l:life) (u:R) (n:R) :=
  RInt (fun t:R => /(\v[i]^t * \p[l]_{t & u + n - t})) 0 n.
Notation "\sbar[ i , l ]_{ u : n }" := (life_acc_cont i l u n) (at level 9, u at level 9).

(* present value of a temporary life annuity due *)
Definition life_ann_due (i:R) (l:life) (m:nat) (x:nat) (n:nat) :=
  /m * \Rsum_(0 <= k < m*n) (\v[i])^(k/m) * (\p[l]_{k/m & x}).
Notation "\a''[ i , l ]^{ m }_{ x : n }" :=
  (life_ann_due i l m x n) (at level 9, x at level 9).
Notation "\a''[ i , l ]_{ x : n }" := (\a''[i,l]^{1}_{x:n}) (at level 9, x at level 9).

(* future value of a temporary life annuity due *)
Definition life_acc_due (i:R) (l:life) (m:nat) (x:nat) (n:nat) :=
  /m * \Rsum_(0 <= k < m*n) /(\v[i]^((k+1)/m) * \p[l]_{(k+1)/m & x + n - (k+1)/m}).
Notation "\s''[ i , l ]^{ m }_{ x : n }" :=
  (life_acc_due i l m x n) (at level 9, x at level 9).
Notation "\s''[ i , l ]_{ x : n }" := (\s''[i,l]^{1}_{x:n}) (at level 9, x at level 9).

(* present value of a whole life annuity immediate *)
Definition whole_life_ann (i:R) (l:life) (l_fin : l_finite l) (m:nat) (x:nat) :=
  \a[i,l]^{m}_{x:(\ω[l,l_fin]-x)}.
Notation "\a[ i , l , l_fin ]^{ m }_ x" := (whole_life_ann i l l_fin m x) (at level 9).
Notation "\a[ i , l , l_fin ]_ x" := (\a[i,l,l_fin]^{1}_x) (at level 9).
Definition whole_life_ann_cont (i:R) (l:life) (l_fin : l_finite l) (u:R) :=
  \abar[i,l]_{u:(\ψ[l]-u)}.
Notation "\abar[ i , l , l_fin ]_ u" :=
  (whole_life_ann_cont i l l_fin u) (at level 9, u at level 9).

(* present value of a whole life annuity due *)
Definition whole_life_ann_due (i:R) (l:life) (l_fin : l_finite l) (m:nat) (x:nat) :=
  \a''[i,l]^{m}_{x:(\ω[l,l_fin]-x)}.
Notation "\a''[ i , l , l_fin ]^{ m }_ x" := (whole_life_ann_due i l l_fin m x) (at level 9).
Notation "\a''[ i , l , l_fin ]_ x" := (\a''[i,l,l_fin]^{1}_x) (at level 9).

(* REMARK
   In the notations of the form \P^{m}, we assume that the insurance payment can occur m
   times a year. Note that some other definitions assume that the insurance payment occurs
   only once a year. *)

(* level premium of a term life insurance *)
Definition prem_term_life (i:R) (l:life) (m:nat) (x:nat) (n:nat) :=
  \A[i,l]^{m}_{x`1:n} / \a''[i,l]^{m}_{x:n}.
Notation "\P[ i , l ]^{ m }_{ x `1: n }" :=
  (prem_term_life i l m x n) (at level 9, x at level 9).
Notation "\P[ i , l ]_{ x `1: n }" := (\P[i,l]^{1}_{x`1:n}) (at level 9, x at level 9).
Definition prem_term_life_cont (i:R) (l:life) (m:nat) (x:nat) (n:nat) :=
  \Abar[i,l]_{x`1:n} / \a''[i,l]^{m}_{x:n}.
Notation "\Pbar[ i , l ]^{ m }_{ x `1: n }" :=
  (prem_term_life_cont i l m x n) (at level 9, x at level 9).
Notation "\Pbar[ i , l ]_{ x `1: n }" := (\Pbar[i,l]^{1}_{x`1:n}) (at level 9, x at level 9).
Definition prem_cont_term_life_cont (i:R) (l:life) (u:R) (n:R) :=
  \Abar[i,l]_{u`1:n} / \abar[i,l]_{u:n}.
Notation "\Pbar[ i , l ]^{p_infty}_{ u `1: n }" :=
  (prem_cont_term_life_cont i l u n) (at level 9, u at level 9).

(* level premium of a whole life insurance *)
Definition prem_whole_life (i:R) (l:life) (l_fin : l_finite l) (m:nat) (x:nat) :=
  \A[i,l,l_fin]^{m}_x / \a''[i,l,l_fin]^{m}_x.
Notation "\P[ i , l , l_fin ]^{ m }_ x" := (prem_whole_life i l l_fin m x) (at level 9).
Notation "\P[ i , l , l_fin ]_ x" := (\P[i,l,l_fin]^{1}_x) (at level 9).
Definition prem_whole_life_cont (i:R) (l:life) (l_fin : l_finite l) (m:nat) (x:nat) :=
  \Abar[i,l,l_fin]_x / \a''[i,l,l_fin]^{m}_x.
Notation "\Pbar[ i , l , l_fin ]^{ m }_ x" :=
  (prem_whole_life_cont i l l_fin m x) (at level 9).
Notation "\Pbar[ i , l , l_fin ]_ x" := (\Pbar[i,l,l_fin]^{1}_x) (at level 9).
Definition prem_cont_whole_life_cont (i:R) (l:life) (l_fin : l_finite l) (u:R) :=
  \Abar[i,l,l_fin]_u / \abar[i,l,l_fin]_u.
Notation "\Pbar[ i , l , l_fin ]^{p_infty}_ u" :=
  (prem_cont_whole_life_cont i l l_fin u) (at level 9).

(* level premium of a pure endowment life insurance *)
Definition prem_pure_endow_life (i:R) (l:life) (m:nat) (x:nat) (n:nat) :=
  \A[i,l]_{x:n`1} / \a''[i,l]^{m}_{x:n}.
Notation "\P[ i , l ]^{ m }_{ x : n `1}" :=
  (prem_pure_endow_life i l m x n) (at level 9, x at level 9).
Notation "\P[ i , l ]_{ x : n `1}" := (\P[i,l]^{1}_{x:n`1}) (at level 9, x at level 9).
Definition prem_cont_pure_endow_life (i:R) (l:life) (u:R) (n:R) :=
  \A[i,l]_{u:n`1} / \abar[i,l]_{u:n}.
Notation "\P[ i , l ]^{p_infty}_{ u : n `1}" :=
  (prem_cont_pure_endow_life i l u n) (at level 9, u at level 9).

(* level premium of an endowment life insurance *)
Definition prem_endow_life (i:R) (l:life) (m:nat) (x:nat) (n:nat) :=
  \A[i,l]^{m}_{x:n} / \a''[i,l]^{m}_{x:n}.
Notation "\P[ i , l ]^{ m }_{ x : n }" :=
  (prem_endow_life i l m x n) (at level 9, x at level 9).
Notation "\P[ i , l ]_{ x : n }" := (\P[i,l]^{1}_{x:n}) (at level 9, x at level 9).
Definition prem_endow_life_cont (i:R) (l:life) (m:nat) (x:nat) (n:nat) :=
  \Abar[i,l]_{x:n} / \a''[i,l]^{m}_{x:n}.
Notation "\Pbar[ i , l ]^{ m }_{ x : n }" :=
  (prem_endow_life_cont i l m x n) (at level 9, x at level 9).
Notation "\Pbar[ i , l ]_{ x : n }" := (\Pbar[i,l]^{1}_{x:n}) (at level 9, x at level 9).
Definition prem_cont_endow_life_cont (i:R) (l:life) (u:R) (n:R) :=
  \Abar[i,l]_{u:n} / \abar[i,l]_{u:n}.
Notation "\Pbar[ i , l ]^{p_infty}_{ u : n }" :=
  (prem_cont_endow_life_cont i l u n) (at level 9, u at level 9).

(****************************************************************************************)

Section Premium.

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

Hint Resolve i_nom_pos i_nom_add_pos delta_pos d_nom_pos v_pos lt_v_1 v_in_0_1 : core.
Hint Resolve l_0_pos l_neg_nil l_infty_0 l_decr l_nonneg psi_nonneg l_u_pos : core.
Hint Resolve psi_finite omega_pos l_x_pos : core.

Lemma ins_pure_endow_0_1 : forall x:nat, x < \ω -> \A_{x:0`1} = 1.
Proof.
  move => x Hx.
  rewrite /ins_pure_endow_life.
  rewrite Rpower_O; auto.
  rewrite p_0_1; lra.
Qed.

Lemma ins_pure_endow_0_1' : forall u:R, u < \ψ -> \A_{u:0`1} = 1.
Proof.
  move => u Hu.
  rewrite /ins_pure_endow_life.
  rewrite Rpower_O; auto.
  rewrite p_0_1' //; lra.
Qed.

Lemma ins_pure_endow_old_0 : forall (x n : nat), x < \ω -> \ω - x <= n -> \A_{x:n`1} = 0.
Proof.
  move => x n Hx Hn.
  rewrite /ins_pure_endow_life.
  rewrite p_old_0; [| lra].
  rewrite Rmult_0_r //.
Qed.

Lemma ins_pure_endow_pos : forall (x n : nat), x+n < \ω -> 0 < \A_{x:n`1}.
Proof.
  move => x n Hxn.
  rewrite /ins_pure_endow_life.
  apply Rmult_lt_0_compat; [apply exp_pos |].
  apply Rmult_lt_0_compat.
  - rewrite -plus_INR.
    apply (l_x_pos _ l_fin).
    rewrite plus_INR //.
  - apply /Rinv_0_lt_compat /(l_x_pos _ l_fin) /lt_INR.
    move: Hxn; rewrite -plus_INR => /INR_lt; lia.
Qed.

Lemma ins_pure_endow_pos' : forall (u n : R), u+n < \ψ -> 0 <= n -> 0 < \A_{u:n`1}.
Proof.
  move => u n Hun Hn.
  rewrite /ins_pure_endow_life.
  apply Rmult_lt_0_compat; [apply exp_pos |].
  apply Rmult_lt_0_compat.
  - apply l_u_pos.
    rewrite -psi_finite //.
  - apply /Rinv_0_lt_compat /l_u_pos.
    rewrite -psi_finite //=; lra.
Qed.

Lemma ins_pure_endow_1 : forall u:R, \A_{u:1`1} = \v * \p_u.
Proof.
  move => u.
  rewrite /ins_pure_endow_life.
  rewrite Rpower_1; auto.
Qed.

Lemma ins_pure_endow_mult : forall (t x n : nat), x+t < \ω -> t <= n ->
  \A_{x:n`1} = \A_{x:t`1} * \A_{(x+t):(n-t)`1}.
Proof.
  move => t x n Hxt Htn.
  rewrite {-1}/ins_pure_endow_life.
  rewrite -Rmult_assoc (Rmult_assoc (\v^t)) (Rmult_comm \p_{_&_}) -Rmult_assoc.
  rewrite -Rpower_plus Rplus_minus.
  rewrite Rmult_assoc -p_mult;
    [| rewrite -plus_INR; apply /pos_neq0 /(l_x_pos _ l_fin); rewrite plus_INR //].
  rewrite Rplus_minus /ins_pure_endow_life //.
Qed.

Lemma ins_pure_endow_mult' : forall (t u n : R), u+t < \ψ -> t <= n ->
  \A_{u:n`1} = \A_{u:t`1} * \A_{(u+t):(n-t)`1}.
Proof.
  move => t u n Hut Htn.
  rewrite {-1}/ins_pure_endow_life.
  rewrite -Rmult_assoc (Rmult_assoc (\v^t)) (Rmult_comm \p_{_&_}) -Rmult_assoc.
  rewrite -Rpower_plus Rplus_minus.
  rewrite Rmult_assoc -p_mult; [| apply /pos_neq0 /l_u_pos; rewrite -psi_finite //].
  rewrite Rplus_minus /ins_pure_endow_life //.
Qed.

Lemma ins_pure_endow_rec : forall (x n :nat), x+1 < \ω -> 0 < n ->
  \A_{x:n`1} = \v * \p_x * \A_{(x+1):(n-1)`1}.
Proof.
  move => x n Hx Hn.
  rewrite (ins_pure_endow_mult 1) //.
  rewrite ins_pure_endow_1 //.
  move: Hn => /(INR_lt 0); apply le_INR.
Qed.

Lemma ins_pure_endow_rec' : forall (x n : nat), x+n < \ω ->
  \A_{x:(n+1)`1} = \v * \p_(x+n) * \A_{x:n`1}.
Proof.
  move => x n Hxn.
  rewrite -(plus_INR n 1).
  rewrite (ins_pure_endow_mult n _ (n+1)); [| | rewrite addn1; apply le_INR]; auto.
  rewrite (_ : (n + 1)%N - n = 1); [| rewrite plus_INR /=; lra].
  rewrite -{1}(plus_INR x n).
  rewrite ins_pure_endow_1 plus_INR; lra.
Qed.

Lemma ins_term_0_0 : forall (m x : nat), 0 < m -> \A^{m}_{x`1:0} = 0.
Proof.
  move => m x _.
  rewrite /ins_term_life.
  rewrite big_geq //.
  rewrite muln0 //.
Qed.

Lemma ins_term_1 : forall x:nat, \A_{x`1:1} = \v * \q_x.
Proof.
  move => x.
  rewrite /ins_term_life.
  rewrite mul1n big_nat1.
  rewrite Rplus_0_l !Rdiv_1 Rpower_1; auto.
Qed.

Lemma ins_term_annual : forall (x n : nat), \A_{x`1:n} = \Rsum_(0 <= k < n) \v^(k+1) * \q_{k|&x}.
Proof.
  move => x n.
  rewrite /ins_term_life mul1n.
    by under eq_big_nat => k _ do rewrite !Rdiv_1.
Qed.

Lemma ins_term_whole : forall (m x n : nat), 0 < m -> x < \ω -> \ω - x <= n ->
  \A^{m}_{x`1:n} = \A^{m}_x.
Proof.
  move => m x n Hm Hx Hn.
  rewrite /ins_whole_life /ins_term_life.
  have Hx' : (x < \ω)%coq_nat by apply INR_lt => //.
  have Hn' : (\ω - x <= n)%N.
  { apply /leP /INR_le.
    rewrite !SSR_minus !minus_INR; [lra | lia]. }
  have Hmn' : (m*(\ω - x) <= m*n)%N by apply /leP /Nat.mul_le_mono_l /leP.
  rewrite (big_cat_nat _ _ _ _ Hmn') //=.
  under [\big[_/_]_(m*(\ω - x) <= _ < m*n) _]eq_big_nat => k Hk.
  { rewrite (q_defer_old_0' _ l_fin (k/m) (1/m) x).
    - rewrite Rmult_0_r.
      over.
    - by apply /Rlt_le /Rdiv_lt_0_compat.
    - move: Hk => /andP; case => /leP /le_INR.
      rewrite mult_INR minus_INR; [| lia].
      rewrite Rmult_comm Rle_div_r; lra. }
  rewrite big1_eq Rplus_0_r //.
Qed.

Lemma ins_term_pure_endow : forall (m t x n : nat), 0 < m -> x+t < \ω -> t <= n ->
  \A^{m}_{x`1:n} = \A^{m}_{x`1:t} + \A_{x:t`1} * \A^{m}_{(x+t)`1:(n-t)}.
Proof.
  move => m t x n Hm Hxt Htn.
  have Htn' : (t <= n)%N by apply /leP /INR_le => //.
  rewrite /ins_pure_endow_life {-1}/ins_term_life.
  rewrite big_distrr /=.
  under [\big[Rplus/0]_(0 <= i0 < m*(n-t)) _] eq_big_nat => k Hk.
  { rewrite -Rmult_assoc (Rmult_assoc (\v^t)) (Rmult_comm \p_{_&_}) -Rmult_assoc.
    rewrite -Rpower_plus Rmult_assoc.
    rewrite plus_INR.
    rewrite q_defer_p_q_defer;
      [| rewrite -plus_INR; apply /pos_neq0 /(l_x_pos _ l_fin); rewrite plus_INR //].
    rewrite (_ : t + (k+1)/m = (k + m*t + 1)/m); [| field; lra].
    rewrite (_ : k/m + t = (k + m*t)/m); [| field; lra].
    rewrite -mult_INR -plus_INR.
    over. }
  rewrite /=.
  rewrite mulnBr.
  rewrite -[\big[_/_]_(_<=_<_-_)_]
             (big_addn _ _ _ xpredT (fun j:nat => (\v^((j+1)/m) * \q_{j/m | 1/m & x}))).
  rewrite add0n.
  rewrite -big_cat_nat //.
    by apply (INR_lt 0) in Hm; apply leq_mul.
Qed.

Lemma ins_term_rec : forall (x n : nat), x+1 < \ω -> 0 < n ->
  \A_{x`1:n} = \v * \q_x + \v * \p_x * \A_{(x+1)`1:(n-1)}.
Proof.
  move => x n Hx Hn.
  rewrite (ins_term_pure_endow 1 1) //; last by move: Hn => /(INR_lt 0); apply le_INR.
  rewrite ins_term_1 ins_pure_endow_1 //.
Qed.

Lemma ins_whole_rec : forall x:nat, x+1 < \ω -> \A_x = \v * \q_x + \v * \p_x * \A_(x+1).
Proof.
  move => x Hx.
  rewrite /ins_whole_life.
  rewrite ins_term_rec //; [| rewrite SSR_minus minus_INR; [lra | apply INR_le; lra]].
  rewrite subnDA //.
Qed.

Lemma ins_endow_whole : forall (m x n : nat), 0 < m -> x < \ω -> \ω - x <= n ->
  \A^{m}_{x:n} = \A^{m}_x.
Proof.
  move => m x n Hm Hx Hn.
  rewrite /ins_endow_life.
  rewrite ins_term_whole //.
  rewrite ins_pure_endow_old_0; lra.
Qed.

Lemma ins_endow_0_1 : forall (m x : nat), 0 < m -> x < \ω -> \A^{m}_{x:0} = 1.
Proof.
  move => m x Hm Hx.
  rewrite /ins_endow_life.
  rewrite ins_term_0_0 // ins_pure_endow_0_1; lra.
Qed.

Lemma ins_endow_pure_endow : forall (m t x n : nat), 0 < m -> x+t < \ω -> t <= n ->
  \A^{m}_{x:n} = \A^{m}_{x`1:t} + \A_{x:t`1} * \A^{m}_{(x+t):(n-t)}.
Proof.
  move => m t x n Hm Hxt Htn.
  rewrite /ins_endow_life.
  rewrite plus_INR minus_INR; [| apply (INR_le _ _ Htn)].
  rewrite (ins_term_pure_endow m t) //.
  rewrite (ins_pure_endow_mult t x n) //; lra.
Qed.

Lemma ins_endow_rec : forall (x n : nat), x+1 < \ω -> 0 < n ->
  \A_{x:n} = \v * \q_x + \v * \p_x * \A_{(x+1):(n-1)}.
Proof.
  move => x n Hx Hn.
  rewrite (ins_endow_pure_endow 1 1) //; last by move: Hn => /(INR_lt 0); apply le_INR.
  rewrite ins_term_1 ins_pure_endow_1 //.
Qed.

Lemma ann' : forall (m x n : nat), 0 < m ->
  m * \a^{m}_{x:n} = \Rsum_(0 <= k < m*n) \v^((k+1)/m) * \p_{(k+1)/m & x}.
Proof.
  move => m x n Hm.
  rewrite /life_ann.
  rewrite -Rmult_assoc Rinv_r ?Rmult_1_l; auto.
Qed.

Lemma ann_rev : forall (m x n : nat), 0 < m ->
  \a^{m}_{x:n} = /m * \Rsum_(0 <= k < m*n) \v^(n-k/m) * \p_{n-k/m & x}.
Proof.
  move => m x n Hm.
  rewrite /life_ann.
  rewrite big_nat_rev /=.
  under eq_big_nat => k Hk.
  { rewrite minus_INR.
    - rewrite plus_INR mult_INR Rplus_0_l -Nat.add_1_r plus_INR /Rminus Ropp_plus_distr
        -Rplus_assoc Rplus_assoc Rplus_opp_l Rplus_0_r.
      rewrite Rdiv_plus_distr (Rmult_comm m n) /Rdiv Rinv_r_simpl_l; auto.
      rewrite -Ropp_mult_distr_l -/(Rdiv _ m) -/(Rminus _ (k/m)).
      over.
    - rewrite add0n.
      apply /lt_le_S /ltP.
      move: Hk => /andP; intuition. }
    by [].
Qed.

Lemma ann_0_0 : forall (m x : nat), 0 < m -> \a^{m}_{x:0} = 0.
Proof.
  move => m x Hm.
  rewrite /life_ann.
  rewrite big_geq; [rewrite Rmult_0_r | rewrite muln0]; auto.
Qed.

Lemma ann_annual : forall (x n : nat), \a_{x:n} = \Rsum_(0 <= k < n) \v^(k+1) * \p_{k+1 & x}.
Proof.
  move => x n.
  rewrite /life_ann mul1n Rinv_1 Rmult_1_l /=.
    by under [in LHS]eq_big_nat do rewrite Rdiv_1.
Qed.

Lemma ann_due' : forall (m x n : nat), 0 < m ->
  m * \a''^{m}_{x:n} = \Rsum_(0 <= k < m*n) \v^(k/m) * \p_{k/m & x}.
Proof.
  move => m x n Hm.
  rewrite /life_ann_due.
  rewrite -Rmult_assoc Rinv_r ?Rmult_1_l; auto.
Qed.

Lemma ann_due_rev : forall (m x n : nat), 0 < m ->
  \a''^{m}_{x:n} = /m * \Rsum_(0 <= k < m*n) \v^(n-(k+1)/m) * \p_{n-(k+1)/m & x}.
Proof.
  move => m x n Hm.
  rewrite /life_ann_due.
  rewrite big_nat_rev /=.
  under eq_big_nat => k Hk.
  { rewrite add0n minus_INR.
    - rewrite mult_INR -Nat.add_1_r plus_INR.
      rewrite Rdiv_plus_distr (Rmult_comm m n) /Rdiv Rinv_r_simpl_l; auto.
      rewrite /= -Ropp_mult_distr_l -/(Rdiv _ m) -/(Rminus _ (_ / _)).
      over.
    - apply /lt_le_S /ltP.
      move: Hk => /andP; intuition. }
    by [].
Qed.

Lemma ann_due_0_0 : forall (m x : nat), 0 < m -> \a''^{m}_{x:0} = 0.
Proof.
  move => m x Hm.
  rewrite /life_ann_due.
  rewrite big_geq; [rewrite Rmult_0_r | rewrite muln0]; auto.
Qed.
  
Lemma ann_due_lb : forall (m x n : nat), 0 < m -> x < \ω -> 0 < n -> /m <= \a''^{m}_{x:n}.
Proof.
  move => m x n Hm Hx Hn.
  have Hn' : (0 < n)%coq_nat by (apply INR_lt => //).
  have Hm' : (0 < m)%coq_nat by (apply INR_lt => //).
  rewrite /life_ann_due.
  rewrite (S_pred (m*n) 0); [| rewrite /muln /muln_rec; lia].
  rewrite big_nat_recl; [| apply /leP; lia].
  rewrite {1 2}/Rdiv Rmult_0_l.
  rewrite Rpower_O; [| apply /v_pos /i_pos]; rewrite p_0_1 // Rmult_1_r.
  rewrite Rmult_plus_distr_l Rmult_1_r.
  rewrite -{1}(Rplus_0_r (/m)); apply (Rplus_le_compat (/m)); [lra |].
  apply Rmult_le_pos; [by apply /Rlt_le /Rinv_0_lt_compat |].
  apply Rsum_nonneg => k Hk.
  rewrite -(Rmult_0_r (\v^((k.+1)/m))); apply (Rmult_le_compat_l (\v^((k.+1)/m)));
    [apply /Rlt_le /exp_pos | apply (p_nonneg' _ l_fin) => //].
Qed.

Lemma ann_due_annual : forall (x n : nat), \a''_{x:n} = \Rsum_(0 <= k < n) \v^k * \p_{k&x}.
Proof.
  move => x n.
  rewrite /life_ann_due mul1n Rinv_1 Rmult_1_l /=.
    by under [in LHS]eq_big_nat do rewrite Rdiv_1.
Qed.

Lemma ann_temp_whole : forall (m x n : nat), 0 < m -> x < \ω -> \ω - x <= n ->
  \a^{m}_{x:n} = \a^{m}_x.
Proof.
  move => m x n Hm Hx Hn.
  have Hx' : (x < \ω)%coq_nat by apply INR_lt => //.
  have Hmn : (m*(\ω - x) <= m*n)%N.
  { rewrite leq_pmul2l; [apply /leP /INR_le | by apply /ltP /INR_lt].
    rewrite minus_INR //; lia. }
  rewrite /whole_life_ann /life_ann.
  rewrite (big_cat_nat _ _ _ _ Hmn) //=.
  under [\big[_/_]_(_*_ <= i0 < _*_) _]eq_big_nat => k Hk.
  { rewrite (_ : 1 = 1%N) // p_old_0'.
    - rewrite Rmult_0_r.
      over.
    - move: Hk => /andP; case => /leP /le_INR.
      rewrite /= /muln /muln_rec mult_INR SSR_minus minus_INR; [| lia] => Hklb _.
      rewrite Rdiv_plus_distr -Rplus_assoc.
      apply (Rle_trans _ (x+k/m)).
      + rewrite Rmult_comm in Hklb.
        apply Rle_div_r in Hklb; lra.
      + have Hm' : 0 < 1/m by rewrite /Rdiv Rmult_1_l; apply Rinv_0_lt_compat.
        lra. }
  rewrite big1_eq Rplus_0_r //.
Qed.

Lemma ann_due_temp_whole : forall (m x n : nat), 0 < m -> x < \ω -> \ω - x <= n ->
  \a''^{m}_{x:n} = \a''^{m}_x.
Proof.
  move => m x n Hm Hx Hn.
  have Hx' : (x < \ω)%coq_nat by apply INR_lt => //.
  have Hmn : (m*(\ω - x) <= m*n)%N.
  { rewrite leq_pmul2l; [apply /leP /INR_le | by apply /ltP /INR_lt].
    rewrite minus_INR //; lia. }
  rewrite /whole_life_ann_due /life_ann_due.
  rewrite (big_cat_nat _ _ _ _ Hmn) //=.
  under [\big[_/_]_(_*_ <= i0 < _*_) _]eq_big_nat => k Hk.
  { rewrite p_old_0'.
    - rewrite Rmult_0_r.
      over.
    - move: Hk => /andP; case => /leP /le_INR.
      rewrite /= /muln /muln_rec mult_INR SSR_minus minus_INR; [| lia] => Hklb _.
      rewrite Rmult_comm in Hklb.
      apply Rle_div_r in Hklb; lra. }
  rewrite big1_eq Rplus_0_r //.
Qed.

Lemma ann_due_annual_sum_pure_endow : forall (x n : nat), \a''_{x:n} = \Rsum_(0 <= k < n) \A_{x:k`1}.
Proof.
  move => x n.
  under eq_big_nat do rewrite /ins_pure_endow_life.
  rewrite ann_due_annual //.
Qed.

Lemma ann_imm_due : forall (x n : nat), x+1 < \ω -> \a_{x:n} = \v * \p_x * \a''_{(x+1):n}.
Proof.
  move => x n Hx.
  rewrite ann_annual ann_due_annual /=.
  under eq_big_nat => k Hk.
  { rewrite Rpower_plus Rpower_1; [| apply /v_pos /i_pos].
    rewrite (_ : 1 = 1%N) in Hx * => //.
    rewrite (Rplus_comm k 1%N) (p_mult _ 1%N k x).
    2:{ apply pos_neq0.
        rewrite -plus_INR in Hx *.
        apply (l_x_pos _ l_fin) => //. }
    rewrite -Rmult_assoc (Rmult_assoc _ \v _) (Rmult_comm (\v^k)) Rmult_assoc.
    over. }
  rewrite big_distrr /= plus_INR //.
Qed.

Lemma ann_due_1_imm : forall (x n : nat), x < \ω -> 0 < n -> \a''_{x:n} = 1 + \a_{x:(n-1)}. 
Proof.
  move => x n Hx Hn.
  rewrite ann_annual ann_due_annual.
  rewrite {1}(S_pred n 0); [| apply INR_lt => //].
  rewrite big_nat_recl //.
  rewrite Rpower_O; [| apply /v_pos /i_pos]; rewrite p_0_1 // Rmult_1_r.
  rewrite pred_of_minus -SSR_minus.
    by under eq_big_nat => k Hk do rewrite S_INR.
Qed.

Lemma ann_imm_due_pure_endow : forall (m x n : nat), 0 < m -> x < \ω ->
  \a^{m}_{x:n} = \a''^{m}_{x:n} - /m + \A_{x:n`1}/m.
Proof.
  move => m x n Hm Hx.
  have Hm' : (0 < m)%coq_nat by apply INR_lt.
  rewrite /life_ann /life_ann_due /ins_pure_endow_life.
  rewrite -{3}(Rmult_1_r (/m)) {5}/Rdiv (Rmult_comm _ (/m)).
  rewrite -Rmult_minus_distr_l -Rmult_plus_distr_l.
  case: (zerop n) => [Hn0 | Hnpos].
  - rewrite !big_geq Hn0; [| rewrite muln0 //; apply /leP ..].
    rewrite Rpower_O; [| apply /v_pos /i_pos]; rewrite p_0_1; lra.
  - have Hmn : (0 < m * n)%coq_nat
      by apply /ltP; rewrite muln_gt0; apply /andP; split; apply /ltP.
    rewrite {2}(S_pred (m*n) 0) //.
    rewrite big_nat_recl; [| apply /leP; lia].
    rewrite /(Rdiv 0) Rmult_0_l.
    rewrite Rpower_O; [| apply /v_pos /i_pos]; rewrite p_0_1 // Rmult_1_r.
    rewrite (Rplus_comm 1) Ropp_r_simpl_l.
    rewrite [in LHS](S_pred (m*n) 0) //.
    rewrite (_ : \v^n * \p_{n&x} = (\v^(((m*n).-1.+1)/m) * \p_{((m*n).-1.+1)/m&x}));
      [|rewrite -(S_pred _ 0) // mulnC mult_INR /Rdiv Rinv_r_simpl_l; auto].
    rewrite -(big_nat_recr _ _ _ ); [| apply /leP; lia].
      by under eq_big_nat => k Hk do [rewrite (_ : 1 = 1%N) // -plus_INR Nat.add_1_r].
Qed.

Lemma ann_imm_due_pure_endow_annual : forall (x n : nat), x < \ω ->
  \a_{x:n} = \a''_{x:n} - 1 + \A_{x:n`1}.
Proof.
  move => x n Hx.
  move: (ann_imm_due_pure_endow 1 x n).
  rewrite /Rdiv Rinv_1 Rmult_1_r; auto.
Qed.

Lemma ann_due_rec : forall (x n : nat), x+1 < \ω -> 0 < n ->
  \a''_{x:n} = 1 + \v * \p_x * \a''_{(x+1):(n-1)}.
Proof.
  move => x n Hx Hn.
  rewrite ann_due_1_imm //; [| eapply Rlt_trans; [| apply Hx]; lra].
  rewrite ann_imm_due //.
Qed.

Lemma ann_due_pure_endow : forall (m t x n : nat), 0 < m -> x+t < \ω -> t <= n ->
  \a''^{m}_{x:n} = \a''^{m}_{x:t} + \A_{x:t`1} * \a''^{m}_{(x+t):(n-t)}.
Proof.
  move => m t x n Hm Hxt Htn.
  rewrite {3}/life_ann_due /ins_pure_endow_life mulnBr.
  rewrite -Rmult_assoc (Rmult_comm _ (/m)) Rmult_assoc.
  rewrite big_distrr /=.
  under eq_big_nat => k Hk.
  { rewrite -Rmult_assoc (Rmult_assoc (\v^t)) (Rmult_comm \p_{_&_}) -Rmult_assoc Rmult_assoc.
    rewrite -Rpower_plus plus_INR.
    rewrite -p_mult;
      [| rewrite -plus_INR; apply /pos_neq0 /(l_x_pos l l_fin); rewrite plus_INR //].
    rewrite -(Rinv_r_simpl_l m t); auto.
    rewrite -Rdiv_plus_distr Rplus_comm (Rmult_comm t m).
    rewrite -mult_INR -plus_INR -/addn_rec -/addn -/muln_rec -/muln.
    over. }
  rewrite -(big_addn _ _ _ xpredT (fun k:nat => \v^(k/m) * \p_{k/m & x})) add0n.
  rewrite [in RHS]/life_ann_due.
  rewrite -Rmult_plus_distr_l.
  rewrite -big_cat_nat //.
  rewrite leq_pmul2l; [by apply /leP /INR_le | by apply /ltP /INR_lt].
Qed.

Lemma ins_endow_ann_due : forall (m x n : nat), 0 < m -> x < \ω ->
  \A^{m}_{x:n} = 1 - \d^{m} * \a''^{m}_{x:n}.
Proof.
  move => m x n Hm Hx.
  have Hx' : (x < \ω)%coq_nat by apply INR_lt => //.
  wlog : n / n <= \ω - x.
  { move => Hspec.
    case: (Rle_lt_dec n (\ω - x)); [apply Hspec => // |].
    move => Hn_lb.
    rewrite /ins_endow_life.
    rewrite ins_term_whole; try lra.
    rewrite ins_pure_endow_old_0; try lra.
    rewrite -(ins_pure_endow_old_0 x (\ω - x)) //;
      [| rewrite SSR_minus minus_INR; [lra | lia]].
    rewrite ann_due_temp_whole; try lra.
    rewrite /ins_whole_life /whole_life_ann_due.
    rewrite -/(ins_endow_life _ _  x (\ω - x)).
    apply Hspec; rewrite SSR_minus minus_INR; [lra | lia]. }
  move => Hn_ub.
  have Hn_ub' : (n <= (\ω - x)%coq_nat)%coq_nat
    by apply INR_le; rewrite minus_INR; [lra | lia].
  rewrite /ins_endow_life /ins_term_life.
  under eq_big_nat => k Hk.
  { move: Hk => /andP [Hk_lb Hk_ub].
    move: Hk_ub => /ltP => Hk_ub.
    rewrite q_defer_p.
    rewrite Rmult_minus_distr_l.
    rewrite {1}Rdiv_plus_distr Rpower_plus (Rmult_comm _ (_^(1/m))) Rmult_assoc.
    rewrite /Rminus -Rmult_opp1_l -Rdiv_plus_distr.
    over. }
  rewrite big_split /=.
  rewrite -!big_distrr /= Rmult_opp1_l.
  rewrite -ann' -?ann_due'//.
  rewrite ann_imm_due_pure_endow //.
  rewrite Rmult_plus_distr_l Rmult_minus_distr_l Rinv_r; auto.
  rewrite /(Rdiv \A_{_:_`1}) -(Rmult_assoc _ _ (/m)) Rinv_r_simpl_m; auto.
  rewrite Ropp_plus_distr Ropp_minus_distr !Rplus_assoc Rplus_opp_l Rplus_0_r.
  rewrite Rplus_comm Rplus_assoc -Rmult_opp1_l -Rmult_plus_distr_r (Rplus_comm (-1))
    -/(Rminus _ 1) -Ropp_minus_distr -Rmult_assoc (Rmult_comm _ m) -Ropp_mult_distr_r.
  rewrite (_ : 1/m = /m) -?d_nom_v //; [lra | rewrite /Rdiv Rmult_1_l //].
Qed.

Lemma ins_whole_ann_due : forall (m x : nat), 0 < m -> x < \ω -> \A^{m}_x = 1 - \d^{m} * \a''^{m}_x.
Proof.
  move => m x Hm Hx.
  have Hx' : (x < \ω)%coq_nat by apply INR_lt => //.
  rewrite /ins_whole_life /whole_life_ann_due.
  rewrite -ins_endow_ann_due //.
  rewrite /ins_endow_life.
  rewrite ins_pure_endow_old_0; [lra .. |]; rewrite SSR_minus minus_INR; [lra | lia].
Qed.

Lemma acc' : forall (m x n : nat), 0 < m ->
  m * \s^{m}_{x:n} = \Rsum_(0 <= k < m*n) /(\v^(k/m) * \p_{k/m & x+n-k/m}).
Proof.
  move => m x n Hm.
  rewrite /life_acc.
  rewrite -Rmult_assoc Rinv_r ?Rmult_1_l; auto.
Qed.

Lemma acc_rev : forall (m x n : nat), 0 < m ->
  \s^{m}_{x:n} = /m * \Rsum_(0 <= k < m*n) /(\v^(n-(k+1)/m) * \p_{n-(k+1)/m & x+(k+1)/m}).
Proof.
  move => m x n Hm.
  rewrite /life_acc.
  rewrite big_nat_rev add0n /=.
  under eq_big_nat => k Hk.
  { rewrite minus_INR.
    - rewrite mult_INR RIneq.Rdiv_minus_distr /Rdiv Rinv_r_simpl_m; auto.
      rewrite /(Rminus (x+n)) -Rmult_opp1_l Rmult_minus_distr_l
        !Rmult_opp1_l -Rplus_assoc (Rplus_assoc x n) Rplus_opp_r Rplus_0_r Ropp_involutive.
      rewrite -Nat.add_1_r plus_INR /= -/(Rdiv _ m).
      over.
    - apply /lt_le_S /ltP.
      move: Hk => /andP; intuition. }
    by [].
Qed.

Lemma acc_annual : forall (x n : nat), \s_{x:n} = \Rsum_(0 <= k < n) /(\v^k * \p_{k & x+n-k}).
Proof.
  move => x n.
  rewrite /life_acc.
  rewrite Rinv_1 Rmult_1_l mul1n.
    by under eq_big_nat => k _ do rewrite Rdiv_1.
Qed.

Lemma acc_due' : forall (m x n : nat), 0 < m ->
  m * \s''^{m}_{x:n} = \Rsum_(0 <= k < m*n) /(\v^((k+1)/m) * \p_{(k+1)/m & x+n-(k+1)/m}).
Proof.
  move => m x n Hm.
  rewrite /life_acc_due.
  rewrite -Rmult_assoc Rinv_r ?Rmult_1_l; auto.
Qed.

Lemma acc_due_rev : forall (m x n : nat), 0 < m ->
  \s''^{m}_{x:n} = /m * \Rsum_(0 <= k < m*n) /(\v^(n-k/m) * \p_{n-k/m & x+k/m}).
Proof.
  move => m x n Hm.
  rewrite /life_acc_due.
  rewrite big_nat_rev add0n /=.
  under eq_big_nat => k Hk.
  { rewrite minus_INR; [| rewrite -Nat.add_1_r; move: Hk => /andP; case => _ /ltP; lia].
    rewrite (_ : (m * n)%N - k.+1 + 1 = m*n - k);
      [| rewrite mult_INR -Nat.add_1_r plus_INR /=; lra].
    rewrite RIneq.Rdiv_minus_distr /(Rdiv (m*n)) Rinv_r_simpl_m; auto.
    rewrite (_ : x + n - (n - k / m) = x + k/m); [| lra].
    over. }
    by [].
Qed.

Lemma acc_due_annual : forall (x n : nat),
    \s''_{x:n} = \Rsum_(0 <= k < n) /(\v^(k+1) * \p_{k+1 & x+n-(k+1)}).
Proof.
  move => x n.
  rewrite /life_acc_due.
  rewrite Rinv_1 Rmult_1_l mul1n.
    by under eq_big_nat => k _ do rewrite Rdiv_1.
Qed.

Lemma ann_pure_endow_acc : forall (m x n : nat), 0 < m -> x+n < \ω ->
  \a^{m}_{x:n} = \A_{x:n`1} * \s^{m}_{x:n}.
Proof.
  move => m x n Hm Hxn.
  have Hlxn : 0 < \l_(x+n) by rewrite -plus_INR; apply (l_x_pos l l_fin); rewrite plus_INR.
  rewrite /life_acc.
  rewrite -Rmult_assoc (Rmult_comm _ (/m)) Rmult_assoc.
  rewrite big_distrr /=.
  under eq_big_nat => k Hk.
  { move: Hk => /andP; case => /leP => Hk_lb /ltP => Hk_ub.
    have Hl : 0 < \l_ (x + n - k/m).
    { apply (Rlt_le_trans _ \l_(x+n)); auto.
      apply l_decr.
      rewrite /Rminus -{2}(Rplus_0_r (x+n)).
      apply Rplus_le_compat_l.
      rewrite -(Ropp_involutive 0); apply Ropp_le_contravar; rewrite Ropp_0.
      apply Rdiv_le_0_compat; by [| move: Hk_lb => /le_INR /=; lra]. }
    rewrite /ins_pure_endow_life.
    rewrite (_ : \p_{n&x} = \p_{n-k/m & x} * \p_{k/m & x+n-k/m}).
    2:{ rewrite (_ : INR n = n - k/m + k/m); [| lra].
        rewrite p_mult; [| by rewrite /Rminus -Rplus_assoc; apply pos_neq0].
        rewrite Rplus_assoc Rplus_opp_l Rplus_0_r.
        rewrite /Rminus -Rplus_assoc //. }
    have Hp : \p_{ k/m & x + n - k/m} <> 0.
    { rewrite /survive.
      apply /pos_neq0 /Rdiv_lt_0_compat; auto.
      rewrite /Rminus !Rplus_assoc Rplus_opp_l Rplus_0_r //. }
    rewrite Rinv_mult_distr //; [| apply /pos_neq0 /exp_pos].
    rewrite Rmult_assoc (Rmult_comm _ (/ _ * / _)) -3!Rmult_assoc Rmult_assoc
      (Rmult_comm \p_{_&_}) -Rmult_assoc (Rmult_assoc _ (/ \p_{_&_}) (\p_{_&_}))
      Rinv_l ?Rmult_1_r; auto.
    rewrite -Rpower_Ropp -Rpower_plus -/(Rminus n (k/m)).
    over. }
    by rewrite ann_rev.
Qed.

Lemma ann_due_pure_endow_acc_due : forall (m x n : nat), 0 < m -> x+n < \ω ->
  \a''^{m}_{x:n} = \A_{x:n`1} * \s''^{m}_{x:n}.
Proof.
  move => m x n Hm Hxn.
  have Hlxn : 0 < \l_(x+n) by rewrite -plus_INR; apply (l_x_pos l l_fin); rewrite plus_INR.
  rewrite /life_acc_due.
  rewrite -Rmult_assoc (Rmult_comm _ (/m)) Rmult_assoc.
  rewrite big_distrr /=.
  under eq_big_nat => k Hk.
  { move: Hk => /andP; case => /leP => Hk_lb /ltP => Hk_ub.
    have Hl : 0 < \l_ (x + n - (k+1)/m).
    { apply (Rlt_le_trans _ \l_(x+n)); auto.
      apply l_decr.
      rewrite /Rminus -{2}(Rplus_0_r (x+n)).
      apply Rplus_le_compat_l.
      rewrite -(Ropp_involutive 0); apply Ropp_le_contravar; rewrite Ropp_0.
      apply Rdiv_le_0_compat; by [| move: Hk_lb => /le_INR /=; lra]. }
    rewrite /ins_pure_endow_life.
    rewrite (_ : \p_{n&x} = \p_{n-(k+1)/m & x} * \p_{(k+1)/m & x+n-(k+1)/m}).
    2:{ rewrite (_ : INR n = n - (k+1)/m + (k+1)/m); [| lra].
        rewrite p_mult; [| by rewrite /Rminus -Rplus_assoc; apply pos_neq0].
        rewrite Rplus_assoc Rplus_opp_l Rplus_0_r.
        rewrite /Rminus -Rplus_assoc //. }
    have Hp : \p_{(k+1)/m & x + n - (k+1)/m} <> 0.
    { rewrite /survive.
      apply /pos_neq0 /Rdiv_lt_0_compat; auto.
      rewrite /Rminus !Rplus_assoc Rplus_opp_l Rplus_0_r //. }
    rewrite Rinv_mult_distr //; [| apply /pos_neq0 /exp_pos].
    rewrite Rmult_assoc (Rmult_comm _ (/ _ * / _)) -3!Rmult_assoc Rmult_assoc
      (Rmult_comm \p_{_&_}) -Rmult_assoc (Rmult_assoc _ (/ \p_{_&_}) (\p_{_&_}))
      Rinv_l ?Rmult_1_r; auto.
    rewrite -Rpower_Ropp -Rpower_plus -/(Rminus n (k/m)).
    over. }
    by rewrite ann_due_rev.
Qed.

Lemma acc_imm_due : forall (x n : nat), x+1+n < \ω -> \s_{x:n} = \v * \p_(x+n) * \s''_{(x+1):n}.
Proof.
  move => x n Hxn.
  have Hxn' : (((x+1)%coq_nat + n)%coq_nat < \ω)%coq_nat by apply INR_lt; rewrite !plus_INR.
  have Hp : \p_(x+n) <> 0.
  { rewrite /survive.
    rewrite (_ : 1 = 1%N) // -!plus_INR.
    apply /pos_neq0 /Rdiv_lt_0_compat; apply /l_x_pos /lt_INR; lia. }
  rewrite /life_acc_due Rinv_1 Rmult_1_l mul1n.
  rewrite big_distrr /=.
  under eq_big_nat => k Hk.
  { have Hxnkk : x + n - k + k = x + n by lra.
    have Hpk : \p_{ k & x + n - k} <> 0.
    { rewrite /survive Hxnkk.
      rewrite -plus_INR -minus_INR; [| by move: Hk => /andP; case => _ /ltP; lia].
      apply /pos_neq0 /Rdiv_lt_0_compat; apply /l_x_pos /lt_INR; lia. }
    rewrite Rdiv_1 plus_INR /=.
    rewrite (_ : x + 1 + n - (k + 1) = x + n - k); [| lra].
    rewrite p_mult.
    2:{ rewrite /Rminus Rplus_assoc Rplus_opp_l Rplus_0_r -plus_INR.
        apply /pos_neq0 /l_x_pos.
        rewrite plus_INR; lra. }
    rewrite Rinv_mult_distr ?Hxnkk;
      [| apply /pos_neq0 /exp_pos | by apply Rmult_integral_contrapositive_currified].
    rewrite Rinv_mult_distr // -Rmult_assoc (Rmult_assoc \v) (Rmult_comm \p_(x+n))
      -(Rmult_assoc \v) Rmult_assoc (Rmult_comm (/ _)) -(Rmult_assoc \p_(x+n)) Rinv_r //
      Rmult_1_l.
    rewrite -Rpower_Ropp -{1}(Rpower_1 \v); auto.
    rewrite -Rpower_plus Ropp_plus_distr (Rplus_comm 1) Rplus_assoc Rplus_opp_l Rplus_0_r.
    rewrite Rpower_Ropp -Rinv_mult_distr //; [| apply /pos_neq0 /exp_pos].
    over. }
    by rewrite acc_annual.
Qed.

Lemma acc_imm_1_due : forall (x n : nat), x+n < \ω -> 0 < n -> \s_{x:n} = 1 + \s''_{(x+1):(n-1)}.
Proof.
  move => x n Hxn Hn.
  rewrite acc_annual acc_due_annual.
  rewrite {1}(_ : n = (n-1).+1);
    [| rewrite SSR_minus -pred_of_minus -(S_pred _ 0) //;
         apply INR_lt; rewrite (_ : INR 0%N = 0) //].
  rewrite big_nat_recl; [| apply /leP; move: Hn => /(INR_lt 0); lia].
  rewrite Rpower_O ?Rmult_1_l; auto.
  rewrite (_ : x+n-0 = INR (x+n)%N); [| rewrite /Rminus Ropp_0 Rplus_0_r plus_INR //].
  rewrite p_0_1 ?plus_INR // Rinv_1.
  under eq_big_nat => k Hk.
  { rewrite -Nat.add_1_r plus_INR /=.
    rewrite (_ : x + n = x + 1%N + (n - 1)%N);
      [| rewrite minus_INR; [lra | move: Hn => /(INR_lt 0); lia]].
    over. }
    by[].
Qed.

Lemma acc_due_pure_endow : forall (x n : nat), x+n < \ω -> 0 < n ->
  \s''_{x:n} = \s''_{(x+1):(n-1)} + /(\A_{x:n`1}).
Proof.
  move => x n Hxn Hn.
  have Hn' : (0 < n)%coq_nat by apply INR_lt.
  rewrite acc_due_annual.
  rewrite {1}(_ : n = (n-1).+1);
    [| rewrite SSR_minus -pred_of_minus -(S_pred _ 0) //;
         apply INR_lt; rewrite (_ : INR 0%N = 0) //].
  rewrite big_nat_recr /=; [| apply /leP; lia].
  rewrite (_ : (n-1)%N+1 = n); [| rewrite minus_INR /=; [lra | lia]].
  rewrite (_ : x+n-n = x); [| lra].
  under eq_big_nat => k _ do
    [rewrite (_ : x+n-(k+1) = (x + 1)%N + (n - 1)%N - (k + 1));
      [| rewrite plus_INR minus_INR //; lra]].
  rewrite acc_due_annual /ins_pure_endow_life //.
Qed.

Lemma acc_imm_due_pure_endow_1 : forall (x n : nat), x+n < \ω -> 0 < n ->
  \s_{x:n} = \s''_{x:n} - /(\A_{x:n`1}) + 1.
Proof.
  move => x n Hxn Hn.
  rewrite acc_imm_1_due //.
  rewrite (acc_due_pure_endow x n); lra.
Qed.

Lemma prem_endow_term : forall (m x n : nat), 0 < m -> 0 < n ->
  \P^{m}_{x:n} = \P^{m}_{x`1:n} + \P^{m}_{x:n`1}.
Proof.
  move => m x n _ _.
  rewrite /prem_endow_life /prem_term_life /prem_pure_endow_life /ins_endow_life.
    by rewrite Rdiv_plus_distr.
Qed.

Lemma prem_term_whole : forall (m x n : nat), 0 < m -> x < \ω -> \ω - x <= n ->
  \P^{m}_{x`1:n} = \P^{m}_x.
Proof.
  move => m x n Hm Hx Hn.
  rewrite /prem_term_life.
  rewrite ins_term_whole //.
  rewrite ann_due_temp_whole //.
Qed.

Lemma prem_pure_endow_old_0 : forall (m x n : nat), 0 < m -> x < \ω -> \ω - x <= n ->
  \P^{m}_{x:n`1} = 0.
Proof.
  move => m x n Hm Hx Hn.
  rewrite /prem_pure_endow_life.
  rewrite ins_pure_endow_old_0; lra.
Qed.

Lemma prem_endow_whole : forall (m x n : nat), 0 < m -> x < \ω -> \ω - x <= n ->
  \P^{m}_{x:n} = \P^{m}_x.
Proof.
  move => m x n Hm Hx Hn.
  have Hnpos : 0 < n by eapply Rlt_le_trans; [| apply Hn]; lra.
  rewrite prem_endow_term // prem_term_whole // prem_pure_endow_old_0 //; lra.
Qed.

Lemma prem_endow_ann_due_d : forall (m x n : nat), 0 < m -> x < \ω -> 0 < n ->
  \P^{m}_{x:n} = /(\a''^{m}_{x:n}) - \d^{m}.
Proof.
  move => m x n Hm Hx Hn.
  rewrite /prem_endow_life.
  rewrite ins_endow_ann_due //.
  rewrite RIneq.Rdiv_minus_distr.
  rewrite /Rdiv Rinv_r_simpl_l;
    [| apply pos_neq0; eapply Rlt_le_trans; [| apply ann_due_lb];
         first apply Rinv_0_lt_compat; lra].
  rewrite Rmult_1_l //.
Qed.

Lemma prem_whole_ann_due_d : forall (m x : nat), 0 < m -> x < \ω ->
  \P^{m}_x = /(\a''^{m}_x) - \d^{m}.
Proof.
  move => m x Hm Hx.
  have Hx' : (x < \ω)%coq_nat by apply INR_lt => //.
  rewrite -(prem_endow_whole m x (\ω - x)) //; [| rewrite SSR_minus minus_INR; [lra | lia]].
  rewrite prem_endow_ann_due_d //; rewrite SSR_minus minus_INR; [lra | lia].
Qed.

Lemma acc_due_plus_ann_due : forall (m t x n : nat), 0 < m -> x+t < \ω -> t <= n ->
    (\s''^{m}_{x:t} + \a''^{m}_{(x+t):(n-t)}) * \A_{x:t`1} = \a''^{m}_{x:n}.
Proof.
  move => m t x n Hm Hxt Htn.
  have Hlxt : 0 < \l_(x+t) by rewrite -plus_INR; apply /l_x_pos; rewrite plus_INR.
  rewrite Rmult_plus_distr_r.
  rewrite acc_due_rev // Rmult_assoc.
  rewrite big_distrl /=.
  under eq_big_nat => k Hk.
  { move: Hk => /andP; case => /leP Hle0k /ltP Hltkt.
    have Hlxkm : 0 < \l_(x+k/m).
    { apply (Rlt_le_trans _ \l_(x+t)); auto.
      apply l_decr.
      move: Hltkt => /lt_INR; rewrite mult_INR => /(Rmult_lt_compat_r (/m)).
      rewrite Rinv_r_simpl_m; auto;
        rewrite -/(Rdiv k m) => /(_ (Rinv_0_lt_compat m Hm)); lra. }
    have Hptkmx : 0 < \p_{t-k/m & x+k/m}.
    { rewrite /survive.
      apply Rdiv_lt_0_compat; auto.
      by rewrite (_ : x + k / m + (t - k / m) = x + t); [| lra]. }
    rewrite /ins_pure_endow_life.
    rewrite Rinv_mult_distr; [| apply /pos_neq0 /exp_pos | auto].
    rewrite -Rmult_assoc (Rmult_assoc _ _ (\v^t)) (Rmult_comm _ (\v^t))
      -Rmult_assoc Rmult_assoc.
    rewrite -Rpower_Ropp -Rpower_plus (_ : - (t - k / m) + t = k/m); [| lra].
    rewrite {2}(_ : INR t = k/m + (t - k/m)); [| lra].
    rewrite p_mult; auto.
    rewrite (Rmult_comm (/ _)) Rmult_assoc Rinv_r ?Rmult_1_r; auto.
    over. }
  rewrite /life_ann_due Rmult_assoc.
  rewrite big_distrl /= mulnBr.
  under [\big[Rplus/0]_(_<=_<_-_)_]eq_big_nat => k Hk.
  { move: Hk => /andP; case => /leP Hle0k /ltP Hltknt.
    rewrite /ins_pure_endow_life.
    rewrite -Rmult_assoc (Rmult_assoc _ _ (\v^t)) (Rmult_comm _ (\v^t))
      -Rmult_assoc Rmult_assoc.
    rewrite -Rpower_plus.
    rewrite plus_INR (Rmult_comm \p_{_&_}) -p_mult ?(Rplus_comm _ (k/m)); auto.
    rewrite (_ : k / m + t = (k + m*t)%N/m);
      [| rewrite plus_INR mult_INR Rdiv_plus_distr /Rdiv Rinv_r_simpl_m; auto].
    over. }
  rewrite -Rmult_plus_distr_l.
  rewrite -(big_addn _ _ _ xpredT (fun k:nat => \v ^ (k / m) * \p_{ k / m & x})) add0n.
  rewrite -big_cat_nat; auto.
    by rewrite leq_pmul2l; [apply /leP /INR_le | apply /ltP /INR_lt].
Qed.

(******************************************************************************)

Hypothesis l_C1 : forall u:R, ex_derive l u /\ continuous (Derive l) u.

Hint Resolve ex_derive_l continuous_l continuous_Derive_l : core.
Hint Resolve l_omega_0 psi_finite omega_pos le_psi_omega l_old_0 : core.

Lemma ins_pure_endow_old_0' : forall (u n : R), u < \ψ -> \ψ - u <= n -> \A_{u:n`1} = 0.
Proof.
  move => u n Hu Hn.
  rewrite /ins_pure_endow_life.
  rewrite p_old_0'' //; lra.
Qed.

Lemma ins_term_cont_0_0 : forall u:R, \Abar_{u`1:0} = 0.
Proof.
  move => x.
  rewrite /ins_term_life_cont /=.
  rewrite RInt_point.
    by rewrite Rmult_0_r.
Qed.

Lemma lim_ins_term_cont : forall x n : nat, is_lim_seq (fun m:nat => \A^{m}_{x`1:n}) \Abar_{x`1:n}.
Proof.
  move => x.
  case.
  { rewrite ins_term_cont_0_0.
    apply (is_lim_seq_ext_loc (fun _ => 0)); [| apply is_lim_seq_const].
    exists 1%N => m Hm.
    rewrite ins_term_0_0 //.
      by apply (lt_INR 0). }
  move => n.
  set (dl := (fun u:R => (Derive l u))).
  set (IdxSum := {m:nat &{ k:nat | (k < m.+1*n.+1)%N }}).
  set (RMVT := (fun p:IdxSum => (fun u:R => let 'existT m (exist k _) := p in
                 x + (k+1)/(m+1) - 1/(m+1) <= u <= x + (k+1)/(m+1) /\
                 \l_(x + (k+1)/(m+1)) - \l_(x + (k+1)/(m+1) - 1/(m+1)) = (dl u)/(m+1)))).
  have HMVT : forall p:IdxSum, exists u:R, RMVT p u.
  { case => m; case => k Hk.
    case: (@MVT' l (x+(k+1)/(m+1)-1/(m+1)) (x+(k+1)/(m+1)) dl).
    - rewrite /Rminus -{2}(Rplus_0_r (x+(k+1)/(m+1))).
      apply Rplus_le_compat_l.
      rewrite -Ropp_0.
      apply /Ropp_le_contravar /Rdiv_le_0_compat;
        [lra | rewrite -(plus_INR m 1); apply (lt_INR 0); lia].
    - move => v _; auto_derive; [| rewrite Rmult_1_l]; auto.
    - move => v _; apply eq_R_continuous; auto.
    - move => v; case => Hv Hvspec.
      exists v.
        by split; lra. }
  case: (choice RMVT HMVT) => xi Hxi.
  apply (@is_lim_seq_diff_0 (fun m:nat =>
    -/(\l_x) * (/m * \Rsum_(0 <= j < m*n.+1) \v^((j+1)/m) * dl (x + (j+1)/m)))).
  { rewrite /ins_term_life_cont.
    rewrite (_ : (- / \l_ x * RInt (fun s:R => \v^s*Derive (fun r:R => \l_(x+r)) s) 0 n.+1)
      = Rbar_mult (- / \l_x) (RInt (fun s:R => \v^s*Derive (fun r:R => \l_(x+r)) s) 0 n.+1));
      auto.
    apply (is_lim_seq_scal_l _ _
      (RInt (fun s:R => \v^s * Derive (fun r:R => \l_(x+r)) s) 0 n.+1)).
    apply (is_lim_seq_ext_loc
      (fun m:nat => n.+1 / (m*n.+1)%N *
      \Rsum_(0 <= j < m*n.+1) \v^(j.+1*n.+1/(m*n.+1)%N) * dl (x + j.+1*n.+1/(m*n.+1)%N))).
    { exists 1%N => m Hm.
      have Hminv : n.+1 / (m*n.+1)%N = /m
        by rewrite mult_INR; field; split; apply /pos_neq0 /(lt_INR 0); lia.
      rewrite !Hminv.
        by under eq_big_nat => j Hj do
          (rewrite (_ : j.+1*n.+1/(m*n.+1)%N = (j+1)/m);
            [| by rewrite -Nat.add_1_r plus_INR /Rdiv Rmult_assoc
                                       -/(Rdiv n.+1 (m*n.+1)%N) Hminv]). }
    apply (is_lim_seq_subseq
      (fun N:nat => n.+1/N * \Rsum_(0 <= j < N) \v^(j.+1*n.+1/N) * dl (x + j.+1*n.+1/N)) _
      (fun m:nat => (m*n.+1)%N));
      [apply mulnr_eventually; lia |].
    rewrite is_lim_seq_incr_1.
    apply (is_lim_seq_ext
      (fun N:nat => (n.+1-0)/(N+1) *
                 \Rsum_(0<=j<N+1) (\v^(0+j.+1*(n.+1-0)/(N+1)) *
                                     Derive (fun r:R => \l_(x+r)) (0+j.+1*(n.+1-0)/(N+1))))).
    { move => N.
      rewrite Rminus_0_r -(plus_INR N 1) /addn /addn_rec Nat.add_1_r.
        by under eq_big_nat => j _ do (rewrite Rplus_0_l Derive_incr; auto). }
    apply quadr_right; [apply (le_INR 0); lia |].
    apply (ex_RInt_continuous (fun s:R => \v^s * Derive (fun r:R => \l_(x+r)) s)) => s Hs.
    apply (continuous_mult _ (Derive _)); [apply continuous_Rpower_snd |].
    apply (continuous_ext (fun r:R => Derive l (x+r))).
    + move => t.
      rewrite Derive_incr; auto.
    + apply continuous_comp; [apply continuous_Rplus_snd | auto]. }
  { rewrite is_lim_seq_incr_1.
    rewrite /ins_term_life /die.
    apply (is_lim_seq_ext (fun N:nat => - / \l_x * (\Rsum_(0<=k<N.+1*n.+1) \v^((k+1)/N.+1) *
      (dl (x+(k+1)/N.+1) / N.+1 - (\l_(x+k/N.+1+1/N.+1) - \l_(x+k/N.+1)))))).
    { move => N.
      rewrite (S_addn N).
      under eq_big_nat => k _.
      { rewrite Rmult_minus_distr_l {1}/Rminus.
        rewrite /(Rdiv (dl _) (N+1)%N) -/(Rdiv (k+1) (N+1)%N) -Rmult_assoc.
        over. }
      rewrite big_split /=.
      rewrite -big_distrl /=.
      rewrite (Rmult_comm _ (/(N+1)%N)).
      rewrite Rmult_plus_distr_l.
      rewrite -(Ropp_mult_distr_l (/ \l_x) (\Rsum_(_<=_<_) _)) (big_distrr (/ \l_x)) /=.
      under [\Rsum_(_<=_<_) (/ \l_x * _)]eq_big_nat => k _ do
        rewrite Ropp_mult_distr_r Ropp_minus_distr Rmult_comm Rmult_assoc -/(Rdiv _ \l_x).
          by rewrite /Rminus. }
    rewrite -{2}(Rmult_0_r (- / \l_x)).
    rewrite (_ : - / \l_x * 0 = Rbar_mult (- / \l_x) 0); auto.
    apply (is_lim_seq_scal_l _ (- / \l_x) 0).
    apply is_lim_seq_abs_minus_0.
    rewrite /is_lim_seq /filterlim /filter_le /Rbar_locally /locally.
    apply is_lim_seq_Reals.
    rewrite /Un_cv => eps Heps.
    have HdlC0' : forall u:R, x <= u <= x + n.+1 -> continuity_pt dl u.
    { move => u Hu.
      apply continuity_pt_continuous.
      rewrite /dl; auto. }
    move: (@Heine_cor2 dl x (x+n.+1) HdlC0').
    set (eps' := eps / (2*(n+1))).
    have Heps' : 0 < eps' by apply Rdiv_lt_0_compat;
      [| rewrite -(plus_INR n 1) -(mult_INR 2); apply (lt_INR 0); lia].
    set (Peps' := mkposreal eps' Heps').
    move => /(_ Peps').
    case => delta Hdl.
    destruct delta as [delta Hdelta].
    set (N := Z.to_nat (ceil (/delta))).
    exists N => m Hm.
    have Hm1 : 0 < m + 1 by rewrite -(plus_INR m 1); apply /(lt_INR 0); lia.
    have Hm1' : m + 1 <> 0; auto.
    have HinvSm : 0 <= /(m+1) by apply /Rlt_le /RinvN_pos.
    rewrite -Nat.add_1_r plus_INR /=.
    rewrite /R_dist.
    rewrite !Rminus_0_r Rabs_Rabsolu.
    eapply Rle_lt_trans; [apply Rsum_Rabs |] => /=.
    apply (Rle_lt_trans _ (\Rsum_(0<=k<(m+1)%coq_nat*n.+1) eps'/(m+1))).
    { apply Rsum_le_compat => k Hk.
      have Hk' : (k < m.+1 * n.+1)%N
        by move: Hk => /andP; case => _ /ltP; rewrite Nat.add_1_r => Hk''; apply /ltP.
      have H0divSkSm : 0 < (k+1)/(m+1)
        by apply Rdiv_lt_0_compat; rewrite -(plus_INR _ 1); apply /(lt_INR 0); lia.
      have HdivSkSmSn : (k+1)/(m+1) <= n.+1.
      { rewrite /Rdiv -(Rinv_r_simpl_l (m+1) n.+1) //.
        apply Rmult_le_compat_r; auto.
        rewrite Rmult_comm -!(plus_INR _ 1) -mult_INR !Nat.add_1_r; apply le_INR.
          by cut (k < m.+1 * n.+1)%coq_nat; [| apply /ltP]. }
      rewrite Rabs_mult.
      rewrite Rabs_pos_eq; [| rewrite /v_pres /Rpower; apply /Rlt_le /exp_pos].
      rewrite (_ : x + k/(m+1) + 1/(m+1) = x + (k+1)/(m+1)); [| by field].
      rewrite (_ : x + k/(m+1) = x + (k+1)/(m+1) - 1/(m+1)); [| by field].
      set (p := (existT (fun m0:nat => {k:nat | (k < m0.+1 * n.+1)%N}) m
                        (exist (fun k0:nat => (k0 < m.+1 * n.+1)%N) k Hk'))).
      case: (Hxi p); rewrite /RMVT /= => Hxidom Hxispec.
      rewrite Hxispec.
      rewrite -RIneq.Rdiv_minus_distr.
      rewrite Rabs_div //.
      rewrite (Rabs_pos_eq (m+1)); [| by apply Rlt_le].
      rewrite -(Rmult_1_l (eps' / (m+1))).
      apply Rmult_le_compat;
        [rewrite /v_pres /Rpower; apply /Rlt_le /exp_pos |
         by apply Rmult_le_pos; [apply Rabs_pos |] |
         by apply /Rlt_le /lt_vpow_1 |].
      rewrite !/Rdiv.
      apply Rmult_le_compat_r; auto.
      apply /Rlt_le /Hdl.
      - rewrite -{1}(Rplus_0_r x) -/(Rdiv (k+1) (m+1)).
          by split; apply Rplus_le_compat_l; [apply /Rlt_le| ].
      - split.
        + apply (Rle_trans _ (x + (k+1)/(m+1) - 1/(m+1))); [| apply Hxidom].
          rewrite -{1}(Rplus_0_r x) /Rminus Rplus_assoc; apply Rplus_le_compat_l.
          rewrite (_ : (k+1)/(m+1) + - (1/(m+1)) = k/(m+1)); [| by field].
          apply Rdiv_le_0_compat; [apply (le_INR 0); lia | auto].
        + by apply (Rle_trans _ (x + (k+1)/(m+1))); [apply Hxidom | apply Rplus_le_compat_l].
      - rewrite Rabs_pos_eq; [| lra].
        apply (Rle_lt_trans _ (1/(m+1))); [lra |].
        have Hdelta' : 0 < ceil (/ delta)
          by apply (Rlt_le_trans _ (/delta));
          [by apply Rinv_0_lt_compat | apply ceil_correct].
        apply (Rlt_le_trans _ (1/N)).
        + rewrite /(Rdiv 1) !Rmult_1_l.
          apply Rinv_1_lt_contravar; [| move: Hm; rewrite /ge => /le_INR; lra].
          apply (le_INR 1); rewrite -/(lt 0%N N); apply (INR_lt 0) => /=.
          rewrite /N.
          rewrite INR_Ztonat_IZR; by [| apply le_0_IZR; lra].
        + rewrite /N /=.
          rewrite -{2}(Rinv_involutive delta); auto.
          rewrite /Rdiv Rmult_1_l.
          apply Rinv_le_contravar; auto; [by apply Rinv_0_lt_compat |].
          rewrite INR_Ztonat_IZR; [apply ceil_correct | apply le_0_IZR; lra]. }
    rewrite big_const_nat subn0.
    rewrite iter_Rplus Rplus_0_r.
    rewrite /Peps' /eps' /=.
    rewrite (_ : ((m+1)%coq_nat * n.+1)%N * (eps/(2*(n+1))/(m+1)) = eps/2); [lra |].
    rewrite mult_INR -(Nat.add_1_r n) !plus_INR /=; field.
    split; apply pos_neq0; rewrite -(plus_INR _ 1); apply /(lt_INR 0); lia. }
Qed.

Lemma Lim_ins_term_cont : forall x n : nat, Lim_seq (fun m:nat => \A^{m}_{x`1:n}) = \Abar_{x`1:n}.
Proof.
  move => x n.
  apply /is_lim_seq_unique /lim_ins_term_cont.
Qed.

Lemma ins_term_cont_whole_cont : forall u n : R, u < \ψ -> \ψ - u <= n -> \Abar_{u`1:n} = \Abar_u.
Proof.
  move => u n Hu Hn.
  have HlC0 : forall w:R, continuous (fun s:R => \v^s * Derive (fun r:R => \l_(u+r)) s) w.
  { move => w.
    apply (continuous_mult (Rpower \v)).
    - apply continuous_Rpower_snd.
    - apply (continuous_ext (fun r:R => (Derive l) (u+r))).
      + move => r.
        rewrite Derive_incr; auto.
      + apply continuous_comp; auto.
        apply continuous_Rplus_snd. }
  rewrite /ins_whole_life_cont /ins_term_life_cont.
  rewrite -(RInt_Chasles _ 0 (\ψ-u) n); [| by apply ex_RInt_continuous => w _ ..].
  rewrite (RInt_ext (fun s:R => \v^s * Derive (fun r:R => \l_(u+r)) s) (fun => 0) (\ψ-u) n).
    by rewrite RInt_const /scal /= /mult /= Rmult_0_r /plus /= Rplus_0_r.
  move => w.
  rewrite Rmin_left //.
  case => Hw _.
  rewrite (Derive_ext_loc (fun r:R => \l_(u+r)) (fun => 0)); [rewrite Derive_const; lra |].
  set (eps := w - (\ψ - u)).
  have Heps : 0 < eps by rewrite /eps; lra.
  exists (mkposreal eps Heps) => /= t Ht.
  apply l_out_0.
  rewrite -psi_finite //=.
  move: Ht; rewrite /ball /= /AbsRing_ball /R_AbsRing /abs /= /minus /plus /opp /=.
  case /Rabs_def2.
  rewrite /eps; lra.
Qed.

Lemma lim_ins_whole_cont : forall x:nat,  x < \ω -> is_lim_seq (fun m:nat => \A^{m}_x) \Abar_x.
Proof.
  move => x Hx.
  have Hx' : (x <= \ω)%coq_nat by apply INR_le; lra.
  have Homegax : \ω - x <= (\ω - x)%N by rewrite minus_INR; [lra | done].
  have Hxpsi : x < \ψ by apply (lt_omega_lt_psi _ l_fin).
  have Hpsix : \ψ - x <= \ω - x
    by move: (le_psi_omega l l_fin); rewrite -psi_finite //=; lra.
  rewrite -(ins_term_cont_whole_cont _ (\ω-x)) //.
  apply (is_lim_seq_ext_loc (fun m:nat => \A^{m}_{x`1:(\ω-x)})).
  - exists 1%N => m Hm.
    apply ins_term_whole => //.
    apply /(lt_INR 0); lia.
  - rewrite -minus_INR //.
    apply lim_ins_term_cont => //.
Qed.

Lemma Lim_ins_whole_cont : forall x:nat, x < \ω -> Lim_seq (fun m:nat => \A^{m}_x) = \Abar_x.
Proof.
  move => x n.
    by apply /is_lim_seq_unique /lim_ins_whole_cont.
Qed.

Lemma ins_term_cont_pure_endow : forall t u n : R, u+t < \ψ -> 0 <= t <= n ->
  \Abar_{u`1:n} = \Abar_{u`1:t} + \A_{u:t`1} * \Abar_{(u+t)`1:(n-t)}.
Proof.
  move => t u n Hut [H0t Htn].
  have Hntt : n - t + t = n by lra.
  have Ht : u < \ψ by lra.
  have HC0 : forall w u' : R, continuous (fun s:R => \v^s * Derive (fun r:R => \l_(u'+r)) s) w.
  { move => w u'.
    apply (continuous_mult (Rpower \v)).
    - apply continuous_Rpower_snd.
    - apply (continuous_ext (fun r:R => (Derive l) (u'+r))).
      + move => r.
        rewrite Derive_incr; auto.
      + apply continuous_comp; auto.
        apply continuous_Rplus_snd. }
  rewrite /ins_term_life_cont /ins_pure_endow_life.
  rewrite /survive.
  rewrite -Rmult_assoc (Rmult_assoc (\v^t)).
  rewrite (_ : \v^t * (\l_(u+t) / \l_u * - / \l_(u+t)) = - / \l_u * \v^t);
    [| field; split; apply /pos_neq0 /l_u_pos; rewrite -psi_finite //].
  rewrite Rmult_assoc.
  rewrite {6}(_ : Rmult = scal) // -RInt_scal; [| by apply ex_RInt_continuous];
    rewrite /scal /= /mult /=.
  rewrite (RInt_ext (fun x:R => \v^t * (\v^x * Derive (fun r:R => \l_(u+t+r)) x))
                    (fun s:R => \v^(s+t) * (Derive l) (u+(s+t)))).
  2:{ move => s _.
      rewrite -Rmult_assoc Rpower_plus.
      rewrite Derive_incr; auto.
      rewrite (Rplus_comm s t) Rplus_assoc; lra. }
  rewrite (@RInt_comp_plus _ (fun s:R => \v^s * Derive l (u+s))); rewrite Rplus_0_l Hntt.
  2:{ apply ex_RInt_continuous => s _.
      apply (continuous_mult (Rpower \v)).
      - apply continuous_Rpower_snd.
      - apply continuous_comp; auto.
        apply continuous_Rplus_snd. }
  rewrite (RInt_ext (fun s:R => \v^s * Derive l (u+s))
                    (fun s:R => \v^s * Derive (fun r:R => \l_(u+r)) s));
    [| move => s _; rewrite Derive_incr; auto].
  rewrite -Rmult_plus_distr_l (_ : Rplus = plus) // RInt_Chasles //;
                              apply ex_RInt_continuous; auto.
Qed.

Lemma lim_ins_endow_cont : forall x n : nat, is_lim_seq (fun m:nat => \A^{m}_{x:n}) \Abar_{x:n}.
Proof.
  move => x n.
  rewrite /ins_endow_life /ins_endow_life_cont.
  rewrite Finite_Rplus.
  apply is_lim_seq_plus'; [apply lim_ins_term_cont | apply is_lim_seq_const].
Qed.

Lemma Lim_ins_endow_cont : forall x n : nat, Lim_seq (fun m:nat => \A^{m}_{x:n}) = \Abar_{x:n}.
Proof.
  move => x n.
  apply /is_lim_seq_unique /lim_ins_endow_cont.
Qed.

Lemma ins_endow_cont_whole_cont : forall u n : R, u < \ψ -> \ψ - u <= n -> \Abar_{u:n} = \Abar_u.
Proof.
  move => u n Hu Hn.
  rewrite /ins_endow_life_cont.
  rewrite ins_term_cont_whole_cont //.
  rewrite ins_pure_endow_old_0' //.
  lra.
Qed.

Lemma ins_endow_cont_0_1 : forall u:R, u < \ψ -> \Abar_{u:0} = 1.
Proof.
  move => u Hu.
  rewrite /ins_endow_life_cont.
  rewrite ins_term_cont_0_0.
  rewrite ins_pure_endow_0_1' //.
  lra.
Qed.

Lemma ins_endow_cont_pure_endow : forall t u n : R, u+t < \ψ -> 0 <= t <= n ->
  \Abar_{u:n} = \Abar_{u`1:t} + \A_{u:t`1} * \Abar_{(u+t):(n-t)}.
Proof.
  move => t u n Hut [H0t Htn].
  rewrite /ins_endow_life_cont.
  rewrite Rmult_plus_distr_l.
  rewrite (ins_term_cont_pure_endow t) //.
  rewrite (ins_pure_endow_mult' t u n) //.
  lra.
Qed.

Lemma ann_cont_0_0 : forall u:R, \abar_{u:0} = 0.
Proof.
  move => u.
  rewrite /life_ann_cont.
    by rewrite RInt_point.
Qed.

Lemma ex_RInt_vp : forall a b u : R, u < \ψ -> ex_RInt (fun s:R => \v^s * \p_{s&u}) a b.
Proof.
  move => a b u Hu.
    have Hu' : Rbar_lt u \ψ by rewrite -psi_finite.
    apply @ex_RInt_continuous => s _.
    apply (continuous_mult (Rpower \v)).
    - apply continuous_Rpower_snd.
    - by apply continuous_p_fst.
Qed.

Lemma ann_cont_pos : forall u n : R, u < \ψ -> 0 < n -> 0 < \abar_{u:n}.
Proof.
  move => u n Hu Hn.
  have Hu' : Rbar_lt u \ψ by rewrite -psi_finite.
  have Hlu : 0 < \l_u by apply l_u_pos.
  case: (l_u_nbh_pos _ l_fin l_C1 u Hu); move => [eps' Heps'] /= Hlueps'.
  set (eps := Rmin eps' n).
  have Heps : 0 < eps by apply Rmin_pos.
  have Hepsn : eps <= n by apply Rmin_r.
  have Hlueps : 0 < \l_(u + eps).
  { eapply Rlt_le_trans; [apply Hlueps' |].
    rewrite /eps.
    apply /l_decr /Rplus_le_compat_l /Rmin_l. }
  apply (Rlt_le_trans _ (eps * \v^eps * \p_{eps&u})).
  - apply Rmult_lt_0_compat; [| by apply Rdiv_lt_0_compat].
      by apply Rmult_lt_0_compat; [| apply exp_pos].
  - move: (RInt_const 0 eps (\v^eps * \p_{eps&u}));
      rewrite (_ : scal = Rmult) // Rminus_0_r -Rmult_assoc => <-.
    apply (Rle_trans _ (RInt (fun t:R => \v^t * \p_{t&u}) 0 eps)).
    + apply RInt_le; [lra | apply ex_RInt_const | by apply ex_RInt_vp |].
      move => t Ht.
      apply Rmult_le_compat;
        [apply /Rlt_le /exp_pos | apply Rdiv_le_0_compat; auto |
         apply /Rlt_le /vpow_decreasing; lra|].
      rewrite /survive /Rdiv.
        by apply Rmult_le_compat_r; [apply /Rlt_le /Rinv_0_lt_compat | apply l_decr; lra].
    + rewrite /life_ann_cont.
      rewrite -(RInt_Chasles (fun t:R => \v^t*\p_{t&u}) 0 eps n); [| by apply ex_RInt_vp ..].
      rewrite -{1}(Rplus_0_r (RInt (fun t : R => \v ^ t * \p_{ t & u}) 0 eps)).
      apply Rplus_le_compat_l.
      apply RInt_ge_0; [done | by apply ex_RInt_vp |].
      move => t Ht.
      apply Rmult_le_pos; [apply /Rlt_le /exp_pos |  apply Rdiv_le_0_compat; auto].
Qed.

Lemma lim_ann_cont : forall x n : nat, x < \ω -> is_lim_seq (fun m:nat => \a^{m}_{x:n}) \abar_{x:n}.
Proof.
  move => x.
  case.
  - move => _.
    rewrite ann_cont_0_0.
    apply (is_lim_seq_ext_loc (fun => 0)); [| apply is_lim_seq_const].
    exists 1%N => m Hm.
    rewrite ann_0_0 //.
    apply /lt_0_INR; lia.
  - move => n Hx.
    rewrite /life_ann /life_ann_cont.
    apply is_lim_seq_incr_1.
    apply (is_lim_seq_ext
             (fun m:nat => n.+1 / (m.+1 * n.+1)%N *
                        \Rsum_(0<= k < m.+1*n.+1) (\v^(k.+1*n.+1/(m.+1*n.+1)%N) *
                                                     \p_{k.+1*n.+1/(m.+1*n.+1)%N & x}))).
    + move => m.
      rewrite (_ : n.+1 / (m.+1 * n.+1)%N = / m.+1);
        [| rewrite mult_INR; field; split; rewrite S_INR; apply /pos_neq0 /INRp1_pos].
        by under eq_big_nat => k _ do       
        (rewrite (_ : k.+1 * n.+1 / (m.+1 * n.+1)%N = (k+1) / m.+1);
         [| rewrite mult_INR S_INR; field; split; apply /pos_neq0 /lt_0_INR; lia]).
    + apply (is_lim_seq_subseq
               (fun N:nat => n.+1/N * \Rsum_(0<=k<N) (\v^(k.+1*n.+1/N) * \p_{k.+1*n.+1/N & x}))
               _
               (fun m:nat => (m.+1*n.+1)%N));
        [apply (filterlim_comp _ _ _ S (muln^~ n.+1) _ eventually);
         [apply eventually_subseq => m | apply mulnr_eventually]; lia |].
      apply is_lim_seq_incr_1.
      apply (is_lim_seq_ext
               (fun N:nat => (n.+1-0) / (N+1) *
                          \big[Rplus/0]_(0 <= k < N+1)
                           (\v ^ (0+k.+1*(n.+1-0)/(N+1))*\p_{0+k.+1*(n.+1-0)/(N+1)&x}))).
      { move => N.
        rewrite Rminus_0_r (S_INR N) addn1.
          by under eq_big_nat => k _ do rewrite Rplus_0_l. }
      apply quadr_right; [apply (le_INR 0); lia |].
      apply (ex_RInt_continuous (fun t : R => \v ^ t * \p_{ t & x})) => t Ht.
      apply (continuous_mult _ (survive l ^~ x));
        [apply continuous_Rpower_snd | apply (continuous_p_fst' _ l_fin); auto].
Qed.

Lemma lim_ann_due_cont : forall x n : nat, x < \ω ->
  is_lim_seq (fun m:nat => \a''^{m}_{x:n}) \abar_{x:n}.
Proof.
  move => x.
  case.
  - move => _.
    rewrite ann_cont_0_0.
    apply (is_lim_seq_ext_loc (fun => 0)); [| apply is_lim_seq_const].
    exists 1%N => m Hm.
    rewrite ann_due_0_0 //.
    apply /lt_0_INR; lia.
  - move => n Hx.
    rewrite /life_ann_due /life_ann_cont.
    apply is_lim_seq_incr_1.
    apply (is_lim_seq_ext
             (fun m:nat => n.+1 / (m.+1 * n.+1)%N *
                        \Rsum_(0<= k < m.+1*n.+1) (\v^(k*n.+1/(m.+1*n.+1)%N) *
                                                     \p_{k*n.+1/(m.+1*n.+1)%N & x}))).
    + move => m.
      rewrite (_ : n.+1 / (m.+1 * n.+1)%N = / m.+1);
        [| rewrite mult_INR; field; split; rewrite S_INR; apply /pos_neq0 /INRp1_pos].
        by under eq_big_nat => k _ do
        (rewrite (_ : k * n.+1 / (m.+1 * n.+1)%N = k / m.+1);
         [| rewrite mult_INR; field; split; apply /pos_neq0 /lt_0_INR; lia]).
    + apply (is_lim_seq_subseq
               (fun N:nat => n.+1/N * \Rsum_(0<=k<N) (\v^(k*n.+1/N) * \p_{k*n.+1/N & x}))
               _
               (fun m:nat => (m.+1*n.+1)%N));
        [apply (filterlim_comp _ _ _ S (muln^~ n.+1) _ eventually);
         [apply eventually_subseq => m | apply mulnr_eventually]; lia |].
      apply is_lim_seq_incr_1.
      apply (is_lim_seq_ext
               (fun N:nat => (n.+1-0) / (N+1) *
                          \big[Rplus/0]_(0 <= k < N+1)
                           (\v ^ (0+k*(n.+1-0)/(N+1))*\p_{0+k*(n.+1-0)/(N+1)&x}))).
      { move => N.
        rewrite Rminus_0_r (S_INR N) addn1.
          by under eq_big_nat => k _ do rewrite Rplus_0_l. }
      apply quadr_left; [apply (le_INR 0); lia |].
      apply (ex_RInt_continuous (fun t : R => \v ^ t * \p_{ t & x})) => t Ht.
      apply (continuous_mult _ (survive l ^~ x));
        [apply continuous_Rpower_snd | apply (continuous_p_fst' _ l_fin); auto].
Qed.
  
Lemma Lim_ann_cont : forall x n : nat, x < \ω -> Lim_seq (fun m:nat => \a^{m}_{x:n}) = \abar_{x:n}.
Proof.
  move => x n Hx.
    by apply /is_lim_seq_unique /lim_ann_cont.
Qed.

Lemma Lim_ann_due_cont : forall x n : nat, x < \ω ->
  Lim_seq (fun m:nat => \a''^{m}_{x:n}) = \abar_{x:n}.
Proof.
  move => x n Hx.
    by apply /is_lim_seq_unique /lim_ann_due_cont.
Qed.

Lemma ann_cont_temp_whole : forall u n : R, u < \ψ -> \ψ - u <= n ->
  \abar_{u:n} = \abar_u.
Proof.
  move => u n Hu Hn.
  have Hu' : Rbar_lt u \ψ by rewrite -psi_finite.
  rewrite /whole_life_ann_cont /life_ann_cont.
  rewrite /ins_whole_life_cont /ins_term_life_cont.
  rewrite -(RInt_Chasles _ 0 (\ψ-u) n); [| by apply ex_RInt_vp ..].
  rewrite (RInt_ext (fun s:R => \v^s * \p_{s&u}) (fun => 0) (\ψ-u) n);
    [by rewrite RInt_const /scal /= /mult /= Rmult_0_r /plus /= Rplus_0_r |].
  move => w.
  rewrite Rmin_left //.
  case => Hw _.
  have Huw : Rbar_lt \ψ (u+w) by rewrite -psi_finite //=; lra.
  rewrite /survive.
  move: (l_out_0 l (u+w) Huw) ->; lra.
Qed.

Lemma ann_cont_pure_endow : forall t u n : R, u+t < \ψ -> 0 <= t <= n ->
  \abar_{u:n} = \abar_{u:t} + \A_{u:t`1} * \abar_{(u+t):(n-t)}.
Proof.
  move => t u n Hut Ht.
  have Hu : u < \ψ by lra.
  have Hut' : Rbar_lt (u+t) \ψ by rewrite -psi_finite.
  rewrite /life_ann_cont /ins_pure_endow_life.
  rewrite {3}(_ : Rmult = scal) //.
  rewrite -RInt_scal; [| by apply ex_RInt_vp].
  rewrite (RInt_ext (fun s:R => scal (\v^t * \p_{t&u}) (\v^s * \p_{s&u+t}))
                    (fun s:R => \v^(s+t) * \p_{(s+t)&u})).
  2:{ move => s _.
      rewrite /scal /= /mult /=.
      rewrite (Rplus_comm s t) p_mult; auto.
      rewrite Rpower_plus.
      lra. }
  rewrite (@RInt_comp_plus _ (fun s:R => \v^s * \p_{s&u})); [| by apply ex_RInt_vp ].
  rewrite Rplus_0_l.
  rewrite (_ : n-t+t = n); [| lra].
    by rewrite -(RInt_Chasles _ 0 t n); [| by apply ex_RInt_vp ..].
Qed.

Lemma ins_endow_cont_ann_cont : forall u n : R, u < \ψ -> \Abar_{u:n} = 1 - \δ * \abar_{u:n}.
Proof.
  move => u n Hu.
  have Hu' : Rbar_lt u \ψ by rewrite -psi_finite.
  have Hdl : forall r:R, is_derive (fun s:R => \l_(u+s)) r (Derive l (u+r)).
  { move => r.
    auto_derive; auto.
      by rewrite Rmult_1_l. }
  have Hexdl : forall r:R, ex_derive (fun s:R => \l_(u+s)) r
      by move => r; exists (Derive l (u+r)); apply Hdl.
  have HC0dl : forall r:R, continuous (Derive (fun s:R => \l_(u+s))) r.
  { move => r.
    apply (continuous_ext (fun s:R => (Derive l) (u+s))).
    - move => s.
      rewrite Derive_incr; auto.
    - apply continuous_comp; auto.
      apply continuous_Rplus_snd. }
  have HC0dpow : forall r:R ,continuous (Derive (Rpower \v)) r.
  { move => r.
    apply (continuous_ext (fun s:R => -\δ*\v^s)).
    - move => s.
        by rewrite (is_derive_unique _ _ _ (is_derive_vpow _ s)).
    - rewrite (_ : Rmult = scal) //; apply (continuous_scal_r _ (Rpower \v)).
      apply continuous_Rpower_snd. }
  rewrite /life_ann_cont.
  rewrite /Rminus Ropp_mult_distr_l {1}(_ : Rmult = scal) // -RInt_scal;
    [| by apply ex_RInt_vp]; rewrite /scal /= /mult /=.
  rewrite (RInt_ext _ (fun s:R => /(\l_u) * ((Derive (Rpower \v) s) * \l_(u+s)))).
  2:{ move => r _.
      rewrite (is_derive_unique _ _ _ (is_derive_vpow _ r)) //.
      rewrite /survive.
      rewrite /Rdiv; lra. }
  rewrite RInt_scal /scal /= /mult /=.
  2:{ apply ex_RInt_continuous.
      move => r _.
      apply (continuous_mult (Derive (Rpower \v))); auto.
      apply (ex_derive_continuous _ _ (Hexdl r)). }
  rewrite RInt_scal_Derive_l; auto;
    [| move => t _; apply ex_derive_Rpower_snd];
    rewrite /scal /= /mult /= /minus /opp /plus /=.
  rewrite Rpower_O; auto; rewrite Rmult_1_l Rplus_0_r.
  rewrite /ins_endow_life_cont /ins_term_life_cont /ins_pure_endow_life /survive.
  field; auto.
Qed.

Lemma ins_whole_cont_ann_cont : forall u:R, u < \ψ -> \Abar_u = 1 - \δ * \abar_u.
Proof.
  move => u Hu.
  rewrite /whole_life_ann_cont -(ins_endow_cont_whole_cont _ (\ψ-u)); [| done | lra].
    by apply ins_endow_cont_ann_cont.
Qed.

Lemma ann_cont_ins_pure_endow_acc_cont : forall u n : R, u+n < \ψ -> 0 <= n ->
  \abar_{u:n} = \A_{u:n`1} * \sbar_{u:n}.
Proof.
  move => u n Hun Hn.
  have Hun' : Rbar_lt (u+n) \ψ by rewrite -psi_finite.
  have Hlun : 0 < \l_(u+n) by apply (l_u_pos).
  rewrite /life_ann_cont /life_acc_cont.
  have HexRInt : ex_RInt (fun t : R => / (\v ^ t * \p_{ t & u + n - t})) 0 n.
  { apply (ex_RInt_continuous (fun t:R => /(\v^t * \p_{t&u+n-t}))) => t [Ht_lb Ht_ub].
    have Hlunt : 0 < \l_ (u + n - t).
    { eapply Rlt_le_trans; [apply Hlun |].
      apply l_decr.
      move: Ht_lb; rewrite Rmin_left; [lra | done]. }
    apply continuous_Rinv_comp.
    - apply (continuous_mult (Rpower \v)); [apply continuous_Rpower_snd |].
      rewrite /survive /Rdiv.
      apply (continuous_mult _ (fun s:R => /(\l_(u+n-s)))).
      + apply (continuous_comp _ l); auto.
        apply (continuous_ext (fun => u+n)); [move => s; lra | apply continuous_const].
      + apply (continuous_Rinv_comp (fun s:R => \l_(u+n-s))); [| by apply pos_neq0].
        apply (continuous_comp _ l); [apply continuous_Rminus_snd |]; auto.
    - apply pos_neq0.
      apply Rmult_lt_0_compat; [apply exp_pos |].
        by apply Rdiv_lt_0_compat; [rewrite (_ : u+n-t+t = u+n); [| lra] |]. }
  have HexRInt' : ex_RInt (fun y:R => scal (-1) (/(\v^(-1*y+n) * \p_{-1*y+n&u+n-(-1*y+n)})))
                          n 0.
  { apply (ex_RInt_comp_lin (fun t : R => / (\v ^ t * \p_{ t & u + n - t})) (-1) n n 0).
    rewrite (_ : -1*n+n=0); [| lra].
    rewrite (_ : -1*0+n=n); [| lra].
      by[]. }
  have HexRInt'' : ex_RInt
    (fun z:R => scal \A_{u:n`1} (scal (-1) (/(\v^(-1*z+n) * \p_{-1*z+n&u+n-(-1*z+n)}))))
    0 n.
  { apply (ex_RInt_scal (fun z:R => (scal (-1) (/(\v^(-1*z+n) * \p_{-1*z+n&u+n-(-1*z+n)}))))).
      by apply ex_RInt_swap. }
  move: (RInt_comp_lin (fun t:R => /(\v^t * \p_{t&u+n-t})) (-1) n n 0).
  rewrite (_ : -1*n + n = 0); [| lra].
  rewrite (_ : -1*0 + n = n); [| lra].
  move => HRInt.
  rewrite -HRInt //.
  rewrite {2}(_ : Rmult = scal) //.
  rewrite -RInt_scal //=.
  rewrite -(opp_RInt_swap _ 0 n) //.
  rewrite -RInt_opp //.
  apply RInt_ext => t [Ht_lb Ht_ub].
  have Hlut : 0 < \l_(u+t).
  { move: Ht_ub; rewrite Rmax_right // => Ht_ub.
    eapply Rlt_le_trans; [apply Hlun |].
    apply l_decr; lra. }
  have Hpntut : \p_{ n - t & u + t} <> 0
    by apply /pos_neq0 /Rdiv_lt_0_compat; [rewrite (_ : u+t+(n-t) = u+n) //; lra | auto].
  rewrite (_ : opp = Ropp) //.
  rewrite (_ : scal = Rmult) //.
  rewrite (_ : -1*t + n = n - t); [| lra].
  rewrite (_ : u+n-(n-t) = u+t); [| lra].
  rewrite -(Rmult_assoc _ (-1)) (Rmult_comm \A_{_:_`1})
                                Rmult_opp1_l Ropp_mult_distr_l Ropp_involutive.
  rewrite /ins_pure_endow_life.
  rewrite Rinv_mult_distr; [| apply /pos_neq0 /exp_pos | done].
  rewrite -(Rmult_assoc (\v^n*\p_{n&u})) (Rmult_assoc (\v^n)).
  rewrite (Rmult_comm \p_{n&u}) -Rmult_assoc Rmult_assoc.
  rewrite -Rpower_Ropp -Rpower_plus (_ : n+-(n-t) = t); [| lra].
  move: (p_mult l t (n-t) u).
  rewrite (_ : t+(n-t) = n); [| lra] => ->; auto.
  rewrite Rinv_r_simpl_l //.
Qed.

Lemma lim_acc_cont : forall x n : nat, x+n < \ω -> is_lim_seq (fun m:nat => \s^{m}_{x:n}) \sbar_{x:n}.
Proof.
  move => x n Hx.
  have Hn : 0 <= n by apply (le_INR 0); lia.
  have Hx' : x+n < \ψ
    by rewrite -plus_INR; apply (lt_omega_lt_psi _ l_fin l_C1); rewrite plus_INR.
  have HAneq0 : \A_{x:n`1} <> 0
    by apply /pos_neq0 /ins_pure_endow_pos.
  apply (is_lim_seq_ext_loc (fun m:nat => \a^{m}_{x:n} / \A_{x:n`1})).
  - exists 1%N => m Hm.
    rewrite ann_pure_endow_acc; [| apply lt_0_INR; lia | done].
      by field.
  - rewrite (_ : \sbar_{x:n} = \abar_{x:n} */ \A_{x:n`1}).
    2:{ rewrite ann_cont_ins_pure_endow_acc_cont //.
        rewrite Rinv_r_simpl_m //. }
    rewrite (_ : \abar_{x:n} */ \A_{x:n`1} = Rbar_mult \abar_{x:n} (/ \A_{x:n`1})); [| done].
    apply (is_lim_seq_scal_r (fun m:nat => \a^{m}_{x:n}) (/ \A_{x:n`1}) \abar_{x:n}).
    apply lim_ann_cont; lra.
Qed.

Lemma Lim_acc_cont : forall x n : nat, x+n < \ω -> Lim_seq (fun m:nat => \s^{m}_{x:n}) = \sbar_{x:n}.
Proof.
  move => x n Hx.
    by apply /is_lim_seq_unique /lim_acc_cont.
Qed.

Lemma lim_acc_due_cont : forall x n : nat, x+n < \ω ->
  is_lim_seq (fun m:nat => \s''^{m}_{x:n}) \sbar_{x:n}.
Proof.
  move => x n Hxn.
  have Hn : 0 <= n by apply (le_INR 0); lia.
  have Hx' : x+n < \ψ
    by rewrite -plus_INR; apply (lt_omega_lt_psi _ l_fin l_C1); rewrite plus_INR.
  have HAneq0 : \A_{x:n`1} <> 0
    by apply /pos_neq0 /ins_pure_endow_pos.
  apply (is_lim_seq_ext_loc (fun m:nat => \a''^{m}_{x:n} / \A_{x:n`1})).
  - exists 1%N => m Hm.
    rewrite ann_due_pure_endow_acc_due; [| apply lt_0_INR; lia | done].
      by field.
  - rewrite (_ : \sbar_{x:n} = \abar_{x:n} */ \A_{x:n`1}).
    2:{ rewrite ann_cont_ins_pure_endow_acc_cont //.
        rewrite Rinv_r_simpl_m //. }
    rewrite (_ : \abar_{x:n} */ \A_{x:n`1} = Rbar_mult \abar_{x:n} (/ \A_{x:n`1})); [| done].
    apply (is_lim_seq_scal_r (fun m:nat => \a''^{m}_{x:n}) (/ \A_{x:n`1}) \abar_{x:n}).
    apply lim_ann_due_cont; lra.
Qed.

Lemma Lim_acc_due_cont : forall x n : nat, x+n < \ω ->
  Lim_seq (fun m:nat => \s''^{m}_{x:n}) = \sbar_{x:n}.
Proof.
  move => x n Hx.
    by apply /is_lim_seq_unique /lim_acc_due_cont.
Qed.

Lemma prem_term_whole_cont : forall m x n : nat, 0 < m -> x < \ω -> \ω - x <= n ->
  \Pbar^{m}_{x`1:n} = \Pbar^{m}_x.
Proof.
  move => m x n Hm Hx Hn.
  have Hx' : x < \ψ by apply (lt_omega_lt_psi _ l_fin l_C1).
  have Hn' : \ψ - x <= n.
  { apply /Rle_minus_l /(l_0_equiv _ l_fin l_C1).
    rewrite -plus_INR.
    apply (l_old_0 _ l_fin).
    rewrite plus_INR; lra. }
  rewrite /prem_term_life_cont /prem_whole_life_cont.
  rewrite ins_term_cont_whole_cont //.
  rewrite ann_due_temp_whole //.
Qed.

Lemma prem_cont_term_whole : forall u n : R, u < \ψ -> \ψ - u <= n ->
  \Pbar^{p_infty}_{u`1:n} = \Pbar^{p_infty}_u.
Proof.
  move => u n Hu Hn.
  rewrite /prem_cont_term_life_cont /prem_cont_whole_life_cont.
  rewrite ins_term_cont_whole_cont //.
  rewrite ann_cont_temp_whole //.
Qed.

Lemma lim_prem_term_cont : forall x n : nat, x < \ω -> 0 < n ->
    is_lim_seq (fun m:nat => \P^{m}_{x`1:n}) \Pbar^{p_infty}_{x`1:n}.
Proof.
  move => x n Hx Hn.
  have Hx' : x < \ψ by apply (lt_omega_lt_psi _ l_fin l_C1).
  rewrite /prem_term_life /prem_term_life_cont.
    by apply is_lim_seq_div';
      [apply lim_ins_term_cont | apply lim_ann_due_cont | apply /pos_neq0 /ann_cont_pos].
Qed.

Lemma Lim_prem_term_cont : forall x n : nat, x < \ω -> 0 < n ->
  Lim_seq (fun m:nat => \P^{m}_{x`1:n}) = \Pbar^{p_infty}_{x`1:n}.
Proof.
  move => x n Hx Hn.
    by apply /is_lim_seq_unique /lim_prem_term_cont.
Qed.

Lemma lim_prem_whole_cont : forall x:nat, x < \ω ->
  is_lim_seq (fun m:nat => \P^{m}_x) \Pbar^{p_infty}_x.
Proof.
  move => x Hx.
  have Hx' : x < \ψ by apply (lt_omega_lt_psi _ l_fin l_C1).
  have Hxomega : INR (\ω - x)%N = \ω - x by rewrite minus_INR; try apply INR_le; lra.
  have Hxpsiomega : \ψ - x <= \ω - x
    by move: (le_psi_omega _ l_fin); rewrite -psi_finite //=; lra.
  apply (is_lim_seq_ext_loc (fun m:nat => \P^{m}_{x`1:\ω-x})).
  - exists 1%N => m Hm.
      by apply prem_term_whole; [apply lt_0_INR; lia | | rewrite Hxomega //; lra].
  - rewrite -(prem_cont_term_whole _ (\ω-x)) //.
    rewrite -!Hxomega.
    apply lim_prem_term_cont => //.
    rewrite Hxomega; lra.
Qed.

Lemma Lim_prem_whole_cont : forall x:nat, x < \ω ->
  Lim_seq (fun m:nat => \P^{m}_x) = \Pbar^{p_infty}_x.
Proof.
  move => x Hx.
    by apply /is_lim_seq_unique /lim_prem_whole_cont.
Qed.

Lemma lim_prem_pure_endow_cont : forall x n : nat, x < \ω -> 0 < n ->
  is_lim_seq (fun m:nat => \P^{m}_{x:n`1}) \P^{p_infty}_{x:n`1}.
Proof.
  move => x n Hx Hn.
  have Hx' : x < \ψ by apply (lt_omega_lt_psi _ l_fin l_C1).
  rewrite /prem_pure_endow_life /prem_cont_pure_endow_life /Rdiv.
  rewrite (_ : \A_{x:n`1} */ \abar_{x:n} = Rbar_mult \A_{x:n`1} (/(\abar_{x:n})));
    [| done].
  apply (is_lim_seq_scal_l (fun m:nat => (/ \a''^{m}_{x:n})) _ (/ \abar_{x:n})).
    by apply (is_lim_seq_inv (fun m:nat => \a''^{m}_{x:n}) \abar_{x:n});
      [apply lim_ann_due_cont | apply /Rbar_finite_neq /pos_neq0 /ann_cont_pos].
Qed.

Lemma Lim_prem_pure_endow_cont : forall x n : nat, x < \ω -> 0 < n ->
  Lim_seq (fun m:nat => \P^{m}_{x:n`1}) = \P^{p_infty}_{x:n`1}.
Proof.
  move => x n Hx Hn.
    by apply /is_lim_seq_unique /lim_prem_pure_endow_cont.
Qed.

Lemma lim_prem_endow_cont : forall x n : nat, x < \ω -> 0 < n ->
    is_lim_seq (fun m:nat => \P^{m}_{x:n}) \Pbar^{p_infty}_{x:n}.
Proof.
  move => x n Hx Hn.
  have Hx' : x < \ψ by apply (lt_omega_lt_psi _ l_fin l_C1).
  rewrite /prem_endow_life /prem_endow_life_cont.
    by apply is_lim_seq_div';
      [apply lim_ins_endow_cont | apply lim_ann_due_cont | apply /pos_neq0 /ann_cont_pos].
Qed.

Lemma Lim_prem_endow_cont : forall x n : nat, x < \ω -> 0 < n ->
  Lim_seq (fun m:nat => \P^{m}_{x:n}) = \Pbar^{p_infty}_{x:n}.
Proof.
  move => x n Hx Hn.
    by apply /is_lim_seq_unique /lim_prem_endow_cont.
Qed.

Lemma prem_cont_endow_term : forall u n : R,
  \Pbar^{p_infty}_{u:n} = \Pbar^{p_infty}_{u`1:n} + \P^{p_infty}_{u:n`1}.
Proof.
  move => u n.
  rewrite /prem_cont_endow_life_cont /prem_cont_term_life_cont /prem_cont_pure_endow_life.
    by rewrite -Rdiv_plus_distr.
Qed.

Lemma prem_cont_pure_endow_old_0 : forall u n : R, u < \ψ -> \ψ - u <= n ->
  \P^{p_infty}_{u:n`1} = 0.
Proof.
  move => u n Hu Hn.
  rewrite /prem_cont_pure_endow_life /Rdiv.
  rewrite ins_pure_endow_old_0' //; lra.
Qed.

Lemma prem_endow_whole_cont : forall m x n : nat, 0 < m -> x < \ω -> \ω - x <= n ->
  \Pbar^{m}_{x:n} = \Pbar^{m}_x.
Proof.
  move => m x n Hm Hx Hn.
  have Hx' : x < \ψ by apply (lt_omega_lt_psi _ l_fin l_C1).
  have Hn' : \ψ - x <= n.
  { apply /Rle_minus_l /(l_0_equiv _ l_fin l_C1).
    rewrite -plus_INR.
    apply (l_old_0 _ l_fin).
    rewrite plus_INR; lra. }
  rewrite /prem_endow_life_cont /prem_whole_life_cont.
    by rewrite ins_endow_cont_whole_cont ?ann_due_temp_whole.
Qed.

Lemma prem_cont_endow_whole : forall u n : R, u < \ψ -> \ψ - u <= n ->
  \Pbar^{p_infty}_{u:n} = \Pbar^{p_infty}_u.
Proof.
  move => u n Hu Hn.
  rewrite /prem_cont_endow_life_cont /prem_cont_whole_life_cont.
    by rewrite ins_endow_cont_whole_cont ?ann_cont_temp_whole.
Qed.

Lemma prem_cont_endow_ann_d : forall u n : R, u < \ψ -> 0 < n ->
  \Pbar^{p_infty}_{u:n} = / \abar_{u:n} - \δ.
Proof.
  move => u n Hu Hn.
  rewrite /prem_cont_endow_life_cont.
  rewrite ins_endow_cont_ann_cont //.
  field.
    by apply /pos_neq0 /ann_cont_pos.
Qed.

Lemma prem_cont_whole_ann_due_d : forall u:R, u < \ψ -> \Pbar^{p_infty}_u = / \abar_u - \δ.
Proof.
  move => u Hu.
  rewrite /prem_cont_whole_life_cont.
  rewrite ins_whole_cont_ann_cont //.
  field.
  apply /pos_neq0 /ann_cont_pos; lra.
Qed.

Lemma acc_cont_plus_ann_cont : forall t u n : R, u + t < \ψ -> 0 <= t <= n ->
  (\sbar_{u:t} + \abar_{(u+t):n-t}) * \A_{u:t`1} = \abar_{u:n}.
Proof.
  move => t u n Hut [H0t Htn].
  have Hu : u < \ψ by eapply Rle_lt_trans; [| apply Hut]; lra.
  have Hut' : Rbar_lt (u + t) \ψ by rewrite -psi_finite.
  rewrite Rmult_plus_distr_r.
  rewrite (Rmult_comm \sbar_{_:_}) (Rmult_comm \abar_{_:_}).
  rewrite -ann_cont_ins_pure_endow_acc_cont //.
  rewrite /life_ann_cont /ins_pure_endow_life.
  rewrite {2}(_ : Rmult = scal) //.
  rewrite -(RInt_scal (fun t0 : R => \v ^ t0 * \p_{ t0 & u+t})); [| by apply ex_RInt_vp].
  under [RInt _ 0 (n-t)]RInt_ext => s Hs.
  { rewrite (_ : scal = Rmult) //.
    rewrite -Rmult_assoc (Rmult_assoc (\v^t)) (Rmult_comm _ (\v^s)) -Rmult_assoc Rmult_assoc.
    rewrite -Rpower_plus.
    rewrite -p_mult; [| by apply /pos_neq0 /l_u_pos].
    rewrite (Rplus_comm t s).
    over. }
  rewrite (@RInt_comp_plus _ (fun r:R => \v^r * \p_{r&u})); [| by apply ex_RInt_vp].
  rewrite Rplus_0_l.
  rewrite (_ : n - t + t = n); [| lra].
  rewrite (_ : Rplus = plus) //.
    by rewrite RInt_Chasles; [| apply ex_RInt_vp ..].
Qed.

End Premium.
