Require Import Reals Lra Lia.
From mathcomp Require Import all_ssreflect.
From Actuary Require Export Basics Interest LifeTable Premium.
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(****************************************************************************************)

From Coquelicot Require Import Coquelicot.

(* the reserve for a term life insurance *)
Definition res_term_life (i:R) (l:life) (x n t : nat) :=
  \A[i,l]_{(x+t)`1:(n-t)} - \P[i,l]_{x`1:n} * \a''[i,l]_{(x+t):(n-t)}.
Notation "\V[ i , l ]_{ t & x `1: n }" :=
  (res_term_life i l x n t) (at level 9, x at level 9).

(* the reserve for a whole life insurance *)
Definition res_whole_life (i:R) (l:life) (l_fin : l_finite l) (x t : nat) :=
  \A[i,l,l_fin]_(x+t) - \P[i,l,l_fin]_x * \a''[i,l,l_fin]_(x+t).
Notation "\V[ i , l , l_fin ]_{ t & x }" :=
  (res_whole_life i l l_fin x t) (at level 9, x at level 9).

(* the reserve for an endowment life insurance *)
Definition res_endow_life (i:R) (l:life) (x n t : nat) :=
  \A[i,l]_{(x+t):(n-t)} - \P[i,l]_{x:n} * \a''[i,l]_{(x+t):(n-t)}.
Notation "\V[ i , l ]_{ t & x : n }" :=
  (res_endow_life i l x n t) (at level 9, x at level 9).

(****************************************************************************************)

Section Reserve.

Variable i:R.
Hypothesis i_pos : i > 0.

Variable l:life.
Hypothesis l_fin : (l_finite l).

Notation "\i" := (\i[i]) (at level 9).
Notation "\i^{ m }" := (\i[i]^{m}) (at level 9).
Notation "\d^{ m }" := (\d[i]^{m}) (at level 9).
Notation "\d" := (\d^{1}) (at level 9).
Notation "'δ'" := (δ[i]) (at level 9).
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
Notation "\d_ u" := (\d[l]_u) (at level 9).
Notation "\p_{ t & u }" := (\p[l]_{t&u}) (at level 9).
Notation "\p_ u" := (\p[l]_{1&u}) (at level 9).
Notation "\q_{ f | t & u }" := (\q[l]_{f|t&u}) (at level 9).
Notation "\q_{ t & u }" := (\q_{0|t & u}) (at level 9).
Notation "\q_{ f | & u }" := (\q_{f|1 & u}) (at level 9).
Notation "\q_ u" := (\q_{0|1 & u}) (at level 9).
Notation "\e_{ x : n }" := (\e[l]_{x:n}) (at level 9, x at level 9).
Notation "'ω'" := (ω[l,l_fin]) (at level 8).
Notation "\e_ x" := (\e[l,l_fin]_ x) (at level 9).

Notation "\A_{ x `1: n }" := (\A[i,l]_{x`1:n}) (at level 9, x at level 9).
Notation "\A_ x" := (\A[i,l,l_fin]_x) (at level 9).
Notation "\A_{ x : n `1}" := (\A[i,l]_{x:n`1}) (at level 9, x at level 9).
Notation "\A_{ x : n }" := (\A[i,l]_{x:n}) (at level 9, x at level 9).

Notation "\a_{ x : n }" := (\a[i,l]_{x:n}) (at level 9, x at level 9).
Notation "\s_{ x : n }" := (\s[i,l]_{x:n}) (at level 9, x at level 9).
Notation "\a''_{ x : n }" := (\a''[i,l]_{x:n}) (at level 9, x at level 9).
Notation "\s''_{ x : n }" := (\s''[i,l]_{x:n}) (at level 9, x at level 9).
Notation "\a_ x" := (\a[i,l,l_fin]_x) (at level 9).
Notation "\a''_ x" := (\a''[i,l,l_fin]_x) (at level 9).

Notation "\P_{ x `1: n }" := (\P[i,l]_{x`1:n}) (at level 9, x at level 9).
Notation "\P_ x" := (\P[i,l,l_fin]_x) (at level 9).
Notation "\P_{ x : n `1}" := (\P[i,l]_{x:n`1}) (at level 9, x at level 9).
Notation "\P_{ x : n }" := (\P[i,l]_{x:n}) (at level 9, x at level 9).

Notation "\V_{ t & x `1: n }" := (\V[i,l]_{t&x`1:n}) (at level 9, x at level 9).
Notation "\V_{ t & x }" := (\V[i,l,l_fin]_{t&x}) (at level 9, x at level 9).
Notation "\V_{ t & x : n }" := (\V[i,l]_{t&x:n}) (at level 9, x at level 9).

Lemma res_term_life_0_0 : forall (x n : nat), x < ω -> n > 0 -> \V_{0 & x`1:n} = 0.
Proof.
  move => x n Hx Hn.
  rewrite /res_term_life /prem_term_life.
  rewrite addn0 subn0.
  rewrite /Rdiv Rmult_assoc Rinv_l;
    [| apply pos_neq0; eapply Rge_gt_trans;
       [apply (ann_due_ge1 _ i_pos _ l_fin) => // | lra]].
  lra.
Qed.

Lemma res_whole_life_0_0 : forall x:nat, x < ω -> \V_{0 & x} = 0.
Proof.
  move => x Hx.
  assert (Hx' : (x < ω)%coq_nat) by (apply INR_lt; lra).
  rewrite /res_whole_life /prem_whole_life.
  rewrite addn0.
  rewrite /Rdiv Rmult_assoc Rinv_l; try lra.
  apply pos_neq0; eapply Rge_gt_trans;
    [apply (ann_due_ge1 _ i_pos _ l_fin) => //; rewrite SSR_minus minus_INR; [lra | lia] |
     lra].
Qed.

Lemma res_endow_life_0_0 : forall (x n : nat), x < ω -> n > 0 -> \V_{0 & x:n} = 0.
Proof.
  move => x n Hx Hn.
  rewrite /res_endow_life /prem_endow_life.
  rewrite addn0 subn0.
  rewrite /Rdiv Rmult_assoc Rinv_l;
    [| apply pos_neq0; eapply Rge_gt_trans;
       [apply (ann_due_ge1 _ i_pos _ l_fin) => // | lra]].
  lra.
Qed.

Lemma res_term_life_n_0 : forall (x n : nat), \V_{n & x`1:n} = 0.
Proof.
  move => x n.
  rewrite /res_term_life.
  rewrite subnn.
  rewrite ins_term_0_0 ann_due_0_0; lra.
Qed.

Lemma res_endow_life_n_1 : forall (x n : nat), x+n < ω -> \V_{n & x:n} = 1.
Proof.
  move => x n Hx.
  rewrite /res_endow_life.
  rewrite subnn.
  rewrite ins_endow_0_1 //; [| rewrite plus_INR //].
  rewrite ann_due_0_0; lra.
Qed.

Lemma res_term_whole : forall (t x : nat), x+t < ω -> \V_{t & x`1:(ω-x)} = \V_{t & x}.
Proof.
  move => t x Hxt.
  assert (Hx : x < ω)
    by (apply (Rle_lt_trans _ (x+t)); [rewrite -plus_INR; apply le_INR; lia | done]).
  assert (Hxt' : (x+t)%N < ω) by rewrite plus_INR //.
  assert (Hxt'' : (ω - x - t)%N >= ω - (x + t)%N)
    by (rewrite -subnDA SSR_minus minus_INR; [lra | apply INR_le; lra]).
  rewrite /res_whole_life /res_term_life.
  rewrite ins_term_whole //.
  rewrite prem_term_whole //; [| rewrite SSR_minus minus_INR; [| apply INR_le]; lra].
  rewrite ann_due_temp_whole //.
Qed.

Lemma res_endow_whole : forall (t x : nat), x+t < ω -> \V_{t & x:(ω-x)} = \V_{t & x}.
Proof.
  move => t x Hxt.
  assert (Hx : x < ω)
    by (apply (Rle_lt_trans _ (x+t)); [rewrite -plus_INR; apply le_INR; lia | done]).
  assert (Hxt' : (x+t)%N < ω) by rewrite plus_INR //.
  assert (Hxt'' : (ω - x - t)%N >= ω - (x + t)%N)
    by (rewrite -subnDA SSR_minus minus_INR; [lra | apply INR_le; lra]).
  rewrite -res_term_whole //.
  rewrite /res_endow_life /res_term_life.
  rewrite ins_endow_whole //.
  rewrite ins_term_whole //.
  rewrite prem_endow_whole //; rewrite SSR_minus minus_INR; [| apply INR_le]; lra.
Qed.  

Lemma res_endow_prem_ann_due : forall (t x n : nat), x+t < ω ->
  \V_{t & x:n} = 1 - (\P_{x:n} + \d) * \a''_{(x+t):(n-t)}.
Proof.
  move => t x n Hx.
  assert (Hx' : (x+t)%N < ω) by rewrite plus_INR //.
  rewrite /res_endow_life.
  rewrite ins_endow_ann_due; lra.
Qed.

Lemma res_endow_ann_due : forall (t x n : nat), x+t < ω -> n > 0 ->
  \V_{t & x:n} = 1 - \a''_{(x+t):(n-t)} / \a''_{x:n}.
Proof.
  move => t x n Hx Hn.
  assert (Hx' : (x+t)%N < ω) by rewrite plus_INR //.
  rewrite res_endow_prem_ann_due //.
  rewrite (_ : \P_{x:n} + \d = /(\a''_{x:n})); [lra |].
  rewrite prem_endow_ann_due_d //; [lra |].
  apply lt_INR; move: Hx' => /INR_lt; apply le_lt_trans.
  rewrite -{1}(addn0 x); apply plus_le_compat_l; lia.
Qed.
  
Lemma res_endow_ins_endow : forall (t x n : nat), x+t < ω -> n > 0 ->
  \V_{t & x:n} = (\A_{(x+t):(n-t)} - \A_{x:n}) / (1 - \A_{x:n}).
Proof.
  move => t x n Hxt Hn.
  assert (Hxt' : (x+t)%N < ω) by rewrite plus_INR //.
  assert (Hx : x < ω).
  { apply lt_INR; move: Hxt' => /INR_lt; apply le_lt_trans.
    rewrite -{1}(addn0 x); apply plus_le_compat_l; lia. }
  assert (Hd : \d <> 0) by (apply /pos_neq0 /d_nom_pos => //=; lra).
  assert (Ha'' : \a''_{x:n} <> 0).
  { apply /pos_neq0; eapply Rge_gt_trans. apply (ann_due_ge1 _ i_pos _ l_fin) => //. lra. }
  rewrite res_endow_ann_due // !ins_endow_ann_due //.
  rewrite /Rminus Ropp_plus_distr -!Rplus_assoc.
  rewrite (Rplus_assoc _ (-(\d * _))) (Rplus_comm (-(\d * _))) -Rplus_assoc.
  rewrite Rplus_opp_r !Rplus_0_l.
  rewrite Ropp_involutive Ropp_mult_distr_r.
  rewrite -Rmult_plus_distr_l.
  rewrite /Rdiv Rinv_mult_distr // -Rmult_assoc Rinv_r_simpl_m //.
  rewrite Rmult_plus_distr_r Rinv_r //; lra.
Qed.

Lemma res_endow_prem : forall (t x n : nat), t < n -> x+t < ω -> n > 0 ->
  \V_{t & x:n} = (\P_{(x+t):(n-t)} - \P_{x:n}) / (\P_{(x+t):(n-t)} + \d).
Proof.
  move => t x n Htn Hxt Hn.
  assert (Hxt' : (x+t)%N < ω) by rewrite plus_INR //.
  assert (Hx : x < ω).
  { apply lt_INR; move: Hxt' => /INR_lt; apply le_lt_trans.
    rewrite -{1}(addn0 x); apply plus_le_compat_l; lia. }
  assert (Htn' :  (n - t)%N > 0)
    by (rewrite SSR_minus minus_INR; [lra | apply INR_le; lra]).
  assert (Ha'' : \a''_{ (x + t) : n - t} <> 0).
  { apply /pos_neq0; eapply Rge_gt_trans. apply (ann_due_ge1 _ i_pos _ l_fin) => //. lra. }
  rewrite res_endow_ann_due // !prem_endow_ann_due_d //.
  rewrite /Rminus Ropp_plus_distr (Rplus_comm _ (--_)) -Rplus_assoc !(Rplus_assoc _ (-\d));
    rewrite Rplus_opp_l Rplus_opp_r Rplus_0_r.
  rewrite Rdiv_plus_distr.
  rewrite /Rdiv Rinv_r; [| apply Rinv_neq_0_compat => //]; rewrite Rinv_involutive //; lra.
Qed.

Lemma res_whole_prem_ann_due : forall (t x : nat), x+t < ω ->
  \V_{t & x} = 1 - (\P_x + \d) * \a''_(x+t).
Proof.
  move => t x Hxt.
  assert (Hx : x < ω)
    by (apply (Rle_lt_trans _ (x+t)); [rewrite -plus_INR; apply le_INR; lia | done]).
  assert (Hxt' : (x+t)%N < ω) by rewrite plus_INR //.
  assert (Hxt'' : (ω - x - t)%N >= ω - (x + t)%N)
    by (rewrite -subnDA SSR_minus minus_INR; [lra | apply INR_le; lra]).
  rewrite -res_endow_whole //.
  rewrite res_endow_prem_ann_due //.
  rewrite prem_endow_whole //; [| rewrite SSR_minus minus_INR; [lra | apply INR_le; lra]].
  rewrite ann_due_temp_whole //.
Qed.

Lemma res_whole_ann_due : forall (t x : nat), x+t < ω -> \V_{t & x} = 1 - \a''_(x+t) / \a''_x.
Proof.
  move => t x Hxt.
  assert (Hx : x < ω)
    by (apply (Rle_lt_trans _ (x+t)); [rewrite -plus_INR; apply le_INR; lia | done]).
  assert (Hxt' : (x+t)%N < ω) by rewrite plus_INR //.
  assert (Hxt'' : (ω - x - t)%N >= ω - (x + t)%N)
    by (rewrite -subnDA SSR_minus minus_INR; [lra | apply INR_le; lra]).
  rewrite -res_endow_whole //.
  rewrite res_endow_ann_due //; [| rewrite SSR_minus minus_INR; [lra | apply INR_le; lra]].
  rewrite ann_due_temp_whole //.
Qed.

Lemma res_whole_ins_whole : forall (t x : nat), x+t < ω ->
  \V_{t & x} = (\A_(x+t) - \A_x) / (1 - \A_x).
Proof.
  move => t x Hxt.
  assert (Hx : x < ω)
    by (apply (Rle_lt_trans _ (x+t)); [rewrite -plus_INR; apply le_INR; lia | done]).
  assert (Hxt' : (x+t)%N < ω) by rewrite plus_INR //.
  assert (Hxt'' : (ω - x - t)%N >= ω - (x + t)%N)
    by (rewrite -subnDA SSR_minus minus_INR; [lra | apply INR_le; lra]).
  rewrite -res_endow_whole //.
  rewrite res_endow_ins_endow //;
          [| rewrite SSR_minus minus_INR; [lra | apply INR_le; lra]].
  rewrite !ins_endow_whole //;
          rewrite SSR_minus minus_INR; [lra | apply INR_le; lra].
Qed.

Lemma res_whole_prem : forall (t x : nat), x+t < ω ->
  \V_{t & x} = (\P_(x+t) - \P_x) / (\P_(x+t) + \d).
Proof.
  move => t x Hxt.
  assert (Hx : x < ω)
    by (apply (Rle_lt_trans _ (x+t)); [rewrite -plus_INR; apply le_INR; lia | done]).
  assert (Htx : t < (ω - x)%N)
    by (rewrite SSR_minus minus_INR; [lra | apply INR_le; lra]).
  assert (Hxt' : (x+t)%N < ω) by rewrite plus_INR //.
  assert (Hxt'' : (ω - x - t)%N >= ω - (x + t)%N)
    by (rewrite -subnDA SSR_minus minus_INR; [lra | apply INR_le; lra]).
  rewrite -res_endow_whole //.
  rewrite res_endow_prem //;
          [| rewrite SSR_minus minus_INR; [lra | apply INR_le; lra]].
  rewrite !prem_endow_whole //;
          rewrite SSR_minus minus_INR; [lra | apply INR_le; lra].
Qed.

Lemma res_term_rec : forall (t x n : nat), 0 < t <= n -> x+t < ω ->
  \V_{(t-1) & x`1:n} + \P_{x`1:n} - \v * \q_(x+t-1) = \v * \p_(x+t-1) * \V_{t & x`1:n}.
Proof.
  move => t x n [H0t Htn] Hxt.
  assert (H0t' : (0 < t)%N) by (apply /ltP /INR_lt => //).
  assert (Htn' : (t <= n)%N) by (apply /leP /INR_le => //).
  assert (H1t : (1 <= t)%coq_nat)
   by (rewrite (_ : 0 = 0%N) in H0t => //; apply INR_lt in H0t; lia).
  assert (Ht1n : ((t - 1)%coq_nat <= n)%coq_nat) by (apply INR_le in Htn; lia).
  assert (Hx : x < ω)
    by (apply (Rle_lt_trans _ (x+t)); [rewrite -plus_INR; apply le_INR; lia | done]).
  assert (Hxt' : (x+t)%N < ω) by rewrite plus_INR //.
  assert (Hxt'' : (x + (t - 1))%N < ω)
    by (rewrite plus_INR SSR_minus minus_INR // (_ : INR 1%N = 1) //; lra).
  assert (Hnt : 0 < (n - (t - 1))%N)
    by (rewrite !SSR_minus !minus_INR // (_ : INR 1%N = 1) //; lra).
  rewrite /res_term_life.
  rewrite ins_term_rec //.
  rewrite ann_due_rec //;
          [| rewrite plus_INR SSR_minus minus_INR // (_ : INR 1%N = 1) //; lra].
  rewrite (_ : (x + (t - 1) + 1)%N = (x + t)%N);
    [| rewrite addnBA // subnK // addn_gt0 // H0t'; apply /orP; auto].
  rewrite (_ : (n - (t - 1) - 1)%N = (n - t)%N); [| rewrite subnA // addnK //].
  rewrite (_ : INR (x + (t - 1))%N = x + t -1);
    [| rewrite plus_INR SSR_minus minus_INR // (_ : INR 1%N = 1) //; lra].
  lra.
Qed.

Lemma res_endow_rec : forall (t x n : nat), 0 < t <= n -> x+t < ω ->
  \V_{(t-1) & x:n} + \P_{x:n} - \v * \q_(x+t-1) = \v * \p_(x+t-1) * \V_{t & x:n}.
Proof.
  move => t x n [H0t Htn] Hxt.
  assert (H0t' : (0 < t)%N) by (apply /ltP /INR_lt => //).
  assert (Htn' : (t <= n)%N) by (apply /leP /INR_le => //).
  assert (H1t : (1 <= t)%coq_nat)
   by (rewrite (_ : 0 = 0%N) in H0t => //; apply INR_lt in H0t; lia).
  assert (Ht1n : ((t - 1)%coq_nat <= n)%coq_nat) by (apply INR_le in Htn; lia).
  assert (Hx : x < ω)
    by (apply (Rle_lt_trans _ (x+t)); [rewrite -plus_INR; apply le_INR; lia | done]).
  assert (Hxt' : (x+t)%N < ω) by rewrite plus_INR //.
  assert (Hxt'' : (x + (t - 1))%N < ω)
    by (rewrite plus_INR SSR_minus minus_INR // (_ : INR 1%N = 1) //; lra).
  assert (Hnt : 0 < (n - (t - 1))%N)
    by (rewrite !SSR_minus !minus_INR // (_ : INR 1%N = 1) //; lra).
  rewrite /res_endow_life.
  rewrite ins_endow_rec //;
          [| rewrite plus_INR SSR_minus minus_INR // (_ : INR 1%N = 1) //; lra].
  rewrite ann_due_rec //;
          [| rewrite plus_INR SSR_minus minus_INR // (_ : INR 1%N = 1) //; lra].
  rewrite (_ : (x + (t - 1) + 1)%N = (x + t)%N);
    [| rewrite addnBA // subnK // addn_gt0 // H0t'; apply /orP; auto].
  rewrite (_ : (n - (t - 1) - 1)%N = (n - t)%N); [| rewrite subnA // addnK //].
  rewrite (_ : INR (x + (t - 1))%N = x + t -1);
    [| rewrite plus_INR SSR_minus minus_INR // (_ : INR 1%N = 1) //; lra].
  lra.
Qed.

Lemma res_whole_rec : forall (t x : nat), 0 < t -> x+t < ω ->
  \V_{(t-1) & x} + \P_x - \v * \q_(x+t-1) = \v * \p_(x+t-1) * \V_{t & x}.
Proof.
  move => t x Ht Hxt.
  assert (H1t : (1 <= t)%coq_nat)
   by (rewrite (_ : 0 = 0%N) in Ht => //; apply INR_lt in Ht; lia).
  assert (Htx : t < (ω - x)%N)
    by (rewrite SSR_minus minus_INR; [lra | apply INR_le; lra]).
  assert (Hxt' : x + (t - 1)%N < ω)
    by (rewrite SSR_minus minus_INR // (_ : INR 1%N = 1) //; lra).
  assert (Hx : x < ω)
    by (apply (Rle_lt_trans _ (x+t)); [rewrite -plus_INR; apply le_INR; lia | done]).
  rewrite -!res_endow_whole //.
  rewrite -(prem_endow_whole _ _ l_fin _ (ω-x)) //;
    [| rewrite SSR_minus minus_INR; [lra | apply INR_le; lra]].
  rewrite res_endow_rec //; split; lra.
Qed.
  
End Reserve.



