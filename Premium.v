Require Import Reals Lra Lia.
From mathcomp Require Import all_ssreflect.
From Actuary Require Export Basics Interest LifeTable.
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(****************************************************************************************)

From Coquelicot Require Import Coquelicot.

(* present value of a term life insurance *)
Definition ins_term_life (i:R) (l:life) (x:nat) (n:nat) :=
  \Rsum_(0 <= k < n) (\v[i])^(k+1) * (\q[l]_{k|&x}).
Notation "\A[ i , l ]_{ x `1: n }" :=
  (ins_term_life i l x n) (at level 9, x at level 9).

(* present value of a whole life insurance *)
Definition ins_whole_life (i:R) (l:life) (l_fin : l_finite l) (x:nat) :=
  \A[i,l]_{x`1:ω[l,l_fin]-x}.
Notation "\A[ i , l , l_fin ]_ x" := (ins_whole_life i l l_fin x) (at level 9).

(* present value of a pure endowment life insurance *)
Definition ins_pure_endow_life (i:R) (l:life) (x:nat) (n:nat) := \v[i]^n * \p[l]_{n&x}.
Notation "\A[ i , l ]_{ x : n `1}" :=
  (ins_pure_endow_life i l x n) (at level 9, x at level 9).

(* present value of an endowment life insurance *)
Definition ins_endow_life (i:R) (l:life) (x:nat) (n:nat) :=
  \A[i,l]_{x`1:n} + \A[i,l]_{x:n`1}.
Notation "\A[ i , l ]_{ x : n }" := (ins_endow_life i l x n) (at level 9, x at level 9).

(* present value of a temporary life annuity immediate *)
Definition life_ann (i:R) (l:life) (x:nat) (n:nat) :=
  \Rsum_(0 <= k < n) (\v[i])^(k+1) * (\p[l]_{(k+1)&x}).
Notation "\a[ i , l ]_{ x : n }" := (life_ann i l x n) (at level 9, x at level 9).

(* future value of a temporary life annuity immediate *)
Definition life_acc (i:R) (l:life) (x:nat) (n:nat) :=
  \Rsum_(0 <= k < n) /(\A[i,l]_{(x+k+1):(n-k-1)`1}).
Notation "\s[ i , l ]_{ x : n }" := (life_acc i l x n) (at level 9, x at level 9).
                      
(* present value of a temporary life annuity due *)
Definition life_ann_due (i:R) (l:life) (x:nat) (n:nat) :=
  \Rsum_(0 <= k < n) (\v[i])^k * (\p[l]_{k&x}).
Notation "\a''[ i , l ]_{ x : n }" := (life_ann_due i l x n) (at level 9, x at level 9).

(* future value of a temporary life annuity due *)
Definition life_acc_due (i:R) (l:life) (x:nat) (n:nat) :=
  \Rsum_(0 <= k < n) /(\A[i,l]_{(x+k):(n-k)`1}).
Notation "\s''[ i , l ]_{ x : n }" := (life_acc_due i l x n) (at level 9, x at level 9).

(* present value of a whole life annuity immediate *)
Definition whole_life_ann (i:R) (l:life) (l_fin : l_finite l) (x:nat) :=
  \a[i,l]_{x:(ω[l,l_fin]-x-1)}.
Notation "\a[ i , l , l_fin ]_ x" := (whole_life_ann i l l_fin x) (at level 9).

(* present value of a whole life annuity due *)
Definition whole_life_ann_due (i:R) (l:life) (l_fin : l_finite l) (x:nat) :=
  \a''[i,l]_{x:(ω[l,l_fin]-x)}.
Notation "\a''[ i , l , l_fin ]_ x" := (whole_life_ann_due i l l_fin x) (at level 9).

(* level premium of a term life insurance *)
Definition prem_term_life (i:R) (l:life) (x:nat) (n:nat) :=
  \A[i,l]_{x`1:n} / \a''[i,l]_{x:n}.
Notation "\P[ i , l ]_{ x `1: n }" :=
  (prem_term_life i l x n) (at level 9, x at level 9).

(* level premium of a whole life insurance *)
Definition prem_whole_life (i:R) (l:life) (l_fin : l_finite l) (x:nat) :=
  \A[i,l,l_fin]_x / \a''[i,l,l_fin]_x.
Notation "\P[ i , l , l_fin ]_ x" := (prem_whole_life i l l_fin x) (at level 9).

(* level premium of a pure endowment life insurance *)
Definition prem_pure_endow_life (i:R) (l:life) (x:nat) (n:nat) :=
  \A[i,l]_{x:n`1} / \a''[i,l]_{x:n}.
Notation "\P[ i , l ]_{ x : n `1}" :=
  (prem_pure_endow_life i l x n) (at level 9, x at level 9).

(* level premium of an endowment life insurance *)
Definition prem_endow_life (i:R) (l:life) (x:nat) (n:nat) :=
  \A[i,l]_{x:n} / \a''[i,l]_{x:n}.
Notation "\P[ i , l ]_{ x : n }" :=
  (prem_endow_life i l x n) (at level 9, x at level 9).

(****************************************************************************************)

Section Premium.

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

Lemma ins_term_0_0 : forall x:nat, \A_{x`1:0} = 0.
Proof.
  move => x.
  rewrite /ins_term_life.
  rewrite big_geq //.
Qed.

Lemma ins_term_whole : forall (x n : nat), x < ω -> n >= ω-x -> \A_{x`1:n} = \A_x.
Proof.
  move => x n Hx Hn.
  rewrite /ins_whole_life /ins_term_life.
  assert (Hx' : (x < ω)%coq_nat) by apply INR_lt => //.
  assert (Hn' : (ω-x <= n)%N).
  { apply /leP /INR_le.
    rewrite !SSR_minus !minus_INR; try lia; lra. }
  rewrite /whole_life_ann /life_ann.
  rewrite (big_cat_nat _ _ _ _ Hn') //=.
  under [\big[_/_]_(ω-x <= _ < n) _]eq_big_nat => k Hk.
  { rewrite (q_defer_old_0 _ _ k 1 x).
    2:{ move: Hk => /andP [Hk_lb Hkub].
        move: Hk_lb => /leP /le_INR.
        rewrite !SSR_minus !minus_INR; try lia; lra. }
    rewrite Rmult_0_r.
    over. }
  rewrite big1_eq Rplus_0_r //.
Qed.

Lemma ins_term_rec : forall (x n : nat), x < ω -> 0 < n ->
  \A_{x`1:n} = \v * \q_x + \v * \p_x * \A_{(x+1)`1:(n-1)}.
Proof.
  move => x n Hx'.
  assert (Hx : (x <= ω)%coq_nat) by (apply INR_le; lra).
  wlog : n / n <= ω-x.
  { move => Hspec.
    case: (Rle_lt_dec n (ω-x)); [apply Hspec |].
    move => Hnlong Hnpos.
    assert (Hnlong' : (ω-x <= n)%N)
      by (rewrite SSR_minus; apply /leP /INR_le /Rlt_le; rewrite minus_INR //).
    assert (Hxyng : (0 <= ω-x)%N) by done.
    rewrite /ins_term_life.
    rewrite (big_cat_nat _ _ _ Hxyng) //=.
    rewrite Rplus_comm.
    under eq_big_nat => j Hj.
    { rewrite (q_defer_old_0 _ _ j 1).
      2:{ move: Hj => /andP [Hj_lb Hj_ub].
          move: Hj_lb => /leP /le_INR.
          rewrite SSR_minus minus_INR; [lra | move: Hx' => /INR_lt; lia]. }
      rewrite Rmult_0_r.
      over. }
    assert (Hx1yng : (0 <= ω-(x+1))%N) by done.
    apply esym.
    rewrite (big_cat_nat _ _ _ Hx1yng) /=; [| rewrite subnDA; apply (leq_sub2r 1) => //].
    rewrite (Rplus_comm (\big[Rplus/0]_(_ <= _ < _) _)).
    under eq_big_nat => j Hj.
    { rewrite (q_defer_old_0 _ _ j 1).
      2:{ move: Hj => /andP [Hj_lb Hj_ub].
          move: Hj_lb => /leP /le_INR.
          rewrite SSR_minus minus_INR;
            [lra | move: Hx' => /INR_lt; rewrite /lt -Nat.add_1_r //]. }
      rewrite Rmult_0_r.
      over. }
    rewrite !big1_eq !Rplus_0_l.
    rewrite -/(ins_term_life _ _ _ (ω-x)) -/(ins_term_life _ _ _ (ω-(x+1))).
    rewrite Hspec; try (rewrite SSR_minus minus_INR //; lra).
    rewrite subnDA //. }
  move => Hn_ub Hn_lb.
  rewrite (_ : 0 = 0%N) in Hn_lb * => //.
  apply INR_lt in Hn_lb.
  rewrite -minus_INR in Hn_ub; [| apply Hx].
  apply INR_le in Hn_ub.
  apply le_lt_or_eq in Hn_lb.
  destruct Hn_lb as [Hlt | Heq].
  - rewrite /ins_term_life.
    rewrite {1}(S_pred n 0); [| lia].
    rewrite big_nat_recl; [| apply /leP /Nat.lt_le_pred; lia].
    rewrite Rplus_0_l Rpower_1; [| apply /v_pos /i_pos].
    under eq_big_seq => k Hk.
    rewrite /index_iota mem_iota in Hk.
    move: Hk => /andP [Hk_lb Hk_ub].
    move: Hk_ub => /ltP Hk_ub.
    rewrite add0n subn0 in Hk_ub.
    assert (Hlnot0 : forall j:nat, (j < n.-1)%coq_nat -> \l_(x+j.+1) <> 0).
    { move => j Hj.
      apply pos_neq0.
      rewrite -plus_INR.
      apply /(l_x_pos _ l_fin) /lt_INR.
      rewrite Nat.add_comm.
      rewrite -(Nat.sub_add x ω); [| apply /Nat.lt_le_incl /lt_O_minus_lt; lia].
      apply (plus_lt_compat_r _ _ x).
      apply (Nat.le_lt_trans _ _ n) in Hj; [| apply Nat.lt_pred_l; lia].
      apply (Nat.lt_le_trans _ n); lia. }
    { rewrite q_defer_pq; [| apply (Hlnot0 k) => //].
      rewrite -Nat.add_1_r Nat.add_comm plus_INR.
      rewrite (p_mult _ 1 k x); [| apply (Hlnot0 0%N); lia].
      rewrite Rpower_plus Rpower_1; [| apply /v_pos /i_pos].
      rewrite -Rplus_assoc (Rplus_comm 1) -2!Rmult_assoc.
      rewrite (Rmult_assoc _ \v ) (Rmult_comm (\v ^ _)) 2!Rmult_assoc.
      rewrite -q_defer_pq;
        [| rewrite Rplus_assoc (Rplus_comm 1) -(plus_INR _ 1) Nat.add_1_r;
           apply (Hlnot0 k) => //].
      rewrite -(plus_INR x 1).
      over. }
    rewrite big_distrr /=.
    rewrite pred_of_minus !SSR_minus //.
  - rewrite /ins_term_life.
    rewrite -Heq.
    rewrite big_nat1.
    rewrite Rplus_0_l Rpower_1; [| apply /v_pos /i_pos].
    rewrite big_geq //.
    rewrite Rmult_0_r Rplus_0_r //.
Qed.

Lemma ins_term_pure_endow : forall (t x n : nat), x+t < ω -> t <= n ->
  \A_{x`1:n} = \A_{x`1:t} + \A_{x:t`1} * \A_{(x+t)`1:(n-t)}.
Proof.
  move => t x n Hxt Htn.
  assert (Htn' : (t <= n)%N) by apply /leP /INR_le => //.
  rewrite /(ins_pure_endow_life) {-1}/(ins_term_life).
  rewrite big_distrr /=.
  under [\big[Rplus/0]_(0 <= i0 < n - t) _]eq_big_nat => k Hk.
  { rewrite -Rmult_assoc (Rmult_assoc (\v^t)) (Rmult_comm \p_{_&_}) -Rmult_assoc.
    rewrite -Rpower_plus Rmult_assoc.
    rewrite plus_INR.
    rewrite q_defer_p_q_defer;
      [| rewrite -plus_INR; apply /pos_neq0 /(l_x_pos _ l_fin); rewrite plus_INR //].
    rewrite -Rplus_assoc (Rplus_comm t k).
    rewrite (_ : k + t = INR (k + t)%N); [| rewrite plus_INR //].
    over. }
  rewrite /=.
  rewrite -[\big[_/_]_(0<=_<n-t)_]
             (big_addn _ _ _ xpredT (fun j:nat => (\v^(j+1) * \q_{j|&x}))).
  rewrite add0n.
  rewrite -big_cat_nat //.
Qed.
  
Lemma ins_whole_rec : forall x:nat, x < ω -> \A_x = \v * \q_x + \v * \p_x * \A_(x+1).
Proof.
  move => x Hx.
  rewrite /ins_whole_life.
  rewrite ins_term_rec //; [| rewrite SSR_minus minus_INR; [lra | apply INR_le; lra]].
  rewrite subnDA //.
Qed.

Lemma ins_pure_endow_0_1 : forall x:nat, x < ω -> \A_{x:0`1} = 1.
Proof.
  move => x Hx.
  rewrite /ins_pure_endow_life.
  rewrite Rpower_O; [| apply /v_pos /i_pos].
  rewrite p_0_1; lra.
Qed.

Lemma ins_pure_endow_old_0 : forall (x n : nat), x < ω -> n >= ω-x -> \A_{x:n`1} = 0.
Proof.
  move => x n Hx Hn.
  rewrite /ins_pure_endow_life.
  rewrite p_old_0; [| lra].
  rewrite Rmult_0_r //.
Qed.

Lemma ins_pure_endow_pos : forall (x n : nat), x+n < ω -> \A_{x:n`1} > 0.
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

Lemma ins_endow_whole : forall (x n : nat), x < ω -> n >= ω-x -> \A_{x:n} = \A_x.
Proof.
  move => x n Hx Hn.
  rewrite /ins_endow_life.
  rewrite ins_term_whole //.
  rewrite ins_pure_endow_old_0; lra.
Qed.

Lemma ins_pure_endow_rec : forall (x n :nat), x+1 < ω -> 0 < n ->
  \A_{x:n`1} = \v * \p_x * \A_{(x+1):(n-1)`1}.
Proof.
  move => x n Hx Hn.
  rewrite (_ : 0 = 0%N) in Hn => //.
  apply INR_lt in Hn.
  rewrite /lt in Hn.
  case: (le_lt_or_eq _ _ Hn) => [Hlt1n | Heq1n].
  - rewrite /ins_pure_endow_life.
    rewrite -Rmult_assoc (Rmult_assoc \v) (Rmult_comm \p_x) -Rmult_assoc.
    rewrite -{2}(Rpower_1 \v); [| apply /v_pos /i_pos].
    rewrite -Rpower_plus.
    assert (H1n1 : 1 + (n-1)%N = n)
      by (rewrite {1}(_ : 1 = 1%N) //; rewrite (Rplus_comm 1%N) -plus_INR Nat.sub_add //).
    rewrite H1n1.
    rewrite plus_INR (Rmult_assoc _ \p_{1 & x}).
    rewrite -(p_mult _ 1 (n-1)%N x).
    + rewrite H1n1 //.
    + apply pos_neq0.
      rewrite (_ : 1 = 1%N) // -plus_INR.
      apply (l_x_pos _ l_fin).
      rewrite plus_INR //.
  - rewrite -Heq1n.
    rewrite SSR_minus Nat.sub_diag.
    rewrite /ins_pure_endow_life.
    rewrite p_0_1; [| rewrite plus_INR //].
    rewrite Rpower_1; [| apply /v_pos /i_pos].
    rewrite Rpower_O; [| apply /v_pos /i_pos].
    rewrite !Rmult_1_r //.
Qed.

Lemma ins_pure_endow_mult : forall (t x n : nat), x+t < ω -> t <= n ->
  \A_{x:n`1} = \A_{x:t`1} * \A_{(x+t):(n-t)`1}.
Proof.
  move => t x n Hxt Htn.
  rewrite {-1}/ins_pure_endow_life.
  rewrite plus_INR SSR_minus minus_INR; last by apply INR_le.
  rewrite -Rmult_assoc (Rmult_assoc (\v^t)) (Rmult_comm \p_{_&_}) -Rmult_assoc.
  rewrite -Rpower_plus Rplus_minus.
  rewrite Rmult_assoc -p_mult;
    [| rewrite -plus_INR; apply /pos_neq0 /(l_x_pos _ l_fin); rewrite plus_INR //].
  rewrite Rplus_minus /ins_pure_endow_life //.
Qed.

Lemma ins_pure_endow_rec' : forall (x n : nat), x+n < ω ->
  \A_{x:(n+1)`1} = \v * \p_(x+n) * \A_{x:n`1}.
Proof.
  move => x n Hxn.
  rewrite (ins_pure_endow_mult n x (n+1)%N) //;
          [| rewrite plus_INR (_ : INR 1%N = 1) //; lra].
  rewrite (addnC n 1%N) addnK.
  rewrite {2}/ins_pure_endow_life (_ : INR 1%N = 1) // plus_INR
          Rpower_1; [| apply /v_pos /i_pos]; lra.
Qed.

Lemma ins_endow_0_1 : forall x:nat, x < ω -> \A_{x:0} = 1.
Proof.
  move => x Hx.
  rewrite /ins_endow_life.
  rewrite ins_term_0_0 ins_pure_endow_0_1; lra.
Qed.

Lemma ins_endow_rec : forall (x n : nat), x+1 < ω -> 0 < n ->
  \A_{x:n} = \v * \q_x + \v * \p_x * \A_{(x+1):(n-1)}.
Proof.
  move => x n Hx Hn.
  rewrite /ins_endow_life.
  rewrite ins_term_rec //.
  2:{ apply (Rlt_trans _ (x+1)) => //.
      rewrite -{1}(Rplus_0_r x).
      apply Rplus_lt_compat_l; lra. }
  rewrite ins_pure_endow_rec //.
  rewrite Rmult_plus_distr_l Rplus_assoc //.
Qed.

Lemma ins_endow_pure_endow : forall (t x n : nat), x+t < ω -> t <= n ->
  \A_{x:n} = \A_{x`1:t} + \A_{x:t`1} * \A_{(x+t):(n-t)}.
Proof.
  move => t x n Hxt Htn.
  rewrite /ins_endow_life.
  rewrite (ins_term_pure_endow t) //.
  rewrite (ins_pure_endow_mult t x n) //; lra.
Qed.

Lemma ann_due_0_0 : forall x:nat, \a''_{x:0} = 0.
Proof.
  move => x.
  rewrite /life_ann_due.
  rewrite big_geq //.
Qed.

Lemma ann_due_ge1 : forall (x n : nat), x < ω -> n > 0 -> \a''_{x:n} >= 1.
Proof.
  move => x n Hx Hn.
  assert (Hn' : (n > 0)%coq_nat) by (apply INR_lt => //).
  rewrite /life_ann_due.
  rewrite (S_pred n 0) //.
  rewrite big_nat_recl; [| apply /leP; lia].
  rewrite Rpower_O; [| apply /v_pos /i_pos]; rewrite p_0_1 // Rmult_1_r.
  rewrite -{2}(Rplus_0_r 1).
  apply (Rplus_ge_compat 1 1 _ 0); try lra.
  apply Rsum_nonneg => k Hk.
  rewrite -(Rmult_0_r (\v^k.+1)); apply (Rmult_ge_compat_l (\v^k.+1));
    [apply /Rgt_ge /exp_pos | apply (p_nonneg _ l_fin) => //].
Qed.

Lemma ann_temp_whole : forall (x n : nat), x < ω -> n >= ω-x-1 -> \a_{x:n} = \a_x.
Proof.
  move => x n Hx Hn.
  assert (Hx' : (x < ω)%coq_nat) by apply INR_lt => //.
  assert (Hn' : (ω-x-1 <= n)%N).
  { apply /leP /INR_le.
    rewrite !SSR_minus !minus_INR; try lia.
    rewrite (_ : INR 1%N = 1) //; try lra. }
  rewrite /whole_life_ann /life_ann.
  rewrite (big_cat_nat _ _ _ _ Hn') //=.
  under [\big[_/_]_(ω-x-1 <= i0 < n) _]eq_big_nat => k Hk.
  { rewrite (_ : 1 = 1%N) // -plus_INR p_old_0.
    2:{ move: Hk => /andP [Hk_lb Hkub].
        move: Hk_lb => /leP /le_INR.
        rewrite !SSR_minus !minus_INR; try lia; rewrite plus_INR; lra. }
    rewrite Rmult_0_r.
    over. }
  rewrite big1_eq Rplus_0_r //.
Qed.

Lemma ann_due_temp_whole : forall (x n : nat), x < ω -> n >= ω-x -> \a''_{x:n} = \a''_x.
Proof.
  move => x n Hx Hn.
  assert (Hx' : (x < ω)%coq_nat) by apply INR_lt => //.
  assert (Hn' : (ω-x <= n)%N).
  { apply /leP /INR_le.
    rewrite !SSR_minus !minus_INR; try lia; lra. }
  rewrite /whole_life_ann_due /life_ann_due.
  rewrite (big_cat_nat _ _ _ _ Hn') //=.
  under [\big[_/_]_(ω-x <= _ < n) _]eq_big_nat => k Hk.
  { rewrite p_old_0.
    2:{ move: Hk => /andP [Hk_lb Hkub].
        move: Hk_lb => /leP /le_INR.
        rewrite !SSR_minus !minus_INR; try lia; lra. }
    rewrite Rmult_0_r.
    over. }
  rewrite big1_eq Rplus_0_r //.
Qed.

Lemma ann_due_sum_pure_endow : forall (x n : nat), \a''_{x:n} = \Rsum_(0 <= k < n) \A_{x:k`1}.
Proof.
  move => x n.
  under eq_big_nat do rewrite /ins_pure_endow_life.
  rewrite /life_ann_due //.
Qed.

Lemma ann_imm_due : forall (x n : nat), x+1 < ω -> \a_{x:n} = \v * \p_x * \a''_{(x+1):n}.
Proof.
  move => x n Hx.
  rewrite /life_ann /life_ann_due /=.
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

Lemma ann_due_1_imm : forall (x n : nat), x < ω -> n > 0 -> \a''_{x:n} = 1 + \a_{x:(n-1)}. 
Proof.
  move => x n Hx Hn.
  rewrite /life_ann /life_ann_due.
  rewrite {1}(S_pred n 0); [| apply INR_lt => //].
  rewrite big_nat_recl //.
  rewrite Rpower_O; [| apply /v_pos /i_pos]; rewrite p_0_1 // Rmult_1_r.
  rewrite pred_of_minus -SSR_minus.
    by under eq_big_nat => k Hk do rewrite S_INR.
Qed.

Lemma ann_imm_due_1_pure_endow : forall (x n : nat), x < ω ->
  \a_{x:n} = \a''_{x:n} - 1 + \A_{x:n`1}.
Proof.
  move => x n Hx.
  rewrite /life_ann /life_ann_due /ins_pure_endow_life.
  case: (zerop n) => [Hn0 | Hnpos].
  - rewrite !big_geq; try (rewrite Hn0 //).
    rewrite Rpower_O; [| apply /v_pos /i_pos]; rewrite p_0_1; lra.
  - rewrite {2}(S_pred n 0) //.
    rewrite big_nat_recl; [| apply /leP; lia].
    rewrite Rpower_O; [| apply /v_pos /i_pos]; rewrite p_0_1 // Rmult_1_r.
    rewrite (Rplus_comm 1) Ropp_r_simpl_l.
    rewrite {3 4}(S_pred n 0) // -big_nat_recr; [| apply /leP; lia].
    rewrite -(S_pred n 0) //.
      by under eq_big_nat => k Hk do [rewrite (_ : 1 = 1%N) // -plus_INR Nat.add_1_r].
Qed.

Lemma ann_due_rec : forall (x n : nat), x+1 < ω -> n > 0 ->
  \a''_{x:n} = 1 + \v * \p_x * \a''_{(x+1):(n-1)}.
Proof.
  move => x n Hx Hn.
  rewrite ann_due_1_imm //; [| eapply Rlt_trans; [| apply Hx]; lra].
  rewrite ann_imm_due //.
Qed.

Lemma ann_due_pure_endow : forall (t x n : nat), x+t < ω -> t <= n ->
  \a''_{x:n} = \a''_{x:t} + \A_{x:t`1} * \a''_{(x+t):(n-t)}.
Proof.
  move => t x n Hxt Htn.
  rewrite (ann_due_sum_pure_endow x t) (ann_due_sum_pure_endow (x+t) (n-t)).
  rewrite big_distrr /=.
  assert (Heq : forall k:nat, (0 <= k < n - t)%N ->
                        (\A_{ x : t`1} * \A_{ (x + t) : k`1}) = (\A_{x:(k+t)%N`1})).
  { move => k Hk.
    rewrite {1}(_ : (k = t+k-t)%coq_nat); [| rewrite (_ : (t+k)%N = (t+k)%coq_nat) //; lia].
    rewrite (addnC k t).
    rewrite -ins_pure_endow_mult //;
      move: (Nat.le_0_l k) => /le_INR; rewrite (_ : INR 0%N = 0) // plus_INR; lra. }
  rewrite (eq_big_nat 0 Rplus Heq).
  rewrite -(big_addn _ _ _ xpredT) add0n.
  rewrite -big_cat_nat; [| apply /leP; lia | apply /leP /INR_le => //].
    by rewrite /life_ann_due.
Qed.    
  
Lemma ins_endow_ann_due : forall (x n : nat), x < ω -> \A_{x:n} = 1 - \d * \a''_{x:n}.
Proof.
  move => x n Hx.
  assert (Hx' : (x < ω)%coq_nat) by apply INR_lt => //.
  wlog : n / n <= ω-x.
  { move => Hspec.
    case: (Rle_lt_dec n (ω-x)); [apply Hspec => // |].
    move => Hn_lb.
    rewrite /ins_endow_life.
    rewrite ins_term_whole; try lra.
    rewrite ins_pure_endow_old_0; try lra.
    rewrite -(ins_pure_endow_old_0 x (ω-x)) //;
      [| rewrite SSR_minus minus_INR; [lra | lia]].
    rewrite ann_due_temp_whole; try lra.
    rewrite /ins_whole_life /whole_life_ann_due.
    rewrite -/(ins_endow_life _ _  x (ω-x)).
    apply Hspec; rewrite SSR_minus minus_INR; [lra | lia]. }
  move => Hn_ub.
  assert (Hn_ub' : (n <= (ω-x)%coq_nat)%coq_nat)
    by (apply INR_le; rewrite minus_INR; [lra | lia]).
  rewrite /ins_endow_life /ins_term_life.
  under eq_big_nat => k Hk.
  { move: Hk => /andP [Hk_lb Hk_ub].
    move: Hk_ub => /ltP => Hk_ub.
    rewrite q_defer_pq;
      [| rewrite -plus_INR; apply /pos_neq0 /(l_x_pos _ l_fin) /lt_INR; lia].
    rewrite (_ : \q_(x+k) = 1 - \p_(x+k)).
    2:{ rewrite -{2}(p_q_1 l 1 (x+k));
        [| rewrite -plus_INR; apply /pos_neq0 /(l_x_pos _ l_fin) /lt_INR; lia].
        rewrite (Rplus_comm _ \q_(x+k)) Ropp_r_simpl_l //. }
    rewrite !Rmult_plus_distr_l Rmult_1_r.
    rewrite {1}Rpower_plus Rpower_1; [| apply /v_pos /i_pos => //].
    rewrite (Rmult_comm _ \v) Rmult_assoc.
    over. }
  rewrite big_split /=.
  under [\big[_/_]_(0<=i0<n) (\v^(i0+1) * _)]eq_big_nat => k Hk.
  { move: Hk => /andP [Hk_lb Hk_ub].
    move: Hk_ub => /ltP => Hk_ub.
    rewrite -!Ropp_mult_distr_r.
    rewrite -p_mult;
      [| rewrite -plus_INR; apply /pos_neq0 /(l_x_pos _ l_fin) /lt_INR; lia].
    rewrite -(Rmult_1_l (\v^(k+1) * _)) Ropp_mult_distr_l.
    over. }
  rewrite -!big_distrr /=; rewrite -Ropp_mult_distr_l Rmult_1_l /=.
  rewrite -/(life_ann_due _ _  x n) -/(life_ann _ _ x n).
  rewrite ann_imm_due_1_pure_endow //.
  rewrite Ropp_plus_distr Ropp_minus_distr.
  rewrite /Rminus -!Rplus_assoc (Rplus_comm _ 1) (Rplus_assoc 1).
  rewrite (_ : -\a''_{x:n} = (-1) * \a''_{x:n}); try lra.
  rewrite -Rmult_plus_distr_r.
  rewrite (_ : \v + -1 = -\d).
  2:{ rewrite /v_pres. rewrite (i_nom_1 i_pos). rewrite -{1}(Rdiv_1 (\i^{1})).
      rewrite -d_nom_i_nom //; [| rewrite (_ : INR 1%N = 1) //; lra].
      rewrite /Rminus (Rplus_comm 1) Rplus_assoc Rplus_opp_r Rplus_0_r Rdiv_1.
      rewrite -i_nom_1 //. }
  rewrite Rplus_assoc Rplus_opp_l Rplus_0_r Ropp_mult_distr_l //.
Qed.

Lemma ins_whole_ann_due : forall x:nat, x < ω -> \A_x = 1 - \d * \a''_x.
Proof.
  move => x Hx.
  assert (Hx' : (x < ω)%coq_nat) by apply INR_lt => //.
  rewrite /ins_whole_life /whole_life_ann_due.
  rewrite -ins_endow_ann_due //.
  rewrite /ins_endow_life.
  rewrite ins_pure_endow_old_0; try lra; rewrite SSR_minus minus_INR; [lra | lia].
Qed.

Lemma ann_pure_endow_acc : forall (x n : nat), x+n < ω ->
  \a_{x:n} = \A_{x:n`1} * \s_{x:n}.
Proof.
  move => x n Hxn.
  rewrite /life_acc.
  rewrite big_distrr /=.
  under eq_big_nat => k Hk.
  { move: Hk => /andP; case => /leP => Hk_lb /ltP => Hk_ub.
    rewrite !/ins_pure_endow_life.
    rewrite (_ : \p_{n&x} = \p_{(k+1)&x} * \p_{(n-k-1)&(x+k+1)}).
    2:{ rewrite Rplus_assoc (_ : n-k-1 = n-(k+1)); try lra.
        rewrite -p_mult.
        - rewrite Rplus_comm Rplus_assoc Rplus_opp_l Rplus_0_r //.
        - rewrite (_ : 1 = 1%N) // -!plus_INR; apply /pos_neq0 /(l_x_pos _ l_fin) /lt_INR.
          move: Hxn; rewrite -plus_INR => /INR_lt; lia. }
    assert (Hp : \p_{(n-k-1)&(x+k+1)} <> 0).
    { rewrite Rplus_assoc (_ : n-k-1 = n-(k+1)); try lra.
      rewrite /survive.
      apply /pos_neq0 /Rmult_gt_0_compat.
      - rewrite /Rminus (Rplus_comm n) -Rplus_assoc (Rplus_assoc x) Rplus_opp_r Rplus_0_r.
        rewrite -plus_INR; apply (l_x_pos _ l_fin); rewrite plus_INR //.
      - rewrite (_ : 1 = 1%N) // -!plus_INR;
          apply /Rinv_0_lt_compat /(l_x_pos _ l_fin) /lt_INR.
        move: Hxn; rewrite -plus_INR => /INR_lt; lia. }
    rewrite !plus_INR !SSR_minus !minus_INR; try lia.
    rewrite (_ : INR 1%N = 1) //.
    rewrite (Rmult_comm (\v ^ (n-k-1))).
    rewrite Rinv_mult_distr //; [| apply /pos_neq0 /exp_pos].
    rewrite -2!Rmult_assoc (Rmult_assoc _ \p_{_&_}) Rinv_r // Rmult_1_r.
    rewrite Rmult_assoc (Rmult_comm \p_{_&_}) -Rmult_assoc -Rpower_Ropp -Rpower_plus.
    rewrite (_ : n-k-1 = n-(k+1)); try lra.
    rewrite Ropp_plus_distr -Rplus_assoc Rplus_opp_r Rplus_0_l Ropp_involutive.
    over. }
    by [].
Qed.  

Lemma ann_due_pure_endow_acc_due : forall (x n : nat), x+n < ω ->
  \a''_{x:n} = \A_{x:n`1} * \s''_{x:n}.
Proof.
  move => x n Hxn.
  rewrite /life_acc_due.
  rewrite big_distrr /=.
  under eq_big_nat => k Hk.
  { move: Hk => /andP; case => /leP => Hk_lb /ltP => Hk_ub.
    rewrite !/ins_pure_endow_life.
    rewrite (_ : \p_{n&x} = \p_{k&x} * \p_{(n-k)&(x+k)}).
    2:{ rewrite -p_mult.
        - rewrite Rplus_comm Rplus_assoc Rplus_opp_l Rplus_0_r //.
        - rewrite -plus_INR; apply /pos_neq0 /(l_x_pos _ l_fin); rewrite plus_INR.
          apply lt_INR in Hk_ub; lra. }
    assert (Hp : \p_{(n-k)&(x+k)} <> 0).
    { rewrite /survive.
      apply /pos_neq0 /Rmult_gt_0_compat.
      - rewrite /Rminus (Rplus_comm n) -Rplus_assoc (Rplus_assoc x) Rplus_opp_r Rplus_0_r.
        rewrite -plus_INR; apply (l_x_pos _ l_fin); rewrite plus_INR //.
      - rewrite -plus_INR; apply /Rinv_0_lt_compat /(l_x_pos _ l_fin).
        rewrite plus_INR; move: Hk_ub => /lt_INR; lra. }
    rewrite plus_INR SSR_minus minus_INR; [| lia].
    rewrite (Rmult_comm (\v ^ (n-k))).
    rewrite Rinv_mult_distr //; [| apply /pos_neq0 /exp_pos].
    rewrite -2!Rmult_assoc (Rmult_assoc _ \p_{_&_}) Rinv_r // Rmult_1_r.
    rewrite Rmult_assoc (Rmult_comm \p_{_&_}) -Rmult_assoc -Rpower_Ropp -Rpower_plus
      Ropp_plus_distr -Rplus_assoc Rplus_opp_r Rplus_0_l Ropp_involutive.
    over. }
    by [].
Qed.

Lemma acc_imm_due : forall (x n : nat), x+1+n < ω -> \s_{x:n} = \v * \p_(x+n) * \s''_{(x+1):n}.
Proof.
  move => x n Hxn.
  assert (Hvp : \v * \p_ (x + n) <> 0).
  { apply /pos_neq0 /Rmult_gt_0_compat; [apply /v_pos /i_pos |].
    apply Rmult_gt_0_compat.
    + rewrite (_ : 1 = 1%N) // -!plus_INR; apply (l_x_pos _ l_fin);
        rewrite !plus_INR (_ : INR 1%N = 1) //; lra.
    + apply Rinv_0_lt_compat; rewrite -plus_INR; apply (l_x_pos _ l_fin);
        rewrite plus_INR; lra. }
  rewrite /life_acc_due.
  rewrite big_distrr /=.
  under eq_big_nat => k Hk.
  { move: Hk => /andP; case => /leP Hk_lb /ltP Hk_ub.
    assert (Hnk : (0 < n - k)%coq_nat) by (rewrite SSR_minus; lia).
    assert (Heqxn : (x + 1 + k)%N + (n - k - 1)%coq_nat = x + n)
      by (rewrite !plus_INR SSR_minus !minus_INR //; [lra | lia]).
    rewrite (S_pred (n-k) 0) // -(Nat.add_1_r (n-k).-1) pred_of_minus.
    rewrite ins_pure_endow_rec'; [| rewrite Heqxn; lra].
    rewrite Heqxn.
    rewrite /Rdiv Rinv_mult_distr //;
            [| apply /pos_neq0 /ins_pure_endow_pos; rewrite Heqxn; lra].
    rewrite -Rmult_assoc Rinv_r // Rmult_1_l.
    rewrite -addnA (addnC 1%N) addnA -SSR_minus.
    over. }
    by [].
Qed.

Lemma acc_imm_due_1 : forall (x n : nat), x+n < ω -> n > 0 -> \s_{x:n} = \s''_{(x+1):(n-1)} + 1.
Proof.
  move => x n Hxn Hn.
  assert (Hn' : (0 < n)%N) by ( apply /ltP /INR_lt; rewrite (_ : INR 0%N = 0) //).
  assert (Hn'' : (0 <= n - 1)%N) by (apply /leP; lia).
  assert (Hnn : (n <= n)%N) by (apply /leP; lia).
  assert (Hxn' : (x + (n - 1) + 1)%N < ω)
    by (rewrite addnBA // subnK;
      [rewrite plus_INR // | apply /ltP; move: Hn' => /ltP; apply Nat.add_pos_r]).
  rewrite /life_acc.
  rewrite {1}(_ : n = (n-1).+1);
    [| rewrite SSR_minus -pred_of_minus -(S_pred _ 0) //;
         apply INR_lt; rewrite (_ : INR 0%N = 0) //].
  rewrite big_nat_recr //=.
  rewrite subnA // !subnn.
  rewrite ins_pure_endow_0_1 // Rinv_1.
  under eq_big_nat => k Hk do rewrite -addnA -subnDA (addnC k) addnA subnDA.
  rewrite /life_acc_due //.
Qed.

Lemma acc_due_pure_endow : forall (x n : nat), x+n < ω -> n > 0 ->
  \s''_{x:n} = /(\A_{x:n`1}) + \s''_{(x+1):(n-1)}.
Proof.
  move => x n Hxn Hn.
  rewrite /life_acc_due.
  rewrite {1}(_ : n = (n-1).+1);
    [| rewrite SSR_minus -pred_of_minus -(S_pred _ 0) //;
         apply INR_lt; rewrite (_ : INR 0%N = 0) //].
  rewrite big_nat_recl //=.
  rewrite addn0 subn0.
  by under eq_big_nat => k _ do
      (rewrite -Nat.add_1_r (_ : (k+1)%coq_nat = (k+1)%N) // (addnC k) addnA subnDA).
Qed.

Lemma acc_imm_due_pure_endow_1 : forall (x n : nat), x+n < ω -> n > 0 ->
  \s_{x:n} = \s''_{x:n} - /(\A_{x:n`1}) + 1.
Proof.
  move => x n Hxn Hn.
  rewrite acc_imm_due_1 //.
  rewrite (acc_due_pure_endow x n); lra.
Qed.  

Lemma prem_endow_term : forall (x n : nat), \P_{x:n} = \P_{x`1:n} + \P_{x:n`1}.
Proof.
  move => x n.
  rewrite /prem_endow_life /prem_term_life /prem_pure_endow_life /ins_endow_life; lra.
Qed.

Lemma prem_term_whole : forall (x n : nat), x < ω -> n >= ω-x -> \P_{x`1:n} = \P_x.
Proof.
  move => x n Hx Hn.
  rewrite /prem_term_life.
  rewrite ins_term_whole //.
  rewrite ann_due_temp_whole //.
Qed.

Lemma prem_pure_endow_old_0 : forall (x n : nat), x < ω -> n >= ω-x -> \P_{x:n`1} = 0.
Proof.
  move => x n Hx Hn.
  rewrite /prem_pure_endow_life.
  rewrite ins_pure_endow_old_0; lra.
Qed.

Lemma prem_endow_whole : forall (x n : nat), x < ω -> n >= ω-x -> \P_{x:n} = \P_x.
Proof.
  move => x n Hx Hn.
  rewrite prem_endow_term prem_term_whole // prem_pure_endow_old_0 //; lra.
Qed.

Lemma prem_endow_ann_due_d : forall (x n : nat), x < ω -> n > 0 -> \P_{x:n} = /(\a''_{x:n}) - \d.
Proof.
  move => x n Hx Hn.
  rewrite /prem_endow_life.
  rewrite ins_endow_ann_due //.
  rewrite RIneq.Rdiv_minus_distr.
  rewrite /Rdiv Rinv_r_simpl_l;
    [| apply pos_neq0; eapply Rge_gt_trans; [ apply ann_due_ge1 |]; try lra].
  rewrite Rmult_1_l //.
Qed.

Lemma prem_whole_ann_due_d : forall x:nat, x < ω -> \P_x = /(\a''_x) - \d.
Proof.
  move => x Hx.
  assert (Hx' : (x < ω)%coq_nat) by apply INR_lt => //.
  rewrite -(prem_endow_whole x (ω-x)) //; [| rewrite SSR_minus minus_INR; [lra | lia]].
  rewrite prem_endow_ann_due_d //; rewrite SSR_minus minus_INR; [lra | lia].
Qed.

Lemma acc_due_plus_ann_due : forall (t x n : nat), x+t < ω -> t <= n ->
    (\s''_{x:t} + \a''_{(x+t):(n-t)}) * \A_{x:t`1} = \a''_{x:n}.
Proof.
  move => t x n Hxt Htn.
  rewrite Rmult_plus_distr_r.
  rewrite /life_acc_due.
  rewrite big_distrl /=.
  under eq_big_nat => k Hk.
  { move: Hk => /andP; case => /leP Hle0k /ltP Hltkt.
    rewrite (ins_pure_endow_mult k x t); try apply lt_INR in Hltkt; try lra.
    rewrite Rmult_comm /Rdiv Rmult_assoc Rinv_r.
    2:{ apply /pos_neq0 /ins_pure_endow_pos.
        rewrite plus_INR SSR_minus minus_INR; [lra | apply INR_le; lra]. }
    rewrite Rmult_1_r.
    over. }
  rewrite -ann_due_sum_pure_endow.
  rewrite (ann_due_pure_endow t x n) //; lra.
Qed.

End Premium.
