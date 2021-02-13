Require Import Reals Lra Lia.
From mathcomp Require Import all_ssreflect.
From Actuary Require Export Basics.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(****************************************************************************************)

From Coquelicot Require Import Coquelicot.

(* interest rate *)
(* The interest rate "i" is supposed to be positive. *)
Notation "\i[ i ]" := i (at level 9).

(* nominal interest rate *)
Definition i_nom (i:R) (m:nat) := m * ((1+i)^(/m) - 1).
Notation "\i[ i ]^{ m }" := (i_nom i m) (at level 9).

(* discount rate *)
Definition d_nom (i:R) (m:nat) := (i_nom i m) / (1 + (i_nom i m)/m).
Notation "\d[ i ]^{ m }" := (d_nom i m) (at level 9).
Notation "\d[ i ]" := (\d[i]^{1}) (at level 9).

(* force of interest *)
Definition i_force (i:R) := ln (1+i).
Notation "δ[ i ]" := (i_force i) (at level 9).

(* present value factor *)
Definition v_pres (i:R) := /(1+i).
Notation "\v[ i ]" := (v_pres i) (at level 9).

(* present value of an immediate annuity *)
Definition ann (i:R) (m n : nat) := \Rsum_(0 <= k < n*m) (1 + (\i[i]^{m})/m)^(-(k+1)) / m.
Notation "\a[ i ]^{ m }_: n" := (ann i m n) (at level 9).
Notation "\a[ i ]_: n" := (\a[i]^{1}_:n) (at level 9).

(* future value of an immediate annuity *)
Definition acc (i:R) (m n : nat) := \Rsum_(0 <= k < n*m) (1 + (\i[i]^{m})/m)^k / m.
Notation "\s[ i ]^{ m }_: n" := (acc i m n) (at level 9).
Notation "\s[ i ]_: n" := (\s[i]^{1}_:n) (at level 9).

(* present value of an annuity-due *)
Definition ann_due (i:R) (m n : nat) := \Rsum_(0 <= k < n*m) (1 + (\i[i]^{m})/m)^(-k) / m.
Notation "\a''[ i ]^{ m }_: n" := (ann_due i m n) (at level 9).
Notation "\a''[ i ]_: n" := (\a''[i]^{1}_:n) (at level 9).

(* future value of an annuity-due *)
Definition acc_due (i:R) (m n : nat) := \Rsum_(0 <= k < n*m) (1 + (\i[i]^{m})/m)^(k+1) / m.
Notation "\s''[ i ]^{ m }_: n" := (acc_due i m n) (at level 9).
Notation "\s''[ i ]_: n" := (\s[i]^{1}_:n) (at level 9).

(* present value of a continuous annuity *)
Definition ann_cont (i:R) (n:nat) := (1 - (\v[i])^n) / (δ[i]).
Notation "\abar[ i ]_: n" := (ann_cont i n) (at level 9).

(* future value of a continuous annuity *)
Definition acc_cont (i:R) (n:nat) := ((1+\i[i])^n - 1) / (δ[i]).
Notation "\sbar[ i ]_: n" := (acc_cont i n) (at level 9).

(* present value of a perpetual annuity *)
Definition perp (i:R) (m:nat) := /(\i[i]^{m}).
Notation "\a[ i ]^{ m }_:(p_infty)" := (perp i m) (at level 9).
Notation "\a[ i ]_:(p_infty)" := (\a[i]^{1}_:(p_infty)) (at level 9).

(* present value of a perpetual annuity-due *)
Definition perp_due (i:R) (m:nat) := /(\d[i]^{m}).
Notation "\a''[ i ]^{ m }_:(p_infty)" := (perp_due i m) (at level 9).
Notation "\a''[ i ]_:(p_infty)" := (\a''[i]^{1}_:(p_infty)) (at level 9).

(* present value of an increasing annuity-immediate *)
Definition ann_incr (i:R) (l m n : nat) :=
 \Rsum_(0 <= k < n*m) (1 + (\i[i]^{m})/m)^(-(k+1)) * ceil(l*(k+1)/m) / (l*m).
Notation "\(I^{ l }a)[ i ]^{ m }_: n" := (ann_incr i l m n) (at level 9).
Notation "\(Ia)[ i ]^{ m }_: n" := (\(I^{1}a)[i]^{m}_:n) (at level 9).
Notation "\(Ia)[ i ]_: n" := (\(Ia)[i]^{1}_:n) (at level 9).

(* futue value of an increasing annuity-immediate *)
Definition acc_incr (i:R) (l m n : nat) :=
 \Rsum_(0 <= k < n*m) (1 + (\i[i]^{m})/m)^(n*m-(k+1)) * ceil(l*(k+1)/m) / (l*m).
Notation "\(I^{ l }s)[ i ]^{ m }_: n" := (acc_incr i l m n) (at level 9).
Notation "\(Is)[ i ]^{ m }_: n" := (\(I^{1}s)[i]^{m}_:n) (at level 9).
Notation "\(Is)[ i ]_: n" := (\(Is)[i]^{1}_:n) (at level 9).

(* present value of an increasing annuity-due *)
Definition ann_due_incr (i:R) (l m n : nat) :=
 \Rsum_(0 <= k < n*m) (1 + (\i[i]^{m})/m)^(-k) * ceil(l*(k+1)/m) / (l*m).
Notation "\(I^{ l }a'')[ i ]^{ m }_: n" := (ann_due_incr i l m n) (at level 9).
Notation "\(Ia'')[ i ]^{ m }_: n" := (\(I^{1}a'')[i]^{m}_:n) (at level 9).
Notation "\(Ia'')[ i ]_: n" := (\(I^{1}a'')[i]^{1}_:n) (at level 9).

(* future value of an increasing annuity-due *)
Definition acc_due_incr (i:R) (l m n : nat) :=
 \Rsum_(0 <= k < n*m) (1 + (\i[i]^{m})/m)^(n*m-k) * ceil(l*(k+1)/m) / (l*m).
Notation "\(I^{ l }s'')[ i ]^{ m }_: n" := (acc_due_incr i l m n) (at level 9).
Notation "\(Is'')[ i ]^{ m }_: n" := (\(I^{1}s'')[i]^{m}_:n) (at level 9).
Notation "\(Is'')[ i ]_: n" := (\(I^{1}s'')[i]^{1}_:n) (at level 9).

(* present value of an increasing perpetual annuity-immediate *)
Definition perp_incr (i:R) (l m : nat) := Lim_seq (fun n:nat => \(I^{l}a)[i]^{m}_:n).
Notation "\(I^{ l }a)[ i ]^{ m }_:(p_infty)" := (perp_incr i l m) (at level 9).
Notation "\(Ia)[ i ]_:(p_infty)" := (\(I^{1}a)[i]^{1}_:(p_infty)) (at level 9).

(* present value of an increasing perpetual annuity-due *)
Definition perp_due_incr (i:R) (l m : nat) := Lim_seq (fun n:nat => \(I^{l}a'')[i]^{m}_:n).
Notation "\(I^{ l }a'')[ i ]^{ m }_:(p_infty)" := (perp_due_incr i l m) (at level 9).
Notation "\(Ia'')[ i ]_:(p_infty)" := (\(I^{1}a'')[i]^{1}_:(p_infty)) (at level 9).

(****************************************************************************************)

Section Interest.

Variable i:R.
Hypothesis i_pos : i > 0.

(* In this section, the interest rate "i" is omitted in the notations. *)
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

Lemma i_nom_1 : \i = \i^{1}.
Proof.
 rewrite /i_nom Rinv_1 Rpower_1; [rewrite Rmult_1_l; lra | lra].
Qed.

Lemma i_nom_pos : forall m:nat, m > 0 -> \i^{m} > 0.
Proof.
 move=> m Hgtm0.
 rewrite /i_nom -{2}(Rpower_O (1+i)); [| lra].
 apply Rmult_gt_0_compat => //.
 apply Rgt_minus.
 apply Rpower_lt; [lra |].
 apply Rinv_0_lt_compat=> //.
Qed.

Lemma i_nom_eff : forall m:nat, m > 0 -> (1 + (\i^{m})/m)^m = 1 + \i.
Proof.
 rewrite /i_nom /Rdiv => m Hm0.
 rewrite Rinv_r_simpl_m; try lra.
 rewrite Rplus_comm Rplus_assoc Rplus_opp_l Rplus_0_r Rpower_mult Rinv_l; [| lra].
 rewrite Rpower_1; lra.
Qed.

Lemma i_nom_add_pos : forall m:nat, m > 0 -> 1 + \i^{m} / m > 0.
Proof.
 move => m Hmpos.
 apply Rplus_lt_0_compat; [lra|].
 rewrite /Rdiv;
 apply Rmult_lt_0_compat; [by apply i_nom_pos | by apply Rinv_0_lt_compat].
Qed.

Lemma i_nom_i : forall m:nat, m > 0 -> 1 + (\i^{m})/m = (1 + \i)^(/m).
Proof.
 move => m Hgtm0.
 rewrite -(i_nom_eff Hgtm0).
 rewrite Rpower_mult Rinv_r; [| lra].
 rewrite Rpower_1 //; apply i_nom_add_pos => //.
Qed.

Lemma e_delta : 1+\i = exp δ.
Proof.
 rewrite /i_force (exp_ln (1+i)); lra.
Qed.

Lemma delta_pos : 0 < δ.
Proof.
 rewrite /i_force -ln_1; apply ln_increasing; lra.
Qed.

Lemma delta_neq0 : δ <> 0.
Proof.
 by apply (pos_neq0 delta_pos).
Qed.

Lemma lim_i_nom : is_lim_seq (fun m:nat => \i^{m}) δ.
Proof.
 rewrite /i_nom.
 apply (is_lim_seq_incr_n _ 1).
 apply (is_lim_seq_ext
 (fun n : nat => δ * ((exp (δ/(n+1)%N) - 1) / (δ/(n+1)%N)))).
  move => n.
  rewrite {3}plus_INR /Rpower -/i_force.
  rewrite -(Rinv_r_simpl_m δ (n+1)); [| apply delta_neq0].
  rewrite (Rmult_assoc δ _) -/(Rdiv _ δ) -(Rinv_Rdiv δ (n+1));
  [| apply delta_neq0 | apply (pos_neq0 (INRp1_pos n))].
  rewrite Rmult_assoc (Rmult_comm (/_) _) -/(Rdiv _ (_ /_)) -(plus_INR n 1).
  by rewrite {5}/Rdiv (Rmult_comm _ δ) -/(Rdiv δ _).
 rewrite -(Rbar_mult_1_r δ).
 apply (is_lim_seq_scal_l _ δ 1).
 apply (is_lim_comp_seq (fun y:R => (exp y - 1)/y) (fun n:nat => δ / (n+1)%N) 0 1).
   apply is_lim_div_expm1_0.
  rewrite /eventually; exists 0%N => n Hge0n.
  apply /Rbar_finite_neq /pos_neq0 /Rdiv_lt_0_compat;
  [apply delta_pos | apply Sn_pos].
 apply (is_lim_seq_ext (fun n => δ * / (n+1)%N) _); [move => n // |].
 rewrite (_ : 0 = Rbar_mult δ 0); last by rewrite /= Rmult_0_r.
 apply (is_lim_seq_scal_l _ δ 0).
 apply (is_lim_seq_inv _ p_infty); last by move=> H0; inversion H0.
 rewrite -(is_lim_seq_incr_n _ 1 _); apply is_lim_seq_INR.
Qed.

Lemma d_nom_pos : forall m:nat, m > 0 -> \d^{m} > 0.
Proof.
  move => m Hmpos.
  rewrite /d_nom.
  apply Rdiv_lt_0_compat; [apply i_nom_pos | apply i_nom_add_pos] => //.
Qed.

Lemma d_nom_i_nom : forall m:nat, m > 0 -> 1 - (\d^{m})/m = /(1 + (\i^{m})/m).
Proof.
 move=> m Hmpos.
 have Hipos : 1 + \i^{m} / m > 0
 by apply Rplus_lt_0_compat;
 [lra | apply Rmult_lt_0_compat; [by apply i_nom_pos | by apply Rinv_0_lt_compat]].
 rewrite (_ : (\d^{m})/m = 1 - /(1 + (\i^{m})/m)); [lra |].
 rewrite -(Rmult_1_l (/ _)) {1}(Rinv_r_sym (1 + \i^{m} / m));
 [rewrite -RIneq.Rdiv_minus_distr | lra].
 rewrite Rplus_comm /Rminus Rplus_assoc Rplus_opp_r Rplus_0_r /d_nom /Rdiv Rmult_assoc
 -Rinv_mult_distr; try lra.
 rewrite (Rmult_comm (1+_)) Rinv_mult_distr; try lra.
 by rewrite -Rmult_assoc Rplus_comm.
Qed.

Lemma lim_d_nom : is_lim_seq (fun m:nat => \d^{m}) δ.
Proof.
 rewrite /d_nom.
 rewrite -(Rdiv_1 δ).
 apply (is_lim_seq_div' _ _ δ 1); try lra.
  apply lim_i_nom.
 rewrite -(Rplus_0_r 1).
 apply (is_lim_seq_plus' _ _ 1 0).
  rewrite (Rplus_0_r 1); apply is_lim_seq_const.
 apply (is_lim_seq_div _ _ δ p_infty).
    apply lim_i_nom.
   apply is_lim_seq_INR.
  move => Hp; inversion Hp.
 by rewrite /is_Rbar_div /is_Rbar_mult /Rbar_inv /= Rmult_0_r.
Qed.

Lemma v_pos : \v > 0.
Proof.
 apply Rinv_0_lt_compat; lra.
Qed.

Lemma lt_v_1 : \v < 1.
Proof.
 rewrite -Rinv_1; apply Rinv_1_lt_contravar; lra.
Qed.

Lemma v_in_0_1 : 0 < \v < 1.
Proof.
 apply conj; [apply v_pos | apply lt_v_1].
Qed.

Lemma lt_vpow_1 : forall r:R, r > 0 -> (\v)^r < 1.
Proof.
 move => r Hrpos.
 rewrite -(Rpower_O \v); [| apply v_pos].
 apply Rpower_lt' => // ; apply v_in_0_1.
Qed.

Lemma i_v : 1 + \i = (\v)^(-1).
Proof.
 rewrite /v_pres.
 rewrite -(Rpower_1 (1+i));
 [by rewrite -Rpower_Ropp Rpower_mult Rmult_opp_opp Rmult_1_l | lra].
Qed.

Lemma d_nom_i_nom_v : forall m:nat, m > 0 -> \d^{m} = (\i^{m}) * (\v)^(/m).
Proof.
  move => m Hmpos.
  rewrite /d_nom.
  rewrite i_nom_i // i_v Rpower_mult -(Ropp_mult_distr_l) Rmult_1_l /Rdiv Rpower_Ropp.
    by rewrite Rinv_involutive; [| apply /pos_neq0 /exp_pos].
Qed.

Lemma a_calc : forall (n m : nat), m > 0 -> \a^{m}_:n = (1 - (\v)^n) / (\i^{m}).
Proof.
 move=> n m Hmpos.
 rewrite /ann.
 rewrite (i_nom_i Hmpos) i_v Rpower_mult.
 under eq_big_nat => k.
  rewrite Rpower_mult (Rmult_comm (-1)) Rmult_assoc Rmult_opp_opp
  Rmult_1_l -(Rpower_mult _ (/m)).
  rewrite Rpower_plus Rpower_1; [| apply exp_pos].
  rewrite /Rdiv Rmult_assoc.
  over.
 rewrite /=.
 rewrite -big_distrl /=.
 rewrite sum_geom;
 [| apply exp_pos
 | apply /Rlt_not_eq /lt_vpow_1 /Rinv_0_lt_compat => //].
 rewrite Rpower_mult mult_INR (Rmult_comm _ (n*m)) Rinv_r_simpl_l; [| lra].
 rewrite -/(Rdiv _ m) -(Rinv_Rdiv _ ((\v)^(/m))); [| lra | apply /pos_neq0 /exp_pos].
 rewrite /Rdiv Rmult_assoc -Rinv_mult_distr;
 [| apply /Rminus_eq_contra /Rgt_not_eq /lt_vpow_1 /Rinv_0_lt_compat => //
 | apply /pos_neq0 /Rmult_gt_0_compat => //; apply /Rinv_0_lt_compat /exp_pos].
 rewrite (Rmult_comm m _) -Rmult_assoc -/(Rdiv _ ((\v)^(/m))) RIneq.Rdiv_minus_distr.
 rewrite /Rdiv Rinv_r; [| apply /pos_neq0 /exp_pos].
 rewrite Rmult_1_l -Rpower_Ropp {2}/v_pres -Rpower_Ropp'; [| lra]; rewrite Ropp_involutive.
 rewrite (Rmult_comm _ m).
 by rewrite /i_nom.
Qed.

Lemma s_a : forall (n m : nat), m > 0 -> \s^{m}_:n = (1 + \i)^n * \a^{m}_:n.
Proof.
  move => n m Hmpos.
  rewrite /acc /ann.
  rewrite big_distrr /=.
  rewrite -(i_nom_eff Hmpos).
  under [\big[Rplus/0]_(_<=_<_)((_^m)^n*_)]eq_big_nat => k Hk.
  { rewrite Rpower_mult /Rdiv -Rmult_assoc -Rpower_plus.
    rewrite (_ : m * n + - (k + 1) = INR (0 + n*m - k.+1)%N);
      [| rewrite SSR_minus minus_INR;
         [rewrite -Nat.add_1_r plus_INR mult_INR (_ : 1 = 1%N) //; lra |
          rewrite add0n; move: Hk => /andP; case => _ /ltP; lia]].
    over. }
  rewrite big_nat_rev //.
Qed.

Lemma s_calc : forall (n m :nat), m > 0 -> \s^{m}_:n = ((1+\i)^n - 1) / (\i^{m}).
Proof.
  move => n m Hmpos.
  rewrite s_a // a_calc //.
  rewrite /Rdiv -Rmult_assoc Rmult_plus_distr_l Rmult_1_r -Ropp_mult_distr_r.
  rewrite {2}i_v.
  rewrite Rpower_mult -Rpower_plus -Ropp_mult_distr_l Rmult_1_l Rplus_opp_l Rpower_O //;
    apply v_pos.
Qed.

Lemma a''_a : forall (n m : nat), m > 0 -> \a''^{m}_:n = (1 + (\i^{m})/m) * \a^{m}_:n.
Proof.
 move => n m Hmpos.
 rewrite big_distrr /=.
 under eq_big_nat => k.
  rewrite {1}/Rdiv -Rmult_assoc -{1}(Rpower_1 (1 + \i^{m} / m));
  [| apply Rplus_lt_0_compat; [lra | apply Rdiv_lt_0_compat; [apply i_nom_pos |]]; done];
  rewrite -Rpower_plus Ropp_plus_minus_distr Rplus_minus.
  over.
 by [].
Qed.

Lemma a_a'' : forall (n m : nat), m > 0 -> \a^{m}_:n = (\v)^(/m) * \a''^{m}_:n.
Proof.
 move => n m Hmpos.
 rewrite a''_a //.
 rewrite i_nom_i //.
 rewrite -Rmult_assoc Rpower_mult_distr; [| apply v_pos | lra].
 by rewrite Rinv_l; [| lra]; rewrite one_pow Rmult_1_l.
Qed.

Lemma a''_calc : forall (n m : nat), m > 0 -> \a''^{m}_:n = (1 - (\v)^n) / \d^{m}.
Proof.
 move => n m Hmpos.
 rewrite a''_a //; rewrite a_calc //.
 rewrite -(Rinv_involutive (1 + \i^{m} / m)); [| apply /pos_neq0 /i_nom_add_pos => //].
 rewrite Rmult_comm {1}/Rdiv Rmult_assoc -/Rdiv -Rinv_mult_distr;
   [| apply /pos_neq0 /i_nom_pos => // |
    apply /Rinv_neq_0_compat /pos_neq0 /i_nom_add_pos => //].
 by[].
Qed.

Lemma s''_s : forall (n m : nat), m > 0 -> \s''^{m}_:n = (1 + (\i^{m})/m) * \s^{m}_:n.
Proof.
  move => n m Hmpos.
  rewrite big_distrr /=.
  under eq_big_nat => k Hk.
  { rewrite -{1}(Rpower_1 (1+_)); [| apply i_nom_add_pos => //].
    rewrite -Rmult_assoc -Rpower_plus (Rplus_comm _ k).
    over. }
  by [].
Qed.

Lemma s_s'' : forall (n m : nat), m > 0 -> \s^{m}_:n = (\v)^(/m) * \s''^{m}_:n.
Proof.
  move => n m Hmpos.
  rewrite s''_s //.
  rewrite i_nom_i //.
  rewrite -Rmult_assoc Rpower_mult_distr; [| apply v_pos | lra].
    by rewrite Rinv_l; [| lra]; rewrite one_pow Rmult_1_l.
Qed.  

Lemma s''_calc : forall (n m : nat), m > 0 -> \s''^{m}_:n = ((1+\i)^n - 1) / \d^{m}.
Proof.
  move => n m Hmpos.
  rewrite s''_s //; rewrite s_calc //.
  rewrite -(Rinv_involutive (1 + \i^{m} / m)); [| apply /pos_neq0 /i_nom_add_pos => //].
  rewrite Rmult_comm {1}/Rdiv Rmult_assoc -/Rdiv -Rinv_mult_distr;
    [| apply /pos_neq0 /i_nom_pos => // |
     apply /Rinv_neq_0_compat /pos_neq0 /i_nom_add_pos => //].
    by[].
Qed.

Lemma s''_a'' : forall (n m : nat), m > 0 -> \s''^{m}_:n = (1 + \i)^n * \a''^{m}_:n.
Proof.
  move => n m Hmpos.
  rewrite s''_calc // a''_calc //.
  rewrite /Rdiv -Rmult_assoc Rmult_plus_distr_l Rmult_1_r -Ropp_mult_distr_r.
  rewrite {3}i_v.
  rewrite Rpower_mult -Rpower_plus -Ropp_mult_distr_l Rmult_1_l Rplus_opp_l Rpower_O //;
    apply v_pos.
Qed.

Lemma sbar_abar : forall n:nat, \sbar_:n = (1 + \i)^n * \abar_:n.
Proof.
  move => n.
  rewrite /ann_cont /acc_cont.
  rewrite /Rdiv -Rmult_assoc Rmult_plus_distr_l Rmult_1_r -Ropp_mult_distr_r.
  rewrite {3}i_v.
  rewrite Rpower_mult -Rpower_plus -Ropp_mult_distr_l Rmult_1_l Rplus_opp_l Rpower_O //;
    apply v_pos.
Qed.  

Lemma lim_m_a : forall n:nat, is_lim_seq (fun m:nat => \a^{m}_:n) (\abar_:n).
Proof.
 move => n.
 rewrite (is_lim_seq_incr_n _ 1).
 apply (is_lim_seq_ext (fun m : nat => (1 - (\v)^n) */ \i^{m+1})).
  by move => m; rewrite a_calc; [| apply Sn_pos]; rewrite /Rdiv.
 rewrite /ann_cont /Rdiv.
 apply (is_lim_seq_scal_l _ _ (/δ)).
 apply (is_lim_seq_inv _ δ); [| apply /Rbar_finite_neq /delta_neq0].
 apply /(is_lim_seq_incr_n (fun m:nat => \i^{m})) /lim_i_nom.
Qed.

Lemma lim_m_a'' : forall n:nat, is_lim_seq (fun m:nat => \a''^{m}_:n) (\abar_:n).
Proof.
 move => n.
 rewrite (is_lim_seq_incr_n _ 1).
 apply (is_lim_seq_ext (fun m : nat => (1 - (\v)^n) */ \d^{m+1})).
  by move => m; rewrite a''_calc; [| apply Sn_pos]; rewrite /Rdiv.
 rewrite /ann_cont /Rdiv.
 apply (is_lim_seq_scal_l _ _ (/δ)).
 apply (is_lim_seq_inv _ δ); [| apply /Rbar_finite_neq /delta_neq0].
 apply /(is_lim_seq_incr_n (fun m:nat => \d^{m})) /lim_d_nom.
Qed.

Lemma lim_m_s : forall n:nat, is_lim_seq (fun m:nat => \s^{m}_:n) (\sbar_:n).
Proof.
  move => n.
  rewrite (is_lim_seq_incr_n _ 1).  
  apply (is_lim_seq_ext (fun m:nat => (1+\i)^n * \a^{(m+1)%coq_nat}_:n)).
  - move => m.
    rewrite s_a // (_ : 0 = 0%N) //.
    apply /Rlt_gt /lt_INR; lia.
  - rewrite sbar_abar.
    rewrite (_ : (1+\i)^n * \abar_:n = Rbar_mult ((1+\i)^n) \abar_:n) //.
    apply (is_lim_seq_scal_l _ _ \abar_:n).
    rewrite -(is_lim_seq_incr_n (fun m:nat => \a^{m}_:n) 1).
    apply lim_m_a.
Qed.

Lemma lim_m_s'' : forall n:nat, is_lim_seq (fun m:nat => \s''^{m}_:n) (\sbar_:n).
Proof.
  move => n.
  rewrite (is_lim_seq_incr_n _ 1).  
  apply (is_lim_seq_ext (fun m:nat => (1+\i)^n * \a''^{(m+1)%coq_nat}_:n)).
  - move => m.
    rewrite s''_a'' // (_ : 0 = 0%N) //.
    apply /Rlt_gt /lt_INR; lia.
  - rewrite sbar_abar.
    rewrite (_ : (1+\i)^n * \abar_:n = Rbar_mult ((1+\i)^n) \abar_:n) //.
    apply (is_lim_seq_scal_l _ _ \abar_:n).
    rewrite -(is_lim_seq_incr_n (fun m:nat => \a''^{m}_:n) 1).
    apply lim_m_a''.
Qed.  

Lemma lim_n_a : forall (m:nat), m > 0 ->
 is_lim_seq (fun n:nat => \a^{m}_:n) (\a^{m}_:(p_infty)).
Proof.
 move => m Hmpos.
 apply (is_lim_seq_ext (fun n:nat => (1-(\v)^n) */ \i^{m})).
  by move => n; rewrite a_calc.
 rewrite /perp -(Rbar_mult_1_l (/ \i^{m})).
 apply is_lim_seq_scal_r.
 rewrite -{2}(Rminus_0_r 1).
 apply (is_lim_seq_minus' _ _ 1 0) => //.
  apply is_lim_seq_const.
 apply lim_pow_0.
 apply v_in_0_1.
Qed.

Lemma lim_n_a'' : forall (m:nat), m > 0 ->
 is_lim_seq (fun n:nat => \a''^{m}_:n) (\a''^{m}_:(p_infty)).
Proof.
 move => m Hmpos.
 apply (is_lim_seq_ext (fun n:nat => (1-(\v)^n) */ \d^{m})).
  by move => n; rewrite a''_calc.
 rewrite /perp -(Rbar_mult_1_l (/ \d^{m})).
 apply is_lim_seq_scal_r.
 rewrite -{2}(Rminus_0_r 1).
 apply (is_lim_seq_minus' _ _ 1 0) => //.
  apply is_lim_seq_const.
 apply lim_pow_0.
 apply v_in_0_1.
Qed.

Lemma Ilsm_Ilam : forall (l n m : nat), l > 0 -> m > 0 ->
  \(I^{l}s)^{m}_:n = (1 + \i)^n * \(I^{l}a)^{m}_:n.
Proof.
  move => l n m Hlpos Hmpos.
  rewrite big_distrr /=.
  rewrite -(i_nom_eff Hmpos).
  under eq_big_nat do
    (rewrite Rpower_mult -!Rmult_assoc -Rpower_plus (Rmult_comm m n) -/(Rminus (n*m) _)).
  rewrite /acc_incr //.
Qed.

Lemma Iam_calc : forall (n m : nat), m > 0 ->
 \(Ia)^{m}_:n = \Rsum_(0<=j<n) (j+1)/m * \Rsum_(j*m <= k < (j+1)*m) (\v)^((k+1)/m).
Proof.
 move => n m Hmpos.
 rewrite /ann_incr.
 rewrite /index_iota !subn0.
 rewrite -(iota_pttn n m).
 rewrite big_allpairs_dep.
 under eq_bigr => j HT.
  under eq_big_seq => k Hk.
   rewrite mem_iota in Hk.
   rewrite !Rmult_1_l.
   rewrite -(ceil_unique (n := Z.of_nat j + 1)).
    rewrite plus_IZR -INR_IZR_INZ.
    rewrite /(Rdiv _ m) Rmult_assoc -!/(Rdiv _ m) Rmult_comm.
    rewrite i_nom_i // i_v !Rpower_mult (Rmult_comm (-1)) Rmult_assoc
    Rmult_opp_opp Rmult_1_r (Rmult_comm (/m)) -/(Rdiv _ m).
    over.
   split.
    rewrite plus_IZR -INR_IZR_INZ Ropp_r_simpl_l.
    rewrite -(Rinv_r_simpl_l m j) /Rdiv; [| apply /pos_neq0 /Hmpos];
    apply Rmult_lt_compat_r; [apply Rinv_0_lt_compat => // | ].
    rewrite -(plus_INR _ 1) -mult_INR;
    apply lt_INR; rewrite Nat.add_1_r; apply le_lt_n_Sm; case: (andP Hk) => /leP //.
   rewrite -(Rinv_r_simpl_l m (_ + _)%Z) /Rdiv; [| apply /pos_neq0 /Hmpos];
   apply Rmult_le_compat_r; [by apply /Rlt_le /Rinv_0_lt_compat |].
   rewrite plus_IZR -INR_IZR_INZ -!S_INR -mult_INR; apply le_INR; rewrite -/(lt k _).
   rewrite Nat.mul_succ_l; case: (andP Hk) => _ /leP //.
  rewrite /=.
  rewrite -(big_distrr ((j+1)/m)).
  rewrite -{3}(addnK (j*m) m) addnC -{4}(mul1n m) -mulnDl.
  over.
 by[].
Qed.

Lemma Ism_calc : forall (n m : nat), m > 0 ->
 \(Is)^{m}_:n = \Rsum_(0<=j<n) (j+1)/m * \Rsum_(j*m <= k < (j+1)*m) (1+\i)^(n-(k+1)/m).
Proof.
  move => n m Hmpos.
  assert (H1pos : 1%N > 0) by (rewrite (_ : INR 1%N = 1) //; lra).
  rewrite Ilsm_Ilam //.
  rewrite Iam_calc //.
  rewrite big_distrr /=.
  under eq_big_nat => j Hj.
  { rewrite -Rmult_assoc. rewrite (Rmult_comm (_^n)) Rmult_assoc.
    rewrite big_distrr /=.
    under eq_big_nat => k Hk.
    { rewrite /v_pres -Rpower_Ropp1;
        [| rewrite -(i_nom_eff H1pos) Rpower_1; apply i_nom_add_pos; lra].
      rewrite Rpower_mult -Rpower_plus -Ropp_mult_distr_l Rmult_1_l -/(Rminus n ((k+1)/m)).
      over. }
    over. }
    by [].
Qed.

Lemma Imam_calc_aux : forall (n m : nat), m > 0 ->
 \(I^{m}a)^{m}_:n = \Rsum_(0 <= k < n*m) (\v)^((k+1)/m) * (k+1) / m^2.
Proof.
 move => n m Hmpos.
 rewrite /ann_incr.
 under eq_big_seq => k Hk.
  rewrite {3}/Rdiv Rinv_r_simpl_m; [| apply pos_neq0 => //].
  rewrite -{2}(plus_INR k 1) (INR_IZR_INZ (k+1)) ceil_n -INR_IZR_INZ plus_INR.
  rewrite -Rpower_2 //.
  rewrite i_nom_i // i_v !Rpower_mult /(Rdiv _ m) (Rmult_comm (-1))
  (Rmult_assoc (/m)) Rmult_opp_opp Rmult_1_r (Rmult_comm (/m)) -/(Rdiv _ m).
  over.
 by[].
Qed.

Lemma Imam_calc : forall (n m : nat), m > 0 ->
  \(I^{m}a)^{m}_:n =
  ((\v)^(/m) * (1 - (n*m+1)*(\v)^n + n*m*(\v)^(n+1/m))) / (m*(1-(\v)^(/m)))^2.
Proof.
 move => n m Hmpos.
 rewrite Imam_calc_aux //.
 under eq_big_nat => k Hk.
  rewrite {1}/Rdiv Rdiv_plus_distr Rpower_plus (Rmult_comm ((\v)^(k/m))).
  rewrite (Rmult_assoc _ _ (k+1)) (Rmult_comm _  (k+1)) /Rdiv Rmult_1_l.
  rewrite (Rmult_comm k) -Rpower_mult.
  over.
 rewrite /=.
 rewrite -big_distrl -big_distrr /=.
 rewrite sum_geom_incr; [| split;
 [apply exp_pos | apply /lt_vpow_1 /Rinv_0_lt_compat => //]].
 rewrite mult_INR !Rpower_mult.
 rewrite 2!(Rmult_comm (/m)) (Rmult_plus_distr_r _ _ (/m))
 Rinv_r_simpl_l; [| apply pos_neq0 => //].
 rewrite {1}/Rdiv 2!Rmult_assoc -Rinv_mult_distr; try apply /pos_neq0 /exp_pos.
 rewrite Rpower_mult_distr; [| apply /Rgt_minus /lt_vpow_1 /Rinv_0_lt_compat => // | done].
 by rewrite -Rmult_assoc (Rmult_comm (1-(\v)^(/m)) m) -/(Rdiv _ (_^2)).
Qed.

Lemma Imsm_calc : forall (n m : nat), m > 0 ->
  \(I^{m}s)^{m}_:n =
  ((1+\i)^(n+1/m) - (n*m+1)*(1+\i)^(/m) + n*m) / (m*((1+\i)^(/m)-1))^2.
Proof.
  move => n m Hmpos.
  assert (H0 : 0 < 1 - \v ^ (/ m)) by apply /Rgt_minus /lt_vpow_1 /Rinv_0_lt_compat => //.
  assert (H1 : 0 < m * (1 - \v ^ (/ m))) by apply Rmult_gt_0_compat => //.
  rewrite Ilsm_Ilam // Imam_calc //.
  rewrite /Rdiv -!Rmult_assoc.
  rewrite i_v.
  rewrite !Rpower_mult.
  rewrite (_ : \v ^ (-1 * / m) - 1 = \v ^ (-1 * / m) * (1 - (\v)^(/m)));
    [| by rewrite Rmult_minus_distr_l Rmult_1_r -Rpower_plus -{4}(Rmult_1_l (/m))
          -Rmult_plus_distr_r Rplus_opp_l Rmult_0_l Rpower_O; [| apply /v_pos]].
  rewrite -Rmult_assoc (Rmult_comm m (\v ^ _)) (Rmult_assoc (\v ^ _) m).
  rewrite -(Rpower_mult_distr (\v ^ (-1 * / m)) _ 2) //; [| apply exp_pos].
  rewrite Rinv_mult_distr; try apply pos_neq0; try apply exp_pos.
  rewrite Rpower_mult -Rmult_assoc.
  rewrite (_ : / \v ^ (-1 * / m * 2) = \v ^ (2 */ m));
    [| rewrite -Rpower_Ropp -Ropp_mult_distr_l Rmult_1_l
       -Ropp_mult_distr_l Ropp_involutive Rmult_comm //].
  rewrite !(Rmult_plus_distr_r _ _ (\v^(2*/m))).
  rewrite -Ropp_mult_distr_l (Rmult_assoc (n*m+1)) -!Rpower_plus.
  rewrite -(Rmult_plus_distr_r _ _ (/m)) (_ : -1 + 2 = 1); [| lra].
  rewrite !Rmult_plus_distr_l.
  rewrite (_ : -1*n +  -1 * (1 * / m) + 2 * / m = -1 * n + /m); [| lra].
  rewrite Rmult_1_r (Rmult_comm _ (-_)) -Ropp_mult_distr_l.
  rewrite (Rmult_assoc (n*m+1)) -Rpower_plus -Rplus_assoc
    (_ : n + -1 * n = 0); [| lra]; rewrite Rplus_0_l.
  rewrite (Rmult_comm (n*m)) -Rmult_assoc -Rpower_plus.
  rewrite (_ : -1 * n + / m + (n + 1 * / m) = 2 * /m); [| lra].
  rewrite Rmult_1_l; lra.
Qed.
      
Lemma Ila''m_Ilam : forall (l n m : nat), l > 0 -> m > 0 ->
 \(I^{l}a'')^{m}_:n = (1 + (\i^{m})/m) * \(I^{l}a)^{m}_:n.
Proof.
 move => l n m Hlpos Hmpos.
 rewrite /ann_incr /ann_due_incr.
 rewrite big_distrr /=.
 under eq_big_nat => k Hk.
  rewrite -(Ropp_r_simpl_l (-1) (-k)) -(Ropp_plus_distr) /Rminus Ropp_involutive.
  rewrite Rpower_plus Rpower_1; [| apply i_nom_add_pos => //]; rewrite (Rmult_comm _ (1+_)).
  rewrite {1}/Rdiv !Rmult_assoc -(Rmult_assoc _ _ (/(l*m))).
  over.
 rewrite /=.
 by[].
Qed.

Lemma Ia''m_calc : forall (n m : nat), m > 0 ->
 \(Ia'')^{m}_:n = \Rsum_(0<=j<n) (j+1)/m * \Rsum_(j*m <= k < (j+1)*m) (\v)^(k/m).
Proof.
 move => n m Hmpos.
 rewrite Ila''m_Ilam; [| apply INR1_pos | done].
 rewrite Iam_calc //.
 rewrite big_distrr /=.
 under eq_big_nat => j Hj.
  rewrite -Rmult_assoc (Rmult_comm (1+_)) Rmult_assoc.
  rewrite big_distrr /=.
  under eq_big_nat => k Hk.
   rewrite Rdiv_plus_distr Rpower_plus Rmult_comm Rmult_assoc i_nom_i // i_v
   Rpower_mult -Rpower_plus -Rmult_plus_distr_r Rplus_opp_r Rmult_0_l
   Rpower_O; [| apply v_pos]; rewrite Rmult_1_r.
   over.
  over.
 by[].
Qed.

Lemma Ima''m_calc_aux : forall (n m : nat), m > 0 ->
 \(I^{m}a'')^{m}_:n = \Rsum_(0 <= k < n*m) (\v)^(k/m) * (k+1) / m^2.
Proof.
 move => n m Hmpos.
 rewrite Ila''m_Ilam //.
 rewrite Imam_calc_aux //.
 rewrite big_distrr /=.
  under eq_big_nat => k Hk.
   rewrite Rdiv_plus_distr Rpower_plus (Rmult_comm ((\v) ^ _)) -!Rmult_assoc i_nom_i // i_v
   Rpower_mult -Rpower_plus -Rmult_plus_distr_r Rplus_opp_l Rmult_0_l
   Rpower_O; [| apply v_pos]; rewrite Rmult_1_l.
   over.
 by[].
Qed.

Lemma Ima''m_calc : forall (n m : nat), m > 0 ->
 \(I^{m}a'')^{m}_:n = (1 - (n*m+1)*(\v)^n + n*m*(\v)^(n+1/m)) / (m*(1-(\v)^(/m)))^2.
Proof.
 move => n m Hmpos.
 rewrite Ila''m_Ilam // Imam_calc //.
 rewrite /Rdiv -!Rmult_assoc i_nom_i // {1}/v_pres Rpower_mult_distr; [| lra | apply v_pos].
 by rewrite Rinv_r; try lra; rewrite one_pow Rmult_1_l.
Qed.

Lemma Ils''m_Ilsm : forall (l n m : nat), l > 0 -> m > 0 ->
 \(I^{l}s'')^{m}_:n = (1 + (\i^{m})/m) * \(I^{l}s)^{m}_:n.
Proof.
 move => l n m Hlpos Hmpos.
 rewrite /acc_incr /acc_due_incr.
 rewrite big_distrr /=.
 under eq_big_nat => k Hk.
  rewrite /Rminus -(Ropp_r_simpl_l (-1) (-k)) -(Ropp_plus_distr) /Rminus Ropp_involutive.
  rewrite -Rplus_assoc Rpower_plus Rpower_1;
    [| apply i_nom_add_pos => //]; rewrite (Rmult_comm _ (1+_)).
  rewrite {1}/Rdiv !Rmult_assoc -(Rmult_assoc _ _ (/(l*m))).
  over.
 rewrite /=.
 by[].
Qed.

Lemma Ims''m_calc : forall (n m : nat), m > 0 ->
  \(I^{m}s'')^{m}_:n =
  (1+\i)^(/m) * ((1+\i)^(n+1/m) - (n*m+1)*(1+\i)^(/m) + n*m) / (m*((1+\i)^(/m)-1))^2.
Proof.
  move => n m Hmpos.
  rewrite Ils''m_Ilsm //.
  rewrite (_ : 1 + (\i^{m})/m = (1 + \i)^(/m));
    [| by rewrite -(i_nom_eff Hmpos) Rpower_mult Rinv_r; [| apply pos_neq0 => //];
       rewrite Rpower_1; [| apply i_nom_add_pos => //]].
  rewrite Imsm_calc; lra.
Qed.

Lemma lim_Imam : forall m:nat, m > 0 ->
 is_lim_seq (fun n:nat => \(I^{m}a)^{m}_:n) (/(\i^{m} * \d^{m})).
Proof.
  move => m Hmpos.
  assert (H_i : \i^{m} = m * ((\v)^(-/m) - 1)).
  by rewrite /i_nom i_v Rpower_mult -Ropp_mult_distr_l Rmult_1_l.
  rewrite -(Rmult_1_l (/ _)) -/(Rdiv 1 _).
  apply (is_lim_seq_ext
    (fun n:nat => ((\v)^(/m) * (1 - (n*m+1)*(\v)^n + n*m*(\v)^(n+1/m))) / (m*(1-(\v)^(/m)))^2));
    [move => n; rewrite Imam_calc // |].
  apply (is_lim_seq_div _ _ ((\v)^(/m) * 1) ((m * (1 - (\v)^(/m)))^2));
    [| apply is_lim_seq_const
     | rewrite /Rpower; apply /Rbar_finite_neq /pos_neq0 /exp_pos |].
  - rewrite (_ : (\v)^(/m) * 1 = Rbar_mult ((\v)^(/m)) 1) //.
    apply (is_lim_seq_scal_l _ _ 1).
    apply (is_lim_seq_ext
      (fun n:nat => 1 + (- (n * m + 1) * (\v)^n + n * m * (\v)^(n+1/m))));
      [move => n; lra |].
    rewrite {4}(_ : 1 = 1 + 0); [| by rewrite Rplus_0_r].
    apply is_lim_seq_plus'; [apply is_lim_seq_const |].
    rewrite -(Rplus_0_r 0).
    apply is_lim_seq_plus'.
    + rewrite (_ : Finite 0 = Rbar_opp 0); [| rewrite /= (_ : -0 = 0) //; apply Ropp_0].
      apply (is_lim_seq_ext (fun n:nat => - ((m*n + 1) * (\v)^n)));
        [by move => n; rewrite (Rmult_comm m n) Ropp_mult_distr_l |].
      rewrite -is_lim_seq_opp.
      apply (is_lim_seq_ext (fun n:nat => m * (n * (\v)^n) + (\v)^n));
      [ by move => n; rewrite Rmult_plus_distr_r Rmult_1_l Rmult_assoc |].
      rewrite (_ : 0 = 0 + 0); [| lra].
      apply (is_lim_seq_plus' _ _ 0 0).
      * rewrite (_ : Finite 0 = Rbar_mult m 0); [| by rewrite /= Rmult_0_r].
        apply is_lim_seq_scal_l.
        apply /lim_mult1_pow_0 /v_in_0_1.
      * apply /lim_pow_0 /v_in_0_1.
    + apply (is_lim_seq_ext (fun n:nat => (m * (\v)^(1/m)) * (n * (\v)^n))).
      * move => n.
        rewrite Rpower_plus (Rmult_comm n m) (Rmult_assoc m n) -(Rmult_assoc n).
        by rewrite (Rmult_comm (n * (\v)^n)) (Rmult_assoc m).
      * rewrite (_ : Finite 0 = Rbar_mult (m * (\v)^(1/m)) 0);
          [| by rewrite /= Rmult_0_r].
        apply is_lim_seq_scal_l.
        apply /lim_mult1_pow_0 /v_in_0_1.      
  - rewrite /is_Rbar_div /is_Rbar_mult /= Rmult_1_r.
    rewrite {1}(_ : (\v)^(/m) = /((\v)^(-/m)));
      [| by rewrite -{1}(Ropp_involutive (/m)) (Rpower_Ropp \v (-/m))].
    rewrite -Rinv_mult_distr; try apply /pos_neq0 /exp_pos.
    rewrite Rpower_2;
      [| apply Rmult_gt_0_compat => //; apply /Rgt_minus /lt_vpow_1 /Rinv_0_lt_compat => //].
    rewrite -3!Rmult_assoc (Rmult_comm (\v ^ _) m) (Rmult_assoc m (\v ^ _)).
    rewrite (Rmult_minus_distr_l (\v ^ _)) Rmult_1_r -Rpower_plus Rplus_opp_l.
    rewrite Rpower_O; [| apply v_pos].
    rewrite /d_nom i_nom_i // /i_nom i_v.
    rewrite Rpower_mult /(Rdiv _ (\v ^ (-1 * / m))) -Rpower_Ropp.
    rewrite !Rmult_assoc.
    rewrite (Rmult_minus_distr_r _ _ (\v ^ _)).
    rewrite -Rpower_plus Rplus_opp_r Rpower_O; [| apply v_pos].
    by rewrite -Ropp_mult_distr_l /Rdiv !Rmult_1_l Ropp_involutive.
Qed.

Lemma perp_incr_calc :
  forall m:nat, m > 0 -> \(I^{m}a)^{m}_:(p_infty) = / ((\i^{m}) * (\d^{m})).
Proof.
  move => m Hmpos.
  apply is_lim_seq_unique.
  apply lim_Imam => //.
Qed.

Lemma lim_Ima''m : forall m:nat,
    m > 0 -> is_lim_seq (fun n:nat => \(I^{m}a'')^{m}_:n) (/(\d^{m})^2).
Proof.
  move => m Hmpos.
  apply (is_lim_seq_ext (fun n:nat => (/(\v)^(/m) * \(I^{m}a)^{m}_:n))).
  - move => n.
    rewrite Ila''m_Ilam //.
      by rewrite i_nom_i // i_v Rpower_mult -Ropp_mult_distr_l Rmult_1_l Rpower_Ropp.    
  - rewrite Rpower_2; [| apply d_nom_pos => //].
    rewrite {1}d_nom_i_nom_v // (Rmult_comm _ (\v ^ _)) Rmult_assoc.
    rewrite Rinv_mult_distr;
      [| apply /pos_neq0 /exp_pos |
       apply /pos_neq0 /Rmult_gt_0_compat; [apply i_nom_pos | apply d_nom_pos] => //].
    apply (is_lim_seq_scal_l _ _ (/ (\i^{m} * \d^{m}))).
    apply lim_Imam => //.
Qed.

End Interest.

