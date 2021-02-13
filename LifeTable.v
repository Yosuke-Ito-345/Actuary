Require Import Logic.Description Classical_sets Reals Lra Lia.
From mathcomp Require Import all_ssreflect.
From Actuary Require Export Basics Interest.
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(****************************************************************************************)

From Coquelicot Require Import Coquelicot.

(* life table *)
Record life : Type := Life {
  l_fun :> R -> R;
  l_0_pos : l_fun 0 > 0;
  l_neg_nil : forall u:R, u <= 0 -> l_fun u = l_fun 0;
  l_infty_0 : is_lim l_fun p_infty 0;
  l_decr : decreasing l_fun
}.

Notation "\l[ l ]_ u" := (l_fun l u) (at level 9).

Definition death (l:life) (u:R) := \l[l]_(u) - \l[l]_(u+1).
Notation "\d[ l ]_ u" := (death l u) (at level 9).

Definition survive (l:life) (t u : R) := \l[l]_(u+t) / \l[l]_u.

Notation "\p[ l ]_{ t & u }" := (survive l t u) (at level 9).
Notation "\p[ l ]_ u" := (\p[l]_{1&u}) (at level 9).

Definition die (l:life) (f t u : R) := (\l[l]_(u+f) - \l[l]_(u+f+t)) / (\l[l]_u).
Notation "\q[ l ]_{ f | t & u }" := (die l f t u) (at level 9).
Notation "\q[ l ]_{ t & u }" := (\q[l]_{0|t & u}) (at level 9).
Notation "\q[ l ]_{ f | & u }" := (\q[l]_{f|1 & u}) (at level 9).
Notation "\q[ l ]_ u" := (\q[l]_{0|1 & u}) (at level 9).

(* temporary curtate life expectation *)
Definition temp_curt_life_exp (l:life) (x:nat) (n:nat) :=
  \Rsum_(0 <= k < n) (k * \q[l]_{k|&x}) + n * \p[l]_{n&x}.
Notation "\e[ l ]_{ x : n }" := (temp_curt_life_exp l x n) (at level 9, x at level 9).

Definition ages_dead (l:life) : Ensemble nat := fun x:nat => \l[l]_x = 0.

Definition l_finite (l:life) := exists x:nat, (ages_dead l x).

Definition ult_age (l:life) (l_fin : l_finite l) := sval (leastN l_fin). 

(* conventional notation for ultimate age *)
Notation "ω[ l , l_fin ]" := (ult_age l l_fin) (at level 9).

(* curtate life expectation *)
Definition curt_life_exp (l:life) (l_fin : l_finite l) (x:nat) :=
  \Rsum_(0 <= k < ω[l,l_fin] - x) (k * \q[l]_{k|&x}).
Notation "\e[ l , l_fin ]_ x" := (curt_life_exp l l_fin x) (at level 9).

(****************************************************************************************)

Section LifeTable.

Variable l:life.

Notation "\l_ u" := (\l[l]_u) (at level 9). 
Notation "\d_ u" := (\d[l]_u) (at level 9).
Notation "\p_{ t & u }" := (\p[l]_{t&u}) (at level 9).
Notation "\p_ u" := (\p[l]_{1&u}) (at level 9).
Notation "\q_{ f | t & u }" := (\q[l]_{f|t&u}) (at level 9).
Notation "\q_{ t & u }" := (\q_{0|t & u}) (at level 9).
Notation "\q_{ f | & u }" := (\q_{f|1 & u}) (at level 9).
Notation "\q_ u" := (\q_{0|1 & u}) (at level 9).
Notation "\e_{ x : n }" := (\e[l]_{x:n}) (at level 9, x at level 9).

Lemma l_nonneg : forall u:R, \l_ u >= 0.
Proof.
  move => u.
  apply Rge_lim_decr; [apply l_decr | apply l_infty_0].
Qed.

Lemma q_d_l : forall u:R, \q_u = \d_u / \l_u.
Proof.
  move => u.
  rewrite /death /die.
  rewrite Rplus_0_r //.
Qed.

Lemma p_q_1 : forall (t u : R), (\l_u <> 0) -> \p_{t&u} + \q_{t&u} = 1.
Proof.
  move => t u Hlu.
  rewrite /survive /die.
  rewrite Rplus_0_r -Rdiv_plus_distr.
  rewrite /Rminus Rplus_comm Rplus_assoc Rplus_opp_l Rplus_0_r.
  rewrite /Rdiv Rinv_r; lra.
Qed.

Lemma p_mult : forall (s t u : R), (\l_(u+s) <> 0) -> \p_{s+t & u} = \p_{s&u} * \p_{t & u+s}.
Proof.
  move => s t u Hlus.
  rewrite 3!/survive.
  rewrite /Rdiv Rinv_mult_simpl //; rewrite Rplus_assoc //.
Qed.

Lemma q_defer_q : forall (f t u : R), \q_{f|t&u} = \q_{f+t & u} - \q_{f&u}.
Proof.
  move => f t u.
  rewrite 3!/die !Rplus_0_r.
  rewrite -RIneq.Rdiv_minus_distr.
  rewrite /Rminus Ropp_minus_distr (Rplus_comm (\l_u + _) _) -Rplus_assoc /Rminus.
  rewrite (Rplus_assoc _ _ (\l_u)) Rplus_opp_l Rplus_0_r -Rplus_assoc //.
Qed.

Lemma q_defer_p : forall (f t u : R), \q_{f|t&u} = \p_{f&u} - \p_{f+t & u}.
Proof.
  move => f t u.
  rewrite /die /survive.
    by rewrite RIneq.Rdiv_minus_distr Rplus_assoc.
Qed.

Lemma q_defer_pq : forall (f t u : R), (\l_(u+f) <> 0) -> \q_{f|t&u} = \p_{f&u} * \q_{t & u+f}.
Proof.
  move => f t u Hluf.
  rewrite /die /survive.
  rewrite Rplus_0_r /Rdiv Rinv_mult_simpl //.
Qed.

Lemma q_defer_p_q_defer : forall (f s t u : R), (\l_(u+s) <> 0) ->
  \p_{s&u} * \q_{f|t & u+s} = \q_{f+s|t & u}.
Proof.
  move => f s t u Hlus.
  rewrite /survive {1}/die.
  rewrite /Rdiv.
  rewrite Rmult_comm -Rmult_assoc (Rmult_assoc _ (/_)) Rinv_l // Rmult_1_r.
  rewrite /die (Rplus_comm f s) -!Rplus_assoc //.
Qed.

Lemma e_p_n : forall (x n : nat), \e_{x:n} = \Rsum_(0 <= k < n) \p_{k+1 & x}.
Proof.
  move => x n.
  rewrite /temp_curt_life_exp.
  case: (zerop n) => [Hn0 | Hnpos].
  - rewrite !big_geq; [rewrite Hn0 Rmult_0_l; lra | |]; rewrite Hn0 //.
  - under eq_big_nat => k Hk.
    { rewrite q_defer_p.
      rewrite Rmult_minus_distr_l.
      rewrite (_ : k*\p_{k+1 & x} = (k+1)*\p_{k+1 & x} - \p_{k+1 & x}).
      - rewrite {1}/Rminus Ropp_plus_distr -Rplus_assoc Ropp_involutive.
        over.
      - rewrite /survive.
        rewrite /Rdiv -!(Rmult_assoc _ _ (/ \l_x)) -Rmult_minus_distr_r.
        rewrite Rmult_plus_distr_r Rmult_1_l Ropp_r_simpl_l //. }
    rewrite 2!big_split /=.
    rewrite Rplus_comm -!Rplus_assoc (Rplus_comm (n * _) _).
    rewrite -big_nat_recr //=.
    rewrite big_nat_recl // Rmult_0_l Rplus_0_l.
    rewrite -big_split.
    under eq_big_nat => i Hi.
    { rewrite -Nat.add_1_r plus_INR /= Rplus_opp_r.
      over. }
    rewrite big1_eq.
      by rewrite Rplus_0_l.
Qed.

(****************************************************************************************)

Section FiniteLifeTable.

Hypothesis l_fin : (l_finite l).

Notation "'ω'" := (ω[l,l_fin]) (at level 8).
Notation "\e_ x" := (\e[l,l_fin]_ x) (at level 9).

Lemma l_omega_0 : \l_ω = 0.
Proof.
  rewrite /ω.
  case: leastN  => m Hmin /=.
  apply Hmin.
Qed.

Lemma omega_pos : ω > 0.
Proof.
  rewrite -Nat2Z.inj_0; apply Rlt_gt; rewrite -INR_IZR_INZ; apply lt_INR.
  apply neq_0_lt => Homega0.
  apply (Rlt_irrefl \l_ω).
  rewrite {1}l_omega_0  -Homega0.
  apply l_0_pos.
Qed.

Lemma l_old_0 : forall x:nat, (x >= ω) -> \l_x = 0.
Proof.
  move => x Hx.
  apply Rge_antisym.
  - apply l_nonneg.
  - rewrite -l_omega_0.
    apply /Rle_ge /l_decr; lra.
Qed.

Lemma l_x_pos : forall x:nat, x < ω -> \l_x > 0.
Proof.
  move => x Hx.
  case: (Rlt_le_dec 0 (\l_x)).
  - lra.
  - case => [Hlxneg | Hlx0].
    + contradict Hlxneg.
      apply /Rle_not_gt /Rge_le /l_nonneg.
    + contradict Hx.
      apply /Rge_not_lt / Rle_ge /le_INR.
      rewrite /ω.
      case: leastN => y Hmin /=.
        by apply Hmin.
Qed.

Lemma p_nonneg : forall (t x : nat), x < ω -> \p_{t&x} >= 0.
Proof.
  move => t x Hx.
  rewrite /survive /Rdiv.
  rewrite -(Rmult_0_l (/(\l_x))).
  apply (Rmult_ge_compat_r (/(\l_x)) _ 0);
    [apply /Rgt_ge /Rinv_0_lt_compat /l_x_pos => // | apply l_nonneg].
Qed.    

Lemma p_omega_0 : forall x:nat, \p_{ω-x & x} = 0.
Proof.
  move => x.
  rewrite /survive.
  rewrite Rplus_comm /Rminus Rplus_assoc Rplus_opp_l Rplus_0_r.
  rewrite l_omega_0; lra.
Qed.

Lemma p_old_0 : forall (x y : nat), x+y >= ω -> \p_{y & x} = 0.
Proof.
  move => x y Hxy.
  rewrite /survive /Rdiv.
  rewrite -plus_INR.
  rewrite (l_old_0 (x+y)); [rewrite Rmult_0_l | rewrite plus_INR]; done.
Qed.  

Lemma p_0_1 : forall (x : nat), x < ω -> \p_{0&x} = 1.
Proof.
  move => x Hx.
  rewrite /survive.
  rewrite Rplus_0_r.
  rewrite /Rdiv Rinv_r //.
  apply /pos_neq0 /l_x_pos => //.
Qed.

Lemma q_omega_1 : \q_(ω-1) = 1.
Proof.
  rewrite /die Rplus_0_r {3}/Rminus Rplus_assoc Rplus_opp_l Rplus_0_r.
  rewrite l_old_0; [| lra]; rewrite Rminus_0_r.
  rewrite /Rdiv Rinv_r //.
  apply pos_neq0.
  rewrite -(minus_INR ω 1);
    [apply /l_x_pos /lt_INR /Nat.sub_lt => // |]; apply /INR_lt /omega_pos.
Qed.

Lemma q_defer_old_0 : forall (f t x : nat), x+f >= ω -> \q_{f|t&x} = 0.
Proof.
  move => f t x Hxf.
  rewrite /die.
  rewrite -!plus_INR.
  rewrite (l_old_0 (x+f)%coq_nat); [| rewrite plus_INR //].
  rewrite (l_old_0 (((x+f)%coq_nat+t)%coq_nat)).
  - rewrite Rminus_0_r /Rdiv Rmult_0_l //.
  - apply /Rle_ge /le_INR /(Nat.le_trans _ (x+f)%coq_nat);
      [apply INR_le; rewrite plus_INR; lra | lia].
Qed.

Lemma e_p : forall x:nat, \e_x = \Rsum_(0 <= k < ω-x) \p_{k+1 & x}.
Proof.
  move => x.
  rewrite /curt_life_exp.
  case: (le_lt_dec 1 (ω-x)) => [Hdead | Halive].
  - under eq_big_nat => k Hk.
    { rewrite q_defer_p.
      rewrite Rmult_minus_distr_l.
      rewrite (_ : k*\p_{k+1 & x} = (k+1)*\p_{k+1 & x} - \p_{k+1 & x}).
      - rewrite {1}/Rminus Ropp_plus_distr -Rplus_assoc Ropp_involutive.
        over.
      - rewrite /survive.
        rewrite /Rdiv -!(Rmult_assoc _ _ (/ \l_x)) -Rmult_minus_distr_r.
        rewrite Rmult_plus_distr_r Rmult_1_l Ropp_r_simpl_l //. }
    rewrite 2!big_split /=.
    rewrite -(Rplus_0_r (\Rsum_(0 <= i < ω-x) i * \p_{i&x})).
    rewrite -{2}(Rmult_0_r (ω-x)) -{2}(p_omega_0 x).
    rewrite -(minus_INR ω x); [| apply /Nat.lt_le_incl /lt_O_minus_lt; rewrite /lt //].
    rewrite -(big_nat_recr (ω-x) 0) /= ; [| rewrite /leP //].
    rewrite big_nat_recl //.
    rewrite Rmult_0_l Rplus_0_l.
    rewrite -big_split.
    under eq_big_nat => i Hi.
    { rewrite -Nat.add_1_r plus_INR /= Rplus_opp_r.
      over. }
    rewrite big1_eq.
    by rewrite Rplus_0_l.
  - rewrite !big_geq //; apply /leP; lia.
Qed.

Lemma e_rec : forall x:nat, \e_x = \p_x * (1 + \e_(x+1)).
Proof.
  move => x.
  rewrite e_p.
  case: (le_lt_dec 2 (ω-x)) => [Halive | Hdead].
  - assert (Halive0 : (0 < ω-x)%N).
    { apply /ltP /(Nat.lt_le_trans 0 2); [lia | done]. }
    assert (Halive1 : (1 < ω-x)%N).
    { apply /ltP /(Nat.lt_le_trans 1 2); [lia | done]. }
    rewrite -(prednK Halive0).
    rewrite big_nat_recl; [| by rewrite -Nat.pred_0; apply /leP /Nat.pred_le_mono /leP].
    rewrite Rplus_0_l.
    under eq_big_nat => i Hi.
    { rewrite Rplus_comm (p_mult 1 (i.+1)).
      - rewrite S_INR.
        over.
      - rewrite -(plus_INR x 1).
        apply /pos_neq0 /l_x_pos /lt_INR /lt_O_minus_lt.
        rewrite Nat.sub_add_distr.
        apply lt_minus_O_lt.
        move /ltP in Halive1.
        rewrite -SSR_minus //. }
    rewrite -big_distrr.
    rewrite -{1}(Rmult_1_r (\p_x)).
    rewrite -Rmult_plus_distr_l.
      by rewrite pred_of_minus -SSR_minus -subnDA e_p plus_INR.
  - apply lt_n_Sm_le in Hdead.
    apply Nat.le_1_r in Hdead.
    destruct Hdead as [H0 | H1].
    + rewrite H0.
      rewrite big_geq //.
      rewrite (p_old_0 x 1); [rewrite Rmult_0_l // |].
      apply Nat.sub_0_le in H0.
      apply Rle_ge; rewrite -plus_INR; apply /le_INR /(le_trans _ x) => //; lia.
    + rewrite H1.
      rewrite big_nat1 Rplus_0_l.
      rewrite e_p subnDA H1 SSR_minus Nat.sub_diag.
      rewrite big_geq //.
      rewrite Rplus_0_r Rmult_1_r //.
Qed.
    
End FiniteLifeTable.

End LifeTable.
