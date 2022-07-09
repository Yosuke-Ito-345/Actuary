Require Import Logic.Description Classical_sets Reals Lra Lia.
From mathcomp Require Import all_ssreflect.
From Coquelicot Require Import Coquelicot.
From Actuary Require Export Basics.
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(****************************************************************************************)

(* life table *)
Record life : Type := Life {
  l_fun :> R -> R;
  l_0_pos : 0 < l_fun 0;
  l_neg_nil : forall u:R, u <= 0 -> l_fun u = l_fun 0;
  l_infty_0 : is_lim l_fun p_infty 0;
  l_decr : decreasing l_fun
}.

Hint Resolve l_0_pos l_neg_nil l_infty_0 l_decr : core.

Notation "\l[ l ]_ u" := (l_fun l u) (at level 9).

Definition end_pt (l:life) := Glb_Rbar (fun u:R => \l[l]_u = 0).
Notation "\ψ[ l ]" := (end_pt l) (at level 9).

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

(* force of mortality *)
Definition d_force (l:life) (u:R) := - (Derive l u) / \l[l]_u.
Notation "\μ[ l ]_ u" := (d_force l u) (at level 9).

(* temporary curtate life expectation *)
Definition temp_curt_life_expct (l:life) (x:nat) (n:nat) :=
  \Rsum_(0 <= k < n) (k * \q[l]_{k|&x}) + n * \p[l]_{n&x}.
Notation "\e[ l ]_{ x : n }" := (temp_curt_life_expct l x n) (at level 9, x at level 9).

Definition ages_dead (l:life) : Ensemble nat := fun x:nat => \l[l]_x = 0.

Definition l_finite (l:life) := exists x:nat, (ages_dead l x).

Definition ult_age (l:life) (l_fin : l_finite l) := sval (leastN l_fin). 

(* conventional notation for ultimate age *)
Notation "\ω[ l , l_fin ]" := (ult_age l l_fin) (at level 9).

(* curtate life expectation *)
Definition curt_life_expct (l:life) (l_fin : l_finite l) (x:nat) :=
  \Rsum_(0 <= k < \ω[l,l_fin] - x) (k * \q[l]_{k|&x}).
Notation "\e[ l , l_fin ]_ x" := (curt_life_expct l l_fin x) (at level 9).

(* temporary complete life expectation *)
Definition temp_life_expct (l:life) (l_fin : l_finite l) (u t : R) :=
  RInt (fun s:R => -s * (Derive l (u+s)) / \l[l]_u) 0 t +
  RInt (fun s:R => -t * (Derive l (u+s)) / \l[l]_u) t (\ψ[l] - u).
Notation "\e`o[ l , l_fin ]_{ u : t }" :=
  (temp_life_expct l l_fin u t) (at level 9, u at level 9).

(* complete life expectation *)
Definition life_expct (l:life) (l_fin : l_finite l) (u:R) :=
  RInt (fun s:R => -s * (Derive l (u+s)) / \l[l]_u) 0 (\ψ[l] - u).
Notation "\e`o[ l , l_fin ]_ u" := (life_expct l l_fin u) (at level 9).

(****************************************************************************************)

Section LifeTable.

Variable l:life.

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

Lemma l_nonneg : forall u:R, 0 <= \l_ u.
Proof.
  move => u.
  apply Rle_lim_decr; [apply l_decr | apply l_infty_0].
Qed.

Hint Resolve l_nonneg : core.

Lemma psi_nonneg : Rbar_le 0 \ψ.
Proof.
  set (E := fun u:R => \l[l]_u = 0).
  rewrite /end_pt.
  case: (Glb_Rbar_correct E) => Hlb Hglb.
  apply Hglb.
  rewrite /is_lb_Rbar.
  move => x Hx; apply Rbar_not_lt_le.
  move => Hltx0.
  apply (Rlt_irrefl 0).
  rewrite -{2}Hx.
  rewrite l_neg_nil; [apply l_0_pos | apply /Rlt_le /Hltx0].
Qed.

Hint Resolve psi_nonneg : core.

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

Lemma l_u_pos : forall u:R, Rbar_lt u \ψ -> 0 < \l_u.
Proof.
  move => u Hu.
  case: (Rlt_le_dec 0 (\l_u)) => // Hlu0.
  apply False_ind.
  apply (Rbar_lt_not_eq u u) => //.
  apply (Rbar_lt_le_trans _ _ _ Hu).
  rewrite /end_pt.
  set (E := (fun u0 : R => \l_ u0 = 0)).
  case: (Glb_Rbar_correct E) => Hlb _.
  apply Hlb.
  rewrite /E.
  apply Rle_antisym => //.
Qed.

Hint Resolve l_u_pos : core.

Lemma l_pos_bound : forall u:R, 0 < \l_u -> Rbar_le u \ψ.
Proof.
  move => u Hlu0.
  set (K := (fun t:R => \l_t = 0)).
  case: (Glb_Rbar_correct K) => _; apply.
  rewrite /is_lb_Rbar => s Hs.
  apply Rbar_not_lt_le => /= Hsu.
  apply (Rlt_irrefl 0).
  rewrite {2}(_ : 0 = \l_u) //.
  apply Rle_antisym; auto.
  rewrite -Hs.
  apply l_decr; lra.
Qed.

Lemma l_out_0 : forall u:R, Rbar_lt \ψ u -> \l_u = 0.
Proof.
  move => u Hpsiu.
  apply NNPP => Hluneq0.
  apply (Rbar_lt_not_le u \ψ); auto.
  apply l_pos_bound.
  move: (l_nonneg u); lra.
Qed.

Lemma e_p_n : forall (x n : nat), \e_{x:n} = \Rsum_(0 <= k < n) \p_{k+1 & x}.
Proof.
  move => x n.
  rewrite /temp_curt_life_expct.
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

Notation "\ω" := (\ω[l,l_fin]) (at level 8).
Notation "\e_ x" := (\e[l,l_fin]_ x) (at level 9).

Lemma l_omega_0 : \l_\ω = 0.
Proof.
  rewrite /(\ω).
  case: leastN  => m Hmin /=.
  apply Hmin.
Qed.

Lemma psi_finite : is_finite \ψ.
Proof.
  apply is_finite_correct.
  set E := (fun u:R => \l_u = 0).
  case: (@completeness' E).
  - rewrite /bound'.
    exists 0.
    rewrite /is_lower_bound.
    move => t Ht.
    apply Rnot_gt_le => Ht0.
    apply (Rlt_irrefl 0).
    rewrite /E in Ht.
    rewrite -{2}Ht.
    rewrite l_neg_nil; [auto | lra].      
  - exists \ω.
    rewrite /E; apply l_omega_0.
  - move => t Hglb.
    exists t.
    apply is_glb_Rbar_unique.
    rewrite /is_glb_Rbar.
    split.
    + rewrite /is_lb_Rbar.
      move => s Hs.
      rewrite /=.
      by apply Hglb.
    + move => [r Hr | Hpinfty | Hminfty].
      * rewrite /=.
        apply Hglb.
        rewrite /is_lower_bound => s Hs.
        by apply Hr.
      * rewrite /is_lb_Rbar in Hpinfty.
        by move: (Hpinfty \ω l_omega_0).
      * rewrite /Rbar_le //.
Qed.

Hint Resolve psi_finite : core.

Lemma omega_pos : 0 < \ω.
Proof.
  rewrite -Nat2Z.inj_0; apply Rlt_gt; rewrite -INR_IZR_INZ; apply lt_INR.
  apply Nat.neq_0_lt_0 => Homega0.
  apply (Rlt_irrefl \l_\ω).
  rewrite {1}l_omega_0  Homega0.
  apply l_0_pos.
Qed.

Hint Resolve omega_pos : core.

Lemma le_psi_omega : Rbar_le \ψ \ω.
Proof.
  apply Rbar_not_lt_le.
  apply (contra_not (l_u_pos \ω)).
  rewrite l_omega_0; lra.
Qed.

Lemma l_old_0 : forall x:nat, (\ω <= x) -> \l_x = 0.
Proof.
  move => x Hx.
  apply Rle_antisym.
  - rewrite -l_omega_0.
    apply /l_decr; lra.
  - apply l_nonneg.
Qed.

Lemma l_old_0' : forall u:R, \ω <= u -> \l_u = 0.
Proof.
  move => u Hu.
  apply Rle_antisym; auto.
  rewrite -l_omega_0.
  apply /l_decr; lra.
Qed.

Lemma l_x_pos : forall x:nat, x < \ω -> 0 < \l_x.
Proof.
  move => x Hx.
  case: (Rlt_le_dec 0 (\l_x)).
  - lra.
  - case => [Hlxneg | Hlx0].
    + contradict Hlxneg.
      apply /Rle_not_gt /l_nonneg.
    + contradict Hx.
      apply /Rge_not_lt / Rle_ge /le_INR.
      rewrite /(\ω).
      case: leastN => y Hmin /=.
        by apply Hmin.
Qed.

Hint Resolve l_x_pos : core.

Lemma p_nonneg : forall (t x : nat), x < \ω -> 0 <= \p_{t&x}.
Proof.
  move => t x Hx.
  rewrite /survive /Rdiv.
  rewrite -(Rmult_0_l (/(\l_x))).
  apply (Rmult_le_compat_r (/(\l_x)) 0);
    [apply /Rlt_le /Rinv_0_lt_compat /l_x_pos => // | apply l_nonneg].
Qed.

Lemma p_nonneg' : forall (t:R) (x:nat), x < \ω -> 0 <= \p_{t&x}.
Proof.
  move => t x Hx.
  rewrite /survive.
  apply Rdiv_le_0_compat; [| apply l_x_pos]; auto.
Qed.

Lemma p_omega_0 : forall x:nat, \p_{\ω-x & x} = 0.
Proof.
  move => x.
  rewrite /survive.
  rewrite Rplus_comm /Rminus Rplus_assoc Rplus_opp_l Rplus_0_r.
  rewrite l_omega_0; lra.
Qed.

Lemma p_old_0 : forall (x y : nat), \ω <= x+y -> \p_{y & x} = 0.
Proof.
  move => x y Hxy.
  rewrite /survive /Rdiv.
  rewrite -plus_INR.
  rewrite (l_old_0 (x+y)); [rewrite Rmult_0_l | rewrite plus_INR]; done.
Qed.  

Lemma p_old_0' : forall (t:R) (x:nat), \ω <= x+t -> \p_{t&x} = 0.
Proof.
  move => t x Hxt.
  rewrite /survive.
  rewrite l_old_0'; lra.
Qed.

Lemma p_0_1 : forall (x : nat), x < \ω -> \p_{0&x} = 1.
Proof.
  move => x Hx.
  rewrite /survive.
  rewrite Rplus_0_r.
  rewrite /Rdiv Rinv_r //.
  apply /pos_neq0 /l_x_pos => //.
Qed.

Lemma p_0_1' : forall u:R, u < \ψ -> \p_{0 & u} = 1.
Proof.
  move => u Hu.
  rewrite /survive.
  rewrite Rplus_0_r.
  rewrite /Rdiv Rinv_r //.
  apply /pos_neq0 /l_u_pos.
    by move: psi_finite <-.
Qed.

Lemma q_omega_1 : \q_(\ω-1) = 1.
Proof.
  rewrite /die Rplus_0_r {3}/Rminus Rplus_assoc Rplus_opp_l Rplus_0_r.
  rewrite l_old_0; [| lra]; rewrite Rminus_0_r.
  rewrite /Rdiv Rinv_r //.
  apply pos_neq0.
  rewrite -(minus_INR \ω 1);
    [apply /l_x_pos /lt_INR /Nat.sub_lt => // |]; apply /INR_lt /omega_pos.
Qed.

Lemma q_defer_old_0 : forall (f t x : nat), \ω <= x+f -> \q_{f|t&x} = 0.
Proof.
  move => f t x Hxf.
  rewrite /die.
  rewrite -!plus_INR.
  rewrite (l_old_0 (x+f)%coq_nat); [| rewrite plus_INR //].
  rewrite (l_old_0 (((x+f)%coq_nat+t)%coq_nat)).
  - rewrite Rminus_0_r /Rdiv Rmult_0_l //.
  - apply /le_INR /(Nat.le_trans _ (x+f)%coq_nat);
      [apply INR_le; rewrite plus_INR; lra | lia].
Qed.

Lemma q_defer_old_0' : forall (f t u : R), 0 <= t -> \ω <= u+f -> \q_{f|t&u} = 0.
Proof.
  move => f t u H0t Homegauf.
  rewrite /die.
  have Homegauft : \ω <= u+f+t by apply (Rle_trans _ (u+f)); lra.
  rewrite (l_old_0' (u+f)) // (l_old_0' (u+f+t)) //; lra.
Qed.

Lemma e_p : forall x:nat, \e_x = \Rsum_(0 <= k < \ω-x) \p_{k+1 & x}.
Proof.
  move => x.
  rewrite /curt_life_expct.
  case: (le_lt_dec 1 (\ω-x)) => [Hdead | Halive].
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
    rewrite -(Rplus_0_r (\Rsum_(0 <= i < \ω-x) i * \p_{i&x})).
    rewrite -{2}(Rmult_0_r (\ω-x)) -{2}(p_omega_0 x).
    rewrite -(minus_INR \ω x); [| apply /Nat.lt_le_incl /(Nat.lt_add_lt_sub_r 0); rewrite /lt //].
    rewrite -(big_nat_recr (\ω-x) 0) /= ; [| rewrite /leP //].
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
  case: (le_lt_dec 2 (\ω-x)) => [Halive | Hdead].
  - have Halive0 : (0 < \ω-x)%N by apply /ltP /(Nat.lt_le_trans 0 2); [lia | done].
    have Halive1 : (1 < \ω-x)%N by apply /ltP /(Nat.lt_le_trans 1 2); [lia | done].
    rewrite -(prednK Halive0).
    rewrite big_nat_recl; [| by rewrite -Nat.pred_0; apply /leP /Nat.pred_le_mono /leP].
    rewrite Rplus_0_l.
    under eq_big_nat => i Hi.
    { rewrite Rplus_comm (p_mult 1 (i.+1)).
      - rewrite S_INR.
        over.
      - rewrite -(plus_INR x 1).
        apply /pos_neq0 /l_x_pos /lt_INR /(Nat.lt_add_lt_sub_r 0).
        rewrite Nat.sub_add_distr.
        apply lt_minus_O_lt.
        move /ltP in Halive1.
        rewrite -SSR_minus //. }
    rewrite -big_distrr.
    rewrite -{1}(Rmult_1_r (\p_x)).
    rewrite -Rmult_plus_distr_l.
      by rewrite -Nat.sub_1_r -SSR_minus -subnDA e_p plus_INR.
  - apply (Nat.lt_succ_r (\ω - x)) in Hdead.
    apply Nat.le_1_r in Hdead.
    destruct Hdead as [H0 | H1].
    + rewrite H0.
      rewrite big_geq //.
      rewrite (p_old_0 x 1); [rewrite Rmult_0_l // |].
      apply Nat.sub_0_le in H0.
      rewrite -plus_INR; apply /le_INR /(Nat.le_trans _ x) => //; lia.
    + rewrite H1.
      rewrite big_nat1 Rplus_0_l.
      rewrite e_p subnDA H1 SSR_minus Nat.sub_diag.
      rewrite big_geq //.
      rewrite Rplus_0_r Rmult_1_r //.
Qed.
    
End FiniteLifeTable.

(****************************************************************************************)

Section DifferentiableLifeTable.

(* Suppose l is continuously differentiable. *)
Hypothesis l_C1 : forall u:R, ex_derive l u /\ continuous (Derive l) u.

Lemma ex_derive_l : forall u:R, ex_derive l u.
Proof.
  apply l_C1.
Qed.

Hint Resolve ex_derive_l : core.

Lemma continuous_l : forall u:R, continuous l u.
Proof.
  move => u.
  apply (ex_derive_continuous l u) => //.
Qed.

Hint Resolve continuous_l : core.

Lemma continuous_Derive_l : forall u:R, continuous (Derive l) u.
Proof.
  apply l_C1.
Qed.

Hint Resolve continuous_Derive_l : core.

Lemma continuous_p_fst : forall t u : R, Rbar_lt u \ψ -> continuous (fun s:R => \p_{ s & u }) t.
Proof.
  move => t u Hupsi.
  rewrite /survive /Rdiv.
  apply (continuous_comp (Rplus u) (fun r:R => \l_r */ \l_u)).
  - apply continuous_Rplus_snd.
  - apply (continuous_scal_l _ (/ \l_u)); auto.
Qed.

Lemma continuous_mu :  forall u:R, Rbar_lt u \ψ -> continuous (fun v:R => \μ_v) u.
Proof.
  move => u Hu.
  rewrite /d_force /Rdiv.
  apply (continuous_mult (fun v:R => - Derive l v)).
  - apply (continuous_opp (Derive l)); auto.
  - by apply (continuous_Rinv_comp); last apply /pos_neq0 /l_u_pos.
Qed.

Lemma mu_Derive_ln : forall u:R, Rbar_lt u \ψ -> \μ_u = - Derive (fun v:R => ln \l_v) u.
Proof.
  move => u Hu.
  rewrite Derive_comp; try auto_derive; auto.
  rewrite Derive_ln; auto.
  rewrite /d_force; lra.
Qed.

Lemma RInt_mu_ln : forall u:R, 0 <= u -> Rbar_lt u \ψ ->
  RInt (fun v:R => \μ_v) 0 u = -ln(\l_u / \l_0).
Proof.
  move => u H0u Hupsi.
  have H0v : forall v:R, Rmin 0 u < v -> 0 < v.
  { move => v Huv.
    rewrite (_ : 0 = Rmin 0 u); [apply Huv |].
    rewrite /Rmin.
    case Rle_dec => [_ | Hn0u] //. }
  have Hvpsi : forall v:R, v <= Rmax 0 u -> Rbar_lt v \ψ.
  { move => v Hvu.
    eapply Rbar_le_lt_trans; [| apply Hupsi].
    rewrite (_ : u = Rmax 0 u); [apply Hvu |].
    rewrite /Rmax.
    case Rle_dec => [_ | Hn0u] //. }
  have HC0Dlnl : forall v:R, Rbar_lt v \ψ -> continuous (Derive (fun w : R => ln \l_ w)) v.
  { move => v Hv.
    apply (continuous_ext_loc _ (fun w:R => - \μ_w));
      [| by apply /(continuous_opp (d_force l)) /continuous_mu].
    have Hexball : exists eps:posreal, Rbar_lt (v + eps) \ψ.
    { move: Hv.
      case: \ψ => [r Hur | Hpsi_p_infty | Hpsi_m_infty].
      - have Hepsilon_pos : 0 < (r-v)/2 by rewrite /= in Hur; lra.
        exists (mkposreal ((r-v)/2) Hepsilon_pos) => /=; lra.
      - have Hepsilon_pos : 0 < 1 by lra.
        exists (mkposreal 1 Hepsilon_pos); auto.
      - contradiction. }
    destruct Hexball as [eps Heps].
    exists eps => /= w Hw.
    rewrite mu_Derive_ln; [lra |].
    apply (Rbar_lt_trans _ (v + eps)) => //=.
    suff H : w - v < eps; [lra |].
    apply (Rle_lt_trans _ (Rabs (w-v))); [apply Rle_abs | auto]. }
  under RInt_ext => v Hv.
  { rewrite mu_Derive_ln; [| apply Hvpsi; lra].
    rewrite -(Rmult_1_l (Derive _ _)) Ropp_mult_distr_l.
    over. }
  rewrite RInt_scal.
  - rewrite RInt_Derive.
    + rewrite ln_div; auto; rewrite /scal /= /mult /= -Ropp_mult_distr_l Rmult_1_l //.
    + move => v Hv.
      apply ex_derive_comp; auto.
      auto_derive.
      apply /l_u_pos /Hvpsi; lra.
    + move => v Hv.
      apply /HC0Dlnl /Hvpsi; lra.
  - apply ex_RInt_continuous => w Hw.
    apply /HC0Dlnl /Hvpsi; lra.
Qed.

Lemma l_exp_RInt_mu : forall u:R, 0 <= u -> Rbar_lt u \ψ ->
  \l_u = \l_0 * exp (- RInt (fun v:R => \μ_v) 0 u).
Proof.
  move => u H0u Hupsi.
  rewrite RInt_mu_ln // Ropp_involutive.
  rewrite exp_ln.
  - field; apply /pos_neq0 /l_u_pos /(Rbar_le_lt_trans _ u); auto.
  - apply Rdiv_lt_0_compat; auto.
Qed.

Lemma p_exp_RInt_mu : forall (t u : R), 0 <= t -> 0 <= u -> Rbar_lt (u+t) \ψ ->
  \p_{t & u} = exp (- RInt (fun v:R => \μ_v) u (u+t)).
Proof.
  move => t u H0t H0u Hutpsi.
  have HC0mu : forall v:R, v <= (u+t) -> continuous [eta d_force l] v.
  { move => v Hv.
    apply continuous_mu.
    apply (Rbar_le_lt_trans _ (u+t)) => //. }
  rewrite /survive.
  rewrite (l_exp_RInt_mu (u+t)) //; [| lra].
  rewrite (l_exp_RInt_mu u) //; [| apply (Rbar_le_lt_trans _ (u+t)) => //=; lra].
  rewrite /Rdiv Rinv_mult_distr; auto; [| apply /pos_neq0 /exp_pos].
  rewrite -!Rmult_assoc (Rmult_comm \l_0) (Rmult_assoc _ \l_0) Rinv_r;
    auto; rewrite Rmult_1_r.
  rewrite -exp_Ropp -exp_plus -Ropp_plus_distr.
  rewrite (_ : - RInt [eta d_force l] 0 u = opp (RInt [eta d_force l] 0 u)) //.
  rewrite opp_RInt_swap;
    [| apply /ex_RInt_continuous => v Hv; apply HC0mu; rewrite Rmax_right in Hv; lra].
  rewrite (Rplus_comm (RInt _ _ _)).
  rewrite (_ : RInt [eta d_force l] u 0 + RInt [eta d_force l] 0 (u + t) =
               plus (RInt [eta d_force l] u 0) (RInt [eta d_force l] 0 (u + t))) //.
  rewrite RInt_Chasles //; apply ex_RInt_continuous => v Hv; apply HC0mu;
    [rewrite Rmax_left in Hv | rewrite Rmax_right in Hv]; lra.
Qed.

Lemma q_exp_RInt_mu : forall (t u : R), 0 <= t -> 0 <= u -> Rbar_lt (u+t) \ψ ->
  \q_{t & u} = 1 - exp (- RInt (fun v:R => \μ_v) u (u+t)).
Proof.
  move => t u H0t H0u Hutpsi.
  have Hupsi : Rbar_lt u \ψ by apply (Rbar_le_lt_trans _ (u+t)); [rewrite /=; lra | auto].
  rewrite -(p_q_1 t u); auto.
  rewrite p_exp_RInt_mu; auto; lra.
Qed.

Lemma mu_incr : forall (u s : R), Rbar_lt (u+s) \ψ ->
  \μ_(u+s) = - (Derive (fun r:R => \l_(u+r)) s) / \l_(u+s).
Proof.
  move => u s Huspsi.
  rewrite Derive_incr; auto.
Qed.

Lemma RInt_l_mu : forall (u t : R), 0 <= t -> Rbar_lt (u+t) \ψ ->
  \l_u - \l_(u+t) = RInt (fun s:R => \l_(u+s) * \μ_(u+s)) 0 t.
Proof.
  move => u t H0t Hutpsi.
  have HDC0 : forall s:R, s <= t -> continuous (Derive (fun r : R => \l_ (u + r))) s.
  { move => s Hs.
    apply (continuous_ext (fun r:R => (Derive l) (u+r))).
    - move => r.
      rewrite Derive_incr; auto.
    - apply continuous_comp; auto; apply continuous_Rplus_snd. }
  under RInt_ext => s [H0s Hst].
  { rewrite Rmax_right in Hst; [| lra].
    have Huspsi :  Rbar_lt (u + s) \ψ
      by apply (Rbar_lt_trans _ (u+t)); [ rewrite /=; lra | auto].
    rewrite mu_incr //.
    rewrite /Rdiv Rmult_comm Rmult_assoc Rinv_l; auto; rewrite Rmult_1_r.
    rewrite -(Rmult_1_l (Derive _ _)) Ropp_mult_distr_l.
    over. }
  rewrite RInt_scal.
  - rewrite RInt_Derive.
    + rewrite Rplus_0_r /scal /= /mult /=; lra.      
    + move => s _.
      auto_derive; auto.
    + move => s [_ Hst].
      rewrite Rmax_right in Hst; [| lra].
        by apply HDC0.
  - apply ex_RInt_continuous => s [_ Hst].
    rewrite Rmax_right in Hst; [| lra].
      by apply HDC0.
Qed.

Lemma q_RInt_p_mu : forall (f u t : R), 0 <= f -> 0 <= t -> Rbar_lt (u+f+t) \ψ ->
  \q_{f|t & u} = RInt (fun s:R => \p_{s & u} * \μ_(u+s)) f (f+t).
Proof.
  move => f u t H0f H0t Huftpsi.
  rewrite /die.
  rewrite RInt_l_mu //.
  rewrite /Rdiv Rmult_comm.
  rewrite (_ : / \l_ u * RInt (fun s : R => \l_ (u + f + s) * \μ_ (u + f + s)) 0 t =
               scal (/ \l_u) (RInt (fun s : R => \l_ (u + f + s) * \μ_ (u + f + s)) 0 t));
    [| rewrite /scal /= /mult //=].
  rewrite -RInt_scal.
  - rewrite /scal /= /mult /=.
    under RInt_ext => s _.
    { rewrite -Rmult_assoc (Rmult_comm (/ \l_u)) -/(Rdiv \l_(u+s) \l_u) Rplus_assoc.
      rewrite -/(Rdiv _ \l_u) -/(survive _ (f+s) u).
      rewrite !(Rplus_comm f s).
      over. }
    rewrite (@RInt_comp_plus _ (fun r:R => \p_{r&u} * \μ_(u+r))).
    + rewrite Rplus_0_l (Rplus_comm f t) //.
    + apply ex_RInt_continuous => r Hr.
      apply (continuous_mult (fun s:R => \p_{s&u})).
      * apply continuous_p_fst.
        apply (Rbar_le_lt_trans _ (u+f+t)); [rewrite /=; lra | auto].
      * apply (continuous_comp (Rplus u) (d_force l)); [apply continuous_Rplus_snd |].
        apply continuous_mu.
        destruct Hr as [_ Hrtf].
        rewrite Rmax_right in Hrtf; [| lra].
        rewrite Rplus_comm in Hrtf.
        apply (Rbar_le_lt_trans _ (u+f+t)); [rewrite /=; lra | auto].
  - apply ex_RInt_continuous => s [_ Hst].
    rewrite Rmax_right in Hst; [| lra].
    apply (continuous_mult (fun r:R => \l_(u+f+r))).
    + apply continuous_comp; [apply continuous_Rplus_snd | auto].
    + apply continuous_comp; [apply continuous_Rplus_snd | apply continuous_mu].
      apply (Rbar_le_lt_trans _ (u+f+t)); [rewrite /=; lra | auto].
Qed.

Lemma q_imm_RInt_p_mu : forall (u t : R), 0 <= t -> Rbar_lt (u+t) \ψ ->
  \q_{t & u} = RInt (fun s:R => \p_{s & u} * \μ_(u+s)) 0 t.
Proof.
  move => u t H0t Hutpsi.
    by rewrite (q_RInt_p_mu 0); try lra; rewrite ?Rplus_assoc Rplus_0_l.
Qed.  

End DifferentiableLifeTable.

(****************************************************************************************)

Section FiniteDefferentiableLifeTable.

Hypothesis l_fin : (l_finite l).
Hypothesis l_C1 : forall u:R, ex_derive l u /\ continuous (Derive l) u.

Notation "\ω" := (\ω[l,l_fin]) (at level 8).
Notation "\e_ x" := (\e[l,l_fin]_ x) (at level 9).
Notation "\e`o_{ u : t }" := (\e`o[l,l_fin]_{u:t}) (at level 9, u at level 9).
Notation "\e`o_ u" := (\e`o[l,l_fin]_u) (at level 9).

Hint Resolve ex_derive_l continuous_l continuous_Derive_l : core.
Hint Resolve l_omega_0 psi_finite omega_pos le_psi_omega l_old_0 : core.

Lemma l_psi_0 : \l_\ψ = 0.
Proof.
  case: (Req_dec \l_\ψ 0) => // Hlpsineq0.
  apply False_ind.
  set (K := (fun u:R => \l_u = 0)).
  have HpsiCK : (complementary K) \ψ by [].
  have : closed_set K.
  { rewrite (_ : K = image_rec l (eq^~ 0)) //.
    apply continuity_closed; [apply eq_R_continuous; auto |].
    apply Rsingleton_closed. }
  apply/open_set_P1 => HKclosed.
  have HpsiNBH : neighbourhood (complementary K) \ψ
    by rewrite -/(interior _ \ψ); apply HKclosed.
  rewrite /neighbourhood in HpsiNBH.
  case: HpsiNBH => eps Hdisk.
  destruct eps as [eps Hepspos].
  suff Hlneq0 : \l_(\ψ+eps/2) <> 0.
  - apply Hlneq0.
    apply l_out_0.
    rewrite -psi_finite //=; lra.
  - apply Hdisk.
    rewrite /disc.
    rewrite (_ : \ψ + eps/2 - \ψ = eps/2) /=; try lra.
    rewrite Rabs_pos_eq; lra.
Qed.

Lemma l_0_equiv : forall u:R, \l_u = 0 <-> \ψ <= u.
Proof.
  move => u.
  split.
  - move => Hlu0.
    apply Rnot_lt_le.
    contradict Hlu0.
    apply /pos_neq0 /l_u_pos.
    rewrite -psi_finite //=.
  - case.
    + move: (l_out_0 u).
      rewrite -psi_finite //=.
    + by move <-; rewrite l_psi_0.
Qed.

Lemma l_pos_equiv : forall u:R, 0 < \l_u <-> u < \ψ.
Proof.
  move => u; split.
  - move => Hlupos.
    apply Rnot_le_lt => /l_0_equiv; lra.
  - move => Hu.
    apply Rnot_le_lt => /Rle_antisym /(_ (l_nonneg _)) /l_0_equiv; lra.
Qed.

Lemma lt_omega_lt_psi : forall x:nat, x < \ω -> x < \ψ.
Proof.
  move => x /l_x_pos; apply l_pos_equiv.
Qed.

Lemma l_u_nbh_pos : forall u:R, u < \ψ -> exists eps:posreal, 0 < \l_(u + eps).
Proof.
  move => u Hu.
  have Hu' : Rbar_lt u \ψ by rewrite -psi_finite.
  move: (l_u_pos u Hu') => Hlu.
  have Hlu2 : 0 < \l_u / 2 by lra.
  have HuC0 : continuity_pt l u by apply continuity_pt_continuous; auto.
  set (Blu := open_interval (\l_u / 2) (\l_u * 3/2)).
  have HBlunbh : neighbourhood Blu \l_u
    by exists (mkposreal (\l_u / 2) Hlu2) => v;
      rewrite /disc /Blu /open_interval /=; move /Rabs_def2; lra.
  case: (continuity_P1 l u) => /(_ HuC0 _ HBlunbh).
  case => V; case; case; move => [r Hr] HDuV HVBlu _.
  have Hr2 : 0 < r/2 by lra.
  exists (mkposreal (r/2) Hr2) => /=.
  eapply Rlt_trans; [apply Hlu2 |].
  apply HVBlu.
  apply HDuV.
  rewrite /disc.
  apply Rabs_def1 => /=; lra.
Qed.

Lemma p_old_0'' : forall (t u : R), \ψ <= u + t -> \p_{t & u} = 0.
Proof.
  move => t u Hut.
  rewrite /survive.
  case: (l_0_equiv (u+t)) => _ ->; lra.
Qed.  

Lemma continuous_p_fst' : forall (t:R) (x:nat), x < \ω -> continuous (fun s:R => \p_{ s & x }) t.
Proof.
  move => t x Hxomega.
  rewrite /survive /Rdiv.
  apply (continuous_comp (Rplus x) (fun r:R => \l_r */ \l_x)).
  - apply continuous_Rplus_snd.
  - apply (continuous_scal_l _ (/ \l_x)); auto.
Qed.

Lemma temp_compl_expct : forall u:R, \e`o_u = \e`o_{u : \ψ-u}.
Proof.
  move => u.
  rewrite /temp_life_expct /life_expct.
  rewrite RInt_point /zero /=; lra.
Qed.

Lemma temp_life_expct_RInt_p : forall (u t : R), u < \ψ -> 0 <= t -> u+t <= \ψ ->
  \e`o_{u:t} = RInt (fun s:R => \p_{s&u}) 0 t.
Proof.
  move => u t Hupsi H0t Hutpsi.
  have Hutpsi' : Rbar_le (u+t) \ψ by rewrite -psi_finite //=.
  have HC0scall : forall r:R, continuous (fun s : R => / \l_ u * \l_ s) r.
  { move => r.
    rewrite (_ : Rmult = scal) //.
    apply (continuous_scal_r (/ \l_u) l); auto. }
  rewrite /temp_life_expct.
  have HRInt0t : RInt (fun s:R => -s * Derive l (u+s) / \l_u) 0 t =
                 RInt (fun s:R => \p_{ s & u}) 0 t + - t * \p_{t & u}.
  { under RInt_ext => s _.
    { rewrite Rplus_comm Rmult_comm.
      rewrite /Rdiv Rmult_assoc -Ropp_mult_distr_l (Rmult_comm s).
      rewrite -{2}(Ropp_r_simpl_l u s).
      over. }
    rewrite (@RInt_comp_plus _ (fun r:R => scal (Derive l r) (- (/ \l_u * (r-u))))) Rplus_0_l.
    - rewrite (@RInt_scal_Derive_l l (fun r:R => - (/ \l_ u * (r - u)))); auto.
      + rewrite /minus /scal /plus /opp /= /mult /=.
        rewrite (_ : t + u - u = t + (u - u)); try lra.
        rewrite !Rminus_eq_0 Rplus_0_r Rmult_0_r -!Ropp_mult_distr_r
                Rmult_0_r Ropp_involutive Rplus_0_r.
        under RInt_ext => s Hs.
        { rewrite Derive_opp Derive_scal Derive_minus; try auto_derive; auto;
            rewrite Derive_id Derive_const Rminus_0_r Rmult_1_r.
          rewrite Rmult_comm -Ropp_mult_distr_l (_ : Ropp = opp) //.
          over. }
        rewrite RInt_opp /opp /=; [| apply ex_RInt_continuous => s _; auto].
        rewrite Ropp_involutive -{4}(Rplus_0_l u) -RInt_comp_plus;
          [| apply ex_RInt_continuous => s _; auto].
        under RInt_ext => s _ do
          rewrite Rmult_comm Rplus_comm -/(Rdiv _ \l_u) -/(survive l s u).
        rewrite (_ : - (\l_ (t + u) * (/ \l_ u * t)) = -t * \p_{t&u})
                /survive /Rdiv Rplus_comm; lra.
      + move => s _; auto_derive; auto.
      + move => s _.
        apply (continuous_ext (fun _ => - / \l_u)); [| apply continuous_const].
        move => r.
        rewrite Derive_opp Derive_scal Derive_minus; try auto_derive; auto.
        rewrite Derive_id Derive_const; lra.
    - apply ex_RInt_continuous => s Hs.
      apply continuous_mult; auto.
      rewrite (_ : Ropp = opp) //; apply (continuous_opp (fun y:R => / \l_ u * (y - u))).
      rewrite (_ : Rmult = scal) //; apply (continuous_scal_r _ (fun y:R => (y-u))).
      apply continuous_Rminus_fst. }
  have HRInttpsiu :
    RInt (fun s:R => -t * Derive l (u+s) / \l_u) t (\ψ-u) = t * \p_{t&u}.
  { under RInt_ext => s _.
    { rewrite Rplus_comm /Rdiv.
      rewrite Rmult_assoc (Rmult_comm (Derive _ _)) -Rmult_assoc -Ropp_mult_distr_l.
      over. }
    rewrite (@RInt_comp_plus _ (fun s:R => -(t * / \l_u) * (Derive l s)))
      (_ : \ψ-u+u = \ψ); try lra.
    - rewrite {1}(_ : Rmult = scal) //.
      rewrite RInt_scal; [| apply ex_RInt_continuous; auto].
      rewrite RInt_Derive; auto.
      rewrite l_psi_0 Rminus_0_l /scal /= /mult /= Rmult_opp_opp.
      rewrite /survive Rplus_comm; field.
      apply /pos_neq0 /l_u_pos.
      rewrite -psi_finite //=; lra.
    - apply ex_RInt_continuous => s _.
      apply (continuous_scal_r _ (fun r:R => Derive l r)); auto. }
  rewrite HRInt0t HRInttpsiu; lra.
Qed.

Lemma life_expct_RInt_p : forall u:R, u < \ψ ->
  \e`o_u = RInt (fun s:R => \p_{s&u}) 0 (\ψ-u).
Proof.
  move => u Hupsi.
  rewrite temp_compl_expct.
  rewrite temp_life_expct_RInt_p; lra.
Qed.

End FiniteDefferentiableLifeTable.

End LifeTable.
