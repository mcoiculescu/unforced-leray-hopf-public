import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.CompactDuhamelNorm.WindowSide

/-!
# `PartII-b:F2/4/3` (`CompactDuhamelNorm.lean`): Compact-Duhamel operator-norm convergence

Source of record: `the November 2 reference manuscript` (SP), lines 978–1003
(`lem:short-compact-duhamel`), 2104–2115, 2141–2150 (`short-bg:compact-duhamel`).

Proves `compactDuhamelNormConvergence_proof : UnforcedLeray.Short.IIb.CompactDuhamelNormConvergence`
by contradiction along a counterexample sequence `δ_k = ν₀_k = 1 / (k + 1)`:
1. Extract a subsequence along which the slow age `σ_n = ν_n t_n ∈ [0, Sig]` converges to `σ*`,
   shifting the index so `p_n.H ≥ Lmax` and `‖Sc_n‖ ≤ 2` hold for all `n`;
2. On the shifted window `[t'_n, t'_n + Lmax] ⊆ [0, p_n.H]` with `t'_n = min t_n (p_n.H - Lmax)`,
   apply `RCDuhamel.real_compact_duhamel_window` on `Xm m` with limit `(T_pl σ*, AplOp σ*, E_pl σ*)`;
3. Combine with `planar_diff_tendsto` (`RCDuhamel.real_compact_duhamel` on the frozen planar family
   along `σ_n → σ*`) to contradict `> η`.
-/

set_option autoImplicit false

open Set MeasureTheory Filter Topology Real Metric

open UnforcedLeray.Short.IIb UnforcedLeray.Short.IIb.CompactDuhamelNormHelp
  UnforcedLeray.Cons.C03.Concrete in
theorem compactDuhamelNormConvergence_proof :
    UnforcedLeray.Short.IIb.CompactDuhamelNormConvergence := by
  intro m hm Sig Lmax hSig hLmax C_Sg AplOp hC_Sg hAcont hAop _hAtb _hAball
    T_pl E_pl hT hEcont hEmild dm dp hdm hFree η hη
  by_contra hnot
  let rk : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hrk_pos : ∀ k, 0 < rk k := fun k => by dsimp [rk]; positivity
  have hrk_le1 : ∀ k, rk k ≤ 1 := fun k => by
    dsimp [rk]
    rw [div_le_iff₀ (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hrk_lim : Tendsto rk atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- Step 1: Counterexample sequence for `δ = ν₀ = 1 / (k + 1)`.
  have hcounter : ∀ k : ℕ, ∃ (p : Params) (d : ℝ),
      BgRegime p d dm dp ∧ p.ν ≤ rk k ∧ p.ageCut = Sig ∧ TrainCloseM m p.train Sig (rk k) ∧
      ∃ (Sc U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
        (Ac : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)),
        IsCoupledDuhamelPropagator m p Sc Ac U ∧
        (∀ s ∈ Icc 0 p.H,
          ‖(Jc p.c m).comp ((Ac s).comp (Rc p.c m)) - AplOp (p.ν * s)‖ ≤
            C_Sg * (p.c ^ (-2 : ℝ) + rk k)) ∧
        ∃ t L : ℝ, 0 ≤ t ∧ 0 ≤ L ∧ L ≤ Lmax ∧ t + L ≤ p.H ∧
          η < ‖(Jc p.c m).comp ((U (t + L) t - Sc (t + L) t).comp (Rc p.c m)) -
              (E_pl (p.ν * t) L - T_pl (p.ν * t) L)‖ := by
    intro k
    by_contra hk
    apply hnot
    refine ⟨rk k, rk k, hrk_pos k, hrk_le1 k, hrk_pos k, hrk_le1 k, ?_⟩
    intro p d hbg hν hAge hTCM Sc U Ac hCD hAc t L ht hL hLL htL
    by_contra hlt
    exact hk ⟨p, d, hbg, hν, hAge, hTCM, Sc, U, Ac, hCD, hAc, t, L, ht, hL, hLL, htL,
      lt_of_not_ge hlt⟩
  choose pk dk hrest using hcounter
  have hbgk : ∀ k, BgRegime (pk k) (dk k) dm dp := fun k => (hrest k).1
  have hνk : ∀ k, (pk k).ν ≤ rk k := fun k => (hrest k).2.1
  have hAgek : ∀ k, (pk k).ageCut = Sig := fun k => (hrest k).2.2.1
  have hTCMk : ∀ k, TrainCloseM m (pk k).train Sig (rk k) := fun k => (hrest k).2.2.2.1
  choose Sck Uk Ack hCDk hAck hrest2 using fun k => (hrest k).2.2.2.2
  choose tk Lk htk0 hLk0 hLkL htLk hbadk using hrest2
  have hHk : ∀ k, (pk k).H = Sig / (pk k).ν := fun k => by
    change (pk k).ageCut / (pk k).ν = Sig / (pk k).ν
    rw [hAgek k]
  have hσk_mem : ∀ k, (pk k).ν * tk k ∈ Icc 0 Sig := by
    intro k
    have hν0 : 0 < (pk k).ν := (pk k).ν_pos
    refine ⟨mul_nonneg hν0.le (htk0 k), ?_⟩
    have htH : tk k ≤ Sig / (pk k).ν := hHk k ▸ (by linarith [hLk0 k, htLk k] : tk k ≤ (pk k).H)
    calc (pk k).ν * tk k ≤ (pk k).ν * (Sig / (pk k).ν) := mul_le_mul_of_nonneg_left htH hν0.le
      _ = Sig := mul_div_cancel₀ Sig hν0.ne'
  -- Step 2: Subsequence with `σ_k → σ*` and shift `N₀` so `p_n.H ≥ Lmax` and `‖Sc_n‖ ≤ 2` for all `n`.
  obtain ⟨σstar, hσstar, φ, hφ_mono, hφ_lim⟩ := isCompact_Icc.tendsto_subseq hσk_mem
  obtain ⟨δ₁, ν₁, hδ₁, _hδ₁1, hν₁, _hν₁1, hFree1⟩ := hFree ∅ isCompact_empty 1 one_pos
  set r_thresh : ℝ := min (min δ₁ ν₁) (Sig / Lmax)
  have hr_thresh : 0 < r_thresh := lt_min (lt_min hδ₁ hν₁) (div_pos hSig hLmax)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (Metric.tendsto_nhds.1 hrk_lim r_thresh hr_thresh)
  let idx : ℕ → ℕ := fun n => φ (n + N₀)
  have hidx_ge : ∀ n, N₀ ≤ idx n := fun n =>
    le_trans (Nat.le_add_left N₀ n) (hφ_mono.id_le (n + N₀))
  have hidx_atTop : Tendsto idx atTop atTop :=
    Filter.tendsto_atTop.2 fun B => Filter.eventually_atTop.2
      ⟨B, fun n hn => le_trans hn (le_trans (Nat.le_add_right n N₀) (hφ_mono.id_le (n + N₀)))⟩
  have hshift_atTop : Tendsto (fun n : ℕ => n + N₀) atTop atTop :=
    Filter.tendsto_atTop.2 fun B => Filter.eventually_atTop.2
      ⟨B, fun n hn => le_trans hn (Nat.le_add_right n N₀)⟩
  let pn : ℕ → Params := fun n => pk (idx n)
  let dn : ℕ → ℝ := fun n => dk (idx n)
  let rn : ℕ → ℝ := fun n => rk (idx n)
  let Scn : ∀ n, ℝ → ℝ → (Xmc (pn n).c m →L[ℝ] Xmc (pn n).c m) := fun n => Sck (idx n)
  let Un : ∀ n, ℝ → ℝ → (Xmc (pn n).c m →L[ℝ] Xmc (pn n).c m) := fun n => Uk (idx n)
  let Acn : ∀ n, ℝ → (Xmc (pn n).c m →L[ℝ] Xmc (pn n).c m) := fun n => Ack (idx n)
  let tn : ℕ → ℝ := fun n => tk (idx n)
  let Ln : ℕ → ℝ := fun n => Lk (idx n)
  let σn : ℕ → ℝ := fun n => (pn n).ν * tn n
  have hσn_mem : ∀ n, σn n ∈ Icc 0 Sig := fun n => hσk_mem (idx n)
  have hσn_lim : Tendsto σn atTop (nhds σstar) := hφ_lim.comp hshift_atTop
  have hrn_lim : Tendsto rn atTop (nhds 0) := hrk_lim.comp hidx_atTop
  have hrn_lt : ∀ n, rn n < r_thresh := by
    intro n
    have h := hN₀ (idx n) (hidx_ge n)
    rwa [Real.dist_eq, sub_zero, abs_of_pos (hrk_pos (idx n))] at h
  have hrn_le1 : ∀ n, rn n ≤ 1 := fun n => hrk_le1 (idx n)
  have hνn_pos : ∀ n, 0 < (pn n).ν := fun n => (pn n).ν_pos
  have hνn_le_rn : ∀ n, (pn n).ν ≤ rn n := fun n => hνk (idx n)
  have hνn_le1 : ∀ n, (pn n).ν ≤ 1 := fun n => (hνn_le_rn n).trans (hrn_le1 n)
  have hνn_lim : Tendsto (fun n => (pn n).ν) atTop (nhds 0) :=
    squeeze_zero (fun n => (hνn_pos n).le) hνn_le_rn hrn_lim
  have hLmax_le_H : ∀ n, Lmax ≤ (pn n).H := by
    intro n
    have h1 : (pn n).ν ≤ Sig / Lmax :=
      (hνn_le_rn n).trans ((hrn_lt n).le.trans (min_le_right _ _))
    rw [hHk (idx n), le_div_iff₀ (hνn_pos n)]
    calc Lmax * (pn n).ν ≤ Lmax * (Sig / Lmax) := mul_le_mul_of_nonneg_left h1 hLmax.le
      _ = Sig := mul_div_cancel₀ Sig hLmax.ne'
  -- Step 3: Window start `t'_n = min t_n (p_n.H - Lmax)` and lifted window families on `[0, Lmax]`.
  let t'n : ℕ → ℝ := fun n => min (tn n) ((pn n).H - Lmax)
  have ht'n0 : ∀ n, 0 ≤ t'n n := fun n => le_min (htk0 (idx n)) (sub_nonneg.2 (hLmax_le_H n))
  have ht'n_le_tn : ∀ n, t'n n ≤ tn n := fun _ => min_le_left _ _
  have ht'nH : ∀ n, t'n n + Lmax ≤ (pn n).H := fun n =>
    add_le_of_le_sub_right (min_le_right (tn n) ((pn n).H - Lmax))
  have htnLn_le : ∀ n, tn n + Ln n ≤ t'n n + Lmax := fun n => by
    have h1 : tn n + Ln n - Lmax ≤ tn n := sub_le_iff_le_add.2 (add_le_add_right (hLkL (idx n)) (tn n))
    have h2 : tn n + Ln n - Lmax ≤ (pn n).H - Lmax := sub_le_sub_right (htLk (idx n)) Lmax
    exact sub_le_iff_le_add.1 (le_min h1 h2)
  have htn_sub_le : ∀ n, tn n - t'n n ≤ Lmax := fun n =>
    sub_le_iff_le_add'.2 ((le_add_of_nonneg_right (hLk0 (idx n))).trans (htnLn_le n))
  have hwin_age_mem : ∀ n, ∀ r ∈ Icc 0 Lmax, (pn n).ν * (t'n n + r) ∈ Icc 0 Sig := by
    intro n r hr
    have htr0 : 0 ≤ t'n n + r := add_nonneg (ht'n0 n) hr.1
    have htrH : t'n n + r ≤ Sig / (pn n).ν :=
      hHk (idx n) ▸ (add_le_add_right hr.2 (t'n n)).trans (ht'nH n)
    refine ⟨mul_nonneg (hνn_pos n).le htr0, ?_⟩
    calc (pn n).ν * (t'n n + r) ≤ (pn n).ν * (Sig / (pn n).ν) :=
          mul_le_mul_of_nonneg_left htrH (hνn_pos n).le
      _ = Sig := mul_div_cancel₀ Sig (hνn_pos n).ne'
  have hwin_age_dist : ∀ n, ∀ r ∈ Icc 0 Lmax,
      |(pn n).ν * (t'n n + r) - σstar| ≤ (pn n).ν * Lmax + |σn n - σstar| := by
    intro n r hr
    have hsub_abs : |r - (tn n - t'n n)| ≤ Lmax :=
      abs_le.2 ⟨by linarith [hr.1, htn_sub_le n], by linarith [hr.2, ht'n_le_tn n]⟩
    have h1 : |(pn n).ν * (t'n n + r) - σn n| ≤ (pn n).ν * Lmax := by
      have heq : (pn n).ν * (t'n n + r) - σn n = (pn n).ν * (r - (tn n - t'n n)) := by
        dsimp [σn]; ring
      rw [heq, abs_mul, abs_of_pos (hνn_pos n)]
      exact mul_le_mul_of_nonneg_left hsub_abs (hνn_pos n).le
    have htri : |(pn n).ν * (t'n n + r) - σstar| ≤
        |(pn n).ν * (t'n n + r) - σn n| + |σn n - σstar| := by
      simpa only [sub_add_sub_cancel] using abs_add_le ((pn n).ν * (t'n n + r) - σn n) (σn n - σstar)
    exact htri.trans (add_le_add_left h1 _)
  have hage_err_lim : Tendsto (fun n => (pn n).ν * Lmax + |σn n - σstar|) atTop (nhds 0) := by
    have h1 : Tendsto (fun n => (pn n).ν * Lmax) atTop (nhds 0) := by
      simpa only [zero_mul] using hνn_lim.mul_const Lmax
    have h2 : Tendsto (fun n => |σn n - σstar|) atTop (nhds 0) :=
      tendsto_zero_iff_norm_tendsto_zero.1 (tendsto_sub_nhds_zero_iff.2 hσn_lim)
    simpa only [add_zero] using h1.add h2
  let F : ℕ → Unit → ℝ → ℝ → Xm m →L[ℝ] Xm m :=
    fun n _ τ ρ => (Jc (pn n).c m).comp ((Scn n (t'n n + τ) (t'n n + ρ)).comp (Rc (pn n).c m))
  let F₀ : Unit → ℝ → ℝ → Xm m →L[ℝ] Xm m := fun _ τ ρ => T_pl σstar (τ - ρ)
  let A : ℕ → Unit → ℝ → Xm m →L[ℝ] Xm m :=
    fun n _ r => (Jc (pn n).c m).comp ((Acn n (t'n n + r)).comp (Rc (pn n).c m))
  let A₀ : Unit → ℝ → Xm m →L[ℝ] Xm m := fun _ _ => AplOp σstar
  let U : ℕ → Unit → ℝ → ℝ → Xm m →L[ℝ] Xm m :=
    fun n _ τ ρ => (Jc (pn n).c m).comp ((Un n (t'n n + τ) (t'n n + ρ)).comp (Rc (pn n).c m))
  let U₀ : Unit → ℝ → ℝ → Xm m →L[ℝ] Xm m := fun _ τ ρ => E_pl σstar (τ - ρ)
  -- Step 4: Hypotheses of `real_compact_duhamel_window` on `[0, Lmax]`.
  have hFb : ∃ M, ∀ (n : ℕ) (p : Unit) (τ ρ : ℝ), 0 ≤ ρ → ρ ≤ τ → τ ≤ Lmax →
      ‖F n p τ ρ‖ ≤ M ∧ ‖F₀ p τ ρ‖ ≤ M := by
    refine ⟨2, fun n _ τ ρ hρ hρτ hτ => ⟨?_, ?_⟩⟩
    · have hrδ₁ : rn n ≤ δ₁ := (hrn_lt n).le.trans ((min_le_left _ _).trans (min_le_left _ _))
      have hνν₁ : (pn n).ν ≤ ν₁ :=
        (hνn_le_rn n).trans ((hrn_lt n).le.trans ((min_le_left _ _).trans (min_le_right _ _)))
      have hTCM₁ : TrainCloseM m (pn n).train Sig δ₁ :=
        PartIIbF24Sub.trainCloseM_mono (hTCMk (idx n)) hrδ₁
      have hSc := (hFree1 (pn n) (dn n) (hbgk (idx n)) hνν₁ (hAgek (idx n)) hTCM₁ (Scn n)
        (hCDk (idx n)).free_prop (t'n n + ρ) (τ - ρ)
        (add_nonneg (ht'n0 n) hρ) (sub_nonneg.2 hρτ) (sub_le_self τ hρ |>.trans hτ)
        (by have := ht'nH n; linarith)).1
      have heq : t'n n + ρ + (τ - ρ) = t'n n + τ := by ring
      rw [heq] at hSc
      exact norm_Jc_comp_Rc_le _ _ _ (by norm_num) (hSc.trans_eq (by norm_num))
    · exact (norm_T_pl_le_one hT hσstar (τ - ρ)).trans (by norm_num)
  have hF : ∀ x : Xm m, ∀ ε > 0, ∀ᶠ n in atTop, ∀ (p : Unit) (τ ρ : ℝ),
      0 ≤ ρ → ρ ≤ τ → τ ≤ Lmax → ‖F n p τ ρ x - F₀ p τ ρ x‖ < ε := by
    intro x ε hε
    let Kx : Set (Xm m) := (fun q : ℝ × ℝ => T_pl q.1 q.2 x) '' (Icc 0 Sig ×ˢ Icc 0 Lmax)
    obtain ⟨δ₂, ν₂, hδ₂, _hδ₂1, hν₂, _hν₂1, hFree2⟩ :=
      hFree Kx (isCompact_T_pl_image hm hSig hT x) (ε / 2) (half_pos hε)
    obtain ⟨δ_u, hδ_u, hage⟩ := exists_age_delta_T_pl (Lmax := Lmax) hm hSig hT x (half_pos hε)
    have hev1 : ∀ᶠ n in atTop, rn n < min δ₂ ν₂ := by
      filter_upwards [Metric.tendsto_nhds.1 hrn_lim (min δ₂ ν₂) (lt_min hδ₂ hν₂)] with n hn
      rwa [Real.dist_eq, sub_zero, abs_of_pos (hrk_pos (idx n))] at hn
    have hev2 : ∀ᶠ n in atTop, (pn n).ν * Lmax + |σn n - σstar| < δ_u := by
      filter_upwards [Metric.tendsto_nhds.1 hage_err_lim δ_u hδ_u] with n hn
      have hnn : 0 ≤ (pn n).ν * Lmax + |σn n - σstar| :=
        add_nonneg (mul_nonneg (hνn_pos n).le hLmax.le) (abs_nonneg _)
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hn
    filter_upwards [hev1, hev2] with n hn1 hn2 _ τ ρ hρ hρτ hτ
    have hL_mem : τ - ρ ∈ Icc 0 Lmax := ⟨sub_nonneg.2 hρτ, (sub_le_self τ hρ).trans hτ⟩
    have hρ_mem : ρ ∈ Icc 0 Lmax := ⟨hρ, hρτ.trans hτ⟩
    have hσ_mem : (pn n).ν * (t'n n + ρ) ∈ Icc 0 Sig := hwin_age_mem n ρ hρ_mem
    have hf_mem : T_pl ((pn n).ν * (t'n n + ρ)) (τ - ρ) x ∈ Kx :=
      ⟨((pn n).ν * (t'n n + ρ), τ - ρ), ⟨hσ_mem, hL_mem⟩, rfl⟩
    have hTCM₂ : TrainCloseM m (pn n).train Sig δ₂ :=
      PartIIbF24Sub.trainCloseM_mono (hTCMk (idx n)) (hn1.le.trans (min_le_left _ _))
    have hν₂' : (pn n).ν ≤ ν₂ := (hνn_le_rn n).trans (hn1.le.trans (min_le_right _ _))
    have hfr := (hFree2 (pn n) (dn n) (hbgk (idx n)) hν₂' (hAgek (idx n)) hTCM₂ (Scn n)
      (hCDk (idx n)).free_prop (t'n n + ρ) (τ - ρ) (add_nonneg (ht'n0 n) hρ) hL_mem.1 hL_mem.2
      (by have := ht'nH n; linarith)).2 _ hf_mem
    have hcont_step : ‖T_pl ((pn n).ν * (t'n n + ρ)) (τ - ρ) x - T_pl σstar (τ - ρ) x‖ < ε / 2 :=
      hage hσ_mem hσstar ⟨(neg_nonpos.2 hLmax.le).trans hL_mem.1, hL_mem.2⟩
        ((hwin_age_dist n ρ hρ_mem).trans_lt hn2)
    exact lifted_free_apply_sub_lt hT (Scn n) hσ_mem x hfr hcont_step
  have hFadj : ∀ x : Xm m, ∀ ε > 0, ∀ᶠ n in atTop, ∀ (p : Unit) (τ ρ : ℝ),
      0 ≤ ρ → ρ ≤ τ → τ ≤ Lmax →
        ‖ContinuousLinearMap.adjoint (F n p τ ρ) x -
          ContinuousLinearMap.adjoint (F₀ p τ ρ) x‖ < ε := by
    intro x ε hε
    set D : ℝ := 3 * ‖x‖ ^ 2 + 2 * ‖x‖ + 1
    have hD_pos : 0 < D := by positivity
    set ε₁ : ℝ := min 1 ((ε / 3) ^ 2 / D)
    have hε₁_pos : 0 < ε₁ := lt_min one_pos (div_pos (pow_pos (by positivity) 2) hD_pos)
    have hε₁_le1 : ε₁ ≤ 1 := min_le_left _ _
    have hDε₁ : D * ε₁ ≤ (ε / 3) ^ 2 := by
      calc D * ε₁ ≤ D * ((ε / 3) ^ 2 / D) := mul_le_mul_of_nonneg_left (min_le_right _ _) hD_pos.le
        _ = (ε / 3) ^ 2 := mul_div_cancel₀ _ hD_pos.ne'
    obtain ⟨δ₂, ν₂, hδ₂, _hδ₂1, hν₂, _hν₂1, hFree2⟩ :=
      hFree {x} isCompact_singleton ε₁ hε₁_pos
    obtain ⟨δ_u, hδ_u, hage⟩ :=
      exists_age_delta_T_pl (Lmax := Lmax) hm hSig hT x (by positivity : 0 < ε / 3)
    have hev1 : ∀ᶠ n in atTop, rn n < min δ₂ ν₂ := by
      filter_upwards [Metric.tendsto_nhds.1 hrn_lim (min δ₂ ν₂) (lt_min hδ₂ hν₂)] with n hn
      rwa [Real.dist_eq, sub_zero, abs_of_pos (hrk_pos (idx n))] at hn
    have hev2 : ∀ᶠ n in atTop, (pn n).ν * Lmax + |σn n - σstar| < δ_u := by
      filter_upwards [Metric.tendsto_nhds.1 hage_err_lim δ_u hδ_u] with n hn
      have hnn : 0 ≤ (pn n).ν * Lmax + |σn n - σstar| :=
        add_nonneg (mul_nonneg (hνn_pos n).le hLmax.le) (abs_nonneg _)
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hn
    filter_upwards [hev1, hev2] with n hn1 hn2 _ τ ρ hρ hρτ hτ
    have hL_mem : τ - ρ ∈ Icc 0 Lmax := ⟨sub_nonneg.2 hρτ, (sub_le_self τ hρ).trans hτ⟩
    have hρ_mem : ρ ∈ Icc 0 Lmax := ⟨hρ, hρτ.trans hτ⟩
    have hσ_mem : (pn n).ν * (t'n n + ρ) ∈ Icc 0 Sig := hwin_age_mem n ρ hρ_mem
    have hTCM₂ : TrainCloseM m (pn n).train Sig δ₂ :=
      PartIIbF24Sub.trainCloseM_mono (hTCMk (idx n)) (hn1.le.trans (min_le_left _ _))
    have hν₂' : (pn n).ν ≤ ν₂ := (hνn_le_rn n).trans (hn1.le.trans (min_le_right _ _))
    obtain ⟨hSc_bd, hWx_raw⟩ := hFree2 (pn n) (dn n) (hbgk (idx n)) hν₂' (hAgek (idx n)) hTCM₂
      (Scn n) (hCDk (idx n)).free_prop (t'n n + ρ) (τ - ρ) (add_nonneg (ht'n0 n) hρ) hL_mem.1
      hL_mem.2 (by have := ht'nH n; linarith)
    have hcont_step :
        ‖T_pl ((pn n).ν * (t'n n + ρ)) (-(τ - ρ)) x - T_pl σstar (-(τ - ρ)) x‖ < ε / 3 :=
      hage hσ_mem hσstar ⟨neg_le_neg hL_mem.2, (neg_nonpos.2 hL_mem.1).trans hLmax.le⟩
        ((hwin_age_dist n ρ hρ_mem).trans_lt hn2)
    exact lifted_free_adjoint_sub_lt hT (Scn n) hσ_mem hσstar x hε₁_pos hε₁_le1 hDε₁
      hSc_bd (hWx_raw x (mem_singleton x)) hcont_step
  obtain ⟨K_A, hK_A⟩ := isCompact_Icc.exists_bound_of_continuousOn hAcont
  have hAb : ∃ K, ∀ (n : ℕ) (p : Unit) (r : ℝ), r ∈ Icc 0 Lmax → ‖A n p r‖ ≤ K := by
    refine ⟨K_A + C_Sg * 2, fun n _ r hr => ?_⟩
    have htr_mem : t'n n + r ∈ Icc 0 (pn n).H :=
      ⟨add_nonneg (ht'n0 n) hr.1, (add_le_add_right hr.2 (t'n n)).trans (ht'nH n)⟩
    have hσ_mem : (pn n).ν * (t'n n + r) ∈ Icc 0 Sig := hwin_age_mem n r hr
    have hcmp := hAck (idx n) (t'n n + r) htr_mem
    rw [c_rpow_neg_two (hbgk (idx n))] at hcmp
    have hν4 : (pn n).ν ^ 4 ≤ 1 := pow_le_one₀ (hνn_pos n).le (hνn_le1 n)
    have h2le : (pn n).ν ^ 4 + rn n ≤ 2 := by
      calc (pn n).ν ^ 4 + rn n ≤ 1 + 1 := add_le_add hν4 (hrn_le1 n)
        _ = 2 := by norm_num
    have hcmp2 : ‖A n () r - AplOp ((pn n).ν * (t'n n + r))‖ ≤ C_Sg * 2 :=
      hcmp.trans (mul_le_mul_of_nonneg_left h2le hC_Sg.le)
    calc ‖A n () r‖
        = ‖AplOp ((pn n).ν * (t'n n + r)) + (A n () r - AplOp ((pn n).ν * (t'n n + r)))‖ := by
            rw [add_sub_cancel]
      _ ≤ ‖AplOp ((pn n).ν * (t'n n + r))‖ + ‖A n () r - AplOp ((pn n).ν * (t'n n + r))‖ :=
            norm_add_le _ _
      _ ≤ K_A + C_Sg * 2 := add_le_add (hK_A _ hσ_mem) hcmp2
  have hA : ∀ ε > 0, ∀ᶠ n in atTop, ∀ (p : Unit) (r : ℝ),
      r ∈ Icc 0 Lmax → ‖A n p r - A₀ p r‖ < ε := by
    intro ε hε
    have hunifA : UniformContinuousOn AplOp (Icc 0 Sig) :=
      isCompact_Icc.uniformContinuousOn_of_continuous hAcont
    obtain ⟨δ_A, hδ_A, hdistA⟩ := Metric.uniformContinuousOn_iff.1 hunifA (ε / 2) (half_pos hε)
    have hcmp_lim : Tendsto (fun n => C_Sg * ((pn n).ν ^ 4 + rn n)) atTop (nhds 0) := by
      have hν4_lim : Tendsto (fun n => (pn n).ν ^ 4) atTop (nhds 0) := by
        simpa using hνn_lim.pow 4
      have hsum : Tendsto (fun n => (pn n).ν ^ 4 + rn n) atTop (nhds 0) := by
        simpa only [add_zero] using hν4_lim.add hrn_lim
      simpa only [mul_zero] using hsum.const_mul C_Sg
    have hev1 : ∀ᶠ n in atTop, C_Sg * ((pn n).ν ^ 4 + rn n) < ε / 2 := by
      filter_upwards [Metric.tendsto_nhds.1 hcmp_lim (ε / 2) (half_pos hε)] with n hn
      have hnn : 0 ≤ C_Sg * ((pn n).ν ^ 4 + rn n) :=
        mul_nonneg hC_Sg.le (add_nonneg (pow_nonneg (hνn_pos n).le 4) (hrk_pos (idx n)).le)
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hn
    have hev2 : ∀ᶠ n in atTop, (pn n).ν * Lmax + |σn n - σstar| < δ_A := by
      filter_upwards [Metric.tendsto_nhds.1 hage_err_lim δ_A hδ_A] with n hn
      have hnn : 0 ≤ (pn n).ν * Lmax + |σn n - σstar| :=
        add_nonneg (mul_nonneg (hνn_pos n).le hLmax.le) (abs_nonneg _)
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hn
    filter_upwards [hev1, hev2] with n hn1 hn2 _ r hr
    have htr_mem : t'n n + r ∈ Icc 0 (pn n).H :=
      ⟨add_nonneg (ht'n0 n) hr.1, (add_le_add_right hr.2 (t'n n)).trans (ht'nH n)⟩
    have hσ_mem : (pn n).ν * (t'n n + r) ∈ Icc 0 Sig := hwin_age_mem n r hr
    have hcmp := hAck (idx n) (t'n n + r) htr_mem
    rw [c_rpow_neg_two (hbgk (idx n))] at hcmp
    have hdσ : dist ((pn n).ν * (t'n n + r)) σstar < δ_A := by
      rw [Real.dist_eq]
      exact (hwin_age_dist n r hr).trans_lt hn2
    have hA_cont_step : ‖AplOp ((pn n).ν * (t'n n + r)) - AplOp σstar‖ < ε / 2 := by
      have h := hdistA _ hσ_mem _ hσstar hdσ
      rwa [dist_eq_norm] at h
    calc ‖A n () r - A₀ () r‖
        = ‖(A n () r - AplOp ((pn n).ν * (t'n n + r))) +
            (AplOp ((pn n).ν * (t'n n + r)) - AplOp σstar)‖ := by
            dsimp [A₀]; rw [sub_add_sub_cancel]
      _ ≤ ‖A n () r - AplOp ((pn n).ν * (t'n n + r))‖ +
            ‖AplOp ((pn n).ν * (t'n n + r)) - AplOp σstar‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hcmp.trans_lt hn1) hA_cont_step
      _ = ε := add_halves ε
  have hA₀c : ∀ (_ : Unit) (r : ℝ), r ∈ Icc 0 Lmax → IsCompactOperator (A₀ () r) :=
    fun _ _ _ => (hAop σstar hσstar).2
  have hA₀p : TotallyBounded {K : Xm m →L[ℝ] Xm m | ∃ p : Unit, ∃ r ∈ Icc 0 Lmax, A₀ p r = K} := by
    refine (Set.finite_singleton (AplOp σstar)).totallyBounded.subset ?_
    rintro _ ⟨_, _, _, rfl⟩
    exact mem_singleton _
  have hU_win : ∀ n, RCDuhamel.IsDuhamelEvolutionOn (𝕜 := ℝ) 0 Lmax (F n) (A n) (U n) :=
    fun n => isDuhamelEvolutionOn_lifted (hCDk (idx n)) (ht'n0 n) (ht'nH n)
  have hU₀_win : RCDuhamel.IsDuhamelEvolutionOn (𝕜 := ℝ) 0 Lmax F₀ A₀ U₀ :=
    (isDuhamelEvolution_planar (Lmax := Lmax - 0) hEcont hEmild hσstar).toOn
  -- Step 5: Combine window norm convergence and planar norm convergence to contradict `hbadk`.
  have hwin_norm := (RCDuhamel.real_compact_duhamel_window hFb hF hFadj hAb hA hA₀c hA₀p
    hU_win hU₀_win).2.2 (η / 2) (half_pos hη)
  have hpl_norm := planar_diff_tendsto (Lmax := Lmax) hm hSig hAcont hAop hT hEcont hEmild
    hσn_mem hσstar hσn_lim (η / 2) (half_pos hη)
  obtain ⟨n, hn_win, hn_pl⟩ := (hwin_norm.and hpl_norm).exists
  let s₀ : ℝ := tn n - t'n n
  let t₀ : ℝ := tn n + Ln n - t'n n
  have hs₀ : 0 ≤ s₀ := sub_nonneg.2 (ht'n_le_tn n)
  have hst₀ : s₀ ≤ t₀ := sub_le_sub_right (le_add_of_nonneg_right (hLk0 (idx n))) (t'n n)
  have ht₀ : t₀ ≤ Lmax := sub_le_iff_le_add'.2 (htnLn_le n)
  have h1 := hn_win () t₀ s₀ hs₀ hst₀ ht₀
  have h2 := hn_pl () (Ln n) 0 (hLk0 (idx n)) (by rw [zero_add]; exact hLkL (idx n))
  have heq_t : t'n n + t₀ = tn n + Ln n := by dsimp [t₀]; ring
  have heq_s : t'n n + s₀ = tn n := by dsimp [s₀]; ring
  have heq_d : t₀ - s₀ = Ln n := by dsimp [t₀, s₀]; ring
  have hUF_eq : U n () t₀ s₀ - F n () t₀ s₀ =
      (Jc (pn n).c m).comp
        ((Un n (tn n + Ln n) (tn n) - Scn n (tn n + Ln n) (tn n)).comp (Rc (pn n).c m)) := by
    dsimp only [U, F]
    rw [heq_t, heq_s]
    exact ContinuousLinearMap.ext fun y => by
      simp only [sub_apply, ContinuousLinearMap.comp_apply, map_sub]
  have hU₀F₀_eq : U₀ () t₀ s₀ - F₀ () t₀ s₀ = E_pl σstar (Ln n) - T_pl σstar (Ln n) := by
    dsimp only [U₀, F₀]; rw [heq_d]
  rw [hUF_eq, hU₀F₀_eq] at h1
  simp only [sub_zero] at h2
  let X : Xm m →L[ℝ] Xm m := (Jc (pn n).c m).comp
    ((Un n (tn n + Ln n) (tn n) - Scn n (tn n + Ln n) (tn n)).comp (Rc (pn n).c m))
  let Y : Xm m →L[ℝ] Xm m := E_pl σstar (Ln n) - T_pl σstar (Ln n)
  let Z : Xm m →L[ℝ] Xm m := E_pl (σn n) (Ln n) - T_pl (σn n) (Ln n)
  have hXZ : ‖X - Z‖ < η := by
    calc ‖X - Z‖ = ‖(X - Y) - (Z - Y)‖ := by rw [sub_sub_sub_cancel_right]
      _ ≤ ‖X - Y‖ + ‖Z - Y‖ := norm_sub_le _ _
      _ < η / 2 + η / 2 := add_lt_add h1 h2
      _ = η := add_halves η
  exact (lt_irrefl η) ((hbadk (idx n)).trans hXZ)
