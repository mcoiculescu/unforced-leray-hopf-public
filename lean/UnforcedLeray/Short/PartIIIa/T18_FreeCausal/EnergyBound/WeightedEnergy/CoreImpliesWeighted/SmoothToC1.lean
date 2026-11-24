import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.CoreImpliesWeighted.CoreToSmooth
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Part III-a, `PartIII-a:T18/3/1/4/3`: `SmoothToC1Weighted` (Lemma 3)

Source of record: `the November 2 reference manuscript`, lines 3541-3552 and 3427-3440.

For a `C¹` cutoff `ψ` (compact support in `(0,∞)`, `ψ ≥ 0`) the mollifications `ψₙ = ρₙ ⋆ ψ` with
`ρₙ` a nonnegative normalized bump of radius `1/(n+1)` are smooth, nonnegative, supported in a fixed
compact subset of `(0,∞)`, and `ψₙ → ψ`, `ψₙ' → ψ'` uniformly. The smooth inequality holds for each
`ψₙ`, and all three integrals converge by dominated convergence on that compact set.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIIa.SmoothToC1Aux

open UnforcedLeray.Short.IIIa.CoreToSmoothAux

/-- The normalized-bump family: radius `1/(n+1)`. -/
def bumpR (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1 / (2 * ((n : ℝ) + 1))
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    apply (one_div_lt_one_div (by positivity) (by positivity)).2
    linarith

/-- The normalized mollifier `ρₙ`. -/
def mol (n : ℕ) : ℝ → ℝ := (bumpR n).normed volume

theorem mol_nonneg (n : ℕ) (x : ℝ) : 0 ≤ mol n x := (bumpR n).nonneg_normed x

theorem mol_contDiff (n : ℕ) : ContDiff ℝ ∞ (mol n) := (bumpR n).contDiff_normed

theorem mol_hasCompactSupport (n : ℕ) : HasCompactSupport (mol n) :=
  (bumpR n).hasCompactSupport_normed

theorem mol_zero (n : ℕ) {x : ℝ} (hx : 1 / ((n : ℝ) + 1) ≤ |x|) : mol n x = 0 := by
  by_contra h
  have hmem : x ∈ Function.support (mol n) := h
  unfold mol at hmem
  rw [(bumpR n).support_normed_eq, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hmem
  exact absurd hmem (not_lt.2 hx)

/-- The smoothing `sm g n = ρₙ ⋆ g`. -/
def sm (g : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  convolution (mol n) g (ContinuousLinearMap.lsmul ℝ ℝ) volume

theorem sm_apply (g : ℝ → ℝ) (n : ℕ) (x : ℝ) : sm g n x = ∫ t, mol n t * g (x - t) := by
  unfold sm
  rw [convolution_def]
  simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul]

theorem sm_nonneg (g : ℝ → ℝ) (hg : ∀ x, 0 ≤ g x) (n : ℕ) (x : ℝ) : 0 ≤ sm g n x := by
  rw [sm_apply]
  exact integral_nonneg fun t => mul_nonneg (mol_nonneg n t) (hg _)

theorem sm_contDiff (g : ℝ → ℝ) (hg : Continuous g) (n : ℕ) : ContDiff ℝ ∞ (sm g n) :=
  (mol_hasCompactSupport n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (mol_contDiff n) hg.locallyIntegrable

theorem sm_hasDerivAt (g : ℝ → ℝ) (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (n : ℕ)
    (x : ℝ) : HasDerivAt (sm g n) (sm (deriv g) n x) x := by
  unfold sm
  exact HasCompactSupport.hasDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (mol_contDiff n).continuous.locallyIntegrable hgc hg x

theorem sm_uniform (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) {ε : ℝ}
    (hε : 0 < ε) : ∃ N : ℕ, ∀ n, N ≤ n → ∀ x, dist (sm g n x) (g x) ≤ ε := by
  obtain ⟨δ, hδ, hδε⟩ :=
    Metric.uniformContinuous_iff.1 (hgc.uniformContinuous_of_continuous hg) ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨N, fun n hn x => ?_⟩
  have hr : (bumpR n).rOut < δ := by
    show 1 / ((n : ℝ) + 1) < δ
    refine lt_of_le_of_lt ?_ hN
    apply one_div_le_one_div_of_le (by positivity)
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hloc : ∀ y ∈ Metric.ball x (bumpR n).rOut, dist (g y) (g x) ≤ ε := fun y hy => by
    have hyx : dist y x < δ := (Metric.mem_ball.1 hy).trans hr
    exact (hδε hyx).le
  exact ContDiffBump.dist_normed_convolution_le (φ := bumpR n) (μ := volume)
    hg.aestronglyMeasurable hloc

theorem sm_tendsto (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) (x : ℝ) :
    Tendsto (fun n => sm g n x) atTop (𝓝 (g x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := sm_uniform g hg hgc (half_pos hε)
  exact ⟨N, fun n hn => lt_of_le_of_lt (hN n hn x) (by linarith)⟩

theorem sm_bound (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∃ M : ℝ, ∀ᶠ n in atTop, ∀ s, |sm g n s| ≤ M := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  obtain ⟨N, hN⟩ := sm_uniform g hg hgc one_pos
  refine ⟨C + 1, Filter.eventually_atTop.2 ⟨N, fun n hn s => ?_⟩⟩
  have h1 := hN n hn s
  have h2 := hC s
  rw [Real.dist_eq] at h1
  rw [Real.norm_eq_abs] at h2
  have := abs_sub_abs_le_abs_sub (sm g n s) (g s)
  linarith

/-- The support of the smoothing lies in a fixed compact interval for large `n`. -/
theorem sm_zero (ψ : ℝ → ℝ) (a b : ℝ) (hsupp : tsupport ψ ⊆ Icc a b) (n : ℕ)
    (hr : 1 / ((n : ℝ) + 1) ≤ a / 2) (hr1 : 1 / ((n : ℝ) + 1) ≤ 1) {x : ℝ}
    (hx : x ∉ Icc (a / 2) (b + 1)) : sm ψ n x = 0 := by
  rw [sm_apply]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  show mol n t * ψ (x - t) = 0
  by_cases h1 : ψ (x - t) = 0
  · simp [h1]
  by_cases h2 : mol n t = 0
  · simp [h2]
  exfalso
  have hxt : x - t ∈ Icc a b := hsupp (subset_tsupport ψ h1)
  have ht : |t| < 1 / ((n : ℝ) + 1) := by
    by_contra hc
    exact h2 (mol_zero n (not_lt.1 hc))
  have hab := abs_lt.1 ht
  apply hx
  constructor
  · linarith [hxt.1, hab.1, hr]
  · linarith [hxt.2, hab.2, hr1]

theorem toK_Ioi (a b : ℝ) (ha : 0 < a) (f : ℝ → ℝ) (hf : ∀ s, s ∉ Icc a b → f s = 0) :
    ∫ s in Ioi (0 : ℝ), f s = ∫ s in Icc a b, f s :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun s hs => lt_of_lt_of_le ha hs.1) (fun s hs => hf s hs.2)

/-- Dominated convergence on `[a,b] ⊂ (0,∞)` for the `Ioi`-integrals of a family. -/
theorem tendsto_Ioi_dom (a b : ℝ) (ha : 0 < a) (g : ℕ → ℝ → ℝ) (g0 : ℝ → ℝ) (H : ℝ → ℝ)
    (hH : IntegrableOn H (Icc a b))
    (hmeas : ∀ n, AEStronglyMeasurable (g n) (volume.restrict (Icc a b)))
    (hpt : ∀ s, Tendsto (fun n => g n s) atTop (𝓝 (g0 s)))
    (hbd : ∀ᶠ n in atTop, ∀ s ∈ Icc a b, |g n s| ≤ H s)
    (hzero : ∀ᶠ n in atTop, ∀ s, s ∉ Icc a b → g n s = 0)
    (hzero0 : ∀ s, s ∉ Icc a b → g0 s = 0) :
    Tendsto (fun n => ∫ s in Ioi (0 : ℝ), g n s) atTop (𝓝 (∫ s in Ioi (0 : ℝ), g0 s)) := by
  rw [toK_Ioi a b ha g0 hzero0]
  refine Tendsto.congr' (hzero.mono fun n hn => (toK_Ioi a b ha (g n) hn).symm) ?_
  refine tendsto_integral_filter_of_dominated_convergence H (Eventually.of_forall hmeas) ?_ hH ?_
  · filter_upwards [hbd] with n hn
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_)
    rw [Real.norm_eq_abs]
    exact hn s hs
  · exact Eventually.of_forall fun s => hpt s

/-- `Uf c ν γ b s = ∫_cell |g⁻¹ b|²`. -/
def Uf (c ν γ : ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (s : ℝ) : ℝ :=
  ∫ x in UnforcedLeray.B0579.cell c, vnorm2 (gainConj γ ν b (s, x)) ^ 2

/-- `Vf c ν γ G s = ∫_cell |g⁻¹ G|²`. -/
def Vf (c ν γ : ℝ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (s : ℝ) : ℝ :=
  ∫ x in UnforcedLeray.B0579.cell c, tnorm2 (gainConj γ ν G (s, x)) ^ 2

/-- `Jf c ν γ F G s = ∫_cell |g⁻¹ F| |g⁻¹ G|`. -/
def Jf (c ν γ : ℝ) (F G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (s : ℝ) : ℝ :=
  ∫ x in UnforcedLeray.B0579.cell c, tnorm2 (gainConj γ ν F (s, x)) * tnorm2 (gainConj γ ν G (s, x))

/-- The coefficient `A(s) = (1/2 + 2μ) s^{-3/2} U(s) + 2ν s^{-1/2} V(s)` of the smooth LHS. -/
def Aw (μr ν : ℝ) (U V : ℝ → ℝ) (s : ℝ) : ℝ :=
  (1 / 2 + 2 * μr) * s ^ (-3 / 2 : ℝ) * U s + 2 * ν * s ^ (-1 / 2 : ℝ) * V s

theorem Uf_eq (c ν γ : ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (s : ℝ) :
    Uf c ν γ b s = qWt γ ν s * energyE c b s := by
  unfold Uf energyE
  rw [← integral_const_mul]
  congr 1
  funext x
  exact vnorm2_gainConj_sq γ ν b (s, x)

theorem Vf_eq (c ν γ : ℝ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    Vf c ν γ G s = qWt γ ν s * energyN c G s := by
  unfold Vf energyN
  rw [← integral_const_mul]
  congr 1
  funext x
  exact tnorm2_gainConj_sq γ ν G (s, x)

theorem Jf_eq (c ν γ : ℝ) (F G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (s : ℝ) :
    Jf c ν γ F G s = qWt γ ν s * ∫ x in UnforcedLeray.B0579.cell c,
      tnorm2 (F (s, x)) * tnorm2 (G (s, x)) := by
  unfold Jf
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [ct_tnorm2_gainConj_eq, ct_tnorm2_gainConj_eq]
  dsimp only
  unfold qWt
  ring

end UnforcedLeray.Short.IIIa.SmoothToC1Aux

namespace UnforcedLeray.Short.IIIa.SmoothToC1Aux

open UnforcedLeray.Short.IIIa UnforcedLeray.Short.IIIa.CoreToSmoothAux

end UnforcedLeray.Short.IIIa.SmoothToC1Aux

open UnforcedLeray.Short.IIIa UnforcedLeray.Short.IIIa.CoreToSmoothAux
  UnforcedLeray.Short.IIIa.SmoothToC1Aux

/-- **Lemma 3** (`PartIII-a:T18/3/1/4/3`; SP 3541-3552): smooth weights to `C¹` weights. -/
theorem smoothToC1Weighted : UnforcedLeray.Short.IIIa.SmoothToC1Weighted := by
  unfold UnforcedLeray.Short.IIIa.SmoothToC1Weighted
    UnforcedLeray.Short.IIIa.WeightedEnergyIdentitySmooth
  intro hLoc hSm
  unfold UnforcedLeray.Short.IIIa.WeightedEnergyIdentity
  intro c ν γ μ hc hν hγ F b G hF hmeasF hcaus ψ hψ hψc hψsupp hψnn
  obtain ⟨s1, s2, hs1, hs12, hsub⟩ :=
    exists_Icc_contains (tsupport ψ) (hψc : IsCompact (tsupport ψ)) hψsupp
  have hD : FreeSolData c ν μ F b G := ⟨hc, hν, hF, hmeasF, hcaus⟩
  have ha : 0 < s1 / 2 := by positivity
  have hab : s1 / 2 < s2 + 1 := by linarith
  obtain ⟨hEI, hNI, hRI, hJI⟩ := hLoc c ν μ F b G hD (s1 / 2) (s2 + 1) ha hab
  have hψcont : Continuous ψ := hψ.continuous
  have hdψcont : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hdψc : HasCompactSupport (deriv ψ) := hψc.deriv
  have hsuppd : tsupport (deriv ψ) ⊆ Icc s1 s2 := tsupport_deriv_subset.trans hsub
  have hψ0 : ∀ s, s ∉ Icc (s1 / 2) (s2 + 1) → ψ s = 0 := fun s hs =>
    image_eq_zero_of_notMem_tsupport
      (fun h => hs ⟨by linarith [(hsub h).1], by linarith [(hsub h).2]⟩)
  have hdψ0 : ∀ s, s ∉ Icc (s1 / 2) (s2 + 1) → deriv ψ s = 0 := fun s hs =>
    deriv_of_notMem_tsupport
      (fun h => hs ⟨by linarith [(hsub h).1], by linarith [(hsub h).2]⟩)
  obtain ⟨N1, hN1⟩ := exists_nat_one_div_lt (show (0 : ℝ) < min (s1 / 2) 1 from lt_min ha one_pos)
  have hthr : ∀ n, N1 ≤ n → 1 / ((n : ℝ) + 1) ≤ s1 / 2 ∧ 1 / ((n : ℝ) + 1) ≤ 1 := by
    intro n hn
    have hN : (N1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N1 : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have h2 := lt_of_le_of_lt h1 hN1
    exact ⟨(h2.trans_le (min_le_left _ _)).le, (h2.trans_le (min_le_right _ _)).le⟩
  have hzero_n : ∀ n, N1 ≤ n → ∀ x, x ∉ Icc (s1 / 2) (s2 + 1) → sm ψ n x = 0 := fun n hn x hx =>
    sm_zero ψ s1 s2 hsub n (hthr n hn).1 (hthr n hn).2 hx
  have hcs : ∀ n, N1 ≤ n → HasCompactSupport (sm ψ n) := fun n hn =>
    HasCompactSupport.intro isCompact_Icc (fun x hx => hzero_n n hn x hx)
  have htsupp : ∀ n, N1 ≤ n → tsupport (sm ψ n) ⊆ Ioi 0 := fun n hn => by
    have hsub' : Function.support (sm ψ n) ⊆ Icc (s1 / 2) (s2 + 1) := fun x hx => by
      by_contra h
      exact hx (hzero_n n hn x h)
    exact (closure_minimal hsub' isClosed_Icc).trans (fun s hs => lt_of_lt_of_le ha hs.1)
  have hderiv : ∀ n, deriv (sm ψ n) = sm (deriv ψ) n := fun n =>
    funext fun x => (sm_hasDerivAt ψ hψc hψ n x).deriv
  have hcontder : ∀ n, Continuous (deriv (sm ψ n)) := fun n => by
    rw [hderiv n]
    exact (sm_contDiff _ hdψcont n).continuous
  have hKc : IsCompact (Icc (s1 / 2) (s2 + 1)) := isCompact_Icc
  have hKm : MeasurableSet (Icc (s1 / 2) (s2 + 1)) := measurableSet_Icc
  have hqK : ContinuousOn (qWt γ ν) (Icc (s1 / 2) (s2 + 1)) := fun s hs =>
    (hasDerivAt_qWt γ ν hν (lt_of_lt_of_le ha hs.1)).continuousAt.continuousWithinAt
  have hpowK : ContinuousOn (fun s : ℝ => s ^ (-1 / 2 : ℝ)) (Icc (s1 / 2) (s2 + 1)) := fun s hs =>
    (Real.continuousAt_rpow_const s _ (Or.inl (lt_of_lt_of_le ha hs.1).ne')).continuousWithinAt
  have hpow3K : ContinuousOn (fun s : ℝ => s ^ (-3 / 2 : ℝ)) (Icc (s1 / 2) (s2 + 1)) := fun s hs =>
    (Real.continuousAt_rpow_const s _ (Or.inl (lt_of_lt_of_le ha hs.1).ne')).continuousWithinAt
  have hUI : IntegrableOn (Uf c ν γ b) (Icc (s1 / 2) (s2 + 1)) :=
    (intK_mul hKc hEI hqK).congr_fun (fun s _ => (Uf_eq c ν γ b s).symm) hKm
  have hVI : IntegrableOn (Vf c ν γ G) (Icc (s1 / 2) (s2 + 1)) :=
    (intK_mul hKc hNI hqK).congr_fun (fun s _ => (Vf_eq c ν γ G s).symm) hKm
  have hJI' : IntegrableOn (Jf c ν γ F G) (Icc (s1 / 2) (s2 + 1)) :=
    (intK_mul hKc hJI hqK).congr_fun (fun s _ => (Jf_eq c ν γ F G s).symm) hKm
  have hA1 : IntegrableOn (fun s => (1 / 2 + 2 * μ.re) * s ^ (-3 / 2 : ℝ) * Uf c ν γ b s)
      (Icc (s1 / 2) (s2 + 1)) :=
    intK_mul hKc hUI (continuousOn_const.mul hpow3K)
  have hA2 : IntegrableOn (fun s => 2 * ν * s ^ (-1 / 2 : ℝ) * Vf c ν γ G s)
      (Icc (s1 / 2) (s2 + 1)) :=
    intK_mul hKc hVI (continuousOn_const.mul hpowK)
  have hAI : IntegrableOn (fun s => Aw μ.re ν (Uf c ν γ b) (Vf c ν γ G) s)
      (Icc (s1 / 2) (s2 + 1)) := hA1.add hA2
  have hBI : IntegrableOn (fun s => s ^ (-1 / 2 : ℝ) * Uf c ν γ b s) (Icc (s1 / 2) (s2 + 1)) :=
    intK_mul hKc hUI hpowK
  have hCI : IntegrableOn (fun s => s ^ (-1 / 2 : ℝ) * Jf c ν γ F G s)
      (Icc (s1 / 2) (s2 + 1)) :=
    intK_mul hKc hJI' hpowK
  obtain ⟨MΨ, hMΨ⟩ := sm_bound ψ hψcont hψc
  obtain ⟨MD, hMD⟩ := sm_bound (deriv ψ) hdψcont hdψc
  have hpt : ∀ s, Tendsto (fun n => sm ψ n s) atTop (𝓝 (ψ s)) := fun s =>
    sm_tendsto ψ hψcont hψc s
  have hptd : ∀ s, Tendsto (fun n => deriv (sm ψ n) s) atTop (𝓝 (deriv ψ s)) := fun s => by
    simp only [hderiv]
    exact sm_tendsto (deriv ψ) hdψcont hdψc s
  -- the LHS family
  have hLHS : Tendsto (fun n => ∫ s in Ioi (0 : ℝ), sm ψ n s * Aw μ.re ν (Uf c ν γ b) (Vf c ν γ G) s)
      atTop (𝓝 (∫ s in Ioi (0 : ℝ), ψ s * Aw μ.re ν (Uf c ν γ b) (Vf c ν γ G) s)) := by
    refine tendsto_Ioi_dom (s1 / 2) (s2 + 1) ha _ _ _ (hAI.abs.const_mul MΨ) ?_ ?_ ?_ ?_ ?_
    · exact fun n => ((sm_contDiff ψ hψcont n).continuous.aestronglyMeasurable).mul
        hAI.aestronglyMeasurable
    · exact fun s => (hpt s).mul_const _
    · filter_upwards [hMΨ] with n hn s _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hn s) (abs_nonneg _)
    · filter_upwards [eventually_ge_atTop N1] with n hn s hs
      rw [hzero_n n hn s hs, zero_mul]
    · intro s hs
      rw [hψ0 s hs, zero_mul]
  -- the derivative family
  have hRHS1 : Tendsto (fun n => ∫ s in Ioi (0 : ℝ), deriv (sm ψ n) s * (s ^ (-1 / 2 : ℝ) * Uf c ν γ b s))
      atTop (𝓝 (∫ s in Ioi (0 : ℝ), deriv ψ s * (s ^ (-1 / 2 : ℝ) * Uf c ν γ b s))) := by
    refine tendsto_Ioi_dom (s1 / 2) (s2 + 1) ha _ _ _ (hBI.abs.const_mul MD) ?_ ?_ ?_ ?_ ?_
    · exact fun n => (hcontder n).aestronglyMeasurable.mul hBI.aestronglyMeasurable
    · exact fun s => (hptd s).mul_const _
    · filter_upwards [hMD] with n hn s _
      rw [congrFun (hderiv n) s, abs_mul]
      exact mul_le_mul_of_nonneg_right (hn s) (abs_nonneg _)
    · filter_upwards [eventually_ge_atTop N1] with n hn s hs
      rw [congrFun (hderiv n) s, sm_zero (deriv ψ) s1 s2 hsuppd n (hthr n hn).1 (hthr n hn).2 hs,
        zero_mul]
    · intro s hs
      rw [hdψ0 s hs, zero_mul]
  -- the `C` family
  have hCeq : ∀ n, (fun s => sm ψ n s * s ^ (-1 / 2 : ℝ) * Jf c ν γ F G s) =
      fun s => sm ψ n s * (s ^ (-1 / 2 : ℝ) * Jf c ν γ F G s) := fun n =>
    funext fun s => mul_assoc _ _ _
  have hRHS2 : Tendsto (fun n => ∫ s in Ioi (0 : ℝ), sm ψ n s * s ^ (-1 / 2 : ℝ) * Jf c ν γ F G s)
      atTop (𝓝 (∫ s in Ioi (0 : ℝ), ψ s * s ^ (-1 / 2 : ℝ) * Jf c ν γ F G s)) := by
    refine tendsto_Ioi_dom (s1 / 2) (s2 + 1) ha _ _ _ (hCI.abs.const_mul MΨ) ?_ ?_ ?_ ?_ ?_
    · exact fun n => by
        rw [hCeq n]
        exact ((sm_contDiff ψ hψcont n).continuous.aestronglyMeasurable).mul
          hCI.aestronglyMeasurable
    · exact fun s => by
        simpa only [mul_assoc] using (hpt s).mul_const (s ^ (-1 / 2 : ℝ) * Jf c ν γ F G s)
    · filter_upwards [hMΨ] with n hn s _
      rw [mul_assoc, abs_mul]
      exact mul_le_mul_of_nonneg_right (hn s) (abs_nonneg _)
    · filter_upwards [eventually_ge_atTop N1] with n hn s hs
      simp [hzero_n n hn s hs]
    · intro s hs
      simp [hψ0 s hs]
  -- the smooth inequality for the mollifications, and the passage to the limit
  have hle : ∀ᶠ n in atTop,
      (∫ s in Ioi (0 : ℝ), sm ψ n s * Aw μ.re ν (Uf c ν γ b) (Vf c ν γ G) s) ≤
        (∫ s in Ioi (0 : ℝ), deriv (sm ψ n) s * (s ^ (-1 / 2 : ℝ) * Uf c ν γ b s)) +
          2 * ∫ s in Ioi (0 : ℝ), sm ψ n s * s ^ (-1 / 2 : ℝ) * Jf c ν γ F G s := by
    filter_upwards [eventually_ge_atTop N1] with n hn
    exact hSm c ν γ μ hc hν hγ F b G hF hmeasF hcaus (sm ψ n) (sm_contDiff ψ hψcont n)
      (hcs n hn) (htsupp n hn) (fun s => sm_nonneg ψ hψnn n s)
  exact le_of_tendsto_of_tendsto hLHS (hRHS1.add (hRHS2.const_mul 2)) hle
