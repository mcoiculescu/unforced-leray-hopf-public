import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntFderivFormula.Helpers
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_4
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# `PartII-a:N01/9/1/2/4/4/4` scalar core of `HeatIntFderivFormula`

Source `the November 2 reference manuscript`
lines 3379-3383.  Differentiation under the `σ`-integral of `∫₀^s (σ/s)^μ planeHeat(ν(s-σ)) g(σ,·) dσ`
for a scalar `C¹` slice `g` that vanishes for `σ < s₁` with bounded values and `w`-derivatives.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01.HIFD

open UnforcedLeray.B0224 (planeHeat)

theorem planeHeat_norm_le_all {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (θ : ℝ) {g : ℝ × ℝ → E} {B : ℝ}
    (hB : ∀ y, ‖g y‖ ≤ B) (x : ℝ × ℝ) : ‖planeHeat θ g x‖ ≤ B := by
  by_cases h : 0 < θ
  · exact planeHeat_norm_le h hB x
  · rw [UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 h)]
    exact hB x

theorem hasFDerivAt_planeHeat (hP : UnforcedLeray.Short.PartIIa.N01.PlaneHeatFderiv) (θ : ℝ)
    (u : ℝ × ℝ → ℂ) (hu : ContDiff ℝ 1 u) (hb : ∃ M : ℝ, ∀ x, ‖u x‖ ≤ M)
    (hd : ∃ M : ℝ, ∀ x, ‖fderiv ℝ u x‖ ≤ M) (z v : ℝ × ℝ) :
    HasFDerivAt (planeHeat θ u) (fderiv ℝ (planeHeat θ u) z) z ∧
      fderiv ℝ (planeHeat θ u) z v = planeHeat θ (fun y => fderiv ℝ u y v) z := by
  by_cases h : 0 < θ
  · obtain ⟨hd', hf⟩ := hP θ h u hu hb hd
    exact ⟨(hd' z).hasFDerivAt, hf z v⟩
  · simp only [UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 h)]
    exact ⟨((hu.differentiable (by norm_num)) z).hasFDerivAt, trivial⟩

theorem core (hP : UnforcedLeray.Short.PartIIa.N01.PlaneHeatFderiv) {ν s : ℝ} (hν : 0 < ν)
    (hs : 0 < s) (μ : ℂ) (g : ℝ × (ℝ × ℝ) → ℂ) (hg : ContDiff ℝ 1 g) {s1 : ℝ} (hs1 : 0 < s1)
    (hz : ∀ σ w, σ < s1 → g (σ, w) = 0) {M : ℝ} (hM0 : ∀ p, ‖g p‖ ≤ M)
    (hM1 : ∀ σ w, ‖fderiv ℝ (fun w => g (σ, w)) w‖ ≤ M) (y : ℝ × ℝ) :
    (∀ v : ℝ × ℝ, IntervalIntegrable (fun σ : ℝ => ((σ / s : ℝ) : ℂ) ^ μ •
        planeHeat (ν * (s - σ)) (fun z => fderiv ℝ (fun w => g (σ, w)) z v) y) volume 0 s) ∧
    ∃ L : (ℝ × ℝ) →L[ℝ] ℂ, HasFDerivAt (fun z : ℝ × ℝ =>
        ∫ σ in (0 : ℝ)..s, ((σ / s : ℝ) : ℂ) ^ μ •
          planeHeat (ν * (s - σ)) (fun w => g (σ, w)) z) L y ∧
      ∀ v : ℝ × ℝ, (v = (1, 0) ∨ v = (0, 1)) →
        L v = ∫ σ in (0 : ℝ)..s, ((σ / s : ℝ) : ℂ) ^ μ •
          planeHeat (ν * (s - σ)) (fun z => fderiv ℝ (fun w => g (σ, w)) z v) y := by
  classical
  set a : ℝ → ℂ := fun σ => ((σ / s : ℝ) : ℂ) ^ μ with ha
  set sl : ℝ → ℝ × ℝ → ℂ := fun σ w => g (σ, w) with hsl
  have hM : 0 ≤ M := (norm_nonneg _).trans (hM0 (0, 0))
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hdsl : ∀ σ w v, fderiv ℝ (sl σ) w v = fderiv ℝ g (σ, w) (0, v) := by
    intro σ w v
    have h := ((hg1 (σ, w)).hasFDerivAt.comp w (hasFDerivAt_prodMk_right σ w)).fderiv
    have h' : fderiv ℝ (sl σ) w = (fderiv ℝ g (σ, w)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) :=
      h
    rw [h']
    rfl
  have hslC : ∀ σ, ContDiff ℝ 1 (sl σ) := fun σ =>
    hg.comp (contDiff_const.prodMk contDiff_id)
  have hjc : ∀ v : ℝ × ℝ, Continuous (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (sl p.1) p.2 v) := by
    intro v
    have : (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (sl p.1) p.2 v) =
        fun p => fderiv ℝ g p (0, v) := by
      funext p; rw [hdsl]
    rw [this]
    exact (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hvbound : ∀ σ w (v : ℝ × ℝ), ‖fderiv ℝ (sl σ) w v‖ ≤ M * ‖v‖ := fun σ w v =>
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hM1 σ w) (norm_nonneg v))
  have hDvan : ∀ σ, σ < s1 → ∀ (v : ℝ × ℝ) (z : ℝ × ℝ),
      planeHeat (ν * (s - σ)) (fun w => fderiv ℝ (sl σ) w v) z = 0 := by
    intro σ hσ v z
    have h0 : sl σ = fun _ => 0 := funext fun w => hz σ w hσ
    have : (fun w => fderiv ℝ (sl σ) w v) = fun _ => (0 : ℂ) := by
      funext w; rw [h0]; simp
    rw [this]
    exact congrFun (planeHeat_zero_fun _) z
  have hPvan : ∀ σ, σ < s1 → ∀ z : ℝ × ℝ, planeHeat (ν * (s - σ)) (sl σ) z = 0 := by
    intro σ hσ z
    have h0 : sl σ = fun _ => 0 := funext fun w => hz σ w hσ
    rw [h0]
    exact congrFun (planeHeat_zero_fun _) z
  -- the weight
  have haIoi : ContinuousOn a (Ioi 0) := by
    intro σ hσ
    have hpos : 0 < σ / s := div_pos hσ hs
    apply ContinuousAt.continuousWithinAt
    refine ContinuousAt.cpow ?_ continuousAt_const ?_
    · exact Complex.continuous_ofReal.continuousAt.comp (continuousAt_id.div_const s)
    · exact Complex.ofReal_mem_slitPlane.2 hpos
  obtain ⟨K0, hK0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (haIoi.mono (fun σ (hσ : σ ∈ Icc s1 s) => lt_of_lt_of_le hs1 hσ.1))
  set K : ℝ := max K0 0 with hK
  have hK0' : 0 ≤ K := le_max_right _ _
  have haM : AEStronglyMeasurable a (volume.restrict (Ioc 0 s)) :=
    (haIoi.mono (fun σ (hσ : σ ∈ Ioc 0 s) => hσ.1)).aestronglyMeasurable measurableSet_Ioc
  have hDc : ∀ (v : ℝ × ℝ) (z : ℝ × ℝ), Continuous fun σ : ℝ =>
      planeHeat (ν * (s - σ)) (fun w => fderiv ℝ (sl σ) w v) z := by
    intro v z
    exact continuous_planeHeat_param (θ := fun σ => ν * (s - σ))
      (continuous_const.mul (continuous_const.sub continuous_id))
      (u := fun σ w => fderiv ℝ (sl σ) w v) (hjc v) (M := M * ‖v‖) (fun t w => hvbound t w v) z
  have hPc : ∀ z : ℝ × ℝ, Continuous fun σ : ℝ => planeHeat (ν * (s - σ)) (sl σ) z := by
    intro z
    exact continuous_planeHeat_param (θ := fun σ => ν * (s - σ))
      (continuous_const.mul (continuous_const.sub continuous_id))
      (u := sl) hg.continuous (M := M) (fun t w => hM0 (t, w)) z
  have hbD : ∀ (v z : ℝ × ℝ) σ, σ ∈ Ioc 0 s →
      ‖a σ • planeHeat (ν * (s - σ)) (fun w => fderiv ℝ (sl σ) w v) z‖ ≤ K * (M * ‖v‖) := by
    intro v z σ hσ
    by_cases h : σ < s1
    · rw [hDvan σ h v z, smul_zero, norm_zero]
      positivity
    · rw [norm_smul]
      have hσ' : σ ∈ Icc s1 s := ⟨not_lt.1 h, hσ.2⟩
      exact mul_le_mul ((hK0 σ hσ').trans (le_max_left _ _))
        (planeHeat_norm_le_all _ (fun w => hvbound σ w v) z) (norm_nonneg _) hK0'
  have hbP : ∀ (z : ℝ × ℝ) σ, σ ∈ Ioc 0 s →
      ‖a σ • planeHeat (ν * (s - σ)) (sl σ) z‖ ≤ K * M := by
    intro z σ hσ
    by_cases h : σ < s1
    · rw [hPvan σ h z, smul_zero, norm_zero]
      positivity
    · rw [norm_smul]
      have hσ' : σ ∈ Icc s1 s := ⟨not_lt.1 h, hσ.2⟩
      exact mul_le_mul ((hK0 σ hσ').trans (le_max_left _ _))
        (planeHeat_norm_le_all _ (fun w => hM0 (σ, w)) z) (norm_nonneg _) hK0'
  have hintD : ∀ v : ℝ × ℝ, IntervalIntegrable (fun σ : ℝ => a σ •
      planeHeat (ν * (s - σ)) (fun w => fderiv ℝ (sl σ) w v) y) volume 0 s := by
    intro v
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.le]
    refine Integrable.mono' (g := fun _ => K * (M * ‖v‖)) (integrable_const _)
      (haM.smul (hDc v y).aestronglyMeasurable) ?_
    exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun σ hσ => hbD v y σ hσ)
  have hintP : ∀ z : ℝ × ℝ, IntervalIntegrable (fun σ : ℝ => a σ •
      planeHeat (ν * (s - σ)) (sl σ) z) volume 0 s := by
    intro z
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.le]
    refine Integrable.mono' (g := fun _ => K * M) (integrable_const _)
      (haM.smul (hPc z).aestronglyMeasurable) ?_
    exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun σ hσ => hbP z σ hσ)
  refine ⟨fun v => hintD v, ?_⟩
  -- the CLM-valued derivative
  let e1 : ℝ × ℝ := (1, 0)
  let e2 : ℝ × ℝ := (0, 1)
  let D : ℝ × ℝ → ℝ → ℝ × ℝ → ℂ := fun v σ z =>
    planeHeat (ν * (s - σ)) (fun w => fderiv ℝ (sl σ) w v) z
  let F' : ℝ × ℝ → ℝ → (ℝ × ℝ) →L[ℝ] ℂ := fun z σ =>
    (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℂ (ContinuousLinearMap.fst ℝ ℝ ℝ)) (a σ • D e1 σ z) +
    (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℂ (ContinuousLinearMap.snd ℝ ℝ ℝ)) (a σ • D e2 σ z)
  have hF'apply : ∀ z σ (v : ℝ × ℝ), F' z σ v = v.1 • (a σ • D e1 σ z) + v.2 • (a σ • D e2 σ z) := by
    intro z σ v
    simp [F']
  have hF'norm : ∀ z σ, σ ∈ Ioc 0 s →
      ‖F' z σ‖ ≤ K * (M * ‖e1‖) + K * (M * ‖e2‖) := by
    intro z σ hσ
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.norm_smulRight_apply]
      exact (mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)).trans
        (hbD e1 z σ hσ)
    · rw [ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.norm_smulRight_apply]
      exact (mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)).trans
        (hbD e2 z σ hσ)
  have hF'meas : AEStronglyMeasurable (F' y) (volume.restrict (Ioc 0 s)) := by
    refine AEStronglyMeasurable.add ?_ ?_
    · exact ((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℂ
        (ContinuousLinearMap.fst ℝ ℝ ℝ)).continuous.comp_aestronglyMeasurable
          (haM.smul (hDc e1 y).aestronglyMeasurable))
    · exact ((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℂ
        (ContinuousLinearMap.snd ℝ ℝ ℝ)).continuous.comp_aestronglyMeasurable
          (haM.smul (hDc e2 y).aestronglyMeasurable))
  have hF'int : IntervalIntegrable (F' y) volume 0 s := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.le]
    refine Integrable.mono' (g := fun _ => K * (M * ‖e1‖) + K * (M * ‖e2‖)) (integrable_const _)
      hF'meas ?_
    exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun σ hσ => hF'norm y σ hσ)
  have hdiff : ∀ t (x : ℝ × ℝ), HasFDerivAt (fun z => a t • planeHeat (ν * (s - t)) (sl t) z)
      (F' x t) x := by
    intro t x
    have hbd : ∃ M' : ℝ, ∀ w, ‖sl t w‖ ≤ M' := ⟨M, fun w => hM0 (t, w)⟩
    have hbd' : ∃ M' : ℝ, ∀ w, ‖fderiv ℝ (sl t) w‖ ≤ M' := ⟨M, fun w => hM1 t w⟩
    obtain ⟨hd0, -⟩ := hasFDerivAt_planeHeat hP (ν * (s - t)) (sl t) (hslC t) hbd hbd' x e1
    have key : fderiv ℝ (planeHeat (ν * (s - t)) (sl t)) x =
        (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (D e1 t x) +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (D e2 t x) := by
      refine ContinuousLinearMap.ext fun v => ?_
      have hv : v = v.1 • e1 + v.2 • e2 := by ext <;> simp [e1, e2]
      have f1 := (hasFDerivAt_planeHeat hP (ν * (s - t)) (sl t) (hslC t) hbd hbd' x e1).2
      have f2 := (hasFDerivAt_planeHeat hP (ν * (s - t)) (sl t) (hslC t) hbd hbd' x e2).2
      have e : fderiv ℝ (planeHeat (ν * (s - t)) (sl t)) x v =
          v.1 • fderiv ℝ (planeHeat (ν * (s - t)) (sl t)) x e1 +
            v.2 • fderiv ℝ (planeHeat (ν * (s - t)) (sl t)) x e2 := by
        conv_lhs => rw [hv]
        rw [map_add, map_smul, map_smul]
      rw [e, f1, f2]
      simp [D]
    have hL : a t • fderiv ℝ (planeHeat (ν * (s - t)) (sl t)) x = F' x t := by
      refine ContinuousLinearMap.ext fun v => ?_
      rw [hF'apply, ContinuousLinearMap.smul_apply, key]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
      simp only [Complex.real_smul, smul_eq_mul]
      ring
    rw [← hL]
    exact hd0.const_smul (a t)
  have hmain := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F := fun z σ => a σ • planeHeat (ν * (s - σ)) (sl σ) z) (F' := F') (x₀ := y)
    (s := univ) (μ := volume) (a := 0) (b := s)
    (bound := fun _ => K * (M * ‖e1‖) + K * (M * ‖e2‖)) Filter.univ_mem
    (Filter.Eventually.of_forall fun x => by
      rw [Set.uIoc_of_le hs.le]; exact haM.smul (hPc x).aestronglyMeasurable)
    (hintP y)
    (by rw [Set.uIoc_of_le hs.le]; exact hF'meas)
    (ae_of_all _ fun t ht x _ => hF'norm x t (by rwa [Set.uIoc_of_le hs.le] at ht))
    intervalIntegrable_const
    (ae_of_all _ fun t _ x _ => hdiff t x)
  refine ⟨∫ t in (0 : ℝ)..s, F' y t, hmain, fun v hv => ?_⟩
  rw [ContinuousLinearMap.intervalIntegral_apply hF'int v]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rcases hv with rfl | rfl
  · simp only [hF'apply, e1, e2, one_smul, zero_smul, add_zero, zero_add]
    rfl
  · simp only [hF'apply, e1, e2, one_smul, zero_smul, add_zero, zero_add]
    rfl

end UnforcedLeray.Short.PartIIa.N01.HIFD
