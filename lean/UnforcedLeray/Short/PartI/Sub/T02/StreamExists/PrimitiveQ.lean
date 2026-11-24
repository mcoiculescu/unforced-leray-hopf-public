import UnforcedLeray.Short.PartI.Sub.T02_5
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part I, task `PartI:T02/5`: the `q`-primitive of a `C¹` function is `C¹`

Source of record: `the November 2 reference manuscript`, lines 261-288.

Target: `ContDiffPrimitiveQ` (`Short/PartI/Sub/T02_5.lean`) is proved from the
differentiation-under-the-integral lemma `HasDerivAtEtaIntervalIntegral`, taken as a black box.

For `f : Plane → ℝ` of class `C¹`, let `V(q, η) = ∫₀^q f(s, η) ds`.  The derivative of
`V` at `(a, b)` is the linear map `(p, r) ↦ f(a, b) p + D(a, b) r`, where
`D(a, b) = ∫₀^a ∂_η f(s, b) ds`.  The partial in `η` comes from `HasDerivAtEtaIntervalIntegral`;
the increment in `q` is the integral over `[a, a + p]`, which is `f(a, b) p + o(|h|)` by continuity
of `f`.  The map `z ↦ D z` is jointly continuous by the parametric integral lemma, and
`z ↦ f z` is continuous, so the derivative is continuous.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- **`PartI:T02/5`, primitive regularity** (source lines 261-288): the `q`-primitive of a `C¹`
function is `C¹`, given differentiation under the integral sign in `η`. -/
theorem contDiffPrimitiveQ (hD : HasDerivAtEtaIntervalIntegral) : ContDiffPrimitiveQ := by
  unfold ContDiffPrimitiveQ
  intro f hf
  have hfc : Continuous f := hf.continuous
  have hgc : Continuous (Cyl.partialEta f) :=
    (Cyl.contDiff_partialEta (n := 0) (h := f) (by simpa using hf)).continuous
  have hF : Continuous (Function.uncurry fun (z : Plane) (t : ℝ) => Cyl.partialEta f (t, z.2)) :=
    hgc.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
  have hDc : Continuous fun z : Plane => ∫ s in (0 : ℝ)..z.1, Cyl.partialEta f (s, z.2) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF continuous_fst
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨fun z => f z • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (∫ s in (0 : ℝ)..z.1, Cyl.partialEta f (s, z.2)) • ContinuousLinearMap.snd ℝ ℝ ℝ,
    (hfc.smul continuous_const).add (hDc.smul continuous_const), ?_⟩
  intro z0
  have hpart : HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..z0.1, f (s, y))
      (∫ s in (0 : ℝ)..z0.1, Cyl.partialEta f (s, z0.2)) z0.2 :=
    hD f hf 0 z0.1 z0.2
  have hlo := hasDerivAt_iff_isLittleO.1 hpart
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
  obtain ⟨δ1, hδ1, hcont⟩ :=
    Metric.continuousAt_iff.1 (hfc.continuousAt (x := z0)) (c / 2) (half_pos hc)
  obtain ⟨δ2, hδ2, hball⟩ :=
    Metric.eventually_nhds_iff.1 (hlo.def (half_pos hc))
  refine Metric.eventually_nhds_iff.2 ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
  intro h hh
  rw [dist_zero_right] at hh
  have hh1 : ‖h.1‖ ≤ ‖h‖ := norm_fst_le h
  have hh2 : ‖h.2‖ ≤ ‖h‖ := norm_snd_le h
  have hlt1 : ‖h‖ < δ1 := lt_of_lt_of_le hh (min_le_left _ _)
  have hlt2 : ‖h‖ < δ2 := lt_of_lt_of_le hh (min_le_right _ _)
  have h1lt : |h.1| < δ1 := by
    rw [← Real.norm_eq_abs]
    exact lt_of_le_of_lt hh1 hlt1
  have h2lt : |h.2| < δ1 := by
    rw [← Real.norm_eq_abs]
    exact lt_of_le_of_lt hh2 hlt1
  -- the `η`-increment: one-variable differentiability in `η`
  have hη : ‖(∫ s in (0 : ℝ)..z0.1, f (s, z0.2 + h.2)) - (∫ s in (0 : ℝ)..z0.1, f (s, z0.2))
      - h.2 * (∫ s in (0 : ℝ)..z0.1, Cyl.partialEta f (s, z0.2))‖ ≤ c / 2 * ‖h.2‖ := by
    have hd : dist (z0.2 + h.2) z0.2 < δ2 := by
      rw [Real.dist_eq, add_sub_cancel_left, ← Real.norm_eq_abs]
      exact lt_of_le_of_lt hh2 hlt2
    have := hball hd
    simp only [add_sub_cancel_left, smul_eq_mul] at this
    exact this
  -- the `q`-increment: the integral over `[z0.1, z0.1 + h.1]` is `f z0 * h.1 + o(|h|)`
  have hT1 : ‖∫ s in z0.1..(z0.1 + h.1), (f (s, z0.2 + h.2) - f z0)‖ ≤ c / 2 * ‖h.1‖ := by
    have hbound : ∀ s ∈ Set.uIoc z0.1 (z0.1 + h.1), ‖f (s, z0.2 + h.2) - f z0‖ ≤ c / 2 := by
      intro s hs
      have hsa : |s - z0.1| ≤ |h.1| := by
        rcases Set.mem_uIoc.1 hs with ⟨k₁, k₂⟩ | ⟨k₁, k₂⟩ <;>
          rw [abs_le] <;> constructor <;>
          linarith [le_abs_self h.1, neg_abs_le h.1, abs_nonneg h.1]
      have hpt : dist ((s, z0.2 + h.2) : Plane) z0 < δ1 := by
        rw [Prod.dist_eq]
        refine max_lt ?_ ?_
        · simp only [Real.dist_eq]
          exact lt_of_le_of_lt hsa h1lt
        · simp only [Real.dist_eq, add_sub_cancel_left]
          exact h2lt
      have hfz := hcont hpt
      rw [dist_eq_norm] at hfz
      exact hfz.le
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [add_sub_cancel_left, ← Real.norm_eq_abs] at this
    exact this
  -- integrability and the additivity splitting
  have hcs : Continuous fun s : ℝ => f (s, z0.2 + h.2) :=
    hfc.comp (continuous_id.prodMk continuous_const)
  have hint1 : IntervalIntegrable (fun s : ℝ => f (s, z0.2 + h.2)) volume 0 z0.1 :=
    hcs.intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun s : ℝ => f (s, z0.2 + h.2)) volume z0.1 (z0.1 + h.1) :=
    hcs.intervalIntegrable _ _
  have hint3 : IntervalIntegrable (fun _ : ℝ => f z0) volume z0.1 (z0.1 + h.1) :=
    continuous_const.intervalIntegrable _ _
  have hadj : ∫ s in (0 : ℝ)..(z0.1 + h.1), f (s, z0.2 + h.2)
      = (∫ s in (0 : ℝ)..z0.1, f (s, z0.2 + h.2)) + ∫ s in z0.1..(z0.1 + h.1), f (s, z0.2 + h.2) :=
    (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
  have hI : ∫ s in z0.1..(z0.1 + h.1), (f (s, z0.2 + h.2) - f z0)
      = (∫ s in z0.1..(z0.1 + h.1), f (s, z0.2 + h.2)) - h.1 * f z0 := by
    rw [intervalIntegral.integral_sub hint2 hint3, intervalIntegral.integral_const,
      add_sub_cancel_left, smul_eq_mul]
  have hmain : ‖(∫ s in z0.1..(z0.1 + h.1), (f (s, z0.2 + h.2) - f z0))
      + ((∫ s in (0 : ℝ)..z0.1, f (s, z0.2 + h.2)) - (∫ s in (0 : ℝ)..z0.1, f (s, z0.2))
        - h.2 * (∫ s in (0 : ℝ)..z0.1, Cyl.partialEta f (s, z0.2)))‖ ≤ c * ‖h‖ := by
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add hT1 hη).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hh1 hh2) (half_pos hc).le]
  refine (le_of_eq ?_).trans hmain
  congr 1
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst_add, Prod.snd_add,
    smul_eq_mul]
  rw [hadj, hI]
  ring

end UnforcedLeray.Short.PartI
