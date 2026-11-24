import UnforcedLeray.Lib.Parabolic.Fourier

/-!
# The causal Duhamel integral on test functions (INF02 T6)


step 1 ("define `T_{ij}` on `C_c^∞` by `T_{ij}f = ∂_{ij}u`, with `u` the Duhamel integral (a
classical derivative); this needs no principal value or truncation") and §5 target T6.
Manuscript: eq:free-stress-11 (`paper/main.tex` lines 7447–7477, blueprint unit B0423), whose
causal kernel is `1_{θ>0}∂_{ij}H_θ` (line 7466).

* `causalHeat ν (s, y) = 1_{s>0} G_{νs}(y)`, the fundamental solution of `∂_t - νΔ`
  (`ν > 0`); it is locally integrable (`locallyIntegrable_causalHeat`) with unit spatial mass
  at each positive time (`integral_causalHeat_slice`).
* `duhamel ν f (t,x) = ∫_{s>0} ∫ G_{νs}(y) f(t-s, x-y) dy ds = (causalHeat ν ⋆ f)(t,x)`.
* For a test `f`, `duhamel ν f` is `C^∞` (`contDiff_duhamel`) and derivatives fall on `f`
  (`dirD_duhamel`).
* `secondDerivTest ν i j f = duhamel ν (∂_i∂_j f) = ∂_i∂_j (duhamel ν f)` (`sD2_duhamel`).
* `duhamel_eq_iterated`: the iterated form `∫_s ∫_y` used by the `L²` estimate.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Parabolic

open MeasureTheory Real Set
open scoped ENNReal NNReal ContDiff Convolution

open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {d : ℕ}

/-- The causal heat kernel `1_{s>0} G_{νs}(y)` on `ℝ × ℝ^d`. -/
def causalHeat (ν : ℝ) (Y : PS d) : ℝ := if 0 < Y.1 then gaussKernel d (ν * Y.1) Y.2 else 0

theorem causalHeat_of_pos (ν : ℝ) {Y : PS d} (h : 0 < Y.1) :
    causalHeat ν Y = gaussKernel d (ν * Y.1) Y.2 := by simp [causalHeat, h]

theorem causalHeat_of_nonpos (ν : ℝ) {Y : PS d} (h : Y.1 ≤ 0) : causalHeat ν Y = 0 := by
  simp [causalHeat, not_lt.2 h]

theorem causalHeat_nonneg {ν : ℝ} (hν : 0 < ν) (Y : PS d) : 0 ≤ causalHeat ν Y := by
  unfold causalHeat
  split_ifs with h
  · exact Gaussian.gaussKernel_nonneg (mul_pos hν h) _
  · exact le_rfl

theorem measurable_causalHeat (ν : ℝ) : Measurable (causalHeat (d := d) ν) := by
  unfold causalHeat Gaussian.gaussKernel
  refine Measurable.ite (measurableSet_lt measurable_const measurable_fst) ?_ measurable_const
  fun_prop

/-- Unit spatial mass at positive times. -/
theorem lintegral_causalHeat_slice {ν : ℝ} (hν : 0 < ν) (s : ℝ) :
    ∫⁻ y : Euc d, ENNReal.ofReal (causalHeat ν (s, y)) = if 0 < s then 1 else 0 := by
  split_ifs with hs
  · have h := ofReal_integral_eq_lintegral_ofReal (Gaussian.integrable_gaussKernel
      (d := d) (mul_pos hν hs)) (Filter.Eventually.of_forall fun y =>
        Gaussian.gaussKernel_nonneg (mul_pos hν hs) y)
    rw [Gaussian.integral_gaussKernel (mul_pos hν hs), ENNReal.ofReal_one] at h
    rw [h]
    congr 1; funext y
    rw [causalHeat_of_pos ν (Y := (s, y)) hs]
  · simp [causalHeat_of_nonpos ν (Y := (s, _)) (not_lt.1 hs)]

theorem integral_causalHeat_slice {ν : ℝ} (hν : 0 < ν) {s : ℝ} (hs : 0 < s) :
    ∫ y : Euc d, causalHeat ν (s, y) = 1 := by
  simp only [causalHeat_of_pos ν (Y := (s, _)) hs]
  exact Gaussian.integral_gaussKernel (mul_pos hν hs)

/-- `causalHeat ν` is integrable on every time slab `[-T, T] × ℝ^d`. -/
theorem integrableOn_causalHeat {ν : ℝ} (hν : 0 < ν) (T : ℝ) :
    IntegrableOn (causalHeat (d := d) ν) (Icc (-T) T ×ˢ univ) volume := by
  refine ⟨(measurable_causalHeat ν).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have hrw : ∀ Y : PS d, ‖causalHeat ν Y‖ₑ = ENNReal.ofReal (causalHeat ν Y) := fun Y => by
    rw [← ofReal_norm, Real.norm_of_nonneg (causalHeat_nonneg hν Y)]
  simp_rw [hrw]
  have hprod : (volume : Measure (PS d)).restrict (Icc (-T) T ×ˢ univ) =
      (volume.restrict (Icc (-T) T)).prod (volume.restrict univ) :=
    (Measure.prod_restrict _ _).symm
  rw [hprod, lintegral_prod _ ((measurable_causalHeat ν).ennreal_ofReal.aemeasurable),
    Measure.restrict_univ]
  simp_rw [lintegral_causalHeat_slice hν]
  calc ∫⁻ s in Icc (-T) T, (if 0 < s then (1 : ℝ≥0∞) else 0)
      ≤ ∫⁻ _s in Icc (-T) T, (1 : ℝ≥0∞) := lintegral_mono fun s => by split_ifs <;> simp
    _ < ⊤ := by simp

theorem locallyIntegrable_causalHeat {ν : ℝ} (hν : 0 < ν) :
    LocallyIntegrable (causalHeat (d := d) ν) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine (integrableOn_causalHeat hν R).mono_set fun Y hY => ?_
  have hm := hR hY
  rw [Metric.mem_closedBall, dist_zero_right] at hm
  have h1 : |Y.1| ≤ R := by rw [← Real.norm_eq_abs]; exact (norm_fst_le Y).trans hm
  exact ⟨⟨by linarith [neg_abs_le Y.1], by linarith [le_abs_self Y.1]⟩, mem_univ _⟩

/-- **The causal Duhamel integral** `u(t,x) = ∫ causalHeat ν (Y) f((t,x) - Y) dY`. -/
def duhamel (ν : ℝ) (f : PS d → ℝ) (X : PS d) : ℝ := ∫ Y, causalHeat ν Y * f (X - Y)

theorem duhamel_eq_convolution (ν : ℝ) (f : PS d → ℝ) :
    duhamel ν f = causalHeat ν ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f := by
  funext X
  rw [convolution_def]
  rfl

theorem integrable_causalHeat_mul {ν : ℝ} (hν : 0 < ν) {f : PS d → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (X : PS d) :
    Integrable (fun Y => causalHeat ν Y * f (X - Y)) volume := by
  have := (locallyIntegrable_causalHeat (d := d) hν).integrable_smul_right_of_hasCompactSupport
    (g := fun Y => f (X - Y)) (hf.comp (continuous_const.sub continuous_id))
    (hfc.comp_homeomorph (Homeomorph.subLeft X))
  simpa [smul_eq_mul] using this

/-- `duhamel ν f` of a test is `C^∞`. -/
theorem contDiff_duhamel {ν : ℝ} (hν : 0 < ν) {f : PS d → ℝ} (hf : IsSTTest f) :
    ContDiff ℝ ∞ (duhamel ν f) := by
  rw [duhamel_eq_convolution]
  exact hf.2.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (locallyIntegrable_causalHeat hν) hf.1

theorem continuous_duhamel {ν : ℝ} (hν : 0 < ν) {f : PS d → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) : Continuous (duhamel ν f) := by
  rw [duhamel_eq_convolution]
  exact hfc.continuous_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (locallyIntegrable_causalHeat hν) hf

/-- Derivatives of `duhamel ν f` fall on the test `f`. -/
theorem dirD_duhamel {ν : ℝ} (hν : 0 < ν) {f : PS d → ℝ} (hf : IsSTTest f) (v : PS d) :
    dirD v (duhamel ν f) = duhamel ν (dirD v f) := by
  funext X
  have hloc := locallyIntegrable_causalHeat (d := d) hν
  have h := hf.2.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hloc
    (hf.1.of_le (by simp)) X
  rw [← duhamel_eq_convolution] at h
  rw [dirD, h.fderiv, convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hloc
    (hf.2.fderiv (𝕜 := ℝ)) (hf.1.continuous_fderiv (by simp)) X v, ← duhamel_eq_convolution]
  rfl

/-- **INF02 T6, test level.** `T_{ij}f = duhamel ν (∂_i∂_j f)`. -/
def secondDerivTest (ν : ℝ) (i j : Fin d) (f : PS d → ℝ) : PS d → ℝ := duhamel ν (sD2 i j f)

/-- `T_{ij}f = ∂_i∂_j u` for the Duhamel solution `u = duhamel ν f` (classical derivatives). -/
theorem sD2_duhamel {ν : ℝ} (hν : 0 < ν) {f : PS d → ℝ} (hf : IsSTTest f) (i j : Fin d) :
    sD2 i j (duhamel ν f) = secondDerivTest ν i j f := by
  unfold sD2 sD secondDerivTest
  rw [dirD_duhamel hν hf, dirD_duhamel hν (hf.dirD _)]

theorem continuous_secondDerivTest {ν : ℝ} (hν : 0 < ν) {f : PS d → ℝ} (hf : IsSTTest f)
    (i j : Fin d) : Continuous (secondDerivTest ν i j f) :=
  continuous_duhamel hν (hf.sD2 i j).continuous (hf.sD2 i j).2

theorem duhamel_add {ν : ℝ} (hν : 0 < ν) {f g : PS d → ℝ} (hf : IsSTTest f) (hg : IsSTTest g) :
    duhamel ν (f + g) = duhamel ν f + duhamel ν g := by
  funext X
  simp only [duhamel, Pi.add_apply, mul_add]
  exact integral_add (integrable_causalHeat_mul hν hf.continuous hf.2 X)
    (integrable_causalHeat_mul hν hg.continuous hg.2 X)

theorem duhamel_smul (ν c : ℝ) (f : PS d → ℝ) : duhamel ν (c • f) = c • duhamel ν f := by
  funext X
  simp only [duhamel, Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  congr 1; funext Y; ring

/-- The iterated form `∫_s ∫_y`. -/
theorem duhamel_eq_iterated {ν : ℝ} (hν : 0 < ν) {f : PS d → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (X : PS d) :
    duhamel ν f X = ∫ s, ∫ y, causalHeat ν (s, y) * f (X.1 - s, X.2 - y) := by
  have h := integral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Euc d))) _
    (integrable_causalHeat_mul hν hf hfc X)
  exact h

theorem duhamel_slice_of_pos (ν : ℝ) (f : PS d → ℝ) (X : PS d) {s : ℝ} (hs : 0 < s) :
    (∫ y, causalHeat ν (s, y) * f (X.1 - s, X.2 - y)) =
      ∫ y, gaussKernel d (ν * s) y * f (X.1 - s, X.2 - y) := by
  congr 1; funext y; rw [causalHeat_of_pos ν (Y := (s, y)) hs]

theorem duhamel_slice_of_nonpos (ν : ℝ) (f : PS d → ℝ) (X : PS d) {s : ℝ} (hs : s ≤ 0) :
    (∫ y, causalHeat ν (s, y) * f (X.1 - s, X.2 - y)) = 0 := by
  simp [causalHeat_of_nonpos ν (Y := (s, _)) hs]

end UnforcedLeray.Parabolic
