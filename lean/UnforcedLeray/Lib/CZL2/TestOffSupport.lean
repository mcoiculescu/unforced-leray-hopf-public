import UnforcedLeray.Lib.CZL2.RieszL2
import UnforcedLeray.Lib.CZL2.HessianKernel

/-!
# The Newton Hessian of a test off its support, and its decay (INF01 level L0, target T2)

Blueprint: INF01 target T2 (scoping note `INF01-CZ.md` §4.2, §5: `rieszPairTest_offSupport`,
`rieszPairTest_decay`). Manuscript: `R_iR_k = ∂_i∂_k(-Δ)^{-1}` (`paper/main.tex`
lines 107–111), whose off-support kernel is `K_ik = ∂_i∂_k N`.

* `spatialTestDerivative_newtonConv_eq`: `∂ₖ(N ∗ f)(y) = ∫ ∂ₖN(y - x) f(x) dx`.
* `rieszPairTest_offSupport`: if `x ∉ tsupport f`, then
  `∂ᵢ∂ₖ(N ∗ f)(x) = ∫ K_ik(x - y) f(y) dy`. The proof differentiates the kernel
  integral under the integral sign along the line `x + t eᵢ`, `|t| < δ`, where the
  kernel stays at distance `≥ δ` from its singularity
  (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`).
* `rieszPairTest_decay`: `|∂ᵢ∂ₖ(N ∗ f)(x)| ≤ C|x|⁻³` for `|x| ≥ R`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ContDiff ENNReal Topology

namespace UnforcedLeray.RieszLp

open PressureAnalysis

theorem rpow_neg_three_eq {a : ℝ} (ha : 0 ≤ a) : a ^ (-3 : ℝ) = (a ^ 3)⁻¹ := by
  rw [Real.rpow_neg ha, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- `|K_ik(z)| ≤ π⁻¹ δ⁻³` when `δ ≤ |z|`. -/
theorem abs_newtonHessianKernel_le_of_le (i k : Fin 3) {δ : ℝ} (hδ : 0 < δ) {z : Space}
    (hz : δ ≤ ‖z‖) : |newtonHessianKernel i k z| ≤ Real.pi⁻¹ * (δ ^ 3)⁻¹ := by
  refine (norm_newtonHessianKernel_le i k z).trans ?_
  rw [rpow_neg_three_eq (norm_nonneg z)]
  gcongr

/-- `|∂ₖN(z)| ≤ (4π)⁻¹ δ⁻²` when `δ ≤ |z|`. -/
theorem abs_newtonGradientKernel_le_of_le (k : Fin 3) {δ : ℝ} (hδ : 0 < δ) {z : Space}
    (hz : δ ≤ ‖z‖) : |newtonGradientKernel k z| ≤ (4 * Real.pi)⁻¹ * (δ ^ 2)⁻¹ := by
  have h := norm_newtonGradientKernel_le k z
  rw [Real.norm_eq_abs, Real.rpow_neg (norm_nonneg z), Real.rpow_two] at h
  refine h.trans ?_
  gcongr

theorem newtonGradientKernel_neg (k : Fin 3) (z : Space) :
    newtonGradientKernel k (-z) = -newtonGradientKernel k z := by
  simp [newtonGradientKernel, neg_div]

/-- `∂ₖ(N ∗ f)(y) = ∫ ∂ₖN(y - x) f(x) dx` for a compact smooth test `f`. -/
theorem spatialTestDerivative_newtonConv_eq {f : Space → ℝ} (hf : IsSpatialTest f)
    (k : Fin 3) (y : Space) :
    spatialTestDerivative k (newtonConv f) y = ∫ x, newtonGradientKernel k (y - x) * f x := by
  rw [spatialTestDerivative_newtonConv hf k, newtonConv_partial hf k y, newtonPair,
    ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [show y - x = -(x - y) by abel, newtonGradientKernel_neg, neg_mul]

/-- Away from the origin, `∂ᵢ(∂ₖN) = K_ik` as a classical derivative. -/
theorem fderiv_newtonGradientKernel_apply (i k : Fin 3) {z : Space} (hz : z ≠ 0) :
    fderiv ℝ (newtonGradientKernel k) z (coordinateVector i) = newtonHessianKernel i k z := by
  have hev : (fun y => fderiv ℝ newtonPotential y (coordinateVector k)) =ᶠ[𝓝 z]
      newtonGradientKernel k := by
    filter_upwards [isOpen_ne.mem_nhds hz] with y hy
    exact fderiv_newtonPotential_coordinate hy k
  rw [newtonHessianKernel_eq i k hz, hev.fderiv_eq]

/-- A point outside the closed support has positive distance to the support. -/
theorem exists_pos_le_norm_sub_of_notMem_tsupport {f : Space → ℝ} {x : Space}
    (hx : x ∉ tsupport f) : ∃ δ > 0, ∀ y, f y ≠ 0 → 2 * δ ≤ ‖x - y‖ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isClosed_tsupport f).isOpen_compl x hx
  refine ⟨ε / 2, by positivity, fun y hy => ?_⟩
  have hyt : y ∈ tsupport f := subset_tsupport f hy
  have hy' : y ∉ ball x ε := fun h => hball h hyt
  rw [mem_ball, not_lt, dist_eq_norm] at hy'
  rw [norm_sub_rev]
  linarith

/-- **INF01 T2.** Off the support of a compact smooth test `f`,
`∂ᵢ∂ₖ(N ∗ f)(x) = ∫ K_ik(x - y) f(y) dy`. -/
theorem rieszPairTest_offSupport {f : Space → ℝ} (hf : IsSpatialTest f) (i k : Fin 3)
    {x : Space} (hx : x ∉ tsupport f) :
    rieszPairTest i k f x = ∫ y, newtonHessianKernel i k (x - y) * f y := by
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_norm_sub_of_notMem_tsupport hx
  have he1 : ‖coordinateVector i‖ = 1 := norm_coordinateVector i
  have hHs : ContDiff ℝ ∞ (spatialTestDerivative k (newtonConv f)) :=
    contDiff_spatialTestDerivative (newtonConv_contDiff hf) k
  have hline : ∀ (y : Space) (t : ℝ),
      HasDerivAt (fun s : ℝ => x + s • coordinateVector i - y) (coordinateVector i) t :=
    fun y t => by
      simpa using (((hasDerivAt_id t).smul_const (coordinateVector i)).const_add x).sub_const y
  -- the derivative of `∂ₖ(N ∗ f)` along the line `x + t eᵢ`
  have h1 : HasDerivAt (fun t : ℝ => spatialTestDerivative k (newtonConv f)
      (x + t • coordinateVector i))
      (fderiv ℝ (spatialTestDerivative k (newtonConv f)) x (coordinateVector i)) 0 := by
    have hl : HasDerivAt (fun s : ℝ => x + s • coordinateVector i) (coordinateVector i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector i)).const_add x
    have hd : HasFDerivAt (spatialTestDerivative k (newtonConv f))
        (fderiv ℝ (spatialTestDerivative k (newtonConv f)) x)
        (x + (0 : ℝ) • coordinateVector i) := by
      rw [zero_smul, add_zero]
      exact (hHs.differentiable (by simp) x).hasFDerivAt
    exact hd.comp_hasDerivAt (0 : ℝ) hl
  have hfi : Integrable f volume := hf.continuous.integrable_of_hasCompactSupport hf.compact
  have hnear : ∀ y, f y ≠ 0 → ∀ t ∈ ball (0 : ℝ) δ,
      δ ≤ ‖x + t • coordinateVector i - y‖ := by
    intro y hy t ht
    have h2 := hsep y hy
    have ht' : |t| < δ := by simpa [Real.norm_eq_abs] using ht
    have hte : ‖t • coordinateVector i‖ = |t| := by
      rw [norm_smul, he1, mul_one, Real.norm_eq_abs]
    have h3 : ‖x - y‖ - ‖t • coordinateVector i‖ ≤ ‖x + t • coordinateVector i - y‖ := by
      have := norm_sub_norm_le (x - y) (-(t • coordinateVector i))
      rw [norm_neg, sub_neg_eq_add] at this
      calc ‖x - y‖ - ‖t • coordinateVector i‖ ≤ ‖x - y + t • coordinateVector i‖ := this
        _ = ‖x + t • coordinateVector i - y‖ := by congr 1; abel
    linarith
  have hmeasF : ∀ t : ℝ, AEStronglyMeasurable
      (fun y => newtonGradientKernel k (x + t • coordinateVector i - y) * f y) volume :=
    fun t => (((newtonGradientKernel_measurable k).comp
      (continuous_const.sub continuous_id).measurable).mul
        hf.continuous.measurable).aestronglyMeasurable
  have hmeasF' : ∀ t : ℝ, AEStronglyMeasurable
      (fun y => newtonHessianKernel i k (x + t • coordinateVector i - y) * f y) volume :=
    fun t => (((newtonHessianKernel_measurable i k).comp
      (continuous_const.sub continuous_id).measurable).mul
        hf.continuous.measurable).aestronglyMeasurable
  have hFint : Integrable
      (fun y => newtonGradientKernel k (x + (0 : ℝ) • coordinateVector i - y) * f y) volume := by
    refine (hfi.abs.const_mul ((4 * Real.pi)⁻¹ * (δ ^ 2)⁻¹)).mono' (hmeasF 0)
      (Eventually.of_forall fun y => ?_)
    by_cases hy : f y = 0
    · simp [hy]
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (abs_newtonGradientKernel_le_of_le k hδ (hnear y hy 0 (mem_ball_self hδ)))
        (abs_nonneg _)
  have hbound : ∀ᵐ y ∂volume, ∀ t ∈ ball (0 : ℝ) δ,
      ‖newtonHessianKernel i k (x + t • coordinateVector i - y) * f y‖ ≤
        Real.pi⁻¹ * (δ ^ 3)⁻¹ * |f y| := Eventually.of_forall fun y t ht => by
    by_cases hy : f y = 0
    · simp [hy]
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (abs_newtonHessianKernel_le_of_le i k hδ (hnear y hy t ht)) (abs_nonneg _)
  have hdiff : ∀ᵐ y ∂volume, ∀ t ∈ ball (0 : ℝ) δ,
      HasDerivAt (fun s : ℝ => newtonGradientKernel k (x + s • coordinateVector i - y) * f y)
        (newtonHessianKernel i k (x + t • coordinateVector i - y) * f y) t :=
    Eventually.of_forall fun y t ht => by
      by_cases hy : f y = 0
      · simp only [hy, mul_zero]
        exact hasDerivAt_const t (0 : ℝ)
      · have hz : x + t • coordinateVector i - y ≠ 0 := by
          intro h0
          have := hnear y hy t ht
          rw [h0, norm_zero] at this
          linarith
        have hG : HasFDerivAt (newtonGradientKernel k)
            (fderiv ℝ (newtonGradientKernel k) (x + t • coordinateVector i - y))
            (x + t • coordinateVector i - y) :=
          (hasFDerivAt_newtonGradientKernel k hz).differentiableAt.hasFDerivAt
        have h := (hG.comp_hasDerivAt t (hline y t)).mul_const (f y)
        rw [fderiv_newtonGradientKernel_apply i k hz] at h
        exact h
  obtain ⟨-, h2⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t y => newtonGradientKernel k (x + t • coordinateVector i - y) * f y)
    (F' := fun t y => newtonHessianKernel i k (x + t • coordinateVector i - y) * f y)
    (ball_mem_nhds (0 : ℝ) hδ) (Eventually.of_forall hmeasF) hFint (hmeasF' 0) hbound
    (hfi.abs.const_mul _) hdiff
  have hfun : (fun t : ℝ => ∫ y, newtonGradientKernel k (x + t • coordinateVector i - y) * f y) =
      fun t => spatialTestDerivative k (newtonConv f) (x + t • coordinateVector i) := by
    funext t
    rw [spatialTestDerivative_newtonConv_eq hf k]
  rw [hfun] at h2
  have hu := h1.unique h2
  change fderiv ℝ (spatialTestDerivative k (newtonConv f)) x (coordinateVector i) = _
  rw [hu]
  simp only [zero_smul, add_zero]

/-- **INF01 T2.** Decay `|∂ᵢ∂ₖ(N ∗ f)(x)| ≤ C|x|⁻³` far out, for a compact smooth test. -/
theorem rieszPairTest_decay {f : Space → ℝ} (hf : IsSpatialTest f) (i k : Fin 3) :
    ∃ C R : ℝ, ∀ x : Space, R ≤ ‖x‖ → |rieszPairTest i k f x| ≤ C * ‖x‖ ^ (-3 : ℝ) := by
  obtain ⟨ρ, hρ⟩ := hf.compact.isCompact.isBounded.subset_closedBall 0
  have hfi : Integrable f volume := hf.continuous.integrable_of_hasCompactSupport hf.compact
  refine ⟨8 * Real.pi⁻¹ * ∫ y, |f y|, 2 * |ρ| + 1, fun x hx => ?_⟩
  have hρa := le_abs_self ρ
  have hxpos : 0 < ‖x‖ := by linarith [abs_nonneg ρ]
  have hsupp : ∀ y, y ∈ tsupport f → ‖y‖ ≤ |ρ| := fun y hy => by
    have := hρ hy
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  have hxt : x ∉ tsupport f := fun h => by
    have := hsupp x h
    linarith [abs_nonneg ρ]
  rw [rieszPairTest_offSupport hf i k hxt, rpow_neg_three_eq hxpos.le]
  have hpt : ∀ y, ‖newtonHessianKernel i k (x - y) * f y‖ ≤
      8 * Real.pi⁻¹ * (‖x‖ ^ 3)⁻¹ * |f y| := by
    intro y
    by_cases hy : f y = 0
    · simp [hy]
    · have hy' := hsupp y (subset_tsupport f hy)
      have hd : ‖x‖ / 2 ≤ ‖x - y‖ := by
        have := norm_sub_norm_le x y
        linarith
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      refine (abs_newtonHessianKernel_le_of_le i k (by positivity) hd).trans (le_of_eq ?_)
      field_simp
      ring
  have h := norm_integral_le_of_norm_le (hfi.abs.const_mul (8 * Real.pi⁻¹ * (‖x‖ ^ 3)⁻¹))
    (Eventually.of_forall hpt)
  rw [integral_const_mul, Real.norm_eq_abs] at h
  exact h.trans (le_of_eq (by ring))

end UnforcedLeray.RieszLp
