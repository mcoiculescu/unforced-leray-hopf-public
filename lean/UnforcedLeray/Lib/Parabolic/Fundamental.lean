import UnforcedLeray.Lib.Parabolic.OffSupport

/-!
# The causal heat kernel is a fundamental solution on tests (INF02 T8, first step)


target T8 ("identification"), and §4 BP-B step 1. Manuscript: eq:free-stress-11
(`paper/main.tex` lines 7447–7477, blueprint unit B0423): "the causal heat formula applies".

* `fderiv_gaussKernel_one_apply`: `∂_v G_1(z) = -(1/2)⟨z, v⟩ G_1(z)`.
* `integral_gaussKernel_scale`: `∫ G_{c²}(y) f(y) dy = ∫ G_1(z) f(c z) dz` for `c > 0`.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Parabolic

open MeasureTheory Real Set Filter
open scoped ENNReal NNReal ContDiff Topology RealInnerProductSpace

open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {d : ℕ}

/-- `∂_v G_1(z) = -(1/2)⟨z, v⟩ G_1(z)`. -/
theorem fderiv_gaussKernel_one_apply (z v : Euc d) :
    fderiv ℝ (gaussKernel d 1) z v = -(1 / 2) * ⟪z, v⟫ * gaussKernel d 1 z := by
  set K : ℝ := (4 * π * 1) ^ (-(d : ℝ) / 2)
  have hfun : gaussKernel d 1 = fun z : Euc d => K * Real.exp (-(1 / 4) * ‖z‖ ^ 2) := by
    funext z; unfold Gaussian.gaussKernel; congr 2; ring
  have hn : HasFDerivAt (fun z : Euc d => ‖z‖ ^ 2) (2 • (innerSL ℝ z).comp
      (ContinuousLinearMap.id ℝ (Euc d))) z := (hasFDerivAt_id z).norm_sq
  have h := ((hn.const_mul (-(1 / 4))).exp).const_mul K
  rw [hfun, h.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  rw [show ((innerSL ℝ) z) v = ⟪z, v⟫ from rfl]
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-- **Gaussian scaling of an integral.** `∫ G_{c²}(y) f(y) dy = ∫ G_1(z) f(c z) dz`, `c > 0`. -/
theorem integral_gaussKernel_scale {c : ℝ} (hc : 0 < c) (f : Euc d → ℝ) :
    ∫ y, gaussKernel d (c ^ 2) y * f y = ∫ z, gaussKernel d 1 z * f (c • z) := by
  have h := MeasureTheory.Measure.integral_comp_smul (volume : Measure (Euc d))
    (fun y => gaussKernel d (c ^ 2) y * f y) c
  rw [Gaussian.finrank_euc] at h
  have hscale : ∀ z : Euc d, gaussKernel d (c ^ 2) (c • z) = c ^ (-(d : ℝ)) * gaussKernel d 1 z := by
    intro z
    have := Gaussian.gaussKernel_scale (d := d) (lam := c) (θ := 1) hc one_pos z
    rwa [mul_one] at this
  simp_rw [hscale] at h
  have hcd : (0 : ℝ) < c ^ d := pow_pos hc d
  rw [abs_of_pos (inv_pos.2 hcd)] at h
  have hcd' : c ^ (-(d : ℝ)) = (c ^ d)⁻¹ := by rw [Real.rpow_neg hc.le, Real.rpow_natCast]
  simp_rw [hcd', mul_assoc] at h
  rw [integral_const_mul, smul_eq_mul] at h
  exact (mul_left_cancel₀ (inv_ne_zero hcd.ne') h).symm

theorem norm_mul_gauss_le (z : Euc d) :
    ‖z‖ * gaussKernel d 1 z ≤ 2 * (4 * π * 1) ^ (-(d : ℝ) / 2) * Real.exp (-(1 / 8) * ‖z‖ ^ 2) := by
  have hr : ‖z‖ ≤ 2 * Real.exp ((1 / 8) * ‖z‖ ^ 2) := by
    have := Real.add_one_le_exp ((1 / 8) * ‖z‖ ^ 2)
    nlinarith [sq_nonneg (‖z‖ - 2)]
  have hsplit : Real.exp (-‖z‖ ^ 2 / (4 * 1)) =
      Real.exp (-(1 / 8) * ‖z‖ ^ 2) * Real.exp (-(1 / 8) * ‖z‖ ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold Gaussian.gaussKernel
  rw [hsplit]
  have hK : 0 ≤ (4 * π * 1) ^ (-(d : ℝ) / 2) := by positivity
  have he : 0 ≤ Real.exp (-(1 / 8) * ‖z‖ ^ 2) := (Real.exp_pos _).le
  have hprod : ‖z‖ * Real.exp (-(1 / 8) * ‖z‖ ^ 2) ≤ 2 := by
    calc ‖z‖ * Real.exp (-(1 / 8) * ‖z‖ ^ 2)
        ≤ 2 * Real.exp ((1 / 8) * ‖z‖ ^ 2) * Real.exp (-(1 / 8) * ‖z‖ ^ 2) := by gcongr
      _ = 2 := by rw [mul_assoc, ← Real.exp_add]; simp
  calc ‖z‖ * ((4 * π * 1) ^ (-(d : ℝ) / 2) *
        (Real.exp (-(1 / 8) * ‖z‖ ^ 2) * Real.exp (-(1 / 8) * ‖z‖ ^ 2)))
      = (4 * π * 1) ^ (-(d : ℝ) / 2) * (‖z‖ * Real.exp (-(1 / 8) * ‖z‖ ^ 2)) *
          Real.exp (-(1 / 8) * ‖z‖ ^ 2) := by ring
    _ ≤ (4 * π * 1) ^ (-(d : ℝ) / 2) * 2 * Real.exp (-(1 / 8) * ‖z‖ ^ 2) := by gcongr
    _ = _ := by ring

theorem integrable_norm_mul_gauss : Integrable (fun z : Euc d => ‖z‖ * gaussKernel d 1 z) := by
  have h := Gaussian.integrable_exp_neg_mul_sq_norm (d := d) (b := 1 / 8) (by norm_num)
  have h2 : Integrable (fun z : Euc d => Real.exp (-(1 / 8) * ‖z‖ ^ 2)) volume := by
    simpa [neg_mul] using h
  refine (h2.const_mul (2 * (4 * π * 1) ^ (-(d : ℝ) / 2))).mono'
    ((continuous_norm.mul (Gaussian.continuous_gaussKernel 1)).aestronglyMeasurable)
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Gaussian.gaussKernel_nonneg one_pos z))]
  exact (norm_mul_gauss_le z).trans (le_of_eq (by ring))

/-- **Gaussian integration by parts.** `∫ G_1(z) ⟨z, e_k⟩ ψ(z) dz = 2 ∫ G_1(z) ∂_k ψ(z) dz`. -/
theorem integral_gauss_mul_inner {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (k : Fin d) :
    ∫ z, gaussKernel d 1 z * (⟪z, ev k⟫ * ψ z) = 2 * ∫ z, gaussKernel d 1 z * fderiv ℝ ψ z (ev k) := by
  have hG : ContDiff ℝ 1 (gaussKernel d 1) := Gaussian.contDiff_gaussKernel 1
  have h := integral_mul_fderiv_euc hG hψ hψc (ev k)
  simp_rw [fderiv_gaussKernel_one_apply] at h
  have e : ∀ z, -(1 / 2) * ⟪z, ev k⟫ * gaussKernel d 1 z * ψ z =
      -(1 / 2) * (gaussKernel d 1 z * (⟪z, ev k⟫ * ψ z)) := fun z => by ring
  simp_rw [e, integral_const_mul] at h
  linarith

section FS

variable {ν : ℝ}

/-- The scaled point `(t - s, x - √(νs) z)`. -/
def scaledPt (ν : ℝ) (X : PS d) (s : ℝ) (z : Euc d) : PS d :=
  (X.1 - s, X.2 - Real.sqrt (ν * s) • z)

/-- `A(s) = ∫ G_1(z) g(t - s, x - √(νs) z) dz`. -/
def heatAvg (ν : ℝ) (g : PS d → ℝ) (X : PS d) (s : ℝ) : ℝ :=
  ∫ z, gaussKernel d 1 z * g (scaledPt ν X s z)

theorem slice_eq_heatAvg (hν : 0 < ν) (h : PS d → ℝ) (X : PS d) {s : ℝ} (hs : 0 < s) :
    ∫ y, causalHeat ν (s, y) * h (X.1 - s, X.2 - y) = heatAvg ν h X s := by
  have hc : 0 < Real.sqrt (ν * s) := Real.sqrt_pos.2 (mul_pos hν hs)
  have hsq : ν * s = Real.sqrt (ν * s) ^ 2 := (Real.sq_sqrt (mul_pos hν hs).le).symm
  simp only [causalHeat_of_pos ν (Y := (s, _)) hs]
  rw [hsq, integral_gaussKernel_scale hc (fun y => h (X.1 - s, X.2 - y))]
  rfl

theorem integrable_gauss_mul_bdd {b : Euc d → ℝ} (hb : Continuous b) {M : ℝ}
    (hM : ∀ z, |b z| ≤ M) : Integrable (fun z => gaussKernel d 1 z * b z) volume :=
  (Gaussian.integrable_gaussKernel one_pos).mul_bdd hb.aestronglyMeasurable
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hM z)

theorem continuous_scaledPt (ν : ℝ) (X : PS d) :
    Continuous fun p : ℝ × Euc d => scaledPt ν X p.1 p.2 := by
  unfold scaledPt; fun_prop

theorem heatAvg_zero {g : PS d → ℝ} (X : PS d) : heatAvg ν g X 0 = g X := by
  unfold heatAvg scaledPt
  simp only [sub_zero, mul_zero, Real.sqrt_zero, zero_smul, Prod.mk.eta]
  rw [integral_mul_const, Gaussian.integral_gaussKernel one_pos, one_mul]

theorem continuous_heatAvg {g : PS d → ℝ} (hg : IsSTTest g) (X : PS d) :
    Continuous (heatAvg ν g X) := by
  obtain ⟨M, -, hM⟩ := hg.bounded
  refine continuous_of_dominated (bound := fun z => gaussKernel d 1 z * M)
    (fun s => ((Gaussian.continuous_gaussKernel 1).mul
      (hg.continuous.comp ((continuous_scaledPt ν X).comp (continuous_const.prodMk
        continuous_id)))).aestronglyMeasurable)
    (fun s => Eventually.of_forall fun z => ?_)
    ((Gaussian.integrable_gaussKernel one_pos).mul_const M)
    (Eventually.of_forall fun z => ?_)
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Gaussian.gaussKernel_nonneg one_pos z)]
    exact mul_le_mul_of_nonneg_left (hM _) (Gaussian.gaussKernel_nonneg one_pos z)
  · exact continuous_const.mul (hg.continuous.comp ((continuous_scaledPt ν X).comp
      (continuous_id.prodMk continuous_const)))

theorem heatAvg_eq_zero {g : PS d → ℝ} {R : ℝ} (hR : ∀ Y : PS d, g Y ≠ 0 → |Y.1| ≤ R)
    (X : PS d) {s : ℝ} (hs : X.1 + R < s) : heatAvg ν g X s = 0 := by
  unfold heatAvg
  have : ∀ z, g (scaledPt ν X s z) = 0 := by
    intro z; by_contra h
    have := hR _ h
    simp only [scaledPt] at this
    have := neg_abs_le (X.1 - s)
    linarith
  simp [this]

theorem scaled_hasCompactSupport {f : PS d → ℝ} (hf : IsSTTest f) (X : PS d) (s : ℝ) {c : ℝ}
    (hc : 0 < c) : HasCompactSupport (fun z : Euc d => f (X.1 - s, X.2 - c • z)) := by
  obtain ⟨R, -, hR⟩ := hf.spaceBound
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) ((R + ‖X.2‖) / c))
    fun z hz => ?_
  by_contra h
  have h1 := hR _ h
  simp only at h1
  apply hz
  rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hc]
  have : ‖c • z‖ ≤ R + ‖X.2‖ := by
    calc ‖c • z‖ = ‖X.2 - (X.2 - c • z)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖X.2‖ + ‖X.2 - c • z‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  rwa [norm_smul, Real.norm_of_nonneg hc.le, mul_comm] at this

theorem hasFDerivAt_scaled (X : PS d) (s c : ℝ) (z : Euc d) :
    HasFDerivAt (fun z : Euc d => ((X.1 - s, X.2 - c • z) : PS d))
      ((0 : Euc d →L[ℝ] ℝ).prod (0 - c • ContinuousLinearMap.id ℝ (Euc d))) z :=
  (hasFDerivAt_const (X.1 - s) z).prodMk
    ((hasFDerivAt_const X.2 z).sub ((hasFDerivAt_id (𝕜 := ℝ) z).const_smul c))

theorem fderiv_scaled_apply {f : PS d → ℝ} (hf : Differentiable ℝ f) (X : PS d) (s c : ℝ)
    (z v : Euc d) :
    fderiv ℝ (fun z : Euc d => f (X.1 - s, X.2 - c • z)) z v =
      -c * dirD (0, v) f (X.1 - s, X.2 - c • z) := by
  have h : HasFDerivAt (fun z : Euc d => f (X.1 - s, X.2 - c • z))
      ((fderiv ℝ f (X.1 - s, X.2 - c • z)).comp
        ((0 : Euc d →L[ℝ] ℝ).prod (0 - c • ContinuousLinearMap.id ℝ (Euc d)))) z :=
    (hf ((X.1 - s, X.2 - c • z))).hasFDerivAt.comp z (hasFDerivAt_scaled X s c z)
  rw [h.fderiv, ContinuousLinearMap.comp_apply]
  have e : ((0 : Euc d →L[ℝ] ℝ).prod (0 - c • ContinuousLinearMap.id ℝ (Euc d))) v =
      (-c) • ((0 : ℝ), v) := by
    ext <;> simp
  rw [e, map_smul, smul_eq_mul]
  rfl

theorem pair_zero_eq_sum (z : Euc d) : ((0, z) : PS d) = ∑ k, ⟪z, ev k⟫ • sdir k := by
  ext
  · simp [Prod.fst_sum]
  · rename_i j
    simp [Prod.snd_sum, EuclideanSpace.inner_single_right, Pi.single_apply]

theorem dirD_zero_eq_sum {f : PS d → ℝ} (X : PS d) (z : Euc d) :
    dirD (0, z) f X = ∑ k, ⟪z, ev k⟫ * sD k f X := by
  unfold dirD sD dirD
  rw [pair_zero_eq_sum z, map_sum]
  congr 1; funext k
  rw [map_smul, smul_eq_mul]

theorem isSTTest_tD {g : PS d → ℝ} (hg : IsSTTest g) : IsSTTest (tD g) := hg.dirD _

theorem isSTTest_sLap {g : PS d → ℝ} (hg : IsSTTest g) : IsSTTest (sLap g) := by
  have : sLap g = ∑ k : Fin d, sD2 k k g := by funext X; simp [sLap, Finset.sum_apply]
  rw [this]
  induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
  | empty => simpa using IsSTTest.zero
  | insert k S hk ih => rw [Finset.sum_insert hk]; exact (hg.sD2 k k).add ih

theorem isSTTest_heatOp {g : PS d → ℝ} (hg : IsSTTest g) (ν : ℝ) :
    IsSTTest (tD g - ν • sLap g) := by
  have h := (isSTTest_tD hg).add ((isSTTest_sLap hg).smul (-ν))
  have e : tD g - ν • sLap g = tD g + (-ν) • sLap g := by
    funext X; simp [sub_eq_add_neg]
  rw [e]; exact h

/-- **The derivative of the heat average.** `A'(s) = -∫ G_1(z) ((∂_t - νΔ) g)(t-s, x-√(νs) z)`. -/
theorem hasDerivAt_heatAvg (hν : 0 < ν) {g : PS d → ℝ} (hg : IsSTTest g) (X : PS d) {s₀ : ℝ}
    (hs₀ : 0 < s₀) :
    HasDerivAt (heatAvg ν g X) (-heatAvg ν (tD g - ν • sLap g) X s₀) s₀ := by
  obtain ⟨M, hM⟩ := (hg.1.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hg.2.fderiv (𝕜 := ℝ))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set cp : ℝ → ℝ := fun s => ν / (2 * Real.sqrt (ν * s)) with hcp
  set F' : ℝ → Euc d → ℝ := fun s z =>
    gaussKernel d 1 z * fderiv ℝ g (scaledPt ν X s z) ((-1 : ℝ), -(cp s) • z) with hF'
  have hball : ∀ s ∈ Metric.ball s₀ (s₀ / 2), s₀ / 2 < s := fun s hs => by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs; linarith [hs.1]
  have hpath : ∀ z : Euc d, ∀ s, 0 < s →
      HasDerivAt (fun s => scaledPt ν X s z) ((-1 : ℝ), -(cp s) • z) s := by
    intro z s hs
    have h1 : HasDerivAt (fun s : ℝ => X.1 - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub X.1
    have h2 : HasDerivAt (fun s : ℝ => Real.sqrt (ν * s)) (ν / (2 * Real.sqrt (ν * s))) s := by
      have := ((hasDerivAt_id s).const_mul ν).sqrt (mul_pos hν hs).ne'
      simpa using this
    have h3 : HasDerivAt (fun s : ℝ => X.2 - Real.sqrt (ν * s) • z) (-(cp s) • z) s := by
      have := (h2.smul_const z).const_sub X.2
      simpa [hcp, neg_smul] using this
    exact h1.prodMk h3
  have hdiff : ∀ z : Euc d, ∀ s ∈ Metric.ball s₀ (s₀ / 2),
      HasDerivAt (fun s => gaussKernel d 1 z * g (scaledPt ν X s z)) (F' s z) s := by
    intro z s hs
    have hs0 : 0 < s := by linarith [hball s hs]
    exact ((hg.differentiable _).hasFDerivAt.comp_hasDerivAt s (hpath z s hs0)).const_mul
      (gaussKernel d 1 z)
  have hcp_le : ∀ s ∈ Metric.ball s₀ (s₀ / 2), cp s ≤ cp (s₀ / 2) := by
    intro s hs
    have h1 := hball s hs
    simp only [hcp]
    apply div_le_div_of_nonneg_left hν.le (by positivity)
    gcongr
  have hbound : ∀ z, ∀ s ∈ Metric.ball s₀ (s₀ / 2),
      ‖F' s z‖ ≤ gaussKernel d 1 z * (M * (1 + cp (s₀ / 2) * ‖z‖)) := by
    intro z s hs
    simp only [hF', norm_mul, Real.norm_of_nonneg (Gaussian.gaussKernel_nonneg one_pos z)]
    refine mul_le_mul_of_nonneg_left ?_ (Gaussian.gaussKernel_nonneg one_pos z)
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have hv : ‖(((-1 : ℝ), -(cp s) • z) : PS d)‖ ≤ 1 + cp (s₀ / 2) * ‖z‖ := by
      have hcs : 0 ≤ cp s := by simp only [hcp]; positivity
      rw [Prod.norm_def]
      refine max_le ?_ ?_
      · simp only [norm_neg, norm_one]
        have : 0 ≤ cp (s₀ / 2) * ‖z‖ := by simp only [hcp]; positivity
        linarith
      · show ‖-(cp s) • z‖ ≤ _
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hcs]
        have := hcp_le s hs
        nlinarith [norm_nonneg z]
    exact mul_le_mul (hM _) hv (norm_nonneg _) hM0
  have hbint : Integrable (fun z : Euc d =>
      gaussKernel d 1 z * (M * (1 + cp (s₀ / 2) * ‖z‖))) volume := by
    have h1 := (Gaussian.integrable_gaussKernel (d := d) one_pos).mul_const M
    have h2 := (integrable_norm_mul_gauss (d := d)).const_mul (M * cp (s₀ / 2))
    refine (h1.add h2).congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply]; ring
  have hgc : ∀ s, Continuous fun z => g (scaledPt ν X s z) := fun s =>
    hg.continuous.comp ((continuous_scaledPt ν X).comp (continuous_const.prodMk continuous_id))
  obtain ⟨M0, -, hM0'⟩ := hg.bounded
  have hF'c : Continuous (F' s₀) := by
    simp only [hF']
    refine (Gaussian.continuous_gaussKernel 1).mul ?_
    have hv : Continuous fun z : Euc d => (((-1 : ℝ), -(cp s₀) • z) : PS d) := by fun_prop
    exact ((hg.1.continuous_fderiv (by simp)).comp ((continuous_scaledPt ν X).comp
      (continuous_const.prodMk continuous_id))).clm_apply hv
  obtain ⟨-, hder⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s z => gaussKernel d 1 z * g (scaledPt ν X s z)) (F' := F')
    (Metric.ball_mem_nhds s₀ (half_pos hs₀))
    (Eventually.of_forall fun s =>
      ((Gaussian.continuous_gaussKernel 1).mul (hgc s)).aestronglyMeasurable)
    (integrable_gauss_mul_bdd (hgc s₀) (fun z => hM0' _))
    hF'c.aestronglyMeasurable (Eventually.of_forall hbound) hbint (Eventually.of_forall hdiff)
  refine hder.congr_deriv ?_
  -- the identity `∫ F' s₀ = -heatAvg ν (∂_t g - νΔg) X s₀`
  have hcpos : 0 < Real.sqrt (ν * s₀) := Real.sqrt_pos.2 (mul_pos hν hs₀)
  have hcc : cp s₀ * (2 * Real.sqrt (ν * s₀)) = ν := by
    simp only [hcp]; field_simp
  have hPc : Continuous fun z => scaledPt ν X s₀ z :=
    (continuous_scaledPt ν X).comp (continuous_const.prodMk continuous_id)
  obtain ⟨Mt, -, hMt⟩ := (isSTTest_tD hg).bounded
  have hk : ∀ k : Fin d, ∃ Mk, ∀ Y, |sD k g Y| ≤ Mk := fun k =>
    let ⟨Mk, _, h⟩ := (hg.dirD (sdir k)).bounded; ⟨Mk, h⟩
  have hkk : ∀ k : Fin d, ∃ Mk, ∀ Y, |sD2 k k g Y| ≤ Mk := fun k =>
    let ⟨Mk, _, h⟩ := (hg.sD2 k k).bounded; ⟨Mk, h⟩
  have iT : Integrable (fun z => gaussKernel d 1 z * tD g (scaledPt ν X s₀ z)) volume :=
    integrable_gauss_mul_bdd ((isSTTest_tD hg).continuous.comp hPc) (fun z => hMt _)
  have iL : ∀ k : Fin d,
      Integrable (fun z => gaussKernel d 1 z * sD2 k k g (scaledPt ν X s₀ z)) volume :=
    fun k => let ⟨Mk, h⟩ := hkk k
      integrable_gauss_mul_bdd ((hg.sD2 k k).continuous.comp hPc) (fun z => h _)
  have iI : ∀ k : Fin d, Integrable (fun z => gaussKernel d 1 z *
      (⟪z, ev k⟫ * sD k g (scaledPt ν X s₀ z))) volume := by
    intro k
    obtain ⟨Mk, h⟩ := hk k
    refine ((integrable_norm_mul_gauss (d := d)).mul_const Mk).mono' ?_
      (Eventually.of_forall fun z => ?_)
    · exact ((Gaussian.continuous_gaussKernel 1).mul ((continuous_id.inner continuous_const).mul
        ((hg.dirD (sdir k)).continuous.comp hPc))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (Gaussian.gaussKernel_nonneg one_pos z)]
      have h1 : |⟪z, ev k⟫| ≤ ‖z‖ := by
        have := abs_real_inner_le_norm z (ev k)
        rwa [norm_ev, mul_one] at this
      calc gaussKernel d 1 z * (|⟪z, ev k⟫| * |sD k g (scaledPt ν X s₀ z)|)
          ≤ gaussKernel d 1 z * (‖z‖ * Mk) :=
            mul_le_mul_of_nonneg_left (mul_le_mul h1 (h _) (abs_nonneg _) (norm_nonneg _))
              (Gaussian.gaussKernel_nonneg one_pos z)
        _ = ‖z‖ * gaussKernel d 1 z * Mk := by ring
  have iS : Integrable (fun z => ∑ k : Fin d, gaussKernel d 1 z *
      (⟪z, ev k⟫ * sD k g (scaledPt ν X s₀ z))) volume :=
    integrable_finsetSum _ fun k _ => iI k
  have iLS : Integrable (fun z => ∑ k : Fin d, gaussKernel d 1 z *
      sD2 k k g (scaledPt ν X s₀ z)) volume :=
    integrable_finsetSum _ fun k _ => iL k
  -- (f1)
  have f1 : ∫ z, F' s₀ z = -(∫ z, gaussKernel d 1 z * tD g (scaledPt ν X s₀ z)) -
      cp s₀ * ∑ k : Fin d, ∫ z, gaussKernel d 1 z * (⟪z, ev k⟫ * sD k g (scaledPt ν X s₀ z)) := by
    have hpt : ∀ z, F' s₀ z = -(gaussKernel d 1 z * tD g (scaledPt ν X s₀ z)) -
        cp s₀ * ∑ k : Fin d, gaussKernel d 1 z * (⟪z, ev k⟫ * sD k g (scaledPt ν X s₀ z)) := by
      intro z
      simp only [hF']
      have hv : (((-1 : ℝ), -(cp s₀) • z) : PS d) =
          (-1 : ℝ) • tdir + (-(cp s₀)) • ((0 : ℝ), z) := by
        ext <;> simp
      rw [hv, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      have e1 : fderiv ℝ g (scaledPt ν X s₀ z) ((0 : ℝ), z) =
          dirD (0, z) g (scaledPt ν X s₀ z) := rfl
      have e2 : fderiv ℝ g (scaledPt ν X s₀ z) tdir = tD g (scaledPt ν X s₀ z) := rfl
      rw [e1, e2, dirD_zero_eq_sum]
      have hs : ∑ k : Fin d, gaussKernel d 1 z * (⟪z, ev k⟫ * sD k g (scaledPt ν X s₀ z)) =
          gaussKernel d 1 z * ∑ k : Fin d, ⟪z, ev k⟫ * sD k g (scaledPt ν X s₀ z) := by
        rw [Finset.mul_sum]
      rw [hs]; ring
    have iTn : Integrable (fun z => -(gaussKernel d 1 z * tD g (scaledPt ν X s₀ z))) volume :=
      iT.neg
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_sub iTn (iS.const_mul (cp s₀)),
      integral_neg, integral_const_mul, integral_finsetSum _ fun k _ => iI k]
  -- (f2)
  have f2 : ∀ k : Fin d, ∫ z, gaussKernel d 1 z * (⟪z, ev k⟫ * sD k g (scaledPt ν X s₀ z)) =
      -(2 * Real.sqrt (ν * s₀)) * ∫ z, gaussKernel d 1 z * sD2 k k g (scaledPt ν X s₀ z) := by
    intro k
    have hψ : ContDiff ℝ ∞ (fun z : Euc d =>
        sD k g (X.1 - s₀, X.2 - Real.sqrt (ν * s₀) • z)) :=
      (hg.dirD (sdir k)).1.comp (contDiff_const.prodMk (contDiff_const.sub
        (contDiff_id.const_smul _)))
    have hψc := scaled_hasCompactSupport (hg.dirD (sdir k)) X s₀ hcpos
    have h := integral_gauss_mul_inner (hψ.of_le (by simp)) hψc k
    simp only [scaledPt]
    rw [h]
    have e : ∀ z, fderiv ℝ (fun z : Euc d => sD k g (X.1 - s₀, X.2 - Real.sqrt (ν * s₀) • z))
        z (ev k) = -Real.sqrt (ν * s₀) * sD2 k k g (X.1 - s₀, X.2 - Real.sqrt (ν * s₀) • z) := by
      intro z
      rw [fderiv_scaled_apply (hg.dirD (sdir k)).differentiable]
    simp_rw [e]
    have e2 : ∀ z, gaussKernel d 1 z *
        (-Real.sqrt (ν * s₀) * sD2 k k g (X.1 - s₀, X.2 - Real.sqrt (ν * s₀) • z)) =
        -Real.sqrt (ν * s₀) * (gaussKernel d 1 z *
          sD2 k k g (X.1 - s₀, X.2 - Real.sqrt (ν * s₀) • z)) := fun z => by ring
    simp_rw [e2, integral_const_mul]
    ring
  -- (f3)
  have f3 : heatAvg ν (tD g - ν • sLap g) X s₀ =
      (∫ z, gaussKernel d 1 z * tD g (scaledPt ν X s₀ z)) -
        ν * ∑ k : Fin d, ∫ z, gaussKernel d 1 z * sD2 k k g (scaledPt ν X s₀ z) := by
    unfold heatAvg
    have hpt : ∀ z, gaussKernel d 1 z * (tD g - ν • sLap g) (scaledPt ν X s₀ z) =
        gaussKernel d 1 z * tD g (scaledPt ν X s₀ z) -
          ν * ∑ k : Fin d, gaussKernel d 1 z * sD2 k k g (scaledPt ν X s₀ z) := by
      intro z
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sLap]
      have hs : ∑ k : Fin d, gaussKernel d 1 z * sD2 k k g (scaledPt ν X s₀ z) =
          gaussKernel d 1 z * ∑ k : Fin d, sD2 k k g (scaledPt ν X s₀ z) := by
        rw [Finset.mul_sum]
      rw [hs]
      try ring
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_sub iT (iLS.const_mul ν),
      integral_const_mul, integral_finsetSum _ fun k _ => iL k]
  rw [f1, f3]
  simp_rw [f2]
  rw [← Finset.mul_sum]
  have : cp s₀ * (-(2 * Real.sqrt (ν * s₀)) *
      ∑ k : Fin d, ∫ z, gaussKernel d 1 z * sD2 k k g (scaledPt ν X s₀ z)) =
      -ν * ∑ k : Fin d, ∫ z, gaussKernel d 1 z * sD2 k k g (scaledPt ν X s₀ z) := by
    rw [← mul_assoc, mul_neg, hcc]
    try ring
  rw [this]; ring

/-- **The causal heat kernel is a fundamental solution.** For a test `g` and `ν > 0`,
`H_ν ⋆ ((∂_t - νΔ) g) = g`. -/
theorem duhamel_heatOp (hν : 0 < ν) {g : PS d → ℝ} (hg : IsSTTest g) :
    duhamel ν (tD g - ν • sLap g) = g := by
  funext X
  set h := tD g - ν • sLap g with hhdef
  have hh : IsSTTest h := isSTTest_heatOp hg ν
  obtain ⟨Rg, -, hRg⟩ := hg.timeBound
  obtain ⟨Rh, -, hRh⟩ := hh.timeBound
  set S : ℝ := max (X.1 + max Rg Rh + 1) 1 with hS
  have hS0 : 0 < S := lt_of_lt_of_le one_pos (le_max_right _ _)
  rw [duhamel_eq_iterated hν hh.continuous hh.2]
  have hin : ∀ s, (∫ y, causalHeat ν (s, y) * h (X.1 - s, X.2 - y)) =
      (Ioc 0 S).indicator (heatAvg ν h X) s := by
    intro s
    by_cases hs : s ∈ Ioc 0 S
    · rw [indicator_of_mem hs, slice_eq_heatAvg hν h X hs.1]
    · rw [indicator_of_notMem hs]
      rcases le_or_gt s 0 with h0 | h0
      · exact duhamel_slice_of_nonpos ν h X h0
      · have hSs : S < s := by
          by_contra hle; exact hs ⟨h0, not_lt.1 hle⟩
        rw [slice_eq_heatAvg hν h X h0]
        refine heatAvg_eq_zero hRh X ?_
        have := le_max_left (X.1 + max Rg Rh + 1) 1
        have := le_max_right Rg Rh
        linarith
  simp_rw [hin]
  rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hS0.le]
  -- FTC
  have hcont : ContinuousOn (heatAvg ν g X) (Icc 0 S) := (continuous_heatAvg hg X).continuousOn
  have hderiv : ∀ s ∈ Ioo 0 S, HasDerivWithinAt (heatAvg ν g X) (-heatAvg ν h X s) (Ioi s) s :=
    fun s hs => (hasDerivAt_heatAvg hν hg X hs.1).hasDerivWithinAt
  have hint : IntegrableOn (fun s => -heatAvg ν h X s) (Icc 0 S) :=
    ((continuous_heatAvg hh X).neg.continuousOn).integrableOn_compact isCompact_Icc
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le_real hS0.le hcont hderiv
    hint
  rw [intervalIntegral.integral_neg] at hftc
  have hgS : heatAvg ν g X S = 0 := heatAvg_eq_zero hRg X (by
    have := le_max_left (X.1 + max Rg Rh + 1) 1
    have := le_max_left Rg Rh
    linarith)
  rw [hgS, heatAvg_zero] at hftc
  linarith

end FS

end UnforcedLeray.Parabolic
