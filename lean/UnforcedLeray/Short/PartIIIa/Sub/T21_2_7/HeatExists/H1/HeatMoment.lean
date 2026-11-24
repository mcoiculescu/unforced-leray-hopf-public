import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.LeavesOf
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeatS0

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/1/3`: the axial Gaussian moment, uniform in `τ ∈ (0,1]`

Proves `AdjHeatMoment` (SP 2819-2836, 3044-3050).  The moment `kerAxialMoment m (adjHeatKer ν τ)`
equals `ofReal ∫ G_{ντ}(z) G-weight`, and the scaling `z = r·w` with `r = √τ ≤ 1` reduces the
integral to its value at time `ν`, uniformly in `τ ∈ (0,1]`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- One-dimensional Gaussian scaling at general diffusivity:
`G_{ν r²}(r x) = r⁻¹ G_ν(x)`. -/
theorem adjHM_heatKernel_scale {ν r : ℝ} (hν : 0 < ν) (hr : 0 < r) (x : ℝ) :
    UnforcedLeray.B0191.heatKernel 1 (ν * r ^ 2) (r * x) =
      r⁻¹ * UnforcedLeray.B0191.heatKernel 1 ν x := by
  have hroot : Real.sqrt (4 * Real.pi * 1 * (ν * r ^ 2)) =
      r * Real.sqrt (4 * Real.pi * 1 * ν) := by
    rw [show 4 * Real.pi * 1 * (ν * r ^ 2) = (4 * Real.pi * 1 * ν) * r ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hr.le]
    ring
  have hexp : -(r * x) ^ 2 / (4 * 1 * (ν * r ^ 2)) = -x ^ 2 / (4 * 1 * ν) := by
    have hr0 : r ≠ 0 := hr.ne'
    have hν0 : ν ≠ 0 := hν.ne'
    field_simp
  unfold UnforcedLeray.B0191.heatKernel
  rw [hroot, hexp, mul_inv]
  ring

/-- The planar Gaussian scaling at general diffusivity. -/
theorem adjHM_heatKernel2_scale {ν r : ℝ} (hν : 0 < ν) (hr : 0 < r) (w : ℝ × ℝ) :
    UnforcedLeray.B0284.heatKernel2 (ν * r ^ 2) (r • w) =
      (r ^ 2)⁻¹ * UnforcedLeray.B0284.heatKernel2 ν w := by
  rw [UnforcedLeray.B0284.heatKernel2, UnforcedLeray.B0284.heatKernel2]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [adjHM_heatKernel_scale hν hr w.1, adjHM_heatKernel_scale hν hr w.2]
  ring

theorem adjHM_axialWeight_nonneg (m : ℝ) (w : ℝ × ℝ) : 0 ≤ axialWeight m w := by
  unfold axialWeight axialBracket
  positivity

/-- Pointwise scaling bound for the axially weighted density at time `ν r²`, `r² ≤ 1`. -/
theorem adjHM_density_scale_le {ν r m : ℝ} (hν : 0 < ν) (hr : 0 < r) (hr2 : r ^ 2 ≤ 1)
    (hm : 0 ≤ m) (w : ℝ × ℝ) :
    axialHeatMomentDensity (ν * r ^ 2) m (r • w) ≤
      (r ^ 2)⁻¹ * axialHeatMomentDensity ν m w := by
  have hbase : 1 + (r * w.2) ^ 2 ≤ 1 + w.2 ^ 2 := by
    rw [mul_pow]
    nlinarith [sq_nonneg w.2]
  have hweight : axialWeight m (r • w) ≤ axialWeight m w := by
    rw [axialWeight, axialBracket_rpow, Prod.smul_snd,
      axialWeight, axialBracket_rpow]
    exact Real.rpow_le_rpow (by positivity) hbase (by linarith)
  have hk : 0 ≤ UnforcedLeray.B0284.heatKernel2 ν w :=
    UnforcedLeray.B0284.heatKernel2_nonneg hν w
  have hscale : 0 ≤ (r ^ 2)⁻¹ := by positivity
  unfold axialHeatMomentDensity
  rw [adjHM_heatKernel2_scale hν hr w]
  calc
    (r ^ 2)⁻¹ * UnforcedLeray.B0284.heatKernel2 ν w * axialWeight m (r • w) =
        ((r ^ 2)⁻¹ * UnforcedLeray.B0284.heatKernel2 ν w) * axialWeight m (r • w) := by ring
    _ ≤ ((r ^ 2)⁻¹ * UnforcedLeray.B0284.heatKernel2 ν w) * axialWeight m w :=
      mul_le_mul_of_nonneg_left hweight (mul_nonneg hscale hk)
    _ = (r ^ 2)⁻¹ * (UnforcedLeray.B0284.heatKernel2 ν w * axialWeight m w) := by ring

/-- The axially weighted density at time `ν r²` has integral at most that at time `ν`
(`r ∈ (0,1]`), by the planar change of variables `w ↦ r • w`. -/
theorem adjHM_integral_le {ν r m : ℝ} (hν : 0 < ν) (hr : 0 < r) (hr2 : r ^ 2 ≤ 1)
    (hm : 0 ≤ m) :
    ∫ w : ℝ × ℝ, axialHeatMomentDensity (ν * r ^ 2) m w ≤
      ∫ w : ℝ × ℝ, axialHeatMomentDensity ν m w := by
  have hr0 : r ≠ 0 := hr.ne'
  have hθ : 0 < ν * r ^ 2 := mul_pos hν (by positivity)
  have hθint : Integrable (axialHeatMomentDensity (ν * r ^ 2) m) :=
    integrable_axialHeatMomentDensity hθ hm
  have h1int : Integrable (axialHeatMomentDensity ν m) :=
    integrable_axialHeatMomentDensity hν hm
  have hcomp : Integrable (fun w : ℝ × ℝ => axialHeatMomentDensity (ν * r ^ 2) m (r • w)) := by
    exact (integrable_comp_smul_iff (volume : Measure (ℝ × ℝ))
      (fun w : ℝ × ℝ => axialHeatMomentDensity (ν * r ^ 2) m w) hr0).2 hθint
  have hmajor : Integrable (fun w : ℝ × ℝ => (r ^ 2)⁻¹ * axialHeatMomentDensity ν m w) := by
    simpa [mul_comm] using h1int.const_mul ((r ^ 2)⁻¹)
  have hmono : ∫ w : ℝ × ℝ, axialHeatMomentDensity (ν * r ^ 2) m (r • w) ≤
      ∫ w : ℝ × ℝ, (r ^ 2)⁻¹ * axialHeatMomentDensity ν m w :=
    integral_mono hcomp hmajor (fun w => adjHM_density_scale_le hν hr hr2 hm w)
  have hchange := MeasureTheory.Measure.integral_comp_smul (volume : Measure (ℝ × ℝ))
    (fun w : ℝ × ℝ => axialHeatMomentDensity (ν * r ^ 2) m w) r
  have hdim : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp [Module.finrank_prod]
  rw [hdim] at hchange
  have hchange' : ∫ w : ℝ × ℝ, axialHeatMomentDensity (ν * r ^ 2) m (r • w) =
      (r ^ 2)⁻¹ * ∫ w : ℝ × ℝ, axialHeatMomentDensity (ν * r ^ 2) m w := by
    simpa [abs_of_pos hr, smul_eq_mul, Real.rpow_neg hr.le, Real.rpow_natCast] using hchange
  have hsolve : ∫ w : ℝ × ℝ, axialHeatMomentDensity (ν * r ^ 2) m w =
      r ^ 2 * ∫ w : ℝ × ℝ, axialHeatMomentDensity (ν * r ^ 2) m (r • w) := by
    rw [hchange']
    field_simp
  calc
    ∫ w : ℝ × ℝ, axialHeatMomentDensity (ν * r ^ 2) m w =
        r ^ 2 * ∫ w : ℝ × ℝ, axialHeatMomentDensity (ν * r ^ 2) m (r • w) := hsolve
    _ ≤ r ^ 2 * ∫ w : ℝ × ℝ, (r ^ 2)⁻¹ * axialHeatMomentDensity ν m w :=
      mul_le_mul_of_nonneg_left hmono (sq_nonneg r)
    _ = ∫ w : ℝ × ℝ, axialHeatMomentDensity ν m w := by
      rw [MeasureTheory.integral_const_mul]
      field_simp

/-- The kernel moment is the `ofReal` of the weighted planar integral. -/
theorem adjHM_kerAxialMoment_eq {ν τ m : ℝ} (hθ : 0 < ν * τ) (hm : 0 ≤ m) :
    kerAxialMoment m (adjHeatKer ν τ) =
      ENNReal.ofReal (∫ w : ℝ × ℝ, axialHeatMomentDensity (ν * τ) m w) := by
  have hint : Integrable (axialHeatMomentDensity (ν * τ) m) :=
    integrable_axialHeatMomentDensity hθ hm
  have hnn : 0 ≤ᵐ[volume] axialHeatMomentDensity (ν * τ) m :=
    Filter.Eventually.of_forall fun w =>
      mul_nonneg (UnforcedLeray.B0284.heatKernel2_nonneg hθ w) (adjHM_axialWeight_nonneg m w)
  rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
  unfold kerAxialMoment
  refine lintegral_congr fun z => ?_
  have hk : 0 ≤ adjHeatKer ν τ z := adjHeatKer_nonneg hθ z
  rw [Real.enorm_eq_ofReal hk, ← ENNReal.ofReal_mul hk]
  congr 1
  have hw : axialWeight m z = (1 + z.2 ^ 2) ^ (m / 2) := axialBracket_rpow m z
  unfold axialHeatMomentDensity
  rw [hw]
  rfl

/-- **(H1.2) Axial Gaussian moment uniform in `τ ∈ (0,1]`** (SP 2819-2836). -/
theorem adjHeatMoment : AdjHeatMoment := by
  intro ν m hν hm
  refine ⟨∫ w : ℝ × ℝ, axialHeatMomentDensity ν m w, ?_, ?_⟩
  · exact integral_nonneg fun w =>
      mul_nonneg (UnforcedLeray.B0284.heatKernel2_nonneg hν w) (adjHM_axialWeight_nonneg m w)
  · intro τ hτ
    have hτ0 : 0 < τ := hτ.1
    have hτ1 : τ ≤ 1 := hτ.2
    have hr : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ0
    have hr2 : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ0.le
    have hle : Real.sqrt τ ^ 2 ≤ 1 := by rw [hr2]; exact hτ1
    have hint := adjHM_integral_le hν hr hle hm
    rw [hr2] at hint
    rw [adjHM_kerAxialMoment_eq (mul_pos hν hτ0) hm]
    exact ENNReal.ofReal_le_ofReal hint

end UnforcedLeray.Short.IIIa
