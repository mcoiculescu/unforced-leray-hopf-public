import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.LeavesOf
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelMoment

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/2/1`: (H2.1) the axial moment of the kernel gradient

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836.
Statement: `AdjHeatGradMoment` in `HeatExists/Leaves.lean`.

With `θ = ντ` and `D_θ(w) = (|∂_1 G_θ(w_1)| + |∂_2 G_θ(w_2)|) ⟨w_2⟩^m`
(`gradKernelAxialMomentDensity`, `MixedEvolution/KernelMoment.lean`):

* `kerAxialMoment_adjHeatGradKer_le`: each component of `adjHeatGradKer ν τ` has axial moment at
  most `∫ D_{ντ}`;
* `adjGrad_scale_le`, `adjGrad_integral_le`: the parabolic scaling of `D` for every `θ > 0`
  (the weight is compared with `(1 + θ)^{m/2}`, so no restriction `θ ≤ 1` is needed):
  `∫ D_θ ≤ θ^{-1/2} (1 + θ)^{m/2} ∫ D_1`;
* `adjHeatGradMoment`: with `θ = ντ ≤ ν`, `θ^{-1/2} = ν^{-1/2} τ^{-1/2}`, so `A = ν^{-1/2} (1+ν)^{m/2} ∫ D_1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
  (gradKernelAxialMomentDensity gradHeatKernel2_scale_sqr integrable_gradKernelNorm_mul_axialWeight)

namespace UnforcedLeray.Short.IIIa

/-- Parabolic scaling of the axial gradient moment density, for every `r > 0`: the weight
`1 + (r w₂)² ≤ (1 + r²)(1 + w₂²)`. -/
theorem adjGrad_scale_le {r m : ℝ} (hr : 0 < r) (hm : 0 ≤ m) (w : Plane) :
    gradKernelAxialMomentDensity (r ^ 2) m (r • w) ≤
      (r ^ 3)⁻¹ * ((1 + r ^ 2) ^ (m / 2) * gradKernelAxialMomentDensity 1 m w) := by
  have hc : 0 ≤ (r ^ 3)⁻¹ := by positivity
  have hgrad :
      (‖(UnforcedLeray.B0296.gradHeatKernel2 (r ^ 2) (r • w)).1‖ +
        ‖(UnforcedLeray.B0296.gradHeatKernel2 (r ^ 2) (r • w)).2‖) =
      (r ^ 3)⁻¹ *
        (‖(UnforcedLeray.B0296.gradHeatKernel2 1 w).1‖ +
          ‖(UnforcedLeray.B0296.gradHeatKernel2 1 w).2‖) := by
    rw [gradHeatKernel2_scale_sqr hr]
    simp [Real.norm_of_nonneg hc]
    ring
  have hbase : 1 + (r * w.2) ^ 2 ≤ (1 + r ^ 2) * (1 + w.2 ^ 2) := by
    nlinarith [sq_nonneg w.2, sq_nonneg r]
  have hweight : (1 + (r * w.2) ^ 2) ^ (m / 2) ≤
      (1 + r ^ 2) ^ (m / 2) * (1 + w.2 ^ 2) ^ (m / 2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) hbase (by linarith)
  unfold gradKernelAxialMomentDensity
  rw [hgrad]
  simp only [Prod.smul_snd, smul_eq_mul]
  set S := ‖(UnforcedLeray.B0296.gradHeatKernel2 1 w).1‖ +
    ‖(UnforcedLeray.B0296.gradHeatKernel2 1 w).2‖ with hSdef
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  calc (r ^ 3)⁻¹ * S * (1 + (r * w.2) ^ 2) ^ (m / 2)
      ≤ (r ^ 3)⁻¹ * S * ((1 + r ^ 2) ^ (m / 2) * (1 + w.2 ^ 2) ^ (m / 2)) :=
        mul_le_mul_of_nonneg_left hweight (mul_nonneg hc hS0)
    _ = (r ^ 3)⁻¹ * ((1 + r ^ 2) ^ (m / 2) * (S * (1 + w.2 ^ 2) ^ (m / 2))) := by ring

/-- The axial gradient moment density is integrable (for every `θ > 0`, `m ≥ 0`). -/
theorem adjGrad_integrable {θ m : ℝ} (hθ : 0 < θ) (hm : 0 ≤ m) :
    Integrable (fun w : Plane => gradKernelAxialMomentDensity θ m w) := by
  simpa [gradKernelAxialMomentDensity] using integrable_gradKernelNorm_mul_axialWeight hθ hm

/-- The integral of the axial gradient moment density, for every `θ > 0`:
`∫ D_θ ≤ θ^{-1/2} (1 + θ)^{m/2} ∫ D_1`. -/
theorem adjGrad_integral_le {θ m : ℝ} (hθ : 0 < θ) (hm : 0 ≤ m) :
    ∫ w : Plane, gradKernelAxialMomentDensity θ m w ≤
      θ ^ (-(1 / 2 : ℝ)) *
        ((1 + θ) ^ (m / 2) * ∫ w : Plane, gradKernelAxialMomentDensity 1 m w) := by
  let r := Real.sqrt θ
  have hr : 0 < r := Real.sqrt_pos.2 hθ
  have hr2 : r ^ 2 = θ := Real.sq_sqrt hθ.le
  have hθmem : Integrable (fun w : Plane => gradKernelAxialMomentDensity θ m w) :=
    adjGrad_integrable hθ hm
  have h1mem : Integrable (fun w : Plane => gradKernelAxialMomentDensity 1 m w) :=
    adjGrad_integrable one_pos hm
  have hcomp : Integrable (fun w : Plane => gradKernelAxialMomentDensity θ m (r • w)) :=
    (integrable_comp_smul_iff volume (fun w : Plane => gradKernelAxialMomentDensity θ m w)
      hr.ne').2 hθmem
  have hmajor : Integrable (fun w : Plane =>
      (r ^ 3)⁻¹ * ((1 + θ) ^ (m / 2) * gradKernelAxialMomentDensity 1 m w)) :=
    (h1mem.const_mul ((1 + θ) ^ (m / 2))).const_mul ((r ^ 3)⁻¹)
  have hmono : ∫ w : Plane, gradKernelAxialMomentDensity θ m (r • w) ≤
      ∫ w : Plane, (r ^ 3)⁻¹ * ((1 + θ) ^ (m / 2) * gradKernelAxialMomentDensity 1 m w) :=
    integral_mono hcomp hmajor (fun w => by
      have h := adjGrad_scale_le hr hm w
      rw [hr2] at h
      exact h)
  have hchange := MeasureTheory.Measure.integral_comp_smul (volume : Measure Plane)
    (fun w : Plane => gradKernelAxialMomentDensity θ m w) r
  have hdim : Module.finrank ℝ Plane = 2 := by simp [Plane, Module.finrank_prod]
  rw [hdim] at hchange
  have hchange' : ∫ w : Plane, gradKernelAxialMomentDensity θ m (r • w) =
      (r ^ 2)⁻¹ * ∫ w : Plane, gradKernelAxialMomentDensity θ m w := by
    simpa [abs_of_pos hr, smul_eq_mul, Real.rpow_neg hr.le, Real.rpow_natCast] using hchange
  have hsolve : ∫ w : Plane, gradKernelAxialMomentDensity θ m w =
      r ^ 2 * ∫ w : Plane, gradKernelAxialMomentDensity θ m (r • w) := by
    rw [hchange']
    field_simp
  have hscale : ∫ w : Plane, gradKernelAxialMomentDensity θ m w ≤
      r⁻¹ * ((1 + θ) ^ (m / 2) * ∫ w : Plane, gradKernelAxialMomentDensity 1 m w) := by
    calc ∫ w : Plane, gradKernelAxialMomentDensity θ m w
        = r ^ 2 * ∫ w : Plane, gradKernelAxialMomentDensity θ m (r • w) := hsolve
      _ ≤ r ^ 2 * ∫ w : Plane,
          (r ^ 3)⁻¹ * ((1 + θ) ^ (m / 2) * gradKernelAxialMomentDensity 1 m w) :=
        mul_le_mul_of_nonneg_left hmono (sq_nonneg r)
      _ = r⁻¹ * ((1 + θ) ^ (m / 2) * ∫ w : Plane, gradKernelAxialMomentDensity 1 m w) := by
        rw [integral_const_mul, integral_const_mul]
        field_simp
  have hrInv : r⁻¹ = θ ^ (-(1 / 2 : ℝ)) := by
    dsimp [r]
    rw [Real.rpow_neg hθ.le, ← Real.sqrt_eq_rpow]
  rw [← hrInv]
  exact hscale

/-- `‖·‖ₑ` of a real number is the `ofReal` of its norm. -/
theorem adjGrad_enorm_eq (x : ℝ) : ‖x‖ₑ = ENNReal.ofReal ‖x‖ := by
  rw [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs]

/-- The axial moment of each component of the heat-kernel gradient is bounded by the integral of
the axial gradient moment density at time `ντ`. -/
theorem adjGrad_kerAxialMoment_le {ν τ : ℝ} (hθ : 0 < ν * τ) {m : ℝ} (hm : 0 ≤ m) (j : Fin 2) :
    kerAxialMoment m (adjHeatGradKer ν τ j) ≤
      ENNReal.ofReal (∫ w : Plane, gradKernelAxialMomentDensity (ν * τ) m w) := by
  have hint := adjGrad_integrable hθ hm
  have hnn : 0 ≤ᵐ[volume] (fun w : Plane => gradKernelAxialMomentDensity (ν * τ) m w) :=
    ae_of_all _ (fun w => by
      show (0 : ℝ) ≤ gradKernelAxialMomentDensity (ν * τ) m w
      unfold gradKernelAxialMomentDensity
      positivity)
  rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
  unfold kerAxialMoment
  refine lintegral_mono (fun z => ?_)
  have hk : ‖adjHeatGradKer ν τ j z‖ ≤
      ‖(UnforcedLeray.B0296.gradHeatKernel2 (ν * τ) z).1‖ +
        ‖(UnforcedLeray.B0296.gradHeatKernel2 (ν * τ) z).2‖ := by
    unfold adjHeatGradKer
    split_ifs
    · linarith [norm_nonneg (UnforcedLeray.B0296.gradHeatKernel2 (ν * τ) z).2]
    · linarith [norm_nonneg (UnforcedLeray.B0296.gradHeatKernel2 (ν * τ) z).1]
  rw [adjGrad_enorm_eq, ← ENNReal.ofReal_mul (norm_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  unfold gradKernelAxialMomentDensity
  exact mul_le_mul_of_nonneg_right hk (by positivity)

/-- **(H2.1) The axial moment of the kernel gradient** (SP 2819-2836): for `ν > 0`, `m ≥ 0`
there is `A` with `∫ |∂_j G_{ντ}(z)| ⟨z₂⟩^m dz ≤ A τ^{-1/2}` for all `τ ∈ (0, 1]`, `j = 0, 1`. -/
theorem adjHeatGradMoment : AdjHeatGradMoment := by
  intro ν m hν hm
  have hI1 : 0 ≤ ∫ w : Plane, gradKernelAxialMomentDensity 1 m w :=
    integral_nonneg (fun w => by unfold gradKernelAxialMomentDensity; positivity)
  refine ⟨ν ^ (-(1 / 2 : ℝ)) *
      ((1 + ν) ^ (m / 2) * ∫ w : Plane, gradKernelAxialMomentDensity 1 m w),
    mul_nonneg (Real.rpow_nonneg hν.le _)
      (mul_nonneg (Real.rpow_nonneg (by linarith) _) hI1), ?_⟩
  intro τ hτ j
  have hτ0 : 0 < τ := hτ.1
  have hτ1 : τ ≤ 1 := hτ.2
  have hθ : 0 < ν * τ := mul_pos hν hτ0
  refine (adjGrad_kerAxialMoment_le hθ hm j).trans (ENNReal.ofReal_le_ofReal ?_)
  refine (adjGrad_integral_le hθ hm).trans ?_
  have hmul : (ν * τ) ^ (-(1 / 2 : ℝ)) = ν ^ (-(1 / 2 : ℝ)) * τ ^ (-(1 / 2 : ℝ)) :=
    Real.mul_rpow hν.le hτ0.le
  have hντ : ν * τ ≤ ν := by nlinarith
  have hpow : (1 + ν * τ) ^ (m / 2) ≤ (1 + ν) ^ (m / 2) :=
    Real.rpow_le_rpow (by linarith [mul_pos hν hτ0]) (by linarith) (by linarith)
  rw [hmul]
  calc ν ^ (-(1 / 2 : ℝ)) * τ ^ (-(1 / 2 : ℝ)) *
        ((1 + ν * τ) ^ (m / 2) * ∫ w : Plane, gradKernelAxialMomentDensity 1 m w)
      ≤ ν ^ (-(1 / 2 : ℝ)) * τ ^ (-(1 / 2 : ℝ)) *
        ((1 + ν) ^ (m / 2) * ∫ w : Plane, gradKernelAxialMomentDensity 1 m w) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hI1)
          (mul_nonneg (Real.rpow_nonneg hν.le _) (Real.rpow_nonneg hτ0.le _))
    _ = ν ^ (-(1 / 2 : ℝ)) *
        ((1 + ν) ^ (m / 2) * ∫ w : Plane, gradKernelAxialMomentDensity 1 m w) *
        τ ^ (-(1 / 2 : ℝ)) := by ring

end UnforcedLeray.Short.IIIa

end
