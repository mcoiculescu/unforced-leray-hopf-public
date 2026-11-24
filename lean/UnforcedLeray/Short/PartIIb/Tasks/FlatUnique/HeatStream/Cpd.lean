import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.Smooth
import UnforcedLeray.Units.B0284.Contraction

/-!
# Part II-b, leaf `PartII-b:T11/3/3` (`HeatConvCpd`): spatial derivatives pass under the heat flow

Source of record: `the November 2 reference manuscript`, lines 1923-1927 (the heat
semigroup commutes with the derivatives in `q` and `η`). The statement is `HeatConvCpd` of
`Sub/T11_3.lean`.

Proof. For `τ = x.1 > 0` and `k = heatKernel2 (ν τ)` the planar heat flow is
`z ↦ ∫ k(w) ζ(z - w) dw` (`heatStreamH`). Its derivative along a fixed direction `e` is
`∫ k(w) ∂_e ζ(z - w) dw`, by differentiation under the integral with the integrable dominating
function `(sup ‖∇ζ‖ ‖e‖) k` (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`). The heat flow is
differentiable at `x` (`heatConvSmooth`, `Tasks/FlatUnique/HeatStream/Smooth.lean`), so
`fderiv H x (0, e)` is the derivative along the line `t ↦ x + t (0, e)`, which only varies `z` and
keeps `τ` fixed.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Differentiation under the Gaussian integral along a fixed direction `e`: for `θ > 0`,
`t ↦ ∫ G_θ(w) ζ(p + t e - w) dw` has derivative `∫ G_θ(w) ∂_e ζ(p - w) dw` at `t = 0`. -/
theorem hcp_hasDerivAt_conv {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) {ζ : ℝ × ℝ → ℝ}
    (hζ : NiceStream c ζ) (p e : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * ζ (p + t • e - w))
      (∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * fderiv ℝ ζ (p - w) e) 0 := by
  obtain ⟨B, -, hB⟩ := hcs_nice_iteratedFDeriv_bound hc hζ 0
  obtain ⟨M, hM0, hM⟩ := hcs_nice_iteratedFDeriv_bound hc hζ 1
  have hζB : ∀ y : ℝ × ℝ, ‖ζ y‖ ≤ B := fun y => by simpa using hB y
  have hdζ : ∀ y : ℝ × ℝ, ‖fderiv ℝ ζ y‖ ≤ M := fun y => by simpa using hM y
  have hζs : ContDiff ℝ ∞ ζ := hζ.smooth
  have hζc : Continuous ζ := hζs.continuous
  have hdc : Continuous (fderiv ℝ ζ) := hζs.continuous_fderiv (by simp)
  have hk : Integrable (UnforcedLeray.B0284.heatKernel2 θ) :=
    UnforcedLeray.B0284.integrable_heatKernel2 hθ
  have hk0 : ∀ w : ℝ × ℝ, 0 ≤ UnforcedLeray.B0284.heatKernel2 θ w :=
    fun w => UnforcedLeray.B0284.heatKernel2_nonneg hθ w
  have harg : ∀ t : ℝ, Continuous fun w : ℝ × ℝ => p + t • e - w := fun t => by fun_prop
  have hmeasζ : ∀ t : ℝ,
      AEStronglyMeasurable (fun w : ℝ × ℝ => ζ (p + t • e - w)) (volume : Measure (ℝ × ℝ)) :=
    fun t => (hζc.comp (harg t)).aestronglyMeasurable
  have hmeasd : ∀ t : ℝ,
      AEStronglyMeasurable (fun w : ℝ × ℝ => fderiv ℝ ζ (p + t • e - w) e)
        (volume : Measure (ℝ × ℝ)) :=
    fun t => ((hdc.comp (harg t)).clm_apply continuous_const).aestronglyMeasurable
  have hF_meas : ∀ᶠ t in 𝓝 (0 : ℝ),
      AEStronglyMeasurable (fun w : ℝ × ℝ => UnforcedLeray.B0284.heatKernel2 θ w *
        ζ (p + t • e - w)) (volume : Measure (ℝ × ℝ)) :=
    Eventually.of_forall fun t => hk.aestronglyMeasurable.mul (hmeasζ t)
  have hF_int : Integrable (fun w : ℝ × ℝ =>
      UnforcedLeray.B0284.heatKernel2 θ w * ζ (p + (0 : ℝ) • e - w)) :=
    hk.mul_bdd (hmeasζ 0) (ae_of_all _ fun w => hζB (p + (0 : ℝ) • e - w))
  have hF'_meas : AEStronglyMeasurable (fun w : ℝ × ℝ =>
      UnforcedLeray.B0284.heatKernel2 θ w * fderiv ℝ ζ (p + (0 : ℝ) • e - w) e)
      (volume : Measure (ℝ × ℝ)) :=
    hk.aestronglyMeasurable.mul (hmeasd 0)
  have hbd : ∀ᵐ w ∂(volume : Measure (ℝ × ℝ)), ∀ t ∈ (univ : Set ℝ),
      ‖UnforcedLeray.B0284.heatKernel2 θ w * fderiv ℝ ζ (p + t • e - w) e‖ ≤
        UnforcedLeray.B0284.heatKernel2 θ w * (M * ‖e‖) :=
    ae_of_all _ fun w t _ => by
      rw [norm_mul, Real.norm_of_nonneg (hk0 w)]
      exact mul_le_mul_of_nonneg_left
        (((fderiv ℝ ζ (p + t • e - w)).le_opNorm e).trans
          (mul_le_mul_of_nonneg_right (hdζ _) (norm_nonneg e))) (hk0 w)
  have hbi : Integrable (fun w : ℝ × ℝ =>
      UnforcedLeray.B0284.heatKernel2 θ w * (M * ‖e‖)) :=
    hk.mul_const _
  have hdiff : ∀ᵐ w ∂(volume : Measure (ℝ × ℝ)), ∀ t ∈ (univ : Set ℝ),
      HasDerivAt (fun s : ℝ => UnforcedLeray.B0284.heatKernel2 θ w * ζ (p + s • e - w))
        (UnforcedLeray.B0284.heatKernel2 θ w * fderiv ℝ ζ (p + t • e - w) e) t := by
    refine ae_of_all _ fun w t _ => ?_
    have hl : HasDerivAt (fun s : ℝ => p + s • e - w) e t := by
      simpa using (((hasDerivAt_id' t).smul_const e).const_add p).sub_const w
    exact ((hζs.differentiable (by simp) (p + t • e - w)).hasFDerivAt.comp_hasDerivAt t hl).const_mul _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (ℝ × ℝ))) (x₀ := (0 : ℝ)) (s := univ)
    (F := fun t w => UnforcedLeray.B0284.heatKernel2 θ w * ζ (p + t • e - w))
    (F' := fun t w => UnforcedLeray.B0284.heatKernel2 θ w * fderiv ℝ ζ (p + t • e - w) e)
    (bound := fun w => UnforcedLeray.B0284.heatKernel2 θ w * (M * ‖e‖))
    univ_mem hF_meas hF_int hF'_meas hbd hbi hdiff
  simp only [zero_smul, add_zero] at key
  exact key.2

/-- For `τ = x.1 > 0`, the derivative of the planar heat flow at `x` in the direction `(0, e)`
is the heat flow of the directional derivative `∂_e ζ`. -/
theorem hcp_fderiv_eq {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {ζ : ℝ × ℝ → ℝ}
    (hζ : NiceStream c ζ) {x : Coord} (hx : 0 < x.1) (e : ℝ × ℝ) :
    fderiv ℝ (heatStreamH ν ζ) x ((0 : ℝ), e) =
      ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (ν * x.1) w * fderiv ℝ ζ (x.2 - w) e := by
  have hSm := heatConvSmooth c ν ζ hc hν hζ
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hmem : x ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hx, mem_univ _⟩
  have hdiff : DifferentiableAt ℝ (heatStreamH ν ζ) x :=
    (hSm.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by simp)
  have hl : HasDerivAt (fun t : ℝ => x + t • ((0 : ℝ), e)) ((0 : ℝ), e) 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const ((0 : ℝ), e)).const_add x
  have hH : HasDerivAt (fun t : ℝ => heatStreamH ν ζ (x + t • ((0 : ℝ), e)))
      (fderiv ℝ (heatStreamH ν ζ) x ((0 : ℝ), e)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hdiff.hasFDerivAt hl (by simp)
  have hpt : (fun t : ℝ => heatStreamH ν ζ (x + t • ((0 : ℝ), e))) =
      fun t : ℝ => ∫ w : ℝ × ℝ,
        UnforcedLeray.B0284.heatKernel2 (ν * x.1) w * ζ (x.2 + t • e - w) := by
    funext t
    have h1 : x + t • ((0 : ℝ), e) = (x.1, x.2 + t • e) := Prod.ext (by simp) (by simp)
    rw [h1]
    simp [heatStreamH, hx]
  have hc' := hcp_hasDerivAt_conv hc (mul_pos hν hx) hζ x.2 e
  have hH2 : HasDerivAt (fun t : ℝ => heatStreamH ν ζ (x + t • ((0 : ℝ), e)))
      (∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (ν * x.1) w * fderiv ℝ ζ (x.2 - w) e) 0 := by
    rw [hpt]
    exact hc'
  exact hH.unique hH2

/-- **Leaf `PartII-b:T11/3/3`** (`HeatConvCpd`, `Sub/T11_3.lean`): for a nice stream `ζ` and
`τ > 0`, the `q`- and `η`-partial derivatives of the heat flow are the heat flows of `∂_q ζ` and
`∂_η ζ`. -/
theorem heatConvCpd : UnforcedLeray.Short.IIb.HeatConvCpd := by
  intro c ν ζ hc hν hζ x hx
  refine ⟨?_, ?_⟩
  · show fderiv ℝ (heatStreamH ν ζ) x ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) =
      heatStreamH ν (qDer ζ) x
    rw [hcp_fderiv_eq hc hν hζ hx ((1 : ℝ), (0 : ℝ))]
    simp [heatStreamH, hx, qDer]
  · show fderiv ℝ (heatStreamH ν ζ) x ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) =
      heatStreamH ν (etaDer ζ) x
    rw [hcp_fderiv_eq hc hν hζ hx ((0 : ℝ), (1 : ℝ))]
    simp [heatStreamH, hx, etaDer]

end UnforcedLeray.Short.IIb
