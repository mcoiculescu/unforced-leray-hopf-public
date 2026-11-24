import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.HeatEq.ThetaDeriv

/-!
# Part II-b, helper for leaf `PartII-b:T11/3/4` (`HeatConvEq`): the time derivative of the flow

Source of record: `the November 2 reference manuscript`, line 1924.

For `τ = x.1 > 0`, `∂_τ H(x) = ν ∫ (∂_θ G)_{ντ}(w) ζ(x.2 - w) dw`, by the chain rule for
`τ ↦ ντ` applied to `hce_theta_hasDerivAt`. The planar flow is differentiable at `x`
(`heatConvSmooth`), so `cpd 0 H x` is the derivative of `t ↦ H(x + t (1, 0))` at `0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- The time derivative of the planar heat flow at `τ > 0`: `∂_τ H = ν ∫ (∂_θ G)_{ντ} ζ`. -/
theorem hce_cpd0 {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {ζ : ℝ × ℝ → ℝ}
    (hζ : NiceStream c ζ) {x : Coord} (hx : 0 < x.1) :
    cpd 0 (heatStreamH ν ζ) x =
      ν * ∫ w : ℝ × ℝ, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative (ν * x.1) w *
        ζ (x.2 - w) := by
  have hSm := heatConvSmooth c ν ζ hc hν hζ
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hmem : x ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hx, mem_univ _⟩
  have hdiff : DifferentiableAt ℝ (heatStreamH ν ζ) x :=
    (hSm.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by simp)
  have hl : HasDerivAt (fun t : ℝ => x + t • ((1 : ℝ), ((0 : ℝ), (0 : ℝ))))
      ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))).const_add x
  have hH : HasDerivAt (fun t : ℝ => heatStreamH ν ζ (x + t • ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))))
      (fderiv ℝ (heatStreamH ν ζ) x ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hdiff.hasFDerivAt hl (by simp)
  -- for `t > -x.1`, the flow at `x + t (1,0)` is the Gaussian convolution at age `ν (x.1 + t)`
  have hval : ∀ t : ℝ, -x.1 < t →
      heatStreamH ν ζ (x + t • ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))) =
        ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (ν * (x.1 + t)) w * ζ (x.2 - w) := by
    intro t ht
    have h1 : (x + t • ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))).1 = x.1 + t := by simp
    have h2 : (x + t • ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))).2 = x.2 := by simp
    have hpos : 0 < (x + t • ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))).1 := by rw [h1]; linarith
    unfold heatStreamH
    rw [if_pos hpos]
    simp only [h1, h2]
  have hG := hce_theta_hasDerivAt hc hζ (θ₀ := ν * x.1) (mul_pos hν hx) x.2
  have hlin : HasDerivAt (fun t : ℝ => ν * (x.1 + t)) ν 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_add x.1).const_mul ν
  have hcomp := HasDerivAt.comp_of_eq (0 : ℝ) hG hlin (by simp)
  have hfun : (fun t : ℝ => heatStreamH ν ζ (x + t • ((1 : ℝ), ((0 : ℝ), (0 : ℝ))))) =ᶠ[𝓝 (0 : ℝ)]
      ((fun θ : ℝ => ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w * ζ (x.2 - w)) ∘
        (fun t : ℝ => ν * (x.1 + t))) := by
    filter_upwards [Ioi_mem_nhds (show -x.1 < (0 : ℝ) by linarith)] with t ht
    exact hval t ht
  have h2 := hcomp.congr_of_eventuallyEq hfun
  have hu := hH.unique h2
  show fderiv ℝ (heatStreamH ν ζ) x ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) = _
  rw [hu, mul_comm]

end UnforcedLeray.Short.IIb
