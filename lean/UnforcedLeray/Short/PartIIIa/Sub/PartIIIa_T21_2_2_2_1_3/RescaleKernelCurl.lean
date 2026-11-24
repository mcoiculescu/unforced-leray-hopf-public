import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2_1_F1.ChangeVar

/-!
# Part III-a, `PartIII-a:T21/2/2/2/1/3/5`: the curl clause `RescaleKernelCurl`

Source `the November 2 reference manuscript` (SP), lines 2875-2896 (kernel
velocity) and 3052-3057 (adjoint localized interaction). Same change of variables `x = √a y`
as `RescaleKernelDiv`: `φ̃(y) = φ(√a y)` is a test of the cell `c/√a` when `φ` is a test of the
cell `c`; `∂_kφ̃(y) = √a (∂_kφ)(√a y)`; both sides of the curl identity are integrals of
`G(√a y)` and `integral_cell_scale` gives the common factor `a⁻¹`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-- Dilation `y ↦ φ(s y)` of a cylinder test of the cell `c` is a cylinder test of the cell `c/s`. -/
theorem rescaleKernelCurl_test {c s : ℝ} (hs : 0 < s) (φ : ℝ × ℝ → ℝ)
    (hφ : B0579.IsCylTest c φ) :
    B0579.IsCylTest (c / s) (fun y : ℝ × ℝ => φ (s * y.1, s * y.2)) where
  smooth := hφ.smooth.comp
    ((contDiff_const.mul contDiff_fst).prodMk (contDiff_const.mul contDiff_snd))
  periodic x := by
    show φ (s * (x.1 + c / s), s * x.2) = φ (s * x.1, s * x.2)
    rw [show s * (x.1 + c / s) = s * x.1 + c by field_simp]
    exact hφ.periodic (s * x.1, s * x.2)
  band := by
    obtain ⟨R, hR⟩ := hφ.band
    refine ⟨R / s, fun x hx => hR (s * x.1, s * x.2) ?_⟩
    show R < |s * x.2|
    rw [abs_mul, abs_of_pos hs, mul_comm]
    exact (div_lt_iff₀ hs).1 hx

/-- Chain rule for the dilation: `∂_j [φ(s ·)](y) = s (∂_jφ)(s y)`. -/
theorem rescaleKernelCurl_pd {φ : ℝ × ℝ → ℝ} (hφ : Differentiable ℝ φ) (s : ℝ) (j : Fin 2)
    (y : ℝ × ℝ) :
    B0579.pd j (fun y : ℝ × ℝ => φ (s * y.1, s * y.2)) y =
      s * B0579.pd j φ (s * y.1, s * y.2) := by
  have hg : HasFDerivAt (fun z : ℝ × ℝ => s • z) (s • ContinuousLinearMap.id ℝ (ℝ × ℝ)) y :=
    (hasFDerivAt_id y).const_smul s
  have hc := (hφ (s • y)).hasFDerivAt.comp y hg
  have hpt : ∀ z : ℝ × ℝ, s • z = (s * z.1, s * z.2) := fun z => by ext <;> simp
  have hfun : (fun y : ℝ × ℝ => φ (s * y.1, s * y.2)) = φ ∘ (fun z : ℝ × ℝ => s • z) := by
    funext z
    simp only [Function.comp_apply, hpt]
  unfold B0579.pd
  rw [hfun, hc.fderiv, hpt y]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

/-- **`RescaleKernelCurl`** (SP 2875-2896, 3052-3057): the curl clause of the kernel velocity
transported from the cell `c/√a` to the cell `c`. -/
theorem rescaleKernelCurl : UnforcedLeray.Short.IIIa.E0.RescaleKernelCurl := by
  intro c a hc ha ψ u hyp φ hφ
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsne : Real.sqrt a ≠ 0 := hs.ne'
  have hainv : (a⁻¹ : ℝ) ≠ 0 := inv_ne_zero ha.ne'
  -- left side: `∫_{C_{c/√a}} ψ(y) φ(√a y) dy = a⁻¹ ∫_{C_c} ψ(x/√a) φ(x) dx`
  have hA := integral_cell_scale c a ha
    (fun x => ψ (x.1 / Real.sqrt a, x.2 / Real.sqrt a) * φ x)
  simp only [mul_div_cancel_left₀ _ hsne, Prod.mk.eta] at hA
  -- right side of the transported curl integrand
  have hB := integral_cell_scale c a ha
    (fun x => Real.sqrt a *
      (u (x.1 / Real.sqrt a, x.2 / Real.sqrt a) 0 * B0579.pd 1 φ x -
        u (x.1 / Real.sqrt a, x.2 / Real.sqrt a) 1 * B0579.pd 0 φ x))
  simp only [mul_div_cancel_left₀ _ hsne, Prod.mk.eta] at hB
  -- the hypothesis applied to the dilated test `φ(√a ·)` of the cell `c/√a`
  have H := hyp (fun y : ℝ × ℝ => φ (Real.sqrt a * y.1, Real.sqrt a * y.2))
    (rescaleKernelCurl_test hs φ hφ)
  simp only [rescaleKernelCurl_pd hφ.differentiable (Real.sqrt a)] at H
  have key : ∫ x in B0579.cell (cellLen c a), ψ x * φ (Real.sqrt a * x.1, Real.sqrt a * x.2) =
      ∫ x in B0579.cell (cellLen c a), Real.sqrt a *
        (u x 0 * B0579.pd 1 φ (Real.sqrt a * x.1, Real.sqrt a * x.2) -
          u x 1 * B0579.pd 0 φ (Real.sqrt a * x.1, Real.sqrt a * x.2)) := by
    rw [H]
    congr 1
    funext x
    ring
  refine mul_left_cancel₀ hainv ((hA.symm.trans key).trans hB) |>.trans ?_
  congr 1
  funext x
  ring

end UnforcedLeray.Short.IIIa.E0
