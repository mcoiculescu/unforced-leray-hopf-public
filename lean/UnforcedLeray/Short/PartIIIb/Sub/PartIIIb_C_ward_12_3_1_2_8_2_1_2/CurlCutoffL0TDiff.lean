import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.Statements

/-!
# `curlCutoffL0TDiff`: `L₀ᵗ` of the cut-off curl minus `L₀ᵗ` of the curl is `L₀ᵗ` of the cut-off error

Proves `CurlCutoffL0TDiff` (`Statements.lean`), source lines 1446-1455.
Pointwise, `projectedPotentialCurlCutoff R B = realC(curl B) + cutoffErr R B`, because
`χ_R B = B + (χ_R - 1) B` and `spatialCurlST` is additive on differentiable fields. Then `L₀ᵗ` is
additive on smooth fields.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.SolApprox

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.RieszLp
open UnforcedLeray.Cons.C03.Concrete
open NavierStokesR3.ComparisonCutoffs

theorem clDiff_realC_eq_cplxV : (realC : Space → CVec3) = ⇑UnforcedLeray.Axi.cplxV := by
  funext x
  ext i
  simp [realC_apply, UnforcedLeray.Axi.cplxV_apply]

theorem clDiff_realC_add (x y : Space) : realC (x + y) = realC x + realC y := by
  ext i
  simp [realC_apply]

theorem clDiff_contDiff_realC_comp {F : ℝ × Space → Space} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun w => realC (F w)) := by
  rw [clDiff_realC_eq_cplxV]
  exact UnforcedLeray.Axi.cplxV.contDiff.comp hF

/-- `spatialCurlST` is additive on differentiable fields. -/
theorem clDiff_spatialCurlST_add {F G : ℝ × Space → Space} (hF : Differentiable ℝ F)
    (hG : Differentiable ℝ G) (z : ℝ × Space) :
    spatialCurlST (fun x => F x + G x) z = spatialCurlST F z + spatialCurlST G z := by
  unfold spatialCurlST
  rw [← Finset.sum_add_distrib]
  have hd : fderiv ℝ (fun x => F x + G x) z = fderiv ℝ F z + fderiv ℝ G z :=
    fderiv_add (hF z) (hG z)
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hd, add_apply, UnforcedLeray.L09.crossProd_add_right]

/-- `L₀ᵗ` is additive on smooth `ℂ³`-valued fields. -/
theorem clDiff_L0T_add (ν : ℝ) {A C : ℝ × Space → CVec3} (hA : ContDiff ℝ ∞ A)
    (hC : ContDiff ℝ ∞ C) : L0T ν (A + C) = L0T ν A + L0T ν C := by
  have dA : Differentiable ℝ A := hA.differentiable (by simp)
  have dC : Differentiable ℝ C := hC.differentiable (by simp)
  have dyA : ∀ j, Differentiable ℝ (dy j A) := fun j =>
    (contDiff_dy hA j).differentiable (by simp)
  have dyC : ∀ j, Differentiable ℝ (dy j C) := fun j =>
    (contDiff_dy hC j).differentiable (by simp)
  have hdy1 : ∀ j, dy j (A + C) = dy j A + dy j C := fun j => dy_add dA dC j
  have hdy2 : ∀ j, dy j (dy j (A + C)) = dy j (dy j A) + dy j (dy j C) := fun j => by
    rw [hdy1 j, dy_add (dyA j) (dyC j) j]
  have hτ : dτ (A + C) = dτ A + dτ C := by
    funext p
    simp [dτ, fderiv_add (dA p) (dC p)]
  have hrad : radialT (A + C) = radialT A + radialT C := by
    funext p
    simp only [radialT, hdy1, Pi.add_apply, smul_add, Finset.sum_add_distrib]
  have hlap : lapT (A + C) = lapT A + lapT C := by
    funext p
    simp only [lapT, hdy2, Pi.add_apply, Finset.sum_add_distrib]
  funext p
  simp only [L0T, driftT, nuLapT, hτ, hrad, hlap, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  module

theorem curlCutoffL0TDiff : UnforcedLeray.Short.PartIIIb.Concrete.SolApprox.CurlCutoffL0TDiff := by
  intro B hB R ν hR z
  have hBd : Differentiable ℝ B := hB.differentiable (by simp)
  have hG : ContDiff ℝ ∞ (fun w : ℝ × Space => (cutoff R w.2 - 1) • B w) :=
    (((cutoff_smooth R).comp contDiff_snd).sub contDiff_const).smul hB
  have hGd : Differentiable ℝ (fun w : ℝ × Space => (cutoff R w.2 - 1) • B w) :=
    hG.differentiable (by simp)
  have hpt : projectedPotentialCurlCutoff R B =
      (fun w => realC (spatialCurlST B w)) + cutoffErr R B := by
    funext w
    have hfun : (fun x : ℝ × Space => cutoff R x.2 • B x) =
        fun x => B x + (cutoff R x.2 - 1) • B x := by
      funext x
      rw [sub_smul, one_smul]
      abel
    unfold projectedPotentialCurlCutoff cutoffErr
    rw [Pi.add_apply, hfun, clDiff_spatialCurlST_add hBd hGd, clDiff_realC_add]
  have hA : ContDiff ℝ ∞ (fun w => realC (spatialCurlST B w)) :=
    clDiff_contDiff_realC_comp (contDiff_spatialCurlST_of_contDiff hB)
  have hC : ContDiff ℝ ∞ (cutoffErr R B) := by
    unfold cutoffErr
    exact clDiff_contDiff_realC_comp (contDiff_spatialCurlST_of_contDiff hG)
  rw [hpt, clDiff_L0T_add ν hA hC]
  simp only [Pi.add_apply]
  abel

end UnforcedLeray.Short.PartIIIb.Concrete.SolApprox
