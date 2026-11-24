import UnforcedLeray.Short.Spine.RefProofs
import UnforcedLeray.Cons.C01ReferenceChoice

/-!
# Part I, Gaussian half, from the draft Step C1

Source: `the November 2 reference manuscript`, `prop:short-gaussian-seed`
(lines 592-634), `prop:short-canonical` (lines 1075-1150), `cor:short-mellin` (lines 1155-1180).

The draft `Cons/C01ReferenceChoice.lean` proves G1 (growing eigenpair, `-2 < ω < 0`), G3a
(adjoint, oscillator domain, `ℓ(H) ≠ 0`, `M_q ≠ 0`) and the Mellin facts (G4) for the whole-line
Rayleigh mode, under the single named hypothesis `CanonicalBranchHyp` (G3b = `prop:short-canonical`).
This file packages those conclusions as `GaussianInstability`, so the planar half of `PartIOutput`
is reduced to `Cons.C01.CanonicalBranchHyp`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Blueprint.Planar
open UnforcedLeray.ComplexODEC

/-- The planar half of Part I from the canonical branch (G3b). -/
theorem gaussianInstability_of_canonicalBranch (hcan : Cons.C01.CanonicalBranchHyp) :
    ∃ P : PlanarData, GaussianInstability P := by
  obtain ⟨c, -, hre0, hre1, F, hF⟩ := Cons.C01.exists_wholeLineData
  obtain ⟨V, hV, hVc⟩ := hcan c F hF
  obtain ⟨σ₀, hRef⟩ := Cons.C01.exists_referenceChoice_of_mode hF hre0 hre1 hV hVc
  have hPR : IsPlanarReference (Cons.C01.modeData c F V) := hRef.1
  have hcurve : Cons.C01.CurveFacts (Cons.C01.modeData c F V).canonical
      (Cons.C01.modeData c F V).eigenvalue (Cons.C01.modeData c F V).kappa
      (Cons.C01.modeData c F V).mode :=
    ⟨hPR.eigenpair.re_pos, hPR.eigenpair.memXG, hPR.canonical.memXG, hVc,
      hPR.canonical.bounded_near_zero, hPR.canonical.asymptotic⟩
  have hq : quadrupole (Cons.C01.modeData c F V).mode ≠ 0 := modeQuadrupole_ne_zero hF
  have hJ := Cons.C01.directAdjointPairing_ne_zero hF
  refine ⟨Cons.C01.modeData c F V, hPR, hRef.2.1, hq,
    Cons.C01.strainCoupling_adjointMode_ne_zero hF hJ, ?_, ?_, ?_⟩
  · intro μ hμ
    have hs : 0 < (μ + 3 / 2).re := by
      simp only [Complex.add_re]
      norm_num
      linarith
    have hc := Cons.C01.mellinConvergent_quadCurve hcurve hs
    refine IntegrableOn.congr_fun hc (fun θ hθ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul, Cons.C01.quadCurve]
    congr 2
    ring
  · intro μ hμ
    have hμ' : -(3 / 2) < μ.re := hμ
    have hs : 0 < (μ + 3 / 2).re := by
      simp only [Complex.add_re]
      norm_num
      linarith
    have hd := Cons.C01.differentiableAt_mellin_quadCurve hcurve hs
    have hfun : mellinJC (Cons.C01.modeData c F V) =
        fun x => mellin (Cons.C01.quadCurve (Cons.C01.modeData c F V).canonical) (x + 3 / 2) :=
      funext fun x => Cons.C01.mellinJC_eq_mellin (Cons.C01.modeData c F V).canonical x
    rw [hfun]
    exact (hd.comp μ (differentiableAt_id.add_const _)).differentiableWithinAt
  · exact Cons.C01.exists_mellinJC_ne_zero hcurve hq

end UnforcedLeray.Short.Spine
