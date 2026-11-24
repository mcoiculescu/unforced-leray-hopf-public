import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.Hess.Defs
import UnforcedLeray.Short.PartIIa.Tasks.F03cWindowBackEquation.LapCalc

/-!
# Complex fields and the Cartesian Hessian (source 1426-1436)

Task `PartIII-b:C/ward/12/3/1/2/2/4`.  Calculus for the complex-valued Hessian: for a smooth
`ℂ`-valued `ψ` on the phase space, `∂_{y_j}∂_{y_k}ψ = ∂_j∂_k(Re ψ) + i ∂_j∂_k(Im ψ)`.
This is the Hessian analogue of `WinBack.lapT_complex`: the real-linear decomposition
`ψ = Re ψ · 1 + Im ψ · i` is differentiated twice, using `WinBack.dy_add_gen`,
`WinBack.dy_smul_gen`, `WinBack.contDiff_sD_gen`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Short.PartIIa.Rep
open UnforcedLeray.Parabolic (PS IsSTTest sD2)
open UnforcedLeray.Short.PartIIa (WindowCutoff windowField windowLap winSet)

theorem dy_dy_complex {ψ : ℝ × Space → ℂ} (hψ : ContDiff ℝ ∞ ψ) (j k : Fin 3) (p : ℝ × Space) :
    dy j (dy k ψ) p = ((sD2 j k (fun q => (ψ q).re) p : ℝ) : ℂ) +
      ((sD2 j k (fun q => (ψ q).im) p : ℝ) : ℂ) * Complex.I := by
  have hre : ContDiff ℝ ∞ (fun q => (ψ q).re) := Complex.reCLM.contDiff.comp hψ
  have him : ContDiff ℝ ∞ (fun q => (ψ q).im) := Complex.imCLM.contDiff.comp hψ
  have hdec : ψ = fun q => (ψ q).re • (1 : ℂ) + (ψ q).im • Complex.I := by
    funext q
    simp only [Complex.real_smul, mul_one]
    exact (Complex.re_add_im (ψ q)).symm
  have hdy1 : dy k ψ = fun q => UnforcedLeray.Parabolic.sD k (fun q => (ψ q).re) q • (1 : ℂ) +
      UnforcedLeray.Parabolic.sD k (fun q => (ψ q).im) q • Complex.I := by
    have hA : ContDiff ℝ ∞ (fun q => (ψ q).re • (1 : ℂ)) := hre.smul contDiff_const
    have hB : ContDiff ℝ ∞ (fun q => (ψ q).im • Complex.I) := him.smul contDiff_const
    conv_lhs => rw [hdec]
    rw [UnforcedLeray.Short.PartIIa.WinBack.dy_add_gen (hA.differentiable (by simp))
        (hB.differentiable (by simp)) k,
      UnforcedLeray.Short.PartIIa.WinBack.dy_smul_gen hre (1 : ℂ) k,
      UnforcedLeray.Short.PartIIa.WinBack.dy_smul_gen him Complex.I k]
  have hA2 : ContDiff ℝ ∞ (fun q => UnforcedLeray.Parabolic.sD k (fun q => (ψ q).re) q • (1 : ℂ)) :=
    (UnforcedLeray.Short.PartIIa.WinBack.contDiff_sD_gen hre k).smul contDiff_const
  have hB2 : ContDiff ℝ ∞
      (fun q => UnforcedLeray.Parabolic.sD k (fun q => (ψ q).im) q • Complex.I) :=
    (UnforcedLeray.Short.PartIIa.WinBack.contDiff_sD_gen him k).smul contDiff_const
  rw [hdy1, UnforcedLeray.Short.PartIIa.WinBack.dy_add_gen (hA2.differentiable (by simp))
    (hB2.differentiable (by simp)) j]
  rw [UnforcedLeray.Short.PartIIa.WinBack.dy_smul_gen
      (UnforcedLeray.Short.PartIIa.WinBack.contDiff_sD_gen hre k) (1 : ℂ) j,
    UnforcedLeray.Short.PartIIa.WinBack.dy_smul_gen
      (UnforcedLeray.Short.PartIIa.WinBack.contDiff_sD_gen him k) Complex.I j]
  simp only [Complex.real_smul, mul_one]

end UnforcedLeray.Short.PartIIIb.Concrete
