import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.Statements
import UnforcedLeray.Short.PartIIb.Tasks.OrdRelUnique.ProjTestIsNewtonCurl
import UnforcedLeray.Short.PartIIb.Tasks.OrdRelUnique.Complexify

/-!
# `newtonCurlRepSliceAE`: the Newton-curl representative is a.e. the Leray projection

Proves `NewtonCurlRepSliceAE` (`Statements.lean`), source lines 119-120, 1356-1366.
Split `Φ = realC(reV Φ) + I • realC(imV Φ)`; apply `projTest_add_smul_ae` to the sum and
`projTestIsNewtonCurl` to each real part.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.SolApprox

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.RieszLp
open UnforcedLeray.Cons.C03.Concrete
open NavierStokesR3.ComparisonCutoffs

theorem newtonCurlRepSliceAE : UnforcedLeray.Short.PartIIIb.Concrete.SolApprox.NewtonCurlRepSliceAE := by
  intro P hP Φ hΦ τ
  have hφ1 : IsPhaseTest P (fun z => reV (Φ z)) := hΦ.clm_comp reV
  have hφ2 : IsPhaseTest P (fun z => imV (Φ z)) := hΦ.clm_comp imV
  have hA : IsPhaseTest P (fun z => realC (reV (Φ z))) :=
    UnforcedLeray.Short.IIb.isPhaseTest_realC_comp hφ1
  have hB : IsPhaseTest P (fun z => realC (imV (Φ z))) :=
    UnforcedLeray.Short.IIb.isPhaseTest_realC_comp hφ2
  have hΦeq : Φ = (fun z => realC (reV (Φ z))) + Complex.I • (fun z => realC (imV (Φ z))) := by
    funext z
    simp only [Pi.add_apply, Pi.smul_apply]
    exact UnforcedLeray.Short.IIb.realC_reV_add_I_smul_imV (Φ z)
  have hsum := UnforcedLeray.Short.IIb.projTest_add_smul_ae (P := P) Complex.I hA hB τ
  rw [← hΦeq] at hsum
  have hA' := UnforcedLeray.Short.IIb.projTestIsNewtonCurl P (fun z => reV (Φ z)) hφ1 τ
  have hB' := UnforcedLeray.Short.IIb.projTestIsNewtonCurl P (fun z => imV (Φ z)) hφ2 τ
  have hmain := hA'.symm.add (hB'.symm.const_smul Complex.I)
  exact hmain.trans hsum.symm

end UnforcedLeray.Short.PartIIIb.Concrete.SolApprox
