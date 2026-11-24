import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RABound
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Proofs.MultPin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HhatCoefLinear
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefLinear
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EACoefLinear
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HhatCoefBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EACoefBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.IBPAdjointC2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.IBPDivC1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.IBPGradC1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.IBPContC
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RAPhysAxi
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RALinear
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RPerBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RAGeoBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RAConvBound

/-!
# `raBoundExists` (source 5001-5016, proof 5022-5079)

Source of record: `the November 2 reference manuscript` (73 pages).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)
open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem raBoundExists (D : SeqData) (dm dp : ℝ) (hdm : 0 < dm) (hω : D.Pl.eigenvalue.im ≠ 0) (hγ : 0 < D.Pl.eigenvalue.re) (hσ0 : 0 < D.σ₀) (hσ1 : D.σ₀ < 1 / 4) (hχf : IsSourceCutoffC D.K.χf) (hC0 : 0 < D.K.C0) (has : 0 ≤ D.K.as) (hsplit : ∀ᶠ n : ℕ in atTop, ∃ M : Hsp (cOf (D.level n).ν) →L[ℝ] Zsp (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K), NearInst.IsSplitMult M ((D.level n).params D.Pl).R (D.level n).V (D.level n).rb) (hax : ∀ᶠ n : ℕ in atTop, ∀ τ, AxiNoSwirlPt ((D.level n).U τ)) (hW1 : ∀ᶠ n : ℕ in atTop, ∃ d : ℝ, D.W1InfAt n d) : RABoundExists D dm dp :=
  raBoundExists_of D dm dp hdm hω hγ hσ0 hσ1 hχf hC0 has hsplit hax hW1 NearInst.multPinOfLink (hhatCoefLinear _ _ hχf) (faCoefLinear _ _ hχf) (eaCoefLinear _ _ hχf) (hhatCoefBound _ _ hχf) (faCoefBound _ _ hχf) (eaCoefBound _ _ hχf) ibpAdjointC2 ibpDivC1 ibpGradC1 ibpContC (affineLiftReg _ _) (raPhysAxi _ _) (raLinear _ _) (rPerBound _ _) (raGeoBound _ _) (raConvBound _ _)

end UnforcedLeray.Short.PartIIIb.Concrete
