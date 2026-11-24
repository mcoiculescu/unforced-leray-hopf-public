import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.LjOld
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.FreeWeakUniqueness
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.WeakDmuAdd
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.WardEnergyEquation
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.HhatSolenoidal
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.WardFieldsZero
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.WardYoungPointwise
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.HhatYoungPointwise
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.ChiOMultYoung

/-!
# Target PartIII-b:IIIb-D2: the Ward, physical-affine and H-nilpotent identities of the exact return

Source of record: `the November 2 reference manuscript` (73 pages):
4290-4322 (ward:stress-normal, support, H^2 = 0), 5001-5008 (ret:physical-affine), 5796-5811
(use in the exact return). The leaves PartIII-b:IIIb-D2/1..8 and PartIII-b:C/LjOld are the
library theorems named below; the proof is the term of the task spec.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace ReturnBase

/-- The Ward, physical-affine and H-nilpotent identities of the exact return (source 4290-4322,
5001-5008, 5796-5811). -/
theorem toOps_wardAffineNilpotent {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) {ε μ as : ℝ}
    {χo χy χf : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (hχy : IsYoungCutoff χy)
    (hχf : IsSourceCutoffC χf) {V rb : ℝ → SpatialField} {p : ℝ → Space → ℝ}
    {ι : Aff →ₗ[ℝ] (ℝ → Mat3)} {S : ConcreteYF.FlatSetting} {lam κ ell : ℂ} {J : ℂ → ℂ}
    (hc : 0 < c) (hρb : 0 < ρb) (hmZ : 0 ≤ mZ) (hcν : c = cOf ν) (hν : 0 < ν) (hε : 0 < ε)
    (hP : 2 * ε * c ≤ 1) (hμ0 : 0 < μ) (hμ1 : μ < 1 / 4) (hι : ∀ A, IsAffElem as (ι A))
    (hUp : IsExactProfile ν (2 * ε * c) (fun τ y => V τ y + rb τ y) p)
    (hM : IsExactMultiplier B ε⁻¹ V rb) (hax : ∀ τ, AxiNoSwirlPt (fun y => V τ y + rb τ y))
    (hR : IsBodyInverse B ε μ) (hS : IsStressInverse B ε μ)
    (hW : IsWardPinned B ε μ hχo χy (fun τ y => V τ y + rb τ y) p)
    (hAff : IsAffinePinned B ι χf μ ε) (hrA : IsRAPinned B ι χf ε μ)
    (hιinj : Function.Injective ι) (hL : IsSourceLPinned B ι S lam κ ell J ε μ χo χy χf) :
    B.toOps.WardStressNormal ∧ B.toOps.PhysAffineIdentity ∧ B.toOps.HNilpotent := by
  exact B.wardAffineNilpotent_of hχo hR hS hW hAff hrA (isLjOld_of B hχo hιinj hν hL)
    (wardEnergyEquation_of B hχo hχy hc hρb hmZ hν hε hμ0 hμ1 hUp hM hax hS hW)
    (freeWeakUniqueness hc hν hε hP (by linarith)) (weakDmuAdd hc hν hε)
    (hhatSolenoidal_of B hχf hι hc hcν hν hε hAff) (wardFieldsZero ν μ ε⁻¹ c χy _)
    (wardYoungPointwise _ hν (inv_pos.2 hε) hχy) (hhatYoungPointwise hχf)
    (chiOMultYoung_of B hM hχo)

end ReturnBase

end UnforcedLeray.Short.PartIIIb.Concrete
