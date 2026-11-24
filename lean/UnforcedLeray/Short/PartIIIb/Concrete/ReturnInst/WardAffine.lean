import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst
import UnforcedLeray.Short.PartIIIb.Proofs.DeferredWardAffine

set_option autoImplicit false

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)
open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem concreteOps_wardAffineNilpotent {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ} (h : NearAt Pl K L μ) (hχy : IsYoungCutoff K.χy) (hχf : IsSourceCutoffC K.χf) (hP : 2 * L.ε * cOf L.ν ≤ 1) (hμ0 : 0 < μ) (hμ1 : μ < 1 / 4) (hUp : IsExactProfile L.ν (2 * L.ε * cOf L.ν) L.U L.pres) (hρb : 0 < L.ρb Pl K) (hmZ : 0 ≤ K.mZ) (hax : ∀ τ, AxiNoSwirlPt (fun y => L.V τ y + L.rb τ y)) (hpin : NearInst.MultPinOfLink) (hs : ∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K), NearInst.IsSplitMult M (L.params Pl).R L.V L.rb) (hR : IsBodyInverse (concreteBase Pl K L μ h) L.ε μ) (hS : ∃ S : LStr Pl K L →L[ℝ] LVel Pl L, IsWeakStressInverse S L.ε μ) (hW : ∃ t : (LStr Pl K L →L[ℝ] LVel Pl L) × (LStr Pl K L →L[ℝ] LVel Pl L) × (LStr Pl K L →L[ℝ] LSrc L), IsWardTriple t.1 t.2.1 t.2.2 L.ε μ K.hχo K.χy L.U L.pres) (hd : AffineFieldData K.as L.ν μ L.ε (gRate Pl) K.χf (affIota K.as)) (hr : ∃ r : AffSp K.as →L[ℝ] LSrc L, IsRAOp (multOp Pl K L) (hAOp Pl K L) (FAOp K L μ) (EAOp K L μ) r (affIota K.as) K.χf L.ε μ) (hLj : ∃ Lj : LStr Pl K L →L[ℝ] AffSp K.as, ∀ T, affIota K.as (Lj T) = LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T) (ha : ∃ a : AffSp K.as, affIota K.as a = aMuFun μ) (hLam : ∃ l : AffSp K.as →L[ℝ] ℝ, ∀ A, l A = LamFun Pl.eigenvalue Pl.kappa Pl.strainCoupling (planarJ Pl) L.ε L.ν μ K.χf (affIota K.as A)) (hKf : ∃ Kf : AffSp K.as →L[ℝ] AffSp K.as, ∀ A, affIota K.as (Kf A) = KflatFun L.flat (cOf L.ν) L.ν L.ε μ K.χo K.χy K.χf (affIota K.as A)) : (ConcreteReturnOps Pl K L μ h).WardStressNormal ∧ (ConcreteReturnOps Pl K L μ h).PhysAffineIdentity ∧ (ConcreteReturnOps Pl K L μ h).HNilpotent :=
  (concreteBase Pl K L μ h).toOps_wardAffineNilpotent K.hχo hχy hχf (cOf_pos L.ν_pos) hρb hmZ rfl L.ν_pos L.ε_pos hP hμ0 hμ1 (affIota_mem K.as) hUp (concreteBase_isExactMultiplier h hpin hs) hax hR (concreteBase_isStressInverse h hS) (concreteBase_isWardPinned h hW) (concreteBase_isAffinePinned h hd) (concreteBase_isRAPinned h hr) (affIota_injective K.as) (concreteBase_isSourceLPinned h hLj ha hLam hKf)

end UnforcedLeray.Short.PartIIIb.Concrete
