import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.Assembly
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.OldNorm
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.XAdd
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.XDiff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.YHAdd
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.EAdd
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Smul
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.YMeas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.HMeas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.EMeas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.YBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.HBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.EBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L8

/-!
# `PartIII-b:C/ward`: `seqWardTriple_exists`

Source: `the November 2 reference manuscript` lines 4161-4303, 5926-5950.
Assembles `seqWardTriple_exists` from `seqWardTriple_exists_ofL` and the 18 leaf/input theorems.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)
open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem seqWardTriple_exists (D : SeqData) {dm dp : ℝ}
    (hq : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair D.Pl.eigenvalue D.Pl.mode)
    (hω : D.Pl.eigenvalue.im ≠ 0) (hσ0 : 0 < D.σ₀) (hσ1 : D.σ₀ < 1 / 4)
    (hm0 : 0 < D.K.m0) (h2m : 2 * D.K.m0 < 3 * dm / 11) (hC0 : 0 < D.K.C0)
    (hmZ : 0 ≤ D.K.mZ) (hχy : IsYoungCutoff D.K.χy)
    (hact : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ t : (LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n)) ×
            (LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n)) ×
            (LStr D.Pl D.K (D.level n) →L[ℝ] LSrc (D.level n)),
        IsWardTriple t.1 t.2.1 t.2.2 (D.level n).ε (D.mu n z) D.K.hχo D.K.χy
          (D.level n).U (D.level n).pres :=
  seqWardTriple_exists_ofL D chartOfNullPullback sepWCongrAE
    (wardOldNormLe_of gainMeasureLower) wardSmul_proved
    (wardYHAdd_of wardXAdd_proved wardXDiff_proved)
    (wardEAdd_of wardXAdd_proved wardXDiff_proved
      (wardYHAdd_of wardXAdd_proved wardXDiff_proved))
    wardYMeas_proved wardHMeas_proved wardEMeas_proved
    wardYBound_proved (wardHBoundL_of wardXYoungL2_proved) wardEBoundL_proved
    bgYoungW2_proved bgPresY2B_proved
    hq hω hσ0 hσ1 hm0 h2m hC0 hmZ hχy hact

end UnforcedLeray.Short.PartIIIb.Concrete
