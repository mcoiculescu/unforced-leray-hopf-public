import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.ChartConj

/-!
# `LiftVecCplx` (source 1640-1679, 2682)

`B0223.liftVec` on complexified real fields is the complexification of `B0220.J`, moved to the
periodic space by `toX`.  Route: both sides are weighted compositions with the same pointwise
frame-and-weight map; the complexified real field is replaced by the pointwise `merC ∘ g` through
`WeightedComp.compFun_congr`, the chart identity `periodize c g (chart ε y) = g (cellChart ε c y)`
is definitional, and `frameC x (merC v) = cplx3 (frame x v)` for real `v`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- The complexified real frame: `cplx3 (k • frame x v) = k • frameC x (merC v)` for real `v`. -/
theorem cplx3_frame_smul (x : Space) (k : ℝ) (v : UnforcedLeray.B0220.Merid) :
    cplx3 (k • UnforcedLeray.B0220.frame x v) = k • UnforcedLeray.B0223.frameC x (merC v) := by
  ext i
  fin_cases i <;>
    simp [cplx3_apply, UnforcedLeray.B0220.frame_apply, UnforcedLeray.B0223.frameC_apply,
      UnforcedLeray.B0220.unitR, UnforcedLeray.B0223.unitRC, UnforcedLeray.B0220.unitZ,
      UnforcedLeray.B0223.unitZC, merC, Complex.real_smul]

/-- The constant-and-weight frame identity for the lift at a point. -/
theorem cplx3_jConst_fieldU (ε : ℝ) (x : Space) (v : UnforcedLeray.B0220.Merid) :
    cplx3 (UnforcedLeray.B0220.jConst ε • (UnforcedLeray.B0220.liftA x • UnforcedLeray.B0220.frame x v))
      = (UnforcedLeray.B0220.jConst ε * UnforcedLeray.B0220.liftA x) •
          UnforcedLeray.B0223.frameC x (merC v) := by
  rw [← mul_smul, cplx3_frame_smul]

/-- The pointwise value of the weighted composition of the lift. -/
theorem compFun_liftVecWC_apply {P ε c : ℝ} [Fact (0 < P)] (hε : 0 < ε) (hc : 0 < c)
    (hP : P = 2 * ε * c) (f : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
    (z : UnforcedLeray.B0223.PSpace P) :
    (UnforcedLeray.B0223.liftVecWC hε hc hP).compFun f z =
      (UnforcedLeray.B0220.jConst ε * UnforcedLeray.B0220.liftA z.1) •
        UnforcedLeray.B0223.frameC z.1
          (f (UnforcedLeray.B0220.cellChart ε c (UnforcedLeray.B0223.toCell P z))) := rfl

/-- **`LiftVecCplx`**: the complexified lift of a real field is the complexified `J_ε`. -/
theorem liftVecCplx : LiftVecCplx := by
  intro ε c P _ hε hc hP g
  apply Lp.ext
  have h1 : (UnforcedLeray.B0223.liftVec hε hc hP (cplxH c g) :
      UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
      (UnforcedLeray.B0223.liftVecWC hε hc hP).compFun (cplxH c g) := by
    rw [UnforcedLeray.B0223.liftVec, UnforcedLeray.B0223.wcToLIC_apply]
    exact (UnforcedLeray.B0223.liftVecWC hε hc hP).coeFn_toLI _
  have hcomp := (UnforcedLeray.B0223.liftVecWC hε hc hP).compFun_congr (cplxH_ae c g)
  have hJ : ∀ᵐ w ∂(volume : Measure (UnforcedLeray.B0223.PSpace P)),
      ((UnforcedLeray.B0220.J hε hc g : UnforcedLeray.B0220.PhysL2 ε c) :
          Space × ℝ → Space) (UnforcedLeray.B0223.toCell P w) =
        (UnforcedLeray.B0220.jConst ε) •
          UnforcedLeray.B0220.fieldU ε (UnforcedLeray.B0220.periodize c g)
            (UnforcedLeray.B0223.toCell P w) := by
    have hq := (mp_toCell_phys (P := P) hP).quasiMeasurePreserving
    filter_upwards [hq.ae (UnforcedLeray.B0220.coeFn_J hε hc g)] with w hw
    exact hw
  have htoX := toX_ae hP (UnforcedLeray.B0220.J hε hc g)
  filter_upwards [h1, hcomp, htoX, hJ] with w hw1 hw2 hw3 hw4
  rw [hw1, hw2, hw3, hw4, compFun_liftVecWC_apply hε hc hP]
  simp only [UnforcedLeray.B0220.fieldU]
  rw [cplx3_jConst_fieldU]
  rfl

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
