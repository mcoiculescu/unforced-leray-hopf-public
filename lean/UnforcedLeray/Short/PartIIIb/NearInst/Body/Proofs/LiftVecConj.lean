import UnforcedLeray.Short.PartIIIb.NearInst.Body.Defs

/-!
# `LiftVecConj` (source 1638-1646)

The meridional lift `J_ε = B0223.liftVec` is a weighted composition with a real weight `ρ`, and a
real frame: `L z (v) = (jConst ε * liftA z.1) • frameC z.1 v` with `frameC` built on the real
vectors `e_r`, `e_z` (complexified).  Conjugation commutes with each pointwise map
`L z`, hence with `J_ε` almost everywhere.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.NearInst.Body

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.B0223
open UnforcedLeray.B0220 (HSpace measureH Profile cell)

/-- The pointwise frame-and-weight map commutes with conjugation. -/
theorem liftVecWC_conj {P ε c : ℝ} [Fact (0 < P)] (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (z : PSpace P) (v : MeridC) :
    (liftVecWC hε hc hP).L z (conjV 2 v) = conjV 3 ((liftVecWC hε hc hP).L z v) := by
  simp only [liftVecWC, LinearMap.smul_apply, LinearMap.restrictScalars_apply]
  ext i
  fin_cases i <;>
    simp [frameC_apply, unitRC, unitZC, Complex.real_smul,
      conjV_apply, Complex.conj_ofReal]

/-- **The meridional lift is real** (source 1638-1646). -/
theorem liftVecConj : LiftVecConj := by
  intro P ε c _ hε hc hP b
  apply Lp.ext
  have h1 : (liftVec hε hc hP (cjLp (measureH c) 2 b) : PSpace P → SpaceC) =ᵐ[volume]
      (liftVecWC hε hc hP).compFun (cjLp (measureH c) 2 b) := by
    rw [liftVec, wcToLIC_apply]
    exact (liftVecWC hε hc hP).coeFn_toLI _
  have h3 : (liftVec hε hc hP b : PSpace P → SpaceC) =ᵐ[volume]
      (liftVecWC hε hc hP).compFun b := by
    rw [liftVec, wcToLIC_apply]
    exact (liftVecWC hε hc hP).coeFn_toLI _
  have h4 := (liftVecWC hε hc hP).compFun_congr (coeFn_cjLp (measureH c) 2 b)
  have h2 := coeFn_cjLp (volume : Measure (PSpace P)) 3 (liftVec hε hc hP b)
  filter_upwards [h1, h4, h3, h2] with z hz1 hz4 hz3 hz2
  rw [hz1, hz4, hz2, hz3]
  simp only [UnforcedLeray.B0220.WeightedComp.compFun]
  rw [liftVecWC_conj]

end UnforcedLeray.Short.PartIIIb.NearInst.Body
