import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2_2
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol2.PairWithLift.VelPhysDict

/-!
# `OuterVelJoint` (task `PartIII-b:C/near/pins/3/4/2/2/3`)

Source `the November 2 reference manuscript` lines 2671-2689: the chart
`s = R²/ρ²`, `q = R log(ρ/R) + Rτ/2`, `η = Rz/ρ`, the lift `𝒩_v b = √s b` and the change of
variables. The joint `(x, τ)` statement is proved by the weighted composition `jComp`
(its `ae_comp`), the dictionary `nv_eq_fieldU`, and a pointwise componentwise identity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

/-- A real meridional vector `v` seen in `ℂ²`, multiplied by a real scalar `a`, is mapped by the
complex meridional frame to the real Cartesian vector `a • frame x v` seen in `ℂ³`. -/
theorem smul_frameC_merC_eq_realC (a : ℝ) (x : Space) (v : Merid) :
    a • UnforcedLeray.B0223.frameC x (merC v) =
      UnforcedLeray.B0412.realC (a • UnforcedLeray.B0220.frame x v) := by
  ext i
  fin_cases i <;>
    simp [UnforcedLeray.B0223.frameC_apply, UnforcedLeray.B0223.unitRC,
      UnforcedLeray.B0223.unitZC, merC, UnforcedLeray.B0220.frame_apply,
      UnforcedLeray.B0220.unitR, UnforcedLeray.B0220.unitZ, UnforcedLeray.B0412.realC_apply,
      Complex.real_smul]

theorem realC_zero_eq : UnforcedLeray.B0412.realC (0 : Space) = 0 := by
  ext i
  simp [UnforcedLeray.B0412.realC_apply]

theorem outerVelJoint : OuterVelJoint := by
  intro p
  refine ⟨1, one_ne_zero, fun u f hf => ?_⟩
  unfold ChartRep at hf
  have hae := (UnforcedLeray.B0220.jComp p.ε_pos p.c_pos).ae_comp
    (P := fun q => (u : Profile → MeridC) q = merC (f (cellPt p.c q))) hf
  have hJ : UnforcedLeray.B0220.jConst p.ε ≠ 0 := by
    have hε := p.ε_pos
    unfold UnforcedLeray.B0220.jConst; positivity
  change ∀ᵐ z ∂UnforcedLeray.B0220.physMeasure p.ε p.c, _
  filter_upwards [hae] with z hz
  rw [one_smul]
  have hV : velPhys p.ε⁻¹ p.c f (z.2, p.ε⁻¹ • z.1) =
      UnforcedLeray.B0412.realC (UnforcedLeray.B0220.fieldU p.ε
        (UnforcedLeray.B0220.periodize p.c (fun q => f (cellPt p.c q))) (z.1, z.2)) := by
    unfold velPhys
    exact congrArg UnforcedLeray.B0412.realC (nv_eq_fieldU p.ε_pos p.c_pos f z.1 z.2)
  rw [hV]
  unfold UnforcedLeray.B0220.fieldU
  have hL : UnforcedLeray.B0220.periodize p.c (u : Profile → MeridC)
      (UnforcedLeray.B0220.chart p.ε z) =
        (u : Profile → MeridC) (UnforcedLeray.B0220.cellChart p.ε p.c z) := rfl
  rw [hL]
  by_cases h0 : UnforcedLeray.B0220.liftA z.1 = 0
  · rw [h0, zero_smul, zero_smul, realC_zero_eq]
  · have hz' : (u : Profile → MeridC) (UnforcedLeray.B0220.cellChart p.ε p.c z) =
        merC (f (cellPt p.c (UnforcedLeray.B0220.cellChart p.ε p.c z))) :=
      hz (mul_ne_zero hJ h0)
    rw [hz']
    exact smul_frameC_merC_eq_realC _ _ _
