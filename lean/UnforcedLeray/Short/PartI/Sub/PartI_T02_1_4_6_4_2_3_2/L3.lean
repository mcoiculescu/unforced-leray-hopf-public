import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_2_3_2
import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_2_3.ShiftRep

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Short.PartI

theorem leafParamIntBoundedCH_proof : UnforcedLeray.Short.PartI.LeafParamIntBoundedCH := by
  unfold LeafParamIntBoundedCH
  intro c hc ψ G hψ
  have hTm : MemLp ψ 2 (Cyl.cellμ c) := by
    obtain ⟨hsm, _, hsupp⟩ := hψ
    exact Cyl.memLp_of_vanishes hsm.continuous (R := hsupp.choose) hsupp.choose_spec 2
  have heq : ((hTm.toLp ψ : Cyl.L2v c) : Plane → Vec) =ᵐ[Cyl.cellμ c] ψ := hTm.coeFn_toLp
  refine ⟨‖hTm.toLp ψ‖ * ‖G‖, fun x => ?_⟩
  have hrep := leafShiftRepCH_proof c hc ψ (hTm.toLp ψ) G hψ heq x
  have hiso : ∀ y : Cyl.L2v c, ‖HeatCylinder.planeShiftL2CLM hc x y‖ = ‖y‖ := by
    intro y
    show ‖(UnforcedLeray.TrainB.qShiftL2Isometry hc (-x.1))
      ((UnforcedLeray.TrainB.etaShiftL2 c (-x.2)) y)‖ = ‖y‖
    rw [LinearIsometry.norm_map, LinearIsometry.norm_map]
  have hp : paramIntCH c ψ G x = inner ℝ (HeatCylinder.planeShiftL2CLM hc x (hTm.toLp ψ)) G :=
    hrep.symm
  rw [hp]
  refine (norm_inner_le_norm _ _).trans (le_of_eq ?_)
  rw [hiso]
