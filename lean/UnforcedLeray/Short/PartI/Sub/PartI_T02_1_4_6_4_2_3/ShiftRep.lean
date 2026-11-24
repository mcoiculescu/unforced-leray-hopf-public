import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_2_3
import UnforcedLeray.Lib.HeatCylinder.HeatVecGaussianShiftPairing

/-!
# Part I, leaf `PartI:T02/1/4/6/4/2/3/1` (`LeafShiftRepCH`)

Proof: the shift pairing is `inner (planeShiftL2CLM hc v ψL) G`; `ψL` is the `L²` class of the
smooth periodic cell test `ψ`, so it equals `hTm.toLp ψ`, and the library lemma
`HeatCylinder.inner_planeShiftL2_smooth_eq_integral` gives the literal cell integral.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

theorem leafShiftRepCH_proof : LeafShiftRepCH := by
  intro c hc ψ ψL G hψ hψL v
  obtain ⟨hsm, hper, hsupp⟩ := hψ
  have hT : UnforcedLeray.Sob.IsCylSmooth c ψ :=
    { smooth := hsm
      periodic := fun z => by
        have h := hper z
        have e : z + ((c : ℝ), (0 : ℝ)) = (z.1 + c, z.2) := by ext <;> simp
        rw [e]
        exact h
      bounded := hsupp }
  have hTm : MemLp ψ 2 (Cyl.cellμ c) :=
    Cyl.memLp_of_vanishes hsm.continuous (R := hsupp.choose) hsupp.choose_spec 2
  have hUm : MemLp (G : Plane → Vec) 2 (Cyl.cellμ c) := Lp.memLp G
  have heq : hTm.toLp ψ = ψL := Lp.ext ((hTm.coeFn_toLp).trans hψL.symm)
  have key := HeatCylinder.inner_planeShiftL2_smooth_eq_integral hc hT hTm hUm v
  rw [Lp.toLp_coeFn G hUm] at key
  show inner ℝ (HeatCylinder.planeShiftL2CLM hc v ψL) G = _
  rw [HeatCylinder.planeShiftL2CLM_apply, ← heq]
  exact key
