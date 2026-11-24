import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelTensorDensity
import UnforcedLeray.Lib.SobolevC.CylExtend
import UnforcedLeray.Units.B0289.Periodize

/-!
# Boundedness of smooth periodic kernel tensors

The compact-axial smooth fields supplied by the genuine cylinder Sobolev density theorem are
globally bounded: periodicity reduces the horizontal coordinate to one compact cell, and the
vertical support condition reduces the other coordinate to a compact interval.
-/

set_option autoImplicit false

noncomputable section

open Set
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0284
open UnforcedLeray.B0289

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open UnforcedLeray.TrainB (TensorVal)

/-- A continuous field with the actual `IsCylSmooth` periodicity and axial support is bounded
on the whole plane. -/
theorem exists_bound_of_isCylSmooth {c : ℝ} (hc : 0 < c)
    {u : Plane → TensorVal} (hu : UnforcedLeray.Sob.IsCylSmooth c u) :
    ∃ M : ℝ, ∀ z, ‖UnforcedLeray.TrainB.tensorToPlaneCLE (u z)‖ ≤ M := by
  rcases hu.bounded with ⟨R, hR⟩
  let R' := max R 0
  let K : Set Plane := Set.Icc (-(c / 2)) (c / 2) ×ˢ Set.Icc (-R') R'
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  let g : Plane → ℝ := fun z => ‖UnforcedLeray.TrainB.tensorToPlaneCLE (u z)‖
  have hg : Continuous g := by
    exact (UnforcedLeray.TrainB.tensorToPlaneCLE.continuous.comp hu.smooth.continuous).norm
  have hbdd := hK.bddAbove_image hg.continuousOn
  rcases hbdd with ⟨M, hM⟩
  refine ⟨max M 0, fun z => ?_⟩
  let q₀ := toIcoMod hc (-(c / 2)) z.1
  let z₀ : Plane := (q₀, z.2)
  have hq₀ : q₀ ∈ Set.Ico (-(c / 2)) (-(c / 2) + c) :=
    toIcoMod_mem_Ico hc (-(c / 2)) z.1
  have hq₀' : q₀ ∈ Set.Icc (-(c / 2)) (c / 2) := by
    constructor
    · exact hq₀.1
    · have : -(c / 2) + c = c / 2 := by ring
      rw [this] at hq₀
      exact hq₀.2.le
  by_cases hη : R' < |z.2|
  · have hzero : u z = 0 := hR z (lt_of_le_of_lt (le_max_left _ _) hη)
    change ‖UnforcedLeray.TrainB.tensorToPlaneCLE (u z)‖ ≤ max M 0
    rw [hzero]
    simp only [map_zero, norm_zero]
    exact le_max_right M 0
  · have hη' : z.2 ∈ Set.Icc (-R') R' := by
      have habs := (abs_le.mp (le_of_not_gt hη))
      exact habs
    have hz₀K : z₀ ∈ K := ⟨hq₀', hη'⟩
    have hdecomp : z = z₀ + (toIcoDiv hc (-(c / 2)) z.1 • c, 0) := by
      have hq : q₀ + toIcoDiv hc (-(c / 2)) z.1 • c = z.1 := by
        simpa [q₀] using toIcoMod_add_toIcoDiv_zsmul hc (-(c / 2)) z.1
      ext
      · simpa [z₀] using hq.symm
      · simp [z₀]
    have hperiodic : IsQPeriodic c u := by
      intro w
      simpa [Prod.add_def] using hu.periodic w
    have hval : u z = u z₀ := by
      rw [hdecomp]
      simpa [z₀, Prod.add_def] using
        IsQPeriodic.add_int_mul hperiodic (toIcoDiv hc (-(c / 2)) z.1) z₀
    have hbound : g z₀ ≤ M := hM ⟨z₀, hz₀K, rfl⟩
    change g z ≤ max M 0
    change ‖UnforcedLeray.TrainB.tensorToPlaneCLE (u z)‖ ≤ max M 0
    rw [hval]
    exact le_trans hbound (le_max_left _ _)

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.exists_bound_of_isCylSmooth
