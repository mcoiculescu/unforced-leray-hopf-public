import UnforcedLeray.Short.Interface.Statements
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Interface I01: a `C_per C_0` path is continuous, bounded and periodic

Source of record: `the November 2 reference manuscript`, lines 6064-6070
(`U ∈ C_per C_0`, the continuity and boundedness part of the regular-background class).

The statement is the leaf `c0Path_props`. The proof uses only the continuity of `V`, the
bounded-continuous inclusion `ZeroAtInftyContinuousMap.toBCF` (an isometry), evaluation on
bounded continuous functions (`ContinuousEval`), and periodicity to reduce the sup bound to a
compact period interval.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint

/-- Source lines 6064-6070: a continuous `P`-periodic path `V : ℝ → C₀(ℝ³, ℝ³)` gives a
continuous slice, a uniform bound, joint continuity in `(τ, y)`, and a periodic slice map. -/
theorem c0Path_props {P : ℝ} (hP : 0 < P) (V : ℝ → ZeroAtInftyContinuousMap Space Space)
    (hVc : Continuous V) (hVp : Function.Periodic V P) :
    (∀ τ, Continuous (V τ : SpatialField)) ∧
      (∃ C : ℝ, ∀ τ y, ‖(V τ : SpatialField) y‖ ≤ C) ∧
      Continuous (fun z : SpaceTime => (V z.1 : SpatialField) z.2) ∧
      Function.Periodic (fun τ => (V τ : SpatialField)) P := by
  -- (1) each slice is a continuous function on space
  have hslice : ∀ τ, Continuous (V τ : SpatialField) := fun τ => map_continuous (V τ)
  -- pointwise bound by the C₀ norm
  have hnorm : ∀ (τ : ℝ) (y : Space), ‖(V τ : SpatialField) y‖ ≤ ‖V τ‖ := by
    intro τ y
    have h := BoundedContinuousFunction.norm_coe_le_norm (V τ).toBCF y
    rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] at h
    exact h
  -- (2) uniform bound: τ ↦ ‖V τ‖ is continuous, bounded on [0, P], and periodic
  have hbound : ∃ C : ℝ, ∀ τ y, ‖(V τ : SpatialField) y‖ ≤ C := by
    have hg : Continuous (fun τ : ℝ => ‖V τ‖) := continuous_norm.comp hVc
    have hcpt : IsCompact (Icc (0 : ℝ) P) := isCompact_Icc
    obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hg.continuousOn
    refine ⟨C, fun τ y => ?_⟩
    obtain ⟨s, hs, hVs⟩ := hVp.exists_mem_Ico₀ hP τ
    have hsC : ‖‖V s‖‖ ≤ C := hC s ⟨hs.1, hs.2.le⟩
    rw [norm_norm] at hsC
    calc ‖(V τ : SpatialField) y‖ ≤ ‖V τ‖ := hnorm τ y
      _ = ‖V s‖ := by rw [hVs]
      _ ≤ C := hsC
  -- (3) joint continuity: evaluation on bounded continuous functions is jointly continuous
  have hjoint : Continuous (fun z : SpaceTime => (V z.1 : SpatialField) z.2) := by
    have hB : Continuous (fun τ : ℝ => (V τ).toBCF) :=
      ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp hVc
    exact (hB.comp continuous_fst).eval continuous_snd
  -- (4) periodicity of the slice map
  have hper : Function.Periodic (fun τ => (V τ : SpatialField)) P := fun τ => by
    simp only [hVp τ]
  exact ⟨hslice, hbound, hjoint, hper⟩

end UnforcedLeray.Short.Interface
