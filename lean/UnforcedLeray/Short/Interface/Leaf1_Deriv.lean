import UnforcedLeray.Short.Interface.Statements
import UnforcedLeray.Infra.JointMeasurableRep
import UnforcedLeray.Cons.C08PhysicalMode.Slices

/-!
# Interface I02: a continuous periodic `L³` path has a periodic jointly measurable representative

Source of record: `the November 2 reference manuscript`, lines 6064-6070
(`∇U ∈ C_per L³`, the `L³` part of the regular-background class `IsL3Background`).

The statement is the leaf `l3Path_rep`. The proof:

1. `Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn` gives a jointly
   strongly measurable `F : ℝ × Space → Space` with `F (t, ·) =ᵐ W t` for every `t`.
2. `dW τ y := F (toIocMod P 0 τ, y)` is the periodization of `F`. It is `P`-periodic by
   `toIocMod_add_right`; it is jointly measurable as `F` composed with the measurable map
   `(τ, y) ↦ (toIocMod τ, y)` (`UnforcedLeray.Cons.C08.measurable_toIocMod`); and
   `dW τ =ᵐ W (toIocMod τ) = W τ` by periodicity of `W`.
3. `τ ↦ ‖W τ‖` is continuous, hence bounded on `[0, P]`. Since `toIocMod τ ∈ (0, P]`, this
   gives a uniform bound on `eLpNorm (dW τ) 3`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint

theorem l3Path_rep {P : ℝ} (hP : 0 < P) (W : ℝ → Lp Space 3 (volume : Measure Space))
    (hWc : Continuous W) (hWp : Function.Periodic W P) :
    ∃ dW : ℝ → SpatialField, Function.Periodic dW P ∧
      AEStronglyMeasurable (fun z : SpaceTime => dW z.1 z.2) volume ∧
      (∀ τ, dW τ =ᵐ[volume] (W τ : SpatialField)) ∧
      ∃ C : ℝ, ∀ τ, eLpNorm (dW τ) 3 volume ≤ ENNReal.ofReal C := by
  -- Step 1: a jointly strongly measurable representative of the whole continuous path.
  obtain ⟨F, hFm, hF⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn
      (μ := (volume : Measure Space)) (f := W) (s := univ) MeasurableSet.univ hWc.continuousOn
  -- Step 2: the phase reduction `toIocMod` is `τ - k • P`, so periodicity of `W` applies.
  have hWmod : ∀ τ : ℝ, W (toIocMod hP 0 τ) = W τ := fun τ => by
    have hmod : toIocMod hP 0 τ = τ - toIocDiv hP 0 τ • P := rfl
    rw [hmod]
    exact hWp.sub_zsmul_eq (toIocDiv hP 0 τ)
  have hrep : ∀ τ : ℝ, (fun y => F (toIocMod hP 0 τ, y)) =ᵐ[volume] (W τ : SpatialField) := by
    intro τ
    have h1 := hF (toIocMod hP 0 τ) (mem_univ _)
    rw [hWmod τ] at h1
    exact h1
  have hmeas : Measurable (fun z : SpaceTime => (toIocMod hP 0 z.1, z.2)) :=
    ((UnforcedLeray.Cons.C08.measurable_toIocMod hP).comp measurable_fst).prodMk measurable_snd
  -- Step 3: the periodization, its periodicity, measurability, and a.e. representation.
  refine ⟨fun τ y => F (toIocMod hP 0 τ, y), fun τ => ?_, ?_, fun τ => hrep τ, ?_⟩
  · simp only [toIocMod_add_right]
  · exact (hFm.comp_measurable hmeas).aestronglyMeasurable
  -- Step 4: a uniform bound from continuity of `τ ↦ ‖W τ‖` on `[0, P]`.
  · obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) P)).exists_bound_of_continuousOn
      (f := fun s : ℝ => ‖W s‖) hWc.norm.continuousOn
    refine ⟨C, fun τ => ?_⟩
    have hmem : toIocMod hP 0 τ ∈ Icc (0 : ℝ) P := by
      have h := toIocMod_mem_Ioc hP 0 τ
      rw [zero_add] at h
      exact Ioc_subset_Icc_self h
    have hb : ‖W τ‖ ≤ C := by
      rw [← hWmod τ]
      have h := hC _ hmem
      simpa using h
    have hnorm : eLpNorm (W τ : SpatialField) 3 volume = ENNReal.ofReal ‖W τ‖ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (W τ))]
    show eLpNorm (fun y => F (toIocMod hP 0 τ, y)) 3 volume ≤ ENNReal.ofReal C
    rw [eLpNorm_congr_ae (hrep τ), hnorm]
    exact ENNReal.ofReal_le_ofReal hb

end UnforcedLeray.Short.Interface
