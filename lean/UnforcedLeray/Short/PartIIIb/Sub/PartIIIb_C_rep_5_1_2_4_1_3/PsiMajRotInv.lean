import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3/4`: rotation invariance of the majorant

Source `the November 2 reference manuscript` 2672-2684 (the source weight depends
on `z` only through `ϱ(z)` and `z₂`).  Proves `PsiMajRotInv`: for `ρ = rotZ α`,
`psiMaj τ (ρ y) = psiMaj τ y`.

In each inner integral the substitution `z = ρ z'` (`MeasurePreserving.lintegral_comp_emb` for the
measurable embedding `ρ`) is applied to the indicator form.  Pointwise:
`ϱ(ρ z) = ϱ z`, `ϱ(ρ y) = ϱ y`, `‖ρ y - l • ρ z‖ = ‖y - l • z‖`, `age R (ρ z) = age R z`,
`chartOf R c (ρ z) σ = chartOf R c z σ` (it reads only `hRad z = ϱ z` and `z 2`, both fixed by ρ).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

theorem psiMajRotInv : PsiMajRotInv := by
  intro R c θ G α τ y
  have hfix : FixesAxis (Axi.rotZ α) := fixesAxis_rotZ α
  have hϱ : ∀ w : Space, ϱ (Axi.rotZ α w) = ϱ w := fun w => ϱ_map hfix w
  have h2 : ∀ w : Space, (Axi.rotZ α w) 2 = w 2 := fun w => apply_two_map hfix w
  have hemb : MeasurableEmbedding (⇑(Axi.rotZ α)) :=
    (Axi.rotZ α).toHomeomorph.measurableEmbedding
  have hmp : MeasurePreserving (⇑(Axi.rotZ α)) := (Axi.rotZ α).measurePreserving
  -- the source weight is invariant under `ρ`
  have hsrc : ∀ (σ : ℝ) (z : Space), srcW R c G σ (Axi.rotZ α z) = srcW R c G σ z := by
    intro σ z
    have hR : NearInst.hRad (Axi.rotZ α z) = NearInst.hRad z := hϱ z
    have hc : NearInst.chartOf R c (Axi.rotZ α z) σ = NearInst.chartOf R c z σ := by
      unfold NearInst.chartOf
      rw [hR, h2 z]
    have ha : age R (Axi.rotZ α z) = age R z := by
      unfold age
      rw [hϱ z]
    unfold srcW
    rw [ha, hc]
  -- the kernel is invariant under `ρ` (both points rotated)
  have hn : ∀ (l : ℝ) (z : Space),
      ‖Axi.rotZ α y - l • Axi.rotZ α z‖ = ‖y - l • z‖ := by
    intro l z
    have e : Axi.rotZ α y - l • Axi.rotZ α z = Axi.rotZ α (y - l • z) := by
      simp only [map_sub, map_smul]
    rw [e, LinearIsometryEquiv.norm_map]
  unfold psiMaj
  refine lintegral_congr fun l => ?_
  have hS1 : MeasurableSet {z : Space | ϱ z < θ * ϱ (Axi.rotZ α y)} :=
    measurableSet_lt measurable_ϱ measurable_const
  have hS2 : MeasurableSet {z : Space | ϱ z < θ * ϱ y} :=
    measurableSet_lt measurable_ϱ measurable_const
  rw [← lintegral_indicator hS1, ← lintegral_indicator hS2]
  refine Eq.trans (hmp.lintegral_comp_emb hemb _).symm ?_
  refine lintegral_congr fun z => ?_
  by_cases h : ϱ z < θ * ϱ y
  · have h' : ϱ (Axi.rotZ α z) < θ * ϱ (Axi.rotZ α y) := by
      rw [hϱ, hϱ]
      exact h
    rw [Set.indicator_of_mem (show Axi.rotZ α z ∈ {z : Space | ϱ z < θ * ϱ (Axi.rotZ α y)} from h'),
      Set.indicator_of_mem (show z ∈ {z : Space | ϱ z < θ * ϱ y} from h)]
    simp only [hn, hsrc]
  · have h' : ¬ ϱ (Axi.rotZ α z) < θ * ϱ (Axi.rotZ α y) := by
      rw [hϱ, hϱ]
      exact h
    rw [Set.indicator_of_notMem (show Axi.rotZ α z ∉ {z : Space | ϱ z < θ * ϱ (Axi.rotZ α y)} from h'),
      Set.indicator_of_notMem (show z ∉ {z : Space | ϱ z < θ * ϱ y} from h)]

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore

end
