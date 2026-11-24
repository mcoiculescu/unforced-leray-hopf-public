import UnforcedLeray.Short.PartIIIa.Sub.T21_3_Horizon
import UnforcedLeray.Infra.VolterraEvolution

/-!
# Part III-a, `PartIII-a:T21/3/9/5`: locality of the horizon evolutions

Source of record: `the November 2 reference manuscript`, SP 2819-2836 (the
evolution is unique). Statement `HorizonLocality` is in `Sub/T21_3_Horizon.lean`.

Two horizon evolutions with the same heat family agree on common ages `0 ≤ s ≤ τ ≤ T, T'`.
Step 1 is one unit strip, by uniqueness of the strip Volterra equation
(`VolterraData.eqOn_stripEvolution`) with the clamped fluxes agreeing on the strip
(`actualTrainFluxBOn_congr`). Step 2 is the induction on strips of
`VolterraData.eq_evolution_of_volterra`, using the evolution law `evolution_apply_comp`.
-/

set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
open UnforcedLeray.Infra.VolterraEvolution

/-- **Locality of the horizon evolutions** (`T21/3/9/5`). -/
theorem horizonLocality : UnforcedLeray.Short.IIIa.Exist.HorizonLocality := by
  intro ν c m _ hm tr H T T' hT hT' P P' s τ hs hsτ hτT hτT'
  have hD := horizonData_compatible hm P H
  have hD' := horizonData_compatible hm P' H
  -- Step 1: one unit strip.
  have step1 : ∀ σ t : ℝ, 0 ≤ σ → σ ≤ t → t ≤ σ + 1 → t ≤ T → t ≤ T' → ∀ x,
      (horizonData hm P H).evolution t σ x = (horizonData hm P' H).evolution t σ x := by
    intro σ t hσ hσt ht1 htT htT' x
    have hσt' : t ∈ Icc σ (σ + 1) := ⟨hσt, ht1⟩
    rw [VolterraData.evolution_eq_stripEvolution hD hσt',
      VolterraData.evolution_eq_stripEvolution hD' hσt']
    have hcont : ContinuousOn (fun u => (horizonData hm P H).stripEvolution u σ x) (Icc σ t) :=
      ((horizonData hm P H).continuousOn_stripEvolution σ x).mono (Icc_subset_Icc_right ht1)
    have heq : ∀ u ∈ Icc σ t, (horizonData hm P H).stripEvolution u σ x =
        (horizonData hm P' H).S₀ (u - σ) x + ∫ r in σ..u,
          (horizonData hm P' H).S (u - r)
            ((horizonData hm P' H).B r ((horizonData hm P H).stripEvolution r σ x)) := by
      intro u hu
      have hu' : u ∈ Icc σ (σ + 1) := ⟨hu.1, hu.2.trans ht1⟩
      rw [(horizonData hm P H).stripEvolution_eq hu' x]
      congr 1
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hu.1] at hr
      have hB : (horizonData hm P H).B r = (horizonData hm P' H).B r :=
        actualTrainFluxBOn_congr hm P P' (le_trans hσ hr.1) ((hr.2.trans hu.2).trans htT)
          ((hr.2.trans hu.2).trans htT')
      rw [hB]
      rfl
    exact ((horizonData hm P' H).eqOn_stripEvolution (s := σ) (T := t) ht1 hcont heq t
      ⟨hσt, le_rfl⟩)
  -- Step 2: induction on strips.
  have key : ∀ n : ℕ, ∀ σ u : ℝ, 0 ≤ σ → σ ≤ u → u ≤ T → u ≤ T' → u ≤ σ + n + 1 → ∀ x,
      (horizonData hm P H).evolution u σ x = (horizonData hm P' H).evolution u σ x := by
    intro n
    induction n with
    | zero =>
      intro σ u hσ h1 h2 h3 h4 x
      push_cast at h4
      exact step1 σ u hσ h1 (by linarith) h2 h3 x
    | succ n ih =>
      intro σ u hσ h1 h2 h3 h4 x
      by_cases h : u ≤ σ + 1
      · exact step1 σ u hσ h1 h h2 h3 x
      · rw [not_le] at h
        have hs1 : σ ≤ σ + 1 := by linarith
        have hs2 : σ + 1 ≤ u := h.le
        calc (horizonData hm P H).evolution u σ x
            = (horizonData hm P H).evolution u (σ + 1)
                ((horizonData hm P H).evolution (σ + 1) σ x) :=
              (VolterraData.evolution_apply_comp hD hs1 hs2 x).symm
          _ = (horizonData hm P' H).evolution u (σ + 1)
                ((horizonData hm P H).evolution (σ + 1) σ x) := by
              refine ih (σ + 1) u (by linarith) hs2 h2 h3 ?_ _
              push_cast at h4
              linarith
          _ = (horizonData hm P' H).evolution u (σ + 1)
                ((horizonData hm P' H).evolution (σ + 1) σ x) := by
              rw [step1 σ (σ + 1) hσ hs1 le_rfl (by linarith) (by linarith) x]
          _ = (horizonData hm P' H).evolution u σ x :=
              VolterraData.evolution_apply_comp hD' hs1 hs2 x
  refine ContinuousLinearMap.ext fun x => ?_
  exact key ⌊τ - s⌋₊ s τ hs hsτ hτT hτT' (by
    have := Nat.lt_floor_add_one (τ - s)
    linarith) x

end UnforcedLeray.Short.IIIa.Exist
