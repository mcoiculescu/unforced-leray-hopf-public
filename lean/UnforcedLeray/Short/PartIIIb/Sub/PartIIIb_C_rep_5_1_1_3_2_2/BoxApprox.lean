import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3_2_2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.BoxDenseZ

/-!
# `thinBoxApprox` (source 3905-3912)

Window cut of `1_A T₁` as in `boxDenseZ`; the repair component of a thin stress is `0`, and the
`ρ_b > 0` hypothesis makes the weighted measure `ρ_b⁻¹ ageμ` equivalent to `ageμ`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal Classical Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem thinBoxApprox : ThinBoxApprox := by
  intro c mZ ρb γ ν hc hρ T A hA hT hsupp
  set μ : Measure Chart := gainZ1Measure c mZ γ ν with hμ
  set g : Chart → Ten3 := ⇑T.fst with hg
  have m1 : Measurable g := (Lp.stronglyMeasurable T.fst).measurable
  have hl : MemLp g 2 μ := Lp.memLp T.fst
  set gA : Chart → Ten3 := A.indicator g with hgA
  have mgA : Measurable gA := m1.indicator hA
  have hlA : MemLp gA 2 μ := hl.indicator hA
  have m0 : Measurable (fun _ : Chart => (0 : Ten3)) := measurable_const
  have hsnd : T.snd = 0 := by
    have h2 : (thinPart T).snd = 0 := rfl
    rw [hT] at h2
    exact h2
  have aeμ : ae μ = ae (ageμ c (-1 / 2)) := by
    rw [hμ, NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure]
  have hAeq : gA =ᵐ[μ] g := by
    rw [Filter.EventuallyEq, aeμ]
    filter_upwards [hsupp] with p hp
    by_cases hpA : p ∈ A
    · simp [hgA, Set.indicator_of_mem hpA]
    · simp [hgA, Set.indicator_of_notMem hpA, hp hpA]
  set W : ℕ → Set Chart := bdWin gA (fun _ => 0) with hW
  have hWm : ∀ n, MeasurableSet (W n) := fun n => bdWin_meas mgA m0 n
  set f : ℕ → Chart → Ten3 := fun n => (W n).indicator gA with hf
  have hfbox : ∀ n, NearInst.IsBoxTensor (f n) := by
    intro n
    refine ⟨mgA.indicator (hWm n), ⟨n, fun p => ?_⟩, ⟨1 / ((n : ℝ) + 1), n, n, by positivity,
      fun p hp => ?_⟩⟩
    · by_cases hp : p ∈ W n
      · simp only [hf, Set.indicator_of_mem hp]
        exact hp.2.2.2.1
      · simp only [hf, Set.indicator_of_notMem hp, norm_zero]
        positivity
    · by_cases hpW : p ∈ W n
      · exact ⟨hpW.1, hpW.2.1, hpW.2.2.1⟩
      · exact absurd (by simp [hf, Set.indicator_of_notMem hpW]) hp
  have hfle : ∀ n p, ‖f n p‖ ≤ ‖g p‖ := by
    intro n p
    by_cases hpW : p ∈ W n
    · by_cases hpA : p ∈ A
      · simp [hf, hgA, Set.indicator_of_mem hpW, Set.indicator_of_mem hpA]
      · simp [hf, hgA, Set.indicator_of_mem hpW, Set.indicator_of_notMem hpA]
    · simp [hf, Set.indicator_of_notMem hpW]
  have hfzero : ∀ n p, p ∉ A → f n p = 0 := by
    intro n p hp
    by_cases hpW : p ∈ W n
    · simp [hf, hgA, Set.indicator_of_mem hpW, Set.indicator_of_notMem hp]
    · simp [hf, Set.indicator_of_notMem hpW]
  have hfmem : ∀ n, MemLp (f n) 2 μ := fun n => hlA.indicator (hWm n)
  refine ⟨f, fun n => WithLp.toLp 1 ((hfmem n).toLp (f n), 0), hfbox, hfzero, hfle, ?_, ?_⟩
  · intro n
    have e1 : ((hfmem n).toLp (f n) : Chart → Ten3) =ᵐ[μ] f n := (hfmem n).coeFn_toLp
    rw [aeμ] at e1
    have e2 : ((0 : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν)) : Chart → Ten3) =ᵐ[
        gainHTMeasure c ρb γ ν] 0 := Lp.coeFn_zero _ _ _
    rw [Filter.EventuallyEq, NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ] at e2
    filter_upwards [e1, e2] with p h1 h2
    change ((hfmem n).toLp (f n) : Chart → Ten3) p +
      ((0 : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν)) : Chart → Ten3) p = _
    rw [h1, h2]
    simp
  · have key : ∀ n, ‖T - WithLp.toLp 1 ((hfmem n).toLp (f n), 0)‖ =
        (eLpNorm ((W n)ᶜ.indicator gA) 2 μ).toReal := by
      intro n
      rw [WithLp.prod_norm_eq_of_L1]
      have hs : (T - WithLp.toLp 1 ((hfmem n).toLp (f n), (0 : Lp (α := Chart) Ten3 2
          (gainHTMeasure c ρb γ ν)))).snd = 0 := by
        change T.snd - 0 = 0
        rw [hsnd, sub_zero]
      have hf1 : (T - WithLp.toLp 1 ((hfmem n).toLp (f n), (0 : Lp (α := Chart) Ten3 2
          (gainHTMeasure c ρb γ ν)))).fst = T.fst - (hfmem n).toLp (f n) := rfl
      rw [hs, hf1, norm_zero, add_zero, Lp.norm_def]
      congr 1
      refine eLpNorm_congr_ae ?_
      refine (Lp.coeFn_sub _ _).trans ?_
      filter_upwards [(hfmem n).coeFn_toLp, hAeq] with p h1 h2
      simp only [Pi.sub_apply]
      rw [h1]
      change g p - f n p = _
      rw [← h2]
      by_cases hpW : p ∈ W n
      · have e : p ∉ (W n)ᶜ := fun h => h hpW
        rw [Set.indicator_of_notMem e]
        simp only [hf, Set.indicator_of_mem hpW, hgA, sub_self]
      · rw [Set.indicator_of_mem (show p ∈ (W n)ᶜ from hpW)]
        simp [hf, Set.indicator_of_notMem hpW, hgA]
    have hcov : ∀ᵐ p ∂μ, ∃ n, p ∈ W n := by
      rw [aeμ]
      filter_upwards [UnforcedLeray.Short.IIIa.ae_pos_ageμ c (-1 / 2)] with p hp
      exact bdWin_cover gA (fun _ => 0) hp
    have hT0 := bd_tendsto_cut mgA hlA W hWm (bdWin_mono gA (fun _ => 0)) hcov
    simp_rw [key]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hT0
    exact this

end UnforcedLeray.Short.PartIIIb.Concrete
