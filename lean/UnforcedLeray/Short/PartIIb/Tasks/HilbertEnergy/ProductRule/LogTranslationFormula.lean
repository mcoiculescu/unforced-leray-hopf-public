import UnforcedLeray.Short.PartIIb.Sub.T15_2
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogFundamental
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogShiftWeak
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogAvgLocInt
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogTestBounds

/-!
# Part II-b, task `PartII-b:T15/2/9`: the translation formula in the logarithmic chart

Source of record: `the November 2 reference manuscript`, lines 1975-1979. The target is
the Prop `LogTranslationFormula` (`Sub/T15_2.lean`, leaf `PartII-b:T15/2/9`), proved unchanged.

Proof outline. Fix `c, u, g, h`, put `G = g - u/4` and
`F x = u(x.1 + h, x.2) - u x - ∫_0^h G(x.1 + σ, x.2) dσ`.
1. `F` is a.e.-strongly measurable and integrable on every box `{|t| ≤ T, |η| ≤ L}`
   (`u(· + h)` and `u` are `L²`, the box has finite `logMeas c`-measure, and the average is
   integrable there by `LogAvgLocInt`).
2. For a `LogTest Φ`, `∫ F Φ = ∫ (u(·+h) - u) Φ - ∫ (avg) Φ = 0`, by `LogShiftWeak`.
3. `LogFundamental` gives `F =ᵐ 0`, and `sub_eq_zero` finishes.
-/

set_option autoImplicit false

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb

/-- An `L²` function is integrable on every box `{|t| ≤ T, |η| ≤ L}` of the logarithmic chart. -/
theorem logTr_box_integrable {c : ℝ} {f : Coord → ℂ} (hf : MemLp f 2 (logMeas c)) (T L : ℝ) :
    IntegrableOn f {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L} (logMeas c) := by
  have : IsFiniteMeasure ((logMeas c).restrict {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L}) :=
    isFiniteMeasure_restrict.mpr (logAL_box_lt_top c T L).ne
  exact (hf.restrict _).integrable (by norm_num)

/-- **Leaf `PartII-b:T15/2/9`** (the translation formula; uses `T15/2/6`, `T15/2/8`, `T15/2/17`). -/
theorem logTranslationFormula : UnforcedLeray.Short.IIb.LogTranslationFormula := by
  intro c u g hc hu hg hweak h
  have hu_h : MemLp (fun x : Coord => u (x.1 + h, x.2)) 2 (logMeas c) :=
    hu.comp_measurePreserving (logAL_measurePreserving c h)
  have hu4 : MemLp (fun x : Coord => u x / 4) 2 (logMeas c) := by
    have h4 := hu.const_mul (4⁻¹ : ℂ)
    simpa only [div_eq_inv_mul] using h4
  have hGmem : MemLp (fun x : Coord => g x - u x / 4) 2 (logMeas c) := hg.sub hu4
  obtain ⟨hAm, hAint⟩ := logAvgLocInt c (fun x : Coord => g x - u x / 4) hc hGmem h
  -- the function `F` of the proof
  have hFm : AEStronglyMeasurable (fun x : Coord => u (x.1 + h, x.2) - u x
      - ∫ σ in (0 : ℝ)..h, (g (x.1 + σ, x.2) - u (x.1 + σ, x.2) / 4)) (logMeas c) :=
    (hu_h.aestronglyMeasurable.sub hu.aestronglyMeasurable).sub hAm
  have hFint : ∀ T L : ℝ, IntegrableOn (fun x : Coord => u (x.1 + h, x.2) - u x
      - ∫ σ in (0 : ℝ)..h, (g (x.1 + σ, x.2) - u (x.1 + σ, x.2) / 4))
      {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L} (logMeas c) := by
    intro T L
    exact ((logTr_box_integrable hu_h T L).sub (logTr_box_integrable hu T L)).sub (hAint T L)
  -- the test identity
  have hFtest : ∀ Φ : Coord → ℝ, LogTest c Φ →
      ∫ x, (u (x.1 + h, x.2) - u x
        - ∫ σ in (0 : ℝ)..h, (g (x.1 + σ, x.2) - u (x.1 + σ, x.2) / 4)) * (Φ x : ℂ)
        ∂(logMeas c) = 0 := by
    intro Φ hΦ
    obtain ⟨T, L, hTL⟩ := hΦ.compact
    obtain ⟨⟨C₀, hC₀⟩, _, hint⟩ := logTestBounds c Φ hc hΦ
    have hI1 : Integrable (fun x : Coord => u x * (Φ x : ℂ)) (logMeas c) :=
      (hint u hu).1
    have hI2 : Integrable (fun x : Coord => u (x.1 + h, x.2) * (Φ x : ℂ)) (logMeas c) :=
      (hint (fun x : Coord => u (x.1 + h, x.2)) hu_h).1
    have hLHSint : Integrable (fun x : Coord => (u (x.1 + h, x.2) - u x) * (Φ x : ℂ))
        (logMeas c) :=
      (hI2.sub hI1).congr (ae_of_all _ fun x => by simp only [Pi.sub_apply, sub_mul])
    -- the support of the average-times-test lies in the box
    have hSupp : Function.support (fun x : Coord =>
        (∫ σ in (0 : ℝ)..h, (g (x.1 + σ, x.2) - u (x.1 + σ, x.2) / 4)) * (Φ x : ℂ))
        ⊆ {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L} := by
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hcon
      apply hx
      have hΦx : Φ x = 0 := by
        apply hTL x
        simp only [Set.mem_setOf_eq, not_and_or, not_le] at hcon
        exact hcon
      simp [hΦx]
    have hAΦ : Integrable (fun x : Coord =>
        (∫ σ in (0 : ℝ)..h, (g (x.1 + σ, x.2) - u (x.1 + σ, x.2) / 4)) * (Φ x : ℂ))
        (logMeas c) := by
      refine (integrableOn_iff_integrable_of_support_subset hSupp).mp ?_
      have hbdd : Integrable (fun x : Coord =>
          (Φ x : ℂ) * (∫ σ in (0 : ℝ)..h, (g (x.1 + σ, x.2) - u (x.1 + σ, x.2) / 4)))
          ((logMeas c).restrict {x : Coord | |x.1| ≤ T ∧ |x.2.2| ≤ L}) := by
        have hΦc : Continuous (fun x : Coord => ((Φ x : ℝ) : ℂ)) :=
          Complex.continuous_ofReal.comp hΦ.smooth.continuous
        refine Integrable.bdd_mul (c := C₀) (hAint T L) hΦc.aestronglyMeasurable
          (ae_of_all _ fun x => ?_)
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact hC₀ x
      exact hbdd.congr (ae_of_all _ fun x => mul_comm _ _)
    have hsplit : ∫ x, (u (x.1 + h, x.2) - u x) * (Φ x : ℂ) ∂(logMeas c)
        = ∫ x, (∫ σ in (0 : ℝ)..h, (g (x.1 + σ, x.2) - u (x.1 + σ, x.2) / 4)) * (Φ x : ℂ)
          ∂(logMeas c) :=
      logShiftWeak c u g hc hu hg hweak h Φ hΦ
    have hFsplit : ∫ x, (u (x.1 + h, x.2) - u x
        - ∫ σ in (0 : ℝ)..h, (g (x.1 + σ, x.2) - u (x.1 + σ, x.2) / 4)) * (Φ x : ℂ)
        ∂(logMeas c)
        = ∫ x, (u (x.1 + h, x.2) - u x) * (Φ x : ℂ) ∂(logMeas c)
          - ∫ x, (∫ σ in (0 : ℝ)..h, (g (x.1 + σ, x.2) - u (x.1 + σ, x.2) / 4))
            * (Φ x : ℂ) ∂(logMeas c) := by
      rw [← integral_sub hLHSint hAΦ]
      congr 1
      funext x
      ring
    rw [hFsplit, hsplit, sub_self]
  -- conclude by the periodic fundamental lemma
  have hz := logFundamental c (fun x : Coord => u (x.1 + h, x.2) - u x
      - ∫ σ in (0 : ℝ)..h, (g (x.1 + σ, x.2) - u (x.1 + σ, x.2) / 4)) hc hFm hFint hFtest
  filter_upwards [hz] with x hx
  have hx' : u (x.1 + h, x.2) - u x
      - ∫ σ in (0 : ℝ)..h, (g (x.1 + σ, x.2) - u (x.1 + σ, x.2) / 4) = 0 := hx
  exact sub_eq_zero.mp hx'

end UnforcedLeray.Short.IIb
