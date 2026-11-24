import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.PhaseFold
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L5
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.CoeffMult
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4.WardBin

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3/19`: the folded source mass

Source `the November 2 reference manuscript` 5571-5575 (`N₀(a)`), 2679-2684
(chart change of variables).  Proves `SourceMass`: with `P = 2c/R`, `G = ‖g‖ₑ`,

`∫⁻ 1_{age>a₀} srcW √omega2(σ) ≤ (√P + 1/√P) · P πR² · N₀(a₀)`.

Route: Tonelli over `ℝ × Space` gives `∫⁻ σ, √omega2(σ) H(σ)` with `H σ = ∫⁻ z, 1_{age>a₀} srcW σ z`;
`H` is measurable and `P`-periodic (`chartOf_add_int_period`), so `phaseFold` gives
`(√P + 1/√P) ∫⁻_{(0,P]} H`; `H σ` is the chart integral of `1_{s>a₀} s G`, and
`chartPhaseLIntegral` plus `lintegral_ageμ_succ'` identify the result with `P πR² N₀(a₀)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

/-- The chart integrand `s · G` restricted to the ages `s > a₀`. -/
def sourceFun (G : Chart → ℝ≥0∞) (a0 : ℝ) : Chart → ℝ≥0∞ :=
  Set.indicator {p : Chart | a0 < p.1} (fun p => ENNReal.ofReal p.1 * G p)

/-- The general form of `SourceMass` for an arbitrary measurable chart weight `G`. -/
theorem sourceMass_of_G (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (G : Chart → ℝ≥0∞)
    (hG : Measurable G) (a0 : ℝ) :
    ∫⁻ a : ℝ × Space, Set.indicator {a : ℝ × Space | a0 < age R a.2}
        (fun a => srcW R c G a.1 a.2) a *
        ENNReal.ofReal (Real.sqrt (omega2 (2 * c / R) a.1)) ≤
      ENNReal.ofReal (Real.sqrt (2 * c / R) + 1 / Real.sqrt (2 * c / R)) *
        ENNReal.ofReal (2 * c / R * (Real.pi * R ^ 2)) *
        ∫⁻ p in {p : Chart | a0 < p.1}, G p ∂(ageμ c (-3 / 2)) := by
  have hP : 0 < 2 * c / R := div_pos (mul_pos two_pos hc) hR
  have hage : Measurable (fun z : Space => age R z) := by
    unfold age
    exact measurable_const.div (measurable_ϱ.pow_const 2)
  have hset : MeasurableSet {a : ℝ × Space | a0 < age R a.2} :=
    measurableSet_lt measurable_const (hage.comp measurable_snd)
  have hω : Measurable (omega2 (2 * c / R)) := by
    unfold omega2
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
      (measurable_const.mul (measurable_const.min Real.measurable_exp)) measurable_const
  have hInd : Measurable (fun a : ℝ × Space => Set.indicator {a : ℝ × Space | a0 < age R a.2}
      (fun a => srcW R c G a.1 a.2) a) :=
    (measurable_srcW R c hG).indicator hset
  have hfull : Measurable (fun a : ℝ × Space => Set.indicator {a : ℝ × Space | a0 < age R a.2}
      (fun a => srcW R c G a.1 a.2) a *
      ENNReal.ofReal (Real.sqrt (omega2 (2 * c / R) a.1))) :=
    hInd.mul (ENNReal.measurable_ofReal.comp
      (Real.continuous_sqrt.measurable.comp (hω.comp measurable_fst)))
  -- periodicity of the source weight in the phase
  have hcp : ∀ (z : Space) (σ : ℝ), NearInst.chartOf R c z (σ + 2 * c / R) = NearInst.chartOf R c z σ := by
    intro z σ
    have h1 := chartOf_add_int_period R c hR hc z σ 1
    simpa only [Int.cast_one, one_mul] using h1
  have hsrc : ∀ (z : Space) (σ : ℝ), srcW R c G (σ + 2 * c / R) z = srcW R c G σ z := by
    intro z σ
    unfold srcW
    rw [hcp z σ]
  -- the phase-slice integral `H`
  have hHmeas : Measurable (fun σ : ℝ => ∫⁻ z, Set.indicator {a : ℝ × Space | a0 < age R a.2}
      (fun a => srcW R c G a.1 a.2) (σ, z)) :=
    hInd.lintegral_prod_right'
  have hHper : Function.Periodic (fun σ : ℝ => ∫⁻ z, Set.indicator {a : ℝ × Space | a0 < age R a.2}
      (fun a => srcW R c G a.1 a.2) (σ, z)) (2 * c / R) := by
    intro σ
    dsimp only
    refine lintegral_congr fun z => ?_
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, hsrc z σ]
  -- the chart form of the slice integral
  have hfst : ∀ (z : Space) (σ : ℝ), (NearInst.chartOf R c z σ).1 = age R z := fun z σ => rfl
  have hHF : ∀ σ : ℝ, (∫⁻ z, Set.indicator {a : ℝ × Space | a0 < age R a.2}
      (fun a => srcW R c G a.1 a.2) (σ, z)) =
      ∫⁻ z, sourceFun G a0 (NearInst.chartOf R c z σ) := by
    intro σ
    refine lintegral_congr fun z => ?_
    simp only [sourceFun, srcW, Set.indicator_apply, Set.mem_ofPred_eq, hfst z σ]
  have hFm : Measurable (sourceFun G a0) := by
    have hm : Measurable (fun p : Chart => ENNReal.ofReal p.1 * G p) :=
      (ENNReal.measurable_ofReal.comp measurable_fst).mul hG
    exact hm.indicator (measurableSet_lt measurable_const measurable_fst)
  -- the chart integral against `ageμ (-5/2)` is the source mass `N₀(a₀)`
  have hkey : ∫⁻ p, sourceFun G a0 p ∂(ageμ c (-5 / 2)) =
      ∫⁻ p in {p : Chart | a0 < p.1}, G p ∂(ageμ c (-3 / 2)) := by
    have hf : Measurable (Set.indicator {p : Chart | a0 < p.1} G) :=
      hG.indicator (measurableSet_lt measurable_const measurable_fst)
    have h := NearInst.CoeffMult.lintegral_ageμ_succ' hc (-5 / 2) hf
    rw [show (-5 / 2 : ℝ) + 1 = -3 / 2 by norm_num] at h
    rw [lintegral_indicator (measurableSet_lt measurable_const measurable_fst)] at h
    rw [h]
    refine lintegral_congr fun p => ?_
    simp only [sourceFun, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs <;> simp
  -- the main chain
  calc ∫⁻ a : ℝ × Space, Set.indicator {a : ℝ × Space | a0 < age R a.2}
        (fun a => srcW R c G a.1 a.2) a *
        ENNReal.ofReal (Real.sqrt (omega2 (2 * c / R) a.1))
      = ∫⁻ σ, ENNReal.ofReal (Real.sqrt (omega2 (2 * c / R) σ)) * ∫⁻ z,
          Set.indicator {a : ℝ × Space | a0 < age R a.2}
            (fun a => srcW R c G a.1 a.2) (σ, z) := by
        rw [Measure.volume_eq_prod, lintegral_prod _ hfull.aemeasurable]
        refine lintegral_congr fun σ => ?_
        dsimp only
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
    _ ≤ ENNReal.ofReal (Real.sqrt (2 * c / R) + 1 / Real.sqrt (2 * c / R)) * ∫⁻ σ in Ioc 0 (2 * c / R),
          ∫⁻ z, Set.indicator {a : ℝ × Space | a0 < age R a.2}
            (fun a => srcW R c G a.1 a.2) (σ, z) :=
        phaseFold (2 * c / R) hP _ hHmeas hHper
    _ = ENNReal.ofReal (Real.sqrt (2 * c / R) + 1 / Real.sqrt (2 * c / R)) *
          ∫⁻ τ in Ioc 0 (2 * c / R), ∫⁻ z, sourceFun G a0 (NearInst.chartOf R c z τ) := by
        exact congrArg _ (lintegral_congr fun σ => hHF σ)
    _ = ENNReal.ofReal (Real.sqrt (2 * c / R) + 1 / Real.sqrt (2 * c / R)) *
          (ENNReal.ofReal (2 * c / R) * ENNReal.ofReal (Real.pi * R ^ 2) *
            ∫⁻ p, sourceFun G a0 p ∂(ageμ c (-5 / 2))) := by
        rw [chartPhaseLIntegral R c hR hc _ hFm]
    _ = ENNReal.ofReal (Real.sqrt (2 * c / R) + 1 / Real.sqrt (2 * c / R)) *
          ENNReal.ofReal (2 * c / R * (Real.pi * R ^ 2)) *
          ∫⁻ p in {p : Chart | a0 < p.1}, G p ∂(ageμ c (-3 / 2)) := by
        rw [hkey, ENNReal.ofReal_mul hP.le]
        ring

/-- **Source mass** (source 5571-5575 for `N₀`, 2679-2684 for the change of variables): the atom
weights of age `> a₀`, folded over periods, carry `(√P + 1/√P) · PπR² · N₀(a₀)`. -/
theorem sourceMass : SourceMass := by
  intro R c hR hc g hg a0
  exact sourceMass_of_G R c hR hc (fun p => ‖g p‖ₑ) hg.enorm a0

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore

end
