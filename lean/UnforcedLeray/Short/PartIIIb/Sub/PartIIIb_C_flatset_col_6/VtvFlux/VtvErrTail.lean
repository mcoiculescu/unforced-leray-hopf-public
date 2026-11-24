import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFluxLemmas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFubini
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvErrFlat
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvErrBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvIntegrandLe
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvBandCS
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvEnergyBand
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE.FlatIntegrandBound
import UnforcedLeray.Short.PartI.TrainClass

/-!
# Part III-b, task `PartIII-b:C/flatset/col/6/5/17`: the flux remainder is negligible

Target (`VtvFluxLemmas.lean`): `VtvErrTail`. Source of record:
`the November 2 reference manuscript`, lines 3511-3514 and 3426-3440.

For `R ≥ 1`, `E_R = vtvErr Φ R₀ R` is a flat test supported in `[s₁,s₂] × {|η| ≤ 2R}`, so the
tested integral over `Ioi 0 × cell` is the integral over the slab `fibK1 c s₁ s₂ (2R)`.  On the
slab the pointwise bound `VtvIntegrandLe` with `δ = K/R` gives `‖integrand‖ ≤ (K/R) A ∑_i(|b_i|+|f_i|)`,
and the Cauchy-Schwarz slab bound `VtvBandCS` gives `∫ ∑_i(|b_i|+|f_i|) ≤ C₀ √R`.  Hence the
integral is at most `K A C₀ / √R → 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsFlatTest trainVel fibK1 fibK1_mem fibK1_measurable fibK1_subset_cell fib_outside)

/-- Target: `VtvErrTail`. -/
theorem vtvErrTail : VtvErrTail := by
  intro ν c μ tr ω g b G f H Φ s₁ s₂ R₀ hS
  have hs1 : 0 < s₁ := hS.2.1
  obtain ⟨-, -, hBUC, hE, -, hf, -, -, -⟩ := H
  obtain ⟨K, hK⟩ := vtvErrBound c Φ s₁ s₂ R₀ hS
  -- the train velocity is bounded on the age band
  obtain ⟨V, hV0, hvel⟩ : ∃ V : ℝ, 0 ≤ V ∧ ∀ p : ℝ × (ℝ × ℝ), s₁ ≤ p.1 → p.1 ≤ s₂ →
      ∀ i, |trainVel tr p.1 p.2 i| ≤ V := by
    obtain ⟨M, hM⟩ := UnforcedLeray.Short.PartI.IsBUCTrain.sup_bound hBUC (le_max_right s₂ 0)
    refine ⟨max M 0, le_max_right _ _, fun p hp1 hp2 i => ?_⟩
    have h0 : 0 ≤ p.1 := hs1.le.trans hp1
    have htv : trainVel tr p.1 p.2 i = tr.v p.1 p.2 i := by
      simp [trainVel, h0]
    rw [htv, ← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le _ i).trans
      (((hM p.1 ⟨h0, hp2.trans (le_max_left _ _)⟩ p.2)).trans (le_max_left _ _))
  -- Cauchy-Schwarz constants on the slabs
  have hbB : ∀ i, ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → IntegrableOn (fun p => ‖b p i‖)
      (fibK1 c s₁ s₂ (2 * R)) ∧ ∫ p in fibK1 c s₁ s₂ (2 * R), ‖b p i‖ ≤ C * Real.sqrt R :=
    fun i => vtvBandCS c s₁ s₂ (fun p => b p i) (vtvEnergyBand c b G hE s₁ s₂ hs1 i)
  have hfB : ∀ i, ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → IntegrableOn (fun p => ‖f p i‖)
      (fibK1 c s₁ s₂ (2 * R)) ∧ ∫ p in fibK1 c s₁ s₂ (2 * R), ‖f p i‖ ≤ C * Real.sqrt R :=
    fun i => vtvBandCS c s₁ s₂ (fun p => f p i) (hf s₁ s₂ hs1 i)
  choose Cb hCb using hbB
  choose Cf hCf using hfB
  have hA : ∀ (R : ℝ), 0 ≤ 1 + ‖(μ : ℂ)‖ / s₁ + |ν| + 4 * V := fun _ => by
    have h1 : 0 ≤ ‖(μ : ℂ)‖ / s₁ := div_nonneg (norm_nonneg _) hs1.le
    have h2 := abs_nonneg ν
    linarith
  -- the bound at each large `R`
  have hbound : ∀ R : ℝ, 1 ≤ R →
      ‖∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          forcedIntegrand ν (μ : ℂ) (trainVel tr) f b (vtvErr Φ R₀ R) p‖
        ≤ K * (1 + ‖(μ : ℂ)‖ / s₁ + |ν| + 4 * V) * (∑ i : Fin 2, (Cb i + Cf i)) *
          (Real.sqrt R)⁻¹ := by
    intro R hR1
    have hR0 : 0 < R := by linarith
    have hsq : 0 < Real.sqrt R := Real.sqrt_pos.2 hR0
    obtain ⟨hEF, hEs⟩ := vtvErrFlat c Φ s₁ s₂ R₀ hS R hR0
    -- the integrand vanishes off the slab
    have hzero : ∀ p ∈ Ioi (0 : ℝ) ×ˢ B0579.cell c \ fibK1 c s₁ s₂ (2 * R),
        forcedIntegrand ν (μ : ℂ) (trainVel tr) f b (vtvErr Φ R₀ R) p = 0 := fun p hp =>
      vtv_zero_outside hEF hEs ν (μ : ℂ) (trainVel tr) f b p (fib_outside hp.1 hp.2)
    have hmeasT : MeasurableSet (Ioi (0 : ℝ) ×ˢ B0579.cell c) :=
      MeasurableSet.prod measurableSet_Ioi
        (MeasurableSet.prod measurableSet_Ico MeasurableSet.univ)
    have hsl : ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          forcedIntegrand ν (μ : ℂ) (trainVel tr) f b (vtvErr Φ R₀ R) p =
        ∫ p in fibK1 c s₁ s₂ (2 * R), forcedIntegrand ν (μ : ℂ) (trainVel tr) f b (vtvErr Φ R₀ R) p :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeasT (fibK1_subset_cell hs1) hzero
    -- pointwise bound on the slab
    have hpt : ∀ p ∈ fibK1 c s₁ s₂ (2 * R),
        ‖forcedIntegrand ν (μ : ℂ) (trainVel tr) f b (vtvErr Φ R₀ R) p‖ ≤
          (K / R) * (1 + ‖(μ : ℂ)‖ / s₁ + |ν| + 4 * V) *
            ∑ i : Fin 2, (‖b p i‖ + ‖f p i‖) := by
      intro p hp
      obtain ⟨⟨h1, h2⟩, -, -⟩ := fibK1_mem.1 hp
      exact vtvIntegrandLe ν (μ : ℂ) (trainVel tr) f b (vtvErr Φ R₀ R) p s₁ (K / R) V hs1 h1
        (fun i => hK R hR1 p.1 p.2 i) (fun i => hvel p h1 h2 i)
    have hKR : 0 ≤ K / R := le_trans (abs_nonneg _) (hK R hR1 0 (0, 0) 0).1
    have hSm : MeasurableSet (fibK1 c s₁ s₂ (2 * R)) := fibK1_measurable c s₁ s₂ (2 * R)
    have hTi : ∀ i, IntegrableOn (fun p => ‖b p i‖ + ‖f p i‖) (fibK1 c s₁ s₂ (2 * R)) :=
      fun i => (hCb i R hR1).1.add (hCf i R hR1).1
    have hTint : IntegrableOn (fun p => ∑ i : Fin 2, (‖b p i‖ + ‖f p i‖))
        (fibK1 c s₁ s₂ (2 * R)) :=
      integrable_finsetSum _ fun i _ => hTi i
    have hTle : ∫ p in fibK1 c s₁ s₂ (2 * R), ∑ i : Fin 2, (‖b p i‖ + ‖f p i‖) ≤
        (∑ i : Fin 2, (Cb i + Cf i)) * Real.sqrt R := by
      rw [integral_finsetSum _ fun i _ => hTi i, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [integral_add (hCb i R hR1).1 (hCf i R hR1).1, add_mul]
      linarith [(hCb i R hR1).2, (hCf i R hR1).2]
    have hint := norm_integral_le_of_norm_le (hTint.const_mul
        ((K / R) * (1 + ‖(μ : ℂ)‖ / s₁ + |ν| + 4 * V)))
      (ae_restrict_of_forall_mem hSm (fun p hp => hpt p hp))
    rw [hsl]
    refine hint.trans ?_
    rw [integral_const_mul]
    have hcoef : 0 ≤ (K / R) * (1 + ‖(μ : ℂ)‖ / s₁ + |ν| + 4 * V) :=
      mul_nonneg hKR (hA R)
    calc (K / R) * (1 + ‖(μ : ℂ)‖ / s₁ + |ν| + 4 * V) *
            ∫ p in fibK1 c s₁ s₂ (2 * R), ∑ i : Fin 2, (‖b p i‖ + ‖f p i‖)
        ≤ (K / R) * (1 + ‖(μ : ℂ)‖ / s₁ + |ν| + 4 * V) *
            ((∑ i : Fin 2, (Cb i + Cf i)) * Real.sqrt R) :=
          mul_le_mul_of_nonneg_left hTle hcoef
      _ = K * (1 + ‖(μ : ℂ)‖ / s₁ + |ν| + 4 * V) * (∑ i : Fin 2, (Cb i + Cf i)) *
            (Real.sqrt R)⁻¹ := by
          have hs : Real.sqrt R * Real.sqrt R = R := Real.mul_self_sqrt hR0.le
          have hs0 : Real.sqrt R ≠ 0 := hsq.ne'
          generalize Real.sqrt R = s at hs hs0 ⊢
          rw [← hs]
          field_simp
  -- squeeze
  have hlim : Tendsto (fun R : ℝ => K * (1 + ‖(μ : ℂ)‖ / s₁ + |ν| + 4 * V) *
      (∑ i : Fin 2, (Cb i + Cf i)) * (Real.sqrt R)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => (Real.sqrt R)⁻¹) atTop (𝓝 0) :=
      Real.tendsto_sqrt_atTop.inv_tendsto_atTop
    have h2 := h1.const_mul (K * (1 + ‖(μ : ℂ)‖ / s₁ + |ν| + 4 * V) *
      (∑ i : Fin 2, (Cb i + Cf i)))
    rw [mul_zero] at h2
    exact h2
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR1
  exact hbound R hR1

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
