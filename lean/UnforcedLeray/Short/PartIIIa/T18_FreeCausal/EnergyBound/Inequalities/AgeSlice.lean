import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities.SliceLoc

/-!
# Part III-a, task `PartIII-a:T18/3/2/5` (ageSlice): age measure as slice integrals

Source: `the November 2 reference manuscript` lines 3541-3552.
For `c > 0` and a measurable `g ≥ 0` with finite `∫⁻` over every `[s₁,s₂] × cell c` (`0 < s₁`),
`∫ g dageμ c a = c⁻¹ ∫_{(0,∞)} s^a ∫_cell g`, and the same restricted to `s ∈ (0,δ)`.
Proof: `Axi.lintegral_ageμ` (weight `c⁻¹ s^a`), Tonelli on the product (`lintegral_restrict_prod_eq`,
from `SliceLoc.lean`), and `SliceLoc` for a.e. slice integrability.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem qCell_eq_B0579_cell (c : ℝ) : qCell c = B0579.cell c := by
  unfold qCell B0579.cell
  rw [neg_div]

/-- Restricted age slice formula on an age set `I ⊆ (0,∞)`. -/
theorem ageSlice_aux {c a : ℝ} (g : ℝ × (ℝ × ℝ) → ℝ) (hc : 0 < c) (hg : Measurable g)
    (hg0 : ∀ p, 0 ≤ g p)
    (hfin : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (g p) < ⊤)
    (I : Set ℝ) (hI : MeasurableSet I) (hI0 : I ⊆ Ioi 0) :
    ∫⁻ p in I ×ˢ (univ : Set (ℝ × ℝ)), ENNReal.ofReal (g p) ∂(ageμ c a) =
      ENNReal.ofReal c⁻¹ * ∫⁻ s in I, ENNReal.ofReal (s ^ a * sliceSq c g s) := by
  have hF : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (g p) := hg.ennreal_ofReal
  have hS : MeasurableSet (I ×ˢ (univ : Set (ℝ × ℝ))) := hI.prod MeasurableSet.univ
  rw [← lintegral_indicator hS (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (g p))]
  have hW : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (c⁻¹ * p.1 ^ a) :=
    ENNReal.measurable_ofReal.comp ((measurable_fst.pow_const a).const_mul c⁻¹)
  rw [lintegral_ageμ hc a (hF.indicator hS)]
  rw [lintegral_restrict_prod_eq (Ioi 0) (qCell c)
    (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (c⁻¹ * p.1 ^ a) *
      (I ×ˢ (univ : Set (ℝ × ℝ))).indicator (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (g p)) p)
    (hW.mul (hF.indicator hS))]
  have hstep : ∀ s : ℝ, ∫⁻ x in qCell c,
      ENNReal.ofReal (c⁻¹ * s ^ a) *
        (I ×ˢ (univ : Set (ℝ × ℝ))).indicator (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (g p)) (s, x) =
      I.indicator (fun s : ℝ => ENNReal.ofReal (c⁻¹ * s ^ a) *
        ∫⁻ x in B0579.cell c, ENNReal.ofReal (g (s, x))) s := by
    intro s
    by_cases hs : s ∈ I
    · have hpt : ∀ x : ℝ × ℝ, (I ×ˢ (univ : Set (ℝ × ℝ))).indicator
          (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (g p)) (s, x) = ENNReal.ofReal (g (s, x)) := by
        intro x
        rw [indicator_of_mem (mk_mem_prod hs (mem_univ x))]
      simp only [hpt]
      rw [Set.indicator_of_mem hs, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        qCell_eq_B0579_cell]
    · have hpt : ∀ x : ℝ × ℝ, (I ×ˢ (univ : Set (ℝ × ℝ))).indicator
          (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (g p)) (s, x) = 0 := by
        intro x
        rw [indicator_of_notMem (fun h => hs h.1)]
      simp only [hpt, mul_zero, lintegral_zero, Set.indicator_of_notMem hs]
  refine (lintegral_congr fun s => hstep s).trans ?_
  rw [lintegral_indicator hI, Measure.restrict_restrict hI, inter_eq_left.2 hI0,
    ← lintegral_const_mul' (ENNReal.ofReal c⁻¹) _ ENNReal.ofReal_ne_top]
  have hslice := (sliceLoc c g hc hg hg0 hfin).2.2
  have hae : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ENNReal.ofReal (c⁻¹ * s ^ a) * ∫⁻ x in B0579.cell c, ENNReal.ofReal (g (s, x)) =
        ENNReal.ofReal c⁻¹ * ENNReal.ofReal (s ^ a * sliceSq c g s) := by
    filter_upwards [hslice, ae_restrict_mem measurableSet_Ioi] with s hs hs0
    have hs0' : 0 < s := hs0
    have h1 : ENNReal.ofReal (c⁻¹ * s ^ a) = ENNReal.ofReal c⁻¹ * ENNReal.ofReal (s ^ a) :=
      ENNReal.ofReal_mul (inv_nonneg.2 hc.le)
    have h2 : ENNReal.ofReal (s ^ a * sliceSq c g s) =
        ENNReal.ofReal (s ^ a) * ENNReal.ofReal (sliceSq c g s) :=
      ENNReal.ofReal_mul (Real.rpow_nonneg hs0'.le a)
    have h3 : ∫⁻ x in B0579.cell c, ENNReal.ofReal (g (s, x)) =
        ENNReal.ofReal (sliceSq c g s) :=
      (ofReal_integral_eq_lintegral_ofReal hs (Eventually.of_forall fun x => hg0 (s, x))).symm
    rw [h1, h2, h3, mul_assoc]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hI0 hae] with s hs
  exact hs

theorem ageSlice : UnforcedLeray.Short.IIIa.AgeSlice := by
  intro c a g hc hg hg0 hfin
  refine ⟨?_, ?_⟩
  · have hres : (ageμ c a).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) = ageμ c a := by
      apply Measure.restrict_eq_self_of_ae_mem
      filter_upwards [ae_ageμ_mem hc a] with p hp
      exact ⟨hp.1, mem_univ _⟩
    have h := ageSlice_aux (a := a) g hc hg hg0 hfin (Ioi 0) measurableSet_Ioi (subset_refl _)
    rw [← hres]
    exact h
  · intro δ
    exact ageSlice_aux (a := a) g hc hg hg0 hfin (Ioo 0 δ) measurableSet_Ioo (fun s hs => hs.1)

end UnforcedLeray.Short.IIIa
