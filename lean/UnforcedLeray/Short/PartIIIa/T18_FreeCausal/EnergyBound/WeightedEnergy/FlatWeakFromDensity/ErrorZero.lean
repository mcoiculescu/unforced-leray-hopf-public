import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.FlatWeakFromDensity.ErrorInt
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.FlatWeakFromDensity.Spatial
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.FlatWeakFromDensity.Pointwise

/-!
# Part III-a, helper of `PartIII-a:T18/3/1/2`: the error term integrates to zero

Fubini on `(0,∞) × cell`: at each time `s > 0` the cell integral of the error term vanishes by the
weak gradient identity (`cell_integral_Q_zero`). Combined with the decomposition
`extWeak = flat + errTerm` this gives the extended tested identity for every spatial flat test
`φ`, i.e. `ExtWeakH1` for spatial flat tests.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

lemma errTerm_integral_zero {c ν : ℝ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {ψ : ℝ → ℝ} {φ : ℝ × ℝ → Fin 2 → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hts : tsupport ψ ⊆ Ioi 0)
    (hφ : IsFlatSpatialTest c φ)
    (hb : ∀ i, Measurable fun p => b p i) (hG : ∀ i j, Measurable fun p => G p i j)
    (hE : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) < ⊤)
    (hw : ∀ s, 0 < s → ∀ i j, HasWeakCellDerivC c j (fun x => b (s, x) i) (fun x => G (s, x) i j)) :
    ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, errTerm ν b G ψ φ p = 0 := by
  have hint := errTerm_integrableOn (ν := ν) hψ hψc hts hφ hb hG hE
  have hμ : (volume : Measure (ℝ × (ℝ × ℝ))).restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)
      = (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (B0579.cell c)) := by
    rw [Measure.prod_restrict]
    try rfl
  have hint2 : Integrable (errTerm ν b G ψ φ)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (B0579.cell c))) := by
    rw [← hμ]
    exact hint
  rw [hμ, integral_prod _ hint2]
  have hinner : ∀ s : ℝ, 0 < s →
      ∫ y in B0579.cell c, errTerm ν b G ψ φ (s, y) = 0 := by
    intro s hs
    have hfac : ∀ y : ℝ × ℝ, errTerm ν b G ψ φ (s, y) = ((ν : ℂ) * (ψ s : ℂ)) *
        ∑ i : Fin 2, (b (s, y) i * (lapP (fun z => φ z i) y : ℂ) +
          ∑ j : Fin 2, G (s, y) i j * (B0579.pd j (fun z => φ z i) y : ℂ)) := by
      intro y
      simp only [errTerm]
    simp only [hfac]
    rw [integral_const_mul, cell_integral_Q_zero (hw s hs) hφ, mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s (hs : s ∈ Ioi (0 : ℝ)) => hinner s hs)]
  simp

/-- The extended tested identity for a spatial flat test `φ` (no density needed). -/
lemma spatial_extWeak {c ν : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hdat : FreeSolData c ν μ F b G) {ψ : ℝ → ℝ} {φ : ℝ × ℝ → Fin 2 → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hts : tsupport ψ ⊆ Ioi 0)
    (hφ : IsFlatSpatialTest c φ) :
    IntegrableOn (extWeakIntegrand ν μ F b G ψ φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, extWeakIntegrand ν μ F b G ψ φ p = 0 := by
  have hΦ := isFlatTest_mul_spatial (c := c) hψ hψc hts hφ
  have hF := hdat.sol.integrable _ hΦ
  have hW := hdat.sol.weak _ hΦ
  have hE := errTerm_integrableOn (ν := ν) hψ hψc hts hφ hdat.sol.measurable hdat.sol.gradMeasurable
    hdat.sol.energyLoc
  have hZ := errTerm_integral_zero (ν := ν) hψ hψc hts hφ hdat.sol.measurable hdat.sol.gradMeasurable
    hdat.sol.energyLoc hdat.sol.weakGrad
  have hfun : extWeakIntegrand ν μ F b G ψ φ = fun p =>
      flatIntegrand ν μ (fun _ _ _ => 0) F b (fun s x i => ψ s * φ x i) p + errTerm ν b G ψ φ p :=
    funext fun p => extWeak_eq_flat_add c ν μ F b G ψ φ hφ p
  rw [hfun]
  exact ⟨hF.add hE, by rw [integral_add hF hE, hW, hZ, add_zero]⟩

end UnforcedLeray.Short.IIIa
