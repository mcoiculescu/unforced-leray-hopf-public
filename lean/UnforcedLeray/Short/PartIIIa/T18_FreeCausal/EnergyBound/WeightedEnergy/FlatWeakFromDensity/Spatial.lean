import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.FlatWeakFromDensity.Basic

/-!
# Part III-a, helper of `PartIII-a:T18/3/1/2`: the weak gradient at a fixed time

At a fixed time `s > 0` the weak gradient identity `HasWeakCellDerivC` tested with the cylinder
tests `∂ⱼφᵢ` gives `∫_cell (bᵢ Δφᵢ + ∑ⱼ Gᵢⱼ ∂ⱼφᵢ) = 0` (integrability included).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

lemma cell_slice_integrable_zero {c : ℝ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {s : ℝ}
    (hw : ∀ i j, HasWeakCellDerivC c j (fun x => b (s, x) i) (fun x => G (s, x) i j))
    {φ : ℝ × ℝ → Fin 2 → ℝ} (hφ : IsFlatSpatialTest c φ) (i : Fin 2) :
    IntegrableOn (fun x => b (s, x) i * (lapP (fun y => φ y i) x : ℂ) +
        ∑ j : Fin 2, G (s, x) i j * (B0579.pd j (fun y => φ y i) x : ℂ)) (B0579.cell c) ∧
    ∫ x in B0579.cell c, (b (s, x) i * (lapP (fun y => φ y i) x : ℂ) +
        ∑ j : Fin 2, G (s, x) i j * (B0579.pd j (fun y => φ y i) x : ℂ)) = 0 := by
  have hc := isCylTest_component hφ i
  have hpt : ∀ x : ℝ × ℝ, b (s, x) i * (lapP (fun y => φ y i) x : ℂ) +
      ∑ j : Fin 2, G (s, x) i j * (B0579.pd j (fun y => φ y i) x : ℂ) =
      ∑ j : Fin 2, (b (s, x) i * (B0579.pd j (B0579.pd j (fun y => φ y i)) x : ℂ) +
        G (s, x) i j * (B0579.pd j (fun y => φ y i) x : ℂ)) := by
    intro x
    simp only [lapP, Fin.sum_univ_two, Complex.ofReal_add, mul_add]
    ring
  have hI : ∀ j : Fin 2,
      IntegrableOn (fun x => b (s, x) i * (B0579.pd j (B0579.pd j (fun y => φ y i)) x : ℂ) +
        G (s, x) i j * (B0579.pd j (fun y => φ y i) x : ℂ)) (B0579.cell c) := by
    intro j
    exact ((hw i j).1 _ (hc.pd j)).1.add ((hw i j).1 _ (hc.pd j)).2
  have hA : ∀ j : Fin 2,
      ∫ x in B0579.cell c, b (s, x) i * (B0579.pd j (B0579.pd j (fun y => φ y i)) x : ℂ) =
        -∫ x in B0579.cell c, G (s, x) i j * (B0579.pd j (fun y => φ y i) x : ℂ) :=
    fun j => (hw i j).2 _ (hc.pd j)
  have hfun : (fun x : ℝ × ℝ => b (s, x) i * (lapP (fun y => φ y i) x : ℂ) +
        ∑ j : Fin 2, G (s, x) i j * (B0579.pd j (fun y => φ y i) x : ℂ)) =
      fun x => ∑ j : Fin 2, (b (s, x) i * (B0579.pd j (B0579.pd j (fun y => φ y i)) x : ℂ) +
        G (s, x) i j * (B0579.pd j (fun y => φ y i) x : ℂ)) := funext hpt
  rw [hfun]
  refine ⟨integrable_finsetSum _ (fun j _ => hI j), ?_⟩
  rw [integral_finsetSum _ (fun j _ => hI j)]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_add ((hw i j).1 _ (hc.pd j)).1 ((hw i j).1 _ (hc.pd j)).2, hA j]
  ring

lemma cell_integral_Q_zero {c : ℝ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {s : ℝ}
    (hw : ∀ i j, HasWeakCellDerivC c j (fun x => b (s, x) i) (fun x => G (s, x) i j))
    {φ : ℝ × ℝ → Fin 2 → ℝ} (hφ : IsFlatSpatialTest c φ) :
    ∫ x in B0579.cell c, ∑ i : Fin 2, (b (s, x) i * (lapP (fun y => φ y i) x : ℂ) +
        ∑ j : Fin 2, G (s, x) i j * (B0579.pd j (fun y => φ y i) x : ℂ)) = 0 := by
  rw [integral_finsetSum _ (fun i _ => (cell_slice_integrable_zero hw hφ i).1)]
  exact Finset.sum_eq_zero fun i _ => (cell_slice_integrable_zero hw hφ i).2

end UnforcedLeray.Short.IIIa
