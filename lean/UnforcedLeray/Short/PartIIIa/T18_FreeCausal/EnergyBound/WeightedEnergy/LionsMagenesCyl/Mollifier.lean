import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.Mollifier.Targets
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.Mollifier.DivFree
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.Mollifier.Limit
import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2_2.LmJH1

/-!
# Part III-a, `PartIII-a:T18/3/1/3/1`: the mollifier family `HasLMMollifier`

Source of record: `the November 2 reference manuscript` lines 3427-3440 (the energy
class on the cylinder `C_c = (ℝ/cℤ) × ℝ`, `∇b ∈ L²_loc((0,∞); L²)`) and 3541-3552 (the energy
identity, whose proof mollifies `b(s)` on the cylinder). The periodic convolution `lmJ c k` of
`Mollifier/Defs.lean` satisfies every clause of `IsLMMollifier`:

* `smooth`, `periodic`, `add`, `smul`: `lmJs_contDiff`, `lmJ_periodic`, `lmJs_integrable`, `lmJ_smul`;
* `selfAdj`, `contr`, `memL2`: `lmJ_selfAdj`, `lmJ_contr`, `lmJs_memLp` (Jensen, Fubini, evenness);
* `commute`, `divFree`: `lmJs_commute`, `lmJ_divFree` (the derivative falls on the kernel);
* `tendsto`: `lmJ_tendsto` (a.e. convergence by Lebesgue differentiation, Fatou);
* `measurable`: `lmJ_measurable`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIIa

theorem lmJ_measurable (c : ℝ) (k : ℕ) (f : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (hf : ∀ i : Fin 2, Measurable fun p => f p i) (i : Fin 2) :
    Measurable fun p : ℝ × (ℝ × ℝ) => lmJ c k (fun y => f (p.1, y)) p.2 i := by
  have h : StronglyMeasurable (Function.uncurry fun (p : ℝ × (ℝ × ℝ)) (y : ℝ × ℝ) =>
      (lmK c k (p.2 - y) : ℂ) * f (p.1, y) i) := by
    apply Measurable.stronglyMeasurable
    refine (Complex.measurable_ofReal.comp ((measurable_lmK c k).comp ?_)).mul ((hf i).comp ?_)
    · exact (measurable_snd.comp measurable_fst).sub measurable_snd
    · exact (measurable_fst.comp measurable_fst).prodMk measurable_snd
  exact (h.integral_prod_right (ν := volume.restrict (B0579.cell c))).measurable

theorem lmJ_selfAdj {c : ℝ} (hc : 0 < c) (k : ℕ) (f g : LMSpField) (hf : LMCellL2 c f)
    (hg : LMCellL2 c g) :
    ∫ x in B0579.cell c, ∑ i : Fin 2, starRingEnd ℂ (lmJ c k f x i) * g x i =
      ∫ x in B0579.cell c, ∑ i : Fin 2, starRingEnd ℂ (f x i) * lmJ c k g x i := by
  have hint1 : ∀ i : Fin 2, Integrable (fun x => starRingEnd ℂ (lmJ c k f x i) * g x i)
      (volume.restrict (B0579.cell c)) := fun i =>
    ((lmJs_memLp hc k (hf i)).star).integrable_mul (hg i)
  have hint2 : ∀ i : Fin 2, Integrable (fun x => starRingEnd ℂ (f x i) * lmJ c k g x i)
      (volume.restrict (B0579.cell c)) := fun i =>
    ((hf i).star).integrable_mul (lmJs_memLp hc k (hg i))
  rw [integral_finsetSum _ (fun i _ => hint1 i), integral_finsetSum _ (fun i _ => hint2 i)]
  exact Finset.sum_congr rfl fun i _ => lmJs_selfAdj hc k (hf i) (hg i)

theorem lmJ_contr {c : ℝ} (hc : 0 < c) (k : ℕ) (f : LMSpField) (hf : LMCellL2 c f) :
    ∫ x in B0579.cell c, ∑ i : Fin 2, ‖lmJ c k f x i‖ ^ 2 ≤
      ∫ x in B0579.cell c, ∑ i : Fin 2, ‖f x i‖ ^ 2 := by
  have hint1 : ∀ i : Fin 2, Integrable (fun x => ‖lmJ c k f x i‖ ^ 2)
      (volume.restrict (B0579.cell c)) := fun i => lm_integrable_sq (lmJs_memLp hc k (hf i))
  have hint2 : ∀ i : Fin 2, Integrable (fun x => ‖f x i‖ ^ 2)
      (volume.restrict (B0579.cell c)) := fun i => lm_integrable_sq (hf i)
  rw [integral_finsetSum _ (fun i _ => hint1 i), integral_finsetSum _ (fun i _ => hint2 i)]
  exact Finset.sum_le_sum fun i _ => lmJs_contr hc k (hf i)

theorem lmJ_tendsto {c : ℝ} (hc : 0 < c) (f : LMSpField) (hf : LMCellL2 c f) :
    Tendsto (fun k : ℕ => ∫ x in B0579.cell c, ∑ i : Fin 2, ‖lmJ c k f x i - f x i‖ ^ 2) atTop
      (𝓝 0) := by
  have hint : ∀ (k : ℕ) (i : Fin 2), Integrable (fun x => ‖lmJ c k f x i - f x i‖ ^ 2)
      (volume.restrict (B0579.cell c)) := fun k i =>
    lm_integrable_sq ((lmJs_memLp hc k (hf i)).sub (hf i))
  have heq : ∀ k : ℕ, ∫ x in B0579.cell c, ∑ i : Fin 2, ‖lmJ c k f x i - f x i‖ ^ 2 =
      ∑ i : Fin 2, ∫ x in B0579.cell c, ‖lmJ c k f x i - f x i‖ ^ 2 := fun k =>
    integral_finsetSum _ (fun i _ => hint k i)
  simp only [heq]
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin 2)) fun i _ => lmJs_tendsto hc (hf i)
  simpa [lmJ_apply] using h

/-- **The mollifier family exists** (part (a) of the split of `LionsMagenesCyl`,
`Sub/T18_3_1_3.lean`). -/
theorem hasLMMollifier : HasLMMollifier :=
  hasLMMollifier_of @lmJs_integrable @lmJs_contDiff @lmJs_commute @lmJ_divFree @lmJs_memLp
    lmJ_measurable @lmJ_selfAdj @lmJ_contr @lmJ_tendsto
    (fun hc k => lmJ_gradL2 hc k) (fun hc k f hf hd => lmJ_divFreeWeak hc k f hf hd)

end UnforcedLeray.Short.IIIa
