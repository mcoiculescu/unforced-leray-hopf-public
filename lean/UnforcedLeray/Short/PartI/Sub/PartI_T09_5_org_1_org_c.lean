import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1.FiniteEnergy
import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1_org_c.JetSum

/-!
# `PartI:T09/5/org/1/org/c`: decomposition of `TrainFiniteEnergyClass`

Source: `the November 2 reference manuscript`,
lines 270-288.  The cell is unbounded in `eta`, so `L^2` convergence at age `0` is obtained from
pointwise convergence plus convergence of the norms (Scheffe/Riesz): the norm statement is the
energy inequality of lines 281-288, the pointwise statement is smoothness of `v` on `[0,inf) x R^2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- **Source fact (line 270-288, `smooth_v`):** each word derivative of `v(s)` is continuous in
`z` for `s >= 0` and converges pointwise as `s -> 0+`. -/
def TrainJetPointwiseAt0 : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    ∀ (w : List Bool) (k : Fin 2),
      (∀ s : ℝ, 0 ≤ s → Continuous (wordComp w (tr.v s) k)) ∧
      ∀ z : Plane, Tendsto (fun s : ℝ => wordComp w (tr.v s) k z)
        (nhdsWithin (0 : ℝ) (Ici 0)) (𝓝 (wordComp w (tr.v 0) k z))

/-- **Source fact (lines 270-278, 294):** the initial datum `v 0 = Vc 0` has Gaussian decay, so
all its word derivatives are square integrable on the cell. -/
def TrainDatumJetL2Finite : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    ∀ (w : List Bool) (k : Fin 2),
      ∫⁻ z in UnforcedLeray.Cyl.cell c, ENNReal.ofReal ((wordComp w (tr.v 0) k z) ^ 2) < ⊤

/-- **Generic Scheffe lemma in `L^2`:** pointwise convergence of continuous functions along
`s -> 0+`, square-integrable limit, and `limsup` of the squared norms at most that of the limit,
give convergence in `L^2(A)`. -/
def ScheffeL2At0 : Prop :=
  ∀ (A : Set Plane) (F : ℝ → Plane → ℝ),
    MeasurableSet A → (∀ s : ℝ, 0 ≤ s → Continuous (F s)) →
    (∀ z : Plane, Tendsto (fun s : ℝ => F s z) (nhdsWithin (0 : ℝ) (Ici 0)) (𝓝 (F 0 z))) →
    ∫⁻ z in A, ENNReal.ofReal ((F 0 z) ^ 2) < ⊤ →
    limsup (fun s : ℝ => ∫⁻ z in A, ENNReal.ofReal ((F s z) ^ 2)) (nhdsWithin (0 : ℝ) (Ici 0)) ≤
      ∫⁻ z in A, ENNReal.ofReal ((F 0 z) ^ 2) →
    Tendsto (fun s : ℝ => ∫⁻ z in A, ENNReal.ofReal ((F s z - F 0 z) ^ 2))
      (nhdsWithin (0 : ℝ) (Ici 0)) (𝓝 0)

/-- `TrainFiniteEnergyClass` from the summed jet energy inequality (`TrainJetSumLimsup`,
`PartI_T09_5_org_1_org_c/JetSum.lean`), pointwise convergence, the datum, and the vector Scheffe
lemma applied to the family `(w, k)`, `|w| ≤ |w₀|`. -/
theorem trainFiniteEnergyClass_of (h1 : TrainJetSumLimsup) (h2 : TrainJetPointwiseAt0)
    (h3 : TrainDatumJetL2Finite) (h4 : ScheffeL2FamilyAt0) : TrainFiniteEnergyClass := by
  intro ν c hν hc tr htr
  refine ⟨fun w k => ?_⟩
  have hI : (w, k) ∈ (wordsUpTo w.length) ×ˢ (Finset.univ : Finset (Fin 2)) :=
    Finset.mem_product.2 ⟨mem_wordsUpTo.2 le_rfl, Finset.mem_univ k⟩
  have hlim : limsup (fun s : ℝ => ∫⁻ z in UnforcedLeray.Cyl.cell c, ENNReal.ofReal
        (∑ x ∈ (wordsUpTo w.length) ×ˢ (Finset.univ : Finset (Fin 2)),
          (wordComp x.1 (tr.v s) x.2 z) ^ 2)) (nhdsWithin (0 : ℝ) (Ici 0)) ≤
      ∫⁻ z in UnforcedLeray.Cyl.cell c, ENNReal.ofReal
        (∑ x ∈ (wordsUpTo w.length) ×ˢ (Finset.univ : Finset (Fin 2)),
          (wordComp x.1 (tr.v 0) x.2 z) ^ 2) := by
    simp only [Finset.sum_product]
    exact h1 ν c hν hc tr htr w.length
  exact h4 (List Bool × Fin 2) ((wordsUpTo w.length) ×ˢ (Finset.univ : Finset (Fin 2)))
    (UnforcedLeray.Cyl.cell c) (fun x s => wordComp x.1 (tr.v s) x.2)
    (measurableSet_Ico.prod MeasurableSet.univ)
    (fun x _ s hs => (h2 ν c hν hc tr htr x.1 x.2).1 s hs)
    (fun x _ z => (h2 ν c hν hc tr htr x.1 x.2).2 z)
    (fun x _ => h3 ν c hν hc tr htr x.1 x.2) hlim (w, k) hI

end UnforcedLeray.Short.PartI
