import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2

/-!


Source: `the November 2 reference manuscript` lines 2085-2093 (train comparison
gives bounded drift derivatives) and 2100-2105 (weighted estimates).

Plan: weighted Bernstein estimates, each a weighted maximum principle for a quadratic quantity
(`|∇φ|² + λφ²` resp. `|D²φ|² + λ|∇φ|²`, times `(1+η²)^N`), using bounded drift and drift
derivatives.  Since the drift derivatives are only assumed bounded, `DriftC2Bdd` is stated
on the plane, not only on the cell (`TrainClose.plane_bound` plus boundedness of `V_c` and its
derivatives, SP 2085-2093).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-- The drift `v` and its derivatives of orders `1, 2` are bounded by `V` on `[0, T] × ℝ²`. -/
def DriftC2Bdd (v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec) (T V : ℝ) : Prop :=
  ∀ r ∈ Icc (0 : ℝ) T, ∀ x : B0579.Plane, ∀ i : Fin 2,
    |v r x i| ≤ V ∧ (∀ j : Fin 2, |B0579.pd j (fun y => v r y i) x| ≤ V) ∧
    ∀ j k : Fin 2, |B0579.pd j (B0579.pd k (fun y => v r y i)) x| ≤ V

/-- **Leaf `/3`** (SP 2085-2093): the train drift and its first two derivatives are bounded. -/
def BwdDriftC2Bound : Prop :=
  ∀ (Sg ν c δ : ℝ), 0 < Sg → 0 < ν → 0 < c → 0 ≤ δ → ∀ tr : B0140.TrainSol ν c,
    TrainClose tr Sg δ → ∃ V : ℝ, DriftC2Bdd tr.v (Sg / ν) V

/-- **Leaf `/1`** (SP 2100-2105): weighted Bernstein bound for the first derivatives. -/
def BwdWeightedGrad : Prop :=
  ∀ (Sg ν c δ V : ℝ), 0 < Sg → 0 < ν → 0 < c → 0 ≤ δ → ∀ tr : B0140.TrainSol ν c,
    TrainClose tr Sg δ → DriftC2Bdd tr.v (Sg / ν) V → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ Sg / ν →
    ∀ ψ : B0579.Plane → ℝ, B0579.IsCylTest c ψ → ∀ φ : ℝ → B0579.Plane → ℝ,
      BwdSol ν c s t tr.v ψ φ → WeightedSup s t φ → ∀ N : ℝ, ∃ C : ℝ,
        ∀ r ∈ Icc s t, ∀ x : B0579.Plane,
          (|B0579.pd 0 (φ r) x| + |B0579.pd 1 (φ r) x|) * (1 + x.2 ^ 2) ^ N ≤ C

/-- **Leaf `/2`** (SP 2100-2105): weighted bound for `Δφ` given weighted decay of `φ` and `∇φ`
(Bernstein for `D²φ`, or `νΔφ = -(φ_r + v·∇φ)` with a weighted bound on `φ_r`). -/
def BwdWeightedLap : Prop :=
  ∀ (Sg ν c δ V : ℝ), 0 < Sg → 0 < ν → 0 < c → 0 ≤ δ → ∀ tr : B0140.TrainSol ν c,
    TrainClose tr Sg δ → DriftC2Bdd tr.v (Sg / ν) V → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ Sg / ν →
    ∀ ψ : B0579.Plane → ℝ, B0579.IsCylTest c ψ → ∀ φ : ℝ → B0579.Plane → ℝ,
      BwdSol ν c s t tr.v ψ φ → WeightedSup s t φ →
      (∀ N : ℝ, ∃ C : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane,
        (|B0579.pd 0 (φ r) x| + |B0579.pd 1 (φ r) x|) * (1 + x.2 ^ 2) ^ N ≤ C) →
      ∀ N : ℝ, ∃ C : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane,
        |lapP (φ r) x| * (1 + x.2 ^ 2) ^ N ≤ C

theorem bwdWeightedDeriv_of (h0 : BwdDriftC2Bound) (h1 : BwdWeightedGrad) (h2 : BwdWeightedLap) :
    BwdWeightedDeriv := by
  intro Sg ν c δ hSg hν hc hδ tr htr s t hs hst ht ψ hψ φ hφ hW N
  obtain ⟨V, hV⟩ := h0 Sg ν c δ hSg hν hc hδ tr htr
  have hg := h1 Sg ν c δ V hSg hν hc hδ tr htr hV s t hs hst ht ψ hψ φ hφ hW
  have hl := h2 Sg ν c δ V hSg hν hc hδ tr htr hV s t hs hst ht ψ hψ φ hφ hW hg
  obtain ⟨C1, h1'⟩ := hg N
  obtain ⟨C2, h2'⟩ := hl N
  refine ⟨C1 + C2, fun r hr x => ?_⟩
  have a := h1' r hr x
  have b := h2' r hr x
  nlinarith

end UnforcedLeray.Short.IIb
