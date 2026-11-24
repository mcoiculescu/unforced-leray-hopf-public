import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3

/-!


Source: `the November 2 reference manuscript` lines 2100-2105.  Split into
* `BwdWeightedSup`: weighted maximum principle for `φ` itself (Phragmen-Lindelof for bounded
  solutions, bounded drift, compactly supported terminal datum, weight `(1+η²)^N`);
* `BwdWeightedDeriv`: given weighted decay of `φ` for all `N`, the same for `∇φ` and `Δφ`
  (weighted interior parabolic estimates on unit parabolic cylinders, backward from the terminal time).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-- `φ` decays faster than every power of `1 + η²`, uniformly on `[s,t]`. -/
def WeightedSup (s t : ℝ) (φ : ℝ → B0579.Plane → ℝ) : Prop :=
  ∀ N : ℝ, ∃ C : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane, |φ r x| * (1 + x.2 ^ 2) ^ N ≤ C

/-- **Sub-lemma 1** (SP 2100-2105): weighted maximum principle for `φ`. -/
def BwdWeightedSup : Prop :=
  ∀ (Sg ν c δ : ℝ), 0 < Sg → 0 < ν → 0 < c → 0 ≤ δ → ∀ tr : B0140.TrainSol ν c,
    TrainClose tr Sg δ → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ Sg / ν →
    ∀ ψ : B0579.Plane → ℝ, B0579.IsCylTest c ψ → ∀ φ : ℝ → B0579.Plane → ℝ,
      BwdSol ν c s t tr.v ψ φ → WeightedSup s t φ

/-- **Sub-lemma 2** (SP 2100-2105): weighted decay of `φ` gives weighted decay of `∇φ`, `Δφ`. -/
def BwdWeightedDeriv : Prop :=
  ∀ (Sg ν c δ : ℝ), 0 < Sg → 0 < ν → 0 < c → 0 ≤ δ → ∀ tr : B0140.TrainSol ν c,
    TrainClose tr Sg δ → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ Sg / ν →
    ∀ ψ : B0579.Plane → ℝ, B0579.IsCylTest c ψ → ∀ φ : ℝ → B0579.Plane → ℝ,
      BwdSol ν c s t tr.v ψ φ → WeightedSup s t φ → ∀ N : ℝ, ∃ C : ℝ,
        ∀ r ∈ Icc s t, ∀ x : B0579.Plane,
          (|B0579.pd 0 (φ r) x| + |B0579.pd 1 (φ r) x| + |lapP (φ r) x|) * (1 + x.2 ^ 2) ^ N ≤ C

theorem bwdDecay_of (h1 : BwdWeightedSup) (h2 : BwdWeightedDeriv) : BwdDecay := by
  intro Sg ν c δ hSg hν hc hδ tr htr s t hs hst ht ψ hψ φ hφ N
  have hW := h1 Sg ν c δ hSg hν hc hδ tr htr s t hs hst ht ψ hψ φ hφ
  obtain ⟨C1, h1'⟩ := hW N
  obtain ⟨C2, h2'⟩ := h2 Sg ν c δ hSg hν hc hδ tr htr s t hs hst ht ψ hψ φ hφ hW N
  refine ⟨C1 + C2, fun r hr x => ?_⟩
  have a := h1' r hr x
  have b := h2' r hr x
  nlinarith
end UnforcedLeray.Short.IIb
