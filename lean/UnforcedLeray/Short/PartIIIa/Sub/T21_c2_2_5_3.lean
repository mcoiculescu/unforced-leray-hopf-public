import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2_5_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2_5_1.Growth

/-!
# `PartIII-a:T21/c2/2/5/3`: `FmrIBPTrans`, decomposed (SP 2950-2954)

The transport identity `-2∫ g (v·∇g) p = ∫ g² (v·∇p)` for `p = movWeight m a` is the weight-generic
version of `PartII-b` `TransportIBP.core` (there `p = jb^m`).  The proof there only uses of the
weight: `C¹`, evenness in `q` (seam), and the bound `|p|+|∂_q p|+|∂_η p| ≤ K jb^m`.  Leaves:
`FmrTransGenInt` (integrability of the two integrands) and `FmrTransGenId` (the identity, given
integrability).  Proved here: `fmrIBPTrans_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Short.IIb
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- Admissible weights: `C¹`, `q`-even across the seam, `|w|+|∂w| ≤ K jb^m`. -/
structure TransWt (c m : ℝ) (w : B0579.Plane → ℝ) : Prop where
  smooth : ContDiff ℝ 1 w
  seam : ∀ η : ℝ, w (-c / 2, η) = w (c / 2, η)
  bound : ∃ K : ℝ, ∀ x : B0579.Plane,
    |w x| + |B0579.pd 0 w x| + |B0579.pd 1 w x| ≤ K * B0579.jb x ^ m

/-- **Leaf 1** (SP 2950-2954): both transport integrands are integrable on the cell, for a bounded
train velocity, `g ∈ CylSmoothDecay`, admissible weight `w` (generalise `TransportIBP.integrable_Gf`,
`integrable_Hf` from `jb^m` to `w`, using the bound `K jb^m`). -/
def FmrTransGenInt : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (σ : ℝ), 0 ≤ σ → 0 < c → 0 < ν →
    (∃ M : ℝ, ∀ x : B0579.Plane, |tr.v σ x 0| + |tr.v σ x 1| ≤ M) →
    ∀ (m : ℝ) (w : B0579.Plane → ℝ), TransWt c m w → ∀ g : B0579.Plane → ℝ, CylSmoothDecay c g →
      IntegrableOn (fun x => g x * (tr.v σ x 0 * B0579.pd 0 g x + tr.v σ x 1 * B0579.pd 1 g x) *
        w x) (B0579.cell c) ∧
      IntegrableOn (fun x => g x ^ 2 * (tr.v σ x 0 * B0579.pd 0 w x +
        tr.v σ x 1 * B0579.pd 1 w x)) (B0579.cell c)

/-- **Leaf 2** (SP 2950-2954): the transport identity, given the integrability of Leaf 1
(generalise `TransportIBP.transport_identity`, `tendsto_Lf`, `core` to the weight `w`: cutoff
`cutF R η`, `Cyl.transport_antisymm`, `div v = 0`, seam symmetry of `w`, cutoff error `→ 0`). -/
def FmrTransGenId : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (σ : ℝ), 0 ≤ σ → 0 < c → 0 < ν →
    (∃ M : ℝ, ∀ x : B0579.Plane, |tr.v σ x 0| + |tr.v σ x 1| ≤ M) →
    ∀ (m : ℝ) (w : B0579.Plane → ℝ), TransWt c m w → ∀ g : B0579.Plane → ℝ, CylSmoothDecay c g →
      IntegrableOn (fun x => g x * (tr.v σ x 0 * B0579.pd 0 g x + tr.v σ x 1 * B0579.pd 1 g x) *
        w x) (B0579.cell c) →
      IntegrableOn (fun x => g x ^ 2 * (tr.v σ x 0 * B0579.pd 0 w x +
        tr.v σ x 1 * B0579.pd 1 w x)) (B0579.cell c) →
      -(2 * ∫ x in B0579.cell c, g x * (tr.v σ x 0 * B0579.pd 0 g x + tr.v σ x 1 * B0579.pd 1 g x) *
          w x) =
        ∫ x in B0579.cell c, g x ^ 2 * (tr.v σ x 0 * B0579.pd 0 w x +
          tr.v σ x 1 * B0579.pd 1 w x)

theorem transWt_movWeight (c m a : ℝ) (hm : 0 ≤ m) (ha : 0 < a) :
    TransWt c m (movWeight m a) := by
  refine ⟨(movWeight_contDiff2 m a ha).of_le (by norm_num), ?_, ?_⟩
  · intro η
    unfold movWeight
    simp only [neg_div, neg_sq]
  · obtain ⟨K, hK⟩ := mwGrowth m a hm ha
    refine ⟨K, fun x => ?_⟩
    have := hK x
    have h3 := abs_nonneg (lapP (movWeight m a) x)
    linarith

theorem fmrIBPTrans_of (h1 : FmrTransGenInt) (h2 : FmrTransGenId) : FmrIBPTrans := by
  intro ν c tr σ hσ hc hν hM m a hm ha g hg
  have hw := transWt_movWeight c m a hm ha
  obtain ⟨i1, i2⟩ := h1 ν c tr σ hσ hc hν hM m _ hw g hg
  exact h2 ν c tr σ hσ hc hν hM m _ hw g hg i1 i2

end UnforcedLeray.Short.IIIa

#print axioms UnforcedLeray.Short.IIIa.fmrIBPTrans_of
