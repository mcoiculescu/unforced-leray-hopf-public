import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2

/-!
# `PartIII-a:T21/c2/2/5`: `FmrIBP`, decomposed (SP 2950-2954)

`fmrIBP_of` derives `FmrIBP` from three leaves on the cell with the weight `p = movWeight m a`:
integrability of the four integrands, the diffusion inequality `2∫ gΔg p ≤ ∫ g²Δp`, and the
transport identity `-2∫ g (v·∇g) p = ∫ g² (v·∇p)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Short.IIb
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- **Leaf 1** (SP 2950-2954; decay of `CylSmoothDecay`, polynomial growth of `p` and its
derivatives, bounded `v`): the four integrands are integrable on the cell. -/
def FmrIBPInt : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (σ : ℝ), 0 ≤ σ → 0 < c → 0 < ν →
    (∃ M : ℝ, ∀ x : B0579.Plane, |tr.v σ x 0| + |tr.v σ x 1| ≤ M) →
    ∀ (m a : ℝ), 0 ≤ m → 0 < a → ∀ g : B0579.Plane → ℝ, CylSmoothDecay c g →
      IntegrableOn (fun x => g x ^ 2 * lapP (movWeight m a) x) (B0579.cell c) ∧
      IntegrableOn (fun x => g x ^ 2 * (tr.v σ x 0 * B0579.pd 0 (movWeight m a) x +
        tr.v σ x 1 * B0579.pd 1 (movWeight m a) x)) (B0579.cell c) ∧
      IntegrableOn (fun x => g x * lapP g x * movWeight m a x) (B0579.cell c) ∧
      IntegrableOn (fun x => g x * (tr.v σ x 0 * B0579.pd 0 g x + tr.v σ x 1 * B0579.pd 1 g x) *
        movWeight m a x) (B0579.cell c)

/-- **Leaf 2** (diffusion; SP 2950-2954): `2∫ g Δg p = -2∫|∇g|²p + ∫ g²Δp - [g² p_q]` with the
seam term `≥ 0` since `p_q(c/2) ≥ 0` (`p` even in `q`); the cutoff `χ(η/R)` is removed by the
`η`-decay of `CylSmoothDecay`. -/
def FmrIBPDiff : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (m a : ℝ), 0 ≤ m → 0 < a → ∀ g : B0579.Plane → ℝ, CylSmoothDecay c g →
    2 * ∫ x in B0579.cell c, g x * lapP g x * movWeight m a x ≤
      ∫ x in B0579.cell c, g x ^ 2 * lapP (movWeight m a) x

/-- **Leaf 3** (transport; SP 2950-2954): for a bounded `c`-periodic divergence-free train
velocity `v` and `c`-periodic `g`, `p` even in `q`: `-2∫ g (v·∇g) p = ∫ g² (v·∇p)`
(`div v = 0`; the seam terms cancel by periodicity and evenness). -/
def FmrIBPTrans : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (σ : ℝ), 0 ≤ σ → 0 < c → 0 < ν →
    (∃ M : ℝ, ∀ x : B0579.Plane, |tr.v σ x 0| + |tr.v σ x 1| ≤ M) →
    ∀ (m a : ℝ), 0 ≤ m → 0 < a → ∀ g : B0579.Plane → ℝ, CylSmoothDecay c g →
      -(2 * ∫ x in B0579.cell c, g x * (tr.v σ x 0 * B0579.pd 0 g x + tr.v σ x 1 * B0579.pd 1 g x) *
          movWeight m a x) =
        ∫ x in B0579.cell c, g x ^ 2 * (tr.v σ x 0 * B0579.pd 0 (movWeight m a) x +
          tr.v σ x 1 * B0579.pd 1 (movWeight m a) x)

theorem fmrIBP_of (h1 : FmrIBPInt) (h2 : FmrIBPDiff) (h3 : FmrIBPTrans) : FmrIBP := by
  intro ν c tr σ hσ hc hν hM m a hm ha g hg
  obtain ⟨i1, i2, i3, i4⟩ := h1 ν c tr σ hσ hc hν hM m a hm ha g hg
  have d := h2 c hc m a hm ha g hg
  have t := h3 ν c tr σ hσ hc hν hM m a hm ha g hg
  have e1 : (fun x => g x ^ 2 * (ν * lapP (movWeight m a) x +
      (tr.v σ x 0 * B0579.pd 0 (movWeight m a) x + tr.v σ x 1 * B0579.pd 1 (movWeight m a) x))) =
      fun x => ν * (g x ^ 2 * lapP (movWeight m a) x) +
        g x ^ 2 * (tr.v σ x 0 * B0579.pd 0 (movWeight m a) x +
          tr.v σ x 1 * B0579.pd 1 (movWeight m a) x) := by
    funext x; ring
  have e2 : (fun x => g x * (ν * lapP g x -
      (tr.v σ x 0 * B0579.pd 0 g x + tr.v σ x 1 * B0579.pd 1 g x)) * movWeight m a x) =
      fun x => ν * (g x * lapP g x * movWeight m a x) -
        g x * (tr.v σ x 0 * B0579.pd 0 g x + tr.v σ x 1 * B0579.pd 1 g x) * movWeight m a x := by
    funext x; ring
  rw [e1, e2]
  refine ⟨(i1.const_mul ν).add i2, (i3.const_mul ν).sub i4, ?_⟩
  rw [integral_sub (i3.const_mul ν) i4, integral_const_mul, integral_add (i1.const_mul ν) i2,
    integral_const_mul]
  nlinarith [mul_le_mul_of_nonneg_left d hν.le]

end UnforcedLeray.Short.IIIa
