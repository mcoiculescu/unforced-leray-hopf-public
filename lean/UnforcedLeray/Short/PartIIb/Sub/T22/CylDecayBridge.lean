import UnforcedLeray.Short.PartIIb.Sub.T22

/-!
# Bridge for the corrected cylinder decay class (`ORG:cyl-weight`, `PartII-b:T22`)

`CylSmoothDecay c g` and `IsRegularCylFlow.decay` (`Sub/T22.lean`) now ask for decay in `η` only,
with the weight `(1 + η²)^N` (SP 2074-2076: the weight `(1 + q² + η²)^m` lives on the centered
cell, where `|q| ≤ c/2`). On the closed cell strip `|q| ≤ c/2` the two weights are comparable:

  `1 + η² ≤ jb ≤ (1 + c²/4)(1 + η²)`, `jb = 1 + q² + η²`.

Hence the decay estimate in the old `jb^N` form holds on the strip `|q| ≤ c/2` (in particular on
`B0579.cell c` and at its seam points `q = ±c/2`), with the constant multiplied by
`(1 + c²/4)^|N|`. This is what the proofs of the leaves `RegularEnergyDeriv`, `CylDiffusionBound`
and `CylTransportIBP` need: replace `hg.decay N` (pointwise on the whole plane) by
`hg.cell_decay N` (pointwise on `|x.1| ≤ c/2`).

Main results: `jb_le_cell_mul`, `jb_rpow_le_cell`, `cell_jb_rpow_le`, `CylSmoothDecay.cell_decay`,
`IsRegularCylFlow.cell_decay`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-- A point of the centered cell has `|q| ≤ c/2`. -/
theorem abs_fst_le_of_mem_cell {c : ℝ} {x : B0579.Plane} (hx : x ∈ B0579.cell c) :
    |x.1| ≤ c / 2 := by
  have h := hx.1
  rw [abs_le]
  exact ⟨h.1, h.2.le⟩

/-- The `η`-weight is dominated by `jb`. -/
theorem one_add_eta_sq_le_jb (x : B0579.Plane) : 1 + x.2 ^ 2 ≤ B0579.jb x := by
  unfold B0579.jb
  nlinarith [sq_nonneg x.1]

/-- On the strip `|q| ≤ c/2`: `jb ≤ (1 + c²/4)(1 + η²)`. -/
theorem jb_le_cell_mul {c : ℝ} {x : B0579.Plane} (hx : |x.1| ≤ c / 2) :
    B0579.jb x ≤ (1 + c ^ 2 / 4) * (1 + x.2 ^ 2) := by
  unfold B0579.jb
  have hq : x.1 ^ 2 ≤ c ^ 2 / 4 := by
    rw [abs_le] at hx
    nlinarith [hx.1, hx.2]
  nlinarith [sq_nonneg c, sq_nonneg x.2, mul_nonneg (sq_nonneg c) (sq_nonneg x.2)]

private theorem one_le_A (c : ℝ) : 1 ≤ 1 + c ^ 2 / 4 := by
  have := sq_nonneg c
  linarith

/-- Upper comparison of the powers: on `|q| ≤ c/2`, `jb^N ≤ (1 + c²/4)^|N| (1 + η²)^N`. -/
theorem jb_rpow_le_cell {c N : ℝ} {x : B0579.Plane} (hx : |x.1| ≤ c / 2) :
    B0579.jb x ^ N ≤ (1 + c ^ 2 / 4) ^ |N| * (1 + x.2 ^ 2) ^ N := by
  have hA1 := one_le_A c
  have hη : 0 < 1 + x.2 ^ 2 := by positivity
  rcases le_total 0 N with hN | hN
  · rw [abs_of_nonneg hN, ← Real.mul_rpow (by linarith) hη.le]
    exact Real.rpow_le_rpow (B0579.jb_pos x).le (jb_le_cell_mul hx) hN
  · rw [abs_of_nonpos hN]
    calc B0579.jb x ^ N ≤ (1 + x.2 ^ 2) ^ N :=
          Real.rpow_le_rpow_of_nonpos hη (one_add_eta_sq_le_jb x) hN
      _ = 1 * (1 + x.2 ^ 2) ^ N := (one_mul _).symm
      _ ≤ (1 + c ^ 2 / 4) ^ (-N) * (1 + x.2 ^ 2) ^ N :=
          mul_le_mul_of_nonneg_right (Real.one_le_rpow hA1 (neg_nonneg.2 hN))
            (Real.rpow_nonneg hη.le _)

/-- Lower comparison of the powers: on `|q| ≤ c/2`, `(1 + c²/4)^(-|N|) (1 + η²)^N ≤ jb^N`. -/
theorem cell_jb_rpow_le {c N : ℝ} {x : B0579.Plane} (hx : |x.1| ≤ c / 2) :
    (1 + c ^ 2 / 4) ^ (-|N|) * (1 + x.2 ^ 2) ^ N ≤ B0579.jb x ^ N := by
  have hA1 := one_le_A c
  have hA0 : 0 < 1 + c ^ 2 / 4 := by linarith
  have hη : 0 < 1 + x.2 ^ 2 := by positivity
  rcases le_total 0 N with hN | hN
  · rw [abs_of_nonneg hN]
    calc (1 + c ^ 2 / 4) ^ (-N) * (1 + x.2 ^ 2) ^ N ≤ 1 * (1 + x.2 ^ 2) ^ N :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_one_of_one_le_of_nonpos hA1 (neg_nonpos.2 hN))
            (Real.rpow_nonneg hη.le _)
      _ = (1 + x.2 ^ 2) ^ N := one_mul _
      _ ≤ B0579.jb x ^ N := Real.rpow_le_rpow hη.le (one_add_eta_sq_le_jb x) hN
  · rw [abs_of_nonpos hN, neg_neg]
    calc (1 + c ^ 2 / 4) ^ N * (1 + x.2 ^ 2) ^ N
        = ((1 + c ^ 2 / 4) * (1 + x.2 ^ 2)) ^ N := (Real.mul_rpow hA0.le hη.le).symm
      _ ≤ B0579.jb x ^ N :=
          Real.rpow_le_rpow_of_nonpos (B0579.jb_pos x) (jb_le_cell_mul hx) hN

/-- **The old `jb`-weighted decay on the cell strip.** A function of class `CylSmoothDecay c`
satisfies the bound `(|g| + |∂_q g| + |∂_η g| + |Δ g|) jb^N ≤ C` on `|q| ≤ c/2` for every real `N`. -/
theorem CylSmoothDecay.cell_decay {c : ℝ} {g : B0579.Plane → ℝ} (hg : CylSmoothDecay c g)
    (N : ℝ) : ∃ C : ℝ, ∀ x : B0579.Plane, |x.1| ≤ c / 2 →
      (|g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x|) * B0579.jb x ^ N ≤ C := by
  obtain ⟨C, hC⟩ := hg.decay N
  refine ⟨(1 + c ^ 2 / 4) ^ |N| * C, fun x hx => ?_⟩
  have hA0 : 0 ≤ (1 + c ^ 2 / 4) ^ |N| := Real.rpow_nonneg (by linarith [one_le_A c]) _
  have hS : 0 ≤ |g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x| := by positivity
  calc (|g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x|) * B0579.jb x ^ N
      ≤ (|g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x|) *
          ((1 + c ^ 2 / 4) ^ |N| * (1 + x.2 ^ 2) ^ N) :=
        mul_le_mul_of_nonneg_left (jb_rpow_le_cell hx) hS
    _ = (1 + c ^ 2 / 4) ^ |N| *
          ((|g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x|) * (1 + x.2 ^ 2) ^ N) := by
        ring
    _ ≤ (1 + c ^ 2 / 4) ^ |N| * C := mul_le_mul_of_nonneg_left (hC x) hA0

/-- The same for a regular flow, uniformly in the age. -/
theorem IsRegularCylFlow.cell_decay {c ν : ℝ}
    {v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec} {s T : ℝ} {ω : ℝ → B0579.Plane → ℝ}
    (hω : IsRegularCylFlow c ν v s T ω) (N : ℝ) :
    ∃ C : ℝ, ∀ σ ∈ Icc s T, ∀ x : B0579.Plane, |x.1| ≤ c / 2 →
      (|ω σ x| + |B0579.pd 0 (ω σ) x| + |B0579.pd 1 (ω σ) x| + |lapP (ω σ) x|) *
        B0579.jb x ^ N ≤ C := by
  obtain ⟨C, hC⟩ := hω.decay N
  refine ⟨(1 + c ^ 2 / 4) ^ |N| * C, fun σ hσ x hx => ?_⟩
  have hA0 : 0 ≤ (1 + c ^ 2 / 4) ^ |N| := Real.rpow_nonneg (by linarith [one_le_A c]) _
  have hS : 0 ≤ |ω σ x| + |B0579.pd 0 (ω σ) x| + |B0579.pd 1 (ω σ) x| + |lapP (ω σ) x| := by
    positivity
  calc (|ω σ x| + |B0579.pd 0 (ω σ) x| + |B0579.pd 1 (ω σ) x| + |lapP (ω σ) x|) *
        B0579.jb x ^ N
      ≤ (|ω σ x| + |B0579.pd 0 (ω σ) x| + |B0579.pd 1 (ω σ) x| + |lapP (ω σ) x|) *
          ((1 + c ^ 2 / 4) ^ |N| * (1 + x.2 ^ 2) ^ N) :=
        mul_le_mul_of_nonneg_left (jb_rpow_le_cell hx) hS
    _ = (1 + c ^ 2 / 4) ^ |N| *
          ((|ω σ x| + |B0579.pd 0 (ω σ) x| + |B0579.pd 1 (ω σ) x| + |lapP (ω σ) x|) *
            (1 + x.2 ^ 2) ^ N) := by ring
    _ ≤ (1 + c ^ 2 / 4) ^ |N| * C := mul_le_mul_of_nonneg_left (hC σ hσ x) hA0

end UnforcedLeray.Short.IIb
