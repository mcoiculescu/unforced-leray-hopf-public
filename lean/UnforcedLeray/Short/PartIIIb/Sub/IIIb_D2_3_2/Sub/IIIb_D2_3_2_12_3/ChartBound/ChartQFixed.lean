import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_12_3_1_4

/-!
# `PartIII-b:IIIb-D2/3/2/12/3/1/4/3`: the `q`-coordinate of `chartOf` is fixed by `cellRep`

Source of record: `the November 2 reference manuscript`,
lines 2683, 2698-2700, 3256-3268, 4284-4286.

`chartOf R c z τ` has `q`-coordinate `u - c ⌊u/c + 1/2⌋` with `u = R log(ϱ/R) + Rτ/2`, which lies in
`[-c/2, c/2)`; `Axi.cellRep c` fixes every point of that interval.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray

theorem hh2_cellRep_fixed_aux (c u : ℝ) (hc : 0 < c) :
    UnforcedLeray.Axi.cellRep c (u - c * ⌊u / c + 1 / 2⌋) = u - c * ⌊u / c + 1 / 2⌋ := by
  unfold UnforcedLeray.Axi.cellRep
  have hfl : ⌊(u - c * ⌊u / c + 1 / 2⌋ + c / 2) / c⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    have h1 := Int.floor_le (u / c + 1 / 2)
    have h2 := Int.lt_floor_add_one (u / c + 1 / 2)
    have e : (u - c * ⌊u / c + 1 / 2⌋ + c / 2) / c = u / c + 1 / 2 - ⌊u / c + 1 / 2⌋ := by
      field_simp
      ring
    rw [e]
    constructor <;> linarith
  rw [hfl]
  simp

theorem chartOf_q_fixed_by_cellRep : ∀ (R c : ℝ), 0 < R → 0 < c → ∀ (z : UnforcedLeray.Space) (τ : ℝ), UnforcedLeray.Axi.cellRep c (UnforcedLeray.Short.PartIIIb.NearInst.chartOf R c z τ).2.1 = (UnforcedLeray.Short.PartIIIb.NearInst.chartOf R c z τ).2.1 := by
  intro R c _hR hc z τ
  dsimp only [UnforcedLeray.Short.PartIIIb.NearInst.chartOf]
  exact hh2_cellRep_fixed_aux c _ hc

end
