import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_1

/-!
# Part II-b, task `PartII-b:G4/5/2/1/1` (`RingLiftVanish`, locality of the ring lift)

Source of record: `the November 2 reference manuscript` lines 2347-2369.
`Nv R b τ y = √(age R y) • frameL y (b (chart R τ y))`.

If `b` vanishes for `s > S`, then `Nv R b τ` vanishes near every axis point and near every point
with `age R y > S`:
* a point `z` with `ϱ z ^ 2 < R ^ 2 / S` has `Nv z = 0`: either `ϱ z = 0` (so `age z = 0` and
  `√0 = 0`), or `ϱ z > 0` and then `age z > S`, so `b (chart z) = 0`;
* near an axis point `y`, `ϱ ^ 2 < R ^ 2 / S` holds by continuity;
* near `y` with `S < age R y`, `S < age R z` holds by continuity of `age` (as `ϱ y ^ 2 ≠ 0`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology

theorem ringLiftVanish : UnforcedLeray.Short.IIb.RingLiftVanish := by
  unfold UnforcedLeray.Short.IIb.RingLiftVanish
  intro S R τ b hS hR hb y hy
  have hR2 : 0 < R ^ 2 / S := div_pos (by nlinarith) hS
  -- points with `ϱ² < R²/S` have vanishing lift
  have key : ∀ z : UnforcedLeray.Space, UnforcedLeray.Axi.ϱ z ^ 2 < R ^ 2 / S →
      UnforcedLeray.Axi.Nv R b τ z = 0 := by
    intro z hz
    by_cases h0 : UnforcedLeray.Axi.ϱ z = 0
    · have hage : UnforcedLeray.Axi.age R z = 0 := by
        simp [UnforcedLeray.Axi.age, h0]
      simp [UnforcedLeray.Axi.Nv, hage]
    · have hpos : 0 < UnforcedLeray.Axi.ϱ z ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))
      have hz' : UnforcedLeray.Axi.ϱ z ^ 2 * S < R ^ 2 := by
        rw [lt_div_iff₀ hS] at hz
        exact hz
      have hSlt : S < UnforcedLeray.Axi.age R z := by
        unfold UnforcedLeray.Axi.age
        rw [lt_div_iff₀ hpos]
        linarith [mul_comm S (UnforcedLeray.Axi.ϱ z ^ 2)]
      have hb0 : b (UnforcedLeray.Axi.chart R τ z) = 0 :=
        hb (UnforcedLeray.Axi.chart R τ z) hSlt
      simp [UnforcedLeray.Axi.Nv, hb0]
  rcases hy with hy | hy
  · -- `y` on the axis: `ϱ y = 0`, so `ϱ² < R²/S` nearby by continuity
    have hy' : y 0 = 0 ∧ y 1 = 0 := hy
    have hϱy : UnforcedLeray.Axi.ϱ y ^ 2 = 0 := by
      have h : UnforcedLeray.Axi.ϱ y = 0 := by
        simp [UnforcedLeray.Axi.ϱ, hy'.1, hy'.2]
      simp [h]
    have hlt : UnforcedLeray.Axi.ϱ y ^ 2 < R ^ 2 / S := by
      rw [hϱy]
      exact hR2
    have hev : ∀ᶠ z in 𝓝 y, UnforcedLeray.Axi.ϱ z ^ 2 < R ^ 2 / S :=
      (UnforcedLeray.Axi.continuous_ϱ.pow 2).continuousAt.eventually_lt continuousAt_const hlt
    filter_upwards [hev] with z hz
    exact key z hz
  · -- `S < age R y`: `S < age R z` nearby by continuity of `age` (as `ϱ y ^ 2 ≠ 0`)
    have hy0 : UnforcedLeray.Axi.ϱ y ^ 2 ≠ 0 := by
      intro h
      unfold UnforcedLeray.Axi.age at hy
      rw [h, div_zero] at hy
      linarith
    have hc : ContinuousAt (fun z => UnforcedLeray.Axi.age R z) y :=
      continuousAt_const.div ((UnforcedLeray.Axi.continuous_ϱ.pow 2).continuousAt) hy0
    have hev : ∀ᶠ z in 𝓝 y, S < UnforcedLeray.Axi.age R z :=
      continuousAt_const.eventually_lt hc hy
    filter_upwards [hev] with z hz
    have hb0 : b (UnforcedLeray.Axi.chart R τ z) = 0 :=
      hb (UnforcedLeray.Axi.chart R τ z) hz
    simp [UnforcedLeray.Axi.Nv, hb0]

end
