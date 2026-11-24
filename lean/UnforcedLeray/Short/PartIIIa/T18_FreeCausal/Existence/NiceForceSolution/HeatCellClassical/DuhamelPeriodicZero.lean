import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_1

/-!
# Part III-a, leaf `PartIII-a:T18/2/4/1/2`: periodicity and zero entrance of the scalar Duhamel solve

Target: `DuhamelPeriodicZero` (defined in `Sub/T18_2_4_1.lean`, with `NiceScalar` and `duhamelHeat`).
Proof sketch: the substitution `z ↦ x - z` turns the `q`-shift of the output into a `q`-shift of
the source `h`, which is `c`-periodic; for `s ≤ a` and `r > 0` the time argument `s - r` is below
`a`, so the source vanishes on the whole integration domain.
Source of record: `the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The `q`-periodicity of a nice source, read at the shifted point `x - z`. -/
theorem duhPZ_integrand_shift (c : ℝ) (h : ℝ × (ℝ × ℝ) → ℂ)
    (hper : ∀ (s : ℝ) (x : ℝ × ℝ), h (s, (x.1 + c, x.2)) = h (s, x))
    (t : ℝ) (x z : ℝ × ℝ) :
    h (t, (x.1 + c - z.1, x.2 - z.2)) = h (t, (x.1 - z.1, x.2 - z.2)) := by
  rw [add_sub_right_comm]
  exact hper t (x.1 - z.1, x.2 - z.2)

/-- **Leaf 2: periodicity and the zero entrance** (`PartIII-a:T18/2/4/1/2`). For `c, ν > 0` and a
nice scalar source `h`, the Duhamel solve is `c`-periodic in `q` and vanishes for `s ≤ a`. -/
theorem duhamelPeriodicZero : DuhamelPeriodicZero := by
  intro c ν h _ _ hh
  obtain ⟨-, hper, a, B, R, ha, hz⟩ := hh
  refine ⟨fun s x => ?_, a, ha, fun s x hs => ?_⟩
  · -- periodicity: the shift by `c` in the output becomes a shift of the source
    unfold duhamelHeat
    congr 1
    funext r
    congr 1
    funext z
    congr 1
    exact duhPZ_integrand_shift c h hper (s - r) x z
  · -- zero entrance: for `r > 0` and `s ≤ a` the source vanishes at time `s - r < a`
    unfold duhamelHeat
    have hinner : ∀ r ∈ Ioi (0 : ℝ),
        (∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
            h (s - r, (x.1 - z.1, x.2 - z.2))) = 0 := by
      intro r hr
      have hr0 : (0 : ℝ) < r := hr
      have hlt : s - r < a := by linarith
      have hzero : ∀ z : ℝ × ℝ,
          ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
            h (s - r, (x.1 - z.1, x.2 - z.2)) = 0 := by
        intro z
        rw [hz (s - r) (x.1 - z.1, x.2 - z.2) (Or.inl hlt), mul_zero]
      simp only [hzero, integral_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi hinner]
    simp

end UnforcedLeray.Short.IIIa

end
