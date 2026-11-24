import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_5

/-!
# Leaf `PartIII-a:T21/2/1/2/5/5`: the lattice `{den = 0}` is a null set

Source of record: `the November 2 reference manuscript` lines 2081-2084.
`den d z = 2 (sin²(πq/d) + sinh²(πη/d))` (`B0592.den_eq`), so `den d z = 0` forces `η = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Leaf `KerLatticeNull`** (SP 2081-2084). -/
theorem kerLatticeNull : KerLatticeNull := by
  intro d hd
  have hsub : {z : ℝ × ℝ | UnforcedLeray.B0592.den d z = 0} ⊆
      (univ : Set ℝ) ×ˢ ({0} : Set ℝ) := by
    intro z hz
    have hz' : UnforcedLeray.B0592.den d z = 0 := hz
    rw [UnforcedLeray.B0592.den_eq] at hz'
    have h1 := sq_nonneg (Real.sin (Real.pi * z.1 / d))
    have h2 := sq_nonneg (Real.sinh (Real.pi * z.2 / d))
    have hb : Real.sinh (Real.pi * z.2 / d) ^ 2 ≤ 0 := by linarith
    have hs : Real.sinh (Real.pi * z.2 / d) ^ 2 = 0 := le_antisymm hb h2
    have hsh : Real.sinh (Real.pi * z.2 / d) = 0 := pow_eq_zero_iff two_ne_zero |>.1 hs
    have h0 : Real.pi * z.2 / d = 0 := Real.sinh_eq_zero.1 hsh
    refine Set.mem_prod.2 ⟨Set.mem_univ _, ?_⟩
    rw [Set.mem_singleton_iff]
    rcases div_eq_zero_iff.1 h0 with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' Real.pi_ne_zero
      · exact h'
    · exact absurd h hd.ne'
  have hvol : volume ((univ : Set ℝ) ×ˢ ({0} : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
  exact measure_mono_null hsub hvol

end UnforcedLeray.Short.IIIa
