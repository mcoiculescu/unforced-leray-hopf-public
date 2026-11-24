import UnforcedLeray.Short.Spine.Sub.SP_CAN4_5_3

/-!
# Leaf 1 of `Spine:SP-CAN/4/5/3`: the radial-square profile of a test function

Proves `UnforcedLeray.Short.Spine.TestBeta`: a smooth `ψ` vanishing on `(-∞, a)` and `(b, ∞)`
with `0 < a` is `ψ(r) = r² β(r²)` on `(0, ∞)` for some smooth `β` on `ℝ` that vanishes on
`(-∞, a²)` and `(b², ∞)`.

Source of record: `the November 2 reference manuscript` line 1086 and lines
1134-1140.

Witness: `β s = ψ(√s) / s` for `s > 0` and `β s = 0` for `s ≤ 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b
open UnforcedLeray.Short.Spine.DClassicalAux

theorem testBeta_proof : UnforcedLeray.Short.Spine.TestBeta := by
  intro ψ hψ a b ha hψa hψb
  let β : ℝ → ℂ := fun s => if 0 < s then ψ (Real.sqrt s) * ((s : ℂ))⁻¹ else 0
  have hβpos : ∀ s : ℝ, 0 < s → β s = ψ (Real.sqrt s) * ((s : ℂ))⁻¹ :=
    fun s hs => if_pos hs
  have hβneg : ∀ s : ℝ, s ≤ 0 → β s = 0 :=
    fun s hs => if_neg (not_lt.mpr hs)
  -- `β` vanishes below `a²`
  have hbelow : ∀ s : ℝ, s < a ^ 2 → β s = 0 := by
    intro s hs
    by_cases h : 0 < s
    · rw [hβpos s h, hψa _ ((Real.sqrt_lt' ha).2 hs), zero_mul]
    · exact hβneg s (not_lt.mp h)
  -- `β` vanishes above `b²`
  have habove : ∀ s : ℝ, b ^ 2 < s → β s = 0 := by
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt (sq_nonneg b) hs
    have habs : |b| < Real.sqrt s := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_lt_sqrt (sq_nonneg b) hs
    have hbs : b < Real.sqrt s := lt_of_le_of_lt (le_abs_self b) habs
    rw [hβpos s hs0, hψb _ hbs, zero_mul]
  -- `β` is smooth on `ℝ`
  have hsmooth : ContDiff ℝ ∞ β := by
    refine contDiff_iff_contDiffAt.2 fun s => ?_
    by_cases hs : s < a ^ 2
    · refine (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℂ)) s).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hs] with t ht
      exact hbelow t (Set.mem_Iio.mp ht)
    · have hs' : a ^ 2 ≤ s := not_lt.mp hs
      have hs0 : 0 < s := lt_of_lt_of_le (pow_pos ha 2) hs'
      have hsqrt : ContDiffAt ℝ ∞ (fun t : ℝ => ψ (Real.sqrt t)) s :=
        hψ.contDiffAt.comp s (Real.contDiffAt_sqrt hs0.ne')
      have hinv : ContDiffAt ℝ ∞ (fun t : ℝ => ((t : ℂ))⁻¹) s := by
        have h1 : ContDiffAt ℝ ∞ (fun z : ℂ => z⁻¹) (s : ℂ) :=
          contDiffAt_inv (𝕜 := ℝ) (Complex.ofReal_ne_zero.mpr hs0.ne')
        exact h1.comp s Complex.ofRealCLM.contDiff.contDiffAt
      have hg : ContDiffAt ℝ ∞ (fun t : ℝ => ψ (Real.sqrt t) * ((t : ℂ))⁻¹) s :=
        hsqrt.mul hinv
      refine hg.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hs0] with t ht
      rw [hβpos t (Set.mem_Ioi.mp ht)]
  refine ⟨β, hsmooth, ?_, hbelow, habove⟩
  intro r hr
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [hβpos (r ^ 2) (pow_pos hr 2), Real.sqrt_sq hr.le]
  push_cast
  rw [mul_left_comm, mul_inv_cancel₀ (pow_ne_zero 2 hr0), mul_one]

end UnforcedLeray.Short.Spine
