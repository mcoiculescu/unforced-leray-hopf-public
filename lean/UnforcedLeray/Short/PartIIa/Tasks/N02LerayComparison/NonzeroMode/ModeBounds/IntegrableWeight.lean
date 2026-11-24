import UnforcedLeray.Short.PartIIa.Sub.N02_4_7
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Part II-a, task `PartII-a:N02/4/7/2`: `NzmbIntegrableWeight`

Source of record: `the November 2 reference manuscript`, lines 1722-1727.
A function `g` supported in an `s`-band `[s0, s1]` (with `s0 > 0`) and bounded by
`C exp(-κ|η|)` has `(|η|^j)^2 ‖g‖^2 s^{-3/2}` integrable on `Ioi 0 × univ`.
Domination: the integrand is bounded by `1_{[s0,s1]}(s) · K · (|η|^j)^2 exp(-2κ|η|)` with
`K = C^2 s0^{-3/2}`, which is a product of integrable functions.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- `|t|^m exp(-b|t|)` is integrable on `ℝ` for `b > 0`. -/
theorem nzmbiw_abs_exp (m : ℕ) (b : ℝ) (hb : 0 < b) :
    Integrable (fun t : ℝ => |t| ^ m * Real.exp (-b * |t|)) := by
  have hpos : IntegrableOn (fun t : ℝ => |t| ^ m * Real.exp (-b * |t|)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (m : ℝ)) (b := b)
      (by have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m; linarith) one_pos hb
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx' : (0 : ℝ) < x := hx
    simp only [abs_of_pos hx', Real.rpow_one, Real.rpow_natCast]
  have hiio : IntegrableOn (fun t : ℝ => |t| ^ m * Real.exp (-b * |t|)) (Iio 0) := by
    have h := (MeasurePreserving.integrableOn_comp_preimage
      (Measure.measurePreserving_neg (volume : Measure ℝ))
      (Homeomorph.neg ℝ).measurableEmbedding
      (f := fun t : ℝ => |t| ^ m * Real.exp (-b * |t|)) (s := Ioi 0)).2 hpos
    have e1 : (fun x : ℝ => -x) ⁻¹' Ioi (0 : ℝ) = Iio 0 := by ext x; simp
    simpa [Function.comp_def, abs_neg, e1] using h
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨hiio, hpos⟩

theorem nzmbIntegrableWeight : NzmbIntegrableWeight := by
  intro g hg s0 s1 κ C hs0 hκ hsupp hdecay j
  have hH : Integrable (fun t : ℝ => (|t| ^ j) ^ 2 * Real.exp (-(2 * κ) * |t|)) := by
    refine (nzmbiw_abs_exp (j * 2) (2 * κ) (by linarith)).congr
      (ae_of_all _ fun t => ?_)
    simp only [pow_mul]
  have hI1 : Integrable (fun s : ℝ => (Icc s0 s1).indicator (fun _ => (1 : ℝ)) s) :=
    (integrableOn_const (C := (1 : ℝ)) (s := Icc s0 s1)
      (measure_Icc_lt_top).ne).integrable_indicator measurableSet_Icc
  have hG : Integrable (fun z : ℝ × ℝ => (Icc s0 s1).indicator (fun _ => (1 : ℝ)) z.1 *
      ((C ^ 2 * s0 ^ (-(3 / 2 : ℝ))) * ((|z.2| ^ j) ^ 2 * Real.exp (-(2 * κ) * |z.2|))))
      (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact hI1.mul_prod (hH.const_mul (C ^ 2 * s0 ^ (-(3 / 2 : ℝ))))
  refine Integrable.mono' hG.integrableOn ?_ (ae_of_all _ fun x => ?_)
  · apply Measurable.aestronglyMeasurable
    have m1 : Measurable (fun x : ℝ × ℝ => (|x.2| ^ j) ^ 2) :=
      ((measurable_snd.abs).pow_const j).pow_const 2
    have m2 : Measurable (fun x : ℝ × ℝ => ‖g x‖ ^ 2) :=
      ((hg.continuous.norm).measurable).pow_const 2
    have m3 : Measurable (fun x : ℝ × ℝ => x.1 ^ (-(3 / 2 : ℝ))) :=
      measurable_fst.pow_const _
    exact (m1.mul m2).mul m3
  · by_cases hx : x.1 ∈ Icc s0 s1
    · have hx0 : 0 < x.1 := lt_of_lt_of_le hs0 hx.1
      have hA : ‖g x‖ ^ 2 ≤ C ^ 2 * Real.exp (-(2 * κ) * |x.2|) := by
        have h1 := hdecay x
        have h2 : ‖g x‖ ^ 2 ≤ (C * Real.exp (-κ * |x.2|)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
        have h3 : Real.exp (-(2 * κ) * |x.2|) = (Real.exp (-κ * |x.2|)) ^ 2 := by
          rw [sq, ← Real.exp_add]; congr 1; ring
        rw [h3, ← mul_pow]
        exact h2
      have hB : x.1 ^ (-(3 / 2 : ℝ)) ≤ s0 ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hs0 hx.1 (by norm_num)
      have hB0 : 0 ≤ x.1 ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
      have hP : 0 ≤ (|x.2| ^ j) ^ 2 := by positivity
      have hnn : 0 ≤ (|x.2| ^ j) ^ 2 * ‖g x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) :=
        mul_nonneg (mul_nonneg hP (sq_nonneg _)) hB0
      have key : (|x.2| ^ j) ^ 2 * ‖g x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) ≤
          (C ^ 2 * s0 ^ (-(3 / 2 : ℝ))) * ((|x.2| ^ j) ^ 2 * Real.exp (-(2 * κ) * |x.2|)) := by
        calc (|x.2| ^ j) ^ 2 * ‖g x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))
            ≤ (|x.2| ^ j) ^ 2 * (C ^ 2 * Real.exp (-(2 * κ) * |x.2|)) * s0 ^ (-(3 / 2 : ℝ)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hA hP) hB hB0 (by positivity)
          _ = (C ^ 2 * s0 ^ (-(3 / 2 : ℝ))) * ((|x.2| ^ j) ^ 2 * Real.exp (-(2 * κ) * |x.2|)) := by
              ring
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      simp only [Set.indicator_of_mem hx, one_mul]
      exact key
    · have hg0 : g x = 0 := by
        by_contra h
        exact hx (hsupp x h)
      rw [hg0]
      simp [hx]

end UnforcedLeray.Short.PartIIa
