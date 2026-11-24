import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.KT.Defs

/-!
# `KTPairInt`: the pairing `Σ_l F_l uψ_l` is integrable on the cell

Source: `the November 2 reference manuscript` lines 3052-3058 ("including the
horizontal mean").  For `IsKernelBiotSavart c ψ uψ`, the component `uψ j` splits as
`(uψ j - meanShear) + meanShear`: the first summand is in `L²(C_c)` by the definition of
`IsKernelBiotSavart`, so `F j` times it is integrable as an `L² · L²` product; the mean shear is
bounded by `|Γ / (2c)|` and measurable, so `F j` times it is integrable as an `L¹ · L^∞` product.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem ktPI_measurable_sign : Measurable Real.sign := by
  have e : Real.sign = fun r : ℝ => if r < 0 then (-1 : ℝ) else if 0 < r then 1 else 0 := by
    funext r
    rfl
  rw [e]
  exact Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)

theorem ktPI_meanShear_measurable (c Γ : ℝ) (j : Fin 2) :
    Measurable (fun x : ℝ × ℝ => meanShear c Γ x j) := by
  by_cases h : j = 0
  · have e : (fun x : ℝ × ℝ => meanShear c Γ x j) =
        fun x => -(Γ / (2 * c)) * Real.sign x.2 := by
      funext x
      simp [meanShear, h]
    rw [e]
    exact measurable_const.mul (ktPI_measurable_sign.comp measurable_snd)
  · have e : (fun x : ℝ × ℝ => meanShear c Γ x j) = fun _ => (0 : ℝ) := by
      funext x
      simp [meanShear, h]
    rw [e]
    exact measurable_const

theorem ktPI_meanShear_norm_le (c Γ : ℝ) (x : ℝ × ℝ) (j : Fin 2) :
    ‖((meanShear c Γ x j : ℝ) : ℂ)‖ ≤ |Γ / (2 * c)| := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold meanShear
  split_ifs
  · rw [abs_mul, abs_neg]
    have hs : |Real.sign x.2| ≤ 1 := by
      rcases Real.sign_apply_eq x.2 with h | h | h <;> rw [h] <;> norm_num
    exact mul_le_of_le_one_right (abs_nonneg _) hs
  · simp

theorem ktPairInt : UnforcedLeray.Short.IIIa.KTPairInt := by
  intro c F hF ψ uψ _hψ hu
  unfold IsKernelBiotSavart at hu
  obtain ⟨hL2, -, -⟩ := hu
  have hj : ∀ j : Fin 2,
      IntegrableOn (fun x => F j x * ((uψ x j : ℝ) : ℂ)) (B0579.cell c) := by
    intro j
    have e : (fun x => F j x * ((uψ x j : ℝ) : ℂ)) = fun x =>
        F j x * ((uψ x j - meanShear c (∫ y in B0579.cell c, ψ y) x j : ℝ) : ℂ) +
          F j x * ((meanShear c (∫ y in B0579.cell c, ψ y) x j : ℝ) : ℂ) := by
      funext x
      push_cast
      ring
    rw [e]
    have h1 : Integrable (fun x => F j x * ((uψ x j - meanShear c (∫ y in B0579.cell c, ψ y) x j : ℝ) : ℂ))
        (volume.restrict (B0579.cell c)) :=
      MemLp.integrable_mul (hF j).2 (hL2 j).ofReal
    have hms : AEStronglyMeasurable
        (fun x => ((meanShear c (∫ y in B0579.cell c, ψ y) x j : ℝ) : ℂ))
        (volume.restrict (B0579.cell c)) :=
      (Complex.measurable_ofReal.comp (ktPI_meanShear_measurable c _ j)).aestronglyMeasurable
    have h2 : Integrable (fun x => F j x * ((meanShear c (∫ y in B0579.cell c, ψ y) x j : ℝ) : ℂ))
        (volume.restrict (B0579.cell c)) :=
      (hF j).1.mul_bdd hms (Filter.Eventually.of_forall fun x =>
        ktPI_meanShear_norm_le c _ x j)
    exact h1.add h2
  exact (hj 0).add (hj 1)

end UnforcedLeray.Short.IIIa
