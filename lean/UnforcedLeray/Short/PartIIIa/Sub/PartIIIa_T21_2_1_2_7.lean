import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelDefs

/-!
# `KerVelFarField` from three leaves (SP 3052-3057, 2084)

`K_dψ - meanShear` is in `L²(C_d)`: it is measurable, bounded (near/far kernel bounds) and, outside
the support band of `ψ`, bounded by `C e^{-2π|η|/d}` (cot expansion; sign of `(x-y).2` equals that
of `x.2` on the support of `ψ`).  Hence it is dominated by `K e^{-2π|η|/d}`, square integrable on
the cell of width `d`.

Leaves: `KerVelMeas`, `KerVelBdd`, `KerVelTail`.  Assembly: `kerVelFarField_of_leaves`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Measurability of the kernel velocity of a test (parametric integral of the jointly measurable
`ψ(y) K_d(x - y)`, `K_d` measurable by `KerNearFar`). -/
def KerVelMeas : Prop :=
  ∀ d : ℝ, 1 ≤ d → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest d ψ → ∀ j : Fin 2,
    AEStronglyMeasurable (fun x => kerVel d ψ x j) (volume.restrict (B0579.cell d))

/-- Global boundedness of the kernel velocity of a test (SP 3054-3055: integrable near part,
bounded far part, `ψ` bounded with bounded support; periodic shift). -/
def KerVelBdd : Prop :=
  ∀ d : ℝ, 1 ≤ d → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest d ψ →
    ∃ B : ℝ, ∀ (x : ℝ × ℝ) (j : Fin 2), |kerVel d ψ x j| ≤ B

/-- Exponential tail of `K_dψ - meanShear` away from the support band of `ψ` (SP 3056-3057, 2084:
`|K_d(z) - m(z)| ≤ C_d e^{-2π|z.2|/d}` for `|z.2| ≥ 1`, from `cot w = -i - 2i e^{2iw}/(1-e^{2iw})`
for `Im w > 0`; `sign((x-y).2) = sign(x.2)` on the support of `ψ`). -/
def KerVelTail : Prop :=
  ∀ d : ℝ, 1 ≤ d → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest d ψ →
    ∃ R C : ℝ, ∀ x : ℝ × ℝ, R ≤ |x.2| → ∀ j : Fin 2,
      |kerVel d ψ x j - meanShear d (∫ y in B0579.cell d, ψ y) x j| ≤
        C * Real.exp (-(2 * Real.pi / d) * |x.2|)

lemma integrable_exp_neg_abs (a : ℝ) (ha : 0 < a) :
    Integrable (fun t : ℝ => Real.exp (-a * |t|)) := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-a * |t|)) (Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0).congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp [abs_of_pos (show (0:ℝ) < t from ht)]
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-a * |t|)) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic (a := a) ha 0).congr_fun ?_ measurableSet_Iic
    intro t ht
    simp [abs_of_nonpos (show t ≤ (0:ℝ) from ht)]
  have := h1.union h2
  rwa [Ioi_union_Iic, integrableOn_univ] at this

lemma meanShear_abs_le (c Γ : ℝ) (x : ℝ × ℝ) (j : Fin 2) :
    |meanShear c Γ x j| ≤ |Γ| / (2 * |c|) := by
  unfold meanShear
  split_ifs
  · rw [abs_mul, abs_neg, abs_div, abs_mul, abs_two]
    have : |Real.sign x.2| ≤ 1 := by
      rcases Real.sign_apply_eq x.2 with h | h | h <;> simp [h]
    calc |Γ| / (2 * |c|) * |Real.sign x.2| ≤ |Γ| / (2 * |c|) * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := mul_one _
  · simp; positivity

lemma measurable_meanShear (c Γ : ℝ) (j : Fin 2) : Measurable fun x : ℝ × ℝ => meanShear c Γ x j := by
  unfold meanShear
  split_ifs
  · have hs : Measurable Real.sign := by
      unfold Real.sign
      exact Measurable.ite measurableSet_Iio measurable_const
        (Measurable.ite measurableSet_Ioi measurable_const measurable_const)
    exact (hs.comp measurable_snd).const_mul _
  · exact measurable_const

/-- **Assembly** (SP 3052-3057, 2084). -/
theorem kerVelFarField_of_leaves (hM : KerVelMeas) (hB : KerVelBdd) (hT : KerVelTail) :
    KerVelFarField := by
  intro d hd ψ hψ j
  have hd0 : 0 < d := by linarith
  set Γ := ∫ y in B0579.cell d, ψ y with hΓ
  set a : ℝ := 2 * Real.pi / d with ha
  have ha0 : 0 < a := by positivity
  obtain ⟨B, hB'⟩ := hB d hd ψ hψ
  obtain ⟨R, C, hC⟩ := hT d hd ψ hψ
  set f : ℝ × ℝ → ℝ := fun x => kerVel d ψ x j - meanShear d Γ x j with hf
  have hfm : AEStronglyMeasurable f (volume.restrict (B0579.cell d)) :=
    (hM d hd ψ hψ j).sub (measurable_meanShear d Γ j).aestronglyMeasurable
  set B' : ℝ := B + |Γ| / (2 * |d|) with hB''
  set K : ℝ := max C (B' * Real.exp (a * |R|)) with hK
  have hbound : ∀ x : ℝ × ℝ, ‖f x‖ ≤ K * Real.exp (-a * |x.2|) := by
    intro x
    rw [Real.norm_eq_abs]
    by_cases hx : R ≤ |x.2|
    · calc |f x| ≤ C * Real.exp (-(2 * Real.pi / d) * |x.2|) := hC x hx j
        _ ≤ K * Real.exp (-a * |x.2|) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    · rw [not_le] at hx
      have h1 : |f x| ≤ B' := by
        calc |f x| ≤ |kerVel d ψ x j| + |meanShear d Γ x j| := abs_sub _ _
          _ ≤ B + |Γ| / (2 * |d|) := add_le_add (hB' x j) (meanShear_abs_le d Γ x j)
      have h2 : 1 ≤ Real.exp (a * |R|) * Real.exp (-a * |x.2|) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        have : |x.2| ≤ |R| := by
          have : |x.2| < R := hx
          exact this.le.trans (le_abs_self R)
        nlinarith
      have hB0 : 0 ≤ B' := le_trans (abs_nonneg _) h1
      calc |f x| ≤ B' := h1
        _ ≤ B' * (Real.exp (a * |R|) * Real.exp (-a * |x.2|)) := by
          calc B' = B' * 1 := (mul_one _).symm
            _ ≤ _ := mul_le_mul_of_nonneg_left h2 hB0
        _ = (B' * Real.exp (a * |R|)) * Real.exp (-a * |x.2|) := by ring
        _ ≤ K * Real.exp (-a * |x.2|) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  -- the dominating function is in L²
  have hg : MemLp (fun x : ℝ × ℝ => K * Real.exp (-a * |x.2|)) 2
      (volume.restrict (B0579.cell d)) := by
    have hgm : Measurable fun x : ℝ × ℝ => K * Real.exp (-a * |x.2|) :=
      measurable_const.mul (Real.measurable_exp.comp
        (measurable_const.mul (continuous_abs.measurable.comp measurable_snd)))
    rw [memLp_two_iff_integrable_sq hgm.aestronglyMeasurable]
    have hsq : (fun x : ℝ × ℝ => (K * Real.exp (-a * |x.2|)) ^ 2) =
        fun x => K ^ 2 * Real.exp (-(2 * a) * |x.2|) := by
      funext x
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast; ring
    rw [hsq]
    have hfin : IsFiniteMeasure (volume.restrict (Ico (-(d / 2)) (d / 2))) := by
      rw [isFiniteMeasure_restrict]; simp
    have hint : Integrable (fun t : ℝ => K ^ 2 * Real.exp (-(2 * a) * |t|)) :=
      (integrable_exp_neg_abs (2 * a) (by positivity)).const_mul _
    have := hint.comp_snd (volume.restrict (Ico (-(d / 2)) (d / 2)))
    have heq : volume.restrict (B0579.cell d) =
        (volume.restrict (Ico (-(d / 2)) (d / 2))).prod (volume : Measure ℝ) := by
      unfold B0579.cell
      rw [Measure.volume_eq_prod, Measure.restrict_prod_eq_prod_univ]
    rw [heq]
    exact this
  exact hg.mono' hfm (Eventually.of_forall hbound)

end UnforcedLeray.Short.IIIa
