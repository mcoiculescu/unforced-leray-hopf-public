import UnforcedLeray.Short.PartI.Sub.PartI_T08_2

/-!
# Part I, task `PartI:T08/2/1` (`VcWordL2`): L² of the word derivatives of `V_c^p`

Source: `the November 2 reference manuscript` lines 326-329 (the bounds for `V_c`
and `Q_c`) and line 294 (`V_c^p`).

Route: `Train.Vc_bounds j 1` gives the pointwise bound
`(1 + η²/a) |∂_w V_c,k| ≤ C a^{-(3+j)/2}`, so `|∂_w V_c,k| ≤ K (1 + η²/a)⁻¹` with `K` independent
of `z`. The function `(1 + η²/a)⁻¹` is in `L²` of the centred cell: its square is
`φ(η/√a)` with `φ(x) = ((1+x²)⁻¹)²` integrable (dominated by `(1+x²)⁻¹`), and the cell is
`(volume.restrict Ico) × volume`, so the `η`-integrable factor is paired with a finite `q`-measure.
Continuity of `∂_w V_c,k` (from `vcReg_contDiff_Vc` and `contDiff_derivWord`) gives measurability.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc width)

/-- Integrability of the square of the transverse weight `(1 + η²/a)⁻¹` on the real line. -/
private theorem weight_sq_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun η : ℝ => ((1 + η ^ 2 / a)⁻¹) ^ 2) := by
  have hφ : Integrable (fun x : ℝ => ((1 + x ^ 2)⁻¹) ^ 2) := by
    refine (integrable_inv_one_add_sq).mono' ?_ ?_
    · have hc : Continuous (fun x : ℝ => (1 + x ^ 2)⁻¹) :=
        Continuous.inv₀ (by fun_prop) (fun x => by positivity)
      exact (hc.pow 2).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      have h0 : 0 ≤ (1 + x ^ 2)⁻¹ := by positivity
      have h1 : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith
  have hsq : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have h := hφ.comp_div hsq
  have e : (fun η : ℝ => ((1 + (η / Real.sqrt a) ^ 2)⁻¹) ^ 2) =
      fun η : ℝ => ((1 + η ^ 2 / a)⁻¹) ^ 2 := by
    funext η
    rw [div_pow, Real.sq_sqrt ha.le]
  simpa only [e] using h

/-- The `L²` membership of the transverse weight `(1 + η²/a)⁻¹` on the centred cell. -/
private theorem weight_memLp_cell {a c : ℝ} (ha : 0 < a) :
    MemLp (fun z : Plane => (1 + z.2 ^ 2 / a)⁻¹) 2 (Cyl.cellμ c) := by
  have hcont : Continuous (fun z : Plane => (1 + z.2 ^ 2 / a)⁻¹) := by
    refine Continuous.inv₀ (by fun_prop) (fun z => ?_)
    have h : 0 < 1 + z.2 ^ 2 / a := by
      have := div_nonneg (sq_nonneg z.2) ha.le
      linarith
    exact h.ne'
  refine (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 ?_
  rw [Cyl.cellμ_eq_prod]
  haveI : IsFiniteMeasure (volume.restrict (Set.Ico (-c / 2) (c / 2))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ico_lt_top⟩
  exact (weight_sq_integrable ha).comp_snd _

theorem vcWordL2_proof : UnforcedLeray.Short.PartI.VcWordL2 := by
  intro ν c s hc ha1 hac w k
  have ha : 0 < width ν s := lt_of_lt_of_le one_pos ha1
  obtain ⟨C, b, hC, hb, h⟩ := UnforcedLeray.Train.Vc_bounds w.length 1
  have hV : ContDiff ℝ ∞ (Vc ν c s) := UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc ha
  have hVk : ContDiff ℝ ∞ (fun x => Vc ν c s x k) :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hV
  have hmeas : AEStronglyMeasurable (wordComp w (Vc ν c s) k) (Cyl.cellμ c) :=
    (B0151.contDiff_derivWord hVk w).continuous.aestronglyMeasurable
  have hK : MemLp (fun z : Plane => (C * width ν s ^ (-(3 + (w.length : ℝ)) / 2)) *
      (1 + z.2 ^ 2 / width ν s)⁻¹) 2 (Cyl.cellμ c) :=
    (weight_memLp_cell (c := c) ha).const_mul _
  refine MemLp.of_le hK hmeas (Filter.Eventually.of_forall fun z => ?_)
  have hp : 0 < 1 + z.2 ^ 2 / width ν s := by
    have := div_nonneg (sq_nonneg z.2) ha.le
    linarith
  have hz := (h ν c s hc ha1 hac).1 w rfl k z
  rw [pow_one] at hz
  have key : |wordComp w (Vc ν c s) k z| ≤
      (C * width ν s ^ (-(3 + (w.length : ℝ)) / 2)) * (1 + z.2 ^ 2 / width ν s)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hp]
    calc |wordComp w (Vc ν c s) k z| * (1 + z.2 ^ 2 / width ν s)
        = (1 + z.2 ^ 2 / width ν s) * |wordComp w (Vc ν c s) k z| := mul_comm _ _
      _ ≤ C * width ν s ^ (-(3 + (w.length : ℝ)) / 2) := hz
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact key.trans (le_abs_self _)

end UnforcedLeray.Short.PartI
