import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2

/-!
# Part III-a helper: integrability of a weighted flux against a bounded continuous function on the cell

For `m ≥ 1`, `∫_cell ⟨x⟩^{-m} dx < ∞` (the cell is bounded in `q` and the `η`-integral of
`(1+η²)^{-1}` is finite). Consequently a flux `f ∈ X_{c,m}` times a bounded continuous `g` is
integrable on the cell.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.Exist

theorem integrableOn_jb_rpow_neg_cell {c : ℝ} (m : ℝ) (hm : 1 ≤ m) :
    IntegrableOn (fun x : ℝ × ℝ => UnforcedLeray.B0579.jb x ^ (-m))
      (UnforcedLeray.B0579.cell c) := by
  have hη : Integrable (fun y : ℝ => (1 + y ^ 2) ^ (-(1 : ℝ))) := by
    have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := (volume : Measure ℝ)) (r := 2)
      (by simp)
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only [Real.norm_eq_abs, sq_abs]
    norm_num
  have hI : Integrable (fun z : ℝ × ℝ =>
      (Set.indicator (Ico (-(c / 2)) (c / 2)) (fun _ : ℝ => (1 : ℝ)) z.1) *
        (1 + z.2 ^ 2) ^ (-(1 : ℝ))) (volume : Measure (ℝ × ℝ)) := by
    have h1 : Integrable (Set.indicator (Ico (-(c / 2)) (c / 2)) (fun _ : ℝ => (1 : ℝ)))
        (volume : Measure ℝ) := by
      rw [integrable_indicator_iff measurableSet_Ico]
      exact integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
    exact h1.mul_prod hη
  refine Integrable.mono' hI.integrableOn
    (UnforcedLeray.B0579.continuous_jb_rpow (-m)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (UnforcedLeray.B0579.measurableSet_cell c)] with x hx
  have hx1 : x.1 ∈ Ico (-(c / 2)) (c / 2) := hx.1
  have hjb : 1 + x.2 ^ 2 ≤ UnforcedLeray.B0579.jb x := by
    unfold UnforcedLeray.B0579.jb
    nlinarith [sq_nonneg x.1]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (UnforcedLeray.B0579.jb_pos x).le _),
    Set.indicator_of_mem hx1]
  have h1le : (1 : ℝ) ≤ 1 + x.2 ^ 2 := by nlinarith [sq_nonneg x.2]
  calc UnforcedLeray.B0579.jb x ^ (-m) ≤ (1 + x.2 ^ 2) ^ (-m) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hjb (by linarith)
    _ ≤ (1 + x.2 ^ 2) ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le h1le (by linarith)
    _ = 1 * (1 + x.2 ^ 2) ^ (-(1 : ℝ)) := by ring

theorem memLp_cellMeasure_neg_of_bdd {c : ℝ} {m : ℝ} (hm : 1 ≤ m) {g : ℝ × ℝ → ℝ}
    (hg : Continuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) :
    MemLp g 2 (UnforcedLeray.B0579.cellMeasure c (-m)) := by
  rw [UnforcedLeray.B0579.memLp_cellMeasure_iff]
  have hsq : MemLp (fun x => UnforcedLeray.B0579.jb x ^ (-m / 2)) 2
      (volume.restrict (UnforcedLeray.B0579.cell c)) := by
    refine (memLp_two_iff_integrable_sq
      (UnforcedLeray.B0579.continuous_jb_rpow _).aestronglyMeasurable).2 ?_
    refine (integrableOn_jb_rpow_neg_cell (c := c) m hm).congr_fun ?_
      (UnforcedLeray.B0579.measurableSet_cell c)
    intro x _
    show UnforcedLeray.B0579.jb x ^ (-m) = (UnforcedLeray.B0579.jb x ^ (-m / 2)) ^ 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul (UnforcedLeray.B0579.jb_pos x).le]
    norm_num
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine (hsq.const_mul M).mono ?_ ?_
  · exact ((UnforcedLeray.B0579.continuous_bracket_rpow (-m)).mul hg).aestronglyMeasurable
  · filter_upwards with x
    have hb : UnforcedLeray.B0579.bracket x ^ (-m) = UnforcedLeray.B0579.jb x ^ (-m / 2) :=
      UnforcedLeray.B0579.bracket_rpow (-m) x
    have hpos := Real.rpow_nonneg (UnforcedLeray.B0579.jb_pos x).le (-m / 2)
    have hgx := hM x
    show ‖UnforcedLeray.B0579.bracket x ^ (-m) * g x‖ ≤ ‖M * UnforcedLeray.B0579.jb x ^ (-m / 2)‖
    rw [hb, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hpos,
      abs_of_nonneg hM0]
    linarith [mul_le_mul_of_nonneg_left hgx hpos]

/-- A weighted flux `f ∈ X_{c,m}` times a bounded continuous function is integrable on the cell. -/
theorem integrableOn_mul_bdd_cont {c m : ℝ} (hm : 1 ≤ m) (f : UnforcedLeray.B0579.X c m)
    {g : ℝ × ℝ → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) :
    IntegrableOn (fun x => f x * g x) (UnforcedLeray.B0579.cell c) := by
  have hφ := memLp_cellMeasure_neg_of_bdd (c := c) hm hg hM
  have h := UnforcedLeray.B0579.integrableOn_mul_neg c m f (hφ.toLp g)
  have hae : (hφ.toLp g) =ᵐ[volume.restrict (UnforcedLeray.B0579.cell c)] g :=
    (UnforcedLeray.B0579.ac_cellMeasure c (-m)).ae_le hφ.coeFn_toLp
  refine h.congr_fun_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]

end UnforcedLeray.Short.IIIa.Exist
