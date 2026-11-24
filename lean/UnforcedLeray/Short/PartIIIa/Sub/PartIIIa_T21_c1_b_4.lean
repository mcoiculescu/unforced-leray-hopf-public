import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c1_b
import UnforcedLeray.Lib.Gaussian.Periodization

/-!
# Part III-a, `PartIII-a:T21/c1/b/4`: uniform dual bound of the periodized rows (SP 2894-2897)

Source: `the November 2 reference manuscript`, lines 2894-2897.

`perLam0Bound_meas`: for `m > 8` there is `K` such that for `d ≥ 1` and measurable `W` with
`‖W‖_{X_{m,d}} < ∞`, `Λ⁰_i W` is integrable on the cell and `|∫_cell Λ⁰_i W| ≤ K ‖W‖_{X_{m,d}}`.

Note (statement issue): `PerLam0Bound` quantifies over *all* `W` with `xNorm d m W ≠ ∞`, including
non-a.e.-measurable `W` (for which `xNorm` may be finite although `Λ⁰_i W` is not integrable).
The statement here adds the hypothesis `AEStronglyMeasurable W (volume.restrict (cell d))`.

Proof: `Λ⁰_i` is continuous and bounded by `B` on the cell uniformly in `d ≥ 1`
(`|y₁ + n d| ≥ |n|/2` for `n ≠ 0`), then Hölder `L²·L²→L¹` against the weight `jb^{m/2}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.Lam0B

/-- Measurable-`W` form of `PerLam0Bound`. -/
def PerLam0BoundM (κ : PlanarFrameKernels) : Prop :=
  ∀ m : ℝ, 8 < m → ∃ K : ℝ, ∀ d : ℝ, 1 ≤ d → ∀ (i : Fin 2) (W : ℝ × ℝ → ℂ),
    AEStronglyMeasurable W (volume.restrict (B0579.cell d)) →
    xNorm d m W ≠ ∞ →
      IntegrableOn (fun x => perLam0 κ d i x * W x) (B0579.cell d) ∧
      ENNReal.ofReal ‖∫ x in B0579.cell d, perLam0 κ d i x * W x‖ ≤
        ENNReal.ofReal K * xNorm d m W

lemma rpow_neg_two_eq (x : ℝ) (hx : 0 ≤ x) : x ^ (-(2 : ℝ)) = (x⁻¹) ^ 2 := by
  rw [Real.rpow_neg hx, Real.rpow_two, inv_pow]

lemma perLam0_eq (κ : PlanarFrameKernels) (d : ℝ) (i : Fin 2) :
    perLam0 κ d i = fun y => ∑' n : ℤ, κ.lamP i (y - Gaussian.shiftVec (-d) n) := by
  funext y
  unfold perLam0 perSum
  refine tsum_congr fun n => ?_
  congr 1
  ext <;> simp [Gaussian.shiftVec]

lemma lamP_translate_bound (κ : PlanarFrameKernels) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i z, ‖κ.lamP i z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC⟩ := κ.lamP_decay
  refine ⟨|C|, abs_nonneg C, fun i z => ?_⟩
  refine (hC i z).trans ?_
  rw [rpow_neg_two_eq _ (by positivity)]
  have h1 : (1 + |z.1| + |z.2|)⁻¹ ≤ (1 + |z.1|)⁻¹ :=
    inv_anti₀ (by positivity) (by linarith [abs_nonneg z.2])
  have h2 : ((1 + |z.1| + |z.2|)⁻¹) ^ 2 ≤ ((1 + |z.1|)⁻¹) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  calc C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 ≤ |C| * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * ((1 + |z.1|)⁻¹) ^ 2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)

theorem perLam0_continuous (κ : PlanarFrameKernels) {d : ℝ} (hd : 0 < d) (i : Fin 2) :
    Continuous (perLam0 κ d i) := by
  obtain ⟨C, -, hC⟩ := lamP_translate_bound κ
  rw [perLam0_eq]
  exact Gaussian.continuous_tsum_translates (κ.lamP_cont i) (s := 2) (c := -d) (C := C)
    (by norm_num) (by linarith) (fun z => hC i z)

/-- Uniform sup bound of the periodized dual rows on the cells with `d ≥ 1`. -/
theorem perLam0_sup (κ : PlanarFrameKernels) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ d : ℝ, 1 ≤ d → ∀ i : Fin 2, ∀ y ∈ B0579.cell d, ‖perLam0 κ d i y‖ ≤ B := by
  obtain ⟨C, hC0, hC⟩ := lamP_translate_bound κ
  have hs : Summable (fun n : ℤ => (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) :=
    Gaussian.summable_one_add_abs_int_rpow (by norm_num)
  have hsum : HasSum (fun n : ℤ => 4 * C * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)))
      (4 * C * ∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) := by
    have := (hs.hasSum).mul_left (4 * C)
    exact this
  refine ⟨4 * C * ∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-(2 : ℝ)), by
    have : 0 ≤ ∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) :=
      tsum_nonneg fun n => by positivity
    positivity, fun d hd i y hy => ?_⟩
  have hy1 : |y.1| ≤ d / 2 := by
    have h1 := hy.1.1
    have h2 := hy.1.2
    rw [abs_le]; constructor <;> linarith
  have hperm : perLam0 κ d i y = ∑' n : ℤ, κ.lamP i (y.1 + n * d, y.2) := rfl
  rw [hperm]
  refine tsum_of_norm_bounded hsum fun n => ?_
  refine (hC i _).trans ?_
  have hlow : (1 + |(n : ℝ)|) / 2 ≤ 1 + |y.1 + n * d| := by
    by_cases hn : n = 0
    · subst hn; simp
      linarith [abs_nonneg y.1]
    · have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        have := Int.one_le_abs hn
        exact_mod_cast this
      have h3 : |(n : ℝ) * d| ≤ |y.1 + n * d| + |y.1| := by
        have := abs_sub_le (y.1 + n * d) y.1 0
        have h4 : |(n : ℝ) * d| = |(y.1 + n * d) - y.1| := by congr 1; ring
        rw [h4]
        have := abs_sub (y.1 + n * d) y.1
        linarith
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < d)] at h3
      nlinarith [abs_nonneg (y.1 + n * d)]
  have hpos : 0 < (1 + |(n : ℝ)|) / 2 := by positivity
  have h5 : (1 + |y.1 + n * d|) ^ (-(2 : ℝ)) ≤ ((1 + |(n : ℝ)|) / 2) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hpos hlow (by norm_num)
  have h6 : ((1 + |(n : ℝ)|) / 2) ^ (-(2 : ℝ)) = 4 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by
    rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg (by positivity), Real.rpow_two]
    field_simp
    norm_num
  show C * (1 + |y.1 + n * d|) ^ (-(2 : ℝ)) ≤ 4 * C * (1 + |(n : ℝ)|) ^ (-(2 : ℝ))
  calc C * (1 + |y.1 + n * d|) ^ (-(2 : ℝ)) ≤ C * (4 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) := by
        rw [← h6]; exact mul_le_mul_of_nonneg_left h5 hC0
    _ = 4 * C * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by ring

lemma enorm_ofReal_cx (r : ℝ) : ‖((r : ℝ) : ℂ)‖ₑ = ‖r‖ₑ := by
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, Complex.nnnorm_real]

/-- Complex version of `B0579.eLpNorm_cellMeasure`. -/
theorem eLpNorm_cellMeasure_cx (c m : ℝ) (f : ℝ × ℝ → ℂ) :
    eLpNorm f 2 (B0579.cellMeasure c m) =
      eLpNorm (fun x => ((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * f x) 2
        (volume.restrict (B0579.cell c)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), B0579.cellMeasure,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (B0579.measurable_density m).coe_nnreal_ennreal
      (Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
  congr 1
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, enorm_mul, ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have h0 : 0 ≤ B0579.jb x ^ (m / 2) := Real.rpow_nonneg (B0579.jb_pos x).le _
  rw [enorm_ofReal_cx, mul_pow, Real.enorm_eq_ofReal h0, ← ENNReal.ofReal_pow h0,
    ← Real.rpow_natCast, ← Real.rpow_mul (B0579.jb_pos x).le]
  have : m / 2 * ((2 : ℕ) : ℝ) = m := by push_cast; ring
  rw [this]
  rfl

lemma jb_ge_one (x : ℝ × ℝ) : 1 ≤ B0579.jb x := by
  unfold B0579.jb; nlinarith [sq_nonneg x.1, sq_nonneg x.2]

lemma one_add_norm_sq_le_jb (x : ℝ × ℝ) : 1 + ‖x‖ ^ 2 ≤ B0579.jb x := by
  have h1 : ‖x.1‖ ^ 2 = x.1 ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  have h2 : ‖x.2‖ ^ 2 = x.2 ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  have hn : ‖x‖ ^ 2 ≤ x.1 ^ 2 + x.2 ^ 2 := by
    rw [Prod.norm_def]
    rcases le_total ‖x.1‖ ‖x.2‖ with h | h
    · rw [max_eq_right h, h2]
      nlinarith [sq_nonneg x.1]
    · rw [max_eq_left h, h1]
      nlinarith [sq_nonneg x.2]
  unfold B0579.jb
  linarith

theorem integrable_jb_neg_two : Integrable (fun y : ℝ × ℝ => B0579.jb y ^ (-(2 : ℝ))) := by
  have hd : ((Module.finrank ℝ (ℝ × ℝ) : ℕ) : ℝ) = 2 := by simp
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ × ℝ) (μ := volume) (r := 2 * 2)
    (by rw [hd]; norm_num)
  have hexp : -((2 : ℝ) * 2) / 2 = -(2 : ℝ) := by norm_num
  rw [hexp] at h
  refine Integrable.mono' h (B0579.continuous_jb_rpow _).aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (B0579.jb_pos y).le _)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (one_add_norm_sq_le_jb y) (by norm_num)

theorem perLam0BoundM (κ : PlanarFrameKernels) : PerLam0BoundM κ := by
  intro m hm
  obtain ⟨B, hB0, hB⟩ := perLam0_sup κ
  set G : ℝ × ℝ → ℝ := fun y => B * B0579.jb y ^ ((m) / 2 * (-1)) with hG
  have hGmem : MemLp G 2 volume := by
    have hcont : Continuous G :=
      continuous_const.mul (B0579.continuous_jb_rpow _)
    refine (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 ?_
    refine (integrable_jb_neg_two.const_mul (B ^ 2)).mono'
      (hcont.pow 2).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    have hj0 : 0 ≤ B0579.jb y := (B0579.jb_pos y).le
    have e1 : (B0579.jb y ^ (m / 2 * (-1))) ^ 2 = B0579.jb y ^ (-m) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hj0]
      congr 1; push_cast; ring
    have e2 : B0579.jb y ^ (-m) ≤ B0579.jb y ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (jb_ge_one y) (by linarith)
    rw [Real.norm_of_nonneg (sq_nonneg _), hG]
    simp only
    rw [mul_pow, e1]
    exact mul_le_mul_of_nonneg_left e2 (sq_nonneg _)
  set K : ℝ := (eLpNorm G 2 volume).toReal with hK
  have hGfin : eLpNorm G 2 volume ≠ ⊤ := hGmem.2.ne
  refine ⟨K, fun d hd i W hWm hW => ?_⟩
  have hd0 : 0 < d := by linarith
  set F := perLam0 κ d i with hF
  have hFc : Continuous F := perLam0_continuous κ hd0 i
  have hAmem : MemLp (fun y => ((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * W y) 2
      (volume.restrict (B0579.cell d)) := by
    have hcont : Continuous fun y : ℝ × ℝ => ((B0579.jb y ^ (m / 2) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (B0579.continuous_jb_rpow _)
    refine ⟨hcont.aestronglyMeasurable.mul hWm, ?_⟩
    rw [← eLpNorm_cellMeasure_cx]
    exact lt_top_iff_ne_top.2 hW
  have hAnorm : eLpNorm (fun y => ((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * W y) 2
      (volume.restrict (B0579.cell d)) = xNorm d m W := by
    rw [← eLpNorm_cellMeasure_cx]
    rfl
  have hGr : MemLp G 2 (volume.restrict (B0579.cell d)) := hGmem.restrict _
  have hGnn : ∀ y, 0 ≤ G y := fun y =>
    mul_nonneg hB0 (Real.rpow_nonneg (B0579.jb_pos y).le _)
  -- pointwise domination
  have hpt : ∀ y ∈ B0579.cell d, ‖F y * W y‖ ≤
      ‖((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * W y * ((G y : ℝ) : ℂ)‖ := by
    intro y hy
    have h1 := hB d hd i y hy
    have hj : B0579.jb y ^ (m / 2) * B0579.jb y ^ (m / 2 * (-1)) = 1 := by
      rw [← Real.rpow_add (B0579.jb_pos y)]
      simp
    have hj0 : 0 ≤ B0579.jb y ^ (m / 2) := Real.rpow_nonneg (B0579.jb_pos y).le _
    rw [norm_mul (F y), norm_mul (((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * W y),
      norm_mul ((( B0579.jb y ^ (m / 2) : ℝ) : ℂ)), Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hj0, Real.norm_of_nonneg (hGnn y)]
    have : B0579.jb y ^ (m / 2) * ‖W y‖ * G y = B * ‖W y‖ := by
      simp only [hG]
      calc B0579.jb y ^ (m / 2) * ‖W y‖ * (B * B0579.jb y ^ (m / 2 * (-1)))
          = (B0579.jb y ^ (m / 2) * B0579.jb y ^ (m / 2 * (-1))) * (B * ‖W y‖) := by ring
        _ = B * ‖W y‖ := by rw [hj, one_mul]
    rw [this]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have hHold := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
    (f := fun y => ((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * W y)
    (g := G)
    (p := 2) (q := 2) (r := 1) hAmem.1 hGr.1
    (fun z t => z * ((t : ℝ) : ℂ)) 1
    (Eventually.of_forall fun y => by
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hGnn y), NNReal.coe_one,
        one_mul, le_refl])
  have hHold' : eLpNorm (fun y => ((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * W y *
      ((G y : ℝ) : ℂ)) 1 (volume.restrict (B0579.cell d)) ≤
      eLpNorm (fun y => ((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * W y) 2
        (volume.restrict (B0579.cell d)) * eLpNorm G 2 (volume.restrict (B0579.cell d)) := by
    simpa using hHold
  have hL1 : eLpNorm (fun y => F y * W y) 1 (volume.restrict (B0579.cell d)) ≤
      ENNReal.ofReal K * xNorm d m W := by
    calc _ ≤ eLpNorm (fun y => ((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * W y *
            ((G y : ℝ) : ℂ)) 1 (volume.restrict (B0579.cell d)) :=
          eLpNorm_mono_ae (ae_restrict_of_forall_mem (B0579.measurableSet_cell d) hpt)
      _ ≤ _ := hHold'
      _ = eLpNorm G 2 (volume.restrict (B0579.cell d)) * xNorm d m W := by
          rw [hAnorm, mul_comm]
      _ ≤ ENNReal.ofReal K * xNorm d m W := by
          gcongr
          calc eLpNorm G 2 (volume.restrict (B0579.cell d)) ≤ eLpNorm G 2 volume :=
                eLpNorm_mono_measure _ Measure.restrict_le_self
            _ = ENNReal.ofReal K := (ENNReal.ofReal_toReal hGfin).symm
  have hsrcAE : AEStronglyMeasurable (fun y => F y * W y) (volume.restrict (B0579.cell d)) :=
    hFc.aestronglyMeasurable.mul hWm
  have hlt : eLpNorm (fun y => F y * W y) 1 (volume.restrict (B0579.cell d)) < ⊤ :=
    lt_of_le_of_lt hL1 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hW))
  have hint : IntegrableOn (fun y => F y * W y) (B0579.cell d) :=
    memLp_one_iff_integrable.1 ⟨hsrcAE, hlt⟩
  refine ⟨hint, ?_⟩
  rw [ofReal_norm]
  calc ‖∫ x in B0579.cell d, F x * W x‖ₑ ≤ ∫⁻ x in B0579.cell d, ‖F x * W x‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun y => F y * W y) 1 (volume.restrict (B0579.cell d)) :=
        (eLpNorm_one_eq_lintegral_enorm).symm
    _ ≤ _ := hL1

end UnforcedLeray.Short.IIIa.Lam0B
