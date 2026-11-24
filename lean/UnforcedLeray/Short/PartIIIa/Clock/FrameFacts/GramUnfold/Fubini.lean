import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts.GramTail.Bound
import UnforcedLeray.Lib.Cylinder.Basic
import UnforcedLeray.Lib.Gaussian.LatticeSum
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Part III-a, helpers for `PartIII-a:T21/c1/b/1`: unfolding the Gram entry (SP 2894-2895)

* `integral_bcell_perSum`: `∫_{cell d} P_d F = ∫_{ℝ²} F` for integrable `F` (centred cell),
  from `Gaussian.integral_cell_periodize` and `Cyl.integral_strip_eq_cell`;
* `gramCross_int`: the planar cross integrals `λ_i(y) e_j(y₁ + a, y₂)` are integrable with
  `∫ ‖·‖ ≤ K/(1+|a|)²` (norm version of `gramCross_bound`);
* `summable_cross_bound`, `summable_e_shift`, `measurable_perSum`: summability and measurability
  of the lattice sums.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace UnforcedLeray.Short.IIIa

theorem perSum_eq_periodize (d : ℝ) (f : ℝ × ℝ → ℂ) (z : ℝ × ℝ) :
    perSum d f z = UnforcedLeray.Gaussian.periodize d f z := by
  unfold perSum UnforcedLeray.Gaussian.periodize
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  simp [sub_eq_add_neg]

/-- `P_d E` is `d`-periodic in the first variable, at every integer multiple. -/
theorem perSum_int_period (d : ℝ) (f : ℝ × ℝ → ℂ) (n : ℤ) (x : ℝ × ℝ) :
    perSum d f (x.1 + (n : ℝ) * d, x.2) = perSum d f x := by
  have h := ((UnforcedLeray.Gaussian.periodic_periodize d f x.2).int_mul n) x.1
  simp only [perSum_eq_periodize]
  simpa using h

theorem integral_bcell_perSum {F : ℝ × ℝ → ℂ} (hF : Integrable F) {d : ℝ} (hd : 0 < d) :
    ∫ x in B0579.cell d, perSum d F x = ∫ y, F y := by
  have hper : UnforcedLeray.Cyl.IsPeriodic d (perSum d F) := by
    intro z
    simp only [perSum_eq_periodize]
    exact UnforcedLeray.Gaussian.periodic_periodize d F z.2 z.1
  have hcell : B0579.cell d = UnforcedLeray.Cyl.cell d := by
    unfold B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  have h1 := UnforcedLeray.Cyl.integral_strip_eq_cell hd hper 0
  have h2 := UnforcedLeray.Gaussian.integral_cell_periodize hF hd
  rw [hcell, ← h1, zero_add]
  simp only [perSum_eq_periodize]
  exact h2

theorem gramCross_int (κ : PlanarFrameKernels) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i j : Fin 2) (a : ℝ),
      Integrable (fun y : ℝ × ℝ => κ.lamP i y * κ.e j (y.1 + a, y.2)) ∧
      ∫ y : ℝ × ℝ, ‖κ.lamP i y * κ.e j (y.1 + a, y.2)‖ ≤ K / (1 + |a|) ^ 2 := by
  obtain ⟨C1, hC1⟩ := κ.lamP_decay
  obtain ⟨C2, hC2⟩ := κ.e_decay
  refine ⟨|C1| * |C2| * (2080 * Real.pi), by positivity, fun i j a => ?_⟩
  have hA : 0 ≤ |C1| * |C2| := by positivity
  have hpt : ∀ y : ℝ × ℝ, ‖κ.lamP i y * κ.e j (y.1 + a, y.2)‖ ≤
      (|C1| * |C2|) * (4 / (1 + |a|) ^ 2 * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
        Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4))) := by
    intro y
    rw [norm_mul]
    have h1 : ‖κ.lamP i y‖ ≤ |C1| * (1 + |y.1| + |y.2|)⁻¹ ^ 2 :=
      (hC1 i y).trans (mul_le_mul_of_nonneg_right (le_abs_self C1) (by positivity))
    have h2 : ‖κ.e j (y.1 + a, y.2)‖ ≤
        |C2| * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) := by
      have h := hC2 j (y.1 + a, y.2)
      have hh : Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / 8) =
          Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) := by norm_num
      refine h.trans ?_
      dsimp only
      rw [hh]
      exact mul_le_mul_of_nonneg_right (le_abs_self C2) (Real.exp_pos _).le
    calc ‖κ.lamP i y‖ * ‖κ.e j (y.1 + a, y.2)‖
        ≤ (|C1| * (1 + |y.1| + |y.2|)⁻¹ ^ 2) *
            (|C2| * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = (|C1| * |C2|) * ((1 + |y.1| + |y.2|)⁻¹ ^ 2 *
            Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2))) := by ring
      _ ≤ (|C1| * |C2|) * (4 / (1 + |a|) ^ 2 *
            Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
            Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4))) :=
          mul_le_mul_of_nonneg_left (gram_pt a y.1 y.2) hA
  have G8 := integrable_shift_gauss (c := a) (t := 2) (by norm_num)
  have G16 := integrable_shift_gauss (c := a) (t := 4) (by norm_num)
  have hint : Integrable (fun y : ℝ × ℝ => (|C1| * |C2|) *
      (4 / (1 + |a|) ^ 2 * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
        Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4)))) :=
    ((G8.const_mul (4 / (1 + |a|) ^ 2)).add
      (G16.const_mul (Real.exp (-a ^ 2 / (4 * 16))))).const_mul _
  have hcont : Continuous (fun y : ℝ × ℝ => κ.lamP i y * κ.e j (y.1 + a, y.2)) :=
    (κ.lamP_cont i).mul ((κ.e_cont j).comp (by fun_prop))
  refine ⟨Integrable.mono' hint hcont.aestronglyMeasurable (Filter.Eventually.of_forall hpt), ?_⟩
  have hE := exp_neg_sq_mul_le a
  have hE' : Real.exp (-a ^ 2 / (4 * 16)) ≤ 128 / (1 + |a|) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  calc ∫ y : ℝ × ℝ, ‖κ.lamP i y * κ.e j (y.1 + a, y.2)‖
      ≤ ∫ y : ℝ × ℝ, (|C1| * |C2|) *
          (4 / (1 + |a|) ^ 2 * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
            Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4))) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _) hint
          (Filter.Eventually.of_forall hpt)
    _ = (|C1| * |C2|) * (4 / (1 + |a|) ^ 2 * (4 * Real.pi * 2) +
          Real.exp (-a ^ 2 / (4 * 16)) * (4 * Real.pi * 4)) := by
        rw [integral_const_mul, integral_add (G8.const_mul _) (G16.const_mul _),
          integral_const_mul, integral_const_mul,
          integral_shift_gauss (c := a) (t := 2) (by norm_num),
          integral_shift_gauss (c := a) (t := 4) (by norm_num)]
    _ ≤ (|C1| * |C2|) * (4 / (1 + |a|) ^ 2 * (4 * Real.pi * 2) +
          128 / (1 + |a|) ^ 2 * (4 * Real.pi * 4)) := by
        gcongr
    _ = |C1| * |C2| * (2080 * Real.pi) / (1 + |a|) ^ 2 := by ring

theorem summable_cross_bound {K d : ℝ} (hd : 0 < d) :
    Summable (fun k : ℤ => K / (1 + |(k : ℝ) * d|) ^ 2) := by
  have hS : Summable (fun k : ℤ => 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  refine Summable.of_norm_bounded_eventually (hS.mul_left (|K| / d ^ 2)) ?_
  filter_upwards [eventually_cofinite_ne 0] with k hk
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hkd : 0 < ((k : ℝ) * d) ^ 2 := by
    have : (k : ℝ) * d ≠ 0 := mul_ne_zero hkR hd.ne'
    positivity
  have hpos : 0 < (1 + |(k : ℝ) * d|) ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
  calc |K| / (1 + |(k : ℝ) * d|) ^ 2 ≤ |K| / ((k : ℝ) * d) ^ 2 :=
        div_le_div_of_nonneg_left (abs_nonneg K) hkd
          (by nlinarith [sq_abs ((k : ℝ) * d), abs_nonneg ((k : ℝ) * d)])
    _ = |K| / d ^ 2 * (1 / (k : ℝ) ^ 2) := by field_simp

theorem summable_e_shift (κ : PlanarFrameKernels) {d : ℝ} (hd : 0 < d) (j : Fin 2)
    (y : ℝ × ℝ) : Summable (fun n : ℤ => ‖κ.e j (y.1 + n * d, y.2)‖) := by
  obtain ⟨C, hC⟩ := κ.e_decay
  have hs := (UnforcedLeray.Gaussian.summable_translate (s := 2) (c := -d) (by norm_num)
    (neg_ne_zero.2 hd.ne') y.1).mul_left (|C| * 128)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hs
  have h1 := hC j (y.1 + n * d, y.2)
  have hq : y.1 - (n : ℝ) * (-d) = y.1 + n * d := by ring
  rw [hq]
  generalize y.1 + (n : ℝ) * d = s at h1 ⊢
  have hE := exp_neg_sq_mul_le s
  have hpos : 0 < (1 + |s|) ^ 2 := by positivity
  have hE' : Real.exp (-s ^ 2 / (4 * 16)) ≤ 128 / (1 + |s|) ^ 2 := by
    rw [le_div_iff₀ hpos]; linarith
  have h2 : Real.exp (-(s ^ 2 + y.2 ^ 2) / 8) ≤ Real.exp (-s ^ 2 / (4 * 16)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg y.2, sq_nonneg s]
  have hr : (1 + |s|) ^ (-(2 : ℝ)) = 1 / (1 + |s|) ^ 2 := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two, one_div]
  rw [hr]
  calc ‖κ.e j (s, y.2)‖ ≤ C * Real.exp (-(s ^ 2 + y.2 ^ 2) / 8) := h1
    _ ≤ |C| * Real.exp (-(s ^ 2 + y.2 ^ 2) / 8) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    _ ≤ |C| * (128 / (1 + |s|) ^ 2) :=
        mul_le_mul_of_nonneg_left (h2.trans hE') (abs_nonneg C)
    _ = |C| * 128 * (1 / (1 + |s|) ^ 2) := by ring

theorem measurable_perSum {g : ℝ × ℝ → ℂ} (hg : Continuous g) {d : ℝ}
    (hs : ∀ y : ℝ × ℝ, Summable (fun n : ℤ => g (y.1 + n * d, y.2))) :
    Measurable (perSum d g) := by
  have hmeas : ∀ s : Finset ℤ, Measurable (fun y : ℝ × ℝ => ∑ n ∈ s, g (y.1 + n * d, y.2)) :=
    fun s => Finset.measurable_sum _ fun n _ => (hg.comp (by fun_prop)).measurable
  refine measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset ℤ)) hmeas ?_
  rw [tendsto_pi_nhds]
  intro y
  exact (hs y).hasSum

end UnforcedLeray.Short.IIIa
