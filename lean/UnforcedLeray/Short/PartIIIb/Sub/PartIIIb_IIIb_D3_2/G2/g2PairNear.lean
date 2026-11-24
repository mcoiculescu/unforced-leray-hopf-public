import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G2Org
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts.GramUnfold
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts.GramTail

/-!
# `PartIII-b:IIIb-D3/2/G2/3`: `g2PairNear` (Gram-normalized periodized dual rows, SP 2894-2912)
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G2

private theorem periodizeC_eq_perSum (d : ℝ) (g : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    IIIa.periodizeC d g y = IIIa.perSum d g y := by
  unfold IIIa.periodizeC IIIa.perSum
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  simp [sub_eq_add_neg]

private theorem integrableOn_bcell_perSum {F : ℝ × ℝ → ℂ} (hF : Integrable F) {d : ℝ} (hd : 0 < d)
    (hm : AEStronglyMeasurable (IIIa.perSum d F) (volume.restrict (B0579.cell d))) :
    IntegrableOn (IIIa.perSum d F) (B0579.cell d) := by
  refine ⟨hm, ?_⟩
  have hper : UnforcedLeray.Cyl.IsPeriodic d (fun z => ‖IIIa.perSum d F z‖ₑ) := fun z => by
    simp only [IIIa.perSum_eq_periodize]
    exact congrArg (fun w => ‖w‖ₑ) (UnforcedLeray.Gaussian.periodic_periodize d F z.2 z.1)
  have hcell : B0579.cell d = UnforcedLeray.Cyl.cell d := by
    unfold B0579.cell UnforcedLeray.Cyl.cell; rw [neg_div]
  have h1 := UnforcedLeray.Cyl.lintegral_strip_eq_cell hd hper 0
  rw [HasFiniteIntegral, hcell, ← h1, zero_add]
  have hmeas : ∀ n : ℤ,
      AEMeasurable (fun z : ℝ × ℝ => ‖F (z - UnforcedLeray.Gaussian.shiftVec d n)‖ₑ)
        (volume.restrict (UnforcedLeray.Gaussian.cell d)) :=
    fun n => (hF.comp_sub_right (UnforcedLeray.Gaussian.shiftVec d n)).aestronglyMeasurable.restrict.enorm
  calc ∫⁻ z in UnforcedLeray.Gaussian.cell d, ‖IIIa.perSum d F z‖ₑ
      ≤ ∫⁻ z in UnforcedLeray.Gaussian.cell d,
          ∑' n : ℤ, ‖F (z - UnforcedLeray.Gaussian.shiftVec d n)‖ₑ := by
        refine lintegral_mono fun z => ?_
        rw [IIIa.perSum_eq_periodize, UnforcedLeray.Gaussian.periodize_eq]
        exact enorm_tsum_le_tsum_enorm
    _ = ∑' n : ℤ, ∫⁻ z in UnforcedLeray.Gaussian.cell d,
          ‖F (z - UnforcedLeray.Gaussian.shiftVec d n)‖ₑ :=
        lintegral_tsum hmeas
    _ = ∫⁻ w, ‖F w‖ₑ := UnforcedLeray.Gaussian.tsum_setLIntegral_cell_translate (fun w => ‖F w‖ₑ) hd
    _ < ⊤ := hF.2

private theorem gCross_int (κ : IIIa.PlanarFrameKernels) {g : ℝ × ℝ → ℂ} (hg : Continuous g)
    {C2 : ℝ} (hC2 : ∀ y : ℝ × ℝ, ‖g y‖ ≤ C2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin 2) (a : ℝ),
      Integrable (fun y : ℝ × ℝ => κ.lamP i y * g (y.1 + a, y.2)) ∧
      ∫ y : ℝ × ℝ, ‖κ.lamP i y * g (y.1 + a, y.2)‖ ≤ K / (1 + |a|) ^ 2 := by
  obtain ⟨C1, hC1⟩ := κ.lamP_decay
  refine ⟨|C1| * |C2| * (2080 * Real.pi), by positivity, fun i a => ?_⟩
  have hA : 0 ≤ |C1| * |C2| := by positivity
  have hpt : ∀ y : ℝ × ℝ, ‖κ.lamP i y * g (y.1 + a, y.2)‖ ≤
      (|C1| * |C2|) * (4 / (1 + |a|) ^ 2 * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
        Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4))) := by
    intro y
    rw [norm_mul]
    have h1 : ‖κ.lamP i y‖ ≤ |C1| * (1 + |y.1| + |y.2|)⁻¹ ^ 2 :=
      (hC1 i y).trans (mul_le_mul_of_nonneg_right (le_abs_self C1) (by positivity))
    have h2 : ‖g (y.1 + a, y.2)‖ ≤
        |C2| * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) := by
      have h := hC2 (y.1 + a, y.2)
      have hh : Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / 8) =
          Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) := by norm_num
      refine h.trans ?_
      dsimp only
      rw [hh]
      exact mul_le_mul_of_nonneg_right (le_abs_self C2) (Real.exp_pos _).le
    calc ‖κ.lamP i y‖ * ‖g (y.1 + a, y.2)‖
        ≤ (|C1| * (1 + |y.1| + |y.2|)⁻¹ ^ 2) *
            (|C2| * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = (|C1| * |C2|) * ((1 + |y.1| + |y.2|)⁻¹ ^ 2 *
            Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2))) := by ring
      _ ≤ (|C1| * |C2|) * (4 / (1 + |a|) ^ 2 *
            Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
            Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4))) :=
          mul_le_mul_of_nonneg_left (IIIa.gram_pt a y.1 y.2) hA
  have G8 := IIIa.integrable_shift_gauss (c := a) (t := 2) (by norm_num)
  have G16 := IIIa.integrable_shift_gauss (c := a) (t := 4) (by norm_num)
  have hint : Integrable (fun y : ℝ × ℝ => (|C1| * |C2|) *
      (4 / (1 + |a|) ^ 2 * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
        Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4)))) :=
    ((G8.const_mul (4 / (1 + |a|) ^ 2)).add
      (G16.const_mul (Real.exp (-a ^ 2 / (4 * 16))))).const_mul _
  have hcont : Continuous (fun y : ℝ × ℝ => κ.lamP i y * g (y.1 + a, y.2)) :=
    (κ.lamP_cont i).mul (hg.comp (by fun_prop))
  refine ⟨Integrable.mono' hint hcont.aestronglyMeasurable (Filter.Eventually.of_forall hpt), ?_⟩
  have hE := IIIa.exp_neg_sq_mul_le a
  have hE' : Real.exp (-a ^ 2 / (4 * 16)) ≤ 128 / (1 + |a|) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  calc ∫ y : ℝ × ℝ, ‖κ.lamP i y * g (y.1 + a, y.2)‖
      ≤ ∫ y : ℝ × ℝ, (|C1| * |C2|) *
          (4 / (1 + |a|) ^ 2 * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
            Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4))) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _) hint
          (Filter.Eventually.of_forall hpt)
    _ = (|C1| * |C2|) * (4 / (1 + |a|) ^ 2 * (4 * Real.pi * 2) +
          Real.exp (-a ^ 2 / (4 * 16)) * (4 * Real.pi * 4)) := by
        rw [integral_const_mul, integral_add (G8.const_mul _) (G16.const_mul _),
          integral_const_mul, integral_const_mul,
          IIIa.integral_shift_gauss (c := a) (t := 2) (by norm_num),
          IIIa.integral_shift_gauss (c := a) (t := 4) (by norm_num)]
    _ ≤ (|C1| * |C2|) * (4 / (1 + |a|) ^ 2 * (4 * Real.pi * 2) +
          128 / (1 + |a|) ^ 2 * (4 * Real.pi * 4)) := by
        gcongr
    _ = |C1| * |C2| * (2080 * Real.pi) / (1 + |a|) ^ 2 := by ring

private theorem summable_g_shift {g : ℝ × ℝ → ℂ} {C : ℝ}
    (hC : ∀ y : ℝ × ℝ, ‖g y‖ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8))
    {d : ℝ} (hd : 0 < d) (y : ℝ × ℝ) :
    Summable (fun n : ℤ => ‖g (y.1 + n * d, y.2)‖) := by
  have hs := (UnforcedLeray.Gaussian.summable_translate (s := 2) (c := -d) (by norm_num)
    (neg_ne_zero.2 hd.ne') y.1).mul_left (|C| * 128)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hs
  have h1 := hC (y.1 + n * d, y.2)
  have hq : y.1 - (n : ℝ) * (-d) = y.1 + n * d := by ring
  rw [hq]
  generalize y.1 + (n : ℝ) * d = s at h1 ⊢
  have hE := IIIa.exp_neg_sq_mul_le s
  have hpos : 0 < (1 + |s|) ^ 2 := by positivity
  have hE' : Real.exp (-s ^ 2 / (4 * 16)) ≤ 128 / (1 + |s|) ^ 2 := by
    rw [le_div_iff₀ hpos]; linarith
  have h2 : Real.exp (-(s ^ 2 + y.2 ^ 2) / 8) ≤ Real.exp (-s ^ 2 / (4 * 16)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg y.2, sq_nonneg s]
  have hr : (1 + |s|) ^ (-(2 : ℝ)) = 1 / (1 + |s|) ^ 2 := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two, one_div]
  rw [hr]
  calc ‖g (s, y.2)‖ ≤ C * Real.exp (-(s ^ 2 + y.2 ^ 2) / 8) := h1
    _ ≤ |C| * Real.exp (-(s ^ 2 + y.2 ^ 2) / 8) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    _ ≤ |C| * (128 / (1 + |s|) ^ 2) :=
        mul_le_mul_of_nonneg_left (h2.trans hE') (abs_nonneg C)
    _ = |C| * 128 * (1 / (1 + |s|) ^ 2) := by ring

private theorem gPair0_unfold (κ : IIIa.PlanarFrameKernels) {g : ℝ × ℝ → ℂ} (hg : Continuous g)
    {C2 : ℝ} (hC2 : ∀ y : ℝ × ℝ, ‖g y‖ ≤ C2 * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :
    ∃ C0 K0 : ℝ, 0 ≤ C0 ∧ 0 ≤ K0 ∧
      (∀ j : Fin 2, ‖∫ y, κ.lamP j y * g y‖ ≤ K0) ∧
      ∀ d : ℝ, 1 ≤ d → ∀ j : Fin 2,
        IntegrableOn (fun x => IIIa.perLam0 κ d j x * IIIa.perSum d g x) (B0579.cell d) ∧
        ‖(∫ x in B0579.cell d, IIIa.perLam0 κ d j x * IIIa.perSum d g x) -
            ∫ y, κ.lamP j y * g y‖ ≤ C0 * d⁻¹ ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := gCross_int κ hg hC2
  have hS : Summable (fun k : ℤ => 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have hS0 : 0 ≤ ∑' k : ℤ, 1 / (k : ℝ) ^ 2 := tsum_nonneg fun k => by positivity
  refine ⟨K * ∑' k : ℤ, 1 / (k : ℝ) ^ 2, K, by positivity, hK0, fun j => ?_, fun d hd j => ?_⟩
  · have h0 := (hK j 0).2
    simp only [add_zero, abs_zero, one_pow, div_one] at h0
    exact (norm_integral_le_integral_norm _).trans h0
  · have hdpos : 0 < d := by linarith
    set Fk : ℤ → ℝ × ℝ → ℂ := fun k y => κ.lamP j y * g (y.1 + (k : ℝ) * d, y.2) with hFk
    set gt : ℤ → ℂ := fun k => ∫ y, Fk k y with hgt
    have hint : ∀ k, Integrable (Fk k) := fun k => (hK j ((k : ℝ) * d)).1
    have hnorm : ∀ k, ∫ y, ‖Fk k y‖ ≤ K / (1 + |(k : ℝ) * d|) ^ 2 := fun k =>
      (hK j ((k : ℝ) * d)).2
    have hb := IIIa.summable_cross_bound (K := K) hdpos
    have hsumI : Summable (fun k => ∫ y, ‖Fk k y‖) :=
      Summable.of_nonneg_of_le (fun k => integral_nonneg fun y => norm_nonneg _) hnorm hb
    have hsum : Summable gt :=
      hsumI.of_norm_bounded fun k => norm_integral_le_integral_norm _
    have hPgSum : ∀ y : ℝ × ℝ, Summable (fun n : ℤ => g (y.1 + n * d, y.2)) := fun y =>
      (summable_g_shift hC2 hdpos y).of_norm
    have hPgMeas : Measurable (IIIa.perSum d g) := IIIa.measurable_perSum hg hPgSum
    have hFsum : ∀ y, κ.lamP j y * IIIa.perSum d g y = ∑' k : ℤ, Fk k y := by
      intro y
      simp only [IIIa.perSum, hFk]
      exact tsum_mul_left.symm
    have hlin : ∀ k, ∫⁻ y, ‖Fk k y‖ₑ = ENNReal.ofReal (∫ y, ‖Fk k y‖) := fun k =>
      (ofReal_integral_norm_eq_lintegral_enorm (hint k)).symm
    have hsumL : ∑' k, ∫⁻ y, ‖Fk k y‖ₑ ≠ ⊤ := by
      simp_rw [hlin]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => integral_nonneg fun y => norm_nonneg _) hsumI]
      exact ENNReal.ofReal_ne_top
    have hmeasF : ∀ k, AEStronglyMeasurable (Fk k) volume := fun k => (hint k).1
    have hInt : Integrable (fun y => ∑' k, Fk k y) := by
      refine ⟨?_, ?_⟩
      · have : (fun y => ∑' k, Fk k y) = fun y => κ.lamP j y * IIIa.perSum d g y :=
          funext fun y => (hFsum y).symm
        rw [this]
        exact ((κ.lamP_cont j).measurable.mul hPgMeas).aestronglyMeasurable
      · calc ∫⁻ y, ‖∑' k, Fk k y‖ₑ ≤ ∫⁻ y, ∑' k, ‖Fk k y‖ₑ :=
              lintegral_mono fun y => enorm_tsum_le_tsum_enorm
          _ = ∑' k, ∫⁻ y, ‖Fk k y‖ₑ := lintegral_tsum (fun k => (hmeasF k).enorm)
          _ < ⊤ := lt_top_iff_ne_top.2 hsumL
    have h1 : ∀ x : ℝ × ℝ,
        IIIa.perLam0 κ d j x * IIIa.perSum d g x = IIIa.perSum d (fun y => ∑' k, Fk k y) x := by
      intro x
      simp only [IIIa.perLam0, IIIa.perSum]
      rw [← tsum_mul_right]
      refine tsum_congr fun n => ?_
      rw [← hFsum]
      congr 1
      exact (IIIa.perSum_int_period d g n x).symm
    have hfeq : (fun x => IIIa.perLam0 κ d j x * IIIa.perSum d g x) =
        IIIa.perSum d (fun y => ∑' k, Fk k y) := funext h1
    have hm_cell : AEStronglyMeasurable (IIIa.perSum d (fun y => ∑' k, Fk k y))
        (volume.restrict (B0579.cell d)) := by
      rw [← hfeq]
      exact ((IIIa.FrameCont.perLam0_continuous κ hdpos j).measurable.mul hPgMeas).aestronglyMeasurable
    have hIntCell : IntegrableOn (fun x => IIIa.perLam0 κ d j x * IIIa.perSum d g x)
        (B0579.cell d) := by
      rw [hfeq]
      exact integrableOn_bcell_perSum hInt hdpos hm_cell
    have hcell : (∫ x in B0579.cell d, IIIa.perLam0 κ d j x * IIIa.perSum d g x) =
        ∑' k : ℤ, gt k := by
      rw [hfeq, IIIa.integral_bcell_perSum hInt hdpos, integral_tsum hmeasF hsumL]
    refine ⟨hIntCell, ?_⟩
    have hsplit := hsum.tsum_eq_add_tsum_ite 0
    have h0 : gt 0 = ∫ y, κ.lamP j y * g y := by
      simp only [hgt, hFk, Int.cast_zero, zero_mul, add_zero]
    have hrest : (∫ x in B0579.cell d, IIIa.perLam0 κ d j x * IIIa.perSum d g x) -
        (∫ y, κ.lamP j y * g y) = ∑' k : ℤ, (if k = 0 then (0 : ℂ) else gt k) := by
      rw [hcell, hsplit, h0, add_sub_cancel_left]
    rw [hrest]
    have hterm : ∀ k : ℤ, ‖(if k = 0 then (0 : ℂ) else gt k)‖ ≤
        K / d ^ 2 * (1 / (k : ℝ) ^ 2) := by
      intro k
      by_cases hk : k = 0
      · subst hk; simp
      · simp only [hk, ite_false]
        have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
        have hkd : (0 : ℝ) < ((k : ℝ) * d) ^ 2 := by
          have : (k : ℝ) * d ≠ 0 := mul_ne_zero hkR hdpos.ne'
          positivity
        calc ‖gt k‖ ≤ ∫ y, ‖Fk k y‖ := norm_integral_le_integral_norm _
          _ ≤ K / (1 + |(k : ℝ) * d|) ^ 2 := hnorm k
          _ ≤ K / ((k : ℝ) * d) ^ 2 := by
              apply div_le_div_of_nonneg_left hK0 hkd
              nlinarith [sq_abs ((k : ℝ) * d), abs_nonneg ((k : ℝ) * d)]
          _ = K / d ^ 2 * (1 / (k : ℝ) ^ 2) := by field_simp
    have hnormS : Summable (fun k : ℤ => ‖(if k = 0 then (0 : ℂ) else gt k)‖) :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) hterm (hS.mul_left _)
    calc ‖∑' k : ℤ, (if k = 0 then (0 : ℂ) else gt k)‖
        ≤ ∑' k : ℤ, ‖(if k = 0 then (0 : ℂ) else gt k)‖ := norm_tsum_le_tsum_norm hnormS
      _ ≤ ∑' k : ℤ, K / d ^ 2 * (1 / (k : ℝ) ^ 2) := hnormS.tsum_le_tsum hterm (hS.mul_left _)
      _ = K / d ^ 2 * ∑' k : ℤ, 1 / (k : ℝ) ^ 2 := tsum_mul_left
      _ = (K * ∑' k : ℤ, 1 / (k : ℝ) ^ 2) * d⁻¹ ^ 2 := by rw [inv_pow, div_eq_mul_inv]; ring

private theorem gram_inv_sub_one_bound (G : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ}
    (h14 : ∀ i j : Fin 2, ‖G i j - (if i = j then 1 else 0)‖ ≤ 1 / 4)
    (hε : ∀ i j : Fin 2, ‖G i j - (if i = j then 1 else 0)‖ ≤ ε) :
    (∀ i j : Fin 2, ‖G⁻¹ i j‖ ≤ 3) ∧
      ∀ i j : Fin 2, ‖G⁻¹ i j - (if i = j then 1 else 0)‖ ≤ 6 * ε := by
  obtain ⟨hU, hbd⟩ := IIIa.gram_inv_bound G h14
  refine ⟨hbd, fun i j => ?_⟩
  have hmul := Matrix.nonsing_inv_mul G hU
  have hij := congrFun (congrFun hmul i) j
  rw [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] at hij
  have hid : G⁻¹ i j - (if i = j then (1 : ℂ) else 0) =
      -(G⁻¹ i 0 * (G 0 j - (if (0 : Fin 2) = j then 1 else 0)) +
        G⁻¹ i 1 * (G 1 j - (if (1 : Fin 2) = j then 1 else 0))) := by
    rw [← hij]
    fin_cases j <;> simp <;> ring
  rw [hid, norm_neg]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have b0 := hbd i 0
  have b1 := hbd i 1
  have e0 := hε 0 j
  have e1 := hε 1 j
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans e0
  nlinarith [norm_nonneg (G⁻¹ i 0), norm_nonneg (G⁻¹ i 1),
    norm_nonneg (G 0 j - (if (0 : Fin 2) = j then 1 else 0)),
    norm_nonneg (G 1 j - (if (1 : Fin 2) = j then 1 else 0)),
    mul_le_mul b0 e0 (norm_nonneg _) (by norm_num),
    mul_le_mul b1 e1 (norm_nonneg _) (by norm_num)]

theorem g2PairNear : UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G2.PairNear := by
  intro κ g hg ⟨K_g, hKg⟩
  have hU := IIIa.perGramUnfold κ
  obtain ⟨CG, DG, hTail⟩ := IIIa.perGramTail κ
  obtain ⟨D1, hD1⟩ := IIIa.perGramNear_of κ hU ⟨CG, DG, hTail⟩ (1 / 4) (by norm_num)
  obtain ⟨C0, K0, hC0, hK0, hIbd, hPair0⟩ := gPair0_unfold κ hg hKg
  set CG' : ℝ := max CG 0
  have hCG'0 : 0 ≤ CG' := le_max_right _ _
  set d0 : ℝ := max (max D1 DG) 1
  have hd0_1 : 1 ≤ d0 := le_max_right _ _
  have hd0_pos : 0 < d0 := by linarith
  refine ⟨6 * C0 + 12 * CG' * K0, d0, hd0_pos, fun d hd i => ?_⟩
  have hd1 : 1 ≤ d := le_trans hd0_1 hd
  have hdpos : 0 < d := by linarith
  have hdD1 : D1 ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hd
  have hdDG : DG ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hd
  have hGε : ∀ a b : Fin 2,
      ‖IIIa.perGram κ d a b - (if a = b then 1 else 0)‖ ≤ CG' * d⁻¹ ^ 2 := by
    intro a b
    obtain ⟨hs, he⟩ := hU d hdpos a b
    have hsplit := hs.tsum_eq_add_tsum_ite 0
    have h0 : IIIa.gramTerm κ d a b 0 = if a = b then 1 else 0 := by
      simp only [IIIa.gramTerm, Int.cast_zero, zero_mul, add_zero]
      exact κ.biorth a b
    have hrest : IIIa.perGram κ d a b - (if a = b then 1 else 0) =
        ∑' k : ℤ, (if k = 0 then (0 : ℂ) else IIIa.gramTerm κ d a b k) := by
      rw [he, hsplit, h0, add_sub_cancel_left]
    rw [hrest]
    refine (hTail d hdDG a b).trans ?_
    rw [inv_pow, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  obtain ⟨hGinv, hGsub⟩ := gram_inv_sub_one_bound (IIIa.perGram κ d) (hD1 d hdD1) hGε
  have hlin : (∫ y in B0579.cell d, IIIa.perLam κ d i y * IIIa.periodizeC d g y) =
      ∑ j : Fin 2, (IIIa.perGram κ d)⁻¹ i j *
        ∫ y in B0579.cell d, IIIa.perLam0 κ d j y * IIIa.perSum d g y := by
    have hfun : (fun y => IIIa.perLam κ d i y * IIIa.periodizeC d g y) =
        fun y => ∑ j : Fin 2, (IIIa.perGram κ d)⁻¹ i j *
          (IIIa.perLam0 κ d j y * IIIa.perSum d g y) := by
      funext y
      rw [periodizeC_eq_perSum]
      simp only [IIIa.perLam, Finset.sum_mul, mul_assoc]
    rw [hfun, integral_finsetSum]
    · simp only [integral_const_mul]
    · intro j _
      exact ((hPair0 d hd1 j).1).const_mul _
  rw [hlin]
  set P0 : Fin 2 → ℂ := fun j => ∫ y in B0579.cell d, IIIa.perLam0 κ d j y * IIIa.perSum d g y
  set I0 : Fin 2 → ℂ := fun j => ∫ y, κ.lamP j y * g y
  set Ginv : Matrix (Fin 2) (Fin 2) ℂ := (IIIa.perGram κ d)⁻¹
  have hdecomp : (∑ j : Fin 2, Ginv i j * P0 j) - I0 i =
      (Ginv i 0 * (P0 0 - I0 0) + Ginv i 1 * (P0 1 - I0 1)) +
      ((Ginv i 0 - (if i = 0 then 1 else 0)) * I0 0 +
        (Ginv i 1 - (if i = 1 then 1 else 0)) * I0 1) := by
    rw [Fin.sum_univ_two]
    fin_cases i <;> simp <;> ring
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  have hA : ‖Ginv i 0 * (P0 0 - I0 0) + Ginv i 1 * (P0 1 - I0 1)‖ ≤
      6 * C0 * d⁻¹ ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have b0 := hGinv i 0
    have b1 := hGinv i 1
    have p0 := (hPair0 d hd1 0).2
    have p1 := (hPair0 d hd1 1).2
    have hd2 : 0 ≤ d⁻¹ ^ 2 := by positivity
    nlinarith [norm_nonneg (Ginv i 0), norm_nonneg (Ginv i 1),
      norm_nonneg (P0 0 - I0 0), norm_nonneg (P0 1 - I0 1),
      mul_le_mul b0 p0 (norm_nonneg _) (by norm_num),
      mul_le_mul b1 p1 (norm_nonneg _) (by norm_num)]
  have hB : ‖(Ginv i 0 - (if i = 0 then 1 else 0)) * I0 0 +
      (Ginv i 1 - (if i = 1 then 1 else 0)) * I0 1‖ ≤
      12 * CG' * K0 * d⁻¹ ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have s0 := hGsub i 0
    have s1 := hGsub i 1
    have i0 := hIbd 0
    have i1 := hIbd 1
    have hd2 : 0 ≤ d⁻¹ ^ 2 := by positivity
    nlinarith [norm_nonneg (Ginv i 0 - (if i = 0 then 1 else 0)),
      norm_nonneg (Ginv i 1 - (if i = 1 then 1 else 0)),
      norm_nonneg (I0 0), norm_nonneg (I0 1),
      mul_le_mul s0 i0 (norm_nonneg _) (by positivity),
      mul_le_mul s1 i1 (norm_nonneg _) (by positivity)]
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G2
