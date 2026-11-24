import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c1_b.FrameCont
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.L4
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjWeakChi.XNorm
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.PairingCoV
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Part III-a, task `PartIII-a:T21/c3/1`: measurability of the frame amplitude and complement norms

Source of record: `the November 2 reference manuscript` (SP), lines 2894-2902 and
2975-3004.

Proves `frameFlowMeasurable κ : FrameFlowMeasurable κ` (composed into `FrameStableAll κ` by
`frameStableAll_of` in `Sub/PartIII-a_T21_c3.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa

namespace FlowMeas

/-! ## Continuity of `perGram` and `(perGram)⁻¹` in `d` -/

lemma gramTerm_eq_shift (κ : PlanarFrameKernels) (d : ℝ) (i j : Fin 2) (k : ℤ) :
    gramTerm κ d i j k = ∫ y : ℝ × ℝ, κ.lamP i (y.1 - (k : ℝ) * d, y.2) * κ.e j y := by
  unfold gramTerm
  have h := MeasureTheory.integral_add_right_eq_self
    (μ := (volume : Measure (ℝ × ℝ)))
    (fun y : ℝ × ℝ => κ.lamP i (y.1 - (k : ℝ) * d, y.2) * κ.e j y) ((k : ℝ) * d, 0)
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  have h1 : (y + ((k : ℝ) * d, (0 : ℝ))).1 - (k : ℝ) * d = y.1 := by simp
  have h2 : (y + ((k : ℝ) * d, (0 : ℝ))).2 = y.2 := by simp
  have h3 : y + ((k : ℝ) * d, (0 : ℝ)) = (y.1 + (k : ℝ) * d, y.2) := by
    ext <;> simp
  rw [h1, h2, h3]

lemma continuous_gramTerm (κ : PlanarFrameKernels) (i j : Fin 2) (k : ℤ) :
    Continuous (fun d : ℝ => gramTerm κ d i j k) := by
  simp_rw [gramTerm_eq_shift]
  obtain ⟨C₁, hC₁⟩ := κ.lamP_decay
  obtain ⟨C₂, hC₂⟩ := κ.e_decay
  set bound : ℝ × ℝ → ℝ := fun y =>
    (|C₁| * |C₂|) * Real.exp (-((y.1 + 0) ^ 2 + y.2 ^ 2) / (4 * 2))
  have hbound_int : Integrable bound volume :=
    (integrable_shift_gauss 0 (t := 2) (by norm_num)).const_mul (|C₁| * |C₂|)
  refine MeasureTheory.continuous_of_dominated ?_ ?_ hbound_int ?_
  · intro d
    have hc : Continuous (fun y : ℝ × ℝ => κ.lamP i (y.1 - (k : ℝ) * d, y.2) * κ.e j y) :=
      ((κ.lamP_cont i).comp ((continuous_fst.sub continuous_const).prodMk continuous_snd)).mul
        (κ.e_cont j)
    exact hc.aestronglyMeasurable
  · intro d
    refine Eventually.of_forall fun y => ?_
    rw [norm_mul]
    have h1 : ‖κ.lamP i (y.1 - (k : ℝ) * d, y.2)‖ ≤ |C₁| := by
      have hd := (hC₁ i (y.1 - (k : ℝ) * d, y.2)).trans
        (mul_le_mul_of_nonneg_right (le_abs_self C₁) (by positivity))
      have hinv : (1 + |y.1 - (k : ℝ) * d| + |y.2|)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (by linarith [abs_nonneg (y.1 - (k : ℝ) * d), abs_nonneg y.2])
      have hsq : ((1 + |y.1 - (k : ℝ) * d| + |y.2|)⁻¹) ^ 2 ≤ 1 := by
        nlinarith [inv_nonneg.2 (by positivity : (0 : ℝ) ≤ 1 + |y.1 - (k : ℝ) * d| + |y.2|)]
      calc ‖κ.lamP i (y.1 - (k : ℝ) * d, y.2)‖
          ≤ |C₁| * ((1 + |y.1 - (k : ℝ) * d| + |y.2|)⁻¹) ^ 2 := hd
        _ ≤ |C₁| * 1 := mul_le_mul_of_nonneg_left hsq (abs_nonneg C₁)
        _ = |C₁| := mul_one _
    have h2 : ‖κ.e j y‖ ≤ |C₂| * Real.exp (-((y.1 + 0) ^ 2 + y.2 ^ 2) / (4 * 2)) := by
      have he := (hC₂ j y).trans
        (mul_le_mul_of_nonneg_right (le_abs_self C₂) (Real.exp_pos _).le)
      simpa [add_zero, show (4 : ℝ) * 2 = 8 by norm_num] using he
    calc ‖κ.lamP i (y.1 - (k : ℝ) * d, y.2)‖ * ‖κ.e j y‖
        ≤ |C₁| * (|C₂| * Real.exp (-((y.1 + 0) ^ 2 + y.2 ^ 2) / (4 * 2))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (abs_nonneg C₁)
      _ = bound y := by simp only [bound]; ring
  · refine Eventually.of_forall fun y => ?_
    exact (((κ.lamP_cont i).comp
      ((continuous_const.sub (continuous_const.mul continuous_id)).prodMk
        continuous_const)).mul continuous_const)

lemma continuousOn_perGram (κ : PlanarFrameKernels) (i j : Fin 2) :
    ContinuousOn (fun d : ℝ => perGram κ d i j) (Ici 1) := by
  obtain ⟨K_g, _hK_g0, hK_g⟩ := gramCross_int κ
  have hcont_sum : ContinuousOn (fun d : ℝ => ∑' k : ℤ, gramTerm κ d i j k) (Ici 1) := by
    refine continuousOn_tsum (fun k => (continuous_gramTerm κ i j k).continuousOn)
      (summable_cross_bound (K := K_g) zero_lt_one) (fun k d hd => ?_)
    have hd1 : (1 : ℝ) ≤ d := hd
    have hkd : |(k : ℝ) * 1| ≤ |(k : ℝ) * d| := by
      rw [abs_mul, abs_mul, abs_one, abs_of_pos (by linarith : (0 : ℝ) < d)]
      exact mul_le_mul_of_nonneg_left hd1 (abs_nonneg _)
    calc ‖gramTerm κ d i j k‖
        ≤ ∫ y : ℝ × ℝ, ‖κ.lamP i y * κ.e j (y.1 + (k : ℝ) * d, y.2)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ K_g / (1 + |(k : ℝ) * d|) ^ 2 := (hK_g i j ((k : ℝ) * d)).2
      _ ≤ K_g / (1 + |(k : ℝ) * 1|) ^ 2 := by
          gcongr
  refine hcont_sum.congr fun d hd => ?_
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  exact (perGramUnfold κ d hd0 i j).2

lemma continuousOn_perGram_inv (κ : PlanarFrameKernels) {D₁ : ℝ}
    (hD₁ : ∀ d : ℝ, D₁ ≤ d → ∀ i j : Fin 2,
      ‖perGram κ d i j - (if i = j then 1 else 0)‖ ≤ 1 / 4)
    (i j : Fin 2) :
    ContinuousOn (fun d : ℝ => (perGram κ d)⁻¹ i j) (Ici (max D₁ 1)) := by
  have hsub : Ici (max D₁ 1) ⊆ Ici 1 := Ici_subset_Ici.2 (le_max_right _ _)
  have hG : ∀ a b : Fin 2, ContinuousOn (fun d : ℝ => perGram κ d a b) (Ici (max D₁ 1)) :=
    fun a b => (continuousOn_perGram κ a b).mono hsub
  have hdet : ContinuousOn (fun d : ℝ => (perGram κ d).det) (Ici (max D₁ 1)) := by
    have heq : (fun d : ℝ => (perGram κ d).det) =
        fun d => perGram κ d 0 0 * perGram κ d 1 1 - perGram κ d 0 1 * perGram κ d 1 0 := by
      funext d; exact Matrix.det_fin_two (perGram κ d)
    rw [heq]
    exact ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0))
  have hdet_ne : ∀ d ∈ Ici (max D₁ 1), (perGram κ d).det ≠ 0 := by
    intro d hd
    have hdD : D₁ ≤ d := le_trans (le_max_left _ _) hd
    exact isUnit_iff_ne_zero.1 (gram_inv_bound _ (hD₁ d hdD)).1
  have hdet_inv : ContinuousOn (fun d : ℝ => ((perGram κ d).det)⁻¹) (Ici (max D₁ 1)) :=
    hdet.inv₀ hdet_ne
  fin_cases i <;> fin_cases j
  · change ContinuousOn (fun d : ℝ => (perGram κ d)⁻¹ 0 0) (Ici (max D₁ 1))
    have hentry : (fun d : ℝ => (perGram κ d)⁻¹ 0 0) =
        fun d => ((perGram κ d).det)⁻¹ * perGram κ d 1 1 := by
      funext d; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    rw [hentry]; exact hdet_inv.mul (hG 1 1)
  · change ContinuousOn (fun d : ℝ => (perGram κ d)⁻¹ 0 1) (Ici (max D₁ 1))
    have hentry : (fun d : ℝ => (perGram κ d)⁻¹ 0 1) =
        fun d => ((perGram κ d).det)⁻¹ * (-perGram κ d 0 1) := by
      funext d; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    rw [hentry]; exact hdet_inv.mul (hG 0 1).neg
  · change ContinuousOn (fun d : ℝ => (perGram κ d)⁻¹ 1 0) (Ici (max D₁ 1))
    have hentry : (fun d : ℝ => (perGram κ d)⁻¹ 1 0) =
        fun d => ((perGram κ d).det)⁻¹ * (-perGram κ d 1 0) := by
      funext d; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    rw [hentry]; exact hdet_inv.mul (hG 1 0).neg
  · change ContinuousOn (fun d : ℝ => (perGram κ d)⁻¹ 1 1) (Ici (max D₁ 1))
    have hentry : (fun d : ℝ => (perGram κ d)⁻¹ 1 1) =
        fun d => ((perGram κ d).det)⁻¹ * perGram κ d 0 0 := by
      funext d; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    rw [hentry]; exact hdet_inv.mul (hG 0 0)

/-! ## Pointwise continuity of `perSum (d r) f (x / √(a r))` on `Icc t s` -/

lemma continuousOn_clockA {ν : ℝ} (S : Set ℝ) : ContinuousOn (clockA ν) S := by
  unfold clockA
  exact continuousOn_const.add (continuousOn_const.mul continuousOn_id)

lemma continuousOn_sqrt_clockA {ν : ℝ} (S : Set ℝ) :
    ContinuousOn (fun r => Real.sqrt (clockA ν r)) S :=
  Real.continuous_sqrt.comp_continuousOn (continuousOn_clockA S)

lemma continuousOn_cellLen_clockA {ν c t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (S : Set ℝ)
    (hS : ∀ r ∈ S, t ≤ r) :
    ContinuousOn (fun r => cellLen c (clockA ν r)) S := by
  unfold cellLen
  refine continuousOn_const.div (continuousOn_sqrt_clockA S) (fun r hr => ?_)
  have ha : 1 ≤ clockA ν r := one_le_clockA hν.le (ht.trans (hS r hr))
  exact (Real.sqrt_pos.2 (by linarith)).ne'

lemma continuousOn_perSum_scaled {f : ℝ × ℝ → ℂ} (hf : Continuous f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ z, ‖f z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    {ν c t s : ℝ} (hν : 0 < ν) (ht : 0 ≤ t)
    (hd1 : ∀ r ∈ Icc t s, 1 ≤ cellLen c (clockA ν r)) (x : ℝ × ℝ) :
    ContinuousOn
      (fun r => perSum (cellLen c (clockA ν r)) f
        (x.1 / Real.sqrt (clockA ν r), x.2 / Real.sqrt (clockA ν r)))
      (Icc t s) := by
  unfold perSum
  have hsa_ne : ∀ r ∈ Icc t s, Real.sqrt (clockA ν r) ≠ 0 := fun r hr => by
    have ha : 1 ≤ clockA ν r := one_le_clockA hν.le (ht.trans hr.1)
    exact (Real.sqrt_pos.2 (by linarith)).ne'
  have hcont_term : ∀ n : ℤ, ContinuousOn
      (fun r => f (x.1 / Real.sqrt (clockA ν r) + (n : ℝ) * cellLen c (clockA ν r),
        x.2 / Real.sqrt (clockA ν r))) (Icc t s) := by
    intro n
    have hc1 : ContinuousOn (fun r => x.1 / Real.sqrt (clockA ν r) +
        (n : ℝ) * cellLen c (clockA ν r)) (Icc t s) :=
      (continuousOn_const.div (continuousOn_sqrt_clockA _) hsa_ne).add
        (continuousOn_const.mul (continuousOn_cellLen_clockA hν ht _ fun _ hr => hr.1))
    have hc2 : ContinuousOn (fun r => x.2 / Real.sqrt (clockA ν r)) (Icc t s) :=
      continuousOn_const.div (continuousOn_sqrt_clockA _) hsa_ne
    exact hf.comp_continuousOn (hc1.prodMk hc2)
  have hsum : Summable (fun n : ℤ =>
      C * (1 + |x.1|) ^ (2 : ℝ) * (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) :=
    (UnforcedLeray.Gaussian.summable_one_add_abs_int_rpow (s := 2) (by norm_num)).mul_left _
  refine continuousOn_tsum hcont_term hsum (fun n r hr => ?_)
  set a := clockA ν r
  set d := cellLen c a
  set y₁ := x.1 / Real.sqrt a
  have ha1 : 1 ≤ a := one_le_clockA hν.le (ht.trans hr.1)
  have hsa1 : 1 ≤ Real.sqrt a := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ha1
  have hy1_le : |y₁| ≤ |x.1| := by
    simp only [y₁, abs_div, abs_of_pos (by linarith : (0 : ℝ) < Real.sqrt a)]
    exact div_le_self (abs_nonneg x.1) hsa1
  have hpeetre := UnforcedLeray.Gaussian.one_add_abs_rpow_neg_le (s := 2) (by norm_num)
    (y₁ + (n : ℝ) * d) (-y₁)
  have hadd : y₁ + (n : ℝ) * d + -y₁ = (n : ℝ) * d := by ring
  rw [hadd, abs_neg] at hpeetre
  have hdr : 1 ≤ d := hd1 r hr
  have hnd : 1 + |(n : ℝ)| ≤ 1 + |(n : ℝ) * d| := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < d)]
    nlinarith [abs_nonneg (n : ℝ)]
  have hnd_rpow : (1 + |(n : ℝ) * d|) ^ (-(2 : ℝ)) ≤ (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hnd (by norm_num)
  have hy1_rpow : (1 + |y₁|) ^ (2 : ℝ) ≤ (1 + |x.1|) ^ (2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  calc ‖f (y₁ + (n : ℝ) * d, x.2 / Real.sqrt a)‖
      ≤ C * (1 + |y₁ + (n : ℝ) * d|) ^ (-(2 : ℝ)) := hC _
    _ ≤ C * ((1 + |y₁|) ^ (2 : ℝ) * (1 + |(n : ℝ) * d|) ^ (-(2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hpeetre hC0
    _ ≤ C * ((1 + |x.1|) ^ (2 : ℝ) * (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hy1_rpow hnd_rpow (by positivity) (by positivity)) hC0
    _ = C * (1 + |x.1|) ^ (2 : ℝ) * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by ring

lemma continuousOn_physFrameLam (κ : PlanarFrameKernels) {D₁ ν t s : ℝ}
    (hD₁ : ∀ d : ℝ, D₁ ≤ d → ∀ i j : Fin 2,
      ‖perGram κ d i j - (if i = j then 1 else 0)‖ ≤ 1 / 4)
    (hν : 0 < ν) (ht : 0 ≤ t)
    (hd : ∀ r ∈ Icc t s, max D₁ 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (i : Fin 2) (x : ℝ × ℝ) :
    ContinuousOn
      (fun r => physAdj (clockA ν r)
        (perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i) x)
      (Icc t s) := by
  obtain ⟨C, hC0, hC⟩ := Lam0B.lamP_translate_bound κ
  have hd1 : ∀ r ∈ Icc t s, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := fun r hr =>
    le_trans (le_max_right _ _) (hd r hr)
  have hmaps : MapsTo (fun r => cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (Icc t s) (Ici (max D₁ 1)) :=
    fun r hr => hd r hr
  have ha_cont : ContinuousOn (fun r => ((clockA ν r : ℝ) : ℂ)) (Icc t s) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_clockA _)
  have hd_cont : ContinuousOn (fun r => cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (Icc t s) :=
    continuousOn_cellLen_clockA hν ht _ fun _ hr => hr.1
  unfold physAdj perLam
  refine ha_cont.mul (continuousOn_finsetSum Finset.univ fun j _ => ?_)
  have hGinv : ContinuousOn (fun r => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i j)
      (Icc t s) :=
    (continuousOn_perGram_inv κ hD₁ i j).comp hd_cont hmaps
  have hLam0 : ContinuousOn
      (fun r => perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j
        (x.1 / Real.sqrt (clockA ν r), x.2 / Real.sqrt (clockA ν r)))
      (Icc t s) :=
    continuousOn_perSum_scaled (κ.lamP_cont j) hC0 (hC j) hν ht hd1 x
  exact hGinv.mul hLam0

/-! ## Bounds and continuity of `ampl` and `amplNorm` on `Icc t s` -/

lemma integrableOn_of_memLp_cellMeasure {c m : ℝ} (hm : 8 < m) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (B0579.cellMeasure c m)) :
    IntegrableOn g (B0579.cell c) := by
  set G : ℝ × ℝ → ℝ := fun y => B0579.jb y ^ (m / 2 * (-1))
  have hGmem : MemLp G 2 volume := by
    have hcont : Continuous G := B0579.continuous_jb_rpow _
    refine (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 ?_
    refine Lam0B.integrable_jb_neg_two.mono' (hcont.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    have hj0 : 0 ≤ B0579.jb y := (B0579.jb_pos y).le
    have e1 : (B0579.jb y ^ (m / 2 * (-1))) ^ 2 = B0579.jb y ^ (-m) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hj0]
      congr 1; push_cast; ring
    rw [Real.norm_of_nonneg (sq_nonneg _), e1]
    exact Real.rpow_le_rpow_of_exponent_le (Lam0B.jb_ge_one y) (by linarith)
  have hgm_vol : AEStronglyMeasurable g (volume.restrict (B0579.cell c)) :=
    hg.1.mono_ac (B0579.ac_cellMeasure c m)
  have hAmem : MemLp (fun y => ((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * g y) 2
      (volume.restrict (B0579.cell c)) := by
    have hcont : Continuous fun y : ℝ × ℝ => ((B0579.jb y ^ (m / 2) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (B0579.continuous_jb_rpow _)
    refine ⟨hcont.aestronglyMeasurable.mul hgm_vol, ?_⟩
    rw [← Lam0B.eLpNorm_cellMeasure_cx]
    exact hg.2
  have hGr : MemLp G 2 (volume.restrict (B0579.cell c)) := hGmem.restrict _
  have hGnn : ∀ y, 0 ≤ G y := fun y => Real.rpow_nonneg (B0579.jb_pos y).le _
  have hHold := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
    (f := fun y => ((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * g y)
    (g := G) (p := 2) (q := 2) (r := 1) hAmem.1 hGr.1
    (fun z t => z * ((t : ℝ) : ℂ)) 1
    (Eventually.of_forall fun y => by
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hGnn y), NNReal.coe_one,
        one_mul, le_refl])
  have hpt : ∀ y : ℝ × ℝ, ((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * g y * ((G y : ℝ) : ℂ) = g y := by
    intro y
    have hj : B0579.jb y ^ (m / 2) * B0579.jb y ^ (m / 2 * (-1)) = 1 := by
      rw [← Real.rpow_add (B0579.jb_pos y)]
      simp
    calc ((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * g y * ((G y : ℝ) : ℂ)
        = (((B0579.jb y ^ (m / 2) * B0579.jb y ^ (m / 2 * (-1)) : ℝ) : ℂ)) * g y := by
          simp only [G]; push_cast; ring
      _ = g y := by rw [hj]; simp
  have hHold' : eLpNorm g 1 (volume.restrict (B0579.cell c)) ≤
      eLpNorm (fun y => ((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * g y) 2
        (volume.restrict (B0579.cell c)) * eLpNorm G 2 (volume.restrict (B0579.cell c)) := by
    simpa only [hpt, ENNReal.coe_one, one_mul] using hHold
  exact memLp_one_iff_integrable.1
    ⟨hgm_vol, lt_of_le_of_lt hHold' (ENNReal.mul_lt_top hAmem.2 hGr.2)⟩

lemma physFrameLam_bound (κ : PlanarFrameKernels) {D₁ : ℝ}
    (hD₁ : ∀ d : ℝ, D₁ ≤ d → ∀ i j : Fin 2,
      ‖perGram κ d i j - (if i = j then 1 else 0)‖ ≤ 1 / 4) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ν r : ℝ), 0 < ν → 0 ≤ r →
      max D₁ 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) →
      ∀ (i : Fin 2) (x : ℝ × ℝ), x ∈ B0579.cell (ν ^ (-2 : ℝ)) →
        ‖physAdj (clockA ν r)
          (perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i) x‖ ≤
          clockA ν r * B := by
  obtain ⟨B₀, hB₀, hsup⟩ := Lam0B.perLam0_sup κ
  refine ⟨6 * B₀, by positivity, fun ν r hν hr hd i x hx => ?_⟩
  set a := clockA ν r
  set d := cellLen (ν ^ (-2 : ℝ)) a
  have ha : 1 ≤ a := one_le_clockA hν.le hr
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 (by linarith)
  have hd1 : 1 ≤ d := le_trans (le_max_right _ _) hd
  have hdD : D₁ ≤ d := le_trans (le_max_left _ _) hd
  have hy : (x.1 / Real.sqrt a, x.2 / Real.sqrt a) ∈ B0579.cell d := by
    have hsmul : Real.sqrt a • (x.1 / Real.sqrt a, x.2 / Real.sqrt a) ∈
        B0579.cell (d * Real.sqrt a) := by
      have heq1 : Real.sqrt a • (x.1 / Real.sqrt a, x.2 / Real.sqrt a) = x := by
        ext <;> simp [smul_eq_mul, mul_div_cancel₀ _ hsa.ne']
      have heq2 : d * Real.sqrt a = ν ^ (-2 : ℝ) := by
        simp only [d, cellLen, div_mul_cancel₀ _ hsa.ne']
      rwa [heq1, heq2]
    exact (T07.smul_mem_cell_iff d (Real.sqrt a) hsa _).1 hsmul
  have hG := (gram_inv_bound _ (hD₁ d hdD)).2
  unfold physAdj perLam
  rw [norm_mul, Complex.norm_of_nonneg (by linarith), Fin.sum_univ_two]
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have h0 := hsup d hd1 0 _ hy
  have h1 := hsup d hd1 1 _ hy
  have g0 := hG i 0
  have g1 := hG i 1
  nlinarith [norm_nonneg ((perGram κ d)⁻¹ i 0), norm_nonneg ((perGram κ d)⁻¹ i 1),
    norm_nonneg (perLam0 κ d 0 (x.1 / Real.sqrt a, x.2 / Real.sqrt a)),
    norm_nonneg (perLam0 κ d 1 (x.1 / Real.sqrt a, x.2 / Real.sqrt a)),
    mul_le_mul g0 h0 (norm_nonneg _) (by norm_num),
    mul_le_mul g1 h1 (norm_nonneg _) (by norm_num)]

lemma continuousOn_ampl (κ : PlanarFrameKernels) {D₁ ν m b K t s : ℝ}
    (hD₁ : ∀ d : ℝ, D₁ ≤ d → ∀ i j : Fin 2,
      ‖perGram κ d i j - (if i = j then 1 else 0)‖ ≤ 1 / 4)
    (hm : 8 < m) (hν : 0 < ν) (ht : 0 ≤ t) (hts : t ≤ s)
    (hbs : b ≤ clockTheta ν s) (hF : PerFrameFacts κ ν m b K)
    (hd : ∀ r ∈ Icc t s, max D₁ 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u) (i : Fin 2) :
    ContinuousOn (fun r => ampl (periodizedFrame κ ν m b K hν hF) w r i) (Icc t s) := by
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  set Φ : ℝ → ℝ × ℝ → ℂ := fun r x =>
    physAdj (clockA ν r) (perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i) x
  obtain ⟨B, hB0, hB⟩ := physFrameLam_bound κ hD₁
  have hΦ_bdd : ∀ r ∈ Icc t s, ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      ‖Φ r x‖ ≤ clockA ν s * B := by
    intro r hr x hx
    calc ‖Φ r x‖ ≤ clockA ν r * B := hB ν r hν (ht.trans hr.1) (hd r hr) i x hx
      _ ≤ clockA ν s * B := mul_le_mul_of_nonneg_right (clockA_mono hν.le hr.2) hB0
  have hΦ_cont_x : ∀ r ∈ Icc t s, Continuous (Φ r) := by
    intro r hr
    have hd_pos : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
      lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) (hd r hr))
    unfold Φ physAdj
    exact continuous_const.mul ((FrameCont.perLam_continuous κ hd_pos i).comp
      ((continuous_fst.div_const _).prodMk (continuous_snd.div_const _)))
  have hprod_int : ∀ r₁ ∈ Icc t s, ∀ r₂ ∈ Icc t s,
      IntegrableOn (fun x => w r₁ x * Φ r₂ x) (B0579.cell (ν ^ (-2 : ℝ))) := by
    intro r₁ hr₁ r₂ hr₂
    have hw_int := integrableOn_of_memLp_cellMeasure hm (hw.memX r₁ hr₁.1)
    refine (hw_int.norm.const_mul (clockA ν s * B)).mono'
      (hw_int.aestronglyMeasurable.mul (hΦ_cont_x r₂ hr₂).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem (B0579.measurableSet_cell _)] with x hx
    rw [norm_mul]
    calc ‖w r₁ x‖ * ‖Φ r₂ x‖ ≤ ‖w r₁ x‖ * (clockA ν s * B) :=
          mul_le_mul_of_nonneg_left (hΦ_bdd r₂ hr₂ x hx) (norm_nonneg _)
      _ = clockA ν s * B * ‖w r₁ x‖ := mul_comm _ _
  have hampl_eq : ∀ r ∈ Icc t s,
      ampl (periodizedFrame κ ν m b K hν hF) w r i =
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w r x * Φ r x := by
    intro r hr
    have ha : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le (ht.trans hr.1))
    have hco := pairingCoV (ν ^ (-2 : ℝ)) (clockA ν r) hc ha (w r)
      (perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i)
    simpa only [ampl, periodizedFrame, movingW, movingCell, Φ, mul_comm] using hco
  intro r hr
  rw [ContinuousWithinAt]
  have h1 : Tendsto (fun r' => ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (w r' x - w r x) * Φ r' x)
      (𝓝[Icc t s] r) (𝓝 0) := by
    set C_s : ℝ := max K 0 * (clockA ν s) ^ ((3 : ℝ) / 2)
    have hAs0 : 0 ≤ clockA ν s := le_trans zero_le_one (one_le_clockA hν.le (ht.trans hts))
    have hC_s0 : 0 ≤ C_s := by positivity
    have hdiff_le : ∀ r' ∈ Icc t s,
        ‖∫ x in B0579.cell (ν ^ (-2 : ℝ)), (w r' x - w r x) * Φ r' x‖ ≤
          C_s * (xNorm (ν ^ (-2 : ℝ)) m (w r' - w r)).toReal := by
      intro r' hr'
      have hr'0 : 0 ≤ r' := ht.trans hr'.1
      have ha' : 1 ≤ clockA ν r' := one_le_clockA hν.le hr'0
      have hbr' : b ≤ clockTheta ν r' := hbs.trans (theta_anti hν hr'0 hr'.2)
      have hco := pairingCoV (ν ^ (-2 : ℝ)) (clockA ν r') hc (by linarith) (w r' - w r)
        (perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) i)
      have heq : (∫ x in B0579.cell (ν ^ (-2 : ℝ)), (w r' x - w r x) * Φ r' x) =
          ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')),
            perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) i y *
              JscaleInv (clockA ν r') (w r' - w r) y := by
        simpa only [Φ, Pi.sub_apply, mul_comm] using hco.symm
      rw [heq]
      have hmem_sub : MemLp (w r' - w r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) :=
        (hw.memX r' hr'.1).sub (hw.memX r hr.1)
      have hfin : xNorm (ν ^ (-2 : ℝ)) m (w r' - w r) ≠ ⊤ := hmem_sub.2.ne
      have hbd1 : ENNReal.ofReal ‖∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')),
            perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) i y *
              JscaleInv (clockA ν r') (w r' - w r) y‖ ≤
          ENNReal.ofReal K * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) m
            (JscaleInv (clockA ν r') (w r' - w r)) :=
        hF.2.2 r' hr'0 hbr' i (JscaleInv (clockA ν r') (w r' - w r))
      have hbd2 := xNorm_JscaleInv_le (ν ^ (-2 : ℝ)) m (clockA ν r') (by linarith) ha'
        (w r' - w r) hmem_sub
      have hA_le : (clockA ν r') ^ ((3 : ℝ) / 2) ≤ (clockA ν s) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow (by linarith) (clockA_mono hν.le hr'.2) (by norm_num)
      have hcomb : ENNReal.ofReal ‖∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')),
            perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) i y *
              JscaleInv (clockA ν r') (w r' - w r) y‖ ≤
          ENNReal.ofReal (C_s * (xNorm (ν ^ (-2 : ℝ)) m (w r' - w r)).toReal) := by
        calc _ ≤ ENNReal.ofReal K * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) m
                (JscaleInv (clockA ν r') (w r' - w r)) := hbd1
          _ ≤ ENNReal.ofReal (max K 0) * (ENNReal.ofReal ((clockA ν s) ^ ((3 : ℝ) / 2)) *
                xNorm (ν ^ (-2 : ℝ)) m (w r' - w r)) := by
              gcongr
              · exact le_max_left K 0
              · exact hbd2.trans (by gcongr)
          _ = ENNReal.ofReal C_s *
                ENNReal.ofReal (xNorm (ν ^ (-2 : ℝ)) m (w r' - w r)).toReal := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul (le_max_right K 0),
                ENNReal.ofReal_toReal hfin]
          _ = ENNReal.ofReal (C_s * (xNorm (ν ^ (-2 : ℝ)) m (w r' - w r)).toReal) :=
              (ENNReal.ofReal_mul hC_s0).symm
      exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC_s0 ENNReal.toReal_nonneg)).1 hcomb
    have hsc := (hw.strongCont r hr.1).mono_left
      (nhdsWithin_mono r fun r' (hr' : r' ∈ Icc t s) => (hr'.1 : r' ∈ Ici t))
    have htoR : Tendsto (fun r' => (xNorm (ν ^ (-2 : ℝ)) m (w r' - w r)).toReal)
        (𝓝[Icc t s] r) (𝓝 0) := by
      have := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hsc
      simpa only [Function.comp_def, ENNReal.toReal_zero] using this
    have hmul : Tendsto (fun r' => C_s * (xNorm (ν ^ (-2 : ℝ)) m (w r' - w r)).toReal)
        (𝓝[Icc t s] r) (𝓝 0) := by
      simpa using htoR.const_mul C_s
    exact squeeze_zero_norm' (eventually_nhdsWithin_of_forall hdiff_le) hmul
  have h2 : Tendsto (fun r' => ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w r x * Φ r' x)
      (𝓝[Icc t s] r) (𝓝 (∫ x in B0579.cell (ν ^ (-2 : ℝ)), w r x * Φ r x)) := by
    have hw_int := integrableOn_of_memLp_cellMeasure hm (hw.memX r hr.1)
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun x => (clockA ν s * B) * ‖w r x‖) ?_ ?_ (hw_int.norm.const_mul _) ?_
    · filter_upwards [self_mem_nhdsWithin] with r' hr'
      exact (hprod_int r hr r' hr').aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with r' hr'
      filter_upwards [ae_restrict_mem (B0579.measurableSet_cell _)] with x hx
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hΦ_bdd r' hr' x hx) (norm_nonneg _)
    · filter_upwards [ae_restrict_mem (B0579.measurableSet_cell _)] with x _hx
      exact tendsto_const_nhds.mul (continuousOn_physFrameLam κ hD₁ hν ht hd i x r hr)
  have hsum := h1.add h2
  rw [zero_add, ← hampl_eq r hr] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r' hr'
  have hsub : (∫ x in B0579.cell (ν ^ (-2 : ℝ)), (w r' x - w r x) * Φ r' x) =
      (∫ x in B0579.cell (ν ^ (-2 : ℝ)), w r' x * Φ r' x) -
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w r x * Φ r' x := by
    simp_rw [sub_mul]
    exact integral_sub (hprod_int r' hr' r' hr') (hprod_int r hr r' hr')
  rw [hsub, sub_add_cancel, hampl_eq r' hr']

lemma continuousOn_amplNorm (κ : PlanarFrameKernels) {D₁ ν m b K t s : ℝ}
    (hD₁ : ∀ d : ℝ, D₁ ≤ d → ∀ i j : Fin 2,
      ‖perGram κ d i j - (if i = j then 1 else 0)‖ ≤ 1 / 4)
    (hm : 8 < m) (hν : 0 < ν) (ht : 0 ≤ t) (hts : t ≤ s)
    (hbs : b ≤ clockTheta ν s) (hF : PerFrameFacts κ ν m b K)
    (hd : ∀ r ∈ Icc t s, max D₁ 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u) :
    ContinuousOn (fun r => amplNorm (periodizedFrame κ ν m b K hν hF) w r) (Icc t s) := by
  have h0 := ENNReal.continuous_ofReal.comp_continuousOn
    (continuous_norm.comp_continuousOn (continuousOn_ampl κ hD₁ hm hν ht hts hbs hF hd hw 0))
  have h1 := ENNReal.continuous_ofReal.comp_continuousOn
    (continuous_norm.comp_continuousOn (continuousOn_ampl κ hD₁ hm hν ht hts hbs hF hd hw 1))
  have heq : (fun r => amplNorm (periodizedFrame κ ν m b K hν hF) w r) =
      fun r => ENNReal.ofReal ‖ampl (periodizedFrame κ ν m b K hν hF) w r 0‖ +
        ENNReal.ofReal ‖ampl (periodizedFrame κ ν m b K hν hF) w r 1‖ := by
    funext r; unfold amplNorm; exact Fin.sum_univ_two _
  rw [heq]
  exact h0.add h1

/-! ## Pullback to the fixed cell `B0579.cell c` and continuity of the complement norm -/

/-- Scalar weight factor pulling `X_{m, c/√a}` back to `X_{m, c}` via `y = x / √a`. -/
def wFactor (a m : ℝ) (x : ℝ × ℝ) : ℝ :=
  a ^ (-(1 / 2 : ℝ)) *
    (B0579.jb (x.1 / Real.sqrt a, x.2 / Real.sqrt a) / B0579.jb x) ^ (m / 2)

/-- Pullback of a moving-cell field `G` on `B0579.cell (c / √a)` to `B0579.cell c`. -/
def pullCell (a m : ℝ) (G : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  ((wFactor a m x : ℝ) : ℂ) * G (x.1 / Real.sqrt a, x.2 / Real.sqrt a)

lemma wFactor_nonneg {a m : ℝ} (ha : 0 < a) (x : ℝ × ℝ) : 0 ≤ wFactor a m x := by
  unfold wFactor
  exact mul_nonneg (Real.rpow_nonneg ha.le _)
    (Real.rpow_nonneg (div_nonneg (B0579.jb_pos _).le (B0579.jb_pos _).le) _)

lemma wFactor_le_one {a m : ℝ} (ha : 1 ≤ a) (hm : 0 ≤ m) (x : ℝ × ℝ) :
    wFactor a m x ≤ 1 := by
  unfold wFactor
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have h1 : a ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha (by norm_num)
  have hjb : B0579.jb (x.1 / Real.sqrt a, x.2 / Real.sqrt a) ≤ B0579.jb x := by
    unfold B0579.jb
    rw [div_pow, div_pow, Real.sq_sqrt ha0.le]
    have hsq1 : x.1 ^ 2 / a ≤ x.1 ^ 2 := div_le_self (sq_nonneg x.1) ha
    have hsq2 : x.2 ^ 2 / a ≤ x.2 ^ 2 := div_le_self (sq_nonneg x.2) ha
    linarith
  have hdiv : B0579.jb (x.1 / Real.sqrt a, x.2 / Real.sqrt a) / B0579.jb x ≤ 1 :=
    (div_le_one (B0579.jb_pos x)).2 hjb
  have h2 : (B0579.jb (x.1 / Real.sqrt a, x.2 / Real.sqrt a) / B0579.jb x) ^ (m / 2) ≤ 1 :=
    Real.rpow_le_one (div_nonneg (B0579.jb_pos _).le (B0579.jb_pos _).le) hdiv (by linarith)
  calc a ^ (-(1 / 2 : ℝ)) *
        (B0579.jb (x.1 / Real.sqrt a, x.2 / Real.sqrt a) / B0579.jb x) ^ (m / 2)
      ≤ 1 * 1 := mul_le_mul h1 h2 (Real.rpow_nonneg (div_nonneg (B0579.jb_pos _).le (B0579.jb_pos _).le) _) zero_le_one
    _ = 1 := mul_one 1

lemma wFactor_sq_mul_jb {a m : ℝ} (ha : 0 < a) (x : ℝ × ℝ) :
    B0579.jb x ^ m * (wFactor a m x) ^ 2 =
      a⁻¹ * B0579.jb (x.1 / Real.sqrt a, x.2 / Real.sqrt a) ^ m := by
  unfold wFactor
  have hjx : 0 < B0579.jb x := B0579.jb_pos x
  have hjy : 0 < B0579.jb (x.1 / Real.sqrt a, x.2 / Real.sqrt a) := B0579.jb_pos _
  have hdiv_nn : 0 ≤ B0579.jb (x.1 / Real.sqrt a, x.2 / Real.sqrt a) / B0579.jb x :=
    div_nonneg hjy.le hjx.le
  have ha_sq : (a ^ (-(1 / 2 : ℝ))) ^ 2 = a⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    have : -(1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = -1 := by push_cast; ring
    rw [this, Real.rpow_neg_one]
  have hjb_sq : ((B0579.jb (x.1 / Real.sqrt a, x.2 / Real.sqrt a) / B0579.jb x) ^ (m / 2)) ^ 2 =
      B0579.jb (x.1 / Real.sqrt a, x.2 / Real.sqrt a) ^ m / B0579.jb x ^ m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hdiv_nn]
    have : m / 2 * ((2 : ℕ) : ℝ) = m := by push_cast; ring
    rw [this, Real.div_rpow hjy.le hjx.le]
  rw [mul_pow, ha_sq, hjb_sq]
  have hjx_ne : B0579.jb x ^ m ≠ 0 := (Real.rpow_pos_of_pos hjx m).ne'
  field_simp

lemma continuous_wFactor {a : ℝ} (m : ℝ) : Continuous (wFactor a m) := by
  unfold wFactor
  have hjb_y : Continuous (fun x : ℝ × ℝ =>
      B0579.jb (x.1 / Real.sqrt a, x.2 / Real.sqrt a)) := by
    unfold B0579.jb
    fun_prop
  have hjb_x : Continuous B0579.jb := by
    unfold B0579.jb
    fun_prop
  have hquot : Continuous (fun x : ℝ × ℝ =>
      B0579.jb (x.1 / Real.sqrt a, x.2 / Real.sqrt a) / B0579.jb x) :=
    hjb_y.div hjb_x (fun x => (B0579.jb_pos x).ne')
  exact continuous_const.mul
    (hquot.rpow_const fun x => Or.inl (div_pos (B0579.jb_pos _) (B0579.jb_pos _)).ne')

lemma continuousOn_wFactor_clockA {ν t s : ℝ} (m : ℝ) (hν : 0 < ν) (ht : 0 ≤ t) (x : ℝ × ℝ) :
    ContinuousOn (fun r => wFactor (clockA ν r) m x) (Icc t s) := by
  unfold wFactor
  have ha_pos : ∀ r ∈ Icc t s, 0 < clockA ν r := fun r hr =>
    lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le (ht.trans hr.1))
  have hsa_ne : ∀ r ∈ Icc t s, Real.sqrt (clockA ν r) ≠ 0 := fun r hr =>
    (Real.sqrt_pos.2 (ha_pos r hr)).ne'
  have hc1 : ContinuousOn (fun r => (clockA ν r) ^ (-(1 / 2 : ℝ))) (Icc t s) :=
    (continuousOn_clockA _).rpow_const fun r hr => Or.inl (ha_pos r hr).ne'
  have hc_jb : ContinuousOn (fun r =>
      B0579.jb (x.1 / Real.sqrt (clockA ν r), x.2 / Real.sqrt (clockA ν r)) / B0579.jb x)
      (Icc t s) := by
    unfold B0579.jb
    have hx1 : ContinuousOn (fun r => x.1 / Real.sqrt (clockA ν r)) (Icc t s) :=
      continuousOn_const.div (continuousOn_sqrt_clockA _) hsa_ne
    have hx2 : ContinuousOn (fun r => x.2 / Real.sqrt (clockA ν r)) (Icc t s) :=
      continuousOn_const.div (continuousOn_sqrt_clockA _) hsa_ne
    exact (((continuousOn_const.add (hx1.pow 2)).add (hx2.pow 2))).div_const _
  exact hc1.mul (hc_jb.rpow_const fun r _hr =>
    Or.inl (div_pos (B0579.jb_pos _) (B0579.jb_pos _)).ne')

lemma xNorm_pullCell (c m a : ℝ) (ha : 0 < a) (G : ℝ × ℝ → ℂ) :
    xNorm c m (pullCell a m G) = xNorm (cellLen c a) m G := by
  unfold xNorm
  rw [T07.eLpNorm_two_eq_lintegral, T07.eLpNorm_two_eq_lintegral,
    T07.lintegral_cellMeasure_eq, T07.lintegral_cellMeasure_eq]
  congr 1
  set s := Real.sqrt a
  have hs : 0 < s := Real.sqrt_pos.2 ha
  have hsinv_ne : s⁻¹ ≠ 0 := inv_ne_zero hs.ne'
  set H : ℝ × ℝ → ℝ≥0∞ := (B0579.cell (cellLen c a)).indicator
    (fun y => ((B0579.density m y : ℝ≥0) : ℝ≥0∞) * ‖G y‖ₑ ^ 2)
  have hpt : ∀ x : ℝ × ℝ,
      (B0579.cell c).indicator
        (fun x => ((B0579.density m x : ℝ≥0) : ℝ≥0∞) * ‖pullCell a m G x‖ₑ ^ 2) x =
      ENNReal.ofReal a⁻¹ * H (s⁻¹ • x) := by
    intro x
    have hsmul_eq : s⁻¹ • x = (x.1 / s, x.2 / s) := by
      ext <;> simp [smul_eq_mul, div_eq_inv_mul]
    have hmem_iff : x ∈ B0579.cell c ↔ s⁻¹ • x ∈ B0579.cell (cellLen c a) := by
      have h1 := T07.smul_mem_cell_iff (cellLen c a) s hs (s⁻¹ • x)
      have h2 : s • (s⁻¹ • x) = x := smul_inv_smul₀ hs.ne' x
      have h3 : cellLen c a * s = c := by simp only [cellLen, s, div_mul_cancel₀ _ hs.ne']
      rwa [h2, h3] at h1
    by_cases hx : x ∈ B0579.cell c
    · have hy : s⁻¹ • x ∈ B0579.cell (cellLen c a) := hmem_iff.1 hx
      simp only [H, indicator_of_mem hx, indicator_of_mem hy, T07.density_coe, pullCell]
      rw [enorm_mul, mul_pow, T07.enorm_ofReal_cast (wFactor_nonneg ha x),
        ← ENNReal.ofReal_pow (wFactor_nonneg ha x), ← mul_assoc,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (B0579.jb_pos x).le m),
        wFactor_sq_mul_jb ha x, ENNReal.ofReal_mul (inv_nonneg.2 ha.le),
        hsmul_eq, mul_assoc]
    · have hy : s⁻¹ • x ∉ B0579.cell (cellLen c a) := fun h => hx (hmem_iff.2 h)
      simp [H, hx, hy]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hmap := Measure.map_addHaar_smul (volume : Measure (ℝ × ℝ)) hsinv_ne
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp [Module.finrank_prod]
  have hsq : |((s⁻¹ ^ 2)⁻¹)| = a := by
    rw [inv_pow, Real.sq_sqrt ha.le, inv_inv, abs_of_pos ha]
  rw [hfin, hsq] at hmap
  rw [← (measurableEmbedding_const_smul₀ hsinv_ne).lintegral_map, hmap,
    lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.2 ha.le), inv_mul_cancel₀ ha.ne',
    ENNReal.ofReal_one, one_mul]

lemma pullCell_compl_eq {ν c m b K r : ℝ} (F : MovingFrame ν c m b K)
    (w : ℝ → ℝ × ℝ → ℂ) (ha : 0 < clockA ν r) (x : ℝ × ℝ) :
    pullCell (clockA ν r) m (compl F w r) x =
      (((wFactor (clockA ν r) m x * (clockA ν r) ^ 2 : ℝ) : ℂ) * w r x) -
        ∑ i : Fin 2, ampl F w r i * pullCell (clockA ν r) m (F.E r i) x := by
  have hsa : Real.sqrt (clockA ν r) ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  unfold pullCell compl movingW JscaleInv
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [mul_div_cancel₀ _ hsa]
  push_cast
  ring

lemma integrable_jb_gauss_scaled {m A : ℝ} (hm : 0 ≤ m) (hA : 0 < A) :
    Integrable (fun x : ℝ × ℝ =>
      B0579.jb x ^ m * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) volume := by
  have hb : 0 < 1 / (8 * A) := by positivity
  have hg : Integrable (fun t : ℝ =>
      (1 + t ^ 2) ^ (2 * m / 2) * Real.exp (-(1 / (8 * A)) * t ^ 2)) :=
    integrable_axialGaussianWeight hb (by linarith)
  have hg' : Integrable (fun t : ℝ =>
      (1 + t ^ 2) ^ m * Real.exp (-(1 / (8 * A)) * t ^ 2)) := by
    simpa [mul_div_cancel_left₀] using hg
  have h := hg'.mul_prod hg'
  refine Integrable.mono' h ?_ (Eventually.of_forall fun x => ?_)
  · have hc : Continuous (fun x : ℝ × ℝ =>
        B0579.jb x ^ m * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) := by
      unfold B0579.jb
      refine Continuous.mul (Continuous.rpow_const (by fun_prop) fun _ => Or.inr hm) (by fun_prop)
    exact hc.aestronglyMeasurable
  · have h1 : 0 ≤ B0579.jb x ^ m * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) :=
      mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (Real.exp_pos _).le
    rw [Real.norm_of_nonneg h1]
    have h2 : B0579.jb x ^ m ≤ (1 + x.1 ^ 2) ^ m * (1 + x.2 ^ 2) ^ m := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      refine Real.rpow_le_rpow (B0579.jb_pos x).le ?_ hm
      unfold B0579.jb
      nlinarith [sq_nonneg x.1, sq_nonneg x.2, mul_nonneg (sq_nonneg x.1) (sq_nonneg x.2)]
    have h3 : Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)) =
        Real.exp (-(1 / (8 * A)) * x.1 ^ 2) * Real.exp (-(1 / (8 * A)) * x.2 ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h3]
    calc B0579.jb x ^ m *
          (Real.exp (-(1 / (8 * A)) * x.1 ^ 2) * Real.exp (-(1 / (8 * A)) * x.2 ^ 2))
        ≤ ((1 + x.1 ^ 2) ^ m * (1 + x.2 ^ 2) ^ m) *
            (Real.exp (-(1 / (8 * A)) * x.1 ^ 2) * Real.exp (-(1 / (8 * A)) * x.2 ^ 2)) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = ((1 + x.1 ^ 2) ^ m * Real.exp (-(1 / (8 * A)) * x.1 ^ 2)) *
            ((1 + x.2 ^ 2) ^ m * Real.exp (-(1 / (8 * A)) * x.2 ^ 2)) := by ring

lemma tendsto_xNorm_W_pull {ν c m t s : ℝ} (hm : 0 ≤ m) (hν : 0 < ν) (ht : 0 ≤ t) (_hts : t ≤ s)
    {tr : UnforcedLeray.B0140.TrainSol ν c}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν c m tr t f w u) (r : ℝ) (hr : r ∈ Icc t s) :
    Tendsto
      (fun r' => xNorm c m (fun x =>
        (((wFactor (clockA ν r') m x * (clockA ν r') ^ 2 : ℝ) : ℂ) * w r' x) -
          (((wFactor (clockA ν r) m x * (clockA ν r) ^ 2 : ℝ) : ℂ) * w r x)))
      (𝓝[Icc t s] r) (𝓝 0) := by
  set α : ℝ → ℝ × ℝ → ℂ := fun r' x =>
    ((wFactor (clockA ν r') m x * (clockA ν r') ^ 2 : ℝ) : ℂ)
  set A₁ : ℝ → ℝ × ℝ → ℂ := fun r' x => α r' x * (w r' x - w r x)
  set A₂ : ℝ → ℝ × ℝ → ℂ := fun r' x => (α r' x - α r x) * w r x
  have hα_cont : ∀ r' : ℝ, Continuous (α r') := fun r' =>
    Complex.continuous_ofReal.comp ((continuous_wFactor m).mul continuous_const)
  have hα_bdd : ∀ r' ∈ Icc t s, ∀ x : ℝ × ℝ, ‖α r' x‖ ≤ (clockA ν s) ^ 2 := by
    intro r' hr' x
    have ha'1 : 1 ≤ clockA ν r' := one_le_clockA hν.le (ht.trans hr'.1)
    have ha's : clockA ν r' ≤ clockA ν s := clockA_mono hν.le hr'.2
    have hw_nn : 0 ≤ wFactor (clockA ν r') m x := wFactor_nonneg (by linarith) x
    have hw_le : wFactor (clockA ν r') m x ≤ 1 := wFactor_le_one ha'1 hm x
    simp only [α, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hw_nn (sq_nonneg _))]
    calc wFactor (clockA ν r') m x * (clockA ν r') ^ 2
        ≤ 1 * (clockA ν s) ^ 2 :=
          mul_le_mul hw_le (pow_le_pow_left₀ (by linarith) ha's 2) (sq_nonneg _) zero_le_one
      _ = (clockA ν s) ^ 2 := one_mul _
  have hA₁ : Tendsto (fun r' => xNorm c m (A₁ r')) (𝓝[Icc t s] r) (𝓝 0) := by
    have hle : ∀ r' ∈ Icc t s,
        xNorm c m (A₁ r') ≤ ENNReal.ofReal ((clockA ν s) ^ 2) * xNorm c m (w r' - w r) := by
      intro r' hr'
      unfold xNorm
      calc eLpNorm (A₁ r') 2 (B0579.cellMeasure c m)
          ≤ eLpNorm (fun x => (((clockA ν s) ^ 2 : ℝ) : ℂ) * (w r' x - w r x)) 2
              (B0579.cellMeasure c m) := by
            refine eLpNorm_mono fun x => ?_
            simp only [A₁, norm_mul, Complex.norm_of_nonneg (sq_nonneg _)]
            exact mul_le_mul_of_nonneg_right (hα_bdd r' hr' x) (norm_nonneg _)
        _ = ENNReal.ofReal ((clockA ν s) ^ 2) * eLpNorm (w r' - w r) 2 (B0579.cellMeasure c m) := by
            have hsmul : (fun x => (((clockA ν s) ^ 2 : ℝ) : ℂ) * (w r' x - w r x)) =
                (((clockA ν s) ^ 2 : ℝ) : ℂ) • (w r' - w r) := rfl
            rw [hsmul, eLpNorm_const_smul, T07.enorm_ofReal_cast (sq_nonneg _)]
    have hsc := (hw.strongCont r hr.1).mono_left
      (nhdsWithin_mono r fun r' (hr' : r' ∈ Icc t s) => (hr'.1 : r' ∈ Ici t))
    have hmul : Tendsto (fun r' => ENNReal.ofReal ((clockA ν s) ^ 2) * xNorm c m (w r' - w r))
        (𝓝[Icc t s] r) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hsc (Or.inr ENNReal.ofReal_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmul
      (Eventually.of_forall fun _ => zero_le) (eventually_nhdsWithin_of_forall hle)
  have hA₂ : Tendsto (fun r' => xNorm c m (A₂ r')) (𝓝[Icc t s] r) (𝓝 0) := by
    have hlint : Tendsto (fun r' => ∫⁻ x, ‖A₂ r' x‖ₑ ^ 2 ∂(B0579.cellMeasure c m))
        (𝓝[Icc t s] r) (𝓝 0) := by
      set C_b : ℝ≥0∞ := ENNReal.ofReal ((2 * (clockA ν s) ^ 2) ^ 2)
      have hwr := hw.memX r hr.1
      have hdom_fin : (∫⁻ x, C_b * ‖w r x‖ₑ ^ 2 ∂(B0579.cellMeasure c m)) ≠ ⊤ := by
        rw [lintegral_const_mul'' _ (hwr.1.enorm.pow_const 2)]
        refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
        have h2 := hwr.2
        rw [T07.eLpNorm_two_eq_lintegral] at h2
        exact fun htop => h2.ne (by rw [htop]; norm_num)
      have hlim : Tendsto (fun r' => ∫⁻ x, ‖A₂ r' x‖ₑ ^ 2 ∂(B0579.cellMeasure c m))
          (𝓝[Icc t s] r) (𝓝 (∫⁻ _ : ℝ × ℝ, 0 ∂(B0579.cellMeasure c m))) := by
        refine MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence'
          (fun x => C_b * ‖w r x‖ₑ ^ 2) ?_ ?_ hdom_fin ?_
        · filter_upwards [self_mem_nhdsWithin] with r' _hr'
          exact (((hα_cont r').sub (hα_cont r)).aemeasurable.mul
            hwr.1.aemeasurable).enorm.pow_const 2
        · filter_upwards [self_mem_nhdsWithin] with r' hr'
          refine Eventually.of_forall fun x => ?_
          simp only [A₂, enorm_mul, mul_pow]
          refine mul_le_mul_of_nonneg_right ?_ zero_le
          have htri : ‖α r' x - α r x‖ ≤ 2 * (clockA ν s) ^ 2 := by
            calc ‖α r' x - α r x‖ ≤ ‖α r' x‖ + ‖α r x‖ := norm_sub_le _ _
              _ ≤ (clockA ν s) ^ 2 + (clockA ν s) ^ 2 :=
                  add_le_add (hα_bdd r' hr' x) (hα_bdd r hr x)
              _ = 2 * (clockA ν s) ^ 2 := by ring
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) htri 2)
        · refine Eventually.of_forall fun x => ?_
          have hc_α : ContinuousOn (fun r' => α r' x) (Icc t s) :=
            Complex.continuous_ofReal.comp_continuousOn
              ((continuousOn_wFactor_clockA m hν ht x).mul ((continuousOn_clockA _).pow 2))
          have hsub0 : Tendsto (fun r' => α r' x - α r x) (𝓝[Icc t s] r) (𝓝 0) := by
            simpa using (hc_α r hr).tendsto.sub (tendsto_const_nhds (x := α r x))
          have hm0 : Tendsto (fun r' => (α r' x - α r x) * w r x) (𝓝[Icc t s] r) (𝓝 0) := by
            simpa using hsub0.mul tendsto_const_nhds
          have he0 : Tendsto (fun r' => ‖A₂ r' x‖ₑ ^ 2) (𝓝[Icc t s] r) (𝓝 (‖(0 : ℂ)‖ₑ ^ 2)) :=
            (((ENNReal.continuous_pow 2).comp continuous_enorm).tendsto 0).comp hm0
          simpa using he0
      simpa using hlim
    have hrpow : Tendsto (fun r' => (∫⁻ x, ‖A₂ r' x‖ₑ ^ 2 ∂(B0579.cellMeasure c m)) ^ (1 / 2 : ℝ))
        (𝓝[Icc t s] r) (𝓝 ((0 : ℝ≥0∞) ^ (1 / 2 : ℝ))) :=
      (ENNReal.continuous_rpow_const.tendsto 0).comp hlint
    simpa only [Function.comp_def, T07.eLpNorm_two_eq_lintegral, xNorm,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hrpow
  have hsum : Tendsto (fun r' => xNorm c m (A₁ r') + xNorm c m (A₂ r'))
      (𝓝[Icc t s] r) (𝓝 0) := by
    simpa using hA₁.add hA₂
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with r' hr'
  have heq : (fun x => α r' x * w r' x - α r x * w r x) = A₁ r' + A₂ r' := by
    funext x; simp only [A₁, A₂, Pi.add_apply]; ring
  unfold xNorm
  rw [heq]
  have hm1 : AEStronglyMeasurable (A₁ r') (B0579.cellMeasure c m) :=
    (hα_cont r').aestronglyMeasurable.mul ((hw.memX r' hr'.1).1.sub (hw.memX r hr.1).1)
  have hm2 : AEStronglyMeasurable (A₂ r') (B0579.cellMeasure c m) :=
    ((hα_cont r').sub (hα_cont r)).aestronglyMeasurable.mul (hw.memX r hr.1).1
  exact eLpNorm_add_le hm1 hm2 (by norm_num)

lemma tendsto_xNorm_E_pull (κ : PlanarFrameKernels) {ν m t s : ℝ}
    (hm : 0 ≤ m) (hν : 0 < ν) (ht : 0 ≤ t) (hts : t ≤ s)
    (hd1 : ∀ r ∈ Icc t s, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (i : Fin 2) (r : ℝ) (hr : r ∈ Icc t s) :
    Tendsto
      (fun r' => xNorm (ν ^ (-2 : ℝ)) m
        (pullCell (clockA ν r') m (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) i) -
          pullCell (clockA ν r) m (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i)))
      (𝓝[Icc t s] r) (𝓝 0) := by
  set Ep : ℝ → ℝ × ℝ → ℂ := fun r' =>
    pullCell (clockA ν r') m (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) i)
  obtain ⟨M, hM0, hM⟩ := perE_pointwise κ
  have hEp_cont : ∀ r' ∈ Icc t s, Continuous (Ep r') := by
    intro r' hr'
    have hd_pos : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν r') := lt_of_lt_of_le zero_lt_one (hd1 r' hr')
    unfold Ep pullCell
    exact (Complex.continuous_ofReal.comp (continuous_wFactor m)).mul
      ((FrameCont.perE_continuous κ hd_pos i).comp
        ((continuous_fst.div_const _).prodMk (continuous_snd.div_const _)))
  have hEp_bdd : ∀ r' ∈ Icc t s, ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      ‖Ep r' x‖ ≤ M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * clockA ν s)) := by
    intro r' hr' x hx
    set a' := clockA ν r'
    set d' := cellLen (ν ^ (-2 : ℝ)) a'
    have ha'1 : 1 ≤ a' := one_le_clockA hν.le (ht.trans hr'.1)
    have ha's : a' ≤ clockA ν s := clockA_mono hν.le hr'.2
    have hsa' : 0 < Real.sqrt a' := Real.sqrt_pos.2 (by linarith)
    have hy : (x.1 / Real.sqrt a', x.2 / Real.sqrt a') ∈ B0579.cell d' := by
      have hsmul : Real.sqrt a' • (x.1 / Real.sqrt a', x.2 / Real.sqrt a') ∈
          B0579.cell (d' * Real.sqrt a') := by
        have heq1 : Real.sqrt a' • (x.1 / Real.sqrt a', x.2 / Real.sqrt a') = x := by
          ext <;> simp [smul_eq_mul, mul_div_cancel₀ _ hsa'.ne']
        have heq2 : d' * Real.sqrt a' = ν ^ (-2 : ℝ) := by
          simp only [d', cellLen, div_mul_cancel₀ _ hsa'.ne']
        rwa [heq1, heq2]
      exact (T07.smul_mem_cell_iff d' (Real.sqrt a') hsa' _).1 hsmul
    have hw_nn : 0 ≤ wFactor a' m x := wFactor_nonneg (by linarith) x
    have hw_le : wFactor a' m x ≤ 1 := wFactor_le_one ha'1 hm x
    have hE := hM d' (hd1 r' hr') i _ hy
    have hexp_le : Real.exp (-((x.1 / Real.sqrt a') ^ 2 + (x.2 / Real.sqrt a') ^ 2) / 16) ≤
        Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * clockA ν s)) := by
      rw [div_pow, div_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ a')]
      have heq : -((x.1 ^ 2 / a' + x.2 ^ 2 / a') / 16) = -(x.1 ^ 2 + x.2 ^ 2) / (16 * a') := by
        ring
      rw [neg_div, heq, neg_div, neg_div]
      refine Real.exp_le_exp.2 (neg_le_neg ?_)
      exact div_le_div_of_nonneg_left (add_nonneg (sq_nonneg x.1) (sq_nonneg x.2))
        (by linarith) (by linarith)
    simp only [Ep, pullCell, norm_mul, Complex.norm_real]
    rw [Real.norm_of_nonneg hw_nn]
    calc wFactor a' m x * ‖perE κ d' i (x.1 / Real.sqrt a', x.2 / Real.sqrt a')‖
        ≤ 1 * (M * Real.exp (-((x.1 / Real.sqrt a') ^ 2 + (x.2 / Real.sqrt a') ^ 2) / 16)) :=
          mul_le_mul hw_le hE (norm_nonneg _) zero_le_one
      _ ≤ M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * clockA ν s)) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left hexp_le hM0
  have hlint : Tendsto
      (fun r' => ∫⁻ x, ‖Ep r' x - Ep r x‖ₑ ^ 2 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) m))
      (𝓝[Icc t s] r) (𝓝 0) := by
    have hAs_pos : 0 < clockA ν s := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le (ht.trans hts))
    set dom : ℝ × ℝ → ℝ≥0∞ := fun x =>
      ENNReal.ofReal ((2 * M) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * clockA ν s)))
    have hdom_meas : Measurable dom := by
      unfold dom
      refine ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp ?_))
      exact (((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)).neg).div_const _
    have hdom_fin : (∫⁻ x, dom x ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) m)) ≠ ⊤ := by
      have hJi := (integrable_jb_gauss_scaled hm hAs_pos).const_mul ((2 * M) ^ 2)
      have hle : (∫⁻ x, dom x ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) m)) ≤
          ∫⁻ x, ENNReal.ofReal ((2 * M) ^ 2 *
            (B0579.jb x ^ m * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * clockA ν s)))) := by
        calc ∫⁻ x, dom x ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) m)
            = ∫⁻ x, (B0579.density m x : ℝ≥0∞) * dom x
                ∂(volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))) := by
              unfold B0579.cellMeasure
              exact lintegral_withDensity_eq_lintegral_mul _
                (B0579.measurable_density m).coe_nnreal_ennreal hdom_meas
          _ ≤ ∫⁻ x, (B0579.density m x : ℝ≥0∞) * dom x :=
              lintegral_mono' Measure.restrict_le_self le_rfl
          _ = _ := by
              refine lintegral_congr fun x => ?_
              rw [T07.density_coe, ← ENNReal.ofReal_mul (Real.rpow_nonneg (B0579.jb_pos x).le m)]
              congr 1; ring
      refine ne_top_of_le_ne_top ?_ hle
      rw [← ofReal_integral_eq_lintegral_ofReal hJi
        (Eventually.of_forall fun x => mul_nonneg (sq_nonneg _)
          (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le m) (Real.exp_pos _).le))]
      exact ENNReal.ofReal_ne_top
    have hlim : Tendsto
        (fun r' => ∫⁻ x, ‖Ep r' x - Ep r x‖ₑ ^ 2 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) m))
        (𝓝[Icc t s] r) (𝓝 (∫⁻ _ : ℝ × ℝ, 0 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) m))) := by
      refine MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence
        dom ?_ ?_ hdom_fin ?_
      · filter_upwards [self_mem_nhdsWithin] with r' hr'
        exact ((hEp_cont r' hr').sub (hEp_cont r hr)).measurable.enorm.pow_const 2
      · filter_upwards [self_mem_nhdsWithin] with r' hr'
        refine (B0579.cellMeasure_ac (ν ^ (-2 : ℝ)) m).ae_le ?_
        filter_upwards [ae_restrict_mem (B0579.measurableSet_cell _)] with x hx
        have htri : ‖Ep r' x - Ep r x‖ ≤
            2 * M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * clockA ν s)) := by
          calc ‖Ep r' x - Ep r x‖ ≤ ‖Ep r' x‖ + ‖Ep r x‖ := norm_sub_le _ _
            _ ≤ M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * clockA ν s)) +
                  M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * clockA ν s)) :=
                add_le_add (hEp_bdd r' hr' x hx) (hEp_bdd r hr x hx)
            _ = 2 * M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * clockA ν s)) := by ring
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖Ep r' x - Ep r x‖ ^ 2
            ≤ (2 * M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * clockA ν s))) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) htri 2
          _ = (2 * M) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * clockA ν s)) := by
              rw [mul_pow, ← Real.exp_nat_mul]
              congr 2; push_cast; ring
      · refine Eventually.of_forall fun x => ?_
        obtain ⟨C_e, hC_e⟩ := FrameCont.e_translate_bound κ
        have hC_e0 : 0 ≤ max C_e 0 := le_max_right _ _
        have hC_e' : ∀ z, ‖κ.e i z‖ ≤ max C_e 0 * (1 + |z.1|) ^ (-(2 : ℝ)) := fun z =>
          (hC_e i z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        have hc_Ep : ContinuousOn (fun r' => Ep r' x) (Icc t s) :=
          (Complex.continuous_ofReal.comp_continuousOn
            (continuousOn_wFactor_clockA m hν ht x)).mul
            (continuousOn_perSum_scaled (κ.e_cont i) hC_e0 hC_e' hν ht hd1 x)
        have hsub0 : Tendsto (fun r' => Ep r' x - Ep r x) (𝓝[Icc t s] r) (𝓝 0) := by
          simpa using (hc_Ep r hr).tendsto.sub (tendsto_const_nhds (x := Ep r x))
        have he0 : Tendsto (fun r' => ‖Ep r' x - Ep r x‖ₑ ^ 2) (𝓝[Icc t s] r)
            (𝓝 (‖(0 : ℂ)‖ₑ ^ 2)) :=
          (((ENNReal.continuous_pow 2).comp continuous_enorm).tendsto 0).comp hsub0
        simpa using he0
    simpa using hlim
  have hrpow : Tendsto
      (fun r' => (∫⁻ x, ‖Ep r' x - Ep r x‖ₑ ^ 2 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) m)) ^ (1 / 2 : ℝ))
      (𝓝[Icc t s] r) (𝓝 ((0 : ℝ≥0∞) ^ (1 / 2 : ℝ))) :=
    (ENNReal.continuous_rpow_const.tendsto 0).comp hlint
  unfold xNorm
  simp_rw [T07.eLpNorm_two_eq_lintegral]
  simpa only [Function.comp_def, Pi.sub_apply, Ep,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hrpow

lemma tendsto_xNorm_mode_pull (κ : PlanarFrameKernels) {D₁ ν m b K t s : ℝ}
    (hD₁ : ∀ d : ℝ, D₁ ≤ d → ∀ i j : Fin 2,
      ‖perGram κ d i j - (if i = j then 1 else 0)‖ ≤ 1 / 4)
    (hm : 8 < m) (hν : 0 < ν) (ht : 0 ≤ t) (hts : t ≤ s)
    (hbs : b ≤ clockTheta ν s) (hF : PerFrameFacts κ ν m b K)
    (hd : ∀ r ∈ Icc t s, max D₁ 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u)
    (i : Fin 2) (r : ℝ) (hr : r ∈ Icc t s) :
    let F := periodizedFrame κ ν m b K hν hF
    Tendsto
      (fun r' => xNorm (ν ^ (-2 : ℝ)) m (fun x =>
        ampl F w r' i * pullCell (clockA ν r') m (F.E r' i) x -
          ampl F w r i * pullCell (clockA ν r) m (F.E r i) x))
      (𝓝[Icc t s] r) (𝓝 0) := by
  intro F
  set Ep : ℝ → ℝ × ℝ → ℂ := fun r' =>
    pullCell (clockA ν r') m (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) i)
  have hd1 : ∀ r' ∈ Icc t s, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r') := fun r' hr' =>
    le_trans (le_max_right _ _) (hd r' hr')
  have hEp_cont : ∀ r' ∈ Icc t s, Continuous (Ep r') := by
    intro r' hr'
    have hd_pos : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν r') := lt_of_lt_of_le zero_lt_one (hd1 r' hr')
    unfold Ep pullCell
    exact (Complex.continuous_ofReal.comp (continuous_wFactor m)).mul
      ((FrameCont.perE_continuous κ hd_pos i).comp
        ((continuous_fst.div_const _).prodMk (continuous_snd.div_const _)))
  set B₁ : ℝ → ℝ × ℝ → ℂ := fun r' x => (ampl F w r' i - ampl F w r i) * Ep r' x
  set B₂ : ℝ → ℝ × ℝ → ℂ := fun r' x => ampl F w r i * (Ep r' x - Ep r x)
  have hB₁ : Tendsto (fun r' => xNorm (ν ^ (-2 : ℝ)) m (B₁ r')) (𝓝[Icc t s] r) (𝓝 0) := by
    have hle : ∀ r' ∈ Icc t s,
        xNorm (ν ^ (-2 : ℝ)) m (B₁ r') ≤
          ENNReal.ofReal ‖ampl F w r' i - ampl F w r i‖ * ENNReal.ofReal K := by
      intro r' hr'
      have hr'0 : 0 ≤ r' := ht.trans hr'.1
      have ha' : 0 < clockA ν r' := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hr'0)
      have hbr' : b ≤ clockTheta ν r' := hbs.trans (theta_anti hν hr'0 hr'.2)
      have hsmul : B₁ r' = (ampl F w r' i - ampl F w r i) • Ep r' := rfl
      unfold xNorm
      rw [hsmul, eLpNorm_const_smul, ← ofReal_norm]
      change ENNReal.ofReal ‖ampl F w r' i - ampl F w r i‖ * xNorm (ν ^ (-2 : ℝ)) m (Ep r') ≤ _
      rw [xNorm_pullCell (ν ^ (-2 : ℝ)) m (clockA ν r') ha'
        (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) i)]
      exact mul_le_mul_of_nonneg_left (hF.2.1 r' hr'0 hbr' i) zero_le
    have hampl : Tendsto (fun r' => ampl F w r' i - ampl F w r i) (𝓝[Icc t s] r) (𝓝 0) := by
      simpa [F] using (continuousOn_ampl κ hD₁ hm hν ht hts hbs hF hd hw i r hr).tendsto.sub
        (tendsto_const_nhds (x := ampl F w r i))
    have hnorm0 : Tendsto (fun r' => ENNReal.ofReal ‖ampl F w r' i - ampl F w r i‖)
        (𝓝[Icc t s] r) (𝓝 0) := by
      simpa [Function.comp_def] using (continuous_enorm.tendsto (0 : ℂ)).comp hampl
    have hmul0 : Tendsto
        (fun r' => ENNReal.ofReal ‖ampl F w r' i - ampl F w r i‖ * ENNReal.ofReal K)
        (𝓝[Icc t s] r) (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const hnorm0 (Or.inr ENNReal.ofReal_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmul0
      (Eventually.of_forall fun _ => zero_le) (eventually_nhdsWithin_of_forall hle)
  have hB₂ : Tendsto (fun r' => xNorm (ν ^ (-2 : ℝ)) m (B₂ r')) (𝓝[Icc t s] r) (𝓝 0) := by
    have heq : (fun r' => xNorm (ν ^ (-2 : ℝ)) m (B₂ r')) =
        fun r' => ENNReal.ofReal ‖ampl F w r i‖ * xNorm (ν ^ (-2 : ℝ)) m (Ep r' - Ep r) := by
      funext r'
      have hsmul : B₂ r' = ampl F w r i • (Ep r' - Ep r) := rfl
      unfold xNorm
      rw [hsmul, eLpNorm_const_smul, ← ofReal_norm]
    rw [heq]
    have hm0 : (0 : ℝ) ≤ m := by linarith
    have hEp_t := tendsto_xNorm_E_pull κ hm0 hν ht hts hd1 i r hr
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul hEp_t (Or.inr (@ENNReal.ofReal_ne_top ‖ampl F w r i‖))
  have hsum : Tendsto (fun r' => xNorm (ν ^ (-2 : ℝ)) m (B₁ r') + xNorm (ν ^ (-2 : ℝ)) m (B₂ r'))
      (𝓝[Icc t s] r) (𝓝 0) := by
    simpa using hB₁.add hB₂
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with r' hr'
  have heq : (fun x => ampl F w r' i * pullCell (clockA ν r') m (F.E r' i) x -
      ampl F w r i * pullCell (clockA ν r) m (F.E r i) x) = B₁ r' + B₂ r' := by
    funext x
    change ampl F w r' i * Ep r' x - ampl F w r i * Ep r x = B₁ r' x + B₂ r' x
    simp only [B₁, B₂]; ring
  unfold xNorm
  rw [heq]
  have hm1 : AEStronglyMeasurable (B₁ r') (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) :=
    (continuous_const.mul (hEp_cont r' hr')).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (B₂ r') (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) :=
    (continuous_const.mul ((hEp_cont r' hr').sub (hEp_cont r hr))).aestronglyMeasurable
  exact eLpNorm_add_le hm1 hm2 (by norm_num)

lemma continuousOn_xNorm_compl (κ : PlanarFrameKernels) {D₁ ν m b K t s : ℝ}
    (hD₁ : ∀ d : ℝ, D₁ ≤ d → ∀ i j : Fin 2,
      ‖perGram κ d i j - (if i = j then 1 else 0)‖ ≤ 1 / 4)
    (hm : 8 < m) (hν : 0 < ν) (ht : 0 ≤ t) (hts : t ≤ s)
    (hbs : b ≤ clockTheta ν s) (hF : PerFrameFacts κ ν m b K)
    (hd : ∀ r ∈ Icc t s, max D₁ 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u) :
    ContinuousOn
      (fun r => xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
        (compl (periodizedFrame κ ν m b K hν hF) w r))
      (Icc t s) := by
  set F := periodizedFrame κ ν m b K hν hF
  set φ : ℝ → ℝ × ℝ → ℂ := fun r => pullCell (clockA ν r) m (compl F w r)
  have hnorm_eq : EqOn
      (fun r => xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (compl F w r))
      (fun r => xNorm (ν ^ (-2 : ℝ)) (- -m) (φ r)) (Icc t s) := by
    intro r hr
    dsimp only
    have ha : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le (ht.trans hr.1))
    rw [neg_neg, ← xNorm_pullCell (ν ^ (-2 : ℝ)) m (clockA ν r) ha (compl F w r)]
  have hφ_aesm : ∀ r ∈ Icc t s, AEStronglyMeasurable (φ r)
      (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := by
    intro r hr
    have ha : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le (ht.trans hr.1))
    have hd_pos : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
      lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) (hd r hr))
    have heq : φ r = fun x =>
        (((wFactor (clockA ν r) m x * (clockA ν r) ^ 2 : ℝ) : ℂ) * w r x) -
          ∑ i : Fin 2, ampl F w r i * pullCell (clockA ν r) m (F.E r i) x :=
      funext (pullCell_compl_eq F w ha)
    rw [heq]
    have hmW : AEStronglyMeasurable
        (fun x => (((wFactor (clockA ν r) m x * (clockA ν r) ^ 2 : ℝ) : ℂ) * w r x))
        (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) :=
      (Complex.continuous_ofReal.comp ((continuous_wFactor m).mul continuous_const)).aestronglyMeasurable.mul
        (hw.memX r hr.1).1
    have hmE : AEStronglyMeasurable
        (fun x => ∑ i : Fin 2, ampl F w r i * pullCell (clockA ν r) m (F.E r i) x)
        (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := by
      refine (continuous_finsetSum Finset.univ fun i _ => continuous_const.mul ?_).aestronglyMeasurable
      change Continuous (pullCell (clockA ν r) m (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i))
      unfold pullCell
      exact (Complex.continuous_ofReal.comp (continuous_wFactor m)).mul
        ((FrameCont.perE_continuous κ hd_pos i).comp
          ((continuous_fst.div_const _).prodMk (continuous_snd.div_const _)))
    exact hmW.sub hmE
  have hφ_mem : ∀ r ∈ Icc t s, MemLp (φ r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (- -m)) := by
    intro r hr
    rw [neg_neg]
    refine ⟨hφ_aesm r hr, ?_⟩
    have ha : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le (ht.trans hr.1))
    have hbr : ∀ r' ∈ Icc t s, b ≤ clockTheta ν r' := fun r' hr' =>
      hbs.trans (theta_anti hν (ht.trans hr'.1) hr'.2)
    have hpb := (pointwise_bounds F hν ht hts (by linarith) hbr hw
      (ENNReal.ofReal (max K 0)) (ENNReal.ofReal_le_ofReal (le_max_left K 0)) r hr).2
    have hS : (⨆ r' ∈ Icc t s, xNorm (ν ^ (-2 : ℝ)) m (w r')) ≠ ⊤ := xNorm_bounded_on_Icc hw
    have htop : ENNReal.ofReal ((clockA ν s) ^ ((3 : ℝ) / 2)) *
          (⨆ r' ∈ Icc t s, xNorm (ν ^ (-2 : ℝ)) m (w r')) +
        ENNReal.ofReal (max K 0) * (2 * (ENNReal.ofReal (max K 0) *
          (ENNReal.ofReal ((clockA ν s) ^ ((3 : ℝ) / 2)) *
            ⨆ r' ∈ Icc t s, xNorm (ν ^ (-2 : ℝ)) m (w r')))) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS)))⟩
    change xNorm (ν ^ (-2 : ℝ)) m (φ r) < ⊤
    rw [xNorm_pullCell (ν ^ (-2 : ℝ)) m (clockA ν r) ha (compl F w r)]
    exact lt_of_le_of_lt hpb (lt_top_iff_ne_top.2 htop)
  have hφ_cont : ∀ r ∈ Icc t s,
      Tendsto (fun r' => xNorm (ν ^ (-2 : ℝ)) (- -m) (φ r' - φ r)) (𝓝[Icc t s] r) (𝓝 0) := by
    intro r hr
    rw [neg_neg]
    set dW : ℝ → ℝ × ℝ → ℂ := fun r' x =>
      (((wFactor (clockA ν r') m x * (clockA ν r') ^ 2 : ℝ) : ℂ) * w r' x) -
        (((wFactor (clockA ν r) m x * (clockA ν r) ^ 2 : ℝ) : ℂ) * w r x)
    set dE : Fin 2 → ℝ → ℝ × ℝ → ℂ := fun i r' x =>
      ampl F w r' i * pullCell (clockA ν r') m (F.E r' i) x -
        ampl F w r i * pullCell (clockA ν r) m (F.E r i) x
    have hm0 : (0 : ℝ) ≤ m := by linarith
    have hdW : Tendsto (fun r' => xNorm (ν ^ (-2 : ℝ)) m (dW r')) (𝓝[Icc t s] r) (𝓝 0) :=
      tendsto_xNorm_W_pull hm0 hν ht hts hw r hr
    have hdE0 : Tendsto (fun r' => xNorm (ν ^ (-2 : ℝ)) m (dE 0 r')) (𝓝[Icc t s] r) (𝓝 0) :=
      tendsto_xNorm_mode_pull κ hD₁ hm hν ht hts hbs hF hd hw 0 r hr
    have hdE1 : Tendsto (fun r' => xNorm (ν ^ (-2 : ℝ)) m (dE 1 r')) (𝓝[Icc t s] r) (𝓝 0) :=
      tendsto_xNorm_mode_pull κ hD₁ hm hν ht hts hbs hF hd hw 1 r hr
    have hsum0 : Tendsto
        (fun r' => xNorm (ν ^ (-2 : ℝ)) m (dW r') +
          (xNorm (ν ^ (-2 : ℝ)) m (dE 0 r') + xNorm (ν ^ (-2 : ℝ)) m (dE 1 r')))
        (𝓝[Icc t s] r) (𝓝 0) := by
      simpa using hdW.add (hdE0.add hdE1)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum0
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with r' hr'
    have ha : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le (ht.trans hr.1))
    have ha' : 0 < clockA ν r' := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le (ht.trans hr'.1))
    have heq : φ r' - φ r = dW r' + -(dE 0 r' + dE 1 r') := by
      funext x
      simp only [φ, Pi.sub_apply, Pi.add_apply, Pi.neg_apply,
        pullCell_compl_eq F w ha', pullCell_compl_eq F w ha, Fin.sum_univ_two, dW, dE]
      ring
    have hmW : AEStronglyMeasurable (dW r') (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := by
      have hc' : Continuous (fun x => ((wFactor (clockA ν r') m x * (clockA ν r') ^ 2 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp ((continuous_wFactor m).mul continuous_const)
      have hc : Continuous (fun x => ((wFactor (clockA ν r) m x * (clockA ν r) ^ 2 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp ((continuous_wFactor m).mul continuous_const)
      exact (hc'.aestronglyMeasurable.mul (hw.memX r' hr'.1).1).sub
        (hc.aestronglyMeasurable.mul (hw.memX r hr.1).1)
    have hmE : ∀ i : Fin 2, AEStronglyMeasurable (dE i r') (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := by
      intro i
      have hd_pos' : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν r') :=
        lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) (hd r' hr'))
      have hd_pos : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
        lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) (hd r hr))
      have hcE' : Continuous (pullCell (clockA ν r') m (F.E r' i)) := by
        change Continuous (pullCell (clockA ν r') m
          (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) i))
        unfold pullCell
        exact (Complex.continuous_ofReal.comp (continuous_wFactor m)).mul
          ((FrameCont.perE_continuous κ hd_pos' i).comp
            ((continuous_fst.div_const _).prodMk (continuous_snd.div_const _)))
      have hcE : Continuous (pullCell (clockA ν r) m (F.E r i)) := by
        change Continuous (pullCell (clockA ν r) m
          (perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i))
        unfold pullCell
        exact (Complex.continuous_ofReal.comp (continuous_wFactor m)).mul
          ((FrameCont.perE_continuous κ hd_pos i).comp
            ((continuous_fst.div_const _).prodMk (continuous_snd.div_const _)))
      exact ((continuous_const.mul hcE').sub (continuous_const.mul hcE)).aestronglyMeasurable
    unfold xNorm
    rw [heq]
    calc eLpNorm (dW r' + -(dE 0 r' + dE 1 r')) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m)
        ≤ eLpNorm (dW r') 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) +
            eLpNorm (-(dE 0 r' + dE 1 r')) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) :=
          eLpNorm_add_le hmW ((hmE 0).add (hmE 1)).neg (by norm_num)
      _ = eLpNorm (dW r') 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) +
            eLpNorm (dE 0 r' + dE 1 r') 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := by
          rw [eLpNorm_neg]
      _ ≤ eLpNorm (dW r') 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) +
            (eLpNorm (dE 0 r') 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) +
              eLpNorm (dE 1 r') 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m)) :=
          add_le_add le_rfl (eLpNorm_add_le (hmE 0) (hmE 1) (by norm_num))
  have hc_φ : ContinuousOn (fun r => xNorm (ν ^ (-2 : ℝ)) (- -m) (φ r)) (Icc t s) :=
    fun r hr => xNorm_continuousWithinAt_of_strongCont hφ_mem hφ_cont r hr
  exact hc_φ.congr hnorm_eq

end FlowMeas

/-- **Leaf 1 (`FrameFlowMeasurable`, SP 2894-2902, 2975-3004)**: along any weak linearised flow,
for `m > 8`, `b` large and `ν` small, the unnormalised amplitude norm and complement norm of the
periodized frame are a.e.-measurable on `Icc t s`. -/
theorem frameFlowMeasurable (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.FrameFlowMeasurable κ := by
  intro _hκ m hm K
  obtain ⟨D₁, hD₁⟩ := perGramNear_of κ (perGramUnfold κ) (perGramTail κ) (1 / 4) (by norm_num)
  set D : ℝ := max D₁ 1
  have hD0 : 0 ≤ D := le_trans zero_le_one (le_max_right D₁ 1)
  refine ⟨1, le_rfl, fun b hb => ⟨1 / (D + 1) ^ 2, by positivity, ?_⟩⟩
  intro ν hν hF tr _htr t s ht hts hbs f w u hw _hz
  have hd : ∀ r ∈ Icc t s, max D₁ 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := by
    intro r hr
    have hr0 : 0 ≤ r := ht.trans hr.1
    have hbr : b ≤ clockTheta ν r := hbs.trans (theta_anti hν.1 hr0 hr.2)
    exact cellLen_ge hD0 hν.1 hν.2 hb hr0 hbr
  refine ⟨?_, ?_⟩
  · exact (FlowMeas.continuousOn_amplNorm κ hD₁ hm hν.1 ht hts hbs hF hd hw).aemeasurable
      measurableSet_Icc
  · exact (FlowMeas.continuousOn_xNorm_compl κ hD₁ hm hν.1 ht hts hbs hF hd hw).aemeasurable
      measurableSet_Icc

end UnforcedLeray.Short.IIIa
