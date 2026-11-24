import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T17

/-!
# Part III-a, task `PartIII-a:T17/4`: `sep:moment-split` (SP 3735-3740, N_1)

Jensen in `L²(dq/c)` for each `(x', Y)`, then the cheap Minkowski form
`|F - F̄|² ≤ 2|F|² + 2|F̄|²`, giving the constants `1` and `2`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem t17m_tn_sq (M : Matrix (Fin 3) (Fin 3) ℝ) : tensorNorm M ^ 2 = ∑ i, ∑ j, M i j ^ 2 := by
  unfold tensorNorm
  rw [Real.sq_sqrt (by positivity)]

theorem t17m_entry_sq_le (M : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    M i j ^ 2 ≤ tensorNorm M ^ 2 := by
  rw [t17m_tn_sq]
  have h1 : M i j ^ 2 ≤ ∑ j', M i j' ^ 2 :=
    Finset.single_le_sum (f := fun j' => M i j' ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', M i j' ^ 2 ≤ ∑ i', ∑ j', M i' j' ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', M i' j' ^ 2)
      (fun k _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i)
  linarith

theorem t17m_sub_sq_le (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    tensorNorm (A - B) ^ 2 ≤ 2 * tensorNorm A ^ 2 + 2 * tensorNorm B ^ 2 := by
  rw [t17m_tn_sq, t17m_tn_sq, t17m_tn_sq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  simp only [Matrix.sub_apply]
  nlinarith [sq_nonneg (A i j + B i j)]

/-- Algebra behind Jensen: `m = c⁻¹ I`, `I = ∫ g` gives `m² ≤ c⁻¹ ∫ g²`. -/
theorem t17m_sq_aux (c : ℝ) (hc : 0 < c) (g : ℝ → ℝ) (hg : IntegrableOn g (Ioc 0 c))
    (hg2 : IntegrableOn (fun q => g q ^ 2) (Ioc 0 c)) (m I : ℝ)
    (hI : I = ∫ q in Ioc 0 c, g q) (hm : m = c⁻¹ * I) :
    m ^ 2 ≤ c⁻¹ * ∫ q in Ioc 0 c, g q ^ 2 := by
  have hIm : I = c * m := by
    rw [hm]; field_simp
  have hcst : IntegrableOn (fun _ : ℝ => m ^ 2) (Ioc 0 c) := integrableOn_const (by simp)
  have hi1 : IntegrableOn (fun q => g q ^ 2 - 2 * m * g q) (Ioc 0 c) :=
    hg2.sub (hg.const_mul _)
  have h0 : 0 ≤ ∫ q in Ioc 0 c, (g q - m) ^ 2 := integral_nonneg (fun q => sq_nonneg _)
  have hexp : ∫ q in Ioc 0 c, (g q - m) ^ 2 =
      (∫ q in Ioc 0 c, g q ^ 2) - 2 * m * I + c * m ^ 2 := by
    have e : (fun q => (g q - m) ^ 2) = fun q => (g q ^ 2 - 2 * m * g q) + m ^ 2 := by
      funext q; ring
    rw [e, integral_add hi1 hcst, integral_sub hg2 (hg.const_mul _), integral_const_mul,
      setIntegral_const, hI]
    simp [Real.volume_real_Ioc_of_le hc.le, smul_eq_mul]
  have h1 : c * m ^ 2 ≤ ∫ q in Ioc 0 c, g q ^ 2 := by
    rw [hexp, hIm] at h0
    nlinarith
  calc m ^ 2 = c⁻¹ * (c * m ^ 2) := by field_simp
    _ ≤ c⁻¹ * ∫ q in Ioc 0 c, g q ^ 2 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hc.le)

theorem t17m_int_entries (c : ℝ) (F' : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hm : ∀ i j, Measurable fun q => F' q i j)
    (hI : IntegrableOn (fun q => tensorNorm (F' q) ^ 2) (Ioc 0 c)) (i j : Fin 3) :
    IntegrableOn (fun q => F' q i j) (Ioc 0 c) ∧ IntegrableOn (fun q => F' q i j ^ 2) (Ioc 0 c) := by
  have hsq : IntegrableOn (fun q => F' q i j ^ 2) (Ioc 0 c) := by
    refine Integrable.mono' hI ((hm i j).pow_const 2).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun q => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact t17m_entry_sq_le _ i j
  refine ⟨?_, hsq⟩
  have hc1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 c) := integrableOn_const (by simp)
  refine Integrable.mono' (hc1.add hI) (hm i j).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun q => ?_)
  have h2 : F' q i j ^ 2 ≤ tensorNorm (F' q) ^ 2 := t17m_entry_sq_le _ i j
  rw [Real.norm_eq_abs]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (|F' q i j| - 1), sq_abs (F' q i j)]

theorem t17m_jensen_mat (c : ℝ) (hc : 0 < c) (F' : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hm : ∀ i j, Measurable fun q => F' q i j)
    (hI : IntegrableOn (fun q => tensorNorm (F' q) ^ 2) (Ioc 0 c)) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : ∀ i j, M i j = c⁻¹ * ∫ q in Ioc 0 c, F' q i j) :
    tensorNorm M ^ 2 ≤ c⁻¹ * ∫ q in Ioc 0 c, tensorNorm (F' q) ^ 2 := by
  have hent := fun i j => t17m_int_entries c F' hm hI i j
  rw [t17m_tn_sq]
  simp only [hM]
  have hsum : ∑ i, ∑ j, (c⁻¹ * ∫ q in Ioc 0 c, F' q i j) ^ 2 ≤
      ∑ i, ∑ j, c⁻¹ * ∫ q in Ioc 0 c, F' q i j ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact t17m_sq_aux c hc (fun q => F' q i j) (hent i j).1 (hent i j).2
      _ _ rfl rfl
  refine hsum.trans (le_of_eq ?_)
  have hint : ∀ i j, Integrable (fun q => F' q i j ^ 2) (volume.restrict (Ioc 0 c)) :=
    fun i j => (hent i j).2
  have e1 : ∫ q in Ioc 0 c, ∑ i, ∑ j, F' q i j ^ 2 = ∑ i, ∑ j, ∫ q in Ioc 0 c, F' q i j ^ 2 := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hint i j)]
  have e2 : ∫ q in Ioc 0 c, tensorNorm (F' q) ^ 2 = ∫ q in Ioc 0 c, ∑ i, ∑ j, F' q i j ^ 2 := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun q => t17m_tn_sq (F' q))
  rw [e2, e1, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

theorem t17m_mono_ofReal_sq (c : ℝ) (hc : 0 < c) (F' : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hm : ∀ i j, Measurable fun q => F' q i j)
    (hI : IntegrableOn (fun q => tensorNorm (F' q) ^ 2) (Ioc 0 c)) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : ∀ i j, M i j = c⁻¹ * ∫ q in Ioc 0 c, F' q i j) :
    ENNReal.ofReal (tensorNorm M ^ 2) ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F' q) ^ 2) := by
  have hJ := t17m_jensen_mat c hc F' hm hI M hM
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 c)] fun q => tensorNorm (F' q) ^ 2 :=
    Filter.Eventually.of_forall (fun q => sq_nonneg _)
  calc ENNReal.ofReal (tensorNorm M ^ 2)
      ≤ ENNReal.ofReal (c⁻¹ * ∫ q in Ioc 0 c, tensorNorm (F' q) ^ 2) := ENNReal.ofReal_le_ofReal hJ
    _ = ENNReal.ofReal c⁻¹ * ENNReal.ofReal (∫ q in Ioc 0 c, tensorNorm (F' q) ^ 2) := by
        rw [ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F' q) ^ 2) := by
        rw [ofReal_integral_eq_lintegral_ofReal hI hnn]

theorem t17m_K1 (c : ℝ) (hc : 0 < c) (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hF : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) (x' : ℝ × ℝ) (Y : ℝ) :
    ∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (phaseMean c F x' Y) ^ 2) ≤
      ∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (F x' Y q) ^ 2) := by
  by_cases htop : (∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (F x' Y q) ^ 2)) = ⊤
  · rw [htop]; exact le_top
  have hfin : ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F x' Y q) ^ 2) < ⊤ := by
    refine lt_top_iff_ne_top.2 (fun h => htop ?_)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h,
      ENNReal.mul_top (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne']
  have hq : ∀ i j, Measurable fun q => F x' Y q i j := fun i j =>
    (hF i j).comp (f := fun q : ℝ => (x', (Y, q))) (by fun_prop)
  have hT : Measurable fun q => tensorNorm (F x' Y q) := by
    unfold tensorNorm
    exact (Finset.measurable_sum _
      (fun i _ => Finset.measurable_sum _ (fun j _ => (hq i j).pow_const 2))).sqrt
  have hI : IntegrableOn (fun q => tensorNorm (F x' Y q) ^ 2) (Ioc 0 c) := by
    refine ⟨(hT.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun q => sq_nonneg _))]
    exact hfin
  have hconst : ∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (phaseMean c F x' Y) ^ 2)
      = ENNReal.ofReal (tensorNorm (phaseMean c F x' Y) ^ 2) := by
    rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm, ← mul_assoc,
      ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one, one_mul]
  rw [hconst, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact t17m_mono_ofReal_sq c hc (fun q => F x' Y q) hq hI (phaseMean c F x' Y) (fun i j => rfl)

theorem t17m_partA (c : ℝ) (hc : 0 < c) (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hF : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) :
    thinMoment c (meanLift (phaseMean c F)) ≤ thinMoment c F := by
  unfold thinMoment
  refine lintegral_mono (fun w : (ℝ × ℝ) × ℝ => ?_)
  exact mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow (t17m_K1 c hc F hF w.1 w.2) (by norm_num))
    zero_le

theorem t17m_four_rpow : (4 : ℝ≥0∞) ^ (1 / 2 : ℝ) = 2 := by
  rw [show (4 : ℝ≥0∞) = 2 ^ (2 : ℝ) by norm_num, ← ENNReal.rpow_mul]
  norm_num

theorem t17m_perp_int (c : ℝ) (hc : 0 < c) (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hF : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) (x' : ℝ × ℝ) (Y : ℝ) :
    ∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (perpPart c F x' Y q) ^ 2) ≤
      4 * ∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (F x' Y q) ^ 2) := by
  have hq : ∀ i j, Measurable fun q => F x' Y q i j := fun i j =>
    (hF i j).comp (f := fun q : ℝ => (x', (Y, q))) (by fun_prop)
  have hT : Measurable fun q => tensorNorm (F x' Y q) := by
    unfold tensorNorm
    exact (Finset.measurable_sum _
      (fun i _ => Finset.measurable_sum _ (fun j _ => (hq i j).pow_const 2))).sqrt
  have hT2m : Measurable fun q => ENNReal.ofReal (tensorNorm (F x' Y q) ^ 2) :=
    ENNReal.measurable_ofReal.comp (hT.pow_const 2)
  have hgm : Measurable fun q => 2 * (ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (F x' Y q) ^ 2)) :=
    (hT2m.const_mul _).const_mul _
  have hpt : ∀ q, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (perpPart c F x' Y q) ^ 2) ≤
      2 * (ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (F x' Y q) ^ 2)) +
        2 * (ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (phaseMean c F x' Y) ^ 2)) := by
    intro q
    have h : tensorNorm (perpPart c F x' Y q) ^ 2 ≤
        2 * tensorNorm (F x' Y q) ^ 2 + 2 * tensorNorm (phaseMean c F x' Y) ^ 2 :=
      t17m_sub_sq_le (F x' Y q) (phaseMean c F x' Y)
    have hA : (0 : ℝ) ≤ 2 * tensorNorm (F x' Y q) ^ 2 := by positivity
    have hB : (0 : ℝ) ≤ 2 * tensorNorm (phaseMean c F x' Y) ^ 2 := by positivity
    have e : ENNReal.ofReal (2 * tensorNorm (F x' Y q) ^ 2 + 2 * tensorNorm (phaseMean c F x' Y) ^ 2) =
        2 * ENNReal.ofReal (tensorNorm (F x' Y q) ^ 2) +
          2 * ENNReal.ofReal (tensorNorm (phaseMean c F x' Y) ^ 2) := by
      rw [ENNReal.ofReal_add hA hB, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
        ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      simp
    have hle : ENNReal.ofReal (tensorNorm (perpPart c F x' Y q) ^ 2) ≤
        ENNReal.ofReal (2 * tensorNorm (F x' Y q) ^ 2 + 2 * tensorNorm (phaseMean c F x' Y) ^ 2) :=
      ENNReal.ofReal_le_ofReal h
    calc ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (perpPart c F x' Y q) ^ 2)
        ≤ ENNReal.ofReal c⁻¹ * ENNReal.ofReal (2 * tensorNorm (F x' Y q) ^ 2 +
            2 * tensorNorm (phaseMean c F x' Y) ^ 2) := mul_le_mul_of_nonneg_left hle zero_le
      _ = _ := by rw [e]; ring
  calc ∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (perpPart c F x' Y q) ^ 2)
      ≤ ∫⁻ q in Ioc 0 c, (2 * (ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (F x' Y q) ^ 2)) +
          2 * (ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (phaseMean c F x' Y) ^ 2))) :=
        lintegral_mono hpt
    _ = (∫⁻ q in Ioc 0 c, 2 * (ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (F x' Y q) ^ 2))) +
          ∫⁻ q in Ioc 0 c, 2 * (ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (phaseMean c F x' Y) ^ 2)) :=
        lintegral_add_left hgm _
    _ = 2 * (∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (F x' Y q) ^ 2)) +
          2 * (∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (phaseMean c F x' Y) ^ 2)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofNat_ne_top, lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
    _ ≤ 2 * (∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (F x' Y q) ^ 2)) +
          2 * (∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (F x' Y q) ^ 2)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (t17m_K1 c hc F hF x' Y) zero_le)
    _ = 4 * ∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (F x' Y q) ^ 2) := by
        ring

theorem t17m_partB (c : ℝ) (hc : 0 < c) (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hF : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) :
    thinMoment c (perpPart c F) ≤ 2 * thinMoment c F := by
  unfold thinMoment
  calc ∫⁻ w : (ℝ × ℝ) × ℝ, ENNReal.ofReal (1 + |w.2|) *
        (∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (perpPart c F w.1 w.2 q) ^ 2)) ^ (1 / 2 : ℝ)
      ≤ ∫⁻ w : (ℝ × ℝ) × ℝ, 2 * (ENNReal.ofReal (1 + |w.2|) *
        (∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (F w.1 w.2 q) ^ 2)) ^ (1 / 2 : ℝ)) := by
        refine lintegral_mono (fun w : (ℝ × ℝ) × ℝ => ?_)
        have hp := t17m_perp_int c hc F hF w.1 w.2
        have hr : (∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (perpPart c F w.1 w.2 q) ^ 2)) ^ (1 / 2 : ℝ)
            ≤ 2 * (∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (F w.1 w.2 q) ^ 2)) ^ (1 / 2 : ℝ) := by
          calc _ ≤ (4 * ∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (F w.1 w.2 q) ^ 2)) ^ (1 / 2 : ℝ) :=
                ENNReal.rpow_le_rpow hp (by norm_num : (0:ℝ) ≤ 1 / 2)
            _ = 2 * (∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (F w.1 w.2 q) ^ 2)) ^ (1 / 2 : ℝ) := by
                rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2), t17m_four_rpow]
        calc ENNReal.ofReal (1 + |w.2|) *
              (∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (perpPart c F w.1 w.2 q) ^ 2)) ^ (1 / 2 : ℝ)
            ≤ ENNReal.ofReal (1 + |w.2|) *
              (2 * (∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (F w.1 w.2 q) ^ 2)) ^ (1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hr zero_le
          _ = 2 * (ENNReal.ofReal (1 + |w.2|) *
              (∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (F w.1 w.2 q) ^ 2)) ^ (1 / 2 : ℝ)) := by
              ring
    _ = 2 * ∫⁻ w : (ℝ × ℝ) × ℝ, ENNReal.ofReal (1 + |w.2|) *
        (∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (F w.1 w.2 q) ^ 2)) ^ (1 / 2 : ℝ) :=
        lintegral_const_mul' _ _ ENNReal.ofNat_ne_top

theorem sepMomentSplit : UnforcedLeray.Short.IIIa.SepMomentSplit := by
  intro c hc F hF
  exact ⟨t17m_partA c hc F hF, t17m_partB c hc F hF⟩

end UnforcedLeray.Short.IIIa

end
