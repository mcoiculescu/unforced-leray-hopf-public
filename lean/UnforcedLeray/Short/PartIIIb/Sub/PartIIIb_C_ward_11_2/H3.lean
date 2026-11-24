import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_11_2.H2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_3

/-!
# Helpers for `wardD2XYoungL2_proved` (3): radial jet bounds and pointwise `D²X` domination

Source of record: `the November 2 reference manuscript` (73 pages), 4180-4196.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Horizontal projection `y ↦ (y₀, y₁, 0) = y - y₂ e₂`. -/
def w112_P01 (y : Space) : Space := y + (-y 2) • coordinateVector 2

lemma w112_varrho_add_z (x : Space) (z : ℝ) :
    ϱ (x + z • coordinateVector 2) = ϱ x := by
  have h0 : (x + z • coordinateVector 2) 0 = x 0 := by simp [coordinateVector]
  have h1 : (x + z • coordinateVector 2) 1 = x 1 := by simp [coordinateVector]
  simp only [ϱ, h0, h1]

lemma w112_P01_add_z (y : Space) :
    w112_P01 y + (y 2) • coordinateVector 2 = y := by
  ext i
  fin_cases i <;> simp [w112_P01, coordinateVector]

lemma w112_varrho_P01 (y : Space) : ϱ (w112_P01 y) = ϱ y :=
  w112_varrho_add_z y (-y 2)

lemma w112_P01_eq_sum (y : Space) :
    w112_P01 y = (y 0) • coordinateVector 0 + (y 1) • coordinateVector 1 := by
  ext i
  fin_cases i <;> simp [w112_P01, coordinateVector]

lemma w112_norm_P01_le (y : Space) : ‖w112_P01 y‖ ≤ 2 * ϱ y := by
  rw [w112_P01_eq_sum]
  have h0 : |y 0| ≤ ϱ y := by unfold ϱ; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (y 1)])
  have h1 : |y 1| ≤ ϱ y := by unfold ϱ; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (y 0)])
  calc ‖(y 0) • (coordinateVector 0 : Space) + (y 1) • (coordinateVector 1 : Space)‖
      ≤ ‖(y 0) • (coordinateVector 0 : Space)‖ + ‖(y 1) • (coordinateVector 1 : Space)‖ :=
        norm_add_le _ _
    _ = |y 0| + |y 1| := by
        rw [norm_smul, norm_smul, wyl_norm_coordinateVector, wyl_norm_coordinateVector,
          Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one]
    _ ≤ 2 * ϱ y := by linarith

lemma w112_sd1_z_inv {f : Space → ℝ}
    (hf : ∀ (x : Space) (z : ℝ), f (x + z • coordinateVector 2) = f x)
    (k : Fin 3) (x : Space) (z : ℝ) :
    w112_sd1 f k (x + z • coordinateVector 2) = w112_sd1 f k x := by
  have hfun : (fun w : Space => f (w + z • coordinateVector 2)) = f := by
    funext w; exact hf w z
  simp only [w112_sd1, ← fderiv_comp_add_right (z • coordinateVector 2), hfun]

lemma w112_sd2_z_inv {f : Space → ℝ}
    (hf : ∀ (x : Space) (z : ℝ), f (x + z • coordinateVector 2) = f x)
    (j l : Fin 3) (x : Space) (z : ℝ) :
    w112_sd2 f j l (x + z • coordinateVector 2) = w112_sd2 f j l x :=
  w112_sd1_z_inv (w112_sd1_z_inv hf l) j x z

lemma w112_sd1_zero_of_gt {r2 c₀ : ℝ} {f : Space → ℝ}
    (hf : ∀ y : Space, r2 < ϱ y → f y = c₀) (k : Fin 3) {y : Space} (hy : r2 < ϱ y) :
    w112_sd1 f k y = 0 := by
  have hopen : IsOpen {w : Space | r2 < ϱ w} := isOpen_lt continuous_const continuous_ϱ
  have hev : f =ᶠ[𝓝 y] fun _ => c₀ :=
    Filter.mem_of_superset (hopen.mem_nhds hy) fun w hw => hf w hw
  unfold w112_sd1
  rw [hev.fderiv_eq]
  simp

lemma w112_sd2_zero_of_gt {r2 c₀ : ℝ} {f : Space → ℝ}
    (hf : ∀ y : Space, r2 < ϱ y → f y = c₀) (j l : Fin 3) {y : Space} (hy : r2 < ϱ y) :
    w112_sd2 f j l y = 0 :=
  w112_sd1_zero_of_gt (fun _w hw => w112_sd1_zero_of_gt hf l hw) j hy

/-- Combined 2-jet norm of a scalar function `φ : Space → ℝ`. -/
def w112_jet2 (φ : Space → ℝ) (w : Space) : ℝ :=
  |φ w| + (∑ k : Fin 3, |w112_sd1 φ k w|) + ∑ j : Fin 3, ∑ l : Fin 3, |w112_sd2 φ j l w|

lemma w112_jet2_continuousOn {U : Set Space} (hUo : IsOpen U) {φ : Space → ℝ}
    (hφ : ContDiffOn ℝ 2 φ U) :
    ContinuousOn (w112_jet2 φ) U := by
  have hφ' : ContDiffOn ℝ ((1 : WithTop ℕ∞) + 1) φ U := hφ
  have hf1 : ContDiffOn ℝ 1 (fderiv ℝ φ) U :=
    ((contDiffOn_succ_iff_fderiv_of_isOpen hUo).1 hφ').2.2
  have hsd1 : ∀ l : Fin 3, ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1) (w112_sd1 φ l) U := fun l =>
    (ContinuousLinearMap.apply ℝ ℝ (coordinateVector l)).contDiff.comp_contDiffOn hf1
  have hsd2 : ∀ j l : Fin 3, ContDiffOn ℝ 0 (w112_sd2 φ j l) U := fun j l => by
    have hf2 : ContDiffOn ℝ 0 (fderiv ℝ (w112_sd1 φ l)) U :=
      ((contDiffOn_succ_iff_fderiv_of_isOpen hUo).1 (hsd1 l)).2.2
    exact (ContinuousLinearMap.apply ℝ ℝ (coordinateVector j)).contDiff.comp_contDiffOn hf2
  unfold w112_jet2
  refine (hφ.continuousOn.abs.add ?_).add ?_
  · exact continuousOn_finsetSum _ fun k _ => (hsd1 k).continuousOn.abs
  · exact continuousOn_finsetSum _ fun j _ =>
      continuousOn_finsetSum _ fun l _ => (hsd2 j l).continuousOn.abs

/-- Uniform 2-jet bound on `R√ν ≤ ϱ y` for any `z`-independent `C²` function constant for `ϱ > r₂`. -/
theorem w112_radial_jet2_bound {ν R c₀ : ℝ} (hν : 0 < ν) (hR : 0 < R) {φ : Space → ℝ}
    (hφc : ContDiffOn ℝ 2 φ (youngOpen ν R))
    (hφz : ∀ (x : Space) (z : ℝ), φ (x + z • coordinateVector 2) = φ x)
    (hφgt : ∀ y : Space, R * Real.sqrt (5 * ν / 4) < ϱ y → φ y = c₀) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ y : Space, R * Real.sqrt ν ≤ ϱ y →
        |φ y| ≤ C ∧ (∀ k : Fin 3, |w112_sd1 φ k y| ≤ C) ∧
          (∀ j l : Fin 3, |w112_sd2 φ j l y| ≤ C)) ∧
      (∀ y : Space, R * Real.sqrt (5 * ν / 4) < ϱ y →
        φ y = c₀ ∧ (∀ k : Fin 3, w112_sd1 φ k y = 0) ∧
          (∀ j l : Fin 3, w112_sd2 φ j l y = 0)) := by
  set r1 : ℝ := R * Real.sqrt ν
  set r2 : ℝ := R * Real.sqrt (5 * ν / 4)
  have hrr : R * Real.sqrt (5 * ν / 6) < r1 :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hUo : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  set K : Set Space := Metric.closedBall (0 : Space) (2 * r2) ∩ {w : Space | r1 ≤ ϱ w}
  have hKc : IsCompact K :=
    (isCompact_closedBall (0 : Space) (2 * r2)).inter_right
      (isClosed_le continuous_const continuous_ϱ)
  have hKU : K ⊆ youngOpen ν R := fun w hw => lt_of_lt_of_le hrr hw.2
  have hjet_cont : ContinuousOn (w112_jet2 φ) K :=
    (w112_jet2_continuousOn hUo hφc).mono hKU
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hjet_cont
  set C : ℝ := max (max M 0) |c₀|
  have hC0 : 0 ≤ C := le_trans (le_max_right M 0) (le_max_left _ _)
  have hgt : ∀ y : Space, r2 < ϱ y →
      φ y = c₀ ∧ (∀ k : Fin 3, w112_sd1 φ k y = 0) ∧
        (∀ j l : Fin 3, w112_sd2 φ j l y = 0) :=
    fun y hy => ⟨hφgt y hy, fun k => w112_sd1_zero_of_gt hφgt k hy,
      fun j l => w112_sd2_zero_of_gt hφgt j l hy⟩
  refine ⟨C, hC0, fun y hy => ?_, hgt⟩
  by_cases hle : ϱ y ≤ r2
  · have hP_mem : w112_P01 y ∈ K := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right]
        exact (w112_norm_P01_le y).trans (by linarith)
      · change r1 ≤ ϱ (w112_P01 y)
        rw [w112_varrho_P01]; exact hy
    have hJM : w112_jet2 φ (w112_P01 y) ≤ C := by
      have h1 := hM (w112_P01 y) hP_mem
      have h2 : w112_jet2 φ (w112_P01 y) ≤ ‖w112_jet2 φ (w112_P01 y)‖ := le_abs_self _
      exact (h2.trans h1).trans ((le_max_left M 0).trans (le_max_left _ _))
    have heq0 : φ y = φ (w112_P01 y) := by
      conv_lhs => rw [← w112_P01_add_z y, hφz]
    have heq1 : ∀ k : Fin 3, w112_sd1 φ k y = w112_sd1 φ k (w112_P01 y) := fun k => by
      conv_lhs => rw [← w112_P01_add_z y, w112_sd1_z_inv hφz]
    have heq2 : ∀ j l : Fin 3, w112_sd2 φ j l y = w112_sd2 φ j l (w112_P01 y) := fun j l => by
      conv_lhs => rw [← w112_P01_add_z y, w112_sd2_z_inv hφz]
    have hs1_nn : 0 ≤ ∑ k : Fin 3, |w112_sd1 φ k (w112_P01 y)| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hs2_nn : 0 ≤ ∑ j : Fin 3, ∑ l : Fin 3, |w112_sd2 φ j l (w112_P01 y)| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    unfold w112_jet2 at hJM
    refine ⟨?_, fun k => ?_, fun j l => ?_⟩
    · rw [heq0]; linarith
    · rw [heq1 k]
      have hk : |w112_sd1 φ k (w112_P01 y)| ≤ ∑ i : Fin 3, |w112_sd1 φ i (w112_P01 y)| :=
        Finset.single_le_sum (f := fun i : Fin 3 => |w112_sd1 φ i (w112_P01 y)|)
          (fun i _ => abs_nonneg _) (Finset.mem_univ k)
      linarith [abs_nonneg (φ (w112_P01 y))]
    · rw [heq2 j l]
      have hjl1 : |w112_sd2 φ j l (w112_P01 y)| ≤
          ∑ l' : Fin 3, |w112_sd2 φ j l' (w112_P01 y)| :=
        Finset.single_le_sum (f := fun l' : Fin 3 => |w112_sd2 φ j l' (w112_P01 y)|)
          (fun l' _ => abs_nonneg _) (Finset.mem_univ l)
      have hjl2 : ∑ l' : Fin 3, |w112_sd2 φ j l' (w112_P01 y)| ≤
          ∑ j' : Fin 3, ∑ l' : Fin 3, |w112_sd2 φ j' l' (w112_P01 y)| :=
        Finset.single_le_sum
          (f := fun j' : Fin 3 => ∑ l' : Fin 3, |w112_sd2 φ j' l' (w112_P01 y)|)
          (fun j' _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      linarith [abs_nonneg (φ (w112_P01 y))]
  · obtain ⟨h0, h1, h2⟩ := hgt y (not_le.1 hle)
    refine ⟨?_, fun k => ?_, fun j l => ?_⟩
    · rw [h0]; exact le_max_right _ _
    · rw [h1 k, abs_zero]; exact hC0
    · rw [h2 j l, abs_zero]; exact hC0

/-- 2-jet bound on `R√ν ≤ ϱ y` for the young cutoff `y ↦ χy (ν * age R y)`. -/
theorem w112_cut_jet2_bound {ν R : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : Space, R * Real.sqrt ν ≤ ϱ y →
        |χy (ν * age R y)| ≤ C ∧
          (∀ k : Fin 3, |w112_sd1 (fun x => χy (ν * age R x)) k y| ≤ C) ∧
          (∀ j l : Fin 3, |w112_sd2 (fun x => χy (ν * age R x)) j l y| ≤ C) := by
  have hne : ∀ y ∈ youngOpen ν R, ϱ y ≠ 0 := fun y hy => by
    have hp := t9_thr_pos hν hR
    have hy' : R * Real.sqrt (5 * ν / 6) < ϱ y := hy
    linarith
  have hϱ : ContDiffOn ℝ 2 (fun y : Space => ϱ y) (youngOpen ν R) :=
    contDiffOn_ϱ.mono (fun y hy => t9_not_axis hν hR hy)
  have hage : ContDiffOn ℝ 2 (fun y : Space => ν * age R y) (youngOpen ν R) :=
    contDiffOn_const.mul
      (ContDiffOn.div contDiffOn_const (hϱ.pow 2) (fun y hy => pow_ne_zero 2 (hne y hy)))
  have hχ2 : ContDiff ℝ 2 χy :=
    hχy.smooth.of_le (WithTop.coe_le_coe.2 le_top)
  have hφc : ContDiffOn ℝ 2 (fun y : Space => χy (ν * age R y)) (youngOpen ν R) :=
    hχ2.comp_contDiffOn hage
  have hφz : ∀ (x : Space) (z : ℝ),
      χy (ν * age R (x + z • coordinateVector 2)) = χy (ν * age R x) := by
    intro x z
    simp only [age, w112_varrho_add_z]
  have hφgt : ∀ y : Space, R * Real.sqrt (5 * ν / 4) < ϱ y → χy (ν * age R y) = 1 := by
    intro y hy
    have hρ : 0 < ϱ y := lt_of_le_of_lt (by positivity) hy
    have hsq : 5 * ν / 4 * R ^ 2 < ϱ y ^ 2 := by
      have := pow_lt_pow_left₀ hy (by positivity) two_ne_zero
      rw [mul_pow, Real.sq_sqrt (by positivity)] at this
      linarith
    have ht : ν * age R y ≤ 4 / 5 := by
      unfold age
      rw [← mul_div_assoc, div_le_iff₀ (pow_pos hρ 2)]
      nlinarith [mul_pos hν (pow_pos hR 2)]
    exact hχy.one _ ht
  obtain ⟨C, hC0, hbd, -⟩ := w112_radial_jet2_bound hν hR hφc hφz hφgt
  exact ⟨C, hC0, hbd⟩

/-- 2-jet bound on `R√ν ≤ ϱ y` for the stream radial factor `y ↦ w2a ν R χy (ϱ y)`. -/
theorem w112_w2a_jet2_bound {ν R : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ y : Space, R * Real.sqrt ν ≤ ϱ y →
        |w2a ν R χy (ϱ y)| ≤ C ∧
          (∀ k : Fin 3, |w112_sd1 (fun x => w2a ν R χy (ϱ x)) k y| ≤ C) ∧
          (∀ j l : Fin 3, |w112_sd2 (fun x => w2a ν R χy (ϱ x)) j l y| ≤ C)) ∧
      (∀ y : Space, R * Real.sqrt (5 * ν / 4) < ϱ y →
        w2a ν R χy (ϱ y) = 0 ∧
          (∀ k : Fin 3, w112_sd1 (fun x => w2a ν R χy (ϱ x)) k y = 0) ∧
          (∀ j l : Fin 3, w112_sd2 (fun x => w2a ν R χy (ϱ x)) j l y = 0)) := by
  have hne : ∀ y ∈ youngOpen ν R, ϱ y ≠ 0 := fun y hy => by
    have hp := t9_thr_pos hν hR
    have hy' : R * Real.sqrt (5 * ν / 6) < ϱ y := hy
    linarith
  have hϱ : ContDiffOn ℝ 2 (fun y : Space => ϱ y) (youngOpen ν R) :=
    contDiffOn_ϱ.mono (fun y hy => t9_not_axis hν hR hy)
  have hage : ContDiffOn ℝ 2 (fun y : Space => ν * (R ^ 2 / ϱ y ^ 2)) (youngOpen ν R) :=
    contDiffOn_const.mul
      (ContDiffOn.div contDiffOn_const (hϱ.pow 2) (fun y hy => pow_ne_zero 2 (hne y hy)))
  have hdχ2 : ContDiff ℝ 2 (deriv χy) :=
    ((show ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) χy from hχy.smooth).deriv').of_le
      (WithTop.coe_le_coe.2 le_top)
  have hdA : ContDiffOn ℝ 2 (fun y : Space => deriv χy (ν * (R ^ 2 / ϱ y ^ 2))) (youngOpen ν R) :=
    hdχ2.comp_contDiffOn hage
  have hK : ContDiffOn ℝ 2 (fun y : Space => -2 * ν * R ^ 2 / ϱ y ^ 3) (youngOpen ν R) :=
    ContDiffOn.div contDiffOn_const (hϱ.pow 3) (fun y hy => pow_ne_zero 3 (hne y hy))
  have hφc : ContDiffOn ℝ 2 (fun y : Space => w2a ν R χy (ϱ y)) (youngOpen ν R) :=
    (hdA.mul hK).div hϱ hne
  have hφz : ∀ (x : Space) (z : ℝ),
      w2a ν R χy (ϱ (x + z • coordinateVector 2)) = w2a ν R χy (ϱ x) := by
    intro x z; rw [w112_varrho_add_z]
  have hφgt : ∀ y : Space, R * Real.sqrt (5 * ν / 4) < ϱ y → w2a ν R χy (ϱ y) = 0 :=
    fun y hy => w2a_zero_of_gt hχy hν hR hy
  exact w112_radial_jet2_bound hν hR hφc hφz hφgt

/-- Additivity of `physPd2` on an open set where both summands are `C²`. -/
lemma w112_physPd2_add_norm_le {U : Set Space} (hUo : IsOpen U) {F₁ F₂ : Space → Space}
    (hF₁ : ContDiffOn ℝ 2 F₁ U) (hF₂ : ContDiffOn ℝ 2 F₂ U)
    (j l : Fin 3) {y : Space} (hy : y ∈ U) :
    ‖physPd2 (fun x => F₁ x + F₂ x) j l y‖ ≤ ‖physPd2 F₁ j l y‖ + ‖physPd2 F₂ j l y‖ := by
  have hF₁' : ContDiffOn ℝ ((1 : WithTop ℕ∞) + 1) F₁ U := hF₁
  have hF₂' : ContDiffOn ℝ ((1 : WithTop ℕ∞) + 1) F₂ U := hF₂
  have hd1 : DifferentiableAt ℝ (physPd F₁ l) y := by
    have hf1 : ContDiffOn ℝ 1 (fderiv ℝ F₁) U :=
      ((contDiffOn_succ_iff_fderiv_of_isOpen hUo).1 hF₁').2.2
    have hpd1 : ContDiffOn ℝ 1 (physPd F₁ l) U :=
      (ContinuousLinearMap.apply ℝ Space (coordinateVector l)).contDiff.comp_contDiffOn hf1
    exact (hpd1.contDiffAt (hUo.mem_nhds hy)).differentiableAt one_ne_zero
  have hd2 : DifferentiableAt ℝ (physPd F₂ l) y := by
    have hf2 : ContDiffOn ℝ 1 (fderiv ℝ F₂) U :=
      ((contDiffOn_succ_iff_fderiv_of_isOpen hUo).1 hF₂').2.2
    have hpd2 : ContDiffOn ℝ 1 (physPd F₂ l) U :=
      (ContinuousLinearMap.apply ℝ Space (coordinateVector l)).contDiff.comp_contDiffOn hf2
    exact (hpd2.contDiffAt (hUo.mem_nhds hy)).differentiableAt one_ne_zero
  have hev : physPd (fun x => F₁ x + F₂ x) l =ᶠ[𝓝 y] fun w => physPd F₁ l w + physPd F₂ l w := by
    refine Filter.mem_of_superset (hUo.mem_nhds hy) fun w hw => ?_
    have hw1 : DifferentiableAt ℝ F₁ w :=
      (hF₁.contDiffAt (hUo.mem_nhds hw)).differentiableAt (by norm_num)
    have hw2 : DifferentiableAt ℝ F₂ w :=
      (hF₂.contDiffAt (hUo.mem_nhds hw)).differentiableAt (by norm_num)
    show fderiv ℝ (fun x => F₁ x + F₂ x) w (coordinateVector l) =
      fderiv ℝ F₁ w (coordinateVector l) + fderiv ℝ F₂ w (coordinateVector l)
    rw [fderiv_fun_add hw1 hw2, add_apply]
  have heq : physPd2 (fun x => F₁ x + F₂ x) j l y = physPd2 F₁ j l y + physPd2 F₂ j l y := by
    change fderiv ℝ (physPd (fun x => F₁ x + F₂ x) l) y (coordinateVector j) =
      fderiv ℝ (physPd F₁ l) y (coordinateVector j) + fderiv ℝ (physPd F₂ l) y (coordinateVector j)
    rw [hev.fderiv_eq, fderiv_fun_add hd1 hd2, add_apply]
  rw [heq]
  exact norm_add_le _ _

/-- Norms of `0`th, `1`st, and `2`nd partials of `y ↦ Ψ y • coordinateVector 2`. -/
lemma w112_smul_e2_jets {U : Set Space} (hUo : IsOpen U) {Ψ : Space → ℝ}
    (hΨ : ContDiffOn ℝ 2 Ψ U) {y : Space} (hy : y ∈ U) :
    ‖Ψ y • (coordinateVector 2 : Space)‖ = |Ψ y| ∧
      (∀ k : Fin 3, ‖physPd (fun x => Ψ x • (coordinateVector 2 : Space)) k y‖ =
        |w112_sd1 Ψ k y|) ∧
      (∀ j l : Fin 3, ‖physPd2 (fun x => Ψ x • (coordinateVector 2 : Space)) j l y‖ =
        |w112_sd2 Ψ j l y|) := by
  have hΨ' : ContDiffOn ℝ ((1 : WithTop ℕ∞) + 1) Ψ U := hΨ
  have hf1 : ContDiffOn ℝ 1 (fderiv ℝ Ψ) U :=
    ((contDiffOn_succ_iff_fderiv_of_isOpen hUo).1 hΨ').2.2
  have hpd_eq : ∀ (k : Fin 3) {w : Space}, w ∈ U →
      physPd (fun x => Ψ x • (coordinateVector 2 : Space)) k w =
        (w112_sd1 Ψ k w) • (coordinateVector 2 : Space) := fun k {w} hw => by
    have hwd : DifferentiableAt ℝ Ψ w :=
      (hΨ.contDiffAt (hUo.mem_nhds hw)).differentiableAt (by norm_num)
    unfold physPd w112_sd1
    rw [(hwd.hasFDerivAt.smul_const (coordinateVector 2 : Space)).fderiv,
      ContinuousLinearMap.smulRight_apply]
  refine ⟨?_, fun k => ?_, fun j l => ?_⟩
  · rw [norm_smul, wyl_norm_coordinateVector, mul_one, Real.norm_eq_abs]
  · rw [hpd_eq k hy, norm_smul, wyl_norm_coordinateVector, mul_one, Real.norm_eq_abs]
  · have hev : physPd (fun x => Ψ x • (coordinateVector 2 : Space)) l =ᶠ[𝓝 y]
        fun w => (w112_sd1 Ψ l w) • (coordinateVector 2 : Space) :=
      Filter.mem_of_superset (hUo.mem_nhds hy) fun w hw => hpd_eq l hw
    have hsd1_c : ContDiffOn ℝ 1 (w112_sd1 Ψ l) U :=
      (ContinuousLinearMap.apply ℝ ℝ (coordinateVector l)).contDiff.comp_contDiffOn hf1
    have hsd1_d : DifferentiableAt ℝ (w112_sd1 Ψ l) y :=
      (hsd1_c.contDiffAt (hUo.mem_nhds hy)).differentiableAt one_ne_zero
    change ‖fderiv ℝ (physPd (fun x => Ψ x • (coordinateVector 2 : Space)) l) y (coordinateVector j)‖ =
      |fderiv ℝ (w112_sd1 Ψ l) y (coordinateVector j)|
    rw [hev.fderiv_eq, (hsd1_d.hasFDerivAt.smul_const (coordinateVector 2 : Space)).fderiv,
      ContinuousLinearMap.smulRight_apply, norm_smul, wyl_norm_coordinateVector, mul_one,
      Real.norm_eq_abs]

end UnforcedLeray.Short.PartIIIb.Concrete
end
