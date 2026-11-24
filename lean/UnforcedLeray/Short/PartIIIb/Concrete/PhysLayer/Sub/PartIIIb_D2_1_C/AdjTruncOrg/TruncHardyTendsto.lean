import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg

/-!
# `truncHardyTendsto`: the Hardy commutator `EHardy n` tends to zero in `Y_2`

Source: `the November 2 reference manuscript` lines 1334-1337, 1351-1362,
1470-1480.  `EHardy n ν D = ∇χₙ × w + ½ ∇(y·∇χₙ) × ψ - ν ∇Δχₙ × ψ`.

Pointwise: `EHardy n` vanishes off the annulus `n+1 ≤ |y| ≤ 2(n+1)`, and on it the coefficients
are `≤ 2C/|y|` (`C/(n+1) ≤ 2C/|y|`), so `‖EHardy n x‖ ≤ K (|y|⁻¹‖w x‖ + |y|⁻¹‖ψ x‖)` with
`K = 2C(3 + 2|ν|)`.  The majorant is in `L²` (Hardy fields `|y|⁻¹ w, |y|⁻¹ ψ ∈ Y_2`), and
pointwise `EHardy n x → 0` (it vanishes once `n + 1 > |y|`).  Dominated convergence on the
phase measure finishes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The constant of the Hardy bound. -/
def trhK (C ν : ℝ) : ℝ := 2 * C * (3 + 2 * |ν|)

theorem trhK_nonneg {C : ℝ} (hC0 : 0 ≤ C) (ν : ℝ) : 0 ≤ trhK C ν := by
  unfold trhK
  have : (0:ℝ) ≤ 3 + 2 * |ν| := by positivity
  exact mul_nonneg (mul_nonneg (by norm_num) hC0) this

/-- Componentwise Cauchy-Schwarz for the cross product. -/
theorem trh_pair_sq (x1 x2 y1 y2 : ℂ) :
    ‖x1 * y2 - x2 * y1‖ ^ 2 ≤ (‖x1‖ ^ 2 + ‖x2‖ ^ 2) * (‖y1‖ ^ 2 + ‖y2‖ ^ 2) := by
  have h1 : ‖x1 * y2 - x2 * y1‖ ≤ ‖x1‖ * ‖y2‖ + ‖x2‖ * ‖y1‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖x1‖ * ‖y1‖ - ‖x2‖ * ‖y2‖)]

theorem trh_cross_sq (a b : CVec3) : ‖crossC a b‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 * ‖b‖ ^ 2) := by
  have c0 : crossC a b 0 = a 1 * b 2 - a 2 * b 1 := by simp [crossC]
  have c1 : crossC a b 1 = a 2 * b 0 - a 0 * b 2 := by simp [crossC]
  have c2 : crossC a b 2 = a 0 * b 1 - a 1 * b 0 := by simp [crossC]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, c0, c1, c2]
  have e1 := trh_pair_sq (a 1) (a 2) (b 1) (b 2)
  have e2 := trh_pair_sq (a 2) (a 0) (b 2) (b 0)
  have e3 := trh_pair_sq (a 0) (a 1) (b 0) (b 1)
  have hA0 : 0 ≤ ‖a 0‖ ^ 2 + ‖a 1‖ ^ 2 + ‖a 2‖ ^ 2 := by positivity
  have hB0 : 0 ≤ ‖b 0‖ ^ 2 + ‖b 1‖ ^ 2 + ‖b 2‖ ^ 2 := by positivity
  have m1 : (‖a 1‖ ^ 2 + ‖a 2‖ ^ 2) * (‖b 1‖ ^ 2 + ‖b 2‖ ^ 2)
      ≤ (‖a 0‖ ^ 2 + ‖a 1‖ ^ 2 + ‖a 2‖ ^ 2) * (‖b 0‖ ^ 2 + ‖b 1‖ ^ 2 + ‖b 2‖ ^ 2) :=
    mul_le_mul (by linarith [sq_nonneg ‖a 0‖]) (by linarith [sq_nonneg ‖b 0‖])
      (by positivity) hA0
  have m2 : (‖a 2‖ ^ 2 + ‖a 0‖ ^ 2) * (‖b 2‖ ^ 2 + ‖b 0‖ ^ 2)
      ≤ (‖a 0‖ ^ 2 + ‖a 1‖ ^ 2 + ‖a 2‖ ^ 2) * (‖b 0‖ ^ 2 + ‖b 1‖ ^ 2 + ‖b 2‖ ^ 2) :=
    mul_le_mul (by linarith [sq_nonneg ‖a 1‖]) (by linarith [sq_nonneg ‖b 1‖])
      (by positivity) hA0
  have m3 : (‖a 0‖ ^ 2 + ‖a 1‖ ^ 2) * (‖b 0‖ ^ 2 + ‖b 1‖ ^ 2)
      ≤ (‖a 0‖ ^ 2 + ‖a 1‖ ^ 2 + ‖a 2‖ ^ 2) * (‖b 0‖ ^ 2 + ‖b 1‖ ^ 2 + ‖b 2‖ ^ 2) :=
    mul_le_mul (by linarith [sq_nonneg ‖a 2‖]) (by linarith [sq_nonneg ‖b 2‖])
      (by positivity) hA0
  nlinarith [mul_nonneg hA0 hB0]

theorem trh_cross_norm (a b : CVec3) : ‖crossC a b‖ ≤ 2 * (‖a‖ * ‖b‖) := by
  have h := trh_cross_sq a b
  nlinarith [norm_nonneg (crossC a b), mul_nonneg (norm_nonneg a) (norm_nonneg b)]

theorem crossC_zero_left_trh (b : CVec3) : crossC 0 b = 0 := by
  unfold crossC
  ext i
  fin_cases i <;> simp

theorem trh_grad_cont (a : Space → ℝ) (ha : ContDiff ℝ ∞ a) :
    Continuous fun y : Space => gradC a y := by
  unfold gradC
  have hc : Continuous fun y : Space => fun j : Fin 3 => ((sd j a y : ℝ) : ℂ) :=
    continuous_pi fun j => Complex.continuous_ofReal.comp (contDiff_sd ha j).continuous
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp hc

theorem trh_cross_cont : Continuous fun p : CVec3 × CVec3 => crossC p.1 p.2 := by
  have c : ∀ i : Fin 3, Continuous fun p : CVec3 × CVec3 => p.1 i := fun i => by
    first
      | exact (PiLp.continuous_apply i).comp continuous_fst
      | fun_prop
      | (have := (continuous_apply i).comp (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℂ)
          |>.comp continuous_fst)
         exact this)
  have d : ∀ i : Fin 3, Continuous fun p : CVec3 × CVec3 => p.2 i := fun i => by
    first
      | exact (PiLp.continuous_apply i).comp continuous_snd
      | fun_prop
      | (have := (continuous_apply i).comp (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℂ)
          |>.comp continuous_snd)
         exact this)
  unfold crossC
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp ?_
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact ((c 1).mul (d 2)).sub ((c 2).mul (d 1))
  · exact ((c 2).mul (d 0)).sub ((c 0).mul (d 2))
  · exact ((c 0).mul (d 1)).sub ((c 1).mul (d 0))

theorem trh_radS_cd (n : ℕ) : ContDiff ℝ ∞ (radS (cutχ n)) := by
  unfold radS
  apply ContDiff.sum
  intro j _
  exact ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff).mul (contDiff_sd (contDiff_cutχ n) j)

theorem trh_lapS_cd (n : ℕ) : ContDiff ℝ ∞ (lapS (cutχ n)) := by
  unfold lapS
  apply ContDiff.sum
  intro j _
  exact contDiff_sd (contDiff_sd (contDiff_cutχ n) j) j

theorem trh_meas (n : ℕ) (ν : ℝ) (D : TruncData)
    (hw : AEStronglyMeasurable D.w volume) (hψ : AEStronglyMeasurable D.ψ volume) :
    AEStronglyMeasurable (EHardy n ν D) volume := by
  have hgC : Continuous fun x : ℝ × Space => gradC (cutχ n) x.2 :=
    (trh_grad_cont _ (contDiff_cutχ n)).comp continuous_snd
  have hgR : Continuous fun x : ℝ × Space => gradC (radS (cutχ n)) x.2 :=
    (trh_grad_cont _ (trh_radS_cd n)).comp continuous_snd
  have hgL : Continuous fun x : ℝ × Space => gradC (lapS (cutχ n)) x.2 :=
    (trh_grad_cont _ (trh_lapS_cd n)).comp continuous_snd
  have t1 := trh_cross_cont.comp_aestronglyMeasurable (hgC.aestronglyMeasurable.prodMk hw)
  have t2 := trh_cross_cont.comp_aestronglyMeasurable (hgR.aestronglyMeasurable.prodMk hψ)
  have t3 := trh_cross_cont.comp_aestronglyMeasurable (hgL.aestronglyMeasurable.prodMk hψ)
  unfold EHardy
  exact ((t1.add (t2.const_smul (1 / 2 : ℝ))).sub (t3.const_smul ν))

theorem trh_zero (n : ℕ) (ν : ℝ) (D : TruncData) (x : ℝ × Space)
    (hsupp : gradC (cutχ n) x.2 = 0 ∧ gradC (radS (cutχ n)) x.2 = 0 ∧
      gradC (lapS (cutχ n)) x.2 = 0) :
    EHardy n ν D x = 0 := by
  obtain ⟨h1, h2, h3⟩ := hsupp
  unfold EHardy
  rw [h1, h2, h3]
  simp [crossC_zero_left_trh]

theorem trh_pointwise (C : ℝ) (hC0 : 0 ≤ C) (n : ℕ) (ν : ℝ) (D : TruncData) (x : ℝ × Space)
    (hsupp : (‖x.2‖ < (n : ℝ) + 1 ∨ 2 * ((n : ℝ) + 1) < ‖x.2‖) →
      gradC (cutχ n) x.2 = 0 ∧ gradC (radS (cutχ n)) x.2 = 0 ∧ gradC (lapS (cutχ n)) x.2 = 0)
    (hgr : ‖gradC (cutχ n) x.2‖ ≤ C / ((n : ℝ) + 1) ∧
      ‖gradC (radS (cutχ n)) x.2‖ ≤ C / ((n : ℝ) + 1) ∧
      ‖gradC (lapS (cutχ n)) x.2‖ ≤ C / ((n : ℝ) + 1)) :
    ‖EHardy n ν D x‖ ≤ trhK C ν * (‖x.2‖⁻¹ * ‖D.w x‖ + ‖x.2‖⁻¹ * ‖D.ψ x‖) := by
  by_cases h : ‖x.2‖ < (n : ℝ) + 1 ∨ 2 * ((n : ℝ) + 1) < ‖x.2‖
  · rw [trh_zero n ν D x (hsupp h), norm_zero]
    have hK := trhK_nonneg hC0 ν
    have h1 : 0 ≤ ‖x.2‖⁻¹ * ‖D.w x‖ + ‖x.2‖⁻¹ * ‖D.ψ x‖ := by positivity
    exact mul_nonneg hK h1
  · push_neg at h
    unfold trhK
    obtain ⟨hl, hu⟩ := h
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hpos : 0 < ‖x.2‖ := lt_of_lt_of_le hn1 hl
    have ht0 : 0 ≤ ‖x.2‖⁻¹ := inv_nonneg.2 hpos.le
    have hC' : C / ((n : ℝ) + 1) ≤ 2 * C * ‖x.2‖⁻¹ := by
      have h1 : 1 ≤ 2 * ((n : ℝ) + 1) * ‖x.2‖⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hpos]
        linarith
      rw [div_le_iff₀ hn1]
      nlinarith [mul_le_mul_of_nonneg_left h1 hC0]
    have g1 : ‖gradC (cutχ n) x.2‖ ≤ 2 * C * ‖x.2‖⁻¹ := hgr.1.trans hC'
    have g2 : ‖gradC (radS (cutχ n)) x.2‖ ≤ 2 * C * ‖x.2‖⁻¹ := hgr.2.1.trans hC'
    have g3 : ‖gradC (lapS (cutχ n)) x.2‖ ≤ 2 * C * ‖x.2‖⁻¹ := hgr.2.2.trans hC'
    have e1 : ‖crossC (gradC (cutχ n) x.2) (D.w x)‖ ≤ 2 * (2 * C * ‖x.2‖⁻¹ * ‖D.w x‖) := by
      have := trh_cross_norm (gradC (cutχ n) x.2) (D.w x)
      have h' := mul_le_mul_of_nonneg_right g1 (norm_nonneg (D.w x))
      linarith
    have e2 : ‖crossC (gradC (radS (cutχ n)) x.2) (D.ψ x)‖ ≤ 2 * (2 * C * ‖x.2‖⁻¹ * ‖D.ψ x‖) := by
      have := trh_cross_norm (gradC (radS (cutχ n)) x.2) (D.ψ x)
      have h' := mul_le_mul_of_nonneg_right g2 (norm_nonneg (D.ψ x))
      linarith
    have e3 : ‖crossC (gradC (lapS (cutχ n)) x.2) (D.ψ x)‖ ≤ 2 * (2 * C * ‖x.2‖⁻¹ * ‖D.ψ x‖) := by
      have := trh_cross_norm (gradC (lapS (cutχ n)) x.2) (D.ψ x)
      have h' := mul_le_mul_of_nonneg_right g3 (norm_nonneg (D.ψ x))
      linarith
    have hh : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
    have hsplit : ‖EHardy n ν D x‖ ≤ ‖crossC (gradC (cutχ n) x.2) (D.w x)‖
        + (1 / 2) * ‖crossC (gradC (radS (cutχ n)) x.2) (D.ψ x)‖
        + |ν| * ‖crossC (gradC (lapS (cutχ n)) x.2) (D.ψ x)‖ := by
      unfold EHardy
      have hsub := norm_sub_le ((crossC (gradC (cutχ n) x.2) (D.w x))
        + (1 / 2 : ℝ) • crossC (gradC (radS (cutχ n)) x.2) (D.ψ x))
        (ν • crossC (gradC (lapS (cutχ n)) x.2) (D.ψ x))
      have hadd := norm_add_le (crossC (gradC (cutχ n) x.2) (D.w x))
        ((1 / 2 : ℝ) • crossC (gradC (radS (cutχ n)) x.2) (D.ψ x))
      rw [norm_smul, Real.norm_eq_abs ν] at hsub
      rw [norm_smul, hh] at hadd
      linarith
    have hw0 := norm_nonneg (D.w x)
    have hψ0 := norm_nonneg (D.ψ x)
    have f3 := mul_le_mul_of_nonneg_left e3 (abs_nonneg ν)
    have hCt : 0 ≤ C * ‖x.2‖⁻¹ := mul_nonneg hC0 ht0
    nlinarith [mul_nonneg hCt hw0, mul_nonneg hCt hψ0,
      mul_nonneg (mul_nonneg hCt (abs_nonneg ν)) hw0,
      mul_nonneg (mul_nonneg hCt (abs_nonneg ν)) hψ0]

theorem trh_enorm_sq (v : CVec3) : ‖v‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    Real.rpow_two]

theorem truncHardyTendsto : TruncHardyTendsto := by
  unfold TruncHardyTendsto
  intro hCut P ν hP D hspΦ hspg
  obtain ⟨C, hC0, hall⟩ := hCut
  have hsupp : ∀ n : ℕ, ∀ x : ℝ × Space, (‖x.2‖ < (n : ℝ) + 1 ∨ 2 * ((n : ℝ) + 1) < ‖x.2‖) →
      gradC (cutχ n) x.2 = 0 ∧ gradC (radS (cutχ n)) x.2 = 0 ∧ gradC (lapS (cutχ n)) x.2 = 0 := by
    intro n x h
    obtain ⟨h1, h2, h3, -⟩ := (hall n x.2).1 h
    exact ⟨h1, h2, h3⟩
  have hgr : ∀ n : ℕ, ∀ x : ℝ × Space,
      ‖gradC (cutχ n) x.2‖ ≤ C / ((n : ℝ) + 1) ∧
      ‖gradC (radS (cutχ n)) x.2‖ ≤ C / ((n : ℝ) + 1) ∧
      ‖gradC (lapS (cutχ n)) x.2‖ ≤ C / ((n : ℝ) + 1) := by
    intro n x
    obtain ⟨g1, g2, g3, -⟩ := (hall n x.2).2
    exact ⟨g1, g2, g3⟩
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (EHardy n ν D) volume := fun n =>
    trh_meas n ν D hspg.meas hspΦ.meas
  have hbound : ∀ n : ℕ, ∀ z : ℝ × Space,
      ‖EHardy n ν D z‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (2 * (trhK C ν) ^ 2) *
        (‖(‖z.2‖⁻¹ : ℝ) • D.w z‖ₑ ^ (2 : ℝ) + ‖(‖z.2‖⁻¹ : ℝ) • D.ψ z‖ₑ ^ (2 : ℝ)) := by
    intro n z
    have hp := trh_pointwise C hC0 n ν D z (hsupp n z) (hgr n z)
    have hK := trhK_nonneg hC0 ν
    have hw' : ‖(‖z.2‖⁻¹ : ℝ) • D.w z‖ = ‖z.2‖⁻¹ * ‖D.w z‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _))]
    have hψ' : ‖(‖z.2‖⁻¹ : ℝ) • D.ψ z‖ = ‖z.2‖⁻¹ * ‖D.ψ z‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _))]
    have hreal : ‖EHardy n ν D z‖ ^ 2 ≤ 2 * (trhK C ν) ^ 2 *
        (‖(‖z.2‖⁻¹ : ℝ) • D.w z‖ ^ 2 + ‖(‖z.2‖⁻¹ : ℝ) • D.ψ z‖ ^ 2) := by
      rw [hw', hψ']
      have h0 : 0 ≤ ‖EHardy n ν D z‖ := norm_nonneg _
      have h1 := pow_le_pow_left₀ h0 hp 2
      nlinarith [mul_nonneg (sq_nonneg (trhK C ν))
        (sq_nonneg (‖z.2‖⁻¹ * ‖D.w z‖ - ‖z.2‖⁻¹ * ‖D.ψ z‖))]
    simp only [trh_enorm_sq]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
  have hwI : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x : ℝ × Space => (‖x.2‖⁻¹ : ℝ) • D.w x) :=
    hspg.hardy
  have hψI : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x : ℝ × Space => (‖x.2‖⁻¹ : ℝ) • D.ψ x) :=
    hspΦ.hardy
  have hIw := lint_lt_top_of_phaseLpNorm hP hwI.meas hwI.finite
  have hIψ := lint_lt_top_of_phaseLpNorm hP hψI.meas hψI.finite
  have hbfin : ∫⁻ z, ENNReal.ofReal (2 * (trhK C ν) ^ 2) *
        (‖(‖z.2‖⁻¹ : ℝ) • D.w z‖ₑ ^ (2 : ℝ) + ‖(‖z.2‖⁻¹ : ℝ) • D.ψ z‖ₑ ^ (2 : ℝ))
        ∂(muP P) ≠ ⊤ := by
    have hm1 : AEMeasurable (fun z : ℝ × Space => ‖(‖z.2‖⁻¹ : ℝ) • D.w z‖ₑ ^ (2 : ℝ))
        (muP P) := ((aesm_muP hwI.meas).enorm).pow_const 2
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hm1]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.2 ⟨hIw.ne, hIψ.ne⟩)
  have hpt : ∀ z : ℝ × Space, Tendsto (fun n : ℕ => ‖EHardy n ν D z‖ₑ ^ (2 : ℝ)) atTop (𝓝 0) := by
    intro z
    obtain ⟨N, hN⟩ := exists_nat_gt ‖z.2‖
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have hlt : ‖z.2‖ < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    rw [trh_zero n ν D z (hsupp n z (Or.inl hlt)), enorm_zero,
      ENNReal.zero_rpow_of_pos (by norm_num)]
  have key := tendsto_lintegral_of_dominated_convergence'
    (μ := muP P)
    (F := fun n z => ‖EHardy n ν D z‖ₑ ^ (2 : ℝ))
    (f := fun _ => (0 : ℝ≥0∞))
    (fun z => ENNReal.ofReal (2 * (trhK C ν) ^ 2) *
        (‖(‖z.2‖⁻¹ : ℝ) • D.w z‖ₑ ^ (2 : ℝ) + ‖(‖z.2‖⁻¹ : ℝ) • D.ψ z‖ₑ ^ (2 : ℝ)))
    (fun n => ((aesm_muP (hmeas n)).enorm).pow_const 2)
    (fun n => Filter.Eventually.of_forall (fun z => hbound n z))
    hbfin
    (Filter.Eventually.of_forall (fun z => hpt z))
  have hJ : Tendsto (fun n : ℕ => ∫⁻ z, ‖EHardy n ν D z‖ₑ ^ (2 : ℝ) ∂(muP P)) atTop (𝓝 0) := by
    simpa using key
  have hfun : (fun n : ℕ => UnforcedLeray.Short.IIb.phaseLpNorm P 2 (EHardy n ν D)) =
      fun n : ℕ => (ENNReal.ofReal P⁻¹ * ∫⁻ z, ‖EHardy n ν D z‖ₑ ^ (2 : ℝ) ∂(muP P)) ^ (1 / 2 : ℝ) :=
    funext fun n => phaseLpNorm_eq P _ (hmeas n)
  refine ⟨hmeas, ?_⟩
  rw [hfun]
  have h8 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal P⁻¹) hJ (Or.inr ENNReal.ofReal_ne_top)
  have h9 := ((ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto
    (ENNReal.ofReal P⁻¹ * 0)).comp h8
  have h10 : (ENNReal.ofReal P⁻¹ * 0) ^ (1 / 2 : ℝ) = 0 := by
    rw [mul_zero]
    exact ENNReal.zero_rpow_of_pos (by norm_num)
  rw [h10] at h9
  exact h9
