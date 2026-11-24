import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.DivZero
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.WeightLogBounds.Calc

/-!
# Helpers for `PartIII-a:T21/2/2/3/8` and `T21/2/2/3/9` (the `E_1` leaves 8 and 9)

Source: `the November 2 reference manuscript` lines 2954-2956, 3060-3071.
Smoothness, periodicity and gradient bound of the periodic weight, smoothness and periodicity of
`pdCx k Φ`, the product rule for `‖u‖²`, and the cell divergence identity.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

open UnforcedLeray.Short.IIIa

/-! ## The periodic weight -/

theorem pw_eq_Qf (m d : ℝ) (y : ℝ × ℝ) : periodicWeight m d y = WLB.Qf d y ^ m := rfl

theorem Qf_contDiff (d : ℝ) : ContDiff ℝ ∞ (WLB.Qf d) := by
  unfold WLB.Qf
  fun_prop

theorem pw_contDiff (m d : ℝ) : ContDiff ℝ ∞ (periodicWeight m d) := by
  have : periodicWeight m d = fun y => WLB.Qf d y ^ m := rfl
  rw [this]
  exact (Qf_contDiff d).rpow_const_of_ne (fun y => (WLB.Qf_pos d y).ne')

theorem pw_pos (m d : ℝ) (y : ℝ × ℝ) : 0 < periodicWeight m d y :=
  Real.rpow_pos_of_pos (WLB.Qf_pos d y) m

theorem pw_periodic (m d : ℝ) (hd : d ≠ 0) (y : ℝ × ℝ) :
    periodicWeight m d (y.1 + d, y.2) = periodicWeight m d y := by
  unfold periodicWeight
  have : Real.sin (Real.pi * (y.1 + d) / d) ^ 2 = Real.sin (Real.pi * y.1 / d) ^ 2 := by
    have h : Real.pi * (y.1 + d) / d = Real.pi * y.1 / d + Real.pi := by field_simp
    rw [h, Real.sin_add_pi]; ring
  simp only [this]


theorem pw_pd_eq (m d : ℝ) (k : Fin 2) (y : ℝ × ℝ) :
    B0579.pd k (periodicWeight m d) y =
      periodicWeight m d y * B0579.pd k (fun x => Real.log (periodicWeight m d x)) y := by
  have hd : DifferentiableAt ℝ (periodicWeight m d) y :=
    ((pw_contDiff m d).differentiable (by simp)) y
  have hp := pw_pos m d y
  have hlog := hd.hasFDerivAt.log hp.ne'
  have e : B0579.pd k (fun x => Real.log (periodicWeight m d x)) y =
      (periodicWeight m d y)⁻¹ * B0579.pd k (periodicWeight m d) y := by
    unfold B0579.pd
    rw [hlog.fderiv]
    simp
  rw [e]; field_simp

theorem pw_pd_abs_le (m d CW : ℝ)
    (h : ∀ (y : ℝ × ℝ) (k : Fin 2),
      |B0579.pd k (fun x => Real.log (periodicWeight m d x)) y| ≤ CW)
    (k : Fin 2) (y : ℝ × ℝ) :
    |B0579.pd k (periodicWeight m d) y| ≤ CW * periodicWeight m d y := by
  have hp := pw_pos m d y
  rw [pw_pd_eq, abs_mul, abs_of_pos hp, mul_comm]
  exact mul_le_mul_of_nonneg_right (h y k) hp.le

/-! ## Derivatives of complex fields -/

theorem pdCx_contDiff {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (k : Fin 2) :
    ContDiff ℝ ∞ (pdCx k Φ) := by
  unfold pdCx
  exact (hΦ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem fderiv_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ × ℝ → E}
    (d : ℝ) (hp : ∀ y : ℝ × ℝ, f (y.1 + d, y.2) = f y) (y : ℝ × ℝ) :
    fderiv ℝ f (y.1 + d, y.2) = fderiv ℝ f y := by
  have h1 : (fun x : ℝ × ℝ => f (x + (d, 0))) = f := by
    funext x
    have e : x + (d, 0) = (x.1 + d, x.2) := by ext <;> simp
    rw [e]
    exact hp x
  have h2 := fderiv_comp_add_right (f := f) (𝕜 := ℝ) (x := y) (d, 0)
  rw [h1] at h2
  have e : y + (d, 0) = (y.1 + d, y.2) := by ext <;> simp
  rw [e] at h2
  exact h2.symm

theorem pdCx_periodic {Φ : ℝ × ℝ → ℂ} (d : ℝ) (hp : ∀ y : ℝ × ℝ, Φ (y.1 + d, y.2) = Φ y)
    (k : Fin 2) (y : ℝ × ℝ) : pdCx k Φ (y.1 + d, y.2) = pdCx k Φ y := by
  unfold pdCx
  rw [fderiv_periodic d hp y]

theorem pd_normSq {u : ℝ × ℝ → ℂ} (hu : Differentiable ℝ u) (k : Fin 2) (y : ℝ × ℝ) :
    B0579.pd k (fun x => ‖u x‖ ^ 2) y = 2 * (starRingEnd ℂ (u y) * pdCx k u y).re := by
  have h := (hu y).hasFDerivAt.norm_sq
  unfold B0579.pd pdCx
  rw [h.fderiv]
  simp [Complex.inner]
  ring_nf

theorem pd_mul {f g : ℝ × ℝ → ℝ} {y : ℝ × ℝ} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) (k : Fin 2) :
    B0579.pd k (fun x => f x * g x) y = f y * B0579.pd k g y + g y * B0579.pd k f y := by
  unfold B0579.pd
  rw [fderiv_fun_mul hf hg]
  simp


/-! ## The cell divergence identity for the transport -/

open UnforcedLeray.Short.IIb.TransportIBP in
theorem pdContinuous {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (j : Fin 2) :
    Continuous (B0579.pd j φ) := continuous_pd hφ j

theorem re_conj_transC (V : ℝ × ℝ → Fin 2 → ℝ) (u : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    (starRingEnd ℂ (u y) * transC V u y).re =
      V y 0 * (starRingEnd ℂ (u y) * pdCx 0 u y).re +
        V y 1 * (starRingEnd ℂ (u y) * pdCx 1 u y).re := by
  have h : ∀ (a : ℝ) (z z' : ℂ), (z * ((a : ℂ) * z')).re = a * (z * z').re := by
    intro a z z'
    rw [mul_left_comm]
    exact Complex.re_ofReal_mul a _
  unfold transC
  rw [mul_add, Complex.add_re, h, h]

theorem div_expr (w : ℝ × ℝ → ℝ) (V : ℝ × ℝ → Fin 2 → ℝ) (u : ℝ × ℝ → ℂ)
    (hw : ContDiff ℝ 1 w) (hV : ContDiff ℝ 1 V) (hu : ContDiff ℝ 1 u) (y : ℝ × ℝ) :
    B0579.pd 0 (fun x => w x * V x 0 * ‖u x‖ ^ 2) y +
        B0579.pd 1 (fun x => w x * V x 1 * ‖u x‖ ^ 2) y =
      (V y 0 * B0579.pd 0 w y + V y 1 * B0579.pd 1 w y +
          w y * (B0579.pd 0 (fun x => V x 0) y + B0579.pd 1 (fun x => V x 1) y)) * ‖u y‖ ^ 2 +
        2 * (w y * (starRingEnd ℂ (u y) * transC V u y).re) := by
  have hwd : DifferentiableAt ℝ w y := (hw.differentiable one_ne_zero) y
  have hVj : ∀ j : Fin 2, DifferentiableAt ℝ (fun x => V x j) y := fun j =>
    ((contDiff_pi.1 hV j).differentiable one_ne_zero) y
  have hud : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hN : DifferentiableAt ℝ (fun x => ‖u x‖ ^ 2) y :=
    (((contDiff_norm_sq ℝ).comp hu).differentiable one_ne_zero) y
  have key : ∀ k j : Fin 2, B0579.pd k (fun x => w x * V x j * ‖u x‖ ^ 2) y =
      w y * V y j * (2 * (starRingEnd ℂ (u y) * pdCx k u y).re) +
        ‖u y‖ ^ 2 * (w y * B0579.pd k (fun x => V x j) y + V y j * B0579.pd k w y) := by
    intro k j
    have hwV : DifferentiableAt ℝ (fun x => w x * V x j) y := hwd.mul (hVj j)
    rw [pd_mul hwV hN, pd_normSq hud, pd_mul hwd (hVj j)]
  rw [key 0 0, key 1 1, re_conj_transC]
  ring

theorem transport_core (d : ℝ) (hd : 0 < d) (w : ℝ × ℝ → ℝ) (V : ℝ × ℝ → Fin 2 → ℝ)
    (u : ℝ × ℝ → ℂ) (hw : ContDiff ℝ 1 w) (hwp : ∀ y : ℝ × ℝ, w (y.1 + d, y.2) = w y)
    (hV : ContDiff ℝ 1 V) (hVp : ∀ y : ℝ × ℝ, V (y.1 + d, y.2) = V y)
    (hu : ContDiff ℝ 1 u) (hup : ∀ y : ℝ × ℝ, u (y.1 + d, y.2) = u y)
    (hi1 : IntegrableOn (fun y => w y * V y 1 * ‖u y‖ ^ 2) (B0579.cell d))
    (hA : IntegrableOn (fun y => (V y 0 * B0579.pd 0 w y + V y 1 * B0579.pd 1 w y +
          w y * (B0579.pd 0 (fun x => V x 0) y + B0579.pd 1 (fun x => V x 1) y)) * ‖u y‖ ^ 2)
        (B0579.cell d))
    (hB : IntegrableOn (fun y => w y * (starRingEnd ℂ (u y) * transC V u y).re)
        (B0579.cell d)) :
    2 * ∫ y in B0579.cell d, w y * (starRingEnd ℂ (u y) * transC V u y).re =
      -∫ y in B0579.cell d, (V y 0 * B0579.pd 0 w y + V y 1 * B0579.pd 1 w y +
          w y * (B0579.pd 0 (fun x => V x 0) y + B0579.pd 1 (fun x => V x 1) y)) * ‖u y‖ ^ 2 := by
  have hN : ContDiff ℝ 1 (fun x => ‖u x‖ ^ 2) := (contDiff_norm_sq ℝ).comp hu
  have h0 : ContDiff ℝ 1 (fun y => w y * V y 0 * ‖u y‖ ^ 2) :=
    (hw.mul (contDiff_pi.1 hV 0)).mul hN
  have h1 : ContDiff ℝ 1 (fun y => w y * V y 1 * ‖u y‖ ^ 2) :=
    (hw.mul (contDiff_pi.1 hV 1)).mul hN
  have hp0 : ∀ y : ℝ × ℝ, (fun y => w y * V y 0 * ‖u y‖ ^ 2) (y.1 + d, y.2) =
      (fun y => w y * V y 0 * ‖u y‖ ^ 2) y := by
    intro y
    simp only [hwp, hVp, hup]
  have hdiv : IntegrableOn (fun y => B0579.pd 0 (fun x => w x * V x 0 * ‖u x‖ ^ 2) y +
      B0579.pd 1 (fun x => w x * V x 1 * ‖u x‖ ^ 2) y) (B0579.cell d) := by
    have := hA.add (hB.const_mul 2)
    refine this.congr_fun (fun y _ => ?_) (B0579.measurableSet_cell d)
    exact (div_expr w V u hw hV hu y).symm
  have hz := UnforcedLeray.Short.IIIa.E0.cellDivZero d hd _ _ h0 h1 hp0 hi1 hdiv
  have hz' : ∫ y in B0579.cell d, (B0579.pd 0 (fun x => w x * V x 0 * ‖u x‖ ^ 2) y +
      B0579.pd 1 (fun x => w x * V x 1 * ‖u x‖ ^ 2) y) =
      (∫ y in B0579.cell d, (V y 0 * B0579.pd 0 w y + V y 1 * B0579.pd 1 w y +
          w y * (B0579.pd 0 (fun x => V x 0) y + B0579.pd 1 (fun x => V x 1) y)) * ‖u y‖ ^ 2) +
        2 * ∫ y in B0579.cell d, w y * (starRingEnd ℂ (u y) * transC V u y).re := by
    rw [← integral_const_mul, ← integral_add hA (hB.const_mul 2)]
    exact integral_congr_ae (ae_of_all _ fun y => div_expr w V u hw hV hu y)
  linarith


/-! ## Bounds of the velocity -/

theorem V_abs_le {V : ℝ × ℝ → Fin 2 → ℝ} {CV : ℝ}
    (hVb : ∀ j : ℕ, j ≤ 1 → ∀ y : ℝ × ℝ, ‖iteratedFDeriv ℝ j V y‖ ≤ CV) (y : ℝ × ℝ)
    (j : Fin 2) : |V y j| ≤ CV := by
  have h := hVb 0 (by norm_num) y
  rw [norm_iteratedFDeriv_zero] at h
  have := norm_le_pi_norm (V y) j
  rw [Real.norm_eq_abs] at this
  exact this.trans h

theorem CV_nonneg {V : ℝ × ℝ → Fin 2 → ℝ} {CV : ℝ}
    (hVb : ∀ j : ℕ, j ≤ 1 → ∀ y : ℝ × ℝ, ‖iteratedFDeriv ℝ j V y‖ ≤ CV) : 0 ≤ CV :=
  (norm_nonneg _).trans (hVb 0 (by norm_num) 0)

theorem norm_dir (k : Fin 2) : ‖B0579.dir k‖ = 1 := by
  fin_cases k <;> simp [B0579.dir]

theorem pdV_abs_le {V : ℝ × ℝ → Fin 2 → ℝ} {CV : ℝ} (hV : ContDiff ℝ 1 V)
    (hVb : ∀ j : ℕ, j ≤ 1 → ∀ y : ℝ × ℝ, ‖iteratedFDeriv ℝ j V y‖ ≤ CV) (y : ℝ × ℝ)
    (k j : Fin 2) : |B0579.pd k (fun x => V x j) y| ≤ CV := by
  have hd : DifferentiableAt ℝ V y := (hV.differentiable one_ne_zero) y
  have h1 := hVb 1 le_rfl y
  rw [norm_iteratedFDeriv_one] at h1
  have e : B0579.pd k (fun x => V x j) y = fderiv ℝ V y (B0579.dir k) j := by
    unfold B0579.pd
    have := (hasFDerivAt_pi'.1 hd.hasFDerivAt) j
    rw [this.fderiv]
    simp
  rw [e]
  have h2 := norm_le_pi_norm (fderiv ℝ V y (B0579.dir k)) j
  rw [Real.norm_eq_abs] at h2
  refine h2.trans ?_
  calc ‖fderiv ℝ V y (B0579.dir k)‖ ≤ ‖fderiv ℝ V y‖ * ‖B0579.dir k‖ :=
        (fderiv ℝ V y).le_opNorm _
    _ ≤ CV := by rw [norm_dir, mul_one]; exact h1

/-! ## Integrability and the identity -/

theorem pdCx_cont {u : ℝ × ℝ → ℂ} (hu : ContDiff ℝ ∞ u) (l : Fin 2) : Continuous (pdCx l u) :=
  (pdCx_contDiff hu l).continuous

theorem transport_ibp_gen (d : ℝ) (hd : 0 < d) (w : ℝ × ℝ → ℝ) (CW CV : ℝ)
    (V : ℝ × ℝ → Fin 2 → ℝ) (u : ℝ × ℝ → ℂ) (hw : ContDiff ℝ 1 w)
    (hwp : ∀ y : ℝ × ℝ, w (y.1 + d, y.2) = w y) (hw0 : ∀ y, 0 ≤ w y)
    (hgrad : ∀ (y : ℝ × ℝ) (l : Fin 2), |B0579.pd l w y| ≤ CW * w y)
    (hV : ContDiff ℝ 1 V) (hVp : ∀ y : ℝ × ℝ, V (y.1 + d, y.2) = V y)
    (hVb : ∀ j : ℕ, j ≤ 1 → ∀ y : ℝ × ℝ, ‖iteratedFDeriv ℝ j V y‖ ≤ CV)
    (hu : ContDiff ℝ ∞ u) (hup : ∀ y : ℝ × ℝ, u (y.1 + d, y.2) = u y)
    (hi0 : IntegrableOn (fun y => w y * ‖u y‖ ^ 2) (B0579.cell d))
    (hi1 : ∀ l : Fin 2, IntegrableOn (fun y => w y * ‖pdCx l u y‖ ^ 2) (B0579.cell d)) :
    IntegrableOn (fun y => w y * (starRingEnd ℂ (u y) * transC V u y).re) (B0579.cell d) ∧
    IntegrableOn (fun y => (V y 0 * B0579.pd 0 w y + V y 1 * B0579.pd 1 w y +
          w y * (B0579.pd 0 (fun x => V x 0) y + B0579.pd 1 (fun x => V x 1) y)) * ‖u y‖ ^ 2)
        (B0579.cell d) ∧
    2 * ∫ y in B0579.cell d, w y * (starRingEnd ℂ (u y) * transC V u y).re =
      -∫ y in B0579.cell d, (V y 0 * B0579.pd 0 w y + V y 1 * B0579.pd 1 w y +
          w y * (B0579.pd 0 (fun x => V x 0) y + B0579.pd 1 (fun x => V x 1) y)) * ‖u y‖ ^ 2 := by
  have hCV := CV_nonneg hVb
  have hcell := B0579.measurableSet_cell d
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by exact_mod_cast le_top)
  have hwc : Continuous w := hw.continuous
  have huc : Continuous u := hu.continuous
  have hVc : Continuous V := hV.continuous
  have hV0 : Continuous (fun y => V y 0) := (continuous_apply 0).comp hVc
  have hV1 : Continuous (fun y => V y 1) := (continuous_apply 1).comp hVc
  have hpw : ∀ l, Continuous (B0579.pd l w) := fun l => pdContinuous hw l
  have hpV : ∀ k j : Fin 2, Continuous (B0579.pd k (fun x => V x j)) := fun k j =>
    pdContinuous (contDiff_pi.1 hV j) k
  have hpu : ∀ l, Continuous (pdCx l u) := fun l => pdCx_cont hu l
  have hnu : Continuous (fun y => ‖u y‖ ^ 2) := huc.norm.pow 2
  have hcA : Continuous (fun y => (V y 0 * B0579.pd 0 w y + V y 1 * B0579.pd 1 w y +
          w y * (B0579.pd 0 (fun x => V x 0) y + B0579.pd 1 (fun x => V x 1) y)) * ‖u y‖ ^ 2) :=
    (((hV0.mul (hpw 0)).add (hV1.mul (hpw 1))).add
      (hwc.mul ((hpV 0 0).add (hpV 1 1)))).mul hnu
  have hcT : ∀ l, Continuous (fun y => (starRingEnd ℂ (u y) * pdCx l u y).re) := fun l =>
    Complex.continuous_re.comp ((Complex.continuous_conj.comp huc).mul (hpu l))
  have hcB : Continuous (fun y => w y * (starRingEnd ℂ (u y) * transC V u y).re) := by
    have : (fun y => w y * (starRingEnd ℂ (u y) * transC V u y).re) =
        fun y => w y * (V y 0 * (starRingEnd ℂ (u y) * pdCx 0 u y).re +
          V y 1 * (starRingEnd ℂ (u y) * pdCx 1 u y).re) := by
      funext y; rw [re_conj_transC]
    rw [this]
    exact hwc.mul ((hV0.mul (hcT 0)).add (hV1.mul (hcT 1)))
  have hA : IntegrableOn (fun y => (V y 0 * B0579.pd 0 w y + V y 1 * B0579.pd 1 w y +
          w y * (B0579.pd 0 (fun x => V x 0) y + B0579.pd 1 (fun x => V x 1) y)) * ‖u y‖ ^ 2)
        (B0579.cell d) := by
    refine Integrable.mono' (hi0.const_mul (2 * CV * CW + 2 * CV)) hcA.aestronglyMeasurable
      (ae_restrict_of_forall_mem hcell fun y _ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖u y‖ ^ 2)]
    have hwy := hw0 y
    have b0 := V_abs_le hVb y 0
    have b1 := V_abs_le hVb y 1
    have g0 := hgrad y 0
    have g1 := hgrad y 1
    have d0 := pdV_abs_le hV hVb y 0 0
    have d1 := pdV_abs_le hV hVb y 1 1
    have t1 : |V y 0 * B0579.pd 0 w y| ≤ CV * (CW * w y) := by
      rw [abs_mul]; exact mul_le_mul b0 g0 (abs_nonneg _) hCV
    have t2 : |V y 1 * B0579.pd 1 w y| ≤ CV * (CW * w y) := by
      rw [abs_mul]; exact mul_le_mul b1 g1 (abs_nonneg _) hCV
    have t3 : |w y * (B0579.pd 0 (fun x => V x 0) y + B0579.pd 1 (fun x => V x 1) y)| ≤
        w y * (2 * CV) := by
      rw [abs_mul, abs_of_nonneg hwy]
      exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (by linarith)) hwy
    have hsum : |V y 0 * B0579.pd 0 w y + V y 1 * B0579.pd 1 w y +
          w y * (B0579.pd 0 (fun x => V x 0) y + B0579.pd 1 (fun x => V x 1) y)| ≤
        (2 * CV * CW + 2 * CV) * w y := by
      refine ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans ?_
      nlinarith
    calc _ ≤ (2 * CV * CW + 2 * CV) * w y * ‖u y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hsum (sq_nonneg _)
      _ = _ := by ring
  have hB : IntegrableOn (fun y => w y * (starRingEnd ℂ (u y) * transC V u y).re)
      (B0579.cell d) := by
    have hint : IntegrableOn (fun y => CV * (w y * ‖u y‖ ^ 2) +
        CV / 2 * (w y * ‖pdCx 0 u y‖ ^ 2) + CV / 2 * (w y * ‖pdCx 1 u y‖ ^ 2))
        (B0579.cell d) :=
      ((hi0.const_mul CV).add ((hi1 0).const_mul (CV / 2))).add ((hi1 1).const_mul (CV / 2))
    refine Integrable.mono' hint hcB.aestronglyMeasurable
      (ae_restrict_of_forall_mem hcell fun y _ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 y)]
    rw [re_conj_transC]
    have b0 := V_abs_le hVb y 0
    have b1 := V_abs_le hVb y 1
    have r0 : |(starRingEnd ℂ (u y) * pdCx 0 u y).re| ≤ ‖u y‖ * ‖pdCx 0 u y‖ := by
      calc _ ≤ ‖starRingEnd ℂ (u y) * pdCx 0 u y‖ := Complex.abs_re_le_norm _
        _ = _ := by rw [norm_mul, Complex.norm_conj]
    have r1 : |(starRingEnd ℂ (u y) * pdCx 1 u y).re| ≤ ‖u y‖ * ‖pdCx 1 u y‖ := by
      calc _ ≤ ‖starRingEnd ℂ (u y) * pdCx 1 u y‖ := Complex.abs_re_le_norm _
        _ = _ := by rw [norm_mul, Complex.norm_conj]
    have q0 : |V y 0 * (starRingEnd ℂ (u y) * pdCx 0 u y).re| ≤ CV * (‖u y‖ * ‖pdCx 0 u y‖) := by
      rw [abs_mul]; exact mul_le_mul b0 r0 (abs_nonneg _) hCV
    have q1 : |V y 1 * (starRingEnd ℂ (u y) * pdCx 1 u y).re| ≤ CV * (‖u y‖ * ‖pdCx 1 u y‖) := by
      rw [abs_mul]; exact mul_le_mul b1 r1 (abs_nonneg _) hCV
    have hq := (abs_add_le _ _).trans (add_le_add q0 q1)
    have hwy := hw0 y
    have h2 : ‖u y‖ * ‖pdCx 0 u y‖ + ‖u y‖ * ‖pdCx 1 u y‖ ≤
        ‖u y‖ ^ 2 + (‖pdCx 0 u y‖ ^ 2 + ‖pdCx 1 u y‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖u y‖ - ‖pdCx 0 u y‖), sq_nonneg (‖u y‖ - ‖pdCx 1 u y‖)]
    calc w y * |V y 0 * (starRingEnd ℂ (u y) * pdCx 0 u y).re +
          V y 1 * (starRingEnd ℂ (u y) * pdCx 1 u y).re|
        ≤ w y * (CV * (‖u y‖ * ‖pdCx 0 u y‖) + CV * (‖u y‖ * ‖pdCx 1 u y‖)) :=
          mul_le_mul_of_nonneg_left hq hwy
      _ = w y * (CV * (‖u y‖ * ‖pdCx 0 u y‖ + ‖u y‖ * ‖pdCx 1 u y‖)) := by ring
      _ ≤ w y * (CV * (‖u y‖ ^ 2 + (‖pdCx 0 u y‖ ^ 2 + ‖pdCx 1 u y‖ ^ 2) / 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hCV) hwy
      _ = _ := by ring
  have hi1' : IntegrableOn (fun y => w y * V y 1 * ‖u y‖ ^ 2) (B0579.cell d) := by
    refine Integrable.mono' (hi0.const_mul CV)
      (((hwc.mul hV1).mul hnu).aestronglyMeasurable)
      (ae_restrict_of_forall_mem hcell fun y _ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hw0 y),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖u y‖ ^ 2)]
    have := V_abs_le hVb y 1
    have hwy := hw0 y
    nlinarith [mul_nonneg hwy (sq_nonneg ‖u y‖), mul_le_mul_of_nonneg_left this
      (mul_nonneg hwy (sq_nonneg ‖u y‖))]
  exact ⟨hB, hA, transport_core d hd w V u hw hwp hV hVp hu1 hup hi1' hA hB⟩

end UnforcedLeray.Short.IIIa.AdjE1
