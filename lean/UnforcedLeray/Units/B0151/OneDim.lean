import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# B0151, part 1: the two one-dimensional pointwise bounds

Blueprint unit **B0151** (`unlabeled:2291`), `paper/main.tex` lines 2291–2294, 2310–2314,
2510–2511. The manuscript says the Sobolev and interpolation constants are uniform for
cylinder periods at least one, "by the usual two-dimensional proof with its harmless
low-frequency term". Every such proof below reduces to two one-dimensional facts.

* On a circle of length `L` (`abs_le_periodic`):
  `|φ(q)| ≤ L⁻¹ ∫₀ᴸ |φ| + ∫₀ᴸ |φ'|`. The term `L⁻¹ ∫₀ᴸ |φ|` is the low-frequency term; it is
  at most `∫₀ᴸ |φ|` once `L ≥ 1`, which is the whole source of uniformity.
* On the line (`abs_le_integral_deriv`): `|φ(t)| ≤ ∫ |φ'|` when `φ` and `φ'` are integrable.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace UnforcedLeray.B0151

/-- The periodic pointwise bound with its low-frequency term (B0151, tex 2291–2294). -/
theorem abs_le_periodic {L : ℝ} (hL : 0 < L) {φ φ' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt φ (φ' x) x) (hc : Continuous φ') (hp : Function.Periodic φ L)
    (q : ℝ) :
    |φ q| ≤ L⁻¹ * (∫ s in Ioc 0 L, |φ s|) + ∫ s in Ioc 0 L, |φ' s| := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  obtain ⟨q', hq', hqq'⟩ := hp.exists_mem_Ico₀ hL q
  have hvol : volume (Ioc (0 : ℝ) L) = ENNReal.ofReal L := by
    simp [Real.volume_Ioc]
  have hint : IntegrableOn (fun s => |φ s|) (Ioc 0 L) :=
    (hφc.abs.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  obtain ⟨q0, hq0, hmin⟩ := exists_le_setAverage (μ := volume) (s := Ioc 0 L)
    (by simp [hvol, hL]) (by simp [hvol]) hint
  rw [setAverage_eq, smul_eq_mul] at hmin
  have hreal : volume.real (Ioc (0 : ℝ) L) = L := by
    simp [Measure.real, hvol, hL.le]
  rw [hreal] at hmin
  have hftc : φ q' - φ q0 = ∫ s in q0..q', φ' s :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (hc.intervalIntegrable _ _)).symm
  have hsub : Set.uIoc q0 q' ⊆ Ioc 0 L := by
    intro x hx
    rcases Set.mem_uIoc.1 hx with h | h
    · exact ⟨lt_trans hq0.1 h.1, h.2.trans hq'.2.le⟩
    · exact ⟨lt_of_le_of_lt hq'.1 h.1, h.2.trans hq0.2⟩
  have hbound : |∫ s in q0..q', φ' s| ≤ ∫ s in Ioc 0 L, |φ' s| := by
    have h1 := intervalIntegral.norm_integral_le_integral_norm_uIoc (f := φ') (a := q0)
      (b := q') (μ := volume)
    simp only [Real.norm_eq_abs] at h1
    refine h1.trans ?_
    refine setIntegral_mono_set ?_ ?_ hsub.eventuallyLE
    · exact (hc.abs.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    · exact ae_of_all _ fun x => abs_nonneg _
  rw [hqq']
  calc |φ q'| = |φ q0 + (φ q' - φ q0)| := by ring_nf
    _ ≤ |φ q0| + |φ q' - φ q0| := abs_add_le _ _
    _ ≤ _ := by rw [hftc]; exact add_le_add hmin hbound

/-- The line bound: a function vanishing at `-∞` is bounded by the total variation
(B0151, tex 2310–2314). -/
theorem abs_le_integral_deriv {φ φ' : ℝ → ℝ} (hd : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ' : Integrable φ') (hφ : Integrable φ) (t : ℝ) : |φ t| ≤ ∫ x, |φ' x| := by
  have h0 : Tendsto φ atBot (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := t) (fun x _ => hd x)
      hφ'.integrableOn hφ.integrableOn
  have h := integral_Iic_of_hasDerivAt_of_tendsto' (a := t) (fun x _ => hd x)
    hφ'.integrableOn h0
  rw [sub_zero] at h
  rw [← h]
  calc |∫ x in Iic t, φ' x| ≤ ∫ x in Iic t, |φ' x| := abs_integral_le_integral_abs
    _ ≤ ∫ x, |φ' x| := setIntegral_le_integral hφ'.abs (ae_of_all _ fun x => abs_nonneg _)

/-- The line bound in `ℝ≥0∞`, the form used under Tonelli. -/
theorem ofReal_abs_le_lintegral_deriv {φ φ' : ℝ → ℝ} (hd : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ' : Integrable φ') (hφ : Integrable φ) (t : ℝ) :
    ENNReal.ofReal |φ t| ≤ ∫⁻ x, ‖φ' x‖ₑ := by
  have h := ofReal_integral_eq_lintegral_ofReal hφ'.abs (ae_of_all _ fun x => abs_nonneg (φ' x))
  simp only [Real.enorm_eq_ofReal_abs]
  rw [← h]
  exact ENNReal.ofReal_le_ofReal (abs_le_integral_deriv hd hφ' hφ t)

/-- The periodic bound in `ℝ≥0∞`. -/
theorem ofReal_abs_le_periodic {L : ℝ} (hL : 0 < L) {φ φ' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt φ (φ' x) x) (hc : Continuous φ') (hp : Function.Periodic φ L)
    (q : ℝ) :
    ENNReal.ofReal |φ q| ≤ ENNReal.ofReal L⁻¹ * (∫⁻ s in Ioc 0 L, ‖φ s‖ₑ) +
      ∫⁻ s in Ioc 0 L, ‖φ' s‖ₑ := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  have hi1 : IntegrableOn φ (Ioc 0 L) := (hφc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hi2 : IntegrableOn φ' (Ioc 0 L) := (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have e1 := ofReal_integral_eq_lintegral_ofReal hi1.abs (ae_of_all _ fun x => abs_nonneg (φ x))
  have e2 := ofReal_integral_eq_lintegral_ofReal hi2.abs (ae_of_all _ fun x => abs_nonneg (φ' x))
  simp only [Real.enorm_eq_ofReal_abs]
  rw [← e1, ← e2, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (integral_nonneg fun x => abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (abs_le_periodic hL hd hc hp q)

end UnforcedLeray.B0151
