import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3_1
import UnforcedLeray.Short.PartIIa.Tasks.F03bWindowNorms
import UnforcedLeray.Units.B0424.Chart

/-!
# The reversed chart `θ = 1 - e^{-t}`, `x = e^{-t/2} y` (task `PartII-a:F09/3/1/2/org`)

Source `the November 2 reference manuscript`
lines 1426-1442 and 1431-1441 (reversed window).  The chart `revChart (t, y) = (1 - e^{-t},
e^{-t/2} y)` carries `e^{-t} e^{-3t/2} dt dy` to `dθ dx` on `θ < 1`; through it
`adjWindowField`, `adjWindowForce` become explicit fields of `(t, y)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Parabolic
  UnforcedLeray.Short.PartIIa.Rep UnforcedLeray.B0424

/-- The reversed chart `(t, y) ↦ (1 - e^{-t}, e^{-t/2} y)` (line 1442). -/
def revChart (p : ℝ × Space) : ℝ × Space := (1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2)

theorem rev_lintegral_time (G : PS 3 → ℝ≥0∞) (hG : Measurable G)
    (h0 : ∀ p : PS 3, 1 ≤ p.1 → G p = 0) :
    ∫⁻ p, G p = ∫⁻ p : PS 3, ENNReal.ofReal (Real.exp (-p.1)) * G (1 - Real.exp (-p.1), p.2) := by
  rw [Measure.volume_eq_prod, lintegral_prod _ hG.aemeasurable]
  have hm : Measurable fun p : PS 3 => ENNReal.ofReal (Real.exp (-p.1)) *
      G (1 - Real.exp (-p.1), p.2) :=
    (by fun_prop : Measurable fun p : PS 3 => ENNReal.ofReal (Real.exp (-p.1))).mul
      (hG.comp (by fun_prop))
  rw [lintegral_prod _ hm.aemeasurable]
  set Φ : ℝ → ℝ≥0∞ := fun θ => ∫⁻ x, G (θ, x) with hΦ
  have hsupp : Φ.support ⊆ Iio (1 : ℝ) := by
    intro θ hθ
    by_contra h
    apply hθ
    simp only [hΦ]
    exact (lintegral_congr fun x => h0 (θ, x) (not_lt.1 h)).trans lintegral_zero
  have hinner : ∀ t : ℝ, ∫⁻ x, ENNReal.ofReal (Real.exp (-t)) * G (1 - Real.exp (-t), x) =
      ENNReal.ofReal (Real.exp (-t)) * Φ (1 - Real.exp (-t)) := fun t =>
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  simp only [hinner]
  have h1 : ∫⁻ θ, Φ θ = ∫⁻ θ in Iio (1 : ℝ), Φ θ := (setLIntegral_eq_of_support_subset hsupp).symm
  rw [h1]
  have himg : (fun t : ℝ => 1 - Real.exp (-t)) '' univ = Iio 1 := by
    ext θ
    simp only [mem_image, mem_univ, true_and, mem_Iio]
    constructor
    · rintro ⟨t, rfl⟩
      have := Real.exp_pos (-t)
      linarith
    · intro hθ
      refine ⟨-Real.log (1 - θ), ?_⟩
      rw [neg_neg, Real.exp_log (by linarith)]
      ring
  have := lintegral_image_eq_lintegral_abs_deriv_mul (s := (univ : Set ℝ))
    (f := fun t : ℝ => 1 - Real.exp (-t)) (f' := fun t => Real.exp (-t)) MeasurableSet.univ
    (fun t _ => by
      have h := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).const_sub 1
      have h' : HasDerivAt (fun t : ℝ => 1 - Real.exp (-t)) (Real.exp (-t)) t := by
        simpa using h
      exact h'.hasDerivWithinAt)
    (fun a _ b _ hab => by
      have : Real.exp (-a) = Real.exp (-b) := by simpa using hab
      have := Real.exp_injective this
      linarith) Φ
  rw [himg] at this
  rw [this, Measure.restrict_univ]
  refine lintegral_congr fun t => ?_
  rw [abs_of_pos (Real.exp_pos _)]

/-- **Change of variables.** For `G ≥ 0` measurable vanishing on `θ ≥ 1`,
`∫ G = ∫ e^{-5t/2} G(revChart (t, y)) dt dy`. -/
theorem rev_lintegral (G : PS 3 → ℝ≥0∞) (hG : Measurable G)
    (h0 : ∀ p : PS 3, 1 ≤ p.1 → G p = 0) :
    ∫⁻ p, G p = ∫⁻ p : PS 3, ENNReal.ofReal (Real.exp (-(5 * p.1 / 2))) * G (revChart p) := by
  rw [rev_lintegral_time G hG h0]
  set H : PS 3 → ℝ≥0∞ := fun p => ENNReal.ofReal (Real.exp (-p.1)) *
    G (1 - Real.exp (-p.1), p.2) with hH
  have := lintegral_dilChart' (fun p : PS 3 => ENNReal.ofReal (Real.exp (-(3 * p.1 / 2))) *
    H (p.1, Real.exp (-(p.1 / 2)) • p.2))
  have e1 : ∫⁻ p : PS 3, H p = ∫⁻ p : PS 3, rhoD p * (ENNReal.ofReal (Real.exp (-(3 * (dilChart p).1 / 2))) *
      H ((dilChart p).1, Real.exp (-((dilChart p).1 / 2)) • (dilChart p).2)) := by
    refine lintegral_congr fun p => ?_
    simp only [dilChart, rhoD, smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp
  rw [← e1] at this
  rw [← this]
  refine lintegral_congr fun p => ?_
  simp only [hH, revChart]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 3
  ring

/-! ### The field and force through the chart -/

theorem rev_windowField_chart (χ : ℝ → ℝ) (τ₀ : ℝ) (W : ℝ × Space → CVec3) (c : Fin 3)
    (p : ℝ × Space) :
    adjWindowField χ τ₀ W c (revChart p) = ((χ p.1 : ℝ) : ℂ) * W (τ₀ - p.1, p.2) c := by
  have hlt : (revChart p).1 < 1 := by
    simp only [revChart]; have := Real.exp_pos (-p.1); linarith
  have hlog : Real.log (1 - (revChart p).1) = -p.1 := by
    simp only [revChart, sub_sub_cancel, Real.log_exp]
  have h2 : Real.exp (p.1 / 2) • (revChart p).2 = p.2 := by
    simp only [revChart, smul_smul]
    rw [← Real.exp_add]
    have : p.1 / 2 + -(p.1 / 2) = 0 := by ring
    rw [this]; simp
  simp only [adjWindowField, hlt, ite_true]
  rw [hlog, neg_neg, h2, show τ₀ + -p.1 = τ₀ - p.1 by ring]

theorem rev_windowForce_chart (μ : ℂ) (χ : ℝ → ℝ) (τ₀ : ℝ) (W Fr : ℝ × Space → CVec3)
    (c : Fin 3) (p : ℝ × Space) :
    adjWindowForce μ χ τ₀ W Fr c (revChart p) =
      ((Real.exp p.1 : ℝ) : ℂ) *
        ((((deriv χ p.1 : ℝ) : ℂ) - (1 + (starRingEnd ℂ) μ) * ((χ p.1 : ℝ) : ℂ)) *
            W (τ₀ - p.1, p.2) c + ((χ p.1 : ℝ) : ℂ) * Fr (τ₀ - p.1, p.2) c) := by
  have hlt : (revChart p).1 < 1 := by
    simp only [revChart]; have := Real.exp_pos (-p.1); linarith
  have hlog : Real.log (1 - (revChart p).1) = -p.1 := by
    simp only [revChart, sub_sub_cancel, Real.log_exp]
  have h2 : Real.exp (p.1 / 2) • (revChart p).2 = p.2 := by
    simp only [revChart, smul_smul]
    rw [← Real.exp_add]
    have : p.1 / 2 + -(p.1 / 2) = 0 := by ring
    rw [this]; simp
  simp only [adjWindowForce, hlt, ite_true]
  rw [hlog, neg_neg, h2, show τ₀ + -p.1 = τ₀ - p.1 by ring]

/-! ### Slices along the reflected time -/

theorem IsRep.slice_sub {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)] {w : Yq P r}
    {W : ℝ × Space → CVec3} (hW : IsRep w W) (τ₀ : ℝ) :
    ∀ᵐ t : ℝ, (fun y => W (τ₀ - t, y)) =ᵐ[volume]
      (w ((τ₀ - t : ℝ) : AddCircle P) : Space → CVec3) :=
  (Measure.measurePreserving_sub_left (volume : Measure ℝ) τ₀).quasiMeasurePreserving.ae hW.slice

/-- `∫ m(t) |W(τ₀ - t, y)|^q dt dy = ∫ m(t) ‖w(τ₀ - t)‖_q^q dt`. -/
theorem rev_lintegral_rep {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)] (hrt : r ≠ ⊤)
    {w : Yq P r} {W : ℝ × Space → CVec3} (hW : IsRep w W) (τ₀ : ℝ) {m : ℝ → ℝ≥0∞}
    (hm : Measurable m) :
    ∫⁻ p : ℝ × Space, m p.1 * ‖W (τ₀ - p.1, p.2)‖ₑ ^ r.toReal =
      ∫⁻ t, m t * ‖w ((τ₀ - t : ℝ) : AddCircle P)‖ₑ ^ r.toReal := by
  have hWm : Measurable fun p : ℝ × Space => ‖W (τ₀ - p.1, p.2)‖ₑ ^ r.toReal := by
    have h1 : Measurable fun p : ℝ × Space => W (τ₀ - p.1, p.2) :=
      hW.meas.measurable.comp (by fun_prop)
    exact h1.enorm.pow_const _
  rw [Measure.volume_eq_prod]
  have hmeas : AEMeasurable (fun p : ℝ × Space => m p.1 * ‖W (τ₀ - p.1, p.2)‖ₑ ^ r.toReal)
      (volume.prod volume) := ((hm.comp measurable_fst).mul hWm).aemeasurable
  rw [lintegral_prod _ hmeas]
  refine lintegral_congr_ae ?_
  filter_upwards [IsRep.slice_sub hW τ₀] with t ht
  have hmt : Measurable fun y : Space => ‖W (τ₀ - t, y)‖ₑ ^ r.toReal :=
    (hW.meas.measurable.comp (by fun_prop : Measurable fun y : Space => (τ₀ - t, y))).enorm.pow_const _
  rw [lintegral_const_mul (m t) hmt]
  congr 1
  rw [← lintegral_enorm_rpow_Lp _ hrt]
  refine lintegral_congr_ae ?_
  filter_upwards [ht] with y hy
  rw [hy]

/-- The window `|t| < 2` becomes `τ ∈ (τ₀-2, τ₀+2)` under `τ = τ₀ - t`. -/
theorem rev_window_transfer {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)] (w : Yq P r)
    (τ₀ : ℝ) :
    ∫⁻ t, (Ioo (-2 : ℝ) 2).indicator (fun t => ‖w ((τ₀ - t : ℝ) : AddCircle P)‖ₑ ^ r.toReal) t =
      ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2), ‖w (τ : AddCircle P)‖ₑ ^ r.toReal := by
  have h1 : ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2), ‖w (τ : AddCircle P)‖ₑ ^ r.toReal =
      ∫⁻ τ, (Ioo (τ₀ - 2) (τ₀ + 2)).indicator (fun τ => ‖w (τ : AddCircle P)‖ₑ ^ r.toReal) τ :=
    (lintegral_indicator measurableSet_Ioo _).symm
  rw [h1]
  calc ∫⁻ t, (Ioo (-2 : ℝ) 2).indicator (fun t => ‖w ((τ₀ - t : ℝ) : AddCircle P)‖ₑ ^ r.toReal) t
      = ∫⁻ t, (Ioo (τ₀ - 2) (τ₀ + 2)).indicator
          (fun τ => ‖w (τ : AddCircle P)‖ₑ ^ r.toReal) (τ₀ - t) := by
        refine lintegral_congr fun t => ?_
        by_cases ht : t ∈ Ioo (-2 : ℝ) 2
        · have ht' : τ₀ - t ∈ Ioo (τ₀ - 2) (τ₀ + 2) :=
            ⟨by linarith [ht.2], by linarith [ht.1]⟩
          rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht']
        · have ht' : τ₀ - t ∉ Ioo (τ₀ - 2) (τ₀ + 2) := fun h =>
            ht ⟨by linarith [h.2], by linarith [h.1]⟩
          rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht']
    _ = ∫⁻ τ, (Ioo (τ₀ - 2) (τ₀ + 2)).indicator
          (fun τ => ‖w (τ : AddCircle P)‖ₑ ^ r.toReal) τ :=
        lintegral_sub_left_eq_self _ τ₀

end UnforcedLeray.Short.PartIIa
