import UnforcedLeray.Units.B0151.Cell
import Mathlib.MeasureTheory.Function.L2Space

/-!
# B0151, part 3: Ladyzhenskaya's inequality on the cylinder, uniform for periods `L ≥ 1`

Blueprint unit **B0151** (`unlabeled:2291`), `paper/main.tex` lines 2291–2294 and 2310–2314:
`‖h‖₄² ≤ C ‖h‖₂ (‖∇h‖₂ + ‖h‖₂)` with `C` independent of the period `L ≥ 1`.

Proof (the two-dimensional proof with its low-frequency term). For every `(q, η)`,
`h(q,η)² ≤ F(η) := L⁻¹ ∫₀ᴸ h(s,η)² ds + ∫₀ᴸ |2 h ∂_q h|(s,η) ds` (`sq_le_circle`), and for
almost every `q`, `h(q,η)² ≤ G(q) := ∫ |2 h ∂_η h|(q,t) dt` (`ae_sq_le_line`). Hence
`∫ h⁴ ≤ (∫ G)(∫ F)` by Tonelli, and `L⁻¹ ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal ContDiff

namespace UnforcedLeray.B0151

open UnforcedLeray.GaussianVortex (partialX partialY)

/-- Along every `q`-circle, `h²` is bounded by its mean plus its total variation. -/
theorem sq_le_circle {L : ℝ} (hL : 0 < L) {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    (hp : IsPeriodicQ L h) (q η : ℝ) :
    ‖h (q, η)‖ₑ ^ 2 ≤ ENNReal.ofReal L⁻¹ * (∫⁻ s in Ioc 0 L, ‖h (s, η)‖ₑ ^ 2) +
      ∫⁻ s in Ioc 0 L, ‖2 * h (s, η) * partialX h (s, η)‖ₑ := by
  have hd : Differentiable ℝ h := hh.differentiable one_ne_zero
  have hc0 : Continuous h := hh.continuous
  have hc1 : Continuous (partialX h) := continuous_partialX hh
  have hc : Continuous fun s => 2 * h (s, η) * partialX h (s, η) := by fun_prop
  have hper : Function.Periodic (fun s => h (s, η) ^ 2) L := fun s => by
    simp only [hp s η]
  have := ofReal_abs_le_periodic hL (fun s => hasDerivAt_sq_sliceX hd s η) hc hper q
  simpa only [enorm_pow, ← enorm_sq_eq] using this

/-- Along almost every `η`-line, `h²` is bounded by its total variation. -/
theorem ae_sq_le_line {L : ℝ} {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    (h2 : MemLp h 2 (cellMeasure L)) (hy : MemLp (partialY h) 2 (cellMeasure L)) :
    ∀ᵐ q ∂(volume.restrict (Ioc 0 L)), ∀ η,
      ‖h (q, η)‖ₑ ^ 2 ≤ ∫⁻ t, ‖2 * h (q, t) * partialY h (q, t)‖ₑ := by
  have hd : Differentiable ℝ h := hh.differentiable one_ne_zero
  have i1 : Integrable (fun z => h z ^ 2) (cellMeasure L) := h2.integrable_sq
  have i2 : Integrable (fun z => 2 * h z * partialY h z) (cellMeasure L) := by
    have := (h2.integrable_mul hy).const_mul 2
    simpa [mul_assoc] using this
  filter_upwards [ae_integrable_slice i1, ae_integrable_slice i2] with q hq1 hq2 η
  have := ofReal_abs_le_lintegral_deriv (fun t => hasDerivAt_sq_sliceY hd q t) hq2 hq1 η
  simpa only [← enorm_sq_eq] using this

/-- The Tonelli form of Ladyzhenskaya's inequality. -/
theorem lintegral_four_le {L : ℝ} (hL : 1 ≤ L) {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    (hp : IsPeriodicQ L h) (h2 : MemLp h 2 (cellMeasure L))
    (hy : MemLp (partialY h) 2 (cellMeasure L)) :
    ∫⁻ z, ‖h z‖ₑ ^ 4 ∂cellMeasure L ≤
      (∫⁻ z, ‖2 * h z * partialY h z‖ₑ ∂cellMeasure L) *
        ((∫⁻ z, ‖h z‖ₑ ^ 2 ∂cellMeasure L) +
          ∫⁻ z, ‖2 * h z * partialX h z‖ₑ ∂cellMeasure L) := by
  have hL0 : 0 < L := by linarith
  have hc0 : Continuous h := hh.continuous
  have hcx : Continuous (partialX h) := continuous_partialX hh
  have hcy : Continuous (partialY h) := continuous_partialY hh
  have m1 : Measurable fun z : ℝ × ℝ => ‖h z‖ₑ ^ 2 := by fun_prop
  have m2 : Measurable fun z : ℝ × ℝ => ‖2 * h z * partialX h z‖ₑ := by fun_prop
  have m3 : Measurable fun z : ℝ × ℝ => ‖2 * h z * partialY h z‖ₑ := by fun_prop
  have m4 : Measurable fun z : ℝ × ℝ => ‖h z‖ₑ ^ 4 := by fun_prop
  set F : ℝ → ℝ≥0∞ := fun η => ENNReal.ofReal L⁻¹ * (∫⁻ s in Ioc 0 L, ‖h (s, η)‖ₑ ^ 2) +
      ∫⁻ s in Ioc 0 L, ‖2 * h (s, η) * partialX h (s, η)‖ₑ with hF
  set G : ℝ → ℝ≥0∞ := fun q => ∫⁻ t, ‖2 * h (q, t) * partialY h (q, t)‖ₑ with hG
  have mF1 : Measurable fun η : ℝ => ∫⁻ s in Ioc 0 L, ‖h (s, η)‖ₑ ^ 2 :=
    m1.lintegral_prod_left'
  have mF2 : Measurable fun η : ℝ => ∫⁻ s in Ioc 0 L, ‖2 * h (s, η) * partialX h (s, η)‖ₑ :=
    m2.lintegral_prod_left'
  have hFm : Measurable F := (mF1.const_mul _).add mF2
  have hGm : Measurable G := m3.lintegral_prod_right'
  have hstep : ∀ᵐ q ∂(volume.restrict (Ioc 0 L)), ∀ η, ‖h (q, η)‖ₑ ^ 4 ≤ G q * F η := by
    filter_upwards [ae_sq_le_line hh h2 hy] with q hq η
    calc ‖h (q, η)‖ₑ ^ 4 = ‖h (q, η)‖ₑ ^ 2 * ‖h (q, η)‖ₑ ^ 2 := by ring
      _ ≤ G q * F η := mul_le_mul' (hq η) (sq_le_circle hL0 hh hp q η)
  have hLinv : ENNReal.ofReal L⁻¹ ≤ 1 := ENNReal.ofReal_le_one.2 (inv_le_one_of_one_le₀ hL)
  calc ∫⁻ z, ‖h z‖ₑ ^ 4 ∂cellMeasure L
      = ∫⁻ q in Ioc 0 L, ∫⁻ η, ‖h (q, η)‖ₑ ^ 4 := lintegral_cell L m4
    _ ≤ ∫⁻ q in Ioc 0 L, G q * ∫⁻ η, F η := by
        refine lintegral_mono_ae ?_
        filter_upwards [hstep] with q hq
        rw [← lintegral_const_mul _ hFm]
        exact lintegral_mono fun η => hq η
    _ = (∫⁻ q in Ioc 0 L, G q) * ∫⁻ η, F η := lintegral_mul_const _ hGm
    _ = (∫⁻ z, ‖2 * h z * partialY h z‖ₑ ∂cellMeasure L) *
          (ENNReal.ofReal L⁻¹ * (∫⁻ z, ‖h z‖ₑ ^ 2 ∂cellMeasure L) +
            ∫⁻ z, ‖2 * h z * partialX h z‖ₑ ∂cellMeasure L) := by
        congr 1
        · exact (lintegral_cell L m3).symm
        · rw [hF, lintegral_add_left (mF1.const_mul _), lintegral_const_mul _ mF1,
            lintegral_cell_symm L m1, lintegral_cell_symm L m2]
    _ ≤ _ := by
        gcongr
        calc ENNReal.ofReal L⁻¹ * (∫⁻ z, ‖h z‖ₑ ^ 2 ∂cellMeasure L)
            ≤ 1 * (∫⁻ z, ‖h z‖ₑ ^ 2 ∂cellMeasure L) := by gcongr
          _ = _ := one_mul _

/-- `∫ |2 f g| ≤ 2 ‖f‖₂ ‖g‖₂` on the cell. -/
theorem lintegral_two_mul_le {L : ℝ} {f g : ℝ × ℝ → ℝ}
    (hf : AEStronglyMeasurable f (cellMeasure L)) (hg : AEStronglyMeasurable g (cellMeasure L)) :
    ∫⁻ z, ‖2 * f z * g z‖ₑ ∂cellMeasure L ≤
      2 * (eLpNorm f 2 (cellMeasure L) * eLpNorm g 2 (cellMeasure L)) := by
  have e : ∀ z, ‖2 * f z * g z‖ₑ = 2 * (‖f z‖ₑ * ‖g z‖ₑ) := fun z => by
    rw [enorm_mul, enorm_mul, mul_assoc]
    congr 1
    simp [Real.enorm_eq_ofReal_abs]
  simp_rw [e]
  rw [lintegral_const_mul' _ _ (by simp)]
  gcongr
  exact lintegral_enorm_mul_le hf hg

theorem lintegral_enorm_four_eq {μ : Measure (ℝ × ℝ)} (f : ℝ × ℝ → ℝ) :
    ∫⁻ z, ‖f z‖ₑ ^ 4 ∂μ = eLpNorm f 4 μ ^ 4 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := 4) (by norm_num)
  have e4 : ((4 : NNReal) : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
  simp only [e4, ENNReal.rpow_natCast, ENNReal.coe_ofNat] at h
  exact h.symm

/-- **Ladyzhenskaya's inequality on the cylinder** (B0151, tex 2310–2314):
`‖h‖₄² ≤ 2 ‖h‖₂ (‖∂_q h‖₂ + ‖∂_η h‖₂ + ‖h‖₂)` on one cell, for every period `L ≥ 1`. The
constant `2` does not depend on `L`. -/
theorem ladyzhenskaya {L : ℝ} (hL : 1 ≤ L) {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    (hp : IsPeriodicQ L h) (h2 : MemLp h 2 (cellMeasure L))
    (hy : MemLp (partialY h) 2 (cellMeasure L)) :
    eLpNorm h 4 (cellMeasure L) ^ 2 ≤
      2 * eLpNorm h 2 (cellMeasure L) *
        (eLpNorm (partialX h) 2 (cellMeasure L) + eLpNorm (partialY h) 2 (cellMeasure L) +
          eLpNorm h 2 (cellMeasure L)) := by
  set A := eLpNorm h 2 (cellMeasure L)
  set Bx := eLpNorm (partialX h) 2 (cellMeasure L)
  set By := eLpNorm (partialY h) 2 (cellMeasure L)
  set S := Bx + By + A
  have hcx : Continuous (partialX h) := continuous_partialX hh
  have ax : AEStronglyMeasurable (partialX h) (cellMeasure L) := hcx.aestronglyMeasurable
  have key := lintegral_four_le hL hh hp h2 hy
  rw [lintegral_enorm_four_eq, lintegral_enorm_sq_eq] at key
  have k1 := lintegral_two_mul_le h2.1 hy.1
  have k2 := lintegral_two_mul_le h2.1 ax
  have hBy : By ≤ S := le_trans le_add_self le_self_add
  have hA : A + 2 * Bx ≤ 2 * S := by
    calc A + 2 * Bx ≤ A + 2 * Bx + (2 * By + A) := le_self_add
      _ = 2 * S := by ring
  have h4 : (eLpNorm h 4 (cellMeasure L) ^ 2) ^ 2 ≤ (2 * A * S) ^ 2 := by
    calc (eLpNorm h 4 (cellMeasure L) ^ 2) ^ 2 = eLpNorm h 4 (cellMeasure L) ^ 4 := by ring
      _ ≤ (2 * (A * By)) * (A ^ 2 + 2 * (A * Bx)) :=
          key.trans (mul_le_mul' k1 (add_le_add le_rfl k2))
      _ = 2 * A ^ 2 * (By * (A + 2 * Bx)) := by ring
      _ ≤ 2 * A ^ 2 * (S * (2 * S)) := by gcongr
      _ = (2 * A * S) ^ 2 := by ring
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h4

end UnforcedLeray.B0151
