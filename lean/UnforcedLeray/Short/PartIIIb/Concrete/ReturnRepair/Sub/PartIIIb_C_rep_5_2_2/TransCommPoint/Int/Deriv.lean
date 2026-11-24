import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Int.Bound
import UnforcedLeray.Short.PartIIIa.Tasks16.Dominated

/-!
# Uniform pointwise bounds on `W_μ`, `X₀` and their derivatives

Source `the November 2 reference manuscript` 3604-3623, 4171, 4181-4192.
For a separated source of finite `L²_τL²` moment, at every phase `τ` and every receiver `y` with
`ϱ y > r_o`, with `D = ϱ y - r_o`: `|D^j W_m| , |D^j X₀| ≤ C D^{-5/2-j}`, `C` independent of `τ, y`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem tcd_wD_bound (j : ℕ) : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (ν : ℝ) (m : ℂ), 0 < ν → -(1 / 4) < m.re →
    ∀ (rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), 0 ≤ rOut → 0 < P →
      IIIa.IsSepSource P rOut T → SepMoment P T → ∀ (τ : ℝ) (y : Space), rOut < ϱ y →
        IIIa.wDerivNorm ν m T j τ y ≤ ENNReal.ofReal C0 *
          (ENNReal.ofReal ((ϱ y - rOut) ^ (-(5 / 2 : ℝ) - j)) * tcKc j * tcMph P T) := by
  obtain ⟨C0, hC0, hdom⟩ := IIIa.sepWDominated IIIa.sepKernelBounds j
  refine ⟨C0, hC0, ?_⟩
  intro ν m hν hm rOut P T hr hP hT hM τ y hy
  have hD : 0 < ϱ y - rOut := by linarith
  have hb : (1 : ℝ) ≤ 2 * m.re + 2 := by linarith
  have hfin : IIIa.sepDom (2 * m.re + 2) 0 (ϱ y - rOut) (IIIa.srcNorm T) τ y < ⊤ := by
    refine lt_of_le_of_lt (tcd_sepDom_bound hP hb hT 0 hD τ y) ?_
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (tcKc_ne_top 0).lt_top)
      (tcMph_ne_top hP hM).lt_top
  have h1 := hdom ν hν m hm rOut (ϱ y) P hr (by linarith) hP T hT τ y le_rfl hfin
  refine h1.trans ?_
  exact mul_le_mul' le_rfl (tcd_sepDom_bound hP hb hT j hD τ y)

theorem tcd_to_real {E : Type*} [NormedAddCommGroup E] {v : E} {a : ℝ≥0∞} (ha : a ≠ ⊤)
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : ‖v‖ₑ ≤ ENNReal.ofReal c * (ENNReal.ofReal d * a)) : ‖v‖ ≤ c * d * a.toReal := by
  have e : ENNReal.ofReal c * (ENNReal.ofReal d * a) = ENNReal.ofReal (c * d * a.toReal) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal ha]
    rw [← ENNReal.ofReal_mul hd, ← ENNReal.ofReal_mul hc, mul_assoc]
  rw [e, ← ofReal_norm] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity [ENNReal.toReal_nonneg (a := a)])).1 h

/-- **Uniform bounds of `W_μ`, `X₀` and their derivatives of order `≤ 2`.** -/
theorem tcd_X0_bound {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (y : Space), rOut < ϱ y →
      (∀ j : ℕ, j ≤ 2 → ‖iteratedFDeriv ℝ j (sepX0 ν μ T τ) y‖ ≤
          C * (ϱ y - rOut) ^ (-(5 / 2 : ℝ) - j)) ∧
      ‖IIIa.sepW ν (μ : ℂ) T y τ‖ ≤ C * (ϱ y - rOut) ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨C0, hC00, h0⟩ := tcd_wD_bound 0
  obtain ⟨C1, hC10, h1⟩ := tcd_wD_bound 1
  obtain ⟨C2, hC20, h2⟩ := tcd_wD_bound 2
  have hQ : ∀ j : ℕ, tcKc j * tcMph P T ≠ ⊤ := fun j =>
    ENNReal.mul_ne_top (tcKc_ne_top j) (tcMph_ne_top hP hM)
  set Q : ℕ → ℝ := fun j => (tcKc j * tcMph P T).toReal with hQdef
  have hQ0 : ∀ j, 0 ≤ Q j := fun j => ENNReal.toReal_nonneg
  have hm1 : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hm2 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  refine ⟨(‖reL‖ * 2 + 1) * (C0 * Q 0 + C1 * Q 1 + C2 * Q 2), by positivity, ?_⟩
  intro τ y hy
  have hD : 0 < ϱ y - rOut := by linarith
  have hU : IsOpen {y : Space | rOut < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  have hWa : ContDiffOn ℝ 2 (fun z => IIIa.sepW ν (μ : ℂ) T z τ) {y : Space | rOut < ϱ y} :=
    contDiffOn_pi.2 (fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) rOut P T hν
      hm1 hr hP hT hM τ i)
  have hWb : ContDiffOn ℝ 2 (fun z => IIIa.sepW ν ((μ : ℂ) + 1) T z τ)
      {y : Space | rOut < ϱ y} :=
    contDiffOn_pi.2 (fun i => sepWSmoothOn_of IIIa.sepKernelBounds ν ((μ : ℂ) + 1) rOut P T hν
      hm2 hr hP hT hM τ i)
  -- real bounds for `W`
  have wb : ∀ (m : ℂ), -(1 / 4) < m.re → ∀ (j : ℕ) (C : ℝ), 0 ≤ C →
      (IIIa.wDerivNorm ν m T j τ y ≤ ENNReal.ofReal C *
          (ENNReal.ofReal ((ϱ y - rOut) ^ (-(5 / 2 : ℝ) - j)) * tcKc j * tcMph P T)) →
      ‖iteratedFDeriv ℝ j (fun y' => IIIa.sepW ν m T y' τ) y‖ ≤
        C * (ϱ y - rOut) ^ (-(5 / 2 : ℝ) - j) * Q j := by
    intro m _ j C hC hb
    refine tcd_to_real (hQ j) hC (Real.rpow_nonneg hD.le _) ?_
    unfold IIIa.wDerivNorm at hb
    simpa only [mul_assoc] using hb
  have b0a := wb (μ : ℂ) hm1 0 C0 hC00 (h0 ν _ hν hm1 rOut P T hr hP hT hM τ y hy)
  have b0b := wb ((μ : ℂ) + 1) hm2 0 C0 hC00 (h0 ν _ hν hm2 rOut P T hr hP hT hM τ y hy)
  have b1a := wb (μ : ℂ) hm1 1 C1 hC10 (h1 ν _ hν hm1 rOut P T hr hP hT hM τ y hy)
  have b1b := wb ((μ : ℂ) + 1) hm2 1 C1 hC10 (h1 ν _ hν hm2 rOut P T hr hP hT hM τ y hy)
  have b2a := wb (μ : ℂ) hm1 2 C2 hC20 (h2 ν _ hν hm1 rOut P T hr hP hT hM τ y hy)
  have b2b := wb ((μ : ℂ) + 1) hm2 2 C2 hC20 (h2 ν _ hν hm2 rOut P T hr hP hT hM τ y hy)
  have hder : ∀ j : ℕ, j ≤ 2 → ‖iteratedFDeriv ℝ j (sepX0 ν μ T τ) y‖ ≤
      ‖reL‖ * (‖iteratedFDeriv ℝ j (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ) y‖ +
        ‖iteratedFDeriv ℝ j (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) T y' τ) y‖) := by
    intro j hj
    have := iteratedFDeriv_reL_le hU hWa hWb hj (show y ∈ {y : Space | rOut < ϱ y} from hy)
    rw [← sepX0_eq_reL] at this
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
      ← ENNReal.ofReal_mul (norm_nonneg _)] at this
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
  have hCnn : 0 ≤ C0 * Q 0 + C1 * Q 1 + C2 * Q 2 := by
    have := hQ0 0; have := hQ0 1; have := hQ0 2; positivity
  have hr0 : 0 ≤ ‖reL‖ := norm_nonneg _
  have hp : ∀ j : ℕ, 0 ≤ (ϱ y - rOut) ^ (-(5 / 2 : ℝ) - j) := fun j => Real.rpow_nonneg hD.le _
  refine ⟨?_, ?_⟩
  · intro j hj
    have hjc : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hjc with rfl | rfl | rfl
    · refine (hder 0 hj).trans ?_
      have := hp 0
      have q0 := hQ0 0; have q1 := hQ0 1; have q2 := hQ0 2
      simp only [Nat.cast_zero, sub_zero] at b0a b0b ⊢
      nlinarith [mul_nonneg hC00 q0, mul_nonneg hC10 q1, mul_nonneg hC20 q2, mul_nonneg this hr0,
        mul_nonneg this (mul_nonneg hC00 q0)]
    · refine (hder 1 hj).trans ?_
      have := hp 1
      have q0 := hQ0 0; have q1 := hQ0 1; have q2 := hQ0 2
      nlinarith [mul_nonneg hC00 q0, mul_nonneg hC10 q1, mul_nonneg hC20 q2, mul_nonneg this hr0,
        mul_nonneg this (mul_nonneg hC10 q1)]
    · refine (hder 2 hj).trans ?_
      have := hp 2
      have q0 := hQ0 0; have q1 := hQ0 1; have q2 := hQ0 2
      nlinarith [mul_nonneg hC00 q0, mul_nonneg hC10 q1, mul_nonneg hC20 q2, mul_nonneg this hr0,
        mul_nonneg this (mul_nonneg hC20 q2)]
  · have e0 : ‖iteratedFDeriv ℝ 0 (fun y' => IIIa.sepW ν (μ : ℂ) T y' τ) y‖ =
        ‖IIIa.sepW ν (μ : ℂ) T y τ‖ := norm_iteratedFDeriv_zero
    rw [e0] at b0a
    simp only [Nat.cast_zero, sub_zero] at b0a
    have := hp 0
    simp only [Nat.cast_zero, sub_zero] at this
    have q0 := hQ0 0; have q1 := hQ0 1; have q2 := hQ0 2
    nlinarith [mul_nonneg hC00 q0, mul_nonneg hC10 q1, mul_nonneg hC20 q2, mul_nonneg this hr0,
      mul_nonneg this (mul_nonneg hC00 q0)]

end UnforcedLeray.Short.PartIIIb.Concrete

end
