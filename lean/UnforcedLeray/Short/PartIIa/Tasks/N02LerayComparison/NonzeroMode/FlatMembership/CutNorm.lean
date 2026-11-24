import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.CutoffApprox.Pt

/-!
# Part II-a, task `PartII-a:N02/4/3` helper: cut-off flat pieces at `ε = 0` and their bounds

For the `ε = 0` flat pieces `cgradC 0` and `streamC 0` (no `opK` term) and their `η`-cut-off versions
`nzcoCut ε Φ = χ(√ε η) Φ`, this file gives the coordinate formulas, the pointwise bounds of the
differences `cgradC 0 (χΦ) - cgradC 0 Φ` (and the stream analogue) by `√ε (|η|(‖∂_qΦ‖+‖∂_ηΦ‖) + B₁‖Φ‖)`,
the uniform bounds of the cut-off pieces, and `IsCTest` for the cut-off potential.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

lemma nzfm_cgrad0_eq (Φ : Profile → ℂ) (p : Profile) :
    cgradC 0 Φ p = !₂[pdQ Φ p, pdEta Φ p] := by
  simp [cgradC]

lemma nzfm_stream0_eq (ψ : Profile → ℂ) (p : Profile) :
    streamC 0 ψ p = !₂[-pdEta ψ p, pdQ ψ p] := by
  simp [streamC]

lemma nzfm_toLp2_sub (x y x' y' : ℂ) :
    (!₂[x, y] : MeridC) - !₂[x', y'] = !₂[x - x', y - y'] := by
  ext i
  fin_cases i <;> simp

lemma nzfm_cut_grad_eq {ε : ℝ} {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (p : Profile) :
    cgradC 0 (nzcoCut ε Φ) p = !₂[nzcoW ε p • pdQ Φ p,
      nzcoW ε p • pdEta Φ p + (deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε) • Φ p] := by
  rw [nzfm_cgrad0_eq, nzcoCut_pdQ ε hΦ, nzcoCut_pdEta ε hΦ]

lemma nzfm_cut_stream_eq {ε : ℝ} {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (p : Profile) :
    streamC 0 (nzcoCut ε Φ) p = !₂[-(nzcoW ε p • pdEta Φ p +
        (deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε) • Φ p),
      nzcoW ε p • pdQ Φ p] := by
  rw [nzfm_stream0_eq, nzcoCut_pdQ ε hΦ, nzcoCut_pdEta ε hΦ]

lemma nzfm_W_nonneg (ε : ℝ) (p : Profile) : 0 ≤ nzcoW ε p :=
  nzcoChi_nonneg _

lemma nzfm_W_le_one (ε : ℝ) (p : Profile) : nzcoW ε p ≤ 1 :=
  nzcoChi_le_one _

lemma nzfm_W_norm_le (ε : ℝ) (p : Profile) (a : ℂ) : ‖nzcoW ε p • a‖ ≤ ‖a‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (nzfm_W_nonneg ε p)]
  exact mul_le_of_le_one_left (norm_nonneg a) (nzfm_W_le_one ε p)

lemma nzfm_sqrt_le_one {ε : ℝ} (hε1 : ε ≤ 1) : Real.sqrt ε ≤ 1 := by
  calc Real.sqrt ε ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hε1
    _ = 1 := Real.sqrt_one

/-- The cut-off derivative coefficient `χ'(√ε η) √ε` is bounded by `B₁` when `ε ≤ 1`. -/
lemma nzfm_cut_coeff_le {ε : ℝ} {B1 : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hB1 : ∀ t : ℝ, |deriv nzcoChi t| ≤ B1) (η : ℝ) :
    |deriv nzcoChi (Real.sqrt ε * η) * Real.sqrt ε| ≤ B1 := by
  have hs : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  rw [abs_mul, abs_of_nonneg hs]
  have h1 := hB1 (Real.sqrt ε * η)
  have h2 := nzfm_sqrt_le_one hε1
  have h3 : 0 ≤ B1 := (abs_nonneg _).trans (hB1 0)
  calc |deriv nzcoChi (Real.sqrt ε * η)| * Real.sqrt ε ≤ B1 * 1 := mul_le_mul h1 h2 hs h3
    _ = B1 := mul_one B1

/-- Algebraic core: `‖W a - a‖ ≤ s |η| ‖a‖` when `1 - W ≤ s|η|`, `W ≤ 1`. -/
lemma nzfm_alg_comp1 {W s η : ℝ} (a : ℂ) (hW1 : W ≤ 1) (hw : 1 - W ≤ s * |η|) :
    ‖W • a - a‖ ≤ s * |η| * ‖a‖ := by
  have h : W • a - a = (W - 1) • a := by rw [sub_smul, one_smul]
  rw [h, norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith : W - 1 ≤ 0)]
  nlinarith [norm_nonneg a]

/-- Algebraic core: `‖W b + e v - b‖ ≤ s |η| ‖b‖ + B₁ s ‖v‖`. -/
lemma nzfm_alg_comp2 {W s η e B1 : ℝ} (b v : ℂ) (hW1 : W ≤ 1) (hw : 1 - W ≤ s * |η|)
    (he : |e| ≤ B1 * s) :
    ‖W • b + e • v - b‖ ≤ s * |η| * ‖b‖ + B1 * s * ‖v‖ := by
  have h : W • b + e • v - b = (W - 1) • b + e • v := by
    rw [sub_smul, one_smul]; abel
  rw [h]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonpos (by linarith : W - 1 ≤ 0)]
  nlinarith [norm_nonneg b, norm_nonneg v, mul_le_mul_of_nonneg_right he (norm_nonneg v),
    mul_le_mul_of_nonneg_right hw (norm_nonneg b)]

/-- Difference of the gradients of the cut-off potential and of the potential, pointwise. -/
lemma nzfm_cut_grad_diff {ε : ℝ} {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hε : 0 ≤ ε)
    {B1 : ℝ} (hB1 : ∀ t : ℝ, |deriv nzcoChi t| ≤ B1) (p : Profile) :
    ‖cgradC 0 (nzcoCut ε Φ) p - cgradC 0 Φ p‖ ≤
      Real.sqrt ε * (|p.2.2| * (‖pdQ Φ p‖ + ‖pdEta Φ p‖) + B1 * ‖Φ p‖) := by
  rw [nzfm_cut_grad_eq hΦ, nzfm_cgrad0_eq, nzfm_toLp2_sub]
  refine (nzco_norm_two _ _).trans ?_
  have hs : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hw : 1 - nzcoW ε p ≤ Real.sqrt ε * |p.2.2| := by
    have h := nzcoChi_one_sub_le (Real.sqrt ε * p.2.2)
    rw [abs_mul, abs_of_nonneg hs] at h
    exact h
  have he : |deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε| ≤ B1 * Real.sqrt ε := by
    rw [abs_mul, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_right (hB1 _) hs
  have h1 := nzfm_alg_comp1 (W := nzcoW ε p) (s := Real.sqrt ε) (η := p.2.2) (pdQ Φ p)
    (nzfm_W_le_one ε p) hw
  have h2 := nzfm_alg_comp2 (W := nzcoW ε p) (s := Real.sqrt ε) (η := p.2.2)
    (e := deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε) (B1 := B1) (pdEta Φ p) (Φ p)
    (nzfm_W_le_one ε p) hw he
  have key : Real.sqrt ε * |p.2.2| * ‖pdQ Φ p‖ + (Real.sqrt ε * |p.2.2| * ‖pdEta Φ p‖ +
      B1 * Real.sqrt ε * ‖Φ p‖) =
      Real.sqrt ε * (|p.2.2| * (‖pdQ Φ p‖ + ‖pdEta Φ p‖) + B1 * ‖Φ p‖) := by ring
  linarith [h1, h2, key]

/-- Difference of the stream fields of the cut-off potential and of the potential, pointwise. -/
lemma nzfm_cut_stream_diff {ε : ℝ} {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hε : 0 ≤ ε)
    {B1 : ℝ} (hB1 : ∀ t : ℝ, |deriv nzcoChi t| ≤ B1) (p : Profile) :
    ‖streamC 0 (nzcoCut ε Φ) p - streamC 0 Φ p‖ ≤
      Real.sqrt ε * (|p.2.2| * (‖pdQ Φ p‖ + ‖pdEta Φ p‖) + B1 * ‖Φ p‖) := by
  rw [nzfm_cut_stream_eq hΦ, nzfm_stream0_eq, nzfm_toLp2_sub]
  have hs : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hx : -(nzcoW ε p • pdEta Φ p + (deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε) • Φ p) -
      -pdEta Φ p = -(nzcoW ε p • pdEta Φ p + (deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε) • Φ p
        - pdEta Φ p) := by
    abel
  rw [hx]
  refine (nzco_norm_two _ _).trans ?_
  rw [norm_neg]
  have hw : 1 - nzcoW ε p ≤ Real.sqrt ε * |p.2.2| := by
    have h := nzcoChi_one_sub_le (Real.sqrt ε * p.2.2)
    rw [abs_mul, abs_of_nonneg hs] at h
    exact h
  have he : |deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε| ≤ B1 * Real.sqrt ε := by
    rw [abs_mul, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_right (hB1 _) hs
  have h1 := nzfm_alg_comp1 (W := nzcoW ε p) (s := Real.sqrt ε) (η := p.2.2) (pdQ Φ p)
    (nzfm_W_le_one ε p) hw
  have h2 := nzfm_alg_comp2 (W := nzcoW ε p) (s := Real.sqrt ε) (η := p.2.2)
    (e := deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε) (B1 := B1) (pdEta Φ p) (Φ p)
    (nzfm_W_le_one ε p) hw he
  have key : Real.sqrt ε * |p.2.2| * ‖pdQ Φ p‖ + (Real.sqrt ε * |p.2.2| * ‖pdEta Φ p‖ +
      B1 * Real.sqrt ε * ‖Φ p‖) =
      Real.sqrt ε * (|p.2.2| * (‖pdQ Φ p‖ + ‖pdEta Φ p‖) + B1 * ‖Φ p‖) := by ring
  linarith [h1, h2, key]

/-- Uniform bound: `‖cgradC 0 (χΦ)‖ ≤ ‖∂_qΦ‖ + ‖∂_ηΦ‖ + B₁‖Φ‖` for `0 ≤ ε ≤ 1`. -/
lemma nzfm_cut_grad_norm {ε : ℝ} {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) {B1 : ℝ} (hB1 : ∀ t : ℝ, |deriv nzcoChi t| ≤ B1) (p : Profile) :
    ‖cgradC 0 (nzcoCut ε Φ) p‖ ≤ ‖pdQ Φ p‖ + ‖pdEta Φ p‖ + B1 * ‖Φ p‖ := by
  rw [nzfm_cut_grad_eq hΦ]
  refine (nzco_norm_two _ _).trans ?_
  have hA := nzfm_W_norm_le ε p (pdQ Φ p)
  have hC : ‖nzcoW ε p • pdEta Φ p + (deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε) • Φ p‖ ≤
      ‖pdEta Φ p‖ + B1 * ‖Φ p‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (nzfm_W_nonneg ε p)]
    nlinarith [mul_le_of_le_one_left (norm_nonneg (pdEta Φ p)) (nzfm_W_le_one ε p),
      mul_le_mul_of_nonneg_right (nzfm_cut_coeff_le hε hε1 hB1 p.2.2) (norm_nonneg (Φ p))]
  linarith

/-- Uniform bound: `‖streamC 0 (χΦ)‖ ≤ ‖∂_qΦ‖ + ‖∂_ηΦ‖ + B₁‖Φ‖` for `0 ≤ ε ≤ 1`. -/
lemma nzfm_cut_stream_norm {ε : ℝ} {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) {B1 : ℝ} (hB1 : ∀ t : ℝ, |deriv nzcoChi t| ≤ B1) (p : Profile) :
    ‖streamC 0 (nzcoCut ε Φ) p‖ ≤ ‖pdQ Φ p‖ + ‖pdEta Φ p‖ + B1 * ‖Φ p‖ := by
  rw [nzfm_cut_stream_eq hΦ]
  refine (nzco_norm_two _ _).trans ?_
  rw [norm_neg]
  have hA := nzfm_W_norm_le ε p (pdQ Φ p)
  have hC : ‖nzcoW ε p • pdEta Φ p + (deriv nzcoChi (Real.sqrt ε * p.2.2) * Real.sqrt ε) • Φ p‖ ≤
      ‖pdEta Φ p‖ + B1 * ‖Φ p‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (nzfm_W_nonneg ε p)]
    nlinarith [mul_le_of_le_one_left (norm_nonneg (pdEta Φ p)) (nzfm_W_le_one ε p),
      mul_le_mul_of_nonneg_right (nzfm_cut_coeff_le hε hε1 hB1 p.2.2) (norm_nonneg (Φ p))]
  linarith

/-- The cut-off potential `χ(√ε η) φ` is a complex band test for `ε > 0`, with `|η| ≤ 2/√ε`. -/
lemma nzfm_cut_isCTest {c ε s0 s1 : ℝ} {φ : Profile → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hper : QPeriodic c φ) (hs0 : 0 < s0)
    (hsupp : ∀ p : Profile, φ p ≠ 0 → p.1 ∈ Icc s0 s1) (hε : 0 < ε) :
    IsCTest c (nzcoCut ε φ) := by
  refine ⟨nzcoCut_contDiff ε hφ, nzcoCut_periodic c ε hper, ⟨s0, s1, 2 / Real.sqrt ε, hs0, ?_⟩⟩
  intro p hp
  have hφp : φ p ≠ 0 := by
    intro h0
    apply hp
    simp [nzcoCut, h0]
  have hW : nzcoW ε p ≠ 0 := by
    intro h0
    apply hp
    simp [nzcoCut, h0]
  refine ⟨hsupp p hφp, ?_⟩
  have hsq : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have h2 := nzcoW_abs_lt hW
  rw [abs_mul, abs_of_pos hsq] at h2
  rw [le_div_iff₀ hsq]
  linarith

end UnforcedLeray.Short.PartIIa
