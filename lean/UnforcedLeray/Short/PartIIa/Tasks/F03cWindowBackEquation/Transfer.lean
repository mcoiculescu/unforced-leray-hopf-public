import UnforcedLeray.Short.PartIIa.Sub.F03

/-!
# Part II-a, task `PartII-a:F03/3` helper: scalar test transfer through the charts

Helper for `WindowBackEquation` (`Sub/F03.lean`). For a real smooth compactly supported test
`ψ` with `tsupport ψ ⊆ (τ₀-1, τ₀+1) × ℝ³`, the two integrals

* `∫ u · sLap (lapTest τ₀ ψ)` with `u = windowField χ τ₀ W c` (the left side of the weak
  Laplacian of the cutoff pull-back), and
* `∫ D · lapTest τ₀ ψ` for a field `D` (the right side, with `D = Σ_i D2 c i i`),

are rewritten by the charts `E(t,x) = (e^t, x)` and `D(t,y) = (t, e^{t/2} y)` of
`Units/B0424/Chart.lean` into integrals over `(τ, y)` with the weights of the window
(`e^{3t/2}`, `e^t`, `e^{-t/2}` cancel exactly on the support of `ψ`, where `χ = 1`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.WinBack

open UnforcedLeray.PhaseSpace UnforcedLeray.Parabolic UnforcedLeray.B0424

/-! ### Elementary identities -/

theorem expNeg_smul_expPos (t : ℝ) (y : Space) :
    Real.exp (-(t / 2)) • (Real.exp (t / 2) • y) = y := by
  rw [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]

theorem exp_scalar_identity (t : ℝ) :
    Real.exp (3 * t / 2) * Real.exp t * Real.exp (-(t / 2)) * Real.exp (-t) *
      Real.exp (-(t / 2)) ^ 2 = 1 := by
  have h3 : Real.exp (3 * t / 2) = Real.exp (t / 2) ^ 3 := (exp_half_pow_three t).symm
  have h1 : Real.exp t = Real.exp (t / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hn : Real.exp (-(t / 2)) = (Real.exp (t / 2))⁻¹ := Real.exp_neg _
  have hm : Real.exp (-t) = (Real.exp (t / 2))⁻¹ ^ 2 := by
    rw [Real.exp_neg, h1, inv_pow]
  have hp : Real.exp (t / 2) ≠ 0 := (Real.exp_pos _).ne'
  rw [h3, h1, hn, hm]
  field_simp

/-! ### Supports -/

theorem tsupport_dirD_subset {d : ℕ} (v : PS d) (f : PS d → ℝ) :
    tsupport (dirD v f) ⊆ tsupport f := by
  have h1 : dirD v f = (fun L : PS d →L[ℝ] ℝ => L v) ∘ fderiv ℝ f := rfl
  rw [h1]
  exact (tsupport_comp_subset (g := fun L : PS d →L[ℝ] ℝ => L v) rfl _).trans
    (tsupport_fderiv_subset ℝ)

theorem sD2_tsupport_subset {d : ℕ} (i j : Fin d) (f : PS d → ℝ) :
    tsupport (sD2 i j f) ⊆ tsupport f :=
  (tsupport_dirD_subset _ _).trans (tsupport_dirD_subset _ _)

theorem sLap_ne_mem_tsupport {ψ : PS 3 → ℝ} {q : PS 3} (h : sLap ψ q ≠ 0) :
    q ∈ tsupport ψ := by
  unfold sLap at h
  obtain ⟨i, hi⟩ : ∃ i, sD2 i i ψ q ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (Finset.sum_eq_zero fun i _ => hc i)
  exact sD2_tsupport_subset i i ψ (subset_tsupport _ (Function.mem_support.2 hi))

theorem abs_lt_of_sLap_ne {ψ : PS 3 → ℝ} {τ₀ : ℝ}
    (hψw : tsupport ψ ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) {t : ℝ} {y : Space}
    (h : sLap ψ (τ₀ + t, y) ≠ 0) : |t| < 1 := by
  have hm := hψw (sLap_ne_mem_tsupport h)
  have h1 : τ₀ + t ∈ Ioo (τ₀ - 1) (τ₀ + 1) := hm.1
  rw [abs_lt]
  constructor <;> linarith [h1.1, h1.2]

/-! ### Values of the charts on `(e^t, e^{t/2} y)` -/

theorem windowField_expDil (χ : ℝ → ℝ) (τ₀ : ℝ) (W : ℝ × Space → CVec3) (c : Fin 3)
    (t : ℝ) (y : Space) :
    windowField χ τ₀ W c (Real.exp t, Real.exp (t / 2) • y) =
      ((χ t * Real.exp (-(t / 2)) : ℝ) : ℂ) * W (τ₀ + t, y) c := by
  simp only [windowField, Real.exp_pos, ite_true, Real.log_exp, expNeg_smul_expPos]

theorem sLap_lapTest_expDil {ψ : PS 3 → ℝ} (hψ : IsSTTest ψ) {τ₀ : ℝ}
    (hψw : tsupport ψ ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) (t : ℝ) (y : Space) :
    sLap (lapTest τ₀ ψ : PS 3 → ℝ) (Real.exp t, Real.exp (t / 2) • y) =
      Real.exp (-t) * Real.exp (-(t / 2)) ^ 2 * sLap ψ (τ₀ + t, y) := by
  simp only [sLap_lapTest hψ hψw, Real.exp_pos, ite_true, Real.log_exp, neg_div,
    expNeg_smul_expPos]

theorem lapTest_expDil (τ₀ : ℝ) (ψ : PS 3 → ℝ) (t : ℝ) (y : Space) :
    lapTest τ₀ ψ (Real.exp t, Real.exp (t / 2) • y) = Real.exp (-t) * ψ (τ₀ + t, y) := by
  simp only [lapTest, Real.exp_pos, ite_true, Real.log_exp, neg_div, expNeg_smul_expPos]

/-! ### The transfer of `∫ u · sLap φ` (the left side) -/

theorem integral_windowField_sLap_t (χ : ℝ → ℝ) (hχ : WindowCutoff χ) (τ₀ : ℝ)
    (W : ℝ × Space → CVec3) (c : Fin 3) {ψ : PS 3 → ℝ} (hψ : IsSTTest ψ)
    (hψw : tsupport ψ ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) :
    ∫ X, windowField χ τ₀ W c X * ((sLap (lapTest τ₀ ψ) X : ℝ) : ℂ) =
      ∫ p : ℝ × Space, W (τ₀ + p.1, p.2) c * ((sLap ψ (τ₀ + p.1, p.2) : ℝ) : ℂ) := by
  have hzero : ∀ X ∉ Ioi (0 : ℝ) ×ˢ (univ : Set Space),
      windowField χ τ₀ W c X * ((sLap (lapTest τ₀ ψ) X : ℝ) : ℂ) = 0 := by
    intro X hX
    have hX1 : ¬ (0 < X.1) := fun h => hX ⟨h, trivial⟩
    simp only [windowField, if_neg hX1, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, integral_expChart]
  refine (integral_dilChart _).trans ?_
  congr 1
  funext p
  obtain ⟨t, y⟩ := p
  simp only [dilChart, expChart]
  rw [windowField_expDil, sLap_lapTest_expDil hψ hψw]
  by_cases h0 : sLap ψ (τ₀ + t, y) = 0
  · simp [h0]
  · have ht : |t| < 1 := abs_lt_of_sLap_ne hψw h0
    have hχ1 : χ t = 1 := hχ.one t ⟨(abs_lt.1 ht).1.le, (abs_lt.1 ht).2.le⟩
    have hc : ((Real.exp (3 * t / 2) * Real.exp t * Real.exp (-(t / 2)) * Real.exp (-t) *
        Real.exp (-(t / 2)) ^ 2 : ℝ) : ℂ) = 1 := by
      rw [exp_scalar_identity t]; simp
    rw [hχ1]
    simp only [Complex.real_smul]
    push_cast at hc ⊢
    linear_combination (W (τ₀ + t, y) c * (sLap ψ (τ₀ + t, y) : ℂ)) * hc

/-! ### The transfer of `∫ D · lapTest φ` (the right side) -/

theorem integral_D_lapTest_t (τ₀ : ℝ) (D : PS 3 → ℂ) {ψ : PS 3 → ℝ} (hψ : IsSTTest ψ)
    (hψw : tsupport ψ ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) :
    ∫ X, D X * ((lapTest τ₀ ψ X : ℝ) : ℂ) =
      ∫ p : ℝ × Space, Real.exp (3 * p.1 / 2) •
        (D (Real.exp p.1, Real.exp (p.1 / 2) • p.2) * ((ψ (τ₀ + p.1, p.2) : ℝ) : ℂ)) := by
  have hzero : ∀ X ∉ Ioi (0 : ℝ) ×ˢ (univ : Set Space),
      D X * ((lapTest τ₀ ψ X : ℝ) : ℂ) = 0 := by
    intro X hX
    have hX1 : ¬ (0 < X.1) := fun h => hX ⟨h, trivial⟩
    simp only [lapTest, if_neg hX1, Complex.ofReal_zero, mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, integral_expChart]
  refine (integral_dilChart _).trans ?_
  congr 1
  funext p
  obtain ⟨t, y⟩ := p
  simp only [dilChart, expChart]
  rw [lapTest_expDil]
  have he : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]; simp
  have hc : ((Real.exp t * Real.exp (-t) : ℝ) : ℂ) = 1 := by
    rw [he]; simp
  simp only [Complex.real_smul]
  push_cast at hc ⊢
  linear_combination Complex.exp (3 * (t : ℂ) / 2) * D (Real.exp t, Real.exp (t / 2) • y) *
    ((ψ (τ₀ + t, y) : ℝ) : ℂ) * hc

end UnforcedLeray.Short.PartIIa.WinBack
