import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.Commute

/-!
# Part II-a, task `PartII-a:N02/4/4`, helper for `NzModeBounds`: decay of `S^α φ` on `s`-slices

Helper file for `NonzeroMode/ModeBounds.lean`. For `φ` with `NzDecay2 φ` (order `≤ 2` bounds) and a
fixed `s`, the slices `t ↦ (S^α φ)(s, t)` and their `t`-derivatives (for `α ∈ {0, 1}`) decay like
`exp(-κ|t|)`, with constants depending on `s`. These are the decay hypotheses of `NzEnergy1D`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

theorem nzmb_decay_smooth (φ : ℝ × ℝ → ℂ) (hφ : NzDecay2 φ) : ContDiff ℝ ∞ φ := by
  obtain ⟨h, _⟩ := hφ
  exact h

theorem nzmb_norm_one_le_prod :
    ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 ∧ ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by
  constructor <;> simp [Prod.norm_def]

/-- Operator-norm form of the order-`≤ 2` bounds of `NzDecay2`. -/
theorem nzmb_decay_norms (g : ℝ × ℝ → ℂ) (hg : NzDecay2 g) :
    ∃ κ C : ℝ, 0 < κ ∧ ∀ x : ℝ × ℝ,
      ‖g x‖ ≤ C * Real.exp (-κ * |x.2|) ∧
      ‖fderiv ℝ g x‖ ≤ C * Real.exp (-κ * |x.2|) ∧
      ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ C * Real.exp (-κ * |x.2|) := by
  obtain ⟨_, _, κ, C, hκ, hbd⟩ := hg
  refine ⟨κ, C, hκ, fun x => ⟨?_, ?_, ?_⟩⟩
  · have h := hbd x 0 (by norm_num)
    rwa [norm_iteratedFDeriv_zero] at h
  · have h := hbd x 1 (by norm_num)
    rwa [norm_iteratedFDeriv_one] at h
  · have h := hbd x 2 (by norm_num)
    have e1 : ‖iteratedFDeriv ℝ 1 (fderiv ℝ g) x‖ = ‖fderiv ℝ (fderiv ℝ g) x‖ :=
      norm_iteratedFDeriv_one (fderiv ℝ g)
    have e2 : ‖iteratedFDeriv ℝ 1 (fderiv ℝ g) x‖ = ‖iteratedFDeriv ℝ 2 g x‖ :=
      norm_iteratedFDeriv_fderiv
    rw [← e1, e2]
    exact h

/-- `‖S g x‖ ≤ |x.1| ‖∂g x‖`. -/
theorem nzmb_norm_nzS2_le (g : ℝ × ℝ → ℂ) (x : ℝ × ℝ) (M : ℝ) (h : ‖fderiv ℝ g x‖ ≤ M) :
    ‖nzS2 g x‖ ≤ |x.1| * M := by
  have h10 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := (nzmb_norm_one_le_prod).1
  have hM : 0 ≤ M := (norm_nonneg (fderiv ℝ g x)).trans h
  have h1 : ‖fderiv ℝ g x (1, 0)‖ ≤ M :=
    ((fderiv ℝ g x).le_opNorm _).trans
      ((mul_le_mul h h10 (norm_nonneg _) hM).trans (mul_one M).le)
  simp only [nzS2]
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

/-- `‖∂_η (S g) x‖ ≤ |x.1| ‖∂_η∂ g x‖`, using `∂_η (S g) = S (∂_η g)` and the symmetry of `∂²g`. -/
theorem nzmb_norm_fderiv_snd_nzS2_le (g : ℝ × ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (x : ℝ × ℝ)
    (M : ℝ) (h : ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M) :
    ‖fderiv ℝ (nzS2 g) x (0, 1)‖ ≤ |x.1| * M := by
  have h10 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := (nzmb_norm_one_le_prod).1
  have h01 : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := (nzmb_norm_one_le_prod).2
  have hM : 0 ≤ M := (norm_nonneg (fderiv ℝ (fderiv ℝ g) x)).trans h
  have hB : ‖fderiv ℝ (fderiv ℝ g) x (1, 0)‖ ≤ M :=
    ((fderiv ℝ (fderiv ℝ g) x).le_opNorm _).trans
      ((mul_le_mul h h10 (norm_nonneg _) hM).trans (mul_one M).le)
  have hW : ‖fderiv ℝ (fderiv ℝ g) x (1, 0) (0, 1)‖ ≤ M :=
    ((fderiv ℝ (fderiv ℝ g) x (1, 0)).le_opNorm _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) h01).trans hB)
  rw [nzmb_fderiv_nzS2 g hg x]
  simp only [nzS2]
  rw [norm_smul, Real.norm_eq_abs, nzmb_fderiv_eval g hg (0, 1) x (1, 0)]
  exact mul_le_mul_of_nonneg_left hW (abs_nonneg _)

/-- The `t`-derivative of a slice `t ↦ G (s, t)` is the `(0,1)`-derivative of `G`. -/
theorem nzmb_deriv_slice (G : ℝ × ℝ → ℂ) (hG : Differentiable ℝ G) (s t : ℝ) :
    deriv (fun τ : ℝ => G (s, τ)) t = fderiv ℝ G (s, t) (0, 1) := by
  have h1 : HasDerivAt (fun τ : ℝ => ((s, τ) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
  exact ((hG (s, t)).hasFDerivAt.comp_hasDerivAt t h1).deriv

/-- Slice decay of `φ` and `∂_η φ` at fixed `s`. -/
theorem nzmb_slice_decay0 (φ : ℝ × ℝ → ℂ) (hφ : NzDecay2 φ) (s : ℝ) :
    ∃ κ C : ℝ, 0 < κ ∧ ∀ t : ℝ,
      ‖φ (s, t)‖ ≤ C * Real.exp (-κ * |t|) ∧
      ‖deriv (fun τ : ℝ => φ (s, τ)) t‖ ≤ C * Real.exp (-κ * |t|) := by
  obtain ⟨κ, C, hκ, hb⟩ := nzmb_decay_norms φ hφ
  refine ⟨κ, C, hκ, fun t => ?_⟩
  obtain ⟨h0, h1, _⟩ := hb (s, t)
  have hdiff : Differentiable ℝ φ := (nzmb_decay_smooth φ hφ).differentiable (by simp)
  have h01 : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := (nzmb_norm_one_le_prod).2
  refine ⟨h0, ?_⟩
  rw [nzmb_deriv_slice φ hdiff s t]
  exact ((fderiv ℝ φ (s, t)).le_opNorm _).trans
    ((mul_le_of_le_one_right (norm_nonneg _) h01).trans h1)

/-- Slice decay of `S φ` and `∂_η S φ` at fixed `s` (constants `|s| C`). -/
theorem nzmb_slice_decay1 (φ : ℝ × ℝ → ℂ) (hφ : NzDecay2 φ) (s : ℝ) :
    ∃ κ C : ℝ, 0 < κ ∧ ∀ t : ℝ,
      ‖nzS2 φ (s, t)‖ ≤ (|s| * C) * Real.exp (-κ * |t|) ∧
      ‖deriv (fun τ : ℝ => nzS2 φ (s, τ)) t‖ ≤ (|s| * C) * Real.exp (-κ * |t|) := by
  obtain ⟨κ, C, hκ, hb⟩ := nzmb_decay_norms φ hφ
  refine ⟨κ, C, hκ, fun t => ?_⟩
  obtain ⟨_, h1, h2⟩ := hb (s, t)
  have hsm : ContDiff ℝ ∞ φ := nzmb_decay_smooth φ hφ
  have hdiff : Differentiable ℝ (nzS2 φ) :=
    (nzmb_contDiff_nzS2 φ hsm).differentiable (by simp)
  have e0 : ‖nzS2 φ (s, t)‖ ≤ |s| * (C * Real.exp (-κ * |t|)) :=
    nzmb_norm_nzS2_le φ (s, t) _ h1
  have e1 : ‖fderiv ℝ (nzS2 φ) (s, t) (0, 1)‖ ≤ |s| * (C * Real.exp (-κ * |t|)) :=
    nzmb_norm_fderiv_snd_nzS2_le φ hsm (s, t) _ h2
  refine ⟨?_, ?_⟩
  · rw [mul_assoc]
    exact e0
  · rw [nzmb_deriv_slice (nzS2 φ) hdiff s t, mul_assoc]
    exact e1

/-- Change of exponential rate and constant in a slice bound. -/
theorem nzmb_upgrade {x C₁ κ₁ κ D t : ℝ} (hκ : κ ≤ κ₁) (hD : |C₁| ≤ D)
    (hx : x ≤ C₁ * Real.exp (-κ₁ * |t|)) :
    x ≤ D * Real.exp (-κ * |t|) := by
  have e1 : Real.exp (-κ₁ * |t|) ≤ Real.exp (-κ * |t|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hκ) (abs_nonneg t)]
  calc x ≤ C₁ * Real.exp (-κ₁ * |t|) := hx
    _ ≤ |C₁| * Real.exp (-κ₁ * |t|) :=
        mul_le_mul_of_nonneg_right (le_abs_self C₁) (Real.exp_pos _).le
    _ ≤ |C₁| * Real.exp (-κ * |t|) := mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
    _ ≤ D * Real.exp (-κ * |t|) := mul_le_mul_of_nonneg_right hD (Real.exp_pos _).le

/-- Two slice decays combine into one (common rate `min κ₁ κ₂`, constant `|C₁| + |C₂|`). -/
theorem nzmb_slice_pair (G1 G2 : ℝ × ℝ → ℂ) (s κ1 C1 κ2 C2 : ℝ) (hκ1 : 0 < κ1) (hκ2 : 0 < κ2)
    (h1 : ∀ t : ℝ, ‖G1 (s, t)‖ ≤ C1 * Real.exp (-κ1 * |t|) ∧
      ‖deriv (fun τ : ℝ => G1 (s, τ)) t‖ ≤ C1 * Real.exp (-κ1 * |t|))
    (h2 : ∀ t : ℝ, ‖G2 (s, t)‖ ≤ C2 * Real.exp (-κ2 * |t|) ∧
      ‖deriv (fun τ : ℝ => G2 (s, τ)) t‖ ≤ C2 * Real.exp (-κ2 * |t|)) :
    ∃ κ C : ℝ, 0 < κ ∧ ∀ t : ℝ,
      ‖G1 (s, t)‖ ≤ C * Real.exp (-κ * |t|) ∧
      ‖deriv (fun τ : ℝ => G1 (s, τ)) t‖ ≤ C * Real.exp (-κ * |t|) ∧
      ‖G2 (s, t)‖ ≤ C * Real.exp (-κ * |t|) ∧
      ‖deriv (fun τ : ℝ => G2 (s, τ)) t‖ ≤ C * Real.exp (-κ * |t|) := by
  have hD1 : |C1| ≤ |C1| + |C2| := le_add_of_nonneg_right (abs_nonneg C2)
  have hD2 : |C2| ≤ |C1| + |C2| := le_add_of_nonneg_left (abs_nonneg C1)
  refine ⟨min κ1 κ2, |C1| + |C2|, lt_min hκ1 hκ2, fun t => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact nzmb_upgrade (min_le_left _ _) hD1 (h1 t).1
  · exact nzmb_upgrade (min_le_left _ _) hD1 (h1 t).2
  · exact nzmb_upgrade (min_le_right _ _) hD2 (h2 t).1
  · exact nzmb_upgrade (min_le_right _ _) hD2 (h2 t).2

/-- Slice decay of `(φ, ψ)` at fixed `s` (the `α = 0` case). -/
theorem nzmb_slice_pair0 (φ ψ : ℝ × ℝ → ℂ) (hφ : NzDecay2 φ) (hψ : NzDecay2 ψ) (s : ℝ) :
    ∃ κ C : ℝ, 0 < κ ∧ ∀ t : ℝ,
      ‖φ (s, t)‖ ≤ C * Real.exp (-κ * |t|) ∧
      ‖deriv (fun τ : ℝ => φ (s, τ)) t‖ ≤ C * Real.exp (-κ * |t|) ∧
      ‖ψ (s, t)‖ ≤ C * Real.exp (-κ * |t|) ∧
      ‖deriv (fun τ : ℝ => ψ (s, τ)) t‖ ≤ C * Real.exp (-κ * |t|) := by
  obtain ⟨κ1, C1, hκ1, h1⟩ := nzmb_slice_decay0 φ hφ s
  obtain ⟨κ2, C2, hκ2, h2⟩ := nzmb_slice_decay0 ψ hψ s
  exact nzmb_slice_pair φ ψ s κ1 C1 κ2 C2 hκ1 hκ2 h1 h2

/-- Slice decay of `(S φ, S ψ)` at fixed `s` (the `α = 1` case). -/
theorem nzmb_slice_pair1 (φ ψ : ℝ × ℝ → ℂ) (hφ : NzDecay2 φ) (hψ : NzDecay2 ψ) (s : ℝ) :
    ∃ κ C : ℝ, 0 < κ ∧ ∀ t : ℝ,
      ‖nzS2 φ (s, t)‖ ≤ C * Real.exp (-κ * |t|) ∧
      ‖deriv (fun τ : ℝ => nzS2 φ (s, τ)) t‖ ≤ C * Real.exp (-κ * |t|) ∧
      ‖nzS2 ψ (s, t)‖ ≤ C * Real.exp (-κ * |t|) ∧
      ‖deriv (fun τ : ℝ => nzS2 ψ (s, τ)) t‖ ≤ C * Real.exp (-κ * |t|) := by
  obtain ⟨κ1, C1, hκ1, h1⟩ := nzmb_slice_decay1 φ hφ s
  obtain ⟨κ2, C2, hκ2, h2⟩ := nzmb_slice_decay1 ψ hψ s
  exact nzmb_slice_pair (nzS2 φ) (nzS2 ψ) s κ1 (|s| * C1) κ2 (|s| * C2) hκ1 hκ2 h1 h2

end UnforcedLeray.Short.PartIIa
