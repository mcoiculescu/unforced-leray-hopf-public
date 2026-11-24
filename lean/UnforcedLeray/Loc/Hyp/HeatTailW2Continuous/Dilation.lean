import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# H-HeatTail helper: dilations of a decaying field are continuous in the sup norm

Helper of `Loc/Hyp/HeatTailW2Continuous.lean` (hypothesis `HeatTailW2Continuous` of
`Loc/L10Nonlinear.lean`; `paper/main.tex` lines 446–461, blueprint units B0720, B0722).

After the heat-scaling identity `K_loc(τ) = e^{hΔ}[λ d̃(λ·)]`, `λ = e^{τ/2}`, the continuity of
`τ ↦ K_loc(τ)` in `W^{2,∞}` reduces to the continuity of `λ ↦ λ^{1+k} (D^k d̃)(λ·)` in the sup
norm. The dilation `x ↦ λx` moves far points by `|λ - λ₀||x|`, so the sup-norm continuity needs
the field to be small at infinity; here it is `‖F x‖‖x‖ ≤ C` far out (`|D^k d_loc| ≤ C|x|^{-1-k}`,
`paper/main.tex` line 155). Near the origin a Lipschitz bound (from the next derivative) is
enough.

Main declarations: `norm_le_of_decay`, `dilation_continuous`, `norm_iteratedFDeriv_sub_le`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace UnforcedLeray.Hyp.HeatTail

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [NormedSpace ℝ E] [NormedSpace ℝ W] in
/-- Far-field smallness from `‖F x‖‖x‖ ≤ C` on `‖x‖ ≥ R`. -/
theorem norm_le_of_decay {F : E → W} {C R : ℝ} (hdec : ∀ x, R ≤ ‖x‖ → ‖F x‖ * ‖x‖ ≤ C)
    {η : ℝ} (hη : 0 < η) : ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ x, R₁ ≤ ‖x‖ → ‖F x‖ ≤ η := by
  have hq : 0 ≤ max C 0 / η := div_nonneg (le_max_right _ _) hη.le
  refine ⟨max R (max C 0 / η + 1), lt_of_lt_of_le (by linarith) (le_max_right _ _),
    fun x hx => ?_⟩
  have hxR : R ≤ ‖x‖ := (le_max_left _ _).trans hx
  have hx2 : max C 0 / η + 1 ≤ ‖x‖ := (le_max_right _ _).trans hx
  have h1 := hdec x hxR
  have h2 : η * (max C 0 / η + 1) = max C 0 + η := by
    rw [mul_add, mul_one, mul_div_cancel₀ _ hη.ne']
  by_contra hcon
  rw [not_le] at hcon
  have hpos : 0 < ‖x‖ := by linarith
  have h3 : η * ‖x‖ < ‖F x‖ * ‖x‖ := mul_lt_mul_of_pos_right hcon hpos
  have h4 : η * (max C 0 / η + 1) ≤ η * ‖x‖ := mul_le_mul_of_nonneg_left hx2 hη.le
  linarith [le_max_left C 0]

/-- **Sup-norm continuity of dilations.** If `F` is Lipschitz, bounded, and `‖F x‖‖x‖ ≤ C` far
out, and `c` is continuous at `a₀ > 0`, then `a ↦ c(a) F(a ·)` is continuous at `a₀` uniformly
on the whole space. -/
theorem dilation_continuous {F : E → W} {c : ℝ → ℝ} {L B C R a₀ : ℝ}
    (hlip : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (hB : ∀ x, ‖F x‖ ≤ B)
    (hdec : ∀ x, R ≤ ‖x‖ → ‖F x‖ * ‖x‖ ≤ C) (hc : ContinuousAt c a₀) (ha₀ : 0 < a₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, |a - a₀| < δ → ∀ x : E,
      ‖c a • F (a • x) - c a₀ • F (a₀ • x)‖ ≤ ε := by
  set B' : ℝ := max B 0 with hB'
  set L' : ℝ := max L 0 with hL'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have hL'0 : 0 ≤ L' := le_max_right _ _
  set η : ℝ := ε / (2 * (|c a₀| + 1)) with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨R₁, hR₁, hfar⟩ := norm_le_of_decay hdec (half_pos hη)
  set R₂ : ℝ := 2 * R₁ / a₀ with hR₂_def
  have hR₂ : 0 < R₂ := by positivity
  have hR₁₂ : a₀ / 2 * R₂ = R₁ := by
    rw [hR₂_def]; field_simp
  obtain ⟨δc, hδc, hcδ⟩ := Metric.continuousAt_iff.mp hc (ε / (2 * (B' + 1))) (by positivity)
  set δl : ℝ := η / ((L' + 1) * (R₂ + 1)) with hδl_def
  have hδl : 0 < δl := by positivity
  refine ⟨min (a₀ / 2) (min δc δl), by positivity, fun a ha x => ?_⟩
  have ha1 : |a - a₀| < a₀ / 2 := lt_of_lt_of_le ha (min_le_left _ _)
  have ha2 : |a - a₀| < δc := lt_of_lt_of_le ha ((min_le_right _ _).trans (min_le_left _ _))
  have ha3 : |a - a₀| < δl := lt_of_lt_of_le ha ((min_le_right _ _).trans (min_le_right _ _))
  have hapos : a₀ / 2 < a := by
    have := (abs_lt.mp ha1).1; linarith
  -- the difference of the two dilates
  have hFd : ‖F (a • x) - F (a₀ • x)‖ ≤ η := by
    by_cases hx : R₂ ≤ ‖x‖
    · have h1 : R₁ ≤ ‖a • x‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by linarith)]
        rw [← hR₁₂]
        exact mul_le_mul hapos.le hx hR₂.le (by linarith)
      have h2 : R₁ ≤ ‖a₀ • x‖ := by
        rw [norm_smul, Real.norm_of_nonneg ha₀.le]
        rw [← hR₁₂]
        exact mul_le_mul (by linarith) hx hR₂.le ha₀.le
      calc ‖F (a • x) - F (a₀ • x)‖ ≤ ‖F (a • x)‖ + ‖F (a₀ • x)‖ := norm_sub_le _ _
        _ ≤ η / 2 + η / 2 := add_le_add (hfar _ h1) (hfar _ h2)
        _ = η := by ring
    · rw [not_le] at hx
      have hxa : |a - a₀| * ‖x‖ ≤ δl * (R₂ + 1) :=
        mul_le_mul ha3.le (by linarith) (norm_nonneg _) hδl.le
      have hδl' : δl * (R₂ + 1) * (L' + 1) = η := by
        rw [hδl_def]; field_simp
      calc ‖F (a • x) - F (a₀ • x)‖ ≤ L * ‖a • x - a₀ • x‖ := hlip _ _
        _ ≤ L' * ‖a • x - a₀ • x‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ = L' * (|a - a₀| * ‖x‖) := by rw [← sub_smul, norm_smul, Real.norm_eq_abs]
        _ ≤ L' * (δl * (R₂ + 1)) := mul_le_mul_of_nonneg_left hxa hL'0
        _ ≤ (L' + 1) * (δl * (R₂ + 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = η := by rw [← hδl']; ring
  have hsplit : c a • F (a • x) - c a₀ • F (a₀ • x) =
      (c a - c a₀) • F (a • x) + c a₀ • (F (a • x) - F (a₀ • x)) := by
    rw [sub_smul, smul_sub]; abel
  have hca : |c a - c a₀| < ε / (2 * (B' + 1)) := by
    have := hcδ (show dist a a₀ < δc by rwa [Real.dist_eq])
    rwa [Real.dist_eq] at this
  have e1 : |c a - c a₀| * B' ≤ ε / 2 := by
    calc |c a - c a₀| * B' ≤ ε / (2 * (B' + 1)) * B' :=
          mul_le_mul_of_nonneg_right hca.le hB'0
      _ ≤ ε / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have e2 : |c a₀| * η ≤ ε / 2 := by
    rw [hη_def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    have := abs_nonneg (c a₀)
    nlinarith
  rw [hsplit]
  calc ‖(c a - c a₀) • F (a • x) + c a₀ • (F (a • x) - F (a₀ • x))‖
      ≤ ‖(c a - c a₀) • F (a • x)‖ + ‖c a₀ • (F (a • x) - F (a₀ • x))‖ := norm_add_le _ _
    _ = |c a - c a₀| * ‖F (a • x)‖ + |c a₀| * ‖F (a • x) - F (a₀ • x)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ |c a - c a₀| * B' + |c a₀| * η :=
        add_le_add (mul_le_mul_of_nonneg_left ((hB _).trans (le_max_left _ _)) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hFd (abs_nonneg _))
    _ ≤ ε / 2 + ε / 2 := add_le_add e1 e2
    _ = ε := by ring

/-- A bound on the `(n+1)`-st derivative makes the `n`-th derivative Lipschitz (mean value
theorem). -/
theorem norm_iteratedFDeriv_sub_le {g : E → W} (hg : ContDiff ℝ ∞ g) (n : ℕ) {M : ℝ}
    (hM : ∀ x, ‖iteratedFDeriv ℝ (n + 1) g x‖ ≤ M) (x y : E) :
    ‖iteratedFDeriv ℝ n g x - iteratedFDeriv ℝ n g y‖ ≤ M * ‖x - y‖ := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n g) :=
    hg.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hd z)
    (fun z _ => by rw [norm_fderiv_iteratedFDeriv]; exact hM z) convex_univ (mem_univ y)
    (mem_univ x)

end UnforcedLeray.Hyp.HeatTail
