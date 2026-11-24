import UnforcedLeray.Loc.L10Nonlinear
import UnforcedLeray.Loc.Hyp.HeatTailW2Continuous.Dilation
import UnforcedLeray.Loc.Hyp.HeatTailW2Continuous.Defect
import UnforcedLeray.Lib.HeatR3.Admissible

/-!
# H-HeatTail: the heat tail `K_loc` is continuous into `W^{2,∞}`

Proof of the hypothesis `HeatTailW2Continuous` of `Loc/L10Nonlinear.lean` (line 79):
`paper/main.tex` lines 446–461 (`K_loc`, `loc:eq:heat-correction`), blueprint units B0720 and
B0722 (the continuity of `𝓒(K_loc,·)` and `G_*` in `τ`, which the blueprint note on B0722 calls
implicit in the manuscript).

## The argument

Let `g` be the defect `d_loc = u₀ - u_dss` with its junk value at `0` removed
(`HeatTailW2Continuous/Defect.lean`): smooth, all derivatives bounded, and
`‖D^k g(x)‖‖x‖ ≤ C_k` far out for `k ≤ 4` (line 155). The heat scaling identity
(`Heat.average_dilate'`, `Lib/HeatR3/Admissible.lean`) turns the moving time `he^τ` into the
fixed time `h`:
`K_loc(τ) = e^{τ/2} [e^{he^τΔ} g](e^{τ/2}·) = e^{hΔ}[g_λ]`, `g_λ = λ g(λ·)`, `λ = e^{τ/2}`.
So `K_loc(τ') - K_loc(τ) = e^{hΔ}[g_{λ'} - g_λ]`, and the heat average of a smooth field with
bounded derivatives obeys the derivative bounds of the field (`L09.heatAverage_smooth_bounds`):
`‖D^k(K_loc(τ') - K_loc(τ))‖_∞ ≤ sup_x ‖λ'^{1+k} D^k g(λ'x) - λ^{1+k} D^k g(λx)‖`.
The right side tends to `0` as `λ' → λ` (`HeatTailW2Continuous/Dilation.lean`): far out both
terms are small by the decay of `D^k g`, near the origin `D^k g` is Lipschitz.

The proof does not use `τ ≤ 0`: the heat tail is continuous into `W^{2,∞}` at every phase.

Main declaration: `heatTailW2Continuous : HeatTailW2Continuous`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Hyp.HeatTail

open UnforcedLeray.Blueprint UnforcedLeray.L09

/-- The heat integrand of a bounded continuous field is integrable. -/
theorem heat_integrable_of_bounded {t : ℝ} (ht : 0 < t) {f : Space → Space} (hf : Continuous f)
    {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (x : Space) :
    Integrable (fun y : Space => Heat.kernel t y • f (x - y)) := by
  refine Integrable.mono' ((Heat.kernel_integrable ht).mul_const M)
    ((Kernels.heatKernel_smooth t).continuous.smul
      (hf.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [norm_smul, Real.norm_of_nonneg (Heat.kernel_nonneg ht y)]
  exact mul_le_mul_of_nonneg_left (hM _) (Heat.kernel_nonneg ht y)

/-- Linearity of the heat average on bounded continuous fields. -/
theorem average_sub_of_bounded {t : ℝ} (ht : 0 < t) {f₁ f₂ : Space → Space}
    (h₁ : Continuous f₁) (h₂ : Continuous f₂) {M₁ M₂ : ℝ} (hM₁ : ∀ x, ‖f₁ x‖ ≤ M₁)
    (hM₂ : ∀ x, ‖f₂ x‖ ≤ M₂) :
    Heat.average t f₁ - Heat.average t f₂ = Heat.average t (f₁ - f₂) := by
  funext y
  rw [Pi.sub_apply]
  unfold Heat.average
  rw [← integral_sub (heat_integrable_of_bounded ht h₁ hM₁ y)
    (heat_integrable_of_bounded ht h₂ hM₂ y)]
  congr 1
  funext z
  rw [Pi.sub_apply, smul_sub]

/-- `D^n(a g(a·) - b g(b·))(x) = a^{1+n} D^n g(ax) - b^{1+n} D^n g(bx)`. -/
theorem iteratedFDeriv_dilate_sub {g : SpatialField} (hg : ContDiff ℝ ∞ g) (a b : ℝ) (n : ℕ)
    (x : Space) :
    iteratedFDeriv ℝ n ((fun z => a • g (a • z)) - fun z => b • g (b • z)) x =
      (a * a ^ n) • iteratedFDeriv ℝ n g (a • x) -
        (b * b ^ n) • iteratedFDeriv ℝ n g (b • x) := by
  have hs : ∀ c : ℝ, ContDiff ℝ ∞ (fun z : Space => c • g (c • z)) := fun c =>
    (hg.comp (contDiff_const_smul c)).const_smul c
  rw [iteratedFDeriv_sub_apply ((hs a).contDiffAt.of_le (by exact_mod_cast le_top))
    ((hs b).contDiffAt.of_le (by exact_mod_cast le_top)),
    Kernels.iteratedFDeriv_comp_smul, Kernels.iteratedFDeriv_comp_smul]

/-- **H-HeatTail** (`paper/main.tex` lines 446–461; blueprint B0720, B0722). For every unstable
background `D` and every compact datum `u₀`, the heat tail `K_loc(τ) = H_h[u₀ - u_dss](τ)` is
continuous in `τ ≤ 0` into `W^{2,∞}`, uniformly in `y`: the hypothesis `HeatTailW2Continuous`
of `Loc/L10Nonlinear.lean`. -/
theorem heatTailW2Continuous : Blueprint.L10.HeatTailW2Continuous := by
  intro D hD u₀ hu τ _hτ ε hε
  have hh : 0 < D.h := hD.background.h_pos
  obtain ⟨g, hg, hgb, hgd, hK⟩ := exists_smooth_defect hD hu
  have hs : ∀ c : ℝ, ContDiff ℝ ∞ (fun z : Space => c • g (c • z)) := fun c =>
    (hg.comp (contDiff_const_smul c)).const_smul c
  obtain ⟨B₀, hB₀⟩ := hgb 0
  have hsb : ∀ c : ℝ, ∀ z : Space, ‖c • g (c • z)‖ ≤ |c| * B₀ := fun c z => by
    rw [norm_smul, Real.norm_eq_abs]
    have h := hB₀ (c • z)
    rw [norm_iteratedFDeriv_zero] at h
    exact mul_le_mul_of_nonneg_left h (abs_nonneg c)
  -- the heat scaling identity: `K_loc(σ) = e^{hΔ}[λ g(λ·)]`, `λ = e^{σ/2}`
  have hKd : ∀ σ : ℝ, heatTail D u₀ σ =
      Heat.average D.h (fun x => Real.exp (σ / 2) • g (Real.exp (σ / 2) • x)) := by
    intro σ
    rw [hK σ, Heat.average_dilate' (Real.exp_pos _) hh g]
    funext y
    rw [show Real.exp (σ / 2) ^ 2 * D.h = D.h * Real.exp σ by
      rw [sq, ← Real.exp_add, add_halves, mul_comm]]
  -- sup-norm continuity of the dilates of `g`, `Dg`, `D²g` at `λ₀ = e^{τ/2}`
  have hdil : ∀ n : ℕ, n ≤ 2 → ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, |a - Real.exp (τ / 2)| < δ →
      ∀ x : Space, ‖(a * a ^ n) • iteratedFDeriv ℝ n g (a • x) -
        (Real.exp (τ / 2) * Real.exp (τ / 2) ^ n) •
          iteratedFDeriv ℝ n g (Real.exp (τ / 2) • x)‖ ≤ ε := by
    intro n hn
    obtain ⟨M, hM⟩ := hgb (n + 1)
    obtain ⟨B, hB⟩ := hgb n
    obtain ⟨C, R, hCR⟩ := hgd n (by omega)
    exact dilation_continuous (F := iteratedFDeriv ℝ n g) (c := fun a : ℝ => a * a ^ n)
      (norm_iteratedFDeriv_sub_le hg n hM) hB hCR
      ((continuous_id.mul (continuous_pow n)).continuousAt) (Real.exp_pos _) hε
  obtain ⟨δ0, hδ0, h0⟩ := hdil 0 (by norm_num)
  obtain ⟨δ1, hδ1, h1⟩ := hdil 1 (by norm_num)
  obtain ⟨δ2, hδ2, h2⟩ := hdil 2 (by norm_num)
  have hcont : Continuous (fun t : ℝ => Real.exp (t / 2)) :=
    Real.continuous_exp.comp (continuous_id.div_const 2)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.mp hcont τ (min δ0 (min δ1 δ2)) (by positivity)
  refine ⟨δ, hδ, fun τ' _ hτ' y => ?_⟩
  have had : |Real.exp (τ' / 2) - Real.exp (τ / 2)| < min δ0 (min δ1 δ2) := by
    have h := hδ' τ' (by rwa [Real.dist_eq])
    rwa [Real.dist_eq] at h
  have ha0 : |Real.exp (τ' / 2) - Real.exp (τ / 2)| < δ0 := lt_of_lt_of_le had (min_le_left _ _)
  have ha1 : |Real.exp (τ' / 2) - Real.exp (τ / 2)| < δ1 :=
    lt_of_lt_of_le had ((min_le_right _ _).trans (min_le_left _ _))
  have ha2 : |Real.exp (τ' / 2) - Real.exp (τ / 2)| < δ2 :=
    lt_of_lt_of_le had ((min_le_right _ _).trans (min_le_right _ _))
  -- the difference `K_loc(τ') - K_loc(τ) = e^{hΔ}[g_{λ'} - g_λ]`
  set f : SpatialField := (fun z => Real.exp (τ' / 2) • g (Real.exp (τ' / 2) • z)) -
    fun z => Real.exp (τ / 2) • g (Real.exp (τ / 2) • z) with hf
  have hfs : ContDiff ℝ ∞ f := (hs _).sub (hs _)
  have hfD : ∀ (n : ℕ) (x : Space), iteratedFDeriv ℝ n f x =
      (Real.exp (τ' / 2) * Real.exp (τ' / 2) ^ n) •
          iteratedFDeriv ℝ n g (Real.exp (τ' / 2) • x) -
        (Real.exp (τ / 2) * Real.exp (τ / 2) ^ n) •
          iteratedFDeriv ℝ n g (Real.exp (τ / 2) • x) :=
    fun n x => iteratedFDeriv_dilate_sub hg _ _ n x
  have hfb : ∀ n : ℕ, ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ M := by
    intro n
    obtain ⟨M, hM⟩ := hgb n
    refine ⟨‖Real.exp (τ' / 2) * Real.exp (τ' / 2) ^ n‖ * M +
      ‖Real.exp (τ / 2) * Real.exp (τ / 2) ^ n‖ * M, fun x => ?_⟩
    rw [hfD]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul] <;>
      exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
  have hdiff : heatTail D u₀ τ' - heatTail D u₀ τ = Heat.average D.h f := by
    rw [hKd τ', hKd τ]
    exact average_sub_of_bounded hh (hs _).continuous (hs _).continuous (hsb _) (hsb _)
  obtain ⟨-, hbd⟩ := heatAverage_smooth_bounds hfs hfb hh
  have hτ'd : ContDiff ℝ ∞ (heatTail D u₀ τ') := hu.tail_smooth τ'
  have hτd : ContDiff ℝ ∞ (heatTail D u₀ τ) := hu.tail_smooth τ
  refine ⟨?_, ?_, ?_⟩
  · have hb := hbd 0 ε (fun x => by rw [hfD]; exact h0 _ ha0 x) y
    rw [norm_iteratedFDeriv_zero, ← hdiff] at hb
    exact hb
  · have hb := hbd 1 ε (fun x => by rw [hfD]; exact h1 _ ha1 x) y
    rw [norm_iteratedFDeriv_one, ← hdiff,
      fderiv_sub (hτ'd.differentiable (by simp) y) (hτd.differentiable (by simp) y)] at hb
    exact hb
  · have hb := hbd 2 ε (fun x => by rw [hfD]; exact h2 _ ha2 x) y
    rw [← hdiff, iteratedFDeriv_sub_apply (hτ'd.of_le (by simp)).contDiffAt
      (hτd.of_le (by simp)).contDiffAt] at hb
    exact hb

end UnforcedLeray.Hyp.HeatTail
