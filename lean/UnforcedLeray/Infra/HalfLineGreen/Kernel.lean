import UnforcedLeray.Infra.HalfLineGreen.Weighted
import UnforcedLeray.Infra.HalfLineGreen.Scalar
import UnforcedLeray.Infra.VolterraEvolution.Operator

/-!
# Kernels of the half-line Green operator; absolute convergence and the weighted bound

`paper/main.tex`, Section `sec:st18-329`, display `loc:eq:mixed-inverse` (lines 422-428) and
the bounds `loc:eq:past-bound`, `loc:eq:future-bound` (lines 408-414):
```
(R f)(τ) = ∫_{-∞}^τ K₋(τ,s) f(s) ds - ∫_τ^{τ₀} K₊(τ,s) f(s) ds,
‖K₋(τ,s)‖ ≤ C (1 + (τ-s)^{-1/2}) e^{β₋(τ-s)}  (s < τ),   ‖K₊(τ,s)‖ ≤ C e^{β₊(τ-s)}  (τ ≤ s).
```
In the manuscript `K₋(τ,s) = E(τ,s) Π₋(s)` and `K₊(τ,s) = E₊(τ,s) Π₊(s)` as maps `X → Z`.

`GreenKernel 𝕜 X Z` bundles the two operator kernels with these bounds and with strong
continuity in the integration variable `s` (`s ↦ K₋ τ s x` on `(-∞, τ)`, `s ↦ K₊ τ s x` on
`[τ, ∞)`), which makes all integrands continuous on the integration domains, hence Bochner
integrable once dominated.

Results, for `β₋ < β < β₊`, `τ ≤ τ₀` and a continuous `u : ℝ → X` with
`‖u s‖ ≤ M e^{βs}` for `s ≤ τ₀`:
* `integrableOn_Km_apply`, `intervalIntegrable_Kp_apply`: the two integrals converge
  absolutely;
* `norm_green_le`: `‖(R u)(τ)‖ ≤ C_β M e^{βτ}`, with the explicit constant
  `C_β = C (1/(β-β₋) + (1/(β-β₋))^{1/2} Γ(1/2) + 1/(β₊-β))` (`greenConst`), which equals
  `C (∫_0^∞ (1+r^{-1/2}) e^{-(β-β₋)r} dr + ∫_0^∞ e^{-(β₊-β)r} dr)` (`greenConst_eq_integral`)
  and does not depend on `τ₀`;
* `green_add`, `green_smul`: linearity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real

namespace UnforcedLeray.Infra.HalfLineGreen

open UnforcedLeray.Infra.VolterraEvolution (continuousOn_clm_apply)

/-- Data of the half-line Green operator (`paper/main.tex`, lines 406-428).

* `Km τ s : X →L Z` is the past kernel (`E(τ,s) Π₋(s)`), used for `s < τ`, with
  `‖Km τ s‖ ≤ C (1 + (τ-s)^{-1/2}) e^{βm (τ-s)}` and `s ↦ Km τ s x` continuous on `(-∞, τ)`;
* `Kp τ s : X →L Z` is the future kernel (`E₊(τ,s) Π₊(s)`), used for `τ ≤ s`, with
  `‖Kp τ s‖ ≤ C e^{βp (τ-s)}` and `s ↦ Kp τ s x` continuous on `[τ, ∞)`. -/
structure GreenKernel (𝕜 : Type*) [RCLike 𝕜] (X Z : Type*) [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] where
  /-- The past kernel `K₋(τ,s)`, `s < τ`. -/
  Km : ℝ → ℝ → X →L[𝕜] Z
  /-- The future kernel `K₊(τ,s)`, `τ ≤ s`. -/
  Kp : ℝ → ℝ → X →L[𝕜] Z
  /-- The constant of the kernel bounds. -/
  C : ℝ
  /-- The past rate `β₋`. -/
  βm : ℝ
  /-- The future rate `β₊`. -/
  βp : ℝ
  norm_Km_le : ∀ τ s, s < τ →
    ‖Km τ s‖ ≤ C * (1 + (τ - s) ^ (-(1 / 2 : ℝ))) * Real.exp (βm * (τ - s))
  norm_Kp_le : ∀ τ s, τ ≤ s → ‖Kp τ s‖ ≤ C * Real.exp (βp * (τ - s))
  continuousOn_Km : ∀ τ x, ContinuousOn (fun s => Km τ s x) (Iio τ)
  continuousOn_Kp : ∀ τ x, ContinuousOn (fun s => Kp τ s x) (Ici τ)

namespace GreenKernel

variable {𝕜 : Type*} [RCLike 𝕜] {X Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] (K : GreenKernel 𝕜 X Z)

theorem C_nonneg : 0 ≤ K.C := by
  have h := K.norm_Km_le 1 0 (by norm_num)
  have hpos : 0 < (1 + (1 - 0 : ℝ) ^ (-(1 / 2 : ℝ))) * Real.exp (K.βm * (1 - 0)) := by
    positivity
  by_contra hC'
  have hC : K.C < 0 := not_le.1 hC'
  have : K.C * (1 + (1 - 0 : ℝ) ^ (-(1 / 2 : ℝ))) * Real.exp (K.βm * (1 - 0)) < 0 := by
    rw [mul_assoc]
    exact mul_neg_of_neg_of_pos hC hpos
  linarith [norm_nonneg (K.Km 1 0)]

/-- The weighted pointwise bound for the past kernel: if `‖x‖ ≤ M e^{βs}` and `s < τ`, then
`‖K₋(τ,s) x‖ ≤ C M e^{βτ} (1 + (τ-s)^{-1/2}) e^{-(β-β₋)(τ-s)}`. -/
theorem norm_Km_apply_le {β M τ s : ℝ} (hs : s < τ) {x : X} (hx : ‖x‖ ≤ M * Real.exp (β * s)) :
    ‖K.Km τ s x‖ ≤ K.C * M * Real.exp (β * τ) * pastProfile (β - K.βm) (τ - s) := by
  have hb : 0 ≤ K.C * (1 + (τ - s) ^ (-(1 / 2 : ℝ))) * Real.exp (K.βm * (τ - s)) :=
    mul_nonneg (mul_nonneg K.C_nonneg (add_nonneg zero_le_one
      (rpow_nonneg (sub_pos.2 hs).le _))) (Real.exp_pos _).le
  calc ‖K.Km τ s x‖ ≤ ‖K.Km τ s‖ * ‖x‖ := (K.Km τ s).le_opNorm x
    _ ≤ (K.C * (1 + (τ - s) ^ (-(1 / 2 : ℝ))) * Real.exp (K.βm * (τ - s))) *
          (M * Real.exp (β * s)) :=
        mul_le_mul (K.norm_Km_le τ s hs) hx (norm_nonneg _) hb
    _ = K.C * M * Real.exp (β * τ) * pastProfile (β - K.βm) (τ - s) := by
        rw [pastProfile]
        have : Real.exp (K.βm * (τ - s)) * Real.exp (β * s)
            = Real.exp (β * τ) * Real.exp (-((β - K.βm) * (τ - s))) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        calc K.C * (1 + (τ - s) ^ (-(1 / 2 : ℝ))) * Real.exp (K.βm * (τ - s)) *
              (M * Real.exp (β * s))
            = K.C * M * (1 + (τ - s) ^ (-(1 / 2 : ℝ))) *
                (Real.exp (K.βm * (τ - s)) * Real.exp (β * s)) := by ring
          _ = _ := by rw [this]; ring

/-- The weighted pointwise bound for the future kernel: if `‖x‖ ≤ M e^{βs}` and `τ ≤ s`, then
`‖K₊(τ,s) x‖ ≤ C M e^{βτ} e^{-(β₊-β)(s-τ)}`. -/
theorem norm_Kp_apply_le {β M τ s : ℝ} (hs : τ ≤ s) {x : X} (hx : ‖x‖ ≤ M * Real.exp (β * s)) :
    ‖K.Kp τ s x‖ ≤ K.C * M * Real.exp (β * τ) * Real.exp (-((K.βp - β) * (s - τ))) := by
  have hb : 0 ≤ K.C * Real.exp (K.βp * (τ - s)) :=
    mul_nonneg K.C_nonneg (Real.exp_pos _).le
  calc ‖K.Kp τ s x‖ ≤ ‖K.Kp τ s‖ * ‖x‖ := (K.Kp τ s).le_opNorm x
    _ ≤ (K.C * Real.exp (K.βp * (τ - s))) * (M * Real.exp (β * s)) :=
        mul_le_mul (K.norm_Kp_le τ s hs) hx (norm_nonneg _) hb
    _ = K.C * M * (Real.exp (K.βp * (τ - s)) * Real.exp (β * s)) := by ring
    _ = K.C * M * Real.exp (β * τ) * Real.exp (-((K.βp - β) * (s - τ))) := by
        rw [mul_assoc (K.C * M), ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring

/-- The future integrand `s ↦ K₊(τ,s) e^{...}` decays: for `β < β₊` and `τ ≤ s`,
`‖K₊(τ,s) x‖ ≤ C M e^{βτ}` whenever `‖x‖ ≤ M e^{βs}`. -/
theorem norm_Kp_apply_le' {β M τ s : ℝ} (hβ : β < K.βp) (hs : τ ≤ s) {x : X}
    (hx : ‖x‖ ≤ M * Real.exp (β * s)) (hM : 0 ≤ M) :
    ‖K.Kp τ s x‖ ≤ K.C * M * Real.exp (β * τ) := by
  refine (K.norm_Kp_apply_le hs hx).trans ?_
  have h1 : Real.exp (-((K.βp - β) * (s - τ))) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg (sub_pos.2 hβ).le (sub_nonneg.2 hs)
  have h0 : 0 ≤ K.C * M * Real.exp (β * τ) :=
    mul_nonneg (mul_nonneg K.C_nonneg hM) (Real.exp_pos _).le
  calc K.C * M * Real.exp (β * τ) * Real.exp (-((K.βp - β) * (s - τ)))
      ≤ K.C * M * Real.exp (β * τ) * 1 := mul_le_mul_of_nonneg_left h1 h0
    _ = _ := mul_one _

/-- Local boundedness of the past kernel near any `s₀ < τ`. -/
theorem eventually_norm_Km_le (τ : ℝ) {s₀ : ℝ} (hs₀ : s₀ ∈ Iio τ) :
    ∃ B, ∀ᶠ s in 𝓝[Iio τ] s₀, ‖K.Km τ s‖ ≤ B := by
  set b : ℝ → ℝ := fun s => K.C * (1 + (τ - s) ^ (-(1 / 2 : ℝ))) * Real.exp (K.βm * (τ - s))
  have hb : ContinuousAt b s₀ := by
    have h1 : ContinuousAt (fun s : ℝ => τ - s) s₀ := continuousAt_const.sub continuousAt_id
    exact (continuousAt_const.mul (continuousAt_const.add
      (h1.rpow_const (Or.inl (sub_pos.2 hs₀).ne')))).mul
      (Real.continuous_exp.continuousAt.comp (continuousAt_const.mul h1))
  refine ⟨b s₀ + 1, ?_⟩
  have hlt : ∀ᶠ s in 𝓝 s₀, b s < b s₀ + 1 := hb.eventually (gt_mem_nhds (lt_add_one _))
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hlt] with s hs hlt'
  exact (K.norm_Km_le τ s hs).trans hlt'.le

/-- Local boundedness of the future kernel near any `s₀ ≥ τ`. -/
theorem eventually_norm_Kp_le (τ : ℝ) (s₀ : ℝ) :
    ∃ B, ∀ᶠ s in 𝓝[Ici τ] s₀, ‖K.Kp τ s‖ ≤ B := by
  set b : ℝ → ℝ := fun s => K.C * Real.exp (K.βp * (τ - s))
  have hb : ContinuousAt b s₀ :=
    continuousAt_const.mul (Real.continuous_exp.continuousAt.comp
      (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)))
  refine ⟨b s₀ + 1, ?_⟩
  have hlt : ∀ᶠ s in 𝓝 s₀, b s < b s₀ + 1 := hb.eventually (gt_mem_nhds (lt_add_one _))
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hlt] with s hs hlt'
  exact (K.norm_Kp_le τ s hs).trans hlt'.le

/-- The past integrand `s ↦ K₋(τ,s) u(s)` is continuous on `(-∞, τ)`. -/
theorem continuousOn_Km_apply {u : ℝ → X} (hu : Continuous u) (τ : ℝ) :
    ContinuousOn (fun s => K.Km τ s (u s)) (Iio τ) :=
  continuousOn_clm_apply (K.continuousOn_Km τ) (fun _ hs₀ => K.eventually_norm_Km_le τ hs₀)
    hu.continuousOn

/-- The future integrand `s ↦ K₊(τ,s) u(s)` is continuous on `[τ, ∞)`. -/
theorem continuousOn_Kp_apply {u : ℝ → X} (hu : Continuous u) (τ : ℝ) :
    ContinuousOn (fun s => K.Kp τ s (u s)) (Ici τ) :=
  continuousOn_clm_apply (K.continuousOn_Kp τ) (fun s₀ _ => K.eventually_norm_Kp_le τ s₀)
    hu.continuousOn

/-- **Absolute convergence of the past integral.** For `β₋ < β` and `‖u s‖ ≤ M e^{βs}`
(`s < τ`), `s ↦ K₋(τ,s) u(s)` is Bochner integrable on `(-∞, τ)`. -/
theorem integrableOn_Km_apply {β M τ : ℝ} (hβ : K.βm < β) {u : ℝ → X} (hu : Continuous u)
    (hM : ∀ s < τ, ‖u s‖ ≤ M * Real.exp (β * s)) :
    IntegrableOn (fun s => K.Km τ s (u s)) (Iio τ) := by
  have hg : IntegrableOn
      (fun s => K.C * M * Real.exp (β * τ) * pastProfile (β - K.βm) (τ - s)) (Iio τ) := by
    rw [integrableOn_Iio_iff]
    simp only [sub_sub_cancel]
    exact (integrableOn_pastProfile (sub_pos.2 hβ)).const_mul _
  refine Integrable.mono' hg
    ((K.continuousOn_Km_apply hu τ).aestronglyMeasurable measurableSet_Iio) ?_
  filter_upwards [ae_restrict_mem measurableSet_Iio] with s hs
  exact K.norm_Km_apply_le hs (hM s hs)

/-- **Absolute convergence of the future integral** on `[τ, τ₀]`. -/
theorem intervalIntegrable_Kp_apply {τ τ₀ : ℝ} (hτ : τ ≤ τ₀) {u : ℝ → X} (hu : Continuous u) :
    IntervalIntegrable (fun s => K.Kp τ s (u s)) volume τ τ₀ := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hτ]
  exact (K.continuousOn_Kp_apply hu τ).mono Icc_subset_Ici_self


section Green

variable [NormedSpace ℝ Z]

/-- The half-line Green operator on functions `u : ℝ → X` (only `u` on `(-∞, τ₀]` matters):
`green τ₀ u τ = ∫_{-∞}^τ K₋(τ,s) u(s) ds - ∫_τ^{τ₀} K₊(τ,s) u(s) ds`. -/
def green (τ₀ : ℝ) (u : ℝ → X) (τ : ℝ) : Z :=
  (∫ s in Iio τ, K.Km τ s (u s)) - ∫ s in τ..τ₀, K.Kp τ s (u s)

end Green

/-- The explicit constant `C_β = C (1/(β-β₋) + (1/(β-β₋))^{1/2} Γ(1/2) + 1/(β₊-β))`. It does
not depend on the terminal time `τ₀`. -/
def greenConst (β : ℝ) : ℝ :=
  K.C * (1 / (β - K.βm) + (1 / (β - K.βm)) ^ (1 / 2 : ℝ) * Gamma (1 / 2) + 1 / (K.βp - β))

/-- `C_β = C (∫_0^∞ (1 + r^{-1/2}) e^{-(β-β₋)r} dr + ∫_0^∞ e^{-(β₊-β)r} dr)`. -/
theorem greenConst_eq_integral {β : ℝ} (hβm : K.βm < β) (hβp : β < K.βp) :
    K.greenConst β = K.C * ((∫ r in Ioi (0 : ℝ), (1 + r ^ (-(1 / 2 : ℝ))) *
        Real.exp (-((β - K.βm) * r))) + ∫ r in Ioi (0 : ℝ), Real.exp (-((K.βp - β) * r))) := by
  have h1 := integral_pastProfile (sub_pos.2 hβm)
  have h2 := integral_exp_neg_mul_Ioi (sub_pos.2 hβp)
  simp only [pastProfile] at h1
  rw [h1, h2, greenConst]

theorem greenConst_nonneg {β : ℝ} (hβm : K.βm < β) (hβp : β < K.βp) : 0 ≤ K.greenConst β := by
  have h1 : 0 < β - K.βm := sub_pos.2 hβm
  have h2 : 0 < K.βp - β := sub_pos.2 hβp
  have : 0 ≤ 1 / (β - K.βm) + (1 / (β - K.βm)) ^ (1 / 2 : ℝ) * Gamma (1 / 2) + 1 / (K.βp - β) := by
    have := Gamma_pos_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
    positivity
  exact mul_nonneg K.C_nonneg this

section Green

variable [NormedSpace ℝ Z]

/-- **The weighted bound.** For `β₋ < β < β₊`, `τ ≤ τ₀`, and a continuous `u` with
`‖u s‖ ≤ M e^{βs}` for `s ≤ τ₀`: `‖(R u)(τ)‖ ≤ C_β M e^{βτ}`. (No measurability of `u` is
needed for the inequality itself; absolute convergence is `integrableOn_Km_apply`.) -/
theorem norm_green_le {β : ℝ} (hβm : K.βm < β) (hβp : β < K.βp) {τ₀ τ M : ℝ} (hτ : τ ≤ τ₀)
    {u : ℝ → X} (hM : ∀ s ≤ τ₀, ‖u s‖ ≤ M * Real.exp (β * s)) :
    ‖K.green τ₀ u τ‖ ≤ K.greenConst β * M * Real.exp (β * τ) := by
  have hM0 : 0 ≤ M :=
    (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).1 ((norm_nonneg _).trans (hM τ₀ le_rfl))
  have ha : 0 < β - K.βm := sub_pos.2 hβm
  have hb : 0 < K.βp - β := sub_pos.2 hβp
  set A := K.C * M * Real.exp (β * τ) with hA
  have hA0 : 0 ≤ A := mul_nonneg (mul_nonneg K.C_nonneg hM0) (Real.exp_pos _).le
  -- the past integral
  have h1 : ‖∫ s in Iio τ, K.Km τ s (u s)‖ ≤
      A * (1 / (β - K.βm) + (1 / (β - K.βm)) ^ (1 / 2 : ℝ) * Gamma (1 / 2)) := by
    have hg : IntegrableOn (fun s => A * pastProfile (β - K.βm) (τ - s)) (Iio τ) := by
      rw [integrableOn_Iio_iff]
      simp only [sub_sub_cancel]
      exact (integrableOn_pastProfile ha).const_mul _
    refine (norm_integral_le_of_norm_le hg ?_).trans (le_of_eq ?_)
    · filter_upwards [ae_restrict_mem measurableSet_Iio] with s hs
      exact K.norm_Km_apply_le hs (hM s (le_trans (le_of_lt hs) hτ))
    · rw [setIntegral_Iio_eq_Ioi]
      simp only [sub_sub_cancel]
      rw [integral_const_mul, integral_pastProfile ha]
  -- the future integral
  have h2 : ‖∫ s in τ..τ₀, K.Kp τ s (u s)‖ ≤ A * (1 / (K.βp - β)) := by
    have hg : IntervalIntegrable (fun s => A * Real.exp (-((K.βp - β) * (s - τ)))) volume τ τ₀ :=
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    refine (intervalIntegral.norm_integral_le_of_norm_le hτ ?_ hg).trans ?_
    · filter_upwards with s hs
      exact K.norm_Kp_apply_le hs.1.le (hM s hs.2)
    · rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (intervalIntegral_exp_neg_mul_sub_le hb hτ) hA0
  calc ‖K.green τ₀ u τ‖ ≤ ‖∫ s in Iio τ, K.Km τ s (u s)‖ + ‖∫ s in τ..τ₀, K.Kp τ s (u s)‖ :=
        norm_sub_le _ _
    _ ≤ A * (1 / (β - K.βm) + (1 / (β - K.βm)) ^ (1 / 2 : ℝ) * Gamma (1 / 2)) +
          A * (1 / (K.βp - β)) := add_le_add h1 h2
    _ = K.greenConst β * M * Real.exp (β * τ) := by
        rw [hA, greenConst]
        ring

/-- **Linearity: additivity.** -/
theorem green_add {β : ℝ} (hβm : K.βm < β) {τ₀ τ M N : ℝ} (hτ : τ ≤ τ₀) {u v : ℝ → X}
    (hu : Continuous u) (hv : Continuous v) (hM : ∀ s ≤ τ₀, ‖u s‖ ≤ M * Real.exp (β * s))
    (hN : ∀ s ≤ τ₀, ‖v s‖ ≤ N * Real.exp (β * s)) :
    K.green τ₀ (u + v) τ = K.green τ₀ u τ + K.green τ₀ v τ := by
  have iu := K.integrableOn_Km_apply hβm hu (fun s hs => hM s (le_trans hs.le hτ))
  have iv := K.integrableOn_Km_apply hβm hv (fun s hs => hN s (le_trans hs.le hτ))
  have ju := K.intervalIntegrable_Kp_apply hτ hu
  have jv := K.intervalIntegrable_Kp_apply hτ hv
  simp only [green, Pi.add_apply, map_add]
  rw [integral_add iu iv, intervalIntegral.integral_add ju jv]
  abel

/-- **Linearity: homogeneity** (no hypotheses needed). -/
theorem green_smul [SMulCommClass ℝ 𝕜 Z] (τ₀ : ℝ) (c : 𝕜) (u : ℝ → X) (τ : ℝ) :
    K.green τ₀ (c • u) τ = c • K.green τ₀ u τ := by
  simp only [green, Pi.smul_apply, map_smul]
  rw [integral_smul, intervalIntegral.integral_smul, smul_sub]

end Green

end GreenKernel

end UnforcedLeray.Infra.HalfLineGreen
