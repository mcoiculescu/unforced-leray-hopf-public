import UnforcedLeray.Short.PartI.Sub.PartI_T21_1
import UnforcedLeray.Short.PartI.Sub.PartI_T20
import UnforcedLeray.Short.PartI.Sub.PartI_T22_1
import UnforcedLeray.Short.PartI.Tasks.TrainClass.BUCMeanStreamSmooth
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound.HmeanC2
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound.HmeanLap

/-!
# `PartI:T21/1/2` Helper: 1D improper integral representation and age derivatives for the zero mode

Source of record: `the November 2 reference manuscript`, lines 504-513.

Provides:
1. Exponential tail integrability and integral evaluation on `Ioi r` (`expTail_Ioi`,
   `norm_integral_Ioi_le_of_exp_decay`).
2. Quadratic-to-linear Gaussian exponent lower bound on `ξ ≥ η ≥ C'/ν + 2 + l`
   (`gaussian_linear_tail_bound`):
   `(|ξ| - C'/ν)² ≥ (l + 2 + (ξ - η))² ≥ l² + 4 (ξ - η)`.
3. Differentiation of `∫_{Ioi η} G(r, ξ) dξ` with respect to age `r > 0` to arbitrary order `k ≤ ℓ`
   under uniform exponential domination (`iteratedDeriv_eq_integral_Ioi`).
4. Pointwise derivative identity `∂_η (\bar v₁) = -\bar ω` (`hasDerivAt_meanVel1_curl`) and base
   (`ℓ = 0`) improper integral representations of `meanVel1` and `meanStream` on `Ioi η` from
   `bucMeanVelDecay` and `meanStreamDecay`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

namespace PartI_T21

/-! ### 1. Exponential tail integrals on `Ioi r` -/

/-- For `a > 0` and `r : ℝ`, `s ↦ exp(-a (s - r))` is integrable on `Ioi r` with integral `a⁻¹`. -/
theorem expTail_Ioi {a : ℝ} (ha : 0 < a) (r : ℝ) :
    IntegrableOn (fun s : ℝ => Real.exp (-a * (s - r))) (Ioi r) ∧
      ∫ s in Ioi r, Real.exp (-a * (s - r)) = a⁻¹ := by
  have hd : ∀ x ∈ Ioi r, HasDerivAt (fun s : ℝ => -a⁻¹ * Real.exp (-a * (s - r)))
      (Real.exp (-a * (x - r))) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => -a * (s - r)) (-a) x := by
      simpa using ((hasDerivAt_id x).sub_const r).const_mul (-a)
    have h2 := h1.exp.const_mul (-a⁻¹)
    refine h2.congr_deriv ?_
    have ha0 : a ≠ 0 := ha.ne'
    field_simp
  have hc : ContinuousWithinAt (fun s : ℝ => -a⁻¹ * Real.exp (-a * (s - r))) (Ici r) r := by
    fun_prop
  have ht : Tendsto (fun s : ℝ => -a⁻¹ * Real.exp (-a * (s - r))) atTop (𝓝 0) := by
    have hf : Tendsto (fun s : ℝ => s - r) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-r) tendsto_id
    have h1 : Tendsto (fun s : ℝ => -a * (s - r)) atTop atBot :=
      hf.const_mul_atTop_of_neg (neg_lt_zero.2 ha)
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (-a⁻¹)
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hc hd (fun x _ => (Real.exp_pos _).le) ht, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hc hd (fun x _ => (Real.exp_pos _).le) ht]
  simp

/-- If `f` is continuous and satisfies `|f s| ≤ B * exp(-a (s - r))` on `Ioi r` (`B ≥ 0, a > 0`),
then `f` is integrable on `Ioi r` and `|∫ s in Ioi r, f s| ≤ B * a⁻¹`. -/
theorem norm_integral_Ioi_le_of_exp_decay {f : ℝ → ℝ} {B a r : ℝ}
    (hf : Continuous f) (_hB : 0 ≤ B) (ha : 0 < a)
    (hbound : ∀ s ∈ Ioi r, |f s| ≤ B * Real.exp (-a * (s - r))) :
    IntegrableOn f (Ioi r) ∧ |∫ s in Ioi r, f s| ≤ B * a⁻¹ := by
  obtain ⟨hint_exp, hval_exp⟩ := expTail_Ioi ha r
  have hint_dom : IntegrableOn (fun s : ℝ => B * Real.exp (-a * (s - r))) (Ioi r) :=
    hint_exp.const_mul B
  have hae : ∀ᵐ s ∂(volume.restrict (Ioi r)), ‖f s‖ ≤ B * Real.exp (-a * (s - r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs]
    exact hbound s hs
  have hint_f : IntegrableOn f (Ioi r) :=
    Integrable.mono' hint_dom hf.aestronglyMeasurable hae
  refine ⟨hint_f, ?_⟩
  have hle := norm_integral_le_of_norm_le hint_dom hae
  rw [Real.norm_eq_abs, MeasureTheory.integral_const_mul, hval_exp] at hle
  exact hle

/-- Reproducing exponential tail bound under `ξ ↦ ∫ ζ in Ioi ξ, g ζ`:
if `|g ζ| ≤ B * exp(-a (ζ - η₀))` for all `ζ ≥ η₀` (`B ≥ 0, a > 0`), then for all `ξ ≥ η₀`,
`g` is integrable on `Ioi ξ` and `|∫ ζ in Ioi ξ, g ζ| ≤ (B * a⁻¹) * exp(-a (ξ - η₀))`. -/
theorem abs_integral_Ioi_exp_reproduce {g : ℝ → ℝ} {B a η₀ : ℝ}
    (hg : Continuous g) (hB : 0 ≤ B) (ha : 0 < a)
    (hbound : ∀ ζ : ℝ, η₀ ≤ ζ → |g ζ| ≤ B * Real.exp (-a * (ζ - η₀)))
    {ξ : ℝ} (hξ : η₀ ≤ ξ) :
    IntegrableOn g (Ioi ξ) ∧
      |∫ ζ in Ioi ξ, g ζ| ≤ (B * a⁻¹) * Real.exp (-a * (ξ - η₀)) := by
  have hB' : 0 ≤ B * Real.exp (-a * (ξ - η₀)) := mul_nonneg hB (Real.exp_nonneg _)
  have hbd' : ∀ ζ ∈ Ioi ξ,
      |g ζ| ≤ (B * Real.exp (-a * (ξ - η₀))) * Real.exp (-a * (ζ - ξ)) := by
    intro ζ hζ
    have hζ₀ : η₀ ≤ ζ := hξ.trans (le_of_lt hζ)
    calc |g ζ| ≤ B * Real.exp (-a * (ζ - η₀)) := hbound ζ hζ₀
      _ = (B * Real.exp (-a * (ξ - η₀))) * Real.exp (-a * (ζ - ξ)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
  obtain ⟨hint, hle⟩ := norm_integral_Ioi_le_of_exp_decay hg hB' ha hbd'
  exact ⟨hint, by linarith⟩

/-! ### 2. Quadratic-to-linear Gaussian exponent lower bound on `ξ ≥ η ≥ C'/ν + 2 + l` -/

/-- For `b, A, C', ν > 0`, `l ≥ 0`, `C' / ν + 2 + l ≤ η`, and `η ≤ ξ`,
`(|ξ| - C'/ν)² ≥ (l + 2 + (ξ - η))² ≥ l² + 4(ξ - η)`, so
`exp(-(b * (max (|ξ| - C'/ν) 0)² / A)) ≤ exp(-(b * l² / A)) * exp(-(4 * b / A) * (ξ - η))`. -/
theorem gaussian_linear_tail_bound {b A C' ν l η ξ : ℝ}
    (hb : 0 < b) (hA : 0 < A) (hC' : 0 < C') (hν : 0 < ν) (hl : 0 ≤ l)
    (hη : C' / ν + 2 + l ≤ η) (hξη : η ≤ ξ) :
    Real.exp (-(b * (max (|ξ| - C' / ν) 0) ^ 2 / A)) ≤
      Real.exp (-(b * l ^ 2 / A)) * Real.exp (-(4 * b / A) * (ξ - η)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have hCν_pos : 0 < C' / ν := div_pos hC' hν
  have hξ_pos : 0 < ξ := by linarith
  have habs_ξ : |ξ| = ξ := abs_of_pos hξ_pos
  have hdiff_ge : l + 2 + (ξ - η) ≤ max (|ξ| - C' / ν) 0 := by
    refine le_trans ?_ (le_max_left _ _)
    rw [habs_ξ]
    linarith
  have hdiff_nn : 0 ≤ l + 2 + (ξ - η) := by linarith
  have hsq1 : (l + 2 + (ξ - η)) ^ 2 ≤ (max (|ξ| - C' / ν) 0) ^ 2 :=
    pow_le_pow_left₀ hdiff_nn hdiff_ge 2
  have hsq2 : l ^ 2 + 4 * (ξ - η) ≤ (l + 2 + (ξ - η)) ^ 2 := by
    have : 0 ≤ ξ - η := by linarith
    nlinarith [sq_nonneg (ξ - η)]
  have hsq : l ^ 2 + 4 * (ξ - η) ≤ (max (|ξ| - C' / ν) 0) ^ 2 := hsq2.trans hsq1
  have hmul : b * (l ^ 2 + 4 * (ξ - η)) ≤ b * (max (|ξ| - C' / ν) 0) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hb.le
  have hdiv : b * (l ^ 2 + 4 * (ξ - η)) / A ≤ b * (max (|ξ| - C' / ν) 0) ^ 2 / A :=
    div_le_div_of_nonneg_right hmul hA.le
  have hring : -(b * l ^ 2 / A) + -(4 * b / A) * (ξ - η) = -(b * (l ^ 2 + 4 * (ξ - η)) / A) := by
    ring
  linarith

/-! ### 3. Differentiation under `∫ ξ in Ioi η` with respect to age `r` -/

/-- Expresses `iteratedDeriv k (fun r => G r ξ) s` via `iteratedFDeriv` of `(r, ξ) ↦ G r ξ`. -/
private theorem slice_iteratedDeriv_1D_eq (G : ℝ → ℝ → ℝ)
    (hG : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => G x.1 x.2) (Ioi 0 ×ˢ univ)) (k : ℕ)
    {s : ℝ} (hs : 0 < s) (ξ : ℝ) :
    iteratedDeriv k (fun r => G r ξ) s =
      iteratedFDeriv ℝ k (fun x : ℝ × ℝ => G x.1 x.2) (s, ξ) (fun _ => (1, 0)) := by
  let K : ℝ × ℝ → ℝ := fun x => G x.1 x.2
  have hopen : IsOpen {p : ℝ × ℝ | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hmaps : MapsTo (fun p : ℝ × ℝ => p + ((0 : ℝ), ξ)) {p : ℝ × ℝ | 0 < p.1}
      (Ioi 0 ×ˢ (univ : Set ℝ)) :=
    fun p hp => ⟨by simpa using hp, mem_univ _⟩
  have hsmooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => K (p + ((0 : ℝ), ξ)))
      {p : ℝ × ℝ | 0 < p.1} :=
    hG.comp (contDiff_id.add contDiff_const).contDiffOn hmaps
  have hfun : (fun r : ℝ => G r ξ) =
      (fun p : ℝ × ℝ => K (p + ((0 : ℝ), ξ))) ∘ (ContinuousLinearMap.inl ℝ ℝ ℝ) := by
    funext r
    simp [K]
  have hL : ContinuousLinearMap.inl ℝ ℝ ℝ s ∈ {p : ℝ × ℝ | 0 < p.1} := by simpa using hs
  have hpre : IsOpen ((ContinuousLinearMap.inl ℝ ℝ ℝ) ⁻¹' {p : ℝ × ℝ | 0 < p.1}) :=
    hopen.preimage (ContinuousLinearMap.continuous _)
  have hs_pre : s ∈ (ContinuousLinearMap.inl ℝ ℝ ℝ) ⁻¹' {p : ℝ × ℝ | 0 < p.1} := hL
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right
    (ContinuousLinearMap.inl ℝ ℝ ℝ) hsmooth hopen.uniqueDiffOn hpre.uniqueDiffOn hL
    (i := k) (mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen k hopen hL,
    iteratedFDerivWithin_of_isOpen k hpre hs_pre] at hcomp
  have hA : iteratedFDeriv ℝ k (fun p : ℝ × ℝ => K (p + ((0 : ℝ), ξ)))
      (ContinuousLinearMap.inl ℝ ℝ ℝ s) = iteratedFDeriv ℝ k K (s, ξ) := by
    simp [iteratedFDeriv_comp_add_right]
  rw [hfun, iteratedDeriv_eq_iteratedFDeriv, hcomp, hA]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1

/-- Joint `C^∞` smoothness of `(r, ξ) ↦ iteratedDeriv k (fun r' => G r' ξ) r` on `(0, ∞) × ℝ`. -/
theorem contDiffOn_iteratedDeriv_1D {G : ℝ → ℝ → ℝ}
    (hG : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => G x.1 x.2) (Ioi 0 ×ˢ univ)) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => iteratedDeriv k (fun r => G r x.2) x.1) (Ioi 0 ×ˢ univ) := by
  refine contDiffOn_infty.2 fun m x hx => ?_
  have hKa : ContDiffAt ℝ ∞ (fun y : ℝ × ℝ => G y.1 y.2) x :=
    hG.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hx)
  have h1 : ContDiffAt ℝ m (iteratedFDeriv ℝ k (fun y : ℝ × ℝ => G y.1 y.2)) x :=
    hKa.iteratedFDeriv_right (m := (m : WithTop ℕ∞)) (i := k) (by exact_mod_cast le_top)
  have h2 : ContDiffAt ℝ m
      (fun y : ℝ × ℝ =>
        iteratedFDeriv ℝ k (fun p : ℝ × ℝ => G p.1 p.2) y (fun _ => (1, 0))) x :=
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => ℝ × ℝ) ℝ
      (fun _ => (1, 0))).contDiff.contDiffAt).comp x h1
  refine h2.contDiffWithinAt.congr (fun y hy => ?_) ?_
  · exact slice_iteratedDeriv_1D_eq G hG k hy.1 y.2
  · exact slice_iteratedDeriv_1D_eq G hG k hx.1 x.2

/-- Continuity of `ξ ↦ iteratedDeriv k (fun r => G r ξ) s` for `s > 0`. -/
theorem continuous_slice_iteratedDeriv_1D {G : ℝ → ℝ → ℝ}
    (hG : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => G x.1 x.2) (Ioi 0 ×ˢ univ)) (k : ℕ)
    {s : ℝ} (hs : 0 < s) :
    Continuous (fun ξ : ℝ => iteratedDeriv k (fun r => G r ξ) s) :=
  ((contDiffOn_iteratedDeriv_1D hG k).comp_contDiff
    (contDiff_const.prodMk contDiff_id) (fun ξ => ⟨hs, mem_univ ξ⟩)).continuous

/-- Pointwise `r`-differentiability of `iteratedDeriv k (fun r' => G r' ξ)` at `r > 0`. -/
theorem hasDerivAt_iteratedDeriv_1D {G : ℝ → ℝ → ℝ}
    (hG : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => G x.1 x.2) (Ioi 0 ×ˢ univ)) (k : ℕ)
    {r : ℝ} (hr : 0 < r) (ξ : ℝ) :
    HasDerivAt (iteratedDeriv k (fun r' => G r' ξ))
      (iteratedDeriv (k + 1) (fun r' => G r' ξ) r) r := by
  have hsm : ContDiffAt ℝ ∞ (fun r' : ℝ => iteratedDeriv k (fun r'' => G r'' ξ) r') r := by
    have h0 : ContDiffAt ℝ ∞ (fun x : ℝ × ℝ => iteratedDeriv k (fun r' => G r' x.2) x.1) (r, ξ) :=
      (contDiffOn_iteratedDeriv_1D hG k).contDiffAt
        ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hr, mem_univ ξ⟩)
    exact h0.comp r (contDiffAt_id.prodMk contDiffAt_const)
  have hd : DifferentiableAt ℝ (iteratedDeriv k (fun r' => G r' ξ)) r :=
    hsm.differentiableAt (by simp)
  rw [iteratedDeriv_succ]
  exact hd.hasDerivAt

/-- **Differentiation under `∫ ξ in Ioi η` to arbitrary age order `k ≤ ℓ`:**
if `F(r, η) = ∫ ξ in Ioi η, G(r, ξ)` for `r ∈ (0, R)` and `η ≥ η₀`, and each age derivative
`∂_r^k G(r, ξ)` (`k ≤ ℓ`) is uniformly dominated by `B_k exp(-a_k (ξ - η))` on `(0, R) × Ioi η`,
then `∂_r^k F(r, η) = ∫ ξ in Ioi η, ∂_r^k G(r, ξ)` for all `k ≤ ℓ`, `r ∈ (0, R)`, and `η ≥ η₀`. -/
theorem iteratedDeriv_eq_integral_Ioi {F G : ℝ → ℝ → ℝ} {R η₀ : ℝ} {ℓ : ℕ}
    (hG_sm : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => G x.1 x.2) (Ioi 0 ×ˢ univ))
    (hbase : ∀ r ∈ Ioo (0 : ℝ) R, ∀ η : ℝ, η₀ ≤ η → F r η = ∫ ξ in Ioi η, G r ξ)
    (hdom : ∀ k ≤ ℓ, ∀ η : ℝ, η₀ ≤ η →
      ∃ B a : ℝ, 0 ≤ B ∧ 0 < a ∧
        ∀ r ∈ Ioo (0 : ℝ) R, ∀ ξ ∈ Ioi η,
          |iteratedDeriv k (fun r' => G r' ξ) r| ≤ B * Real.exp (-a * (ξ - η))) :
    ∀ k ≤ ℓ, ∀ r ∈ Ioo (0 : ℝ) R, ∀ η : ℝ, η₀ ≤ η →
      iteratedDeriv k (fun r' => F r' η) r =
        ∫ ξ in Ioi η, iteratedDeriv k (fun r' => G r' ξ) r := by
  intro k
  induction k with
  | zero =>
    intro _ r hr η hη
    simp only [iteratedDeriv_zero]
    exact hbase r hr η hη
  | succ k ih =>
    intro hk1 r hr η hη
    have hk : k ≤ ℓ := Nat.le_of_succ_le hk1
    obtain ⟨B₀, a₀, hB₀, ha₀, hbd₀⟩ := hdom k hk η hη
    obtain ⟨B₁, a₁, hB₁, ha₁, hbd₁⟩ := hdom (k + 1) hk1 η hη
    have hev : iteratedDeriv k (fun r' => F r' η) =ᶠ[𝓝 r]
        fun y => ∫ ξ in Ioi η, iteratedDeriv k (fun r' => G r' ξ) y := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with y hy using ih hk y hy η hη
    rw [iteratedDeriv_succ, hev.deriv_eq]
    let μ : Measure ℝ := volume.restrict (Ioi η)
    have hs_nhds : Ioo (0 : ℝ) R ∈ 𝓝 r := Ioo_mem_nhds hr.1 hr.2
    have hF_meas : ∀ᶠ y in 𝓝 r,
        AEStronglyMeasurable (fun ξ => iteratedDeriv k (fun r' => G r' ξ) y) μ := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with y hy
      exact (continuous_slice_iteratedDeriv_1D hG_sm k hy.1).aestronglyMeasurable
    have hF_int : Integrable (fun ξ => iteratedDeriv k (fun r' => G r' ξ) r) μ :=
      (norm_integral_Ioi_le_of_exp_decay (continuous_slice_iteratedDeriv_1D hG_sm k hr.1)
        hB₀ ha₀ (hbd₀ r hr)).1
    have hF'_meas : AEStronglyMeasurable
        (fun ξ => iteratedDeriv (k + 1) (fun r' => G r' ξ) r) μ :=
      (continuous_slice_iteratedDeriv_1D hG_sm (k + 1) hr.1).aestronglyMeasurable
    have h_bound : ∀ᵐ ξ ∂μ, ∀ y ∈ Ioo (0 : ℝ) R,
        ‖iteratedDeriv (k + 1) (fun r' => G r' ξ) y‖ ≤ B₁ * Real.exp (-a₁ * (ξ - η)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ y hy
      rw [Real.norm_eq_abs]
      exact hbd₁ y hy ξ hξ
    have h_bound_int : Integrable (fun ξ => B₁ * Real.exp (-a₁ * (ξ - η))) μ :=
      (expTail_Ioi ha₁ η).1.const_mul B₁
    have h_diff : ∀ᵐ ξ ∂μ, ∀ y ∈ Ioo (0 : ℝ) R,
        HasDerivAt (fun y' => iteratedDeriv k (fun r' => G r' ξ) y')
          (iteratedDeriv (k + 1) (fun r' => G r' ξ) y) y := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ _ y hy
      exact hasDerivAt_iteratedDeriv_1D hG_sm k hy.1 ξ
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      hs_nhds hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
    exact key.2.deriv

/-! ### 4. Pointwise derivative `∂_η (\bar v₁) = -\bar ω` and `ℓ = 0` improper integrals -/

/-- For a train `tr : B0140.TrainSol ν c` (`c > 0`) at age `r ≥ 0`,
`HasDerivAt (meanVel1 tr r) (-hmean c (Cyl.curl (tr.v r)) η) η`. -/
theorem hasDerivAt_meanVel1_curl {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c)
    {r : ℝ} (hr : 0 ≤ r) (η : ℝ) :
    HasDerivAt (meanVel1 tr r) (-hmean c (Cyl.curl (tr.v r)) η) η := by
  have hv_cd : ContDiff ℝ ∞ (tr.v r) := bucVel_vslice_contDiff tr hr
  have hv0_cd : ContDiff ℝ 1 (fun w : Plane => tr.v r w 0) :=
    ((EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hv_cd).of_le (by simp)
  have hv1_cd : ContDiff ℝ 2 (fun w : Plane => tr.v r w 1) :=
    ((EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hv_cd).of_le (by simp)
  have hd0 : HasDerivAt (meanVel1 tr r)
      (hmean c (Cyl.partialEta (fun w : Plane => tr.v r w 0)) η) η :=
    cpH2_hasDerivAt_hmean hv0_cd η
  have hper1 : Cyl.IsPeriodic c (fun w : Plane => tr.v r w 1) := fun w =>
    congrArg (fun u : Vec => u 1) (tr.isTrain.periodic_v r hr w)
  have hC2_v1 := Cyl.C2.of_contDiff hv1_cd
  have hQ1_zero : ∫ q in Ioc (-c / 2) (c / 2),
      Cyl.partialQ (fun w : Plane => tr.v r w 1) (q, η) = 0 :=
    cpHL_integral_partialQ_zero hc (hv1_cd.differentiable (by norm_num)) hC2_v1.contQ hper1 η
  have hcurl_cd : ContDiff ℝ ∞ (Cyl.curl (tr.v r)) :=
    PartI_T20.contDiff_curl_of_contDiff hv_cd
  have hcq : Continuous (fun q : ℝ => ((q, η) : Plane)) :=
    continuous_id.prodMk continuous_const
  have hint_Q1 : IntegrableOn
      (fun q : ℝ => Cyl.partialQ (fun w : Plane => tr.v r w 1) (q, η))
      (Ioc (-c / 2) (c / 2)) :=
    (hC2_v1.contQ.comp hcq).integrableOn_Ioc
  have hint_curl : IntegrableOn
      (fun q : ℝ => Cyl.curl (tr.v r) (q, η)) (Ioc (-c / 2) (c / 2)) :=
    (hcurl_cd.continuous.comp hcq).integrableOn_Ioc
  have hpt : (fun q : ℝ => Cyl.partialEta (fun w : Plane => tr.v r w 0) (q, η)) =
      fun q : ℝ => Cyl.partialQ (fun w : Plane => tr.v r w 1) (q, η) -
        Cyl.curl (tr.v r) (q, η) := by
    funext q
    show Cyl.partialEta (fun w : Plane => tr.v r w 0) (q, η) =
      Cyl.partialQ (fun w : Plane => tr.v r w 1) (q, η) -
        (Cyl.partialQ (fun w : Plane => tr.v r w 1) (q, η) -
          Cyl.partialEta (fun w : Plane => tr.v r w 0) (q, η))
    ring
  have hm_eq : hmean c (Cyl.partialEta (fun w : Plane => tr.v r w 0)) η =
      -hmean c (Cyl.curl (tr.v r)) η := by
    unfold hmean
    rw [hpt, MeasureTheory.integral_sub hint_Q1 hint_curl, hQ1_zero, zero_sub,
      smul_neg]
  rwa [hm_eq] at hd0

/-- Base (`ℓ = 0`) improper integral representation of `meanVel1`:
if `hmean c (Cyl.curl (tr.v r))` is integrable on `Ioi η`, then
`meanVel1 tr r η = ∫ ξ in Ioi η, hmean c (Cyl.curl (tr.v r)) ξ`. -/
theorem meanVel1_eq_integral_Ioi_curl {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {r : ℝ} (hr : 0 ≤ r) (η : ℝ)
    (hint : IntegrableOn (hmean c (Cyl.curl (tr.v r))) (Ioi η)) :
    meanVel1 tr r η = ∫ ξ in Ioi η, hmean c (Cyl.curl (tr.v r)) ξ := by
  have hd : ∀ ξ ∈ Ioi η,
      HasDerivAt (meanVel1 tr r) (-hmean c (Cyl.curl (tr.v r)) ξ) ξ :=
    fun ξ _ => hasDerivAt_meanVel1_curl hc tr hr ξ
  have hcont : ContinuousWithinAt (meanVel1 tr r) (Ici η) η :=
    (hasDerivAt_meanVel1_curl hc tr hr η).continuousAt.continuousWithinAt
  have hlim : Tendsto (meanVel1 tr r) atTop (𝓝 0) :=
    (bucMeanVelDecay ν c hν hc tr htr r hr).1
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hint.neg hlim
  rw [MeasureTheory.integral_neg] at hftc
  linarith

/-- Base (`ℓ = 0`) improper integral representation of `meanStream`:
if `meanVel1 tr r` is integrable on `Ioi η`, then
`meanStream tr r η = ∫ ξ in Ioi η, meanVel1 tr r ξ`. -/
theorem meanStream_eq_integral_Ioi_meanVel1 {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) (η : ℝ)
    (hint : IntegrableOn (meanVel1 tr r) (Ioi η)) :
    meanStream tr r η = ∫ ξ in Ioi η, meanVel1 tr r ξ := by
  have hd : ∀ ξ ∈ Ioi η, HasDerivAt (meanStream tr r) (-meanVel1 tr r ξ) ξ :=
    fun ξ _ => bucVel_S_deriv tr hr ξ
  have hcont : ContinuousWithinAt (meanStream tr r) (Ici η) η :=
    (bucVel_S_deriv tr hr η).continuousAt.continuousWithinAt
  have hlim : Tendsto (meanStream tr r) atTop (𝓝 0) :=
    meanStreamDecay ν c hν hc tr r hr
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hint.neg hlim
  rw [MeasureTheory.integral_neg] at hftc
  linarith

end PartI_T21

end UnforcedLeray.Short.PartI
