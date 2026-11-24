import UnforcedLeray.Short.PartI.Sub.PartI_S11_1_1

/-!
# Part I, task `PartI:S11/1/1/1`: the sector stream profile is smooth with Gaussian bounds

Target: `secStreamQ : SecStreamQ`, where `SecStreamQ` (in `Sub/PartI_S11_1_1.lean`) asserts that for
`φ` smooth with compact support in `(0,∞)` the function `Ang.ofProfile m φ` is `C^∞` and every
iterated derivative is bounded by `C (1+|y|)^N e^{-|y|²/4}`.

Method. Off the origin, `Ang.ofProfile m φ z = φ ‖z‖ * (z / ‖z‖)^m` is a product of smooth maps
(`ContDiffAt` of `z ↦ φ ‖z‖` by composition, and of the `zpow` factor through `pow` and `inv`).
Near the origin the function vanishes, since `tsupport φ` is closed and misses `0`. The function
has compact support in a closed ball `closedBall 0 R`, so each `iteratedFDeriv ℝ k` is continuous
with compact support, hence bounded by some `C0`. Taking `N = 0` and `C = max C0 0 * exp (R²/4)`
gives the Gaussian bound, because `exp (R²/4) exp (-|y|²/4) ≥ 1` on the ball and the derivative
vanishes outside it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.Planar.NUE
open Metric

namespace SecStreamQAux

/-- `zpow` of a smooth nonvanishing map is smooth. -/
theorem contDiffAt_zpow_aux {g : ℂ → ℂ} {y : ℂ} (hg : ContDiffAt ℝ ∞ g y) (hy : g y ≠ 0)
    (m : ℤ) : ContDiffAt ℝ ∞ (fun z => g z ^ m) y := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · simp only [zpow_natCast]
    exact hg.pow n
  · simp only [zpow_neg, zpow_natCast]
    exact (hg.pow n).inv (pow_ne_zero _ hy)

/-- The angular phase `(z/|z|)^m` is smooth off the origin. -/
theorem contDiffAt_angPhase_aux {y : ℂ} (hy : y ≠ 0) (m : ℤ) :
    ContDiffAt ℝ ∞ (fun z : ℂ => (z * ((‖z‖⁻¹ : ℝ) : ℂ)) ^ m) y := by
  have hpos : (0 : ℝ) < ‖y‖ := norm_pos_iff.2 hy
  have hn : ContDiffAt ℝ ∞ (fun z : ℂ => ‖z‖) y := contDiffAt_norm ℝ hy
  have hinv : ContDiffAt ℝ ∞ (fun z : ℂ => ‖z‖⁻¹) y := hn.inv hpos.ne'
  have hinvC : ContDiffAt ℝ ∞ (fun z : ℂ => ((‖z‖⁻¹ : ℝ) : ℂ)) y :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp y hinv
  have hid : ContDiffAt ℝ ∞ (fun z : ℂ => z) y := contDiffAt_id
  have hq : ContDiffAt ℝ ∞ (fun z : ℂ => z * ((‖z‖⁻¹ : ℝ) : ℂ)) y := hid.mul hinvC
  have hne : y * ((‖y‖⁻¹ : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero hy (Complex.ofReal_ne_zero.2 (inv_ne_zero hpos.ne'))
  exact contDiffAt_zpow_aux hq hne m

/-- Off the origin, `Ang.ofProfile m φ` is smooth. -/
theorem ofProfile_contDiffAt_ne {φ : ℝ → ℂ} (hs : ContDiff ℝ ∞ φ) {y : ℂ} (hy : y ≠ 0) (m : ℤ) :
    ContDiffAt ℝ ∞ (Ang.ofProfile m φ) y := by
  have hφa : ContDiffAt ℝ ∞ φ ‖y‖ := hs.contDiffAt
  have hn : ContDiffAt ℝ ∞ (fun z : ℂ => ‖z‖) y := contDiffAt_norm ℝ hy
  have hc : ContDiffAt ℝ ∞ (fun z : ℂ => φ ‖z‖) y := hφa.comp y hn
  have hfun : Ang.ofProfile m φ = fun z : ℂ => φ ‖z‖ * (z * ((‖z‖⁻¹ : ℝ) : ℂ)) ^ m := by
    funext z
    simp only [Ang.ofProfile, Ang.angPhase, div_eq_mul_inv, Complex.ofReal_inv]
  rw [hfun]
  exact hc.mul (contDiffAt_angPhase_aux hy m)

/-- `tsupport φ` misses a neighbourhood of `0`, so `Ang.ofProfile m φ` vanishes near `0`. -/
theorem ofProfile_eventually_zero {φ : ℝ → ℂ} (hcl : IsClosed (tsupport φ))
    (hts : tsupport φ ⊆ Ioi 0) (m : ℤ) :
    ∀ᶠ z in 𝓝 (0 : ℂ), Ang.ofProfile m φ z = 0 := by
  have h0 : (0 : ℝ) ∉ tsupport φ := fun h => lt_irrefl (0 : ℝ) (Set.mem_Ioi.1 (hts h))
  have hT : Tendsto (fun z : ℂ => ‖z‖) (𝓝 (0 : ℂ)) (𝓝 (0 : ℝ)) :=
    continuous_norm.tendsto' (0 : ℂ) 0 norm_zero
  have hnb : ∀ᶠ z in 𝓝 (0 : ℂ), ‖z‖ ∈ (tsupport φ)ᶜ :=
    hT.eventually_mem (hcl.isOpen_compl.mem_nhds h0)
  filter_upwards [hnb] with z hz
  simp only [Ang.ofProfile, image_eq_zero_of_notMem_tsupport hz, zero_mul]

/-- The support of `Ang.ofProfile m φ` lies in a closed ball. -/
theorem ofProfile_tsupport_sub {φ : ℝ → ℂ} (hcs : HasCompactSupport φ) (m : ℤ) :
    ∃ R : ℝ, tsupport (Ang.ofProfile m φ) ⊆ closedBall (0 : ℂ) R := by
  obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨R, ?_⟩
  have hsupp : Function.support (Ang.ofProfile m φ) ⊆ closedBall (0 : ℂ) R := by
    intro z hz
    have hφz : φ ‖z‖ ≠ 0 := by
      intro h
      apply Function.mem_support.1 hz
      simp only [Ang.ofProfile, h, zero_mul]
    have hmem : ‖z‖ ∈ tsupport φ := subset_tsupport _ (Function.mem_support.2 hφz)
    have h1 := hR hmem
    rw [mem_closedBall_zero_iff] at h1 ⊢
    rwa [norm_norm] at h1
  exact closure_minimal hsupp Metric.isClosed_closedBall

/-- `Ang.ofProfile m φ` is `C^∞`. -/
theorem ofProfile_contDiff {φ : ℝ → ℂ} (hs : ContDiff ℝ ∞ φ) (hcl : IsClosed (tsupport φ))
    (hts : tsupport φ ⊆ Ioi 0) (m : ℤ) : ContDiff ℝ ∞ (Ang.ofProfile m φ) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = 0
  · subst hy
    have hc : ContDiffAt ℝ ∞ (fun _ : ℂ => (0 : ℂ)) 0 := contDiffAt_const
    exact hc.congr_of_eventuallyEq (ofProfile_eventually_zero hcl hts m)
  · exact ofProfile_contDiffAt_ne hs hy m

/-- Gaussian-class bound for all derivatives of a compactly supported smooth function. -/
theorem iteratedFDeriv_gaussian_bound {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (R : ℝ)
    (hR : tsupport f ⊆ closedBall (0 : ℂ) R) (hcs : HasCompactSupport f) (k : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ y,
      ‖iteratedFDeriv ℝ k f y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4) := by
  have hcont : Continuous (iteratedFDeriv ℝ k f) :=
    hf.continuous_iteratedFDeriv (by first | simp | exact_mod_cast le_top)
  obtain ⟨C0, hC0⟩ := hcont.bounded_above_of_compact_support (hcs.iteratedFDeriv k)
  refine ⟨max C0 0 * Real.exp (R ^ 2 / 4), 0, fun y => ?_⟩
  by_cases hy : y ∈ closedBall (0 : ℂ) R
  · have hyR : ‖y‖ ≤ R := mem_closedBall_zero_iff.1 hy
    have h1 : 1 ≤ Real.exp (R ^ 2 / 4) * Real.exp (-(‖y‖ ^ 2) / 4) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith [norm_nonneg y]
    calc ‖iteratedFDeriv ℝ k f y‖ ≤ max C0 0 := (hC0 y).trans (le_max_left _ _)
      _ ≤ max C0 0 * (Real.exp (R ^ 2 / 4) * Real.exp (-(‖y‖ ^ 2) / 4)) :=
          le_mul_of_one_le_right (le_max_right _ _) h1
      _ = max C0 0 * Real.exp (R ^ 2 / 4) * (1 + ‖y‖) ^ 0 * Real.exp (-(‖y‖ ^ 2) / 4) := by ring
  · have h0 : iteratedFDeriv ℝ k f y = 0 := by
      by_contra h
      exact hy (hR (support_iteratedFDeriv_subset k (Function.mem_support.2 h)))
    rw [h0, norm_zero]
    simp only [pow_zero, mul_one]
    exact mul_nonneg (mul_nonneg (le_max_right _ _) (Real.exp_pos _).le) (Real.exp_pos _).le

end SecStreamQAux

open SecStreamQAux

/-- **Target `PartI:S11/1/1/1`**: `SecStreamQ` (see `Sub/PartI_S11_1_1.lean`, lines 841-889). -/
theorem secStreamQ : UnforcedLeray.Short.PartI.SecStreamQ := by
  unfold SecStreamQ
  intro m φ hφ
  unfold SmoothCptFun at hφ
  obtain ⟨hs, hc, hts⟩ := hφ
  have hcl : IsClosed (tsupport φ) := isClosed_tsupport φ
  obtain ⟨R, hR⟩ := ofProfile_tsupport_sub hc m
  have hcs : HasCompactSupport (Ang.ofProfile m φ) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R) (fun z hz =>
      Classical.byContradiction fun h => hz (hR (subset_tsupport _ (Function.mem_support.2 h))))
  refine ⟨ofProfile_contDiff hs hcl hts m, fun k => ?_⟩
  exact iteratedFDeriv_gaussian_bound (ofProfile_contDiff hs hcl hts m) R hR hcs k

end UnforcedLeray.Short.PartI
