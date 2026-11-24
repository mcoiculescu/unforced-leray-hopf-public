import UnforcedLeray.Short.Spine.Params

/-!
# Proof of `ReferenceFromInstability` (Spine)

Source: `the November 2 reference manuscript`, lines 1155-1180 (`𝒥` holomorphic
and not identically zero on `Re μ > -3/2`) and 5922-5940 (`σ₀ ∈ (0,1/4)` with `𝒞(σ₀) ≠ 0`):
the identity theorem gives a real `σ₀ ∈ (1/16,1/8)` with `𝒥(σ₀) ≠ 0`, and `𝒞 = (63πi/128) 𝓛 𝒥`
with `𝓛 = ℓ(H) Γ(σ+5/2) λ^{-(σ+5/2)}`, all other factors nonzero. The argument is that of the
draft `Cons/C01ReferenceChoice/Mellin.lean` (`exists_mem_Ioo_mellinJ_ne_zero`), here with the
holomorphy of `𝒥` taken from `GaussianInstability`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Blueprint.Planar
open UnforcedLeray.Cons.Data

/-- The real `𝒥` of the draft planar data is the complex `𝒥` at a real argument. -/
theorem mellinJ_eq_mellinJC (P : PlanarData) (μ : ℝ) : P.mellinJ μ = mellinJC P (μ : ℂ) := by
  unfold PlanarData.mellinJ mellinJC
  refine setIntegral_congr_fun measurableSet_Ioi fun θ hθ => ?_
  rw [Complex.ofReal_cpow (le_of_lt hθ)]
  congr 2
  push_cast
  try ring

/-- A real point with `𝒥 ≠ 0` in every real interval of `(-3/2, ∞)`, by the identity theorem. -/
theorem exists_real_mellin_ne_zero (P : PlanarData) (hP : GaussianInstability P) {a b : ℝ}
    (hab : a < b) (ha : -(3 / 2) < a) : ∃ σ ∈ Ioo a b, P.mellinJ σ ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_and, ne_eq, not_not] at hcon
  obtain ⟨μ, hμ, hne⟩ := hP.mellin_nonzero
  set g : ℂ → ℂ := mellinJC P with hg
  set U : Set ℂ := {s : ℂ | -(3 / 2) < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt (-(3 / 2))).isPreconnected
  have hga : AnalyticOnNhd ℂ g U := hP.mellin_holomorphic.analyticOnNhd hUo
  set m : ℝ := (a + b) / 2 with hm
  set d : ℝ := (b - a) / 4 with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  set z₀ : ℂ := (m : ℂ) with hz₀
  have hz₀U : z₀ ∈ U := by
    show -(3 / 2) < z₀.re
    simp only [hz₀, Complex.ofReal_re, hm]
    linarith
  set σ : ℕ → ℝ := fun n => m + d * (1 / ((n : ℝ) + 1)) with hσ
  have hσmem : ∀ n : ℕ, σ n ∈ Ioo a b := by
    intro n
    have hn : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hn1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    constructor
    · simp only [hσ, hm, hd] at *; nlinarith
    · simp only [hσ, hm, hd] at *; nlinarith
  have hσlim : Tendsto σ atTop (𝓝 m) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul d
    simpa [hσ] using (tendsto_const_nhds (x := m)).add this
  set u : ℕ → ℂ := fun n => (σ n : ℂ) with hu
  have hulim : Tendsto u atTop (𝓝[≠] z₀) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · exact (Complex.continuous_ofReal.tendsto m).comp hσlim
    · simp only [mem_compl_iff, mem_singleton_iff, hu, hz₀]
      intro heq
      have h2 : σ n = m := by exact_mod_cast heq
      have h3 : 0 < d * (1 / ((n : ℝ) + 1)) := by positivity
      simp only [hσ] at h2
      linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, g z = 0 := by
    refine hulim.frequently (Frequently.of_forall fun n => ?_)
    simp only [hu, hg]
    rw [← mellinJ_eq_mellinJC]
    exact hcon (σ n) (hσmem n)
  have hzero := hga.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc hz₀U hfreq
  exact hne (hzero hμ)

/-- The real `𝒥` is continuous at every real point of `(-3/2, ∞)`. -/
theorem continuousAt_mellinJ_short (P : PlanarData) (hP : GaussianInstability P) {σ : ℝ}
    (hσ : -(3 / 2) < σ) : ContinuousAt P.mellinJ σ := by
  have hU : {s : ℂ | -(3 / 2) < s.re} ∈ 𝓝 (σ : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simpa using hσ)
  have hc : ContinuousAt (mellinJC P) (σ : ℂ) :=
    (hP.mellin_holomorphic.differentiableAt hU).continuousAt
  have hfun : P.mellinJ = fun μ : ℝ => mellinJC P (μ : ℂ) := funext (mellinJ_eq_mellinJC P)
  rw [hfun]
  exact ContinuousAt.comp (g := mellinJC P) (f := fun μ : ℝ => (μ : ℂ)) hc
    Complex.continuous_ofReal.continuousAt

/-- `𝓛(μ) ≠ 0` for `μ > -5/2`: `ℓ(H) ≠ 0`, `Γ` has no zeros there, `λ ≠ 0`. -/
theorem couplingL_ne_zero_short (P : PlanarData) (hH : P.strainCoupling ≠ 0)
    (hlam : P.eigenvalue ≠ 0) {μ : ℝ} (hμ : -(5 / 2) < μ) : P.couplingL μ ≠ 0 := by
  have hpole : ∀ m : ℕ, (μ : ℂ) + 5 / 2 ≠ -m := by
    intro m h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at h'
    have : (5 / 2 : ℂ).re = 5 / 2 := by norm_num
    rw [this] at h'
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hG : Complex.Gamma ((μ : ℂ) + 5 / 2) ≠ 0 := Complex.Gamma_ne_zero hpole
  have hpow : P.eigenvalue ^ ((μ : ℂ) + 5 / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => hlam h.1
  exact div_ne_zero (mul_ne_zero hH hG) hpow

/-- `𝒞(μ) = (63πi/128)𝓛(μ)𝒥(μ) ≠ 0` when `𝓛(μ) ≠ 0` and `𝒥(μ) ≠ 0`. -/
theorem signedCoeff_ne_zero_short (P : PlanarData) {μ : ℝ} (hL : P.couplingL μ ≠ 0)
    (hJ : P.mellinJ μ ≠ 0) : P.signedCoeff μ ≠ 0 := by
  have hk : (63 * (Real.pi : ℂ) * Complex.I / 128) ≠ 0 := by
    refine div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero)
      (by norm_num)
    exact_mod_cast Real.pi_ne_zero
  exact mul_ne_zero (mul_ne_zero hk hL) hJ

/-- `ReferenceFromInstability`: a Part I planar reference with a Mellin function holomorphic and
not identically zero yields `σ₀ ∈ (1/16, 1/8)` with `𝒞(σ₀) ≠ 0`, `𝒥` continuous at `σ₀`. -/
theorem referenceFromInstability : ReferenceFromInstability := by
  intro P hP
  obtain ⟨σ₀, hσ₀, hJ⟩ := exists_real_mellin_ne_zero P hP (a := 1 / 16) (b := 1 / 8)
    (by norm_num) (by norm_num)
  have hlam : P.eigenvalue ≠ 0 := by
    intro h
    have := hP.reference.eigenpair.re_pos
    rw [h] at this
    simp at this
  have hL : P.couplingL σ₀ ≠ 0 :=
    couplingL_ne_zero_short P hP.strain_ne hlam (by linarith [hσ₀.1])
  exact ⟨⟨P, σ₀⟩, rfl, hP.reference, hP.frequency, hσ₀, signedCoeff_ne_zero_short P hL hJ,
    continuousAt_mellinJ_short P hP (by linarith [hσ₀.1])⟩

end UnforcedLeray.Short.Spine
