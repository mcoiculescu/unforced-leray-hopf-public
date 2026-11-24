import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FlatMembership.CutNorm
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FlatMembership.Env

/-!
# Part II-a, task `PartII-a:N02/4/3` helper: derivatives off the band, continuity and `L²` of the flat pieces

For a potential `φ` supported in an `s`-band, the derivatives `∂_q φ`, `∂_η φ` vanish off the band
(the support is locally zero there). Hence the envelope bounds `‖φ‖, ‖∂_qφ‖, ‖∂_ηφ‖ ≤ C · E` with
`E = 1_{[s0,s1]}(s) e^{-κ|η|}` hold everywhere, and `cgradC 0 φ`, `streamC 0 φ` are continuous and
dominated by a constant multiple of `E`, hence in `L²(measureH c)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- Derivatives of a potential vanish off its band: it is locally zero there. -/
lemma nzfm_pd_zero_of_not_mem {φ : Profile → ℂ} {s0 s1 : ℝ}
    (hsupp : ∀ p : Profile, φ p ≠ 0 → p.1 ∈ Icc s0 s1) {p : Profile} (hp : p.1 ∉ Icc s0 s1) :
    pdQ φ p = 0 ∧ pdEta φ p = 0 := by
  have hclosed : IsClosed ((fun q : Profile => q.1) ⁻¹' Icc s0 s1) :=
    isClosed_Icc.preimage continuous_fst
  have hmem : p ∈ ((fun q : Profile => q.1) ⁻¹' Icc s0 s1)ᶜ := hp
  have hev : φ =ᶠ[𝓝 p] fun _ => (0 : ℂ) := by
    filter_upwards [hclosed.isOpen_compl.mem_nhds hmem] with q hq
    show φ q = 0
    by_contra hne
    exact hq (hsupp q hne)
  have hfd : fderiv ℝ φ p = 0 := by
    rw [hev.fderiv_eq]
    simp
  exact ⟨by simp [pdQ, hfd], by simp [pdEta, hfd]⟩

/-- The envelope bounds for the potential and its first derivatives, everywhere. -/
lemma nzfm_env_bounds {φ : Profile → ℂ} {s0 s1 κ C : ℝ}
    (hsupp : ∀ p : Profile, φ p ≠ 0 → p.1 ∈ Icc s0 s1)
    (hbd : ∀ p : Profile, ‖φ p‖ ≤ C * Real.exp (-κ * |p.2.2|) ∧
      ‖pdQ φ p‖ ≤ C * Real.exp (-κ * |p.2.2|) ∧ ‖pdEta φ p‖ ≤ C * Real.exp (-κ * |p.2.2|))
    (p : Profile) :
    ‖φ p‖ ≤ C * nzfmE s0 s1 κ p ∧ ‖pdQ φ p‖ ≤ C * nzfmE s0 s1 κ p ∧
      ‖pdEta φ p‖ ≤ C * nzfmE s0 s1 κ p := by
  by_cases h : p.1 ∈ Icc s0 s1
  · rw [nzfmE_of_mem h]
    exact hbd p
  · have hz := nzfm_pd_zero_of_not_mem hsupp h
    have hφ0 : φ p = 0 := by
      by_contra hne
      exact h (hsupp p hne)
    rw [nzfmE_of_not_mem h, mul_zero, hφ0, hz.1, hz.2]
    simp

/-- A constant bounding the potential in the envelope is nonnegative. -/
lemma nzfm_C_nonneg {φ : Profile → ℂ} {κ C : ℝ}
    (h : ∀ p : Profile, ‖φ p‖ ≤ C * Real.exp (-κ * |p.2.2|)) : 0 ≤ C := by
  have h0 := h (0 : Profile)
  have he := Real.exp_pos (-κ * |(0 : Profile).2.2|)
  have hn := norm_nonneg (φ (0 : Profile))
  by_contra hneg
  push_neg at hneg
  nlinarith [mul_neg_of_neg_of_pos hneg he]

lemma nzfm_pdQ_cont {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) : Continuous (pdQ Φ) := by
  unfold pdQ
  exact (hΦ.continuous_fderiv (by simp)).clm_apply continuous_const

lemma nzfm_pdEta_cont {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) : Continuous (pdEta Φ) := by
  unfold pdEta
  exact (hΦ.continuous_fderiv (by simp)).clm_apply continuous_const

lemma nzfm_cont_two {f g : Profile → ℂ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun p => (!₂[f p, g p] : MeridC)) := by
  fun_prop

lemma nzfm_cgrad0_cont {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) : Continuous (cgradC 0 Φ) := by
  have h : cgradC 0 Φ = fun p => (!₂[pdQ Φ p, pdEta Φ p] : MeridC) :=
    funext (nzfm_cgrad0_eq Φ)
  rw [h]
  exact nzfm_cont_two (nzfm_pdQ_cont hΦ) (nzfm_pdEta_cont hΦ)

lemma nzfm_stream0_cont {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) : Continuous (streamC 0 Φ) := by
  have h : streamC 0 Φ = fun p => (!₂[-pdEta Φ p, pdQ Φ p] : MeridC) :=
    funext (nzfm_stream0_eq Φ)
  rw [h]
  exact nzfm_cont_two (nzfm_pdEta_cont hΦ).neg (nzfm_pdQ_cont hΦ)

/-- Pointwise bound of the flat gradient by the envelope. -/
lemma nzfm_cgrad0_le {Φ : Profile → ℂ} {E K C : ℝ} (p : Profile) (hE : 0 ≤ E) (hK : 2 * C ≤ K)
    (h1 : ‖pdQ Φ p‖ ≤ C * E) (h2 : ‖pdEta Φ p‖ ≤ C * E) :
    ‖cgradC 0 Φ p‖ ≤ K * E := by
  rw [nzfm_cgrad0_eq]
  refine (nzco_norm_two _ _).trans ?_
  nlinarith [mul_le_mul_of_nonneg_right hK hE]

/-- Pointwise bound of the flat stream field by the envelope. -/
lemma nzfm_stream0_le {Φ : Profile → ℂ} {E K C : ℝ} (p : Profile) (hE : 0 ≤ E) (hK : 2 * C ≤ K)
    (h1 : ‖pdQ Φ p‖ ≤ C * E) (h2 : ‖pdEta Φ p‖ ≤ C * E) :
    ‖streamC 0 Φ p‖ ≤ K * E := by
  rw [nzfm_stream0_eq]
  refine (nzco_norm_two _ _).trans ?_
  rw [norm_neg]
  nlinarith [mul_le_mul_of_nonneg_right hK hE]

/-- The flat gradient of a band potential with exponential envelope is in `L²(measureH c)`. -/
lemma nzfm_cgrad0_memLp {c s0 s1 κ C K : ℝ} {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    (hκ : 0 < κ) (hs0 : 0 < s0) (hK : 2 * C ≤ K) (hC : 0 ≤ C)
    (hpd : ∀ p : Profile, ‖pdQ Φ p‖ ≤ C * nzfmE s0 s1 κ p ∧ ‖pdEta Φ p‖ ≤ C * nzfmE s0 s1 κ p) :
    MemLp (cgradC 0 Φ) 2 (measureH c) :=
  nzfm_memLp_of_env (c := c) (nzfm_cgrad0_cont hΦ) hκ hs0 (by linarith)
    (fun p => nzfm_cgrad0_le p (nzfmE_nonneg _ _ _ _) hK (hpd p).1 (hpd p).2)

/-- The flat stream field of a band potential with exponential envelope is in `L²(measureH c)`. -/
lemma nzfm_stream0_memLp {c s0 s1 κ C K : ℝ} {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    (hκ : 0 < κ) (hs0 : 0 < s0) (hK : 2 * C ≤ K) (hC : 0 ≤ C)
    (hpd : ∀ p : Profile, ‖pdQ Φ p‖ ≤ C * nzfmE s0 s1 κ p ∧ ‖pdEta Φ p‖ ≤ C * nzfmE s0 s1 κ p) :
    MemLp (streamC 0 Φ) 2 (measureH c) :=
  nzfm_memLp_of_env (c := c) (nzfm_stream0_cont hΦ) hκ hs0 (by linarith)
    (fun p => nzfm_stream0_le p (nzfmE_nonneg _ _ _ _) hK (hpd p).1 (hpd p).2)

end UnforcedLeray.Short.PartIIa
