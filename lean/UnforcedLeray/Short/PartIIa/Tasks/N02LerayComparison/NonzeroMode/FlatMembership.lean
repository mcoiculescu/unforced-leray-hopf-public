import UnforcedLeray.Short.PartIIa.Sub.N02_4
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FlatMembership.Pd
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FlatMembership.Lp

/-!
# Part II-a, task `PartII-a:N02/4/3` (`NzFlatMembership`): flat pieces of band potentials lie in the flat subspaces

Target: `nzFlatMembership : NzFlatMembership` (`Sub/N02_4.lean`), source lines 1713-1722 of
`the November 2 reference manuscript`.

Proof. Let `φ` be a smooth `c`-periodic potential supported in an `s`-band with exponential `η`-decay.
Cut off with `χ_n = χ(η/(n+1))` (the potentials `nzcoCut ((n+1)⁻²) φ`, which are complex band tests by
`nzfm_cut_isCTest`). The hypotheses `NearGradMember`, `NearStreamMember` at `ε = 0` put
`cgradC 0 (χ_n φ)` in `(solenoidalHC 0 c)ᗮ` and `streamC 0 (χ_n φ)` in `solenoidalHC 0 c`.
The pointwise difference to `cgradC 0 φ` (resp. `streamC 0 φ`) is at most `(n+1)⁻¹ (|η|(|∂φ|) + B₁|φ|)`
(`nzfm_cut_grad_diff`), which tends to `0`, and both sides are dominated by `2K · 1_{[s0,s1]} e^{-κ|η|}`,
an `L²(measureH c)` function. So `nzfm_tendsto_toLp` gives `L²`-convergence, and the closed subspaces
contain the limits.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- **Lemma NzFlatMembership: the flat pieces lie in the flat subspaces (proved).** -/
theorem nzFlatMembership : NzFlatMembership := by
  unfold NzFlatMembership
  intro hgrad hstream c hc φ hφ hper hband hdec
  obtain ⟨s0, s1, hs0, hsupp⟩ := hband
  unfold NzExpDecay at hdec
  obtain ⟨κ, C, hκ, hbd⟩ := hdec
  obtain ⟨B1, B2, hB1, hB2, hBd⟩ := nzco_bounds
  have hB1' : ∀ t : ℝ, |deriv nzcoChi t| ≤ B1 := fun t => (hBd t).1
  have hCnn : 0 ≤ C := nzfm_C_nonneg (fun p => (hbd p).1)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (2 + B1) * C := ⟨_, rfl⟩
  have hK2 : 2 * C ≤ K := by
    rw [hK]
    nlinarith [mul_nonneg hB1 hCnn]
  have hK0 : 0 ≤ K := by linarith
  have hEpd : ∀ p : Profile, ‖φ p‖ ≤ C * nzfmE s0 s1 κ p ∧ ‖pdQ φ p‖ ≤ C * nzfmE s0 s1 κ p ∧
      ‖pdEta φ p‖ ≤ C * nzfmE s0 s1 κ p := fun p => nzfm_env_bounds hsupp hbd p
  have hEnn : ∀ p : Profile, 0 ≤ nzfmE s0 s1 κ p := fun p => nzfmE_nonneg _ _ _ _
  have hgφ : MemLp (cgradC 0 φ) 2 (measureH c) :=
    nzfm_cgrad0_memLp (c := c) hφ hκ hs0 hK2 hCnn (fun p => ⟨(hEpd p).2.1, (hEpd p).2.2⟩)
  have hsφ : MemLp (streamC 0 φ) 2 (measureH c) :=
    nzfm_stream0_memLp (c := c) hφ hκ hs0 hK2 hCnn (fun p => ⟨(hEpd p).2.1, (hEpd p).2.2⟩)
  have hG : MemLp (fun x => 2 * K * nzfmE s0 s1 κ x) 2 (measureH c) :=
    (nzfmE_memLp s0 s1 c κ hκ hs0).const_mul _
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℝ, t = fun n : ℕ => 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
  have ht_pos : ∀ n, 0 < t n := fun n => by
    rw [ht]
    dsimp only
    positivity
  have ht0 : ∀ n, 0 ≤ t n := fun n => (ht_pos n).le
  have ht1 : ∀ n, t n ≤ 1 := by
    intro n
    rw [ht]
    dsimp only
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have htlim : Tendsto t atTop (𝓝 0) := by
    rw [ht]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hεc : ∀ n, 0 < t n ^ 2 := fun n => pow_pos (ht_pos n) 2
  have hε1 : ∀ n, t n ^ 2 ≤ 1 := fun n => by nlinarith [ht0 n, ht1 n]
  have hct : ∀ n, IsCTest c (nzcoCut (t n ^ 2) φ) := fun n =>
    nzfm_cut_isCTest hφ hper hs0 hsupp (hεc n)
  have hGex : ∀ n, ∃ hm : MemLp (cgradC 0 (nzcoCut (t n ^ 2) φ)) 2 (measureH c),
      hm.toLp _ ∈ (solenoidalHC 0 c)ᗮ := fun n => hgrad 0 c _ (hct n)
  have hSex : ∀ n, ∃ hm : MemLp (streamC 0 (nzcoCut (t n ^ 2) φ)) 2 (measureH c),
      hm.toLp _ ∈ solenoidalHC 0 c := fun n => hstream 0 c _ (hct n)
  choose hGm hGmem using hGex
  choose hSm hSmem using hSex
  -- pointwise differences: `≤ t_n (|η|(|∂_q φ| + |∂_η φ|) + B₁|φ|) → 0`
  have hdiffG : ∀ n x, ‖cgradC 0 (nzcoCut (t n ^ 2) φ) x - cgradC 0 φ x‖ ≤
      t n * (|x.2.2| * (‖pdQ φ x‖ + ‖pdEta φ x‖) + B1 * ‖φ x‖) := by
    intro n x
    have h := nzfm_cut_grad_diff hφ (hεc n).le hB1' x
    rwa [Real.sqrt_sq (ht0 n)] at h
  have hdiffS : ∀ n x, ‖streamC 0 (nzcoCut (t n ^ 2) φ) x - streamC 0 φ x‖ ≤
      t n * (|x.2.2| * (‖pdQ φ x‖ + ‖pdEta φ x‖) + B1 * ‖φ x‖) := by
    intro n x
    have h := nzfm_cut_stream_diff hφ (hεc n).le hB1' x
    rwa [Real.sqrt_sq (ht0 n)] at h
  -- domination by `2 K` times the envelope
  have hbdG : ∀ n x, ‖cgradC 0 (nzcoCut (t n ^ 2) φ) x - cgradC 0 φ x‖ ≤
      2 * K * nzfmE s0 s1 κ x := by
    intro n x
    have h1 := nzfm_cut_grad_norm hφ (hεc n).le (hε1 n) hB1' x
    have h2 : ‖cgradC 0 φ x‖ ≤ K * nzfmE s0 s1 κ x :=
      nzfm_cgrad0_le x (hEnn x) hK2 (hEpd x).2.1 (hEpd x).2.2
    have h3 : B1 * ‖φ x‖ ≤ B1 * (C * nzfmE s0 s1 κ x) :=
      mul_le_mul_of_nonneg_left (hEpd x).1 hB1
    have hKE : K * nzfmE s0 s1 κ x = 2 * (C * nzfmE s0 s1 κ x) + B1 * (C * nzfmE s0 s1 κ x) := by
      rw [hK]
      ring
    have h4 : ‖pdQ φ x‖ + ‖pdEta φ x‖ ≤ 2 * (C * nzfmE s0 s1 κ x) := by
      linarith [(hEpd x).2.1, (hEpd x).2.2]
    have h5 : ‖cgradC 0 (nzcoCut (t n ^ 2) φ) x‖ ≤ K * nzfmE s0 s1 κ x := by
      linarith
    linarith [norm_sub_le (cgradC 0 (nzcoCut (t n ^ 2) φ) x) (cgradC 0 φ x)]
  have hbdS : ∀ n x, ‖streamC 0 (nzcoCut (t n ^ 2) φ) x - streamC 0 φ x‖ ≤
      2 * K * nzfmE s0 s1 κ x := by
    intro n x
    have h1 := nzfm_cut_stream_norm hφ (hεc n).le (hε1 n) hB1' x
    have h2 : ‖streamC 0 φ x‖ ≤ K * nzfmE s0 s1 κ x :=
      nzfm_stream0_le x (hEnn x) hK2 (hEpd x).2.1 (hEpd x).2.2
    have h3 : B1 * ‖φ x‖ ≤ B1 * (C * nzfmE s0 s1 κ x) :=
      mul_le_mul_of_nonneg_left (hEpd x).1 hB1
    have hKE : K * nzfmE s0 s1 κ x = 2 * (C * nzfmE s0 s1 κ x) + B1 * (C * nzfmE s0 s1 κ x) := by
      rw [hK]
      ring
    have h4 : ‖pdQ φ x‖ + ‖pdEta φ x‖ ≤ 2 * (C * nzfmE s0 s1 κ x) := by
      linarith [(hEpd x).2.1, (hEpd x).2.2]
    have h5 : ‖streamC 0 (nzcoCut (t n ^ 2) φ) x‖ ≤ K * nzfmE s0 s1 κ x := by
      linarith
    linarith [norm_sub_le (streamC 0 (nzcoCut (t n ^ 2) φ) x) (streamC 0 φ x)]
  -- pointwise convergence
  have hptG : ∀ x, Tendsto (fun n => cgradC 0 (nzcoCut (t n ^ 2) φ) x) atTop
      (𝓝 (cgradC 0 φ x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => hdiffG n x) ?_
    have := htlim.mul_const (|x.2.2| * (‖pdQ φ x‖ + ‖pdEta φ x‖) + B1 * ‖φ x‖)
    simpa using this
  have hptS : ∀ x, Tendsto (fun n => streamC 0 (nzcoCut (t n ^ 2) φ) x) atTop
      (𝓝 (streamC 0 φ x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => hdiffS n x) ?_
    have := htlim.mul_const (|x.2.2| * (‖pdQ φ x‖ + ‖pdEta φ x‖) + B1 * ‖φ x‖)
    simpa using this
  -- `L²` convergence of the approximants
  have hlimG := nzfm_tendsto_toLp (μ := measureH c)
    (fun n => cgradC 0 (nzcoCut (t n ^ 2) φ)) (cgradC 0 φ) (fun x => 2 * K * nzfmE s0 s1 κ x)
    hGm hgφ hG hbdG hptG
  have hlimS := nzfm_tendsto_toLp (μ := measureH c)
    (fun n => streamC 0 (nzcoCut (t n ^ 2) φ)) (streamC 0 φ) (fun x => 2 * K * nzfmE s0 s1 κ x)
    hSm hsφ hG hbdS hptS
  -- the closed subspaces contain the limits
  have hcl : IsClosed ((solenoidalHC 0 c)ᗮ : Set (HSpace c MeridC)) :=
    Submodule.isClosed_orthogonal _
  have hcl2 : IsClosed ((solenoidalHC 0 c : Submodule ℂ (HSpace c MeridC)) : Set (HSpace c MeridC)) := by
    unfold solenoidalHC
    exact Submodule.isClosed_orthogonal _
  exact ⟨⟨hgφ, hcl.mem_of_tendsto hlimG (Filter.Eventually.of_forall hGmem)⟩,
    ⟨hsφ, hcl2.mem_of_tendsto hlimS (Filter.Eventually.of_forall hSmem)⟩⟩

end UnforcedLeray.Short.PartIIa
