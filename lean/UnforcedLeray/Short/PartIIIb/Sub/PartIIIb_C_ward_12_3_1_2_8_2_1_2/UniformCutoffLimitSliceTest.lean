import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.Statements
import UnforcedLeray.Short.PartIIa.Tasks.F05bSliceContOfDecay
import UnforcedLeray.Short.PartIIb.Tasks.OrdRelUnique.CutoffCrossBound

/-!
# `uniformCutoffLimitSliceTest`: a cut-off tail limit is an `L^{q₀'}` slice test

Proves `UniformCutoffLimitSliceTest` (`Statements.lean`), source lines 1446-1455 (tails in `Y_{r'}`).
For `|y| ≤ (n+1)/2` the cut-off factor is one, so the hypothesis forces `Θ' = Θₙ` there. Hence `Θ'` is
`P`-periodic and continuous; its decay is that of `Θ₀` plus the tail bound; and
`PartIIa.sliceContOfDecay` applies with `s = 2`, since `2 · 11/7 > 3`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.SolApprox

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.RieszLp
open UnforcedLeray.Cons.C03.Concrete
open NavierStokesR3.ComparisonCutoffs

theorem ucl_powWeight_two (y : Space) : powWeight 2 y = ((1 + ‖y‖) ^ 2)⁻¹ := by
  unfold powWeight
  rw [Real.rpow_neg (by positivity), Real.rpow_two]

theorem uniformCutoffLimitSliceTest :
    UnforcedLeray.Short.PartIIIb.Concrete.SolApprox.UniformCutoffLimitSliceTest := by
  intro P hPf Θ Θ' K hΘ hbd
  have hP : (0 : ℝ) < P := hPf.out
  -- on `|y| ≤ (n+1)/2` the limit agrees with `Θₙ`
  have hloc : ∀ (n : ℕ) (τ : ℝ) (y : Space), ‖y‖ ≤ ((n : ℝ) + 1) / 2 → Θ' (τ, y) = Θ n (τ, y) := by
    intro n τ y hy
    have hc : cutoff (((n : ℝ) + 1) / 2) y = 1 := cutoff_eq_one (by positivity) hy
    have h := hbd n τ y
    rw [hc, sub_self, zero_mul, mul_zero, norm_le_zero_iff, sub_eq_zero] at h
    exact h.symm
  have hcover : ∀ y : Space, ‖y‖ ≤ (((⌈2 * ‖y‖⌉₊ : ℕ) : ℝ) + 1) / 2 := by
    intro y
    have := Nat.le_ceil (2 * ‖y‖)
    linarith
  -- periodicity
  have hper : ∀ τ y, Θ' (τ + P, y) = Θ' (τ, y) := by
    intro τ y
    rw [hloc _ (τ + P) y (hcover y), hloc _ τ y (hcover y), (hΘ _).periodic τ y]
  -- continuity
  have hcont : Continuous Θ' := by
    rw [continuous_iff_continuousAt]
    intro z0
    have hopen : IsOpen {z : ℝ × Space | ‖z.2‖ < (((⌈2 * ‖z0.2‖⌉₊ : ℕ) : ℝ) + 1) / 2} :=
      isOpen_lt (continuous_norm.comp continuous_snd) continuous_const
    have hz0 : z0 ∈ {z : ℝ × Space | ‖z.2‖ < (((⌈2 * ‖z0.2‖⌉₊ : ℕ) : ℝ) + 1) / 2} := by
      show ‖z0.2‖ < _
      have := Nat.le_ceil (2 * ‖z0.2‖)
      linarith
    have hEq : Θ (⌈2 * ‖z0.2‖⌉₊) =ᶠ[𝓝 z0] Θ' :=
      Filter.eventually_of_mem (hopen.mem_nhds hz0) (fun z hz => by
        have hz' : ‖z.2‖ ≤ (((⌈2 * ‖z0.2‖⌉₊ : ℕ) : ℝ) + 1) / 2 := le_of_lt hz
        exact (hloc _ z.1 z.2 hz').symm)
    exact ((hΘ (⌈2 * ‖z0.2‖⌉₊)).smooth.continuous.continuousAt).congr hEq
  -- a uniform bound for `Θ₀`
  obtain ⟨ρ, hρ⟩ := (hΘ 0).bounded_support
  have hK : IsCompact (Icc (0 : ℝ) P ×ˢ closedBall (0 : Space) (max ρ 0)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn (hΘ 0).smooth.continuous.continuousOn
  have hΘ0bd : ∀ τ y, ‖Θ 0 (τ, y)‖ ≤ max C₀ 0 * (1 + max ρ 0) ^ 2 * powWeight 2 y := by
    intro τ y
    have hpw : 0 ≤ powWeight 2 y := powWeight_nonneg _ _
    by_cases hy : max ρ 0 < ‖y‖
    · rw [hρ τ y (lt_of_le_of_lt (le_max_left ρ 0) hy), norm_zero]
      exact mul_nonneg (mul_nonneg (le_max_right _ _) (by positivity)) hpw
    · have hy' : ‖y‖ ≤ max ρ 0 := not_lt.mp hy
      obtain ⟨τ', hτ', heq⟩ :=
        (show Function.Periodic (fun τ => Θ 0 (τ, y)) P from fun τ => (hΘ 0).periodic τ y).exists_mem_Ico₀
          hP τ
      have hmem : (τ', y) ∈ Icc (0 : ℝ) P ×ˢ closedBall (0 : Space) (max ρ 0) :=
        ⟨⟨hτ'.1, hτ'.2.le⟩, by simpa using hy'⟩
      have hb := hC₀ (τ', y) hmem
      have hkey : 1 ≤ (1 + max ρ 0) ^ 2 * powWeight 2 y := by
        rw [ucl_powWeight_two, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
        have h2 : (1 + ‖y‖) ^ 2 ≤ (1 + max ρ 0) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 2
        rw [one_mul]
        exact h2
      calc ‖Θ 0 (τ, y)‖ = ‖Θ 0 (τ', y)‖ := by rw [heq]
        _ ≤ C₀ := hb
        _ ≤ max C₀ 0 := le_max_left _ _
        _ = max C₀ 0 * 1 := (mul_one _).symm
        _ ≤ max C₀ 0 * ((1 + max ρ 0) ^ 2 * powWeight 2 y) :=
          mul_le_mul_of_nonneg_left hkey (le_max_right _ _)
        _ = max C₀ 0 * (1 + max ρ 0) ^ 2 * powWeight 2 y := by ring
  -- global decay
  have hkeyK : ∀ (t : ℝ) (y : Space), 0 ≤ t → t ≤ powWeight 2 y →
      K * t ≤ max K 0 * powWeight 2 y := fun t y ht0 ht1 =>
    (mul_le_mul_of_nonneg_right (le_max_left _ _) ht0).trans
      (mul_le_mul_of_nonneg_left ht1 (le_max_right _ _))
  have hbound : ∀ τ y, ‖Θ' (τ, y)‖ ≤
      (max C₀ 0 * (1 + max ρ 0) ^ 2 + max K 0) * powWeight 2 y := by
    intro τ y
    have h1 := hΘ0bd τ y
    have h2 := hbd 0 τ y
    have hc0 : 0 ≤ cutoff (((((0 : ℕ) : ℝ)) + 1) / 2) y := cutoff_nonneg _ _
    have hc1 : cutoff (((((0 : ℕ) : ℝ)) + 1) / 2) y ≤ 1 := cutoff_le_one _ _
    have ht1 : (1 - cutoff (((((0 : ℕ) : ℝ)) + 1) / 2) y) * powWeight 2 y ≤ powWeight 2 y :=
      mul_le_of_le_one_left (powWeight_nonneg _ _) (by linarith)
    have ht0 : 0 ≤ (1 - cutoff (((((0 : ℕ) : ℝ)) + 1) / 2) y) * powWeight 2 y :=
      mul_nonneg (by linarith) (powWeight_nonneg _ _)
    have h3 := hkeyK _ y ht0 ht1
    have htri : ‖Θ' (τ, y)‖ ≤ ‖Θ 0 (τ, y)‖ + ‖Θ 0 (τ, y) - Θ' (τ, y)‖ := by
      calc ‖Θ' (τ, y)‖ = ‖Θ 0 (τ, y) - (Θ 0 (τ, y) - Θ' (τ, y))‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    calc ‖Θ' (τ, y)‖ ≤ ‖Θ 0 (τ, y)‖ + ‖Θ 0 (τ, y) - Θ' (τ, y)‖ := htri
      _ ≤ max C₀ 0 * (1 + max ρ 0) ^ 2 * powWeight 2 y + max K 0 * powWeight 2 y :=
        add_le_add h1 (h2.trans h3)
      _ = (max C₀ 0 * (1 + max ρ 0) ^ 2 + max K 0) * powWeight 2 y := by ring
  -- assemble the slice test
  unfold IsSliceTest
  refine ⟨hper, ?_⟩
  have hne : conjExp q0E ≠ ⊤ := by
    rw [UnforcedLeray.Short.IIb.cutoffCrossBound_conjExp_eq]
    exact ENNReal.ofReal_ne_top
  have h3 : 3 < 2 * (conjExp q0E).toReal := by
    rw [UnforcedLeray.Short.IIb.cutoffCrossBound_conjExp_eq, ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  exact UnforcedLeray.Short.PartIIa.sliceContOfDecay (conjExp q0E) hne 2
    (max C₀ 0 * (1 + max ρ 0) ^ 2 + max K 0) h3 Θ' hcont hbound

end UnforcedLeray.Short.PartIIIb.Concrete.SolApprox
