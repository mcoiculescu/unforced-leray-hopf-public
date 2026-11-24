import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.Mollifier.L2

/-!
# Part III-a, `PartIII-a:T18/3/1/3/1`: strong `L²(cell)` convergence of the mollifier

Source of record: `the November 2 reference manuscript` lines 3427-3440 and
3541-3552. `J_k g → g` almost everywhere on the cell (Lebesgue differentiation through
`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`). Together with the contraction
`‖J_k g‖ ≤ ‖g‖` this upgrades to strong `L²` convergence: `2|J_k g|² + 2|g|² - |J_k g - g|²` is
nonnegative and converges a.e. to `4|g|²`, and Fatou applies.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIIa

theorem lmJs_ae_tendsto {c : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) :
    ∀ᵐ x ∂(volume.restrict (B0579.cell c)), Tendsto (fun k : ℕ => lmJs c k g x) atTop (𝓝 (g x)) := by
  have hloc := lmExt_locallyIntegrable hc hg
  have hrOut : Tendsto (fun k : ℕ => (lmBump c k).rOut) atTop (𝓝 0) := by
    simp only [lmBump_rOut]
    exact tendsto_const_div_atTop_nhds_zero_nat (lmDelta c) |>.comp (tendsto_add_atTop_nat 1) |>.congr
      fun k => by simp
  have hratio : ∀ᶠ k : ℕ in atTop, (lmBump c k).rOut ≤ 2 * (lmBump c k).rIn := by
    refine Eventually.of_forall fun k => ?_
    simp only [lmBump_rOut, lmBump_rIn]
    have hδ := lmDelta_pos c
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume) hrOut hratio
    hloc
  filter_upwards [ae_restrict_of_ae h, ae_restrict_mem (B0579.measurableSet_cell c)] with x hx hmem
  rw [lmExt_of_mem hc g hmem] at hx
  refine hx.congr fun k => ?_
  rw [lmJs_eq_convolution hc k g]
  rfl

/-- Fatou's lemma in the form used here. -/
theorem lm_fatou {α : Type} [MeasurableSpace α] {μ : Measure α} {H : ℕ → α → ℝ} {h : α → ℝ}
    (hH0 : ∀ k, 0 ≤ᵐ[μ] H k) (hHi : ∀ k, Integrable (H k) μ) (hi : Integrable h μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun k => H k x) atTop (𝓝 (h x))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∫ x, h x ∂μ - ε ≤ ∫ x, H k x ∂μ := by
  have hH0all : ∀ᵐ x ∂μ, ∀ k, 0 ≤ H k x := ae_all_iff.2 hH0
  have hh0 : ∀ᵐ x ∂μ, 0 ≤ h x := by
    filter_upwards [hae, hH0all] with x hx hx0
    exact ge_of_tendsto' hx hx0
  have hmin : ∀ k, Integrable (fun x => min (H k x) (h x)) μ := fun k =>
    (hHi k).inf hi
  have hconv : Tendsto (fun k => ∫ x, min (H k x) (h x) ∂μ) atTop (𝓝 (∫ x, h x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence h (fun k => (hmin k).1) hi ?_ ?_
    · intro k
      filter_upwards [hH0all, hh0] with x hx hx0
      rw [Real.norm_of_nonneg (le_min (hx k) hx0)]
      exact min_le_right _ _
    · filter_upwards [hae] with x hx
      have := hx.min (tendsto_const_nhds (x := h x))
      simpa using this
  have hev := (tendsto_order.1 hconv).1 (∫ x, h x ∂μ - ε) (by linarith)
  filter_upwards [hev] with k hk
  exact hk.le.trans (integral_mono (hmin k) (hHi k) fun x => min_le_left _ _)

/-- Almost everywhere convergence with `limsup ‖G_k‖ ≤ ‖g‖` gives strong `L²` convergence. -/
theorem lm_l2_of_ae {α : Type} [MeasurableSpace α] {μ : Measure α} {G : ℕ → α → ℂ} {g : α → ℂ}
    (hg : MemLp g 2 μ) (hG : ∀ k, MemLp (G k) 2 μ)
    (hle : ∀ k, ∫ x, ‖G k x‖ ^ 2 ∂μ ≤ ∫ x, ‖g x‖ ^ 2 ∂μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun k => G k x) atTop (𝓝 (g x))) :
    Tendsto (fun k => ∫ x, ‖G k x - g x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hg2 : Integrable (fun x => ‖g x‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hg.1).1 hg
  have hG2 : ∀ k, Integrable (fun x => ‖G k x‖ ^ 2) μ := fun k =>
    (memLp_two_iff_integrable_sq_norm (hG k).1).1 (hG k)
  have hD2 : ∀ k, Integrable (fun x => ‖G k x - g x‖ ^ 2) μ := fun k =>
    (memLp_two_iff_integrable_sq_norm ((hG k).sub hg).1).1 ((hG k).sub hg)
  have hH0 : ∀ k, 0 ≤ᵐ[μ] fun x => 2 * ‖G k x‖ ^ 2 + 2 * ‖g x‖ ^ 2 - ‖G k x - g x‖ ^ 2 := fun k =>
    ae_of_all _ fun x => by
      have h1 := norm_sub_le (G k x) (g x)
      have h2 := norm_nonneg (G k x - g x)
      have h3 := norm_nonneg (G k x)
      have h4 := norm_nonneg (g x)
      show 0 ≤ 2 * ‖G k x‖ ^ 2 + 2 * ‖g x‖ ^ 2 - ‖G k x - g x‖ ^ 2
      nlinarith [sq_nonneg (‖G k x‖ - ‖g x‖)]
  have hHi : ∀ k, Integrable (fun x => 2 * ‖G k x‖ ^ 2 + 2 * ‖g x‖ ^ 2 - ‖G k x - g x‖ ^ 2) μ :=
    fun k => (((hG2 k).const_mul 2).add (hg2.const_mul 2)).sub (hD2 k)
  have hi : Integrable (fun x => 4 * ‖g x‖ ^ 2) μ := hg2.const_mul 4
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun k => 2 * ‖G k x‖ ^ 2 + 2 * ‖g x‖ ^ 2 - ‖G k x - g x‖ ^ 2) atTop
      (𝓝 (4 * ‖g x‖ ^ 2)) := by
    filter_upwards [hae] with x hx
    have h1 : Tendsto (fun k => ‖G k x‖ ^ 2) atTop (𝓝 (‖g x‖ ^ 2)) := hx.norm.pow 2
    have h2 : Tendsto (fun k => ‖G k x - g x‖ ^ 2) atTop (𝓝 0) := by
      have h3 : Tendsto (fun k => G k x - g x) atTop (𝓝 (g x - g x)) := hx.sub tendsto_const_nhds
      simpa using h3.norm.pow 2
    have h4 := ((h1.const_mul 2).add_const (2 * ‖g x‖ ^ 2)).sub h2
    have h5 : 2 * ‖g x‖ ^ 2 + 2 * ‖g x‖ ^ 2 - 0 = 4 * ‖g x‖ ^ 2 := by ring
    rwa [h5] at h4
  have hnn : ∀ k, 0 ≤ ∫ x, ‖G k x - g x‖ ^ 2 ∂μ := fun k => integral_nonneg fun x => sq_nonneg _
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun k => lt_of_lt_of_le ha (hnn k),
    fun a ha => ?_⟩
  have hev := lm_fatou hH0 hHi hi hlim (half_pos ha)
  filter_upwards [hev] with k hk
  have hsplit : ∫ x, (2 * ‖G k x‖ ^ 2 + 2 * ‖g x‖ ^ 2 - ‖G k x - g x‖ ^ 2) ∂μ =
      2 * ∫ x, ‖G k x‖ ^ 2 ∂μ + 2 * ∫ x, ‖g x‖ ^ 2 ∂μ - ∫ x, ‖G k x - g x‖ ^ 2 ∂μ := by
    have hadd : Integrable (fun x => 2 * ‖G k x‖ ^ 2 + 2 * ‖g x‖ ^ 2) μ :=
      ((hG2 k).const_mul 2).add (hg2.const_mul 2)
    rw [integral_sub hadd (hD2 k), integral_add ((hG2 k).const_mul 2) (hg2.const_mul 2),
      integral_const_mul, integral_const_mul]
  have hfour : ∫ x, 4 * ‖g x‖ ^ 2 ∂μ = 4 * ∫ x, ‖g x‖ ^ 2 ∂μ := integral_const_mul _ _
  rw [hsplit, hfour] at hk
  have := hle k
  linarith

theorem lmJs_tendsto {c : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) :
    Tendsto (fun k : ℕ => ∫ x in B0579.cell c, ‖lmJs c k g x - g x‖ ^ 2) atTop (𝓝 0) :=
  lm_l2_of_ae hg (fun k => lmJs_memLp hc k hg) (fun k => lmJs_contr hc k hg) (lmJs_ae_tendsto hc hg)

end UnforcedLeray.Short.IIIa
