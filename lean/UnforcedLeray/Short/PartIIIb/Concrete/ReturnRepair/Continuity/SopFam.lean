import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_cont_S
import UnforcedLeray.Short.PartIIa.StatementsNear
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas
import UnforcedLeray.Units.B0223

/-!
# `PartIII-b:C/cont/S`: the complex stress maps form a norm-continuous family (source 1556-1583,
1675-1690, 3888-3890)

Source of record: `the November 2 reference manuscript` (73 pages).

Existence of a stress map at each real `μ > -1/4` comes from `NearStressMapExists` (with
`M = ‖μ‖`, `γ_s = μ + 1/4`), as in `stressTransportExists_of`.  Continuity on `(-1/4, ∞)` comes from
the resolvent identity `StressMapResolvent`, which gives
`S μ - S μ₀ = (μ₀ - μ) • (R^{vec}(μ) ∘ S μ₀)`, and `‖R^{vec}(μ)‖ ≤ (μ + 1/4)⁻¹`
(`B0223.norm_RepsVec_le`).  Uniqueness (`StressMapUnique`) is not needed for this direction.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The stress maps `S'_μ` of `T_ε(μ)` form a norm-continuous family** on `μ > -1/4`, from the
existence of stress maps (`NearStressMapExists`), uniqueness (`StressMapUnique`, not needed here)
and the resolvent identity (`StressMapResolvent`). -/
theorem stressMapFamilyCont_of (hN : UnforcedLeray.Short.PartIIa.NearStressMapExists)
    (hUn : UnforcedLeray.Short.PartIIIb.NearInst.Masked.StressMapUnique) (hRes : StressMapResolvent) :
    StressMapFamilyCont := by
  unfold StressMapFamilyCont
  intro p hε1 hP1
  -- existence of a stress map at each real `μ > -1/4`
  have hex : ∀ μ : ℝ, ∃ S : UnforcedLeray.Short.PartIIa.HTSpace p.c →L[ℂ]
      UnforcedLeray.B0220.HSpace p.c UnforcedLeray.B0223.MeridC,
      -(1 / 4 : ℝ) < μ → UnforcedLeray.Short.PartIIa.IsStressMap p.c p.ε
        (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ)) S := by
    intro μ
    by_cases hμ : -(1 / 4 : ℝ) < μ
    · obtain ⟨C, _, hNS⟩ := hN
      have hμr : μ + 1 / 4 ≤ (μ : ℂ).re + 1 / 4 := by rw [Complex.ofReal_re]
      obtain ⟨⟨S', hS', -⟩, -⟩ := hNS p.ν p.c ‖(μ : ℂ)‖ (μ + 1 / 4) p.ν_pos p.c_pos (by linarith)
        p.ε p.ε_pos hε1 p.period rfl hP1 (μ : ℂ) le_rfl hμr
      exact ⟨S', fun _ => hS'⟩
    · exact ⟨0, fun h => absurd h hμ⟩
  choose S hS using hex
  refine ⟨S, ?_, fun μ hμ => hS μ hμ⟩
  -- norm continuity on the window
  intro μ0 hμ0
  have hμ0' : -(1 / 4 : ℝ) < μ0 := hμ0
  have ha : 0 < μ0 + 1 / 4 := by linarith
  -- local Lipschitz bound with constant `(2 / (μ0 + 1/4)) * ‖S μ0‖`
  have hbound : ∀ μ : ℝ, μ0 - (μ0 + 1 / 4) / 2 < μ → μ < μ0 + (μ0 + 1 / 4) / 2 →
      ‖S μ - S μ0‖ ≤ (2 / (μ0 + 1 / 4)) * ‖S μ0‖ * |μ0 - μ| := by
    intro μ h1 h2
    have hμ : -(1 / 4 : ℝ) < μ := by linarith
    have hlow : (μ0 + 1 / 4) / 2 ≤ μ + 1 / 4 := by linarith
    have hres := hRes p.ν p.ε p.c p.period p.ν_pos p.ε_pos p.c_pos rfl μ μ0 hμ hμ0' (S μ) (S μ0)
      (hS μ hμ) (hS μ0 hμ0')
    have hγ : 0 < (μ : ℂ).re + 1 / 4 := by rw [Complex.ofReal_re]; linarith
    have hR : ‖UnforcedLeray.B0223.RepsVec (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ)‖ ≤ (μ + 1 / 4)⁻¹ := by
      have := UnforcedLeray.B0223.norm_RepsVec_le (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl hγ
      rwa [Complex.ofReal_re] at this
    have h1' : ‖((μ0 - μ : ℝ) : ℂ)‖ = |μ0 - μ| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have h2' : ‖(UnforcedLeray.B0223.RepsVec (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ)).comp (S μ0)‖ ≤
        ‖UnforcedLeray.B0223.RepsVec (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ)‖ * ‖S μ0‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    have h3 : (μ + 1 / 4)⁻¹ ≤ 2 / (μ0 + 1 / 4) := by
      rw [← inv_div (μ0 + 1 / 4) 2]
      exact inv_anti₀ (by linarith) hlow
    calc ‖S μ - S μ0‖
        = ‖((μ0 - μ : ℝ) : ℂ) • ((UnforcedLeray.B0223.RepsVec (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ)).comp
            (S μ0))‖ := by rw [hres]
      _ = |μ0 - μ| * ‖(UnforcedLeray.B0223.RepsVec (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ)).comp
            (S μ0)‖ := by rw [norm_smul, h1']
      _ ≤ |μ0 - μ| * (‖UnforcedLeray.B0223.RepsVec (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ)‖ * ‖S μ0‖) :=
          mul_le_mul_of_nonneg_left h2' (abs_nonneg _)
      _ ≤ |μ0 - μ| * ((2 / (μ0 + 1 / 4)) * ‖S μ0‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hR.trans h3) (norm_nonneg _))
            (abs_nonneg _)
      _ = (2 / (μ0 + 1 / 4)) * ‖S μ0‖ * |μ0 - μ| := by ring
  have hev : ∀ᶠ μ in 𝓝 μ0, ‖S μ - S μ0‖ ≤ (2 / (μ0 + 1 / 4)) * ‖S μ0‖ * |μ0 - μ| := by
    filter_upwards [Ioo_mem_nhds (a := μ0 - (μ0 + 1 / 4) / 2) (b := μ0 + (μ0 + 1 / 4) / 2)
      (by linarith) (by linarith)] with μ hμ
    exact hbound μ hμ.1 hμ.2
  have hg : Tendsto (fun μ : ℝ => (2 / (μ0 + 1 / 4)) * ‖S μ0‖ * |μ0 - μ|) (𝓝 μ0) (𝓝 0) := by
    have hc : Continuous (fun μ : ℝ => (2 / (μ0 + 1 / 4)) * ‖S μ0‖ * |μ0 - μ|) := by fun_prop
    simpa using hc.tendsto μ0
  have hgW : Tendsto (fun μ : ℝ => (2 / (μ0 + 1 / 4)) * ‖S μ0‖ * |μ0 - μ|)
      (𝓝[Ioi (-(1 / 4 : ℝ))] μ0) (𝓝 0) :=
    hg.mono_left nhdsWithin_le_nhds
  have hevW : ∀ᶠ μ in 𝓝[Ioi (-(1 / 4 : ℝ))] μ0,
      ‖S μ - S μ0‖ ≤ (2 / (μ0 + 1 / 4)) * ‖S μ0‖ * |μ0 - μ| :=
    eventually_nhdsWithin_of_eventually_nhds hev
  unfold ContinuousWithinAt
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hevW hgW

end UnforcedLeray.Short.PartIIIb.Concrete
