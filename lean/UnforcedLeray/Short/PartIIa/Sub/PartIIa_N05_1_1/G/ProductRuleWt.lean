import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1_1.G.Defs
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1_1.P

/-!
# `Sub/PartII-a_N05_1_1/G/ProductRuleWt`: Proof of `PhaseCutoffProductRuleWt`

Adapts `Sub/PartII-a_N05_1_1/{Weak,Ibp,P}.lean` from `(WeakS, WeakQ, WeakEta)` to
`(WeakS, WeakQWt, WeakEtaWt)` by replacing `cutRep c χ Qw` and `cutRep c χ Ew` with
`cutRep c (fun p => p.1 ^ (-(1/2 : ℝ)) * χ p) Qw` and `... Ew`. On `supp χ ⊆ {σ ≤ s ≤ H₁}`,
`s^{-1/2} ≤ (√σ)⁻¹ ≤ 1 + σ⁻¹ ≤ Γ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open N05_1_1P

namespace N05_1_1G

private def chiWt (χ : Profile → ℝ) (p : Profile) : ℝ :=
  p.1 ^ (-(1 / 2 : ℝ)) * χ p

private theorem inv_sqrt_sigma_le_gamma {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (_hσH : σ ≤ H1) (_hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (_hM : 0 ≤ M) : (Real.sqrt σ)⁻¹ ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
  have hsq : 0 < Real.sqrt σ := Real.sqrt_pos.2 hσ
  have h1 : (Real.sqrt σ)⁻¹ ≤ 1 + σ⁻¹ := by
    by_cases hle : 1 ≤ Real.sqrt σ
    · have : (Real.sqrt σ)⁻¹ ≤ 1⁻¹ := inv_anti₀ zero_lt_one hle
      have : 0 < σ⁻¹ := inv_pos.2 hσ
      linarith
    · have hle' : Real.sqrt σ ≤ 1 := le_of_not_ge hle
      have hσ_le : σ ≤ Real.sqrt σ := by
        calc σ = Real.sqrt σ * Real.sqrt σ := (Real.mul_self_sqrt hσ.le).symm
          _ ≤ 1 * Real.sqrt σ := mul_le_mul_of_nonneg_right hle' hsq.le
          _ = Real.sqrt σ := one_mul _
      have : (Real.sqrt σ)⁻¹ ≤ σ⁻¹ := inv_anti₀ hσ hσ_le
      linarith
  have h2 : 1 + σ⁻¹ ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
    unfold Gamma GammaBox
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  exact h1.trans h2

private theorem rpow_neg_half_eq_inv_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx, ← Real.sqrt_eq_rpow]

private theorem abs_chiWt_le {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (p : Profile) :
    |chiWt χ p| ≤ (Real.sqrt σ)⁻¹ * cNorm8 χ := by
  have hcN := cNorm8_nonneg χ
  have hsq : 0 < Real.sqrt σ := Real.sqrt_pos.2 hσ
  by_cases h0 : χ p = 0
  · simp only [chiWt, h0, mul_zero, abs_zero]
    positivity
  · obtain ⟨hs1, _, _⟩ := hχ.support p h0
    have hp0 : 0 < p.1 := lt_of_lt_of_le hσ hs1
    rw [chiWt, abs_mul, rpow_neg_half_eq_inv_sqrt hp0.le,
      abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    exact mul_le_mul (inv_anti₀ hsq (Real.sqrt_le_sqrt hs1))
      (N05_4Aux.abs_le_cNorm8_of_nearCutoff hc hχ p) (abs_nonneg _) (inv_nonneg.2 hsq.le)

private theorem nice_shalf {c : ℝ} (hc : 0 < c) {ψ : Profile → MeridC} (hψ : Nice c ψ) :
    Nice c (fun p => (p.1 ^ (-(1 / 2 : ℝ))) • ψ p) := by
  obtain ⟨hm, s0, s1, L, C, hs0, hb, hC⟩ := hψ
  have hC0 := nice_C_nonneg hc hC
  have hsq0 : 0 < Real.sqrt s0 := Real.sqrt_pos.2 hs0
  refine ⟨(measurable_fst.pow_const _).smul hm, s0, s1, L, (Real.sqrt s0)⁻¹ * C, hs0,
    fun p hp => hb p (fun h0 => hp (by simp [h0])), fun p hp => ?_⟩
  by_cases h0 : ψ p = 0
  · simp only [h0, smul_zero, norm_zero]; positivity
  · have h1 := (hb p h0).1
    have hp0 : 0 < p.1 := lt_of_lt_of_le hs0 h1.1
    rw [norm_smul, rpow_neg_half_eq_inv_sqrt hp0.le,
      Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    exact mul_le_mul (inv_anti₀ hsq0 (Real.sqrt_le_sqrt h1.1))
      (hC p hp) (norm_nonneg _) (inv_nonneg.2 hsq0.le)

private theorem weakEWt_lam {c : ℝ} {w Ew : HSpace c MeridC} (h : WeakEtaWt c w Ew)
    {φ : Profile → MeridC} (hφ : IsMeridTest c φ) :
    Lam c Ew (fun p => (p.1 ^ (-(1 / 2 : ℝ))) • φ p) = -Lam c w (pdEta φ) := by
  have := h φ hφ
  unfold Lam
  rw [← this]
  congr 1
  funext p
  simp [fromWt]

private theorem weakQWt_lam {c ε : ℝ} {w Qw : HSpace c MeridC} (h : WeakQWt c ε w Qw)
    {φ : Profile → MeridC} (hφ : IsMeridTest c φ) :
    Lam c Qw (fun p => (p.1 ^ (-(1 / 2 : ℝ))) • φ p) =
      -Lam c w (fun p => pdQ φ p - ε • (opK φ p + (2 : ℝ) • φ p)) := by
  have := h φ hφ
  unfold Lam
  rw [← this]
  congr 1
  funext p
  simp [fromWt]

private theorem ibp_eta_wt {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) {w Ew : HSpace c MeridC} (hE : WeakEtaWt c w Ew)
    {φ : Profile → MeridC} (hφ : IsMeridTest c φ) :
    ∫ p, inner ℂ ((fun p => cutRep c (chiWt χ) Ew p + cutRep c (pdEta χ) w p) p)
        (φ p) ∂(cellMeasure c) =
      -∫ p, inner ℂ (cutRep c χ w p) (pdEta φ p) ∂(cellMeasure c) := by
  have hSP := SP.of_cutoff hχ
  have hψ : IsMeridTest c (fun p => χ p • φ p) := mt_smul hSP hφ
  have h2 : IsMeridTest c (fun p => pdEta χ p • φ p) := mt_smul hSP.pdEta hφ
  have h3 : IsMeridTest c (fun p => χ p • pdEta φ p) := mt_smul hSP (mt_pdEta hφ)
  have hweak := weakEWt_lam hE hψ
  have hprod : pdEta (fun p => χ p • φ p) = fun p => χ p • pdEta φ p + pdEta χ p • φ p :=
    funext (pdEta_smul hχ.smooth hφ.smooth)
  rw [hprod, Lam_add hc w (nice_of_mt hc h3) (nice_of_mt hc h2)] at hweak
  have hL : ∫ p, inner ℂ ((fun p => cutRep c (chiWt χ) Ew p + cutRep c (pdEta χ) w p) p)
        (φ p) ∂(cellMeasure c) =
      Lam c Ew (fun p => (p.1 ^ (-(1 / 2 : ℝ))) • (χ p • φ p)) +
        Lam c w (fun p => pdEta χ p • φ p) := by
    unfold Lam
    rw [← integral_add (integrable_inner_periodize hc Ew (nice_shalf hc (nice_of_mt hc hψ)))
      (integrable_inner_periodize hc w (nice_of_mt hc h2))]
    congr 1
    funext p
    simp only [cutRep, chiWt, smul_smul, inner_add_left, inner_rsmul_left, inner_rsmul_right]
  have hR : ∫ p, inner ℂ (cutRep c χ w p) (pdEta φ p) ∂(cellMeasure c) =
      Lam c w (fun p => χ p • pdEta φ p) := by
    unfold Lam
    congr 1
    funext p
    simp [cutRep]
  rw [hL, hR]
  linear_combination hweak

private theorem ibp_q_wt {c σ H1 L1 ε : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) {w Sw Qw Ew : HSpace c MeridC}
    (hS : N05_1_1Org.WeakS c w Sw) (hQ : WeakQWt c ε w Qw) (hE : WeakEtaWt c w Ew)
    {φ : Profile → MeridC} (hφ : IsMeridTest c φ) :
    ∫ p, inner ℂ (dqFromSQE ε (cutRep c χ w)
        (fun p => cutRep c χ Sw p + cutRep c (fun p => p.1 * pdS χ p) w p)
        (fun p => cutRep c (chiWt χ) Qw p + cutRep c
          (fun p => pdQ χ p - ε * (2 * p.1 * pdS χ p + p.2.2 * pdEta χ p)) w p)
        (fun p => cutRep c (chiWt χ) Ew p + cutRep c (pdEta χ) w p) p) (φ p) ∂(cellMeasure c) =
      -∫ p, inner ℂ (cutRep c χ w p) (pdQ φ p) ∂(cellMeasure c) := by
  have hSP := SP.of_cutoff hχ
  have hψ0 : IsMeridTest c (psi0 χ φ) := mt_smul hSP hφ
  have hs : IsMeridTest c (fun p => p.1 • psi0 χ φ p) := mt_smul (SP.fst c) hψ0
  have he : IsMeridTest c (fun p => p.2.2 • psi0 χ φ p) := mt_smul (SP.eta c) hψ0
  have hQ' := weakQWt_lam hQ hψ0
  have hS' := weakS_lam hS hs
  have hE' := weakEWt_lam hE he
  have hS'' : Lam c Sw (psi0 χ φ) = -Lam c w (pdS (fun p => p.1 • psi0 χ φ p)) := by
    rw [← hS']
    refine Lam_congr Sw (fun p hp => ?_)
    have hp1 : 0 < p.1 := hp.1
    simp [smul_smul, hp1.ne']
  have hFQ : IsMeridTest c (fun p => pdQ (psi0 χ φ) p - ε •
      (opK (psi0 χ φ) p + (2 : ℝ) • psi0 χ φ p)) :=
    mt_sub (mt_pdQ hψ0) (mt_smul (SP.const c ε) (mt_add (mt_opK hψ0)
      (mt_smul (SP.const c 2) hψ0)))
  have hFS : IsMeridTest c (pdS (fun p => p.1 • psi0 χ φ p)) := mt_pdS hs
  have hFE : IsMeridTest c (pdEta (fun p => p.2.2 • psi0 χ φ p)) := mt_pdEta he
  have h3 : IsMeridTest c (fun p => χ p • pdQ φ p) := mt_smul hSP (mt_pdQ hφ)
  have h2 : IsMeridTest c (fun p => pdQ χ p • φ p) := mt_smul hSP.pdQ hφ
  have key : Lam c w (fun p => (pdQ (psi0 χ φ) p - ε •
        (opK (psi0 χ φ) p + (2 : ℝ) • psi0 χ φ p)) +
        (2 * ε) • pdS (fun p => p.1 • psi0 χ φ p) p +
        ε • pdEta (fun p => p.2.2 • psi0 χ φ p) p) =
      Lam c w (fun p => (χ p • pdQ φ p + pdQ χ p • φ p) + ε • psi0 χ φ p) := by
    refine Lam_congr w (fun p _ => ?_)
    have e1 : pdQ (psi0 χ φ) p = χ p • pdQ φ p + pdQ χ p • φ p := pdQ_smul hχ.smooth hφ.smooth p
    have e2 : pdS (psi0 χ φ) p = χ p • pdS φ p + pdS χ p • φ p := pdS_smul hχ.smooth hφ.smooth p
    have e3 : pdEta (psi0 χ φ) p = χ p • pdEta φ p + pdEta χ p • φ p :=
      pdEta_smul hχ.smooth hφ.smooth p
    have e4 : pdS (fun p => p.1 • psi0 χ φ p) p = p.1 • pdS (psi0 χ φ) p + (1 : ℝ) • psi0 χ φ p := by
      rw [pdS_smul contDiff_fst hψ0.smooth p, pdS_fst]
    have e5 : pdEta (fun p => p.2.2 • psi0 χ φ p) p =
        p.2.2 • pdEta (psi0 χ φ) p + (1 : ℝ) • psi0 χ φ p := by
      rw [pdEta_smul (g := fun p : Profile => p.2.2)
        (contDiff_snd.comp contDiff_snd : ContDiff ℝ ∞ (fun p : Profile => p.2.2))
        hψ0.smooth p, pdEta_eta]
    simp only [opK, opS]
    simp only [e1, e2, e3, e4, e5]
    simp only [psi0]
    module
  have hn1 := nice_of_mt hc hFQ
  have hn2 := nice_of_mt hc (mt_smul (SP.const c (2 * ε)) hFS)
  have hn3 := nice_of_mt hc (mt_smul (SP.const c ε) hFE)
  rw [Lam_add hc w (nice_of_mt hc (mt_add hFQ (mt_smul (SP.const c (2 * ε)) hFS))) hn3,
    Lam_add hc w hn1 hn2, Lam_smul, Lam_smul,
    Lam_add hc w (nice_of_mt hc (mt_add h3 h2)) (nice_of_mt hc (mt_smul (SP.const c ε) hψ0)),
    Lam_add hc w (nice_of_mt hc h3) (nice_of_mt hc h2), Lam_smul] at key
  have hn4 := nice_shalf hc (nice_of_mt hc hψ0)
  have hn5 := nice_of_mt hc (mt_smul (SP.const c (2 * ε)) hψ0)
  have hn6 : Nice c (fun p => ε • ((p.1 ^ (-(1 / 2 : ℝ))) • (p.2.2 • psi0 χ φ p))) := by
    have hE0 := nice_shalf hc (nice_of_mt hc he)
    have : (fun p => ε • ((p.1 ^ (-(1 / 2 : ℝ))) • (p.2.2 • psi0 χ φ p))) =
        fun p => (p.1 ^ (-(1 / 2 : ℝ))) • (ε • (p.2.2 • psi0 χ φ p)) := by
      funext p; exact smul_comm _ _ _
    rw [this]
    exact nice_shalf hc (nice_of_mt hc (mt_smul (SP.const c ε) he))
  have hn7 := nice_of_mt hc (mt_add (mt_smul (SP.const c ε) hψ0) h2)
  have hL : ∫ p, inner ℂ (dqFromSQE ε (cutRep c χ w)
        (fun p => cutRep c χ Sw p + cutRep c (fun p => p.1 * pdS χ p) w p)
        (fun p => cutRep c (chiWt χ) Qw p + cutRep c
          (fun p => pdQ χ p - ε * (2 * p.1 * pdS χ p + p.2.2 * pdEta χ p)) w p)
        (fun p => cutRep c (chiWt χ) Ew p + cutRep c (pdEta χ) w p) p) (φ p) ∂(cellMeasure c) =
      Lam c Qw (fun p => (p.1 ^ (-(1 / 2 : ℝ))) • psi0 χ φ p) +
        Lam c Sw (fun p => (2 * ε) • psi0 χ φ p) +
        Lam c Ew (fun p => ε • ((p.1 ^ (-(1 / 2 : ℝ))) • (p.2.2 • psi0 χ φ p))) +
        Lam c w (fun p => ε • psi0 χ φ p + pdQ χ p • φ p) := by
    unfold Lam
    have i1 := integrable_inner_periodize hc Qw hn4
    have i2 := integrable_inner_periodize hc Sw hn5
    have i3 := integrable_inner_periodize hc Ew hn6
    have i4 := integrable_inner_periodize hc w hn7
    have I12 : Integrable (fun p =>
        inner ℂ (periodize c (Qw : Profile → MeridC) p) ((p.1 ^ (-(1 / 2 : ℝ))) • psi0 χ φ p) +
        inner ℂ (periodize c (Sw : Profile → MeridC) p) ((2 * ε) • psi0 χ φ p))
        (cellMeasure c) := i1.add i2
    have I123 : Integrable (fun p =>
        inner ℂ (periodize c (Qw : Profile → MeridC) p) ((p.1 ^ (-(1 / 2 : ℝ))) • psi0 χ φ p) +
        inner ℂ (periodize c (Sw : Profile → MeridC) p) ((2 * ε) • psi0 χ φ p) +
        inner ℂ (periodize c (Ew : Profile → MeridC) p)
          (ε • ((p.1 ^ (-(1 / 2 : ℝ))) • (p.2.2 • psi0 χ φ p))))
        (cellMeasure c) := I12.add i3
    rw [← integral_add i1 i2, ← integral_add I12 i3, ← integral_add I123 i4]
    congr 1
    funext p
    simp only [dqFromSQE, cutRep, chiWt, psi0, smul_add, smul_smul, inner_add_left,
      inner_add_right, inner_rsmul_left, inner_rsmul_right]
    push_cast
    ring
  have hR : ∫ p, inner ℂ (cutRep c χ w p) (pdQ φ p) ∂(cellMeasure c) =
      Lam c w (fun p => χ p • pdQ φ p) := by
    unfold Lam
    congr 1
    funext p
    simp [cutRep]
  rw [hL, hR, Lam_smul Sw, Lam_smul Ew,
    Lam_add hc w (nice_of_mt hc (mt_smul (SP.const c ε) hψ0)) (nice_of_mt hc h2), Lam_smul w]
  push_cast at key ⊢
  linear_combination hQ' + (2 * (ε : ℂ)) * hS'' + (ε : ℂ) * hE' - key

/-- Proof of `PhaseCutoffProductRuleWt`. -/
theorem phaseCutoffProductRuleWt : PhaseCutoffProductRuleWt := by
  refine ⟨3, 32, by norm_num, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hM hχ _hχ1 hm B hB ε hε hε1 w Sw Qw Ew hS hQ hE
  set G := Gamma ν c σ H1 L1 M γs χ χ1
  obtain ⟨hG1, hGH, _hGL, hGc, hGa⟩ := gamma_ge χ χ1 hν hc hσ hσH hL1 hγ hM
  have hGσ := inv_sqrt_sigma_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM
  have hcN := cNorm8_nonneg χ
  have hSP := SP.of_cutoff hχ
  let gS : Profile → ℝ := fun p => p.1 * pdS χ p
  let gE : Profile → ℝ := pdEta χ
  let gQ : Profile → ℝ := fun p => pdQ χ p - ε * (2 * p.1 * pdS χ p + p.2.2 * pdEta χ p)
  have hgSP_S : SP c gS := SP.mul (SP.fst c) hSP.pdS
  have hgSP_E : SP c gE := hSP.pdEta
  have hgSP_Q : SP c gQ :=
    SP.sub hSP.pdQ (SP.mul (SP.const c ε) (SP.add (SP.mul (SP.mul (SP.const c 2) (SP.fst c))
      hSP.pdS) (SP.mul (SP.eta c) hSP.pdEta)))
  have hqp_wt : QPeriodic c (chiWt χ) := fun p => by
    show chiWt χ _ = chiWt χ p
    simp [chiWt, hχ.periodic p]
  have box_χ : ∀ p, χ p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := hχ.support
  have box_wt : ∀ p, chiWt χ p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := fun p hp =>
    hχ.support p (fun h0 => hp (by simp [chiWt, h0]))
  have box_S : ∀ p, gS p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := fun p hp =>
    pdS_support hχ (fun h => hp (by simp [gS, h]))
  have box_E : ∀ p, gE p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := fun p hp =>
    pdEta_support hχ hp
  have box_Q : ∀ p, gQ p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := fun p hp => by
    by_contra hbox
    apply hp
    have h1 : pdQ χ p = 0 := by by_contra h; exact hbox (pdQ_support hχ h)
    have h2 : pdS χ p = 0 := by by_contra h; exact hbox (pdS_support hχ h)
    have h3 : pdEta χ p = 0 := by by_contra h; exact hbox (pdEta_support hχ h)
    simp [gQ, h1, h2, h3]
  have hs_of : ∀ {g : Profile → ℝ}, (∀ p, g p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) →
      ∀ p, g p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 := fun h p hp => ⟨(h p hp).1, (h p hp).2.1⟩
  have bχ : ∀ p, |χ p| ≤ cNorm8 χ := N05_4Aux.abs_le_cNorm8_of_nearCutoff hc hχ
  have bwt : ∀ p, |chiWt χ p| ≤ (Real.sqrt σ)⁻¹ * cNorm8 χ := abs_chiWt_le hc hσ hχ
  have bS : ∀ p, |gS p| ≤ H1 * cNorm8 χ := abs_mul_pdS_le hc hσ hσH hχ
  have bE : ∀ p, |gE p| ≤ cNorm8 χ := abs_pdEta_le hc hχ
  have bQ : ∀ p, |gQ p| ≤ (1 + 2 * H1 + L1) * cNorm8 χ := fun p => by
    have e1 := abs_mul_pdS_le hc hσ hσH hχ p
    have e2 := abs_mul_pdEta_le hc hσ hσH hL1 hχ p
    have e3 := abs_pdQ_le hc hχ p
    have e4 : |2 * p.1 * pdS χ p + p.2.2 * pdEta χ p| ≤ 2 * (H1 * cNorm8 χ) + L1 * cNorm8 χ := by
      calc |2 * p.1 * pdS χ p + p.2.2 * pdEta χ p|
          ≤ |2 * p.1 * pdS χ p| + |p.2.2 * pdEta χ p| := abs_add_le _ _
        _ = 2 * |p.1 * pdS χ p| + |p.2.2 * pdEta χ p| := by
            rw [show 2 * p.1 * pdS χ p = 2 * (p.1 * pdS χ p) by ring, abs_mul]; norm_num
        _ ≤ _ := by linarith
    have hε0 : |ε| = ε := abs_of_pos hε
    calc |gQ p| ≤ |pdQ χ p| + |ε * (2 * p.1 * pdS χ p + p.2.2 * pdEta χ p)| := abs_sub _ _
      _ = |pdQ χ p| + ε * |2 * p.1 * pdS χ p + p.2.2 * pdEta χ p| := by rw [abs_mul, hε0]
      _ ≤ cNorm8 χ + 1 * (2 * (H1 * cNorm8 χ) + L1 * cNorm8 χ) := by
          have : ε * |2 * p.1 * pdS χ p + p.2.2 * pdEta χ p| ≤
              1 * (2 * (H1 * cNorm8 χ) + L1 * cNorm8 χ) :=
            mul_le_mul hε1 e4 (abs_nonneg _) zero_le_one
          linarith
      _ = (1 + 2 * H1 + L1) * cNorm8 χ := by ring
  have hmwt : Measurable (chiWt χ) := (measurable_fst.pow_const _).mul hm
  have hmS : Measurable gS :=
    measurable_fst.mul ((hχ.smooth.continuous_fderiv (by simp)).clm_apply
      continuous_const).measurable
  have hmE : Measurable gE :=
    ((hχ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).measurable
  have hmQ : Measurable gQ := hgSP_Q.1.continuous.measurable
  have mχw := memLp_cutRep hc hσ hσH (hs_of box_χ) bχ hm w
  have mχS := memLp_cutRep hc hσ hσH (hs_of box_χ) bχ hm Sw
  have mχQ := memLp_cutRep hc hσ hσH (hs_of box_wt) bwt hmwt Qw
  have mχE := memLp_cutRep hc hσ hσH (hs_of box_wt) bwt hmwt Ew
  have mSw := memLp_cutRep hc hσ hσH (hs_of box_S) bS hmS w
  have mEw := memLp_cutRep hc hσ hσH (hs_of box_E) bE hmE w
  have mQw := memLp_cutRep hc hσ hσH (hs_of box_Q) bQ hmQ w
  refine ⟨cutRep c χ w, fun p => cutRep c χ Sw p + cutRep c gS w p,
    fun p => cutRep c (chiWt χ) Qw p + cutRep c gQ w p,
    fun p => cutRep c (chiWt χ) Ew p + cutRep c gE w p, ?_, ?_⟩
  · refine ⟨N05_4Aux.flatStressCutRep_ae_eq hc χ hm hB w, qp_cutRep hc hχ.periodic w,
      qp_add (qp_cutRep hc hχ.periodic Sw) (qp_cutRep hc hgSP_S.2 w),
      qp_add (qp_cutRep hc hqp_wt Qw) (qp_cutRep hc hgSP_Q.2 w),
      qp_add (qp_cutRep hc hqp_wt Ew) (qp_cutRep hc hgSP_E.2 w),
      supp_cutRep box_χ w,
      supp_add (supp_cutRep box_χ Sw) (supp_cutRep box_S w),
      supp_add (supp_cutRep box_wt Qw) (supp_cutRep box_Q w),
      supp_add (supp_cutRep box_wt Ew) (supp_cutRep box_E w),
      mχw, mχS.add mSw, mχQ.add mQw, mχE.add mEw, ?_, ?_, ?_⟩
    · intro φ hφ
      exact ibp_s hc hχ hS hφ
    · intro φ hφ
      exact ibp_q_wt hc hχ hS hQ hE hφ
    · intro φ hφ
      exact ibp_eta_wt hc hχ hE hφ
  · have n1 := cellL2Norm_cutRep_le_mul hc hσ hσH (hs_of box_χ) bχ hm w
    have n2 := cellL2Norm_cutRep_le_mul hc hσ hσH (hs_of box_χ) bχ hm Sw
    have n3 := cellL2Norm_cutRep_le_mul hc hσ hσH (hs_of box_wt) bwt hmwt Qw
    have n4 := cellL2Norm_cutRep_le_mul hc hσ hσH (hs_of box_wt) bwt hmwt Ew
    have n5 := cellL2Norm_cutRep_le_mul hc hσ hσH (hs_of box_S) bS hmS w
    have n6 := cellL2Norm_cutRep_le_mul hc hσ hσH (hs_of box_E) bE hmE w
    have n7 := cellL2Norm_cutRep_le_mul hc hσ hσH (hs_of box_Q) bQ hmQ w
    have t2 := cellL2Norm_add_le mχS mSw
    have t3 := cellL2Norm_add_le mχQ mQw
    have t4 := cellL2Norm_add_le mχE mEw
    have hw := norm_nonneg w
    have hSw := norm_nonneg Sw
    have hQw := norm_nonneg Qw
    have hEw := norm_nonneg Ew
    set X := cNorm8 χ
    have ha : 1 + H1 ≤ G := hGa
    have hH0 : 0 < H1 := lt_of_lt_of_le hσ hσH
    have hG0 : 0 ≤ G := by linarith
    have k1 : (1 + H1) * X ≤ G * G := mul_le_mul ha hGc hcN hG0
    have kwt : (1 + H1) * ((Real.sqrt σ)⁻¹ * X) ≤ G * (G * G) :=
      mul_le_mul ha (mul_le_mul hGσ hGc hcN hG0)
        (mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) hcN) hG0
    have k2 : (1 + H1) * (H1 * X) ≤ G * (G * G) :=
      mul_le_mul ha (mul_le_mul hGH hGc hcN hG0) (by positivity) hG0
    have hq : 1 + 2 * H1 + L1 ≤ 4 * G := by
      obtain ⟨_, _, hGL, _, _⟩ := gamma_ge χ χ1 hν hc hσ hσH hL1 hγ hM
      linarith
    have k3 : (1 + H1) * ((1 + 2 * H1 + L1) * X) ≤ G * ((4 * G) * G) :=
      mul_le_mul ha (mul_le_mul hq hGc hcN (by linarith)) (by positivity) hG0
    have hG2 : G * G ≤ G * (G * G) := by nlinarith
    have hc1 : (1 + H1) * X * ‖w‖ ≤ G * G * ‖w‖ := mul_le_mul_of_nonneg_right k1 hw
    have hc2 : (1 + H1) * X * ‖Sw‖ ≤ G * G * ‖Sw‖ := mul_le_mul_of_nonneg_right k1 hSw
    have hc3 : (1 + H1) * ((Real.sqrt σ)⁻¹ * X) * ‖Qw‖ ≤ G * (G * G) * ‖Qw‖ :=
      mul_le_mul_of_nonneg_right kwt hQw
    have hc4 : (1 + H1) * ((Real.sqrt σ)⁻¹ * X) * ‖Ew‖ ≤ G * (G * G) * ‖Ew‖ :=
      mul_le_mul_of_nonneg_right kwt hEw
    have hc5 : (1 + H1) * (H1 * X) * ‖w‖ ≤ G * (G * G) * ‖w‖ :=
      mul_le_mul_of_nonneg_right k2 hw
    have hc7 : (1 + H1) * ((1 + 2 * H1 + L1) * X) * ‖w‖ ≤ G * ((4 * G) * G) * ‖w‖ :=
      mul_le_mul_of_nonneg_right k3 hw
    have g3 : 0 ≤ G * (G * G) := by positivity
    have e1 : G * G * ‖w‖ ≤ G * (G * G) * ‖w‖ := mul_le_mul_of_nonneg_right hG2 hw
    have e2 : G * G * ‖Sw‖ ≤ G * (G * G) * ‖Sw‖ := mul_le_mul_of_nonneg_right hG2 hSw
    have : G ^ 3 = G * (G * G) := by ring
    rw [this]
    nlinarith [mul_nonneg g3 hw, mul_nonneg g3 hSw, mul_nonneg g3 hQw, mul_nonneg g3 hEw]

end N05_1_1G

end UnforcedLeray.Short.PartIIa
