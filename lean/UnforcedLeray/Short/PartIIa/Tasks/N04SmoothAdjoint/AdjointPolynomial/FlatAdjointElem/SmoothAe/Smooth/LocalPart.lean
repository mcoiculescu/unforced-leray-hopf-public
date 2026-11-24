import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.Gen1Bound.SliceDerivs

/-!
# Smoothness of `flatAdjointRep` for Spatially Compactly Supported Profiles (`LocalPart`)

Proves `ContDiffOn ℝ ∞ (flatAdjointRep ν μ w) {p : Profile | 0 < p.1}` for any smooth profile `w`
supported in an age band `s ∈ [σ, H1]` and a bounded planar ball `‖y‖ ≤ R`, by induction on the
differentiation order using `FlatAdjointElemAux.hasFDerivAt_causalAdjointRep`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.FlatAdjointSmoothAux

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0224 UnforcedLeray.B0225
  UnforcedLeray.B0226
open UnforcedLeray.Short.PartIIa.FlatAdjointElemAux

/-- Smooth profile supported in the age band `[σ, H1]` and a planar ball `‖q.2‖ ≤ R`. -/
structure IsCompactBand (σ H1 : ℝ) (w : Profile → MeridC) : Prop where
  smooth : ContDiff ℝ ∞ w
  support_s : ∀ q : Profile, q.1 < σ ∨ H1 < q.1 → w q = 0
  support_y : ∃ R : ℝ, ∀ q : Profile, R < ‖q.2‖ → w q = 0

theorem support_y_fderiv_apply {R : ℝ} {w : Profile → MeridC}
    (hw : ∀ p : Profile, R < ‖p.2‖ → w p = 0) (v : Profile) :
    ∀ p : Profile, R < ‖p.2‖ → fderiv ℝ w p v = 0 := by
  intro p hp
  have hopen : IsOpen {q : Profile | R < ‖q.2‖} :=
    isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
  have hev : w =ᶠ[𝓝 p] fun _ => (0 : MeridC) := by
    filter_upwards [hopen.mem_nhds hp] with q hq
    exact hw q hq
  rw [hev.fderiv_eq]
  simp

theorem IsCompactBand.bdd {σ H1 : ℝ} {w : Profile → MeridC} (hw : IsCompactBand σ H1 w) :
    ∃ M : ℝ, ∀ q : Profile, ‖w q‖ ≤ M := by
  obtain ⟨R, hR⟩ := hw.support_y
  set K : Set Profile := Icc σ H1 ×ˢ Metric.closedBall (0 : ℝ × ℝ) (max R 0)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hw.smooth.continuous.continuousOn
  refine ⟨max C 0, fun q => ?_⟩
  by_cases hq : q ∈ K
  · exact (hC q hq).trans (le_max_left C 0)
  · have hw0 : w q = 0 := by
      by_cases hs : q.1 ∈ Icc σ H1
      · have hy : q.2 ∉ Metric.closedBall (0 : ℝ × ℝ) (max R 0) := fun hy => hq ⟨hs, hy⟩
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
        exact hR q ((le_max_left R 0).trans_lt hy)
      · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
        exact hw.support_s q hs
    rw [hw0, norm_zero]
    exact le_max_right C 0

theorem IsCompactBand.pdQ {σ H1 : ℝ} {w : Profile → MeridC} (hw : IsCompactBand σ H1 w) :
    IsCompactBand σ H1 (UnforcedLeray.Short.PartIIa.pdQ w) := by
  obtain ⟨R, hR⟩ := hw.support_y
  exact ⟨contDiff_pdQ hw.smooth, support_s_pdQ hw.support_s,
    ⟨R, support_y_fderiv_apply hR (0, 1, 0)⟩⟩

theorem IsCompactBand.pdEta {σ H1 : ℝ} {w : Profile → MeridC} (hw : IsCompactBand σ H1 w) :
    IsCompactBand σ H1 (UnforcedLeray.Short.PartIIa.pdEta w) := by
  obtain ⟨R, hR⟩ := hw.support_y
  exact ⟨contDiff_pdEta hw.smooth, support_s_pdEta hw.support_s,
    ⟨R, support_y_fderiv_apply hR (0, 0, 1)⟩⟩

theorem IsCompactBand.opS {σ H1 : ℝ} {w : Profile → MeridC} (hw : IsCompactBand σ H1 w) :
    IsCompactBand σ H1 (UnforcedLeray.Short.PartIIa.opS w) := by
  obtain ⟨R, hR⟩ := hw.support_y
  refine ⟨contDiff_opS hw.smooth, support_s_opS hw.support_s, ⟨R, fun p hp => ?_⟩⟩
  have h0 : pdS w p = 0 := support_y_fderiv_apply hR (1, 0, 0) p hp
  simp only [UnforcedLeray.Short.PartIIa.opS, h0, smul_zero]

theorem IsCompactBand.nuSMul_laplaceQEta {σ H1 : ℝ} (ν : ℝ) {w : Profile → MeridC}
    (hw : IsCompactBand σ H1 w) :
    IsCompactBand σ H1 (nuSMul ν 1 (laplaceQEta w)) := by
  obtain ⟨R1, hR1⟩ := hw.pdQ.pdQ.support_y
  obtain ⟨R2, hR2⟩ := hw.pdEta.pdEta.support_y
  refine ⟨contDiff_nuSMul ν 1 (contDiff_laplaceQEta hw.smooth),
    support_s_nuSMul ν 1 (support_s_laplaceQEta hw.support_s), ⟨max R1 R2, fun p hp => ?_⟩⟩
  have h1 : UnforcedLeray.Short.PartIIa.pdQ (UnforcedLeray.Short.PartIIa.pdQ w) p = 0 :=
    hR1 p ((le_max_left R1 R2).trans_lt hp)
  have h2 : UnforcedLeray.Short.PartIIa.pdEta (UnforcedLeray.Short.PartIIa.pdEta w) p = 0 :=
    hR2 p ((le_max_right R1 R2).trans_lt hp)
  simp only [nuSMul, laplaceQEta, h1, h2, add_zero, smul_zero]

theorem IsCompactBand.toIsDiffProfile {σ H1 : ℝ} {w : Profile → MeridC}
    (hw : IsCompactBand σ H1 w) : IsDiffProfile σ H1 w :=
  ⟨hw.smooth, hw.support_s, hw.bdd, hw.opS.bdd, hw.pdQ.bdd, hw.pdQ.pdQ.bdd,
    hw.pdEta.bdd, hw.pdEta.pdEta.bdd⟩

theorem causalAdjointFDeriv_eq_clm (ν : ℝ) (μ : ℂ) (k : ℕ) (w : Profile → MeridC) (p : Profile) :
    causalAdjointFDeriv ν μ k w p =
      p.1⁻¹ • smulRightCLM fstProfileCLM
        (causalAdjointRep ν μ (thetaWeight k) (UnforcedLeray.Short.PartIIa.opS w) p +
          causalAdjointRep ν μ (thetaWeight (k + 1)) (nuSMul ν 1 (laplaceQEta w)) p) +
      smulRightCLM snd1ProfileCLM
        (causalAdjointRep ν μ (thetaWeight k) (UnforcedLeray.Short.PartIIa.pdQ w) p) +
      smulRightCLM snd2ProfileCLM
        (causalAdjointRep ν μ (thetaWeight k) (UnforcedLeray.Short.PartIIa.pdEta w) p) := by
  refine ContinuousLinearMap.ext fun dq => ?_
  simp [causalAdjointFDeriv, smul_smul, mul_comm]

theorem contDiffOn_causalAdjointRep_nat {σ H1 ν : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    {μ : ℂ} (hμ : 0 < μ.re + 1 / 4) :
    ∀ (m k : ℕ) {w : Profile → MeridC}, IsCompactBand σ H1 w →
      ContDiffOn ℝ m (causalAdjointRep ν μ (thetaWeight k) w) {p : Profile | 0 < p.1}
  | 0, k, _, hw =>
    contDiffOn_zero.2 fun _ hp =>
      (differentiableAt_causalAdjointRep hν hσ hσH1 hμ k hw.toIsDiffProfile hp).continuousAt
        |>.continuousWithinAt
  | m + 1, k, w, hw => by
    set S : Set Profile := {p : Profile | 0 < p.1}
    have hS : IsOpen S := isOpen_lt continuous_const continuous_fst
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_of_isOpen hS]
    refine ⟨fun p hp =>
      (differentiableAt_causalAdjointRep hν hσ hσH1 hμ k hw.toIsDiffProfile hp).differentiableWithinAt,
      by simp, ?_⟩
    refine ContDiffOn.congr ?_
      (fun p hp => (hasFDerivAt_causalAdjointRep hν hσ hσH1 hμ k hw.toIsDiffProfile hp).fderiv)
    have hrew : causalAdjointFDeriv ν μ k w = fun p =>
        p.1⁻¹ • smulRightCLM fstProfileCLM
          (causalAdjointRep ν μ (thetaWeight k) (UnforcedLeray.Short.PartIIa.opS w) p +
            causalAdjointRep ν μ (thetaWeight (k + 1)) (nuSMul ν 1 (laplaceQEta w)) p) +
        smulRightCLM snd1ProfileCLM
          (causalAdjointRep ν μ (thetaWeight k) (UnforcedLeray.Short.PartIIa.pdQ w) p) +
        smulRightCLM snd2ProfileCLM
          (causalAdjointRep ν μ (thetaWeight k) (UnforcedLeray.Short.PartIIa.pdEta w) p) :=
      funext (causalAdjointFDeriv_eq_clm ν μ k w)
    rw [hrew]
    have h_inv : ContDiffOn ℝ m (fun p : Profile => p.1⁻¹) S :=
      contDiff_fst.contDiffOn.inv fun _ hp => ne_of_gt hp
    have h_opS := contDiffOn_causalAdjointRep_nat hν hσ hσH1 hμ m k hw.opS
    have h_lap := contDiffOn_causalAdjointRep_nat hν hσ hσH1 hμ m (k + 1)
      (hw.nuSMul_laplaceQEta ν)
    have h_Q := contDiffOn_causalAdjointRep_nat hν hσ hσH1 hμ m k hw.pdQ
    have h_E := contDiffOn_causalAdjointRep_nat hν hσ hσH1 hμ m k hw.pdEta
    have h1 := h_inv.smul
      ((smulRightCLM fstProfileCLM).contDiff.comp_contDiffOn (h_opS.add h_lap))
    have h2 := (smulRightCLM snd1ProfileCLM).contDiff.comp_contDiffOn h_Q
    have h3 := (smulRightCLM snd2ProfileCLM).contDiff.comp_contDiffOn h_E
    exact (h1.add h2).add h3

/-- Smoothness of `flatAdjointRep ν μ w` on `{p : Profile | 0 < p.1}` for any `IsCompactBand`
source profile `w`. -/
theorem contDiffOn_flatAdjointRep_of_compactBand {σ H1 ν : ℝ}
    (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4)
    {w : Profile → MeridC} (hw : IsCompactBand σ H1 w) :
    ContDiffOn ℝ ∞ (flatAdjointRep ν μ w) {p : Profile | 0 < p.1} := by
  rw [← causalAdjointRep_thetaWeight_zero, contDiffOn_infty]
  intro m
  exact contDiffOn_causalAdjointRep_nat hν hσ hσH1 hμ m 0 hw

end UnforcedLeray.Short.PartIIa.FlatAdjointSmoothAux
