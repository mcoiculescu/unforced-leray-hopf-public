import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1_1.Ibp

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace N05_1_1P

theorem qp_cutRep {c : ℝ} (hc : 0 < c) {g : Profile → ℝ} (hg : QPeriodic c g)
    (W : HSpace c MeridC) : QPeriodic c (cutRep c g W) := by
  intro p
  simp only [cutRep, hg p, qPeriodic_periodize hc (W : Profile → MeridC) p]

theorem qp_add {c : ℝ} {f g : Profile → MeridC} (hf : QPeriodic c f) (hg : QPeriodic c g) :
    QPeriodic c (fun p => f p + g p) := fun p => by
  show f _ + g _ = f p + g p
  rw [hf p, hg p]

theorem supp_cutRep {c σ H1 L1 : ℝ} {g : Profile → ℝ}
    (hg : ∀ p, g p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) (W : HSpace c MeridC)
    (p : Profile) (hp : cutRep c g W p ≠ 0) : σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 :=
  hg p (fun h => hp (by simp [cutRep, h]))

theorem supp_add {σ H1 L1 : ℝ} {f g : Profile → MeridC}
    (hf : ∀ p, f p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (hg : ∀ p, g p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) (p : Profile)
    (hp : f p + g p ≠ 0) : σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := by
  by_cases h1 : f p = 0
  · exact hg p (fun h2 => hp (by simp [h1, h2]))
  · exact hf p h1

theorem gamma_ge {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hM : 0 ≤ M) :
    1 ≤ Gamma ν c σ H1 L1 M γs χ χ1 ∧ H1 ≤ Gamma ν c σ H1 L1 M γs χ χ1 ∧
      L1 ≤ Gamma ν c σ H1 L1 M γs χ χ1 ∧ cNorm8 χ ≤ Gamma ν c σ H1 L1 M γs χ χ1 ∧
      1 + H1 ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
  have h1 : 0 < ν⁻¹ := inv_pos.2 hν
  have h2 : 0 < c⁻¹ := inv_pos.2 hc
  have h3 : 0 < γs⁻¹ := inv_pos.2 hγ
  have h4 : 0 < σ⁻¹ := inv_pos.2 hσ
  have h5 := cNorm8_nonneg χ
  have h6 := cNorm8_nonneg χ1
  unfold Gamma GammaBox
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem abs_mul_pdS_le {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1)
    {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (p : Profile) :
    |p.1 * pdS χ p| ≤ H1 * cNorm8 χ := by
  have h0 := cNorm8_nonneg χ
  by_cases h : pdS χ p = 0
  · simp only [h, mul_zero, abs_zero]; nlinarith
  · obtain ⟨h1, h2, _⟩ := pdS_support hχ h
    rw [abs_mul, abs_of_pos (lt_of_lt_of_le hσ h1)]
    exact mul_le_mul h2 (abs_pdS_le hc hχ p) (abs_nonneg _) (by linarith)

theorem abs_mul_pdEta_le {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1)
    (hL1 : 0 ≤ L1) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (p : Profile) :
    |p.2.2 * pdEta χ p| ≤ L1 * cNorm8 χ := by
  have h0 := cNorm8_nonneg χ
  by_cases h : pdEta χ p = 0
  · simp only [h, mul_zero, abs_zero]; positivity
  · obtain ⟨_, _, h3⟩ := pdEta_support hχ h
    rw [abs_mul]
    exact mul_le_mul h3 (abs_pdEta_le hc hχ p) (abs_nonneg _) hL1

theorem phaseCutoffProductRule_aux : N05_1_1Org.PhaseCutoffProductRule := by
  refine ⟨3, 32, by norm_num, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hM hχ hχ1 hm B hB ε hε hε1 w Sw Qw Ew hS hQ hE
  set G := Gamma ν c σ H1 L1 M γs χ χ1 with hGdef
  obtain ⟨hG1, hGH, hGL, hGc, hGa⟩ := gamma_ge χ χ1 hν hc hσ hσH hL1 hγ hM
  have hcN := cNorm8_nonneg χ
  have hSP := SP.of_cutoff hχ
  have hH0 : 0 < H1 := lt_of_lt_of_le hσ hσH
  -- the multipliers
  let gS : Profile → ℝ := fun p => p.1 * pdS χ p
  let gE : Profile → ℝ := pdEta χ
  let gQ : Profile → ℝ := fun p => pdQ χ p - ε * (2 * p.1 * pdS χ p + p.2.2 * pdEta χ p)
  have hgSP_S : SP c gS := SP.mul (SP.fst c) hSP.pdS
  have hgSP_E : SP c gE := hSP.pdEta
  have hgSP_Q : SP c gQ :=
    SP.sub hSP.pdQ (SP.mul (SP.const c ε) (SP.add (SP.mul (SP.mul (SP.const c 2) (SP.fst c))
      hSP.pdS) (SP.mul (SP.eta c) hSP.pdEta)))
  -- supports
  have box_χ : ∀ p, χ p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := hχ.support
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
  -- bounds
  have bχ : ∀ p, |χ p| ≤ cNorm8 χ := N05_4Aux.abs_le_cNorm8_of_nearCutoff hc hχ
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
  -- measurability
  have hmS : Measurable gS :=
    measurable_fst.mul ((hχ.smooth.continuous_fderiv (by simp)).clm_apply
      continuous_const).measurable
  have hmE : Measurable gE :=
    ((hχ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).measurable
  have hmQ : Measurable gQ := hgSP_Q.1.continuous.measurable
  -- memLp
  have mχw := memLp_cutRep hc hσ hσH (hs_of box_χ) bχ hm w
  have mχS := memLp_cutRep hc hσ hσH (hs_of box_χ) bχ hm Sw
  have mχQ := memLp_cutRep hc hσ hσH (hs_of box_χ) bχ hm Qw
  have mχE := memLp_cutRep hc hσ hσH (hs_of box_χ) bχ hm Ew
  have mSw := memLp_cutRep hc hσ hσH (hs_of box_S) bS hmS w
  have mEw := memLp_cutRep hc hσ hσH (hs_of box_E) bE hmE w
  have mQw := memLp_cutRep hc hσ hσH (hs_of box_Q) bQ hmQ w
  refine ⟨cutRep c χ w, fun p => cutRep c χ Sw p + cutRep c gS w p,
    fun p => cutRep c χ Qw p + cutRep c gQ w p,
    fun p => cutRep c χ Ew p + cutRep c gE w p, ?_, ?_⟩
  · refine ⟨N05_4Aux.flatStressCutRep_ae_eq hc χ hm hB w, qp_cutRep hc hχ.periodic w,
      qp_add (qp_cutRep hc hχ.periodic Sw) (qp_cutRep hc hgSP_S.2 w),
      qp_add (qp_cutRep hc hχ.periodic Qw) (qp_cutRep hc hgSP_Q.2 w),
      qp_add (qp_cutRep hc hχ.periodic Ew) (qp_cutRep hc hgSP_E.2 w),
      supp_cutRep box_χ w,
      supp_add (supp_cutRep box_χ Sw) (supp_cutRep box_S w),
      supp_add (supp_cutRep box_χ Qw) (supp_cutRep box_Q w),
      supp_add (supp_cutRep box_χ Ew) (supp_cutRep box_E w),
      mχw, mχS.add mSw, mχQ.add mQw, mχE.add mEw, ?_, ?_, ?_⟩
    · intro φ hφ
      exact ibp_s hc hχ hS hφ
    · intro φ hφ
      exact ibp_q hc hχ hS hQ hE hφ
    · intro φ hφ
      exact ibp_eta hc hχ hE hφ
  · -- norm bounds
    have n1 := cellL2Norm_cutRep_le_mul hc hσ hσH (hs_of box_χ) bχ hm w
    have n2 := cellL2Norm_cutRep_le_mul hc hσ hσH (hs_of box_χ) bχ hm Sw
    have n3 := cellL2Norm_cutRep_le_mul hc hσ hσH (hs_of box_χ) bχ hm Qw
    have n4 := cellL2Norm_cutRep_le_mul hc hσ hσH (hs_of box_χ) bχ hm Ew
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
    set X := cNorm8 χ with hX
    have ha : 1 + H1 ≤ G := hGa
    have ha0 : 0 ≤ 1 + H1 := by linarith
    have hG0 : 0 ≤ G := by linarith
    have k1 : (1 + H1) * X ≤ G * G := mul_le_mul ha hGc hcN hG0
    have k2 : (1 + H1) * (H1 * X) ≤ G * (G * G) :=
      mul_le_mul ha (mul_le_mul hGH hGc hcN hG0) (by positivity) hG0
    have hq : 1 + 2 * H1 + L1 ≤ 4 * G := by linarith
    have k3 : (1 + H1) * ((1 + 2 * H1 + L1) * X) ≤ G * ((4 * G) * G) :=
      mul_le_mul ha (mul_le_mul hq hGc hcN (by linarith)) (by positivity) hG0
    have hG2 : G * G ≤ G * (G * G) := by nlinarith
    -- coefficient comparisons
    have hc1 : (1 + H1) * X * ‖w‖ ≤ G * G * ‖w‖ := mul_le_mul_of_nonneg_right k1 hw
    have hc2 : (1 + H1) * X * ‖Sw‖ ≤ G * G * ‖Sw‖ := mul_le_mul_of_nonneg_right k1 hSw
    have hc3 : (1 + H1) * X * ‖Qw‖ ≤ G * G * ‖Qw‖ := mul_le_mul_of_nonneg_right k1 hQw
    have hc4 : (1 + H1) * X * ‖Ew‖ ≤ G * G * ‖Ew‖ := mul_le_mul_of_nonneg_right k1 hEw
    have hc5 : (1 + H1) * (H1 * X) * ‖w‖ ≤ G * (G * G) * ‖w‖ :=
      mul_le_mul_of_nonneg_right k2 hw
    have hc6 : (1 + H1) * X * ‖w‖ ≤ G * G * ‖w‖ := hc1
    have hc7 : (1 + H1) * ((1 + 2 * H1 + L1) * X) * ‖w‖ ≤ G * ((4 * G) * G) * ‖w‖ :=
      mul_le_mul_of_nonneg_right k3 hw
    have g3 : 0 ≤ G * (G * G) := by positivity
    have e1 : G * G * ‖w‖ ≤ G * (G * G) * ‖w‖ := mul_le_mul_of_nonneg_right hG2 hw
    have e2 : G * G * ‖Sw‖ ≤ G * (G * G) * ‖Sw‖ := mul_le_mul_of_nonneg_right hG2 hSw
    have e3 : G * G * ‖Qw‖ ≤ G * (G * G) * ‖Qw‖ := mul_le_mul_of_nonneg_right hG2 hQw
    have e4 : G * G * ‖Ew‖ ≤ G * (G * G) * ‖Ew‖ := mul_le_mul_of_nonneg_right hG2 hEw
    have hfin : cellL2Norm c (cutRep c χ w) +
        cellL2Norm c (fun p => cutRep c χ Sw p + cutRep c gS w p) +
        cellL2Norm c (fun p => cutRep c χ Qw p + cutRep c gQ w p) +
        cellL2Norm c (fun p => cutRep c χ Ew p + cutRep c gE w p) ≤
        32 * G ^ 3 * (‖w‖ + ‖Sw‖ + ‖Qw‖ + ‖Ew‖) := by
      have : G ^ 3 = G * (G * G) := by ring
      rw [this]
      nlinarith [mul_nonneg g3 hw, mul_nonneg g3 hSw, mul_nonneg g3 hQw, mul_nonneg g3 hEw]
    exact hfin

end N05_1_1P

theorem phaseCutoffProductRule : N05_1_1Org.PhaseCutoffProductRule :=
  N05_1_1P.phaseCutoffProductRule_aux

end UnforcedLeray.Short.PartIIa
