import UnforcedLeray.Short.PartIIb.Sub.T12_1_3
import UnforcedLeray.Lib.SobolevC.CylExtend
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part II-b, task `PartII-b:T12/1/3/2` (`CylSmoothWeakToPointwise`): pointwise div and curl

Source of record: `the November 2 reference manuscript`, lines 1670 and 1923-1926.

Proof outline.
* A cylinder test `φ` (`CylTest`) gives a `CylSolTest` `Ψ = (∂_η φ, -∂_q φ)`, using symmetry of
  second derivatives (`ContDiffAt.isSymmSndFDerivAt`).
* Integration by parts on one cell (`Cyl.integral_cell_partialQ_mul`,
  `Cyl.integral_cell_partialEta_mul`) turns each weak identity into `∫_cell φ · g = 0`, where `g` is
  the divergence (resp. curl) of the smooth field.
* Separation: `perSum` of a compactly supported smooth `χ` is a cylinder test, and
  `Sob.integral_smul_perExt` unfolds `∫_{ℝ²} χ g` into `∫_cell perSum χ · g`. A continuous
  periodic `g` with `∫ χ g = 0` for all smooth compactly supported `χ` vanishes everywhere.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ## Bookkeeping between the two cylinder-test notions -/

lemma smp_cylTest_of_sob {c : ℝ} {φ : ℝ × ℝ → ℝ} (h : Sob.IsCylTest c φ) : CylTest c φ where
  smooth := h.smooth
  periodic z := by
    rw [show (z.1 + c, z.2) = z + (c, 0) from Prod.ext (by simp) (by simp)]
    exact h.periodic z
  bounded := h.bounded

lemma smp_sob_neg {c : ℝ} {ψ : ℝ × ℝ → ℝ} (h : Sob.IsCylTest c ψ) :
    Sob.IsCylTest c (fun x => -ψ x) where
  smooth := h.smooth.neg
  periodic x := by simp [h.periodic x]
  bounded := by
    obtain ⟨R, hR⟩ := h.bounded
    exact ⟨R, fun x hx => by simp [hR x hx]⟩

lemma smp_cell_eq (c : ℝ) : Cyl.cell c = Sob.cylCell c := by
  simp [Cyl.cell, Sob.cylCell, neg_div]

/-- Weak identities on the cylinder average pass to one cell. -/
lemma smp_cell_of_avg {c : ℝ} (hc : 0 < c) {F : ℝ × ℝ → ℂ}
    (h : ∫ z, F z ∂(Cyl.avgμ c) = 0) : ∫ z in Cyl.cell c, F z = 0 := by
  unfold Cyl.avgμ at h
  rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 hc.le)] at h
  rcases smul_eq_zero.1 h with h' | h'
  · exact absurd h' (inv_ne_zero hc.ne')
  · exact h'

/-! ## Periodicity and derivatives -/

lemma smp_perExt_eq_of_periodic {c : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℂ}
    (hper : ∀ z : ℝ × ℝ, g (z.1 + c, z.2) = g z) :
    Sob.perExt hc g = g := by
  funext z
  have hp : Function.Periodic (fun x : ℝ => g (x, z.2)) c := fun x => hper (x, z.2)
  have hk := hp.int_mul (toIcoDiv hc (-(c / 2)) z.1) (toIcoMod hc (-(c / 2)) z.1)
  have hz := toIcoMod_add_toIcoDiv_zsmul hc (-(c / 2)) z.1
  rw [zsmul_eq_mul] at hz
  unfold Sob.perExt
  rw [← hk, hz]

lemma smp_cont_fd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ × ℝ → E}
    (hF : ContDiff ℝ ∞ F) (v : ℝ × ℝ) : Continuous fun z => fderiv ℝ F z v :=
  (hF.continuous_fderiv (by simp)).clm_apply continuous_const

lemma smp_fderiv_per {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ × ℝ → E}
    {c : ℝ} (hper : ∀ z : ℝ × ℝ, F (z.1 + c, z.2) = F z) (z v : ℝ × ℝ) :
    fderiv ℝ F (z.1 + c, z.2) v = fderiv ℝ F z v := by
  have hfun : (fun t : ℝ × ℝ => F (t + (c, 0))) = F := funext fun t => by
    rw [show t + (c, 0) = (t.1 + c, t.2) from Prod.ext (by simp) (by simp)]
    exact hper t
  have h : fderiv ℝ (fun x => F (x + (c, 0))) z = fderiv ℝ F (z + (c, 0)) :=
    fderiv_comp_add_right (c, 0)
  rw [hfun] at h
  rw [show (z.1 + c, z.2) = z + (c, 0) from Prod.ext (by simp) (by simp), h]

lemma smp_fderiv_apply_const {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (z v w : ℝ × ℝ) :
    fderiv ℝ (fun y => fderiv ℝ φ y v) z w = fderiv ℝ (fderiv ℝ φ) z w v := by
  have hd : Differentiable ℝ (fderiv ℝ φ) := (contDiff_infty_iff_fderiv.1 hφ).2.differentiable (by simp)
  have h := congrArg (fun L => L w)
    (fderiv_clm_apply (𝕜 := ℝ) (c := fderiv ℝ φ) (u := fun _ => v) (x := z)
      hd.differentiableAt (differentiableAt_const v))
  simpa using h

lemma smp_fderiv_ofReal {φ : ℝ × ℝ → ℝ} (hφ : Differentiable ℝ φ) (z v : ℝ × ℝ) :
    fderiv ℝ (fun y => (φ y : ℂ)) z v = (fderiv ℝ φ z v : ℂ) := by
  have h1 : HasFDerivAt (fun y => (φ y : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ φ z)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z (hφ z).hasFDerivAt
  rw [h1.fderiv]
  simp

lemma smp_cont_pQ {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) : Continuous (Cyl.partialQ F) := by
  rw [show Cyl.partialQ F = fun z => fderiv ℝ F z (1, 0) from
    funext (Cyl.partialQ_eq_fderiv (hF.differentiable (by simp)))]
  exact smp_cont_fd hF _

lemma smp_cont_pEta {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) : Continuous (Cyl.partialEta F) := by
  rw [show Cyl.partialEta F = fun z => fderiv ℝ F z (0, 1) from
    funext (Cyl.partialEta_eq_fderiv (hF.differentiable (by simp)))]
  exact smp_cont_fd hF _

lemma smp_pq_ofReal {φ : ℝ × ℝ → ℝ} (hφ : Differentiable ℝ φ) (z : ℝ × ℝ) :
    Cyl.partialQ (fun y => (φ y : ℂ)) z = (fderiv ℝ φ z (1, 0) : ℂ) := by
  have hΦd : Differentiable ℝ (fun y => (φ y : ℂ)) := fun z =>
    (Complex.ofRealCLM.hasFDerivAt.comp z (hφ z).hasFDerivAt).differentiableAt
  rw [Cyl.partialQ_eq_fderiv hΦd z, smp_fderiv_ofReal hφ]

lemma smp_pe_ofReal {φ : ℝ × ℝ → ℝ} (hφ : Differentiable ℝ φ) (z : ℝ × ℝ) :
    Cyl.partialEta (fun y => (φ y : ℂ)) z = (fderiv ℝ φ z (0, 1) : ℂ) := by
  have hΦd : Differentiable ℝ (fun y => (φ y : ℂ)) := fun z =>
    (Complex.ofRealCLM.hasFDerivAt.comp z (hφ z).hasFDerivAt).differentiableAt
  rw [Cyl.partialEta_eq_fderiv hΦd z, smp_fderiv_ofReal hφ]

/-! ## Vanishing, continuity and integrability on one cell -/

lemma smp_vanish_q {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : CylTest c φ) {L : ℝ}
    (hL : Cyl.VanishesOutside L φ) :
    Cyl.VanishesOutside L (fun z => (fderiv ℝ φ z (1, 0) : ℂ)) := by
  intro z hz
  have h := Cyl.VanishesOutside.partialQ hL z hz
  rw [Cyl.partialQ_eq_fderiv (hφ.smooth.differentiable (by simp)) z] at h
  simp [h]

lemma smp_vanish_e {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : CylTest c φ) {L : ℝ}
    (hL : Cyl.VanishesOutside L φ) :
    Cyl.VanishesOutside L (fun z => (fderiv ℝ φ z (0, 1) : ℂ)) := by
  intro z hz
  have h := Cyl.VanishesOutside.partialEta hL z hz
  rw [Cyl.partialEta_eq_fderiv (hφ.smooth.differentiable (by simp)) z] at h
  simp [h]

lemma smp_intg_q {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : CylTest c φ) {F : ℝ × ℝ → ℂ}
    (hF : Continuous F) :
    IntegrableOn (fun z => F z * (fderiv ℝ φ z (1, 0) : ℂ)) (Cyl.cell c) := by
  obtain ⟨L, hL⟩ := hφ.bounded
  exact Cyl.VanishesOutside.integrableOn_cell ((smp_vanish_q hφ hL).mul_left F)
    (hF.mul (Complex.continuous_ofReal.comp (smp_cont_fd hφ.smooth _))) c

lemma smp_intg_e {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : CylTest c φ) {F : ℝ × ℝ → ℂ}
    (hF : Continuous F) :
    IntegrableOn (fun z => F z * (fderiv ℝ φ z (0, 1) : ℂ)) (Cyl.cell c) := by
  obtain ⟨L, hL⟩ := hφ.bounded
  exact Cyl.VanishesOutside.integrableOn_cell ((smp_vanish_e hφ hL).mul_left F)
    (hF.mul (Complex.continuous_ofReal.comp (smp_cont_fd hφ.smooth _))) c

lemma smp_intg_phi {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : CylTest c φ) {G : ℝ × ℝ → ℂ}
    (hG : Continuous G) :
    IntegrableOn (fun z => (φ z : ℂ) * G z) (Cyl.cell c) := by
  obtain ⟨L, hL⟩ := hφ.bounded
  have hV : Cyl.VanishesOutside L (fun z => (φ z : ℂ)) := fun z hz => by simp [hL z hz]
  exact Cyl.VanishesOutside.integrableOn_cell (hV.mul_right G)
    ((Complex.continuous_ofReal.comp hφ.smooth.continuous).mul hG) c

/-! ## Integration by parts on one cell -/

lemma smp_ibpQ {c : ℝ} (hc : 0 < c) {φ : ℝ × ℝ → ℝ} (hφ : CylTest c φ) {F : ℝ × ℝ → ℂ}
    (hF : ContDiff ℝ ∞ F) (hFp : ∀ z : ℝ × ℝ, F (z.1 + c, z.2) = F z) :
    ∫ z : ℝ × ℝ in Cyl.cell c, F z * (fderiv ℝ φ z (1, 0) : ℂ) =
      -∫ z : ℝ × ℝ in Cyl.cell c, (φ z : ℂ) * fderiv ℝ F z (1, 0) := by
  obtain ⟨L, hL⟩ := hφ.bounded
  have hΦs : ContDiff ℝ ∞ (fun z => (φ z : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ.smooth
  have hΦd : Differentiable ℝ (fun z => (φ z : ℂ)) := hΦs.differentiable (by simp)
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  have hΦV : Cyl.VanishesOutside L (fun z => (φ z : ℂ)) := fun z hz => by simp [hL z hz]
  have hΦper : Cyl.IsPeriodic c (fun z => (φ z : ℂ)) := fun z => by simp [hφ.periodic z]
  have h1 : IntegrableOn (fun z => Cyl.partialQ (fun y => (φ y : ℂ)) z * F z) (Cyl.cell c) :=
    Cyl.VanishesOutside.integrableOn_cell
      ((Cyl.VanishesOutside.partialQ hΦV).mul_right F) ((smp_cont_pQ hΦs).mul hF.continuous) c
  have h2 : IntegrableOn (fun z => (φ z : ℂ) * Cyl.partialQ F z) (Cyl.cell c) :=
    Cyl.VanishesOutside.integrableOn_cell (hΦV.mul_right (Cyl.partialQ F))
      (hΦs.continuous.mul (smp_cont_pQ hF)) c
  have hI := Cyl.integral_cell_partialQ_mul hc hΦd hFd hΦper hFp h1 h2
  simp only [smp_pq_ofReal (hφ.smooth.differentiable (by simp)), Cyl.partialQ_eq_fderiv hFd] at hI
  rw [show (fun z => F z * (fderiv ℝ φ z (1, 0) : ℂ)) =
    fun z => (fderiv ℝ φ z (1, 0) : ℂ) * F z from funext fun z => mul_comm _ _]
  exact hI

lemma smp_ibpE {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : CylTest c φ) {F : ℝ × ℝ → ℂ}
    (hF : ContDiff ℝ ∞ F) :
    ∫ z : ℝ × ℝ in Cyl.cell c, F z * (fderiv ℝ φ z (0, 1) : ℂ) =
      -∫ z : ℝ × ℝ in Cyl.cell c, (φ z : ℂ) * fderiv ℝ F z (0, 1) := by
  obtain ⟨L, hL⟩ := hφ.bounded
  have hΦs : ContDiff ℝ ∞ (fun z => (φ z : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ.smooth
  have hΦd : Differentiable ℝ (fun z => (φ z : ℂ)) := hΦs.differentiable (by simp)
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  have hΦV : Cyl.VanishesOutside L (fun z => (φ z : ℂ)) := fun z hz => by simp [hL z hz]
  have h0 : IntegrableOn (fun z => (φ z : ℂ) * F z) (Cyl.cell c) :=
    Cyl.VanishesOutside.integrableOn_cell (hΦV.mul_right F) (hΦs.continuous.mul hF.continuous) c
  have h1 : IntegrableOn (fun z => Cyl.partialEta (fun y => (φ y : ℂ)) z * F z) (Cyl.cell c) :=
    Cyl.VanishesOutside.integrableOn_cell
      ((Cyl.VanishesOutside.partialEta hΦV).mul_right F) ((smp_cont_pEta hΦs).mul hF.continuous) c
  have h2 : IntegrableOn (fun z => (φ z : ℂ) * Cyl.partialEta F z) (Cyl.cell c) :=
    Cyl.VanishesOutside.integrableOn_cell (hΦV.mul_right (Cyl.partialEta F))
      (hΦs.continuous.mul (smp_cont_pEta hF)) c
  have hI := Cyl.integral_cell_partialEta_mul hΦd hFd h0 h1 h2
  simp only [smp_pe_ofReal (hφ.smooth.differentiable (by simp)), Cyl.partialEta_eq_fderiv hFd] at hI
  rw [show (fun z => F z * (fderiv ℝ φ z (0, 1) : ℂ)) =
    fun z => (fderiv ℝ φ z (0, 1) : ℂ) * F z from funext fun z => mul_comm _ _]
  exact hI

/-! ## Separation of a continuous periodic function by cylinder tests -/

lemma smp_sep {c : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℂ} (hg : Continuous g)
    (hper : ∀ z : ℝ × ℝ, g (z.1 + c, z.2) = g z)
    (h : ∀ φ : ℝ × ℝ → ℝ, Sob.IsCylTest c φ →
      ∫ z in Sob.cylCell c, (φ z : ℂ) * g z = 0) :
    ∀ z, g z = 0 := by
  have hint : ∀ χ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∫ z, χ z • g z = 0 := by
    intro χ hχ hχc
    have hf : ∀ M : ℝ, IntegrableOn g (Sob.cylCell c ∩ {z : ℝ × ℝ | |z.2| ≤ M}) := by
      intro M
      have hK : IsCompact (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-M) M) :=
        isCompact_Icc.prod isCompact_Icc
      refine (hg.continuousOn.integrableOn_compact hK).mono_set ?_
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      simp only [Sob.cylCell, mem_prod, mem_Ico, mem_univ, and_true, mem_setOf_eq] at ha hb
      exact ⟨⟨ha.1, ha.2.le⟩, abs_le.1 hb⟩
    obtain ⟨_, hEq⟩ :=
      Sob.integral_smul_perExt hc hχ.continuous hχc hg.stronglyMeasurable hf
    rw [smp_perExt_eq_of_periodic hc hper] at hEq
    rw [hEq]
    have hs := h (Sob.perSum c χ) (Sob.isCylTest_perSum hc hχ hχc)
    simpa [Complex.real_smul] using hs
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) hg.locallyIntegrable hint
  have hae' : g =ᵐ[volume] fun _ => (0 : ℂ) := hae
  intro z
  exact congrFun ((Continuous.ae_eq_iff_eq volume hg continuous_const).1 hae') z

/-! ## Div and curl identities for one test function -/

lemma smp_div_identity {c : ℝ} (hc : 0 < c) {F0 F1 : ℝ × ℝ → ℂ}
    (hF0 : ContDiff ℝ ∞ F0) (hF1 : ContDiff ℝ ∞ F1)
    (hp0 : ∀ z : ℝ × ℝ, F0 (z.1 + c, z.2) = F0 z)
    (hp1 : ∀ z : ℝ × ℝ, F1 (z.1 + c, z.2) = F1 z)
    {φ : ℝ × ℝ → ℝ} (hφ : CylTest c φ)
    (hW : ∫ z in Cyl.cell c,
      (F0 z * (fderiv ℝ φ z (1, 0) : ℂ) + F1 z * (fderiv ℝ φ z (0, 1) : ℂ)) = 0) :
    ∫ z : ℝ × ℝ in Cyl.cell c, (φ z : ℂ) * (fderiv ℝ F0 z (1, 0) + fderiv ℝ F1 z (0, 1)) = 0 := by
  rw [integral_add (smp_intg_q hφ hF0.continuous) (smp_intg_e hφ hF1.continuous)] at hW
  rw [smp_ibpQ hc hφ hF0 hp0, smp_ibpE hφ hF1] at hW
  have e : (fun z => (φ z : ℂ) * (fderiv ℝ F0 z (1, 0) + fderiv ℝ F1 z (0, 1))) =
      fun z => (φ z : ℂ) * fderiv ℝ F0 z (1, 0) + (φ z : ℂ) * fderiv ℝ F1 z (0, 1) :=
    funext fun z => mul_add _ _ _
  have i0 : IntegrableOn (fun z : ℝ × ℝ => (φ z : ℂ) * fderiv ℝ F0 z (1, 0)) (Cyl.cell c) :=
    smp_intg_phi hφ (smp_cont_fd hF0 _)
  have i1 : IntegrableOn (fun z : ℝ × ℝ => (φ z : ℂ) * fderiv ℝ F1 z (0, 1)) (Cyl.cell c) :=
    smp_intg_phi hφ (smp_cont_fd hF1 _)
  rw [e, integral_add i0 i1]
  linear_combination (-1 : ℂ) * hW

lemma smp_curl_identity {c : ℝ} (hc : 0 < c) {F0 F1 : ℝ × ℝ → ℂ}
    (hF0 : ContDiff ℝ ∞ F0) (hF1 : ContDiff ℝ ∞ F1)
    (hp1 : ∀ z : ℝ × ℝ, F1 (z.1 + c, z.2) = F1 z)
    {φ : ℝ × ℝ → ℝ} (hφ : CylTest c φ)
    (hS : ∫ z in Cyl.cell c,
      (F0 z * (fderiv ℝ φ z (0, 1) : ℂ) + F1 z * -(fderiv ℝ φ z (1, 0) : ℂ)) = 0) :
    ∫ z : ℝ × ℝ in Cyl.cell c, (φ z : ℂ) * (fderiv ℝ F1 z (1, 0) - fderiv ℝ F0 z (0, 1)) = 0 := by
  simp only [mul_neg] at hS
  have hneg : IntegrableOn (fun z => -(F1 z * (fderiv ℝ φ z (1, 0) : ℂ))) (Cyl.cell c) :=
    (smp_intg_q hφ hF1.continuous).neg
  rw [integral_add (smp_intg_e hφ hF0.continuous) hneg, integral_neg] at hS
  rw [smp_ibpE hφ hF0, smp_ibpQ hc hφ hF1 hp1] at hS
  have e : (fun z => (φ z : ℂ) * (fderiv ℝ F1 z (1, 0) - fderiv ℝ F0 z (0, 1))) =
      fun z => (φ z : ℂ) * fderiv ℝ F1 z (1, 0) - (φ z : ℂ) * fderiv ℝ F0 z (0, 1) :=
    funext fun z => mul_sub _ _ _
  have i0 : IntegrableOn (fun z : ℝ × ℝ => (φ z : ℂ) * fderiv ℝ F1 z (1, 0)) (Cyl.cell c) :=
    smp_intg_phi hφ (smp_cont_fd hF1 _)
  have i1 : IntegrableOn (fun z : ℝ × ℝ => (φ z : ℂ) * fderiv ℝ F0 z (0, 1)) (Cyl.cell c) :=
    smp_intg_phi hφ (smp_cont_fd hF0 _)
  rw [e, integral_sub i0 i1]
  linear_combination hS

/-- The field `Ψ = (∂_η φ, -∂_q φ)` is a divergence-free cylinder test field. -/
lemma smp_solTest {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφS : Sob.IsCylTest c φ) :
    CylSolTest c (fun z => ![fderiv ℝ φ z (0, 1), -fderiv ℝ φ z (1, 0)]) := by
  refine ⟨fun i => ?_, fun z => ?_⟩
  · fin_cases i
    · exact smp_cylTest_of_sob (hφS.dirDeriv (0, 1))
    · exact smp_cylTest_of_sob (smp_sob_neg (hφS.dirDeriv (1, 0)))
  · show fderiv ℝ (fun y => fderiv ℝ φ y (0, 1)) z (1, 0) +
      fderiv ℝ (fun y => -fderiv ℝ φ y (1, 0)) z (0, 1) = 0
    have hsym : IsSymmSndFDerivAt ℝ φ z :=
      (hφS.smooth.contDiffAt : ContDiffAt ℝ ∞ φ z).isSymmSndFDerivAt (by simp [minSmoothness])
    rw [fderiv_fun_neg, ContinuousLinearMap.neg_apply, smp_fderiv_apply_const hφS.smooth,
      smp_fderiv_apply_const hφS.smooth, hsym (1, 0) (0, 1)]
    ring

/-! ## The main theorem -/

theorem cylSmoothWeakToPointwise : CylSmoothWeakToPointwise := by
  intro c r hc E hE hdiv hsol
  obtain ⟨⟨hper, _⟩, hsm, _, _⟩ := hE
  have hd0 : ContDiff ℝ ∞ (fun y => E y 0) := hsm 0
  have hd1 : ContDiff ℝ ∞ (fun y => E y 1) := hsm 1
  have hP0 : ∀ z : ℝ × ℝ, (fun y => E y 0) (z.1 + c, z.2) = (fun y => E y 0) z :=
    fun z => by simp only [hper z]
  have hP1 : ∀ z : ℝ × ℝ, (fun y => E y 1) (z.1 + c, z.2) = (fun y => E y 1) z :=
    fun z => by simp only [hper z]
  constructor
  · have hperg : ∀ z : ℝ × ℝ,
        (fderiv ℝ (fun y => E y 0) (z.1 + c, z.2) (1, 0) +
          fderiv ℝ (fun y => E y 1) (z.1 + c, z.2) (0, 1)) =
        fderiv ℝ (fun y => E y 0) z (1, 0) + fderiv ℝ (fun y => E y 1) z (0, 1) :=
      fun z => by rw [smp_fderiv_per hP0 z, smp_fderiv_per hP1 z]
    have hz := smp_sep hc ((smp_cont_fd hd0 _).add (smp_cont_fd hd1 _)) hperg
      (fun φ hφS => by
        rw [← smp_cell_eq c]
        exact smp_div_identity hc hd0 hd1 hP0 hP1 (smp_cylTest_of_sob hφS)
          (smp_cell_of_avg hc (hdiv φ (smp_cylTest_of_sob hφS))))
    intro z
    exact hz z
  · have hperg : ∀ z : ℝ × ℝ,
        (fderiv ℝ (fun y => E y 1) (z.1 + c, z.2) (1, 0) -
          fderiv ℝ (fun y => E y 0) (z.1 + c, z.2) (0, 1)) =
        fderiv ℝ (fun y => E y 1) z (1, 0) - fderiv ℝ (fun y => E y 0) z (0, 1) :=
      fun z => by rw [smp_fderiv_per hP1 z, smp_fderiv_per hP0 z]
    have hz := smp_sep hc ((smp_cont_fd hd1 _).sub (smp_cont_fd hd0 _)) hperg
      (fun φ hφS => by
        rw [← smp_cell_eq c]
        have hsolφ := hsol (fun z => ![fderiv ℝ φ z (0, 1), -fderiv ℝ φ z (1, 0)])
          (smp_solTest hφS)
        have hS : ∫ z : ℝ × ℝ in Cyl.cell c,
            (E z 0 * (fderiv ℝ φ z (0, 1) : ℂ) + E z 1 * -(fderiv ℝ φ z (1, 0) : ℂ)) = 0 :=
          smp_cell_of_avg hc (by simpa [Fin.sum_univ_two] using hsolφ)
        exact smp_curl_identity hc hd0 hd1 hP1 (smp_cylTest_of_sob hφS) hS)
    intro z
    exact hz z

end UnforcedLeray.Short.IIb
