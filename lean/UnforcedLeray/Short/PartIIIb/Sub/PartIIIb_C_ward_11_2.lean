import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_11_2.H3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.XDiff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.XDiff.Cut3

/-!
# `PartIII-b:C/ward/11/2`: `WardD2XYoungL2`

Source of record: `the November 2 reference manuscript` (73 pages), 4194-4196,
5225-5235, 3633-3648 (`sep:young` with `j = 2`), 3696-3697.

By `wardX_eq_cut_add_corr`, `X = χ_y(ν·age) • X₀ + w2a(ϱ) • (Ψ_{X₀} • e₂)`.
On `R√ν ≤ ϱ y`:
- the 2-jets of the radial factors `χ_y(ν·age)` and `w2a(ϱ)` are uniformly bounded
  (`w112_cut_jet2_bound`, `w112_w2a_jet2_bound`), with `w2a` and its 1st and 2nd partials
  vanishing for `ϱ > R√(5ν/4)`;
- by axisymmetry (`w2_axi`), the 1st and 2nd partials of `Ψ_{X₀}` are bounded by
  `2ϱ‖X₀‖` and `4ϱ‖DX₀‖ + 4‖X₀‖` (`w112_psi_jet`);
- combining `wardD2X0YoungL2_proved` (`H1`), `wardX0YoungL2_proved`, and `w2_psiBd` via `WylBd`
  closure under sums and scalar multiples yields `WardD2XYoungL2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

lemma w112_physPd2_smul_norm_le_c2 {U : Set Space} (hUo : IsOpen U) {φ : Space → ℝ}
    {F : Space → Space} (hφ : ContDiffOn ℝ 2 φ U) (hF : ContDiffOn ℝ 2 F U)
    (j l : Fin 3) {y : Space} (hy : y ∈ U) :
    ‖physPd2 (fun x => φ x • F x) j l y‖ ≤
      |φ y| * ‖physPd2 F j l y‖ + |w112_sd1 φ j y| * ‖physPd F l y‖ +
        |w112_sd1 φ l y| * ‖physPd F j y‖ + |w112_sd2 φ j l y| * ‖F y‖ := by
  have hφ' : ContDiffOn ℝ ((1 : WithTop ℕ∞) + 1) φ U := hφ
  have hF' : ContDiffOn ℝ ((1 : WithTop ℕ∞) + 1) F U := hF
  have hfφ : ContDiffOn ℝ 1 (fderiv ℝ φ) U :=
    ((contDiffOn_succ_iff_fderiv_of_isOpen hUo).1 hφ').2.2
  have hfF : ContDiffOn ℝ 1 (fderiv ℝ F) U :=
    ((contDiffOn_succ_iff_fderiv_of_isOpen hUo).1 hF').2.2
  refine w112_physPd2_smul_norm_le hUo
    (fun w hw => (hφ.contDiffAt (hUo.mem_nhds hw)).differentiableAt (by norm_num))
    (fun k w hw => (((ContinuousLinearMap.apply ℝ ℝ (coordinateVector k)).contDiff.comp_contDiffOn
      hfφ).contDiffAt (hUo.mem_nhds hw)).differentiableAt one_ne_zero)
    (fun w hw => (hF.contDiffAt (hUo.mem_nhds hw)).differentiableAt (by norm_num))
    (fun k w hw => (((ContinuousLinearMap.apply ℝ Space (coordinateVector k)).contDiff.comp_contDiffOn
      hfF).contDiffAt (hUo.mem_nhds hw)).differentiableAt one_ne_zero)
    hy j l

/-- Pointwise bound on `‖physPd2 (wardX ...) j l y‖` on the young region `R√ν ≤ ϱ y`. -/
theorem w112_wardX_pd2_pt_bound {ν μ R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    {C₁ C₂ : ℝ} (_hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hcut : ∀ y : Space, R * Real.sqrt ν ≤ ϱ y →
      |χy (ν * age R y)| ≤ C₁ ∧
        (∀ k : Fin 3, |w112_sd1 (fun x => χy (ν * age R x)) k y| ≤ C₁) ∧
        (∀ j l : Fin 3, |w112_sd2 (fun x => χy (ν * age R x)) j l y| ≤ C₁))
    (hw2a_bd : ∀ y : Space, R * Real.sqrt ν ≤ ϱ y →
      |w2a ν R χy (ϱ y)| ≤ C₂ ∧
        (∀ k : Fin 3, |w112_sd1 (fun x => w2a ν R χy (ϱ x)) k y| ≤ C₂) ∧
        (∀ j l : Fin 3, |w112_sd2 (fun x => w2a ν R χy (ϱ x)) j l y| ≤ C₂))
    (hw2a_gt : ∀ y : Space, R * Real.sqrt (5 * ν / 4) < ϱ y →
      w2a ν R χy (ϱ y) = 0 ∧
        (∀ k : Fin 3, w112_sd1 (fun x => w2a ν R χy (ϱ x)) k y = 0) ∧
        (∀ j l : Fin 3, w112_sd2 (fun x => w2a ν R χy (ϱ x)) j l y = 0))
    {g : Chart → Ten3} (hg : IsOldL2 c ν g) (τ : ℝ) (j l : Fin 3)
    {y : Space} (hy : R * Real.sqrt ν ≤ ϱ y) :
    ‖physPd2 (wardX ν μ R c χy g τ) j l y‖ ≤
      C₁ * ‖physPd2 (wardX0 ν μ R c g τ) j l y‖ +
        (C₁ + 4 * C₂ * (R * Real.sqrt (5 * ν / 4))) * ‖physPd (wardX0 ν μ R c g τ) j y‖ +
        C₁ * ‖physPd (wardX0 ν μ R c g τ) l y‖ +
        (C₁ + 4 * C₂ + 4 * C₂ * (R * Real.sqrt (5 * ν / 4))) * ‖wardX0 ν μ R c g τ y‖ +
        C₂ * w2N ν μ R c (R * Real.sqrt (5 * ν / 4)) g τ y := by
  set r2 : ℝ := R * Real.sqrt (5 * ν / 4)
  have hr2nn : 0 ≤ r2 := by positivity
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hyU : y ∈ youngOpen ν R := lt_of_lt_of_le hrr hy
  have hUo : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  set Z : Space → Space := wardX0 ν μ R c g τ
  set φ₁ : Space → ℝ := fun x => χy (ν * age R x)
  set φ₂ : Space → ℝ := fun x => w2a ν R χy (ϱ x)
  set Ψ : Space → ℝ := fun x => outPrim (wardX0 ν μ R c g) τ (ϱ x) (x 2)
  set G : Space → Space := fun x => Ψ x • (coordinateVector 2 : Space)
  have hne : ∀ w ∈ youngOpen ν R, ϱ w ≠ 0 := fun w hw => by
    have hp := t9_thr_pos hν hR
    have hw' : R * Real.sqrt (5 * ν / 6) < ϱ w := hw
    linarith
  have hϱ2 : ContDiffOn ℝ 2 (fun w : Space => ϱ w) (youngOpen ν R) :=
    contDiffOn_ϱ.mono (fun w hw => t9_not_axis hν hR hw)
  have hage2 : ContDiffOn ℝ 2 (fun w : Space => ν * age R w) (youngOpen ν R) :=
    contDiffOn_const.mul
      (ContDiffOn.div contDiffOn_const (hϱ2.pow 2) (fun w hw => pow_ne_zero 2 (hne w hw)))
  have hφ₁c : ContDiffOn ℝ 2 φ₁ (youngOpen ν R) :=
    (hχy.smooth.of_le (WithTop.coe_le_coe.2 le_top)).comp_contDiffOn hage2
  have hdχ2 : ContDiff ℝ 2 (deriv χy) :=
    ((show ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) χy from hχy.smooth).deriv').of_le
      (WithTop.coe_le_coe.2 le_top)
  have hφ₂c : ContDiffOn ℝ 2 φ₂ (youngOpen ν R) := by
    have h1 : ContDiffOn ℝ 2 (fun w : Space => ν * (R ^ 2 / ϱ w ^ 2)) (youngOpen ν R) := hage2
    have hdA := hdχ2.comp_contDiffOn h1
    have hK : ContDiffOn ℝ 2 (fun w : Space => -2 * ν * R ^ 2 / ϱ w ^ 3) (youngOpen ν R) :=
      ContDiffOn.div contDiffOn_const (hϱ2.pow 3) (fun w hw => pow_ne_zero 3 (hne w hw))
    exact (hdA.mul hK).div hϱ2 hne
  have hZc3 : ContDiffOn ℝ 3 Z (youngOpen ν R) :=
    (w2_smooth hν hR hc hμ hg τ).of_le (WithTop.coe_le_coe.2 le_top)
  have hZc2 : ContDiffOn ℝ 2 Z (youngOpen ν R) := hZc3.of_le (by norm_num)
  have hΨc2 : ContDiffOn ℝ 2 Ψ (youngOpen ν R) :=
    (xc_outPrim_c3 hν hR hZc3 (w2_hdr hν hR hc hμ hg τ)).of_le (by norm_num)
  have hGc2 : ContDiffOn ℝ 2 G (youngOpen ν R) := hΨc2.smul contDiffOn_const
  have hF₁c2 : ContDiffOn ℝ 2 (fun x => φ₁ x • Z x) (youngOpen ν R) := hφ₁c.smul hZc2
  have hF₂c2 : ContDiffOn ℝ 2 (fun x => φ₂ x • G x) (youngOpen ν R) := hφ₂c.smul hGc2
  have hX_eq : wardX ν μ R c χy g τ = fun x => φ₁ x • Z x + φ₂ x • G x := by
    funext x
    rw [wardX_eq_cut_add_corr, wardStreamCorr_eq, mul_smul]
  have hadd := w112_physPd2_add_norm_le hUo hF₁c2 hF₂c2 j l hyU
  rw [← hX_eq] at hadd
  have hsm1 := w112_physPd2_smul_norm_le_c2 hUo hφ₁c hZc2 j l hyU
  have hsm2 := w112_physPd2_smul_norm_le_c2 hUo hφ₂c hGc2 j l hyU
  obtain ⟨hG0, hG1, hG2⟩ := w112_smul_e2_jets hUo hΨc2 hyU
  rw [hG0, hG1 j, hG1 l, hG2 j l] at hsm2
  obtain ⟨hc0, hc1, hc2⟩ := hcut y hy
  have hb1 : ‖physPd2 (fun x => φ₁ x • Z x) j l y‖ ≤
      C₁ * ‖physPd2 Z j l y‖ + C₁ * ‖physPd Z j y‖ + C₁ * ‖physPd Z l y‖ + C₁ * ‖Z y‖ := by
    refine hsm1.trans ?_
    have e1 := mul_le_mul_of_nonneg_right hc0 (norm_nonneg (physPd2 Z j l y))
    have e2 := mul_le_mul_of_nonneg_right (hc1 l) (norm_nonneg (physPd Z j y))
    have e3 := mul_le_mul_of_nonneg_right (hc1 j) (norm_nonneg (physPd Z l y))
    have e4 := mul_le_mul_of_nonneg_right (hc2 j l) (norm_nonneg (Z y))
    linarith
  have hb2 : ‖physPd2 (fun x => φ₂ x • G x) j l y‖ ≤
      (4 * C₂ * r2) * ‖physPd Z j y‖ + (4 * C₂ + 4 * C₂ * r2) * ‖Z y‖ +
        C₂ * w2N ν μ R c r2 g τ y := by
    refine hsm2.trans ?_
    by_cases hle : ϱ y ≤ r2
    · obtain ⟨hw0, hw1, hw2⟩ := hw2a_bd y hy
      obtain ⟨_, hψ1, hψ2⟩ := w112_psi_jet hν hR hc hμ hg τ hyU
      have hN : w2N ν μ R c r2 g τ y = |Ψ y| := by
        unfold w2N Ψ; simp only [hle, ↓reduceIte]
      rw [hN]
      have hρ0 : 0 ≤ ϱ y := ϱ_nonneg y
      have hp2 : |w112_sd2 Ψ j l y| ≤ 4 * r2 * ‖physPd Z j y‖ + 4 * ‖Z y‖ := by
        refine (hψ2 j l).trans ?_
        nlinarith [norm_nonneg (physPd Z j y)]
      have hp1l : |w112_sd1 Ψ l y| ≤ 2 * r2 * ‖Z y‖ := by
        refine (hψ1 l).2.trans ?_
        nlinarith [norm_nonneg (Z y)]
      have hp1j : |w112_sd1 Ψ j y| ≤ 2 * r2 * ‖Z y‖ := by
        refine (hψ1 j).2.trans ?_
        nlinarith [norm_nonneg (Z y)]
      have m1 : |φ₂ y| * |w112_sd2 Ψ j l y| ≤ C₂ * (4 * r2 * ‖physPd Z j y‖ + 4 * ‖Z y‖) :=
        mul_le_mul hw0 hp2 (abs_nonneg _) hC₂
      have m2 : |w112_sd1 φ₂ j y| * |w112_sd1 Ψ l y| ≤ C₂ * (2 * r2 * ‖Z y‖) :=
        mul_le_mul (hw1 j) hp1l (abs_nonneg _) hC₂
      have m3 : |w112_sd1 φ₂ l y| * |w112_sd1 Ψ j y| ≤ C₂ * (2 * r2 * ‖Z y‖) :=
        mul_le_mul (hw1 l) hp1j (abs_nonneg _) hC₂
      have m4 : |w112_sd2 φ₂ j l y| * |Ψ y| ≤ C₂ * |Ψ y| :=
        mul_le_mul_of_nonneg_right (hw2 j l) (abs_nonneg _)
      linarith
    · obtain ⟨hz0, hz1, hz2⟩ := hw2a_gt y (not_le.1 hle)
      change |w2a ν R χy (ϱ y)| * _ + |w112_sd1 (fun x => w2a ν R χy (ϱ x)) j y| * _ +
        |w112_sd1 (fun x => w2a ν R χy (ϱ x)) l y| * _ +
        |w112_sd2 (fun x => w2a ν R χy (ϱ x)) j l y| * _ ≤ _
      rw [hz0, hz1 j, hz1 l, hz2 j l]
      simp only [abs_zero, zero_mul, add_zero]
      have hZ0 := norm_nonneg (Z y)
      have hZj := norm_nonneg (physPd Z j y)
      have hN0 := w2N_nonneg ν μ R c r2 g τ y
      positivity
  linarith

/-- **`D²X ∈ Y₂` on the young support** (`PartIII-b:C/ward/11/2`, source 4194-4196, 5225-5235). -/
theorem wardD2XYoungL2_proved : WardD2XYoungL2 := by
  classical
  intro ν μ R c χy hχy hν hR hc hμ
  obtain ⟨CX0, hX0⟩ := wardX0YoungL2_proved ν μ R c hν hR hc hμ
  obtain ⟨CD2, hD2⟩ := wardD2X0YoungL2_proved ν μ R c hν hR hc hμ
  set r2 : ℝ := R * Real.sqrt (5 * ν / 4)
  have hr2nn : 0 ≤ r2 := by positivity
  obtain ⟨K, hK, hΨ⟩ := w2_psiBd hν hR hc hμ r2
  obtain ⟨C₁, hC₁, hcut⟩ := w112_cut_jet2_bound hχy hν hR
  obtain ⟨C₂, hC₂, hw2a_bd, hw2a_gt⟩ := w112_w2a_jet2_bound hχy hν hR
  set CX0' : ℝ := max CX0 0
  set CD2' : ℝ := max CD2 0
  have hCX0' : 0 ≤ CX0' := le_max_right _ _
  have hCD2' : 0 ≤ CD2' := le_max_right _ _
  set a1 : ℝ := C₁
  set a2 : ℝ := C₁ + 4 * C₂ * r2
  set a3 : ℝ := C₁
  set a4 : ℝ := C₁ + 4 * C₂ + 4 * C₂ * r2
  set a5 : ℝ := C₂
  have ha1 : 0 ≤ a1 := hC₁
  have ha2 : 0 ≤ a2 := by positivity
  have ha3 : 0 ≤ a3 := hC₁
  have ha4 : 0 ≤ a4 := by positivity
  have ha5 : 0 ≤ a5 := hC₂
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hUo : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  refine ⟨a1 * CD2' + a2 * CX0' + a3 * CX0' + a4 * CX0' + a5 * K, fun g hg j l => ?_⟩
  obtain ⟨hX0_val, hX0_pd⟩ := hX0 g hg
  have hD2_jl := hD2 g hg j l
  have b1 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a1 * wardYoungRead ν R (fun τ => physPd2 (wardX0 ν μ R c g τ) j l) q)
      (a1 * CD2') := by
    simpa [abs_of_nonneg ha1] using (wyl_bd_of_young hD2_jl).const_mul a1
  have b2 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a2 * wardYoungRead ν R (fun τ => physPd (wardX0 ν μ R c g τ) j) q)
      (a2 * CX0') := by
    simpa [abs_of_nonneg ha2] using (wyl_bd_of_young (hX0_pd j)).const_mul a2
  have b3 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a3 * wardYoungRead ν R (fun τ => physPd (wardX0 ν μ R c g τ) l) q)
      (a3 * CX0') := by
    simpa [abs_of_nonneg ha3] using (wyl_bd_of_young (hX0_pd l)).const_mul a3
  have b4 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a4 * wardYoungRead ν R (wardX0 ν μ R c g) q)
      (a4 * CX0') := by
    simpa [abs_of_nonneg ha4] using (wyl_bd_of_young hX0_val).const_mul a4
  have b5 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a5 * wardYoungRead ν R (w2Phi ν μ R c r2 g) q)
      (a5 * K) := by
    simpa [abs_of_nonneg ha5] using (hΨ g hg).const_mul a5
  have hc1 : 0 ≤ a1 * CD2' := mul_nonneg ha1 hCD2'
  have hc2 : 0 ≤ a2 * CX0' := mul_nonneg ha2 hCX0'
  have hc3 : 0 ≤ a3 * CX0' := mul_nonneg ha3 hCX0'
  have hc4 : 0 ≤ a4 * CX0' := mul_nonneg ha4 hCX0'
  have hc5 : 0 ≤ a5 * K := mul_nonneg ha5 hK
  have b12 := b1.add b2 hc1 hc2
  have b123 := b12.add b3 (add_nonneg hc1 hc2) hc3
  have b1234 := b123.add b4 (add_nonneg (add_nonneg hc1 hc2) hc3) hc4
  have b12345 := b1234.add b5 (add_nonneg (add_nonneg (add_nonneg hc1 hc2) hc3) hc4) hc5
  have hXm := w3_wardX_measurable ν μ R c hχy hg
  have hX3 : ∀ τ, ContDiffOn ℝ 3 (wardX ν μ R c χy g τ) (youngOpen ν R) :=
    fun τ => ((wardXDiff_proved ν μ R c χy hχy hν hR hc hμ g hg τ).1).mono
      (fun y hy => t9_not_axis hν hR hy)
  have hPd2m := w112_meas_pd2 hXm hUo hX3 j l
  have hread : wardYoungRead ν R (fun τ => physPd2 (wardX ν μ R c χy g τ) j l) =
      wardYoungRead ν R (fun τ y =>
        if y ∈ youngOpen ν R then physPd2 (wardX ν μ R c χy g τ) j l y else 0) := by
    refine w10_read_congr hν hR fun τ y hy => ?_
    have : y ∈ youngOpen ν R := lt_of_lt_of_le hrr hy
    simp [this]
  have hFm : AEStronglyMeasurable
      (wardYoungRead ν R (fun τ => physPd2 (wardX ν μ R c χy g τ) j l))
      (ageμ c (-3 / 2)) := by
    rw [hread]
    exact (w10_read_meas hPd2m).aestronglyMeasurable
  refine ⟨hFm, (eLpNorm_mono_real (fun q => ?_)).trans b12345.2⟩
  rw [Real.norm_of_nonneg (wyl_youngRead_nonneg _ _ _ q)]
  by_cases hq : ν * q.1 ≤ 1
  · rcases le_or_gt q.1 0 with hs | hs
    · rw [wyl_youngRead_zero_of_nonpos _ hs]
      have r1 := wyl_youngRead_nonneg ν R (fun τ => physPd2 (wardX0 ν μ R c g τ) j l) q
      have r2' := wyl_youngRead_nonneg ν R (fun τ => physPd (wardX0 ν μ R c g τ) j) q
      have r3 := wyl_youngRead_nonneg ν R (fun τ => physPd (wardX0 ν μ R c g τ) l) q
      have r4 := wyl_youngRead_nonneg ν R (wardX0 ν μ R c g) q
      have r5 := wyl_youngRead_nonneg ν R (w2Phi ν μ R c r2 g) q
      positivity
    · rw [wyl_youngRead_of_young _ hq, wyl_youngRead_of_young _ hq,
        wyl_youngRead_of_young _ hq, wyl_youngRead_of_young _ hq,
        wyl_youngRead_of_young _ hq, wyl_youngRead_of_young _ hq, w2Phi_norm]
      set τ := NearInst.chartTau R q
      set y := NearInst.chartY R q
      have hy : R * Real.sqrt ν ≤ ϱ y := wyl_young_ϱ hν hR hs hq
      have hpt := w112_wardX_pd2_pt_bound hχy hν hR hc hμ hC₁ hC₂ hcut hw2a_bd hw2a_gt hg τ j l hy
      have hinv : 0 ≤ (Real.sqrt q.1)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
      have hmul := mul_le_mul_of_nonneg_left hpt hinv
      linarith
  · have hqS : q ∉ wardYoungSet ν := hq
    have h0 : wardYoungRead ν R (fun τ => physPd2 (wardX ν μ R c χy g τ) j l) q = 0 := by
      unfold wardYoungRead
      rw [indicator_of_notMem hqS]
    rw [h0]
    have r1 := wyl_youngRead_nonneg ν R (fun τ => physPd2 (wardX0 ν μ R c g τ) j l) q
    have r2' := wyl_youngRead_nonneg ν R (fun τ => physPd (wardX0 ν μ R c g τ) j) q
    have r3 := wyl_youngRead_nonneg ν R (fun τ => physPd (wardX0 ν μ R c g τ) l) q
    have r4 := wyl_youngRead_nonneg ν R (wardX0 ν μ R c g) q
    have r5 := wyl_youngRead_nonneg ν R (w2Phi ν μ R c r2 g) q
    positivity

end UnforcedLeray.Short.PartIIIb.Concrete
end
