import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L7_WardGradYPhase.WreDecay
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.Pointwise
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.Pointwise.Calc
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.Pointwise.Cutoff

/-!
# `PartIII-b:C/rep/2/7`, the pointwise bound for `D(𝒞_y Re W_μ)`

Source `the November 2 reference manuscript` 4181-4192, 5212-5217.  Verbatim analogue
of `wgxPointwise` (`PartIII-b_C_rep_2_5/Pointwise.lean`) with `Re W_μ` in place of `X₀`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The slice density `1_{rIn ≤ |y'|} ‖D^j Re W_μ(τ)‖`. -/
def wgyWJet (j : ℕ) (ν μ rIn : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    (y : Space) : ℝ≥0∞ :=
  if rIn ≤ ϱ y then ‖iteratedFDeriv ℝ j (sepWre ν μ T τ) y‖ₑ else 0

/-- The slice density `1_{annulus} |Ψ_{Re W_μ}(τ, |y'|, y₃)|`. -/
def wgyWPsi (ν μ R : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space) :
    ℝ≥0∞ :=
  (streamAnn ν R).indicator
    (fun y => ENNReal.ofReal |outPrim (sepWre ν μ T) τ (ϱ y) (y 2)|) y

/-- Leaf: differentiability and the pointwise bound for the cut of `Re W_μ`. -/
def WGYCutPointwise : Prop :=
  ∀ σ₁ σ₂ : ℝ, -(1 / 4) < σ₁ → ∀ χy : ℝ → ℝ, IsStreamCutoff χy → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ν μ R P : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R → 0 < P → P ≤ 1 → μ ∈ Icc σ₁ σ₂ →
      ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → IsAxiSource T →
        ∀ (τ : ℝ) (y : Space), 0 < ϱ y →
          DifferentiableAt ℝ (wardStreamCut ν R χy (sepWre ν μ T) τ) y ∧
          ENNReal.ofReal ‖fderiv ℝ (wardStreamCut ν R χy (sepWre ν μ T) τ) y‖ ≤
            wgyWJet 1 ν μ (R * Real.sqrt ν) T τ y +
              ENNReal.ofReal (C * (R * Real.sqrt ν) ^ (-1 : ℝ)) *
                wgyWJet 0 ν μ (R * Real.sqrt ν) T τ y +
              ENNReal.ofReal (C * (R * Real.sqrt ν) ^ (-3 : ℝ)) * wgyWPsi ν μ R T τ y

theorem wgyCutPointwise : WGYCutPointwise := by
  intro σ₁ σ₂ hσ χy hχ
  obtain ⟨M1, M2, hM1n, hM2n, hM1, hM2⟩ := wgx_chi_bounds hχ
  refine ⟨18 * M1 + 4 * M2, by positivity, ?_⟩
  intro ν μ R P hν hν1 hR1 hP0 hP1 hμ T hT hSM hAx τ y hy
  have hR : 0 < R := by linarith
  set L : ℝ := R * Real.sqrt ν with hLdef
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hL : 0 < L := by rw [hLdef]; positivity
  have hLsq : ν * R ^ 2 = L ^ 2 := by
    rw [hLdef, mul_pow, Real.sq_sqrt hν.le]; ring
  have hμ' : -(1 / 4) < μ := lt_of_lt_of_le hσ hμ.1
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hrL : R * Real.sqrt (5 * ν / 6) < L := by
    rw [hLdef]
    exact mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hLQ : L ≤ R * Real.sqrt (5 * ν / 4) := by
    rw [hLdef]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) hR.le
  have hQ2L : R * Real.sqrt (5 * ν / 4) ≤ 2 * L := by
    rw [hLdef]
    have : Real.sqrt (5 * ν / 4) ≤ 2 * Real.sqrt ν := by
      rw [show (2 : ℝ) * Real.sqrt ν = Real.sqrt (2 ^ 2 * ν) by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    calc R * Real.sqrt (5 * ν / 4) ≤ R * (2 * Real.sqrt ν) := by gcongr
      _ = 2 * (R * Real.sqrt ν) := by ring
  have hage : ∀ z : Space, ν * age R z = L ^ 2 / ϱ z ^ 2 := by
    intro z
    unfold age
    rw [← hLsq]; ring
  by_cases ha : ϱ y < L
  · -- `X = 0` near `y`
    have hU : IsOpen {z : Space | 0 < ϱ z ∧ ϱ z < L} :=
      (isOpen_lt continuous_const continuous_ϱ).inter (isOpen_lt continuous_ϱ continuous_const)
    have hev : wardStreamCut ν R χy (sepWre ν μ T) τ =ᶠ[nhds y] fun _ => (0 : Space) := by
      filter_upwards [hU.mem_nhds (show y ∈ {z : Space | 0 < ϱ z ∧ ϱ z < L} from ⟨hy, ha⟩)]
        with z hz
      obtain ⟨hz0, hzL⟩ := hz
      have ht : 1 < ν * age R z := by
        rw [hage]
        exact (one_lt_div (by positivity)).2 (pow_lt_pow_left₀ hzL hz0.le two_ne_zero)
      unfold wardStreamCut
      rw [hχ.zero _ ht.le, (wgx_deriv_zero_gt hχ ht).1]
      simp
    refine ⟨(differentiableAt_const (0 : Space)).congr_of_eventuallyEq hev, ?_⟩
    rw [hev.fderiv_eq]
    simp
  · have hL1 : L ≤ ϱ y := not_lt.1 ha
    have hj1 : wgyWJet 1 ν μ L T τ y = ENNReal.ofReal ‖fderiv ℝ (sepWre ν μ T τ) y‖ := by
      unfold wgyWJet
      rw [if_pos hL1, ← ofReal_norm_eq_enorm, norm_iteratedFDeriv_one]
    have hj0 : wgyWJet 0 ν μ L T τ y = ENNReal.ofReal ‖sepWre ν μ T τ y‖ := by
      unfold wgyWJet
      rw [if_pos hL1, ← ofReal_norm_eq_enorm, norm_iteratedFDeriv_zero]
    rw [hj1, hj0]
    by_cases hb : R * Real.sqrt (5 * ν / 4) < ϱ y
    · -- `X = X₀` near `y`
      have hU : IsOpen {z : Space | R * Real.sqrt (5 * ν / 4) < ϱ z} :=
        isOpen_lt continuous_const continuous_ϱ
      have hev : wardStreamCut ν R χy (sepWre ν μ T) τ =ᶠ[nhds y] sepWre ν μ T τ := by
        filter_upwards [hU.mem_nhds hb] with z hz
        have hz0 : 0 < ϱ z := lt_of_lt_of_le (by positivity) hz.le
        have ht : ν * age R z < 4 / 5 := by
          rw [hage, div_lt_iff₀ (by positivity)]
          have hQs : (R * Real.sqrt (5 * ν / 4)) ^ 2 = R ^ 2 * (5 * ν / 4) := by
            rw [mul_pow, Real.sq_sqrt (by positivity)]
          have h2 : (R * Real.sqrt (5 * ν / 4)) ^ 2 < ϱ z ^ 2 :=
            pow_lt_pow_left₀ hz (by positivity) two_ne_zero
          nlinarith [hQs, hLsq]
        unfold wardStreamCut
        rw [hχ.one _ ht.le, (wgx_deriv_zero_lt hχ ht).1]
        simp
      have hopen' : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
      have hdW : DifferentiableAt ℝ (sepWre ν μ T τ) y :=
        (((wgyw_contDiffOn hν hμ' hr0 hP0 hT hSM τ).contDiffAt
          (hopen'.mem_nhds (lt_of_lt_of_le hrL hL1))).differentiableAt (by norm_num))
      refine ⟨hdW.congr_of_eventuallyEq hev, ?_⟩
      rw [hev.fderiv_eq]
      calc ENNReal.ofReal ‖fderiv ℝ (sepWre ν μ T τ) y‖
          ≤ ENNReal.ofReal ‖fderiv ℝ (sepWre ν μ T τ) y‖ +
              ENNReal.ofReal ((18 * M1 + 4 * M2) * L ^ (-1 : ℝ)) *
                ENNReal.ofReal ‖sepWre ν μ T τ y‖ := le_self_add
        _ ≤ _ := le_self_add
    · -- the annulus
      have hb' : ϱ y ≤ R * Real.sqrt (5 * ν / 4) := not_lt.1 hb
      have hyoung : R * Real.sqrt (5 * ν / 6) < ϱ y := lt_of_lt_of_le hrL hL1
      have hopen : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
      have hZc : ContDiffOn ℝ 2 (sepWre ν μ T τ) (youngOpen ν R) :=
        wgyw_contDiffOn hν hμ' hr0 hP0 hT hSM τ
      have hZd : HasFDerivAt (sepWre ν μ T τ) (fderiv ℝ (sepWre ν μ T τ) y) y :=
        ((hZc.contDiffAt (hopen.mem_nhds hyoung)).differentiableAt (by norm_num)).hasFDerivAt
      have hdr := fun r z (hr : R * Real.sqrt (5 * ν / 6) < r) =>
        wgyw_partials hν hR hμ' hP0 hT hSM hAx τ r z hr
      have hΨ := wgx_outPrim_hasFDerivAt hν hR hZc hdr hyoung
      obtain ⟨hfr, hnorm⟩ := wgyw_axi hν hμ' hr0 hP0 hT hSM hAx τ y hyoung
      have hρ0 : 0 < ϱ y := lt_of_lt_of_le hL hL1
      have hΨb : ‖(ϱ y * sepWre ν μ T τ !₂[ϱ y, 0, y 2] 2) • ϱD y +
          (-(ϱ y * sepWre ν μ T τ !₂[ϱ y, 0, y 2] 0)) •
            (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)‖ ≤ 2 * ϱ y * ‖sepWre ν μ T τ y‖ := by
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
        have hn' : ‖sepWre ν μ T τ !₂[ϱ y, 0, y 2]‖ = ‖sepWre ν μ T τ y‖ := hnorm
        have h2 : |sepWre ν μ T τ !₂[ϱ y, 0, y 2] 2| ≤ ‖sepWre ν μ T τ y‖ :=
          (wgx_abs_apply_le _ 2).trans hn'.le
        have h0 : |sepWre ν μ T τ !₂[ϱ y, 0, y 2] 0| ≤ ‖sepWre ν μ T τ y‖ :=
          (wgx_abs_apply_le _ 0).trans hn'.le
        have hv := wgx_ϱD_le hρ0 v
        have hv2 := wgx_abs_apply_le v 2
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
          EuclideanSpace.coe_proj, Real.norm_eq_abs]
        calc |ϱ y * sepWre ν μ T τ !₂[ϱ y, 0, y 2] 2 * ϱD y v +
              -(ϱ y * sepWre ν μ T τ !₂[ϱ y, 0, y 2] 0) * v 2|
            ≤ |ϱ y * sepWre ν μ T τ !₂[ϱ y, 0, y 2] 2 * ϱD y v| +
              |-(ϱ y * sepWre ν μ T τ !₂[ϱ y, 0, y 2] 0) * v 2| := abs_add_le _ _
          _ = ϱ y * |sepWre ν μ T τ !₂[ϱ y, 0, y 2] 2| * |ϱD y v| +
              ϱ y * |sepWre ν μ T τ !₂[ϱ y, 0, y 2] 0| * |v 2| := by
              simp only [abs_mul, abs_neg, abs_of_pos hρ0]
          _ ≤ ϱ y * ‖sepWre ν μ T τ y‖ * ‖v‖ + ϱ y * ‖sepWre ν μ T τ y‖ * ‖v‖ := by
              gcongr
          _ = 2 * ϱ y * ‖sepWre ν μ T τ y‖ * ‖v‖ := by ring
      obtain ⟨D, hD, hDb⟩ := wgx_cut_hasFDerivAt hχ hM1 hM2 hν hL hLsq hL1 hZd hΨ hΨb
      have hfd : fderiv ℝ (wardStreamCut ν R χy (sepWre ν μ T) τ) y = D := hD.fderiv
      refine ⟨hD.differentiableAt, ?_⟩
      rw [hfd]
      have hmem : y ∈ streamAnn ν R := ⟨hL1, hb'⟩
      have hψ : wgyWPsi ν μ R T τ y =
          ENNReal.ofReal |outPrim (sepWre ν μ T) τ (ϱ y) (y 2)| := by
        unfold wgyWPsi
        rw [Set.indicator_of_mem hmem]
      rw [hψ]
      -- real inequality
      set Zn := ‖sepWre ν μ T τ y‖ with hZn
      set Zdn := ‖fderiv ℝ (sepWre ν μ T τ) y‖ with hZdn
      set Pn := |outPrim (sepWre ν μ T) τ (ϱ y) (y 2)| with hPn
      have hℓ : 0 < L⁻¹ := inv_pos.2 hL
      have hLℓ : L * L⁻¹ = 1 := mul_inv_cancel₀ hL.ne'
      have hϱ2 : ϱ y ≤ 2 * L := hb'.trans hQ2L
      have hZn0 : 0 ≤ Zn := norm_nonneg _
      have hPn0 : 0 ≤ Pn := abs_nonneg _
      have hkey : ‖D‖ ≤ Zdn + (18 * M1 + 4 * M2) * L ^ (-1 : ℝ) * Zn +
          (18 * M1 + 4 * M2) * L ^ (-3 : ℝ) * Pn := by
        rw [wgx_rpow_neg_one, wgx_rpow_neg_three hL]
        have h1 : 2 * M1 * (L⁻¹) ^ 2 * (2 * ϱ y * Zn) ≤ 2 * M1 * (L⁻¹) ^ 2 * (4 * L * Zn) :=
          mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_right hϱ2 hZn0])
            (by positivity)
        have h2 : 2 * M1 * (L⁻¹) ^ 2 * (4 * L * Zn) = 8 * M1 * L⁻¹ * Zn := by
          have : L * L⁻¹ = 1 := hLℓ
          calc 2 * M1 * (L⁻¹) ^ 2 * (4 * L * Zn) = 8 * M1 * L⁻¹ * Zn * (L * L⁻¹) := by ring
            _ = 8 * M1 * L⁻¹ * Zn := by rw [this, mul_one]
        have h3 : 2 * M1 * (L⁻¹) ^ 2 * (2 * ϱ y * Zn) =
            2 * M1 * (L⁻¹) ^ 2 * (2 * ϱ y * Zn) := rfl
        have h4 : 0 ≤ (L⁻¹) ^ 3 * Pn := by positivity
        have h5 : 0 ≤ L⁻¹ * Zn := by positivity
        nlinarith [hDb, h1, h2, h4, h5, mul_nonneg hM1n h5, mul_nonneg hM2n h4,
          mul_nonneg hM1n h4]
      have hE : ENNReal.ofReal ‖D‖ ≤ ENNReal.ofReal Zdn +
          ENNReal.ofReal ((18 * M1 + 4 * M2) * L ^ (-1 : ℝ)) * ENNReal.ofReal Zn +
          ENNReal.ofReal ((18 * M1 + 4 * M2) * L ^ (-3 : ℝ)) * ENNReal.ofReal Pn := by
        have hc1 : 0 ≤ (18 * M1 + 4 * M2) * L ^ (-1 : ℝ) := by positivity
        have hc3 : 0 ≤ (18 * M1 + 4 * M2) * L ^ (-3 : ℝ) := by positivity
        rw [← ENNReal.ofReal_mul hc1, ← ENNReal.ofReal_mul hc3,
          ← ENNReal.ofReal_add (norm_nonneg _) (mul_nonneg hc1 hZn0),
          ← ENNReal.ofReal_add (add_nonneg (norm_nonneg _) (mul_nonneg hc1 hZn0))
            (mul_nonneg hc3 hPn0)]
        exact ENNReal.ofReal_le_ofReal (by linarith [hkey])
      exact hE

end UnforcedLeray.Short.PartIIIb.Concrete

end
