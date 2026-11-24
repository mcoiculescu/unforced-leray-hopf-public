import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.Pointwise.Calc

/-!
# `PartIII-b:C/rep/2/5`, leaf 1: `WGXPointwise` (source 4161-4192, 5212-5217)

Off the axis, `‖D(𝒞_y X₀)‖ ≤ 1_{ϱ≥L}‖DX₀‖ + C L⁻¹ 1_{ϱ≥L}‖X₀‖ + C L⁻³ 1_{ann}|Ψ_{X₀}|`.

* `ϱ < L`: `χ_y = 0 = χ_y'` near `y`, so `X = 0` there (`Cutoff.lean`).
* `ϱ > R√(5ν/4)`: `χ_y = 1`, `χ_y' = 0` near `y`, so `X = X₀`.
* otherwise (annulus): `X₀` is `C²` and the outward primitive `C¹` (`Source.lean`, `Decay.lean`:
  smoothness, divergence, axisymmetry and `StreamDecay` of the separated field), and
  `Calc.lean` gives `DX = χ_y DX₀ + X₀ ⊗ ∇χ_y + D(G(ϱ)Ψ e_z)` with the norm bound; the derivative of
  `Ψ` is `ϱ X₀_z Dϱ - ϱ X₀_r dy₃`, of norm `≤ 2ϱ‖X₀(ϱ,0,z)‖ = 2ϱ‖X₀(y)‖` by axisymmetry.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem wgx_rpow_neg_one {L : ℝ} : L ^ (-1 : ℝ) = L⁻¹ := Real.rpow_neg_one L

theorem wgx_rpow_neg_three {L : ℝ} (hL : 0 < L) : L ^ (-3 : ℝ) = (L⁻¹) ^ 3 := by
  rw [Real.rpow_neg hL.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]

theorem wgxPointwise : WGXPointwise := by
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
  have hX : sepWX ν μ R χy T τ = wardStreamCut ν R χy (sepX0 ν μ T) τ := rfl
  have hage : ∀ z : Space, ν * age R z = L ^ 2 / ϱ z ^ 2 := by
    intro z
    unfold age
    rw [← hLsq]; ring
  by_cases ha : ϱ y < L
  · -- `X = 0` near `y`
    have hU : IsOpen {z : Space | 0 < ϱ z ∧ ϱ z < L} :=
      (isOpen_lt continuous_const continuous_ϱ).inter (isOpen_lt continuous_ϱ continuous_const)
    have hev : sepWX ν μ R χy T τ =ᶠ[nhds y] fun _ => (0 : Space) := by
      filter_upwards [hU.mem_nhds (show y ∈ {z : Space | 0 < ϱ z ∧ ϱ z < L} from ⟨hy, ha⟩)]
        with z hz
      obtain ⟨hz0, hzL⟩ := hz
      have ht : 1 < ν * age R z := by
        rw [hage]
        exact (one_lt_div (by positivity)).2 (pow_lt_pow_left₀ hzL hz0.le two_ne_zero)
      rw [hX]
      unfold wardStreamCut
      rw [hχ.zero _ ht.le, (wgx_deriv_zero_gt hχ ht).1]
      simp
    rw [hev.fderiv_eq]
    simp
  · have hL1 : L ≤ ϱ y := not_lt.1 ha
    have hj1 : wgxJet 1 ν μ L T τ y = ENNReal.ofReal ‖fderiv ℝ (sepX0 ν μ T τ) y‖ := by
      unfold wgxJet
      rw [if_pos hL1, ← ofReal_norm_eq_enorm, norm_iteratedFDeriv_one]
    have hj0 : wgxJet 0 ν μ L T τ y = ENNReal.ofReal ‖sepX0 ν μ T τ y‖ := by
      unfold wgxJet
      rw [if_pos hL1, ← ofReal_norm_eq_enorm, norm_iteratedFDeriv_zero]
    rw [hj1, hj0]
    by_cases hb : R * Real.sqrt (5 * ν / 4) < ϱ y
    · -- `X = X₀` near `y`
      have hU : IsOpen {z : Space | R * Real.sqrt (5 * ν / 4) < ϱ z} :=
        isOpen_lt continuous_const continuous_ϱ
      have hev : sepWX ν μ R χy T τ =ᶠ[nhds y] sepX0 ν μ T τ := by
        filter_upwards [hU.mem_nhds hb] with z hz
        have hz0 : 0 < ϱ z := lt_of_lt_of_le (by positivity) hz.le
        have ht : ν * age R z < 4 / 5 := by
          rw [hage, div_lt_iff₀ (by positivity)]
          have hQs : (R * Real.sqrt (5 * ν / 4)) ^ 2 = R ^ 2 * (5 * ν / 4) := by
            rw [mul_pow, Real.sq_sqrt (by positivity)]
          have h2 : (R * Real.sqrt (5 * ν / 4)) ^ 2 < ϱ z ^ 2 :=
            pow_lt_pow_left₀ hz (by positivity) two_ne_zero
          nlinarith [hQs, hLsq]
        rw [hX]
        unfold wardStreamCut
        rw [hχ.one _ ht.le, (wgx_deriv_zero_lt hχ ht).1]
        simp
      rw [hev.fderiv_eq]
      calc ENNReal.ofReal ‖fderiv ℝ (sepX0 ν μ T τ) y‖
          ≤ ENNReal.ofReal ‖fderiv ℝ (sepX0 ν μ T τ) y‖ +
              ENNReal.ofReal ((18 * M1 + 4 * M2) * L ^ (-1 : ℝ)) *
                ENNReal.ofReal ‖sepX0 ν μ T τ y‖ := le_self_add
        _ ≤ _ := le_self_add
    · -- the annulus
      have hb' : ϱ y ≤ R * Real.sqrt (5 * ν / 4) := not_lt.1 hb
      have hyoung : R * Real.sqrt (5 * ν / 6) < ϱ y := lt_of_lt_of_le hrL hL1
      have hopen : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
      have hZc : ContDiffOn ℝ 2 (sepX0 ν μ T τ) (youngOpen ν R) :=
        wgx_sepX0_contDiffOn hν hμ' hr0 hP0 hT hSM τ
      have hZd : HasFDerivAt (sepX0 ν μ T τ) (fderiv ℝ (sepX0 ν μ T τ) y) y :=
        ((hZc.contDiffAt (hopen.mem_nhds hyoung)).differentiableAt (by norm_num)).hasFDerivAt
      have hdr := fun r z (hr : R * Real.sqrt (5 * ν / 6) < r) =>
        wgx_sepX0_partials hν hR hμ' hP0 hT hSM hAx τ r z hr
      have hΨ := wgx_outPrim_hasFDerivAt hν hR hZc hdr hyoung
      obtain ⟨hfr, hnorm⟩ := wgx_sepX0_axi hν hμ' hr0 hP0 hT hSM hAx τ y hyoung
      have hρ0 : 0 < ϱ y := lt_of_lt_of_le hL hL1
      have hΨb : ‖(ϱ y * sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 2) • ϱD y +
          (-(ϱ y * sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 0)) •
            (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)‖ ≤ 2 * ϱ y * ‖sepX0 ν μ T τ y‖ := by
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
        have hn' : ‖sepX0 ν μ T τ !₂[ϱ y, 0, y 2]‖ = ‖sepX0 ν μ T τ y‖ := hnorm
        have h2 : |sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 2| ≤ ‖sepX0 ν μ T τ y‖ :=
          (wgx_abs_apply_le _ 2).trans hn'.le
        have h0 : |sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 0| ≤ ‖sepX0 ν μ T τ y‖ :=
          (wgx_abs_apply_le _ 0).trans hn'.le
        have hv := wgx_ϱD_le hρ0 v
        have hv2 := wgx_abs_apply_le v 2
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
          EuclideanSpace.coe_proj, Real.norm_eq_abs]
        calc |ϱ y * sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 2 * ϱD y v +
              -(ϱ y * sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 0) * v 2|
            ≤ |ϱ y * sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 2 * ϱD y v| +
              |-(ϱ y * sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 0) * v 2| := abs_add_le _ _
          _ = ϱ y * |sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 2| * |ϱD y v| +
              ϱ y * |sepX0 ν μ T τ !₂[ϱ y, 0, y 2] 0| * |v 2| := by
              simp only [abs_mul, abs_neg, abs_of_pos hρ0]
          _ ≤ ϱ y * ‖sepX0 ν μ T τ y‖ * ‖v‖ + ϱ y * ‖sepX0 ν μ T τ y‖ * ‖v‖ := by
              gcongr
          _ = 2 * ϱ y * ‖sepX0 ν μ T τ y‖ * ‖v‖ := by ring
      obtain ⟨D, hD, hDb⟩ := wgx_cut_hasFDerivAt hχ hM1 hM2 hν hL hLsq hL1 hZd hΨ hΨb
      have hfd : fderiv ℝ (sepWX ν μ R χy T τ) y = D := hD.fderiv
      rw [hfd]
      have hmem : y ∈ streamAnn ν R := ⟨hL1, hb'⟩
      have hψ : wgxPsi ν μ R T τ y =
          ENNReal.ofReal |outPrim (sepX0 ν μ T) τ (ϱ y) (y 2)| := by
        unfold wgxPsi
        rw [Set.indicator_of_mem hmem]
      rw [hψ]
      -- real inequality
      set Zn := ‖sepX0 ν μ T τ y‖ with hZn
      set Zdn := ‖fderiv ℝ (sepX0 ν μ T τ) y‖ with hZdn
      set Pn := |outPrim (sepX0 ν μ T) τ (ϱ y) (y 2)| with hPn
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
