import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2_1

/-!
# Part III-a, `PartIII-a:T21/2/2/2`: the conditional assembly of `AdjointE0Ineq`

Source of record: `the November 2 reference manuscript` lines 3060-3066.

`adjointE0Ineq_of` derives `AdjointE0Ineq m` (`E_0' + β_min E_1 ≤ C_b E_0` on `(0, Δz)`) from the
leaves of `E0/Defs.lean`, the age map `AdjAgeMap` (`Sub/T21_2_2_1.lean`) and
`RescaledTrainBounds m`. At `ζ ∈ (0, Δz)`, with `r = revAge ν s ζ ∈ [t, s)`:
`θ(r) ≥ θ(s) ≥ b ≥ 1` and `β_min = ν a_t ≤ ν a_r = θ(r)⁻¹`; `AdjE0Reynolds` gives
`E_0' = rate0 … (∂_ζΦ + (2θ)⁻¹ y·∇Φ)`, `MovingAdjointEq` (with the interaction `χ` of
`AdjChiWeighted`) identifies `∂_ζΦ + (2θ)⁻¹ y·∇Φ = adjPsi θ Φ χ V` a.e. on the cell, and
`CellRateReduce`, `CellRateEstimate` bound the rate.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-- The moving adjoint equation turns the dilation derivative into `adjPsi` (pointwise algebra:
`θ⁻¹(Δ - ½ y·∇ + 1) + (2θ)⁻¹ y·∇ = θ⁻¹(Δ + 1)`). -/
theorem revDt_add_dil_eq {θ : ℝ} {Φ χ : ℝ × ℝ → ℂ} {V : ℝ × ℝ → Fin 2 → ℝ} {y : ℝ × ℝ}
    {D : ℂ} (hD : D = ((θ⁻¹ : ℝ) : ℂ) * dSharp Φ y + transCx V Φ y - χ y) :
    D + (((2 * θ)⁻¹ : ℝ) : ℂ) * dilCx Φ y = adjPsi θ Φ χ V y := by
  rw [hD]
  unfold adjPsi dSharp
  push_cast
  ring

theorem adjointE0Ineq_of (m : ℝ) (hT : RescaledTrainBounds m) (hA : AdjAgeMap)
    (hLB : LadTrainBddAll m) (hEq : MovingAdjointEq m) (hR : AdjE0Reynolds m) (hReg : RevPhiReg m)
    (hTr : MovingTrainReg) (hWB : AdjWeightBounds m) (hX : AdjChiWeighted m)
    (hRed : CellRateReduce) (hEst : CellRateEstimate) : AdjointE0Ineq m := by
  obtain ⟨K, hK0, hWK⟩ := hWB
  obtain ⟨νB, hνB, hLBν⟩ := hLB
  obtain ⟨bT, hT⟩ := hT
  obtain ⟨bX, hX⟩ := hX
  refine ⟨max 1 (max bT bX), fun b hb => ?_⟩
  have hb1 : 1 ≤ b := le_trans (le_max_left _ _) hb
  have hbT : bT ≤ b := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hb
  have hbX : bX ≤ b := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hb
  obtain ⟨CV, νT, hνT, hT'⟩ := hT b hbT
  obtain ⟨CX, νX, hCX, hνX, hX'⟩ := hX b hbX
  obtain ⟨C, hC0, hEst'⟩ := hEst m K (max CV 0) CX hK0 (le_max_right _ _) hCX
  refine ⟨C, min (min νT νX) (min νB 1), hC0, lt_min (lt_min hνT hνX) (lt_min hνB one_pos), ?_⟩
  intro ν hν tr htr t s ht hts _ hbs G _ φ hφ ζ hζ
  have hν0 : 0 < ν := hν.1
  have hνT' : ν ∈ Ioc 0 νT :=
    ⟨hν0, hν.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hνX' : ν ∈ Ioc 0 νX :=
    ⟨hν0, hν.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hν1 : ν ≤ 1 := hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hνB' : ν ∈ Ioc 0 νB :=
    ⟨hν0, hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hLBν' := hLBν ν hνB' tr htr
  -- the age `r = revAge ν s ζ ∈ [t, s)` and the clock facts
  have hr : revAge ν s ζ ∈ Ico t s := (hA ν t s hν0 ht hts).2.2 ⟨hζ.1, hζ.2.le⟩
  have hr0 : 0 ≤ revAge ν s ζ := ht.trans hr.1
  have ha_pos : 0 < clockA ν (revAge ν s ζ) := by
    unfold clockA
    have := mul_nonneg hν0.le hr0
    linarith
  have hθ_le : clockTheta ν s ≤ clockTheta ν (revAge ν s ζ) := by
    unfold clockTheta
    refine inv_anti₀ (mul_pos hν0 ha_pos) ?_
    unfold clockA
    have := mul_le_mul_of_nonneg_left hr.2.le hν0.le
    nlinarith
  have hbr : b ≤ clockTheta ν (revAge ν s ζ) := hbs.trans hθ_le
  have hθ1 : 1 ≤ revTheta ν s ζ := hb1.trans hbr
  have hθpos : 0 < revTheta ν s ζ := lt_of_lt_of_le one_pos hθ1
  have hβ : betaMin ν t ≤ (revTheta ν s ζ)⁻¹ := by
    unfold revTheta betaMin clockTheta
    rw [inv_inv]
    unfold clockA
    have := mul_le_mul_of_nonneg_left hr.1 hν0.le
    nlinarith
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν0 _
  have hd : 0 < revCell ν (ν ^ (-2 : ℝ)) s ζ := div_pos hc (Real.sqrt_pos.2 ha_pos)
  -- the moving adjoint at `ζ`
  obtain ⟨hF, hΦX⟩ := hReg ν hν0 tr t s ht hts _ φ hφ (revAge ν s ζ) hr
  have hF' : CellField m (revCell ν (ν ^ (-2 : ℝ)) s ζ) (revPhi ν φ s ζ) := hF
  -- the interaction
  obtain ⟨χ, hχX, hχm, hχI, hχint, hχb⟩ := hX' ν hνX' tr htr (revAge ν s ζ) hr0 hbr _ hΦX
  have hae := hEq ν hν0 tr t s ht hts _ φ hφ hν1 hLBν' ζ hζ χ hχX hχI
  obtain ⟨hRint, hRder⟩ := hR ν hν0 tr t s ht hts _ φ hφ ζ hζ
  -- the drift
  obtain ⟨hVs, hVp, hVd⟩ := hTr ν (ν ^ (-2 : ℝ)) hν0 hc tr (revAge ν s ζ) hr0
  have hVb : ∀ (y : ℝ × ℝ) (k : Fin 2), |movingTrainV tr (revAge ν s ζ) y k| ≤ max CV 0 := by
    intro y k
    have h0 := (hT' ν hνT' tr htr (revAge ν s ζ) hr0 hbr).1 0 (by norm_num) y
    rw [norm_iteratedFDeriv_zero] at h0
    have h1 : ‖movingTrainV tr (revAge ν s ζ) y k‖ ≤ ‖movingTrainV tr (revAge ν s ζ) y‖ :=
      norm_le_pi_norm _ k
    rw [Real.norm_eq_abs] at h1
    exact (h1.trans h0).trans (le_max_left _ _)
  have hDrift : CellDrift (revCell ν (ν ^ (-2 : ℝ)) s ζ) (max CV 0)
      (movingTrainV tr (revAge ν s ζ)) := ⟨hVs, hVp, hVd, hVb⟩
  -- identify the dilation derivative a.e.
  have hΨ : (fun y => revDt ν φ s ζ y +
        (((2 * revTheta ν s ζ)⁻¹ : ℝ) : ℂ) * dilCx (revPhi ν φ s ζ) y)
      =ᵐ[volume.restrict (B0579.cell (revCell ν (ν ^ (-2 : ℝ)) s ζ))]
        adjPsi (revTheta ν s ζ) (revPhi ν φ s ζ) χ (movingTrainV tr (revAge ν s ζ)) := by
    filter_upwards [hae] with y hy
    exact revDt_add_dil_eq hy.deriv
  have hwΨ : wRe m (revCell ν (ν ^ (-2 : ℝ)) s ζ) (revPhi ν φ s ζ)
        (fun y => revDt ν φ s ζ y +
          (((2 * revTheta ν s ζ)⁻¹ : ℝ) : ℂ) * dilCx (revPhi ν φ s ζ) y)
      =ᵐ[volume.restrict (B0579.cell (revCell ν (ν ^ (-2 : ℝ)) s ζ))]
        wRe m (revCell ν (ν ^ (-2 : ℝ)) s ζ) (revPhi ν φ s ζ)
          (adjPsi (revTheta ν s ζ) (revPhi ν φ s ζ) χ (movingTrainV tr (revAge ν s ζ))) := by
    filter_upwards [hΨ] with y hy
    simp only [wRe]
    rw [hy]
  have hint2 : IntegrableOn (wRe m (revCell ν (ν ^ (-2 : ℝ)) s ζ) (revPhi ν φ s ζ)
      (adjPsi (revTheta ν s ζ) (revPhi ν φ s ζ) χ (movingTrainV tr (revAge ν s ζ))))
      (B0579.cell (revCell ν (ν ^ (-2 : ℝ)) s ζ)) := Integrable.congr hRint hwΨ
  have hrate : rate0 m (revCell ν (ν ^ (-2 : ℝ)) s ζ) (revTheta ν s ζ) (revPhi ν φ s ζ)
        (fun y => revDt ν φ s ζ y +
          (((2 * revTheta ν s ζ)⁻¹ : ℝ) : ℂ) * dilCx (revPhi ν φ s ζ) y) =
      rate0 m (revCell ν (ν ^ (-2 : ℝ)) s ζ) (revTheta ν s ζ) (revPhi ν φ s ζ)
        (adjPsi (revTheta ν s ζ) (revPhi ν φ s ζ) χ (movingTrainV tr (revAge ν s ζ))) := by
    unfold rate0
    rw [integral_congr_ae hwΨ]
  have hWd := hWK _ hd
  refine ⟨_, hRder, ?_⟩
  rw [hrate, hRed m K (max CV 0) _ _ _ χ _ hd hθpos hWd hF' hDrift hχm hχint hint2]
  have hest := hEst' _ _ _ χ _ hd hθ1 hWd hF' hDrift hχm hχint hχb
  have hE1 := adjE1_nonneg (revCell ν (ν ^ (-2 : ℝ)) s ζ) m (revPhi ν φ s ζ)
  have hβE : betaMin ν t * revE1 ν (ν ^ (-2 : ℝ)) m φ s ζ ≤
      (revTheta ν s ζ)⁻¹ * adjE1 (revCell ν (ν ^ (-2 : ℝ)) s ζ) m (revPhi ν φ s ζ) :=
    mul_le_mul_of_nonneg_right hβ hE1
  have hE0 : revE0 ν (ν ^ (-2 : ℝ)) m φ s ζ =
      adjE0 (revCell ν (ν ^ (-2 : ℝ)) s ζ) m (revPhi ν φ s ζ) := rfl
  rw [hE0]
  linarith

end UnforcedLeray.Short.IIIa.E0
