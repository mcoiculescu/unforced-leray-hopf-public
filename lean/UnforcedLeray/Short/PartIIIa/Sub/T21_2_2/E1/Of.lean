import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Defs

/-!
# Part III-a, `PartIII-a:T21/2/2/3`: the conditional assembly of the `E_1` inequality

Source of record: `the November 2 reference manuscript` lines 3060-3071
(`E_1' + β_min E_2 ≤ C_b(E_1 + E_0)`), 3077-3080 (`β_min = ν a_t`).

`adjointE1Ineq_of` derives `AdjointE1Ineq m` from the leaves of `E1/Defs.lean`, the age map
`AdjAgeMap` (`Sub/T21_2_2_1.lean`) and `RescaledTrainBounds m`. At `ζ ∈ (0, Δz)` the age
`r = revAge ν s ζ` lies in `[t, s)`, so `θ(r) ≥ θ(s) ≥ b`, `β = ν a(r) ∈ [β_min, 1]` (for `b ≥ 1`);
the moving equation provides `χ`, the interaction leaf bounds `Σ_k ∫ w|∂_kχ|²`, the derivative leaf
gives `E_1' = e1Rate`, and the remainder bound gives `e1Rate + β E_2 ≤ K(E_1 + E_0)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

theorem adjointE1Ineq_of (m : ℝ) (hT : RescaledTrainBounds m) (hA : AdjAgeMap)
    (hLB : LadTrainBddAll m) (hV : MovingTrainVReg) (hEq : MovAdjEquation m) (hLo : MovAdjBasicReg m)
    (hHi : MovAdjHigherReg m) (hD : E1MovingDeriv m) (hC : AdjChiDerivBound m)
    (hR : E1RemainderBound m) (hm : 0 ≤ m) : AdjointE1Ineq m := by
  obtain ⟨νB, hνB, hLBν⟩ := hLB
  obtain ⟨bT, hT⟩ := hT
  obtain ⟨bC, hC⟩ := hC hm
  refine ⟨max (max bT bC) 1, fun b hb => ?_⟩
  have hbT : bT ≤ b := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hb
  have hbC : bC ≤ b := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hb
  have hb1 : (1 : ℝ) ≤ b := le_trans (le_max_right _ _) hb
  obtain ⟨CT, νT, hνT, hT'⟩ := hT b hbT
  obtain ⟨Kχ, νC, _hKχ, hνC, hC'⟩ := hC b hbC
  obtain ⟨K, hK, hR'⟩ := hR CT Kχ
  refine ⟨K, min (min νT νC) (min νB 1), hK, lt_min (lt_min hνT hνC) (lt_min hνB one_pos), ?_⟩
  intro ν hν tr htr t s ht hts _hst hbs G hG φ hφ ζ hζ
  have hν0 : 0 < ν := hν.1
  obtain ⟨_, _, hmaps⟩ := hA ν t s hν0 ht hts
  have hr : revAge ν s ζ ∈ Ico t s := hmaps (Ioo_subset_Ioc_self hζ)
  have hr0 : 0 ≤ revAge ν s ζ := ht.trans hr.1
  have ha : 0 < clockA ν (revAge ν s ζ) := by
    unfold clockA
    have : 0 ≤ ν * revAge ν s ζ := mul_nonneg hν0.le hr0
    linarith
  have has : clockA ν (revAge ν s ζ) ≤ clockA ν s := by
    unfold clockA
    have : ν * revAge ν s ζ ≤ ν * s := mul_le_mul_of_nonneg_left hr.2.le hν0.le
    linarith
  have hβ : 0 < ν * clockA ν (revAge ν s ζ) := mul_pos hν0 ha
  have hθ : b ≤ clockTheta ν (revAge ν s ζ) := by
    refine hbs.trans ?_
    unfold clockTheta
    exact inv_anti₀ hβ (mul_le_mul_of_nonneg_left has hν0.le)
  have hβ1 : ν * clockA ν (revAge ν s ζ) ≤ 1 := by
    have h1 : (1 : ℝ) ≤ (ν * clockA ν (revAge ν s ζ))⁻¹ := hb1.trans hθ
    have h2 := inv_le_one_of_one_le₀ h1
    rwa [inv_inv] at h2
  have hβt : betaMin ν t ≤ mvBeta ν s ζ := by
    unfold betaMin mvBeta clockA
    have : ν * t ≤ ν * revAge ν s ζ := mul_le_mul_of_nonneg_left hr.1 hν0.le
    exact mul_le_mul_of_nonneg_left (by linarith) hν0.le
  have hd : 0 < mvLen ν (ν ^ (-2 : ℝ)) s ζ := by
    unfold mvLen cellLen
    exact div_pos (Real.rpow_pos_of_pos hν0 _) (Real.sqrt_pos.mpr ha)
  have hflow : AdjFlowAt m ν tr t s φ ζ := ⟨hν0, ht, hts, ⟨G, hG, hφ⟩, hζ⟩
  have hνB' : ν ∈ Ioc 0 νB := ⟨hν0, hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  obtain ⟨χ, hχC, hχP, hχI, hχD⟩ :=
    hEq ν tr t s φ ζ hflow (hLBν ν hνB' tr htr)
  have hlo := hLo ν tr t s φ ζ hflow
  have hhi := hHi ν tr t s φ ζ hflow
  have hνC' : ν ∈ Ioc 0 νC := ⟨hν0, hν.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hνT' : ν ∈ Ioc 0 νT := ⟨hν0, hν.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  obtain ⟨hχint, hχbd⟩ := hC' ν hνC' tr htr (revAge ν s ζ) hr0 hθ (mvPhi ν φ s ζ) χ
    hlo.smooth.continuous hlo.int0 hχC hχP hχI
  have hder := hD ν tr t s φ ζ hflow χ hχC hχP hχD hχint
  obtain ⟨hVc, hVp⟩ := hV ν _ tr (revAge ν s ζ) hr0 ha
  have hVb : ∀ j : ℕ, j ≤ 1 → ∀ y : ℝ × ℝ,
      ‖iteratedFDeriv ℝ j (movingTrainV tr (revAge ν s ζ)) y‖ ≤ CT := fun j hj y =>
    (hT' ν hνT' tr htr (revAge ν s ζ) hr0 hθ).1 j (hj.trans one_le_two) y
  have hbound := hR' (mvLen ν (ν ^ (-2 : ℝ)) s ζ) (mvBeta ν s ζ)
    (movingTrainV tr (revAge ν s ζ)) (mvPhi ν φ s ζ) χ hd hβ hβ1 hVc hVp hVb hlo hhi hχC
    hχint hχbd
  refine ⟨_, hder, ?_⟩
  have hE2 : 0 ≤ revE2 ν (ν ^ (-2 : ℝ)) m φ s ζ := adjE2_nonneg _ _ _
  calc e1Rate m (mvLen ν (ν ^ (-2 : ℝ)) s ζ) (mvBeta ν s ζ) (movingTrainV tr (revAge ν s ζ))
          (mvPhi ν φ s ζ) χ + betaMin ν t * revE2 ν (ν ^ (-2 : ℝ)) m φ s ζ
      ≤ e1Rate m (mvLen ν (ν ^ (-2 : ℝ)) s ζ) (mvBeta ν s ζ) (movingTrainV tr (revAge ν s ζ))
          (mvPhi ν φ s ζ) χ + mvBeta ν s ζ * revE2 ν (ν ^ (-2 : ℝ)) m φ s ζ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hβt hE2)
    _ ≤ K * (revE1 ν (ν ^ (-2 : ℝ)) m φ s ζ + revE0 ν (ν ^ (-2 : ℝ)) m φ s ζ) := hbound

end UnforcedLeray.Short.IIIa.AdjE1
