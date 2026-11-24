import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.FlatWeakFromDensity.LimitTendsto

/-!
# Part III-a, helper of `PartIII-a:T18/3/1/2`: the `L²` limit of the approximating tests

If `φₖ` are spatial flat tests with `∫_cell D2(φₖ, φ) → 0` (the hypothesis of
`DivFreeCutoffDensity`), then the extended tested identity holds for the `H¹` field `φ`:
`∫_{(0,∞)×cell} extWeakIntegrand ν μ F b G ψ φ = 0`, with integrability.

Proof. The integrand vanishes off the box `T = [a, u] × cell` (`ψ` is supported in `[a, u]`), and
on `T` the difference `Eφₖ - Eφ` is bounded by `3 t (K q)² + D2(φₖ, φ)/(2t)` for every `t > 0`.
Integrating over `T`, using `∫_T Eφₖ = 0` (`spatial_extWeak`), gives
`|∫_T Eφ| ≤ 3 t K² ∫_T q² + (1/(2t)) |[a,u]| ∫_cell D2(φₖ, φ)` for all large `k` and all `t > 0`.
Letting `k → ∞` kills the second term; then `t → 0` gives `∫_T Eφ = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **The `L²` limit step** (`PartIII-a:T18/3/1/2`). For standing data `hdat`, a weight `ψ ∈
C^∞_c(0,∞)`, an `H¹` divergence-free field `φ` and spatial flat tests `φₖ` with the defect `hT` going
to `0`, the extended tested integrand of `φ` is integrable on `(0,∞) × cell` and integrates to `0`. -/
theorem extWeak_limit {c ν : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hdat : FreeSolData c ν μ F b G) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hts : tsupport ψ ⊆ Ioi 0)
    {φ : ℝ × ℝ → Fin 2 → ℝ} (hφ : IsH1DivFreeTest c φ)
    {φk : ℕ → ℝ × ℝ → Fin 2 → ℝ} (hk : ∀ k, IsFlatSpatialTest c (φk k))
    (hT : Tendsto (fun k => ∫⁻ x in B0579.cell c, ENNReal.ofReal (∑ i : Fin 2,
        ((φk k x i - φ x i) ^ 2 +
          ∑ j : Fin 2, (B0579.pd j (fun y => φk k y i) x - B0579.pd j (fun y => φ y i) x) ^ 2)))
      atTop (𝓝 0)) :
    IntegrableOn (extWeakIntegrand ν μ F b G ψ φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, extWeakIntegrand ν μ F b G ψ φ p = 0 := by
  have hT' : Tendsto (fun k => ∫⁻ x in B0579.cell c, ENNReal.ofReal (D2 (φk k) φ x))
      atTop (𝓝 0) := hT
  obtain ⟨a, u, ha, hsub⟩ := exists_Icc_of_tsupport hψc hts
  obtain ⟨Cψ, hCψ⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  obtain ⟨Cd, hCd⟩ := (hψ.continuous_deriv (by simp)).bounded_above_of_compact_support hψc.deriv
  have hCψ0 : 0 ≤ Cψ := (norm_nonneg _).trans (hCψ 0)
  have hCd0 : 0 ≤ Cd := (norm_nonneg _).trans (hCd 0)
  have hTm : MeasurableSet (Icc a u ×ˢ B0579.cell c) :=
    measurableSet_Icc.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hSm : MeasurableSet (Ioi (0 : ℝ) ×ˢ B0579.cell c) :=
    measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hTS : Icc a u ×ˢ B0579.cell c ⊆ Ioi (0 : ℝ) ×ˢ B0579.cell c :=
    prod_mono (fun s hs => Set.mem_Ioi.2 (lt_of_lt_of_le ha hs.1)) subset_rfl
  -- the integrand vanishes on the part of `(0,∞) × cell` outside the box
  have hvan : ∀ φ' : ℝ × ℝ → Fin 2 → ℝ, ∀ p ∈ (Ioi (0 : ℝ) ×ˢ B0579.cell c) \ (Icc a u ×ˢ B0579.cell c),
      extWeakIntegrand ν μ F b G ψ φ' p = 0 := by
    intro φ' p hp
    apply extWeak_eq_zero_of_not_mem hsub φ'
    intro h
    exact hp.2 (Set.mem_prod.2 ⟨h, (Set.mem_prod.1 hp.1).2⟩)
  -- the spatial flat tests satisfy the identity on the box
  have hkT : ∀ k, IntegrableOn (extWeakIntegrand ν μ F b G ψ (φk k)) (Icc a u ×ˢ B0579.cell c) ∧
      ∫ p in Icc a u ×ˢ B0579.cell c, extWeakIntegrand ν μ F b G ψ (φk k) p = 0 := by
    intro k
    obtain ⟨h1, h2⟩ := spatial_extWeak hdat hψ hψc hts (hk k)
    refine ⟨h1.mono_set hTS, ?_⟩
    exact ((setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hSm hTS
      (fun p hp => hvan (φk k) p hp)).symm).trans h2
  -- the integrand of `φ` is integrable on the box (through one index with finite defect)
  obtain ⟨k0, hk0⟩ := (eventually_D2_integrable hφ hk hT').exists
  have hEφT : IntegrableOn (extWeakIntegrand ν μ F b G ψ φ) (Icc a u ×ˢ B0579.cell c) := by
    have hD := diff_integrableOn_T (u := u) hdat hψ ha hCψ0 hCd0 hCψ hCd hφ (hk k0) hk0
    have h : IntegrableOn (fun p => extWeakIntegrand ν μ F b G ψ (φk k0) p -
        (extWeakIntegrand ν μ F b G ψ (φk k0) p - extWeakIntegrand ν μ F b G ψ φ p))
        (Icc a u ×ˢ B0579.cell c) := (hkT k0).1.sub hD
    refine h.congr_fun (fun p _ => ?_) hTm
    dsimp only
    ring
  -- the bound on the box, for every `t > 0`
  have hbound : ∀ t : ℝ, 0 < t →
      ‖∫ p in Icc a u ×ˢ B0579.cell c, extWeakIntegrand ν μ F b G ψ φ p‖ ≤
        3 * t * (Kconst ν μ a Cψ Cd ^ 2 * ∫ p in Icc a u ×ˢ B0579.cell c, qNorm b G F p ^ 2) := by
    intro t ht
    have h0 := tendsto_D2_integral hφ hk hT'
    have h1 : Tendsto (fun k => 3 * t * (Kconst ν μ a Cψ Cd ^ 2 *
          ∫ p in Icc a u ×ˢ B0579.cell c, qNorm b G F p ^ 2) +
        1 / (2 * t) * (volume.real (Icc a u) * ∫ x in B0579.cell c, D2 (φk k) φ x)) atTop
        (𝓝 (3 * t * (Kconst ν μ a Cψ Cd ^ 2 *
          ∫ p in Icc a u ×ˢ B0579.cell c, qNorm b G F p ^ 2) +
          1 / (2 * t) * (volume.real (Icc a u) * 0))) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_const_nhds.mul h0))
    simp only [mul_zero, add_zero] at h1
    refine ge_of_tendsto h1 ?_
    filter_upwards [eventually_D2_integrable hφ hk hT'] with k hkI
    have hd := norm_diff_integral_T_le (u := u) hdat hψ ha hCψ0 hCd0 hCψ hCd hφ (hk k) hkI ht
    have hs : ∫ p in Icc a u ×ˢ B0579.cell c, (extWeakIntegrand ν μ F b G ψ (φk k) p -
        extWeakIntegrand ν μ F b G ψ φ p) =
        -(∫ p in Icc a u ×ˢ B0579.cell c, extWeakIntegrand ν μ F b G ψ φ p) := by
      rw [integral_sub (hkT k).1 hEφT, (hkT k).2, zero_sub]
    rw [hs, norm_neg] at hd
    exact hd.trans_eq (by ring)
  -- `∫_T Eφ` vanishes: the bound holds for all `t > 0`
  have hC1 : 0 ≤ ∫ p in Icc a u ×ˢ B0579.cell c, qNorm b G F p ^ 2 :=
    setIntegral_nonneg hTm fun p _ => sq_nonneg _
  have hA0 : 0 ≤ Kconst ν μ a Cψ Cd ^ 2 * ∫ p in Icc a u ×ˢ B0579.cell c, qNorm b G F p ^ 2 :=
    mul_nonneg (sq_nonneg _) hC1
  have hJ0 : ‖∫ p in Icc a u ×ˢ B0579.cell c, extWeakIntegrand ν μ F b G ψ φ p‖ ≤ 0 := by
    by_contra hnpos
    have hpos : 0 < ‖∫ p in Icc a u ×ˢ B0579.cell c, extWeakIntegrand ν μ F b G ψ φ p‖ :=
      not_le.1 hnpos
    have hden : 0 < 6 * (Kconst ν μ a Cψ Cd ^ 2 * ∫ p in Icc a u ×ˢ B0579.cell c, qNorm b G F p ^ 2) + 1 :=
      by linarith
    have ht : 0 < ‖∫ p in Icc a u ×ˢ B0579.cell c, extWeakIntegrand ν μ F b G ψ φ p‖ /
        (6 * (Kconst ν μ a Cψ Cd ^ 2 * ∫ p in Icc a u ×ˢ B0579.cell c, qNorm b G F p ^ 2) + 1) :=
      div_pos hpos hden
    have hteq := div_mul_cancel₀ (‖∫ p in Icc a u ×ˢ B0579.cell c, extWeakIntegrand ν μ F b G ψ φ p‖)
      hden.ne'
    have hb := hbound _ ht
    nlinarith [hb, hteq, ht, hpos]
  have hJ : ∫ p in Icc a u ×ˢ B0579.cell c, extWeakIntegrand ν μ F b G ψ φ p = 0 :=
    norm_le_zero_iff.1 hJ0
  refine ⟨IntegrableOn.of_forall_sdiff_eq_zero hEφT hSm (fun p hp => hvan φ p hp), ?_⟩
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hSm hTS (fun p hp => hvan φ p hp)]
  exact hJ

end UnforcedLeray.Short.IIIa
