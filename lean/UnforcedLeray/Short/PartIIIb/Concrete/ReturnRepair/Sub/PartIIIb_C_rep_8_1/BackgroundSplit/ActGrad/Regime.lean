import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.BackgroundSplit.ActGrad.Main

/-!
# `ActGrad` helpers: `ActGradAt` on the regimes (source 5203-5217, 5267-5268, 5282-5289)

Source `the November 2 reference manuscript` 5282-5289: "The general thin-source
estimate is `‖DX‖_{L^∞_τL^{22/3}} ≤ P_ν ε^{57/22} N₁`", with `DY` as in `repair:phase-gradient`
(5214-5217) and `D²X`, which has an additional curvature power (5267-5268).

`ag_main`: for fixed planar data and constants there are `C, k` such that `ActGradAt` holds at every
regime with `ν, ε ≤ 1`, period `P = 2εc ≤ 1` and `μ ∈ [σ₁, σ₂]`, `σ₁ > -1/4`.  At each phase the
meridional jet density is bounded pointwise (a.e.) by the normalized majorant `agG`
(`ag_core`), whose `L^{22/3}` norm is `≤ C ∫‖S(·,z)‖_{L²_τ}dz ≤ C πR²N₁` (`agG_lq`, `ag_thinSrc`);
`actJetChartTransfer` turns the phase-wise bound into the ring-chart bound.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

set_option maxHeartbeats 1600000 in
/-- **`ActGradAt` with uniform constants** (source 5203-5217, 5267-5268, 5282-5289). -/
theorem ag_main (Pl : PlanarData) (K : ReturnConsts) (hχy : IsStreamCutoff K.χy)
    (hC0 : 0 < K.C0) (hmZ : 3 / 2 < K.mZ) (σ₁ σ₂ : ℝ) (hσ : -(1 / 4) < σ₁) :
    ∃ (C : ℝ) (k : ℕ), ∀ (L : ReturnLevel) (μ : ℝ), L.ν ≤ 1 → L.ε ≤ 1 →
      2 * L.ε * cOf L.ν ≤ 1 → μ ∈ Icc σ₁ σ₂ → ActGradAt Pl K L μ C k := by
  obtain ⟨Cp, hCp, hXl⟩ := wgxPointwise σ₁ σ₂ hσ K.χy hχy
  obtain ⟨C₁, C₂, hC₁, hC₂, hYl⟩ := wgyPointwise σ₁ σ₂ hσ K.χy hχy
  obtain ⟨Ch, hCh, hHl⟩ := ag_hess K.χy hχy
  obtain ⟨Cx0, hCx0, hJx0⟩ := ag_x0_jet 0 (by norm_num)
  obtain ⟨Cx1, hCx1, hJx1⟩ := ag_x0_jet 1 (by norm_num)
  obtain ⟨Cx2, hCx2, hJx2⟩ := ag_x0_jet 2 (by norm_num)
  obtain ⟨Cw0, hCw0, hJw0⟩ := ag_wre_jet 0 (by norm_num)
  obtain ⟨Cw1, hCw1, hJw1⟩ := ag_wre_jet 1 (by norm_num)
  obtain ⟨Cψ, hCψ, hPs⟩ := ag_psi σ₁ σ₂ hσ
  obtain ⟨Cs0, hCs0, hS0⟩ := ag_sepDom_lq 0
  obtain ⟨Cs1, hCs1, hS1⟩ := ag_sepDom_lq 1
  obtain ⟨Cs2, hCs2, hS2⟩ := ag_sepDom_lq 2
  obtain ⟨Cv, hCv, hVl⟩ := ag_vert_lq
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = 1 - Real.sqrt (5 / 6) := ⟨_, rfl⟩
  have hs56 : Real.sqrt (5 / 6) < 1 := by rw [Real.sqrt_lt' one_pos]; norm_num
  have hc₀pos : 0 < c₀ := by rw [hc₀]; linarith
  obtain ⟨Kc, hKc⟩ : ∃ x : ℝ, x = (Cw1 + C₁ * Cw0 + C₁ * Cψ) +
      C₂ * ((Cx0 + Cx1 + Cψ) + (Cx2 + Cx1)) + 3 * (Cx1 + Cp * Cx0 + Cp * Cψ) +
      Ch * (Cx2 + Cx1 + Cx0 + Cψ) := ⟨_, rfl⟩
  obtain ⟨Cg, hCg⟩ : ∃ x : ℝ, x = Cs0 * c₀ ^ (-4 - ((0 : ℕ) : ℝ) + 9 / 22) +
      Cs1 * c₀ ^ (-4 - ((1 : ℕ) : ℝ) + 9 / 22) + Cs2 * c₀ ^ (-4 - ((2 : ℕ) : ℝ) + 9 / 22) +
      (Real.pi / 4) ^ (3 / 22 : ℝ) * (Cv * c₀⁻¹ * c₀ ^ (-2 + 3 / 22 : ℝ)) := ⟨_, rfl⟩
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  have hCg0 : 0 ≤ Cg := by rw [hCg]; positivity
  have hCpos : 0 < 2 * Kc * Cg * Real.pi + 1 := by
    have := mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hKc0) hCg0) Real.pi_pos.le
    linarith
  refine ⟨2 * Kc * Cg * Real.pi + 1, 4, ?_⟩
  intro L μ hν1 hε1 hP1 hμ T
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hμ' : -(1 / 4) < μ := lt_of_lt_of_le hσ hμ.1
  have hmZ0 : 0 ≤ K.mZ := by linarith
  obtain ⟨hAE, htrans⟩ := actJetChartTransfer Pl K L μ hχy hμ' hC0 hmZ0 T
  refine ⟨hAE, htrans _ ?_⟩
  intro τ
  have hR : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hR1 : 1 ≤ L.ε⁻¹ := (one_le_inv₀ hε).2 hε1
  have hsν : 0 < Real.sqrt L.ν := Real.sqrt_pos.2 hν
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hP0 : 0 < 2 * L.ε * cOf L.ν := by positivity
  have hLr0 : 0 < L.ε⁻¹ * Real.sqrt L.ν := mul_pos hR hsν
  have hrO : 0 ≤ L.ε⁻¹ * Real.sqrt (5 * L.ν / 6) := by positivity
  have hrr : L.ε⁻¹ * Real.sqrt (5 * L.ν / 6) < L.ε⁻¹ * Real.sqrt L.ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hDc : L.ε⁻¹ * Real.sqrt L.ν - L.ε⁻¹ * Real.sqrt (5 * L.ν / 6) =
      c₀ * (L.ε⁻¹ * Real.sqrt L.ν) := by
    rw [hc₀, show 5 * L.ν / 6 = 5 / 6 * L.ν by ring, Real.sqrt_mul (by norm_num)]
    ring
  have hD0 : 0 < L.ε⁻¹ * Real.sqrt L.ν - L.ε⁻¹ * Real.sqrt (5 * L.ν / 6) := by linarith
  have ha : 0 ≤ 2 * μ + 2 := by linarith
  obtain ⟨Λ, hΛ⟩ : ∃ x : ℝ, x = (L.ε⁻¹ * Real.sqrt L.ν) ^ (-(101 / 22 : ℝ)) := ⟨_, rfl⟩
  have hΛ0 : 0 < Λ := by rw [hΛ]; exact Real.rpow_pos_of_pos hLr0 _
  have hκ0 : 0 < Λ * (L.ε⁻¹ * Real.sqrt L.ν) := mul_pos hΛ0 hLr0
  have hκ2 : 0 < Λ * (L.ε⁻¹ * Real.sqrt L.ν)⁻¹ := mul_pos hΛ0 (inv_pos.2 hLr0)
  have hκV : 0 < Λ * (L.ε⁻¹ * Real.sqrt L.ν) ^ 3 := mul_pos hΛ0 (pow_pos hLr0 3)
  obtain ⟨S, hS, hSM, hAx, hzAct, hmass⟩ := ag_thinSrc Pl K L μ hC0 hmZ T
  have hg : Measurable (Function.uncurry (IIIa.srcNorm S)) := IIIa.sepAE_measurable_srcNorm hS
  have hper : ∀ τ z, IIIa.srcNorm S (τ + 2 * L.ε * cOf L.ν) z = IIIa.srcNorm S τ z := by
    intro τ z; unfold IIIa.srcNorm; rw [hS.periodic]
  by_cases hN : oldN1 Pl K L T = ⊤
  · rw [hN, ENNReal.mul_top (ENNReal.ofReal_pos.2 (mul_pos (mul_pos hCpos
      (pow_pos (inv_pos.2 hν) 4)) (Real.rpow_pos_of_pos hε _))).ne']
    exact le_top
  have hMfin : agMass (2 * L.ε * cOf L.ν) (IIIa.srcNorm S) < ⊤ :=
    lt_of_le_of_lt hmass (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hN))
  -- the `L^{22/3}` bounds of the pieces of the majorant
  have h0 : lqNorm (22 / 3) (IIIa.sepDom (2 * μ + 2) 0
        (L.ε⁻¹ * Real.sqrt L.ν - L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) (IIIa.srcNorm S) τ) ≤
      ENNReal.ofReal ((Cs0 * c₀ ^ (-4 - ((0 : ℕ) : ℝ) + 9 / 22)) *
        (Λ * (L.ε⁻¹ * Real.sqrt L.ν))) * agMass (2 * L.ε * cOf L.ν) (IIIa.srcNorm S) := by
    refine (hS0 (2 * μ + 2) ha _ _ hD0 hP0 hP1 _ hg hper τ).trans (le_of_eq ?_)
    rw [hDc, ag_id0 hc₀pos hLr0, ← hΛ]
    congr 2
    ring
  have h1 : lqNorm (22 / 3) (IIIa.sepDom (2 * μ + 2) 1
        (L.ε⁻¹ * Real.sqrt L.ν - L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) (IIIa.srcNorm S) τ) ≤
      ENNReal.ofReal ((Cs1 * c₀ ^ (-4 - ((1 : ℕ) : ℝ) + 9 / 22)) * Λ) *
        agMass (2 * L.ε * cOf L.ν) (IIIa.srcNorm S) := by
    refine (hS1 (2 * μ + 2) ha _ _ hD0 hP0 hP1 _ hg hper τ).trans (le_of_eq ?_)
    rw [hDc, ag_id1 hc₀pos hLr0, ← hΛ]
    congr 2
    ring
  have h2 : lqNorm (22 / 3) (IIIa.sepDom (2 * μ + 2) 2
        (L.ε⁻¹ * Real.sqrt L.ν - L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) (IIIa.srcNorm S) τ) ≤
      ENNReal.ofReal ((Cs2 * c₀ ^ (-4 - ((2 : ℕ) : ℝ) + 9 / 22)) *
        (Λ * (L.ε⁻¹ * Real.sqrt L.ν)⁻¹)) * agMass (2 * L.ε * cOf L.ν) (IIIa.srcNorm S) := by
    refine (hS2 (2 * μ + 2) ha _ _ hD0 hP0 hP1 _ hg hper τ).trans (le_of_eq ?_)
    rw [hDc, ag_id2 hc₀pos hLr0, ← hΛ]
    congr 2
    ring
  have hF : Measurable (vertRed (2 * μ + 2) (L.ε⁻¹ * Real.sqrt L.ν)
      (L.ε⁻¹ * Real.sqrt L.ν - L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) (IIIa.srcNorm S) τ) :=
    ((vertMeasurable _ hg).2 _ _ _).of_uncurry_left
  have hV : lqNorm (22 / 3) ((streamAnn L.ν L.ε⁻¹).indicator (fun y =>
        vertRed (2 * μ + 2) (L.ε⁻¹ * Real.sqrt L.ν)
          (L.ε⁻¹ * Real.sqrt L.ν - L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) (IIIa.srcNorm S) τ (y 2))) ≤
      ENNReal.ofReal (((Real.pi / 4) ^ (3 / 22 : ℝ) * (Cv * c₀⁻¹ * c₀ ^ (-2 + 3 / 22 : ℝ))) *
        (Λ * (L.ε⁻¹ * Real.sqrt L.ν) ^ 3)) * agMass (2 * L.ε * cOf L.ν) (IIIa.srcNorm S) := by
    rw [outAnn7_lq L.ν L.ε⁻¹ hν hR _ hF]
    refine (mul_le_mul' le_rfl (hVl (2 * μ + 2) ha _ _ _ hLr0 hD0 hP0 hP1 _ hg hper τ)).trans
      (le_of_eq ?_)
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [hDc, ag_idV hc₀pos hLr0 hν rfl Cv, ← hΛ]
  have hGlq : lqNorm (22 / 3) (agG (2 * μ + 2)
        (L.ε⁻¹ * Real.sqrt L.ν - L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) (L.ε⁻¹ * Real.sqrt L.ν) Λ
        (IIIa.srcNorm S) L.ν L.ε⁻¹ τ) ≤
      ENNReal.ofReal Cg * agMass (2 * L.ε * cOf L.ν) (IIIa.srcNorm S) := by
    rw [hCg]
    exact agG_lq (by positivity) (by positivity) (by positivity) (by positivity) hκ0 hΛ0 hκ2 hκV
      hg h0 h1 h2 hV
  -- a.e. finiteness of the order-0 majorant
  have hfin_ae : ∀ᵐ z : Space, IIIa.sepDom (2 * μ + 2) 0
      (L.ε⁻¹ * Real.sqrt L.ν - L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) (IIIa.srcNorm S) τ z < ⊤ := by
    have hlt : lqNorm (22 / 3) (IIIa.sepDom (2 * μ + 2) 0
        (L.ε⁻¹ * Real.sqrt L.ν - L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) (IIIa.srcNorm S) τ) < ⊤ :=
      lt_of_le_of_lt h0 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hMfin)
    have hm : Measurable (fun z => IIIa.sepDom (2 * μ + 2) 0
        (L.ε⁻¹ * Real.sqrt L.ν - L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) (IIIa.srcNorm S) τ z ^
          (22 / 3 : ℝ)) :=
      ((IIIa.sepAE_measurable_sepDom _ 0 _ hg).of_uncurry_left).pow_const _
    have hI : (∫⁻ z, IIIa.sepDom (2 * μ + 2) 0
        (L.ε⁻¹ * Real.sqrt L.ν - L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) (IIIa.srcNorm S) τ z ^
          (22 / 3 : ℝ)) ≠ ⊤ := by
      unfold lqNorm at hlt
      exact ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 hlt).ne
    filter_upwards [ae_lt_top' hm.aemeasurable hI] with z hz
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 hz
  -- the fields
  have hreg := HessBoundP.zAct_regular Pl K L μ hmZ0 hC0 hμ' T
  have hXeq : actX Pl K L μ T = sepWX L.ν μ L.ε⁻¹ K.χy S := by
    show wardStreamCut L.ν L.ε⁻¹ K.χy (zAct Pl K L μ T) =
      wardStreamCut L.ν L.ε⁻¹ K.χy (sepX0 L.ν μ S)
    rw [hzAct]
  have hYeq : actY Pl K L μ T = sepWY L.ν μ L.ε⁻¹ K.χy S := by
    show physDmu L.ν (μ + 1) (wardStreamCut L.ν L.ε⁻¹ K.χy (zAct Pl K L μ T)) =
      physDmu L.ν (μ + 1) (wardStreamCut L.ν L.ε⁻¹ K.χy (sepX0 L.ν μ S))
    rw [hzAct]
  have bx0 := hJx0 L.ν μ _ _ _ hν hμ' hrO hrr hP0 S hS hSM τ
  have bx1 := hJx1 L.ν μ _ _ _ hν hμ' hrO hrr hP0 S hS hSM τ
  have bx2 := hJx2 L.ν μ _ _ _ hν hμ' hrO hrr hP0 S hS hSM τ
  have bw0 := hJw0 L.ν μ _ _ _ hν hμ' hrO hrr hP0 S hS hSM τ
  have bw1 := hJw1 L.ν μ _ _ _ hν hμ' hrO hrr hP0 S hS hSM τ
  -- the pointwise bound
  have hpt : ∀ᵐ z : Space, ENNReal.ofReal (meanJetDens (actX Pl K L μ T τ) (actY Pl K L μ T τ)
      !₂[ϱ z, 0, z 2]) ≤
      ENNReal.ofReal (Λ * (1 + (L.ε⁻¹ * Real.sqrt L.ν)⁻¹ ^ 2) * Kc) *
        agG (2 * μ + 2) (L.ε⁻¹ * Real.sqrt L.ν - L.ε⁻¹ * Real.sqrt (5 * L.ν / 6))
          (L.ε⁻¹ * Real.sqrt L.ν) Λ (IIIa.srcNorm S) L.ν L.ε⁻¹ τ z := by
    filter_upwards [ae_not_mem_axis, hfin_ae] with z hz hfz
    have hz0 : 0 < ϱ z :=
      lt_of_le_of_ne (Real.sqrt_nonneg _) (fun h => hz ((mem_axis_iff z).2 h.symm))
    have hy0 : 0 < ϱ (meridPt z) := by rw [ag_meridPt_rho]; exact hz0
    have u0 := agG_unit0 (ν := L.ν) (R := L.ε⁻¹) (a := 2 * μ + 2)
      (D := L.ε⁻¹ * Real.sqrt L.ν - L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) (g := IIIa.srcNorm S)
      (τ := τ) hκ0 z
    have u1 := agG_unit1 (ν := L.ν) (R := L.ε⁻¹) (a := 2 * μ + 2)
      (D := L.ε⁻¹ * Real.sqrt L.ν - L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) (g := IIIa.srcNorm S)
      (τ := τ) (Lr := L.ε⁻¹ * Real.sqrt L.ν) hΛ0 z
    have u2 := agG_unit2 (ν := L.ν) (R := L.ε⁻¹) (a := 2 * μ + 2)
      (D := L.ε⁻¹ * Real.sqrt L.ν - L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) (g := IIIa.srcNorm S)
      (τ := τ) hκ2 z
    have uV := agG_unitV (ν := L.ν) (R := L.ε⁻¹) (a := 2 * μ + 2)
      (D := L.ε⁻¹ * Real.sqrt L.ν - L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) (g := IIIa.srcNorm S)
      (τ := τ) hκV z
    have jx0 := ag_chain hCx0 (ag_wgxJet_merid hAx bx0 hfz) u0
    have jx1 := ag_chain hCx1 (ag_wgxJet_merid hAx bx1 hfz) u1
    have jx2 := ag_chain hCx2 (ag_wgxJet_merid hAx bx2 hfz) u2
    have jw0 := ag_chain hCw0 (ag_wgyWJet_merid hAx bw0 hfz) u0
    have jw1 := ag_chain hCw1 (ag_wgyWJet_merid hAx bw1 hfz) u1
    have qm := hPs L.ν μ L.ε⁻¹ _ hν hR hP0 hμ S hS τ (meridPt z)
    rw [ag_ann_merid L.ν L.ε⁻¹ (vertRed (2 * μ + 2) (L.ε⁻¹ * Real.sqrt L.ν)
      (L.ε⁻¹ * Real.sqrt L.ν - L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) (IIIa.srcNorm S) τ) z] at qm
    have qz := hPs L.ν μ L.ε⁻¹ _ hν hR hP0 hμ S hS τ z
    have pxm := ag_chain hCψ qm.1 uV
    have pwm := ag_chain hCψ qm.2 uV
    have pzz := ag_chain hCψ qz.1 uV
    have hX := hXl L.ν μ L.ε⁻¹ _ hν hν1 hR1 hP0 hP1 hμ S hS hSM hAx τ (meridPt z) hy0
    have hY := hYl L.ν μ L.ε⁻¹ _ hν hν1 hR1 hP0 hP1 hμ S hS hSM hAx τ (meridPt z) hy0
    have hH0 := hHl L.ν L.ε⁻¹ (zAct Pl K L μ T) τ hν hR (hreg.1 τ)
      (fun r' z' h => hreg.2 τ r' z' h) z hz0
    rw [hzAct] at hH0
    have hwj : ∀ j : ℕ, (if L.ε⁻¹ * Real.sqrt L.ν ≤ ϱ z then
        ‖iteratedFDeriv ℝ j (sepX0 L.ν μ S τ) (meridPt z)‖ₑ else 0) =
        wgxJet j L.ν μ (L.ε⁻¹ * Real.sqrt L.ν) S τ (meridPt z) := by
      intro j
      unfold wgxJet
      rw [ag_meridPt_rho]
    rw [hwj 2, hwj 1, hwj 0] at hH0
    have core := ag_core hΛ0.le hLr0 hCp hC₁ hC₂ hCh hCx0 hCx1 hCx2 hCw0 hCw1 hCψ
      jx0 jx1 jx2 jw0 jw1 pxm pwm pzz hX hY hH0
    have hgs : gradSize (sepWX L.ν μ L.ε⁻¹ K.χy S τ) (meridPt z) ≤
        3 * ‖fderiv ℝ (sepWX L.ν μ L.ε⁻¹ K.χy S τ) (meridPt z)‖ := by
      have := ZActJetAux.gradSize_le_iteratedFDeriv (sepWX L.ν μ L.ε⁻¹ K.χy S τ) (meridPt z)
      rwa [norm_iteratedFDeriv_one] at this
    have hmj : ENNReal.ofReal (meanJetDens (actX Pl K L μ T τ) (actY Pl K L μ T τ)
        !₂[ϱ z, 0, z 2]) ≤
        ENNReal.ofReal ‖fderiv ℝ (sepWY L.ν μ L.ε⁻¹ K.χy S τ) (meridPt z)‖ +
          ENNReal.ofReal 3 * ENNReal.ofReal ‖fderiv ℝ (sepWX L.ν μ L.ε⁻¹ K.χy S τ) (meridPt z)‖ +
          ENNReal.ofReal (hessSize (wardStreamCut L.ν L.ε⁻¹ K.χy (sepX0 L.ν μ S) τ)
            (meridPt z)) := by
      rw [hXeq, hYeq]
      show ENNReal.ofReal (‖fderiv ℝ (sepWY L.ν μ L.ε⁻¹ K.χy S τ) (meridPt z)‖ +
          gradSize (sepWX L.ν μ L.ε⁻¹ K.χy S τ) (meridPt z) +
          hessSize (sepWX L.ν μ L.ε⁻¹ K.χy S τ) (meridPt z)) ≤ _
      have hh0 : 0 ≤ hessSize (sepWX L.ν μ L.ε⁻¹ K.χy S τ) (meridPt z) :=
        Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun l _ => norm_nonneg _))
      calc ENNReal.ofReal (‖fderiv ℝ (sepWY L.ν μ L.ε⁻¹ K.χy S τ) (meridPt z)‖ +
            gradSize (sepWX L.ν μ L.ε⁻¹ K.χy S τ) (meridPt z) +
            hessSize (sepWX L.ν μ L.ε⁻¹ K.χy S τ) (meridPt z))
          ≤ ENNReal.ofReal (‖fderiv ℝ (sepWY L.ν μ L.ε⁻¹ K.χy S τ) (meridPt z)‖ +
            3 * ‖fderiv ℝ (sepWX L.ν μ L.ε⁻¹ K.χy S τ) (meridPt z)‖ +
            hessSize (sepWX L.ν μ L.ε⁻¹ K.χy S τ) (meridPt z)) :=
            ENNReal.ofReal_le_ofReal (by linarith)
        _ = _ := by
            rw [ENNReal.ofReal_add (by positivity) hh0, ENNReal.ofReal_add (by positivity)
              (by positivity), ENNReal.ofReal_mul (by norm_num)]
            rfl
    rw [hKc]
    exact hmj.trans core
  have hcoef0 : 0 ≤ Λ * (1 + (L.ε⁻¹ * Real.sqrt L.ν)⁻¹ ^ 2) * Kc := by positivity
  calc lqNorm (22 / 3) (fun z => ENNReal.ofReal (meanJetDens (actX Pl K L μ T τ)
        (actY Pl K L μ T τ) !₂[ϱ z, 0, z 2]))
      ≤ lqNorm (22 / 3) (fun z => ENNReal.ofReal (Λ * (1 + (L.ε⁻¹ * Real.sqrt L.ν)⁻¹ ^ 2) * Kc) *
          agG (2 * μ + 2) (L.ε⁻¹ * Real.sqrt L.ν - L.ε⁻¹ * Real.sqrt (5 * L.ν / 6))
            (L.ε⁻¹ * Real.sqrt L.ν) Λ (IIIa.srcNorm S) L.ν L.ε⁻¹ τ z) :=
        lqNorm_mono_ae (by norm_num) hpt
    _ = ENNReal.ofReal (Λ * (1 + (L.ε⁻¹ * Real.sqrt L.ν)⁻¹ ^ 2) * Kc) *
          lqNorm (22 / 3) (agG (2 * μ + 2) (L.ε⁻¹ * Real.sqrt L.ν - L.ε⁻¹ * Real.sqrt (5 * L.ν / 6))
            (L.ε⁻¹ * Real.sqrt L.ν) Λ (IIIa.srcNorm S) L.ν L.ε⁻¹ τ) :=
        lqNorm_const_mul (by norm_num) _ ENNReal.ofReal_ne_top _
    _ ≤ ENNReal.ofReal (Λ * (1 + (L.ε⁻¹ * Real.sqrt L.ν)⁻¹ ^ 2) * Kc) *
          (ENNReal.ofReal Cg * (ENNReal.ofReal (Real.pi * (L.ε⁻¹) ^ 2) * oldN1 Pl K L T)) :=
        mul_le_mul' le_rfl (hGlq.trans (mul_le_mul' le_rfl hmass))
    _ = ENNReal.ofReal (Λ * (1 + (L.ε⁻¹ * Real.sqrt L.ν)⁻¹ ^ 2) * Kc * Cg *
          (Real.pi * (L.ε⁻¹) ^ 2)) * oldN1 Pl K L T := by
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hcoef0,
          ← ENNReal.ofReal_mul (mul_nonneg hcoef0 hCg0)]
    _ ≤ ENNReal.ofReal ((2 * Kc * Cg * Real.pi + 1) * L.ν⁻¹ ^ 4 * L.ε ^ (57 / 22 : ℝ)) *
          oldN1 Pl K L T := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        rw [hΛ]
        exact ag_final_real hν hν1 hε hε1 hKc0 hCg0

end UnforcedLeray.Short.PartIIIb.Concrete

end
