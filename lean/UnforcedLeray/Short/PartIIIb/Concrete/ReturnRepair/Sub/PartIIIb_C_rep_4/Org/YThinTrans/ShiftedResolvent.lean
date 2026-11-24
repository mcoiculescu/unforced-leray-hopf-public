import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.Trans
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L8_RepairSepBridge
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_1_HRep
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_2_KerPDE
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1_b
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.Window
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.ChiOStrApply
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L9

/-!
# `PartIII-b:C/rep/4/2/org/2`: the shifted resolvent identity on thin sources

Source `the November 2 reference manuscript` 4196-4201 (`ward:shifted-resolvent`),
4171 (`X₀ = W_μ - W_{μ+1}`), 4163-4168 (`χ_o = 0` for `s ≤ 1.2/ν`), 5148-5157 (old thin source).
Exactly as for the repair source (`ShiftedResolventRep.lean`), the identity on the young region
`D_{μ+1}X₀ = W_μ` is the separated-source identity `SepX0FreeEq`, applied to the cut source
`oldCutSrc` of the chart representative `T₁ + T₂` of `χ_o(T₁, 0)` (a.e. equal to it).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The separated source attached to any measurable chart tensor `g` that vanishes for `ν s ≤ 6/5`
and has a finite age moment (source 4155-4171, 2684-2703). -/
theorem thinSepBridge (c ν ε : ℝ) (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε) (g : Chart → Ten3)
    (hgm : Measurable g)
    (hchart : ∀ᵐ p ∂(ageμ c (-1 / 2)), (ν * p.1 ≤ 6 / 5 → g p = 0))
    (hM : ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) < ⊤) :
    ∃ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
      IIIa.IsSepSource (2 * ε * c) (ε⁻¹ * Real.sqrt (5 * ν / 6)) T ∧
      SepMoment (2 * ε * c) T ∧ IsAxiSource T ∧
      (∀ (μ : ℂ) (y : Space) (τ : ℝ),
        IIIa.sepW ν μ (oldPhys ε⁻¹ c g) y τ = IIIa.sepW ν μ T y τ) := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hpull := chartOfNullPullback ε⁻¹ c hR hc _ (ae_iff.1 hchart)
  have hagree : ∀ᵐ x : ℝ × Space ∂volume, oldPhys ε⁻¹ c g x.1 x.2 =
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g x.1 x.2 := by
    filter_upwards [hpull] with x hx
    simp only [Set.mem_setOf_eq, not_not] at hx
    unfold oldCutSrc
    split_ifs with hz
    · rfl
    · have h0r : 0 ≤ ε⁻¹ * Real.sqrt (5 * ν / 6) := by positivity
      have hlt := not_le.1 hz
      have hpos : 0 < NearInst.hRad x.2 := lt_of_le_of_lt h0r hlt
      have hsq : (ε⁻¹ * Real.sqrt (5 * ν / 6)) ^ 2 = ε⁻¹ ^ 2 * (5 * ν / 6) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      have hlt2 : (ε⁻¹ * Real.sqrt (5 * ν / 6)) ^ 2 < NearInst.hRad x.2 ^ 2 := by
        nlinarith
      have hs : ν * (NearInst.chartOf ε⁻¹ c x.2 x.1).1 ≤ 6 / 5 := by
        show ν * (ε⁻¹ ^ 2 / NearInst.hRad x.2 ^ 2) ≤ 6 / 5
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      have hG0 := hx hs
      simp only [oldPhys, NearInst.cartLift, hG0, rb_nsSym_zero, smul_zero, Matrix.mul_zero,
        Matrix.zero_mul]
  -- periodicity, support, measurability of the separated source
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  have hper : ∀ τ z, oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g (τ + 2 * c / ε⁻¹) z =
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g τ z := by
    intro τ z
    unfold oldCutSrc
    rw [oldPhysPeriodic ε⁻¹ c g τ z]
  have hper2 : ∀ τ z, oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g (τ + 2 * ε * c) z =
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g τ z := by
    intro τ z
    rw [hP]
    exact hper τ z
  have hsupp : ∀ τ z, ε⁻¹ * Real.sqrt (5 * ν / 6) < Real.sqrt (z 0 ^ 2 + z 1 ^ 2) →
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g τ z = 0 := by
    intro τ z hz
    have hz' : ¬ NearInst.hRad z ≤ ε⁻¹ * Real.sqrt (5 * ν / 6) := not_le.2 hz
    unfold oldCutSrc
    simp only [hz', ite_false]
  have hsep : IIIa.IsSepSource (2 * ε * c) (ε⁻¹ * Real.sqrt (5 * ν / 6))
      (oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g) :=
    { measurable := oldCutMeasurable ε⁻¹ c _ g hgm
      periodic := hper2
      support := hsupp }
  have hmom := oldCutMoment ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g hR hc hgm hM
  rw [← hP] at hmom
  -- axisymmetry of the cut source
  have hAx : IsAxiSource (oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g) := by
    unfold IsAxiSource
    refine ⟨fun co si hco τ z => ?_, fun τ z => ?_⟩
    · unfold oldCutSrc
      rw [rot_hRad co si hco z]
      split_ifs with hz
      · exact oldPhysRotEquiv co si hco ε⁻¹ c g τ z
      · simp
    · unfold oldCutSrc
      rw [refl_hRad z]
      split_ifs with hz
      · exact oldPhysReflEquiv ε⁻¹ c g τ z
      · simp
  refine ⟨oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g, hsep, hmom, hAx, ?_⟩
  exact fun μ y τ => sepWCongrAE ν μ _ _ hagree y τ

/-- The core identity for one level, one Floquet exponent `μ > -1/4` and one pair of
representatives of the old thin source. -/
theorem srThin_core (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hμ : -(1 / 4) < μ) (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) (T : LStr Pl K L)
    {g₁ g₂ : Chart → Ten3} (hg : IsRep Pl K L (oldThin Pl K L T) g₁ g₂) :
    ShiftedResolventYoung L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂) := by
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hR : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hρ : 0 < L.ρb Pl K := by
    show 0 < UnforcedLeray.Short.IIb.rhoB (L.params Pl) K.m0 K.C0 K.k0
    unfold UnforcedLeray.Short.IIb.rhoB
    have h1 : 0 < ((L.params Pl).ν ^ K.k0)⁻¹ := inv_pos.2 (pow_pos (L.params Pl).ν_pos _)
    have h2 : 0 < (L.params Pl).ε ^ (3 / 11 : ℝ) := Real.rpow_pos_of_pos (L.params Pl).ε_pos _
    have h3 : 0 < Real.exp (K.m0 / (L.params Pl).ν) := Real.exp_pos _
    exact mul_pos (mul_pos (mul_pos hC0 h1) h3) h2
  have hρ' : 0 < L.ρb Pl K := hρ
  have happ := chiOStrApply (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.χo K.hχo (thinPart T)
  have a1 := happ.1
  have a2 := happ.2
  have hgdef : strSum (oldThin Pl K L T) = fun p =>
      ((oldThin Pl K L T).fst : Chart → Ten3) p + ((oldThin Pl K L T).snd : Chart → Ten3) p := rfl
  have hgm : Measurable (strSum (oldThin Pl K L T)) := by
    rw [hgdef]
    exact (l9_lp_meas _).add (l9_lp_meas _)
  have hchart : ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)),
      (L.ν * p.1 ≤ 6 / 5 → strSum (oldThin Pl K L T) p = 0) := by
    rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at a1
    rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ] at a2
    filter_upwards [a1, a2] with p e1 e2
    intro hp
    have h0 : cutFun K.χo L.ν p = 0 := K.hχo.zero _ hp
    rw [hgdef]
    simp only [e1, e2, h0, zero_smul, add_zero]
  have hM : ∫⁻ p, ‖strSum (oldThin Pl K L T) p‖ₑ ^ 2 ∂(ageμ (cOf L.ν) (-1 / 2)) < ⊤ :=
    strChartL2 (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν hρ hmZ hν (oldThin Pl K L T)
  obtain ⟨S, hT1, hT2, -, hresp⟩ := thinSepBridge (cOf L.ν) L.ν L.ε hc hν hε _ hgm hchart hM
  have hae := wo_rep_ae hρ K.hχo (thinPart T) hg.1 hg.2
  have hnull := ae_iff.1 hae
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null hnull
  have hsep : ∀ (μ' : ℂ) (τ : ℝ) (y : Space),
      UnforcedLeray.Short.IIIa.sepW L.ν μ' (oldPhys L.ε⁻¹ (cOf L.ν) (g₁ + g₂)) y τ =
        UnforcedLeray.Short.IIIa.sepW L.ν μ' S y τ := by
    intro μ' τ y
    rw [WardX0Congr.sepW_congr L.ν μ' hR hc (g₁ + g₂) _ N hNm hN0 hsub τ y]
    exact hresp μ' y τ
  have hX0 : wardX0 L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂) = sepX0 L.ν μ S := by
    funext τ y
    simp only [wardX0, sepX0, hsep]
  have hW : ∀ τ y, wardW L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂) τ y = sepWre L.ν μ S τ y := by
    intro τ y
    simp only [wardW, sepWre, hsep]
  intro τ y hϱ hage
  rw [hX0, hW]
  have hϱ2 : L.ν * (L.ε⁻¹) ^ 2 ≤ ϱ y ^ 2 := by
    unfold age at hage
    rw [mul_div_assoc', div_le_one (pow_pos hϱ 2)] at hage
    exact hage
  have hs : (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) ^ 2 = (L.ε⁻¹) ^ 2 * (5 * L.ν / 6) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hpos : 0 ≤ L.ε⁻¹ * Real.sqrt (5 * L.ν / 6) := mul_nonneg hR.le (Real.sqrt_nonneg _)
  have hνR : 0 < L.ν * (L.ε⁻¹) ^ 2 := mul_pos hν (pow_pos hR 2)
  have hr : L.ε⁻¹ * Real.sqrt (5 * L.ν / 6) < ϱ y := by
    by_contra h
    have h' : ϱ y ≤ L.ε⁻¹ * Real.sqrt (5 * L.ν / 6) := not_lt.mp h
    nlinarith [hs, hϱ2, hνR, hϱ, hpos, h']
  exact (sepX0FreeEq_of sepWHRep sepKerPDE sepX0Comb) L.ν μ (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6))
    (2 * L.ε * cOf L.ν) hν hμ hpos (mul_pos (mul_pos two_pos hε) hc) S hT1 hT2 τ y hr

/-- **`ShiftedResolventThin`** (`ward:shifted-resolvent` on the old thin source, 4196-4201). -/
theorem shiftedResolventThin (dm dp : ℝ) : ShiftedResolventThin dm dp := by
  unfold ShiftedResolventThin
  intro D hst
  filter_upwards [muWin_gt_quarter D hst] with n hn
  intro z hz
  unfold ShiftedResolventAt
  intro T g₁ g₂ hg
  exact srThin_core D.Pl D.K (D.level n) (D.mu n z) (hn z hz) hst.C0_pos
    (by linarith [hst.mZ_gt]) T hg

end UnforcedLeray.Short.PartIIIb.Concrete
