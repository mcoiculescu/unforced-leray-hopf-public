import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_ent
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_org2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_org2_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.KernelPt

/-!
# `EntJet` from `EntWPt`, `YoungJetDecayInt` and `MeanJetKernelPt`
(source 2347-2356, 5402-5404, 5440-5446, 5470-5476).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

theorem entJetAt_of (hν1 : L.ν ≤ 1) (hε1 : L.ε ≤ 1) (hμ0 : 0 < μ) (hμ1 : μ < 1 / 4)
    (hmZ : 3 / 2 < K.mZ) (hγ : 0 < gRate Pl) (hχy : IsStreamCutoff K.χy)
    {A1 : ℝ} {k1 : ℕ} {m1 : ℝ}
    (hE : ∀ p : Chart, 0 < p.1 →
      coefChgDens (L.V (NearInst.chartTau L.ε⁻¹ p)) (rawU Pl L (NearInst.chartTau L.ε⁻¹ p))
          (NearInst.chartY L.ε⁻¹ p) ≤
        A1 * L.ν⁻¹ ^ k1 * (Real.exp (K.m0 / L.ν) * L.ε) *
          Real.exp (-(m1 * L.ν ^ 2) * |p.2.2|))
    {C1 : ℝ} {k2 : ℕ}
    (h1 : ∀ (c ν ε μ : ℝ), LHyp c ν ε μ K.χo K.χy → ε ≤ 1 →
      ∀ M : Chart → Mat3, OldThinFinite c ν M → ∀ (τ : ℝ) (p : Chart), 0 < p.1 →
        meanJetDens (Xmean c ν ε μ K.χo K.χy M τ) (Ymean c ν ε μ K.χo K.χy M τ)
            (NearInst.chartY ε⁻¹ p) ≤
          C1 * ν⁻¹ ^ k2 * youngJetWeight ν ε p * oldN0cut c ν K.χo M)
    {CY : ℝ} {kY : ℕ}
    (hY : eLpNorm (fun p : Chart => Real.exp (-(m1 * L.ν ^ 2) * |p.2.2|) *
        youngJetWeight L.ν L.ε p) 2 (ringPhysμ L.ε⁻¹ (cOf L.ν)) ≤
      ENNReal.ofReal (CY * L.ν⁻¹ ^ kY * L.ε ^ 2)) :
    EntJetAt Pl K L μ (|A1| * |C1| * |CY|) (k1 + k2 + kY) := by
  intro T
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  obtain ⟨CN, kN, hCN⟩ := sourceLN0 K.mZ (gRate Pl) hmZ hγ
  have hfin : OldThinFinite (cOf L.ν) L.ν (thinRep T) :=
    (hCN (cOf L.ν) L.ν (L.ρb Pl K) hc hν hν1 T).1
  have hL : LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy :=
    ⟨hc, hν, hν1, hε, hμ0, hμ1, K.hχo, hχy⟩
  set N0 : ℝ := oldN0cut (cOf L.ν) L.ν K.χo (thinRep T) with hN0def
  have hN0 : 0 ≤ N0 := oldN0cut_nonneg _ _ hν K.hχo _
  have hP1 : 0 ≤ L.ν⁻¹ ^ k1 := by positivity
  have hP2 : 0 ≤ L.ν⁻¹ ^ k2 := by positivity
  have hPY : 0 ≤ L.ν⁻¹ ^ kY := by positivity
  have hex : 0 < Real.exp (K.m0 / L.ν) := Real.exp_pos _
  set a : ℝ := |A1| * L.ν⁻¹ ^ k1 * (Real.exp (K.m0 / L.ν) * L.ε) with hadef
  set b : ℝ := |C1| * L.ν⁻¹ ^ k2 * N0 with hbdef
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  set g : Chart → ℝ := fun p => Real.exp (-(m1 * L.ν ^ 2) * |p.2.2|) *
    youngJetWeight L.ν L.ε p with hg
  set μp := ringPhysμ L.ε⁻¹ (cOf L.ν) with hμp
  have hae : ∀ᵐ p ∂μp, 0 < p.1 := by
    rw [hμp]
    unfold ringPhysμ
    exact Measure.ae_smul_measure (ae_ageμ_fst_pos _ _) _
  have hpt : ∀ᵐ p ∂μp, ‖ringRead L.ε⁻¹ (fun τ y => coefChgDens (L.V τ) (rawU Pl L τ) y *
        meanJetDens (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) τ)
          (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) τ) y) p‖ ≤ ((a * b) • g) p := by
    filter_upwards [hae] with p hp
    have e1 := h1 (cOf L.ν) L.ν L.ε μ hL hε1 (thinRep T) hfin (NearInst.chartTau L.ε⁻¹ p) p hp
    have e0 := hE p hp
    have hd1 : 0 ≤ coefChgDens (L.V (NearInst.chartTau L.ε⁻¹ p))
        (rawU Pl L (NearInst.chartTau L.ε⁻¹ p)) (NearInst.chartY L.ε⁻¹ p) :=
      coefChgDens_nonneg _ _ _
    have hd2 := meanJetDens_nonneg
      (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) (NearInst.chartTau L.ε⁻¹ p))
      (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) (NearInst.chartTau L.ε⁻¹ p))
      (NearInst.chartY L.ε⁻¹ p)
    have hw : 0 ≤ youngJetWeight L.ν L.ε p := youngJetWeight_nonneg _ hε.le p
    have hx : 0 ≤ Real.exp (-(m1 * L.ν ^ 2) * |p.2.2|) := (Real.exp_pos _).le
    show ‖_ * _‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg hd1 hd2), Pi.smul_apply, smul_eq_mul]
    have e0' : coefChgDens (L.V (NearInst.chartTau L.ε⁻¹ p))
        (rawU Pl L (NearInst.chartTau L.ε⁻¹ p)) (NearInst.chartY L.ε⁻¹ p) ≤
        a * Real.exp (-(m1 * L.ν ^ 2) * |p.2.2|) := by
      refine e0.trans ?_
      rw [hadef]
      have : A1 ≤ |A1| := le_abs_self _
      have h' : A1 * L.ν⁻¹ ^ k1 * (Real.exp (K.m0 / L.ν) * L.ε) ≤
          |A1| * L.ν⁻¹ ^ k1 * (Real.exp (K.m0 / L.ν) * L.ε) := by gcongr
      exact mul_le_mul_of_nonneg_right h' hx
    have e1' : meanJetDens (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)
        (NearInst.chartTau L.ε⁻¹ p)) (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)
        (NearInst.chartTau L.ε⁻¹ p)) (NearInst.chartY L.ε⁻¹ p) ≤
        b * youngJetWeight L.ν L.ε p := by
      refine e1.trans ?_
      have : C1 ≤ |C1| := le_abs_self _
      have h' : C1 * L.ν⁻¹ ^ k2 * youngJetWeight L.ν L.ε p * N0 ≤
          |C1| * L.ν⁻¹ ^ k2 * youngJetWeight L.ν L.ε p * N0 := by gcongr
      refine h'.trans (le_of_eq ?_)
      rw [hbdef]; ring
    calc _ ≤ (a * Real.exp (-(m1 * L.ν ^ 2) * |p.2.2|)) * (b * youngJetWeight L.ν L.ε p) :=
          mul_le_mul e0' e1' hd2 (mul_nonneg ha0 hx)
      _ = a * b * g p := by rw [hg]; ring
  have hN1 : ENNReal.ofReal N0 ≤ oldN1 Pl K L T :=
    n0cutLeN1 (cOf L.ν) L.ν K.χo hc hν K.hχo (thinRep T) hfin
  have hCY : CY * L.ν⁻¹ ^ kY * L.ε ^ 2 ≤ |CY| * L.ν⁻¹ ^ kY * L.ε ^ 2 := by
    have : 0 ≤ L.ν⁻¹ ^ kY * L.ε ^ 2 := by positivity
    nlinarith [le_abs_self CY]
  have hab : 0 ≤ a * b := mul_nonneg ha0 hb0
  calc _ ≤ eLpNorm ((a * b) • g) 2 μp := eLpNorm_mono_ae_real hpt
    _ = ENNReal.ofReal (a * b) * eLpNorm g 2 μp := by
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hab]
    _ ≤ ENNReal.ofReal (a * b) * ENNReal.ofReal (|CY| * L.ν⁻¹ ^ kY * L.ε ^ 2) := by
        gcongr
        exact hY.trans (ENNReal.ofReal_le_ofReal hCY)
    _ = ENNReal.ofReal (|A1| * |C1| * |CY| * L.ν⁻¹ ^ (k1 + k2 + kY) *
          (L.ε ^ 3 * Real.exp (K.m0 / L.ν))) * ENNReal.ofReal N0 := by
        rw [← ENNReal.ofReal_mul hab, ← ENNReal.ofReal_mul (by positivity), hadef, hbdef, pow_add,
          pow_add]
        congr 1
        ring
    _ ≤ _ := by gcongr

end Regime

theorem entJet (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.EntJet := by
  obtain ⟨A1, k1, m1, hm1, hE⟩ := entWPt D hst
  obtain ⟨C1, k2, hC1⟩ := meanJetKernelPt D.K.χo D.K.χy
  obtain ⟨CY, kY, hCY⟩ := youngJetDecayInt m1 hm1
  refine ⟨|A1| * |C1| * |CY|, k1 + k2 + kY, ?_⟩
  filter_upwards [hE, retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne,
    mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt] with n hEn hle hmu z hz
  have hmz := hmu z hz
  have hs := hst.sigma_pos
  have hs1 := hst.sigma_lt
  exact entJetAt_of D.Pl D.K (D.level n) (D.mu n z) hle.1 hle.2
    (by linarith [hmz.1]) (by linarith [hmz.2]) hst.mZ_gt hst.gamma_pos hst.chiY hEn
    (fun c ν ε μ h hε M hM τ p hp => hC1 c ν ε μ h hε M hM τ p hp)
    (hCY (D.level n).ν (D.level n).ε (D.level n).ν_pos hle.1 (D.level n).ε_pos)

end UnforcedLeray.Short.PartIIIb.Concrete
