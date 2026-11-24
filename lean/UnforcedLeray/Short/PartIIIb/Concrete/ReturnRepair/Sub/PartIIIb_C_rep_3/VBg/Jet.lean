import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.VBg.Leaves
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.VBg.Jet.Integral
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.VBg.Jet.Early
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.VBg.Jet.LateRaw

/-!
# Proof of `RepVJetY2`: the derivative leaf of background hypothesis (H) (`PartIII-b:C/rep/3/4/1`)

Source of record: `the November 2 reference manuscript`, lines 5131-5139,
5225-5235, 2607-2612, 2347-2387, 5461-5465.

Assembles `RepVJetY2 D` from:
1. `JetAux.vJetDens_V_early_eventually` (`Jet/Early.lean`): on `0 < s ≤ 1`,
   `vJetDens (L.V τ) y ≤ P_ν * s * (1 + |η|)⁻¹`;
2. `JetAux.vJetDens_sub_le` + `JetAux.coefChg_V_late_eventually` (`Jet/Early.lean`) and
   `JetAux.vJetDens_rawU_late_eventually` (`Jet/LateRaw.lean`): on `1 < s`,
   `vJetDens (L.V τ) y ≤ P_ν * (1 + |η / √s|)⁻¹`;
3. `JetAux.vJet_ringL2_le` (`Jet/Integral.lean`): integrates the low-age and high-age pointwise
   majorants against `ringPhysμ L.ε⁻¹ (cOf L.ν)` to conclude
   `L.ε * ‖ringRead L.ε⁻¹ (vJetDens ∘ L.V)‖_{L²(ringPhysμ)} ≤ P_ν`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.VBgSq

/-- **Proved leaf `RepVJetY2`** (`PartIII-b:C/rep/3/4/1`): the `Y_2` bound on the first and second
spatial derivatives of the background velocity `V`. -/
theorem repVJetY2 (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : RepVJetY2 D := by
  obtain ⟨C₁, k₁, hC₁, hearly⟩ := JetAux.vJetDens_V_early_eventually D hst
  obtain ⟨C₂, k₂, hC₂, hchg⟩ := JetAux.coefChg_V_late_eventually D hst
  obtain ⟨C₃, k₃, hC₃, hraw⟩ := JetAux.vJetDens_rawU_late_eventually D hst
  have hle1 := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  set k : ℕ := max k₁ (max k₂ k₃)
  set C : ℝ := 3 * Real.sqrt Real.pi * (C₁ + (C₃ + C₂))
  refine ⟨C, k, ?_⟩
  filter_upwards [hearly, hchg, hraw, hle1] with n hearly_n hchg_n hraw_n hle1_n
  set L := D.level n
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hν1 : L.ν ≤ 1 := hle1_n.1
  have hνinv1 : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hR : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hc : 0 < cOf L.ν := cOf_pos hν
  set B₁ : ℝ := C₁ * L.ν⁻¹ ^ k₁
  set B₂ : ℝ := C₃ * L.ν⁻¹ ^ k₃ + C₂ * L.ν⁻¹ ^ k₂
  have hB₁ : 0 ≤ B₁ := by positivity
  have hB₂ : 0 ≤ B₂ := by positivity
  have hhigh : ∀ pt : Chart, 1 < pt.1 →
      vJetDens (L.V (NearInst.chartTau L.ε⁻¹ pt)) (NearInst.chartY L.ε⁻¹ pt) ≤
        B₂ * (1 + |pt.2.2 / Real.sqrt pt.1|)⁻¹ := by
    intro pt hp1
    have hsub := JetAux.vJetDens_sub_le
      (L.V (NearInst.chartTau L.ε⁻¹ pt))
      (rawU D.Pl L (NearInst.chartTau L.ε⁻¹ pt))
      (NearInst.chartY L.ε⁻¹ pt)
    have hr := hraw_n pt hp1
    have hc' := hchg_n pt hp1
    calc vJetDens (L.V (NearInst.chartTau L.ε⁻¹ pt)) (NearInst.chartY L.ε⁻¹ pt)
        ≤ vJetDens (rawU D.Pl L (NearInst.chartTau L.ε⁻¹ pt)) (NearInst.chartY L.ε⁻¹ pt) +
            12 * coefChgDens (L.V (NearInst.chartTau L.ε⁻¹ pt))
              (rawU D.Pl L (NearInst.chartTau L.ε⁻¹ pt)) (NearInst.chartY L.ε⁻¹ pt) := hsub
      _ ≤ C₃ * L.ν⁻¹ ^ k₃ * (1 + |pt.2.2 / Real.sqrt pt.1|)⁻¹ +
            C₂ * L.ν⁻¹ ^ k₂ * (1 + |pt.2.2 / Real.sqrt pt.1|)⁻¹ := add_le_add hr hc'
      _ = B₂ * (1 + |pt.2.2 / Real.sqrt pt.1|)⁻¹ := by simp only [B₂]; ring
  have hL2 := JetAux.vJet_ringL2_le hR hc hB₁ hB₂ (fun τ => vJetDens (L.V τ))
    (fun pt _ => JetAux.vJetDens_nonneg _ _) hearly_n hhigh
  rw [inv_inv] at hL2
  refine hL2.trans (ENNReal.ofReal_le_ofReal ?_)
  have hk1 : L.ν⁻¹ ^ k₁ ≤ L.ν⁻¹ ^ k := pow_le_pow_right₀ hνinv1 (le_max_left _ _)
  have hk2 : L.ν⁻¹ ^ k₂ ≤ L.ν⁻¹ ^ k :=
    pow_le_pow_right₀ hνinv1 ((le_max_left k₂ k₃).trans (le_max_right k₁ _))
  have hk3 : L.ν⁻¹ ^ k₃ ≤ L.ν⁻¹ ^ k :=
    pow_le_pow_right₀ hνinv1 ((le_max_right k₂ k₃).trans (le_max_right k₁ _))
  have hb1 : B₁ ≤ C₁ * L.ν⁻¹ ^ k := mul_le_mul_of_nonneg_left hk1 hC₁
  have hb2 : B₂ ≤ (C₃ + C₂) * L.ν⁻¹ ^ k := by
    have h3 : C₃ * L.ν⁻¹ ^ k₃ ≤ C₃ * L.ν⁻¹ ^ k := mul_le_mul_of_nonneg_left hk3 hC₃
    have h2 : C₂ * L.ν⁻¹ ^ k₂ ≤ C₂ * L.ν⁻¹ ^ k := mul_le_mul_of_nonneg_left hk2 hC₂
    simp only [B₂]; linarith
  calc 3 * Real.sqrt Real.pi * (B₁ + B₂)
      ≤ 3 * Real.sqrt Real.pi * (C₁ * L.ν⁻¹ ^ k + (C₃ + C₂) * L.ν⁻¹ ^ k) :=
        mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) (by positivity)
    _ = C * L.ν⁻¹ ^ k := by simp only [C]; ring

end UnforcedLeray.Short.PartIIIb.Concrete.VBgSq

end
