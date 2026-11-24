import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Inv.Of
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Inv.SrcFinite.RepairSepBridgeAE
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.RepairSource
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.ShiftedResolventRep

/-!
# `PartIII-b:C/rep/4/4/1/org/1/1/inv/2`: `sepOldSrcFinite`

Source `the November 2 reference manuscript`
5169-5176 (`repair:source`), 4155-4171.  As `sepRepSrcFinite`
(`YRepStream/SepYoungRep/SrcFinite.lean`), with `repairSepBridgeAE` in place of `repairSepBridge`
so the representative `T` also carries the a.e. identity `T = oldPhys`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sepOldSrcFiniteAt_of (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ C : ℝ)
    (k : ℕ) (hRS : RepairSourceAt Pl K L C k) (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) :
    SepOldSrcFiniteAt Pl K L μ := by
  intro w g₁ g₂ hg
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
  obtain ⟨T, hT1, -, -, hresp, hlt, hTae⟩ :=
    repairSepBridgeAE (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε K.χo K.hχo hc hρ hmZ hν hε
      (repPart (multOp Pl K L w))
  have hM0 : ((repPart (multOp Pl K L w)).fst : Chart → Ten3) =ᵐ[gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν]
      (0 : Chart → Ten3) := by
    rw [repPart_fst_zero']
    exact Lp.coeFn_zero _ _ _
  have a1 := (chiOStrApply (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.χo K.hχo
    (repPart (multOp Pl K L w))).1
  have hfst : ((chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo
      (repPart (multOp Pl K L w))).fst : Chart → Ten3) =ᵐ[gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν]
      (0 : Chart → Ten3) := by
    filter_upwards [a1, hM0] with p e1 e2
    rw [e1, e2]
    simp
  rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at hfst
  have hae := wo_rep_ae hρ K.hχo (repPart (multOp Pl K L w)) hg.1 hg.2
  have hsum : g₁ + g₂ =ᵐ[ageμ (cOf L.ν) (-1 / 2)]
      ((chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo
        (repPart (multOp Pl K L w))).snd : Chart → Ten3) := by
    filter_upwards [hae, hfst] with p h1 h2
    rw [h1]
    simp [strSum, h2]
  have hnull := ae_iff.1 hsum
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null hnull
  have hsep : ∀ (μ' : ℂ) (τ : ℝ) (y : Space),
      UnforcedLeray.Short.IIIa.sepW L.ν μ' (oldPhys L.ε⁻¹ (cOf L.ν) (g₁ + g₂)) y τ =
        UnforcedLeray.Short.IIIa.sepW L.ν μ' T y τ := by
    intro μ' τ y
    rw [WardX0Congr.sepW_congr L.ν μ' hR hc (g₁ + g₂) _ N hNm hN0 hsub τ y]
    exact hresp μ' y τ
  -- the a.e. identity for the sum of the representatives
  have hpull := chartOfNullPullback L.ε⁻¹ (cOf L.ν) hR hc _ hnull
  have hphys : ∀ᵐ x : ℝ × Space, oldPhys L.ε⁻¹ (cOf L.ν) (g₁ + g₂) x.1 x.2 =
      oldPhys L.ε⁻¹ (cOf L.ν) ((chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo
        (repPart (multOp Pl K L w))).snd : Chart → Ten3) x.1 x.2 := by
    filter_upwards [hpull] with x hx
    have hx' : (g₁ + g₂) (NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1) =
        ((chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo
          (repPart (multOp Pl K L w))).snd : Chart → Ten3)
          (NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1) := not_not.1 hx
    simp only [oldPhys, NearInst.cartLift, hx']
  have hsnd : (chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo
      (repPart (multOp Pl K L w))).snd = (chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo
      (multOp Pl K L w)).snd := by
    simp [chiOStr, repPart]
  refine ⟨T, hT1, ?_, fun τ y => ?_, ?_⟩
  · filter_upwards [hTae, hphys] with x h1 h2
    rw [h1, h2]
  · simp only [wardW, sepWre, hsep]
  · have h2 : IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 19) (IIIa.srcNorm T) ≤
        phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressPhys Pl K L w) := by
      refine hlt.trans (le_of_eq ?_)
      rw [hsnd]
      rfl
    exact lt_of_le_of_lt (h2.trans (hRS w)) ENNReal.ofReal_lt_top

theorem sepOldSrcFinite (dm dp : ℝ) : SepOldSrcFinite dm dp := by
  intro D hst
  obtain ⟨C, k, hC⟩ := repairSource D hst
  filter_upwards [hC] with n hn z _
  exact sepOldSrcFiniteAt_of D.Pl D.K (D.level n) (D.mu n z) C k hn hst.C0_pos
    (by linarith [hst.mZ_gt])

end UnforcedLeray.Short.PartIIIb.Concrete
