import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_4_1_org_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.ShiftedResolventRep

/-!
# Helper (MemLp folder): `sepRepSrcFinite` keeping the `SepMoment` component.

Same proof as `SrcFinite.lean`, retaining the second component of `repairSepBridge`.

# `PartIII-b:C/rep/4/4/1/org/1/1/4`: the separated representative of the old repair source

Source `the November 2 reference manuscript` 5169-5176 (`repair:source`),
4155-4171.  Same extraction as `wardW_eq_sepWre`, keeping `IsAxiSource T` and the `L²_τL^{22/19}`
bound of `repairSepBridge`; the bound is by `phaseL2Lr (repStressPhys w)`, finite by `repair:source`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sepRepSrcMom (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ C : ℝ) (k : ℕ)
    (hRS : RepairSourceAt Pl K L C k) (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) (w : LVel Pl L)
    {g₁ g₂ : Chart → Ten3} (hg : IsRep Pl K L (oldRep Pl K L w) g₁ g₂) :
    ∃ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
      IIIa.IsSepSource (2 * L.ε * cOf L.ν) (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) T ∧
      SepMoment (2 * L.ε * cOf L.ν) T ∧
      IsAxiSource T ∧
      (∀ τ y, wardW L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂) τ y = sepWre L.ν μ T τ y) ∧
      IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 19) (IIIa.srcNorm T) < ⊤ := by
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
  obtain ⟨T, hT1, hMom, hT3, hresp, hlt⟩ :=
    repairSepBridge (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε K.χo K.hχo hc hρ hmZ hν hε
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
  have hsnd : (chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo
      (repPart (multOp Pl K L w))).snd = (chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo
      (multOp Pl K L w)).snd := by
    simp [chiOStr, repPart]
  have hsep : ∀ (μ' : ℂ) (τ : ℝ) (y : Space),
      UnforcedLeray.Short.IIIa.sepW L.ν μ' (oldPhys L.ε⁻¹ (cOf L.ν) (g₁ + g₂)) y τ =
        UnforcedLeray.Short.IIIa.sepW L.ν μ' T y τ := by
    intro μ' τ y
    rw [WardX0Congr.sepW_congr L.ν μ' hR hc (g₁ + g₂) _ N hNm hN0 hsub τ y]
    exact hresp μ' y τ
  refine ⟨T, hT1, hMom, hT3, fun τ y => ?_, ?_⟩
  · simp only [wardW, sepWre, hsep]
  · have h2 : IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 19) (IIIa.srcNorm T) ≤
        phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressPhys Pl K L w) := by
      refine hlt.trans (le_of_eq ?_)
      rw [hsnd]
      rfl
    exact lt_of_le_of_lt (h2.trans (hRS w)) ENNReal.ofReal_lt_top
end UnforcedLeray.Short.PartIIIb.Concrete
end
