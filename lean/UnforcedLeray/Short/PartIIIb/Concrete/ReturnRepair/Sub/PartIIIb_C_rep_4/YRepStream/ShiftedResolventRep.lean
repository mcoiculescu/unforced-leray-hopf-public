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

/-!
# `PartIII-b:C/rep/4/4/1/org` (c): the shifted resolvent identity on repair sources

Source `the November 2 reference manuscript` 4196-4201 (`ward:shifted-resolvent`),
4171 (`X₀ = W_μ - W_{μ+1}`), 5169-5176 (repair source).  The proof reduces the young-region identity
`D_{μ+1}X₀ = W_μ` for the old repair source to the separated-source identity `SepX0FreeEq`
(`PhaseGradient/Defs.lean`), applied to the separated representative of `repairSepBridge`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem repPart_fst_zero' {c mZ ρb γ ν : ℝ} (X : StrG c mZ ρb γ ν) : (repPart X).fst = 0 := by
  simp [repPart]

/-- The core identity for one level, one Floquet exponent `μ > -1/4` and one pair of
representatives of the old repair source. -/
theorem srRep_core (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hμ : -(1 / 4) < μ) (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) (w : LVel Pl L)
    {g₁ g₂ : Chart → Ten3} (hg : IsRep Pl K L (oldRep Pl K L w) g₁ g₂) :
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
  obtain ⟨T, hT1, hT2, -, hresp, -⟩ :=
    repairSepBridge (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε K.χo K.hχo hc hρ hmZ hν hε
      (repPart (multOp Pl K L w))
  -- the repair component of `χ_o(0, M_2)` is a.e. the whole old source (the thin part vanishes)
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
  have hX0 : wardX0 L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂) = sepX0 L.ν μ T := by
    funext τ y
    simp only [wardX0, sepX0, hsep]
  have hW : ∀ τ y, wardW L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂) τ y = sepWre L.ν μ T τ y := by
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
    (2 * L.ε * cOf L.ν) hν hμ hpos (mul_pos (mul_pos two_pos hε) hc) T hT1 hT2 τ y hr

/-- **`ShiftedResolventRep`** (`ward:shifted-resolvent` on the old repair source, 4196-4201). -/
theorem shiftedResolventRep (dm dp : ℝ) : ShiftedResolventRep dm dp := by
  unfold ShiftedResolventRep
  intro D hst
  filter_upwards [muWin_gt_quarter D hst] with n hn
  intro z hz
  unfold ShiftedResolventRepAt
  intro w g₁ g₂ hg
  exact srRep_core D.Pl D.K (D.level n) (D.mu n z) (hn z hz) hst.C0_pos
    (by linarith [hst.mZ_gt]) w hg

end UnforcedLeray.Short.PartIIIb.Concrete
