import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.HessianBound.ZActJet
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.BackgroundSplit.ActGrad.Scalar
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3.K3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3.K4

/-!
# `ActGrad` helpers: the old thin source as a separated `L¹` source (source 5282-5289, 5400)

Source `the November 2 reference manuscript` 4155-4171 (the separated old source,
its disk `|z'| ≤ R√(5ν/6)`), 5377-5379 (`χ_oT₁`), 5400 (`N = N₁(χ_oT₁)`), 2684-2703 (the lift
`𝒩_T` and the physical Jacobian `πR²s^{-5/2}ds dη`).

`ag_thinSrc`: the cut lift `S` of the old thin source is a separated source (periodic, measurable,
in the old disk, finite `Y₂` moment), axisymmetric, has the Ward displacement `X₀ = sepX0 S`, and
`∫ ‖S(·,z)‖_{L²_τ} dz ≤ πR² N₁` (the `L¹` form of the thin source, `R = ε⁻¹`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)
open GeomXAsm

/-- **The old thin source as a separated `L¹` source** (source 4155-4171, 5377-5379, 5400). -/
theorem ag_thinSrc (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hC0 : 0 < K.C0) (hmZ : 3 / 2 < K.mZ) (T : LStr Pl K L) :
    ∃ S : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
      IIIa.IsSepSource (2 * L.ε * cOf L.ν) (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) S ∧
      SepMoment (2 * L.ε * cOf L.ν) S ∧ IsAxiSource S ∧
      zAct Pl K L μ T = sepX0 L.ν μ S ∧
      agMass (2 * L.ε * cOf L.ν) (IIIa.srcNorm S) ≤
        ENNReal.ofReal (Real.pi * (L.ε⁻¹) ^ 2) * oldN1 Pl K L T := by
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hR : 0 < L.ε⁻¹ := inv_pos.2 hε
  set g := thinG Pl K L T with hgdef
  have hρb : 0 < L.ρb Pl K := ZRegAux.rho_b_pos' Pl K L hC0
  have hgm : Measurable g :=
    (Lp.stronglyMeasurable _).measurable.add (Lp.stronglyMeasurable _).measurable
  have hmom : ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ (cOf L.ν) (-1 / 2)) < ⊤ :=
    strChartL2 (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν hρb (by linarith only [hmZ]) hν _
  have hz : ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)), L.ν * p.1 ≤ 6 / 5 → g p = 0 :=
    ZRegAux.strSum_zero_young _ _ _ _ _ K.hχo hρb _
  set rOut : ℝ := L.ε⁻¹ * Real.sqrt (5 * L.ν / 6) with hrOut
  set S := oldCutSrc L.ε⁻¹ (cOf L.ν) rOut g with hSdef
  have hP_eq : 2 * L.ε * cOf L.ν = 2 * cOf L.ν / L.ε⁻¹ := by rw [div_inv_eq_mul]; ring
  have hS : IIIa.IsSepSource (2 * L.ε * cOf L.ν) rOut S := by
    rw [hP_eq]
    exact ⟨oldCutMeasurable L.ε⁻¹ (cOf L.ν) rOut g hgm,
      fun τ z => by simp only [hSdef, oldCutSrc]; rw [oldPhysPeriodic L.ε⁻¹ (cOf L.ν) g τ z],
      fun τ z hz => by
        simp only [hSdef, oldCutSrc]
        exact ite_eq_right_iff.2 fun h => absurd hz (not_lt.2 h)⟩
  have hM : SepMoment (2 * L.ε * cOf L.ν) S := by
    rw [hP_eq]
    exact oldCutMoment L.ε⁻¹ (cOf L.ν) rOut g hR hc hgm hmom
  have hEq : ∀ (μ' : ℂ) (y' : Space) (τ : ℝ),
      IIIa.sepW L.ν μ' (oldPhys L.ε⁻¹ (cOf L.ν) g) y' τ = IIIa.sepW L.ν μ' S y' τ :=
    fun μ' y' τ =>
      (sepWCongrAE L.ν μ' _ _ (PhasePrim.oldCut_ae (cOf L.ν) L.ν L.ε hc hν hε g hz) y' τ).symm
  have hzAct_eq : zAct Pl K L μ T = sepX0 L.ν μ S := by
    funext τ y'
    exact ZRegAux.wardX0_eq_T' (μ := μ) hEq τ y'
  -- axisymmetry of the cut source
  have hAx : IsAxiSource S := by
    unfold IsAxiSource
    refine ⟨fun co si hco τ z => ?_, fun τ z => ?_⟩
    · simp only [hSdef, oldCutSrc]
      rw [rot_hRad co si hco z]
      split_ifs with hz
      · exact oldPhysRotEquiv co si hco L.ε⁻¹ (cOf L.ν) g τ z
      · simp
    · simp only [hSdef, oldCutSrc]
      rw [refl_hRad z]
      split_ifs with hz
      · exact oldPhysReflEquiv L.ε⁻¹ (cOf L.ν) g τ z
      · simp
  -- the `L¹_z L²_τ` size
  set F := PhasePrim.cutLift (cOf L.ν) (Real.sqrt (5 * L.ν / 6)) g with hFdef
  have hFH : FarLeafOrg.ThinHyp (cOf L.ν) (Real.sqrt (5 * L.ν / 6)) F :=
    ⟨PhasePrim.cutLift_measurable _ _ g hgm, PhasePrim.cutLift_periodic _ _ hc.ne' g,
      fun x' Y q h => PhasePrim.cutLift_support _ _ g x' Y q h⟩
  have hS_eq : S = IIIa.thinSource L.ε F :=
    funext fun τ => funext fun z => (PhasePrim.thinSource_cutLift L.ε (cOf L.ν) _ hε g τ z).symm
  have hmass : agMass (2 * L.ε * cOf L.ν) (IIIa.srcNorm S) ≤
      ENNReal.ofReal (Real.pi * (L.ε⁻¹) ^ 2) * oldN1 Pl K L T := by
    rw [hS_eq]
    calc agMass (2 * L.ε * cOf L.ν) (IIIa.srcNorm (IIIa.thinSource L.ε F))
        ≤ ENNReal.ofReal (L.ε⁻¹ ^ 2) * IIIa.thinMoment (cOf L.ν) F :=
          ZActJetAux.ltauAt_srcNorm_thinSource_le hε hc hFH
      _ ≤ ENNReal.ofReal (L.ε⁻¹ ^ 2) *
            (ENNReal.ofReal Real.pi *
              IIIa.firstMoment (cOf L.ν) 0 (fun p => Ten3.toMatrix (g p))) :=
          mul_le_mul' le_rfl (PhasePrim.thinMoment_cutLift_le _ _ hc g hgm)
      _ = ENNReal.ofReal (Real.pi * (L.ε⁻¹) ^ 2) * oldN1 Pl K L T := by
          rw [PhasePrim.firstMoment_thinG Pl K L hC0 T, ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity), mul_comm (L.ε⁻¹ ^ 2) Real.pi]
  exact ⟨S, hS, hM, hAx, hzAct_eq, hmass⟩

end UnforcedLeray.Short.PartIIIb.Concrete

end
