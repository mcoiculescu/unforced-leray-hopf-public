import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.NearYoungOld
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThinParts

/-!
# `PartIII-b:C/rep/4/4/1/org/1/1/inv`: the near part of an old stress vanishes on the young receiver

Source `the November 2 reference manuscript`
5303-5306, 3902-3920, 4163-4166.  `NearYoungOld` (`YRepStream/NearYoungOld.lean`) records
`χ_yS_Nχ_o = 0`, which says nothing where `χ_y` vanishes inside `0.8/ν < s < 1/ν`; the masked
support bound it is built from (`maskedSupport_quarter`) gives the stronger statement
`S_Nχ_oT = 0` at a.e. output point of age `s < 1/ν`, which this file records.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- `S_Nχ_oT = 0` at a.e. output of age `s < 1/ν` (5303-5306): the stronger form of `nyo_core`. -/
theorem nyo_core_lt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hμ : -(1 / 4) < μ) (hmZ : 0 ≤ K.mZ) (hρ : 0 < L.ρb Pl K)
    (hρ1 : L.ρb Pl K ≤ 1) (hδ : 0 < K.δ) (hδ2 : K.δ < Real.log (12 / 11))
    (hS : 1 / L.ν ≤ L.Scut K)
    (hnear : ∃ o : NearInst.NearOps (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsActualNear (L.params Pl) L.V L.rb μ K.δ (L.Scut K) o)
    (T : LStr Pl K L) :
    ∀ᵐ p ∂(ageμ (cOf L.ν) (-3 / 2)), p.1 < 1 / L.ν →
      (SNop Pl K L μ (ftOld Pl K L T) : Chart → Merid) p = 0 := by
  have hν : 0 < L.ν := L.ν_pos
  obtain ⟨ho, -⟩ := nearOpsAt_spec hnear
  set o := nearOpsAt Pl K L μ with hodef
  obtain ⟨Seps, Sf, Seps', hstress, htrans, hfar, hSN⟩ := ho.near
  have hpair : NearInst.Masked.IsMaskedPair (L.params Pl) μ K.δ (L.Scut K) Seps Sf :=
    ⟨⟨Seps', hstress, htrans⟩, hfar⟩
  have hT0 : 0 < 1 / L.ν := by positivity
  have hms := NearInst.Masked.maskedSupport_quarter NearInst.Masked.stressKernelRealization
    NearInst.Masked.boxDenseZ (L.params Pl) K.mZ (L.ρb Pl K) μ K.δ (L.Scut K) (1 / L.ν) hmZ hρ hρ1
    hμ hδ hT0 hS Seps Sf hpair
  set X := ftOld Pl K L T with hX
  set F := NearInst.gainEquiv (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) hν
    (NearInst.strIso (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν X) with hF
  have hexp : Real.exp K.δ < 12 / 11 := by
    have := Real.exp_lt_exp.2 hδ2
    rwa [Real.exp_log (by norm_num)] at this
  have hin : NearInst.Delta.inRestr (cOf L.ν) K.mZ (L.ρb Pl K)
      (NearInst.Delta.ageAbove (Real.exp K.δ * (1 / L.ν))) F = F := by
    refine inRestr_chiO K.hχo hρ hν _ ?_ T
    intro p hp
    have h1 : L.ν * p.1 < L.ν * (Real.exp K.δ * (1 / L.ν)) := mul_lt_mul_of_pos_left hp hν
    have h2 : L.ν * (Real.exp K.δ * (1 / L.ν)) = Real.exp K.δ := by field_simp
    rw [h2] at h1
    linarith
  have hout : NearInst.Delta.outRestr (cOf L.ν) (NearInst.Delta.ageBelow (1 / L.ν)) (o.SN F) = 0 := by
    have h : NearInst.Delta.outRestr (cOf L.ν) (NearInst.Delta.ageBelow (1 / L.ν))
        ((Seps - Sf) (NearInst.Delta.inRestr (cOf L.ν) K.mZ (L.ρb Pl K)
          (NearInst.Delta.ageAbove (Real.exp K.δ * (1 / L.ν))) F)) = 0 := DFunLike.congr_fun hms F
    rw [hin] at h
    rw [hSN]
    exact h
  have hBelow : MeasurableSet (NearInst.Delta.ageBelow (1 / L.ν)) :=
    NearInst.Delta.measurableSet_ageBelow _
  have hres : (NearInst.Delta.outRestr (cOf L.ν) (NearInst.Delta.ageBelow (1 / L.ν)) (o.SN F) :
      Chart → Merid) =ᵐ[ageμ (cOf L.ν) (-3 / 2)]
      NearInst.Delta.ind (NearInst.Delta.ageBelow (1 / L.ν)) • (o.SN F : Chart → Merid) :=
    NearInst.Delta.restrLp_ae hBelow _
  rw [hout] at hres
  have hsn : (SNop Pl K L μ X : Chart → Merid) =ᵐ[ageμ (cOf L.ν) (-3 / 2)]
      (o.SN F : Chart → Merid) := NearInst.coeFn_SNG o (gRate Pl) hν X
  filter_upwards [hsn, hres, Lp.coeFn_zero (E := Merid) 2 (ageμ (cOf L.ν) (-3 / 2))]
    with p e2 e3 e6 hp
  have hi : NearInst.Delta.ind (NearInst.Delta.ageBelow (1 / L.ν)) p = 1 := by
    unfold NearInst.Delta.ind
    exact Set.indicator_of_mem (show p ∈ NearInst.Delta.ageBelow (1 / L.ν) from hp) _
  have h4 := e6.symm.trans e3
  rw [Pi.smul_apply', hi, one_smul] at h4
  rw [e2]
  exact h4.symm

/-- The hyperplane `s = a` is `ageμ c b`-null. -/
theorem ageμ_fst_eq_null (c b a : ℝ) : ∀ᵐ p ∂(ageμ c b), p.1 ≠ a := by
  have h : ageμ c b (Prod.fst ⁻¹' {a}) = 0 := by
    have : Prod.fst ⁻¹' {a} = ({a} : Set ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by
      ext p; simp
    rw [this, ageμ, Measure.prod_prod]
    have h0 : ((volume.restrict (Ioi (0 : ℝ))).withDensity
        fun s => ENNReal.ofReal (s ^ b)) {a} = 0 :=
      (withDensity_absolutelyContinuous _ _) (by simp)
    rw [h0, zero_mul]
  rw [ae_iff]
  simpa [Set.preimage] using h

end UnforcedLeray.Short.PartIIIb.Concrete
