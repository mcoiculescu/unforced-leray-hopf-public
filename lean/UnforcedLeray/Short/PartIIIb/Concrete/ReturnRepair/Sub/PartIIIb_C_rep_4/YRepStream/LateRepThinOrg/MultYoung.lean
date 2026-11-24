import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateEarly
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Proofs.MultPin
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.CoeffMult
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Level

/-!
# `PartIII-b:C/rep/4/4/1/org/5/org` (b): the stream cutoff commutes with `M_U`

Source `the November 2 reference manuscript` 2706, 3876-3878, 4147, 5779-5782
(`M_U w = U ⊗ w + w ⊗ U`, thin part with `V`, repair part with `r_b`, pointwise in the chart point),
4164, 5158 (`χ_y(s) = χ̂_y(νs)`), 5306-5308 (the late-output part `(1-χ_y)F_far` and the young
output `χ_yF_far(1-χ_o)` of the two transition regions).

`M_U` is a pointwise multiplier, so it commutes with multiplication by `χ_y(s)`:
`(M_U(χ_y v))_i = χ_y (M_U v)_i` on both receivers (`multYoungAt_level`, `multYoung`).  This is
the step "output region, then receiver" used by all four repair-source entries of the table
5323-5333 (late output: `1 - χ_y`; early source: `χ_y`).

Proved here (no new leaf): from the exact-multiplier pin of the concrete base
(`concreteBase_isExactMultiplier`, `NearInst.multPinOfLink`), `youngMul_ae`, and the comparison
of the null sets of the chart measures (`NearInst.ae_gainZ1Measure`, `CoeffMult.z1_ac`,
`NearInst.ae_bodyMeasure`, `NearInst.ae_gainHTMeasure`, `NearInst.ae_htRhoMeasure`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `a ⊗ (rb) + (rb) ⊗ a = r(a ⊗ b + b ⊗ a)` as a chart tensor. -/
theorem lrt_ten3Of_symOuter_smul (a b : Merid) (r : ℝ) :
    NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter a (r • b)) =
      r • NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter a b) := by
  ext ij
  simp only [NearInst.ten3Of, UnforcedLeray.Short.IIIa.symOuter,
    UnforcedLeray.Short.IIIa.embedMerid, PiLp.smul_apply, smul_eq_mul]
  fin_cases ij <;> simp <;> ring

/-- **`M_U(χ_y v) = χ_y M_Uv` at one level** (source 2706, 3876-3878, 4147, 4164), on the thin
receiver (`Z₁`, measure `gainZ1Measure`) and on the repair receiver (`H_T`, measure
`gainHTMeasure`), given the near operators of the level and its split multiplier. -/
theorem multYoungAt_level (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hC0 : 0 < K.C0) (hnear : NearAt Pl K L μ)
    (hs : ∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsSplitMult M (L.params Pl).R L.V L.rb)
    (hχ : IsStreamCutoff K.χy) (v : LVel Pl L) :
    ((multOp Pl K L (youngMul hχ v)).fst : Chart → Ten3) =ᵐ[gainZ1Measure (cOf L.ν) K.mZ
        (gRate Pl) L.ν]
      (fun p => cutFun K.χy L.ν p • ((multOp Pl K L v).fst : Chart → Ten3) p) ∧
    ((multOp Pl K L (youngMul hχ v)).snd : Chart → Ten3) =ᵐ[gainHTMeasure (cOf L.ν)
        (L.ρb Pl K) (gRate Pl) L.ν]
      (fun p => cutFun K.χy L.ν p • ((multOp Pl K L v).snd : Chart → Ten3) p) := by
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  have hρ : 0 < L.ρb Pl K := inv_rhoB_pos hC0
  have hEx : IsExactMultiplier (concreteBase Pl K L μ hnear) L.ε⁻¹ L.V L.rb :=
    concreteBase_isExactMultiplier (h := hnear) NearInst.multPinOfLink hs
  have h3 := youngMul_ae (c := cOf L.ν) (γ := gRate Pl) (ν := L.ν) hχ v
  have h3a : ∀ᵐ p ∂(ageμ (cOf L.ν) (-3 / 2)),
      (youngMul hχ v : Chart → Merid) p = cutFun K.χy L.ν p • (v : Chart → Merid) p := by
    rw [← NearInst.ae_bodyMeasure (cOf L.ν) (gRate Pl) L.ν]; exact h3
  have h3b := (NearInst.CoeffMult.z1_ac hc K.mZ).ae_le h3a
  have h3z : ∀ᵐ p ∂(gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν),
      (youngMul hχ v : Chart → Merid) p = cutFun K.χy L.ν p • (v : Chart → Merid) p := by
    rw [NearInst.ae_gainZ1Measure]; exact h3b
  have h3h : ∀ᵐ p ∂(gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν),
      (youngMul hχ v : Chart → Merid) p = cutFun K.χy L.ν p • (v : Chart → Merid) p := by
    rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ, ← NearInst.ae_z1Measure _ K.mZ]
    exact h3b
  have h1 : ((multOp Pl K L (youngMul hχ v)).fst : Chart → Ten3) =ᵐ[gainZ1Measure (cOf L.ν) K.mZ
      (gRate Pl) L.ν] fun p => NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter
        (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.V p) ((youngMul hχ v : Chart → Merid) p)) :=
    (hEx (youngMul hχ v)).1
  have h2 : ((multOp Pl K L v).fst : Chart → Ten3) =ᵐ[gainZ1Measure (cOf L.ν) K.mZ
      (gRate Pl) L.ν] fun p => NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter
        (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.V p) ((v : Chart → Merid) p)) :=
    (hEx v).1
  have h1' : ((multOp Pl K L (youngMul hχ v)).snd : Chart → Ten3) =ᵐ[gainHTMeasure (cOf L.ν)
      (L.ρb Pl K) (gRate Pl) L.ν] fun p => NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter
        (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.rb p) ((youngMul hχ v : Chart → Merid) p)) :=
    (hEx (youngMul hχ v)).2
  have h2' : ((multOp Pl K L v).snd : Chart → Ten3) =ᵐ[gainHTMeasure (cOf L.ν)
      (L.ρb Pl K) (gRate Pl) L.ν] fun p => NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter
        (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.rb p) ((v : Chart → Merid) p)) :=
    (hEx v).2
  refine ⟨?_, ?_⟩
  · filter_upwards [h1, h2, h3z] with p e1 e2 e3
    rw [e1, e2, e3, lrt_ten3Of_symOuter_smul]
  · filter_upwards [h1', h2', h3h] with p e1 e2 e3
    rw [e1, e2, e3, lrt_ten3Of_symOuter_smul]

namespace SeqData

variable (D : SeqData)

/-- **`M_U(χ_y v) = χ_y M_Uv` along the sequence** (source 2706, 3876-3878, 4147, 4164), on both
receivers, for large `n` and every velocity `v`. -/
def MultYoungAt (hχ : IsStreamCutoff D.K.χy) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ v : LVel D.Pl (D.level n),
    ((multOp D.Pl D.K (D.level n) (youngMul hχ v)).fst : Chart → Ten3) =ᵐ[gainZ1Measure
        (cOf (D.level n).ν) D.K.mZ (gRate D.Pl) (D.level n).ν]
      (fun p => cutFun D.K.χy (D.level n).ν p •
        ((multOp D.Pl D.K (D.level n) v).fst : Chart → Ten3) p) ∧
    ((multOp D.Pl D.K (D.level n) (youngMul hχ v)).snd : Chart → Ten3) =ᵐ[gainHTMeasure
        (cOf (D.level n).ν) ((D.level n).ρb D.Pl D.K) (gRate D.Pl) (D.level n).ν]
      (fun p => cutFun D.K.χy (D.level n).ν p •
        ((multOp D.Pl D.K (D.level n) v).snd : Chart → Ten3) p)

end SeqData

/-- `M_U` commutes with the stream cutoff for every standing sequence (proved). -/
theorem multYoung (dm dp : ℝ) (D : SeqData) (hst : D.RepairStanding dm dp) :
    D.MultYoungAt hst.chiY := by
  filter_upwards [hst.pins, hst.near] with n h4 h5 v
  exact multYoungAt_level D.Pl D.K (D.level n) (D.mu n 0) hst.C0_pos
    (h5 0 ⟨by norm_num, by norm_num⟩) (h4 0 ⟨by norm_num, by norm_num⟩).split hst.chiY v

end UnforcedLeray.Short.PartIIIb.Concrete
