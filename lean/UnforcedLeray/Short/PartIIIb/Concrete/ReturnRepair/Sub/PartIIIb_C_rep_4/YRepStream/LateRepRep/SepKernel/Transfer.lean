import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.Props
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepRep.Kernel.Ungained

/-!
# `PartIII-b:C/rep/4/4/1/org/6/1/org` (a): the gain transfer on the scaled repair receiver

Source `the November 2 reference manuscript` 5318 (late output:
`g(s)^{-1} ≤ e^{-4γ/(9ν)}` for `s ≥ 0.8/ν`), 5322-5333 (the table is "in the split stress norm";
late-output entries carry the factor `e^{-4γ/(9ν)}`), 5306-5307 (the late-output part
`(1-χ_y)F_far`), 2698-2700 and 5609 (the split stress norm
`‖g⁻¹T‖_Z = ‖g⁻¹T₁‖_{Z₁} + ρ_b^{-1/2}‖g⁻¹T₂‖_{H_T}`).

The repair-receiver analogue of `LateRepThinOrg/Transfer.lean`: the separated-kernel bound is
stated without the gain (`htUng`, the norm of `ρ_b^{-1/2}H_T` itself), and the output gain of the
late region is read off the support (`lrr_gainHT_le`).  With `M_U` commuting with `χ_y` on the
repair receiver (`multYoung`, second clause), the scaled repair receiver of the late output is
`(1-χ_y)(M_UF_far x)₂`, which vanishes at ages `s < 0.8/ν` and is pointwise below
`(M_UF_far x)₂` (`lrr_lateCutRep`), hence (`lrr_late_level`)
`‖(M_U(1-χ_y)F_far x)₂‖ ≤ e^{-4γ/(9ν)} ‖(M_UF_far x)₂‖_{ρ_b^{-1/2}H_T, ungained}`.

All proved here.  The ungained norm `htUng` (`HtUng.lean`) and the general transfers
`lrr_norm_repPart`, `lrr_htUng_mono`, `lrr_gainHT_le_ae`, `lrr_gainHT_le_glob` are those of
`EarlyRepRep/Kernel/Ungained.lean`, imported above (this file used to declare copies, `hTUng`
among them; removed by organizer item `ORG:clash-pass`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The gain transfer on an age region** (source 5318, 5322-5333): a repair-receiver stress
vanishing at ages `s < a` has gained norm at most `B` times its ungained norm whenever
`g(s)^{-1} ≤ B` for `s ≥ a` (late output: `a = 0.8/ν`, `B = e^{-4γ/(9ν)}`). -/
theorem lrr_gainHT_le {c ρb γ ν a B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ p : Chart, a ≤ p.1 → ginv γ ν p ≤ B)
    (f : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))
    (hf : ∀ᵐ p ∂(gainHTMeasure c ρb γ ν), p.1 < a → (f : Chart → Ten3) p = 0) :
    ENNReal.ofReal ‖f‖ ≤ ENNReal.ofReal B * htUng c ρb f := by
  refine lrr_gainHT_le_ae hB f (hf.mono fun p hp hne => hg p ?_)
  by_contra h
  exact hne (hp (lt_of_not_ge h))

/-- The late output of a far velocity on the repair receiver at one level:
`(M_U(1-χ_y)v)₂ = (1-χ_y)(M_Uv)₂`, vanishing at ages `s < 0.8/ν` and pointwise below `(M_Uv)₂`
(source 4164, 5306-5307). -/
theorem lrr_lateCutRep (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (hχ : IsStreamCutoff K.χy)
    (hM : ∀ v : LVel Pl L,
      ((multOp Pl K L (youngMul hχ v)).snd : Chart → Ten3) =ᵐ[gainHTMeasure
          (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν]
        (fun p => cutFun K.χy L.ν p • ((multOp Pl K L v).snd : Chart → Ten3) p))
    (v : LVel Pl L) :
    (∀ᵐ p ∂(gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν), p.1 < 4 / 5 / L.ν →
        ((multOp Pl K L (v - youngMul hχ v)).snd : Chart → Ten3) p = 0) ∧
      ∀ᵐ p ∂(htRhoMeasure (cOf L.ν) (L.ρb Pl K)),
        ‖((multOp Pl K L (v - youngMul hχ v)).snd : Chart → Ten3) p‖ ≤
          ‖((multOp Pl K L v).snd : Chart → Ten3) p‖ := by
  have hν := L.ν_pos
  have hsnd : (multOp Pl K L (v - youngMul hχ v)).snd =
      (multOp Pl K L v).snd - (multOp Pl K L (youngMul hχ v)).snd := by
    rw [map_sub]; rfl
  have hae : ∀ᵐ p ∂(gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν),
      ((multOp Pl K L (v - youngMul hχ v)).snd : Chart → Ten3) p =
        (1 - cutFun K.χy L.ν p) • ((multOp Pl K L v).snd : Chart → Ten3) p := by
    filter_upwards [Lp.coeFn_sub (multOp Pl K L v).snd
      (multOp Pl K L (youngMul hχ v)).snd, hM v] with p e1 e2
    rw [hsnd, e1, Pi.sub_apply, e2, sub_smul, one_smul]
  refine ⟨hae.mono fun p hp hs => ?_, ?_⟩
  · have h1 : cutFun K.χy L.ν p = 1 := by
      unfold cutFun
      refine hχ.one _ ?_
      have := (lt_div_iff₀ hν).1 hs
      linarith
    rw [hp, h1, sub_self, zero_smul]
  · have hae' : ∀ᵐ p ∂(htRhoMeasure (cOf L.ν) (L.ρb Pl K)),
        ((multOp Pl K L (v - youngMul hχ v)).snd : Chart → Ten3) p =
          (1 - cutFun K.χy L.ν p) • ((multOp Pl K L v).snd : Chart → Ten3) p := by
      rw [← NearInst.ae_gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν]; exact hae
    filter_upwards [hae'] with p hp
    rw [hp, norm_smul, Real.norm_eq_abs]
    have h0 := hχ.range (L.ν * p.1)
    have hab : |1 - cutFun K.χy L.ν p| ≤ 1 := by
      unfold cutFun
      rw [abs_le]; constructor <;> linarith [h0.1, h0.2]
    calc |1 - cutFun K.χy L.ν p| * ‖((multOp Pl K L v).snd : Chart → Ten3) p‖
        ≤ 1 * ‖((multOp Pl K L v).snd : Chart → Ten3) p‖ :=
          mul_le_mul_of_nonneg_right hab (norm_nonneg _)
      _ = _ := one_mul _

/-- **The late-output gain on the repair receiver at one level**: the scaled repair receiver of
the late output is bounded by `e^{-4γ/(9ν)}` times the ungained scaled repair receiver of the far
velocity (source 5318, 5322-5333). -/
theorem lrr_late_level (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hχ : IsStreamCutoff K.χy) (hγ : 0 ≤ gRate Pl)
    (hM : ∀ v : LVel Pl L,
      ((multOp Pl K L (youngMul hχ v)).snd : Chart → Ten3) =ᵐ[gainHTMeasure
          (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν]
        (fun p => cutFun K.χy L.ν p • ((multOp Pl K L v).snd : Chart → Ten3) p))
    (x : LStr Pl K L) :
    ENNReal.ofReal ‖repPart (multOp Pl K L (lateOutOp Pl K L μ hχ x))‖ ≤
      ENNReal.ofReal (Real.exp (-(4 * gRate Pl / 9) / L.ν)) *
        htUng (cOf L.ν) (L.ρb Pl K)
          ((multOp Pl K L ((Sop Pl K L μ - SNop Pl K L μ) x)).snd : Chart → Ten3) := by
  have hlate : lateOutOp Pl K L μ hχ x =
      (Sop Pl K L μ - SNop Pl K L μ) x - youngMul hχ ((Sop Pl K L μ - SNop Pl K L μ) x) := rfl
  obtain ⟨hsupp, hpt⟩ := lrr_lateCutRep Pl K L hχ hM ((Sop Pl K L μ - SNop Pl K L μ) x)
  rw [lrr_norm_repPart, hlate]
  refine (lrr_gainHT_le (Real.exp_pos _).le (fun p hp => lrt_ginv_late hγ L.ν_pos p hp) _
    hsupp).trans ?_
  gcongr
  exact lrr_htUng_mono hpt

end UnforcedLeray.Short.PartIIIb.Concrete
