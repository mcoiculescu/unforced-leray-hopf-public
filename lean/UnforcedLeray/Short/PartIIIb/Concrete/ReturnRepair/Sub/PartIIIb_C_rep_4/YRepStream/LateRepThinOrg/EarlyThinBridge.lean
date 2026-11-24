import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.Props
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Props

/-!
# `PartIII-b:C/rep/4/4/1/org/5/org` (d): the same kernel leaf gives the early-source thin entry

Source `the November 2 reference manuscript` 5303-5308 (the early-source part
`χ_yF_far(1-χ_o)`), 5318-5319 (`g(s)^{-1} ≤ 1` on young output), 5323-5338 (the general separated
kernel bounds, repair-to-thin pointwise exponent `79/22`).

The ungained far-kernel leaf `FarRepThinUng` (`Props.lean`) bounds `F_far` on every repair source
and every output age.  Applied to the early source `(0,((1-χ_o)T)₂)`, with the young cutoff
`χ_y` commuting with `M_U` (`multYoung`) and the young-output gain `g⁻¹ ≤ 1`
(`lrt_gainZ1_le_glob`), it gives the kernel estimate `EarlyRepThinKernel` of
`YRepStream/EarlyRepThin/Props.lean` (task `PartIII-b:C/rep/4/4/1/org/7/1`):
`earlyRepThinKernel_of_farRepThinUng` (proved).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `χ_o` acts componentwise, so it commutes with the repair projection `(T₁,T₂) ↦ (0,T₂)`. -/
theorem lrt_chiO_repPart {c mZ ρb γ ν : ℝ} {χ : ℝ → ℝ} (hχ : IsOutwardCutoff χ)
    (T : StrG c mZ ρb γ ν) :
    chiOStr c mZ ρb γ ν hχ (repPart T) = repPart (chiOStr c mZ ρb γ ν hχ T) := by
  apply (WithLp.prodContinuousLinearEquiv 1 ℝ (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
    (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))).injective
  simp [chiOStr, repPart]

/-- `((0,T₂))₂ = T₂`. -/
theorem lrt_repPart_snd {c mZ ρb γ ν : ℝ} (T : StrG c mZ ρb γ ν) :
    (repPart T).snd = T.snd := by
  simp [repPart]

/-- **One level of the bridge**: the thin receiver of the early-source part on `(0,T₂)` is at most
the ungained thin receiver of `F_far` on `(0,((1-χ_o)T)₂)` (source 5303-5308, 5318-5319). -/
theorem lrt_early_level (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hχ : IsStreamCutoff K.χy) (hγ : 0 ≤ gRate Pl)
    (hM : ∀ v : LVel Pl L,
      ((multOp Pl K L (youngMul hχ v)).fst : Chart → Ten3) =ᵐ[gainZ1Measure
          (cOf L.ν) K.mZ (gRate Pl) L.ν]
        (fun p => cutFun K.χy L.ν p • ((multOp Pl K L v).fst : Chart → Ten3) p))
    (T : LStr Pl K L) :
    ENNReal.ofReal ‖thinPart (multOp Pl K L (earlySrcOp Pl K L μ hχ (repPart T)))‖ ≤
      z1Ung (cOf L.ν) K.mZ
        ((multOp Pl K L ((Sop Pl K L μ - SNop Pl K L μ)
          (repPart (T - chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo T)))).fst :
          Chart → Ten3) := by
  set u := (Sop Pl K L μ - SNop Pl K L μ)
    (repPart (T - chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo T)) with hu
  have hE : earlySrcOp Pl K L μ hχ (repPart T) = youngMul hχ u := by
    simp only [earlySrcOp, hu, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub, lrt_chiO_repPart]
  rw [hE, lrt_norm_thinPart]
  refine (lrt_gainZ1_le_glob zero_le_one (fun p => ginv_le_one hγ L.ν_pos.le p) _).trans ?_
  rw [ENNReal.ofReal_one, one_mul]
  refine lrt_z1Ung_mono ?_
  have h := hM u
  rw [Filter.EventuallyEq, NearInst.ae_gainZ1Measure] at h
  filter_upwards [h] with p hp
  rw [hp, norm_smul, Real.norm_eq_abs]
  have h0 := hχ.range (L.ν * p.1)
  have hab : |cutFun K.χy L.ν p| ≤ 1 := by
    unfold cutFun
    rw [abs_of_nonneg h0.1]; exact h0.2
  calc |cutFun K.χy L.ν p| * ‖((multOp Pl K L u).fst : Chart → Ten3) p‖
      ≤ 1 * ‖((multOp Pl K L u).fst : Chart → Ten3) p‖ :=
        mul_le_mul_of_nonneg_right hab (norm_nonneg _)
    _ = _ := one_mul _

/-- **`EarlyRepThinKernel` from the shared far-kernel leaf** (source 5303-5308, 5318-5319,
5323-5338): the leaf `FarRepThinUng` of the late-output entry also gives the kernel estimate of the
early-source thin entry (task `PartIII-b:C/rep/4/4/1/org/7/1`). -/
theorem earlyRepThinKernel_of_farRepThinUng (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hA : FarRepThinUng Pl σ₀ mZ dm dp) : EarlyRepThinKernel Pl σ₀ mZ dm dp := by
  obtain ⟨k₀, hk⟩ := hA
  refine ⟨k₀, fun D hP hσ hZ hst => ?_⟩
  obtain ⟨C, k, hC, e⟩ := hk D hP hσ hZ hst
  refine ⟨C, k, hC, ?_⟩
  filter_upwards [e, multYoung dm dp D hst] with n a m
  intro z hz T
  have c1 := lrt_early_level D.Pl D.K (D.level n) (D.mu n z) hst.chiY hst.gamma_pos.le
    (fun v => (m v).1) T
  have c2 := a z hz (T - chiOStr (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K)
    (gRate D.Pl) (D.level n).ν D.K.hχo T)
  rw [lrt_repPart_snd] at c2
  exact c1.trans c2

end UnforcedLeray.Short.PartIIIb.Concrete
