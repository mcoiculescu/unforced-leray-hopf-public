import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.Trans

/-!
# `PartIII-b:C/rep/4/4/1/org` (b): the late-output and early-source regions on repair sources

Source `the November 2 reference manuscript` 5303-5309 (the far mask and its
regions), 5318-5319 (gains), 5323-5334 (table, repair-source row, common `P_νS^k`, factors
`G(w)|N_ν|e^{-4γ/(9ν)}` and `G(w)e^{3γ/(5ν)}`), 5337-5339 (repair-to-thin: pointwise exponent
`79/22` then `ρR`; repair-to-repair: source `L^{22/19}` norm and `L^{11/3}` kernel), margins
5362-5365, closure 5607-5623.

`lateEarlyOp = S_far - χ_yS_μχ_o` (`Org/YThinTrans.lean`) is the far mask minus its young-old
rectangle.  The near operator removes only the far mask `s < S`, `t > e^δs`, `S = ε^{-b}`, and
"the young-old rectangle is contained in this mask" (5303-5306): on young receivers `s ≤ 1/ν < S`
the old source `t ≥ 1.2/ν > e^δs` is entirely far, so `χ_yS_Nχ_o = 0` (`NearYoungOldAt`).  Then
`lateEarlyOp = (1-χ_y)F_far + χ_yF_far(1-χ_o)` exactly ("its complement is exactly the late-output
part and the early-source part", 5306-5308; `lateEarlyOp_eq_of`).

The four repair-source entries (late/early × thin/repair receiver) are stated on `lateOutOp`,
`earlySrcOp` applied to `(0,(M_Uw)₂)`, read on the thin receiver `(·)₁` and the scaled repair
receiver `(·)₂`, with the repair-source norm `G(w) = ‖w‖` (5622-5623) and `|N_ν| = gaugeN`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The two regions at one regime -/

section Ops

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
  (hχy : IsStreamCutoff K.χy)

/-- **The late-output part `(1-χ_y)F_far`** of the far mask (source 5306-5307): output ages
`s ≥ 0.8/ν`, `F_far = S_μ - S_N`. -/
def lateOutOp : LStr Pl K L →L[ℝ] LVel Pl L :=
  (ContinuousLinearMap.id ℝ (LVel Pl L) - youngMul hχy).comp (Sop Pl K L μ - SNop Pl K L μ)

/-- **The early-source part `χ_yF_far(1-χ_o)`** of the far mask (source 5307-5308): young
output, source ages `t < 1.5/ν`. -/
def earlySrcOp : LStr Pl K L →L[ℝ] LVel Pl L :=
  (youngMul hχy).comp ((Sop Pl K L μ - SNop Pl K L μ).comp
    (ContinuousLinearMap.id ℝ (LStr Pl K L) -
      chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo))

/-- **The young-old rectangle lies in the far mask** (source 5303-5306; 3902-3920 `S_N = S_μ -
S_far`, `S_far = 1_{s<S, t>e^δs}S_μ`, gap `δ < log(6/5)`): the near operator has no young-old
part, `χ_yS_N(χ_oT) = 0` for every stress `T` (young receivers `s ≤ 1/ν < S`, old sources
`t ≥ 1.2/ν > e^δs`). -/
def NearYoungOldAt : Prop :=
  ∀ T : LStr Pl K L,
    youngMul hχy (SNop Pl K L μ (chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo T)) = 0

/-- **`S_far - χ_yS_μχ_o = (1-χ_y)F_far + χ_yF_far(1-χ_o)`** (source 5303-5308), given that the
young-old rectangle lies in the far mask. -/
theorem lateEarlyOp_eq_of (h : NearYoungOldAt Pl K L μ hχy) (T : LStr Pl K L) :
    lateEarlyOp Pl K L μ hχy T = lateOutOp Pl K L μ hχy T + earlySrcOp Pl K L μ hχy T := by
  have h0 := h T
  simp only [lateEarlyOp, lateOutOp, earlySrcOp, youngOldOp, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.id_apply, map_sub]
  rw [h0]
  abel

end Ops

/-! ## 2. The repair-source row of the table along the sequence -/

namespace SeqData

variable (D : SeqData)

/-- **Late output, repair source → thin receiver** (table 5328 entry `ε^{63/22}e^{m₀/ν}`, times
`G(w)|N_ν|e^{-4γ/(9ν)}`, 5332-5333; "the pointwise exponent `79/22`, followed by `ρR`",
5337-5338; late-output gain `g(s)⁻¹ ≤ e^{-4γ/(9ν)}`, 5318): with `P_ν = Cν^{-k}`,
`S^{k₀} = ε^{-k₀b}`,
`‖(M_U(1-χ_y)F_far(0,(M_Uw)₂))₁‖ ≤ P_νS^{k₀}ε^{63/22}e^{m₀/ν}|N_ν|e^{-4γ/(9ν)}G(w)`. -/
def LateRepThinAt (hχ : IsStreamCutoff D.K.χy) (k₀ : ℕ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ w : LVel D.Pl (D.level n),
      ‖thinPart (multOp D.Pl D.K (D.level n)
          (lateOutOp D.Pl D.K (D.level n) (D.mu n z) hχ
            (repPart (multOp D.Pl D.K (D.level n) w))))‖ ≤
        C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
          (D.level n).ε ^ (63 / 22 : ℝ) * Real.exp (D.K.m0 / (D.level n).ν) *
          gaugeN D.Pl (D.level n) * Real.exp (-(4 * gRate D.Pl / 9) / (D.level n).ν) * ‖w‖

/-- **Late output, repair source → scaled repair receiver** (table 5329 entry
`ε^{79/22}e^{3m₀/(2ν)}`, times `G(w)|N_ν|e^{-4γ/(9ν)}`, 5332-5333; "the source `L^{22/19}` norm
and the `L^{11/3}` kernel", 5338-5339, with `repair:source` 5169-5176):
`‖(M_U(1-χ_y)F_far(0,(M_Uw)₂))₂‖ ≤ P_νS^{k₀}ε^{79/22}e^{3m₀/(2ν)}|N_ν|e^{-4γ/(9ν)}G(w)`. -/
def LateRepRepAt (hχ : IsStreamCutoff D.K.χy) (k₀ : ℕ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ w : LVel D.Pl (D.level n),
      ‖repPart (multOp D.Pl D.K (D.level n)
          (lateOutOp D.Pl D.K (D.level n) (D.mu n z) hχ
            (repPart (multOp D.Pl D.K (D.level n) w))))‖ ≤
        C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
          (D.level n).ε ^ (79 / 22 : ℝ) * Real.exp (3 * D.K.m0 / 2 / (D.level n).ν) *
          gaugeN D.Pl (D.level n) * Real.exp (-(4 * gRate D.Pl / 9) / (D.level n).ν) * ‖w‖

/-- **Early source, repair source → thin receiver** (table 5328 entry `ε^{63/22}e^{m₀/ν}`, times
`G(w)e^{3γ/(5ν)}`, 5333-5334; early-source gain `g(t) ≤ e^{3γ/(5ν)}`, 5318-5319):
`‖(M_Uχ_yF_far(1-χ_o)(0,(M_Uw)₂))₁‖ ≤ P_νS^{k₀}ε^{63/22}e^{m₀/ν}e^{3γ/(5ν)}G(w)`. -/
def EarlyRepThinAt (hχ : IsStreamCutoff D.K.χy) (k₀ : ℕ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ w : LVel D.Pl (D.level n),
      ‖thinPart (multOp D.Pl D.K (D.level n)
          (earlySrcOp D.Pl D.K (D.level n) (D.mu n z) hχ
            (repPart (multOp D.Pl D.K (D.level n) w))))‖ ≤
        C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
          (D.level n).ε ^ (63 / 22 : ℝ) * Real.exp (D.K.m0 / (D.level n).ν) *
          Real.exp (3 * gRate D.Pl / 5 / (D.level n).ν) * ‖w‖

/-- **Early source, repair source → scaled repair receiver** (table 5329 entry
`ε^{79/22}e^{3m₀/(2ν)}`, times `G(w)e^{3γ/(5ν)}`, 5333-5334, 5338-5339):
`‖(M_Uχ_yF_far(1-χ_o)(0,(M_Uw)₂))₂‖ ≤ P_νS^{k₀}ε^{79/22}e^{3m₀/(2ν)}e^{3γ/(5ν)}G(w)`. -/
def EarlyRepRepAt (hχ : IsStreamCutoff D.K.χy) (k₀ : ℕ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ w : LVel D.Pl (D.level n),
      ‖repPart (multOp D.Pl D.K (D.level n)
          (earlySrcOp D.Pl D.K (D.level n) (D.mu n z) hχ
            (repPart (multOp D.Pl D.K (D.level n) w))))‖ ≤
        C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
          (D.level n).ε ^ (79 / 22 : ℝ) * Real.exp (3 * D.K.m0 / 2 / (D.level n).ν) *
          Real.exp (3 * gRate D.Pl / 5 / (D.level n).ν) * ‖w‖

/-- **The late-output and early-source regions on repair sources** (source 5303-5308, 5362-5372,
closure 5617: `δ_G`): `‖g⁻¹M_U(S_far - χ_yS_μχ_o)(0,(M_Uw)₂)‖_Z ≤
P_ν e^{-(19γ/66-ω_b-3m₀/2)/ν}G(w)`. -/
def AgeLateEarlyRepAt (hχ : IsStreamCutoff D.K.χy) (ωb : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ w : LVel D.Pl (D.level n),
      ‖multOp D.Pl D.K (D.level n)
          (lateEarlyOp D.Pl D.K (D.level n) (D.mu n z) hχ
            (repPart (multOp D.Pl D.K (D.level n) w)))‖ ≤
        C * (D.level n).ν⁻¹ ^ k *
          Real.exp (-(19 * gRate D.Pl / 66 - ωb - 3 * D.K.m0 / 2) / (D.level n).ν) * ‖w‖

end SeqData

/-- (L0) The young-old rectangle lies in the far mask, for large `n` and every `z ∈ [-1,1]`
(source 5303-5306, 3902-3920). -/
def NearYoungOld (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, ∀ hst : D.RepairStanding dm dp, ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    NearYoungOldAt D.Pl D.K (D.level n) (D.mu n z) hst.chiY

/-- (L1) Entry (late, repair → thin), with the S-degree `k₀` chosen before `b` (source 5332,
5607). -/
def LateRepThin (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ hst : D.RepairStanding dm dp, D.LateRepThinAt hst.chiY k₀

/-- (L2) Entry (late, repair → repair). -/
def LateRepRep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ hst : D.RepairStanding dm dp, D.LateRepRepAt hst.chiY k₀

/-- (L3) Entry (early, repair → thin). -/
def EarlyRepThin (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ hst : D.RepairStanding dm dp, D.EarlyRepThinAt hst.chiY k₀

/-- (L4) Entry (early, repair → repair). -/
def EarlyRepRep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ hst : D.RepairStanding dm dp, D.EarlyRepRepAt hst.chiY k₀

/-- **The repair far-region leaf** of `repair:age-error` (replaces `AgeFarRep`, which bounds the
whole far mask including its young-old rectangle): margin `19γ/66` (5617), `ω_b = k₀bγ/3`
(5607). -/
def AgeLateEarlyRep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ hst : D.RepairStanding dm dp,
      D.AgeLateEarlyRepAt hst.chiY ((k₀ : ℝ) * D.K.b * (gRate D.Pl / 3))

end UnforcedLeray.Short.PartIIIb.Concrete
