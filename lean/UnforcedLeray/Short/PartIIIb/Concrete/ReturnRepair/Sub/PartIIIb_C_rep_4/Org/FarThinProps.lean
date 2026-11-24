import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThinParts

/-!
# `PartIII-b:C/rep/4/1/org` (b): the thin-source row of the table and the thin far leaf

Source `the November 2 reference manuscript` 5301-5372, table 5323-5331, gains
5317-5321, thin-to-thin mass estimate 5342-5355 with 5573-5576, margins 5357-5365, closure
5607-5627.

The thin-source row of the table: in the split stress norm, thin receiver `ε²`, scaled repair
receiver `ε^{49/22}e^{m₀/(2ν)}`; each entry with a common fixed polynomial `P_νS^{k₀}`
(`S = ε^{-b}`, the S-degree `k₀` chosen before `b`) and multiplied by `|N_ν|e^{-4γ/(9ν)}` on late
output or by `e^{3γ/(5ν)}` on early source (5332-5333).  The four entries are stated on the
concrete regions `ftLateOp`, `ftEarlyOp` (`FarThinParts.lean`) applied to the thin part
`(T₁,0)`, read on the thin receiver `(·)₁` (`thinPart`) and the scaled repair receiver `(·)₂`
(`repPart`) of `M_U`, with the thin-source gain norm `A = ‖g⁻¹T‖_Z` (5622-5623); `|N_ν| = gaugeN`.

* `FarLateThinThin` (late output, thin receiver, `ε²`; mass estimate 5342-5355),
* `FarLateThinRep` (late output, repair receiver, `ε^{49/22}e^{m₀/(2ν)}`; order-four kernel
  `L² → L^{22/3}` with off-diagonal norm `D^{-23/11}`, then `√ρ`, 5336-5338),
* `FarEarlyThinThin`, `FarEarlyThinRep` (early source, the same entries times `e^{3γ/(5ν)}`).

**The leaf** `AgeLateEarlyThin` (replaces the old `AgeFarThin`): the bound of `repair:age-error`
(5368-5372) for the far mask *minus its young-old rectangle* on thin sources, stated on
`lateEarlyOp = S_far - χ_yS_μχ_o` of `Org/YThinTrans.lean` (the split
`ageVel = lateEarlyOp + transOp`).  The four entries bound `ftLEOp = (1-χ_y)F_far + χ_yF_far(1-χ_o)`
(`FtLEThinAt`, `FarThinBridge.lean`), and `lateEarlyOp = ftLEOp - χ_yS_Nχ_o` with `χ_yS_Nχ_o = 0`
(`lateEarlyOp_eq`, `NearYoungOldZero`, `FarThinParts.lean`).  The old leaf `AgeFarThin` bounds the
whole `S_μ - S_N = ftLEOp + ftYoungOldOp` (`ftFarOp_thin_split`); its young-old part has young
receiver and old source and is cancelled only by `Y` (4203-4214, 5687-5689).
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace SeqData

variable (D : SeqData)

/-- **Late output, thin source → thin receiver** (table 5323-5331 entry `ε²`, times
`|N_ν|e^{-4γ/(9ν)}`, 5332; the mass estimate 5342-5355, 5573-5576): with `P_ν = Cν^{-k}` and
`S^{k₀} = ε^{-k₀b}`,
`‖(M_U(1-χ_y)F_far(T₁,0))₁‖ ≤ P_ν S^{k₀} ε² |N_ν| e^{-4γ/(9ν)} ‖T‖`. -/
def FarLateThinThinAt (hχ : IsStreamCutoff D.K.χy) (k₀ : ℕ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ T : LStr D.Pl D.K (D.level n),
      ‖thinPart (multOp D.Pl D.K (D.level n)
          (ftLateOp D.Pl D.K (D.level n) (D.mu n z) hχ (thinPart T)))‖ ≤
        C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
          (D.level n).ε ^ (2 : ℝ) * gaugeN D.Pl (D.level n) *
          Real.exp (-(4 * gRate D.Pl / 9) / (D.level n).ν) * ‖T‖

/-- **Late output, thin source → scaled repair receiver** (table 5323-5331 entry
`ε^{49/22}e^{m₀/(2ν)}`, times `|N_ν|e^{-4γ/(9ν)}`; order-four kernel `L² → L^{22/3}`, `D^{-23/11}`,
then `√ρ`, 5336-5338):
`‖(M_U(1-χ_y)F_far(T₁,0))₂‖ ≤ P_ν S^{k₀} ε^{49/22} e^{m₀/(2ν)} |N_ν| e^{-4γ/(9ν)} ‖T‖`. -/
def FarLateThinRepAt (hχ : IsStreamCutoff D.K.χy) (k₀ : ℕ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ T : LStr D.Pl D.K (D.level n),
      ‖repPart (multOp D.Pl D.K (D.level n)
          (ftLateOp D.Pl D.K (D.level n) (D.mu n z) hχ (thinPart T)))‖ ≤
        C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
          (D.level n).ε ^ (49 / 22 : ℝ) * Real.exp (D.K.m0 / 2 / (D.level n).ν) *
          gaugeN D.Pl (D.level n) * Real.exp (-(4 * gRate D.Pl / 9) / (D.level n).ν) * ‖T‖

/-- **Early source, thin source → thin receiver** (table 5323-5331 entry `ε²`, times
`e^{3γ/(5ν)}`, 5332-5333):
`‖(M_Uχ_yF_far(1-χ_o)(T₁,0))₁‖ ≤ P_ν S^{k₀} ε² e^{3γ/(5ν)} ‖T‖`. -/
def FarEarlyThinThinAt (hχ : IsStreamCutoff D.K.χy) (k₀ : ℕ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ T : LStr D.Pl D.K (D.level n),
      ‖thinPart (multOp D.Pl D.K (D.level n)
          (ftEarlyOp D.Pl D.K (D.level n) (D.mu n z) hχ (thinPart T)))‖ ≤
        C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
          (D.level n).ε ^ (2 : ℝ) * Real.exp (3 * gRate D.Pl / 5 / (D.level n).ν) * ‖T‖

/-- **Early source, thin source → scaled repair receiver** (table 5323-5331 entry
`ε^{49/22}e^{m₀/(2ν)}`, times `e^{3γ/(5ν)}`):
`‖(M_Uχ_yF_far(1-χ_o)(T₁,0))₂‖ ≤ P_ν S^{k₀} ε^{49/22} e^{m₀/(2ν)} e^{3γ/(5ν)} ‖T‖`. -/
def FarEarlyThinRepAt (hχ : IsStreamCutoff D.K.χy) (k₀ : ℕ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ T : LStr D.Pl D.K (D.level n),
      ‖repPart (multOp D.Pl D.K (D.level n)
          (ftEarlyOp D.Pl D.K (D.level n) (D.mu n z) hχ (thinPart T)))‖ ≤
        C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
          (D.level n).ε ^ (49 / 22 : ℝ) * Real.exp (D.K.m0 / 2 / (D.level n).ν) *
          Real.exp (3 * gRate D.Pl / 5 / (D.level n).ν) * ‖T‖

/-- **Late output plus early source on thin sources** (source 5368-5372 for these two regions):
`‖M_U((1-χ_y)F_far + χ_yF_far(1-χ_o))(T₁,0)‖ ≤ P_ν e^{-(γ/15-ω_b-3m₀/2)/ν}‖T‖`. -/
def FtLEThinAt (hχ : IsStreamCutoff D.K.χy) (ωb : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ T : LStr D.Pl D.K (D.level n),
      ‖multOp D.Pl D.K (D.level n)
          (ftLEOp D.Pl D.K (D.level n) (D.mu n z) hχ (thinPart T))‖ ≤
        C * (D.level n).ν⁻¹ ^ k *
          Real.exp (-(gRate D.Pl / 15 - ωb - 3 * D.K.m0 / 2) / (D.level n).ν) * ‖T‖

end SeqData

/-- Entry (late, thin → thin), with the S-degree `k₀` chosen before `b` (source 5332, 5607). -/
def FarLateThinThin (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ hst : D.RepairStanding dm dp, D.FarLateThinThinAt hst.chiY k₀

/-- Entry (late, thin → repair). -/
def FarLateThinRep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ hst : D.RepairStanding dm dp, D.FarLateThinRepAt hst.chiY k₀

/-- Entry (early, thin → thin). -/
def FarEarlyThinThin (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ hst : D.RepairStanding dm dp, D.FarEarlyThinThinAt hst.chiY k₀

/-- Entry (early, thin → repair). -/
def FarEarlyThinRep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ hst : D.RepairStanding dm dp, D.FarEarlyThinRepAt hst.chiY k₀

namespace SeqData

/-- **The leaf at one sequence** (source 5357-5372, 5607-5627; the late-output and early-source
regions, 5306-5309): `‖M_U(S_far - χ_yS_μχ_o)(T₁,0)‖ ≤ P_ν e^{-(γ/15-ω_b-3m₀/2)/ν}‖T‖`, the same
form as `AgeTransThinAt` of `Org/YThinTrans.lean`. -/
def AgeLateEarlyThinAt (D : SeqData) (hχ : IsStreamCutoff D.K.χy) (ωb : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ T : LStr D.Pl D.K (D.level n),
      ‖multOp D.Pl D.K (D.level n)
          (lateEarlyOp D.Pl D.K (D.level n) (D.mu n z) hχ (thinPart T))‖ ≤
        C * (D.level n).ν⁻¹ ^ k *
          Real.exp (-(gRate D.Pl / 15 - ωb - 3 * D.K.m0 / 2) / (D.level n).ν) * ‖T‖

end SeqData

/-- **The thin far leaf of `repair:age-error`** (replaces `AgeFarThin`): late output and early
source on thin sources, margin `γ/15` (5357-5372), the S-degree `k₀` chosen before `b`,
`ω_b = k₀bγ/3` (5607). -/
def AgeLateEarlyThin (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ hst : D.RepairStanding dm dp,
      D.AgeLateEarlyThinAt hst.chiY ((k₀ : ℝ) * D.K.b * (gRate D.Pl / 3))

end UnforcedLeray.Short.PartIIIb.Concrete
