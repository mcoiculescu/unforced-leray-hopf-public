import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.Transfer
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.MultYoung
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.Props

/-!
# `PartIII-b:C/rep/4/4/1/org/5/org` (c): late output, repair source → thin receiver

Source `the November 2 reference manuscript` 5318 (late output
`g(s)^{-1} ≤ e^{-4γ/(9ν)}`), 5322-5333 (the table "in the split stress norm", repair-source row,
thin receiver `ε^{63/22}e^{m₀/ν}`, common `P_νS^k`, factor `G(w)|N_ν|e^{-4γ/(9ν)}` on late
output), 5337-5338 ("the repair-to-thin entry uses the pointwise exponent `79/22`, followed by
`ρR`"), 5303-5308 (far mask `s < S`, `t > e^δs`, `S = ε^{-b}`; late output `(1-χ_y)F_far`),
5169-5176 (`repair:source`), 5134-5139 (`ρ = ε^{3/11}e^{m₀/ν}`).

`LateRepThin` (`YRepStream/LateEarly.lean`) follows from three facts and the gain transfer:

* **(A) `FarRepThinUng`** (leaf): the separated-kernel bound of the far operator
  `F_far = S_μ - S_N` on a repair source `(0,T₂)`, read on the thin receiver *without the gain*
  (`z1Ung`, the norm of `Z₁`): `‖(M_UF_far(0,T₂))₁‖_{Z₁} ≤ P_νS^{k₀}ε^{79/22}‖𝒩_TT₂‖_{L²_τL^{22/19}}`
  ("the pointwise exponent `79/22`", 5337-5338; all output ages `s < S`).
* **(B) `RepairProductFull`** (`YRepStream/LateRepRep/Props.lean`, proved as `repairProductAll` in
  `LateRepRep/ProductFull.lean`): `repair:source` 5169-5176 for the unlocalised repair stress,
  `‖r_b⊗w+w⊗r_b‖_{L²_τL^{22/19}} ≤ P_νρR|N_ν|G(w)` ("followed by `ρR`").
* **(C) the output region and its gain**: `M_U` commutes with `χ_y` (`multYoung`, proved,
  `MultYoung.lean`), so the thin receiver of the late output is `(1-χ_y)(M_UF_far(0,T₂))₁`, which
  vanishes at ages `s < 0.8/ν` and is pointwise below `(M_UF_far(0,T₂))₁`; the gain transfer
  `lrt_gainZ1_le` with `g(s)^{-1} ≤ e^{-4γ/(9ν)}` on `s ≥ 0.8/ν` (`lrt_ginv_late`, 5318) gives
  the factor `e^{-4γ/(9ν)}`.

Exponents: `ε^{79/22}·ρR = ε^{79/22}ε^{3/11}e^{m₀/ν}ε^{-1} = ε^{63/22}e^{m₀/ν}`
(`lateRepThinAt_of`, `lateRepThin_of`).

**Generic design.**  Leaf (A) bounds the whole far operator, every output age `s < S`, on an
arbitrary repair source `(0,T₂)`; it therefore serves both thin-receiver entries: late output
(`T = M_Uw`, then the cutoff `1-χ_y` and the gain `e^{-4γ/(9ν)}` of (C)) and early source
(`T = (1-χ_o)M_Uw`, then the cutoff `χ_y` and `g⁻¹ ≤ 1`).  `MultYoungAt` is stated on both receivers
(`Z₁` and `H_T`), and the transfer `lrt_gainZ1_le` is generic in the age threshold and the gain
bound, so the two repair-receiver entries need only the `H_T` analogue of (A) (kernel
`L^{22/19} → L^{11/3}`, `ε^{95/22}e^{m₀/(2ν)}`, 5338-5339) and of `lrt_gainZ1_le`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace SeqData

variable (D : SeqData)

/-- **(A) The ungained separated-kernel bound, repair source → thin receiver** (source
5323-5338: "the general separated kernel bounds ... the repair-to-thin entry uses the pointwise
exponent `79/22`"; far mask `s < S`, `t > e^δs`, `S = ε^{-b}`, 5303-5306; common `P_νS^{k₀}`,
5332): with the S-degree `k₀` fixed before the sequence, for large `n`, `z ∈ [-1,1]` and every
stress `T`, the far operator `F_far = S_μ - S_N` on the repair source `(0,T₂)` satisfies
`‖(M_UF_far(0,T₂))₁‖_{Z₁} ≤ Cν^{-k}ε^{-k₀b}ε^{79/22}‖𝒩_TT₂‖_{L²_τL^{22/19}}`, where `‖·‖_{Z₁}` is the
`Z₁` norm without the gain (`z1Ung`, 2697) and the source norm is the physical phase norm of
`repair:source` (period `2εc`, 5171). -/
def FarRepThinUngAt (k₀ : ℕ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ T : LStr D.Pl D.K (D.level n),
      z1Ung (cOf (D.level n).ν) D.K.mZ
          ((multOp D.Pl D.K (D.level n)
            ((Sop D.Pl D.K (D.level n) (D.mu n z) - SNop D.Pl D.K (D.level n) (D.mu n z))
              (repPart T))).fst : Chart → Ten3) ≤
        ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
          (D.level n).ε ^ (79 / 22 : ℝ)) *
        phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
          (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) ((repPart T).snd : Chart → Ten3))

end SeqData

/-- **(A) along every standing sequence**, the S-degree `k₀` chosen from `Pl, σ₀, m_Z, d₋, d₊`
before the sequence (before `b`; source 5332, 5607). -/
def FarRepThinUng (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ _hst : D.RepairStanding dm dp, D.FarRepThinUngAt k₀

/-- The late output of a far velocity at one level: `(M_U(1-χ_y)v)₁ = (1-χ_y)(M_Uv)₁`, vanishing
at ages `s < 0.8/ν` and pointwise below `(M_Uv)₁` (source 4164, 5306-5307). -/
theorem lrt_lateCut (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (hχ : IsStreamCutoff K.χy)
    (hM : ∀ v : LVel Pl L,
      ((multOp Pl K L (youngMul hχ v)).fst : Chart → Ten3) =ᵐ[gainZ1Measure
          (cOf L.ν) K.mZ (gRate Pl) L.ν]
        (fun p => cutFun K.χy L.ν p • ((multOp Pl K L v).fst : Chart → Ten3) p))
    (v : LVel Pl L) :
    (∀ᵐ p ∂(gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν), p.1 < 4 / 5 / L.ν →
        ((multOp Pl K L (v - youngMul hχ v)).fst : Chart → Ten3) p = 0) ∧
      ∀ᵐ p ∂(z1Measure (cOf L.ν) K.mZ),
        ‖((multOp Pl K L (v - youngMul hχ v)).fst : Chart → Ten3) p‖ ≤
          ‖((multOp Pl K L v).fst : Chart → Ten3) p‖ := by
  have hν := L.ν_pos
  have hfst : (multOp Pl K L (v - youngMul hχ v)).fst =
      (multOp Pl K L v).fst - (multOp Pl K L (youngMul hχ v)).fst := by
    rw [map_sub]; rfl
  have hae : ∀ᵐ p ∂(gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν),
      ((multOp Pl K L (v - youngMul hχ v)).fst : Chart → Ten3) p =
        (1 - cutFun K.χy L.ν p) • ((multOp Pl K L v).fst : Chart → Ten3) p := by
    filter_upwards [Lp.coeFn_sub (multOp Pl K L v).fst
      (multOp Pl K L (youngMul hχ v)).fst, hM v] with p e1 e2
    rw [hfst, e1, Pi.sub_apply, e2, sub_smul, one_smul]
  refine ⟨hae.mono fun p hp hs => ?_, ?_⟩
  · have h1 : cutFun K.χy L.ν p = 1 := by
      unfold cutFun
      refine hχ.one _ ?_
      have := (lt_div_iff₀ hν).1 hs
      linarith
    rw [hp, h1, sub_self, zero_smul]
  · have hae' : ∀ᵐ p ∂(z1Measure (cOf L.ν) K.mZ),
        ((multOp Pl K L (v - youngMul hχ v)).fst : Chart → Ten3) p =
          (1 - cutFun K.χy L.ν p) • ((multOp Pl K L v).fst : Chart → Ten3) p := by
      rw [← NearInst.ae_gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν]; exact hae
    filter_upwards [hae'] with p hp
    rw [hp, norm_smul, Real.norm_eq_abs]
    have h0 := hχ.range (L.ν * p.1)
    have hab : |1 - cutFun K.χy L.ν p| ≤ 1 := by
      unfold cutFun
      rw [abs_le]; constructor <;> linarith [h0.1, h0.2]
    calc |1 - cutFun K.χy L.ν p| * ‖((multOp Pl K L v).fst : Chart → Ten3) p‖
        ≤ 1 * ‖((multOp Pl K L v).fst : Chart → Ten3) p‖ :=
          mul_le_mul_of_nonneg_right hab (norm_nonneg _)
      _ = _ := one_mul _

/-- **(C) at one level**: the thin receiver of the late output is bounded by `e^{-4γ/(9ν)}` times
the ungained thin receiver of the far velocity (source 5318, 5322-5333). -/
theorem lrt_late_level (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hχ : IsStreamCutoff K.χy) (hγ : 0 ≤ gRate Pl)
    (hM : ∀ v : LVel Pl L,
      ((multOp Pl K L (youngMul hχ v)).fst : Chart → Ten3) =ᵐ[gainZ1Measure
          (cOf L.ν) K.mZ (gRate Pl) L.ν]
        (fun p => cutFun K.χy L.ν p • ((multOp Pl K L v).fst : Chart → Ten3) p))
    (x : LStr Pl K L) :
    ENNReal.ofReal ‖thinPart (multOp Pl K L (lateOutOp Pl K L μ hχ x))‖ ≤
      ENNReal.ofReal (Real.exp (-(4 * gRate Pl / 9) / L.ν)) *
        z1Ung (cOf L.ν) K.mZ
          ((multOp Pl K L ((Sop Pl K L μ - SNop Pl K L μ) x)).fst : Chart → Ten3) := by
  have hlate : lateOutOp Pl K L μ hχ x =
      (Sop Pl K L μ - SNop Pl K L μ) x - youngMul hχ ((Sop Pl K L μ - SNop Pl K L μ) x) := rfl
  obtain ⟨hsupp, hpt⟩ := lrt_lateCut Pl K L hχ hM ((Sop Pl K L μ - SNop Pl K L μ) x)
  rw [lrt_norm_thinPart, hlate]
  refine (lrt_gainZ1_le (Real.exp_pos _).le (fun p hp => lrt_ginv_late hγ L.ν_pos p hp) _
    hsupp).trans ?_
  gcongr
  exact lrt_z1Ung_mono hpt

/-- The exponent bookkeeping of the entry: `ε^{79/22}·ε^{3/11}·ε^{-1} = ε^{63/22}`
(source 5337-5338). -/
theorem lrt_alg {ε ν C1 C2 kb m0 N E W : ℝ} {k1 k2 : ℕ} (hε : 0 < ε) :
    E * ((C1 * ν⁻¹ ^ k1 * ε ^ (-kb) * ε ^ (79 / 22 : ℝ)) *
      (C2 * ν⁻¹ ^ k2 * (ε ^ (3 / 11 : ℝ) * Real.exp (m0 / ν)) * ε⁻¹ * N * W)) =
    C1 * C2 * ν⁻¹ ^ (k1 + k2) * ε ^ (-kb) * ε ^ (63 / 22 : ℝ) * Real.exp (m0 / ν) * N * E *
      W := by
  have e1 : ε ^ (63 / 22 : ℝ) = ε ^ (79 / 22 : ℝ) * ε ^ (3 / 11 : ℝ) * ε⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hε, ← Real.rpow_add hε]; norm_num
  rw [e1, pow_add]
  ring

namespace SeqData

variable (D : SeqData)

/-- **The entry from (A), (B), (C)** (source 5318, 5323-5338): `ε^{79/22}·ε^{3/11}·ε^{-1} =
ε^{63/22}`, `ρ = ε^{3/11}e^{m₀/ν}`, output gain `e^{-4γ/(9ν)}`. -/
theorem lateRepThinAt_of (hχ : IsStreamCutoff D.K.χy) (k₀ : ℕ) (hγ : 0 ≤ gRate D.Pl)
    (hA : D.FarRepThinUngAt k₀) (hM : D.MultYoungAt hχ) (hB : D.RepairProductFull) :
    D.LateRepThinAt hχ k₀ := by
  obtain ⟨C1, k1, hC1, eA⟩ := hA
  obtain ⟨C2, k2, eB⟩ := hB
  refine ⟨C1 * max C2 0, k1 + k2, ?_⟩
  filter_upwards [eA, hM, eB] with n a m b
  intro z hz w
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hN0 : 0 ≤ gaugeN D.Pl (D.level n) := norm_nonneg _
  have c1 := lrt_late_level D.Pl D.K (D.level n) (D.mu n z) hχ hγ (fun v => (m v).1)
    (repPart (multOp D.Pl D.K (D.level n) w))
  have c2 := a z hz (multOp D.Pl D.K (D.level n) w)
  have c3 : phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
      (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν)
        ((repPart (multOp D.Pl D.K (D.level n) w)).snd : Chart → Ten3)) ≤
      ENNReal.ofReal (max C2 0 * (D.level n).ν⁻¹ ^ k2 *
        ((D.level n).ε ^ (3 / 11 : ℝ) * Real.exp (D.K.m0 / (D.level n).ν)) * (D.level n).ε⁻¹ *
          gaugeN D.Pl (D.level n) * ‖w‖) := by
    refine (b w).trans (ENNReal.ofReal_le_ofReal ?_)
    unfold rhoRep
    gcongr
    exact le_max_left C2 0
  have hA0 : 0 ≤ C1 * (D.level n).ν⁻¹ ^ k1 * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
      (D.level n).ε ^ (79 / 22 : ℝ) := by positivity
  have c4 := c1.trans (mul_le_mul' le_rfl (c2.trans (mul_le_mul' le_rfl c3)))
  rw [← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at c4
  exact c4.trans_eq (lrt_alg hε)

end SeqData

/-- **`LateRepThin` from the ungained separated kernel (A), the multiplier commutation (proved)
and the product estimate (B)** (source 5318, 5323-5338, 5169-5176). -/
theorem lateRepThin_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) (hA : FarRepThinUng Pl σ₀ mZ dm dp)
    (hB : RepairProductAll dm dp) : LateRepThin Pl σ₀ mZ dm dp := by
  obtain ⟨k₀, hk⟩ := hA
  exact ⟨k₀, fun D hP hσ hZ hst => D.lateRepThinAt_of hst.chiY k₀ hst.gamma_pos.le
    (hk D hP hσ hZ hst) (multYoung dm dp D hst) (hB D hst)⟩

end UnforcedLeray.Short.PartIIIb.Concrete
