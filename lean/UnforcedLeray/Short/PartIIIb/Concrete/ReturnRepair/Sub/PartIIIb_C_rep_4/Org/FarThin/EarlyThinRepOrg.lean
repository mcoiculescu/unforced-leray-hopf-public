import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.ThinRepKernel
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThinProps
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.MultYoung

/-!
# `PartIII-b:C/rep/4/1/org/5/org` (b): the early-source thin-to-repair entry from the kernel

Source `the November 2 reference manuscript` 5303-5311 (the early-source part
`χ_yF_far(1-χ_o)`), 5318-5319 ("on early source, `g(t) ≤ e^{3γ/(5ν)}`"), 5323-5339 (table entry
thin source → scaled repair receiver `ε^{49/22}e^{m₀/(2ν)}`, common `P_νS^k`, "multiplied by
`G(w)e^{3γ/(5ν)}` for early source"), 4163-4166 (`χ_o = 0` for `t ≤ 1.2/ν`, `χ_o = 1` for
`t ≥ 1.5/ν`), 2697-2700 (the split stress norm).

`farEarlyThinRep_of`: `FarEarlyThinRep` (`Org/FarThinProps.lean`) from the ungained kernel leaf
`FarThinRepKernel` (`Org/FarThin/ThinRepKernel.lean`), in three steps, all proved here:

* **region**: `χ_yF_far(1-χ_o)(T₁,0) = χ_yF_far((T - χ_oT)₁,0)` (`ftk_chiO_thinPart`; `χ_o` acts
  componentwise);
* **output**: `M_U` commutes with `χ_y` on the repair receiver (`multYoung`), `|χ_y| ≤ 1` and
  `g⁻¹ ≤ 1`, so the gained receiver is at most `htUng` of `(M_UF_far((T-χ_oT)₁,0))₂`
  (`ftk_early_level`);
* **source**: `(1-χ_o)T₁` vanishes at ages `t ≥ 1.5/ν`, where `g(t) ≤ e^{3γ/(5ν)}`
  (`ftGain_early`), so `‖(1-χ_o)T₁‖_{Z₁} ≤ e^{3γ/(5ν)}‖g⁻¹T₁‖_{Z₁} ≤ e^{3γ/(5ν)}‖T‖`
  (`ftk_early_source`, `ftk_z1Ung_le_gain`).

The S-degree `k₀` and the constant `P_ν = Cν^{-k}` are those of the kernel (`k₀` chosen before the
sequence, 5332, 5607); the entry is the kernel bound times `e^{3γ/(5ν)}`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Componentwise facts on the split stress space -/

/-- `χ_o` acts componentwise, so it commutes with the thin projection `(T₁,T₂) ↦ (T₁,0)`. -/
theorem ftk_chiO_thinPart {c mZ ρb γ ν : ℝ} {χ : ℝ → ℝ} (hχ : IsOutwardCutoff χ)
    (T : StrG c mZ ρb γ ν) :
    chiOStr c mZ ρb γ ν hχ (thinPart T) = thinPart (chiOStr c mZ ρb γ ν hχ T) := by
  apply (WithLp.prodContinuousLinearEquiv 1 ℝ (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
    (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))).injective
  simp [chiOStr, thinPart]

/-- `‖(0,T₂)‖_Z = ρ_b^{-1/2}‖g⁻¹T₂‖_{H_T}` (source 2697-2700). -/
theorem ftk_norm_repPart {c mZ ρb γ ν : ℝ} (x : StrG c mZ ρb γ ν) :
    ‖repPart x‖ = ‖x.snd‖ := by
  rw [WithLp.prod_norm_eq_of_L1]
  simp [repPart]

/-- `‖g⁻¹T₁‖_{Z₁} ≤ ‖T‖_Z` (source 2697-2700, the sum norm). -/
theorem ftk_norm_fst_le {c mZ ρb γ ν : ℝ} (x : StrG c mZ ρb γ ν) : ‖x.fst‖ ≤ ‖x‖ := by
  rw [WithLp.prod_norm_eq_of_L1]
  exact le_add_of_nonneg_right (norm_nonneg _)

/-- `g⁻¹ ≤ 1` for `γ ≥ 0` (source 3875, 5117). -/
theorem ftk_ginv_le_one {γ ν : ℝ} (hγ : 0 ≤ γ) (hν : 0 ≤ ν) (p : Chart) : ginv γ ν p ≤ 1 := by
  unfold ginv UnforcedLeray.Short.IIIa.gainG
  have hs : 0 ≤ max p.1 0 := le_max_right _ _
  have hd : 0 < 1 + ν * max p.1 0 := by nlinarith
  have h1 : 0 ≤ γ * max p.1 0 / (1 + ν * max p.1 0) := div_nonneg (mul_nonneg hγ hs) hd.le
  exact inv_le_one_of_one_le₀ (Real.one_le_exp h1)

/-- **Early source**: `1 ≤ e^{3γ/(5ν)}g(t)^{-1}` at ages `νt < 3/2` (source 5318-5319;
`ftGain_early`). -/
theorem ftk_one_le_early {γ ν : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (p : Chart) (hp : ν * p.1 < 3 / 2) :
    1 ≤ Real.exp (3 * γ / 5 / ν) * ginv γ ν p := by
  have hs : 0 ≤ max p.1 0 := le_max_right _ _
  have hle : max p.1 0 ≤ 3 / 2 / ν := by
    rw [le_div_iff₀ hν]
    rcases le_total p.1 0 with h | h
    · rw [max_eq_right h]; norm_num
    · rw [max_eq_left h]; linarith
  have hg := ftGain_early hγ hν hs hle
  have hpos : 0 < UnforcedLeray.Short.IIIa.gainG γ ν (max p.1 0) := by
    unfold UnforcedLeray.Short.IIIa.gainG; exact Real.exp_pos _
  unfold ginv
  rw [← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
  exact hg

/-! ## 2. The source and the output of the early-source region at one level -/

section Level

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)

/-- **The early source** (source 5308, 5318-5319, 4163-4166): the ungained thin norm of
`((1-χ_o)T)₁` is at most `e^{3γ/(5ν)}‖g⁻¹T₁‖_{Z₁}`. -/
theorem ftk_early_source (hγ : 0 ≤ gRate Pl) (T : LStr Pl K L) :
    z1Ung (cOf L.ν) K.mZ ((T - ftOld Pl K L T).fst : Chart → Ten3) ≤
      ENNReal.ofReal (Real.exp (3 * gRate Pl / 5 / L.ν)) * ENNReal.ofReal ‖T.fst‖ := by
  have hν := L.ν_pos
  have hO : ((ftOld Pl K L T).fst : Chart → Ten3) =ᵐ[gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν]
      cutFun K.χo L.ν • ((T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure (cOf L.ν) K.mZ
        (gRate Pl) L.ν)) : Chart → Ten3) :=
    NearInst.mulBdd_apply_ae (cutFun K.χo L.ν) (cutFun_measurable K.hχo L.ν) 1
      (cutFun_bound K.hχo L.ν) T.fst
  have hS := Lp.coeFn_sub T.fst (ftOld Pl K L T).fst
  have hae : ∀ᵐ p ∂(gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν),
      ‖((T - ftOld Pl K L T).fst : Chart → Ten3) p‖ ≤
        Real.exp (3 * gRate Pl / 5 / L.ν) * ginv (gRate Pl) L.ν p *
          ‖(T.fst : Chart → Ten3) p‖ := by
    filter_upwards [hO, hS] with p e1 e2
    rw [WithLp.sub_fst, e2, Pi.sub_apply, e1, Pi.smul_apply']
    have hr : (T.fst : Chart → Ten3) p - cutFun K.χo L.ν p • (T.fst : Chart → Ten3) p =
        (1 - cutFun K.χo L.ν p) • (T.fst : Chart → Ten3) p := by
      rw [sub_smul, one_smul]
    rw [hr, norm_smul, Real.norm_eq_abs]
    have h0 := K.hχo.range (L.ν * p.1)
    have hab : |1 - cutFun K.χo L.ν p| ≤ 1 := by
      unfold cutFun
      rw [abs_le]; constructor <;> linarith [h0.1, h0.2]
    by_cases hp : L.ν * p.1 < 3 / 2
    · have h1 := ftk_one_le_early hγ hν p hp
      calc |1 - cutFun K.χo L.ν p| * ‖(T.fst : Chart → Ten3) p‖
          ≤ 1 * ‖(T.fst : Chart → Ten3) p‖ := mul_le_mul_of_nonneg_right hab (norm_nonneg _)
        _ ≤ (Real.exp (3 * gRate Pl / 5 / L.ν) * ginv (gRate Pl) L.ν p) *
              ‖(T.fst : Chart → Ten3) p‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    · have h1 : cutFun K.χo L.ν p = 1 := by
        unfold cutFun
        exact K.hχo.one _ (le_of_not_gt hp)
      rw [h1, sub_self, abs_zero, zero_mul]
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (NearInst.ginv_pos' _ _ p).le)
        (norm_nonneg _)
  have hae' : ∀ᵐ p ∂(z1Measure (cOf L.ν) K.mZ),
      ‖((T - ftOld Pl K L T).fst : Chart → Ten3) p‖ ≤
        Real.exp (3 * gRate Pl / 5 / L.ν) * ginv (gRate Pl) L.ν p *
          ‖(T.fst : Chart → Ten3) p‖ := by
    rw [← NearInst.ae_gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν]; exact hae
  exact ftk_z1Ung_le_gain (Real.exp_pos _).le _ T.fst hae'

/-- **The early-source output at one level** (source 5303-5308, 5318-5319): the scaled repair
receiver of `M_Uχ_yF_far(1-χ_o)(T₁,0)` is at most the ungained repair receiver of
`M_UF_far((T-χ_oT)₁,0)`. -/
theorem ftk_early_level (μ : ℝ) (hχ : IsStreamCutoff K.χy) (hγ : 0 ≤ gRate Pl)
    (hM : ∀ v : LVel Pl L,
      ((multOp Pl K L (youngMul hχ v)).snd : Chart → Ten3) =ᵐ[gainHTMeasure
          (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν]
        (fun p => cutFun K.χy L.ν p • ((multOp Pl K L v).snd : Chart → Ten3) p))
    (T : LStr Pl K L) :
    ENNReal.ofReal ‖repPart (multOp Pl K L (ftEarlyOp Pl K L μ hχ (thinPart T)))‖ ≤
      htUng (cOf L.ν) (L.ρb Pl K)
        ((multOp Pl K L ((Sop Pl K L μ - SNop Pl K L μ)
          (thinPart (T - ftOld Pl K L T)))).snd : Chart → Ten3) := by
  set u := (Sop Pl K L μ - SNop Pl K L μ) (thinPart (T - ftOld Pl K L T)) with hu
  have hE : ftEarlyOp Pl K L μ hχ (thinPart T) = youngMul hχ u := by
    rw [hu, map_sub, ← ftk_chiO_thinPart]
    rfl
  rw [hE, ftk_norm_repPart]
  have c1 := ftk_gainHT_le_glob zero_le_one
    (fun p => ftk_ginv_le_one hγ L.ν_pos.le p) (multOp Pl K L (youngMul hχ u)).snd
  rw [ENNReal.ofReal_one, one_mul] at c1
  refine c1.trans (ftk_htUng_mono ?_)
  have hM' : ∀ᵐ p ∂(htRhoMeasure (cOf L.ν) (L.ρb Pl K)),
      ((multOp Pl K L (youngMul hχ u)).snd : Chart → Ten3) p =
        cutFun K.χy L.ν p • ((multOp Pl K L u).snd : Chart → Ten3) p := by
    rw [← NearInst.ae_gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν]; exact hM u
  filter_upwards [hM'] with p hp
  rw [hp, norm_smul, Real.norm_eq_abs]
  have hab : |cutFun K.χy L.ν p| ≤ 1 := cutFun_bound_y hχ L.ν p
  calc |cutFun K.χy L.ν p| * ‖((multOp Pl K L u).snd : Chart → Ten3) p‖
      ≤ 1 * ‖((multOp Pl K L u).snd : Chart → Ten3) p‖ :=
        mul_le_mul_of_nonneg_right hab (norm_nonneg _)
    _ = _ := one_mul _

end Level

/-! ## 3. The entry -/

namespace SeqData

variable (D : SeqData)

/-- **The early-source thin-to-repair entry at one sequence from the kernel** (source 5318-5319,
5323-5339): the kernel bound `Cν^{-k}ε^{-k₀b}ε^{49/22}e^{m₀/(2ν)}` times the source gain
`e^{3γ/(5ν)}`. -/
theorem farEarlyThinRepAt_of (hχ : IsStreamCutoff D.K.χy) (k₀ : ℕ) (hγ : 0 ≤ gRate D.Pl)
    (hK : D.FarThinRepKernelAt k₀) (hM : D.MultYoungAt hχ) : D.FarEarlyThinRepAt hχ k₀ := by
  obtain ⟨C, k, hC, eK⟩ := hK
  refine ⟨C, k, ?_⟩
  filter_upwards [eK, hM] with n a m
  intro z hz T
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have c1 := ftk_early_level D.Pl D.K (D.level n) (D.mu n z) hχ hγ (fun v => (m v).2) T
  have c2 := a z hz (T - ftOld D.Pl D.K (D.level n) T)
  have c3 := ftk_early_source D.Pl D.K (D.level n) hγ T
  set Kc : ℝ := C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
    (D.level n).ε ^ (49 / 22 : ℝ) * Real.exp (D.K.m0 / 2 / (D.level n).ν) with hKc
  set E : ℝ := Real.exp (3 * gRate D.Pl / 5 / (D.level n).ν) with hE
  have hK0 : 0 ≤ Kc := by positivity
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have c4 := c1.trans (c2.trans (mul_le_mul' le_rfl c3))
  rw [← ENNReal.ofReal_mul hE0, ← ENNReal.ofReal_mul hK0,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at c4
  calc ‖repPart (multOp D.Pl D.K (D.level n)
          (ftEarlyOp D.Pl D.K (D.level n) (D.mu n z) hχ (thinPart T)))‖
      ≤ Kc * (E * ‖T.fst‖) := c4
    _ ≤ Kc * (E * ‖T‖) := by
        gcongr
        exact ftk_norm_fst_le T
    _ = C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
          (D.level n).ε ^ (49 / 22 : ℝ) * Real.exp (D.K.m0 / 2 / (D.level n).ν) *
          Real.exp (3 * gRate D.Pl / 5 / (D.level n).ν) * ‖T‖ := by
        rw [hKc, hE]; ring

end SeqData

/-- **`FarEarlyThinRep` from the ungained thin-to-repair kernel** (source 5303-5311, 5318-5319,
5323-5339), with the multiplier commutation `multYoung` (proved): the S-degree `k₀` is that of the
kernel, chosen before the sequence. -/
theorem farEarlyThinRep_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hK : FarThinRepKernel Pl σ₀ mZ dm dp) : FarEarlyThinRep Pl σ₀ mZ dm dp := by
  obtain ⟨k₀, hk⟩ := hK
  exact ⟨k₀, fun D hP hσ hZ hst => D.farEarlyThinRepAt_of hst.chiY k₀ hst.gamma_pos.le
    (hk D hP hσ hZ hst) (multYoung dm dp D hst)⟩

end UnforcedLeray.Short.PartIIIb.Concrete
