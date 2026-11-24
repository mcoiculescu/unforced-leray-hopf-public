import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.EarlyThinBridge
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.MultYoung
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepRep.Props
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.HtUng

/-!
# `PartIII-b:C/rep/4/4/1/org/8/1/org` (a): the early-source repair-receiver kernel from the
shared ungained far-kernel leaf

Source `the November 2 reference manuscript` 5303-5308 (the early-source part
`χ_yF_far(1-χ_o)` of the far mask `s < S`, `t > e^δ s`), 5318-5319 (`g(s)^{-1} ≤ 1` on young
output), 5323-5339 (table; "the repair-to-repair entry uses the source `L^{22/19}` norm and the
`L^{11/3}` kernel"), 5214-5221 (`repair:phase-gradient`: kernel exponent `11/3`, receiver `L^{22/3}`,
power `ε^{46/11}`), 5336 (scaled repair receiver costs `√ρ = ε^{3/22}e^{m₀/(2ν)}`).

**Receiver norm (decision).**  In 5338-5339 and 5218-5221 the number `11/3` is the *Young kernel
exponent* `b` of `sep:young` (`1 + 1/q = 1/p + 1/b` with `p = 22/19`, `q = 22/3` gives `b = 11/3`,
and `D^{-4-j+3/b} = D^{-5+9/11} = D^{-46/11}` for `j = 1`); the *receiver* norm is `L^{22/3}`
(`IIIa.SepRepair`, second conjunct, which is proved from `sep:young` there).  So the blocker
statement `NeededSepRepairL11` (`Kernel/Needed.lean`, receiver `L^{11/3}`) misreads the source and
is not needed.  The statement `EarlyRepRepKernel` of `EarlyRepRep/Props.lean` is consistent with
the source: `ε^{46/11}·√ρ = ε^{92/22}·ε^{3/22} = ε^{95/22}` (`earlyRepRep_exponent`), the factor
`e^{m₀/(2ν)}` being `√ρ`'s exponential part.

**Design.**  As for the thin receiver (`earlyRepThinKernel_of_farRepThinUng`), the whole far
operator `F_far = S_μ - S_N` on an arbitrary repair source `(0,T₂)` is bounded once, *without the
gain*, on the receiver (`FarRepRepUng`, new leaf, shared with the late-output entry); the
early-source region then only needs `M_U χ_y = χ_y M_U` (`multYoung`, proved), `g⁻¹ ≤ 1` on young
output (gain transfer `lrr_gainHT_le_glob`, proved here) and that `χ_o` commutes with the repair
projection (`lrt_chiO_repPart`, proved).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `ε^{46/11}·ε^{3/22} = ε^{95/22}`: kernel power of `repair:phase-gradient` (5218-5221) times the
polynomial part `ε^{3/22}` of the scaled-receiver factor `√ρ` (5134-5139, 5336). -/
theorem earlyRepRep_exponent {ε : ℝ} (hε : 0 < ε) :
    ε ^ (46 / 11 : ℝ) * ε ^ (3 / 22 : ℝ) = ε ^ (95 / 22 : ℝ) := by
  rw [← Real.rpow_add hε]; norm_num

/-- The repair part `(0,T₂)` of the split stress norm has norm `‖T₂‖`. -/
theorem lrr_norm_repPart {c mZ ρb γ ν : ℝ} (x : StrG c mZ ρb γ ν) :
    ‖repPart x‖ = ‖x.snd‖ := by
  rw [WithLp.prod_norm_eq_of_L1]
  simp [repPart]

/-- `htUng` is monotone under an a.e. pointwise bound. -/
theorem lrr_htUng_mono {c ρb : ℝ} {f g : Chart → Ten3}
    (h : ∀ᵐ p ∂(htRhoMeasure c ρb), ‖f p‖ ≤ ‖g p‖) : htUng c ρb f ≤ htUng c ρb g := by
  unfold htUng
  refine ENNReal.rpow_le_rpow (lintegral_mono_ae (h.mono fun p hp => ?_)) (by norm_num)
  exact ENNReal.rpow_le_rpow (enorm_le_iff_norm_le.2 hp) (by norm_num)

/-- **The gain transfer on the repair receiver**: if `g⁻¹ ≤ B` a.e. on the support of `f`, then
`‖g⁻¹f‖_{H_T} ≤ B‖f‖_{H_T}` (source 5318-5319; mirror of `lrt_gainZ1_le_ae`). -/
theorem lrr_gainHT_le_ae {c ρb γ ν B : ℝ} (hB : 0 ≤ B)
    (f : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))
    (hfg : ∀ᵐ p ∂(gainHTMeasure c ρb γ ν), (f : Chart → Ten3) p ≠ 0 → ginv γ ν p ≤ B) :
    ENNReal.ofReal ‖f‖ ≤ ENNReal.ofReal B * htUng c ρb f := by
  have hf' : ∀ᵐ p ∂(htRhoMeasure c ρb), (f : Chart → Ten3) p ≠ 0 → ginv γ ν p ≤ B := by
    rw [← NearInst.ae_gainHTMeasure c ρb γ ν]; exact hfg
  have hd : Measurable fun p : Chart => ENNReal.ofReal (ginv γ ν p ^ 2) :=
    ENNReal.measurable_ofReal.comp ((NearInst.ginv_measurable' γ ν).pow_const 2)
  have e1 : ENNReal.ofReal ‖f‖ =
      (∫⁻ p, ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainHTMeasure c ρb γ ν)) ^ (1 / 2 : ℝ) := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
  have step1 : ∫⁻ p, ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainHTMeasure c ρb γ ν) ≤
      ∫⁻ p, ENNReal.ofReal (B ^ 2) * ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(htRhoMeasure c ρb) := by
    refine le_trans (lintegral_withDensity_le_lintegral_mul (htRhoMeasure c ρb) hd
      (fun p => ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ))) (lintegral_mono_ae (hf'.mono fun p hp => ?_))
    simp only [Pi.mul_apply]
    by_cases ha : (f : Chart → Ten3) p = 0
    · rw [ha]; simp
    · have h1 : ginv γ ν p ^ 2 ≤ B ^ 2 :=
        pow_le_pow_left₀ (NearInst.ginv_pos' γ ν p).le (hp ha) 2
      gcongr
  rw [e1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at *
  unfold htUng
  calc (∫⁻ p, ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainHTMeasure c ρb γ ν)) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (B ^ 2) *
          ∫⁻ p, ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(htRhoMeasure c ρb)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow step1 (by norm_num)
    _ = ENNReal.ofReal B *
          (∫⁻ p, ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(htRhoMeasure c ρb)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (sq_nonneg B) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq hB]

/-- **The gain transfer with a global bound** (young output, `g⁻¹ ≤ 1`, source 5318-5319). -/
theorem lrr_gainHT_le_glob {c ρb γ ν B : ℝ} (hB : 0 ≤ B) (hg : ∀ p : Chart, ginv γ ν p ≤ B)
    (f : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν)) :
    ENNReal.ofReal ‖f‖ ≤ ENNReal.ofReal B * htUng c ρb f :=
  lrr_gainHT_le_ae hB f (Eventually.of_forall fun p _ => hg p)

/-- **One level of the bridge**: the repair receiver of the early-source part on `(0,T₂)` is at most
the ungained repair receiver of `F_far` on `(0,((1-χ_o)T)₂)` (source 5303-5308, 5318-5319). -/
theorem lrr_early_level (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hχ : IsStreamCutoff K.χy) (hγ : 0 ≤ gRate Pl)
    (hM : ∀ v : LVel Pl L,
      ((multOp Pl K L (youngMul hχ v)).snd : Chart → Ten3) =ᵐ[gainHTMeasure
          (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν]
        (fun p => cutFun K.χy L.ν p • ((multOp Pl K L v).snd : Chart → Ten3) p))
    (T : LStr Pl K L) :
    ENNReal.ofReal ‖repPart (multOp Pl K L (earlySrcOp Pl K L μ hχ (repPart T)))‖ ≤
      htUng (cOf L.ν) (L.ρb Pl K)
        ((multOp Pl K L ((Sop Pl K L μ - SNop Pl K L μ)
          (repPart (T - chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo T)))).snd :
          Chart → Ten3) := by
  set u := (Sop Pl K L μ - SNop Pl K L μ)
    (repPart (T - chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo T)) with hu
  have hE : earlySrcOp Pl K L μ hχ (repPart T) = youngMul hχ u := by
    simp only [earlySrcOp, hu, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub, lrt_chiO_repPart]
  rw [hE, lrr_norm_repPart]
  refine (lrr_gainHT_le_glob zero_le_one (fun p => ginv_le_one hγ L.ν_pos.le p) _).trans ?_
  rw [ENNReal.ofReal_one, one_mul]
  refine lrr_htUng_mono ?_
  have h := hM u
  rw [Filter.EventuallyEq, NearInst.ae_gainHTMeasure] at h
  filter_upwards [h] with p hp
  rw [hp, norm_smul, Real.norm_eq_abs]
  have h0 := hχ.range (L.ν * p.1)
  have hab : |cutFun K.χy L.ν p| ≤ 1 := by
    unfold cutFun
    rw [abs_of_nonneg h0.1]; exact h0.2
  calc |cutFun K.χy L.ν p| * ‖((multOp Pl K L u).snd : Chart → Ten3) p‖
      ≤ 1 * ‖((multOp Pl K L u).snd : Chart → Ten3) p‖ :=
        mul_le_mul_of_nonneg_right hab (norm_nonneg _)
    _ = _ := one_mul _

namespace SeqData

variable (D : SeqData)

/-- **(A') The ungained separated-kernel bound, repair source → scaled repair receiver** (source
5323-5339: "the repair-to-repair entry uses the source `L^{22/19}` norm and the `L^{11/3}`
kernel"; kernel power `ε^{46/11}` of `repair:phase-gradient` 5218-5221 with receiver `L^{22/3}`;
receiver factor `√ρ = ε^{3/22}e^{m₀/(2ν)}`, 5336; far mask `s < S`, `t > e^δ s`, `S = ε^{-b}`,
5303-5306; common `P_νS^{k₀}`, 5332): with the S-degree `k₀` fixed before the sequence, for large
`n`, `z ∈ [-1,1]` and every stress `T`, the far operator `F_far = S_μ - S_N` on the repair source
`(0,T₂)` satisfies
`‖(M_UF_far(0,T₂))₂‖_{H_T,ρ_b⁻¹} ≤ Cν^{-k}ε^{-k₀b}ε^{95/22}e^{m₀/(2ν)}‖𝒩_TT₂‖_{L²_τL^{22/19}}`
where the receiver norm is without the gain (`htUng`) and the source norm is the physical phase
norm of `repair:source` (period `2εc`, 5171).  The late-output entry (`LateSepKernelAt`) is this
leaf times the gain `e^{-4γ/(9ν)}` (it can reuse it exactly as `FarRepThinUng` serves both
thin-receiver entries). -/
def FarRepRepUngAt (k₀ : ℕ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ T : LStr D.Pl D.K (D.level n),
      htUng (cOf (D.level n).ν) ((D.level n).ρb D.Pl D.K)
          ((multOp D.Pl D.K (D.level n)
            ((Sop D.Pl D.K (D.level n) (D.mu n z) - SNop D.Pl D.K (D.level n) (D.mu n z))
              (repPart T))).snd : Chart → Ten3) ≤
        ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
          (D.level n).ε ^ (95 / 22 : ℝ) * Real.exp (D.K.m0 / 2 / (D.level n).ν)) *
        phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
          (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) ((repPart T).snd : Chart → Ten3))

end SeqData

/-- **(A') along every standing sequence**, the S-degree `k₀` chosen from `Pl, σ₀, m_Z, d₋, d₊`
before the sequence (before `b`; source 5332, 5607). -/
def FarRepRepUng (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ _hst : D.RepairStanding dm dp, D.FarRepRepUngAt k₀

/-- **`EarlyRepRepKernel` from the shared far-kernel leaf** (source 5303-5308, 5318-5319,
5323-5339): the leaf `FarRepRepUng` bounds `F_far` on every repair source on the ungained repair
receiver; applied to the early source `(0,((1-χ_o)T)₂)` with the young cutoff `χ_y` commuting with
`M_U` and the young-output gain `g⁻¹ ≤ 1` it gives the kernel estimate of the early-source
repair-receiver entry (task `PartIII-b:C/rep/4/4/1/org/8/1`). -/
theorem earlyRepRepKernel_of_farRepRepUng (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hA : FarRepRepUng Pl σ₀ mZ dm dp) : EarlyRepRepKernel Pl σ₀ mZ dm dp := by
  obtain ⟨k₀, hk⟩ := hA
  refine ⟨k₀, fun D hP hσ hZ hst => ?_⟩
  obtain ⟨C, k, hC, e⟩ := hk D hP hσ hZ hst
  refine ⟨C, k, hC, ?_⟩
  filter_upwards [e, multYoung dm dp D hst] with n a m
  intro z hz T
  have c1 := lrr_early_level D.Pl D.K (D.level n) (D.mu n z) hst.chiY hst.gamma_pos.le
    (fun v => (m v).2) T
  have c2 := a z hz (T - chiOStr (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K)
    (gRate D.Pl) (D.level n).ν D.K.hχo T)
  rw [lrt_repPart_snd] at c2
  exact c1.trans c2

end UnforcedLeray.Short.PartIIIb.Concrete
