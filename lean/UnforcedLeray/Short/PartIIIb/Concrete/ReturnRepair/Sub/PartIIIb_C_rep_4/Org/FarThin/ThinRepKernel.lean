import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.Transfer
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.HtUng

/-!
# `PartIII-b:C/rep/4/1/org/5/org` (a): the thin-to-repair far kernel, shared by both regions

Source `the November 2 reference manuscript` 5303-5311 (the far mask `s < S`,
`t > e^δs`, `S = ε^{-b}`, and its two regions), 5317-5319 (the gains), 5323-5339 (the table "in the
split stress norm": thin source, scaled repair receiver `ε^{49/22}e^{m₀/(2ν)}`, common `P_νS^k`;
"the thin-to-repair entry uses the order-four kernel from `L²` to `L^{22/3}`, with off-diagonal norm
`D^{-23/11}`, followed by `√ρ`"), 3603-3606 (`sep:kernel`), 3622-3626 (`sep:resolvent`), 3631-3650
(`sep:young`), 3902-3912 (the masked far part), 2693-2706 (the split stress norm and `ρ_b`),
5134-5139 (`‖r_b‖_{C_τL^{11/4}} ≤ P_νρ`, `ρ = ε^{3/11}e^{m₀/ν}`).

**The one kernel leaf of the thin-source/repair-receiver column** (`FarThinRepKernel`).  It bounds
the far operator `F_far = S_μ - S_N` on a thin source `(T₁,0)`, read on the scaled repair receiver
`ρ_b^{-1/2}(M_U ·)₂` of `M_U`, *without either gain*: the receiver norm is `htUng` (the norm of
`ρ_b^{-1/2}H_T`, 2697-2700, without `g⁻¹`) and the source norm is `z1Ung` (the norm of `Z₁`,
2697, without `g⁻¹`); every output age `s < S` and every source age `t > e^δs` of the far mask
is included.  The two table entries then follow by reading off the gains from the supports
(5317-5319):

* **early source** `χ_yF_far(1-χ_o)` (`FarEarlyThinRep`, `Org/FarThin/EarlyThinRepOrg.lean`):
  the source `(1-χ_o)T₁` lives at ages `t ≤ 1.5/ν`, so its ungained norm is at most
  `e^{3γ/(5ν)}‖g⁻¹T₁‖_{Z₁}` (`ftGain_early`, `ftk_z1Ung_le_gain`); the output is young and
  `g⁻¹ ≤ 1` (`ftk_gainHT_le_glob`);
* **late output** `(1-χ_y)F_far` (`FarLateThinRep`): the output lives at ages `s ≥ 0.8/ν`, so
  the gained receiver is at most `e^{-4γ/(9ν)}` times `htUng` (`ftk_gainHT_le`, `ftGain_late`); the
  source has `g(t) ≤ e^{γ/ν} = |N_ν|ν^{Re κ}` (`ft_gaugeN_eq`), hence `|N_ν|`.

**The separated-kernel realization (the sep bridge).**  By `concreteBase_isNearSplit`
(`Concrete/ReturnInst/Inverses/Level.lean` 328), along a standing sequence `S_N = S_μ - S_far`
with `S_far` satisfying `IsFarMaskG` (`Concrete/PhysLayer.lean` 234): on the dense class of box
tensors `f = T₁ + T₂` (`NearInst.IsBoxTensor`) `S_far` is, at output ages `s < S`, the chart
coefficient `s^{-1/2}Re(-NearInst.sepWfar ν μ R δ s (cartLift R c f))` of the masked negative
response `IIIa.sepW` (`sep:resolvent` 3622-3626, the tensor at input age `t = R²/|z'|²` kept only
for `t > e^δs`), and zero for `s ≥ S`.  So `FarThinRepKernel` is the statement of 5335-5336 for that
kernel: `sep:young` (3644-3650) with `p = 2`, `q = 22/3`, `1/b = 1/2 + 3/22`, gives
`‖1_young ∇W‖_{L²_τL^{22/3}} ≤ CD^{-23/11}‖T₁‖_{L²_τL²}` (the order-four kernel `|∇K_t| ≤ C|x|^{-4}`,
3603-3606, radial gap `D`, `D^{-4+3/b} = D^{-23/11}` with `D ≍ R/√s`), and Hölder with
`‖r_b‖_{L^{11/4}} ≤ P_νρ` (5136-5139; `1/2 = 3/22 + 4/11`) followed by the scale `ρ_b^{-1/2}`
of the repair receiver (`ρ_b = P_νρ`, 2701-2706) gives `P_νS^{k₀}ε^{23/11}√ρ =
P_νS^{k₀}ε^{49/22}e^{m₀/(2ν)}`.

Contents:

* `htUng` : the ungained scaled repair receiver norm `ρ_b^{-1/2}‖T₂‖_{H_T}`;
* `ftk_htUng_mono` : monotone under an a.e. pointwise bound (proved);
* `ftk_gainHT_le_ae`, `ftk_gainHT_le`, `ftk_gainHT_le_glob` : the output gain transfer on the
  repair receiver (proved; the `H_T` analogue of `lrt_gainZ1_le`);
* `ftk_z1Ung_le_gain` : the source gain transfer, an ungained thin source pointwise below
  `E g⁻¹|T₁|` has `z1Ung ≤ E‖g⁻¹T₁‖_{Z₁}` (proved);
* `SeqData.FarThinRepKernelAt`, `FarThinRepKernel` : the kernel leaf.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The ungained scaled repair receiver and the two gain transfers -/

/-- `htUng` is monotone under an a.e. pointwise bound. -/
theorem ftk_htUng_mono {c ρb : ℝ} {f g : Chart → Ten3}
    (h : ∀ᵐ p ∂(htRhoMeasure c ρb), ‖f p‖ ≤ ‖g p‖) : htUng c ρb f ≤ htUng c ρb g := by
  unfold htUng
  refine ENNReal.rpow_le_rpow (lintegral_mono_ae (h.mono fun p hp => ?_)) (by norm_num)
  exact ENNReal.rpow_le_rpow (enorm_le_iff_norm_le.2 hp) (by norm_num)

/-- **The output gain transfer on the repair receiver, general form**: if `g⁻¹ ≤ B` a.e. on the
support of `f`, then `ρ_b^{-1/2}‖g⁻¹f‖_{H_T} ≤ B ρ_b^{-1/2}‖f‖_{H_T}` (source 5317-5319, 5322-5333). -/
theorem ftk_gainHT_le_ae {c ρb γ ν B : ℝ} (hB : 0 ≤ B)
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

/-- **The output gain transfer on an age region** (late output: `a = 0.8/ν`,
`B = e^{-4γ/(9ν)}`, source 5317-5318): a repair-receiver stress vanishing at ages `s < a` has
`ρ_b^{-1/2}‖g⁻¹f‖_{H_T} ≤ B ρ_b^{-1/2}‖f‖_{H_T}` whenever `g(s)^{-1} ≤ B` for `s ≥ a`. -/
theorem ftk_gainHT_le {c ρb γ ν a B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ p : Chart, a ≤ p.1 → ginv γ ν p ≤ B)
    (f : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))
    (hf : ∀ᵐ p ∂(gainHTMeasure c ρb γ ν), p.1 < a → (f : Chart → Ten3) p = 0) :
    ENNReal.ofReal ‖f‖ ≤ ENNReal.ofReal B * htUng c ρb f := by
  refine ftk_gainHT_le_ae hB f (hf.mono fun p hp hne => hg p ?_)
  by_contra h
  exact hne (hp (lt_of_not_ge h))

/-- **The output gain transfer with a global bound** (young output, `g⁻¹ ≤ 1`, source
5318-5319). -/
theorem ftk_gainHT_le_glob {c ρb γ ν B : ℝ} (hB : 0 ≤ B) (hg : ∀ p : Chart, ginv γ ν p ≤ B)
    (f : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν)) :
    ENNReal.ofReal ‖f‖ ≤ ENNReal.ofReal B * htUng c ρb f :=
  ftk_gainHT_le_ae hB f (Eventually.of_forall fun p _ => hg p)

/-- **The source gain transfer** (source 5318-5319, 5332-5333; early source `E = e^{3γ/(5ν)}`,
late output `E = e^{γ/ν}`): an ungained thin source `f` pointwise below `E g⁻¹|T₁|` has
`‖f‖_{Z₁} ≤ E‖g⁻¹T₁‖_{Z₁}`. -/
theorem ftk_z1Ung_le_gain {c mZ γ ν E : ℝ} (hE : 0 ≤ E) (f : Chart → Ten3)
    (T : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
    (h : ∀ᵐ p ∂(z1Measure c mZ), ‖f p‖ ≤ E * ginv γ ν p * ‖(T : Chart → Ten3) p‖) :
    z1Ung c mZ f ≤ ENNReal.ofReal E * ENNReal.ofReal ‖T‖ := by
  have hd : Measurable fun p : Chart => ENNReal.ofReal (ginv γ ν p ^ 2) :=
    ENNReal.measurable_ofReal.comp ((NearInst.ginv_measurable' γ ν).pow_const 2)
  have e1 : ENNReal.ofReal ‖T‖ =
      (∫⁻ p, ‖(T : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainZ1Measure c mZ γ ν)) ^ (1 / 2 : ℝ) := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top T),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∫⁻ p, ‖(T : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainZ1Measure c mZ γ ν) =
      ∫⁻ p, ENNReal.ofReal (ginv γ ν p ^ 2) * ‖(T : Chart → Ten3) p‖ₑ ^ (2 : ℝ)
        ∂(z1Measure c mZ) :=
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ hd
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _
  have step : ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ) ≤
      ∫⁻ p, ENNReal.ofReal (E ^ 2) *
        (ENNReal.ofReal (ginv γ ν p ^ 2) * ‖(T : Chart → Ten3) p‖ₑ ^ (2 : ℝ)) ∂(z1Measure c mZ) := by
    refine lintegral_mono_ae (h.mono fun p hp => ?_)
    have hg0 : 0 ≤ ginv γ ν p := (NearInst.ginv_pos' γ ν p).le
    have h1 : ‖f p‖ₑ ≤ ENNReal.ofReal E * ENNReal.ofReal (ginv γ ν p) *
        ‖(T : Chart → Ten3) p‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hE,
        ← ENNReal.ofReal_mul (mul_nonneg hE hg0)]
      exact ENNReal.ofReal_le_ofReal hp
    calc ‖f p‖ₑ ^ (2 : ℝ)
        ≤ (ENNReal.ofReal E * ENNReal.ofReal (ginv γ ν p) * ‖(T : Chart → Ten3) p‖ₑ) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow h1 (by norm_num)
      _ = ENNReal.ofReal (E ^ 2) *
            (ENNReal.ofReal (ginv γ ν p ^ 2) * ‖(T : Chart → Ten3) p‖ₑ ^ (2 : ℝ)) := by
          rw [ENNReal.ofReal_pow hE, ENNReal.ofReal_pow hg0]
          simp only [ENNReal.rpow_two]
          ring
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← e2] at step
  rw [e1]
  unfold z1Ung
  calc (∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ)) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (E ^ 2) *
          ∫⁻ p, ‖(T : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainZ1Measure c mZ γ ν)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow step (by norm_num)
    _ = ENNReal.ofReal E *
          (∫⁻ p, ‖(T : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainZ1Measure c mZ γ ν)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (sq_nonneg E) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq hE]

/-! ## 2. The kernel leaf -/

namespace SeqData

variable (D : SeqData)

/-- **The ungained thin-to-repair far kernel** (source 5323-5339: "the thin-to-repair entry uses
the order-four kernel from `L²` to `L^{22/3}`, with off-diagonal norm `D^{-23/11}`, followed by
`√ρ`"; `sep:young` 3644-3650 with `p = 2`, `q = 22/3`; far mask `s < S`, `t > e^δs`,
`S = ε^{-b}`, 5303-5306, 3902-3912, realized by `NearInst.sepWfar` through `IsFarMaskG` and
`concreteBase_isNearSplit`; `‖r_b‖_{L^{11/4}} ≤ P_νρ`, 5136-5139; common `P_νS^{k₀}`, 5332): with
the S-degree `k₀` fixed before the sequence, for large `n`, every `z ∈ [-1,1]` and every stress
`T`, the far operator `F_far = S_μ - S_N` on the thin source `(T₁,0)` satisfies
`ρ_b^{-1/2}‖(M_UF_far(T₁,0))₂‖_{H_T} ≤ Cν^{-k}ε^{-k₀b}ε^{49/22}e^{m₀/(2ν)}‖T₁‖_{Z₁}`, both norms
without the gain (`htUng`, `z1Ung`; 2697-2700), every output and every source age of the mask. -/
def FarThinRepKernelAt (k₀ : ℕ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ T : LStr D.Pl D.K (D.level n),
      htUng (cOf (D.level n).ν) ((D.level n).ρb D.Pl D.K)
          ((multOp D.Pl D.K (D.level n)
            ((Sop D.Pl D.K (D.level n) (D.mu n z) - SNop D.Pl D.K (D.level n) (D.mu n z))
              (thinPart T))).snd : Chart → Ten3) ≤
        ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
          (D.level n).ε ^ (49 / 22 : ℝ) * Real.exp (D.K.m0 / 2 / (D.level n).ν)) *
        z1Ung (cOf (D.level n).ν) D.K.mZ (T.fst : Chart → Ten3)

end SeqData

/-- **The thin-to-repair far kernel along every standing sequence**, the S-degree `k₀` chosen from
`Pl, σ₀, m_Z, d₋, d₊` before the sequence (before `b`; source 5332, 5607).  Shared by the
early-source entry `FarEarlyThinRep` (`farEarlyThinRep_of`, `Org/FarThin/EarlyThinRepOrg.lean`)
and the late-output entry `FarLateThinRep` (`Org/FarThinProps.lean`). -/
def FarThinRepKernel (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ _hst : D.RepairStanding dm dp, D.FarThinRepKernelAt k₀

end UnforcedLeray.Short.PartIIIb.Concrete
