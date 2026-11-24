import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThinBridge
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.LateThinRepOrg.Leaves
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.Bridge
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps

/-!
# `PartIII-b:C/rep/4/1/org/3/org`: late output, thin source → scaled repair receiver

Source `the November 2 reference manuscript` 5303-5311 (far mask `s < S`,
`t > e^δs`, `S = ε^{-b}`; late-output part `(1-χ_y)F_far`), 5317-5318 (late output
`g(s)^{-1} ≤ e^{-4γ/(9ν)}`), 5323-5332 (table, thin source → scaled repair receiver
`ε^{49/22}e^{m₀/(2ν)}`, common `P_νS^k`, factor `|N_ν|e^{-4γ/(9ν)}`), 5336-5338 ("the
thin-to-repair entry uses the order-four kernel from `L²` to `L^{22/3}`, with off-diagonal norm
`D^{-23/11}`, followed by `√ρ`"), 5134-5139 (`‖r_b‖_{C_τL^{11/4}} ≤ P_νρ`, `ρ = ε^{3/11}e^{m₀/ν}`),
2697-2713 (`Z = Z₁ ⊕ ρ_b^{-1/2}H_T`, `ρ_b = C₀ν^{-k₀}e^{m₀/ν}ε^{3/11}`), 2683-2689 (lifts),
3593-3594 and 3902-3920 (`S_far = 1_{s<S,t>e^δs}S_μ` in its kernel realization, pinned on smooth
(box) tensors and completed in the norms).

`FarLateThinRep` (`Org/FarThinProps.lean`) follows from

* **(A) the far-mask bridge for thin sources** `ThinFarSepBridge` (proved here,
  `thinFarSepBridge_of`, from `StrBoxTrunc`, task `PartIII-b:C/rep/4/4/1/org/7/1/1`, and
  `SopSubIsFarSeq`, task `PartIII-b:C/rep/5/1/1/1`): every bound of a continuous linear functional
  of the velocity, proved for far-kernel outputs `farOut f` of box tensors `f` in the source norm
  `‖𝒩_Tf‖_{L²_τL²}`, holds for `F_far = S_μ - S_N` on the thin source `(T₁,0)` with
  `‖𝒩_TT₁‖_{L²_τL²}` (truncation `1_{A_k}T₁`, continuity).  This is the separated-kernel bound
  for `S_far` on thin sources: the far mask (receiver age `s < S`, source age `t > e^δs`) enters
  through the kernel pin `IsFarMaskG`.
* **(B) the order-four kernel `L² → L^{22/3}`** `FarVelYoungBoxL2` (leaf, new, `Leaves.lean`):
  `‖𝒩_v farOut f‖_{L²_τL^{22/3}} ≤ C D₀^{-23/11}‖𝒩_Tf‖_{L²_τL²}`, `D₀ = (1-e^{-δ/2})R/√S`
  (`sep:young` with `j = 0`, `p = 2`, `q = 22/3`, `b = 11/7`: `-4 + 3/b = -23/11`), the twin of
  `FarVelYoungBox` (`p = 22/19`, task `PartIII-b:C/rep/4/4/1/org/6/1/2`) from the same pointwise
  majorant `FarVelPointwise` (task `PartIII-b:C/rep/4/4/1/org/6/1/1`) and `IIIa.sepDomYoung`;
  **followed by `√ρ`**: the receiver conversion `RepRecvConv` (task
  `PartIII-b:C/rep/4/4/1/org/6/1/3`, shared with the repair-to-repair entry):
  `‖(M_Uv)₂‖_{ρ_b^{-1/2}H_T} ≤ P_νε^{25/22}e^{m₀/(2ν)}‖𝒩_vv‖_{L²_τL^{22/3}}`
  (`r_b⊗v + v⊗r_b`, Hölder `1/2 = 4/11 + 3/22`, `‖r_b(τ)‖_{11/4} ≤ ρ_b`, `R⁻¹√ρ_b`).
* **the source lift** `ThinLiftZ1` (leaf, new, `Leaves.lean`): `‖𝒩_TT₁‖_{L²_τL²} ≤ √πR‖T₁‖_{Z₁}` (unweighted
  lift identity `‖𝒩_TT‖²_{Y₂} = πR²‖T‖²_{H_T}`, `|nsSym T| ≤ |T|`, `W ≥ 1`).
* proved here: the late-output gain on the repair receiver (`ltr_late_rep`, `M_Uχ_y = χ_yM_U`,
  `g(s)^{-1} ≤ e^{-4γ/(9ν)}` on `s ≥ 0.8/ν`), the source gain `‖T₁‖_{Z₁} ≤ e^{γ/ν}‖g⁻¹T₁‖`
  (`ltr_z1Ung_le_gain`), `e^{γ/ν} ≤ ν^{-k}|N_ν|` (`ltr_exp_le_gauge`, 5118).

Exponents: `ε^{25/22}·(ε^{23/11}S^{23/22})·R = ε^{25/22+46/22-1}S^{23/22} = ε^{49/22}S^{23/22}`,
`S^{23/22} ≤ S² = ε^{-2b}` (`ε ≤ 1`), so the S-degree is `k₀ = 2`, fixed before the sequence.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi Topology
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. (A) The far-mask bridge for thin sources -/

namespace LateThinRep

/-- The component sum of the thin part `(T₁, 0)` is a.e. `T₁` (for `ρ_b > 0` the gain measure of
the repair receiver has the null sets of `s^{-1/2}dς`). -/
theorem ltr_strSum_thinPart {c mZ ρb γ ν : ℝ} (hρ : 0 < ρb) (T : StrG c mZ ρb γ ν) :
    strSum (thinPart T) =ᵐ[ageμ c (-1 / 2)] (T.fst : Chart → Ten3) := by
  have hs : (thinPart T).snd = 0 := by simp [thinPart]
  have hf : (thinPart T).fst = T.fst := by simp [thinPart]
  have h1 : ((thinPart T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] 0 := by
    rw [hs]; exact Lp.coeFn_zero _ _ _
  have hne : ENNReal.ofReal ρb⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hρ)).ne'
  rw [Filter.EventuallyEq, NearInst.ae_gainHTMeasure, htRhoMeasure,
    Measure.ae_ennreal_smul_measure_eq hne] at h1
  filter_upwards [h1] with p hp
  simp only [strSum, hf, hp, Pi.zero_apply, add_zero]

end LateThinRep

open LateThinRep

/-- **(A) The far-mask bridge for thin sources** (source 3902-3920, 3611-3621, 3593-3594,
5303-5308): for large `n` and `z ∈ [-1,1]`, every bound `‖Φ v‖ ≤ B‖𝒩_Tf‖_{L²_τL²}` (period
`2εc`) of a continuous linear functional `Φ` of the velocity, valid for the far-kernel outputs
`v = farOut f` (`NearInst.Masked.farOut` with the level's `R = ε⁻¹`, `c = ν⁻²`, gap `δ`, output
cut `S = ε^{-b}`: receiver ages `s < S`, source ages `t > e^δs`) of box tensors `f`, holds for the
far operator `F_far = S_μ - S_N` (`ftFarOp`) on the thin source `(T₁,0)`, with `‖𝒩_TT₁‖_{L²_τL²}`
on the right. -/
def ThinFarSepBridge (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ (E : Type) [NormedAddCommGroup E]
      [NormedSpace ℝ E] (Φ : LVel D.Pl (D.level n) →L[ℝ] E) (B : ℝ),
      (∀ (v : LVel D.Pl (D.level n)) (f : Chart → Ten3), NearInst.IsBoxTensor f →
        (v : Chart → Merid) =ᵐ[ageμ (cOf (D.level n).ν) (-3 / 2)]
          NearInst.Masked.farOut (D.level n).ε⁻¹ (cOf (D.level n).ν) (D.level n).ν (D.mu n z)
            D.K.δ ((D.level n).Scut D.K) f →
        ENNReal.ofReal ‖Φ v‖ ≤ ENNReal.ofReal B *
          phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) 2
            (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) f)) →
      ∀ T : LStr D.Pl D.K (D.level n),
        ENNReal.ofReal ‖Φ (ftFarOp D.Pl D.K (D.level n) (D.mu n z) (thinPart T))‖ ≤
          ENNReal.ofReal B * phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) 2
            (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) (T.fst : Chart → Ten3))

/-- **(A) from `StrBoxTrunc` and `SopSubIsFarSeq`** (source 3593-3594, 3902-3920, 5303-5308):
the box truncations `1_{A_k}T₁` of the thin component carry the bound (the lifted source norm
decreases under truncation, `ebr_phaseL2Lr_indicator_le`), and `Φ ∘ S_far` is continuous. -/
theorem thinFarSepBridge_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) (h1 : StrBoxTrunc)
    (h3 : SopSubIsFarSeq Pl σ₀ mZ dm dp) : ThinFarSepBridge Pl σ₀ mZ dm dp := by
  intro D hPl hσ hmZ hst
  filter_upwards [h3 D hPl hσ hmZ hst] with n hn z hz E _ _ Φ B hB T
  obtain ⟨Sf, hSf, hFS⟩ := hn z hz
  have hc : 0 < cOf (D.level n).ν := cOf_pos (D.level n).ν_pos
  have hρ : 0 < (D.level n).ρb D.Pl D.K := inv_rhoB_pos hst.C0_pos
  have hY := ltr_strSum_thinPart hρ T
  obtain ⟨A, Fn, hbox, hsum, hlim⟩ := h1 _ _ _ _ _ hc hρ (D.level n).ν_pos _ _
    (Lp.stronglyMeasurable T.fst).measurable hY
  have hbd : ∀ k, ENNReal.ofReal ‖Φ (Sf (Fn k))‖ ≤ ENNReal.ofReal B *
      phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) 2
        (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) (T.fst : Chart → Ten3)) := by
    intro k
    have e := hSf (Fn k) ((A k).indicator (T.fst : Chart → Ten3)) (hbox k) (hsum k)
    refine (hB (Sf (Fn k)) _ (hbox k) e).trans ?_
    exact mul_le_mul_of_nonneg_left
      (ebr_phaseL2Lr_indicator_le _ _ _ _ (by norm_num) _ _) zero_le
  have hcont : Tendsto (fun k => ENNReal.ofReal ‖Φ (Sf (Fn k))‖) atTop
      (𝓝 (ENNReal.ofReal ‖Φ (Sf (thinPart T))‖)) := by
    have h0 := ((Φ.comp Sf).continuous.tendsto _).comp hlim
    exact (ENNReal.continuous_ofReal.tendsto _).comp (h0.norm)
  have hF : ftFarOp D.Pl D.K (D.level n) (D.mu n z) = Sf := hFS
  rw [hF]
  exact le_of_tendsto' hcont hbd

namespace LateThinRep

/-! ## 2. The gains -/

/-- `g(s) ≤ e^{γ/ν}` for `s ≥ 0`, `γ ≥ 0` (source 3881, 5117: `g(s) = e^{γs/(1+νs)}`). -/
theorem ltr_gain_le {γ ν s : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (hs : 0 ≤ s) :
    UnforcedLeray.Short.IIIa.gainG γ ν s ≤ Real.exp (γ / ν) := by
  unfold UnforcedLeray.Short.IIIa.gainG
  have h1 : 0 < 1 + ν * s := by positivity
  rw [Real.exp_le_exp, div_le_div_iff₀ h1 hν]
  nlinarith [mul_nonneg hγ hs]

theorem ltr_one_le {γ ν : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (p : Chart) :
    1 ≤ Real.exp (γ / ν) ^ 2 * ginv γ ν p ^ 2 := by
  have hg : 0 < UnforcedLeray.Short.IIIa.gainG γ ν (max p.1 0) := by
    unfold UnforcedLeray.Short.IIIa.gainG; exact Real.exp_pos _
  have hle := ltr_gain_le hγ hν (le_max_right p.1 0)
  have h1 : 1 ≤ Real.exp (γ / ν) * ginv γ ν p := by
    unfold ginv
    rw [← div_eq_mul_inv, one_le_div hg]
    exact hle
  have h2 : 1 ≤ (Real.exp (γ / ν) * ginv γ ν p) ^ 2 := one_le_pow₀ h1
  rwa [mul_pow] at h2

/-- **The source gain** (source 5175, 5622-5623): `‖T₁‖_{Z₁} ≤ e^{γ/ν}‖g⁻¹T₁‖_{Z₁}`
(`g ≤ e^{γ/ν}`). -/
theorem ltr_z1Ung_le_gain {c mZ γ ν : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν)
    (f : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)) :
    z1Ung c mZ f ≤ ENNReal.ofReal (Real.exp (γ / ν)) * ENNReal.ofReal ‖f‖ := by
  have hd : Measurable fun p : Chart => ENNReal.ofReal (ginv γ ν p ^ 2) :=
    ENNReal.measurable_ofReal.comp ((NearInst.ginv_measurable' γ ν).pow_const 2)
  have hfm : Measurable fun p => ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) :=
    (Lp.stronglyMeasurable f).measurable.enorm.pow_const _
  have e1 : ENNReal.ofReal ‖f‖ =
      (∫⁻ p, ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainZ1Measure c mZ γ ν)) ^ (1 / 2 : ℝ) := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∫⁻ p, ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(gainZ1Measure c mZ γ ν) =
      ∫⁻ p, ENNReal.ofReal (ginv γ ν p ^ 2) * ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ)
        ∂(z1Measure c mZ) := by
    unfold gainZ1Measure
    exact lintegral_withDensity_eq_lintegral_mul _ hd hfm
  have step : ∫⁻ p, ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ) ≤
      ENNReal.ofReal (Real.exp (γ / ν) ^ 2) *
        ∫⁻ p, ENNReal.ofReal (ginv γ ν p ^ 2) * ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ)
          ∂(z1Measure c mZ) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun p => ?_
    have h1 := ltr_one_le hγ hν p
    calc ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) = 1 * ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) :=
          (one_mul _).symm
      _ ≤ ENNReal.ofReal (Real.exp (γ / ν) ^ 2 * ginv γ ν p ^ 2) *
            ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) := by
          gcongr
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (Real.exp (γ / ν) ^ 2) *
            (ENNReal.ofReal (ginv γ ν p ^ 2) * ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ)) := by
          rw [ENNReal.ofReal_mul (sq_nonneg _), mul_assoc]
  unfold z1Ung
  rw [e1, e2]
  calc (∫⁻ p, ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ)) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (Real.exp (γ / ν) ^ 2) *
          ∫⁻ p, ENNReal.ofReal (ginv γ ν p ^ 2) * ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ)
            ∂(z1Measure c mZ)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow step (by norm_num)
    _ = ENNReal.ofReal (Real.exp (γ / ν)) *
          (∫⁻ p, ENNReal.ofReal (ginv γ ν p ^ 2) * ‖(f : Chart → Ten3) p‖ₑ ^ (2 : ℝ)
            ∂(z1Measure c mZ)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq (Real.exp_pos _).le]

/-- `e^{γ/ν} = |N_ν|ν^{Re κ} ≤ ν^{-k}|N_ν|` for `0 < ν ≤ 1` (source 5118). -/
theorem ltr_exp_le_gauge (Pl : PlanarData) (L : ReturnLevel) (hν1 : L.ν ≤ 1) :
    Real.exp (gRate Pl / L.ν) ≤ L.ν⁻¹ ^ (⌈-Pl.kappa.re⌉₊) * gaugeN Pl L := by
  have hν := L.ν_pos
  have hN := ft_gaugeN_eq Pl L
  have h1 : L.ν ^ Pl.kappa.re ≤ L.ν⁻¹ ^ (⌈-Pl.kappa.re⌉₊) := by
    rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hν.le]
    exact Real.rpow_le_rpow_of_exponent_ge hν hν1 (by linarith [Nat.le_ceil (-Pl.kappa.re)])
  have h2 : Real.exp (gRate Pl / L.ν) = gaugeN Pl L * L.ν ^ Pl.kappa.re := by
    rw [hN, mul_assoc, ← Real.rpow_add hν]; simp
  rw [h2, mul_comm]
  exact mul_le_mul_of_nonneg_right h1 (by rw [hN]; positivity)

/-- **The late-output gain on the repair receiver** (source 5306-5307, 5317-5318): for every
velocity `v`, `‖(M_U(1-χ_y)v)₂‖ ≤ e^{-4γ/(9ν)}‖(M_Uv)₂‖_{ρ_b^{-1/2}H_T, ungained}` (the cut
output vanishes at ages `s < 0.8/ν`, `lrr_lateCutRep`). -/
theorem ltr_late_rep (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (hχ : IsStreamCutoff K.χy) (hγ : 0 ≤ gRate Pl)
    (hM : ∀ v : LVel Pl L,
      ((multOp Pl K L (youngMul hχ v)).snd : Chart → Ten3) =ᵐ[gainHTMeasure
          (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν]
        (fun p => cutFun K.χy L.ν p • ((multOp Pl K L v).snd : Chart → Ten3) p))
    (v : LVel Pl L) :
    ENNReal.ofReal ‖repPart (multOp Pl K L (v - youngMul hχ v))‖ ≤
      ENNReal.ofReal (Real.exp (-(4 * gRate Pl / 9) / L.ν)) *
        htUng (cOf L.ν) (L.ρb Pl K) ((multOp Pl K L v).snd : Chart → Ten3) := by
  obtain ⟨hsupp, hpt⟩ := lrr_lateCutRep Pl K L hχ hM v
  rw [lrr_norm_repPart]
  refine (lrr_gainHT_le (Real.exp_pos _).le (fun p hp => lrt_ginv_late hγ L.ν_pos p hp) _
    hsupp).trans ?_
  gcongr
  exact lrr_htUng_mono hpt

/-! ## 3. The entry -/

/-- `ε^{25/22}·(ε^{23/11}S^{23/22})·ε⁻¹ ≤ ε^{-2b}ε^{49/22}` for `S = ε^{-b}`, `0 < ε ≤ 1`, `b ≥ 0`
(source 5332: the common polynomial `P_νS^k`). -/
theorem ltr_eps_const {ε b S : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hb : 0 ≤ b)
    (hS : S = ε ^ (-b)) :
    ε ^ (25 / 22 : ℝ) * (ε ^ (23 / 11 : ℝ) * S ^ (23 / 22 : ℝ)) * ε⁻¹ ≤
      ε ^ (-(((2 : ℕ) : ℝ) * b)) * ε ^ (49 / 22 : ℝ) := by
  subst hS
  rw [← Real.rpow_mul hε.le, ← Real.rpow_neg_one, ← mul_assoc, ← Real.rpow_add hε,
    mul_comm (ε ^ ((25 / 22 : ℝ) + 23 / 11)) _, mul_assoc, ← Real.rpow_add hε]
  have h1 : (25 / 22 : ℝ) + 23 / 11 + -1 = 49 / 22 := by norm_num
  rw [h1]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hε.le _)
  refine Real.rpow_le_rpow_of_exponent_ge hε hε1 ?_
  push_cast
  nlinarith

end LateThinRep

/-- **`FarLateThinRep` from the bridge (A), the kernel and receiver (B) and the source lift**
(source 5303-5311, 5317-5318, 5323-5338, 5134-5139, 2683-2713), with `k₀ = 2`. -/
theorem farLateThinRep_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hA : ThinFarSepBridge Pl σ₀ mZ dm dp) (hY : FarVelYoungBoxL2) (hC : RepRecvConv dm dp)
    (hL : ThinLiftZ1) : FarLateThinRep Pl σ₀ mZ dm dp := by
  refine ⟨2, fun D hPl hσ hmZ hst => ?_⟩
  obtain ⟨Ca, hCa, hY'⟩ := hY
  obtain ⟨Cc, kc, hCc, ec⟩ := hC D hst
  have hκ0 : 0 < 1 - Real.exp (-D.K.δ / 2) := by
    have h := Real.exp_lt_exp.2 (show -D.K.δ / 2 < 0 by linarith [hst.δ_pos])
    rw [Real.exp_zero] at h
    linarith
  have hcκ : 0 ≤ (1 - Real.exp (-D.K.δ / 2)) ^ (-(23 / 11 : ℝ)) := Real.rpow_nonneg hκ0.le _
  have hγ : 0 ≤ gRate D.Pl := hst.gamma_pos.le
  have hmZ0 : 0 ≤ D.K.mZ := by linarith [hst.mZ_gt]
  refine ⟨Cc * Ca * (1 - Real.exp (-D.K.δ / 2)) ^ (-(23 / 11 : ℝ)) * Real.sqrt Real.pi,
    kc + ⌈-D.Pl.kappa.re⌉₊, ?_⟩
  filter_upwards [hA D hPl hσ hmZ hst, ec, multYoung dm dp D hst,
    mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt,
    retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne] with
    n hbr hcn hm hmu hle z hz T
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hν1 : (D.level n).ν ≤ 1 := hle.1
  have hε1 : (D.level n).ε ≤ 1 := hle.2
  have hc : 0 < cOf (D.level n).ν := cOf_pos hν
  have hS : 0 < (D.level n).Scut D.K := Real.rpow_pos_of_pos hε _
  have hμ : -(1 / 4) < D.mu n z := by
    have := (hmu z hz).1
    linarith [hst.sigma_pos]
  -- the far-output bound for box tensors, on the late repair receiver
  set E0 : ℝ := Real.exp (-(4 * gRate D.Pl / 9) / (D.level n).ν) with hE0
  set Bc : ℝ := Cc * (D.level n).ν⁻¹ ^ kc * (D.level n).ε ^ (25 / 22 : ℝ) *
    Real.exp (D.K.m0 / 2 / (D.level n).ν) with hBc
  set By : ℝ := Ca * (1 - Real.exp (-D.K.δ / 2)) ^ (-(23 / 11 : ℝ)) *
    (D.level n).ε ^ (23 / 11 : ℝ) * (D.level n).Scut D.K ^ (23 / 22 : ℝ) with hBy
  have hE00 : 0 ≤ E0 := (Real.exp_pos _).le
  have hBc0 : 0 ≤ Bc := by positivity
  have hBy0 : 0 ≤ By := by positivity
  set Φ : LVel D.Pl (D.level n) →L[ℝ] LStr D.Pl D.K (D.level n) :=
    repPart.comp ((multOp D.Pl D.K (D.level n)).comp
      (ContinuousLinearMap.id ℝ (LVel D.Pl (D.level n)) - youngMul hst.chiY)) with hΦ
  have hΦv : ∀ v : LVel D.Pl (D.level n),
      Φ v = repPart (multOp D.Pl D.K (D.level n) (v - youngMul hst.chiY v)) := fun v => rfl
  have hbox : ∀ (v : LVel D.Pl (D.level n)) (f : Chart → Ten3), NearInst.IsBoxTensor f →
      (v : Chart → Merid) =ᵐ[ageμ (cOf (D.level n).ν) (-3 / 2)]
        NearInst.Masked.farOut (D.level n).ε⁻¹ (cOf (D.level n).ν) (D.level n).ν (D.mu n z)
          D.K.δ ((D.level n).Scut D.K) f →
      ENNReal.ofReal ‖Φ v‖ ≤ ENNReal.ofReal (E0 * Bc * By) *
        phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) 2
          (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) f) := by
    intro v f hf hv
    have c1 := ltr_late_rep D.Pl D.K (D.level n) hst.chiY hγ (fun w => (hm w).2) v
    have c2 := hcn v
    have c3 := hY' (D.level n).ε (cOf (D.level n).ν) (D.level n).ν D.K.δ ((D.level n).Scut D.K)
      (D.mu n z) hε hc hν hst.δ_pos hS hμ f hf (v : Chart → Merid)
      (Lp.stronglyMeasurable v).measurable hv
    rw [hΦv]
    calc ENNReal.ofReal ‖repPart (multOp D.Pl D.K (D.level n) (v - youngMul hst.chiY v))‖
        ≤ ENNReal.ofReal E0 * (ENNReal.ofReal Bc * (ENNReal.ofReal By *
            phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) 2
              (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) f))) :=
          c1.trans (mul_le_mul_of_nonneg_left (c2.trans (mul_le_mul_of_nonneg_left c3 zero_le))
            zero_le)
      _ = _ := by
          rw [ENNReal.ofReal_mul (mul_nonneg hE00 hBc0), ENNReal.ofReal_mul hE00]
          ring
  -- the bridge on the thin source
  have hB := hbr z hz (LStr D.Pl D.K (D.level n)) Φ (E0 * Bc * By) hbox T
  have hlate : Φ (ftFarOp D.Pl D.K (D.level n) (D.mu n z) (thinPart T)) =
      repPart (multOp D.Pl D.K (D.level n)
        (ftLateOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY (thinPart T))) := rfl
  rw [hlate] at hB
  -- the source lift and the source gain
  have hl := hL (D.level n).ε (cOf (D.level n).ν) D.K.mZ hε hc hmZ0 (T.fst : Chart → Ten3)
    (Lp.stronglyMeasurable T.fst).measurable
  have hg := ltr_z1Ung_le_gain (c := cOf (D.level n).ν) (mZ := D.K.mZ) hγ hν T.fst
  have hfst : ‖T.fst‖ ≤ ‖T‖ := by
    rw [WithLp.prod_norm_eq_of_L1 T]
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hX : 0 ≤ Real.sqrt Real.pi * (D.level n).ε⁻¹ := by positivity
  have c4 := hB.trans (mul_le_mul_of_nonneg_left (hl.trans (mul_le_mul_of_nonneg_left hg
    zero_le)) zero_le)
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hX,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at c4
  refine c4.trans ?_
  -- the real bookkeeping
  have hG := ltr_exp_le_gauge D.Pl (D.level n) hν1
  have hK := ltr_eps_const hε hε1 hst.b_pos.le (rfl : (D.level n).Scut D.K = _)
  have hN0 : 0 ≤ gaugeN D.Pl (D.level n) := norm_nonneg _
  have hT0 : 0 ≤ ‖T‖ := norm_nonneg _
  have hνi : 0 ≤ (D.level n).ν⁻¹ := inv_nonneg.2 hν.le
  have hP0 : 0 ≤ Cc * Ca * (1 - Real.exp (-D.K.δ / 2)) ^ (-(23 / 11 : ℝ)) * Real.sqrt Real.pi *
      (D.level n).ν⁻¹ ^ kc * Real.exp (D.K.m0 / 2 / (D.level n).ν) * E0 := by positivity
  calc E0 * Bc * By * (Real.sqrt Real.pi * (D.level n).ε⁻¹ *
        (Real.exp (gRate D.Pl / (D.level n).ν) * ‖T.fst‖))
      = (Cc * Ca * (1 - Real.exp (-D.K.δ / 2)) ^ (-(23 / 11 : ℝ)) * Real.sqrt Real.pi *
          (D.level n).ν⁻¹ ^ kc * Real.exp (D.K.m0 / 2 / (D.level n).ν) * E0) *
          ((D.level n).ε ^ (25 / 22 : ℝ) * ((D.level n).ε ^ (23 / 11 : ℝ) *
            (D.level n).Scut D.K ^ (23 / 22 : ℝ)) * (D.level n).ε⁻¹) *
          (Real.exp (gRate D.Pl / (D.level n).ν) * ‖T.fst‖) := by
        rw [hBc, hBy]; ring
    _ ≤ (Cc * Ca * (1 - Real.exp (-D.K.δ / 2)) ^ (-(23 / 11 : ℝ)) * Real.sqrt Real.pi *
          (D.level n).ν⁻¹ ^ kc * Real.exp (D.K.m0 / 2 / (D.level n).ν) * E0) *
          ((D.level n).ε ^ (-(((2 : ℕ) : ℝ) * D.K.b)) * (D.level n).ε ^ (49 / 22 : ℝ)) *
          (((D.level n).ν⁻¹ ^ (⌈-D.Pl.kappa.re⌉₊) * gaugeN D.Pl (D.level n)) * ‖T‖) := by
        gcongr
    _ = _ := by rw [hE0, pow_add]; ring

/-- **`FarLateThinRep` from the leaves**: the bridge `ThinFarSepBridge` is `thinFarSepBridge_of`
of `StrBoxTrunc` and `SopSubIsFarSeq`. -/
theorem farLateThinRep_of_leaves (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) (h1 : StrBoxTrunc)
    (h3 : SopSubIsFarSeq Pl σ₀ mZ dm dp) (hY : FarVelYoungBoxL2) (hC : RepRecvConv dm dp)
    (hL : ThinLiftZ1) : FarLateThinRep Pl σ₀ mZ dm dp :=
  farLateThinRep_of Pl σ₀ mZ dm dp (thinFarSepBridge_of Pl σ₀ mZ dm dp h1 h3) hY hC hL

end UnforcedLeray.Short.PartIIIb.Concrete
