import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans

/-!
# `PartIII-b:C/rep/4/1/org` (a): the regions of the far mask, the gains and the thin mass

Source `the November 2 reference manuscript` 5301-5372 (`repair:age-error`),
5573-5576 (the mass `N₀(a)`), with the Ward cutoff identity 4171, 4199-4214.

The near operator removes only the far mask `s < S`, `t > e^δ s`, `S = ε^{-b}` (5303-5306), so
`S_far = S_μ - S_N` (`ftFarOp`; `IsNearSplit`, `Inverses/Level.lean` `concreteBase_isNearSplit`,
kernel `IsFarMaskG`).  With the young receiver cutoff `χ_y(s) = χ̂_y(νs)` on velocities
(`youngMul`, `Org/YThinTrans.lean`) and the outward cutoff `χ_o` on stresses (`chiOStr`):

* the late-output part `(1-χ_y)F_far` is `ftLateOp`,
* the early-source part `χ_yF_far(1-χ_o)` is `ftEarlyOp`,
* the young-old rectangle `χ_yF_farχ_o` is `ftYoungOldOp` (5306: "the young-old rectangle is
  contained in this mask"),

and `S_far = (late + early) + young-old` exactly (`ftFarOp_split`, 5306-5309: "its complement is
exactly the late-output part and the early-source part").

**Relation to the split of `Org/YThinTrans.lean`.**  There `ageVel = lateEarlyOp + transOp` with
`lateEarlyOp = S_far - χ_yS_μχ_o` and `transOp = Y + χ_yS_μχ_o` (the two stream transitions,
4210-4214).  Since `S_μ = S_far + S_N`,
`lateEarlyOp = (late + early) - χ_yS_Nχ_o` (`lateEarlyOp_eq`, algebra), and the near operator
vanishes on the young-old rectangle (`NearYoungOldZero`, 5303-5306: the rectangle lies in the far
mask that `S_N` removes).

**The young-old rectangle is not small**: young receiver (`s < 1/ν`, no output gain), old source
(`t > 1.2/ν`, gain up to `e^{γ/ν}`: `N₀(M) ≤ P_νe^{γ/ν}‖g⁻¹M‖_Z`, 4937-4939).  It is cancelled by
`Y` (4203-4214, 5687-5689) and appears in none of the bounds 5317-5372; hence the old leaf
`AgeFarThin` (a bound on all of `S_μ - S_N` on thin sources) is not a source statement.

Also here: the gains on the two regions (5317-5321, proved), the margins (5357-5365, proved), the
receiver split `‖x‖ ≤ ‖x₁‖ + ‖x₂‖` of the split stress norm, and the thin mass `N₀(a)` with its
estimate `ThinMassN0Bound` (5573-5576, a Prop; renamed from `ThinMassBound` by organize
`PartIII-b:C/rep/5/1/regions/org`, which clashed with the Prop of the same name in
`Sub/PartIII-b_C_rep_5_1_2Org.lean`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The regions of the far mask at one regime -/

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- **`S_far = S_μ - S_N`** (source 5303-5306, 3911-3920, 5785): the original far mask
`s < S`, `t > e^δ s`, `S = ε^{-b}`, removed by the near operator (`IsNearSplit`, kernel
`IsFarMaskG`). -/
def ftFarOp : LStr Pl K L →L[ℝ] LVel Pl L := Sop Pl K L μ - SNop Pl K L μ

/-- The outward cutoff `χ_o` on stresses of the regime (source 4163-4166). -/
abbrev ftOld : LStr Pl K L →L[ℝ] LStr Pl K L :=
  chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo

/-- **The late-output part `(1-χ_y)F_far`** (source 5306-5308): output ages `s ≥ 0.8/ν`. -/
def ftLateOp (hχ : IsStreamCutoff K.χy) : LStr Pl K L →L[ℝ] LVel Pl L :=
  (ContinuousLinearMap.id ℝ (LVel Pl L) - youngMul hχ).comp (ftFarOp Pl K L μ)

/-- **The early-source part `χ_yF_far(1-χ_o)`** (source 5308): young output, source ages
`t < 1.5/ν`. -/
def ftEarlyOp (hχ : IsStreamCutoff K.χy) : LStr Pl K L →L[ℝ] LVel Pl L :=
  (youngMul hχ).comp
    ((ftFarOp Pl K L μ).comp (ContinuousLinearMap.id ℝ (LStr Pl K L) - ftOld Pl K L))

/-- **The young-old rectangle `χ_yF_farχ_o`** (source 5306: contained in the far mask).  It is
cancelled by the Ward field `Y` (4203-4214) and carries no small bound by itself. -/
def ftYoungOldOp (hχ : IsStreamCutoff K.χy) : LStr Pl K L →L[ℝ] LVel Pl L :=
  (youngMul hχ).comp ((ftFarOp Pl K L μ).comp (ftOld Pl K L))

/-- The complement of the young-old rectangle in the far mask: late output plus early source
(source 5306-5309). -/
def ftLEOp (hχ : IsStreamCutoff K.χy) : LStr Pl K L →L[ℝ] LVel Pl L :=
  ftLateOp Pl K L μ hχ + ftEarlyOp Pl K L μ hχ

/-- **`S_far = (1-χ_y)F_far + χ_yF_far(1-χ_o) + χ_yF_farχ_o`** (source 5306-5309). -/
theorem ftFarOp_split (hχ : IsStreamCutoff K.χy) :
    ftFarOp Pl K L μ = ftLEOp Pl K L μ hχ + ftYoungOldOp Pl K L μ hχ := by
  ext1 T
  simp only [ftLEOp, ftLateOp, ftEarlyOp, ftYoungOldOp, add_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, sub_apply,
    ContinuousLinearMap.id_apply, map_sub]
  abel

/-- The far mask on thin sources (the operator of the old leaf `AgeFarThin`):
`(S_μ - S_N)(T₁,0) = late + early + young-old`. -/
theorem ftFarOp_thin_split (hχ : IsStreamCutoff K.χy) (T : LStr Pl K L) :
    (Sop Pl K L μ - SNop Pl K L μ) (thinPart T) =
      ftLateOp Pl K L μ hχ (thinPart T) + ftEarlyOp Pl K L μ hχ (thinPart T) +
        ftYoungOldOp Pl K L μ hχ (thinPart T) := by
  have h := congrArg (fun F : LStr Pl K L →L[ℝ] LVel Pl L => F (thinPart T))
    (ftFarOp_split Pl K L μ hχ)
  simpa only [ftFarOp, ftLEOp, add_apply] using h

/-- **`lateEarlyOp = (late + early) - χ_yS_Nχ_o`** (algebra; `lateEarlyOp = S_far - χ_yS_μχ_o` of
`Org/YThinTrans.lean`, `S_μ = S_far + S_N`). -/
theorem lateEarlyOp_eq (hχ : IsStreamCutoff K.χy) (x : LStr Pl K L) :
    lateEarlyOp Pl K L μ hχ x =
      ftLEOp Pl K L μ hχ x - youngMul hχ (SNop Pl K L μ (ftOld Pl K L x)) := by
  simp only [lateEarlyOp, youngOldOp, ftLEOp, ftLateOp, ftEarlyOp, ftFarOp, add_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, sub_apply,
    ContinuousLinearMap.id_apply, map_sub]
  abel

end Regime

/-! ## 2. The near operator on the young-old rectangle -/

/-- **`χ_yS_Nχ_o = 0`** (source 5303-5306: "Let the near operator remove only the original far
mask `s<S`, `t>e^δ s` ... The young-old rectangle is contained in this mask"; 3902-3920,
`S_N = S_μ - 1_{s<S,t>e^δs}S_μ`).  `χ_y = 0` for `s ≥ 1/ν`, `χ_o = 0` for `t ≤ 1.2/ν` (4163-4166),
`e^δ < 12/11` (`RepairStanding.δ_lt`) and `S = ε^{-b} > 1/ν` for large `n`, so the young-old
rectangle lies inside the far mask removed by `S_N`: for large `n`, every `z ∈ [-1,1]` and every
stress `x`, `χ_yS_N(χ_ox) = 0`. -/
def NearYoungOldZero (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, ∀ hst : D.RepairStanding dm dp, ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ x : LStr D.Pl D.K (D.level n),
      youngMul hst.chiY (SNop D.Pl D.K (D.level n) (D.mu n z) (ftOld D.Pl D.K (D.level n) x)) = 0

/-! ## 3. The receiver split of the split stress norm -/

/-- `‖T‖_Z ≤ ‖(T₁,0)‖_Z + ‖(0,T₂)‖_Z`: the thin and the scaled repair receivers (source
5323-5331, the two columns of the table). -/
theorem ft_norm_le_thin_add_rep {c mZ ρb γ ν : ℝ} (x : StrG c mZ ρb γ ν) :
    ‖x‖ ≤ ‖thinPart x‖ + ‖repPart x‖ := by
  conv_lhs => rw [← thinPart_add_repPart x]
  exact norm_add_le _ _

/-! ## 4. The gains on the two regions (source 5317-5321) -/

/-- **Late output**: `g(s)^{-1} ≤ e^{-4γ/(9ν)}` for `s ≥ 0.8/ν` (source 5317-5318;
`g(s) = e^{γs/(1+νs)}`, 3881, 5117). -/
theorem ftGain_late {γ ν s : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (hs : 4 / 5 / ν ≤ s) :
    (UnforcedLeray.Short.IIIa.gainG γ ν s)⁻¹ ≤ Real.exp (-(4 * γ / 9) / ν) := by
  unfold UnforcedLeray.Short.IIIa.gainG
  have hνs : 4 / 5 ≤ s * ν := (div_le_iff₀ hν).1 hs
  have hs0 : 0 < s := by
    have : 0 < s * ν := by linarith
    exact pos_of_mul_pos_left this hν.le
  have h1 : 0 < 1 + ν * s := by positivity
  rw [← Real.exp_neg, Real.exp_le_exp, neg_div, neg_le_neg_iff, div_le_div_iff₀ hν h1]
  nlinarith [mul_nonneg hγ (sub_nonneg.2 hνs)]

/-- **Early source**: `g(t) ≤ e^{3γ/(5ν)}` for `0 ≤ t ≤ 1.5/ν` (source 5318-5319). -/
theorem ftGain_early {γ ν t : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (ht0 : 0 ≤ t) (ht : t ≤ 3 / 2 / ν) :
    UnforcedLeray.Short.IIIa.gainG γ ν t ≤ Real.exp (3 * γ / 5 / ν) := by
  unfold UnforcedLeray.Short.IIIa.gainG
  have htν : t * ν ≤ 3 / 2 := (le_div_iff₀ hν).1 ht
  have h1 : 0 < 1 + ν * t := by positivity
  rw [Real.exp_le_exp, div_le_div_iff₀ h1 hν]
  nlinarith [mul_nonneg hγ (sub_nonneg.2 htν)]

/-! ## 5. The margins (source 5357-5365, `d₀ = γ/3`) -/

/-- Thin-to-thin, late output: `2d₀ - γ + 4γ/9 = γ/9`. -/
theorem ftMargin_tt_late (γ : ℝ) : 2 * (γ / 3) - γ + 4 * γ / 9 = γ / 9 := by ring

/-- Thin-to-thin, early source: `2d₀ - 3γ/5 = γ/15`. -/
theorem ftMargin_tt_early (γ : ℝ) : 2 * (γ / 3) - 3 * γ / 5 = γ / 15 := by ring

/-- Thin-to-repair, late output: `(49/22)d₀ - γ + 4γ/9 = 37γ/198` (before the `m₀/2` loss). -/
theorem ftMargin_tr_late (γ : ℝ) : 49 / 22 * (γ / 3) - γ + 4 * γ / 9 = 37 * γ / 198 := by ring

/-- Thin-to-repair, early source: `(49/22)d₀ - 3γ/5 = 47γ/330` (before the `m₀/2` loss). -/
theorem ftMargin_tr_early (γ : ℝ) : 49 / 22 * (γ / 3) - 3 * γ / 5 = 47 * γ / 330 := by ring

/-! ## 6. The thin mass `N₀(a)` (source 5573-5576) -/

/-- **`N₀(a) = ∫_a^∞ t^{-3/2} ∫ ‖T(t,·,η)‖_{L²_q} dη dt`** (source 5573-5576): the old physical
mass of an unweighted thin stress divided by `πR²`, with `L²(dq/c)` on the cell (the convention of
`IIIa.firstMoment`, which is `N₀` with the transverse weight `1 + |η|/√t`). -/
def thinMassN0 (c a : ℝ) (T : Chart → Matrix (Fin 3) (Fin 3) ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi a, ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) *
    ∫⁻ η : ℝ, (∫⁻ q in Ico (-(c / 2)) (c / 2),
      ENNReal.ofReal c⁻¹ * ENNReal.ofReal (UnforcedLeray.Short.IIIa.frobSq (T (t, (q, η))))) ^
        (1 / 2 : ℝ)

/-- **The mass estimate** (source 5573-5579): for `m_Z > 3/2` there is `C` with
`N₀(a) ≤ C(a^{-3/4} + a^{-1/2})‖T‖_{Z_1}` for all `c > 0`, `a > 0` and measurable `T`
("transverse Cauchy-Schwarz contributes `(1+t)^{1/4}`, and the remaining squared age integral is
`∫_a^∞ t^{-5/2}(1+t)^{1/2}dt`").  This is the estimate `ThinMassBoundSlice` of
`Sub/PartIII-b_C_rep_5_1_1Org.lean` (proved: `thinMassBoundSlice`,
`Sub/PartIII-b_C_rep_5_1_1/ThinMass.lean`) written with `frobSq` and componentwise measurability;
`Sub/PartIII-b_C_rep_5_1_2Org.lean` has its `L¹` form `ThinMassBound`. -/
def ThinMassN0Bound : Prop :=
  ∀ mZ : ℝ, 3 / 2 < mZ → ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 < c → ∀ a : ℝ, 0 < a →
    ∀ T : Chart → Matrix (Fin 3) (Fin 3) ℝ, (∀ i j, Measurable fun p => T p i j) →
      thinMassN0 c a T ≤ ENNReal.ofReal (C * (a ^ (-3 / 4 : ℝ) + a ^ (-1 / 2 : ℝ))) *
        UnforcedLeray.Short.IIIa.z1NormSq c mZ T ^ (1 / 2 : ℝ)

end UnforcedLeray.Short.PartIIIb.Concrete
