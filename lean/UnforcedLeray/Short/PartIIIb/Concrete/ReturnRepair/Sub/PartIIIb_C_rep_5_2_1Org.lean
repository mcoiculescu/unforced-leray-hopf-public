import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThinParts
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Seq
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_dec
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.RepairSource
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16

/-!
# `PartIII-b:C/rep/5/2/1/org`: the far part of the repair-source velocity

Source `the November 2 reference manuscript` 5301-5319 (the age rectangles),
3631-3664 (`sep:young`, `sep:repair-energy`, the repair product), 5169-5176 (`repair:source`),
5585-5605 (the far velocity, Young `L^{22/19} → L²` for the repair source), 5614-5619.

## The split of `ageVel = S_far + Y`

The near operator removes the original far mask `s < S, t > e^δ s` (5303-5306).  The young-old
rectangle (young output `χ_y`, old source `χ_o`) lies inside this mask; its complement in the mask
is the late-output part `(1-χ_y)F_far` and the early-source part `χ_yF_far(1-χ_o)` (5306-5310).
On the rectangle `χ_yS_μχ_oT = -χ_yW_μ`, and the stream transition
`Y = 𝒞_χW_μ + [D_{μ+1}, 𝒞_χ](W_μ - W_{μ+1})` cancels it: `Y + χ_yS_μχ_o` is the sum of the two
stream-cutoff differences, supported on `0.8/ν < s < 1/ν` (5310-5316).  The source bounds only
these pieces (5317-5319, 5594-5605); neither `S_far` nor `Y` alone has the gain-weighted bound
(the rectangle carries the gain ratio up to `e^{γ/ν}`, against `ρε^{23/11} ≍ e^{-26γ/(33ν)}`).
Hence the leaves `AgeVelSopRep`/`AgeVelWardRep` of `Sub/PartIII-b_C_rep_5_2Org.lean` are not
source statements.  The split used here is the one of `Sub/PartIII-b_C_rep_4/Org`
(`ageVel_split`, `lateEarlyOp_eq`, `NearYoungOldZero`):

`ageVel = ftLEOp - χ_yS_Nχ_o + transOp`, `ftLEOp = (1-χ_y)F_far + χ_yF_far(1-χ_o)`,

and `ageVelRep_of_regions` (proved) gives `AgeVelRep` from `AgeVelFarRep` (bound on `ftLEOp`),
`AgeVelTransRep` (bound on `transOp`) and `NearYoungOldZero`.

## The far part on the repair source (`AgeVelFarRep`)

For `T₂ = (0, M_{r_b}w)`, `ftLEOp T₂ = (1-χ_y)S_far(χ_oT₂) + S_far((1-χ_o)T₂)` (`ftLEOp_old_early`):

1. `SeqNearSplit` (`ReturnInst/Inverses/Seq.lean`): `S_μ - S_N = S_far` with `IsFarMaskG`.
2. `RepFarBox`, `RepFarExt` (3631-3664, 5585-5603): the unweighted far bound
   `R⁻¹‖S_far T‖_{Y_2} ≤ C ε^{34/11} S^{23/22}‖T‖_{L²_τL^{22/19}}` (`RepFarAt`).  For the repair
   class one radial gap suffices: an output of age `s < S` sees only sources of age `t > e^δ s`, so
   the gap is `≥ (1-e^{-δ/2})R/√s ≥ (1-e^{-δ/2})R/√S`, and the order-four kernel in `L^{11/7}`
   outside it has norm `C D^{-23/11} = C_δ ε^{23/11} S^{23/22}` (`sep:repair-energy`; the bins of
   5585-5593 are needed only for the thin mass `N₀(a)`; summing them gives the same power of `S`).
   `RepFarBox` is the bound on the dense class `IsBoxTensor` (leaves `FarDomChart`,
   `ChartPhysL2`, `SepDomFacts`, `IIIa.SepDomYoung`), `RepFarExt` its extension to all stresses.
3. `YoungCutLate`, `VelGLeSrc` (5317-5319): `g⁻¹ ≤ e^{-4γ/(9ν)}` on late output, `g⁻¹ ≤ 1`.
4. `repairSource` (proved, 5169-5176) for the old source `χ_oT₂`; `RepSrcEarly` (5171-5176 with
   `g(t) ≤ e^{3γ/(5ν)}` on early source, 5318-5319) for `(1-χ_o)T₂`, from `RepPhasePointwiseEarly`,
   `VelPhysL2Early`; `RepSplitAE` identifies the two source representatives.
5. `RepMargin` (5601-5605): `ρε^{23/11}` with late gain `e^{-4γ/(9ν)}|N_ν|` and early gain
   `e^{3γ/(5ν)}`: margins `23γ/99 ≥ 31γ/165` and `31γ/165`, before the `m₀` loss; `S^{23/22}`
   costs `e^{ω_b/ν}`, `ω_b = 2bγ/3` (`k₀ = 2`, fixed before `b`).

`farRep_level` and `ageVelFarRep_of` (proved) assemble `AgeVelFarRep` from these.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The split (reused from `Sub/PartIII-b_C_rep_4/Org`)

`Org/YThinTrans.lean`: `youngMul` (`χ_y` on velocities), `youngOldOp = χ_yS_μχ_o`,
`transOp = Y + χ_yS_μχ_o` (the two stream transitions), `lateEarlyOp = S_far - χ_yS_μχ_o`,
`ageVel_split : ageVel = lateEarlyOp + transOp`.  `Org/FarThinParts.lean`: `ftFarOp = S_μ - S_N`,
`ftOld = χ_o`, `ftLEOp = (1-χ_y)F_far + χ_yF_far(1-χ_o)`, `lateEarlyOp_eq : lateEarlyOp =
ftLEOp - χ_yS_Nχ_o`, `NearYoungOldZero` (`χ_yS_Nχ_o = 0` for large `n`, 5303-5306). -/

/-- `ftLEOp T = (S_far(χ_oT) - χ_yS_far(χ_oT)) + S_far(T - χ_oT)`: the old source read at late
output plus the early source read anywhere (5306-5310). -/
theorem ftLEOp_old_early (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hχ : IsStreamCutoff K.χy) (T : LStr Pl K L) :
    ftLEOp Pl K L μ hχ T =
      (ftFarOp Pl K L μ (ftOld Pl K L T) - youngMul hχ (ftFarOp Pl K L μ (ftOld Pl K L T))) +
        ftFarOp Pl K L μ (T - ftOld Pl K L T) := by
  simp only [ftLEOp, ftLateOp, ftEarlyOp, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_sub]
  abel

/-! ## 2. The two region leaves and `AgeVelRep` -/

namespace SeqData

/-- Far part (late output and early source) of the repair velocity (5306-5310, 5601-5605). -/
def AgeVelFarRepAt (D : SeqData) (hχ : IsStreamCutoff D.K.χy) (ωb : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ w : LVel D.Pl (D.level n),
      ‖ftLEOp D.Pl D.K (D.level n) (D.mu n z) hχ (repPart (multOp D.Pl D.K (D.level n) w))‖ ≤
        C * (D.level n).ν⁻¹ ^ k *
          Real.exp (-(31 * gRate D.Pl / 165 - ωb - 3 * D.K.m0 / 2) / (D.level n).ν) * ‖w‖

/-- The two stream transitions `Y + χ_yS_μχ_o` on the repair source (5310-5316, 5590-5592,
5601-5605; supported at late output, margin `23γ/99 ≥ 31γ/165`). -/
def AgeVelTransRepAt (D : SeqData) (hχ : IsStreamCutoff D.K.χy) (ωb : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ w : LVel D.Pl (D.level n),
      ‖transOp D.Pl D.K (D.level n) (D.mu n z) hχ (repPart (multOp D.Pl D.K (D.level n) w))‖ ≤
        C * (D.level n).ν⁻¹ ^ k *
          Real.exp (-(31 * gRate D.Pl / 165 - ωb - 3 * D.K.m0 / 2) / (D.level n).ν) * ‖w‖

end SeqData

/-- Region leaf (far part), `k₀` chosen before `b`. -/
def AgeVelFarRep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ hst : D.RepairStanding dm dp, D.AgeVelFarRepAt hst.chiY ((k₀ : ℝ) * D.K.b * (gRate D.Pl / 3))

/-- Region leaf (stream transitions), `k₀` chosen before `b`. -/
def AgeVelTransRep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ hst : D.RepairStanding dm dp,
      D.AgeVelTransRepAt hst.chiY ((k₀ : ℝ) * D.K.b * (gRate D.Pl / 3))

/-- `ageVel = ftLEOp - χ_yS_Nχ_o + transOp` and `χ_yS_Nχ_o = 0`, so the two region leaves give
`AgeVelRep`. -/
theorem ageVelRep_of_regions (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (h1 : AgeVelFarRep Pl σ₀ mZ dm dp) (h2 : AgeVelTransRep Pl σ₀ mZ dm dp)
    (h0 : NearYoungOldZero dm dp) : AgeVelRep Pl σ₀ mZ dm dp := by
  obtain ⟨k1, H1⟩ := h1
  obtain ⟨k2, H2⟩ := h2
  refine ⟨max k1 k2, fun D hPl hσ hmZ hst => ?_⟩
  have hb := hst.b_pos
  have hg := hst.gamma_pos
  have hmono : ∀ j : ℕ, j ≤ max k1 k2 →
      (j : ℝ) * D.K.b * (gRate D.Pl / 3) ≤ ((max k1 k2 : ℕ) : ℝ) * D.K.b * (gRate D.Pl / 3) := by
    intro j hj
    have : (j : ℝ) ≤ ((max k1 k2 : ℕ) : ℝ) := by exact_mod_cast hj
    have hbg : 0 ≤ D.K.b * (gRate D.Pl / 3) := by positivity
    nlinarith
  obtain ⟨C1, j1, e1⟩ := H1 D hPl hσ hmZ hst
  obtain ⟨C2, j2, e2⟩ := H2 D hPl hσ hmZ hst
  have hν1 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds one_pos)
  set ω := ((max k1 k2 : ℕ) : ℝ) * D.K.b * (gRate D.Pl / 3) with hω
  have m1 := hmono k1 (le_max_left _ _)
  have m2 := hmono k2 (le_max_right _ _)
  refine ⟨|C1| + |C2|, max j1 j2, ?_⟩
  filter_upwards [e1, e2, hν1, h0 D hst] with n a1 a2 hν hz0 z hz w
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν1' : (D.level n).ν ≤ 1 := hν
  have hi : 1 ≤ (D.level n).ν⁻¹ := (one_le_inv₀ hνp).2 hν1'
  have hP : ∀ j : ℕ, 0 ≤ (D.level n).ν⁻¹ ^ j := fun j => by positivity
  have pj1 : (D.level n).ν⁻¹ ^ j1 ≤ (D.level n).ν⁻¹ ^ (max j1 j2) :=
    pow_le_pow_right₀ hi (le_max_left _ _)
  have pj2 : (D.level n).ν⁻¹ ^ j2 ≤ (D.level n).ν⁻¹ ^ (max j1 j2) :=
    pow_le_pow_right₀ hi (le_max_right _ _)
  have ex1 : Real.exp (-(31 * gRate D.Pl / 165 - (k1 : ℝ) * D.K.b * (gRate D.Pl / 3) -
        3 * D.K.m0 / 2) / (D.level n).ν) ≤
        Real.exp (-(31 * gRate D.Pl / 165 - ω - 3 * D.K.m0 / 2) / (D.level n).ν) := by
    refine Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ hνp.le)
    linarith
  have ex2 : Real.exp (-(31 * gRate D.Pl / 165 - (k2 : ℝ) * D.K.b * (gRate D.Pl / 3) -
        3 * D.K.m0 / 2) / (D.level n).ν) ≤
        Real.exp (-(31 * gRate D.Pl / 165 - ω - 3 * D.K.m0 / 2) / (D.level n).ν) := by
    refine Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ hνp.le)
    linarith
  have b1 := lift (a1 z hz w) (le_refl |C1|)
    (hP j1) pj1 (Real.exp_pos _).le ex1 (norm_nonneg w)
  have b2 := lift (a2 z hz w) (le_refl |C2|)
    (hP j2) pj2 (Real.exp_pos _).le ex2 (norm_nonneg w)
  rw [ageVel_split D.Pl D.K (D.level n) (D.mu n z) hst.chiY, ContinuousLinearMap.add_apply,
    lateEarlyOp_eq, hz0 z hz, sub_zero]
  refine (norm_add_le _ _).trans ?_
  linarith [b1, b2]

/-! ## 3. The unweighted far bound for the repair class -/

/-- **The far bound on the dense class** (3611-3664, `sep:resolvent`, `sep:young`,
`sep:repair-energy` with `p = 22/19`, `q = 2`, kernel exponent `11/7`; 3905-3912; 5585-5603): every
`S_far` with the kernel realization `IsFarMaskG` (gap `δ`, output cut `S = ε^{-b}`) satisfies, for
a stress whose sum has a box representative `f`,
`R⁻¹‖S_far F‖_{Y_2} ≤ C ε^{34/11} S^{23/22}‖𝒩_T f‖_{L²_τL^{22/19}}` (`ε^{34/11}S^{23/22} = R⁻¹ D^{-23/11}`
up to `(1-e^{-δ/2})^{23/11}`, `D = (1-e^{-δ/2})R/√S`). -/
def RepFarBoxAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ C : ℝ) : Prop :=
  ∀ Sf : LStr Pl K L →L[ℝ] LVel Pl L, IsFarMaskG L.ε⁻¹ μ K.δ (L.Scut K) Sf →
    ∀ (F : LStr Pl K L) (f : Chart → Ten3), NearInst.IsBoxTensor f →
      strSum F =ᵐ[ageμ (cOf L.ν) (-1 / 2)] f →
      eLpNorm (Sf F : Chart → Merid) 2 (srcMeasure (cOf L.ν)) ≤
        ENNReal.ofReal (C * L.ε ^ (34 / 11 : ℝ) * L.Scut K ^ (23 / 22 : ℝ)) *
          phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (strPhys L.ε⁻¹ (cOf L.ν) f)

/-- **The far bound on all stresses** (same lines), for any measurable representative `f` of
`T₁ + T₂`. -/
def RepFarAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ C : ℝ) : Prop :=
  ∀ Sf : LStr Pl K L →L[ℝ] LVel Pl L, IsFarMaskG L.ε⁻¹ μ K.δ (L.Scut K) Sf →
    ∀ (F : LStr Pl K L) (f : Chart → Ten3), Measurable f →
      strSum F =ᵐ[ageμ (cOf L.ν) (-1 / 2)] f →
      eLpNorm (Sf F : Chart → Merid) 2 (srcMeasure (cOf L.ν)) ≤
        ENNReal.ofReal (C * L.ε ^ (34 / 11 : ℝ) * L.Scut K ^ (23 / 22 : ℝ)) *
          phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (strPhys L.ε⁻¹ (cOf L.ν) f)

/-- Leaf: the box bound with a constant depending only on the gap `δ`, uniform in `μ > -1/4`. -/
def RepFarBox : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ),
    K.δ = δ → -(1 / 4) < μ → RepFarBoxAt Pl K L μ C

/-- Leaf: extension from box tensors to all stresses (truncation `1_{A_n}`, `A_n` a box intersected
with `{‖f‖ ≤ n}`, continuity of `S_far`, an a.e. subsequence and Fatou; `C₀ > 0` makes the gain
measures equivalent to `ageμ c (-1/2)`). -/
def RepFarExt : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ C : ℝ), 0 < K.C0 →
    RepFarBoxAt Pl K L μ C → RepFarAt Pl K L μ C

/-- **Domination at chart points** (3604-3623: `sep:kernel`, `sep:resolvent`, the radial gap
`|y - λz| ≥ |y'| - λ|z'|`; 3905-3912: the mask `t > e^δ s`): at a chart point of age `0 < s < S`
the masked response is dominated by the order-zero gap majorant of the full source, with the gap
`(1-e^{-δ/2})R/√S` (receiver radius `R/√s`, masked sources inside radius `Re^{-δ/2}/√s`).  From
`IIIa.SepWDominated` (proved, `Tasks16/Dominated.lean`), `IIIa.SepKernelBounds` (proved) and
monotonicity of `IIIa.sepDom` in the gap and the source. -/
def FarDomChart : Prop :=
  ∃ C0 : ℝ, 0 < C0 ∧ ∀ ν : ℝ, 0 < ν → ∀ μ : ℝ, -(1 / 4) < μ → ∀ R c δ S : ℝ, 0 < R → 0 < c →
    0 < δ → 0 < S → ∀ f : Chart → Ten3, NearInst.IsBoxTensor f → ∀ p : Chart, 0 < p.1 → p.1 < S →
      ‖NearInst.merRe (-NearInst.sepWfar ν (μ : ℂ) R δ p.1 (NearInst.cartLift R c f)
          (NearInst.chartY R p) (NearInst.chartTau R p))‖ₑ ≤
        ENNReal.ofReal C0 * UnforcedLeray.Short.IIIa.sepDom (2 * μ + 2) 0
          ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt S)
          (UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c f))
          (NearInst.chartTau R p) (NearInst.chartY R p)

/-- **Chart-physical change of variables** (2683-2689: `R⁻¹‖𝒩_v b‖_{Y_2} = √π‖b‖_H`): for a
measurable, `2c/R`-periodic, axisymmetric `G ≥ 0` on `ℝ × ℝ³`,
`∫ s^{-1}G(τ(p), y(p))² d(π s^{-3/2}dς) ≤ R^{-2}‖G‖²_{L²_τL²_y}` (`y = (R/√s, 0, η/√s)`,
`τ = 2q/R + log s`, `2πr dr dz = πR²s^{-5/2}ds dη`, `c⁻¹dq = dτ/P`, `P = 2c/R`). -/
def ChartPhysL2 : Prop :=
  ∀ R c : ℝ, 0 < R → 0 < c → ∀ G : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry G) →
    (∀ τ y, G (τ + 2 * c / R) y = G τ y) →
    (∀ τ (y y' : Space), y' 2 = y 2 → y' 0 ^ 2 + y' 1 ^ 2 = y 0 ^ 2 + y 1 ^ 2 → G τ y' = G τ y) →
    ∫⁻ p, ENNReal.ofReal p.1⁻¹ * G (NearInst.chartTau R p) (NearInst.chartY R p) ^ (2 : ℝ)
        ∂srcMeasure c ≤
      ENNReal.ofReal (R⁻¹ ^ 2) * UnforcedLeray.Short.IIIa.ltauLq (2 * c / R) 2 G ^ (2 : ℝ)

/-- **The gap majorant of a lifted box tensor** (2683, 3611-3617): `sepDom a j D (srcNorm 𝒩_T f)`
is jointly measurable, `2c/R`-periodic in `τ` and axisymmetric in `y` (the lift `cartLift` is
equivariant under rotations about the axis, the Frobenius norm is invariant, and the kernel majorant
`1_{|x|≥D}|x|^{-4-j}` is radial); and the source norm is measurable and `2c/R`-periodic. -/
def SepDomFacts : Prop :=
  ∀ (a : ℝ) (j : ℕ) (D R c : ℝ), 0 < R → 0 < c → ∀ f : Chart → Ten3, Measurable f →
    Measurable (Function.uncurry
        (UnforcedLeray.Short.IIIa.sepDom a j D (UnforcedLeray.Short.IIIa.srcNorm
          (NearInst.cartLift R c f)))) ∧
      Measurable (Function.uncurry
        (UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c f))) ∧
      (∀ τ z, UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c f) (τ + 2 * c / R) z =
        UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c f) τ z) ∧
      (∀ τ y, UnforcedLeray.Short.IIIa.sepDom a j D (UnforcedLeray.Short.IIIa.srcNorm
          (NearInst.cartLift R c f)) (τ + 2 * c / R) y =
        UnforcedLeray.Short.IIIa.sepDom a j D (UnforcedLeray.Short.IIIa.srcNorm
          (NearInst.cartLift R c f)) τ y) ∧
      (∀ τ (y y' : Space), y' 2 = y 2 → y' 0 ^ 2 + y' 1 ^ 2 = y 0 ^ 2 + y 1 ^ 2 →
        UnforcedLeray.Short.IIIa.sepDom a j D (UnforcedLeray.Short.IIIa.srcNorm
            (NearInst.cartLift R c f)) τ y' =
          UnforcedLeray.Short.IIIa.sepDom a j D (UnforcedLeray.Short.IIIa.srcNorm
            (NearInst.cartLift R c f)) τ y)

/-- The sequence form of the far bound, from `RepFarBox`, `RepFarExt` and `μ_n(z) → σ₀ > 0`. -/
theorem repFarSeq_of (hB : RepFarBox) (hE : RepFarExt) (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      RepFarAt D.Pl D.K (D.level n) (D.mu n z) C := by
  obtain ⟨C, hC⟩ := hB D.K.δ hst.δ_pos
  refine ⟨C, ?_⟩
  filter_upwards [mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt] with n hn z hz
  have hμ : -(1 / 4) < D.mu n z := by
    have := (hn z hz).1
    have := hst.sigma_pos
    linarith
  exact hE _ _ _ _ _ hst.C0_pos (hC _ _ _ _ rfl hμ)

/-! ## 4. Gains on the output side -/

/-- **Late output** (5317-5318): on the support of `1 - χ_y(νs)` the age is `≥ 0.8/ν`, so
`g⁻¹ ≤ e^{-4γ/(9ν)}`; hence the gain norm of `(1-χ_y)v` is at most `e^{-4γ/(9ν)}` times the
ungained normalized norm `R⁻¹‖𝒩_v v‖_{Y_2}`. -/
def YoungCutLate : Prop :=
  ∀ {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ) (c γ ν : ℝ), 0 ≤ γ → 0 < ν → ∀ v : VelG c γ ν,
    ENNReal.ofReal ‖v - youngMul hχ v‖ ≤
      ENNReal.ofReal (Real.exp (-(4 * γ / 9) / ν)) * eLpNorm (v : Chart → Merid) 2 (srcMeasure c)

/-- **`g⁻¹ ≤ 1`** (5117, 5143): the gain norm is at most the ungained normalized norm. -/
def VelGLeSrc : Prop :=
  ∀ c γ ν : ℝ, 0 ≤ γ → 0 < ν → ∀ v : VelG c γ ν,
    ENNReal.ofReal ‖v‖ ≤ eLpNorm (v : Chart → Merid) 2 (srcMeasure c)

/-! ## 5. The two repair sources -/

/-- The early repair source `(1-χ_o)M_{r_b}w` as a chart tensor (5306-5310, 5318-5319). -/
def earlyRepTen (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (w : LVel Pl L) :
    Chart → Ten3 :=
  fun p => (1 - K.χo (L.ν * p.1)) • ((multOp Pl K L w).snd : Chart → Ten3) p

/-- The early velocity `(1-χ_o(νs))w` on the chart. -/
def earlyVel (K : ReturnConsts) (L : ReturnLevel) (w : Chart → Merid) : Chart → Merid :=
  fun p => (1 - K.χo (L.ν * p.1)) • w p

/-- **The two source representatives** (5153-5157, 5377-5379): for `T₂ = (0, M_{r_b}w)`,
`T₁+T₂` of `χ_oT₂` is `χ_o M_{r_b}w` (`repSrcTen`) and that of `T₂ - χ_oT₂` is `earlyRepTen`, a.e.
for `ageμ c (-1/2)` (`C₀ > 0`: the gain measures have the null sets of `ageμ c (-1/2)`). -/
def RepSplitAE : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel), 0 < K.C0 → ∀ w : LVel Pl L,
    strSum (ftOld Pl K L (repPart (multOp Pl K L w)))
        =ᵐ[ageμ (cOf L.ν) (-1 / 2)] repSrcTen Pl K L w ∧
      strSum (repPart (multOp Pl K L w) - ftOld Pl K L (repPart (multOp Pl K L w)))
        =ᵐ[ageμ (cOf L.ν) (-1 / 2)] earlyRepTen Pl K L w

/-- **The early repair source** (5169-5176 with 5318-5319): `‖(1-χ_o)(r_b⊗w+w⊗r_b)‖_{L²_τL^{22/19}}
≤ P_ν ρ R e^{3γ/(5ν)} G(w)` (Hölder `19/22 = 4/11 + 1/2`; `g(t) ≤ e^{3γ/(5ν)}` where `χ_o(νt) < 1`). -/
def RepSrcEarlyAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (C : ℝ) (k : ℕ) :
    Prop :=
  ∀ w : LVel Pl L,
    phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (strPhys L.ε⁻¹ (cOf L.ν) (earlyRepTen Pl K L w)) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * rhoRep K L * L.ε⁻¹ *
        Real.exp (3 * gRate Pl / 5 / L.ν) * ‖w‖)

/-- Sequence form of `RepSrcEarlyAt`. -/
def SeqData.RepSrcEarly (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, RepSrcEarlyAt D.Pl D.K (D.level n) C k

/-- **Pointwise early repair stress** (4147, 5169-5171; as `RepPhasePointwise` with the cut
`1-χ_o` moved to the velocity): `|𝒩_T((1-χ_o)M_{r_b}w)| ≤ 2|r_b||𝒩_v((1-χ_o)w)|` a.e. -/
def RepPhasePointwiseEarly : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ), 0 < K.C0 → NearAt Pl K L μ →
    (∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsSplitMult M (L.params Pl).R L.V L.rb) →
    (∀ τ, AxiNoSwirlPt (L.rb τ)) →
    (∀ τ y, L.rb (τ + 2 * cOf L.ν / L.ε⁻¹) y = L.rb τ y) →
    ∀ w : LVel Pl L, ∀ᵐ τ ∂(volume.restrict (Ioc 0 (2 * L.ε * cOf L.ν))), ∀ᵐ y : Space,
      UnforcedLeray.Short.IIIa.tensorNorm
          (strPhys L.ε⁻¹ (cOf L.ν) (earlyRepTen Pl K L w) (τ, y)) ≤
        2 * ‖L.rb τ y‖ * ‖velPhys L.ε⁻¹ (cOf L.ν) (earlyVel K L (w : Chart → Merid)) (τ, y)‖

/-- **Early velocity in `Y_2`** (2683-2689, 5318-5319: `1 - χ_o(νs) = 0` for `νs ≥ 3/2`, where
`g(s) ≤ e^{3γ/(5ν)}` since `s/(1+νs) ≤ 3/(5ν)`): the phase-normalized `L²` norm of
`𝒩_v((1-χ_o)w)` is at most `C₁ R e^{3γ/(5ν)}‖w‖`. -/
def VelPhysL2Early : Prop :=
  ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ (Pl : PlanarData), 0 ≤ gRate Pl → ∀ (K : ReturnConsts) (L : ReturnLevel)
    (w : LVel Pl L),
    ENNReal.ofReal (2 * L.ε * cOf L.ν)⁻¹ *
      ∫⁻ t in Ioc (0 : ℝ) (2 * L.ε * cOf L.ν), ∫⁻ y : Space,
        ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) (earlyVel K L (w : Chart → Merid)) (t, y)‖ ^ 2 ≤
      ENNReal.ofReal ((C1 * L.ε⁻¹ * Real.exp (3 * gRate Pl / 5 / L.ν) * ‖w‖) ^ 2)

/-! ## 6. The margins -/

/-- **The repair margins** (5601-5605): with `ε = C_*ν^r e^{-γ/(3ν)}` (`retEps_eq_form`),
`ρ = ε^{3/11}e^{m₀/ν}`, `S = ε^{-b}`, `|N_ν| = e^{γ/ν}ν^{-Re κ}`:
late output `ε^{34/11}S^{23/22}ρε⁻¹e^{-4γ/(9ν)}|N_ν|` (margin `26γ/33 + 4γ/9 - γ = 23γ/99`) and
early source `ε^{34/11}S^{23/22}ρε⁻¹e^{3γ/(5ν)}` (margin `26γ/33 - 3γ/5 = 31γ/165`) are both
`≤ C ν^{-k} e^{-(31γ/165 - ω_b - 3m₀/2)/ν}`, `ω_b = 2bγ/3 ≥ (23/22)bγ/3`. -/
def RepMarginAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (ωb C : ℝ) (k : ℕ) :
    Prop :=
  L.ε ^ (34 / 11 : ℝ) * L.Scut K ^ (23 / 22 : ℝ) * rhoRep K L * L.ε⁻¹ *
        Real.exp (-(4 * gRate Pl / 9) / L.ν) * gaugeN Pl L ≤
      C * L.ν⁻¹ ^ k * Real.exp (-(31 * gRate Pl / 165 - ωb - 3 * K.m0 / 2) / L.ν) ∧
    L.ε ^ (34 / 11 : ℝ) * L.Scut K ^ (23 / 22 : ℝ) * rhoRep K L * L.ε⁻¹ *
        Real.exp (3 * gRate Pl / 5 / L.ν) ≤
      C * L.ν⁻¹ ^ k * Real.exp (-(31 * gRate Pl / 165 - ωb - 3 * K.m0 / 2) / L.ν)

/-- Sequence form of the margins with `k₀ = 2`. -/
def RepMargin (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop,
      RepMarginAt D.Pl D.K (D.level n) (((2 : ℕ) : ℝ) * D.K.b * (gRate D.Pl / 3)) C k

/-! ## 7. Assembly of the far part -/

theorem earlyRepTen_measurable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (w : LVel Pl L) : Measurable (earlyRepTen Pl K L w) := by
  unfold earlyRepTen
  have h1 : Measurable fun p : Chart => (1 : ℝ) - K.χo (L.ν * p.1) :=
    measurable_const.sub (K.hχo.smooth.continuous.measurable.comp
      (measurable_const.mul measurable_fst))
  exact h1.smul (Lp.stronglyMeasurable _).measurable

theorem repSrcTen_measurable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (w : LVel Pl L) : Measurable (repSrcTen Pl K L w) :=
  (Lp.stronglyMeasurable _).measurable

/-- Chain `A ≤ a·B`, `B ≤ b` in `ℝ≥0∞` with real `a, b`, then read off the real bound. -/
theorem ennChain {x a b X : ℝ} {B : ℝ≥0∞} (h1 : ENNReal.ofReal x ≤ ENNReal.ofReal a * B)
    (h2 : B ≤ ENNReal.ofReal b) (ha : 0 ≤ a) (hX : a * b ≤ X) (hX0 : 0 ≤ X) : x ≤ X := by
  have h3 : ENNReal.ofReal x ≤ ENNReal.ofReal (a * b) := by
    rw [ENNReal.ofReal_mul ha]
    exact h1.trans (by gcongr)
  have h4 : ENNReal.ofReal x ≤ ENNReal.ofReal X := h3.trans (ENNReal.ofReal_le_ofReal hX)
  exact (ENNReal.ofReal_le_ofReal_iff hX0).1 h4

/-- Three-step chain. -/
theorem ennChain3 {x e a b X : ℝ} {A B : ℝ≥0∞} (h1 : ENNReal.ofReal x ≤ ENNReal.ofReal e * A)
    (h2 : A ≤ ENNReal.ofReal a * B) (h3 : B ≤ ENNReal.ofReal b) (he : 0 ≤ e) (ha : 0 ≤ a)
    (hX : e * (a * b) ≤ X) (hX0 : 0 ≤ X) : x ≤ X := by
  have h4 : A ≤ ENNReal.ofReal (a * b) := by
    rw [ENNReal.ofReal_mul ha]
    exact h2.trans (by gcongr)
  exact ennChain h1 h4 he hX hX0

/-- **The far part at one level** (5306-5310, 5601-5605): from `S_μ - S_N = S_far`, the unweighted
far bound, the output gains, the old (`RepairSourceAt`) and early repair sources and the margins. -/
theorem farRep_level (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hχ : IsStreamCutoff K.χy) (hC0 : 0 < K.C0) (hγ : 0 ≤ gRate Pl) (hν1 : L.ν ≤ 1)
    (Sf : LStr Pl K L →L[ℝ] LVel Pl L) (hSf : IsFarMaskG L.ε⁻¹ μ K.δ (L.Scut K) Sf)
    (heq : Sop Pl K L μ - SNop Pl K L μ = Sf)
    {CK : ℝ} (hK : RepFarAt Pl K L μ CK) (hL : YoungCutLate) (hG : VelGLeSrc) (hA : RepSplitAE)
    {Cr : ℝ} {kr : ℕ} (hR : RepairSourceAt Pl K L Cr kr)
    {Ce : ℝ} {ke : ℕ} (hE : RepSrcEarlyAt Pl K L Ce ke)
    {ωb CM : ℝ} {kM : ℕ} (hM : RepMarginAt Pl K L ωb CM kM) (w : LVel Pl L) :
    ‖ftLEOp Pl K L μ hχ (repPart (multOp Pl K L w))‖ ≤
      |CK| * (|Cr| + |Ce|) * |CM| * L.ν⁻¹ ^ (kr + ke + kM) *
        Real.exp (-(31 * gRate Pl / 165 - ωb - 3 * K.m0 / 2) / L.ν) * ‖w‖ := by
  have hνp : 0 < L.ν := L.ν_pos
  have hi : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hνp).2 hν1
  have hεp : 0 < L.ε := L.ε_pos
  set T₂ := repPart (multOp Pl K L w) with hT₂
  set O := ftOld Pl K L T₂ with hO
  have hsplit := hA Pl K L hC0 w
  have e : ftFarOp Pl K L μ = Sf := heq
  have hfar : ftLEOp Pl K L μ hχ T₂ =
      (Sf O - youngMul hχ (Sf O)) + Sf (T₂ - O) := by
    rw [ftLEOp_old_early, e]
  set P1 := L.ε ^ (34 / 11 : ℝ) * L.Scut K ^ (23 / 22 : ℝ) with hP1
  have hS0 : 0 < L.Scut K := Real.rpow_pos_of_pos hεp _
  have hP1n : 0 ≤ P1 := by positivity
  have hρ : 0 ≤ rhoRep K L := by unfold rhoRep; positivity
  have hN : 0 ≤ gaugeN Pl L := norm_nonneg _
  have hw : 0 ≤ ‖w‖ := norm_nonneg w
  set E := Real.exp (-(31 * gRate Pl / 165 - ωb - 3 * K.m0 / 2) / L.ν) with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  obtain ⟨hM1, hM2⟩ := hM
  have hpow : ∀ j : ℕ, 0 ≤ L.ν⁻¹ ^ j := fun j => by positivity
  have hCKP : CK * P1 ≤ |CK| * P1 := mul_le_mul_of_nonneg_right (le_abs_self _) hP1n
  -- (A) the old source, late output
  have hA1 : ‖Sf O - youngMul hχ (Sf O)‖ ≤
      |CK| * |Cr| * |CM| * L.ν⁻¹ ^ (kr + kM) * E * ‖w‖ := by
    have s1 := hL hχ (cOf L.ν) (gRate Pl) L.ν hγ hνp (Sf O)
    have s2 := hK Sf hSf O (repSrcTen Pl K L w) (repSrcTen_measurable _ _ _ w) hsplit.1
    have s2' : eLpNorm (Sf O : Chart → Merid) 2 (srcMeasure (cOf L.ν)) ≤
        ENNReal.ofReal (|CK| * P1) * phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19)
          (strPhys L.ε⁻¹ (cOf L.ν) (repSrcTen Pl K L w)) := by
      refine s2.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le)
      rw [show CK * L.ε ^ (34 / 11 : ℝ) * L.Scut K ^ (23 / 22 : ℝ) = CK * P1 by rw [hP1]; ring]
      exact hCKP
    have s3 : phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19)
        (strPhys L.ε⁻¹ (cOf L.ν) (repSrcTen Pl K L w)) ≤
        ENNReal.ofReal (|Cr| * L.ν⁻¹ ^ kr * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖) := by
      refine (hR w).trans (ENNReal.ofReal_le_ofReal ?_)
      have : 0 ≤ L.ν⁻¹ ^ kr * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖ := by positivity
      have h := mul_le_mul_of_nonneg_right (le_abs_self Cr) this
      calc Cr * L.ν⁻¹ ^ kr * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖
          = Cr * (L.ν⁻¹ ^ kr * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖) := by ring
        _ ≤ |Cr| * (L.ν⁻¹ ^ kr * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖) := h
        _ = _ := by ring
    refine ennChain3 s1 s2' s3 (Real.exp_pos _).le (by positivity) ?_ (by positivity)
    have hm : P1 * rhoRep K L * L.ε⁻¹ * Real.exp (-(4 * gRate Pl / 9) / L.ν) *
        gaugeN Pl L ≤ |CM| * L.ν⁻¹ ^ kM * E := by
      refine hM1.trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (hpow _)) hE0
    have hQ : 0 ≤ |CK| * |Cr| * L.ν⁻¹ ^ kr * ‖w‖ := by positivity
    calc Real.exp (-(4 * gRate Pl / 9) / L.ν) * (|CK| * P1 *
          (|Cr| * L.ν⁻¹ ^ kr * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖))
        = (|CK| * |Cr| * L.ν⁻¹ ^ kr * ‖w‖) * (P1 * rhoRep K L * L.ε⁻¹ *
          Real.exp (-(4 * gRate Pl / 9) / L.ν) * gaugeN Pl L) := by ring
      _ ≤ (|CK| * |Cr| * L.ν⁻¹ ^ kr * ‖w‖) * (|CM| * L.ν⁻¹ ^ kM * E) :=
        mul_le_mul_of_nonneg_left hm hQ
      _ = |CK| * |Cr| * |CM| * L.ν⁻¹ ^ (kr + kM) * E * ‖w‖ := by rw [pow_add]; ring
  -- (B) the early source
  have hB1 : ‖Sf (T₂ - O)‖ ≤ |CK| * |Ce| * |CM| * L.ν⁻¹ ^ (ke + kM) * E * ‖w‖ := by
    have s1 := hG (cOf L.ν) (gRate Pl) L.ν hγ hνp (Sf (T₂ - O))
    have s1' : ENNReal.ofReal ‖Sf (T₂ - O)‖ ≤ ENNReal.ofReal 1 *
        eLpNorm (Sf (T₂ - O) : Chart → Merid) 2 (srcMeasure (cOf L.ν)) := by
      rw [ENNReal.ofReal_one, one_mul]; exact s1
    have s2 := hK Sf hSf (T₂ - O) (earlyRepTen Pl K L w) (earlyRepTen_measurable _ _ _ w) hsplit.2
    have s2' : eLpNorm (Sf (T₂ - O) : Chart → Merid) 2 (srcMeasure (cOf L.ν)) ≤
        ENNReal.ofReal (|CK| * P1) * phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19)
          (strPhys L.ε⁻¹ (cOf L.ν) (earlyRepTen Pl K L w)) := by
      refine s2.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le)
      rw [show CK * L.ε ^ (34 / 11 : ℝ) * L.Scut K ^ (23 / 22 : ℝ) = CK * P1 by rw [hP1]; ring]
      exact hCKP
    have s3 : phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19)
        (strPhys L.ε⁻¹ (cOf L.ν) (earlyRepTen Pl K L w)) ≤
        ENNReal.ofReal (|Ce| * L.ν⁻¹ ^ ke * rhoRep K L * L.ε⁻¹ *
          Real.exp (3 * gRate Pl / 5 / L.ν) * ‖w‖) := by
      refine (hE w).trans (ENNReal.ofReal_le_ofReal ?_)
      have : 0 ≤ L.ν⁻¹ ^ ke * rhoRep K L * L.ε⁻¹ * Real.exp (3 * gRate Pl / 5 / L.ν) * ‖w‖ := by
        positivity
      have h := mul_le_mul_of_nonneg_right (le_abs_self Ce) this
      calc Ce * L.ν⁻¹ ^ ke * rhoRep K L * L.ε⁻¹ * Real.exp (3 * gRate Pl / 5 / L.ν) * ‖w‖
          = Ce * (L.ν⁻¹ ^ ke * rhoRep K L * L.ε⁻¹ * Real.exp (3 * gRate Pl / 5 / L.ν) * ‖w‖) := by
            ring
        _ ≤ |Ce| * (L.ν⁻¹ ^ ke * rhoRep K L * L.ε⁻¹ * Real.exp (3 * gRate Pl / 5 / L.ν) * ‖w‖) := h
        _ = _ := by ring
    refine ennChain3 s1' s2' s3 zero_le_one (by positivity) ?_ (by positivity)
    have hm : P1 * rhoRep K L * L.ε⁻¹ * Real.exp (3 * gRate Pl / 5 / L.ν) ≤
        |CM| * L.ν⁻¹ ^ kM * E := by
      refine hM2.trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (hpow _)) hE0
    have hQ : 0 ≤ |CK| * |Ce| * L.ν⁻¹ ^ ke * ‖w‖ := by positivity
    calc (1 : ℝ) * (|CK| * P1 * (|Ce| * L.ν⁻¹ ^ ke * rhoRep K L * L.ε⁻¹ *
          Real.exp (3 * gRate Pl / 5 / L.ν) * ‖w‖))
        = (|CK| * |Ce| * L.ν⁻¹ ^ ke * ‖w‖) * (P1 * rhoRep K L * L.ε⁻¹ *
          Real.exp (3 * gRate Pl / 5 / L.ν)) := by ring
      _ ≤ (|CK| * |Ce| * L.ν⁻¹ ^ ke * ‖w‖) * (|CM| * L.ν⁻¹ ^ kM * E) :=
        mul_le_mul_of_nonneg_left hm hQ
      _ = |CK| * |Ce| * |CM| * L.ν⁻¹ ^ (ke + kM) * E * ‖w‖ := by rw [pow_add]; ring
  -- combine
  have p1 : L.ν⁻¹ ^ (kr + kM) ≤ L.ν⁻¹ ^ (kr + ke + kM) := pow_le_pow_right₀ hi (by omega)
  have p2 : L.ν⁻¹ ^ (ke + kM) ≤ L.ν⁻¹ ^ (kr + ke + kM) := pow_le_pow_right₀ hi (by omega)
  have hEw : 0 ≤ E * ‖w‖ := by positivity
  have q1 : |CK| * |Cr| * |CM| * L.ν⁻¹ ^ (kr + kM) * E * ‖w‖ ≤
      |CK| * |Cr| * |CM| * L.ν⁻¹ ^ (kr + ke + kM) * E * ‖w‖ := by
    have h0 : 0 ≤ |CK| * |Cr| * |CM| := by positivity
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left p1 h0) hEw
    calc _ = (|CK| * |Cr| * |CM|) * L.ν⁻¹ ^ (kr + kM) * (E * ‖w‖) := by ring
      _ ≤ (|CK| * |Cr| * |CM|) * L.ν⁻¹ ^ (kr + ke + kM) * (E * ‖w‖) := this
      _ = _ := by ring
  have q2 : |CK| * |Ce| * |CM| * L.ν⁻¹ ^ (ke + kM) * E * ‖w‖ ≤
      |CK| * |Ce| * |CM| * L.ν⁻¹ ^ (kr + ke + kM) * E * ‖w‖ := by
    have h0 : 0 ≤ |CK| * |Ce| * |CM| := by positivity
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left p2 h0) hEw
    calc _ = (|CK| * |Ce| * |CM|) * L.ν⁻¹ ^ (ke + kM) * (E * ‖w‖) := by ring
      _ ≤ (|CK| * |Ce| * |CM|) * L.ν⁻¹ ^ (kr + ke + kM) * (E * ‖w‖) := this
      _ = _ := by ring
  rw [hfar]
  refine (norm_add_le _ _).trans ?_
  have hsum : |CK| * (|Cr| + |Ce|) * |CM| * L.ν⁻¹ ^ (kr + ke + kM) * E * ‖w‖ =
      |CK| * |Cr| * |CM| * L.ν⁻¹ ^ (kr + ke + kM) * E * ‖w‖ +
        |CK| * |Ce| * |CM| * L.ν⁻¹ ^ (kr + ke + kM) * E * ‖w‖ := by ring
  rw [hsum]
  linarith [hA1, hB1, q1, q2]

/-- **Assembly of the far part of the repair velocity** (5306-5310, 5601-5605): the near split
(`SeqNearSplit`, `S_μ - S_N = S_far`),
the unweighted far bound, the output gains, the old (`repairSource`) and early repair sources and
the margins give `AgeVelFarRep` with `k₀ = 2`. -/
theorem ageVelFarRep_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hF : ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
      SeqNearSplit D dm dp) (hB : RepFarBox) (hX : RepFarExt)
    (hL : YoungCutLate) (hG : VelGLeSrc) (hA : RepSplitAE)
    (hS : ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
      D.RepSrcEarly)
    (hM : RepMargin Pl σ₀ mZ dm dp) : AgeVelFarRep Pl σ₀ mZ dm dp := by
  refine ⟨2, fun D hPl hσ hmZ hst => ?_⟩
  obtain ⟨CK, hK⟩ := repFarSeq_of hB hX D hst
  obtain ⟨Cr, kr, hR⟩ := repairSource D hst
  obtain ⟨Ce, ke, hE⟩ := hS D hPl hσ hmZ hst
  obtain ⟨CM, kM, hMn⟩ := hM D hPl hσ hmZ hst
  have hν1 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds one_pos)
  refine ⟨|CK| * (|Cr| + |Ce|) * |CM|, kr + ke + kM, ?_⟩
  filter_upwards [hF D hPl hσ hmZ hst hst.actual, hst.near, hK, hR, hE, hMn, hν1] with
    n hFn hnear hKn hRn hEn hMn' hνn z hz w
  obtain ⟨Sf, hSf, hsn⟩ := hFn z hz (hnear z hz)
  have e1 : (concreteBase D.Pl D.K (D.level n) (D.mu n z) (hnear z hz)).S
      = Sop D.Pl D.K (D.level n) (D.mu n z) := rfl
  have e2 : (concreteBase D.Pl D.K (D.level n) (D.mu n z) (hnear z hz)).SN
      = SNop D.Pl D.K (D.level n) (D.mu n z) := rfl
  rw [e1, e2] at hsn
  have heq : Sop D.Pl D.K (D.level n) (D.mu n z) - SNop D.Pl D.K (D.level n) (D.mu n z) = Sf := by
    rw [hsn, sub_sub_cancel]
  exact farRep_level D.Pl D.K (D.level n) (D.mu n z) hst.chiY hst.C0_pos hst.gamma_pos.le hνn
    Sf hSf heq (hKn z hz) hL hG hA hRn hEn hMn' w

end UnforcedLeray.Short.PartIIIb.Concrete
