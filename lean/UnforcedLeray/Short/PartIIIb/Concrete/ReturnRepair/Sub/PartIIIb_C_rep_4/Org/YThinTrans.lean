import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates

/-!
# `PartIII-b:C/rep/4/2/org`: both stream transitions on thin sources

Source `the November 2 reference manuscript` 5301-5372 (`repair:age-error`), the
Ward fields 4161-4214, the normalized old source 5148-5160, closure 5573-5627.

## The split of `ageVel` that the source uses

`ageVel = S_far + Y` (`Estimates.lean`, source 5688-5689).  The source does **not** estimate the two
summands separately.  The near operator removes the whole far mask `s < S, t > e^δ s`, which
contains the young-old rectangle `χ_y S_μ χ_o` (5303-5306: "The young-old rectangle is contained in
this mask"), and the Ward field contains the same rectangle with the opposite sign:
`Y = 𝒞_yW_μ + [D_{μ+1}, 𝒞_y]X₀` (`ward:cutoff-source`, 4203-4204) with `W_μ = -S_μ(χ_oT)` (4171),
so `Y = -χ_yS_μχ_oT + (𝒞_y - χ_y)W_μ + [D_{μ+1}, 𝒞_y]X₀` (4210-4214).  Hence

`ageVel = (S_far - χ_yS_μχ_o) + (Y + χ_yS_μχ_o)` (`ageVel_split`),

the first bracket being the late-output part `(1-χ_y)F_far` and the early-source part
`χ_yF_far(1-χ_o)` (5306-5309), the second the two stream transitions (5309-5316).  These are the
pieces of `δT_a` in `repair:age-error` (5366-5367: "the total stress correction from these regions
and both stream transitions").

The young-old rectangle itself is not small: on a thin source at old ages `t ≥ 1.2/ν` read at young
receivers `s ≤ 1/ν` the order-four kernel gives the curvature power `ε²` (5323-5331) but the gain
ratio `g(t)/g(s)` reaches `e^{γ/ν}` (`g(s) = e^{γs/(1+νs)}`, 5116), so its size is
`P_ν ε²|N_ν| ≍ e^{γ/(3ν)}` (`d₀ = γ/3`, 5119).  Therefore the leaves `AgeYThin` (a bound on `Y`
alone) and `AgeFarThin` (on `S_far` alone) of `Sub/PartIII-b_C_rep_4.lean` are not source
statements (each contains the rectangle); `youngOld_le` records the reduction.  The correct thin
stream-transition leaf is `AgeTransThin` below, on `transOp = Y + χ_yS_μχ_o`.

## Contents

* §1 pointwise fields: `wardW` (`W_μ`), `wardYoungW` (`χ_yW_μ`), `streamCorr` (`(𝒞_y - χ_y)Z`),
  `transCut` (`(𝒞_y - χ_y)W_μ`), `transComm` (`[D_{μ+1}, 𝒞_y]X₀`), `transField` (both);
  `wardY_split` (proved): `Y = χ_yW_μ + transCut + transComm` on `r > 0` from the shifted resolvent
  identity on the young region (`ShiftedResolventYoung`, 4199-4201).
* §2 operators: `youngMul` (`χ_y` on velocities), `youngOldOp` (`χ_yS_μχ_o`), `transOp`,
  `lateEarlyOp`; `ageVel_split`, `youngOld_le` (proved).
* §3 coefficient identity `transOp_coef` (proved): the coefficient of `transOp (T₁,0)` is the
  concrete field `transField` of the old thin source.
* §4 the facts (Props) `SepYoungAt` (`sep:resolvent`, 3611-3621), `ShiftedResolventAt` (4199-4201),
  `TransThinTableAt` (table 5323-5340, late-output gain 5317-5321); the leaf `AgeTransThin`; the
  bridge `transThinOpTable_of` (proved).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. The pointwise fields (source 4171-4214, 5153-5160, 5312-5316) -/

/-- `W_μ = -S_μ(χ_oT)` (source 4171, 5155) in its separated-kernel realization `IIIa.sepW`
(`sep:resolvent`, 3611-3621), real Cartesian components, for a chart representative `g` of the old
source `χ_o(T₁ + T₂)`; `wardX0 = W_μ - W_{μ+1}` (`wardX0_eq`). -/
def wardW (ν μ R c : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) : Space :=
  WithLp.toLp 2 fun i => (UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y τ i).re

theorem wardX0_eq (ν μ R c : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) :
    wardX0 ν μ R c g τ y = wardW ν μ R c g τ y - wardW ν (μ + 1) R c g τ y := by
  ext i
  simp only [wardX0, wardW, PiLp.sub_apply, PiLp.toLp_apply, Complex.sub_re]
  push_cast
  rfl

/-- The stream correction `(𝒞_y - χ_y)Z = (χ_y'/r)Ψ_Z e_z` (source 4180-4186), `Ψ_Z = outPrim Z` the
outward primitive, `χ_y' = ∂_r χ̂_y(νR²/r²)`. -/
def streamCorr (ν R : ℝ) (χy : ℝ → ℝ) (Z : ℝ → Space → Space) (τ : ℝ) (y : Space) : Space :=
  (deriv χy (ν * age R y) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y * outPrim Z τ (ϱ y) (y 2)) •
    coordinateVector 2

/-- `𝒞_yZ = χ_yZ + (𝒞_y - χ_y)Z`. -/
theorem wardStreamCut_eq (ν R : ℝ) (χy : ℝ → ℝ) (Z : ℝ → Space → Space) (τ : ℝ) (y : Space) :
    wardStreamCut ν R χy Z τ y = χy (ν * age R y) • Z τ y + streamCorr ν R χy Z τ y := rfl

/-- `χ_yW_μ`, the scalar-cutoff part of `𝒞_yW_μ` (source 4210-4214: "relative to a scalar-cutoff
reference return"); `-χ_yW_μ = χ_yS_μ(χ_oT)` is the young-old rectangle (5305-5306). -/
def wardYoungW (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) : Space :=
  χy (ν * age R y) • wardW ν μ R c g τ y

/-- **The first stream transition** `(𝒞_χ - χ)W_μ` (source 5312-5316, 4210-4214): the stream
correction of `W_μ`, supported on the transition annulus `0.8/ν < s < 1/ν`. -/
def transCut (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3) : ℝ → Space → Space :=
  streamCorr ν R χy (wardW ν μ R c g)

/-- **The second stream transition** `[L_{free,μ+1}, 𝒞_χ](W_μ - W_{μ+1}) = [D_{μ+1}, 𝒞_y]X₀`
(source 5312-5316, 4203-4214), `X₀ = wardX0`, `D_{μ+1} = physDmu ν (μ+1)`. -/
def transComm (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) : Space :=
  physDmu ν (μ + 1) (wardX ν μ R c χy g) τ y -
    wardStreamCut ν R χy (physDmu ν (μ + 1) (wardX0 ν μ R c g)) τ y

/-- Both stream transitions (source 5312-5316, 5366-5367). -/
def transField (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) : Space :=
  transCut ν μ R c χy g τ y + transComm ν μ R c χy g τ y

/-- **`ward:shifted-resolvent`** (source 4196-4201): `D_{μ+1}X₀ = W_μ`, read pointwise on the young
region `r > 0`, `s = R²/r² ≤ 1/ν` (`r ≥ R√ν`), which is separated from the old source
`χ_oT` (supported in `s ≥ 1.2/ν`, 4163-4168) and where both sides are smooth. -/
def ShiftedResolventYoung (ν μ R c : ℝ) (g : Chart → Ten3) : Prop :=
  ∀ τ (y : Space), 0 < ϱ y → ν * age R y ≤ 1 →
    physDmu ν (μ + 1) (wardX0 ν μ R c g) τ y = wardW ν μ R c g τ y

theorem ϱ_mer {ρ : ℝ} (z : ℝ) (hρ : 0 < ρ) : ϱ (!₂[ρ, 0, z] : Space) = ρ := by
  unfold ϱ
  have e : (!₂[ρ, 0, z] : Space) 0 ^ 2 + (!₂[ρ, 0, z] : Space) 1 ^ 2 = ρ ^ 2 := by simp
  rw [e]
  exact Real.sqrt_sq hρ.le

theorem age_mer_le {R ν ρ : ℝ} (z : ℝ) {y : Space} (hν : 0 ≤ ν) (hy : 0 < ϱ y) (hρ : ϱ y < ρ)
    (h : ν * age R y ≤ 1) : ν * age R (!₂[ρ, 0, z] : Space) ≤ 1 := by
  have hρ0 : 0 < ρ := hy.trans hρ
  have e : age R (!₂[ρ, 0, z] : Space) = R ^ 2 / ρ ^ 2 := by
    unfold age
    rw [ϱ_mer z hρ0]
  rw [e]
  refine le_trans ?_ h
  unfold age
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_left (sq_nonneg R) (by positivity) (pow_le_pow_left₀ hy.le hρ.le 2)) hν

/-- Beyond `t = 1` the stream cutoff and its derivative vanish. -/
theorem streamCut_zero_of_gt {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ) {t : ℝ} (ht : 1 < t) :
    χ t = 0 ∧ deriv χ t = 0 := by
  refine ⟨hχ.zero t ht.le, ?_⟩
  have hev : χ =ᶠ[nhds t] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu using hχ.zero u (le_of_lt hu)
  rw [hev.deriv_eq]
  simp

/-- `𝒞_yZ(τ, y)` at `r > 0` depends only on `Z` in the young region: `χ_y`, `χ_y'` vanish for
`s > 1/ν`, and the outward primitive at `r` reads `Z` at radii `ρ > r`. -/
theorem wardStreamCut_congr {ν R : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) (hν : 0 ≤ ν)
    {Z Z' : ℝ → Space → Space}
    (h : ∀ τ (y : Space), 0 < ϱ y → ν * age R y ≤ 1 → Z τ y = Z' τ y)
    (τ : ℝ) {y : Space} (hy : 0 < ϱ y) :
    wardStreamCut ν R χy Z τ y = wardStreamCut ν R χy Z' τ y := by
  by_cases hyl : ν * age R y ≤ 1
  · have hP : outPrim Z τ (ϱ y) (y 2) = outPrim Z' τ (ϱ y) (y 2) := by
      unfold outPrim
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
      have hρ' : ϱ y < ρ := hρ
      have h0 : 0 < ρ := hy.trans hρ'
      simp only
      rw [h τ _ (by rw [ϱ_mer _ h0]; exact h0) (age_mer_le _ hν hy hρ' hyl)]
    rw [wardStreamCut_eq, wardStreamCut_eq, h τ y hy hyl]
    unfold streamCorr
    rw [hP]
  · obtain ⟨h0, hd⟩ := streamCut_zero_of_gt hχ (lt_of_not_ge hyl)
    rw [wardStreamCut_eq, wardStreamCut_eq]
    unfold streamCorr
    simp [h0, hd]

/-- **`ward:cutoff-source`** (source 4203-4214) in split form: from the shifted resolvent identity
on the young region, `Y = χ_yW_μ + (𝒞_y - χ_y)W_μ + [D_{μ+1}, 𝒞_y]X₀` at every point with `r > 0`. -/
theorem wardY_split {ν μ R c : ℝ} {χy : ℝ → ℝ} {g : Chart → Ten3} (hχ : IsStreamCutoff χy)
    (hν : 0 ≤ ν) (hres : ShiftedResolventYoung ν μ R c g) (τ : ℝ) {y : Space} (hy : 0 < ϱ y) :
    wardY ν μ R c χy g τ y = wardYoungW ν μ R c χy g τ y + transField ν μ R c χy g τ y := by
  have e1 : wardY ν μ R c χy g τ y =
      wardStreamCut ν R χy (physDmu ν (μ + 1) (wardX0 ν μ R c g)) τ y +
        transComm ν μ R c χy g τ y := by
    unfold transComm wardY
    abel
  rw [e1, wardStreamCut_congr (Z' := wardW ν μ R c g) hχ hν hres τ hy, wardStreamCut_eq]
  unfold wardYoungW transField transCut
  abel

/-! ## 2. Coefficients on the chart -/

theorem coefOf_add (R : ℝ) (F G : ℝ → Space → Space) (p : Chart) :
    coefOf R (fun τ y => F τ y + G τ y) p = coefOf R F p + coefOf R G p := by
  unfold coefOf
  rw [← smul_add]
  congr 1
  ext i
  fin_cases i <;> simp

theorem coefOf_congr_pt (R : ℝ) {F G : ℝ → Space → Space} (p : Chart)
    (h : F (NearInst.chartTau R p) (NearInst.chartY R p) =
      G (NearInst.chartTau R p) (NearInst.chartY R p)) :
    coefOf R F p = coefOf R G p := by
  unfold coefOf
  rw [h]

theorem ϱ_chartY {R : ℝ} (hR : 0 < R) {p : Chart} (hs : 0 < p.1) :
    ϱ (NearInst.chartY R p) = R / Real.sqrt p.1 := by
  have : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hs
  unfold ϱ NearInst.chartY
  simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [show (R / Real.sqrt p.1) ^ 2 + 0 ^ 2 = (R / Real.sqrt p.1) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

theorem age_chartY {R : ℝ} (hR : 0 < R) {p : Chart} (hs : 0 < p.1) :
    age R (NearInst.chartY R p) = p.1 := by
  unfold age
  rw [ϱ_chartY hR hs, div_pow, Real.sq_sqrt hs.le]
  field_simp

theorem coefOf_wardYoungW {ν μ R c : ℝ} {χy : ℝ → ℝ} {g : Chart → Ten3} (hR : 0 < R) {p : Chart}
    (hs : 0 < p.1) :
    coefOf R (wardYoungW ν μ R c χy g) p = χy (ν * p.1) • coefOf R (wardW ν μ R c g) p := by
  unfold coefOf wardYoungW
  rw [age_chartY hR hs]
  ext i
  fin_cases i <;> simp [smul_eq_mul] <;> ring

/-! ## 3. The operators of the split -/

theorem cutFun_measurable_y {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ) (ν : ℝ) :
    Measurable (cutFun χ ν) :=
  hχ.smooth.continuous.measurable.comp (measurable_const.mul measurable_fst)

theorem cutFun_bound_y {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ) (ν : ℝ) (p : Chart) :
    |cutFun χ ν p| ≤ 1 := by
  unfold cutFun
  rw [abs_of_nonneg (hχ.range _).1]
  exact (hχ.range _).2

/-- `χ_y` on body velocities: multiplication by `χ̂_y(νs)` (source 4164, 5158). -/
def youngMul {c γ ν : ℝ} {χy : ℝ → ℝ} (hχy : IsStreamCutoff χy) :
    VelG c γ ν →L[ℝ] VelG c γ ν :=
  NearInst.mulBdd (E := Merid) (μ := bodyMeasure c γ ν) (cutFun χy ν)
    (cutFun_measurable_y hχy ν) 1 (cutFun_bound_y hχy ν)

theorem youngMul_ae {c γ ν : ℝ} {χy : ℝ → ℝ} (hχy : IsStreamCutoff χy) (v : VelG c γ ν) :
    (youngMul hχy v : Chart → Merid) =ᵐ[bodyMeasure c γ ν]
      fun p => cutFun χy ν p • (v : Chart → Merid) p := by
  unfold youngMul NearInst.mulBdd
  rw [LinearMap.mkContinuous_apply]
  exact MemLp.coeFn_toLp
    (NearInst.memLp_mulBdd (cutFun_measurable_y hχy ν) (cutFun_bound_y hχy ν) v)

section Ops

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
  (hχy : IsStreamCutoff K.χy)

/-- `χ_o(T₁, 0)`, the old thin source (source 5148-5157). -/
abbrev oldThin (T : LStr Pl K L) : LStr Pl K L :=
  chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (thinPart T)

/-- `g₁, g₂` represent the two components of the stress `F` (as in `IsWardTriple`). -/
def IsRep (F : LStr Pl K L) (g₁ g₂ : Chart → Ten3) : Prop :=
  (F.fst : Chart → Ten3) =ᵐ[gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν] g₁ ∧
    (F.snd : Chart → Ten3) =ᵐ[gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν] g₂

/-- **The young-old rectangle** `χ_yS_μχ_o` (source 5303-5306: contained in the far mask;
4171, 4210-4214: equal to `-χ_yW_μ`). -/
def youngOldOp : LStr Pl K L →L[ℝ] LVel Pl L :=
  (youngMul hχy).comp
    ((Sop Pl K L μ).comp (chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo))

/-- **Both stream transitions** `Y + χ_yS_μχ_o = Y - χ_yW_μ = (𝒞_χ - χ)W_μ +
[L_{free,μ+1}, 𝒞_χ](W_μ - W_{μ+1})` (source 5312-5316, 4210-4214). -/
def transOp : LStr Pl K L →L[ℝ] LVel Pl L :=
  (wardOps Pl K L μ).1 + youngOldOp Pl K L μ hχy

/-- **The late-output and early-source parts** `S_far - χ_yS_μχ_o = (1-χ_y)F_far +
χ_yF_far(1-χ_o)` (source 5303-5311). -/
def lateEarlyOp : LStr Pl K L →L[ℝ] LVel Pl L :=
  Sop Pl K L μ - SNop Pl K L μ - youngOldOp Pl K L μ hχy

/-- `S_far + Y = (S_far - χ_yS_μχ_o) + (Y + χ_yS_μχ_o)` (source 5303-5316, 5366-5367). -/
theorem ageVel_split :
    ageVel Pl K L μ = lateEarlyOp Pl K L μ hχy + transOp Pl K L μ hχy := by
  unfold ageVel lateEarlyOp transOp
  abel

/-- A bound on `Y` alone and one on the transitions bound the young-old rectangle: the leaf
`AgeYThin` of `Sub/PartIII-b_C_rep_4.lean` together with `AgeTransThin` would give the rectangle
the margin `γ/15`, whereas its size is `P_ν ε²|N_ν| ≍ e^{γ/(3ν)}` (module docstring). -/
theorem youngOld_le (x : LStr Pl K L) :
    ‖multOp Pl K L (youngOldOp Pl K L μ hχy x)‖ ≤
      ‖multOp Pl K L (transOp Pl K L μ hχy x)‖ + ‖multOp Pl K L ((wardOps Pl K L μ).1 x)‖ := by
  have e : multOp Pl K L (youngOldOp Pl K L μ hχy x) =
      multOp Pl K L (transOp Pl K L μ hχy x) - multOp Pl K L ((wardOps Pl K L μ).1 x) := by
    rw [← map_sub]
    unfold transOp
    simp
  rw [e]
  exact norm_sub_le _ _

/-! ## 4. The facts at one regime -/

/-- **`sep:resolvent` on the young receiver** (source 3611-3621: `S_μT = -W_μ`; 4163-4171,
5153-5157: `W_μ = -S_μ(χ_oT)`): for the old thin source `χ_o(T₁,0)` and representatives of its
components, the coefficient of `S_μ(χ_o(T₁,0))` is `-W_μ` at almost every young chart point
`s ≤ 1/ν` (separated from the source support `s ≥ 1.2/ν`). -/
def SepYoungAt : Prop :=
  ∀ (T : LStr Pl K L) (g₁ g₂ : Chart → Ten3), IsRep Pl K L (oldThin Pl K L T) g₁ g₂ →
    ∀ᵐ p ∂(bodyMeasure (cOf L.ν) (gRate Pl) L.ν), L.ν * p.1 ≤ 1 →
      (Sop Pl K L μ (oldThin Pl K L T) : Chart → Merid) p =
        -coefOf L.ε⁻¹ (wardW L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂)) p

/-- **`ward:shifted-resolvent`** (source 4196-4201) for the old thin source, on the young region. -/
def ShiftedResolventAt : Prop :=
  ∀ (T : LStr Pl K L) (g₁ g₂ : Chart → Ten3), IsRep Pl K L (oldThin Pl K L T) g₁ g₂ →
    ShiftedResolventYoung L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂)

/-- **The thin-source row of the table for both transitions** (source 5312-5316: support
`0.8/ν < s < 1/ν`; 5317-5321: late output `g(s)⁻¹ ≤ e^{-4γ/(9ν)}`; 5323-5331: thin receiver `ε²`,
scaled repair receiver `ε^{49/22}e^{m₀/(2ν)}`, common `P_νS^k`, factor `|N_ν|e^{-4γ/(9ν)}` for late
output; 5333-5340: "The outward stream primitive has the same norm powers, so both transition
terms have the late-output bound"; 5342-5355 and 5573-5592: the age-zero thin estimate through the
mass `N₀(a) ≤ C(a^{-3/4}+a^{-1/2})‖T‖_{Z₁}`).  For every thin stress `T`, representatives of
`χ_o(T₁,0)` and every body velocity `v` whose coefficient is the transition field,
`‖g⁻¹M_Uv‖_Z ≤ P_ν S^{k₁}|N_ν|(ε² + ε^{49/22}e^{m₀/(2ν)})e^{-4γ/(9ν)}‖g⁻¹T‖_Z`. -/
def TransThinTableAt (k₁ : ℕ) (C : ℝ) (k : ℕ) : Prop :=
  ∀ (T : LStr Pl K L) (g₁ g₂ : Chart → Ten3), IsRep Pl K L (oldThin Pl K L T) g₁ g₂ →
    ∀ v : LVel Pl L,
      (v : Chart → Merid) =ᵐ[bodyMeasure (cOf L.ν) (gRate Pl) L.ν]
          coefOf L.ε⁻¹ (transField L.ν μ L.ε⁻¹ (cOf L.ν) K.χy (g₁ + g₂)) →
        ‖multOp Pl K L v‖ ≤
          C * L.ν⁻¹ ^ k * L.Scut K ^ k₁ * gaugeN Pl L *
            (L.ε ^ (2 : ℝ) + L.ε ^ (49 / 22 : ℝ) * Real.exp (K.m0 / (2 * L.ν))) *
            Real.exp (-(4 * gRate Pl / 9) / L.ν) * ‖T‖

theorem bodyMeasure_ae_pos (c γ ν : ℝ) : ∀ᵐ p ∂(bodyMeasure c γ ν), 0 < p.1 := by
  have h1 : ∀ᵐ s ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
      fun s => ENNReal.ofReal (s ^ (-3 / 2 : ℝ))), 0 < s :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  have h2 : ∀ᵐ p ∂(ageμ c (-3 / 2)), 0 < p.1 := by
    unfold ageμ
    exact Measure.quasiMeasurePreserving_fst.ae h1
  unfold bodyMeasure
  exact (withDensity_absolutelyContinuous _ _).ae_le h2

/-- **The coefficient of `transOp` on thin sources** (source 4203-4214, 5312-5316): from the Ward
pin, `sep:resolvent` on the young receiver and the shifted resolvent identity, the coefficient of
`(Y + χ_yS_μχ_o)(T₁,0)` is the concrete transition field of the old thin source. -/
theorem transOp_coef
    (hW : IsWardTriple (wardOps Pl K L μ).1 (wardOps Pl K L μ).2.1 (wardOps Pl K L μ).2.2 L.ε μ
      K.hχo K.χy L.U L.pres)
    (h1 : SepYoungAt Pl K L μ) (h2 : ShiftedResolventAt Pl K L μ) (T : LStr Pl K L)
    {g₁ g₂ : Chart → Ten3} (hg : IsRep Pl K L (oldThin Pl K L T) g₁ g₂) :
    (transOp Pl K L μ hχy (thinPart T) : Chart → Merid) =ᵐ[bodyMeasure (cOf L.ν) (gRate Pl) L.ν]
      coefOf L.ε⁻¹ (transField L.ν μ L.ε⁻¹ (cOf L.ν) K.χy (g₁ + g₂)) := by
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  have hν : 0 ≤ L.ν := L.ν_pos.le
  have hY := (hW (thinPart T) g₁ g₂ hg.1 hg.2).1
  have hS := h1 T g₁ g₂ hg
  have hres := h2 T g₁ g₂ hg
  have hM := youngMul_ae (c := cOf L.ν) (γ := gRate Pl) (ν := L.ν) hχy
    (Sop Pl K L μ (oldThin Pl K L T))
  have hadd := Lp.coeFn_add ((wardOps Pl K L μ).1 (thinPart T))
    (youngOldOp Pl K L μ hχy (thinPart T))
  filter_upwards [hY, hS, hM, hadd, bodyMeasure_ae_pos (cOf L.ν) (gRate Pl) L.ν]
    with p hYp hSp hMp haddp hp
  have hsplit : coefOf L.ε⁻¹ (wardY L.ν μ L.ε⁻¹ (cOf L.ν) K.χy (g₁ + g₂)) p =
      K.χy (L.ν * p.1) • coefOf L.ε⁻¹ (wardW L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂)) p +
        coefOf L.ε⁻¹ (transField L.ν μ L.ε⁻¹ (cOf L.ν) K.χy (g₁ + g₂)) p := by
    rw [coefOf_congr_pt L.ε⁻¹ p (G := fun τ y => wardYoungW L.ν μ L.ε⁻¹ (cOf L.ν) K.χy (g₁ + g₂) τ y +
        transField L.ν μ L.ε⁻¹ (cOf L.ν) K.χy (g₁ + g₂) τ y)
      (wardY_split hχy hν hres _ (by rw [ϱ_chartY hR hp]; positivity)),
      coefOf_add, coefOf_wardYoungW hR hp]
  have e1 : (transOp Pl K L μ hχy (thinPart T) : Chart → Merid) p =
      ((wardOps Pl K L μ).1 (thinPart T) : Chart → Merid) p +
        (youngMul hχy (Sop Pl K L μ (oldThin Pl K L T)) : Chart → Merid) p := haddp
  rw [e1, hYp, hMp, hsplit]
  change K.χy (L.ν * p.1) • _ + _ + K.χy (L.ν * p.1) • _ = _
  by_cases hyl : L.ν * p.1 ≤ 1
  · rw [hSp hyl, smul_neg]
    abel
  · rw [hχy.zero _ (le_of_lt (lt_of_not_ge hyl))]
    simp

end Ops

/-! ## 5. Along the sequence: the facts, the leaf and the bridge -/

/-- (P1) `sep:resolvent` on the young receiver for the old thin source, for large `n` and every
`z ∈ [-1,1]` (source 3611-3621, 4163-4171, 5153-5157). -/
def SepYoungThin (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    SepYoungAt D.Pl D.K (D.level n) (D.mu n z)

/-- (P2) The shifted resolvent identity `D_{μ+1}X₀ = W_μ` on the young region for the old thin
source (source 4196-4201). -/
def ShiftedResolventThin (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ShiftedResolventAt D.Pl D.K (D.level n) (D.mu n z)

/-- (P3) The thin-source table row for both transitions (source 5312-5355, 5573-5592), with the
`S`-degree `k₁` chosen before `b` (depending only on `Pl, σ₀, m_Z, dm, dp`). -/
def TransThinTable (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₁ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      TransThinTableAt D.Pl D.K (D.level n) (D.mu n z) k₁ C k

/-- The table row as a bound on the operator `transOp` (output of `transThinOpTable_of`). -/
def TransThinOpTable (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₁ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ hst : D.RepairStanding dm dp,
    ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ T : LStr D.Pl D.K (D.level n),
        ‖multOp D.Pl D.K (D.level n)
            (transOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY (thinPart T))‖ ≤
          C * (D.level n).ν⁻¹ ^ k * (D.level n).Scut D.K ^ k₁ * gaugeN D.Pl (D.level n) *
            ((D.level n).ε ^ (2 : ℝ) +
              (D.level n).ε ^ (49 / 22 : ℝ) * Real.exp (D.K.m0 / (2 * (D.level n).ν))) *
            Real.exp (-(4 * gRate D.Pl / 9) / (D.level n).ν) * ‖T‖

namespace SeqData

/-- **Both stream transitions on thin sources** (source 5312-5316, 5333-5340, margins 5357-5365,
closure 5607-5627): `‖g⁻¹M_U(Y + χ_yS_μχ_o)(T₁,0)‖_Z ≤ P_ν e^{-(γ/15-ω_b-3m₀/2)/ν}‖g⁻¹T‖_Z`. -/
def AgeTransThinAt (D : SeqData) (hχy : IsStreamCutoff D.K.χy) (ωb : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ T : LStr D.Pl D.K (D.level n),
      ‖multOp D.Pl D.K (D.level n)
          (transOp D.Pl D.K (D.level n) (D.mu n z) hχy (thinPart T))‖ ≤
        C * (D.level n).ν⁻¹ ^ k *
          Real.exp (-(gRate D.Pl / 15 - ωb - 3 * D.K.m0 / 2) / (D.level n).ν) * ‖T‖

end SeqData

/-- **The thin stream-transition leaf** of `repair:age-error` (replaces `AgeYThin`, which bounds
`Y` alone): the `S`-degree `k₀` chosen before `b`, `ω_b = k₀bγ/3` (5607). -/
def AgeTransThin (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ hst : D.RepairStanding dm dp,
      D.AgeTransThinAt hst.chiY ((k₀ : ℝ) * D.K.b * (gRate D.Pl / 3))

/-- **Bridge** (proved): (P1)-(P3) and the Ward pin of the standing hypotheses give the table row
for the operator `transOp`. -/
theorem transThinOpTable_of {Pl : PlanarData} {σ₀ mZ dm dp : ℝ} (h1 : SepYoungThin dm dp)
    (h2 : ShiftedResolventThin dm dp) (h3 : TransThinTable Pl σ₀ mZ dm dp) :
    TransThinOpTable Pl σ₀ mZ dm dp := by
  obtain ⟨k₁, H⟩ := h3
  refine ⟨k₁, fun D hPl hσ hmZ hst => ?_⟩
  obtain ⟨C, k, HC⟩ := H D hPl hσ hmZ hst
  refine ⟨C, k, ?_⟩
  filter_upwards [HC, h1 D hst, h2 D hst, hst.pins] with n hn s1 s2 pins z hz T
  have hW : IsWardTriple (wardOps D.Pl D.K (D.level n) (D.mu n z)).1
      (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.1 (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2
      (D.level n).ε (D.mu n z) D.K.hχo D.K.χy (D.level n).U (D.level n).pres :=
    Classical.epsilon_spec (pins z hz).ward
  have hg : IsRep D.Pl D.K (D.level n) (oldThin D.Pl D.K (D.level n) T)
      ((oldThin D.Pl D.K (D.level n) T).fst : Chart → Ten3)
      ((oldThin D.Pl D.K (D.level n) T).snd : Chart → Ten3) :=
    ⟨EventuallyEq.rfl, EventuallyEq.rfl⟩
  exact hn z hz T _ _ hg _
    (transOp_coef D.Pl D.K (D.level n) (D.mu n z) hst.chiY hW (s1 z hz) (s2 z hz) T hg)

end UnforcedLeray.Short.PartIIIb.Concrete
