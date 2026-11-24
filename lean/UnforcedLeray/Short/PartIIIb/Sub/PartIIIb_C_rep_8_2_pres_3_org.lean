import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3
import UnforcedLeray.Short.PartIIb.Sub.R1
import UnforcedLeray.Lib.LerayLp.Leray

/-!
# The exact pressure against the flat lifted pressure (`PartIII-b:C/rep/8/2/pres/3/org`)

Source of record: `the November 2 reference manuscript`
(73 pages), lines 5245-5260 (the exact pressure correction `∇(p - p_V) = -(I-ℙ)(V·∇r_b + r_b·∇V +
r_b·∇r_b)`), 5272-5281 (`∇(p_raw - p_lift) = -(I-ℙ)F_raw`; "the entrance convection terms and the
explicit radial pressure completion then give `‖∇p - G_flat‖_{Y_{11/4}} ≤ P_ν ε^{3/11}e^{m₀/ν}`"),
1205-1225 (Proposition `sct:lift`: the raw lift, `p_raw = (R/r)²p`, the residual bound
`‖F_R‖_{C_per W^{1,p}} ≤ P_p ε^{1-2/p}`, `p = 11/4` gives `Pε^{3/11}`), 2681-2688 (the `Y_r` norms in
the ring chart).

## The identity

Write `U = V + r_b` (`L.U`), `p = L.pres` (`IsExactProfile`: `D₀U + U·∇U + ∇p = 0`), `U_raw = rawU`,
`p_lift = liftP` (in the similarity variables `p_raw = (R/r)²p` *is* `s·p_cyl = p_lift`, source
1217), and `F_R` the similarity residual of the raw lift (`rawResidF`, the Part II-a object
`PartIIa.ringResidual`; off the axis `F_R = D₀U_raw + U_raw·∇U_raw + ∇p_lift`,
`IIb.RingResidualCartesianNS`).  Subtracting the two equations,

  `∇p - ∇p_lift = -D₀(U - U_raw) - (U·∇U - U_raw·∇U_raw) - F_R`.

`D₀(U - U_raw)` is solenoidal and the left side is a gradient, so applying `I - ℙ`

  `∇p - ∇p_lift = -(I-ℙ)(convChg + entSrc + F_R)`   (`PresHelmholtzAt`),

`convChg = U·∇U - V·∇V` (repair convection), `entSrc = D₀(V - U_raw) + V·∇V - U_raw·∇U_raw` (the
complete equation source of the entrance lift `E_εα = V - U_raw`, which is in `Y_p` although `E_εα`
itself is not: source 2346-2347, 2388-2390), `D₀(U - V) = D₀r_b` solenoidal.

This is the sum of the source's three identities: `∇(p - p_V) = -(I-ℙ)(U·∇U - V·∇V)` (5254-5257),
`∇(p_V - p_raw) = -(I-ℙ)(V·∇V - U_raw·∇U_raw)` with `V - U_raw = E_εα` (the entrance convection
terms, 5277-5279) and `∇(p_raw - p_lift) = -(I-ℙ)F_raw` (5274-5276), `∇p_V`, `∇p_raw` the canonical
pressures.  `I - ℙ` is `lerayComp114` (the `L^{11/4}` Leray projection `RieszLp.lerayLp` of
`Lib/LerayLp/Leray.lean`), bounded on `L^{11/4}` (`LerayComp114Bound`).

## The estimate

`|convChg| ≤ (|∇U| + |V|)(|U - V| + Σ_j|∂_j(U - V)|)` pointwise (`norm_convChg_le`),
so with `|∇U| + |V| ≤ P_ν` (`GradUAt`, the sup part of `CoefChgAt`), the `Y_{11/4}` bound
`P_νρ` of the repair change (`CoefChgAt`, task `PartIII-b:C/rep/8/2/pres/4`), the `Y_{11/4}` bound
`P_νρ` of the entrance source (`EntSrcAt`) and
`sup_τ‖F_R(τ)‖_{L^{11/4}} ≤ P_ν ε^{3/11}` (`RawResidAt`, from `PartIIa.RingResidualBound`),
`‖∇p - ∇p_lift‖_{Y_{11/4}} ≤ C_{11/4}(P_ν·P_νρ + P_νρ + P_νε^{3/11}) ≤ P_νρ`, `ρ = ε^{3/11}e^{m₀/ν}`.
The `Y_{11/4}` norm is the phase average `phaseLr` over one period `P = 2εc` of the `L^{11/4}(ℝ³)`
norm; for axisymmetric densities it equals the chart form `eLpNorm (ringRead R f) (ringPhysμ R c)`
(`RingReadPhaseLr`, from `Axi.phaseAvg_ringChart`, source 2681-2688).

## Contents

* objects: `merPt`, `IsAxiScalar`, `axisZero`, `lerayComp114`, `rawResidF`, `convChg`,
  `entSrc`, `presForce`;
* general leaves: `LerayComp114Bound` (Calderón–Zygmund on `L^{11/4}`, from `RieszLp.lerayLp`),
  `RingReadPhaseLr` (the chart form of the `Y_r` norm, from `Axi.phaseAvg_ringChart`);
* leaves at one level: `PresHelmholtzAt`, `PresChgPhysAt`, `PresForcePhysAt`, `RawResidAt`,
  `EntSrcAt`, `GradUAt` (and the existing `CoefChgAt`), with their sequence forms;
* **proved here:** `lerayComp114Bound`, `ringReadPhaseLr` (the two general leaves),
  `norm_convChg_le`, `presFlatBoundAt_of`, `presFlatBound_of`, `presFlatBound_of_leaves`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. Objects -/

/-- The point at azimuth `0` with the cylindrical coordinates `(ϱ, y₃)` of `y` (the chart point
`chartY` of the chart coordinates of `y`, source 2666-2674). -/
def merPt (y : Space) : Space := WithLp.toLp 2 ![ϱ y, 0, y 2]

/-- A phase-dependent scalar invariant under the rotations about the axis:
`f(τ, y) = f(τ, merPt y)` (the densities of the axisymmetric fields of the return, source
2031, 2681-2688). -/
def IsAxiScalar (f : ℝ → Space → ℝ) : Prop := ∀ τ y, f τ y = f τ (merPt y)

open Classical in
/-- `f` set to `0` on the axis `ℝ × {ϱ = 0}` (a null set where the lifted fields carry junk
values). -/
def axisZero (f : ℝ → Space → ℝ) (x : ℝ × Space) : ℝ := if x.2 ∈ axis then 0 else f x.1 x.2

theorem one_lt_elevenFourths : (1 : ℝ≥0∞) < 11 / 4 := by
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  norm_num

theorem elevenFourths_ne_top : (11 / 4 : ℝ≥0∞) ≠ ⊤ :=
  ENNReal.div_ne_top (by norm_num) (by norm_num)

instance instFactOneLeElevenFourthsPF : Fact ((1 : ℝ≥0∞) ≤ 11 / 4) :=
  ⟨one_lt_elevenFourths.le⟩

open Classical in
/-- **The Leray complement `(I - ℙ)G` on `L^{11/4}(ℝ³; ℝ³)`** (source 5245-5281: `∇p_V =
-(I-ℙ)(V·∇V)`, `∇(p_raw - p_lift) = -(I-ℙ)F_raw`), with `ℙ = RieszLp.lerayLp (11/4)` the Leray
projection `𝔓 = I + R⊗R` of `Lib/LerayLp/Leray.lean`; `0` if `G ∉ L^{11/4}`. -/
def lerayComp114 (G : Space → Space) : Space → Space :=
  if h : MemLp G (11 / 4) volume then
    ⇑(h.toLp G - RieszLp.lerayLp (11 / 4) one_lt_elevenFourths elevenFourths_ne_top (h.toLp G))
  else 0

/-- **The residual `F_R` of the raw ring lift** of the level's actual train (source 1205-1225,
Proposition `sct:lift`; 1263: `F_R = s^{3/2}r`): the similarity residual `PartIIa.ringResidual` of
the stream and pressure profiles of the train with `R = ε⁻¹` (velocity `U_raw`, pressure
`p_raw = (R/r)²p`, which in the similarity variables is `liftP`).  Off the axis
`F_R = D₀U_raw + U_raw·∇U_raw + ∇p_lift` (`IIb.RingResidualCartesianNS`, `IIb.RawIsRingLift`). -/
def rawResidF (Pl : PlanarData) (L : ReturnLevel) : ℝ → Space → Space :=
  UnforcedLeray.Short.PartIIa.ringResidual (L.params Pl).R L.ν
    (UnforcedLeray.Short.IIb.trainStream (L.params Pl))
    (UnforcedLeray.Short.IIb.trainPressure (L.params Pl))

/-- **The repair convection change** `U·∇U - V·∇V` (source 5254-5257: the repair convection
`V·∇r_b + r_b·∇V + r_b·∇r_b`, `U = V + r_b`). -/
def convChg (L : ReturnLevel) (τ : ℝ) (y : Space) : Space :=
  fderiv ℝ (L.U τ) y (L.U τ y) - fderiv ℝ (L.V τ) y (L.V τ y)

/-- **The entrance equation source** `D₀(V - U_raw) + V·∇V - U_raw·∇U_raw` (source 5277-5279,
2346-2347, 2388-2390: the entrance convection terms; "its complete equation source is in `Y_p`").
`D₀ = physDmu ν 0`; `V - U_raw = E_εα` is solenoidal, so `(I-ℙ)D₀(V - U_raw) = 0` and the
term does not change the Leray complement. -/
def entSrc (Pl : PlanarData) (L : ReturnLevel) (τ : ℝ) (y : Space) : Space :=
  physDmu L.ν 0 (fun t y' => L.V t y' - rawU Pl L t y') τ y +
    (fderiv ℝ (L.V τ) y (L.V τ y) - fderiv ℝ (rawU Pl L τ) y (rawU Pl L τ y))

/-- The force whose Leray complement is `-(∇p - ∇p_lift)`: `convChg + entSrc + F_R`
(source 5245-5281). -/
def presForce (Pl : PlanarData) (L : ReturnLevel) (τ : ℝ) (y : Space) : Space :=
  convChg L τ y + entSrc Pl L τ y + rawResidF Pl L τ y

/-! ## 2. The general leaves -/

/-- **`I - ℙ` is bounded on `L^{11/4}(ℝ³; ℝ³)`** (source 5245-5281: "`(I-ℙ)` bounded on
`L^{11/4}`"; `RieszLp.eLpNorm_lerayLp_toLp_le`, unit B0414). -/
def LerayComp114Bound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ G : Space → Space, MemLp G (11 / 4) volume →
    eLpNorm (lerayComp114 G) (11 / 4) volume ≤ ENNReal.ofReal C * eLpNorm G (11 / 4) volume

/-- **The ring-chart form of the `Y_r` norm** (source 2681-2688: "the physical space Jacobian after
azimuthal integration is `πR²s^{-5/2}ds dη` and normalized phase becomes `dq/c`";
`Axi.phaseAvg_ringChart`, `Axi.lintegral_ageμ`): for a `P`-periodic (`P = 2c/R`) axisymmetric
scalar `f`, measurable off the axis, `‖ringRead R f‖_{L^r(ringPhysμ R c)} = ‖f‖_{Y_r}`. -/
def RingReadPhaseLr : Prop :=
  ∀ (R c P r : ℝ) (f : ℝ → Space → ℝ), 0 < R → 0 < c → P = 2 * c / R → 0 < r →
    Measurable (axisZero f) → (∀ τ y, f (τ + P) y = f τ y) → IsAxiScalar f →
    eLpNorm (ringRead R f) (ENNReal.ofReal r) (ringPhysμ R c) =
      phaseLr P r (fun x => f x.1 x.2)

/-! ## 3. The leaves at one level (`R = ε⁻¹`, `c = ν⁻²`, period `P = 2εc`) -/

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)

/-- **The pressure identity** (source 5245-5260, 5272-5281, 1205-1225, 4139-4141): at every phase
`τ` the force `convChg + entSrc + F_R` is measurable, and if it lies in `L^{11/4}` then
`∇p - ∇p_lift = -(I-ℙ)(convChg + entSrc + F_R)` a.e. (`IsExactProfile.equation` minus the raw
equation `F_R = D₀U_raw + U_raw·∇U_raw + ∇p_lift`; `D₀(U - U_raw) = D₀r_b + D₀(V - U_raw)` is
solenoidal, `∇(p - p_lift)` is a gradient). -/
def PresHelmholtzAt : Prop :=
  ∀ τ : ℝ, AEStronglyMeasurable (presForce Pl L τ) volume ∧
    (MemLp (presForce Pl L τ) (11 / 4) volume →
      (fun y => physGrad (L.pres τ) y - physGrad (liftP L τ) y) =ᵐ[volume]
        fun y => -lerayComp114 (presForce Pl L τ) y)

/-- **The pressure-change density is measurable off the axis, `P`-periodic and axisymmetric**
(source 4139-4141: `p` smooth and `P`-periodic, `IsExactProfile`; 1205-1225, 1217: `p_lift = s·p_cyl`
smooth off the axis and `P`-periodic, `p_cyl` `c`-periodic in `q`; 2031, 4144-4145: the
background is axisymmetric, so `|∇p - ∇p_lift|` is rotation invariant). -/
def PresChgPhysAt : Prop :=
  Measurable (axisZero fun τ => presChgDens (L.pres τ) (liftP L τ)) ∧
    (∀ τ y, presChgDens (L.pres (τ + 2 * L.ε * cOf L.ν)) (liftP L (τ + 2 * L.ε * cOf L.ν)) y =
      presChgDens (L.pres τ) (liftP L τ) y) ∧
    IsAxiScalar fun τ => presChgDens (L.pres τ) (liftP L τ)

/-- **`|convChg + entSrc + F_R|` is measurable off the axis, `P`-periodic and axisymmetric** (source
1205-1225: `U_raw`, `F_R` smooth off the axis, discretely self-similar of period `2c/R`, and
axisymmetric without swirl, `IIb.RingResidualAxisymmetric`; 4139-4141, 2031: `U`). -/
def PresForcePhysAt : Prop :=
  Measurable (axisZero fun τ y => ‖presForce Pl L τ y‖) ∧
    (∀ τ y, ‖presForce Pl L (τ + 2 * L.ε * cOf L.ν) y‖ = ‖presForce Pl L τ y‖) ∧
    IsAxiScalar fun τ y => ‖presForce Pl L τ y‖

/-- **The raw residual bound** (source 1219-1225, `sct:residual-bound` at `p = 11/4`:
`‖F_R‖_{C_per W^{1,p}(ℝ³)} ≤ P_p ε^{1-2/p} = Pε^{3/11}`; `PartIIa.RingResidualBound`,
`IIb.RingResidualAxisymmetric`): `|F_R|` is measurable off the axis, `P`-periodic, axisymmetric, and
`sup_τ ‖F_R(τ)‖_{L^{11/4}} ≤ C ν^{-k} ε^{3/11}`. -/
def RawResidAt (C : ℝ) (k : ℕ) : Prop :=
  Measurable (axisZero fun τ y => ‖rawResidF Pl L τ y‖) ∧
    (∀ τ y, ‖rawResidF Pl L (τ + 2 * L.ε * cOf L.ν) y‖ = ‖rawResidF Pl L τ y‖) ∧
    IsAxiScalar (fun τ y => ‖rawResidF Pl L τ y‖) ∧
    ∀ τ, eLpNorm (rawResidF Pl L τ) (11 / 4) volume ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ (3 / 11 : ℝ))

/-- **The entrance source bound** (source 2388-2390, 5277-5279: the quadratic inlet source has the
bound `P_ν|α|²`, the equation source of `E_εα` the bound `P_ν|α|` in `Y_{11/4}` — "these assertions
compare sources, never the nonintegrable inlet states" — with `|α| ≤ P_ν e^{m₀/ν}ε ≤ P_νρ`,
2519-2520): `|entSrc|` is measurable off the axis, `P`-periodic, axisymmetric, and
`sup_τ ‖entSrc(τ)‖_{L^{11/4}} ≤ C ν^{-k} ρ`, `ρ = ε^{3/11}e^{m₀/ν}`. -/
def EntSrcAt (K : ReturnConsts) (C : ℝ) (k : ℕ) : Prop :=
  Measurable (axisZero fun τ y => ‖entSrc Pl L τ y‖) ∧
    (∀ τ y, ‖entSrc Pl L (τ + 2 * L.ε * cOf L.ν) y‖ = ‖entSrc Pl L τ y‖) ∧
    IsAxiScalar (fun τ y => ‖entSrc Pl L τ y‖) ∧
    ∀ τ, eLpNorm (entSrc Pl L τ) (11 / 4) volume ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * rhoRep K L)

/-- **The gradient of the exact background is bounded** at the chart points (source 1219-1220: the
raw lift has globally bounded fixed spatial derivatives; 2697-2713 and `background:eq:2.28`: the
inlet columns `E_εα`, `|α| ≤ ρ_b`; 5134-5139: `‖r_b‖_{W^{1,∞}} ≤ P_νρ`): `|∇U| ≤ C ν^{-k}`. -/
def GradUAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ p : Chart, 0 < p.1 →
    ‖fderiv ℝ (L.U (NearInst.chartTau L.ε⁻¹ p)) (NearInst.chartY L.ε⁻¹ p)‖ ≤ C * L.ν⁻¹ ^ k

end Regime

namespace SeqData

variable (D : SeqData)

/-- The pressure identity along the sequence. -/
def PresHelmholtz : Prop := ∀ᶠ n : ℕ in atTop, PresHelmholtzAt D.Pl (D.level n)

/-- The regularity of the pressure-change density along the sequence. -/
def PresChgPhys : Prop := ∀ᶠ n : ℕ in atTop, PresChgPhysAt (D.level n)

/-- The regularity of `|convChg + F_R|` along the sequence. -/
def PresForcePhys : Prop := ∀ᶠ n : ℕ in atTop, PresForcePhysAt D.Pl (D.level n)

/-- The raw residual bound along the sequence. -/
def RawResid : Prop := ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, RawResidAt D.Pl (D.level n) C k

/-- The entrance source bound along the sequence. -/
def EntSrc : Prop := ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, EntSrcAt D.Pl (D.level n) D.K C k

/-- The gradient bound of the exact background along the sequence. -/
def ExactGradBound : Prop := ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, GradUAt (D.level n) C k

end SeqData

/-! ## 4. Elementary lemmas -/

theorem pf_eq_sum_coord (v : Space) : v = ∑ j : Fin 3, v j • coordinateVector j := by
  ext i
  simp [coordinateVector, Pi.single_apply, mul_ite, Finset.sum_ite_eq']

/-- `‖T‖ ≤ Σ_j ‖T e_j‖`. -/
theorem pf_opNorm_le_sum (T : Space →L[ℝ] Space) :
    ‖T‖ ≤ ∑ j : Fin 3, ‖T (coordinateVector j)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun j _ => norm_nonneg _)
    fun v => ?_
  conv_lhs => rw [pf_eq_sum_coord v]
  rw [map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [map_smul, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v j) (norm_nonneg _)

/-- **The convection change, pointwise** (algebra): `|∇U₁[U₁] - ∇U₂[U₂]| ≤
(|∇U₁| + |U₂|)(|U₁ - U₂| + |DU₁ - DU₂|) ≤ (|∇U₁| + |U₂|) coefChgDens U₁ U₂`. -/
theorem norm_convChg_le (U₁ U₂ : Space → Space) (y : Space) :
    ‖fderiv ℝ U₁ y (U₁ y) - fderiv ℝ U₂ y (U₂ y)‖ ≤
      (‖fderiv ℝ U₁ y‖ + ‖U₂ y‖) * coefChgDens U₁ U₂ y := by
  set A := fderiv ℝ U₁ y
  set B := fderiv ℝ U₂ y
  have hsplit : A (U₁ y) - B (U₂ y) = A (U₁ y - U₂ y) + (A - B) (U₂ y) := by
    rw [map_sub, ContinuousLinearMap.sub_apply]
    abel
  have hAB : ‖A - B‖ ≤ ‖fderiv ℝ U₁ y - fderiv ℝ U₂ y‖ := le_rfl
  set S := ‖fderiv ℝ U₁ y - fderiv ℝ U₂ y‖
  have hS0 := norm_nonneg (fderiv ℝ U₁ y - fderiv ℝ U₂ y)
  have hT0 := norm_nonneg (secondJet U₁ y - secondJet U₂ y)
  have hD : ‖U₁ y - U₂ y‖ + S ≤ coefChgDens U₁ U₂ y := by
    unfold coefChgDens
    linarith
  have hA0 := norm_nonneg A
  have hu0 := norm_nonneg (U₂ y)
  have hd0 := norm_nonneg (U₁ y - U₂ y)
  calc ‖A (U₁ y) - B (U₂ y)‖ ≤ ‖A (U₁ y - U₂ y)‖ + ‖(A - B) (U₂ y)‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ ‖A‖ * ‖U₁ y - U₂ y‖ + ‖A - B‖ * ‖U₂ y‖ :=
        add_le_add (A.le_opNorm _) ((A - B).le_opNorm _)
    _ ≤ ‖A‖ * ‖U₁ y - U₂ y‖ + S * ‖U₂ y‖ := by gcongr
    _ ≤ (‖A‖ + ‖U₂ y‖) * (‖U₁ y - U₂ y‖ + S) := by nlinarith
    _ ≤ (‖A‖ + ‖U₂ y‖) * coefChgDens U₁ U₂ y :=
        mul_le_mul_of_nonneg_left hD (by positivity)

theorem pf_e114 : (11 / 4 : ℝ≥0∞) = ENNReal.ofReal (11 / 4) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

theorem pf_toReal114 : (11 / 4 : ℝ≥0∞).toReal = 11 / 4 := by
  rw [pf_e114, ENNReal.toReal_ofReal (by norm_num)]

theorem pf_ne_zero114 : (11 / 4 : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans one_lt_elevenFourths).ne'

/-- `∫ ‖f‖^{11/4} = ‖f‖_{11/4}^{11/4}`. -/
theorem pf_lintegral_enorm_rpow {E : Type*} [NormedAddCommGroup E] (f : Space → E) :
    ∫⁻ y, ‖f y‖ₑ ^ (11 / 4 : ℝ) = eLpNorm f (11 / 4) volume ^ (11 / 4 : ℝ) := by
  rw [eLpNorm_eq_eLpNorm' pf_ne_zero114 elevenFourths_ne_top, pf_toReal114,
    lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num)]

theorem pf_lintegral_ofReal_norm {E : Type*} [NormedAddCommGroup E] (f : Space → E) :
    ∫⁻ y, ENNReal.ofReal |‖f y‖| ^ (11 / 4 : ℝ) = eLpNorm f (11 / 4) volume ^ (11 / 4 : ℝ) := by
  rw [← pf_lintegral_enorm_rpow]
  congr 1
  funext y
  rw [abs_norm, ofReal_norm]

/-- A phase-uniform `L^{11/4}` bound bounds the `Y_{11/4}` norm. -/
theorem pf_phaseLr_le_of_sup {P B : ℝ} (hP : 0 < P) (F : ℝ → Space → Space)
    (h : ∀ τ, eLpNorm (F τ) (11 / 4) volume ≤ ENNReal.ofReal B) :
    phaseLr P (11 / 4) (fun x => ‖F x.1 x.2‖) ≤ ENNReal.ofReal B := by
  unfold phaseLr
  have hin : ∀ t : ℝ, ∫⁻ y, ENNReal.ofReal |‖F t y‖| ^ (11 / 4 : ℝ) ≤
      ENNReal.ofReal B ^ (11 / 4 : ℝ) := by
    intro t
    rw [pf_lintegral_ofReal_norm]
    exact ENNReal.rpow_le_rpow (h t) (by norm_num)
  calc (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
        ENNReal.ofReal |‖F (t, y).1 (t, y).2‖| ^ (11 / 4 : ℝ)) ^ (1 / (11 / 4 : ℝ))
      ≤ (ENNReal.ofReal P⁻¹ * ∫⁻ _ in Ioc (0 : ℝ) P, ENNReal.ofReal B ^ (11 / 4 : ℝ)) ^
          (1 / (11 / 4 : ℝ)) :=
        ENNReal.rpow_le_rpow (mul_le_mul_right (lintegral_mono fun t => hin t) _) (by norm_num)
    _ = ENNReal.ofReal B := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm (ENNReal.ofReal B ^ _),
          ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hP.le), inv_mul_cancel₀ hP.ne',
          ENNReal.ofReal_one, one_mul, one_div, ENNReal.rpow_rpow_inv (by norm_num)]

theorem pf_measurable_chartTau (R : ℝ) : Measurable (NearInst.chartTau R) := by
  unfold NearInst.chartTau
  exact ((measurable_const.mul (measurable_fst.comp measurable_snd)).div_const _).add
    (Real.measurable_log.comp measurable_fst)

theorem pf_measurable_chartY (R : ℝ) : Measurable (NearInst.chartY R) := by
  unfold NearInst.chartY
  have : Measurable fun p : Chart =>
      (![R / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1] : Fin 3 → ℝ) := by
    refine measurable_pi_lambda _ fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp this

theorem pf_chartY_not_mem_axis {R : ℝ} (hR : R ≠ 0) {p : Chart} (hp : 0 < p.1) :
    NearInst.chartY R p ∉ axis := by
  intro h
  have h0 : (NearInst.chartY R p) 0 = R / Real.sqrt p.1 := by simp [NearInst.chartY]
  have hne : R / Real.sqrt p.1 ≠ 0 := div_ne_zero hR (Real.sqrt_pos.2 hp).ne'
  exact hne (h0 ▸ h.1)

theorem pf_ae_ringPhysμ_pos (R c : ℝ) (hc : 0 < c) : ∀ᵐ p ∂ringPhysμ R c, 0 < p.1 := by
  unfold ringPhysμ
  refine Measure.ae_smul_measure ?_ _
  filter_upwards [ae_ageμ_mem hc (-5 / 2)] with p hp using hp.1

/-- The ring read of a density measurable off the axis is a.e. strongly measurable. -/
theorem pf_aesm_ringRead {R c : ℝ} (hR : R ≠ 0) (hc : 0 < c) {f : ℝ → Space → ℝ}
    (hf : Measurable (axisZero f)) : AEStronglyMeasurable (ringRead R f) (ringPhysμ R c) := by
  have hm : Measurable fun p : Chart =>
      axisZero f (NearInst.chartTau R p, NearInst.chartY R p) :=
    hf.comp ((pf_measurable_chartTau R).prodMk (pf_measurable_chartY R))
  refine hm.aestronglyMeasurable.congr ?_
  filter_upwards [pf_ae_ringPhysμ_pos R c hc] with p hp
  have hax := pf_chartY_not_mem_axis hR hp
  classical
  simp only [axisZero, ringRead, if_neg hax]

/-! ## 4a. The two general leaves, proved -/

/-- **`I - ℙ` is bounded on `L^{11/4}`**, with constant `1 + ‖ℙ‖` (`RieszLp.lerayLp`). -/
theorem lerayComp114Bound : LerayComp114Bound := by
  set T := RieszLp.lerayLp (11 / 4) one_lt_elevenFourths elevenFourths_ne_top with hT
  refine ⟨1 + ‖T‖, by positivity, fun G hG => ?_⟩
  set x := hG.toLp G with hx
  have e : lerayComp114 G = ⇑(x - T x) := by
    simp only [lerayComp114, dif_pos hG]
    rfl
  have eG : eLpNorm G (11 / 4) volume = ‖x‖ₑ := by
    rw [Lp.enorm_def]
    exact (eLpNorm_congr_ae hG.coeFn_toLp).symm
  rw [e, ← Lp.enorm_def, eG, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖x - T x‖ ≤ ‖x‖ + ‖T x‖ := norm_sub_le _ _
    _ ≤ ‖x‖ + ‖T‖ * ‖x‖ := by gcongr; exact T.le_opNorm x
    _ = (1 + ‖T‖) * ‖x‖ := by ring

theorem pf_chartTau_chart {R : ℝ} (hR : 0 < R) (τ : ℝ) (y : Space) :
    NearInst.chartTau R (chart R τ y) = τ := by
  simp only [NearInst.chartTau, chart, phase]
  field_simp
  ring

theorem pf_chartY_chart {R : ℝ} (hR : 0 < R) (τ : ℝ) {y : Space} (hy : y ∉ axis) :
    NearInst.chartY R (chart R τ y) = merPt y := by
  have hs := sqrt_age hR hy
  have hϱ := ϱ_pos hy
  simp only [NearInst.chartY, chart, merPt, hs]
  congr 1
  funext i
  fin_cases i <;> simp [Axi.trans] <;> field_simp

theorem pf_merPt_not_mem_axis {y : Space} (hy : y ∉ axis) : merPt y ∉ axis := by
  intro h
  have h0 : (merPt y) 0 = ϱ y := by simp [merPt]
  exact (ϱ_pos hy).ne' (h0 ▸ h.1)

/-- **The ring-chart form of the `Y_r` norm** (source 2681-2688; `Axi.phaseAvg_ringChart`). -/
theorem ringReadPhaseLr : RingReadPhaseLr := by
  intro R c P r f hR hc hP hr hf hper hax
  classical
  have hP0 : 0 < P := by rw [hP]; positivity
  set G : ℝ × (ℝ × ℝ) → ℝ≥0∞ := fun p =>
    ‖axisZero f (NearInst.chartTau R p, NearInst.chartY R p)‖ₑ ^ r with hG
  have hGm : Measurable G :=
    (hf.comp ((pf_measurable_chartTau R).prodMk (pf_measurable_chartY R))).enorm.pow_const r
  have hGper : ∀ s q η, G (s, (q + c, η)) = G (s, (q, η)) := by
    intro s q η
    have hτ : NearInst.chartTau R (s, (q + c, η)) = NearInst.chartTau R (s, (q, η)) + P := by
      simp only [NearInst.chartTau]
      rw [hP]
      field_simp
      ring
    have hY : NearInst.chartY R (s, (q + c, η)) = NearInst.chartY R (s, (q, η)) := rfl
    simp only [hG]
    rw [hτ, hY]
    simp only [axisZero, hper]
  have hr' : ENNReal.ofReal r ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero]
    linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hr.le]
  unfold phaseLr
  congr 1
  have hL : ∫⁻ p, ‖ringRead R f p‖ₑ ^ r ∂ringPhysμ R c = ∫⁻ p, G p ∂ringPhysμ R c := by
    refine lintegral_congr_ae ?_
    filter_upwards [pf_ae_ringPhysμ_pos R c hc] with p hp
    simp only [hG, axisZero, ringRead, if_neg (pf_chartY_not_mem_axis hR.ne' hp)]
  rw [hL, ringPhysμ, lintegral_smul_measure, lintegral_ageμ hc _ hGm, smul_eq_mul,
    show (-5 / 2 : ℝ) = -(5 / 2 : ℝ) by norm_num, ← phaseAvg_ringChart hR hc hP G hGm hGper,
    ENNReal.ofReal_inv_of_pos hP0]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioc fun τ _ => ?_
  refine lintegral_congr_ae ?_
  filter_upwards [ae_not_mem_axis] with y hy
  have h1 := pf_chartTau_chart hR τ y
  have h2 := pf_chartY_chart hR τ hy
  have hm := pf_merPt_not_mem_axis hy
  change ‖axisZero f (NearInst.chartTau R (chart R τ y), NearInst.chartY R (chart R τ y))‖ₑ ^ r =
    ENNReal.ofReal |f τ y| ^ r
  rw [h1, h2]
  simp only [axisZero, if_neg hm, ← hax τ y, Real.enorm_eq_ofReal_abs]

/-! ## 5. Constants -/

section Mono

variable {Pl : PlanarData} {L : ReturnLevel}

theorem RawResidAt.mono {C C' : ℝ} {k k' : ℕ} (h : RawResidAt Pl L C k) (hν1 : L.ν ≤ 1)
    (hC : C ≤ C') (hC' : 0 ≤ C') (hk : k ≤ k') : RawResidAt Pl L C' k' := by
  have hε := L.ε_pos
  exact ⟨h.1, h.2.1, h.2.2.1, fun τ => (h.2.2.2 τ).trans (ENNReal.ofReal_le_ofReal
    (pnu_le_pnu L.ν_pos hν1 (by positivity) hC hC' hk))⟩

theorem EntSrcAt.mono {K : ReturnConsts} {C C' : ℝ} {k k' : ℕ} (h : EntSrcAt Pl L K C k)
    (hν1 : L.ν ≤ 1) (hC : C ≤ C') (hC' : 0 ≤ C') (hk : k ≤ k') : EntSrcAt Pl L K C' k' :=
  ⟨h.1, h.2.1, h.2.2.1, fun τ => (h.2.2.2 τ).trans (ENNReal.ofReal_le_ofReal
    (pnu_le_pnu L.ν_pos hν1 (rhoRep_nonneg K L) hC hC' hk))⟩

theorem GradUAt.mono {C C' : ℝ} {k k' : ℕ} (h : GradUAt L C k) (hν1 : L.ν ≤ 1)
    (hC : C ≤ C') (hC' : 0 ≤ C') (hk : k ≤ k') : GradUAt L C' k' := by
  intro p hp
  have := pnu_le_pnu L.ν_pos hν1 zero_le_one hC hC' hk
  simp only [mul_one] at this
  exact (h p hp).trans this

end Mono

/-! ## 6. The reduction -/

section Reduction

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)

/-- **`presFlatBoundAt_of`**: at one level, the pressure identity, `I - ℙ` bounded on `L^{11/4}`,
the chart form of `Y_{11/4}`, the coefficient change, the gradient bound and the raw residual bound
give `‖∇p - ∇p_lift‖_{Y_{11/4}} ≤ C_L(2C² + 2C) ν^{-2k} ρ` (source 5245-5281). -/
theorem presFlatBoundAt_of (hν1 : L.ν ≤ 1) (hm0 : 0 ≤ K.m0) {C : ℝ} (hC : 0 ≤ C) {k : ℕ}
    {CL : ℝ} (hCL : 0 < CL)
    (hLB : ∀ G : Space → Space, MemLp G (11 / 4) volume →
      eLpNorm (lerayComp114 G) (11 / 4) volume ≤ ENNReal.ofReal CL * eLpNorm G (11 / 4) volume)
    (hconv : RingReadPhaseLr) (hH : PresHelmholtzAt Pl L) (h1 : PresChgPhysAt L)
    (h2 : PresForcePhysAt Pl L) (hR : RawResidAt Pl L C k) (hE : EntSrcAt Pl L K C k)
    (hCC : CoefChgAt Pl K L C k) (hG : GradUAt L C k) :
    eLpNorm (ringRead L.ε⁻¹ fun τ => presChgDens (L.pres τ) (liftP L τ)) (11 / 4)
        (ringPhysμ L.ε⁻¹ (cOf L.ν)) ≤
      ENNReal.ofReal (CL * (2 * C ^ 2 + 2 * C) * L.ν⁻¹ ^ (2 * k) * rhoRep K L) := by
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hR0 : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hP : 2 * L.ε * cOf L.ν = 2 * cOf L.ν / L.ε⁻¹ := by
    rw [div_inv_eq_mul]; ring
  have hP0 : 0 < 2 * L.ε * cOf L.ν := by positivity
  have hr : (0 : ℝ) < 11 / 4 := by norm_num
  set f₁ : ℝ → Space → ℝ := fun τ => presChgDens (L.pres τ) (liftP L τ) with hf₁
  set f₂ : ℝ → Space → ℝ := fun τ y => ‖presForce Pl L τ y‖ with hf₂
  set f₃ : ℝ → Space → ℝ := fun τ y => ‖rawResidF Pl L τ y‖ with hf₃
  set f₄ : ℝ → Space → ℝ := fun τ y => ‖entSrc Pl L τ y‖ with hf₄
  set μ := ringPhysμ L.ε⁻¹ (cOf L.ν) with hμ
  set P := 2 * L.ε * cOf L.ν with hPdef
  -- Step 1: the chart norm of the pressure change is its `Y_{11/4}` norm
  have s1 : eLpNorm (ringRead L.ε⁻¹ f₁) (11 / 4) μ = phaseLr P (11 / 4) (fun x => f₁ x.1 x.2) := by
    rw [pf_e114]
    exact hconv L.ε⁻¹ (cOf L.ν) P (11 / 4) f₁ hR0 hc hP hr h1.1 h1.2.1 h1.2.2
  -- Step 2: phasewise `I - ℙ` bound
  have hin : ∀ t : ℝ, ∫⁻ y, ENNReal.ofReal |f₁ t y| ^ (11 / 4 : ℝ) ≤
      ENNReal.ofReal CL ^ (11 / 4 : ℝ) * ∫⁻ y, ENNReal.ofReal |f₂ t y| ^ (11 / 4 : ℝ) := by
    intro t
    obtain ⟨hmeas, hid⟩ := hH t
    have eG : ∫⁻ y, ENNReal.ofReal |f₂ t y| ^ (11 / 4 : ℝ) =
        eLpNorm (presForce Pl L t) (11 / 4) volume ^ (11 / 4 : ℝ) :=
      pf_lintegral_ofReal_norm (presForce Pl L t)
    by_cases hm : MemLp (presForce Pl L t) (11 / 4) volume
    · have hae := hid hm
      have e1 : ∫⁻ y, ENNReal.ofReal |f₁ t y| ^ (11 / 4 : ℝ) =
          eLpNorm (lerayComp114 (presForce Pl L t)) (11 / 4) volume ^ (11 / 4 : ℝ) := by
        rw [← pf_lintegral_enorm_rpow]
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with y hy
        simp only [hf₁, presChgDens]
        rw [hy, norm_neg, abs_norm, ofReal_norm]
      rw [e1, eG, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      exact ENNReal.rpow_le_rpow (hLB _ hm) (by norm_num)
    · have htop : eLpNorm (presForce Pl L t) (11 / 4) volume = ⊤ := by
        by_contra hne
        exact hm ⟨hmeas, lt_top_iff_ne_top.2 hne⟩
      rw [eG, htop, ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top]
      · exact le_top
      · exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hCL) ENNReal.ofReal_ne_top).ne'
  have hCLr : ENNReal.ofReal CL ^ (11 / 4 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have s2 : phaseLr P (11 / 4) (fun x => f₁ x.1 x.2) ≤
      ENNReal.ofReal CL * phaseLr P (11 / 4) (fun x => f₂ x.1 x.2) := by
    unfold phaseLr
    calc (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
          ENNReal.ofReal |f₁ (t, y).1 (t, y).2| ^ (11 / 4 : ℝ)) ^ (1 / (11 / 4 : ℝ))
        ≤ (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ENNReal.ofReal CL ^ (11 / 4 : ℝ) *
            ∫⁻ y : Space, ENNReal.ofReal |f₂ t y| ^ (11 / 4 : ℝ)) ^ (1 / (11 / 4 : ℝ)) :=
          ENNReal.rpow_le_rpow (mul_le_mul_right (lintegral_mono fun t => hin t) _)
            (by norm_num)
      _ = ENNReal.ofReal CL * (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
            ENNReal.ofReal |f₂ (t, y).1 (t, y).2| ^ (11 / 4 : ℝ)) ^ (1 / (11 / 4 : ℝ)) := by
          rw [lintegral_const_mul' _ _ hCLr, mul_left_comm,
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), one_div,
            ENNReal.rpow_rpow_inv (by norm_num)]
  -- Step 3: back to the chart
  have s3 : phaseLr P (11 / 4) (fun x => f₂ x.1 x.2) = eLpNorm (ringRead L.ε⁻¹ f₂) (11 / 4) μ := by
    rw [pf_e114]
    exact (hconv L.ε⁻¹ (cOf L.ν) P (11 / 4) f₂ hR0 hc hP hr h2.1 h2.2.1 h2.2.2).symm
  have s3' : eLpNorm (ringRead L.ε⁻¹ f₃) (11 / 4) μ ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ (3 / 11 : ℝ)) := by
    rw [pf_e114, hconv L.ε⁻¹ (cOf L.ν) P (11 / 4) f₃ hR0 hc hP hr hR.1 hR.2.1 hR.2.2.1]
    exact pf_phaseLr_le_of_sup hP0 (rawResidF Pl L) hR.2.2.2
  have s3'' : eLpNorm (ringRead L.ε⁻¹ f₄) (11 / 4) μ ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * rhoRep K L) := by
    rw [pf_e114, hconv L.ε⁻¹ (cOf L.ν) P (11 / 4) f₄ hR0 hc hP hr hE.1 hE.2.1 hE.2.2.1]
    exact pf_phaseLr_le_of_sup hP0 (entSrc Pl L) hE.2.2.2
  -- Step 4: the pointwise bound and Minkowski in the chart
  set Pν : ℝ := C * L.ν⁻¹ ^ k with hPν
  have hPν0 : 0 ≤ Pν := by positivity
  set A : ℝ := 2 * Pν with hA
  have hA0 : 0 ≤ A := by positivity
  set a : Chart → ℝ := ringRead L.ε⁻¹ fun τ => coefChgDens (L.U τ) (L.V τ) with ha
  set b : Chart → ℝ := ringRead L.ε⁻¹ f₃ with hb
  set e : Chart → ℝ := ringRead L.ε⁻¹ f₄ with he
  have hpt : ∀ᵐ p ∂μ, ‖ringRead L.ε⁻¹ f₂ p‖ ≤ ‖A * a p + b p + e p‖ := by
    filter_upwards [pf_ae_ringPhysμ_pos L.ε⁻¹ (cOf L.ν) hc] with p hp
    set τ := NearInst.chartTau L.ε⁻¹ p
    set y := NearInst.chartY L.ε⁻¹ p
    have hU := hCC.2.2 p hp
    have hDU := hG p hp
    have hV : ‖L.V τ y‖ ≤ Pν := by
      have := norm_nonneg (L.U τ y)
      have := norm_nonneg (rawU Pl L τ y)
      linarith
    have hcoef0 : 0 ≤ coefChgDens (L.U τ) (L.V τ) y := coefChgDens_nonneg _ _ _
    have hconvb : ‖convChg L τ y‖ ≤ A * coefChgDens (L.U τ) (L.V τ) y :=
      (norm_convChg_le (L.U τ) (L.V τ) y).trans
        (mul_le_mul_of_nonneg_right (by rw [hA]; linarith) hcoef0)
    have hb0 : 0 ≤ ‖rawResidF Pl L τ y‖ := norm_nonneg _
    have he0 : 0 ≤ ‖entSrc Pl L τ y‖ := norm_nonneg _
    have e2 : ringRead L.ε⁻¹ f₂ p = ‖presForce Pl L τ y‖ := rfl
    have ea : a p = coefChgDens (L.U τ) (L.V τ) y := rfl
    have eb : b p = ‖rawResidF Pl L τ y‖ := rfl
    have ee : e p = ‖entSrc Pl L τ y‖ := rfl
    rw [e2, ea, eb, ee, norm_norm, Real.norm_of_nonneg (by positivity)]
    calc ‖presForce Pl L τ y‖ ≤ ‖convChg L τ y‖ + ‖entSrc Pl L τ y‖ + ‖rawResidF Pl L τ y‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ A * coefChgDens (L.U τ) (L.V τ) y + ‖rawResidF Pl L τ y‖ + ‖entSrc Pl L τ y‖ := by
          linarith
  have h114 : (1 : ℝ≥0∞) ≤ 11 / 4 := one_lt_elevenFourths.le
  have hbm : AEStronglyMeasurable b μ := pf_aesm_ringRead hR0.ne' hc hR.1
  have hem : AEStronglyMeasurable e μ := pf_aesm_ringRead hR0.ne' hc hE.1
  have s4 : eLpNorm (ringRead L.ε⁻¹ f₂) (11 / 4) μ ≤
      ENNReal.ofReal A * ENNReal.ofReal (Pν * rhoRep K L) +
        ENNReal.ofReal (Pν * L.ε ^ (3 / 11 : ℝ)) + ENNReal.ofReal (Pν * rhoRep K L) := by
    have hsm : (fun p => A * a p) = A • a := by funext p; rfl
    calc eLpNorm (ringRead L.ε⁻¹ f₂) (11 / 4) μ
        ≤ eLpNorm (fun p => A * a p + b p + e p) (11 / 4) μ := eLpNorm_mono_ae hpt
      _ ≤ eLpNorm (fun p => A * a p + b p) (11 / 4) μ + eLpNorm e (11 / 4) μ :=
          eLpNorm_add_le ((hCC.1.const_mul A).add hbm) hem h114
      _ ≤ (eLpNorm (fun p => A * a p) (11 / 4) μ + eLpNorm b (11 / 4) μ) +
            eLpNorm e (11 / 4) μ :=
          add_le_add (eLpNorm_add_le (hCC.1.const_mul A) hbm h114) le_rfl
      _ = (ENNReal.ofReal A * eLpNorm a (11 / 4) μ + eLpNorm b (11 / 4) μ) +
            eLpNorm e (11 / 4) μ := by
          rw [hsm, eLpNorm_const_smul, Real.enorm_eq_ofReal hA0]
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal (Pν * rhoRep K L) +
            ENNReal.ofReal (Pν * L.ε ^ (3 / 11 : ℝ)) + ENNReal.ofReal (Pν * rhoRep K L) := by
          exact add_le_add (add_le_add (mul_le_mul_right hCC.2.1 _) s3') s3''
  -- Step 5: the constants
  have hρ0 := rhoRep_nonneg K L
  have hx1 : 0 ≤ Pν * rhoRep K L := mul_nonneg hPν0 hρ0
  have hx2 : 0 ≤ Pν * L.ε ^ (3 / 11 : ℝ) := by positivity
  have hreal : CL * (A * (Pν * rhoRep K L) + Pν * L.ε ^ (3 / 11 : ℝ) + Pν * rhoRep K L) ≤
      CL * (2 * C ^ 2 + 2 * C) * L.ν⁻¹ ^ (2 * k) * rhoRep K L := by
    have h1ν : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
    have hpk : L.ν⁻¹ ^ k ≤ L.ν⁻¹ ^ (2 * k) := pow_le_pow_right₀ h1ν (by omega)
    have hpk0 : 0 ≤ L.ν⁻¹ ^ k := by positivity
    have hsq : L.ν⁻¹ ^ (2 * k) = L.ν⁻¹ ^ k * L.ν⁻¹ ^ k := by rw [two_mul, pow_add]
    have hexp : 1 ≤ Real.exp (K.m0 / L.ν) := Real.one_le_exp (div_nonneg hm0 hν.le)
    have hεr : L.ε ^ (3 / 11 : ℝ) ≤ rhoRep K L := by
      unfold rhoRep
      have : 0 ≤ L.ε ^ (3 / 11 : ℝ) := by positivity
      nlinarith
    have hterm : Pν * L.ε ^ (3 / 11 : ℝ) ≤ C * L.ν⁻¹ ^ (2 * k) * rhoRep K L := by
      rw [hPν]
      have h0 : 0 ≤ L.ε ^ (3 / 11 : ℝ) := by positivity
      calc C * L.ν⁻¹ ^ k * L.ε ^ (3 / 11 : ℝ) ≤ C * L.ν⁻¹ ^ (2 * k) * L.ε ^ (3 / 11 : ℝ) := by
            gcongr
        _ ≤ C * L.ν⁻¹ ^ (2 * k) * rhoRep K L := by gcongr
    have hfirst : A * (Pν * rhoRep K L) = 2 * C ^ 2 * L.ν⁻¹ ^ (2 * k) * rhoRep K L := by
      rw [hA, hPν, hsq]; ring
    have hterm2 : Pν * rhoRep K L ≤ C * L.ν⁻¹ ^ (2 * k) * rhoRep K L := by
      rw [hPν]
      gcongr
    calc CL * (A * (Pν * rhoRep K L) + Pν * L.ε ^ (3 / 11 : ℝ) + Pν * rhoRep K L)
        ≤ CL * (2 * C ^ 2 * L.ν⁻¹ ^ (2 * k) * rhoRep K L + C * L.ν⁻¹ ^ (2 * k) * rhoRep K L +
            C * L.ν⁻¹ ^ (2 * k) * rhoRep K L) := by
          rw [hfirst]; gcongr
      _ = CL * (2 * C ^ 2 + 2 * C) * L.ν⁻¹ ^ (2 * k) * rhoRep K L := by ring
  calc eLpNorm (ringRead L.ε⁻¹ f₁) (11 / 4) μ
      ≤ ENNReal.ofReal CL * eLpNorm (ringRead L.ε⁻¹ f₂) (11 / 4) μ := by rw [s1, ← s3]; exact s2
    _ ≤ ENNReal.ofReal CL * (ENNReal.ofReal A * ENNReal.ofReal (Pν * rhoRep K L) +
          ENNReal.ofReal (Pν * L.ε ^ (3 / 11 : ℝ)) + ENNReal.ofReal (Pν * rhoRep K L)) := by
        gcongr
    _ = ENNReal.ofReal (CL * (A * (Pν * rhoRep K L) + Pν * L.ε ^ (3 / 11 : ℝ) +
          Pν * rhoRep K L)) := by
        rw [← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_add (mul_nonneg hA0 hx1) hx2,
          ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hA0 hx1) hx2) hx1,
          ← ENNReal.ofReal_mul hCL.le]
    _ ≤ ENNReal.ofReal (CL * (2 * C ^ 2 + 2 * C) * L.ν⁻¹ ^ (2 * k) * rhoRep K L) :=
        ENNReal.ofReal_le_ofReal hreal

end Reduction

/-- **`presFlatBound_of`**: the `Y_{11/4}` bound of `∇p - ∇p_lift` along the sequence
(`PresFlatBound`, source 5272-5281) from the two general leaves and the five level leaves, with
the coefficient change `CoefChg` (task `PartIII-b:C/rep/8/2/pres/4`). -/
theorem presFlatBound_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hLB : LerayComp114Bound) (hconv : RingReadPhaseLr) (hH : D.PresHelmholtz)
    (h1 : D.PresChgPhys) (h2 : D.PresForcePhys) (hR : D.RawResid) (hE : D.EntSrc)
    (hCC : D.CoefChg) (hG : D.ExactGradBound) : PresFlatBound D := by
  obtain ⟨CL₀, hCL₀, hLB₀⟩ := hLB
  obtain ⟨C1, k1, e1⟩ := hR
  obtain ⟨C2, k2, e2⟩ := hCC
  obtain ⟨C3, k3, e3⟩ := hG
  obtain ⟨C4, k4, e4⟩ := hE
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  set C : ℝ := |C1| + |C2| + |C3| + |C4| with hCdef
  set k : ℕ := max k1 (max k2 (max k3 k4)) with hkdef
  set CL : ℝ := CL₀ + 1 with hCLdef
  have hC0 : 0 ≤ C := by positivity
  have hCL : 0 < CL := by rw [hCLdef]; linarith
  have hC1 : C1 ≤ C :=
    (le_abs_self C1).trans (by rw [hCdef]; linarith [abs_nonneg C2, abs_nonneg C3, abs_nonneg C4])
  have hC2 : C2 ≤ C :=
    (le_abs_self C2).trans (by rw [hCdef]; linarith [abs_nonneg C1, abs_nonneg C3, abs_nonneg C4])
  have hC3 : C3 ≤ C :=
    (le_abs_self C3).trans (by rw [hCdef]; linarith [abs_nonneg C1, abs_nonneg C2, abs_nonneg C4])
  have hC4 : C4 ≤ C :=
    (le_abs_self C4).trans (by rw [hCdef]; linarith [abs_nonneg C1, abs_nonneg C2, abs_nonneg C3])
  have hLB' : ∀ G : Space → Space, MemLp G (11 / 4) volume →
      eLpNorm (lerayComp114 G) (11 / 4) volume ≤ ENNReal.ofReal CL * eLpNorm G (11 / 4) volume :=
    fun G hG => (hLB₀ G hG).trans (mul_le_mul_left
      (ENNReal.ofReal_le_ofReal (by rw [hCLdef]; linarith)) _)
  refine ⟨CL * (2 * C ^ 2 + 2 * C), 2 * k, ?_⟩
  filter_upwards [hH, h1, h2, e1, e2, e3, e4, hle] with n a0 a1 a2 a3 a4 a5 a6 hν
  have hν1 : (D.level n).ν ≤ 1 := hν.1
  exact presFlatBoundAt_of D.Pl D.K (D.level n) hν1 hst.m0_pos.le hC0 hCL hLB' hconv a0 a1 a2
    (a3.mono hν1 hC1 hC0 (le_max_left _ _))
    (a6.mono hν1 hC4 hC0
      (((le_max_right k3 k4).trans (le_max_right k2 _)).trans (le_max_right _ _)))
    (a4.mono hν1 hC2 hC0 ((le_max_left k2 (max k3 k4)).trans (le_max_right _ _)))
    (a5.mono hν1 hC3 hC0
      (((le_max_left k3 k4).trans (le_max_right k2 _)).trans (le_max_right _ _)))

/-- **`presFlatBound_of_leaves`**: `presFlatBound_of` with the two general leaves supplied
(`lerayComp114Bound`, `ringReadPhaseLr`): the five level leaves and `CoefChg` give `PresFlatBound`. -/
theorem presFlatBound_of_leaves (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hH : D.PresHelmholtz) (h1 : D.PresChgPhys) (h2 : D.PresForcePhys) (hR : D.RawResid)
    (hE : D.EntSrc) (hCC : D.CoefChg) (hG : D.ExactGradBound) : PresFlatBound D :=
  presFlatBound_of D hst lerayComp114Bound ringReadPhaseLr hH h1 h2 hR hE hCC hG

end UnforcedLeray.Short.PartIIIb.Concrete
