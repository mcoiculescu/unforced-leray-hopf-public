import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_org

/-!
# The ring expansion of the mean Ward residual (`PartIII-b:C/rep/8/2`, source 5449-5506)

Source of record: `the November 2 reference manuscript` (73 pages), lines
5449-5483 (ring expansion), 5272-5289 and 5496-5506 (exact-pressure and repair-coefficient
errors).

## The correction to the split of `Sub/PartIII-b_C_rep_8_org.lean`

`meanE` (the mean Ward residual) is built on the *exact* background `U = V + r_b` with its exact
pressure `p` (`L.U`, `L.pres`), whereas `ringAff` uses only the flat train `v, p_cyl`
(`trainV`, `trainP`).  Their difference therefore contains the exact-pressure and
repair-coefficient errors `U - U_raw = r_b + E_εα`, `∇p - ∇p_lift`, which the source bounds by
`P_ν ε^{85/22} e^{m₀/ν} N` (5272-5289: `‖∇p - G_flat‖_{Y_{11/4}} ≤ P_ν ε^{3/11}e^{m₀/ν}`,
`‖DX‖_{L^∞_τL^{22/3}} ≤ P_ν ε^{57/22}N₁`, exponent `1 + 3/11 + 57/22 = 85/22`; "Nonpressure
repair and entrance coefficient changes are bounded in the same way", 5287-5289; 5496-5498,
5506 "The `85/22` term retains the entire Cartesian pressure correction").  This is larger than
`ε⁴N` for small `ε`, so `RingExpansionAt` of `PartIII-b_C_rep_8_org` (bound `P_ν ε⁴ N`) is not
the source's estimate; `GaussianReplaceAt` (`ringAff` against `E_{A_T}`) contains no exact
pressure, so the `85/22` term cannot be placed there either.  The source's estimate is

  `‖meanE - ringAff‖ ≤ P_ν N (ε⁴ + ε^{85/22} e^{m₀/ν})`   (`RingExpansionFullAt`).

The statement of `RingExpansionAt` itself (and the
arithmetic of `thinCompleteAt_of`, `ThinCompleteAt` already carries the `85/22` term) is corrected
to this bound in `PartIII-b_C_rep_8_org.lean` by the organizer item `PartIII-b:C/rep/8/2/pres/org`;
`RingExpansionFull` then coincides with the corrected `RingExpansion`.

## The split of `RingExpansionFull`

With the raw coefficient `U_raw = (L.params Pl).raw` (`rawU`, source 2076-2077, 5461) and the
flat lifted pressure `p_lift = s·p_cyl` (`liftP`, `p_raw = a_r²p`, source 1217, 5272-5282),
`meanERaw` is the mean Ward residual with these coefficients.  Then

  `meanE - ringAff = (meanE - meanERaw) + (meanERaw - ringAffJet) + (ringAffJet - ringAff)`:

* `CoefReplaceAt` (5272-5289, 5496-5498): the first difference is `P_ν ε^{85/22}e^{m₀/ν}N`;
* `RingSubstAt` (5460-5477): pointwise on the young range `0 < s ≤ 1/ν`, the substitution of
  the ring-chart rules into the four Ward terms gives the ring expression with the jet matrix
  `B_j` (`ringAffJet`) up to `P_ν ε⁴ s^{5/2} 𝔴(s,q,η) N` in chart-coefficient units (physical
  `ε⁴s³N` for `2U·∇Y`, `ε⁴s⁴N ≤ ν⁻¹ε⁴s³N` for the other terms), `𝔴 = trainWeight 4`;
* the clock (5449-5453, 5476-5477): `ringAffJet - ringAff = 2s·(B_j - B_T)v`, of size
  `P_ν ν ε⁵ s^{7/2} N 𝔴 ≤ P_ν ε⁴ s^{5/2} N 𝔴` by `JetClockAt` (proved here);
* the support: for `s > 1/ν` both `meanERaw` (stream cutoff, `MeanSupportAt`) and `ringAff`
  (`A_T = 0`, `ActualJetAt`, proved here) vanish;
* `TrainMomentAt` (5464-5465, 5477-5482): the weight is measurable, bounded on the young range,
  and `s^{5/2}𝔴` is square integrable for the density `π s^{-3/2} ds dq/c dη` of `srcMeasure`
  (the source's `π s^{-5/2}` for the physical field; `s^{7/2}` integrable at zero, Gaussian
  moments of fixed order, polynomial in `1/ν`).

`RingSubstAt` itself comes from the ring-chart rules (`RingChartRulesAt`, 5460-5465), the mean
transverse Taylor and Hessian estimates of the mean field (`MeanJetAt`, 5438-5448), `ActualJet`
and `JetClock` (task `ringSubst_of`).

**Proved here:** `ringAff_eq_zero_of_lt`, `norm_ringAffJet_sub_ringAff` (the clock),
`ringExpansionFullAt_of`, `SeqData.ringExpansionFull_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. Raw coefficient, flat lifted pressure, raw mean residual and the jet ring expression -/

/-- The raw ring lift `U_raw = √s[v₁e_r + (v₂ + εH)e_z]` of the actual train of the level
(source 2076-2077, 5460-5461; `Params.raw`). -/
def rawU (Pl : PlanarData) (L : ReturnLevel) : ℝ → SpatialField := (L.params Pl).raw

/-- The flat lifted pressure `p_lift = a_r² p_cyl = s·p_cyl(s, q, η)` at the chart point of
`(τ, y)` (source 1217, 5272-5282), `p_cyl` the decaying pressure of the actual train. -/
def liftP (L : ReturnLevel) (τ : ℝ) (y : Space) : ℝ :=
  age L.ε⁻¹ y * L.train.p (chart L.ε⁻¹ τ y).1 (chart L.ε⁻¹ τ y).2

/-- The ring expression `2Bv + 2νA^y:D²_flat v - (A^y + (A^y)ᵀ)∇_flat p` at one age, for given
matrices `B`, `A^y` and flat profiles `vv`, `pp` (source 5468-5470). -/
def ringAffB (ν : ℝ) (B Ayv : Mat3) (vv : ℝ × ℝ → ℝ × ℝ) (pp : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    Vec3 :=
  (2 : ℝ) • mv B (emb (vv x)) + (2 * ν) • hessContr Ayv vv x -
    mv (fun a b => Ayv a b + Ayv b a) (emb (mgrad pp x))

theorem ringAffGen_eq_ringAffB (ν μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3)
    (vv : ℝ → ℝ × ℝ → ℝ × ℝ) (pp : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ) :
    ringAffGen ν μ χf A vv pp s x = ringAffB ν (Bmat ν μ χf A s) (Ay ν χf A s) (vv s) (pp s) x :=
  rfl

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- The mean Ward residual with the raw coefficient `U_raw` and the flat lifted pressure
(source 5460-5467): the residual into which the ring-chart rules are substituted. -/
def meanERaw (T : LStr Pl K L) : Chart → Merid :=
  coefOf L.ε⁻¹ (wardEXY L.ν μ L.ε⁻¹ (rawU Pl L) (liftP L)
    (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T))
    (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)))

/-- The ring expression with the jet matrix `B_j(s) = s⁻¹D_yY^mt(R/√s,0,0)` (`Bjet`) in place of
`B_T` (source 5446, 5466-5470): the chart coefficient
`s^{-1/2}·s^{3/2}{2B_jv + 2νA_T:D²_flat v - (A_T+A_Tᵀ)∇_flat p_cyl}` of the actual train. -/
def ringAffJet (T : LStr Pl K L) : Chart → Merid := fun p =>
  merOf ((Real.sqrt p.1)⁻¹ • (p.1 ^ (3 / 2 : ℝ) •
    ringAffB L.ν (Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) p.1)
      (Ay L.ν K.χf (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T) p.1)
      (trainV L p.1) (trainP L p.1) p.2))

end Regime

/-! ## 2. The weighted train coefficient -/

/-- The train velocity in the dilation variable `σ = log s`: `(σ, x) ↦ v(e^σ, x)`, so that
`∂_σ = s∂_s` (source 5464-5465). -/
def trainFv (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) : Cyl.Vec2 := L.train.v (Real.exp z.1) z.2

/-- The train pressure in the dilation variable. -/
def trainFp (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) : ℝ := L.train.p (Real.exp z.1) z.2

/-- The decaying train stream in the dilation variable. -/
def trainFpsi (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) : ℝ := L.train.ψ (Real.exp z.1) z.2

/-- **The weighted train coefficient** `𝔴_m(s,q,η)` (source 5464-5465, 5472-5473, 5480-5482):
`(1+|η|)^m Σ_{j≤4}(|D^jv| + |D^jp| + |D^jψ|)`, all derivatives in `(σ, q, η)`, `σ = log s`
(so the `s∂_s` derivatives of the chart differentiation are included).  `H, C₁, C₂` of the
ring-chart rules are bounded by `𝔴_3`; `𝔴_4` absorbs one more transverse factor `|η|`. -/
def trainWeight (m : ℕ) (L : ReturnLevel) (p : Chart) : ℝ :=
  (1 + |p.2.2|) ^ m * ∑ j ∈ Finset.range 5,
    (‖iteratedFDeriv ℝ j (trainFv L) (Real.log p.1, p.2)‖ +
      ‖iteratedFDeriv ℝ j (trainFp L) (Real.log p.1, p.2)‖ +
      ‖iteratedFDeriv ℝ j (trainFpsi L) (Real.log p.1, p.2)‖)

/-- `s^{5/2}𝔴_4` on the young range `0 < s ≤ 1/ν`, zero elsewhere (source 5477-5480). -/
def youngWeight (L : ReturnLevel) : Chart → ℝ :=
  Set.indicator {p : Chart | p.1 ∈ Ioc 0 (1 / L.ν)} fun p => p.1 ^ (5 / 2 : ℝ) * trainWeight 4 L p

/-! ## 3. Flat derivatives and the Cartesian frame at azimuth zero -/

/-- A `Vec3` (components `(r, φ, z)` at azimuth zero, `e_r = e_1`) as a point of `Space`. -/
def vecSp (v : Vec3) : Space := WithLp.toLp 2 v

/-- The flat direction of the Cartesian index `j` at azimuth zero: `∂_{y₁} ↦ ∂_q`,
`∂_{y₂} ↦ 0` (hoop, `O(ε)` in the chart), `∂_{y₃} ↦ ∂_η`. -/
def flatDir (j : Fin 3) : ℝ × ℝ := ![((1 : ℝ), (0 : ℝ)), (0, 0), (0, 1)] j

/-- `D_flat v` in the direction of the Cartesian index `j`, embedded (source 5462). -/
def flatD1 (L : ReturnLevel) (s : ℝ) (x : ℝ × ℝ) (j : Fin 3) : Vec3 :=
  emb (fderiv ℝ (trainV L s) x (flatDir j))

/-- `D²_flat v` in the directions of the Cartesian indices `j, l` (`∂_j∂_l`), embedded
(source 5463). -/
def flatD2 (L : ReturnLevel) (s : ℝ) (x : ℝ × ℝ) (j l : Fin 3) : Vec3 :=
  emb (fderiv ℝ (fun x' => fderiv ℝ (trainV L s) x' (flatDir l)) x (flatDir j))

/-! ## 4. The hypotheses -/

section Hyp

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- **The exact ring-chart rules** (source 5460-5465): at the chart point `p = (s,(q,η))`,
`y = (R/√s, 0, η/√s)`, `τ = 2q/R + log s`, on the young range,
`U_raw = √s(v + εHe_z)`, `DU_raw = s(D_flat v + εC₁)`, `D²U_raw = s^{3/2}(D²_flat v + εC₂)` and
`∇p_lift = s^{3/2}(∇_flat p_cyl + εC₃)` (Cartesian components at azimuth zero), with
`|H|, |C₁|, |C₂|, |C₃| ≤ P_ν 𝔴_3` (explicit chart differentiation). -/
def RingChartRulesAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ p : Chart, 0 < p.1 → p.1 ≤ 1 / L.ν →
    ‖rawU Pl L (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p) -
        Real.sqrt p.1 • vecSp (emb (trainV L p.1 p.2))‖ ≤
      C * L.ν⁻¹ ^ k * L.ε * Real.sqrt p.1 * trainWeight 3 L p ∧
    (∀ j : Fin 3, ‖physPd (rawU Pl L (NearInst.chartTau L.ε⁻¹ p)) j (NearInst.chartY L.ε⁻¹ p) -
        p.1 • vecSp (flatD1 L p.1 p.2 j)‖ ≤ C * L.ν⁻¹ ^ k * L.ε * p.1 * trainWeight 3 L p) ∧
    (∀ j l : Fin 3,
      ‖physPd2 (rawU Pl L (NearInst.chartTau L.ε⁻¹ p)) j l (NearInst.chartY L.ε⁻¹ p) -
        p.1 ^ (3 / 2 : ℝ) • vecSp (flatD2 L p.1 p.2 j l)‖ ≤
      C * L.ν⁻¹ ^ k * L.ε * p.1 ^ (3 / 2 : ℝ) * trainWeight 3 L p) ∧
    ‖physGrad (liftP L (NearInst.chartTau L.ε⁻¹ p)) (NearInst.chartY L.ε⁻¹ p) -
        p.1 ^ (3 / 2 : ℝ) • vecSp (emb (mgrad (trainP L p.1) p.2))‖ ≤
      C * L.ν⁻¹ ^ k * L.ε * p.1 ^ (3 / 2 : ℝ) * trainWeight 3 L p

/-- **The mean transverse Taylor and Hessian estimates** (source 5438-5448, for the phase-mean
zero-width field `X^mt, Y^mt`, 5380-5387): at `y = (R/√s, 0, η/√s)`, `0 < s ≤ 1/ν`,
`|D_yX^mt - A_T(s)| + |D_yY^mt - sB_j(s)| ≤ P_ν ε⁴ s^{5/2}|η| N` (columns `∂_jX`, `A_T = 𝓛T₁`
`= LjFun`, `B_j = Bjet`) and `|D²_yX^mt| ≤ P_ν ε⁴ s³ N`. -/
def MeanJetAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ∀ p : Chart, 0 < p.1 → p.1 ≤ 1 / L.ν →
    (∀ j : Fin 3,
      ‖physPd (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) (NearInst.chartTau L.ε⁻¹ p)) j
          (NearInst.chartY L.ε⁻¹ p) -
        vecSp (fun i => LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T
          p.1 i j)‖ₑ ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 4 * p.1 ^ (5 / 2 : ℝ) * |p.2.2|) *
        oldN1 Pl K L T) ∧
    (∀ j : Fin 3,
      ‖physPd (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) (NearInst.chartTau L.ε⁻¹ p)) j
          (NearInst.chartY L.ε⁻¹ p) -
        p.1 • vecSp (fun i => Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) p.1 i j)‖ₑ ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 4 * p.1 ^ (5 / 2 : ℝ) * |p.2.2|) *
        oldN1 Pl K L T) ∧
    ∀ j l : Fin 3,
      ‖physPd2 (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) (NearInst.chartTau L.ε⁻¹ p)) j l
          (NearInst.chartY L.ε⁻¹ p)‖ₑ ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 4 * p.1 ^ (3 : ℝ)) * oldN1 Pl K L T

/-- **The weighted train bounds** (source 5464-5465, 5477-5482, young train 5484-5495): the
weight is measurable, bounded on the young range, and `s^{5/2}𝔴_4` is square integrable for
`srcMeasure` (density `π s^{-3/2}` on the chart coefficient, i.e. the source's `π s^{-5/2}` on the
physical field; `s^{7/2}` is integrable at zero, the Gaussian moments are of fixed order). -/
def TrainMomentAt (C : ℝ) (k : ℕ) : Prop :=
  Measurable (trainWeight 4 L) ∧
    (∀ p : Chart, 0 < p.1 → p.1 ≤ 1 / L.ν → trainWeight 4 L p ≤ C * L.ν⁻¹ ^ k) ∧
    eLpNorm (youngWeight L) 2 (srcMeasure (cOf L.ν)) ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k)

/-- **The exact-pressure and repair-coefficient errors** (source 5272-5289, 5496-5498, 5506):
replacing `U` by `U_raw` and the exact pressure by the flat lifted pressure in the mean Ward
residual costs `P_ν ε^{85/22} e^{m₀/ν} N` (`R⁻¹‖·‖_{Y_2}` is the `L²(srcMeasure)` norm of the
chart coefficient). -/
def CoefReplaceAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L,
    AEStronglyMeasurable (meanE Pl K L μ T - meanERaw Pl K L μ T) (srcMeasure (cOf L.ν)) ∧
    eLpNorm (meanE Pl K L μ T - meanERaw Pl K L μ T) 2 (srcMeasure (cOf L.ν)) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν))) *
        oldN1 Pl K L T

/-- **Substitution into the four Ward terms** (source 5460-5477): on the young range the raw mean
residual equals the jet ring expression up to `P_ν ε⁴ s^{5/2} 𝔴_4 N` in chart-coefficient units
(physical `ε⁴s³N` in `2U·∇Y`; `ε⁴s⁴N ≤ ν⁻¹ε⁴s³N` in `DXD²U`, `DX∇p`, `DUD²X`,
`(U⊗U):D²X`). -/
def RingSubstAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ∀ p : Chart, 0 < p.1 → p.1 ≤ 1 / L.ν →
    ‖meanERaw Pl K L μ T p - ringAffJet Pl K L μ T p‖ₑ ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 4 * p.1 ^ (5 / 2 : ℝ) * trainWeight 4 L p) *
        oldN1 Pl K L T

/-- **Young support of the mean field** (source 4161-4166, 5395): the stream cutoff `χ_y` vanishes
for `s ≥ 1/ν`, so `X^mt, Y^mt` vanish near every chart point of age `s > 1/ν` and so does the
raw mean residual. -/
def MeanSupportAt : Prop :=
  ∀ (T : LStr Pl K L) (p : Chart), 1 / L.ν < p.1 → meanERaw Pl K L μ T p = 0

/-- **The ring expansion with its exact-pressure term** (source 5449-5483 with 5272-5289,
5496-5506): `‖meanE - ringAff‖ ≤ P_ν N (ε⁴ + ε^{85/22} e^{m₀/ν})`. -/
def RingExpansionFullAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L,
    eLpNorm (meanE Pl K L μ T - ringAff Pl K L μ T) 2 (srcMeasure (cOf L.ν)) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k *
        (L.ε ^ 4 + L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν))) * oldN1 Pl K L T

end Hyp

namespace SeqData

variable (D : SeqData)

/-- The ring-chart rules along the sequence. -/
def RingChartRules : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, RingChartRulesAt D.Pl (D.level n) C k

/-- The mean jet estimates along the sequence. -/
def MeanJet : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    MeanJetAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- The weighted train bounds along the sequence. -/
def TrainMoment : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, TrainMomentAt (D.level n) C k

/-- The exact-pressure and repair-coefficient errors along the sequence. -/
def CoefReplace : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    CoefReplaceAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- The substitution estimate along the sequence. -/
def RingSubst : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    RingSubstAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- The young support of the mean field along the sequence. -/
def MeanSupport : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, MeanSupportAt D.Pl D.K (D.level n) (D.mu n z)

/-- (b) along the sequence, with the exact-pressure term. -/
def RingExpansionFull : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    RingExpansionFullAt D.Pl D.K (D.level n) (D.mu n z) C k

end SeqData

/-! ## 5. Elementary bounds -/

theorem merOf_sub (a b : Vec3) : merOf (a - b) = merOf a - merOf b := by
  ext i; fin_cases i <;> simp [merOf]

theorem norm_merOf_le (v : Vec3) : ‖merOf v‖ ≤ 2 * ‖v‖ := by
  have h0 : ‖v 0‖ ≤ ‖v‖ := norm_le_pi_norm v 0
  have h2 : ‖v 2‖ ≤ ‖v‖ := norm_le_pi_norm v 2
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have e0 : ‖(merOf v) 0‖ = ‖v 0‖ := by simp [merOf]
  have e1 : ‖(merOf v) 1‖ = ‖v 2‖ := by simp [merOf]
  rw [e0, e1]
  calc √(‖v 0‖ ^ 2 + ‖v 2‖ ^ 2) ≤ √((‖v 0‖ + ‖v 2‖) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [norm_nonneg (v 0), norm_nonneg (v 2)])
    _ = ‖v 0‖ + ‖v 2‖ := Real.sqrt_sq (by positivity)
    _ ≤ 2 * ‖v‖ := by linarith

theorem abs_le_frob (M : Mat3) (i j : Fin 3) : |M i j| ≤ frob M := by
  unfold frob
  refine Real.abs_le_sqrt ?_
  have h1 : M i j ^ 2 ≤ ∑ j', M i j' ^ 2 :=
    Finset.single_le_sum (f := fun j' => M i j' ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', M i j' ^ 2 ≤ ∑ i', ∑ j', M i' j' ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', M i' j' ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact h1.trans h2

theorem norm_mv_le (M : Mat3) (w : Vec3) : ‖mv M w‖ ≤ 3 * frob M * ‖w‖ := by
  have hF := frob_nonneg M
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  unfold mv
  calc |∑ j, M i j * w j| ≤ ∑ j, |M i j * w j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, frob M * ‖w‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (abs_le_frob M i j) (by simpa using norm_le_pi_norm w j)
          (abs_nonneg _) hF
    _ = 3 * frob M * ‖w‖ := by simp; ring

theorem frob_sub_comm (A B : Mat3) : frob (A - B) = frob (B - A) := by
  unfold frob
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.sub_apply]
  ring

theorem norm_emb_le (x : ℝ × ℝ) : ‖emb x‖ ≤ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  fin_cases i
  · simpa [emb] using norm_fst_le x
  · simp [emb]
  · simpa [emb] using norm_snd_le x

theorem ringAffB_sub (ν : ℝ) (B₁ B₂ Ayv : Mat3) (vv : ℝ × ℝ → ℝ × ℝ) (pp : ℝ × ℝ → ℝ)
    (x : ℝ × ℝ) :
    ringAffB ν B₁ Ayv vv pp x - ringAffB ν B₂ Ayv vv pp x = (2 : ℝ) • mv (B₁ - B₂) (emb (vv x)) := by
  funext i
  simp only [ringAffB, mv, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
    Finset.sum_sub_distrib]
  ring

/-- The weight dominates the train velocity. -/
theorem trainV_le_weight (m : ℕ) (L : ReturnLevel) {p : Chart} (hp : 0 < p.1) :
    ‖trainV L p.1 p.2‖ ≤ trainWeight m L p := by
  have h1 : ‖trainV L p.1 p.2‖ ≤ ‖L.train.v p.1 p.2‖ := by
    refine norm_prod_le_iff.2 ⟨?_, ?_⟩
    · exact PiLp.norm_apply_le _ _
    · exact PiLp.norm_apply_le _ _
  have h2 : ‖L.train.v p.1 p.2‖ = ‖iteratedFDeriv ℝ 0 (trainFv L) (Real.log p.1, p.2)‖ := by
    rw [norm_iteratedFDeriv_zero]
    simp [trainFv, Real.exp_log hp]
  set g : ℕ → ℝ := fun j => ‖iteratedFDeriv ℝ j (trainFv L) (Real.log p.1, p.2)‖ +
      ‖iteratedFDeriv ℝ j (trainFp L) (Real.log p.1, p.2)‖ +
      ‖iteratedFDeriv ℝ j (trainFpsi L) (Real.log p.1, p.2)‖ with hg
  have hg0 : ∀ j, 0 ≤ g j := fun j => by positivity
  have h3 : ‖iteratedFDeriv ℝ 0 (trainFv L) (Real.log p.1, p.2)‖ ≤ g 0 := by
    simp only [hg]
    linarith [norm_nonneg (iteratedFDeriv ℝ 0 (trainFp L) (Real.log p.1, p.2)),
      norm_nonneg (iteratedFDeriv ℝ 0 (trainFpsi L) (Real.log p.1, p.2))]
  have h4 : g 0 ≤ ∑ j ∈ Finset.range 5, g j :=
    Finset.single_le_sum (fun j _ => hg0 j) (by simp)
  have h5 : 1 ≤ (1 + |p.2.2|) ^ m := one_le_pow₀ (by linarith [abs_nonneg p.2.2])
  have h6 : 0 ≤ ∑ j ∈ Finset.range 5, g j := Finset.sum_nonneg fun j _ => hg0 j
  unfold trainWeight
  calc ‖trainV L p.1 p.2‖ ≤ ∑ j ∈ Finset.range 5, g j := by
        rw [h2] at h1; exact h1.trans (h3.trans h4)
    _ ≤ (1 + |p.2.2|) ^ m * ∑ j ∈ Finset.range 5, g j := le_mul_of_one_le_left h6 h5

theorem trainWeight_nonneg (m : ℕ) (L : ReturnLevel) (p : Chart) : 0 ≤ trainWeight m L p := by
  unfold trainWeight
  have : 0 ≤ 1 + |p.2.2| := by positivity
  positivity

theorem youngWeight_nonneg (L : ReturnLevel) (p : Chart) : 0 ≤ youngWeight L p := by
  unfold youngWeight
  by_cases h : p ∈ {p : Chart | p.1 ∈ Ioc 0 (1 / L.ν)}
  · rw [Set.indicator_of_mem h]
    exact mul_nonneg (Real.rpow_nonneg h.1.le _) (trainWeight_nonneg 4 L p)
  · rw [Set.indicator_of_notMem h]

theorem youngWeight_of_mem (L : ReturnLevel) {p : Chart} (h0 : 0 < p.1) (h1 : p.1 ≤ 1 / L.ν) :
    youngWeight L p = p.1 ^ (5 / 2 : ℝ) * trainWeight 4 L p := by
  unfold youngWeight
  exact Set.indicator_of_mem (show p ∈ {p : Chart | p.1 ∈ Ioc 0 (1 / L.ν)} from ⟨h0, h1⟩) _

/-- From an `ENNReal` bound by `ofReal (c·d)·ofReal n` to a real bound. -/
theorem le_of_ofReal_le_mul {x c d n : ℝ} (hd : 0 ≤ d) (hn : 0 ≤ n)
    (h : ENNReal.ofReal x ≤ ENNReal.ofReal (c * d) * ENNReal.ofReal n) : x ≤ |c| * d * n := by
  have h1 : ENNReal.ofReal (c * d) ≤ ENNReal.ofReal (|c| * d) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self c) hd)
  have h2 : ENNReal.ofReal x ≤ ENNReal.ofReal (|c| * d) * ENNReal.ofReal n :=
    h.trans (by gcongr)
  rw [← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg c) hd)] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2


/-- Minkowski with one summand bounded pointwise by a measurable majorant. -/
theorem eLpNorm_add_le_of_ae_le {f g : Chart → Merid} {G : Chart → ℝ} {μs : Measure Chart}
    (hf : AEStronglyMeasurable f μs) (hG : AEStronglyMeasurable G μs)
    (hg : ∀ᵐ p ∂μs, ‖g p‖ ≤ G p) :
    eLpNorm (f + g) 2 μs ≤ eLpNorm f 2 μs + eLpNorm G 2 μs := by
  have h1 : eLpNorm (f + g) 2 μs ≤ eLpNorm ((fun p => ‖f p‖) + G) 2 μs := by
    refine eLpNorm_mono_ae_real ?_
    filter_upwards [hg] with p hp
    simp only [Pi.add_apply]
    exact (norm_add_le _ _).trans (by linarith)
  refine h1.trans ((eLpNorm_add_le hf.norm hG (by norm_num)).trans ?_)
  rw [eLpNorm_norm]

/-! ## 6. The support of `ringAff` and the clock error -/

section Clock

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- For `s > 1/ν` the ring expression vanishes, since `A_T = 0` on `[1/ν, ∞)` (`ActualJetAt`,
source 5403). -/
theorem ringAff_eq_zero_of_lt (T : LStr Pl K L)
    (hA : ∀ s : ℝ, 1 / L.ν ≤ s →
      LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T s = 0)
    {p : Chart} (hp : 1 / L.ν < p.1) : ringAff Pl K L μ T p = 0 := by
  have hAy : ∀ s, 1 / L.ν < s →
      Ay L.ν K.χf (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T) s = 0 :=
    fun s hs => by simp [Ay, hA s hs.le]
  have hev : Ay L.ν K.χf (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T)
      =ᶠ[𝓝 p.1] fun _ => 0 := by
    filter_upwards [lt_mem_nhds hp] with s hs using hAy s hs
  have hd : deriv (Ay L.ν K.χf
      (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T)) p.1 = 0 := by
    rw [hev.deriv_eq]; simp
  have hB : Bmat L.ν μ K.χf
      (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T) p.1 = 0 := by
    simp [Bmat, hd, hAy p.1 hp]
  show merOf ((Real.sqrt p.1)⁻¹ • (p.1 ^ (3 / 2 : ℝ) •
    ringAffGen L.ν μ K.χf (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T)
      (trainV L) (trainP L) p.1 p.2)) = 0
  rw [ringAffGen_eq_ringAffB, hB, hAy p.1 hp]
  have hz : ringAffB L.ν 0 0 (trainV L p.1) (trainP L p.1) p.2 = 0 := by
    have m0 : ∀ w : Vec3, mv 0 w = 0 := fun w => funext fun i => by simp [mv]
    have m1 : ∀ w : Vec3, mv (fun a b => (0 : Mat3) a b + (0 : Mat3) b a) w = 0 :=
      fun w => funext fun i => by simp [mv]
    have m2 : hessContr 0 (trainV L p.1) p.2 = 0 := by
      funext i; fin_cases i <;> simp [hessContr, emb]
    simp only [ringAffB, m0, m1, m2, smul_zero, add_zero, sub_zero]
  rw [hz, smul_zero, smul_zero]
  ext i; fin_cases i <;> simp [merOf]

/-- **The clock error** (source 5449-5453, 5476-5477): the jet and actual ring expressions
differ by `s^{-1/2}s^{3/2}·2(B_j - B_T)v`. -/
theorem norm_ringAffJet_sub_ringAff (T : LStr Pl K L) {p : Chart} (hp : 0 < p.1) :
    ‖ringAffJet Pl K L μ T p - ringAff Pl K L μ T p‖ ≤
      12 * p.1 * frob (Bmat L.ν μ K.χf
          (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T) p.1 -
        Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) p.1) * ‖trainV L p.1 p.2‖ := by
  set A := LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T with hAdef
  set Bj := Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) p.1 with hBj
  set Bm := Bmat L.ν μ K.χf A p.1 with hBm
  have e1 : ringAff Pl K L μ T p = merOf ((Real.sqrt p.1)⁻¹ • (p.1 ^ (3 / 2 : ℝ) •
      ringAffB L.ν Bm (Ay L.ν K.χf A p.1) (trainV L p.1) (trainP L p.1) p.2)) := rfl
  have e2 : ringAffJet Pl K L μ T p = merOf ((Real.sqrt p.1)⁻¹ • (p.1 ^ (3 / 2 : ℝ) •
      ringAffB L.ν Bj (Ay L.ν K.χf A p.1) (trainV L p.1) (trainP L p.1) p.2)) := rfl
  rw [e1, e2, ← merOf_sub, ← smul_sub, ← smul_sub, ringAffB_sub]
  have hsq : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hp
  have h32 : p.1 ^ (3 / 2 : ℝ) = p.1 * Real.sqrt p.1 := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hp,
      Real.rpow_one]
  have hsc : (Real.sqrt p.1)⁻¹ * p.1 ^ (3 / 2 : ℝ) * 2 = 2 * p.1 := by
    rw [h32]; field_simp
  have hrw : (Real.sqrt p.1)⁻¹ • (p.1 ^ (3 / 2 : ℝ) •
      ((2 : ℝ) • mv (Bj - Bm) (emb (trainV L p.1 p.2)))) =
      (2 * p.1) • mv (Bj - Bm) (emb (trainV L p.1 p.2)) := by
    rw [smul_smul, smul_smul, hsc]
  rw [hrw]
  have hF : 0 ≤ frob (Bm - Bj) := frob_nonneg _
  have hw := norm_emb_le (trainV L p.1 p.2)
  have hmv := norm_mv_le (Bj - Bm) (emb (trainV L p.1 p.2))
  rw [frob_sub_comm] at hmv
  calc ‖merOf ((2 * p.1) • mv (Bj - Bm) (emb (trainV L p.1 p.2)))‖
      ≤ 2 * ‖(2 * p.1) • mv (Bj - Bm) (emb (trainV L p.1 p.2))‖ := norm_merOf_le _
    _ = 2 * ((2 * p.1) * ‖mv (Bj - Bm) (emb (trainV L p.1 p.2))‖) := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ 2 * ((2 * p.1) * (3 * frob (Bm - Bj) * ‖trainV L p.1 p.2‖)) := by
        gcongr
        exact hmv.trans (mul_le_mul_of_nonneg_left hw (by positivity))
    _ = 12 * p.1 * frob (Bm - Bj) * ‖trainV L p.1 p.2‖ := by ring

end Clock

/-! ## 7. Assembly of `RingExpansionFull` -/

section Assembly

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- **`ringExpansionFullAt_of`**: at one regime, the four hypotheses with `ActualJetAt` and
`JetClockAt` give `RingExpansionFullAt` (source 5449-5483, 5496-5506). -/
theorem ringExpansionFullAt_of {CA CJ CC CS CW : ℝ} {kA kJ kC kS kW : ℕ}
    (hν1 : L.ν ≤ 1) (hε1 : L.ε ≤ 1)
    (hA : ActualJetAt Pl K L μ CA kA) (hJ : JetClockAt Pl K L μ CJ kJ)
    (hC : CoefReplaceAt Pl K L μ CC kC) (hS : RingSubstAt Pl K L μ CS kS)
    (hW : TrainMomentAt L CW kW) (hM : MeanSupportAt Pl K L μ) :
    RingExpansionFullAt Pl K L μ (|CC| + (|CS| + 12 * |CJ|) * |CW| + 1)
      (kC + kS + kJ + kW) := by
  intro T
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hP1 : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  rcases eq_or_ne (oldN1 Pl K L T) ⊤ with hN | hN
  · rw [hN, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.2 (by positivity)))]
    exact le_top
  obtain ⟨n, hn0, hnN⟩ : ∃ n : ℝ, 0 ≤ n ∧ oldN1 Pl K L T = ENNReal.ofReal n :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hN).symm⟩
  obtain ⟨hfm, hfb⟩ := hC T
  rw [hnN] at hfb
  obtain ⟨hWm, -, hWL⟩ := hW
  have hsplit : meanE Pl K L μ T - ringAff Pl K L μ T =
      (meanE Pl K L μ T - meanERaw Pl K L μ T) + (meanERaw Pl K L μ T - ringAff Pl K L μ T) :=
    (sub_add_sub_cancel _ _ _).symm
  set Kc : ℝ := (|CS| * L.ν⁻¹ ^ kS + 12 * |CJ| * L.ν⁻¹ ^ kJ) * L.ε ^ 4 * n with hKcdef
  have hKc : 0 ≤ Kc := by positivity
  have hYm : Measurable (youngWeight L) := by
    unfold youngWeight
    refine Measurable.indicator ?_ ?_
    · exact (measurable_fst.pow_const _).mul hWm
    · exact measurableSet_Ioc.preimage measurable_fst
  -- the pointwise bound of the raw-to-ring difference
  have hg : ∀ᵐ p ∂(srcMeasure (cOf L.ν)),
      ‖(meanERaw Pl K L μ T - ringAff Pl K L μ T) p‖ ≤ Kc * youngWeight L p := by
    filter_upwards [ae_srcMeasure_fst_pos (cOf L.ν)] with p hp0
    rw [Pi.sub_apply]
    by_cases hp1 : p.1 ≤ 1 / L.ν
    · have hW0 := trainWeight_nonneg 4 L p
      have hsr : 0 ≤ p.1 ^ (5 / 2 : ℝ) := Real.rpow_nonneg hp0.le _
      have h1 : ‖meanERaw Pl K L μ T p - ringAffJet Pl K L μ T p‖ ≤
          |CS| * (L.ν⁻¹ ^ kS * L.ε ^ 4 * p.1 ^ (5 / 2 : ℝ) * trainWeight 4 L p) * n := by
        have h := hS T p hp0 hp1
        rw [hnN, ← ofReal_norm, show CS * L.ν⁻¹ ^ kS * L.ε ^ 4 * p.1 ^ (5 / 2 : ℝ) *
            trainWeight 4 L p = CS * (L.ν⁻¹ ^ kS * L.ε ^ 4 * p.1 ^ (5 / 2 : ℝ) *
            trainWeight 4 L p) by ring] at h
        exact le_of_ofReal_le_mul (by positivity) hn0 h
      have hfr : frob (Bmat L.ν μ K.χf
            (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T) p.1 -
          Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) p.1) ≤
          |CJ| * (L.ν⁻¹ ^ kJ * L.ν * L.ε ^ 5 * p.1 ^ (5 / 2 : ℝ)) * n := by
        have h := (hJ T p.1 ⟨hp0, hp1⟩).2
        rw [hnN, show CJ * L.ν⁻¹ ^ kJ * L.ν * L.ε ^ 5 * p.1 ^ (5 / 2 : ℝ) =
            CJ * (L.ν⁻¹ ^ kJ * L.ν * L.ε ^ 5 * p.1 ^ (5 / 2 : ℝ)) by ring] at h
        exact le_of_ofReal_le_mul (by positivity) hn0 h
      have hv := trainV_le_weight 4 L hp0
      have h2 : ‖ringAffJet Pl K L μ T p - ringAff Pl K L μ T p‖ ≤
          12 * |CJ| * L.ν⁻¹ ^ kJ * L.ε ^ 4 * n * (p.1 ^ (5 / 2 : ℝ) * trainWeight 4 L p) := by
        have hc := norm_ringAffJet_sub_ringAff Pl K L μ T hp0
        have hsν : p.1 * L.ν ≤ 1 := by rwa [le_div_iff₀ hν] at hp1
        have he : p.1 * L.ν * L.ε ^ 5 ≤ L.ε ^ 4 :=
          calc p.1 * L.ν * L.ε ^ 5 ≤ 1 * L.ε ^ 5 :=
                mul_le_mul_of_nonneg_right hsν (by positivity)
            _ ≤ L.ε ^ 4 := by
                rw [one_mul]; exact pow_le_pow_of_le_one hε.le hε1 (by norm_num)
        have hF0 : 0 ≤ frob (Bmat L.ν μ K.χf
            (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T) p.1 -
          Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) p.1) := frob_nonneg _
        have ha : 0 ≤ 12 * |CJ| * L.ν⁻¹ ^ kJ * n * (p.1 ^ (5 / 2 : ℝ) * trainWeight 4 L p) := by
          positivity
        calc ‖ringAffJet Pl K L μ T p - ringAff Pl K L μ T p‖
            ≤ 12 * p.1 * (|CJ| * (L.ν⁻¹ ^ kJ * L.ν * L.ε ^ 5 * p.1 ^ (5 / 2 : ℝ)) * n) *
                trainWeight 4 L p := by
              refine hc.trans ?_
              gcongr
          _ = (12 * |CJ| * L.ν⁻¹ ^ kJ * n * (p.1 ^ (5 / 2 : ℝ) * trainWeight 4 L p)) *
                (p.1 * L.ν * L.ε ^ 5) := by ring
          _ ≤ (12 * |CJ| * L.ν⁻¹ ^ kJ * n * (p.1 ^ (5 / 2 : ℝ) * trainWeight 4 L p)) *
                L.ε ^ 4 := mul_le_mul_of_nonneg_left he ha
          _ = 12 * |CJ| * L.ν⁻¹ ^ kJ * L.ε ^ 4 * n * (p.1 ^ (5 / 2 : ℝ) * trainWeight 4 L p) := by
              ring
      rw [youngWeight_of_mem L hp0 hp1]
      calc ‖meanERaw Pl K L μ T p - ringAff Pl K L μ T p‖
          ≤ ‖meanERaw Pl K L μ T p - ringAffJet Pl K L μ T p‖ +
              ‖ringAffJet Pl K L μ T p - ringAff Pl K L μ T p‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ |CS| * (L.ν⁻¹ ^ kS * L.ε ^ 4 * p.1 ^ (5 / 2 : ℝ) * trainWeight 4 L p) * n +
              12 * |CJ| * L.ν⁻¹ ^ kJ * L.ε ^ 4 * n * (p.1 ^ (5 / 2 : ℝ) * trainWeight 4 L p) :=
            add_le_add h1 h2
        _ = Kc * (p.1 ^ (5 / 2 : ℝ) * trainWeight 4 L p) := by rw [hKcdef]; ring
    · have hlt : 1 / L.ν < p.1 := lt_of_not_ge hp1
      rw [hM T p hlt, ringAff_eq_zero_of_lt Pl K L μ T (hA T).2 hlt, sub_zero, norm_zero]
      exact mul_nonneg hKc (youngWeight_nonneg L p)
  have hG : AEStronglyMeasurable (fun p => Kc * youngWeight L p) (srcMeasure (cOf L.ν)) :=
    (hYm.const_mul Kc).aestronglyMeasurable
  have hmink := eLpNorm_add_le_of_ae_le hfm hG hg
  have hGn : eLpNorm (fun p => Kc * youngWeight L p) 2 (srcMeasure (cOf L.ν)) =
      ENNReal.ofReal Kc * eLpNorm (youngWeight L) 2 (srcMeasure (cOf L.ν)) := by
    rw [show (fun p => Kc * youngWeight L p) = Kc • youngWeight L from rfl,
      eLpNorm_const_smul, Real.enorm_of_nonneg hKc]
  rw [hGn] at hmink
  rw [hsplit, hnN]
  refine hmink.trans ?_
  -- real bookkeeping
  set E : ℝ := L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν) with hEdef
  have hE0 : 0 ≤ E := by positivity
  have b1 : ENNReal.ofReal (CC * L.ν⁻¹ ^ kC * E) * ENNReal.ofReal n ≤
      ENNReal.ofReal (|CC| * L.ν⁻¹ ^ kC * E * n) := by
    rw [← ENNReal.ofReal_mul' hn0]
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self CC) (by positivity)) hE0) hn0)
  have b2 : ENNReal.ofReal Kc * eLpNorm (youngWeight L) 2 (srcMeasure (cOf L.ν)) ≤
      ENNReal.ofReal (Kc * (|CW| * L.ν⁻¹ ^ kW)) := by
    rw [ENNReal.ofReal_mul hKc]
    refine mul_le_mul' le_rfl (hWL.trans (ENNReal.ofReal_le_ofReal ?_))
    exact mul_le_mul_of_nonneg_right (le_abs_self CW) (by positivity)
  refine (add_le_add (hfb.trans b1) b2).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have pa : L.ν⁻¹ ^ kC ≤ L.ν⁻¹ ^ (kC + kS + kJ + kW) := pow_le_pow_right₀ hP1 (by omega)
  have pb : L.ν⁻¹ ^ kS * L.ν⁻¹ ^ kW ≤ L.ν⁻¹ ^ (kC + kS + kJ + kW) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hP1 (by omega)
  have pc : L.ν⁻¹ ^ kJ * L.ν⁻¹ ^ kW ≤ L.ν⁻¹ ^ (kC + kS + kJ + kW) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hP1 (by omega)
  set Pf := L.ν⁻¹ ^ (kC + kS + kJ + kW) with hPf
  have hPf0 : 0 ≤ Pf := by positivity
  have he4 : 0 ≤ L.ε ^ 4 := by positivity
  rw [hKcdef]
  calc |CC| * L.ν⁻¹ ^ kC * E * n +
        (|CS| * L.ν⁻¹ ^ kS + 12 * |CJ| * L.ν⁻¹ ^ kJ) * L.ε ^ 4 * n * (|CW| * L.ν⁻¹ ^ kW)
      = (|CC| * E * n) * L.ν⁻¹ ^ kC + (|CS| * |CW| * L.ε ^ 4 * n) * (L.ν⁻¹ ^ kS * L.ν⁻¹ ^ kW) +
          (12 * |CJ| * |CW| * L.ε ^ 4 * n) * (L.ν⁻¹ ^ kJ * L.ν⁻¹ ^ kW) := by ring
    _ ≤ (|CC| * E * n) * Pf + (|CS| * |CW| * L.ε ^ 4 * n) * Pf +
          (12 * |CJ| * |CW| * L.ε ^ 4 * n) * Pf := by gcongr
    _ = Pf * n * (|CC| * E + (|CS| + 12 * |CJ|) * |CW| * L.ε ^ 4) := by ring
    _ ≤ Pf * n * ((|CC| + (|CS| + 12 * |CJ|) * |CW| + 1) * (L.ε ^ 4 + E)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h1 : 0 ≤ (|CS| + 12 * |CJ|) * |CW| := by positivity
        nlinarith [abs_nonneg CC]
    _ = (|CC| + (|CS| + 12 * |CJ|) * |CW| + 1) * Pf * (L.ε ^ 4 + E) * n := by ring

end Assembly

/-- **`ringExpansionFull_of`** along the sequence (source 5449-5483, 5496-5506). -/
theorem SeqData.ringExpansionFull_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h6 : D.ActualJet) (h7 : D.JetClock) (hC : D.CoefReplace) (hS : D.RingSubst)
    (hW : D.TrainMoment) (hM : D.MeanSupport) : D.RingExpansionFull := by
  obtain ⟨CA, kA, e6⟩ := h6
  obtain ⟨CJ, kJ, e7⟩ := h7
  obtain ⟨CC, kC, eC⟩ := hC
  obtain ⟨CS, kS, eS⟩ := hS
  obtain ⟨CW, kW, eW⟩ := hW
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  refine ⟨|CC| + (|CS| + 12 * |CJ|) * |CW| + 1, kC + kS + kJ + kW, ?_⟩
  filter_upwards [e6, e7, eC, eS, eW, hM, hle] with n a6 a7 aC aS aW aM hν z hz
  exact ringExpansionFullAt_of D.Pl D.K (D.level n) (D.mu n z) hν.1 hν.2 (a6 z hz) (a7 z hz)
    (aC z hz) (aS z hz) aW (aM z hz)

end UnforcedLeray.Short.PartIIIb.Concrete
