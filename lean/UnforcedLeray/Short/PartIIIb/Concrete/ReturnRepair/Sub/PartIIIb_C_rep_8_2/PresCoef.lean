import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2Org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.SecondJet

/-!
# The exact-pressure and repair-coefficient errors of the mean residual
(`PartIII-b:C/rep/8/2/pres/org`, source 5272-5289, 5494-5506)

Source of record: `the November 2 reference manuscript` (73 pages).

`CoefReplaceAt` (`Sub/PartIII-b_C_rep_8_2Org.lean`) bounds `meanE - meanERaw`: the mean Ward
residual on the exact background `U = V + r_b` with its exact pressure `p` (`L.U`, `L.pres`) minus
the same residual with the raw coefficient `U_raw` (`rawU`) and the flat lifted pressure
`p_lift = s·p_cyl` (`liftP`, `p_raw = (R/r)²p`, source 1217), with the same mean fields
`X^mt, Y^mt` (`Xmean`, `Ymean`).  The source estimate (5272-5289):

* `∇(p_raw - p_lift) = -(I-ℙ)F_raw`; the entrance convection terms and the explicit radial
  pressure completion give `‖∇p - G_flat‖_{Y_{11/4}} ≤ P_ν ε^{3/11}e^{m₀/ν}`, `G_flat = ∇p_lift`
  (`PresFlatAt`);
* `U - U_raw = r_b + E_εα_bg` (2669, `IIb.ExactSplitII`): "Nonpressure repair and entrance
  coefficient changes are bounded in the same way" (5287-5289), i.e.
  `Σ_{j≤2}‖D^j(U - U_raw)‖_{Y_{11/4}} ≤ P_νρ` (5134-5139 for `r_b`), with `|U| + |U_raw| ≤ P_ν`
  for the quadratic term `(U⊗U):D²X` (`CoefChgAt`);
* "The general thin-source estimate is `‖DX‖_{L^∞_τL^{22/3}} ≤ P_ν ε^{57/22}N₁`" (5282-5284), for
  the mean field, together with `DY` and `D²X` (which "have an additional curvature power",
  5267-5268; the same pair `DX, DY` as `repair:phase-gradient`, 5214-5217) (`MeanGradAt`);
* "Hölder and `R⁻¹ = ε` give the exponent `1 + 3/11 + 57/22 = 85/22`" (5285-5287), `4/11 + 3/22 =
  1/2` (5261).

**The `Y_r` norms in the ring chart.**  For a field of `(τ, y)` invariant under rotations about the
axis (the exact background, its pressure, the lifts and the mean fields are axisymmetric) the
normalized phase/space integral is `πR²∫|f|^r s^{-5/2} ds dq/c dη` over one `q`-cell ("the
physical space Jacobian after azimuthal integration is `πR²s^{-5/2}ds dη` and normalized phase
becomes `dq/c`", source 2681-2688; `Axi.lintegral_Nv_rpow`, `phaseAvg_ringChart`).  So
`‖f‖_{Y_r} = ‖ringRead R f‖_{L^r(ringPhysμ R c)}`, `ringPhysμ R c = πR²·ageμ c (-5/2)`,
`ringRead R f` the value of `f` at the chart point (`τ = 2q/R + log s`,
`y = (R/√s, 0, η/√s)`).  The joint `L^{22/3}` norm over one normalized period is at most the
`L^∞_τL^{22/3}` norm of the source (and equal to it for the phase-independent mean fields).

**Leaves.** `WardEXYChgPt` (algebra of the four Ward terms), `RingHolderConv` (Hölder and the
chart change of variables `‖coefOf R F‖_{L²(srcMeasure)} ≤ R⁻¹‖F‖_{Y_2}`), the source facts
`PresFlatAt`, `CoefChgAt`, `MeanGradAt`, and `MeanResMeasAt` (measurability).

**Proved here:** `coefReplaceAt_of`, `SeqData.coefReplace_of` (the `CoefReplace` hypothesis of
`SeqData.ringExpansionFull_of`), the composition `SeqData.ringExpansion_of_leaves`, and
`SeqData.ringExpansion_of_full` (`RingExpansionAt` of
`Sub/PartIII-b_C_rep_8_org.lean` now carries the source bound `P_ν N(ε⁴ + ε^{85/22}e^{m₀/ν})`, the
bound of `RingExpansionFullAt`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. The densities and the ring-chart form of the physical norms -/

/-- The coefficient-change density `|U₁ - U₂| + |DU₁ - DU₂| + |D²U₁ - D²U₂|` at `y` (source
5287-5289: the repair and entrance coefficient changes, `U₁ = U`, `U₂ = U_raw`), with operator
norms of the first and second derivative, which are invariant under rotations about the axis
(equivalent to the coordinate sums up to the constants `3` and `9`, absorbed in `P_ν`).  The second
derivative is `secondJet`, which equals `fderiv (fderiv U) y` as soon as `fderiv U` is
differentiable at `y` (`secondJet_eq_fderiv`). -/
def coefChgDens (U₁ U₂ : Space → Space) (y : Space) : ℝ :=
  ‖U₁ y - U₂ y‖ + ‖fderiv ℝ U₁ y - fderiv ℝ U₂ y‖ + ‖secondJet U₁ y - secondJet U₂ y‖

/-- The pressure-change density `|∇p₁ - ∇p₂|` at `y` (source 5274-5281: `p₁ = p` the exact
pressure, `∇p₂ = G_flat = ∇p_lift`). -/
def presChgDens (p₁ p₂ : Space → ℝ) (y : Space) : ℝ := ‖physGrad p₁ y - physGrad p₂ y‖

/-- The jet density `|DY| + Σ_j|∂_jX| + Σ_{j,l}|∂_j∂_lX|` of a response `(X, Y)` at `y`
(source 5214-5217, 5267-5268, 5282-5284). -/
def meanJetDens (X Y : Space → Space) (y : Space) : ℝ :=
  ‖fderiv ℝ Y y‖ + ∑ j : Fin 3, ‖physPd X j y‖ + ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 X j l y‖

/-- The ring-chart form `πR² s^{-5/2} ds dq/c dη` (on `(0,∞) × cell`) of the normalized
phase/space measure, for fields invariant under rotations about the axis (source 2681-2688,
`Axi.lintegral_Nv_rpow`). -/
def ringPhysμ (R c : ℝ) : Measure Chart :=
  ENNReal.ofReal (Real.pi * R ^ 2) • ageμ c (-5 / 2)

/-- A physical scalar `f(τ, y)` read at the chart point `p = (s, (q, η))`: `τ = 2q/R + log s`,
`y = (R/√s, 0, η/√s)` (azimuth `0`, source 2670-2674). -/
def ringRead (R : ℝ) (f : ℝ → Space → ℝ) : Chart → ℝ :=
  fun p => f (NearInst.chartTau R p) (NearInst.chartY R p)

theorem coefChgDens_nonneg (U₁ U₂ : Space → Space) (y : Space) : 0 ≤ coefChgDens U₁ U₂ y := by
  unfold coefChgDens; positivity

theorem presChgDens_nonneg (p₁ p₂ : Space → ℝ) (y : Space) : 0 ≤ presChgDens p₁ p₂ y := by
  unfold presChgDens; positivity

theorem meanJetDens_nonneg (X Y : Space → Space) (y : Space) : 0 ≤ meanJetDens X Y y := by
  unfold meanJetDens; positivity

/-! ## 2. The two general leaves -/

/-- **The pointwise form of the coefficient and pressure changes** (algebra; the four Ward terms
`2U·∇Y - 2νC_diff + (U⊗U):D²X - (DX+DXᵀ)∇p` of source 4276-4282): `2U·∇Y`, `C_diff` and
`(DX+DXᵀ)∇p` are linear in `(U, DU, D²U)`, resp. `∇p`, and
`|U₁ⱼU₁ₗ - U₂ⱼU₂ₗ| ≤ |U₁ - U₂|(|U₁| + |U₂|)`, so the change of the residual when `(U, p)` is
replaced by `(U₂, p₂)` with the same response `(X, Y)` is at most an absolute multiple of
`(1 + |ν| + |U₁| + |U₂|)·(coefficient + pressure change)·(jet of the response)`. -/
def WardEXYChgPt : Prop :=
  ∀ (ν μ R : ℝ) (U₁ U₂ : ℝ → SpatialField) (p₁ p₂ : ℝ → Space → ℝ)
    (X Y : ℝ → Space → Space) (τ : ℝ) (y : Space),
    ‖wardEXY ν μ R U₁ p₁ X Y τ y - wardEXY ν μ R U₂ p₂ X Y τ y‖ ≤
      100 * (1 + |ν| + ‖U₁ τ y‖ + ‖U₂ τ y‖) *
        (coefChgDens (U₁ τ) (U₂ τ) y + presChgDens (p₁ τ) (p₂ τ) y) * meanJetDens (X τ) (Y τ) y

/-- **Hölder in the ring chart** (source 2681-2688, 5261, 5285-5287): if at every chart point
`|F| ≤ a·b`, then `‖coefOf R F‖_{L²(srcMeasure)} ≤ R⁻¹‖a‖_{Y_{11/4}}‖b‖_{Y_{22/3}}` with the
`Y_r` norms in chart form.  Indeed `|coefOf R F| ≤ s^{-1/2}|F|` and `srcMeasure c =
π ageμ c (-3/2)`, so `‖coefOf R F‖²_{L²(srcMeasure)} ≤ π∫|F|²s^{-5/2} = R⁻²‖F‖²_{L²(ringPhysμ)}`,
and `4/11 + 3/22 = 1/2`. -/
def RingHolderConv : Prop :=
  ∀ (R c : ℝ), 0 < R → 0 < c → ∀ (F : ℝ → Space → Space) (a b : ℝ → Space → ℝ),
    AEStronglyMeasurable (ringRead R a) (ringPhysμ R c) →
    AEStronglyMeasurable (ringRead R b) (ringPhysμ R c) →
    (∀ p : Chart, 0 < p.1 →
      ‖F (NearInst.chartTau R p) (NearInst.chartY R p)‖ ≤ ringRead R a p * ringRead R b p) →
    eLpNorm (coefOf R F) 2 (srcMeasure c) ≤
      ENNReal.ofReal R⁻¹ * eLpNorm (ringRead R a) (11 / 4) (ringPhysμ R c) *
        eLpNorm (ringRead R b) (22 / 3) (ringPhysμ R c)

/-- **The `L²` chart step** (source 2681-2688, 5470-5476; the first half of the proof of
`RingHolderConv`): if at every chart point `|F| ≤ g`, then
`‖coefOf R F‖_{L²(srcMeasure)} ≤ R⁻¹‖g‖_{Y_2}` with the `Y_2` norm in chart form.  Indeed
`|coefOf R F| ≤ s^{-1/2}|F|` and `srcMeasure c = π ageμ c (-3/2)`. -/
def RingL2Conv : Prop :=
  ∀ (R c : ℝ), 0 < R → 0 < c → ∀ (F : ℝ → Space → Space) (g : ℝ → Space → ℝ),
    (∀ p : Chart, 0 < p.1 →
      ‖F (NearInst.chartTau R p) (NearInst.chartY R p)‖ ≤ ringRead R g p) →
    eLpNorm (coefOf R F) 2 (srcMeasure c) ≤
      ENNReal.ofReal R⁻¹ * eLpNorm (ringRead R g) 2 (ringPhysμ R c)

/-! ## 3. The source leaves at one regime (`R = ε⁻¹`, `c = ν⁻²`, `ρ = ε^{3/11}e^{m₀/ν}`) -/

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- **The exact pressure against the flat lifted pressure** (source 5272-5281):
`∇(p_raw - p_lift) = -(I-ℙ)F_raw`, and with the entrance convection terms and the explicit radial
pressure completion `‖∇p - G_flat‖_{Y_{11/4}} ≤ P_ν ε^{3/11}e^{m₀/ν}`; here `p = L.pres` and
`G_flat = ∇p_lift`, `p_lift = s·p_cyl` (`liftP`), the `Y_{11/4}` norm in chart form. -/
def PresFlatAt (C : ℝ) (k : ℕ) : Prop :=
  AEStronglyMeasurable (ringRead L.ε⁻¹ fun τ => presChgDens (L.pres τ) (liftP L τ))
      (ringPhysμ L.ε⁻¹ (cOf L.ν)) ∧
    eLpNorm (ringRead L.ε⁻¹ fun τ => presChgDens (L.pres τ) (liftP L τ)) (11 / 4)
        (ringPhysμ L.ε⁻¹ (cOf L.ν)) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * rhoRep K L)

/-- **The repair coefficient change** (source 5287-5289 with 5134-5139): `U - V = r_b`
(`ReturnLevel.U`), and the `Y_{11/4}` norm of `|U - V| + |D(U - V)| + |D²(U - V)|` is `≤ P_νρ`
(`RepairDerivBound`, `IIb.ExactSplitII.energy`); and `|U| + |V| + |U_raw| ≤ P_ν` at every chart
point (`sup √s W|v| ≤ P_ν`, 2715-2725; `δ_U`, 5007-5008).  The entrance part `V - U_raw =
E_εα_bg` is *not* in `Y_{11/4}` (its nonzero inlet, source 2346-2347, 2389-2390); it is handled in
`EntJetAt` by the pointwise `W^{2,∞}` bound and the `L²` pairing with the mean jet. -/
def CoefChgAt (C : ℝ) (k : ℕ) : Prop :=
  AEStronglyMeasurable (ringRead L.ε⁻¹ fun τ => coefChgDens (L.U τ) (L.V τ))
      (ringPhysμ L.ε⁻¹ (cOf L.ν)) ∧
    eLpNorm (ringRead L.ε⁻¹ fun τ => coefChgDens (L.U τ) (L.V τ)) (11 / 4)
        (ringPhysμ L.ε⁻¹ (cOf L.ν)) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * rhoRep K L) ∧
    ∀ p : Chart, 0 < p.1 →
      ‖L.U (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)‖ +
          ‖L.V (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)‖ +
          ‖rawU Pl L (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)‖ ≤
        C * L.ν⁻¹ ^ k

/-- **The general thin-source gradient estimate for the mean field** (source 5282-5284:
`‖DX‖_{L^∞_τL^{22/3}} ≤ P_ν ε^{57/22}N₁`; with `DY` as in `repair:phase-gradient`, 5214-5217, and
`D²X`, which has an additional curvature power, 5267-5268): for `X^mt, Y^mt` of `χ_oT₁`
(`Xmean`, `Ymean` of `thinRep T`), the `Y_{22/3}` norm (chart form) of
`|DY^mt| + |DX^mt| + |D²X^mt|` is `≤ P_ν ε^{57/22} N`, `N = N₁(χ_oT₁)` (`oldN1`). -/
def MeanGradAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L,
    AEStronglyMeasurable (ringRead L.ε⁻¹ fun τ =>
        meanJetDens (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) τ)
          (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) τ))
      (ringPhysμ L.ε⁻¹ (cOf L.ν)) ∧
    eLpNorm (ringRead L.ε⁻¹ fun τ =>
        meanJetDens (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) τ)
          (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) τ)) (22 / 3)
        (ringPhysμ L.ε⁻¹ (cOf L.ν)) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ (57 / 22 : ℝ)) * oldN1 Pl K L T

/-- **The entrance coefficient change against the mean jet** (source 2389-2390, 2519-2520,
5402-5404, 5440-5446, 5470-5476): `V - U_raw = E_εα_bg` with `|E_εα|_{W^{j,∞}} ≤ P_ν|α|`,
`|α| ≤ P_ν e^{m₀/ν}ε`, exponential transverse decay, and the mean jet `|D_yX^mt| ≤ |A_T| +
P ε⁴s^{5/2}|η|N`, `|A_T| ≤ Cε³s^{5/2}N`, `A_T = 0` for `s ≥ 1/ν`, in the density
`πs^{-5/2}ds dη`: the `Y_2` norm (chart form) of `|V - U_raw|_{W^{2}}·|jet|` is
`≤ P_ν ε³e^{m₀/ν}N`. -/
def EntJetAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L,
    eLpNorm (ringRead L.ε⁻¹ fun τ y => coefChgDens (L.V τ) (rawU Pl L τ) y *
        meanJetDens (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) τ)
          (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) τ) y) 2
        (ringPhysμ L.ε⁻¹ (cOf L.ν)) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 3 * Real.exp (K.m0 / L.ν))) * oldN1 Pl K L T

/-- The mean Ward residual field with coefficient `U'` and pressure `p'` (the integrand of
`meanE`, `meanERaw`). -/
def meanWard (T : LStr Pl K L) (U' : ℝ → SpatialField) (p' : ℝ → Space → ℝ) :
    ℝ → Space → Space :=
  wardEXY L.ν μ L.ε⁻¹ U' p' (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T))
    (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T))

/-- **Measurability of the coefficient change of the mean residual** (the fields are smooth
off the axis: `IsExactProfile`, the raw lift 1217-1222, the Newton field `X^mt`; Carathéodory). -/
def MeanResMeasAt : Prop :=
  ∀ T : LStr Pl K L,
    AEStronglyMeasurable (meanE Pl K L μ T - meanERaw Pl K L μ T) (srcMeasure (cOf L.ν))

/-- **Measurability of the two parts of the coefficient change** (same reason, with `V = U_raw +
E_εα` smooth off the axis: `rawU_contDiffOn_offAxis_of`, `IIb.inletContDiff`): of the repair and
pressure change `(U, p) → (V, p_lift)` and of the entrance change `V → U_raw`. -/
def MeanResSplitMeasAt : Prop :=
  ∀ T : LStr Pl K L,
    AEStronglyMeasurable (coefOf L.ε⁻¹ (fun τ y =>
      meanWard Pl K L μ T L.U L.pres τ y - meanWard Pl K L μ T L.V (liftP L) τ y))
      (srcMeasure (cOf L.ν)) ∧
    AEStronglyMeasurable (coefOf L.ε⁻¹ (fun τ y =>
      meanWard Pl K L μ T L.V (liftP L) τ y - meanWard Pl K L μ T (rawU Pl L) (liftP L) τ y))
      (srcMeasure (cOf L.ν))

end Regime

namespace SeqData

variable (D : SeqData)

/-- The pressure replacement along the sequence. -/
def PresFlat : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, PresFlatAt D.K (D.level n) C k

/-- The coefficient changes along the sequence. -/
def CoefChg : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, CoefChgAt D.Pl D.K (D.level n) C k

/-- The mean gradient estimate along the sequence. -/
def MeanGrad : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    MeanGradAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- The entrance-against-jet estimate along the sequence. -/
def EntJet : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    EntJetAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- The split measurability along the sequence. -/
def MeanResSplitMeas : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, MeanResSplitMeasAt D.Pl D.K (D.level n) (D.mu n z)

/-- The measurability along the sequence. -/
def MeanResMeas : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, MeanResMeasAt D.Pl D.K (D.level n) (D.mu n z)

end SeqData

/-! ## 4. The reduction -/

theorem coefOf_sub_eq (R : ℝ) (F G : ℝ → Space → Space) :
    coefOf R F - coefOf R G = coefOf R (fun τ y => F τ y - G τ y) := by
  funext p
  simp only [Pi.sub_apply, coefOf, ← smul_sub]
  congr 1
  ext i
  fin_cases i <;> simp

theorem pnu_le_pnu {ν C C' x : ℝ} {k k' : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hx : 0 ≤ x)
    (hC : C ≤ C') (hC' : 0 ≤ C') (hk : k ≤ k') : C * ν⁻¹ ^ k * x ≤ C' * ν⁻¹ ^ k' * x := by
  have h1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hP : ν⁻¹ ^ k ≤ ν⁻¹ ^ k' := pow_le_pow_right₀ h1 hk
  have hP0 : 0 ≤ ν⁻¹ ^ k := by positivity
  calc C * ν⁻¹ ^ k * x ≤ C' * ν⁻¹ ^ k * x :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hP0) hx
    _ ≤ C' * ν⁻¹ ^ k' * x :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP hC') hx

theorem rhoRep_nonneg (K : ReturnConsts) (L : ReturnLevel) : 0 ≤ rhoRep K L := by
  have := L.ε_pos
  unfold rhoRep
  positivity

section Mono

variable {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}

theorem PresFlatAt.mono {C C' : ℝ} {k k' : ℕ} (h : PresFlatAt K L C k) (hν1 : L.ν ≤ 1)
    (hC : C ≤ C') (hC' : 0 ≤ C') (hk : k ≤ k') : PresFlatAt K L C' k' :=
  ⟨h.1, h.2.trans (ENNReal.ofReal_le_ofReal
    (pnu_le_pnu L.ν_pos hν1 (rhoRep_nonneg K L) hC hC' hk))⟩

theorem CoefChgAt.mono {C C' : ℝ} {k k' : ℕ} (h : CoefChgAt Pl K L C k) (hν1 : L.ν ≤ 1)
    (hC : C ≤ C') (hC' : 0 ≤ C') (hk : k ≤ k') : CoefChgAt Pl K L C' k' := by
  refine ⟨h.1, h.2.1.trans (ENNReal.ofReal_le_ofReal
    (pnu_le_pnu L.ν_pos hν1 (rhoRep_nonneg K L) hC hC' hk)), fun p hp => (h.2.2 p hp).trans ?_⟩
  have := pnu_le_pnu L.ν_pos hν1 zero_le_one hC hC' hk
  simpa only [mul_one] using this

theorem EntJetAt.mono {C C' : ℝ} {k k' : ℕ} (h : EntJetAt Pl K L μ C k) (hν1 : L.ν ≤ 1)
    (hC : C ≤ C') (hC' : 0 ≤ C') (hk : k ≤ k') : EntJetAt Pl K L μ C' k' := by
  intro T
  have hε := L.ε_pos
  exact (h T).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
    (pnu_le_pnu L.ν_pos hν1 (by positivity) hC hC' hk)) le_rfl)

theorem MeanGradAt.mono {C C' : ℝ} {k k' : ℕ} (h : MeanGradAt Pl K L μ C k) (hν1 : L.ν ≤ 1)
    (hC : C ≤ C') (hC' : 0 ≤ C') (hk : k ≤ k') : MeanGradAt Pl K L μ C' k' := by
  intro T
  have hε := L.ε_pos
  refine ⟨(h T).1, (h T).2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
    (pnu_le_pnu L.ν_pos hν1 (by positivity) hC hC' hk)) le_rfl)⟩

end Mono

section Reduction

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- **`coefReplaceAt_of`**: the pointwise algebra, Hölder in the ring chart and the source
estimates give the exact-pressure and repair-coefficient bound
`‖meanE - meanERaw‖ ≤ P_ν ε^{85/22}e^{m₀/ν}N`.  The difference of the residuals splits as
`[wardEXY(U,p) - wardEXY(V,p_lift)] + [wardEXY(V,p_lift) - wardEXY(U_raw,p_lift)]`: the first
(repair and pressure change) by Hölder with exponent `1 + 3/11 + 57/22`, the second (entrance
change, not in `Y_{11/4}`) by the `L²` pairing `EntJetAt` with exponent `4 ≥ 85/22`. -/
theorem coefReplaceAt_of (hν1 : L.ν ≤ 1) (hε1 : L.ε ≤ 1) {C : ℝ} (hC : 0 ≤ C) {k : ℕ}
    (hpt : WardEXYChgPt) (hconv : RingHolderConv) (hl2 : RingL2Conv)
    (h0 : MeanResMeasAt Pl K L μ) (h0s : MeanResSplitMeasAt Pl K L μ)
    (h1 : PresFlatAt K L C k) (h2 : CoefChgAt Pl K L C k) (h3 : MeanGradAt Pl K L μ C k)
    (h4 : EntJetAt Pl K L μ C k) :
    CoefReplaceAt Pl K L μ (200 * C ^ 2 * (2 + C) + 100 * C * (2 + C)) (3 * k) := by
  intro T
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hR : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hV1 : 1 ≤ L.ν⁻¹ ^ k := one_le_pow₀ ((one_le_inv₀ hν).2 hν1)
  obtain ⟨hmb, hnb⟩ := h3 T
  obtain ⟨hm1, hm2⟩ := h0s T
  set Xm := Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) with hXm
  set Ym := Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) with hYm
  set P : ℝ := C * L.ν⁻¹ ^ k with hPdef
  have hP0 : 0 ≤ P := by positivity
  set A : ℝ := 100 * (1 + L.ν + P) with hAdef
  have hA0 : 0 ≤ A := by positivity
  set fc : Chart → ℝ := ringRead L.ε⁻¹ fun τ => coefChgDens (L.U τ) (L.V τ) with hfc
  set fp : Chart → ℝ := ringRead L.ε⁻¹ fun τ => presChgDens (L.pres τ) (liftP L τ) with hfp
  set a : ℝ → Space → ℝ := fun τ y =>
    A * (coefChgDens (L.U τ) (L.V τ) y + presChgDens (L.pres τ) (liftP L τ) y) with ha
  set b : ℝ → Space → ℝ := fun τ y => meanJetDens (Xm τ) (Ym τ) y with hb
  set Fa : ℝ → Space → Space := meanWard Pl K L μ T L.U L.pres with hFa
  set Fb : ℝ → Space → Space := meanWard Pl K L μ T L.V (liftP L) with hFb
  set Fc : ℝ → Space → Space := meanWard Pl K L μ T (rawU Pl L) (liftP L) with hFc
  set μp := ringPhysμ L.ε⁻¹ (cOf L.ν) with hμp
  set F1 : ℝ → Space → Space := fun τ y => Fa τ y - Fb τ y with hF1
  set F2 : ℝ → Space → Space := fun τ y => Fb τ y - Fc τ y with hF2
  have hEq : meanE Pl K L μ T - meanERaw Pl K L μ T = coefOf L.ε⁻¹ F1 + coefOf L.ε⁻¹ F2 := by
    have e1 : meanE Pl K L μ T - meanERaw Pl K L μ T =
        coefOf L.ε⁻¹ Fa - coefOf L.ε⁻¹ Fc := rfl
    have e2 := coefOf_sub_eq L.ε⁻¹ Fa Fb
    have e3 := coefOf_sub_eq L.ε⁻¹ Fb Fc
    rw [e1]
    show _ = coefOf L.ε⁻¹ (fun τ y => Fa τ y - Fb τ y) +
      coefOf L.ε⁻¹ (fun τ y => Fb τ y - Fc τ y)
    rw [← e2, ← e3]
    abel
  have hhalf1 : eLpNorm (coefOf L.ε⁻¹ F1) 2 (srcMeasure (cOf L.ν)) ≤
      ENNReal.ofReal (200 * C ^ 2 * (2 + C) * L.ν⁻¹ ^ (3 * k) *
        (L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν))) * oldN1 Pl K L T := by
    have hra : ringRead L.ε⁻¹ a = A • (fc + fp) := by
      funext p
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      rfl
    have hma : AEStronglyMeasurable (ringRead L.ε⁻¹ a) μp := by
      rw [hra]; exact (h2.1.add h1.1).const_smul A
    have hpw : ∀ p : Chart, 0 < p.1 →
        ‖F1 (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)‖ ≤
          ringRead L.ε⁻¹ a p * ringRead L.ε⁻¹ b p := by
      intro p hp
      set τ := NearInst.chartTau L.ε⁻¹ p
      set y := NearInst.chartY L.ε⁻¹ p
      have e := hpt L.ν μ L.ε⁻¹ L.U L.V L.pres (liftP L) Xm Ym τ y
      have hU := h2.2.2 p hp
      have hS : 0 ≤ coefChgDens (L.U τ) (L.V τ) y + presChgDens (L.pres τ) (liftP L τ) y :=
        add_nonneg (coefChgDens_nonneg _ _ _) (presChgDens_nonneg _ _ _)
      have hJ : 0 ≤ meanJetDens (Xm τ) (Ym τ) y := meanJetDens_nonneg _ _ _
      have hle : 100 * (1 + |L.ν| + ‖L.U τ y‖ + ‖L.V τ y‖) ≤ A := by
        rw [abs_of_pos hν, hAdef]
        linarith [hU, norm_nonneg (rawU Pl L τ y)]
      calc ‖F1 τ y‖ ≤ 100 * (1 + |L.ν| + ‖L.U τ y‖ + ‖L.V τ y‖) *
            (coefChgDens (L.U τ) (L.V τ) y + presChgDens (L.pres τ) (liftP L τ) y) *
              meanJetDens (Xm τ) (Ym τ) y := e
        _ ≤ A * (coefChgDens (L.U τ) (L.V τ) y + presChgDens (L.pres τ) (liftP L τ) y) *
              meanJetDens (Xm τ) (Ym τ) y :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hS) hJ
        _ = ringRead L.ε⁻¹ a p * ringRead L.ε⁻¹ b p := rfl
    have hc' := hconv L.ε⁻¹ (cOf L.ν) hR hc F1 a b hma hmb hpw
    have h114 : (1 : ℝ≥0∞) ≤ 11 / 4 := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num
    have hna : eLpNorm (ringRead L.ε⁻¹ a) (11 / 4) μp ≤
        ENNReal.ofReal A * (ENNReal.ofReal (P * rhoRep K L) + ENNReal.ofReal (P * rhoRep K L)) := by
      rw [hra, eLpNorm_const_smul, Real.enorm_eq_ofReal hA0]
      gcongr
      exact (eLpNorm_add_le h2.1 h1.1 h114).trans (add_le_add h2.2.1 h1.2)
    have hρ0 := rhoRep_nonneg K L
    have hx : 0 ≤ P * rhoRep K L := mul_nonneg hP0 hρ0
    have hy : 0 ≤ P * L.ε ^ (57 / 22 : ℝ) := by positivity
    have hεpow : L.ε * L.ε ^ (3 / 11 : ℝ) * L.ε ^ (57 / 22 : ℝ) = L.ε ^ (85 / 22 : ℝ) := by
      rw [show (85 / 22 : ℝ) = 1 + 3 / 11 + 57 / 22 by norm_num, Real.rpow_add hε,
        Real.rpow_add hε, Real.rpow_one]
    have h1νP : 1 + L.ν + P ≤ (2 + C) * L.ν⁻¹ ^ k := by
      rw [hPdef]; linarith
    have hreal : L.ε * (A * (P * rhoRep K L + P * rhoRep K L)) * (P * L.ε ^ (57 / 22 : ℝ)) ≤
        200 * C ^ 2 * (2 + C) * L.ν⁻¹ ^ (3 * k) *
          (L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν)) := by
      have hE0 : 0 ≤ L.ε * L.ε ^ (3 / 11 : ℝ) * L.ε ^ (57 / 22 : ℝ) * Real.exp (K.m0 / L.ν) := by
        positivity
      calc L.ε * (A * (P * rhoRep K L + P * rhoRep K L)) * (P * L.ε ^ (57 / 22 : ℝ))
          = 200 * P ^ 2 * (1 + L.ν + P) *
              (L.ε * L.ε ^ (3 / 11 : ℝ) * L.ε ^ (57 / 22 : ℝ) * Real.exp (K.m0 / L.ν)) := by
            rw [hAdef, rhoRep]
            ring
        _ ≤ 200 * P ^ 2 * ((2 + C) * L.ν⁻¹ ^ k) *
              (L.ε * L.ε ^ (3 / 11 : ℝ) * L.ε ^ (57 / 22 : ℝ) * Real.exp (K.m0 / L.ν)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1νP (by positivity)) hE0
        _ = 200 * C ^ 2 * (2 + C) * L.ν⁻¹ ^ (3 * k) *
              (L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν)) := by
            rw [← hεpow, pow_mul', hPdef]
            ring
    calc eLpNorm (coefOf L.ε⁻¹ F1) 2 (srcMeasure (cOf L.ν))
        ≤ ENNReal.ofReal L.ε⁻¹⁻¹ * eLpNorm (ringRead L.ε⁻¹ a) (11 / 4) μp *
            eLpNorm (ringRead L.ε⁻¹ b) (22 / 3) μp := hc'
      _ ≤ ENNReal.ofReal L.ε *
            (ENNReal.ofReal A * (ENNReal.ofReal (P * rhoRep K L) +
              ENNReal.ofReal (P * rhoRep K L))) *
            (ENNReal.ofReal (P * L.ε ^ (57 / 22 : ℝ)) * oldN1 Pl K L T) := by
          rw [inv_inv]
          exact mul_le_mul' (mul_le_mul' le_rfl hna) hnb
      _ = ENNReal.ofReal (L.ε * (A * (P * rhoRep K L + P * rhoRep K L)) *
            (P * L.ε ^ (57 / 22 : ℝ))) * oldN1 Pl K L T := by
          rw [← ENNReal.ofReal_add hx hx, ← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_mul hε.le,
            ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (200 * C ^ 2 * (2 + C) * L.ν⁻¹ ^ (3 * k) *
            (L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν))) * oldN1 Pl K L T := by
          gcongr
  have hhalf2 : eLpNorm (coefOf L.ε⁻¹ F2) 2 (srcMeasure (cOf L.ν)) ≤
      ENNReal.ofReal (100 * C * (2 + C) * L.ν⁻¹ ^ (3 * k) *
        (L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν))) * oldN1 Pl K L T := by
    set d : ℝ → Space → ℝ := fun τ y => coefChgDens (L.V τ) (rawU Pl L τ) y *
      meanJetDens (Xm τ) (Ym τ) y with hd
    set g : ℝ → Space → ℝ := fun τ y => A * d τ y with hg
    have hrg : ringRead L.ε⁻¹ g = A • ringRead L.ε⁻¹ d := by
      funext p
      simp only [Pi.smul_apply, smul_eq_mul]
      rfl
    have hpw : ∀ p : Chart, 0 < p.1 →
        ‖F2 (NearInst.chartTau L.ε⁻¹ p) (NearInst.chartY L.ε⁻¹ p)‖ ≤ ringRead L.ε⁻¹ g p := by
      intro p hp
      set τ := NearInst.chartTau L.ε⁻¹ p
      set y := NearInst.chartY L.ε⁻¹ p
      have e := hpt L.ν μ L.ε⁻¹ L.V (rawU Pl L) (liftP L) (liftP L) Xm Ym τ y
      have hU := h2.2.2 p hp
      have hz : presChgDens (liftP L τ) (liftP L τ) y = 0 := by
        unfold presChgDens; simp
      have hJ : 0 ≤ meanJetDens (Xm τ) (Ym τ) y := meanJetDens_nonneg _ _ _
      have hS : 0 ≤ coefChgDens (L.V τ) (rawU Pl L τ) y := coefChgDens_nonneg _ _ _
      have hle : 100 * (1 + |L.ν| + ‖L.V τ y‖ + ‖rawU Pl L τ y‖) ≤ A := by
        rw [abs_of_pos hν, hAdef]
        linarith [hU, norm_nonneg (L.U τ y)]
      rw [hz, add_zero] at e
      calc ‖F2 τ y‖ ≤ 100 * (1 + |L.ν| + ‖L.V τ y‖ + ‖rawU Pl L τ y‖) *
            coefChgDens (L.V τ) (rawU Pl L τ) y * meanJetDens (Xm τ) (Ym τ) y := e
        _ ≤ A * coefChgDens (L.V τ) (rawU Pl L τ) y * meanJetDens (Xm τ) (Ym τ) y :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hS) hJ
        _ = ringRead L.ε⁻¹ g p := by
            show _ = A * (coefChgDens (L.V τ) (rawU Pl L τ) y * meanJetDens (Xm τ) (Ym τ) y)
            ring
    have hc' := hl2 L.ε⁻¹ (cOf L.ν) hR hc F2 g hpw
    have hdn := h4 T
    have hρ0 : 0 ≤ P * (L.ε ^ 3 * Real.exp (K.m0 / L.ν)) := by positivity
    have h1νP : 1 + L.ν + P ≤ (2 + C) * L.ν⁻¹ ^ k := by
      rw [hPdef]; linarith
    have hε4 : L.ε ^ 4 ≤ L.ε ^ (85 / 22 : ℝ) := by
      calc L.ε ^ 4 = L.ε ^ ((4 : ℕ) : ℝ) := (Real.rpow_natCast L.ε 4).symm
        _ ≤ L.ε ^ (85 / 22 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hε hε1 (by norm_num)
    have hpow : L.ν⁻¹ ^ k * L.ν⁻¹ ^ k ≤ L.ν⁻¹ ^ (3 * k) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ ((one_le_inv₀ hν).2 hν1) (by omega)
    have hreal : L.ε * (A * (P * (L.ε ^ 3 * Real.exp (K.m0 / L.ν)))) ≤
        100 * C * (2 + C) * L.ν⁻¹ ^ (3 * k) *
          (L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν)) := by
      have he : 0 ≤ Real.exp (K.m0 / L.ν) := (Real.exp_pos _).le
      have hCC : 0 ≤ 100 * C * (2 + C) := by positivity
      calc L.ε * (A * (P * (L.ε ^ 3 * Real.exp (K.m0 / L.ν))))
          = (100 * (1 + L.ν + P)) * P * (L.ε ^ 4 * Real.exp (K.m0 / L.ν)) := by
            rw [hAdef]; ring
        _ ≤ (100 * ((2 + C) * L.ν⁻¹ ^ k)) * (C * L.ν⁻¹ ^ k) *
              (L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν)) := by
            rw [hPdef]
            have hq : 0 ≤ C * L.ν⁻¹ ^ k := by positivity
            have := mul_le_mul_of_nonneg_left h1νP (by norm_num : (0 : ℝ) ≤ 100)
            gcongr
        _ = 100 * C * (2 + C) * (L.ν⁻¹ ^ k * L.ν⁻¹ ^ k) *
              (L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν)) := by ring
        _ ≤ 100 * C * (2 + C) * L.ν⁻¹ ^ (3 * k) *
              (L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν)) := by
            gcongr
    calc eLpNorm (coefOf L.ε⁻¹ F2) 2 (srcMeasure (cOf L.ν))
        ≤ ENNReal.ofReal L.ε⁻¹⁻¹ * eLpNorm (ringRead L.ε⁻¹ g) 2 μp := hc'
      _ = ENNReal.ofReal L.ε * (ENNReal.ofReal A * eLpNorm (ringRead L.ε⁻¹ d) 2 μp) := by
          rw [inv_inv, hrg, eLpNorm_const_smul, Real.enorm_eq_ofReal hA0]
      _ ≤ ENNReal.ofReal L.ε * (ENNReal.ofReal A *
            (ENNReal.ofReal (P * (L.ε ^ 3 * Real.exp (K.m0 / L.ν))) * oldN1 Pl K L T)) := by
          gcongr
      _ = ENNReal.ofReal (L.ε * (A * (P * (L.ε ^ 3 * Real.exp (K.m0 / L.ν))))) *
            oldN1 Pl K L T := by
          simp only [ENNReal.ofReal_mul hε.le, ENNReal.ofReal_mul hA0, mul_assoc]
      _ ≤ _ := by gcongr
  refine ⟨h0 T, ?_⟩
  rw [hEq]
  have h2b : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  calc eLpNorm (coefOf L.ε⁻¹ F1 + coefOf L.ε⁻¹ F2) 2 (srcMeasure (cOf L.ν))
      ≤ eLpNorm (coefOf L.ε⁻¹ F1) 2 (srcMeasure (cOf L.ν)) +
          eLpNorm (coefOf L.ε⁻¹ F2) 2 (srcMeasure (cOf L.ν)) :=
        eLpNorm_add_le hm1 hm2 (by norm_num)
    _ ≤ _ := add_le_add hhalf1 hhalf2
    _ = _ := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2
        ring

end Reduction

/-- **`SeqData.coefReplace_of`**: the sequence form (source 5272-5289, 5494-5506). -/
theorem SeqData.coefReplace_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hpt : WardEXYChgPt) (hconv : RingHolderConv) (hl2 : RingL2Conv) (h0 : D.MeanResMeas)
    (h0s : D.MeanResSplitMeas) (h1 : D.PresFlat) (h2 : D.CoefChg) (h3 : D.MeanGrad) (h4 : D.EntJet) : D.CoefReplace := by
  obtain ⟨C1, k1, e1⟩ := h1
  obtain ⟨C2, k2, e2⟩ := h2
  obtain ⟨C3, k3, e3⟩ := h3
  obtain ⟨C4, k4, e4⟩ := h4
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  set C : ℝ := |C1| + |C2| + |C3| + |C4| with hCdef
  set k : ℕ := max k1 (max k2 (max k3 k4)) with hkdef
  have hC0 : 0 ≤ C := by positivity
  have hC1 : C1 ≤ C :=
    (le_abs_self C1).trans (by rw [hCdef]; linarith [abs_nonneg C2, abs_nonneg C3, abs_nonneg C4])
  have hC2 : C2 ≤ C :=
    (le_abs_self C2).trans (by rw [hCdef]; linarith [abs_nonneg C1, abs_nonneg C3, abs_nonneg C4])
  have hC3 : C3 ≤ C :=
    (le_abs_self C3).trans (by rw [hCdef]; linarith [abs_nonneg C1, abs_nonneg C2, abs_nonneg C4])
  have hC4 : C4 ≤ C :=
    (le_abs_self C4).trans (by rw [hCdef]; linarith [abs_nonneg C1, abs_nonneg C2, abs_nonneg C3])
  refine ⟨200 * C ^ 2 * (2 + C) + 100 * C * (2 + C), 3 * k, ?_⟩
  filter_upwards [e1, e2, e3, e4, h0, h0s, hle] with n a1 a2 a3 a4 a0 a0s hν z hz
  have hν1 : (D.level n).ν ≤ 1 := hν.1
  have hε1 : (D.level n).ε ≤ 1 := hν.2
  exact coefReplaceAt_of D.Pl D.K (D.level n) (D.mu n z) hν1 hε1 hC0 hpt hconv hl2 (a0 z hz) (a0s z hz)
    (a1.mono hν1 hC1 hC0 (le_max_left _ _))
    (a2.mono hν1 hC2 hC0 ((le_max_left k2 (max k3 k4)).trans (le_max_right _ _)))
    ((a3 z hz).mono hν1 hC3 hC0
      (((le_max_left k3 k4).trans (le_max_right k2 _)).trans (le_max_right _ _)))
    ((a4 z hz).mono hν1 hC4 hC0
      (((le_max_right k3 k4).trans (le_max_right k2 _)).trans (le_max_right _ _)))

/-- **`SeqData.ringExpansion_of_full`**: `RingExpansionAt` (`Sub/PartIII-b_C_rep_8_org.lean`)
carries the source bound `P_ν N(ε⁴ + ε^{85/22}e^{m₀/ν})` (source 5449-5483 with 5272-5289,
5494-5506), which is the bound of `RingExpansionFullAt`. -/
theorem SeqData.ringExpansion_of_full (D : SeqData) (h : D.RingExpansionFull) :
    D.RingExpansion := h

/-- **The composition of step (b)** (source 5449-5506): `RingExpansion` from the leaves of
`Sub/PartIII-b_C_rep_8_2Org.lean` (with `CoefReplace` replaced by its six leaves here). -/
theorem SeqData.ringExpansion_of_leaves (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) (h6 : D.ActualJet) (h7 : D.JetClock) (hS : D.RingSubst)
    (hW : D.TrainMoment) (hM : D.MeanSupport) (hpt : WardEXYChgPt) (hconv : RingHolderConv)
    (hl2 : RingL2Conv) (h0 : D.MeanResMeas) (h0s : D.MeanResSplitMeas) (h1 : D.PresFlat)
    (h2 : D.CoefChg) (h3 : D.MeanGrad) (h4 : D.EntJet) : D.RingExpansion :=
  D.ringExpansion_of_full
    (D.ringExpansionFull_of hst h6 h7 (D.coefReplace_of hst hpt hconv hl2 h0 h0s h1 h2 h3 h4) hS hW hM)

end UnforcedLeray.Short.PartIIIb.Concrete
