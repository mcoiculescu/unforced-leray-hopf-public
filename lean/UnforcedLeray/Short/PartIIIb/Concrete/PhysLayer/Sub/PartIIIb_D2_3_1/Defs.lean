import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer

/-!
# Design of the Ward field `h = [U, X]` solenoidality (`PartIII-b:IIIb-D2/3/1`)

Source of record: `the November 2 reference manuscript` 4161-4186 (`X = 𝒞_y X₀`,
the outward primitive `Ψ_Z`, the stream cutoff) and 4240-4258 (`h = [U, X]`, `div U = 0`).

The target is `WardHSolenoidal B ε` (`PhysLayer/Sub/PartIIIb-D2_3.lean`): the lift
`velPhys ε⁻¹ c (B.hf T)` is weakly solenoidal.  By `IsWardPinned`, `B.hf T` is `bodyMeasure`-a.e.
the coefficient `coefOf ε⁻¹ (wardH ...)`.  The route is: `X` is a regular solenoidal axisymmetric
swirl-free field (`WardXRegularAt`), hence `h = [U, X]` is one too (`bracket_div_free`,
`BracketAxiNoSwirl`), hence its lift is `realC h` (`VelPhysCoefOf`) which is weakly solenoidal
(`PhaseSolenoidalOfPointwise`).

**Axis junk.** In Lean `age R y = R²/ϱ² = 0` on the axis, so `χ_y(ν age) = 1` there and
`wardStreamCut` equals `Z` on the axis, whereas the source cutoff is `0` for `r ≤ R√ν` (age `≥ 1/ν`).
Thus `wardX` is *not* continuous across the axis.  The axis is Lebesgue-null and all the source
statements are off the axis; hence the regularity Prop `WardXRegularAt` asserts a globally `C²`
solenoidal field `X'` that agrees with `wardX` off the axis (`X' = wardX · 1_{ϱ > R√ν/2}`), and
`wardH` agrees off the axis with the bracket of `U` and `X'` (the axis is closed, so `fderiv` of
`wardX` equals that of `X'` at every off-axis point).

**Measurability.** `coefOf` of `wardH` must be measurable on `Chart` to compare with the `Lp`
representative `B.hf T` through `wda_velPhys_congr`; this is `WardHCoefMeasurable`.

**Parameters.** Every Ward Prop below assumes `0 < c`, `0 < ρ_b` and `0 ≤ m_Z`.  For `c ≤ 0` or
`ρ_b ≤ 0` the chart measures of `StrG` vanish (`Cyl.avgμ c = 0`, `htRhoMeasure c ρ_b = 0`), so the
representatives `g₁, g₂` are arbitrary functions and the old source carries no information; the
source has `c = ν⁻²` and `ρ_b = P_νε^{3/11}e^{m₀/ν} > 0` (2670, 2703).  The source fixes
`m_Z > 3/2` (2693); only `W ≥ 1`, i.e. `m_Z ≥ 0`, is used: it puts the thin component in `H_T`,
so that the physical old source of every `T ∈ Z` lies in `Y₂` (4155-4156, lifts 2684-2687).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-! ## 1. Definitions -/

/-- The point of the half plane `φ = 0` with the same meridian `(ϱ, z)` as `y`. -/
def meridPt (y : Space) : Space := !₂[ϱ y, 0, y 2]

/-- The young receiver region `ϱ > R√(ν/1.2)` (source 4161-4166): the open set containing the
support `{ν age < 1}` of `χ_y` (`χ_y = 0` for `s ≥ 1/ν`) and disjoint from the old source disk
`r ≤ R√(ν/1.2)` (`χ_o = 0` for `s ≤ 1.2/ν`). -/
def youngOpen (ν R : ℝ) : Set Space := {y | R * Real.sqrt (5 * ν / 6) < ϱ y}

/-- The field `F` is axisymmetric and swirl-free on `S` (source 2666-2668, 4161): off the axis,
`F(τ, y) = F_r(τ, ϱ, 0, z) e_r(y) + F_z(τ, ϱ, 0, z) e_z`, i.e. it is the frame lift of its trace
on the half plane `φ = 0`. -/
def AxiNoSwirlOn (S : Set Space) (F : ℝ → Space → Space) : Prop :=
  ∀ τ y, y ∈ S → y ∉ axis →
    F τ y = frameL y !₂[F τ (meridPt y) 0, F τ (meridPt y) 2]

/-- Axisymmetric swirl-free on all of `Space`. -/
def AxiNoSwirl (F : ℝ → Space → Space) : Prop := AxiNoSwirlOn univ F

/-- **`X = 𝒞_y X₀` is a regular solenoidal field** (source 4161-4186, 4240-4258), for the old
source `g = g₁ + g₂` of the Ward fields: there is a globally `C²` (in `y`) divergence-free,
axisymmetric swirl-free field `X'`, `2c/R`-periodic in the phase, equal to `wardX` off the axis
(see the axis-junk note in the module docstring). -/
def WardXRegularAt (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3) : Prop :=
  ∃ X : ℝ → Space → Space,
    (∀ τ, ContDiff ℝ 2 (X τ)) ∧
    (∀ τ y, y ∉ axis → X τ y = wardX ν μ R c χy g τ y) ∧
    (∀ τ y, ∑ j : Fin 3, physPd (X τ) j y j = 0) ∧
    (∀ τ y, X (τ + 2 * c / R) y = X τ y) ∧
    AxiNoSwirl X

section Ward

variable {c mZ ρb γ ν : ℝ}

/-- **Master regularity Prop** (source 4161-4186): for the two old-source representatives of
`IsWardPinned`, `wardX` is regular (`WardXRegularAt`).  Assumes the young cutoff `χ_y`,
`c, ρ_b > 0`, `m_Z ≥ 0` (module docstring, *Parameters*), `ν, ε > 0`, and `μ > -1/4` (the range of
`sep:young`, source 3631). -/
def WardXRegular (c mZ ρb γ ν : ℝ) (ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    (χy : ℝ → ℝ) : Prop :=
  IsYoungCutoff χy → 0 < c → 0 < ρb → 0 ≤ mZ → 0 < ν → 0 < ε → -(1 / 4) < μ →
  ∀ (T : StrG c mZ ρb γ ν) (g₁ g₂ : Chart → Ten3),
    ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] g₁ →
    ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] g₂ →
      WardXRegularAt ν μ ε⁻¹ c χy (g₁ + g₂)

/-- **(a1)** `X₀ = W_μ - W_{μ+1}` is `C²` in `y` on the young region (source 3611-3621 `sep:resolvent`,
3604-3610 `sep:kernel`: `D^j∇K_t` is bounded by `C|x|^{-4-j}` and the old source is supported in
`r ≤ R√(ν/1.2)`, with the finite `Y₂ = L²_τL²` moment of the old source (4155-4156, 2684-2687; for the
actual stresses also the `N₁` / `L²_τL^{22/19}` moments of 4156-4158) making the integrals
converge; differentiation under the integral). -/
def WardX0Smooth (c mZ ρb γ ν : ℝ) (ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) : Prop :=
  0 < c → 0 < ρb → 0 ≤ mZ → 0 < ν → 0 < ε → -(1 / 4) < μ →
  ∀ (T : StrG c mZ ρb γ ν) (g₁ g₂ : Chart → Ten3),
    ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] g₁ →
    ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] g₂ →
      ∀ τ, ContDiffOn ℝ 2 (wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ) (youngOpen ν ε⁻¹)

/-- **(a2)** `X₀` is solenoidal, axisymmetric swirl-free and `2c/R`-periodic in the phase on the
young region (source 3611-3621: `W_μ = -S_μ(χ_oT)` is the solenoidal response to an axisymmetric
no-swirl tensor source, 4171-4174, 4178). -/
def WardX0Structure (c mZ ρb γ ν : ℝ) (ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) : Prop :=
  0 < c → 0 < ρb → 0 ≤ mZ → 0 < ν → 0 < ε → -(1 / 4) < μ →
  ∀ (T : StrG c mZ ρb γ ν) (g₁ g₂ : Chart → Ten3),
    ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] g₁ →
    ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] g₂ →
      (∀ τ, ∀ y ∈ youngOpen ν ε⁻¹,
        ∑ j : Fin 3, physPd (wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ) j y j = 0) ∧
      (∀ τ y, wardX0 ν μ ε⁻¹ c (g₁ + g₂) (τ + 2 * c / ε⁻¹) y = wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ y) ∧
      AxiNoSwirlOn (youngOpen ν ε⁻¹) (wardX0 ν μ ε⁻¹ c (g₁ + g₂))

/-- **(b)** The outward primitive is a stream function (source 4178-4179): for `Z = X₀` and
`ϱ > R√(ν/1.2)`, `∂_rΨ_Z = r Z_z` and `∂_zΨ_Z = -r Z_r` (the boundary term `rZ_r` at infinity
vanishes by the decay of the separated kernels, 4177-4179, and `div Z = 0`). -/
def OutPrimStream (c mZ ρb γ ν : ℝ) (ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) : Prop :=
  0 < c → 0 < ρb → 0 ≤ mZ → 0 < ν → 0 < ε → -(1 / 4) < μ →
  ∀ (T : StrG c mZ ρb γ ν) (g₁ g₂ : Chart → Ten3),
    ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] g₁ →
    ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] g₂ →
      ∀ τ r z, ε⁻¹ * Real.sqrt (5 * ν / 6) < r →
        HasDerivAt (fun r' => outPrim (wardX0 ν μ ε⁻¹ c (g₁ + g₂)) τ r' z)
            (r * wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ !₂[r, 0, z] 2) r ∧
          HasDerivAt (fun z' => outPrim (wardX0 ν μ ε⁻¹ c (g₁ + g₂)) τ r z')
            (-(r * wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ !₂[r, 0, z] 0)) z

end Ward

/-- **(c)** The stream cutoff preserves solenoidality (source 4180-4186): for a field `Z` that is
`C²`, divergence free and axisymmetric swirl-free on the young region and whose outward primitive
is its stream function, `div (χ_y Z + (χ_y'/r)Ψ_Z e_z) = χ_y' Z_r + (χ_y'/r)(-rZ_r) = 0` off the
axis (`χ_y`, `χ_y'` depend on `r` only). -/
def WardStreamCutDivFree (ν R : ℝ) (χy : ℝ → ℝ) : Prop :=
  IsYoungCutoff χy → 0 < ν → 0 < R →
  ∀ (Z : ℝ → Space → Space) (τ : ℝ),
    ContDiffOn ℝ 2 (Z τ) (youngOpen ν R) →
    (∀ y ∈ youngOpen ν R, ∑ j : Fin 3, physPd (Z τ) j y j = 0) →
    AxiNoSwirlOn (youngOpen ν R) Z →
    (∀ r z, R * Real.sqrt (5 * ν / 6) < r →
      HasDerivAt (fun r' => outPrim Z τ r' z) (r * Z τ !₂[r, 0, z] 2) r ∧
        HasDerivAt (fun z' => outPrim Z τ r z') (-(r * Z τ !₂[r, 0, z] 0)) z) →
    ∀ y, y ∉ axis → ∑ j : Fin 3, physPd (wardStreamCut ν R χy Z τ) j y j = 0

/-- **(c')** The Lie bracket of two `C²` axisymmetric swirl-free fields is axisymmetric
swirl-free (source 4171-4174: `U·∇X - X·∇U` has no swirl because `U·∇e_r = (U_φ/r)e_φ = 0`). -/
def BracketAxiNoSwirl : Prop :=
  ∀ (U X : ℝ → Space → Space), (∀ τ, ContDiff ℝ 2 (U τ)) → (∀ τ, ContDiff ℝ 2 (X τ)) →
    AxiNoSwirl U → AxiNoSwirl X →
      AxiNoSwirl fun τ y => fderiv ℝ (X τ) y (U τ y) - fderiv ℝ (U τ) y (X τ y)

/-- **(e)** A field `C¹` in `y` on every phase slice and pointwise divergence free is weakly
solenoidal (source 4240-4258): `∫ ∇φ·w dy = -∫ φ div w dy = 0` on every slice, `φ` of compact
support, so the phase integral vanishes (no integrability is needed: the slice integrals are
identically `0`). -/
def PhaseSolenoidalOfPointwise (P : ℝ) : Prop :=
  ∀ w : ℝ × Space → CVec3,
    (∀ τ, ContDiff ℝ 1 (fun y => w (τ, y))) →
    (∀ τ y, ∑ j : Fin 3, fderiv ℝ (fun y' => w (τ, y')) y (coordinateVector j) j = 0) →
      IsWeakSolenoidal P w

/-- **(f)** The lift of the coefficient of an axisymmetric swirl-free `2c/R`-periodic field is the
field (source 2666-2668, 2683, `Nv`/`perExt`/`coefOf`): off the axis, `Nv R (perExt c b) τ y =
√s (b_r e_r + b_z e_z)` at `chart R τ y = (s, ξ, η)`, `b = coefOf R F` read at the cell
representative `ξ' = ξ - ck`, the point `(chartY, chartTau) = (meridPt y, τ - 2ck/R)`, so by
periodicity and `AxiNoSwirl` it is `F τ y` (`√s · s^{-1/2} = 1`, `s = R²/ϱ²`). -/
def VelPhysCoefOf (R c : ℝ) : Prop :=
  0 < R → 0 < c →
  ∀ F : ℝ → Space → Space, AxiNoSwirl F → (∀ τ y, F (τ + 2 * c / R) y = F τ y) →
    ∀ x : ℝ × Space, x.2 ∉ axis → velPhys R c (coefOf R F) x = B0412.realC (F x.1 x.2)

/-- **(g)** Measurability of the coefficient of `wardH` on `Chart` (source 4171-4174: `h` is
defined for a.e. phase by the Bochner-measurable `W_μ` of the separated kernel realization;
Carathéodory: continuous in `y`, measurable in `τ`; `χ_y` is the `C^∞` young cutoff and `U` the regular train field, 4240-4258, hence the three extra premises: without them the Prop is false), needed for `wda_velPhys_congr` against the
`Lp` representative `B.hf T`. -/
def WardHCoefMeasurable (c mZ ρb γ ν : ℝ) (ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    (χy : ℝ → ℝ) (U : ℝ → SpatialField) : Prop :=
  IsYoungCutoff χy → (∀ τ, ContDiff ℝ 2 (U τ)) →
  (Measurable fun p : ℝ × Space => U p.1 p.2) →
  0 < c → 0 < ρb → 0 ≤ mZ → 0 < ν → 0 < ε → -(1 / 4) < μ →
  ∀ (T : StrG c mZ ρb γ ν) (g₁ g₂ : Chart → Ten3),
    ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] g₁ →
    ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] g₂ →
      Measurable (coefOf ε⁻¹ (wardH ν μ ε⁻¹ c χy U (g₁ + g₂)))

/-! ## 2. The pure calculus lemma `bracket_div_free` -/

theorem clm_apply_eq (L : Space →L[ℝ] Space) (v : Space) (i : Fin 3) :
    L v i = ∑ k : Fin 3, v k * L (coordinateVector k) i := by
  have hv : v = ∑ k : Fin 3, v k • coordinateVector k := by
    ext i
    simp [coordinateVector, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum]

/-- The divergence of `[U, X]` vanishes pointwise for `C²` fields `U, X` with `div U = div X = 0`
(source 4240-4258). -/
theorem bracket_div_free (U X : Space → Space) (hU : ContDiff ℝ 2 U) (hX : ContDiff ℝ 2 X)
    (hUd : ∀ y, ∑ j : Fin 3, physPd U j y j = 0) (hXd : ∀ y, ∑ j : Fin 3, physPd X j y j = 0)
    (y : Space) :
    ∑ j : Fin 3, physPd (fun y' => fderiv ℝ X y' (U y') - fderiv ℝ U y' (X y')) j y j = 0 := by
  have hDU : ∀ y, HasFDerivAt (fderiv ℝ U) (fderiv ℝ (fderiv ℝ U) y) y := fun y =>
    ((hU.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) y).hasFDerivAt
  have hDX : ∀ y, HasFDerivAt (fderiv ℝ X) (fderiv ℝ (fderiv ℝ X) y) y := fun y =>
    ((hX.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) y).hasFDerivAt
  have hU1 : ∀ y, HasFDerivAt U (fderiv ℝ U y) y := fun y =>
    ((hU.differentiable (by norm_num)) y).hasFDerivAt
  have hX1 : ∀ y, HasFDerivAt X (fderiv ℝ X y) y := fun y =>
    ((hX.differentiable (by norm_num)) y).hasFDerivAt
  have hB : HasFDerivAt (fun y' => fderiv ℝ X y' (U y') - fderiv ℝ U y' (X y'))
      (((fderiv ℝ X y).comp (fderiv ℝ U y) + (fderiv ℝ (fderiv ℝ X) y).flip (U y)) -
        ((fderiv ℝ U y).comp (fderiv ℝ X y) + (fderiv ℝ (fderiv ℝ U) y).flip (X y))) y :=
    ((hDX y).clm_apply (hU1 y)).sub ((hDU y).clm_apply (hX1 y))
  -- trace of the second derivative in a fixed direction vanishes
  have key : ∀ (V : Space → Space), ContDiff ℝ 2 V → (∀ y, ∑ j : Fin 3, physPd V j y j = 0) →
      ∀ a : Space, ∑ i : Fin 3, fderiv ℝ (fderiv ℝ V) y a (coordinateVector i) i = 0 := by
    intro V hV hVd a
    have hDV : ∀ y, HasFDerivAt (fderiv ℝ V) (fderiv ℝ (fderiv ℝ V) y) y := fun y =>
      ((hV.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) y).hasFDerivAt
    have hs : HasFDerivAt (fun y' => ∑ i : Fin 3, fderiv ℝ V y' (coordinateVector i) i)
        (∑ i : Fin 3, ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp
          (ContinuousLinearMap.apply ℝ Space (coordinateVector i))).comp
            (fderiv ℝ (fderiv ℝ V) y)) y := by
      refine HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => ?_
      exact (((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp
          (ContinuousLinearMap.apply ℝ Space (coordinateVector i))).hasFDerivAt).comp y (hDV y)
    have h0 : HasFDerivAt (fun y' => ∑ i : Fin 3, fderiv ℝ V y' (coordinateVector i) i)
        (0 : Space →L[ℝ] ℝ) y := by
      have : (fun y' => ∑ i : Fin 3, fderiv ℝ V y' (coordinateVector i) i) = fun _ => 0 := by
        funext y'; exact hVd y'
      rw [this]; exact hasFDerivAt_const 0 y
    have := congrArg (fun L : Space →L[ℝ] ℝ => L a) (hs.unique h0)
    simpa using this
  have hsymU := hU.contDiffAt.isSymmSndFDerivAt (x := y) (by simp)
  have hsymX := hX.contDiffAt.isSymmSndFDerivAt (x := y) (by simp)
  have e1 := key X hX hXd (U y)
  have e2 := key U hU hUd (X y)
  have step : ∀ i : Fin 3, physPd (fun y' => fderiv ℝ X y' (U y') - fderiv ℝ U y' (X y')) i y =
      (fderiv ℝ X y (fderiv ℝ U y (coordinateVector i)) +
        fderiv ℝ (fderiv ℝ X) y (coordinateVector i) (U y)) -
      (fderiv ℝ U y (fderiv ℝ X y (coordinateVector i)) +
        fderiv ℝ (fderiv ℝ U) y (coordinateVector i) (X y)) := by
    intro i
    unfold physPd
    rw [hB.fderiv]
    rfl
  simp only [step]
  simp only [PiLp.sub_apply, PiLp.add_apply, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have sX : ∀ i : Fin 3, fderiv ℝ (fderiv ℝ X) y (coordinateVector i) (U y) =
      fderiv ℝ (fderiv ℝ X) y (U y) (coordinateVector i) := fun i => hsymX _ _
  have sU : ∀ i : Fin 3, fderiv ℝ (fderiv ℝ U) y (coordinateVector i) (X y) =
      fderiv ℝ (fderiv ℝ U) y (X y) (coordinateVector i) := fun i => hsymU _ _
  simp only [sX, sU, e1, e2]
  have hcomm : ∑ i : Fin 3, fderiv ℝ X y (fderiv ℝ U y (coordinateVector i)) i =
      ∑ i : Fin 3, fderiv ℝ U y (fderiv ℝ X y (coordinateVector i)) i := by
    simp only [clm_apply_eq (fderiv ℝ X y) (fderiv ℝ U y _),
      clm_apply_eq (fderiv ℝ U y) (fderiv ℝ X y _)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete
