import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.Reg

/-!
# Decomposition of `wardHEquation_of` (source 4225-4286)

Source: `the November 2 reference manuscript`.

The weak Ward equation `WardHEquation` is proved in four steps.

1. `WardPointwiseIdentity` (source 4225-4282): the unprojected pointwise identity for an exact
   profile `(U, p)` and an arbitrary smooth *solenoidal* `X`.
2. `SmoothWardInput` (source 4284-4286): the class of smooth symmetry-preserving old data, stated
   for the *regularized* Ward fields `wardXr`, `wardYr`, `wardHr`, `wardEr` of `Dense/Reg.lean`
   (the raw `wardX` is junk on the axis, where Lean's `age = 0`; the regularized fields agree with
   the raw ones off the axis and have the same chart coefficients).
3. `WardWeakFromPointwise`: for stresses with smooth old data, (1) gives the weak equation by
   integration by parts against solenoidal phase tests (`WardIBPLoc`, `Ward3.lean`).
4. `WardSmoothDense` and `WardEqClosed`: smooth data are dense in the stress space and both
   sides of the weak equation are continuous in `T` (separated-kernel bounds, source 4284-4286);
   the decomposition of the density is in `Dense/Defs.lean`.

No decay or growth hypothesis on the fields or the background is needed anywhere: the weak
equation is tested against phase tests of bounded spatial support (`IsPhaseTest.bounded_support`);
the separated-kernel fields decay only like `|y|^{-4}` (`sep:kernel`, source 3604-3610).

NB (correction to the naive reading of (1)).  The identity
`div(U⊗h + h⊗U) = U·∇h + h·∇U` and `div(U⊗Y + Y⊗U) = U·∇Y + Y·∇U` use `div h = 0`,
`div Y = 0`, which hold because `X` is solenoidal (source 4178-4186: `X = 𝒞_yX₀` is built from a
stream function).  So `X` is required to be solenoidal in `WardPointwiseIdentity`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- Pointwise axisymmetry without swirl of a spatial field: `g (U (g⁻¹ x)) = U x` for every linear
isometry `g` fixing `e₃` (source 121-124: axisymmetric without swirl means invariant under all
orthogonal transformations fixing `e₃`, meridional reflections included).  The exact background
`U = V + r_b` is in this class (source 2031, 2522-2523, and "the prescribed orthogonal symmetry"
of 4144-4145), so its Cartesian value is the cylindrical frame applied to its meridional trace,
which is what the exact multiplier `M_U` of 4150 reads through `IIIa.chartCoeff`. -/
def AxiNoSwirlPt (U : SpatialField) : Prop :=
  ∀ g : Space ≃ₗᵢ[ℝ] Space, FixesAxis g → ∀ x, g (U (g.symm x)) = U x

/-- A continuous field that is axisymmetric without swirl in the a.e. sense of the audited
statement (`IsAxisymmetricNoSwirl`, source 121-124) is so pointwise.  This is how `AxiNoSwirlPt`
of a smooth background follows from the background output (`IIb.StrongRegularity`:
`∀ τ, IsAxisymmetricNoSwirl (bgField p z τ)` and joint smoothness). -/
theorem axiNoSwirlPt_of_ae {U : SpatialField} (hU : Continuous U)
    (h : IsAxisymmetricNoSwirl U) : AxiNoSwirlPt U := by
  intro g hg x
  have hc : Continuous fun x => g (U (g.symm x)) :=
    g.continuous.comp (hU.comp g.symm.continuous)
  exact congrFun ((hc.ae_eq_iff_eq volume hU).1 (h g hg)) x

/-- The Lie bracket `[U, X] = U·∇X - X·∇U` of spatial fields (source 4171-4173, 4225). -/
def physBracket (U X : Space → Space) (y : Space) : Space :=
  fderiv ℝ X y (U y) - fderiv ℝ U y (X y)

/-- `(div(a ⊗ b + b ⊗ a))_i = Σ_j ∂_j(a_j b_i + b_j a_i)` (the divergence of the symmetrized
product, source 4268-4270 with `M_U w = U ⊗ w + w ⊗ U`). -/
def physDivSym (a b : Space → Space) (y : Space) : Space :=
  WithLp.toLp 2 fun i => ∑ j : Fin 3,
    fderiv ℝ (fun y' => a y' j * b y' i + b y' j * a y' i) y (coordinateVector j)

/-- The Ward residual `Ẽ_μ` of source 4276-4282 for a general field `X`:
`2U·∇Y - 2νC_diff + (U⊗U):D²X - (DX + DXᵀ)∇p`, `Y = D_{μ+1}X` (the form of `wardE`). -/
def physResidual (ν μ : ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) (X : ℝ → Space → Space)
    (τ : ℝ) (y : Space) : Space :=
  (2 : ℝ) • fderiv ℝ (physDmu ν (μ + 1) X τ) y (U τ y) -
      (2 * ν) • physCdiff (U τ) (X τ) y +
    physUUD2 (U τ) (X τ) y - physDXp (X τ) (p τ) y

/-- `wardE` is `physResidual` of `wardX`. -/
theorem wardE_eq_physResidual (ν μ R c : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField)
    (p : ℝ → Space → ℝ) (g : Chart → Ten3) :
    wardE ν μ R c χy U p g = physResidual ν μ U p (wardX ν μ R c χy g) := rfl

/-- **Pointwise Ward identity** (source 4225-4282, `ward:physical-identity` 4268-4270,
`ward:residual` 4276-4282, before projection): for an exact profile `(U, p)` and every jointly
smooth solenoidal `X`, with `h = [U, X]`, `Y = D_{μ+1}X`,
`D_μh + div(U⊗h + h⊗U) + div(U⊗Y + Y⊗U) - Ẽ_μ = ∇_y(X·∇_y p)`
(the gradient is removed by the Leray projection, source 4258-4259). -/
def WardPointwiseIdentity (ν μ : ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) : Prop :=
  ∀ (P : ℝ), IsExactProfile ν P U p →
    ∀ X : ℝ → Space → Space,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => X x.1 x.2) →
      (∀ τ y, ∑ j : Fin 3, physPd (X τ) j y j = 0) →
      ∀ τ y,
        physDmu ν μ (fun τ' y' => physBracket (U τ') (X τ') y') τ y +
            physDivSym (U τ) (fun y' => physBracket (U τ) (X τ) y') y +
            physDivSym (U τ) (physDmu ν (μ + 1) X τ) y -
          physResidual ν μ U p X τ y =
        physGrad (fun y' => ∑ j : Fin 3, X τ y' j * physGrad (p τ) y' j) y

/-- Schwartz-type decay of a smooth field `F` on `ℝ × ℝ³` in the space variable, with all
derivatives of order `≤ 3`.  A hypothesis of `WardIBP` (`Ward3.lean`); the weak equation uses
`WardIBPLoc`, which needs no decay (the Ward fields decay only like `|y|^{-4}`). -/
def IsSchwartzDecay (F : ℝ → Space → Space) : Prop :=
  ∀ (N : ℕ), ∃ C : ℝ, ∀ (n : ℕ), n ≤ 3 → ∀ x : ℝ × Space,
    ‖iteratedFDeriv ℝ n (fun x : ℝ × Space => F x.1 x.2) x‖ ≤ C * (1 + ‖x.2‖) ^ (-(N : ℤ))

/-- A field is the coefficient lift of its own chart coefficients: `velPhys R c (coefOf R F) = F`
(axisymmetric, swirl-free, quasi-periodic ring structure of source 2666-2689). -/
def IsAxiLift (R c : ℝ) (F : ℝ → Space → Space) : Prop :=
  ∀ x : ℝ × Space, velPhys R c (coefOf R F) x = B0412.realC (F x.1 x.2)

/-- The open chart domain `{s > 0, |q| < c/2}`: the cylinder chart `(0,∞) × T_c × ℝ` of source
2666-2668 (`ageμ` is carried by `(0,∞) × [-c/2, c/2) × ℝ`) with the phase cell cut open at its
seam, so that a smooth tensor supported in it has a smooth periodic lift (`NearInst.cartLift`
reduces `q` modulo `c`). -/
def chartDom (c : ℝ) : Set Chart := {q | 0 < q.1 ∧ |q.2.1| < c / 2}

/-- A smooth chart tensor with compact support inside the open chart domain (source 4284-4286:
the smooth approximants; a chart tensor lifts to an axisymmetric swirl-free tensor, source
121-124, 2683, so chart approximation preserves the prescribed symmetry). -/
structure IsSmoothChart (c : ℝ) (G : Chart → Ten3) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G
  compact : HasCompactSupport G
  inChart : tsupport G ⊆ chartDom c

/-- Smooth old data (source 4163-4166, 4171, 4284-4286): a smooth chart tensor with compact
support in the open chart domain, vanishing for `νs ≤ 6/5` (where `χ_o = 0`), so that its
physical source `oldPhys R c g` lives in the old disk `ϱ ≤ R√(5ν/6)`. -/
structure IsSmoothOld (c ν : ℝ) (g : Chart → Ten3) : Prop where
  chart : IsSmoothChart c g
  old : ∀ q : Chart, ν * q.1 ≤ 6 / 5 → g q = 0

/-- **Smooth symmetry-preserving old data and their Ward fields** (source 4284-4286, 4161-4186,
4276-4282): `g` is smooth old data, and for it the *regularized* Ward fields (`wardXr`,
`wardYr`, `wardHr`, `wardEr` of `Dense/Reg.lean`; the raw `wardX` is junk on the axis) are jointly
`C^∞` and `2c/R`-periodic in the phase, `X` is solenoidal, `X·∇p` is `C^∞`, and `h`, `Ẽ_μ`,
`Y + h` are the lifts of their own chart coefficients (axisymmetric ring structure of source
2666-2689; the background `U` is axisymmetric without swirl).  No decay or growth is required:
the weak equation is tested against phase tests of bounded spatial support. -/
structure SmoothWardInput (ν μ R c : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField)
    (p : ℝ → Space → ℝ) (g : Chart → Ten3) : Prop where
  oldData : IsSmoothOld c ν g
  smoothX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : ℝ × Space => wardXr ν μ R c χy g x.1 x.2)
  periodicX : ∀ τ y, wardXr ν μ R c χy g (τ + 2 * c / R) y = wardXr ν μ R c χy g τ y
  solenoidalX : ∀ τ y, ∑ j : Fin 3, physPd (wardXr ν μ R c χy g τ) j y j = 0
  smoothH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : ℝ × Space => wardHr ν μ R c χy U g x.1 x.2)
  smoothY : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : ℝ × Space => wardYr ν μ R c χy g x.1 x.2)
  smoothE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : ℝ × Space => wardEr ν μ R c χy U p g x.1 x.2)
  smoothQ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space =>
    ∑ j : Fin 3, wardXr ν μ R c χy g x.1 x.2 j * physGrad (p x.1) x.2 j)
  periodicH : ∀ τ y, wardHr ν μ R c χy U g (τ + 2 * c / R) y = wardHr ν μ R c χy U g τ y
  periodicY : ∀ τ y, wardYr ν μ R c χy g (τ + 2 * c / R) y = wardYr ν μ R c χy g τ y
  periodicE : ∀ τ y, wardEr ν μ R c χy U p g (τ + 2 * c / R) y = wardEr ν μ R c χy U p g τ y
  liftH : IsAxiLift R c (wardHr ν μ R c χy U g)
  liftE : IsAxiLift R c (wardEr ν μ R c χy U p g)
  liftYH : IsAxiLift R c (fun τ y => wardYr ν μ R c χy g τ y + wardHr ν μ R c χy U g τ y)

section Ward

variable {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
  [CompleteSpace Aff]

/-- `WardHEquation` for one stress `T`. -/
def WardHEquationAt (B : ReturnBase c mZ ρb γ ν Aff) (ε μ : ℝ) (T : StrG c mZ ρb γ ν) : Prop :=
  ∀ Φ : ℝ × Space → CVec3, IsSolTest (2 * ε * c) Φ →
    pairF (2 * ε * c) (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) (velPhys ε⁻¹ c (B.hf T)) =
      pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (B.Ef T)) +
        stressPair (2 * ε * c)
          (strPhys ε⁻¹ c (strSum (B.M (B.Yf T + B.hf T)))) Φ

theorem wardHEquation_iff (B : ReturnBase c mZ ρb γ ν Aff) (ε μ : ℝ) :
    WardHEquation B ε μ ↔ ∀ T, WardHEquationAt B ε μ T := Iff.rfl

/-- The stresses whose old source `χ_oT` has representatives `g₁, g₂` with
`g₁ + g₂` a smooth symmetry-preserving input (source 4284-4286). -/
def SmoothWardSet (B : ReturnBase c mZ ρb γ ν Aff) (ε μ : ℝ) {χo : ℝ → ℝ}
    (hχo : IsOutwardCutoff χo) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) :
    Set (StrG c mZ ρb γ ν) :=
  {T | ∃ g₁ g₂ : Chart → Ten3,
    ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] g₁ ∧
    ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] g₂ ∧
    SmoothWardInput ν μ ε⁻¹ c χy U p (g₁ + g₂)}

/-- **(3) Weak form from the pointwise identity** (source 4260-4282): for stresses with smooth
old data, the classical identity (1) with the regularized `X = wardXr` gives the weak equation of
`WardHEquation`: integrate `D_μh + div M_U(h+Y) = Ẽ + ∇(X·∇p)` against a solenoidal phase test
`Φ` (the gradient is killed by `IsSolTest`, the divergence gives `stressPair`, `τ`-periodicity
removes the boundary terms), identifying the lifts via `IsWardPinned` and `IsExactMultiplier`.
The background `U = V + r_b` is axisymmetric without swirl (`AxiNoSwirlPt`, source 121-124,
4144-4145): `B.M` reads `U` only through its meridional trace at azimuth `0` (`chartCoeff`), so the
physical stress of `M(Y+h)` is the Cartesian `U ⊗ (Y+h) + (Y+h) ⊗ U` only for such `U`. -/
def WardWeakFromPointwise (B : ReturnBase c mZ ρb γ ν Aff) (ε μ : ℝ) {χo : ℝ → ℝ}
    (hχo : IsOutwardCutoff χo) (χy : ℝ → ℝ) (V rb : ℝ → SpatialField) (p : ℝ → Space → ℝ) :
    Prop :=
  WardPointwiseIdentity ν μ (fun τ y => V τ y + rb τ y) p →
  IsExactProfile ν (2 * ε * c) (fun τ y => V τ y + rb τ y) p →
  IsExactMultiplier B ε⁻¹ V rb →
  (∀ τ, AxiNoSwirlPt (fun y => V τ y + rb τ y)) →
  IsWardPinned B ε μ hχo χy (fun τ y => V τ y + rb τ y) p →
    ∀ T ∈ SmoothWardSet B ε μ hχo χy (fun τ y => V τ y + rb τ y) p, WardHEquationAt B ε μ T

/-- **(4a) Density** (source 4284-4286): stresses with smooth symmetry-preserving old data are
dense in the stress space. -/
def WardSmoothDense (B : ReturnBase c mZ ρb γ ν Aff) (ε μ : ℝ) {χo : ℝ → ℝ}
    (hχo : IsOutwardCutoff χo) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) : Prop :=
  Dense (SmoothWardSet B ε μ hχo χy U p)

/-- **(4b) Continuity** (source 4284-4286, separated-kernel bounds): both sides of the weak
equation are continuous in `T`, so `{T | WardHEquationAt B ε μ T}` is closed. -/
def WardEqClosed (B : ReturnBase c mZ ρb γ ν Aff) (ε μ : ℝ) : Prop :=
  IsClosed {T : StrG c mZ ρb γ ν | WardHEquationAt B ε μ T}

/-- The approximation step: weak equation on a dense set plus closedness give it everywhere. -/
theorem wardHEquation_of_dense_closed (B : ReturnBase c mZ ρb γ ν Aff) {ε μ : ℝ}
    {S : Set (StrG c mZ ρb γ ν)} (hd : Dense S) (hcl : WardEqClosed B ε μ)
    (hS : ∀ T ∈ S, WardHEquationAt B ε μ T) : WardHEquation B ε μ := by
  intro T
  have hsub : S ⊆ {T : StrG c mZ ρb γ ν | WardHEquationAt B ε μ T} := hS
  have h : closure S ⊆ {T : StrG c mZ ρb γ ν | WardHEquationAt B ε μ T} :=
    closure_minimal hsub hcl
  exact h (hd T)

end Ward

end UnforcedLeray.Short.PartIIIb.Concrete
