import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2_3_2

/-!
# Statements for `OuterTransposeDeriv` (organizer task `PartIII-b:C/near/pins/3/4/2/3/2/4/org`)

Source `the November 2 reference manuscript`
lines 1339-1362 (`L = 𝒯 - νΔ - 1/2`), 3346-3352 (outer semigroup `S_ε` and its transpose),
4139-4146 (`D_μ = L₀ + μ`).

Route (semigroup, right derivative at `0`, then two-sided at `t > 0`).  Write
`U h r = outerTransp h r`, `h = νε² ≥ 0`.

* `U h 0 = id`, `‖U h r‖ ≤ e^{-r/4}`, semigroup law for `r, s ≥ 0`, strong continuity on `[0,∞)`.
* On a smooth phase test `ψ` (`IsPhaseTest`), with `Ψ, Ψτ, ΨΔ, Ψx ∈ X` representing
  `ψ, ∂_τψ, Δψ, x·∇ψ` (`OuterRepFn`): factor derivatives at `r = 0` in `X` (strong)
  `transC(-r)Ψ → Ψτ`, `dilN(e^{-r/2})Ψ → -(3/4)Ψ - (1/2)Ψx`, `heatC(h(e^r-1))Ψ → hΨΔ`
  (right derivative only), glued by a product rule for uniformly bounded strongly continuous
  families, giving `d/dr|_{0+} U h r Ψ = hΨΔ - ½Ψx - Ψ + Ψτ = Ψ'`.
* Right derivative at `0` plus semigroup law, norm bound and continuity gives `HasDerivAt` at
  every `t > 0` with derivative `U h t Ψ'`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `outerTransp h 0 = id` (`exp 0 - 1 = 0`, `heatC_of_nonpos`, `dilN_one`, `transC_zero`). -/
def OD_Zero : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (h : ℝ) (Ψ : XC P), outerTransp h 0 Ψ = Ψ

/-- `‖outerTransp h t Ψ‖ ≤ e^{-t/4}‖Ψ‖` (`dilN a` isometry for `a > 0`, `transC` isometry,
`norm_heatC_apply_le`). -/
def OD_Norm : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (h t : ℝ) (Ψ : XC P),
    ‖outerTransp h t Ψ‖ ≤ Real.exp (-t / 4) * ‖Ψ‖

/-- Semigroup law for `s, t ≥ 0`, `h ≥ 0` (mirror of `B0223.Sop_add`, `Semigroup.lean:69-90`, using
`transC_dilN`, `heatC_dilN`, `heatC_transC`, `heatC_add`, `dilN_mul`, `transC_add`):
the heat times combine as `h(e^s-1) + e^{s}·h(e^t-1) = h(e^{s+t}-1)` (check the direction of the
`a²θ` in `heatC_dilN` with `a = e^{∓s/2}`). -/
def OD_Add : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (h : ℝ), 0 ≤ h → ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ Ψ : XC P,
    outerTransp h (s + t) Ψ = outerTransp h s (outerTransp h t Ψ)

/-- Strong continuity of the phase translation (cf. its use inside `B0223.Sop_continuousOn`,
`Semigroup.lean:155`). -/
def OD_TransCont : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (Ψ : XC P),
    Continuous fun t : ℝ => UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC) t Ψ

/-- Strong continuity of `r ↦ dilN (e^{-r/2}) Ψ` (`B0223.tendsto_dilN_at`, `Semigroup.lean:143`). -/
def OD_DilCont : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (Ψ : XC P),
    Continuous fun r : ℝ =>
      UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC) (Real.exp (-r / 2)) Ψ

/-- Strong continuity of `s ↦ outerTransp h s Ψ` on `[0, ∞)` for `h ≥ 0`: the four factors
(`Real.exp`, `OD_TransCont`, `B0223.heatC_continuousOn` composed with `s ↦ h(e^s-1) ≥ 0`,
`OD_DilCont`) with the uniform bounds `‖heatC θ‖, ‖dilN a‖, ‖transC t‖ ≤ 1`; copy the
`Sop_continuousOn` argument (`Semigroup.lean:155`). -/
def OD_Cont : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (h : ℝ), 0 ≤ h → ∀ Ψ : XC P,
    ContinuousOn (fun s : ℝ => outerTransp h s Ψ) (Ici 0)

/-- **Abstract product rule.** `A r` uniformly bounded on `s`, strongly continuous within `s` at
`0`, `r ↦ A r (x 0)` and `x` differentiable within `s` at `0`:
`d/dr (A r (x r)) = a' + A 0 x'`.  (`A r (x r) - A 0 (x 0) = A r (x r - x 0) + (A r (x 0) - A 0 (x 0))`.) -/
def OD_ProdRule : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : Set ℝ) (M : ℝ)
    (A : ℝ → E →L[ℂ] E) (x : ℝ → E) (a' x' : E),
    (∀ r ∈ s, ‖A r‖ ≤ M) → (∀ y : E, ContinuousWithinAt (fun r => A r y) s 0) →
    HasDerivWithinAt (fun r => A r (x 0)) a' s 0 → HasDerivWithinAt x x' s 0 →
    HasDerivWithinAt (fun r => A r (x r)) (a' + A 0 x') s 0

/-- The scaled test `ψ(τ,x) = Φ(τ, x/ε)` is a phase test (smooth, `P`-periodic, support radius
multiplies by `ε`). -/
def OD_ScaledTest : Prop :=
  ∀ (p : Params) (Φ : ℝ × Space → CVec3), IsPhaseTest p.period Φ →
    IsPhaseTest p.period (scaledFn p Φ)

/-- Every phase test is represented by an element of `X` (the restriction of a continuous
compactly supported periodic function to the cell is in `L²`; look first in `PairCLM.lean` and
`Units/B0223/Lift.lean` for an existing lift). -/
def OD_Exists : Prop :=
  ∀ (p : Params) (f : ℝ × Space → CVec3), IsPhaseTest p.period f → ∃ Ψ : XC p.period, OuterRepFn p f Ψ

/-- Linear algebra of representatives: two representatives of the same function are equal in `X`,
and `OuterRepFn` is compatible with `+`, complex scalars and real-scalar multiples of functions
(a.e. algebra via `Lp.coeFn_add`, `Lp.coeFn_smul`).  Concretely, if `Ψ, Ψτ, ΨΔ, Ψx, Ψ'` represent
`ψ, dτ ψ, lapT ψ, radialT ψ, outerGenT p ψ` then
`Ψ' = ((ν ε² : ℝ) : ℂ) • ΨΔ - (1/2 : ℂ) • Ψx - Ψ + Ψτ`. -/
def OD_RepAlg : Prop :=
  ∀ (p : Params) (ψ : ℝ × Space → CVec3) (Ψ Ψτ ΨΔ Ψx Ψ' : XC p.period),
    OuterRepFn p ψ Ψ → OuterRepFn p (dτ ψ) Ψτ → OuterRepFn p (lapT ψ) ΨΔ →
    OuterRepFn p (radialT ψ) Ψx → OuterRepFn p (outerGenT p ψ) Ψ' →
    Ψ' = (((p.ν * p.ε ^ 2 : ℝ)) : ℂ) • ΨΔ - ((1 / 2 : ℝ) : ℂ) • Ψx - Ψ + Ψτ

/-- Strong derivative of the phase translation at `0` on a smooth phase test
(`transC (-r) Ψ (x,τ) = Ψ (x, τ + r)`): pointwise Taylor `|ψ(τ+r,x) - ψ - r ∂_τψ| ≤ C r²`
uniformly (smooth, periodic, support in a fixed `x`-ball), so the `L²(cell)` norm is `≤ C' r²`. -/
def OD_TransDeriv : Prop :=
  ∀ (p : Params) (ψ : ℝ × Space → CVec3), IsPhaseTest p.period ψ →
    ∀ Ψ Ψτ : XC p.period, OuterRepFn p ψ Ψ → OuterRepFn p (dτ ψ) Ψτ →
      HasDerivAt (fun r : ℝ =>
        UnforcedLeray.B0223.transC (E := UnforcedLeray.B0223.SpaceC) (-r) Ψ) Ψτ 0

/-- Strong derivative of the normalized dilation at `0`:
`d/dr|₀ e^{-3r/4} ψ(e^{-r/2}x, τ) = -(3/4)ψ - (1/2) x·∇ψ`; second-order Taylor bound for
`|r| ≤ 1` on the compact set `‖x‖ ≤ e^{1/2}R`, `τ ∈ [0,P]` (smooth in `(r,x,τ)`). -/
def OD_DilDeriv : Prop :=
  ∀ (p : Params) (ψ : ℝ × Space → CVec3), IsPhaseTest p.period ψ →
    ∀ Ψ Ψx : XC p.period, OuterRepFn p ψ Ψ → OuterRepFn p (radialT ψ) Ψx →
      HasDerivAt (fun r : ℝ =>
        UnforcedLeray.B0223.dilN (E := UnforcedLeray.B0223.SpaceC) (Real.exp (-r / 2)) Ψ)
        (-(((3 / 4 : ℝ)) : ℂ) • Ψ - ((1 / 2 : ℝ) : ℂ) • Ψx) 0

/-- **Second-order heat Taylor bound on a smooth phase test**: `‖e^{θΔ}Ψ - Ψ - θΨΔ‖ ≤ C θ²`
for `0 ≤ θ ≤ 1`.  Route: for `θ > 0`, `heatC_rep`, `e^{θΔ}ψ(x) - ψ(x) = ∫ G_θ(y)(ψ(x-y) - ψ(x))dy`;
Taylor to third order with integral remainder, odd Gaussian moments vanish, `∫G_θ y_iy_j = 2θδ_ij`,
`∫G_θ|y|⁴ = cθ²`; Minkowski in `y` and translation invariance of `‖D^kψ(· - sy)‖_{L²(cell)}`
(`Lib/HeatR3/Generator.lean`, `Gaussian` moment lemmas; `PartII-a` `sliceFwdSpatialTaylor`
treats the same expansion on slices with `B0421.freeC`). -/
def OD_HeatTaylor : Prop :=
  ∀ (p : Params) (ψ : ℝ × Space → CVec3), IsPhaseTest p.period ψ →
    ∀ Ψ ΨΔ : XC p.period, OuterRepFn p ψ Ψ → OuterRepFn p (lapT ψ) ΨΔ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        ‖UnforcedLeray.B0223.heatC (E := UnforcedLeray.B0223.SpaceC) θ Ψ - Ψ - (θ : ℂ) • ΨΔ‖
          ≤ C * θ ^ 2

/-- Right derivative of the heat factor along `θ(r) = h(e^r-1)`, from `OD_HeatTaylor` and
`θ(r) = h r + O(r²)` (`|e^r - 1 - r| ≤ r²` for `0 ≤ r ≤ 1`). -/
def OD_HeatDeriv : Prop :=
  ∀ (p : Params) (ψ : ℝ × Space → CVec3), IsPhaseTest p.period ψ →
    ∀ Ψ ΨΔ : XC p.period, OuterRepFn p ψ Ψ → OuterRepFn p (lapT ψ) ΨΔ →
      ∀ h : ℝ, 0 ≤ h →
        HasDerivWithinAt (fun r : ℝ =>
          UnforcedLeray.B0223.heatC (E := UnforcedLeray.B0223.SpaceC) (h * (Real.exp r - 1)) Ψ)
          ((h : ℂ) • ΨΔ) (Ici 0) 0

/-- **Right derivative at `0` of the transposed orbit**: product rule (`OD_ProdRule`, applied to
`transC(-r)` over `heatC(h(e^r-1)) ∘ dilN(e^{-r/2})`, then `HasDerivWithinAt.smul` with `e^{-r/4}`),
`OD_TransDeriv`, `OD_DilDeriv`, `OD_HeatDeriv`, `OD_Cont`-type strong continuity of the
two outer families, `OD_Norm`, `OD_Zero`, and `OD_RepAlg` to name the derivative `Ψ'`. -/
def OD_RightDeriv0 : Prop :=
  ∀ (p : Params) (ψ : ℝ × Space → CVec3), IsPhaseTest p.period ψ →
    ∀ Ψ Ψ' : XC p.period, OuterRepFn p ψ Ψ → OuterRepFn p (outerGenT p ψ) Ψ' →
      HasDerivWithinAt (fun r : ℝ => outerTransp (p.ν * p.ε ^ 2) r Ψ) Ψ' (Ici 0) 0

/-- **Abstract upgrade**: right derivative `Ψ'` at `0` of `r ↦ U r Ψ`, with `U` obeying
`OD_Zero`/`OD_Norm`/`OD_Add`/`OD_Cont`, gives `HasDerivAt` at every `t > 0` with derivative
`U t Ψ'`.  Right: `U(t+r)Ψ = U(t)(U(r)Ψ)` and `U t` is a bounded linear map.  Left: for
`0 < r < t`, `(U(t-r)Ψ - U(t)Ψ)/(-r) = U(t-r)((U(r)Ψ - Ψ)/r)`, the quotient `→ Ψ'` in norm,
`‖U(t-r)‖ ≤ 1`-ish by `OD_Norm`, and `U(t-r)Ψ' → U(t)Ψ'` by `OD_Cont`; glue with
`HasDerivWithinAt.union`. -/
def OD_TwoSided : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (h : ℝ), 0 ≤ h → ∀ Ψ Ψ' : XC P,
    HasDerivWithinAt (fun r : ℝ => outerTransp h r Ψ) Ψ' (Ici 0) 0 →
      ∀ t : ℝ, 0 < t →
        HasDerivAt (fun s : ℝ => outerTransp h s Ψ) (outerTransp h t Ψ') t

end UnforcedLeray.Short.PartIIIb.NearInst
