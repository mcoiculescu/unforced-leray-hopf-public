import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.TableOrg

/-!
# `PartIII-b:C/rep/4/2/org/3/3`: the annulus fields, leaves

Source `the November 2 reference manuscript` 3669-3674 (`sep:thin-global`),
3730 ("its physical phase-averaged mass is `R²N₀`"), 2666-2687 (the chart
`s = R²/ρ²`, `q = R log(ρ/R) + Rτ/2`, `η = Rz/ρ`; "the physical space Jacobian after azimuthal
integration is `πR²s^{-5/2}ds dη` and normalized phase becomes `dq/c`"; `𝒩_TT = sT`),
4163-4168 (the old source disk `r ≤ R√(ν/1.2)` is separated from the young receiver
`r ≥ R√ν`), 5148-5157 (the old source `χ_o(T₁, 0)`), 5571-5576 ("its old physical mass divided
by `πR²` is `N₀(a)`"), 5946-5950 (`P_n = 2ε_nc_n`, the window `μ_n(z)`).

`AnnulusFieldBoundsAt` (`TableOrg.lean`) is `IIIa.SepThinGlobal` for the physical old source
`oldPhys R c (g₁ + g₂)` once its physical mass `∫‖T(z,·)‖_{L²_τ}dz` is bounded by `R²·πN₀`.
The chart tensor behind `g₁ + g₂` is `oldThinTen T = χ̂_o(νs)T₁` (`T₁` the thin component),
whose `oldMassAt (cOf ν) 0` is `oldMass` by definition (`oldMass_eq`).  The leaves:

* `TwoPeriodLtau`: a phase function that is `P`-periodic and a.e. equal to a `p₀`-periodic one
  has the same normalized phase norm over either period (the hypothesis `IsSepSource P` of
  `AnnulusFieldBoundsAt` fixes some period `P`; the lift is `2c/R`-periodic, `P_n = 2ε_nc_n`).
* `ChartPhaseNorm`: at the chart receiver `chartY R p` the normalized phase norm (period `2c/R`)
  of the lift is `s·‖f(s,·,η)‖_{L²(dq/c)}` (`dτ = (2/R)dq`, `|𝒩_TT| = s|T|`).
* `ChartMassLe`: the physical mass of the lift is at most `πR²N₀(0)` (azimuthal integration and
  the Jacobian `πR²s^{-5/2}ds dη`), from `ChartPhaseNorm`.
* `OldThinPhysAE`: for representatives `g₁, g₂` of `χ_o(T₁, 0)`, the lift of `g₁ + g₂` and that
  of `oldThinTen T` have a.e. equal phase profiles at a.e. point (the representatives agree
  `ageμ`-a.e., and chart-null sets pull back to null sets).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## The chart tensor of the old thin source -/

/-- The measurable chart tensor `χ̂_o(νs)T₁` of the old thin source `χ_o(T₁, 0)` (source
5148-5157, 4163-4166): `T₁` read through its `Lp` representative (strongly measurable). -/
def oldThinTen (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (T : LStr Pl K L) :
    Chart → Ten3 :=
  fun p => K.χo (L.ν * p.1) • (T.fst : Chart → Ten3) p

theorem measurable_oldThinTen (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (T : LStr Pl K L) : Measurable (oldThinTen Pl K L T) := by
  have h1 : Measurable fun p : Chart => K.χo (L.ν * p.1) :=
    K.hχo.smooth.continuous.measurable.comp (measurable_const.mul measurable_fst)
  exact h1.smul (Lp.stronglyMeasurable T.fst).measurable

/-- `oldMass` is the old mass `N₀(0)` of the chart tensor `oldThinTen` (source 5573-5576). -/
theorem oldMass_eq (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (T : LStr Pl K L) :
    oldMass Pl K L T =
      oldMassAt (cOf L.ν) 0 (fun p => Ten3.toMatrix (oldThinTen Pl K L T p)) := by
  unfold oldMass
  congr 1

/-! ## The leaves -/

/-- **Normalized phase norm over two periods** (source 5946-5950: one phase period `P = 2εc`;
`IsSepSource P` fixes a period of the physical source, the chart lift has period `2c/R`): if
`h` is `P`-periodic, `k` is `p₀`-periodic, both measurable, and `h = k` a.e. on `ℝ`, then
`‖h‖_{L²_τ}` normalized over `(0, P]` equals `‖k‖_{L²_τ}` normalized over `(0, p₀]`
(`p₀∫_0^P h² = ∫_0^{p₀}∫_x^{x+P}h² dt dx = ∫_0^P∫_0^{p₀}k(x+u)²dx du = P∫_0^{p₀}k²`). -/
def TwoPeriodLtau : Prop :=
  ∀ (P p₀ : ℝ), 0 < P → 0 < p₀ → ∀ h k : ℝ → ℝ≥0∞, Measurable h → Measurable k →
    (∀ τ, h (τ + P) = h τ) → (∀ τ, k (τ + p₀) = k τ) → h =ᵐ[volume] k →
      UnforcedLeray.Short.IIIa.ltauAt P h = UnforcedLeray.Short.IIIa.ltauAt p₀ k

/-- **The phase norm of the lift at a chart receiver** (source 2666-2687: `τ = 2q/R + log s`,
"normalized phase becomes `dq/c`", `𝒩_TT = sT` in the orthonormal cylindrical frame and
`|nsSym T| ≤ |T|`): for `R, c > 0`, a measurable chart tensor `f` and a chart point `p` of age
`s = p.1 > 0`, at the receiver `chartY R p = (R/√s, 0, η/√s)` the normalized phase norm over
one period `2c/R` of the lift is at most `s ‖f(s,·,η)‖_{L²(dq/c)}`, `q ∈ [-c/2, c/2)`. -/
def ChartPhaseNorm : Prop :=
  ∀ (R c : ℝ), 0 < R → 0 < c → ∀ f : Chart → Ten3, Measurable f → ∀ p : Chart, 0 < p.1 →
    UnforcedLeray.Short.IIIa.ltauAt (2 * c / R)
        (fun τ => UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c f) τ
          (NearInst.chartY R p)) ≤
      ENNReal.ofReal p.1 *
        (∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal c⁻¹ *
          ENNReal.ofReal (UnforcedLeray.Short.IIIa.frobSq (Ten3.toMatrix (f (p.1, (q, p.2.2))))))
          ^ (1 / 2 : ℝ)

/-- **Physical mass of the lift** (source 3730: "its physical phase-averaged mass is `R²N₀`";
2685-2687: "the physical space Jacobian after azimuthal integration is `πR²s^{-5/2}ds dη`";
5571-5576: "its old physical mass divided by `πR²` is `N₀(a)`"): for `R, c > 0` and a measurable
chart tensor `f`, `∫‖𝒩_Tf(z,·)‖_{L²_τ}dz ≤ πR² N₀(0)`, the phase norm normalized over one
period `2c/R` and `N₀(0) = oldMassAt c 0 f`. -/
def ChartMassLe : Prop :=
  ∀ (R c : ℝ), 0 < R → 0 < c → ∀ f : Chart → Ten3, Measurable f →
    ∫⁻ z : Space, UnforcedLeray.Short.IIIa.ltauAt (2 * c / R)
        (fun τ => UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c f) τ z) ≤
      ENNReal.ofReal (Real.pi * R ^ 2) * oldMassAt c 0 (fun p => Ten3.toMatrix (f p))

/-- **Representatives of the old thin source have a.e. equal lifts** (source 5148-5157,
4171-4174, 2666-2668): for representatives `g₁, g₂` of `χ_o(T₁, 0)` (`IsRep`, gain measures
with positive densities, `ρ_b > 0`), `g₁ + g₂ = oldThinTen T` `ageμ c (-1/2)`-a.e. (the thin
component is `χ̂_o(νs)T₁`, the repair component `0`), and chart-null sets pull back to null sets
of `(τ, z)` (`chartOfNullPullback`); hence at a.e. `z` the two phase profiles of the lifts agree
for a.e. `τ`. -/
def OldThinPhysAE : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel), 0 < L.ρb Pl K →
    ∀ (T : LStr Pl K L) (g₁ g₂ : Chart → Ten3), IsRep Pl K L (oldThin Pl K L T) g₁ g₂ →
      ∀ᵐ z : Space,
        (fun τ => UnforcedLeray.Short.IIIa.srcNorm (oldPhys L.ε⁻¹ (cOf L.ν) (g₁ + g₂)) τ z)
          =ᵐ[volume]
        (fun τ => UnforcedLeray.Short.IIIa.srcNorm
          (NearInst.cartLift L.ε⁻¹ (cOf L.ν) (oldThinTen Pl K L T)) τ z)

end UnforcedLeray.Short.PartIIIb.Concrete
