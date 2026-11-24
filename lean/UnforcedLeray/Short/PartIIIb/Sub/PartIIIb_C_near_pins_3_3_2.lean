import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_3

/-!
# `GradLiftPairZero`, decomposition (task `PartIII-b:C/near/pins/3/3/2`)

Source `the November 2 reference manuscript`:
1666, 1675-1677 (`P_ε` is orthogonal to the lifted gradients `(D_εΨ, ∂_ηΨ)`), 2666-2668 (the chart
`(τ, y) ↦ (s, q, η)`, `chartOf`), 2683 (`𝒩_v b = √s b`).

The axisymmetric scalar of a profile test `Ψ` is `ψ(τ, y) = Ψ(chartOf ε⁻¹ c y τ)`.  Four leaves:

* `GradLiftChartRep` : `cgrad ε Ψ` is the `H`-class of a real chart form `f`
  (the same transport as `TepsWeakSol1`; `Ψ` is `c`-periodic in `q`);
* `GradLiftScalarTest` : `ψ` is a scalar phase test (smooth, `2εc`-periodic in `τ`, compactly
  supported in `y`: the band `s₀ ≤ s ≤ s₁` keeps `y` away from the axis and bounded);
* `GradLiftPointwise` : the chain rule `velPhys ε⁻¹ c f = ∇_y ψ` off the axis
  (`∂_ϱ = √s (∂_q - εK)`, `∂_z = √s ∂_η`, `Deps`, `dEta`);
* `PhaseIBPScalar` : spatial integration by parts `⟨Φ, F⟩ = -⟨ψ, div Φ⟩` for a gradient `F` off
  the axis (a null set), `ψ`, `Φ` phase tests.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

open MeasureTheory UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open Set
open scoped ENNReal

/-- The axisymmetric scalar `ψ(τ, y) = Ψ(chartOf ε⁻¹ c y τ)` of a profile test (source 2666-2668). -/
def liftScalar (c ε : ℝ) (Ψ : UnforcedLeray.B0226.ProfileTest c) : ℝ × Space → ℝ :=
  fun x => Ψ.1 (chartOf ε⁻¹ c x.2 x.1)

/-- **Leaf A**: `cgrad ε Ψ` has a real chart form `f` (source 1666, 1675-1677). -/
def GradLiftChartRep : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ (Ψ : UnforcedLeray.B0226.ProfileTest c)
    (hm : MemLp (UnforcedLeray.Short.PartIIa.cgrad ε Ψ.1) 2 (measureH c)),
    ∃ f : Chart → Merid, ChartRep c (hm.toLp _) f ∧
      ∀ x : Chart, merC (f x) = UnforcedLeray.Short.PartIIa.cgrad ε Ψ.1 x

/-- **Leaf B**: `ψ` is a scalar phase test for the period `2εc` (source 2666-2668). -/
def GradLiftScalarTest : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ Ψ : UnforcedLeray.B0226.ProfileTest c,
    IsPhaseTest (2 * ε * c) (fun x : ℝ × Space => ((liftScalar c ε Ψ x : ℝ) : ℂ))

/-- **Leaf C**: the chain rule, `𝒩_v f = ∇_y ψ` off the axis (source 1666, 2683). -/
def GradLiftPointwise : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ Ψ : UnforcedLeray.B0226.ProfileTest c, ∀ f : Chart → Merid,
    (∀ x : Chart, merC (f x) = UnforcedLeray.Short.PartIIa.cgrad ε Ψ.1 x) →
    ∀ (τ : ℝ) (y : Space), 0 < hRad y → ∀ i : Fin 3,
      velPhys ε⁻¹ c f (τ, y) i =
        dy i (fun x : ℝ × Space => ((liftScalar c ε Ψ x : ℝ) : ℂ)) (τ, y)

/-- **Leaf D**: spatial integration by parts for the gradient of a scalar phase test (the axis
`{hRad = 0}` is a null set of `ℝ³`). -/
def PhaseIBPScalar : Prop :=
  ∀ (P : ℝ) (ψ : ℝ × Space → ℝ), IsPhaseTest P (fun x : ℝ × Space => ((ψ x : ℝ) : ℂ)) →
    ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ → ∀ F : ℝ × Space → CVec3,
      (∀ (τ : ℝ) (y : Space), 0 < hRad y → ∀ i : Fin 3,
        dy i (fun x : ℝ × Space => ((ψ x : ℝ) : ℂ)) (τ, y) = F (τ, y) i) →
      pairF P Φ F = -scalarPair P ψ Φ

theorem gradLiftPairZero_of (hA : GradLiftChartRep) (hB : GradLiftScalarTest)
    (hC : GradLiftPointwise) (hD : PhaseIBPScalar) : GradLiftPairZero := by
  intro c ε hc hε Φ hΦ Ψ hm
  obtain ⟨f, hrep, hfm⟩ := hA c ε hc hε Ψ hm
  refine ⟨f, hrep, ?_⟩
  have h := hD (2 * ε * c) (liftScalar c ε Ψ) (hB c ε hc hε Ψ) Φ hΦ.1 (velPhys ε⁻¹ c f)
    (fun τ y hy i => (hC c ε hc hε Ψ f hfm τ y hy i).symm)
  rw [h, scalarPair_sol _ hΦ, neg_zero]

end UnforcedLeray.Short.PartIIIb.NearInst
