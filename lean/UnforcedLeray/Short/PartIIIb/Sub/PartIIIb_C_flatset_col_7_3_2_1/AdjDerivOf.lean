import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1
import UnforcedLeray.Lib.HeatR3.Generator

/-!
# `T0adjStrongDerivPos` reduced to five source facts (organizer task
`PartIII-b:C/flatset/col/7/3/2/1/2/org`)

Source `the November 2 reference manuscript` 1650-1656: `A₀ = -S + νsΔ_{q,η}`
with viscosity `ν > 0`, whose `H`-adjoint semigroup is
`T₀(t)*f(s) = e^{-t/2} e^{νs(eᵗ-1)Δ} f(seᵗ)` (`B0224.T0adj_apply_ae`) and whose adjoint generator on
smooth tests is `A₀*ζ = s∂_sζ - ζ/2 + νsΔζ` (`A0adj`).

Route. Write `t0adjFormula c ν s φ` for the explicit formula of `T₀(s)*` applied to a profile `φ`.
1. `T0adjRepAE`: an `H`-class `f` with representative `φ` has `T₀(s)*f = t0adjFormula s φ` a.e.
2. `T0adjPtDeriv`: for a smooth test `ζ`, `ν > 0`, `t > 0`, `s > 0`, the value of the formula at a
   fixed point is differentiable in time with derivative the formula applied to `A₀*ζ` (heat
   equation in `θ`, chain rule in the dilated age `seᵗ`), using
   `PlaneGaussDtLap` (`∂_θG_θ * v = G_θ * Δv` on the plane).
3. `T0adjFormulaDom`: a bound of `t0adjFormula r (A₀*ζ)` uniform for `r` near `t` by one `L²(H)`
   function (age band, Gaussian second moment in `η`).
4. `LpHasDerivOfPointwise`: pointwise derivatives with an `L²` majorant give the strong `L²`
   derivative (mean value inequality and dominated convergence).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa (IsMeridTest pdQ pdEta)

/-- The explicit formula of `T₀(s)*` (source 1650-1656, `B0224.T0adj_apply_ae`) applied to a
profile `φ`: `e^{-s/2} e^{νσ(eˢ-1)Δ_{q,η}}[φ̃(σeˢ, ·)](q, η)` at `p = (σ, q, η)`, `φ̃` the
`c`-periodic extension of `φ` in `q`. -/
def t0adjFormula (c ν s : ℝ) (φ : Profile → MeridC) : Profile → MeridC := fun p =>
  Real.exp (-s / 2) • UnforcedLeray.B0224.planeHeat (ν * p.1 * (Real.exp s - 1))
    (fun z => UnforcedLeray.B0220.periodize c φ (Real.exp s * p.1, z)) p.2

/-- (1) **Representatives.** If the `H`-class `f` has the measurable representative `φ`, then
`T₀(s)*f` is represented by `t0adjFormula c ν s φ` (source 1650-1656, `T₀(s)*` acts on
representatives: the dilation `σ ↦ σeˢ` and the fibrewise heat preserve null sets). -/
def T0adjRepAE : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c) (s : ℝ) (f : HSpace c MeridC) (φ : Profile → MeridC),
    StronglyMeasurable φ → (f : Profile → MeridC) =ᵐ[measureH c] φ →
      (UnforcedLeray.B0224.T0adj hc ν s f : Profile → MeridC) =ᵐ[measureH c]
        t0adjFormula c ν s φ

/-- (5) **The planar heat equation for the kernel** (source 1650-1656, `A₀ = -S + νsΔ_{q,η}`:
`∂_θ e^{θΔ} = e^{θΔ}Δ`): for a smooth meridional test `ζ`, every age `σ`, `θ > 0` and
`x = (q, η)`, `∫ ∂_θG_θ(y) ζ(σ, x - y) dy = ∫ G_θ(y) (∂_q² + ∂_η²)ζ(σ, x - y) dy` on `ℝ²`. -/
def PlaneGaussDtLap : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (ζ : Profile → MeridC), IsMeridTest c ζ → ∀ (θ σ : ℝ), 0 < θ →
    ∀ x : ℝ × ℝ,
      ∫ y : UnforcedLeray.Gaussian.Euc 2, UnforcedLeray.Heat.gaussDt 2 θ y •
          ζ (σ, x - UnforcedLeray.B0224.planeι y) =
        ∫ y : UnforcedLeray.Gaussian.Euc 2, UnforcedLeray.Gaussian.gaussKernel 2 θ y •
          (pdQ (pdQ ζ) (σ, x - UnforcedLeray.B0224.planeι y) +
            pdEta (pdEta ζ) (σ, x - UnforcedLeray.B0224.planeι y))

/-- (2) **Pointwise time derivative of the formula** (source 1650-1656: the generator of
`T₀(t)*` on smooth tests is `A₀* = s∂_s - 1/2 + νsΔ`): for `ν > 0`, `t > 0` and a point with
age `p.1 > 0`, `d/dt t0adjFormula c ν t ζ p = t0adjFormula c ν t (A₀*ζ) p`. -/
def T0adjPtDeriv : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν → ∀ (ζ : Profile → MeridC), IsMeridTest c ζ →
    ∀ t : ℝ, 0 < t → ∀ p : Profile, 0 < p.1 →
      HasDerivAt (fun s : ℝ => t0adjFormula c ν s ζ p) (t0adjFormula c ν t (A0adj ν ζ) p) t

/-- (3) **`L²(H)` domination** (source 1650-1656, `ζ` supported in an age band and `|η| ≤ L`):
near every `t > 0`, the values `t0adjFormula c ν r (A₀*ζ) p` are bounded, uniformly in `r`, by one
function `g ∈ L²(H)`. -/
def T0adjFormulaDom : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν → ∀ (ζ : Profile → MeridC), IsMeridTest c ζ →
    ∀ t : ℝ, 0 < t → ∃ ε : ℝ, 0 < ε ∧ ∃ g : Profile → ℝ, MemLp g 2 (measureH c) ∧
      ∀ᵐ p ∂(measureH c), ∀ r ∈ Ioo (t - ε) (t + ε),
        ‖t0adjFormula c ν r (A0adj ν ζ) p‖ ≤ g p

/-- (4) **Strong `L²` derivative from pointwise derivatives** (the `L²` domination step of
source 1650-1656): if `F s ∈ L²(μ)` is represented by `f s`, `D` by `f' t`, and a.e. the map
`s ↦ f s p` has derivative `f' r p` at every `r` near `t` with `‖f' r p‖ ≤ g p`, `g ∈ L²(μ)`,
then `F` has derivative `D` at `t` in `L²(μ)`. -/
def LpHasDerivOfPointwise : Prop :=
  ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (F : ℝ → Lp MeridC 2 μ) (D : Lp MeridC 2 μ)
    (f f' : ℝ → α → MeridC) (g : α → ℝ) (t ε : ℝ), 0 < ε → MemLp g 2 μ →
    (∀ s, (F s : α → MeridC) =ᵐ[μ] f s) → (D : α → MeridC) =ᵐ[μ] f' t →
    (∀ᵐ p ∂μ, ∀ r ∈ Ioo (t - ε) (t + ε),
      HasDerivAt (fun s : ℝ => f s p) (f' r p) r ∧ ‖f' r p‖ ≤ g p) →
    HasDerivAt F D t

/-- `measureH c` lives on ages `s > 0`. -/
theorem ae_measureH_age_pos (c : ℝ) : ∀ᵐ p ∂(measureH c), 0 < p.1 := by
  filter_upwards [UnforcedLeray.B0220.ae_cell_measureH c] with p hp
  exact hp.1

/-- **Reduction of `T0adjStrongDerivPos`** to the representative formula, the pointwise
derivative, the `L²` domination and the abstract `L²` derivative lemma (source 1650-1656). -/
theorem t0adjStrongDerivPos_of (h1 : T0adjRepAE) (h2 : T0adjPtDeriv) (h3 : T0adjFormulaDom)
    (h4 : LpHasDerivOfPointwise) : T0adjStrongDerivPos := by
  intro c ν hc hν ζ hζ Z AZ hZ hAZ t ht
  obtain ⟨ε₀, hε₀, g, hg, hdom⟩ := h3 c ν hc hν ζ hζ t ht
  have hζm : StronglyMeasurable ζ := hζ.smooth.continuous.stronglyMeasurable
  have hAm : StronglyMeasurable (A0adj ν ζ) :=
    (isMeridTest_A0adj ν hζ).smooth.continuous.stronglyMeasurable
  refine h4 (measureH c) (fun s => UnforcedLeray.B0224.T0adj hc ν s Z)
    (UnforcedLeray.B0224.T0adj hc ν t AZ) (fun s => t0adjFormula c ν s ζ)
    (fun s => t0adjFormula c ν s (A0adj ν ζ)) g t (min ε₀ t) (lt_min hε₀ ht) hg
    (fun s => h1 c ν hc s Z ζ hζm hZ) (h1 c ν hc t AZ _ hAm hAZ) ?_
  filter_upwards [hdom, ae_measureH_age_pos c] with p hp hp1
  intro r hr
  have hmin1 : min ε₀ t ≤ ε₀ := min_le_left _ _
  have hmin2 : min ε₀ t ≤ t := min_le_right _ _
  have hr' : r ∈ Ioo (t - ε₀) (t + ε₀) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hr0 : 0 < r := by linarith [hr.1]
  exact ⟨h2 c ν hc hν ζ hζ r hr0 p hp1, hp r hr'⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
