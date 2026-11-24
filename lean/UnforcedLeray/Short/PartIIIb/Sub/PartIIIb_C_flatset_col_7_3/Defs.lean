import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7

/-!
# Concrete objects for `BodyColumnWeak` (organizer task `PartIII-b:C/flatset/col/7/3/org`)

Source of record `the November 2 reference manuscript`: 1650-1656
(`A₀ = -S + νsΔ_{q,η}`, `T₀ = (μ - A₀)⁻¹P₀`, `P₀` the planar cylinder projection), 1684-1689
(the flat equation `(∂_s + μ/s - νΔ)b = P₀ div₀ M`, here with the body force `h = s f`).

* `A0adj` : the `H`-adjoint `A₀*` of `A₀ = -S + νsΔ` on smooth tests (`H = L²(s^{-3/2}ds dq dη)`):
  `A₀*ζ = S ζ - ζ/2 + νsΔζ` (integrate `-s u_s v̄ s^{-3/2}` by parts; it is the generator of
  `T₀(t)* = e^{-t/2}e^{νs(eᵗ-1)Δ}f(seᵗ)`, `B0224.T0adj_apply_ae`).
* `resolventTest ν μ ζ = (μ - A₀*)ζ`.
* `pairH c u v = ⟨u, v⟩_H = ∫ ⟪v, u⟫ s^{-3/2} ds dq dη` over the cell `(0, c]` (linear in `u`).
* `zetaPhi Φ = s^{1/2}Φ`: the `H`-test attached to a flat test `Φ` of the age-space weak
  equation; `H` has `s^{-3/2}ds`, so `(μ - A₀*)(s^{1/2}Φ) = s^{1/2}(μΦ - sΦ_s - νsΔΦ)`, and
  `⟨b, (μ - A₀*)ζ⟩_H` is the space-time integral `∫(-bΦ_s + (μ/s)bΦ - νbΔΦ)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.IIIa (IsFlatTest flatDt flatLap)
open UnforcedLeray.Short.PartIIa (IsMeridTest PepsC T0flat solenoidalHC pdS pdQ pdEta)

/-- **The adjoint `A₀*` of `A₀ = -S + νsΔ_{q,η}` in `H`** on smooth profiles (source 1650-1656):
`A₀*ζ = s∂_sζ - ζ/2 + νs(∂_q² + ∂_η²)ζ`. -/
def A0adj (ν : ℝ) (ζ : Profile → MeridC) : Profile → MeridC := fun p =>
  p.1 • pdS ζ p - (1 / 2 : ℝ) • ζ p + (ν * p.1) • (pdQ (pdQ ζ) p + pdEta (pdEta ζ) p)

/-- `(μ - A₀*)ζ` for real `μ`. -/
def resolventTest (ν μ : ℝ) (ζ : Profile → MeridC) : Profile → MeridC := fun p =>
  μ • ζ p - A0adj ν ζ p

/-- The inner product `⟨u, v⟩_H = ∫ ⟪v, u⟫ s^{-3/2} ds dq dη` of `H = L²(measureH c; ℂ²)` on
profile functions (linear in `u`; for `u, v ∈ H` it is `inner ℂ v u`). -/
def pairH (c : ℝ) (u v : Profile → MeridC) : ℂ :=
  ∫ p, inner ℂ (v p) (u p) ∂(measureH c)

/-- `ζ_Φ = s^{1/2}Φ` as a meridional profile (the `H`-test of a flat test `Φ`). -/
def zetaPhi (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) : Profile → MeridC := fun p =>
  WithLp.toLp 2 fun i => (((Real.sqrt p.1 * Φ p.1 p.2 i : ℝ)) : ℂ)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
