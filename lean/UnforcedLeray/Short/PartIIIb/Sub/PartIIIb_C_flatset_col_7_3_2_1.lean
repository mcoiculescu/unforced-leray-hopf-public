import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.Of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Generator identity `d/dt ⟨T₀(t)g, ζ⟩_H = ⟨T₀(t)g, A₀*ζ⟩_H` (`ν > 0`), reduced to two source facts

Source `the November 2 reference manuscript` 1650-1656
(`T₀(t)* = e^{-t/2} e^{νs(eᵗ-1)Δ} f(s eᵗ)`, generator `A₀* = s∂_s - 1/2 + νsΔ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa (IsMeridTest)

/-- `T₀(t)*` is the complex `H`-adjoint of `T₀(t)` (`T₀` commutes with multiplication by `i`;
`B0224.adjoint_T0_eq` is the real adjoint; source 1650-1656). -/
def T0ComplexAdjoint : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c) (t : ℝ) (z g : HSpace c MeridC),
    inner ℂ z (UnforcedLeray.B0224.T0 hc ν t g) = inner ℂ (UnforcedLeray.B0224.T0adj hc ν t z) g

/-- Strong `H`-derivative of the adjoint semigroup on smooth tests, for viscosity `ν > 0`: for
`Z, AZ ∈ H` representing `ζ` and `A₀*ζ`, `d/dt T₀(t)*Z = T₀(t)*(A₀*Z)` for `t > 0` (source
1650-1656: `ν > 0` is the viscosity of `A₀ = -S + νsΔ`; differentiate
`e^{-t/2}e^{νs(eᵗ-1)Δ}ζ(seᵗ)`, with `L²` domination). The hypothesis `ν > 0` is needed: for
`ν < 0` the heat time `νs(eᵗ-1)` is negative, `B0224.planeHeat` is then the identity, and the
derivative has no `νsΔ` term while `A₀*ζ` has one. -/
def T0adjStrongDerivPos : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c), 0 < ν → ∀ (ζ : Profile → MeridC), IsMeridTest c ζ →
    ∀ (Z AZ : HSpace c MeridC), (Z : Profile → MeridC) =ᵐ[measureH c] ζ →
      (AZ : Profile → MeridC) =ᵐ[measureH c] UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.A0adj ν ζ →
    ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => UnforcedLeray.B0224.T0adj hc ν s Z)
        (UnforcedLeray.B0224.T0adj hc ν t AZ) t

theorem t0_generator_of (hA : T0ComplexAdjoint) (hD : T0adjStrongDerivPos)
    (c ν : ℝ) (hc : 0 < c) (hν : 0 < ν) (g : HSpace c MeridC) (ζ : Profile → MeridC) (hζ : IsMeridTest c ζ)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => pairH c (UnforcedLeray.B0224.T0 hc ν s g : Profile → MeridC) ζ)
      (pairH c (UnforcedLeray.B0224.T0 hc ν t g : Profile → MeridC) (A0adj ν ζ)) t := by
  obtain ⟨hZm, hAm⟩ := memLp_test_A0adj c ν ζ hζ
  set Z : HSpace c MeridC := hZm.toLp ζ with hZdef
  set AZ : HSpace c MeridC := hAm.toLp _ with hAZdef
  have hZ : (Z : Profile → MeridC) =ᵐ[measureH c] ζ := hZm.coeFn_toLp
  have hAZ : (AZ : Profile → MeridC) =ᵐ[measureH c] A0adj ν ζ := hAm.coeFn_toLp
  have h1 := hD c ν hc hν ζ hζ Z AZ hZ hAZ t ht
  have h2 := h1.inner ℂ (hasDerivAt_const t g)
  have hfun : (fun s : ℝ => pairH c (UnforcedLeray.B0224.T0 hc ν s g : Profile → MeridC) ζ) =
      fun s : ℝ => inner ℂ (UnforcedLeray.B0224.T0adj hc ν s Z) g := by
    funext s
    rw [pairH_eq_inner _ Z hZ, hA c ν hc s Z g]
  rw [hfun]
  rw [pairH_eq_inner _ AZ hAZ, hA c ν hc t AZ g]
  simpa using h2

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
