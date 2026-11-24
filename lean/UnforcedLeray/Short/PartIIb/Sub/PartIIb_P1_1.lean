import UnforcedLeray.Short.PartIIb.Sub.P1

/-!
# Decomposition of `PartII-b:P1/1` (`BodyLiftLinear`)

Source: `the November 2 reference manuscript` 1902-1906.
Three true source facts are stated as `Prop`s and `BodyLiftLinear` is derived from them.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-- (a) Range (SP 1902-1906): every real solenoidal `𝒪`-invariant element of `Y_{q₀}` is the ring
lift `N_v b` of a `c`-periodic profile `b ∈ H_p`, a.e. (inverse chart `(τ,ϱ,z) ↔ (s,q,η)`). -/
def BLRange : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ (p : Params) (d : ℝ), BgRegime p d dm dp →
    ∀ f : p.Y, ∃ g : HpR p.c, ∀ᵐ x : ℝ × Space,
      rep (f : Yq p.period q0E) x.1 x.2 = NvC p.R (toProf p.c g) x

/-- (b) A.e. injectivity of the ring lift on `H_p` profiles (the chart is a bijection mod the
period, up to null sets; SP 1902-1906). -/
def BLUniq : Prop :=
  ∀ (R c : ℝ), 0 < R → 0 < c → ∀ g₁ g₂ : HpR c,
    (∀ᵐ x : ℝ × Space, NvC R (toProf c g₁) x = NvC R (toProf c g₂) x) → g₁ = g₂

/-- (c) Additivity of the lift: `N_v` of the profile of a sum (resp. real multiple) is the sum
(resp. multiple) a.e. -/
def BLNvLin : Prop :=
  ∀ (R c : ℝ), 0 < c → ∀ g₁ g₂ : HpR c,
    (∀ᵐ x : ℝ × Space, NvC R (toProf c (g₁ + g₂)) x
        = NvC R (toProf c g₁) x + NvC R (toProf c g₂) x) ∧
    ∀ a : ℝ, ∀ᵐ x : ℝ × Space, NvC R (toProf c (a • g₁)) x = a • NvC R (toProf c g₁) x

/-- (d) Additivity/homogeneity of the joint representative `rep`. -/
def BLRepLin : Prop :=
  ∀ p : Params, ∀ f h : p.Y,
    (∀ᵐ x : ℝ × Space, rep ((f + h : p.Y) : Yq p.period q0E) x.1 x.2
        = rep (f : Yq p.period q0E) x.1 x.2 + rep (h : Yq p.period q0E) x.1 x.2) ∧
    ∀ a : ℝ, ∀ᵐ x : ℝ × Space, rep ((a • f : p.Y) : Yq p.period q0E) x.1 x.2
        = a • rep (f : Yq p.period q0E) x.1 x.2

theorem bodyLiftLinear_of (h1 : BLRange) (h2 : BLUniq) (h3 : BLNvLin) (h4 : BLRepLin) :
    BodyLiftLinear := by
  intro dm dp hdm p d hreg
  have hR : 0 < p.R := by unfold Params.R; exact inv_pos.2 p.ε_pos
  have hc : 0 < p.c := p.c_pos
  choose G hG using h1 dm dp hdm p d hreg
  have hadd : ∀ f h : p.Y, G (f + h) = G f + G h := by
    intro f h
    apply h2 p.R p.c hR hc
    have e1 := hG (f + h)
    have e2 := (h4 p f h).1
    have e3 := hG f
    have e4 := hG h
    have e5 := (h3 p.R p.c hc (G f) (G h)).1
    filter_upwards [e1, e2, e3, e4, e5] with x a b c' d' e
    rw [← a, b, c', d', e]
  have hsmul : ∀ (a : ℝ) (f : p.Y), G (a • f) = a • G f := by
    intro a f
    apply h2 p.R p.c hR hc
    have e1 := hG (a • f)
    have e2 := (h4 p f f).2 a
    have e3 := hG f
    have e5 := (h3 p.R p.c hc (G f) (G f)).2 a
    filter_upwards [e1, e2, e3, e5] with x a' b c' e
    rw [← a', b, c', e]
  exact ⟨{ toFun := G, map_add' := hadd, map_smul' := hsmul }, hG⟩

end UnforcedLeray.Short.IIb
