import UnforcedLeray.Short.PartIIa.Sub.N01.Defs

/-!
# `PartII-a:N01/2` (decomposition): `PhaseSemigroupConj` from the slice formula

Source of record `the November 2 reference manuscript`
lines 1363-1372 (`S(t)h(y) = e^{t/2}[e^{ν(eᵗ-1)Δ}h](e^{t/2}y)`, `R_μ f(τ) = ∫ e^{-μt}S(t)f(τ-t)dt`),
1639-1643 (`y = Rx`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **Leaf `N01/2/1` — the slice formula for `t > 0`** (lines 1363-1372, 1639-1643): if `U` is the
phase lift, then for `t > 0` and a.e. phase `τ`,
`(U (S_ε(t)F))(τ) = S_ν(t)((UF)(τ - t))` in `L²(ℝ³; ℂ³)` (`freeC` = the free semigroup).
Route: `B0223.S_formula` (`(S_ε(t)F)(x,τ) = e^{t/2}[e^{νε²(eᵗ-1)Δ}F(·,τ-t)](e^{t/2}x)` a.e., heat
operator `Heat.heatConv (ιx P)`), the `IsPhaseLift` formula for `F` and `S_ε(t)F`, Fubini
(a.e. `z = (x,τ)` gives a.e. `τ`, a.e. `x`; `volume = P • haarAddCircle` on the circle), the slice
identity `Heat.heatConv (ιx P) θ u (x,τ) = Heat.heatConv (id) θ (u(·,τ)) x`, the bridge
`Heat.flow = average` to `Heat.heatConv`, and `B0421.coeFn_freeC` (real/imaginary parts) with the
Gaussian dilation identity `B0223.heatConv_dil` (`a = ε`, `θ = ν(eᵗ-1)`). -/
def PhaseSliceFormula : Prop :=
  ∀ (ν ε P : ℝ) [Fact (0 < P)] (hν : 0 < ν), 0 < ε →
    ∀ U : B0223.X B0223.SpaceC P →ₗᵢ[ℂ] Yq P 2, IsPhaseLift ε P U →
      ∀ t : ℝ, 0 < t → ∀ F : B0223.X B0223.SpaceC P,
        ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
          (U ((B0223.outerS (E := B0223.SpaceC) (P := P) hν ε).T t F) τ :
              Lp CVec3 2 (volume : Measure Space)) =
            B0421.freeC (p := 2) ENNReal.ofNat_ne_top ν t (U F (τ - t))

theorem phaseSemigroupConj_of (h : PhaseSliceFormula) : PhaseSemigroupConj := by
  intro ν ε P _ hν hε U hU t ht F
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    rw [B0421.phaseT_zero_apply]
    have : (B0223.outerS (E := B0223.SpaceC) (P := P) hν ε).T 0 F = F := by
      have := (B0223.outerS (E := B0223.SpaceC) (P := P) hν ε).T_zero
      rw [this]; rfl
    rw [this]
  · refine Lp.ext ?_
    filter_upwards [h ν ε P hν hε U hU t hpos F, B0421.coeFn_phaseT (P := P) (q := 2)
      ENNReal.ofNat_ne_top ν t (U F)] with τ h1 h2
    rw [h1, h2]

end UnforcedLeray.Short.PartIIa.N01
