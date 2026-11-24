import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5
import UnforcedLeray.Units.B0223

/-!
# `SemigroupAdjointGrad` decomposed (task `PartIII-b:C/near/pins/3/5/4`)

Source `the November 2 reference manuscript`:
1675-1677, 1339-1362, 4139-4146.  With `a = νε²(e^t - 1)` and `G_a` the heat kernel on `ℝ³`,
the adjoint test is `χ = adjChi a t φ`, `χ(τ,y) = e^{-t/2} ∫ G_a(w) φ(τ+t, e^{-t/2}(y-w)) dw`.
Its gradient is `e^{-t} ∫ G_a(w) ∇φ(τ+t, e^{-t/2}(y-w)) dw` (`adjGradT`).
Leaves: `AdjL0`, `AdjSmooth`, `AdjGrad`, `AdjPair`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.B0223 (SpaceC X outerS)

/-- The adjoint scalar test `χ(τ,y) = e^{-t/2} ∫ G_a(w) φ(τ+t, e^{-t/2}(y-w)) dw`. -/
def adjChi (a t : ℝ) (φ : ℝ × Space → ℂ) : ℝ × Space → ℂ := fun x =>
  (Real.exp (-t / 2) : ℝ) • ∫ w : Euc 3, gaussKernel 3 a w • φ (x.1 + t, Real.exp (-t / 2) • (x.2 - w))

/-- The vector test `e^{-t} ∫ G_a(w) ∇φ(τ+t, e^{-t/2}(y-w)) dw` (the claimed `∇χ`). -/
def adjGradT (a t : ℝ) (φ : ℝ × Space → ℂ) : ℝ × Space → CVec3 := fun x =>
  (Real.exp (-t) : ℝ) • ∫ w : Euc 3, gaussKernel 3 a w • gradT φ (x.1 + t, Real.exp (-t / 2) • (x.2 - w))

/-- **Leaf Z** (`T 0 = 1`, `ExpSemigroup.T_zero`). -/
def AdjZero : Prop :=
  ∀ (ν ε : ℝ) (hν : 0 < ν) (P : ℝ) [Fact (0 < P)] (F : X SpaceC P),
    (outerS (E := SpaceC) (P := P) hν ε).T 0 F = F

/-- **Leaf 0** (a phase test is an `L²` test: smooth, periodic, and compactly supported in `y`, so
`‖φ‖² + ‖∇φ‖²` is continuous with compact support on `[0,P] × ℝ³`). -/
def AdjL0 : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (φ : ℝ × Space → ℂ), IsPhaseTest P φ → IsL2Test P φ

/-- **Leaf 1** (source 1339-1362): for `a > 0`, `t ≥ 0` and a phase test `φ`, `adjChi a t φ` is an
`L²` test: smooth (differentiation under the Gaussian integral; equivalently the convolution of the
smooth compactly supported `φ^t(y,σ) = φ(e^{-t/2}y, σ+t)` with `G_a`), `P`-periodic in `τ`, and
`χ, ∇χ` are bounded with `‖·‖² ≤ (G_a * |·|)²` integrable over `[0,P] × ℝ³` (Cauchy-Schwarz /
Young with the probability kernel `G_a`, `φ` compactly supported). -/
def AdjSmooth : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (a t : ℝ), 0 < a → 0 ≤ t →
    ∀ φ : ℝ × Space → ℂ, IsPhaseTest P φ → IsL2Test P (adjChi a t φ)

/-- **Leaf 2** (the heat kernel commutes with `∇`; chain rule for `y ↦ e^{-t/2}(y-w)` gives the
factor `e^{-t/2}` in `∇_yφ^t`, hence `e^{-t/2}·e^{-t/2} = e^{-t}` in `∇χ`): `gradT (adjChi a t φ) =
adjGradT a t φ` for `a > 0`, `t ≥ 0`, `φ` a phase test (differentiation under the integral). -/
def AdjGrad : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (a t : ℝ), 0 < a → 0 ≤ t →
    ∀ φ : ℝ × Space → ℂ, IsPhaseTest P φ → gradT (adjChi a t φ) = adjGradT a t φ

/-- **Leaf 3** (`B0223.S_formula` + change of variables `y = e^{t/2}x` + Fubini with the even
unit-mass kernel; shift `τ ↦ τ + t` by periodicity; source 1339-1362):
`⟨∇φ, S(t)F⟩ = ⟨adjGradT, F⟩` for `t > 0`, `a = νε²(e^t - 1)`. -/
def AdjPair : Prop :=
  ∀ (ν ε : ℝ) (hν : 0 < ν), 0 < ε → ∀ (P : ℝ) [Fact (0 < P)] (t : ℝ), 0 < t →
    ∀ φ : ℝ × Space → ℂ, IsPhaseTest P φ → ∀ F : X SpaceC P,
      pairX P (gradT φ) ((outerS (E := SpaceC) (P := P) hν ε).T t F) =
        pairX P (adjGradT (ν * ε ^ 2 * (Real.exp t - 1)) t φ) F

theorem adjZero : AdjZero := by
  intro ν ε hν P _ F
  rw [(outerS (E := SpaceC) (P := P) hν ε).T_zero]
  rfl

theorem semigroupAdjointGrad_of (h0 : AdjL0) (h1 : AdjSmooth) (h2 : AdjGrad)
    (h3 : AdjPair) : SemigroupAdjointGrad := by
  intro ν ε hν hε P _ t ht φ hφ
  rcases ht.eq_or_lt with h | h
  · subst h
    refine ⟨φ, h0 P φ hφ, fun F => ?_⟩
    rw [adjZero ν ε hν P F]
  · have ha : 0 < ν * ε ^ 2 * (Real.exp t - 1) := by
      have : 0 < Real.exp t - 1 := by linarith [Real.add_one_lt_exp h.ne']
      positivity
    refine ⟨adjChi _ t φ, h1 P _ t ha h.le φ hφ, fun F => ?_⟩
    rw [h2 P _ t ha h.le φ hφ]
    exact h3 ν ε hν hε P t h φ hφ F

end UnforcedLeray.Short.PartIIIb.NearInst
