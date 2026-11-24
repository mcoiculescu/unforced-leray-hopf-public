import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5_4

/-!
# `AdjPair` decomposed (task `PartIII-b:C/near/pins/3/5/4/4`)

Source `the November 2 reference manuscript`:
1339-1362, 3346-3352 (`S_ε(t)F(x,τ) = e^{t/2}[e^{νε²(e^t-1)Δ}F(·,τ-t)](e^{t/2}x)`).
With `c = e^{t/2}`, `a = νε²(e^t - 1)`:

* `AdjPairRep`  : the a.e. formula `S_formula` transferred from `PSpace` to `ℝ × ℝ³`;
* `RepXGood`    : `repX F` is a.e. strongly measurable, `P`-periodic, `L²` over one period;
* `AdjPairCore` : the pointwise identity `⟨∇φ, c ∫G_a F'(·-t, c·-w)⟩ = ⟨adjGradT, F'⟩`;
  split into `AdjSpatial` (fixed phase, `ℝ³` Fubini) and the phase assembly.

Proved here: `adjPair_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.B0223 (SpaceC X outerS)

/-- **Leaf R** (source 1339-1362, 3350-3352; `B0223.S_formula` + the a.e. transfer along
`(τ,y) ↦ (y, τ mod P)`, which is quasi-measure-preserving `ℝ × ℝ³ → PSpace P`; unfolding
`heatConv (ιx P)` with `ιx w = (w, 0)` and `AddCircle.coe_sub`). -/
def AdjPairRep : Prop :=
  ∀ (ν ε : ℝ) (hν : 0 < ν), 0 < ε → ∀ (P : ℝ) [Fact (0 < P)] (t : ℝ), 0 < t →
    ∀ F : X SpaceC P,
      repX P ((outerS (E := SpaceC) (P := P) hν ε).T t F) =ᵐ[volume]
        fun x : ℝ × Space => (Real.exp (t / 2) : ℝ) •
          ∫ w : Euc 3, gaussKernel 3 (ν * ε ^ 2 * (Real.exp t - 1)) w •
            repX P F (x.1 - t, (Real.exp (t / 2) : ℝ) • x.2 - w)

/-- **Leaf G** (`repX F` is the pull-back of an `L²(PSpace P)` class along `(τ,y) ↦ (y, τ mod P)`):
a.e. strongly measurable, `P`-periodic in `τ`, and `‖repX F‖²` integrable over `(0,P] × ℝ³`. -/
def RepXGood : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (F : X SpaceC P),
    AEStronglyMeasurable (repX P F) volume ∧
    (∀ τ y, repX P F (τ + P, y) = repX P F (τ, y)) ∧
    IntegrableOn (fun x : ℝ × Space => ‖repX P F x‖ ^ 2) (Ioc (0 : ℝ) P ×ˢ univ)

/-- **Leaf S1** (Fubini; source 1339-1362): for fixed `y`, `u = cy - w` turns
`∫ G_a(w) f(cy - w) dw` into `∫ G_a(cy - u) f(u) du`; then swap `y`, `u` (integrable: `A` bounded
with bounded support, `f ∈ L²`, `G_a ∈ L¹ ∩ L^∞`):
`∫ ⟨A(y), c ∫ G_a(w) f(cy - w) dw⟩ dy = c ∫ ⟨∫ G_a(cy - u) A(y) dy, f(u)⟩ du`. -/
def AdjSpatialFubini : Prop :=
  ∀ (a t : ℝ), 0 < a → ∀ (A f : Space → CVec3), Continuous A → (∃ R : ℝ, ∀ y, R < ‖y‖ → A y = 0) →
    AEStronglyMeasurable f volume → Integrable (fun u => ‖f u‖ ^ 2) volume →
    ∫ y, dotL (A y) ((Real.exp (t / 2) : ℝ) • ∫ w : Euc 3, gaussKernel 3 a w •
        f ((Real.exp (t / 2) : ℝ) • y - w))
      = ((Real.exp (t / 2) : ℝ) : ℂ) * ∫ u, dotL (∫ y, gaussKernel 3 a ((Real.exp (t / 2) : ℝ) • y - u) • A y)
          (f u)

/-- **Leaf S2** (scaling and evenness; source 1339-1362): `y = c⁻¹ v` (Jacobian `c⁻³ = e^{-3t/2}`,
`Measure.integral_comp_smul`), `v = u - w`, `G_a` even (`gaussKernel_neg`):
`∫ G_a(cy - u) A(y) dy = e^{-3t/2} ∫ G_a(w) A(e^{-t/2}(u - w)) dw`. -/
def AdjSpatialScale : Prop :=
  ∀ (a t : ℝ), 0 < a → ∀ (A : Space → CVec3), Continuous A → (∃ R : ℝ, ∀ y, R < ‖y‖ → A y = 0) →
    ∀ u : Space, ∫ y, gaussKernel 3 a ((Real.exp (t / 2) : ℝ) • y - u) • A y
      = (Real.exp (-(3 * t / 2)) : ℝ) • ∫ w : Euc 3, gaussKernel 3 a w •
          A ((Real.exp (-t / 2) : ℝ) • (u - w))

/-- **Leaf S** (fixed phase, `ℝ³` change of variables and Fubini; source 1339-1362): for `a > 0`,
`A` continuous with bounded support, `f ∈ L²(ℝ³)`, `c = e^{t/2}`,
`∫ ⟨A(y), c ∫ G_a(w) f(cy - w) dw⟩ dy = ∫ ⟨e^{-t} ∫ G_a(w) A(e^{-t/2}(u - w)) dw, f(u)⟩ du`.
(Proof: `u = cy - w`, Fubini, `y = c⁻¹ v`, Jacobian `c⁻³`, `G_a` even and of unit mass:
`c · c⁻³ = e^{-t}`.) -/
def AdjSpatial : Prop :=
  ∀ (a t : ℝ), 0 < a → ∀ (A f : Space → CVec3), Continuous A → (∃ R : ℝ, ∀ y, R < ‖y‖ → A y = 0) →
    AEStronglyMeasurable f volume → Integrable (fun u => ‖f u‖ ^ 2) volume →
    ∫ y, dotL (A y) ((Real.exp (t / 2) : ℝ) • ∫ w : Euc 3, gaussKernel 3 a w •
        f ((Real.exp (t / 2) : ℝ) • y - w))
      = ∫ u, dotL ((Real.exp (-t) : ℝ) • ∫ w : Euc 3, gaussKernel 3 a w •
          A ((Real.exp (-t / 2) : ℝ) • (u - w))) (f u)

/-- **Leaf C** (the pointwise-field identity; source 1339-1362): for a `P`-periodic locally `L²`
field `F'`, `⟨∇φ, e^{t/2} ∫ G_a(w) F'(· - t, e^{t/2}· - w) dw⟩ = ⟨adjGradT a t φ, F'⟩`. -/
def AdjPairCore : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (a t : ℝ), 0 < a → 0 < t →
    ∀ φ : ℝ × Space → ℂ, IsPhaseTest P φ → ∀ F' : ℝ × Space → CVec3,
      AEStronglyMeasurable F' volume → (∀ τ y, F' (τ + P, y) = F' (τ, y)) →
      IntegrableOn (fun x : ℝ × Space => ‖F' x‖ ^ 2) (Ioc (0 : ℝ) P ×ˢ univ) →
      pairF P (gradT φ) (fun x : ℝ × Space => (Real.exp (t / 2) : ℝ) •
          ∫ w : Euc 3, gaussKernel 3 a w • F' (x.1 - t, (Real.exp (t / 2) : ℝ) • x.2 - w))
        = pairF P (adjGradT a t φ) F'

theorem adjSpatial_of (h1 : AdjSpatialFubini) (h2 : AdjSpatialScale) : AdjSpatial := by
  intro a t ha A f hA hR hfm hf
  rw [h1 a t ha A f hA hR hfm hf, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  beta_reduce
  rw [h2 a t ha A hA hR u]
  have hexp : Real.exp (t / 2) * Real.exp (-(3 * t / 2)) = Real.exp (-t) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [ContinuousLinearMap.map_smul_of_tower, ContinuousLinearMap.map_smul_of_tower,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, Complex.real_smul,
    Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, hexp]

theorem adjPair_of (h1 : AdjPairRep) (h2 : RepXGood) (h3 : AdjPairCore) : AdjPair := by
  intro ν ε hν hε P _ t ht φ hφ F
  have ha : 0 < ν * ε ^ 2 * (Real.exp t - 1) := by
    have : 0 < Real.exp t - 1 := by linarith [Real.add_one_lt_exp ht.ne']
    positivity
  obtain ⟨hm, hp, hi⟩ := h2 P F
  unfold pairX
  rw [pairF_congr_ae (h1 ν ε hν hε P t ht F)]
  exact h3 P _ t ha ht φ hφ _ hm hp hi

end UnforcedLeray.Short.PartIIIb.NearInst
