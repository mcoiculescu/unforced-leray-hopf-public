import UnforcedLeray.Cons.L2.BackgroundConcrete.Spaces
import UnforcedLeray.Cons.L2.BackgroundConcrete.Fields
import UnforcedLeray.Units.B0449.Chart

/-!
# Theorem B3, concrete scheme: the operators of the ordinary and nonlinear problems

`paper/main.tex`, lines 5161–5176 (`eq:m3-ordinary-system`), 5195–5205 (`background:eq:2.15`),
5304–5333 (`background:eq:2.28`), 5380–5398 (`background:eq:2.31`–`2.32`), 5693–5727
(`background:eq:2.42`–`2.43`, `unlabeled:5725`); units B0684, B0282, B0200, B0299, B0458,
B0685, B0688.

## Distributions in the class (2.2)

Every element of the force space `Y` (`Spaces.lean`) is solenoidal, so it is determined by its
pairings with **solenoidal phase tests** `Φ` (`IsSolTest`: a phase test with `div_y Φ = 0`);
on such tests the Leray projection is invisible and a pressure gradient pairs to zero. Each
operator of the proof is therefore characterised by an identity of pairings with solenoidal
tests, in which the pointwise fields `U_raw`, `E_i` (not in `Y`, line 5152) and the
representative `rep w` of `w ∈ Y_{q₀}` enter only through period integrals
`P⁻¹∫₀ᴾ∫_{ℝ³}` (`pairF`, the normalisation of `PhaseSpace.phasePair_eq_periodIntegral`):

* `RawRel g` — `g = 𝔓F_R` (2.15): `⟪Φ, g⟫ = ⟪L₀ᵗΦ, U_raw⟫ - ⟪(U_raw·∇)Φ, U_raw⟫`, i.e.
  `⟪Φ, A₀U_raw + U_raw·∇U_raw + ∇(sp)⟫` with `div U_raw = 0`;
* `OrdRel z g` — `g = A₀w + 𝔓B_{U_raw}w + (A₀E_bg + 𝔓B_{U_raw}E_bg)α` (`eq:m3-ordinary-system`)
  for `z = (w, A)`, `α = R^{-2/p}A`: `B_Vh = V·∇h + h·∇V` pairs as
  `⟪(∇V)ᵀΦ - (V·∇)Φ, h⟫` (`convT`);
* `QuadRel z z' g` — `g = 𝔓((e + w)·∇(e' + w'))`, `e = E_bgα` (the polarized quadratic source
  of (2.42), all four inlet/correction products): `⟪Φ, g⟫ = -⟪((e + w)·∇)Φ, e' + w'⟫`.

These identities have at most one solution in `Y` (solenoidal `L^{q₀}` fields annihilating all
solenoidal tests vanish, the `L^q` Helmholtz decomposition behind the bounded `𝔓`), so the
objects below are the manuscript's. This uniqueness is a remark on meaning only: it is not
formalized and no proof uses it (each choice carries its own specification, `lin_spec`,
`inv_spec`, `quad_spec`, `rawRes_spec`).

## The concrete objects

* `lin`: the ordinary operator `Z → Y`, `Classical.choose` of a bounded linear operator
  satisfying `OrdRel` (the zero map if there is none);
* `inv M`: a bounded right inverse of `lin` of norm `≤ M`. The manuscript's inverse
  (2.31)–(2.32) at terminal value `β = 0` is one; the terminal row `C_H` of (2.30) only selects
  one right inverse, and Theorem B3 does not depend on the selection (every small solution of
  the projected equation gives the background, see the main file);
* `quad Pq`: a bounded bilinear map satisfying `QuadRel` with norm `≤ Pq` (2.42);
* `rawRes δ`: an element of `Y` satisfying `RawRel` with norm `≤ δ` (2.15);
* `pair`: `f ↦ (ψ ↦ -∫∫⟨f, ψ⟩)`, written as `-P⟪periodize ψ, f⟫` with the `P`-periodization
  of the test;
* `contRep w`: the jointly continuous representative of `Re w` when there is one (it is unique:
  Lebesgue measure on `ℝ × ℝ³` charges open sets), the real part of `rep w` otherwise. It is
  `P`-periodic in every case (`contRep_periodic`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint UnforcedLeray.Axi UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-! ## Representatives and period integrals -/

section Rep

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- A jointly strongly measurable representative of `w ∈ Y_q`, lifted from the phase
circle. Each spatial slice represents the actual `L^q` class, and the lift is exactly periodic.
Selecting a representative separately in each spatial `L^q` class would not by itself give
joint measurability. -/
def rep (w : Yq P q) (τ : ℝ) (y : Space) : CVec3 :=
  UnforcedLeray.B0449.jointRep w ((τ : AddCircle P), y)

/-- Every phase slice of the joint representative agrees almost everywhere with the spatial
representative of the underlying phase-space element. -/
theorem rep_slice (w : Yq P q) (τ : ℝ) :
    rep w τ =ᵐ[volume] (w (τ : AddCircle P) : Space → CVec3) :=
  UnforcedLeray.B0449.jointRep_slice w (τ : AddCircle P)

/-- The selected phase-space representative is genuinely jointly strongly measurable. -/
theorem stronglyMeasurable_rep (w : Yq P q) :
    StronglyMeasurable (fun x : ℝ × Space => rep w x.1 x.2) := by
  exact (UnforcedLeray.B0449.stronglyMeasurable_jointRep w).comp_measurable
    (((AddCircle.continuous_mk' P).measurable.comp measurable_fst).prodMk measurable_snd)

theorem rep_add_period (w : Yq P q) (τ : ℝ) (y : Space) : rep w (τ + P) y = rep w τ y := by
  simp only [rep, AddCircle.coe_add_period]

/-- The real part of a complex vector. -/
def reP (v : CVec3) : Space := WithLp.toLp 2 (fun i => (v i).re)

/-- `f` is a jointly continuous representative of `Re w`. -/
def IsContRep (w : Yq P q) (f : ℝ → SpatialField) : Prop :=
  Continuous (fun x : ℝ × Space => f x.1 x.2) ∧
    (fun x : ℝ × Space => f x.1 x.2) =ᵐ[volume] fun x => reP (rep w x.1 x.2)

open Classical in
/-- **The smooth representative of the correction** (`unlabeled:5831`, lines 5831–5850): the
jointly continuous representative of `Re w` if there is one, else the real part of `rep w`. -/
def contRep (w : Yq P q) : ℝ → SpatialField :=
  if h : ∃ f, IsContRep w f then h.choose else fun τ y => reP (rep w τ y)

/-- If the correction has a jointly continuous representative, `contRep` is that
representative and retains both its continuity and its almost-everywhere identification with the
actual phase-space element. -/
theorem contRep_spec {w : Yq P q} (h : ∃ f, IsContRep w f) :
    IsContRep w (contRep w) := by
  simp only [contRep, dif_pos h]
  exact h.choose_spec

/-- In either branch of its definition, `contRep` represents the real part of the correction in
the product almost-everywhere sense used by the phase-space pairing. -/
theorem contRep_ae (w : Yq P q) :
    (fun x : ℝ × Space => contRep w x.1 x.2) =ᵐ[volume]
      fun x => reP (rep w x.1 x.2) := by
  unfold contRep
  split_ifs with h
  · exact h.choose_spec.2
  · rfl

/-- The representative of the correction is `P`-periodic in the phase. -/
theorem contRep_periodic (w : Yq P q) : Function.Periodic (contRep w) P := by
  unfold contRep
  split_ifs with h
  · obtain ⟨hc, hae⟩ := h.choose_spec
    set f := h.choose
    have hshift : Measure.QuasiMeasurePreserving
        (Prod.map (fun t : ℝ => t + P) (id : Space → Space)) volume volume :=
      QuasiMeasurePreserving.prodMap (measurePreserving_add_right volume P).quasiMeasurePreserving
        (Measure.QuasiMeasurePreserving.id volume)
    have hcomp := hshift.ae_eq_comp hae
    have hae' : (fun x : ℝ × Space => f (x.1 + P) x.2) =ᵐ[volume]
        fun x => reP (rep w x.1 x.2) := by
      filter_upwards [hcomp] with x hx
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq] at hx
      rw [hx, rep_add_period]
    have hc' : Continuous (fun x : ℝ × Space => f (x.1 + P) x.2) := by
      have := hc.comp ((continuous_add_const P).prodMap (continuous_id (X := Space)))
      simpa [Function.comp_def] using this
    have heq := (Continuous.ae_eq_iff_eq volume hc' hc).1 (hae'.trans hae.symm)
    intro τ
    funext y
    exact congrFun heq (τ, y)
  · intro τ
    funext y
    simp only [rep_add_period]

end Rep

/-- The normalised period integral `P⁻¹∫₀ᴾ∫_{ℝ³} f`. -/
def phaseInt (P : ℝ) (f : ℝ × Space → ℂ) : ℂ := P⁻¹ • ∫ t in Ioc (0 : ℝ) P, ∫ y, f (t, y)

/-- The pairing `⟪Φ, u⟫ = P⁻¹∫₀ᴾ∫ Φ·u` of a test with a pointwise field. -/
def pairF (P : ℝ) (Φ u : ℝ × Space → CVec3) : ℂ := phaseInt P fun x => dotL (Φ x) (u x)

/-! ## Tests -/

/-- A solenoidal phase test: a phase test with `div_y Φ = 0`. -/
def IsSolTest (P : ℝ) (Φ : ℝ × Space → CVec3) : Prop :=
  IsPhaseTest P Φ ∧ ∀ x, ∑ j : Fin 3, dy j Φ x j = 0

/-- The test `(u·∇)Φ = ∑ₖ uₖ∂ₖΦ`. -/
def advT (u : ℝ × Space → CVec3) (Φ : ℝ × Space → CVec3) (x : ℝ × Space) : CVec3 :=
  ∑ k : Fin 3, u x k • dy k Φ x

/-- The test `(∇V)ᵀΦ`, `((∇V)ᵀΦ)ₖ = ∑ᵢ Φᵢ ∂ₖVᵢ`, for a real field `V`. -/
def gradUT (V : ℝ → SpatialField) (Φ : ℝ × Space → CVec3) (x : ℝ × Space) : CVec3 :=
  WithLp.toLp 2 fun k => ∑ i : Fin 3,
    Φ x i * ((fderiv ℝ (V x.1) x.2 (EuclideanSpace.single k 1) i : ℝ) : ℂ)

/-- The transpose of `B_V h = V·∇h + h·∇V` on solenoidal `h` for solenoidal `V`:
`(∇V)ᵀΦ - (V·∇)Φ`. -/
def convT (V : ℝ → SpatialField) (Φ : ℝ × Space → CVec3) (x : ℝ × Space) : CVec3 :=
  gradUT V Φ x - advT (fun x => realC (V x.1 x.2)) Φ x

/-- The `P`-periodization `∑ₖ ψ(τ + kP, y)` of a similarity test, as a complex test. -/
def periodize (P : ℝ) (ψ : SpaceTime → Space) (x : ℝ × Space) : CVec3 :=
  realC (∑' k : ℤ, ψ (x.1 + k * P, x.2))

/-! ## The spaces and coordinates at one parameter point -/

namespace Params

variable (p : Params)

/-- The force space `Y` at the period `P = 2εc`. -/
abbrev Y : Type := forceSpace p.period

/-- The state space `Z = X_{q₀} × ℝ²` at `(ν, P)`. -/
abbrev Z : Type := graphSpace p.period p.ν

/-- The correction `w` of a state. -/
def wOf (z : p.Z) : Yq p.period q0E := cw p.period (z : Amb p.period)

/-- `A₀w = T₀w - νΔw - ½w` of a state (line 5168). -/
def A0 (z : p.Z) : Yq p.period q0E :=
  cT p.period (z : Amb p.period) - cΔ p.period (z : Amb p.period) -
    (1 / 2 : ℝ) • cw p.period (z : Amb p.period)

/-- **The inlet coordinates** `α = R^{-2/p}A = ε^{8/11}A` of a state (line 5697). -/
def coord (z : p.Z) (i : Fin 2) : ℝ := p.ε ^ (8 / 11 : ℝ) * (cA p.period (z : Amb p.period)) i

/-- `U_raw` as a complex field on `ℝ × ℝ³`. -/
def Ufun (x : ℝ × Space) : CVec3 := realC (p.raw x.1 x.2)

/-- The inlet column `E_i` as a complex field. -/
def Efun (i : Fin 2) (x : ℝ × Space) : CVec3 := realC (p.inlet i x.1 x.2)

/-- The affine inlet `e = E_bgα` of the coordinates `α`, as a complex field. -/
def eFun (α : Fin 2 → ℝ) (x : ℝ × Space) : CVec3 :=
  realC (∑ i : Fin 2, α i • p.inlet i x.1 x.2)

/-- The full perturbation `e + w = E_bgα + w` of a state, as a complex field. -/
def uOf (z : p.Z) (x : ℝ × Space) : CVec3 := p.eFun (p.coord z) x + rep (p.wOf z) x.1 x.2

/-! ## The defining identities -/

/-- **`g = 𝔓F_R`** (`background:eq:2.15`, line 5200): for every solenoidal test,
`⟪Φ, g⟫ = ⟪L₀ᵗΦ, U_raw⟫ - ⟪(U_raw·∇)Φ, U_raw⟫`. -/
def RawRel (g : Yq p.period q0E) : Prop :=
  ∀ Φ, IsSolTest p.period Φ →
    phasePair p.period q0E Φ g =
      pairF p.period (L0T p.ν Φ) p.Ufun - pairF p.period (advT p.Ufun Φ) p.Ufun

/-- **The ordinary operator** of `eq:m3-ordinary-system` (lines 5168–5176) at `z = (w, A)`:
`g = A₀w + 𝔓B_{U_raw}w + (A₀E_bg + 𝔓B_{U_raw}E_bg)α`. -/
def OrdRel (z : p.Z) (g : Yq p.period q0E) : Prop :=
  ∀ Φ, IsSolTest p.period Φ →
    phasePair p.period q0E Φ g =
      phasePair p.period q0E Φ (p.A0 z) +
        pairF p.period (convT p.raw Φ) (fun x => rep (p.wOf z) x.1 x.2) +
        ∑ i : Fin 2, (p.coord z i : ℂ) *
          (pairF p.period (L0T p.ν Φ) (p.Efun i) + pairF p.period (convT p.raw Φ) (p.Efun i))

/-- **The polarized quadratic source** of (2.42) (lines 5693–5713) at `(z, z')`:
`g = 𝔓((e + w)·∇(e' + w'))`, i.e. `⟪Φ, g⟫ = -⟪((e + w)·∇)Φ, e' + w'⟫`. -/
def QuadRel (z z' : p.Z) (g : Yq p.period q0E) : Prop :=
  ∀ Φ, IsSolTest p.period Φ →
    phasePair p.period q0E Φ g = -pairF p.period (advT (p.uOf z) Φ) (p.uOf z')

/-! ## The operators -/

open Classical in
/-- **The ordinary operator** `𝓛 : Z → Y` (`eq:m3-ordinary-system`). -/
def lin : p.Z →L[ℝ] p.Y :=
  if h : ∃ L : p.Z →L[ℝ] p.Y, ∀ z, p.OrdRel z (L z) then h.choose else 0

open Classical in
/-- **The ordinary inverse at terminal value zero** (2.31)–(2.32): a bounded right inverse of
`𝓛` with norm `≤ M`. -/
def inv (M : ℝ) : p.Y →L[ℝ] p.Z :=
  if h : ∃ T : p.Y →L[ℝ] p.Z, (∀ f, p.lin (T f) = f) ∧ ‖T‖ ≤ M then h.choose else 0

open Classical in
/-- **The polarized quadratic source** `𝒬` of (2.42), with norm `≤ Pq`. -/
def quad (Pq : ℝ) : p.Z →L[ℝ] p.Z →L[ℝ] p.Y :=
  if h : ∃ Q : p.Z →L[ℝ] p.Z →L[ℝ] p.Y, (∀ z z', p.QuadRel z z' (Q z z')) ∧ ‖Q‖ ≤ Pq
  then h.choose else 0

open Classical in
/-- **The projected raw residual** `𝔓F_R` (2.15), with norm `≤ δ`. -/
def rawRes (δ : ℝ) : p.Y :=
  if h : ∃ g : p.Y, p.RawRel g ∧ ‖g‖ ≤ δ then h.choose else 0

/-- **The pairing of a body source with similarity tests**, `f ↦ (ψ ↦ -∫∫⟨f, ψ⟩)` (lines
164–168), as `-P⟪periodize ψ, f⟫` (the integral over `ℝ` of a `P`-periodic field against a
compactly supported test is `P` times the period average against its periodization). -/
def pair : p.Y →ₗ[ℝ] ((SpaceTime → Space) → ℝ) where
  toFun f ψ := -(p.period * (phasePair p.period q0E (periodize p.period ψ)
    (f : Yq p.period q0E)).re)
  map_add' f g := by
    funext ψ
    simp only [Submodule.coe_add, map_add, Complex.add_re, Pi.add_apply]
    ring
  map_smul' r f := by
    funext ψ
    simp only [Submodule.coe_smul, ContinuousLinearMap.map_smul_of_tower, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- The correction field `w_bg` of a state: the continuous representative. -/
def corr (z : p.Z) : ℝ → SpatialField := contRep (p.wOf z)

theorem corr_periodic (z : p.Z) : Function.Periodic (p.corr z) p.period :=
  contRep_periodic _

/-! ## The choices meet their specifications -/

theorem lin_spec (h : ∃ L : p.Z →L[ℝ] p.Y, ∀ z, p.OrdRel z (L z)) (z : p.Z) :
    p.OrdRel z (p.lin z) := by
  rw [lin, dite_eq_left h]
  exact h.choose_spec z

theorem inv_spec {M : ℝ} (h : ∃ T : p.Y →L[ℝ] p.Z, (∀ f, p.lin (T f) = f) ∧ ‖T‖ ≤ M) :
    (∀ f, p.lin (p.inv M f) = f) ∧ ‖p.inv M‖ ≤ M := by
  rw [inv, dite_eq_left h]
  exact h.choose_spec

theorem quad_spec {Pq : ℝ}
    (h : ∃ Q : p.Z →L[ℝ] p.Z →L[ℝ] p.Y, (∀ z z', p.QuadRel z z' (Q z z')) ∧ ‖Q‖ ≤ Pq) :
    (∀ z z', p.QuadRel z z' (p.quad Pq z z')) ∧ ‖p.quad Pq‖ ≤ Pq := by
  rw [quad, dite_eq_left h]
  exact h.choose_spec

theorem rawRes_spec {δ : ℝ} (h : ∃ g : p.Y, p.RawRel g ∧ ‖g‖ ≤ δ) :
    p.RawRel (p.rawRes δ) ∧ ‖p.rawRes δ‖ ≤ δ := by
  rw [rawRes, dite_eq_left h]
  exact h.choose_spec

end Params

end UnforcedLeray.Cons.C03.Concrete
