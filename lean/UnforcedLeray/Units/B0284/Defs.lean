import UnforcedLeray.Units.B0191
import UnforcedLeray.Analysis.GaussianVortex.PlanarDefs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# B0284 `background:eq:2.24`, definitions: cylinder, `𝕡₀`, `e^{θΔ}`, `T̄`

Unit B0284 of `paper/main.tex`, label `background:eq:2.24`, tex lines 5247–5250

blueprint/units.json`). This file holds the definitions and their elementary properties; the
`L^p` estimates are in `UnforcedLeray.Units.B0284.Contraction` and `UnforcedLeray.Units.B0284`.

The manuscript's formula is
`T̄F(s) = ∫₀ˢ e^{ν(s-t)Δ} 𝕡₀(F(t)/t) dt`, with `Δ = ∂_q² + ∂_η²` on the cylinder
`T_c × ℝ = (ℝ/cℤ) × ℝ` and `𝕡₀` the flat two-dimensional Leray projection. The field `F` is
an age-dependent `ℝ²`-valued field on the cylinder in the component order `(r, z)`, which
pairs with the coordinates `(q, η)` (tex lines 3745–3755 and 5240–5246).

Formal conventions.
* A field on the cylinder is its `c`-periodic lift `Plane → β`, `Plane = ℝ × ℝ` with
  coordinates `(q, η)` (`IsQPeriodic`). One cell is `cell c = (0, c] × ℝ`
  (the same set as `CylinderNS.oneCell c` of the draft `Analysis/CylinderNS/Defs.lean`).
  `cellMeasure c = c⁻¹ · Lebesgue|_{cell}` is the manuscript's normalized measure
  `dq/c dη` (tex lines 4659, 4960–4964, 5232). The norm on `Plane` is Mathlib's max norm;
  every estimate in this unit holds verbatim for it.
* `heat θ` is `e^{θΔ}` for `θ > 0`: convolution of the periodic lift with the planar Gaussian
  `heatKernel2 θ w = G_θ(w.1) G_θ(w.2)`, where `G_θ = B0191.heatKernel 1 θ
  = (4πθ)^{-1/2} e^{-x²/(4θ)}` (tex line 2738). Convolving the periodic lift with the planar
  Gaussian is the cylinder heat semigroup (its kernel on the cell is the periodized Gaussian).
  For `θ ≤ 0` the definition returns the field unchanged; `T̄` only uses `θ = ν(s-t) > 0`
  when `ν > 0`.
* `𝕡₀` is defined through the Helmholtz decomposition on the cylinder:
  `IsFlatLerayDecomp c F G` says that `F` and `G` lie in one `L^p(cell)`, `1 ≤ p < ∞`, that
  `G` is periodic and weakly divergence free (against smooth periodic test functions with
  bounded `η`-support), and that `F - G` annihilates every smooth periodic divergence-free
  test field with bounded `η`-support, i.e. `F - G` is the gradient of a periodic potential.
  Every pairing carries an explicit integrability clause, so no integral in the definition is
  a junk value. For `1 < p < ∞` the Fourier multiplier `δ - ζζᵀ/|ζ|²` gives such a
  decomposition (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8; blueprint INF01), and it
  is unique (a periodic field that is both divergence free and a gradient is harmonic and lies
  in `L^p + L^{p'}`, hence vanishes). Neither existence nor uniqueness is proved here.
  `flatLeray c F` is a decomposition whenever one exists (`flatLeray_spec`) and `0` otherwise
  (`flatLeray_of_not`); the second case does not occur for the manuscript's inputs
  `F(t)/t ∈ L^p`, `1 < p < ∞`.
* `flatInverse ν c F s z = ∫_{t ∈ (0,s)} (heat (ν(s-t)) (flatLeray c (t⁻¹ • F t))) z dt` is a
  pointwise Bochner integral in `Plane`. Where the integrand is not integrable, Lean's value is
  `0`; the estimates of this unit are proved through `‖∫ g‖ₑ ≤ ∫⁻ ‖g‖ₑ`, which holds without
  integrability, so they hold for Lean's value. For `s ≤ 0` the age interval is empty and the
  value is `0` (zero initial value).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Real
open scoped ContDiff NNReal ENNReal

namespace UnforcedLeray.B0284

open UnforcedLeray.GaussianVortex (Plane partialX partialY gradient divergence)

/-! ## The cylinder `T_c × ℝ` through periodic lifts -/

/-- A function on the plane is `c`-periodic in `q`, i.e. a function on the cylinder
`(ℝ/cℤ) × ℝ` (tex lines 4949, 4960–4964). -/
def IsQPeriodic {β : Type*} (c : ℝ) (f : Plane → β) : Prop :=
  ∀ z : Plane, f (z.1 + c, z.2) = f z

/-- One cell `(0, c] × ℝ` of the cylinder. -/
def cell (c : ℝ) : Set Plane := Ioc 0 c ×ˢ univ

theorem measurableSet_cell (c : ℝ) : MeasurableSet (cell c) :=
  measurableSet_Ioc.prod MeasurableSet.univ

/-- The manuscript's normalized cylinder measure `dq/c dη` on one cell
(tex lines 4659, 4960–4964, 5232). -/
def cellMeasure (c : ℝ) : Measure Plane := (c.toNNReal)⁻¹ • volume.restrict (cell c)

/-- The Euclidean pairing of two planar vectors. -/
def dot (u v : Plane) : ℝ := u.1 * v.1 + u.2 * v.2

/-- A scalar test function on the cylinder: `C^∞`, `c`-periodic in `q`, and vanishing for
`|η|` large. -/
structure IsCylTest (c : ℝ) (φ : Plane → ℝ) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ
  periodic : IsQPeriodic c φ
  bounded_support : ∃ L : ℝ, ∀ z : Plane, L < |z.2| → φ z = 0

/-- A divergence-free vector test field on the cylinder (`divergence` is the classical flat
divergence `∂_q Ψ₁ + ∂_η Ψ₂` of `GaussianVortex`). -/
structure IsSolenoidalCylTest (c : ℝ) (Ψ : Plane → Plane) : Prop where
  fst : IsCylTest c (fun z => (Ψ z).1)
  snd : IsCylTest c (fun z => (Ψ z).2)
  div_free : ∀ z : Plane, divergence Ψ z = 0

/-! ## The flat Leray projection `𝕡₀` on the cylinder -/

/-- `G = 𝕡₀ F`: the Helmholtz decomposition `F = G + (F - G)` on the cylinder, with `G`
weakly divergence free and `F - G` a gradient (it annihilates divergence-free test fields),
both `F` and `G` in one `L^p(cell)`, `1 ≤ p < ∞` (tex line 5249; Grafakos Cor. 5.2.8).
Every pairing is required to be integrable, so no integral below is a junk value. -/
structure IsFlatLerayDecomp (c : ℝ) (F G : Plane → Plane) : Prop where
  exponent : ∃ p : ℝ≥0∞, 1 ≤ p ∧ p ≠ ⊤ ∧
    MemLp F p (cellMeasure c) ∧ MemLp G p (cellMeasure c)
  periodic : IsQPeriodic c G
  solenoidal : ∀ φ : Plane → ℝ, IsCylTest c φ →
    Integrable (fun z => dot (G z) (gradient φ z)) (cellMeasure c) ∧
      ∫ z, dot (G z) (gradient φ z) ∂(cellMeasure c) = 0
  gradient_part : ∀ Ψ : Plane → Plane, IsSolenoidalCylTest c Ψ →
    Integrable (fun z => dot (F z - G z) (Ψ z)) (cellMeasure c) ∧
      ∫ z, dot (F z - G z) (Ψ z) ∂(cellMeasure c) = 0

open Classical in
/-- The flat two-dimensional Leray projection `𝕡₀` on the cylinder `T_c × ℝ` (tex line 5249):
the divergence-free part of the Helmholtz decomposition when one exists, `0` otherwise. -/
def flatLeray (c : ℝ) (F : Plane → Plane) : Plane → Plane :=
  if h : ∃ G, IsFlatLerayDecomp c F G then h.choose else 0

/-- Whenever `F` has a flat Helmholtz decomposition, `flatLeray c F` is one. -/
theorem flatLeray_spec {c : ℝ} {F : Plane → Plane} (h : ∃ G, IsFlatLerayDecomp c F G) :
    IsFlatLerayDecomp c F (flatLeray c F) := by
  classical
  unfold flatLeray
  simp only [h, ↓reduceDIte]
  exact h.choose_spec

/-- Without a decomposition `flatLeray c F = 0` (a junk value, never used by the manuscript). -/
theorem flatLeray_of_not {c : ℝ} {F : Plane → Plane} (h : ¬ ∃ G, IsFlatLerayDecomp c F G) :
    flatLeray c F = 0 := by
  classical
  unfold flatLeray
  simp only [h, ↓reduceDIte]

/-- `𝕡₀ F` is always a field on the cylinder. -/
theorem flatLeray_periodic (c : ℝ) (F : Plane → Plane) : IsQPeriodic c (flatLeray c F) := by
  by_cases h : ∃ G, IsFlatLerayDecomp c F G
  · exact (flatLeray_spec h).periodic
  · rw [flatLeray_of_not h]
    intro z
    rfl

/-! ## The heat semigroup `e^{θΔ}` on the cylinder -/

/-- The planar heat kernel of `e^{θΔ}`, `Δ = ∂_q² + ∂_η²`: the product of two copies of the
one-dimensional kernel `(4πθ)^{-1/2} e^{-x²/(4θ)}` of B0191 (tex line 2738). -/
def heatKernel2 (θ : ℝ) (w : Plane) : ℝ :=
  B0191.heatKernel 1 θ w.1 * B0191.heatKernel 1 θ w.2

/-- `e^{θΔ}` on the cylinder `T_c × ℝ` for `θ > 0`: convolution of the periodic lift with the
planar heat kernel. For `θ ≤ 0` it returns the field unchanged; only `θ > 0` is used
(tex line 5249). -/
def heat (θ : ℝ) (f : Plane → Plane) : Plane → Plane :=
  fun z => if 0 < θ then ∫ w : Plane, heatKernel2 θ w • f (z - w) else f z

theorem heat_apply_of_pos {θ : ℝ} (hθ : 0 < θ) (f : Plane → Plane) (z : Plane) :
    heat θ f z = ∫ w : Plane, heatKernel2 θ w • f (z - w) := by
  simp [heat, hθ]

theorem heat_of_nonpos {θ : ℝ} (hθ : θ ≤ 0) (f : Plane → Plane) : heat θ f = f := by
  funext z
  simp [heat, not_lt.mpr hθ]

/-- The one-dimensional kernel has unit mass. -/
theorem integral_heatKernel_one {θ : ℝ} (hθ : 0 < θ) :
    ∫ x : ℝ, B0191.heatKernel 1 θ x = 1 := by
  have h1 : (fun x : ℝ => B0191.heatKernel 1 θ x) =
      fun x => (√(4 * π * 1 * θ))⁻¹ * Real.exp (-(1 / (4 * θ)) * x ^ 2) := by
    funext x
    simp only [B0191.heatKernel]
    congr 2
    ring
  have hpos : 0 < 4 * π * 1 * θ := by positivity
  rw [h1, integral_const_mul, integral_gaussian]
  rw [show π / (1 / (4 * θ)) = 4 * π * 1 * θ by field_simp]
  exact inv_mul_cancel₀ (Real.sqrt_pos.mpr hpos).ne'

theorem heatKernel2_nonneg {θ : ℝ} (hθ : 0 < θ) (w : Plane) : 0 ≤ heatKernel2 θ w :=
  mul_nonneg (B0191.heatKernel_pos one_pos hθ _).le (B0191.heatKernel_pos one_pos hθ _).le

/-- The planar kernel has unit mass. -/
theorem integral_heatKernel2 {θ : ℝ} (hθ : 0 < θ) : ∫ w : Plane, heatKernel2 θ w = 1 := by
  calc ∫ w : Plane, heatKernel2 θ w
      = ∫ w, B0191.heatKernel 1 θ w.1 * B0191.heatKernel 1 θ w.2
          ∂((volume : Measure ℝ).prod volume) := rfl
    _ = (∫ x, B0191.heatKernel 1 θ x) * ∫ y, B0191.heatKernel 1 θ y :=
        integral_prod_mul (fun x => B0191.heatKernel 1 θ x) (fun y => B0191.heatKernel 1 θ y)
    _ = 1 := by rw [integral_heatKernel_one hθ, one_mul]

/-- `e^{θΔ}` fixes constant fields (`θ > 0`). -/
theorem heat_const {θ : ℝ} (hθ : 0 < θ) (v : Plane) :
    heat θ (fun _ => v) = fun _ => v := by
  funext z
  rw [heat_apply_of_pos hθ, integral_smul_const, integral_heatKernel2 hθ, one_smul]

/-- `e^{θΔ}` maps cylinder fields to cylinder fields. -/
theorem heat_periodic {c θ : ℝ} {f : Plane → Plane} (hf : IsQPeriodic c f) :
    IsQPeriodic c (heat θ f) := by
  intro z
  by_cases hθ : 0 < θ
  · rw [heat_apply_of_pos hθ, heat_apply_of_pos hθ]
    congr 1
    funext w
    have hz : ((z.1 + c, z.2) : Plane) - w = ((z - w).1 + c, (z - w).2) := by
      ext
      · simp only [Prod.fst_sub]
        ring
      · simp
    rw [hz, hf]
  · rw [heat_of_nonpos (not_lt.mp hθ)]
    exact hf z

/-! ## The flat inverse `T̄` (tex lines 5247–5250) -/

/-- The flat (`ε = 0`) cylinder inverse of tex eq. (2.24), `background:eq:2.24`:
`T̄F(s) = ∫₀ˢ e^{ν(s-t)Δ} 𝕡₀(F(t)/t) dt`, evaluated pointwise on the cylinder. -/
def flatInverse (ν c : ℝ) (F : ℝ → Plane → Plane) (s : ℝ) : Plane → Plane :=
  fun z => ∫ t in Ioo 0 s, heat (ν * (s - t)) (flatLeray c (t⁻¹ • F t)) z

/-- For `ν > 0` every heat time in the integral is positive, so the definition is the
manuscript's formula with the Gaussian convolution written out. -/
theorem flatInverse_eq_of_pos {ν : ℝ} (hν : 0 < ν) (c : ℝ) (F : ℝ → Plane → Plane)
    (s : ℝ) (z : Plane) :
    flatInverse ν c F s z =
      ∫ t in Ioo 0 s, ∫ w : Plane,
        heatKernel2 (ν * (s - t)) w • flatLeray c (t⁻¹ • F t) (z - w) := by
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  exact heat_apply_of_pos (mul_pos hν (sub_pos.mpr ht.2)) _ z

/-- Zero initial value: for `s ≤ 0` the age interval is empty. -/
theorem flatInverse_of_nonpos {s : ℝ} (hs : s ≤ 0) (ν c : ℝ) (F : ℝ → Plane → Plane) :
    flatInverse ν c F s = 0 := by
  funext z
  simp [flatInverse, Ioo_eq_empty_of_le hs]

/-- `T̄F(s)` is a field on the cylinder. -/
theorem flatInverse_periodic (ν c : ℝ) (F : ℝ → Plane → Plane) (s : ℝ) :
    IsQPeriodic c (flatInverse ν c F s) := by
  intro z
  refine setIntegral_congr_fun measurableSet_Ioo fun _ _ => ?_
  exact heat_periodic (flatLeray_periodic c _) z

/-- Causality, almost-everywhere form: `T̄F(s)` only sees `F` almost everywhere on `(0, s)`. -/
theorem flatInverse_congr_ae {ν c s : ℝ} {F G : ℝ → Plane → Plane}
    (h : ∀ᵐ t, t ∈ Ioo 0 s → F t = G t) :
    flatInverse ν c F s = flatInverse ν c G s := by
  funext z
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  filter_upwards [h] with _ ht hts
  rw [ht hts]

/-- Causality in age: if two inputs agree on `(0, s)`, their flat inverses agree at every
age `s' ≤ s`. -/
theorem flatInverse_causal {ν c s s' : ℝ} {F G : ℝ → Plane → Plane}
    (h : ∀ t ∈ Ioo 0 s, F t = G t) (hs' : s' ≤ s) :
    flatInverse ν c F s' = flatInverse ν c G s' :=
  flatInverse_congr_ae (Eventually.of_forall fun t ht => h t ⟨ht.1, ht.2.trans_le hs'⟩)

/-- Causality in age, cutoff form: `T̄F = T̄(1_{(0,s)}F)` on ages `s' ≤ s`
(the form used in tex eq. (C.22), line 5024). -/
theorem flatInverse_indicator (ν c : ℝ) (F : ℝ → Plane → Plane) {s s' : ℝ} (hs' : s' ≤ s) :
    flatInverse ν c ((Ioo 0 s).indicator F) s' = flatInverse ν c F s' :=
  flatInverse_causal (fun _ ht => Set.indicator_of_mem ht F) hs'

end UnforcedLeray.B0284
