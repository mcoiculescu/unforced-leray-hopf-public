import UnforcedLeray.Cons.C03Background.Pieces
import UnforcedLeray.Units.B0140
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Theorem B3: the raw lift of the actual train (`eq:m3-ring-lift`)

`paper/main.tex`, lines 2038–2098 (the train `eq:m3-train` and the lift `eq:m3-ring-lift`,
units B0140, B0186) and line 5199 (Section `sec:st18-6030`: "Use the single actual train of
Section `sec:st18-3303`, with its decaying stream. Set `U_raw = U_R`").

The train is the compiled unit B0140 (`Units/B0140.lean`): `TrainSol ν c` bundles `(v, p, ψ)`
with `IsTrain` (smooth on `s ≥ 0`, `c`-periodic, solenoidal, the momentum equation, the
Gaussian datum, finite cell energy, decaying pressure, a differentiable decaying stream
`v = ∇^⊥ψ`, central oddness). Its existence is B0140's named hypothesis `TrainIVPSolvable`
(Gallay–Slijepčević, cited at lines 2152–2155, unit B0141).

**The lift (lines 2075–2077).** `K_age = η∂_η + 2s∂_s`, `H = (1 - K_age)ψ`,
`U_raw = √s[v₁e_r + (v₂ + εH)e_z]`. In the library's ring lift `Axi.Nv R b = √s(b₀e_r + b₁e_z)`
this is the profile `b_raw(s, ξ, η) = (v₁, v₂ + εH)(s, ξ, η)` (`rawProfile`), with the train
evaluated at age `s` and cylinder point `(ξ, η)`. The partial derivatives in `H` are the
one-variable `deriv`s; for the actual train `ψ` is smooth on `s > 0`, so they are genuine.

**Proved here.**
* `stream_periodic_of_isTrain`: the decaying stream is `c`-periodic in `ξ` at every age `s ≥ 0`
  (`ψ(ξ + c) - ψ(ξ)` has zero gradient because `v` is periodic, and it decays as `|η| → ∞`;
  the argument of B0140's `IsTrain.stream_zero`, adapted).
* `rawProfile_periodic`: `b_raw` is `c`-periodic in `ξ` at every age `s > 0` (the `s`-derivative
  only sees ages near `s`).
* `isBackgroundPiece_raw`: a bounded solenoidal field agreeing off the axis with the lift
  `𝒩_v b_raw` is `P`-periodic (`P = 2c/R = 2εc`, line 2079: "the period is `P = 2εc`") and
  axisymmetric without swirl (line 2097: `U_raw` has no `e_ϑ` component).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Cons.C03

open UnforcedLeray.Blueprint UnforcedLeray.Axi UnforcedLeray.GaussianVortex
open UnforcedLeray.B0140

/-- `H = (1 - K_age)ψ = ψ - η∂_ηψ - 2s∂_sψ` at `(s, ξ, η)` (`eq:m3-ring-lift`, line 2076). -/
def raisedStream (ψ : ℝ → Plane → ℝ) (s ξ η : ℝ) : ℝ :=
  ψ s (ξ, η) - (η * deriv (fun t => ψ s (ξ, t)) η + 2 * s * deriv (fun t => ψ t (ξ, η)) s)

/-- The profile `b_raw = (v₁, v₂ + εH)` of `U_raw = √s[v₁e_r + (v₂ + εH)e_z]`
(`eq:m3-ring-lift`, line 2077), at the chart point `(s, (ξ, η))`. -/
def rawProfile (ε : ℝ) (v : ℝ → Plane → Train.Vec) (ψ : ℝ → Plane → ℝ)
    (p : ℝ × (ℝ × ℝ)) : Merid :=
  v p.1 p.2 + (ε * raisedStream ψ p.1 p.2.1 p.2.2) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

theorem rawProfile_zero (ε : ℝ) (v : ℝ → Plane → Train.Vec) (ψ : ℝ → Plane → ℝ)
    (p : ℝ × (ℝ × ℝ)) : rawProfile ε v ψ p 0 = v p.1 p.2 0 := by
  simp [rawProfile]

theorem rawProfile_one (ε : ℝ) (v : ℝ → Plane → Train.Vec) (ψ : ℝ → Plane → ℝ)
    (p : ℝ × (ℝ × ℝ)) :
    rawProfile ε v ψ p 1 = v p.1 p.2 1 + ε * raisedStream ψ p.1 p.2.1 p.2.2 := by
  simp [rawProfile]

/-- **The decaying stream is `c`-periodic** at every age `s ≥ 0` (line 2051: "The field is
`c`-periodic", with the stream fixed by decay, line 2049). -/
theorem stream_periodic_of_isTrain {ν c : ℝ} {v : ℝ → Plane → Train.Vec} {p ψ : ℝ → Plane → ℝ}
    (h : IsTrain ν c v p ψ) {s : ℝ} (hs : 0 ≤ s) (z : Plane) :
    ψ s (z.1 + c, z.2) = ψ s z := by
  have hψd := h.stream_differentiable s hs
  -- the two partials of `ψ` are components of `v`, which is periodic
  have hX : ∀ w : Plane, partialX (ψ s) w = v s w 1 := fun w => by
    rw [h.stream s hs w]; rfl
  have hY : ∀ w : Plane, partialY (ψ s) w = -(v s w 0) := fun w => by
    rw [h.stream s hs w]
    show partialY (ψ s) w = -(-partialY (ψ s) w)
    rw [neg_neg]
  have hper : ∀ w : Plane, v s (w.1 + c, w.2) = v s w := h.periodic_v s hs
  have hq : ∀ w : Plane,
      HasDerivAt (fun t => ψ s (t + c, w.2) - ψ s (t, w.2)) 0 w.1 := by
    intro w
    have hd1 : DifferentiableAt ℝ (fun t => ψ s (t, w.2)) (w.1 + c) :=
      (hψd _).comp (w.1 + c) (differentiableAt_id.prodMk (differentiableAt_const _))
    have hd2 : DifferentiableAt ℝ (fun t => ψ s (t, w.2)) w.1 :=
      (hψd _).comp w.1 (differentiableAt_id.prodMk (differentiableAt_const _))
    have h1 : HasDerivAt (fun t => ψ s (t + c, w.2)) (partialX (ψ s) (w.1 + c, w.2)) w.1 :=
      HasDerivAt.comp_add_const (f := fun t => ψ s (t, w.2)) w.1 c hd1.hasDerivAt
    have h2 : HasDerivAt (fun t => ψ s (t, w.2)) (partialX (ψ s) w) w.1 := hd2.hasDerivAt
    have he : partialX (ψ s) (w.1 + c, w.2) = partialX (ψ s) w := by
      rw [hX, hX, hper]
    rw [he] at h1
    simpa only [sub_self] using h1.fun_sub h2
  have hη : ∀ w : Plane,
      HasDerivAt (fun t => ψ s (w.1 + c, t) - ψ s (w.1, t)) 0 w.2 := by
    intro w
    have hd1 : DifferentiableAt ℝ (fun t => ψ s (w.1 + c, t)) w.2 :=
      (hψd _).comp w.2 ((differentiableAt_const _).prodMk differentiableAt_id)
    have hd2 : DifferentiableAt ℝ (fun t => ψ s (w.1, t)) w.2 :=
      (hψd _).comp w.2 ((differentiableAt_const _).prodMk differentiableAt_id)
    have h1 : HasDerivAt (fun t => ψ s (w.1 + c, t)) (partialY (ψ s) (w.1 + c, w.2)) w.2 :=
      hd1.hasDerivAt
    have h2 : HasDerivAt (fun t => ψ s (w.1, t)) (partialY (ψ s) w) w.2 := hd2.hasDerivAt
    have he : partialY (ψ s) (w.1 + c, w.2) = partialY (ψ s) w := by
      rw [hY, hY, hper]
    rw [he] at h1
    simpa only [sub_self] using h1.fun_sub h2
  -- the difference is constant ...
  set D : Plane → ℝ := fun w => ψ s (w.1 + c, w.2) - ψ s w with hD
  have hconst : ∀ w : Plane, D w = D (0, 0) := by
    intro w
    have hq' : D (w.1, w.2) = D (0, w.2) :=
      is_const_of_deriv_eq_zero (f := fun t => ψ s (t + c, w.2) - ψ s (t, w.2))
        (fun t => (hq (t, w.2)).differentiableAt) (fun t => (hq (t, w.2)).deriv) w.1 0
    have hη' : D (0, w.2) = D (0, 0) :=
      is_const_of_deriv_eq_zero (f := fun t => ψ s ((0 : ℝ) + c, t) - ψ s (0, t))
        (fun t => (hη (0, t)).differentiableAt) (fun t => (hη (0, t)).deriv) w.2 0
    exact hq'.trans hη'
  -- ... and decays as `|η| → ∞`
  have hshift : Tendsto (fun w : Plane => ((w.1 + c, w.2) : Plane))
      (comap (fun w : Plane => |w.2|) atTop) (comap (fun w : Plane => |w.2|) atTop) :=
    tendsto_comap_iff.mpr tendsto_comap
  have hlim : Tendsto D (comap (fun w : Plane => |w.2|) atTop) (𝓝 0) := by
    have h3 := ((h.stream_decay s hs).comp hshift).sub (h.stream_decay s hs)
    rw [sub_zero] at h3
    exact h3
  have hK : D (0, 0) = 0 := by
    have := neBot_comap_abs_snd
    have h2 : Tendsto D (comap (fun w : Plane => |w.2|) atTop) (𝓝 (D (0, 0))) := by
      rw [show D = fun _ => D (0, 0) from funext hconst]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h2 hlim
  have := hconst z
  rw [hK] at this
  have hz : D z = ψ s (z.1 + c, z.2) - ψ s z := rfl
  linarith

/-- **`b_raw` is `c`-periodic in `ξ`** at every age `s > 0` (line 2051 and the decaying stream;
`eq:m3-ring-lift`). -/
theorem rawProfile_periodic {ν c ε : ℝ} (T : TrainSol ν c) {s : ℝ} (hs : 0 < s) (ξ η : ℝ) :
    rawProfile ε T.v T.ψ (s, (ξ + c, η)) = rawProfile ε T.v T.ψ (s, (ξ, η)) := by
  have hT := T.isTrain
  have hv : T.v s (ξ + c, η) = T.v s (ξ, η) := hT.periodic_v s hs.le (ξ, η)
  have hψ : ∀ t, 0 ≤ t → ∀ ζ : ℝ, T.ψ t (ξ + c, ζ) = T.ψ t (ξ, ζ) := fun t ht ζ =>
    stream_periodic_of_isTrain hT ht (ξ, ζ)
  have hdη : deriv (fun t => T.ψ s (ξ + c, t)) η = deriv (fun t => T.ψ s (ξ, t)) η := by
    rw [show (fun t => T.ψ s (ξ + c, t)) = fun t => T.ψ s (ξ, t) from
      funext fun t => hψ s hs.le t]
  have hds : deriv (fun t => T.ψ t (ξ + c, η)) s = deriv (fun t => T.ψ t (ξ, η)) s := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact hψ t (le_of_lt ht) η
  have hH : raisedStream T.ψ s (ξ + c) η = raisedStream T.ψ s ξ η := by
    unfold raisedStream
    rw [hψ s hs.le η, hdη, hds]
  simp only [rawProfile, hv, hH]

/-- **`U_raw` is a background piece** (`eq:m3-ring-lift`, lines 2070–2098; `background:eq:2.15`):
a bounded solenoidal field that agrees off the axis with the ring lift of `b_raw` (radius
`R = ε⁻¹`) is `P`-periodic with `P = 2εc` and axisymmetric without swirl at every phase. -/
theorem isBackgroundPiece_raw {ν c ε : ℝ} (hε : ε ≠ 0) (T : TrainSol ν c)
    {U : ℝ → SpatialField}
    (hlift : ∀ τ y, y ∉ axis → U τ y = Nv ε⁻¹ (rawProfile ε T.v T.ψ) τ y)
    (hb : IsBoundedBackground U) (hsol : ∀ τ, IsSolenoidal (U τ)) :
    IsBackgroundPiece (2 * ε * c) U :=
  isBackgroundPiece_of_lift (inv_ne_zero hε) (by rw [div_inv_eq_mul]; ring)
    (fun s hs ξ η => rawProfile_periodic T hs ξ η) hlift hb hsol

end UnforcedLeray.Cons.C03
