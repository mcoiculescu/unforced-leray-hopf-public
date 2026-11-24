import UnforcedLeray.Short.PartI.Sub.T02
import UnforcedLeray.Short.PartI.StatementsTrain
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part I, task `PartI:T02/2`: the decaying pressure gauge (conditional)

Source of record: `the November 2 reference manuscript`, line 447 ("The decaying
pressure gauge is used here") and line 277 (the bounded periodic pressure choice).

The target is `LerayPressureGauge` (`Short/PartI/Sub/T02.lean`): a classical solution `(v, p)` on
`[0,T]` with all spatial derivatives of `v` bounded and `v → 0` as `|η| → ∞` has a classical
pressure `p' = p - a(s)` with `p' → 0` as `|η| → ∞`, for every `s ∈ [0,T]`.  Note that
`IsClassicalOn` carries no bound on `p`, and `HasBoundedDerivsOn` bounds no time derivative of `v`;
the boundedness of `p(s)` is therefore itself a consequence (`PressureBounded`), proved by
integrating the momentum equation in time (the exponentially growing modes `A e^{λη}` of the
harmonic part of `p` are killed because `∫ₜ^s ∇p dσ = -(v(s) - v(t)) - ∫ₜ^s (v·∇v - νΔv) dσ` is
bounded).

With `p̄(s,η) = c⁻¹ ∫_{-c/2}^{c/2} p(s,q,η) dq` and `a(s) := p̄(s,0) + \overline{v₂²}(s,0)`:

* `PressureMeanIdentity`: `p̄ + \overline{v₂²}` does not depend on `η` (average the `η`-momentum
  equation; `\bar v₂ = 0` by divergence, periodicity and decay), so `p̄ - a(s) = -\overline{v₂²} → 0`;
* `PressureGaugeSmooth`: `a` is `C^∞` on `[0,T]` (differentiation under the integral over the
  compact `q`-interval), so `p' = p - a(s)` is again classical (`∇p' = ∇p`);
* the oscillating part `p - p̄` tends to `0`: `PressurePoisson` (`Δp = -tr((∇v)²)`),
  `FderivTendstoZero` (`∇v → 0`, hence `Δp → 0`), `PressureBounded` and `OscillationDecay`
  (a bounded periodic function with `Δu → 0` has `u - ū → 0`).

`lerayPressureGauge_of` derives `LerayPressureGauge` from the six `Prop`s.  The unconditional
statement is task `PartI:T02/2` (`Short/PartI/Sub/T02/LerayPressureGauge.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- The standing hypotheses of `LerayPressureGauge`. -/
structure GaugeHyp (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ) : Prop where
  nu_pos : 0 < ν
  one_le : 1 ≤ c
  T_pos : 0 < T
  classical : IsClassicalOn ν c T v p
  bounded : HasBoundedDerivsOn T v
  decay : VelocityDecayOn T v

/-! ### The six leaf statements -/

/-- **Poisson equation for the pressure** (source line 447; take the divergence of the momentum
equation, `div v = 0`): `Δp = -tr((∇v)²) = -(∂_q v₁)² - 2 ∂_η v₁ ∂_q v₂ - (∂_η v₂)²` for every
`s ∈ [0,T]` (for `0 < s < T` by differentiating the momentum identity, at `s = 0` by continuity of
the spatial second derivatives). -/
def PressurePoisson : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), GaugeHyp ν c T v p →
    ∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane,
      Train.lapS (p s) z =
        -(Cyl.partialQ (fun w => v s w 0) z ^ 2 +
          2 * Cyl.partialEta (fun w => v s w 0) z * Cyl.partialQ (fun w => v s w 1) z +
          Cyl.partialEta (fun w => v s w 1) z ^ 2)

/-- **Interpolation** (Landau-Kolmogorov type): a `C²` function with bounded Hessian that tends to
`0` as `|η| → ∞` has gradient tending to `0` as `|η| → ∞` (Taylor along a unit vector `e` with step
`r`: `|∂_e g(z)| ≤ 2 sup_{|y.2 - z.2| ≤ r}|g|/r + M r / 2`, then `r = √(sup|g|/M)`). -/
def FderivTendstoZero : Prop :=
  ∀ g : Plane → ℝ, ContDiff ℝ 2 g → (∃ M : ℝ, ∀ z, ‖iteratedFDeriv ℝ 2 g z‖ ≤ M) →
    Tendsto g (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) →
    Tendsto (fun z => ‖fderiv ℝ g z‖) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)

/-- **The pressure is bounded** (source line 277, "the bounded periodic pressure choice"; here a
consequence of the hypotheses): for every `s ∈ [0,T]` there is `M` with `|p(s,z)| ≤ M`.  Route:
mode by mode in `q` (Fourier coefficients `p_k(s,η)`, `k ≠ 0`, solve
`p_k'' - λ_k² p_k = S_k` with `S_k` bounded, `λ_k = 2π|k|/c`, so
`p_k = (decaying kernel) * S_k + A_k(s) e^{λ_k η} + B_k(s) e^{-λ_k η}`); integrating the momentum
equation over `[t, s]` shows `∫_t^s A_k = ∫_t^s B_k = 0` for all `t < s`, hence `A_k = B_k = 0`,
and summability in `k` comes from the smoothness of `S` in `q`; the mean `p̄` is bounded by
`PressureMeanIdentity`. -/
def PressureBounded : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), GaugeHyp ν c T v p →
    ∀ s ∈ Icc (0 : ℝ) T, ∃ M : ℝ, ∀ z : Plane, |p s z| ≤ M

/-- **The oscillating part of a bounded periodic function with decaying Laplacian decays**: if
`u` is `C²`, `c`-periodic in `q`, bounded, and `Δu → 0` as `|η| → ∞`, then `u - ū → 0` as
`|η| → ∞`, with `ū(η)` the `q`-average (Fourier modes `k ≠ 0` in `q` on a cylinder: for the
zero-mean part `ũ`, `r(η) = ‖ũ(·,η)‖_{L²(q)}` satisfies `r'' ≥ (2π/c)² r - ‖Δũ(·,η)‖_{L²(q)}`, and
a sub-mean-value estimate converts the `L²`-in-`q` decay to uniform decay). -/
def OscillationDecay : Prop :=
  ∀ (c : ℝ) (u : Plane → ℝ), 0 < c → ContDiff ℝ 2 u → Cyl.IsPeriodic c u →
    (∃ M : ℝ, ∀ z, |u z| ≤ M) →
    Tendsto (Train.lapS u) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) →
    Tendsto (fun z => u z - hmean c u z.2) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)

/-- **The `q`-mean of `p + v₂²` is constant in `η`** (source line 447): average the `η`-component
of the momentum equation, using `div v = 0` (`v·∇v₂ = ∂_q(v₁v₂) + ∂_η(v₂²)`), periodicity, and
`\bar v₂ = 0` (`∂_η \bar v₂ = -\overline{∂_q v₁} = 0` and `v → 0`). -/
def PressureMeanIdentity : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), GaugeHyp ν c T v p →
    ∀ s ∈ Icc (0 : ℝ) T, ∀ η : ℝ,
      hmean c (p s) η + hmean c (fun z => v s z 1 ^ 2) η =
        hmean c (p s) 0 + hmean c (fun z => v s z 1 ^ 2) 0

/-- **Smoothness of the gauge constant**: `s ↦ p̄(s,0) + \overline{v₂²}(s,0)` is `C^∞` on `[0,T]`
(differentiation under the integral over the compact interval `(-c/2, c/2]`, from the joint
smoothness of `p` and `v` on `[0,T] × ℝ²`). -/
def PressureGaugeSmooth : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), GaugeHyp ν c T v p →
    ContDiffOn ℝ ∞
      (fun s => hmean c (p s) 0 + hmean c (fun z => v s z 1 ^ 2) 0) (Icc 0 T)

/-! ### Helper lemmas for the assembly -/

/-- A slice of a function that is `C^∞` on `[0,T] × ℝ²` is `C^∞`. -/
theorem gg_slice_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → Plane → E} {T s : ℝ} (hs : s ∈ Icc 0 T)
    (h : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => f x.1 x.2) (Icc 0 T ×ˢ univ)) :
    ContDiff ℝ ∞ (f s) := by
  have h1 : ContDiffOn ℝ ∞ ((fun x : ℝ × Plane => f x.1 x.2) ∘ (fun z : Plane => (s, z))) univ :=
    h.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun z _ => ⟨hs, mem_univ z⟩)
  exact contDiffOn_univ.mp h1

/-- The `q`-average of a function tending to `0` tends to `0`. -/
theorem gg_hmean_tendsto {c : ℝ} (hc : 0 < c) {f : Plane → ℝ}
    (hf : Tendsto f (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)) :
    Tendsto (fun z : Plane => hmean c f z.2) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h1 := (Metric.tendsto_nhds.mp hf) (ε / 2) (by positivity)
  rw [Filter.eventually_comap] at h1 ⊢
  filter_upwards [h1] with b hb z hz
  have hbd : ∀ q : ℝ, ‖f (q, z.2)‖ ≤ ε / 2 := fun q => by
    have := hb (q, z.2) (by simpa using hz)
    simpa [Real.dist_eq] using this.le
  have hint := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (-c / 2) (c / 2))
    (f := fun q => f (q, z.2)) (C := ε / 2) (by simp) (fun q _ => hbd q)
  have hvol : (volume : Measure ℝ).real (Ioc (-c / 2) (c / 2)) = c := by
    rw [Measure.real, Real.volume_Ioc]
    rw [ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hvol] at hint
  unfold hmean
  rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hc.le]
  calc c⁻¹ * ‖∫ q in Ioc (-c / 2) (c / 2), f (q, z.2)‖ ≤ c⁻¹ * (ε / 2 * c) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

theorem gg_two_le : (2 : WithTop ℕ∞) ≤ ∞ := by
  simp

/-- The coordinate projection of Euclidean two-space is contractive. -/
theorem gg_proj_norm_le (i : Fin 2) : ‖(EuclideanSpace.proj i : Vec →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  change ‖v i‖ ≤ 1 * ‖v‖
  simpa using (PiLp.norm_apply_le v i)

theorem gg_partialQ_le {g : Plane → ℝ} (hg : Differentiable ℝ g) (z : Plane) :
    |Cyl.partialQ g z| ≤ ‖fderiv ℝ g z‖ := by
  rw [Cyl.partialQ_eq_fderiv hg, ← Real.norm_eq_abs]
  calc ‖fderiv ℝ g z ((1 : ℝ), (0 : ℝ))‖ ≤ ‖fderiv ℝ g z‖ * ‖((1 : ℝ), (0 : ℝ))‖ :=
        (fderiv ℝ g z).le_opNorm _
    _ = ‖fderiv ℝ g z‖ := by simp

theorem gg_partialEta_le {g : Plane → ℝ} (hg : Differentiable ℝ g) (z : Plane) :
    |Cyl.partialEta g z| ≤ ‖fderiv ℝ g z‖ := by
  rw [Cyl.partialEta_eq_fderiv hg, ← Real.norm_eq_abs]
  calc ‖fderiv ℝ g z ((0 : ℝ), (1 : ℝ))‖ ≤ ‖fderiv ℝ g z‖ * ‖((0 : ℝ), (1 : ℝ))‖ :=
        (fderiv ℝ g z).le_opNorm _
    _ = ‖fderiv ℝ g z‖ := by simp

/-- Each velocity component satisfies the hypotheses of `FderivTendstoZero`. -/
theorem gg_component {ν c T : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}
    (h : GaugeHyp ν c T v p) {s : ℝ} (hs : s ∈ Icc 0 T) (i : Fin 2) :
    ContDiff ℝ ∞ (fun z => v s z i) ∧
    (∃ M : ℝ, ∀ z, ‖iteratedFDeriv ℝ 2 (fun w => v s w i) z‖ ≤ M) ∧
    Tendsto (fun z => v s z i) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := by
  have hv : ContDiff ℝ ∞ (v s) := gg_slice_contDiff hs h.classical.smooth_v
  have hg : ContDiff ℝ ∞ (fun z => v s z i) :=
    (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).contDiff.comp hv
  refine ⟨hg, ?_, ?_⟩
  · obtain ⟨M, hM⟩ := h.bounded 2
    refine ⟨M, fun z => ?_⟩
    have h1 := (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left
      (f := v s) (x := z) (N := ∞) (n := 2) (hv.contDiffAt) gg_two_le
    have h2 : ‖(EuclideanSpace.proj i : Vec →L[ℝ] ℝ)‖ * ‖iteratedFDeriv ℝ 2 (v s) z‖ ≤ M := by
      calc _ ≤ 1 * ‖iteratedFDeriv ℝ 2 (v s) z‖ :=
            mul_le_mul_of_nonneg_right (gg_proj_norm_le i) (norm_nonneg _)
        _ ≤ M := by rw [one_mul]; exact hM s hs z
    exact le_trans h1 h2
  · have := ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.tendsto 0).comp (h.decay s hs)
    simpa [Function.comp_def] using this

/-- `Δp → 0` as `|η| → ∞`, from the Poisson identity and the interpolation lemma. -/
theorem gg_lap_tendsto (h1 : PressurePoisson) (h2 : FderivTendstoZero)
    {ν c T : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}
    (h : GaugeHyp ν c T v p) {s : ℝ} (hs : s ∈ Icc 0 T) :
    Tendsto (Train.lapS (p s)) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := by
  have hgrad : ∀ i : Fin 2, Tendsto (fun z => ‖fderiv ℝ (fun w => v s w i) z‖)
      (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := fun i => by
    obtain ⟨hg, hM, hd⟩ := gg_component h hs i
    exact h2 _ (hg.of_le gg_two_le) hM hd
  have hq : ∀ i : Fin 2, Tendsto (fun z => Cyl.partialQ (fun w => v s w i) z)
      (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := fun i => by
    have hg := (gg_component h hs i).1
    exact squeeze_zero_norm (fun z => by
      simpa using gg_partialQ_le (hg.differentiable (by simp)) z) (hgrad i)
  have he : ∀ i : Fin 2, Tendsto (fun z => Cyl.partialEta (fun w => v s w i) z)
      (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := fun i => by
    have hg := (gg_component h hs i).1
    exact squeeze_zero_norm (fun z => by
      simpa using gg_partialEta_le (hg.differentiable (by simp)) z) (hgrad i)
  have hlim := (((hq 0).pow 2).add (((he 0).mul (hq 1)).const_mul 2)).add ((he 1).pow 2) |>.neg
  have hfun : Train.lapS (p s) = fun z =>
      -(Cyl.partialQ (fun w => v s w 0) z ^ 2 +
        2 * (Cyl.partialEta (fun w => v s w 0) z * Cyl.partialQ (fun w => v s w 1) z) +
        Cyl.partialEta (fun w => v s w 1) z ^ 2) := by
    funext z
    rw [h1 ν c T v p h s hs z]
    ring
  rw [hfun]
  simpa using hlim

/-- **`LerayPressureGauge` from the six steps.** -/
theorem lerayPressureGauge_of (h1 : PressurePoisson) (h2 : FderivTendstoZero)
    (h3 : PressureBounded) (h4 : OscillationDecay) (h5 : PressureMeanIdentity)
    (h6 : PressureGaugeSmooth) : LerayPressureGauge := by
  intro ν c T v p hν hc1 hT hcl hb hdec
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hG : GaugeHyp ν c T v p := ⟨hν, hc1, hT, hcl, hb, hdec⟩
  set a : ℝ → ℝ := fun s => hmean c (p s) 0 + hmean c (fun z => v s z 1 ^ 2) 0 with ha
  refine ⟨fun s z => p s z - a s, ?_, ?_⟩
  · have hsm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => p x.1 x.2 - a x.1) (Icc 0 T ×ˢ univ) := by
      refine hcl.smooth_p.sub ?_
      exact (h6 ν c T v p hG).comp contDiff_fst.contDiffOn (fun x hx => hx.1)
    refine
      { smooth_v := hcl.smooth_v
        smooth_p := hsm
        periodic_v := hcl.periodic_v
        periodic_p := fun s hs z => by simp only [hcl.periodic_p s hs z]
        solenoidal := hcl.solenoidal
        momentum := fun s hs z => ?_
        initial := hcl.initial
        finite_energy := hcl.finite_energy }
    have hgrad : Train.gradS (fun w => p s w - a s) z = Train.gradS (p s) z := by
      simp [Train.gradS, Cyl.partialQ, Cyl.partialEta]
    have hm := hcl.momentum s hs z
    simp only [Train.momentumResidual] at hm ⊢
    rw [hgrad]
    exact hm
  · intro s hs
    have hu2 : ContDiff ℝ 2 (p s) :=
      (gg_slice_contDiff hs hcl.smooth_p).of_le gg_two_le
    obtain ⟨M, hM⟩ := h3 ν c T v p hG s hs
    have hS := gg_lap_tendsto h1 h2 hG hs
    have hosc := h4 c (p s) hc hu2 (hcl.periodic_p s hs) ⟨M, hM⟩ hS
    have hv2 : Tendsto (fun z => v s z 1 ^ 2) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := by
      simpa using (gg_component hG hs 1).2.2.pow 2
    have hm := gg_hmean_tendsto hc hv2
    have key : ∀ z : Plane, p s z - a s =
        (p s z - hmean c (p s) z.2) - hmean c (fun w => v s w 1 ^ 2) z.2 := by
      intro z
      have := h5 ν c T v p hG s hs z.2
      simp only [ha]
      linarith
    show Tendsto (fun z => p s z - a s) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)
    rw [show (fun z : Plane => p s z - a s) = fun z =>
        (p s z - hmean c (p s) z.2) - hmean c (fun w => v s w 1 ^ 2) z.2 from funext key]
    simpa using hosc.sub hm

end UnforcedLeray.Short.PartI
