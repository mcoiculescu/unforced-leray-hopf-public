import UnforcedLeray.Units.B0284
import UnforcedLeray.Lib.Sobolev.Cylinder
import UnforcedLeray.Lib.Sobolev.WeakDeriv

/-!
# B0289, definitions: the causal Duhamel integral, the two imported estimates, the cutoff

Unit B0289 of `paper/main.tex` (free graph bound, tex lines 4771–4775; its proof is the
flat-map paragraph of §`sec:free-flat-body-graph`, tex lines 3772–3819). Blueprint unit B0289


* `duhamel ν h s = ∫_{(0,s)} e^{ν(s-t)Δ} h(t) dt`, the causal Duhamel integral on the cylinder
  with the heat semigroup `B0284.heat`. The flat inverse of B0284 is `duhamel ν` applied to
  `t ↦ 𝕡₀(F(t)/t)` (`flatInverse_eq_duhamel`, by definition).
* `stNorm c p h = ‖h‖_{L^p(ds; L^p(dq/c dη))}` over ages `s > 0`, the unweighted space-time
  norm of the heat estimate.
* `CylHeatMaxReg ν c p C`: the parabolic maximal-regularity estimate eq:free-stress-11 on the
  spatial cylinder (tex lines 3801–3810 and 7447–7477; blueprint INF02 targets T8/T9, built
  by another wave in `Lib/Parabolic`), in its Duhamel form.
* `CylGradInterp c p C`: the spatial gradient interpolation on the cylinder
  (tex lines 3811–3815, "spatial heat interpolation"; blueprint INF01 §4.4 / INF11 S9b).
* `cutoff`: a fixed smooth age cutoff, `1` on `[1,2]`, `0` off `(1/2, 5/2)` (tex lines
  3790–3792), and its scaled copies `chi a t = cutoff (t/a)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Real
open scoped NNReal ENNReal ContDiff

namespace UnforcedLeray.B0289

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0284

/-! ## The causal Duhamel integral and the space-time norm -/

/-- The causal Duhamel integral `∫_{(0,s)} e^{ν(s-t)Δ} h(t) dt` on the cylinder, evaluated
pointwise (tex lines 3784–3792; the flat inverse of tex line 5249 is the case
`h(t) = 𝕡₀(F(t)/t)`). Where the age integrand is not integrable, Lean's value is `0`. -/
def duhamel (ν : ℝ) (h : ℝ → Plane → Plane) (s : ℝ) : Plane → Plane :=
  fun z => ∫ t in Ioo 0 s, heat (ν * (s - t)) (h t) z

/-- The flat inverse `T̄` of B0284 is the Duhamel integral of `t ↦ 𝕡₀(F(t)/t)`. -/
theorem flatInverse_eq_duhamel (ν c : ℝ) (F : ℝ → Plane → Plane) :
    flatInverse ν c F = duhamel ν (fun t => flatLeray c (t⁻¹ • F t)) := rfl

/-- The unweighted space-time norm `‖h‖_{L^p((0,∞), ds; L^p(dq/c dη))}` of the heat estimate,
as an iterated `[0,∞]`-valued norm (tex lines 3797–3801). -/
def stNorm (c p : ℝ) (h : ℝ → Plane → Plane) : ℝ≥0∞ :=
  eLpNorm (fun s => eLpNorm (h s) (ENNReal.ofReal p) (cellMeasure c)) (ENNReal.ofReal p)
    (volume.restrict (Ioi 0))

/-! ## The two imported estimates -/

/-- **Parabolic maximal regularity on the cylinder** (named hypothesis; eq:free-stress-11,
tex lines 7447–7477, used on the cylinder at tex lines 3797–3810; blueprint INF02 targets T8
and T9, Fabes–Rivière for the causal kernel `1_{θ>0}∂_{ij}G_θ`, transferred to `T_c × ℝ` by
periodic extension over `N` cells, BP-F).

For every jointly measurable, `q`-periodic source `h` with compact age support in `(0,∞)` and
finite space-time norm, the causal Duhamel integral `u = duhamel ν h` has periodic weak
second spatial derivatives `D2 i j = ∂_i∂_j u` on the cylinder for almost every age, jointly
measurable in `(s, z)`, with `‖ν ∂_i∂_j u‖_{L^p(ds; L^p)} ≤ C ‖h‖_{L^p(ds; L^p)}`.

This is the Duhamel (mild) form of T8/T9: T8 identifies the distributional solution of
`(∂_s - νΔ)u = h` with zero initial value with this integral. For `1 < p < ∞` it holds with a
constant `C = C_p` independent of `ν` and `c` (tex line 3806). Not proved here. -/
def CylHeatMaxReg (ν c p : ℝ) (C : ℝ≥0) : Prop :=
  ∀ h : ℝ → Plane → Plane, StronglyMeasurable (Function.uncurry h) →
    (∀ t, IsQPeriodic c (h t)) →
    (∃ T₀ T₁ : ℝ, 0 < T₀ ∧ ∀ t, t ∉ Ioo T₀ T₁ → h t = 0) →
    stNorm c p h < ⊤ →
    ∃ D2 : Fin 2 → Fin 2 → ℝ → Plane → Plane,
      (∀ i j, StronglyMeasurable (Function.uncurry (D2 i j))) ∧
      (∀ i j s, IsQPeriodic c (D2 i j s)) ∧
      (∀ᵐ s ∂(volume.restrict (Ioi 0)), ∀ i j,
        Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir i, Sob.cylDir j] (duhamel ν h s)
          (D2 i j s)) ∧
      ∀ i j, stNorm c p (fun s => ν • D2 i j s) ≤ C * stNorm c p h

/-- **Gradient interpolation on the cylinder** (named hypothesis; tex lines 3811–3815,
"spatial heat interpolation", `‖√s∇b‖ ≤ C‖b‖^{1/2}‖sΔb‖^{1/2}`; blueprint INF01 §4.4 and
INF11 S9b, heat-semigroup proof without Calderón–Zygmund).

A periodic field `f ∈ L^p` whose weak second derivatives `D2 i j = ∂_i∂_j f` are in `L^p`
has periodic weak first derivatives `D1 i = ∂_i f` with
`‖∂_i f‖_p ≤ C (‖f‖_p Σ_{k,l} ‖∂_k∂_l f‖_p)^{1/2}`. It holds for `1 ≤ p < ∞` with a constant
independent of `c`. Not proved here. -/
def CylGradInterp (c p : ℝ) (C : ℝ≥0) : Prop :=
  ∀ (f : Plane → Plane) (D2 : Fin 2 → Fin 2 → Plane → Plane),
    IsQPeriodic c f → (∀ i j, IsQPeriodic c (D2 i j)) →
    MemLp f (ENNReal.ofReal p) (cellMeasure c) →
    (∀ i j, MemLp (D2 i j) (ENNReal.ofReal p) (cellMeasure c)) →
    (∀ i j, Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir i, Sob.cylDir j] f (D2 i j)) →
    ∃ D1 : Fin 2 → Plane → Plane, (∀ i, IsQPeriodic c (D1 i)) ∧
      (∀ i, Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir i] f (D1 i)) ∧
      ∀ i, eLpNorm (D1 i) (ENNReal.ofReal p) (cellMeasure c) ≤
        C * (eLpNorm f (ENNReal.ofReal p) (cellMeasure c) *
          ∑ k, ∑ l, eLpNorm (D2 k l) (ENNReal.ofReal p) (cellMeasure c)) ^ (1 / 2 : ℝ)

/-! ## The age cutoff (tex lines 3790–3792) -/

/-- A fixed smooth bump on `ℝ`, centred at `3/2`, equal to `1` on `[1,2]` and supported in
`(1/2, 5/2)`. -/
def bump0 : ContDiffBump (3 / 2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The fixed age cutoff: `1` on `[1,2]`, `0` off `(1/2, 5/2)`, smooth, with values in
`[0,1]`. -/
def cutoff (x : ℝ) : ℝ := bump0 x

/-- Its derivative. -/
def cutoffD : ℝ → ℝ := deriv cutoff

theorem contDiff_cutoff : ContDiff ℝ 1 cutoff := bump0.contDiff

theorem hasDerivAt_cutoff (x : ℝ) : HasDerivAt cutoff (cutoffD x) x :=
  (contDiff_cutoff.differentiable one_ne_zero x).hasDerivAt

theorem continuous_cutoff : Continuous cutoff := contDiff_cutoff.continuous

theorem continuous_cutoffD : Continuous cutoffD := contDiff_cutoff.continuous_deriv le_rfl

theorem cutoff_nonneg (x : ℝ) : 0 ≤ cutoff x := bump0.nonneg

theorem cutoff_le_one (x : ℝ) : cutoff x ≤ 1 := bump0.le_one

theorem cutoff_eq_one {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) : cutoff x = 1 := by
  refine bump0.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  have : bump0.rIn = 1 / 2 := rfl
  rw [this]
  constructor <;> linarith

theorem cutoff_eq_zero {x : ℝ} (h : x ∉ Ioo (1 / 2) (5 / 2)) : cutoff x = 0 := by
  refine bump0.zero_of_le_dist ?_
  have : bump0.rOut = 1 := rfl
  rw [this, Real.dist_eq]
  simp only [mem_Ioo, not_and_or, not_lt] at h
  rcases h with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem cutoffD_eq_zero {x : ℝ} (h : x ∉ Icc (1 / 2) (5 / 2)) : cutoffD x = 0 := by
  have hts : tsupport cutoff = Icc (1 / 2) (5 / 2) := by
    have h1 : tsupport cutoff = Metric.closedBall (3 / 2 : ℝ) 1 := bump0.tsupport_eq
    rw [h1, Real.closedBall_eq_Icc]
    norm_num
  have hx : x ∉ Function.support (deriv cutoff) := fun hx =>
    h (hts ▸ support_deriv_subset hx)
  simpa [cutoffD] using hx

theorem exists_cutoffD_bound : ∃ M : ℝ, ∀ x, |cutoffD x| ≤ M := by
  have hc : HasCompactSupport cutoff := bump0.hasCompactSupport
  obtain ⟨M, hM⟩ := continuous_cutoffD.bounded_above_of_compact_support hc.deriv
  exact ⟨M, fun x => by simpa [Real.norm_eq_abs] using hM x⟩

/-- A bound for `|cutoff'|` (a fixed number). -/
def cutoffBound : ℝ≥0 := (Classical.choose exists_cutoffD_bound).toNNReal

theorem abs_cutoffD_le (x : ℝ) : |cutoffD x| ≤ cutoffBound :=
  (Classical.choose_spec exists_cutoffD_bound x).trans (Real.le_coe_toNNReal _)

/-- The scaled cutoff `χ_a(t) = cutoff(t/a)`. -/
def chi (a t : ℝ) : ℝ := cutoff (t / a)

/-- Its derivative `χ_a'(t) = cutoff'(t/a)/a`. -/
def chiD (a t : ℝ) : ℝ := cutoffD (t / a) / a

theorem hasDerivAt_chi (a t : ℝ) : HasDerivAt (chi a) (chiD a t) t := by
  have h := (hasDerivAt_cutoff (t / a)).comp t ((hasDerivAt_id t).div_const a)
  have e2 : chiD a t = cutoffD (t / a) * (1 / a) := by
    simp only [chiD]; ring
  rw [e2]
  exact h

theorem continuous_chi (a : ℝ) : Continuous (chi a) :=
  continuous_cutoff.comp (continuous_id.div_const a)

theorem continuous_chiD (a : ℝ) : Continuous (chiD a) :=
  (continuous_cutoffD.comp (continuous_id.div_const a)).div_const a

end UnforcedLeray.B0289
