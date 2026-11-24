import UnforcedLeray.Units.B0447.Slice
import UnforcedLeray.Lib.PhaseTrace.Comoving
import UnforcedLeray.Lib.PhaseSpace.Charts

/-!
# B0447, part 2: the comoving chart pulls back `T₀` and `νΔ` (`eq:free-stress-20`)

Blueprint unit B0447, `paper/main.tex` lines 7635–7650. For an observation point `(τ₀, y₀)`,

  `W(t, z) = w(τ₀ + t, e^{-t/2}(y₀ + √ν z))`      (tex 7640, `PhaseSpace.chartPullback`)

and, in distributions (tex 7643–7649),

  `W_t = (T₀w) ∘ chart`,   `Δ_z W = ν e^{-t} (Δ_y w) ∘ chart`.

In the model of decision D2, `w ∈ Y_q` is a class of maps `ℝ/Pℤ → L^q(ℝ³)`; `νΔw = a` and
`T₀w = b` are the free-graph identities `HasPhaseOp (nuLapT ν) w a`, `HasPhaseOp driftT w b`
(unit B0411). The chart factors as the comoving dilation `V(t) = w(τ₀ + t, e^{-t/2} ·)`
(`PhaseTrace.comoving`) followed by the fixed affine map `z ↦ √ν z + y₀` (`affL`), so:

* `chartLp f ν τ₀ y₀ t = affL ν y₀ (comoving f τ₀ t) ∈ L^q(ℝ³)` is `W(t)` as an `L^q` class
  (`coeFn_chartLp`: it is a.e. the pointwise `chartPullback f ν τ₀ y₀ t`);
* `chart_hasWeakDerivTime` (first line of (20)): `W_t = (T₀w) ∘ chart` as a weak time
  derivative of `L^q`-valued maps on every bounded interval, from
  `PhaseTrace.comoving_hasWeakDerivTime` and boundedness of `affL`;
* `chart_laplacian` (second line of (20)): for a.e. `t ∈ ℝ`,
  `Δ_z W(t) = e^{-t} (a ∘ chart)(t)` in `D'(ℝ³)`, with `a = νΔw`; i.e.
  `Δ_z W = ν e^{-t} (Δ_y w) ∘ chart`. It follows from the slice identity
  (`slice_identity_ae_all`) by the affine change of variables `y = c z + d`,
  `c = e^{-t/2}√ν`, `d = e^{-t/2} y₀` (`integral_comp_affine`, `laplacian_comp_affine`), with
  `c² / ν = e^{-t}`.

Both identities hold for every `t ∈ ℝ`, in particular on the strip `-1/2 < t < 1/2`.

Status: infrastructure for `Units/B0447.lean`. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0447

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.BochnerTime

/-! ### Calculus under affine maps of `ℝ³` -/

theorem fderiv_comp_affine {g : Space → ℝ} (hg : Differentiable ℝ g) (s : ℝ) (v y u : Space) :
    fderiv ℝ (fun y => g (s • y + v)) y u = s * fderiv ℝ g (s • y + v) u := by
  have hA : HasFDerivAt (fun y : Space => s • y + v) (s • ContinuousLinearMap.id ℝ Space) y :=
    ((hasFDerivAt_id y).const_smul s).add_const v
  have h : HasFDerivAt (fun y => g (s • y + v))
      ((fderiv ℝ g (s • y + v)).comp (s • ContinuousLinearMap.id ℝ Space)) y :=
    (hg (s • y + v)).hasFDerivAt.comp y hA
  rw [h.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

/-- `Δ(ψ(s · + v)) = s² (Δψ)(s · + v)`. -/
theorem laplacian_comp_affine {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (s : ℝ) (v y : Space) :
    Heat.laplacian (fun y => ψ (s • y + v)) y = s ^ 2 * Heat.laplacian ψ (s • y + v) := by
  have hd1 : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have h1 : ∀ i : Fin 3, (fun y => fderiv ℝ (fun y => ψ (s • y + v)) y (coordinateVector i)) =
      fun y => s * fderiv ℝ ψ (s • y + v) (coordinateVector i) := by
    intro i
    funext y
    exact fderiv_comp_affine hd1 s v y _
  simp only [Heat.laplacian, h1]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hd : Differentiable ℝ (fun x => fderiv ℝ ψ x (coordinateVector i)) :=
    (contDiff_fderiv_apply hψ _).differentiable (by simp)
  have hH : DifferentiableAt ℝ (fun y => fderiv ℝ ψ (s • y + v) (coordinateVector i)) y :=
    (hd.comp ((differentiable_id.const_smul s).add_const v)) y
  rw [fderiv_const_mul hH, ContinuousLinearMap.smul_apply, smul_eq_mul,
    fderiv_comp_affine hd s v y]
  ring

/-- Change of variables `∫ k(c z + d) dz = |c|^{-3} ∫ k(y) dy` on `ℝ³`. -/
theorem integral_comp_affine (k : Space → ℂ) (c : ℝ) (d : Space) :
    ∫ z, k (c • z + d) = |(c ^ 3)⁻¹| • ∫ y, k y := by
  have h1 := Measure.integral_comp_smul (volume : Measure Space) (fun x => k (x + d)) c
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  rw [hdim] at h1
  rw [h1, integral_add_right_eq_self (fun x => k x) d]

/-! ### The affine pullback on `L^q(ℝ³)` -/

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- Translation `g ↦ g(· + y₀)` on `L^q(ℝ³; ℂ³)`. -/
def transL (y₀ : Space) :
    Lp CVec3 q (volume : Measure Space) →L[ℝ] Lp CVec3 q (volume : Measure Space) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun z : Space => z + y₀)
    (measurePreserving_add_right volume y₀)).toContinuousLinearMap

theorem coeFn_transL (y₀ : Space) (g : Lp CVec3 q (volume : Measure Space)) :
    (transL y₀ g : Space → CVec3) =ᵐ[volume] fun z => (g : Space → CVec3) (z + y₀) :=
  Lp.coeFn_compMeasurePreserving g _

/-- The affine pullback `g ↦ g(√ν · + y₀)` on `L^q(ℝ³; ℂ³)` (for `ν > 0`). -/
def affL (ν : ℝ) (y₀ : Space) :
    Lp CVec3 q (volume : Measure Space) →L[ℝ] Lp CVec3 q (volume : Measure Space) :=
  (dil CVec3 q (-Real.log ν)).comp (transL y₀)

theorem dilScale_neg_log {ν : ℝ} (hν : 0 < ν) : dilScale (-Real.log ν) = Real.sqrt ν := by
  rw [dilScale, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hν]
  congr 1
  ring

theorem coeFn_affL {ν : ℝ} (hν : 0 < ν) (y₀ : Space) (g : Lp CVec3 q (volume : Measure Space)) :
    (affL ν y₀ g : Space → CVec3) =ᵐ[volume]
      fun z => (g : Space → CVec3) (Real.sqrt ν • z + y₀) := by
  have h1 := coeFn_dil (E := CVec3) (q := q) (-Real.log ν) (transL y₀ g)
  have h2 := (qmp_dilScale (-Real.log ν)).ae_eq_comp (coeFn_transL (q := q) y₀ g)
  rw [dilScale_neg_log hν] at h1 h2
  exact h1.trans h2

theorem qmp_affine {ν : ℝ} (hν : 0 < ν) (y₀ : Space) :
    Measure.QuasiMeasurePreserving (fun z : Space => Real.sqrt ν • z + y₀) volume volume := by
  have h := (measurePreserving_add_right (volume : Measure Space) y₀).quasiMeasurePreserving.comp
    (qmp_dilScale (-Real.log ν))
  rw [dilScale_neg_log hν] at h
  exact h

/-! ### The chart pullback as an `L^q`-valued map of time -/

variable {P : ℝ} [Fact (0 < P)]

/-- `W(t) = w(τ₀ + t, e^{-t/2}(y₀ + √ν ·)) ∈ L^q(ℝ³; ℂ³)` (tex 7640), as an `L^q` class. -/
def chartLp (f : Yq P q) (ν τ₀ : ℝ) (y₀ : Space) (t : ℝ) : Lp CVec3 q (volume : Measure Space) :=
  affL ν y₀ (comoving f τ₀ t)

/-- `chartLp` is a.e. the pointwise chart pullback of `Lib/PhaseSpace/Charts.lean`. -/
theorem coeFn_chartLp {ν : ℝ} (hν : 0 < ν) (f : Yq P q) (τ₀ : ℝ) (y₀ : Space) (t : ℝ) :
    (chartLp f ν τ₀ y₀ t : Space → CVec3) =ᵐ[volume] chartPullback f ν τ₀ y₀ t := by
  have h1 := coeFn_affL (q := q) hν y₀ (comoving f τ₀ t)
  have h2 := (qmp_affine hν y₀).ae_eq_comp
    (coeFn_dil (E := CVec3) (q := q) t (f ((τ₀ + t : ℝ) : AddCircle P)))
  refine h1.trans (h2.trans (Eventually.of_forall fun z => ?_))
  simp only [Function.comp_apply, chartPullback, comovingChart, dilScale]
  rw [add_comm (Real.sqrt ν • z) y₀]

/-- **First line of (20)** (tex 7644): `W_t = (T₀w) ∘ chart`. If `T₀w = b` in distributions
on `Y_q` (`1 ≤ q < ∞`), the `L^q(ℝ³)`-valued chart pullback of `w` has weak time derivative
the chart pullback of `b` on every bounded interval `(a, a')`. -/
theorem chart_hasWeakDerivTime (hq : q ≠ ⊤) {w b : Yq P q} (h : HasPhaseOp driftT w b)
    (ν τ₀ : ℝ) (y₀ : Space) (a a' : ℝ) :
    HasWeakDerivTime a a' (chartLp w ν τ₀ y₀) (chartLp b ν τ₀ y₀) :=
  (comoving_hasWeakDerivTime hq h τ₀ a a').map (affL ν y₀)

/-- The spatial step of the second line of (20): at a phase `τ₀ + t` where
`νΔ w(τ₀ + t) = a(τ₀ + t)` in `D'(ℝ³)`, the chart slice satisfies
`Δ_z W(t) = e^{-t} a(τ₀ + t, e^{-t/2}(y₀ + √ν ·))` in `D'(ℝ³)`. -/
theorem chart_laplacian_of_slice {ν : ℝ} (hν : 0 < ν) {w a : Yq P q} (τ₀ : ℝ) (y₀ : Space)
    (t : ℝ)
    (hs : ∀ ψ : Space → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ e : CVec3,
      (ν : ℂ) * ∫ y, Heat.laplacian ψ y •
          dotL e ((w ((τ₀ + t : ℝ) : AddCircle P) : Space → CVec3) y) =
        ∫ y, ψ y • dotL e ((a ((τ₀ + t : ℝ) : AddCircle P) : Space → CVec3) y))
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (e : CVec3) :
    ∫ z, Heat.laplacian ψ z • dotL e (chartPullback w ν τ₀ y₀ t z) =
      (Real.exp (-t) : ℂ) * ∫ z, ψ z • dotL e (chartPullback a ν τ₀ y₀ t z) := by
  set c : ℝ := Real.exp (-t / 2) * Real.sqrt ν with hc
  set d : Space := Real.exp (-t / 2) • y₀ with hd
  have hc0 : 0 < c := by positivity
  have hW : ∀ z, chartPullback w ν τ₀ y₀ t z =
      (w ((τ₀ + t : ℝ) : AddCircle P) : Space → CVec3) (c • z + d) := fun z => by
    simp only [chartPullback]
    rw [chart_snd]
    rfl
  have hA : ∀ z, chartPullback a ν τ₀ y₀ t z =
      (a ((τ₀ + t : ℝ) : AddCircle P) : Space → CVec3) (c • z + d) := fun z => by
    simp only [chartPullback]
    rw [chart_snd]
    rfl
  have hinv : ∀ z : Space, c⁻¹ • (c • z + d) + -(c⁻¹ • d) = z := fun z => by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul, add_neg_cancel_right]
  set ψt : Space → ℝ := fun y => ψ (c⁻¹ • y + -(c⁻¹ • d)) with hψt
  have hψt_smooth : ContDiff ℝ ∞ ψt :=
    hψ.comp ((contDiff_id.const_smul c⁻¹).add contDiff_const)
  have hψt_c : HasCompactSupport ψt := by
    have H := hψc.comp_homeomorph ((Homeomorph.smulOfNeZero c⁻¹ (inv_ne_zero hc0.ne')).trans
      (Homeomorph.addRight (-(c⁻¹ • d))))
    convert H using 1
    funext y
    rfl
  have hlapt : ∀ y, Heat.laplacian ψt y =
      c⁻¹ ^ 2 * Heat.laplacian ψ (c⁻¹ • y + -(c⁻¹ • d)) :=
    fun y => laplacian_comp_affine hψ _ _ y
  have key := hs ψt hψt_smooth hψt_c e
  set g := (w ((τ₀ + t : ℝ) : AddCircle P) : Space → CVec3) with hg
  set h := (a ((τ₀ + t : ℝ) : AddCircle P) : Space → CVec3) with hh
  have hL : ∫ z, Heat.laplacian ψ z • dotL e (g (c • z + d)) =
      |(c ^ 3)⁻¹| • ((c ^ 2) • ∫ y, Heat.laplacian ψt y • dotL e (g y)) := by
    have h0 := integral_comp_affine
      (fun y => Heat.laplacian ψ (c⁻¹ • y + -(c⁻¹ • d)) • dotL e (g y)) c d
    simp only [hinv] at h0
    rw [h0]
    congr 1
    rw [← integral_smul]
    have hsc : ∀ (r : ℝ) (X : ℂ), r • X = c ^ 2 • ((c⁻¹ ^ 2 * r) • X) := fun r X => by
      rw [smul_smul, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hc0.ne', one_pow, one_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [hlapt]
    exact hsc _ _
  have hR : ∫ z, ψ z • dotL e (h (c • z + d)) = |(c ^ 3)⁻¹| • ∫ y, ψt y • dotL e (h y) := by
    have h0 := integral_comp_affine (fun y => ψt y • dotL e (h y)) c d
    simp only [hψt, hinv] at h0
    exact h0
  simp_rw [hW, hA]
  rw [hL, hR, ← key]
  have hc2 : c ^ 2 = Real.exp (-t) * ν := by
    rw [hc, mul_pow, Real.sq_sqrt (le_of_lt hν), ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hc2' : ((c ^ 2 : ℝ) : ℂ) = (Real.exp (-t) : ℂ) * (ν : ℂ) := by
    rw [hc2]
    push_cast
    ring
  rw [Complex.real_smul, Complex.real_smul, Complex.real_smul, hc2']
  ring

/-- **Second line of (20)** (tex 7645): `Δ_z W = ν e^{-t} (Δ_y w) ∘ chart`. If `νΔw = a` in
distributions on `Y_q`, `1 < q`, then for a.e. `t ∈ ℝ`,
`∫ Δψ(z) e · W(t, z) dz = e^{-t} ∫ ψ(z) e · a(τ₀ + t, e^{-t/2}(y₀ + √ν z)) dz` for every smooth
compactly supported `ψ : ℝ³ → ℝ` and `e ∈ ℂ³`, i.e. `Δ_z W(t) = e^{-t} (a ∘ chart)(t)` in
`D'(ℝ³)`. -/
theorem chart_laplacian {ν : ℝ} (hν : 0 < ν) (hq1 : 1 < q) {w a : Yq P q}
    (h : HasPhaseOp (nuLapT ν) w a) (τ₀ : ℝ) (y₀ : Space) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ ψ : Space → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∀ e : CVec3,
        ∫ z, Heat.laplacian ψ z • dotL e (chartPullback w ν τ₀ y₀ t z) =
          (Real.exp (-t) : ℂ) * ∫ z, ψ z • dotL e (chartPullback a ν τ₀ y₀ t z) := by
  have h1 := slice_identity_ae_all hq1 h
  have h2 := (measurePreserving_add_left (volume : Measure ℝ) τ₀).quasiMeasurePreserving.ae h1
  filter_upwards [h2] with t ht
  intro ψ hψ hψc e
  exact chart_laplacian_of_slice hν τ₀ y₀ t (by simpa using ht) hψ hψc e

end UnforcedLeray.B0447
