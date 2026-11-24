import UnforcedLeray.Units.B0447.Chart
import UnforcedLeray.Units.B0411

/-!
# Unit B0447 (`eq:free-stress-20`, `eq:free-stress-21`): unit-strip pullback identities and bound

Blueprint unit `B0447`, label `eq:free-stress-21`, `paper/main.tex` lines 7635–7661 (proof of
the space-time supremum bound in §`sec:st18-9174`); depends on B0411 (`eq:free-stress-1`,
`Units/B0411.lean`); consumer B0449 (`eq:free-stress-5`).

**Statement (tex 7637–7661).** Standing: `ν > 0`, `0 < P ≤ 1` (tex 7306–7308), `w ∈ D_(ν,q)`
(tex 7322–7327) with `q` in the section's range `1 < q < ∞`. Fix an observation point
`(τ₀, y₀)` and the unit strip `-1/2 < t < 1/2`, and set
`W(t, z) = w(τ₀ + t, e^{-t/2}(y₀ + √ν z))` (tex 7640). In distributions (eq:free-stress-20,
tex 7643–7649):

  `W_t = (T₀w) ∘ chart`,  `Δ_z W = ν e^{-t} (Δ_y w) ∘ chart`,  `dz = ν^{-3/2} e^{3t/2} dy`.

For a nonnegative `P`-periodic `h`, any unit interval has integral at most `(1 + P)` times the
period average of `h`, hence at most twice it (tex 7652–7654). Consequently (eq:free-stress-21,
tex 7656–7661) `‖W‖_{L^q} + ‖W_t‖_{L^q} + ‖Δ_z W‖_{L^q} ≤ C_q ν^{-3/(2q)} ‖w‖_{D_(ν,q)}` on the
strip, independently of `(τ₀, y₀)`.

**Formalization** (model of decision D2: `Y_q = L^q(ℝ/Pℤ; L^q(ℝ³; ℂ³))`, `PhaseSpace.Yq`).
* `W` is `PhaseSpace.chartPullback w ν τ₀ y₀` (pointwise, `Lib/PhaseSpace/Charts.lean`), and,
  as an `L^q(ℝ³)`-valued map of `t`, `chartLp w ν τ₀ y₀` (`Units/B0447/Chart.lean`);
  `coeFn_chartLp` identifies them a.e. in `z` for every `t`.
* (20), first line: `free_stress_20_time`, the weak time derivative (`HasWeakDerivTime`, Bochner
  sense, which implies the distributional one) of `t ↦ W(t)` on `(-1/2, 1/2)` is the chart
  pullback of `T₀w = T0D w`.
* (20), second line: `free_stress_20_lap`, for a.e. `t`, `Δ_z W(t) = e^{-t} (a ∘ chart)(t)` in
  `D'(ℝ³)` with `a = νΔw = nuLapD w`, i.e. `Δ_z W = ν e^{-t} (Δ_y w) ∘ chart`. Spatial tests are
  real smooth compactly supported `ψ` times a vector `e ∈ ℂ³`; the Laplacian of a test is the
  library's Cartesian `Heat.laplacian`. `integrable_test_chartPullback` shows that both
  integrals are integrals of integrable functions (no junk value).
* (20), third line: `chart_jacobian`, the image of `dz` under `z ↦ e^{-t/2}(y₀ + √ν z)` is
  `ν^{-3/2} e^{3t/2} dy`.
* Periodic covering: `lintegral_unit_le_one_add` (`≤ (1 + P)·average`) and
  `PhaseSpace.lintegral_unit_le` (`≤ 2·average` for `P ≤ 1`).
* (21): `free_stress_21`, with `C_q = e^{1/2} (2e^{3/4})^{1/q}` (`Cq`), via
  `PhaseSpace.chart_norm_le`. The strip norm `stripNorm` is the iterated
  `(∫_{-1/2}^{1/2} ∫_{ℝ³} |·|^q dz dt)^{1/q}` in `ℝ≥0∞`, so the bound also asserts finiteness. By
  (20), the three functions bounded are `W`, `W_t` and `Δ_z W`.
* `B0447_spec` bundles all of the above.

Hypotheses versus the manuscript: (20) time line uses only `T₀w ∈ Y_q` and `q < ∞`; (20)
Laplacian line uses only `νΔw ∈ Y_q`, `ν > 0` and `1 < q` (`q = ∞` allowed); the Jacobian
uses only `ν > 0`; the `(1 + P)` covering bound uses only `P > 0`; (21) uses `ν > 0`,
`0 < P ≤ 1`, `1 ≤ q < ∞`. All identities hold for every `t ∈ ℝ`, so in particular on the strip.
None of the hypotheses is stronger than the manuscript's.

Status: every claim of the unit is proved. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0447

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.BochnerTime

/-! ### The Jacobian (third line of (20), tex 7647) -/

/-- **`dz = ν^{-3/2} e^{3t/2} dy`** (tex 7647): the image of Lebesgue measure `dz` under the
spatial chart `z ↦ e^{-t/2}(y₀ + √ν z)` is `ν^{-3/2} e^{3t/2}` times Lebesgue measure `dy`. -/
theorem chart_jacobian {ν : ℝ} (hν : 0 < ν) (τ₀ : ℝ) (y₀ : Space) (t : ℝ) :
    Measure.map (fun z => (comovingChart ν τ₀ y₀ t z).2) (volume : Measure Space) =
      ENNReal.ofReal (ν ^ (-(3 / 2 : ℝ)) * Real.exp (3 * t / 2)) • (volume : Measure Space) := by
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hc : Real.exp (-t / 2) * Real.sqrt ν ≠ 0 :=
    mul_ne_zero (Real.exp_pos _).ne' hs.ne'
  have hfun : (fun z => (comovingChart ν τ₀ y₀ t z).2) =
      (fun x : Space => x + Real.exp (-t / 2) • y₀) ∘
        (fun z : Space => (Real.exp (-t / 2) * Real.sqrt ν) • z) := by
    funext z
    simp only [Function.comp_apply, chart_snd]
  rw [hfun, ← Measure.map_map (measurable_add_const _) (measurable_const_smul _),
    map_smul_space hc, Measure.map_smul, (measurePreserving_add_right volume _).map_eq]
  congr 2
  rw [abs_of_pos (by positivity), mul_pow, mul_inv]
  have h1 : (Real.exp (-t / 2) ^ 3)⁻¹ = Real.exp (3 * t / 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    push_cast
    ring
  have h2 : (Real.sqrt ν ^ 3)⁻¹ = ν ^ (-(3 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hν.le, Real.rpow_neg hν.le]
    norm_num
  rw [h1, h2, mul_comm]

/-! ### Unit intervals against the period average (tex 7652–7654) -/

variable {P : ℝ} [hP : Fact (0 < P)]

/-- **A unit interval carries at most `(1 + P)` times the period average** (tex 7652–7654):
for a nonnegative `P`-periodic `h` (a function on `ℝ/Pℤ`) and any unit interval
`(τ₀ - 1/2, τ₀ + 1/2)`, `∫ h ≤ (1 + P) · P⁻¹ ∫₀ᴾ h`. Adapted from
`PhaseSpace.lintegral_unit_le` (`Lib/PhaseSpace/Charts.lean`), which gives the factor `2`. -/
theorem lintegral_unit_le_one_add (h : AddCircle P → ℝ≥0∞) (τ₀ : ℝ) :
    ∫⁻ t in Ioo (-(1 / 2 : ℝ)) (1 / 2), h ((τ₀ + t : ℝ) : AddCircle P) ≤
      ENNReal.ofReal (1 + P) * ∫⁻ τ, h τ ∂AddCircle.haarAddCircle := by
  have hP0 := hP.out
  set n : ℕ := ⌈1 / P⌉₊ with hn
  have hn1 : 1 ≤ (n : ℝ) * P := by
    have : 1 / P ≤ n := Nat.le_ceil _
    rw [div_le_iff₀ hP0] at this
    linarith
  have hn2 : (n : ℝ) * P ≤ 1 + P := by
    have : (n : ℝ) < 1 / P + 1 := Nat.ceil_lt_add_one (by positivity)
    have h' : (n : ℝ) * P < (1 / P + 1) * P := mul_lt_mul_of_pos_right this hP0
    rw [add_mul, one_div, inv_mul_cancel₀ hP0.ne'] at h'
    linarith
  have hsub : Ioo (-(1 / 2 : ℝ)) (1 / 2) ⊆ Ioc (-(1 / 2 : ℝ)) (-(1 / 2) + n * P) := by
    intro t ht
    exact ⟨ht.1, by linarith [ht.2]⟩
  calc ∫⁻ t in Ioo (-(1 / 2 : ℝ)) (1 / 2), h ((τ₀ + t : ℝ) : AddCircle P)
      ≤ ∫⁻ t in Ioc (-(1 / 2 : ℝ)) (-(1 / 2) + n * P), h ((τ₀ + t : ℝ) : AddCircle P) :=
        lintegral_mono_set hsub
    _ = n * ∫⁻ τ, h τ := lintegral_Ioc_nat_period h τ₀ _ n
    _ = n * (ENNReal.ofReal P * ∫⁻ τ, h τ ∂AddCircle.haarAddCircle) := by
        rw [AddCircle.volume_eq_smul_haarAddCircle, lintegral_smul_measure, smul_eq_mul]
    _ = ENNReal.ofReal ((n : ℝ) * P) * ∫⁻ τ, h τ ∂AddCircle.haarAddCircle := by
        rw [← mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (1 + P) * ∫⁻ τ, h τ ∂AddCircle.haarAddCircle := by
        gcongr

/-! ### The pullback identities (eq:free-stress-20) for `w ∈ D_(ν,q)` -/

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The test integrals of a chart slice are integrals of integrable functions. -/
theorem integrable_test_chartPullback {ν : ℝ} (hν : 0 < ν) (f : Yq P q) (τ₀ : ℝ) (y₀ : Space)
    (t : ℝ) {ψ : Space → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (e : CVec3) :
    Integrable (fun z => ψ z • dotL e (chartPullback f ν τ₀ y₀ t z)) := by
  have hm := memLp_testVec hψ hψc e (conjExp q)
  have hint : Integrable (fun z => dotL ((hm.toLp _ : Space → CVec3) z)
      ((chartLp f ν τ₀ y₀ t : Space → CVec3) z)) :=
    memLp_one_iff_integrable.mp (dotL.memLp_of_bilin 1 (Lp.memLp _) (Lp.memLp _))
  refine hint.congr ?_
  filter_upwards [hm.coeFn_toLp, coeFn_chartLp hν f τ₀ y₀ t] with z h1 h2
  rw [h1, h2, ContinuousLinearMap.map_smul_of_tower, ContinuousLinearMap.smul_apply]

/-- **(20), first line** (tex 7644): `W_t = (T₀w) ∘ chart` on the strip. For `w ∈ D_(ν,q)`,
`q < ∞`, the map `t ↦ W(t) ∈ L^q(ℝ³)` has weak derivative `t ↦ (T₀w)(τ₀ + t,
e^{-t/2}(y₀ + √ν ·))` on `(-1/2, 1/2)`, for every observation point `(τ₀, y₀)`. -/
theorem free_stress_20_time (hq : q ≠ ⊤) {ν : ℝ} (w : B0411.D P ν q) (τ₀ : ℝ) (y₀ : Space) :
    HasWeakDerivTime (-(1 / 2)) (1 / 2) (chartLp (w : Yq P q) ν τ₀ y₀)
      (chartLp (B0411.T0D w) ν τ₀ y₀) :=
  chart_hasWeakDerivTime hq (B0411.hasPhaseOp_T0D w) ν τ₀ y₀ _ _

/-- **(20), second line** (tex 7645): `Δ_z W = ν e^{-t} (Δ_y w) ∘ chart`. For `w ∈ D_(ν,q)`,
`ν > 0`, `1 < q`, and a.e. `t`: for every smooth compactly supported `ψ : ℝ³ → ℝ` and
`e ∈ ℂ³`, `∫ Δψ(z) e · W(t, z) dz = e^{-t} ∫ ψ(z) e · (νΔw)(τ₀ + t, e^{-t/2}(y₀ + √ν z)) dz`. -/
theorem free_stress_20_lap {ν : ℝ} (hν : 0 < ν) (hq1 : 1 < q) (w : B0411.D P ν q) (τ₀ : ℝ)
    (y₀ : Space) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ ψ : Space → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∀ e : CVec3,
        ∫ z, Heat.laplacian ψ z • dotL e (chartPullback (w : Yq P q) ν τ₀ y₀ t z) =
          (Real.exp (-t) : ℂ) * ∫ z, ψ z • dotL e (chartPullback (B0411.nuLapD w) ν τ₀ y₀ t z) :=
  chart_laplacian hν hq1 (B0411.hasPhaseOp_nuLapD w) τ₀ y₀

/-! ### The strip bound (eq:free-stress-21) -/

/-- The constant `C_q = e^{1/2} (2 e^{3/4})^{1/q}` of (21); it depends on `q` only. -/
def Cq (q : ℝ≥0∞) : ℝ := Real.exp (1 / 2) * (2 * Real.exp (3 / 4)) ^ (1 / q.toReal)

/-- **(21)** (tex 7656–7661). Under the standing assumptions `ν > 0`, `0 < P ≤ 1`, for
`1 ≤ q < ∞` and `w ∈ D_(ν,q)`, on the strip `(-1/2, 1/2) × ℝ³`,
`‖W‖ + ‖(T₀w) ∘ chart‖ + ‖e^{-t} (νΔw) ∘ chart‖ ≤ C_q ν^{-3/(2q)} ‖w‖_{D_(ν,q)}`, uniformly in
the observation point `(τ₀, y₀)`. By (20) the second and third functions are `W_t` and
`Δ_z W`. -/
theorem free_stress_21 {ν : ℝ} (hst : B0411.Standing ν P) (hq : q ≠ ⊤) (w : B0411.D P ν q)
    (τ₀ : ℝ) (y₀ : Space) :
    stripNorm q (chartPullback (w : Yq P q) ν τ₀ y₀) +
        stripNorm q (chartPullback (B0411.T0D w) ν τ₀ y₀) +
        stripNorm q (fun t z => (Real.exp (-t) : ℂ) • chartPullback (B0411.nuLapD w) ν τ₀ y₀ t z) ≤
      ENNReal.ofReal (Cq q * ν ^ (-(3 / (2 * q.toReal))) * B0411.graphNormD w) :=
  chart_norm_le hst.period_le_one hst.nu_pos hq (w : Yq P q) (B0411.nuLapD w) (B0411.T0D w) τ₀ y₀

/-! ### The unit, bundled -/

/-- **B0447 (`eq:free-stress-20`, `eq:free-stress-21`, tex 7635–7661), bundled.** Under the
standing assumptions `ν > 0`, `0 < P ≤ 1` (`B0411.Standing`), for `1 < q < ∞`,
`w ∈ D_(ν,q)` and every observation point `(τ₀, y₀)`, with
`W(t, z) = w(τ₀ + t, e^{-t/2}(y₀ + √ν z))`:
1. `W(t)` is (a.e. in `z`) the `L^q(ℝ³)` element `chartLp w ν τ₀ y₀ t`, for every `t`;
2. `W_t = (T₀w) ∘ chart` (weak derivative of `t ↦ W(t) ∈ L^q` on `(-1/2, 1/2)`);
3. `Δ_z W = ν e^{-t}(Δ_y w) ∘ chart` in `D'(ℝ³)` for a.e. `t`, with integrable test integrands;
4. `dz = ν^{-3/2} e^{3t/2} dy` for every `t`;
5. a unit interval carries at most `(1 + P) ≤ 2` times the period average of any nonnegative
   `P`-periodic function;
6. `‖W‖ + ‖W_t‖ + ‖Δ_z W‖ ≤ C_q ν^{-3/(2q)} ‖w‖_{D_(ν,q)}` on the strip, `C_q = Cq q`
   independent of `(τ₀, y₀)`, `P` and `ν`. -/
theorem B0447_spec {ν : ℝ} (hst : B0411.Standing ν P) (hq1 : 1 < q) (hq : q ≠ ⊤)
    (w : B0411.D P ν q) (τ₀ : ℝ) (y₀ : Space) :
    (∀ t, (chartLp (w : Yq P q) ν τ₀ y₀ t : Space → CVec3) =ᵐ[volume]
      chartPullback (w : Yq P q) ν τ₀ y₀ t) ∧
    HasWeakDerivTime (-(1 / 2)) (1 / 2) (chartLp (w : Yq P q) ν τ₀ y₀)
      (chartLp (B0411.T0D w) ν τ₀ y₀) ∧
    (∀ t, (chartLp (B0411.T0D w) ν τ₀ y₀ t : Space → CVec3) =ᵐ[volume]
      chartPullback (B0411.T0D w) ν τ₀ y₀ t) ∧
    (∀ᵐ t ∂(volume : Measure ℝ), ∀ ψ : Space → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∀ e : CVec3,
        ∫ z, Heat.laplacian ψ z • dotL e (chartPullback (w : Yq P q) ν τ₀ y₀ t z) =
          (Real.exp (-t) : ℂ) * ∫ z, ψ z • dotL e (chartPullback (B0411.nuLapD w) ν τ₀ y₀ t z)) ∧
    (∀ t, ∀ ψ : Space → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ e : CVec3,
      Integrable (fun z => Heat.laplacian ψ z • dotL e (chartPullback (w : Yq P q) ν τ₀ y₀ t z)) ∧
      Integrable (fun z => ψ z • dotL e (chartPullback (B0411.nuLapD w) ν τ₀ y₀ t z))) ∧
    (∀ t, Measure.map (fun z => (comovingChart ν τ₀ y₀ t z).2) (volume : Measure Space) =
      ENNReal.ofReal (ν ^ (-(3 / 2 : ℝ)) * Real.exp (3 * t / 2)) • (volume : Measure Space)) ∧
    (∀ (h : AddCircle P → ℝ≥0∞) (τ₁ : ℝ),
      ∫⁻ t in Ioo (-(1 / 2 : ℝ)) (1 / 2), h ((τ₁ + t : ℝ) : AddCircle P) ≤
        ENNReal.ofReal (1 + P) * ∫⁻ τ, h τ ∂AddCircle.haarAddCircle ∧
      ∫⁻ t in Ioo (-(1 / 2 : ℝ)) (1 / 2), h ((τ₁ + t : ℝ) : AddCircle P) ≤
        2 * ∫⁻ τ, h τ ∂AddCircle.haarAddCircle) ∧
    stripNorm q (chartPullback (w : Yq P q) ν τ₀ y₀) +
        stripNorm q (chartPullback (B0411.T0D w) ν τ₀ y₀) +
        stripNorm q (fun t z => (Real.exp (-t) : ℂ) • chartPullback (B0411.nuLapD w) ν τ₀ y₀ t z) ≤
      ENNReal.ofReal (Cq q * ν ^ (-(3 / (2 * q.toReal))) * B0411.graphNormD w) := by
  have hν := hst.nu_pos
  refine ⟨fun t => coeFn_chartLp hν _ τ₀ y₀ t, free_stress_20_time hq w τ₀ y₀,
    fun t => coeFn_chartLp hν _ τ₀ y₀ t, free_stress_20_lap hν hq1 w τ₀ y₀,
    fun t ψ hψ hψc e => ⟨integrable_test_chartPullback hν _ τ₀ y₀ t
      (contDiff_laplacian hψ).continuous (hasCompactSupport_laplacian hψc) e,
      integrable_test_chartPullback hν _ τ₀ y₀ t hψ.continuous hψc e⟩,
    fun t => chart_jacobian hν τ₀ y₀ t,
    fun h τ₁ => ⟨lintegral_unit_le_one_add h τ₁, lintegral_unit_le hst.period_le_one h τ₁⟩,
    free_stress_21 hst hq w τ₀ y₀⟩

end UnforcedLeray.B0447
