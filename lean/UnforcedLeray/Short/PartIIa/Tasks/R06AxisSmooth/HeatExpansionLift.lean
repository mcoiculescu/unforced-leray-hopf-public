import UnforcedLeray.Short.PartIIa.StatementsRing
import UnforcedLeray.Short.PartIIa.Tasks.R02.HeatProfile
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.HeatKernelIterSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.MeanRemainderSmooth
import UnforcedLeray.Lib.AxisymmetricB.AxisRegularity

/-!
# Part II-a, task `PartII-a:R06` helper: explicit smooth lift of the heat-kernel expansion terms

Source of record: `the November 2 reference manuscript`, lines 1305-1322:
\[
  r a_{2j} \partial_\eta^{2j} G_{\nu s}
    = \frac{a_{2j} r^{2j+2}}{R^{2j+1}} \partial_z^{2j} G_{\nu t}(z).
\]

This file defines the explicit Cartesian velocity field `heatTermVel ν R a j` on `ℝ × Space`
corresponding to the `j`-th even heat-kernel stream term `a * ∂_η^{2j} G_{νs}(η)` and proves:
1. `contDiffOn_heatTermVel`: for `ν > 0`, `heatTermVel ν R a j` is `C^∞` on `{z : ℝ × Space | 0 < z.1}`
   (including the symmetry axis `Axi.axis`).
2. `heatTermVel_eq_liftVelocity`: off the axis (`x ∉ Axi.axis`) and for `t > 0`, `R > 0`,
   `heatTermVel ν R a j (t, x)` agrees with `liftVelocity R (fun y => a * lhP ν (2 * j) y) t x`.
3. `heatTermVel_succ_of_mem_axis` and `liftVelocity_of_mem_axis`: on the axis (`x ∈ Axi.axis`),
   `heatTermVel ν R a (j + 1) (t, x) = 0` and `liftVelocity R ψ t x = 0`.
4. `ringSmoothVel` (the global velocity extension on `{t > 0}`) agrees off the axis with
   `liftVelocity R (trainProfile tr.ψ)` and decomposes at every expansion order `N : ℕ` on all of
   `{z : ℝ × Space | 0 < z.1}` (both on and off the axis) into the finite sum of smooth heat terms
   `∑_{j ≤ N} heatTermVel ν R (meanCoeff tr j) j z`, the mean-remainder velocity lift, and the
   fluctuation velocity lift.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.RingLift UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187
  UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (meanStream meanRemainder meanCoeff heatKernel1)

/-! ### 1. The explicit parity-form velocity field of the `j`-th heat expansion term -/

/-- The explicit Cartesian velocity field of the `j`-th heat-expansion stream term
`a_{2j} ∂_η^{2j} G_{νs}(η)`:
* horizontal part `(-a R^{-(2j+1)} (x₀² + x₁²)^j ∂_z^{2j+1} G_{νt}(x₂)) • hor x`,
* axial part `((2j + 2) a R^{-(2j+1)} (x₀² + x₁²)^j ∂_z^{2j} G_{νt}(x₂)) • e₃`. -/
def heatTermVel (ν R a : ℝ) (j : ℕ) (z : ℝ × Space) : Space :=
  (-a * R⁻¹ ^ (2 * j + 1) * (z.2 0 ^ 2 + z.2 1 ^ 2) ^ j *
      iteratedDeriv (2 * j + 1) (heatKernel1 (ν * z.1)) (z.2 2)) • Axi.hor z.2 +
    ((2 * (j : ℝ) + 2) * a * R⁻¹ ^ (2 * j + 1) * (z.2 0 ^ 2 + z.2 1 ^ 2) ^ j *
      iteratedDeriv (2 * j) (heatKernel1 (ν * z.1)) (z.2 2)) • Axi.e3

/-- The global velocity witness on `{t > 0}`: the `j = 0` heat term (which carries the nonzero
axial value `(2 a₀ / R) G_{νt}(z) e₃` on the axis) plus `liftVelocity` of the remainder
`ψ - a₀ G_{νs}` (which vanishes on the axis). -/
def ringSmoothVel (ν R a₀ : ℝ) (ψ : ProfilePoint → ℝ) (z : ℝ × Space) : Space :=
  heatTermVel ν R a₀ 0 z + liftVelocity R (fun y => ψ y - a₀ * lhP ν 0 y) z.1 z.2

/-- The global pressure witness on `{t > 0}` (vanishes on the axis). -/
def ringSmoothPres (R : ℝ) (p : ProfilePoint → ℝ) (z : ℝ × Space) : ℝ :=
  liftPressure R p z.1 z.2

/-- Joint `C^∞` smoothness of `(t, x) ↦ ∂_z^k G_{νt}(x₂)` on `{z : ℝ × Space | 0 < z.1}`. -/
theorem contDiffOn_heatKernel1_spacetime {ν : ℝ} (hν : 0 < ν) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => iteratedDeriv k (heatKernel1 (ν * z.1)) (z.2 2))
      {z : ℝ × Space | 0 < z.1} := by
  have h1 := heatKernelIterSmooth ν hν k
  have hmap : ContDiff ℝ ∞ (fun z : ℝ × Space => (z.1, z.2 2)) := by fun_prop
  have hmaps : MapsTo (fun z : ℝ × Space => (z.1, z.2 2))
      {z : ℝ × Space | 0 < z.1} (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :=
    fun z hz => ⟨hz, trivial⟩
  exact h1.comp hmap.contDiffOn hmaps

/-- Every heat expansion velocity term `heatTermVel ν R a j` is `C^∞` on `{z : ℝ × Space | 0 < z.1}`
(including the axis). -/
theorem contDiffOn_heatTermVel {ν : ℝ} (hν : 0 < ν) (R a : ℝ) (j : ℕ) :
    ContDiffOn ℝ ∞ (heatTermVel ν R a j) {z : ℝ × Space | 0 < z.1} := by
  have hrad_sq : ContDiffOn ℝ ∞ (fun z : ℝ × Space => (z.2 0 ^ 2 + z.2 1 ^ 2) ^ j)
      {z : ℝ × Space | 0 < z.1} := by
    have hm : ContDiff ℝ ∞ (fun z : ℝ × Space => (z.2 0 ^ 2 + z.2 1 ^ 2) ^ j) := by fun_prop
    exact hm.contDiffOn
  have hhor : ContDiffOn ℝ ∞ (fun z : ℝ × Space => Axi.hor z.2) {z : ℝ × Space | 0 < z.1} :=
    (Axi.contDiff_hor.comp contDiff_snd).contDiffOn
  have hk1 := contDiffOn_heatKernel1_spacetime hν (2 * j + 1)
  have hk0 := contDiffOn_heatKernel1_spacetime hν (2 * j)
  have hc1 : ContDiffOn ℝ ∞
      (fun z : ℝ × Space => -a * R⁻¹ ^ (2 * j + 1) * (z.2 0 ^ 2 + z.2 1 ^ 2) ^ j *
        iteratedDeriv (2 * j + 1) (heatKernel1 (ν * z.1)) (z.2 2))
      {z : ℝ × Space | 0 < z.1} :=
    (contDiffOn_const.mul hrad_sq).mul hk1
  have hc0 : ContDiffOn ℝ ∞
      (fun z : ℝ × Space => (2 * (j : ℝ) + 2) * a * R⁻¹ ^ (2 * j + 1) *
        (z.2 0 ^ 2 + z.2 1 ^ 2) ^ j *
        iteratedDeriv (2 * j) (heatKernel1 (ν * z.1)) (z.2 2))
      {z : ℝ × Space | 0 < z.1} :=
    (contDiffOn_const.mul hrad_sq).mul hk0
  exact (hc1.smul hhor).add (hc0.smul contDiffOn_const)

/-! ### 2. Behaviour on the axis -/

theorem hor_eq_zero_of_mem_axis {x : Space} (hx : x ∈ Axi.axis) : Axi.hor x = 0 := by
  obtain ⟨h0, h1⟩ := hx
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simp

theorem sum_sq_eq_zero_of_mem_axis {x : Space} (hx : x ∈ Axi.axis) :
    x 0 ^ 2 + x 1 ^ 2 = 0 := by
  obtain ⟨h0, h1⟩ := hx
  have e0 : x 0 = 0 := h0
  have e1 : x 1 = 0 := h1
  rw [e0, e1]
  ring

/-- For `j ≥ 1`, `heatTermVel ν R a (j + 1)` vanishes on the axis. -/
theorem heatTermVel_succ_of_mem_axis (ν R a : ℝ) (j : ℕ) {z : ℝ × Space}
    (hz : z.2 ∈ Axi.axis) : heatTermVel ν R a (j + 1) z = 0 := by
  unfold heatTermVel
  rw [hor_eq_zero_of_mem_axis hz, sum_sq_eq_zero_of_mem_axis hz,
    zero_pow (Nat.succ_ne_zero j)]
  simp

/-- `liftVelocity` vanishes on the axis for every profile. -/
theorem liftVelocity_of_mem_axis (R : ℝ) (ψ : ProfilePoint → ℝ) (t : ℝ) {x : Space}
    (hx : x ∈ Axi.axis) : liftVelocity R ψ t x = 0 := by
  have hρ : Axi.ϱ x = 0 := (Axi.mem_axis_iff x).1 hx
  rw [liftVelocity_apply, hρ]
  simp [Axi.eR, hρ, liftUr_apply, liftUz_apply, radialScale]

/-- `liftPressure` vanishes on the axis for every profile. -/
theorem liftPressure_of_mem_axis (R : ℝ) (p : ProfilePoint → ℝ) (t : ℝ) {x : Space}
    (hx : x ∈ Axi.axis) : liftPressure R p t x = 0 := by
  have hρ : Axi.ϱ x = 0 := (Axi.mem_axis_iff x).1 hx
  simp [liftPressure, rawPressure_apply, radialScale, hρ]

/-! ### 3. Profile calculus and chart lift of `lhP` -/

theorem lhPartialQ (ν : ℝ) (m : ℕ) {y : ProfilePoint} (hy : 0 < y.2.2) :
    partialQ (lhP ν m) y = 0 := by
  unfold partialQ
  apply lhFderivLine (lhDiff ν m hy)
  have hline : (fun t : ℝ => lhP ν m (y + t • eqDir)) =
      fun _ : ℝ => UnforcedLeray.B0191.heatDeriv ν m y.2.1 y.2.2 := by
    funext t
    simp [lhP, eqDir]
  rw [hline]
  exact hasDerivAt_const 0 _

theorem lhAgeOperator (ν : ℝ) (m : ℕ) {y : ProfilePoint} (hy : 0 < y.2.2) :
    ageOperator (lhP ν m) y = -((m : ℝ) + 1) * lhP ν m y := by
  have hy0 : y.2.2 ≠ 0 := hy.ne'
  unfold ageOperator
  rw [lhPartialEta ν m hy, lhPartialAge ν m hy]
  field_simp
  ring

theorem lhAgeDefect (ν : ℝ) (m : ℕ) {y : ProfilePoint} (hy : 0 < y.2.2) :
    ageDefect (lhP ν m) y = ((m : ℝ) + 2) * lhP ν m y := by
  unfold ageDefect
  rw [lhAgeOperator ν m hy]
  ring

/-- Linearity of `streamV1` and `axialProfile` on profiles differentiable at `y`. -/
theorem streamV1_const_mul (a : ℝ) {f : ProfilePoint → ℝ} {y : ProfilePoint}
    (hf : DifferentiableAt ℝ f y) :
    streamV1 (fun w => a * f w) y = a * streamV1 f y := by
  simp only [streamV1, partialEta, fderiv_const_mul hf, smul_apply, smul_eq_mul]
  ring

theorem axialProfile_const_mul (R a : ℝ) {f : ProfilePoint → ℝ} {y : ProfilePoint}
    (hf : DifferentiableAt ℝ f y) :
    axialProfile R (fun w => a * f w) y = a * axialProfile R f y := by
  simp only [axialProfile, streamV2, ageDefect, ageOperator, partialQ, partialEta, partialAge,
    fderiv_const_mul hf, smul_apply, smul_eq_mul]
  ring

theorem streamV1_add {f g : ProfilePoint → ℝ} {y : ProfilePoint}
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    streamV1 (fun w => f w + g w) y = streamV1 f y + streamV1 g y := by
  have hfd : fderiv ℝ (fun w => f w + g w) y = fderiv ℝ f y + fderiv ℝ g y :=
    (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv
  simp only [streamV1, partialEta, hfd, add_apply]
  ring

theorem axialProfile_add (R : ℝ) {f g : ProfilePoint → ℝ} {y : ProfilePoint}
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    axialProfile R (fun w => f w + g w) y = axialProfile R f y + axialProfile R g y := by
  have hfd : fderiv ℝ (fun w => f w + g w) y = fderiv ℝ f y + fderiv ℝ g y :=
    (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv
  simp only [axialProfile, streamV2, ageDefect, ageOperator, partialQ, partialEta, partialAge,
    hfd, add_apply]
  ring

theorem streamV1_sub {f g : ProfilePoint → ℝ} {y : ProfilePoint}
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    streamV1 (fun w => f w - g w) y = streamV1 f y - streamV1 g y := by
  have hfd : fderiv ℝ (fun w => f w - g w) y = fderiv ℝ f y - fderiv ℝ g y :=
    (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv
  simp only [streamV1, partialEta, hfd, sub_apply]
  ring

theorem axialProfile_sub (R : ℝ) {f g : ProfilePoint → ℝ} {y : ProfilePoint}
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    axialProfile R (fun w => f w - g w) y = axialProfile R f y - axialProfile R g y := by
  have hfd : fderiv ℝ (fun w => f w - g w) y = fderiv ℝ f y - fderiv ℝ g y :=
    (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv
  simp only [axialProfile, streamV2, ageDefect, ageOperator, partialQ, partialEta, partialAge,
    hfd, sub_apply]
  ring

/-- `liftVelocity` of `f + g` equals `liftVelocity f + liftVelocity g` everywhere on `Space`
(including the axis) whenever `f, g` are differentiable on `{y | 0 < y.2.2}` and `R ≠ 0`, `t > 0`. -/
theorem liftVelocity_add {R t : ℝ} (hR : R ≠ 0) (ht : 0 < t) {f g : ProfilePoint → ℝ}
    (hf : ∀ y : ProfilePoint, 0 < y.2.2 → DifferentiableAt ℝ f y)
    (hg : ∀ y : ProfilePoint, 0 < y.2.2 → DifferentiableAt ℝ g y) (x : Space) :
    liftVelocity R (fun y => f y + g y) t x = liftVelocity R f t x + liftVelocity R g t x := by
  by_cases hx : x ∈ Axi.axis
  · simp [liftVelocity_of_mem_axis _ _ _ hx]
  · have hy : 0 < (profileChart R (Axi.ϱ x) (x 2) t).2.2 :=
      mapsTo_profileChart_mer R t hR ht (x := (Axi.ϱ x, x 2)) ⟨Axi.ϱ_pos hx, trivial⟩
    simp only [liftVelocity_apply, liftUr_apply, liftUz_apply,
      streamV1_add (hf _ hy) (hg _ hy), axialProfile_add R (hf _ hy) (hg _ hy)]
    module

/-- `liftVelocity` of `f - g` equals `liftVelocity f - liftVelocity g` everywhere on `Space`
whenever `f, g` are differentiable on `{y | 0 < y.2.2}` and `R ≠ 0`, `t > 0`. -/
theorem liftVelocity_sub {R t : ℝ} (hR : R ≠ 0) (ht : 0 < t) {f g : ProfilePoint → ℝ}
    (hf : ∀ y : ProfilePoint, 0 < y.2.2 → DifferentiableAt ℝ f y)
    (hg : ∀ y : ProfilePoint, 0 < y.2.2 → DifferentiableAt ℝ g y) (x : Space) :
    liftVelocity R (fun y => f y - g y) t x = liftVelocity R f t x - liftVelocity R g t x := by
  by_cases hx : x ∈ Axi.axis
  · simp [liftVelocity_of_mem_axis _ _ _ hx]
  · have hy : 0 < (profileChart R (Axi.ϱ x) (x 2) t).2.2 :=
      mapsTo_profileChart_mer R t hR ht (x := (Axi.ϱ x, x 2)) ⟨Axi.ϱ_pos hx, trivial⟩
    simp only [liftVelocity_apply, liftUr_apply, liftUz_apply,
      streamV1_sub (hf _ hy) (hg _ hy), axialProfile_sub R (hf _ hy) (hg _ hy)]
    module

/-- `liftVelocity` of a finite sum of profiles differentiable on `{y | 0 < y.2.2}`. -/
theorem liftVelocity_sum {R t : ℝ} (hR : R ≠ 0) (ht : 0 < t) {ι : Type*} (s : Finset ι)
    (f : ι → ProfilePoint → ℝ)
    (hf : ∀ i ∈ s, ∀ y : ProfilePoint, 0 < y.2.2 → DifferentiableAt ℝ (f i) y) (x : Space) :
    liftVelocity R (fun y => ∑ i ∈ s, f i y) t x = ∑ i ∈ s, liftVelocity R (f i) t x := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty, liftVelocity_apply, liftUr_apply, liftUz_apply,
      streamV1, axialProfile, streamV2, ageDefect, ageOperator, partialEta, partialQ, partialAge,
      fderiv_const_apply, zero_apply]
    module
  | @insert a s ha ih =>
    have hfa : ∀ y : ProfilePoint, 0 < y.2.2 → DifferentiableAt ℝ (f a) y :=
      hf a (Finset.mem_insert_self a s)
    have hfs : ∀ y : ProfilePoint, 0 < y.2.2 → DifferentiableAt ℝ (fun y => ∑ i ∈ s, f i y) y :=
      fun y hy => DifferentiableAt.fun_sum fun i hi => hf i (Finset.mem_insert_of_mem hi) y hy
    simp only [Finset.sum_insert ha]
    rw [liftVelocity_add hR ht hfa hfs x, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- Value of `lhP ν m` at the chart point `profileChart R r z t` for `r > 0`, `t > 0`, `R > 0`. -/
theorem lhP_profileChart (ν : ℝ) {R r t : ℝ} (hR : 0 < R) (hr : 0 < r) (ht : 0 < t)
    (z : ℝ) (m : ℕ) :
    lhP ν m (profileChart R r z t) =
      (r / R) ^ (m + 1) * iteratedDeriv m (heatKernel1 (ν * t)) z := by
  have hlam : 0 < R / r := div_pos hR hr
  have h1 := UnforcedLeray.B0191.heatDeriv_homogeneous ν m z ht hlam
  unfold lhP
  change UnforcedLeray.B0191.heatDeriv ν m (R / r * z) ((R / r) ^ 2 * t) = _
  rw [h1, inv_div, lhHeatKernelEq ν m z t]

/-- **Exact chart-lift identity for the `j`-th heat expansion term**: off the axis (`x ∉ Axi.axis`)
and for `t > 0`, `R > 0`, `heatTermVel ν R a j (t, x)` equals the B0185 velocity lift of
`y ↦ a * ∂_η^{2j} G_{νs}(η)`. -/
theorem heatTermVel_eq_liftVelocity (ν : ℝ) {R : ℝ} (hR : 0 < R) (a : ℝ) (j : ℕ)
    {t : ℝ} (ht : 0 < t) {x : Space} (hx : x ∉ Axi.axis) :
    heatTermVel ν R a j (t, x) = liftVelocity R (fun y => a * lhP ν (2 * j) y) t x := by
  have hr : 0 < Axi.ϱ x := Axi.ϱ_pos hx
  have hr0 : Axi.ϱ x ≠ 0 := hr.ne'
  have hR0 : R ≠ 0 := hR.ne'
  set y := profileChart R (Axi.ϱ x) (x 2) t
  have hy : 0 < y.2.2 :=
    mapsTo_profileChart_mer R t hR0 ht (x := (Axi.ϱ x, x 2)) ⟨hr, trivial⟩
  have hdiff : DifferentiableAt ℝ (lhP ν (2 * j)) y := lhDiff ν (2 * j) hy
  have hv1 : streamV1 (lhP ν (2 * j)) y = -lhP ν (2 * j + 1) y := by
    rw [streamV1, lhPartialEta ν (2 * j) hy]
  have hax : axialProfile R (lhP ν (2 * j)) y =
      R⁻¹ * ((2 * (j : ℝ) + 2) * lhP ν (2 * j) y) := by
    unfold axialProfile streamV2 ringEps
    rw [lhPartialQ ν (2 * j) hy, lhAgeDefect ν (2 * j) hy]
    push_cast
    ring
  have hur : liftUr R (fun w => a * lhP ν (2 * j) w) (Axi.ϱ x) (x 2) t =
      (-a * R⁻¹ ^ (2 * j + 1) * (Axi.ϱ x ^ 2) ^ j *
        iteratedDeriv (2 * j + 1) (heatKernel1 (ν * t)) (x 2)) * Axi.ϱ x := by
    rw [liftUr_apply, streamV1_const_mul a hdiff, hv1,
      lhP_profileChart ν hR hr ht (x 2) (2 * j + 1), (profileChart_eq R (Axi.ϱ x) (x 2) t).1]
    have hp : (Axi.ϱ x / R) ^ (2 * j + 1 + 1) =
        Axi.ϱ x * Axi.ϱ x * (Axi.ϱ x ^ 2) ^ j * R⁻¹ * R⁻¹ ^ (2 * j + 1) := by
      rw [div_eq_mul_inv, mul_pow]
      ring
    rw [hp]
    field_simp
  have huz : liftUz R (fun w => a * lhP ν (2 * j) w) (Axi.ϱ x) (x 2) t =
      (2 * (j : ℝ) + 2) * a * R⁻¹ ^ (2 * j + 1) * (Axi.ϱ x ^ 2) ^ j *
        iteratedDeriv (2 * j) (heatKernel1 (ν * t)) (x 2) := by
    rw [liftUz_apply, axialProfile_const_mul R a hdiff, hax,
      lhP_profileChart ν hR hr ht (x 2) (2 * j), (profileChart_eq R (Axi.ϱ x) (x 2) t).1]
    have hp : (Axi.ϱ x / R) ^ (2 * j + 1) =
        Axi.ϱ x * (Axi.ϱ x ^ 2) ^ j * R⁻¹ ^ (2 * j + 1) := by
      rw [div_eq_mul_inv, mul_pow]
      ring
    rw [hp]
    field_simp
  have hsq : Axi.ϱ x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := Axi.ϱ_sq x
  rw [liftVelocity_apply, hur, huz, ← smul_smul, ← Axi.hor_eq_smul_eR hx, hsq]
  rfl

/-! ### 4. Global decomposition of `ringSmoothVel` at arbitrary order `N` -/

/-- Off the axis (`x ∉ Axi.axis`) and for `t > 0`, `R > 0`, `ringSmoothVel` agrees with
`liftVelocity R ψ t x` for any stream `ψ` differentiable on `{y | 0 < y.2.2}`. -/
theorem ringSmoothVel_eq_liftVelocity {ν R : ℝ} (hR : 0 < R) (a₀ : ℝ)
    {ψ : ProfilePoint → ℝ} (hψ : ∀ y : ProfilePoint, 0 < y.2.2 → DifferentiableAt ℝ ψ y)
    {t : ℝ} (ht : 0 < t) {x : Space} (hx : x ∉ Axi.axis) :
    ringSmoothVel ν R a₀ ψ (t, x) = liftVelocity R ψ t x := by
  have hd0 : ∀ y : ProfilePoint, 0 < y.2.2 → DifferentiableAt ℝ (fun w => a₀ * lhP ν 0 w) y :=
    fun y hy => (lhDiff ν 0 hy).const_mul a₀
  unfold ringSmoothVel
  rw [heatTermVel_eq_liftVelocity ν hR a₀ 0 ht hx,
    liftVelocity_sub hR.ne' ht hψ hd0 x, add_sub_cancel]

/-- Pointwise decomposition of the stream profile `trainProfile tr.ψ` at order `N : ℕ` into the
heat expansion sum, the mean remainder `meanRemainder tr N`, and the fluctuation `ψ - meanStream`. -/
theorem trainProfile_psi_decomp {ν c : ℝ} (tr : B0140.TrainSol ν c) (N : ℕ) (y : ProfilePoint) :
    trainProfile tr.ψ y =
      (∑ j ∈ Finset.range (N + 1), meanCoeff tr j * lhP ν (2 * j) y) +
        trainProfile (fun s w => meanRemainder tr N s w.2) y +
        trainProfile (fun s w => tr.ψ s w - meanStream tr s w.2) y := by
  simp only [trainProfile, meanRemainder, lhP_eq]
  ring

/-- Global decomposition of `ringSmoothVel` at order `N : ℕ` on `{z : ℝ × Space | 0 < z.1}`
(valid BOTH on the axis and off the axis!). -/
theorem ringSmoothVel_decomp {ν c R : ℝ} (hν : 0 < ν) (hc : 0 < c) (hR : 0 < R)
    (tr : B0140.TrainSol ν c) (hb : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    (hS : LateProfileSmooth) (hE : UnforcedLeray.Short.PartI.TrainMeanEquations)
    (N : ℕ) {z : ℝ × Space} (hz : 0 < z.1) :
    ringSmoothVel ν R (meanCoeff tr 0) (trainProfile tr.ψ) z =
      (∑ j ∈ Finset.range (N + 1), heatTermVel ν R (meanCoeff tr j) j z) +
        liftVelocity R (trainProfile fun s w => meanRemainder tr N s w.2) z.1 z.2 +
        liftVelocity R (trainProfile fun s w => tr.ψ s w - meanStream tr s w.2) z.1 z.2 := by
  rcases z with ⟨t, x⟩
  change 0 < t at hz
  by_cases hx : x ∈ Axi.axis
  · -- On the axis: `liftVelocity` vanishes and `heatTermVel` vanishes for `j ≥ 1`.
    unfold ringSmoothVel
    rw [liftVelocity_of_mem_axis _ _ _ hx, liftVelocity_of_mem_axis _ _ _ hx,
      liftVelocity_of_mem_axis _ _ _ hx, add_zero, add_zero, add_zero,
      Finset.sum_range_succ' (fun j => heatTermVel ν R (meanCoeff tr j) j (t, x)) N]
    have hsum0 : (∑ k ∈ Finset.range N,
        heatTermVel ν R (meanCoeff tr (k + 1)) (k + 1) (t, x)) = 0 :=
      Finset.sum_eq_zero fun k _ => heatTermVel_succ_of_mem_axis ν R (meanCoeff tr (k + 1)) k hx
    rw [hsum0, zero_add]
  · -- Off the axis: `ringSmoothVel = liftVelocity R (trainProfile tr.ψ)` and `liftVelocity` is linear.
    have hU : IsOpen {y : ProfilePoint | 0 < y.2.2} := isOpen_ageDomain
    have hψ_sm : ContDiffOn ℝ ∞ (trainProfile tr.ψ) {y : ProfilePoint | 0 < y.2.2} :=
      (hS ν c hν hc tr hb).1
    have hψ_d : ∀ y : ProfilePoint, 0 < y.2.2 → DifferentiableAt ℝ (trainProfile tr.ψ) y :=
      fun y hy => (hψ_sm.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
    have hrem_sm : ContDiffOn ℝ ∞ (trainProfile fun s w => meanRemainder tr N s w.2)
        {y : ProfilePoint | 0 < y.2.2} :=
      contDiffOn_trainProfile_of_eta
        (meanRemainderSmooth_of hE heatKernelIterSmooth ν c hν hc tr hb N)
    have hrem_d : ∀ y : ProfilePoint, 0 < y.2.2 →
        DifferentiableAt ℝ (trainProfile fun s w => meanRemainder tr N s w.2) y :=
      fun y hy => (hrem_sm.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
    have hmean_sm : ContDiffOn ℝ ∞ (trainProfile fun s w => meanStream tr s w.2)
        {y : ProfilePoint | 0 < y.2.2} :=
      contDiffOn_trainProfile_of_eta (hE ν c hν hc tr hb).1
    have hfl_sm : ContDiffOn ℝ ∞ (trainProfile fun s w => tr.ψ s w - meanStream tr s w.2)
        {y : ProfilePoint | 0 < y.2.2} :=
      hψ_sm.sub hmean_sm
    have hfl_d : ∀ y : ProfilePoint, 0 < y.2.2 →
        DifferentiableAt ℝ (trainProfile fun s w => tr.ψ s w - meanStream tr s w.2) y :=
      fun y hy => (hfl_sm.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
    have hheat_d : ∀ j ∈ Finset.range (N + 1), ∀ y : ProfilePoint, 0 < y.2.2 →
        DifferentiableAt ℝ (fun w => meanCoeff tr j * lhP ν (2 * j) w) y :=
      fun j _ y hy => (lhDiff ν (2 * j) hy).const_mul (meanCoeff tr j)
    have hsum_d : ∀ y : ProfilePoint, 0 < y.2.2 →
        DifferentiableAt ℝ (fun w => ∑ j ∈ Finset.range (N + 1), meanCoeff tr j * lhP ν (2 * j) w) y :=
      fun y hy => DifferentiableAt.fun_sum fun j hj => hheat_d j hj y hy
    rw [ringSmoothVel_eq_liftVelocity hR (meanCoeff tr 0) hψ_d hz hx]
    have hfun : trainProfile tr.ψ = fun y =>
        ((∑ j ∈ Finset.range (N + 1), meanCoeff tr j * lhP ν (2 * j) y) +
          trainProfile (fun s w => meanRemainder tr N s w.2) y) +
          trainProfile (fun s w => tr.ψ s w - meanStream tr s w.2) y :=
      funext (trainProfile_psi_decomp tr N)
    rw [hfun,
      liftVelocity_add (f := fun y =>
          (∑ j ∈ Finset.range (N + 1), meanCoeff tr j * lhP ν (2 * j) y) +
            trainProfile (fun s w => meanRemainder tr N s w.2) y)
        (g := trainProfile (fun s w => tr.ψ s w - meanStream tr s w.2))
        hR.ne' hz (fun y hy => (hsum_d y hy).add (hrem_d y hy)) hfl_d x,
      liftVelocity_add hR.ne' hz hsum_d hrem_d x,
      liftVelocity_sum hR.ne' hz (Finset.range (N + 1))
        (fun j w => meanCoeff tr j * lhP ν (2 * j) w) hheat_d x]
    have hterms : (∑ j ∈ Finset.range (N + 1),
        liftVelocity R (fun w => meanCoeff tr j * lhP ν (2 * j) w) t x) =
        ∑ j ∈ Finset.range (N + 1), heatTermVel ν R (meanCoeff tr j) j (t, x) :=
      Finset.sum_congr rfl fun j _ => (heatTermVel_eq_liftVelocity ν hR (meanCoeff tr j) j hz hx).symm
    rw [hterms]

end UnforcedLeray.Short.PartIIa
