import UnforcedLeray.Units.B0185
import UnforcedLeray.Units.B0140
import UnforcedLeray.Lib.AxisymmetricB.DSS
import UnforcedLeray.Cons.C03Background.RawLift

/-!
# B0190 `unlabeled:2916`: discrete self-similarity of the lift

Blueprint unit B0190 (old ledger C15), `paper/main.tex` lines 2916–2917, end of the subsection
"Coordinates and equations" of the exact solenoidal lift (source range 2038–3243);
infrastructure INF23 ("dilation under which `a_r ↦ a_r/λ`, `q ↦ q + R log λ`, `η` and `s`
invariant; `c`-periodicity in `q`"). Dependencies: B0185 (`eq:st18-t00188`, the lift,
`Units/B0185.lean`) and B0140 (`eq:st18-t00140`, the train, `Units/B0140.lean`).

**Statement (tex 2916–2917).** "The field and its pressure obey the DSS scaling with physical
ratio `e^{c/R}`. In similarity time `τ = log t`, the period is `2c/R`." Here (tex 2838–2857)
`R ≥ 2`, `ε = R⁻¹`, the chart is `a_r = R/r`, `q = R log(r/R)`, `η = a_r z`, `s = a_r² t`
(B0184), the field is `u_r = a_r v₁`, `u_z = a_r (v₂ + εH)` with `v = ∇^⊥ψ`, `H = (1 − K)ψ`,
and the pressure is `p_raw = a_r² p` (B0185), where `(v, p)` is the `c`-periodic train with
decaying stream `ψ` (B0140). With `λ = e^{c/R}` the claim is
`u(λx, λ²t) = λ⁻¹ u(x, t)`, `p_raw(λx, λ²t) = λ⁻² p_raw(x, t)`; in similarity variables
`y = x/√t`, `τ = log t` the similarity profiles `U(τ, y) = √t u(√t y, t)` and
`Π(τ, y) = t p_raw(√t y, t)` are periodic in `τ` with period `2c/R` (`= P = 2εc`, the phase
period of `eq:m3-ring-lift`, unit B0186, tex 2079).

**Proof (blueprint outline).** Under `(r, z, t) ↦ (λr, λz, λ²t)` one has `a_r ↦ a_r/λ`,
`q ↦ q + R log λ`, `η, s` invariant (`profileChart_dilate`, `radialScale_dilate`); for
`R log λ = c` the `c`-periodicity of the train in `q` gives the claim (`scaledLift_dss`). The
profiles `v₁ = −∂_ηψ`, `v₂ + εH` inherit the periodicity of `ψ` at positive ages, since a
derivative only sees a neighbourhood (`fderiv_shift`).

**Contents.**
* §1 `QPeriodicOn c g`: `g(q + c, η, s) = g(q, η, s)` for `s > 0`; `fderiv_shift`,
  `qPeriodicOn_streamV1`, `qPeriodicOn_streamV2`, `qPeriodicOn_ageDefect`,
  `qPeriodicOn_axialProfile`.
* §2 the dilation of the chart: `radialScale_dilate`, `profileChart_dilate`.
* §3 DSS of the lift of any `c`-periodic stream and pressure: `scaledLift_dss`, `liftUr_dss`,
  `liftUz_dss`, `rawPressure_dss` (cylindrical components), `liftVelocity_dss`,
  `liftPressure_dss` (the Cartesian field `u_r e_r + u_z e_z` and pressure on `ℝ³`).
* §4 similarity time: `simProfile k u τ y = e^{kτ/2} u(e^τ, e^{τ/2} y)`,
  `selfSim_simProfile` (the field is recovered, `Axi.selfSim`), `simProfile_periodic`,
  `simProfile_liftVelocity_periodic`, `simProfile_liftPressure_periodic` (period `2c/R`);
  `merProfile`, `liftVelocity_eq_physNv`, `simProfile_liftVelocity_eq_Nv`, `Nv_merProfile_periodic`:
  the similarity profile of the B0185 lift is the library ring lift `Axi.Nv` of the profile
  `(v₁, v₂ + εH)` (the raw lift `U_raw` of B0186), which is `2c/R`-periodic off the axis.
* §5 the train: `trainProfile` (B0140's layout `f(s, (q, η))` to B0184's `(q, (η, s))`),
  `qPeriodicOn_trainStream` (from `Cons.C03.stream_periodic_of_isTrain`),
  `qPeriodicOn_trainPressure`, `qPeriodicOn_trainVelocity`, `streamV1_trainProfile`,
  `streamV2_trainProfile` (B0185's `v₁, v₂` of the train stream are the train's components
  wherever the stream is differentiable).
* §6 `unit_B0190`: the whole unit for the lift of the train.

**Hypotheses and junk values.** The manuscript's hypotheses are `R ≥ 2` and the train of
B0140 (existence is B0140's named hypothesis `TrainIVPSolvable`; `unit_B0190` takes a train
`T : TrainSol ν c` as data, so it holds for every train). The generic statements only need
`R ≠ 0` and `c`-periodicity at positive ages; `unit_B0190` assumes `2 ≤ R` as the manuscript
does. Times are `t > 0`: the train is only constrained for `s ≥ 0`, and `s = a_r² t > 0` off the
axis. No hypothesis on `r` is needed: on the axis `r = 0` (Lean's `R/0 = 0`) both sides of
every identity are `0`, and for `r ≠ 0` the identities are genuine (`Real.log` of a nonzero
product splits). The similarity profile is evaluated only at `t = e^τ > 0`, so Lean's `√t` and
`log t` for `t ≤ 0` never enter. The derivatives in `v₁, v₂, H` are `fderiv`s; the DSS needs no
differentiability (both sides use the same `fderiv`, junk or not), and the bridge lemmas
`streamV1_trainProfile`, `streamV2_trainProfile` assume differentiability explicitly.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.B0190

open Set Filter Topology
open UnforcedLeray.RingLift UnforcedLeray.B0184 UnforcedLeray.B0187 UnforcedLeray.B0185

/-! ## 1. Periodicity in `q` at positive ages -/

/-- A profile `g(q, η, s)` is `c`-periodic in the log-radius `q` at positive ages:
`g(q + c, η, s) = g(q, η, s)` for `s > 0` (the `c`-periodicity of the train, tex 2051, 2141,
on the image `{s > 0}` of the physical domain `r > 0`, `t > 0`). -/
def QPeriodicOn (c : ℝ) (g : ProfilePoint → ℝ) : Prop :=
  ∀ x : ProfilePoint, 0 < x.2.2 → g (x.1 + c, x.2) = g x

/-- The `q`-translate of a profile point is the translate by `(c, 0, 0)`. -/
theorem add_qDir (c : ℝ) (y : ProfilePoint) :
    y + ((c, (0, 0)) : ProfilePoint) = (y.1 + c, y.2) := by
  refine Prod.ext rfl ?_
  simp

/-- The derivative of a profile `c`-periodic at positive ages is `c`-periodic there: the
derivative only sees a neighbourhood, and `{s > 0}` is open. -/
theorem fderiv_shift {c : ℝ} {g : ProfilePoint → ℝ} (hg : QPeriodicOn c g) {x : ProfilePoint}
    (hx : 0 < x.2.2) : fderiv ℝ g (x.1 + c, x.2) = fderiv ℝ g x := by
  have h1 : fderiv ℝ (fun y => g (y + ((c, (0, 0)) : ProfilePoint))) x =
      fderiv ℝ g (x + ((c, (0, 0)) : ProfilePoint)) := fderiv_comp_add_right _
  have h2 : (fun y => g (y + ((c, (0, 0)) : ProfilePoint))) =ᶠ[𝓝 x] g := by
    filter_upwards [isOpen_ageDomain.mem_nhds (show x ∈ ageDomain from hx)] with y hy
    rw [add_qDir]
    exact hg y hy
  rw [← add_qDir, ← h1, h2.fderiv_eq]

theorem partialQ_shift {c : ℝ} {g : ProfilePoint → ℝ} (hg : QPeriodicOn c g) {x : ProfilePoint}
    (hx : 0 < x.2.2) : partialQ g (x.1 + c, x.2) = partialQ g x := by
  simp only [partialQ, fderiv_shift hg hx]

theorem partialEta_shift {c : ℝ} {g : ProfilePoint → ℝ} (hg : QPeriodicOn c g)
    {x : ProfilePoint} (hx : 0 < x.2.2) : partialEta g (x.1 + c, x.2) = partialEta g x := by
  simp only [partialEta, fderiv_shift hg hx]

theorem partialAge_shift {c : ℝ} {g : ProfilePoint → ℝ} (hg : QPeriodicOn c g)
    {x : ProfilePoint} (hx : 0 < x.2.2) : partialAge g (x.1 + c, x.2) = partialAge g x := by
  simp only [partialAge, fderiv_shift hg hx]

theorem ageOperator_shift {c : ℝ} {g : ProfilePoint → ℝ} (hg : QPeriodicOn c g)
    {x : ProfilePoint} (hx : 0 < x.2.2) : ageOperator g (x.1 + c, x.2) = ageOperator g x := by
  simp only [ageOperator, partialEta_shift hg hx, partialAge_shift hg hx]

/-- `v₁ = −∂_ηψ` is `c`-periodic with `ψ`. -/
theorem qPeriodicOn_streamV1 {c : ℝ} {ψ : ProfilePoint → ℝ} (hψ : QPeriodicOn c ψ) :
    QPeriodicOn c (streamV1 ψ) := fun x hx => by
  simp only [streamV1, partialEta_shift hψ hx]

/-- `v₂ = ∂_qψ` is `c`-periodic with `ψ`. -/
theorem qPeriodicOn_streamV2 {c : ℝ} {ψ : ProfilePoint → ℝ} (hψ : QPeriodicOn c ψ) :
    QPeriodicOn c (streamV2 ψ) := fun x hx => by
  simp only [streamV2, partialQ_shift hψ hx]

/-- `H = (1 − K)ψ` is `c`-periodic with `ψ`. -/
theorem qPeriodicOn_ageDefect {c : ℝ} {ψ : ProfilePoint → ℝ} (hψ : QPeriodicOn c ψ) :
    QPeriodicOn c (ageDefect ψ) := fun x hx => by
  simp only [ageDefect, ageOperator_shift hψ hx, hψ x hx]

/-- The axial profile `v₂ + εH` is `c`-periodic with `ψ`. -/
theorem qPeriodicOn_axialProfile (R : ℝ) {c : ℝ} {ψ : ProfilePoint → ℝ}
    (hψ : QPeriodicOn c ψ) : QPeriodicOn c (axialProfile R ψ) := fun x hx => by
  simp only [axialProfile, qPeriodicOn_streamV2 hψ x hx, qPeriodicOn_ageDefect hψ x hx]

/-! ## 2. The dilation of the chart -/

/-- `a_{λr} = a_r/λ` (INF23; tex 2842). -/
theorem radialScale_dilate (R l r : ℝ) : radialScale R (l * r) = l⁻¹ * radialScale R r := by
  simp only [radialScale, div_eq_mul_inv, mul_inv]
  ring

/-- **The dilation `(r, z, t) ↦ (λr, λz, λ²t)` in the chart** (INF23; tex 2842–2843):
`q ↦ q + R log λ`, while `η = a_r z` and `s = a_r² t` are invariant. -/
theorem profileChart_dilate {R l r : ℝ} (hR : R ≠ 0) (hl : 0 < l) (hr : r ≠ 0) (z t : ℝ) :
    profileChart R (l * r) (l * z) (l ^ 2 * t) =
      ((profileChart R r z t).1 + R * Real.log l, (profileChart R r z t).2) := by
  have hl0 : l ≠ 0 := hl.ne'
  have hlog : Real.log (l * r / R) = Real.log l + Real.log (r / R) := by
    rw [mul_div_assoc, Real.log_mul hl0 (div_ne_zero hr hR)]
  simp only [profileChart, logRadius, transverseCoordinate, ageCoordinate, radialScale_dilate,
    hlog]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only
    ring
  · simp only
    field_simp
  · simp only
    field_simp

/-! ## 3. Discrete self-similarity of the lift -/

/-- **DSS of a normalized field** `a_r^k g(q, η, s)` (tex 2916): for a profile `c`-periodic in
`q` and `λ > 0` with `R log λ = c`, `(a^k g)(λr, λz, λ²t) = λ^{-k} (a^k g)(r, z, t)`, `t > 0`. -/
theorem scaledLift_dss_of_log {R c l : ℝ} (hR : R ≠ 0) (hl : 0 < l) (hlc : R * Real.log l = c)
    {k : ℕ} (hk : k ≠ 0) {g : ProfilePoint → ℝ} (hg : QPeriodicOn c g) (r z : ℝ) {t : ℝ}
    (ht : 0 < t) :
    scaledLift R k g (l * r) (l * z) (l ^ 2 * t) = (l ^ k)⁻¹ * scaledLift R k g r z t := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [scaledLift, radialScale, hk]
  · have hs : 0 < (profileChart R r z t).2.2 := by
      have hRr : R / r ≠ 0 := div_ne_zero hR hr
      exact mul_pos (sq_pos_of_ne_zero hRr) ht
    simp only [scaledLift, cylinderLift]
    rw [profileChart_dilate hR hl hr, hlc, hg _ hs, radialScale_dilate, mul_pow, inv_pow]
    ring

/-- `R log e^{c/R} = c`. -/
theorem log_ratio {R : ℝ} (hR : R ≠ 0) (c : ℝ) : R * Real.log (Real.exp (c / R)) = c := by
  rw [Real.log_exp]
  field_simp

/-- **DSS of a normalized field with ratio `λ = e^{c/R}`** (tex 2916). -/
theorem scaledLift_dss {R c : ℝ} (hR : R ≠ 0) {k : ℕ} (hk : k ≠ 0) {g : ProfilePoint → ℝ}
    (hg : QPeriodicOn c g) (r z : ℝ) {t : ℝ} (ht : 0 < t) :
    scaledLift R k g (Real.exp (c / R) * r) (Real.exp (c / R) * z)
        (Real.exp (c / R) ^ 2 * t) =
      (Real.exp (c / R) ^ k)⁻¹ * scaledLift R k g r z t :=
  scaledLift_dss_of_log hR (Real.exp_pos _) (log_ratio hR c) hk hg r z ht

/-- **DSS of `u_r = a_r v₁`** (tex 2855, 2916): `u_r(λr, λz, λ²t) = λ⁻¹ u_r(r, z, t)`. -/
theorem liftUr_dss {R c : ℝ} (hR : R ≠ 0) {ψ : ProfilePoint → ℝ} (hψ : QPeriodicOn c ψ)
    (r z : ℝ) {t : ℝ} (ht : 0 < t) :
    liftUr R ψ (Real.exp (c / R) * r) (Real.exp (c / R) * z) (Real.exp (c / R) ^ 2 * t) =
      (Real.exp (c / R))⁻¹ * liftUr R ψ r z t := by
  have h := scaledLift_dss hR one_ne_zero (qPeriodicOn_streamV1 hψ) r z ht
  rw [pow_one] at h
  exact h

/-- **DSS of `u_z = a_r (v₂ + εH)`** (tex 2856, 2916): `u_z(λr, λz, λ²t) = λ⁻¹ u_z(r, z, t)`. -/
theorem liftUz_dss {R c : ℝ} (hR : R ≠ 0) {ψ : ProfilePoint → ℝ} (hψ : QPeriodicOn c ψ)
    (r z : ℝ) {t : ℝ} (ht : 0 < t) :
    liftUz R ψ (Real.exp (c / R) * r) (Real.exp (c / R) * z) (Real.exp (c / R) ^ 2 * t) =
      (Real.exp (c / R))⁻¹ * liftUz R ψ r z t := by
  have h := scaledLift_dss hR one_ne_zero (qPeriodicOn_axialProfile R hψ) r z ht
  rw [pow_one] at h
  exact h

/-- **DSS of the pressure `p_raw = a_r² p`** (tex 2857, 2916):
`p_raw(λr, λz, λ²t) = λ⁻² p_raw(r, z, t)`. -/
theorem rawPressure_dss {R c : ℝ} (hR : R ≠ 0) {p : ProfilePoint → ℝ} (hp : QPeriodicOn c p)
    (r z : ℝ) {t : ℝ} (ht : 0 < t) :
    rawPressure R p (Real.exp (c / R) * r) (Real.exp (c / R) * z) (Real.exp (c / R) ^ 2 * t) =
      (Real.exp (c / R) ^ 2)⁻¹ * rawPressure R p r z t :=
  scaledLift_dss hR two_ne_zero hp r z ht

theorem ϱ_dilate {l : ℝ} (hl : 0 < l) (y : Space) : Axi.ϱ (l • y) = l * Axi.ϱ y := by
  rw [Axi.ϱ_smul, abs_of_pos hl]

theorem apply_two_dilate (l : ℝ) (y : Space) : (l • y) 2 = l * y 2 := by
  simp

/-- **DSS of the lifted field on `ℝ³`** (tex 2916): the field `u = u_r e_r + u_z e_z`
(B0185's `liftVelocity`) satisfies `u(λx, λ²t) = λ⁻¹ u(x, t)`, `λ = e^{c/R}`, `t > 0`. -/
theorem liftVelocity_dss {R c : ℝ} (hR : R ≠ 0) {ψ : ProfilePoint → ℝ} (hψ : QPeriodicOn c ψ)
    {t : ℝ} (ht : 0 < t) (y : Space) :
    liftVelocity R ψ (Real.exp (c / R) ^ 2 * t) (Real.exp (c / R) • y) =
      (Real.exp (c / R))⁻¹ • liftVelocity R ψ t y := by
  have hl : 0 < Real.exp (c / R) := Real.exp_pos _
  rw [liftVelocity_apply, liftVelocity_apply, ϱ_dilate hl, apply_two_dilate, Axi.eR_smul hl,
    liftUr_dss hR hψ _ _ ht, liftUz_dss hR hψ _ _ ht, smul_add, smul_smul, smul_smul]

/-- **DSS of the pressure on `ℝ³`** (tex 2916): `p_raw(λx, λ²t) = λ⁻² p_raw(x, t)`,
`λ = e^{c/R}`, `t > 0`. -/
theorem liftPressure_dss {R c : ℝ} (hR : R ≠ 0) {p : ProfilePoint → ℝ} (hp : QPeriodicOn c p)
    {t : ℝ} (ht : 0 < t) (y : Space) :
    liftPressure R p (Real.exp (c / R) ^ 2 * t) (Real.exp (c / R) • y) =
      (Real.exp (c / R) ^ 2)⁻¹ * liftPressure R p t y := by
  have hl : 0 < Real.exp (c / R) := Real.exp_pos _
  simp only [liftPressure]
  rw [ϱ_dilate hl, apply_two_dilate, rawPressure_dss hR hp _ _ ht]

/-! ## 4. Similarity time `τ = log t` -/

section Similarity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The similarity profile of a physical field `u(t, x)` of degree `k` (`k = 1` velocity,
`k = 2` pressure): `U(τ, y) = t^{k/2} u(t, √t y)` at `t = e^τ`, i.e. similarity variables
`y = x/√t`, `τ = log t` (tex 2917; B0186, tex 2070–2072). -/
def simProfile (k : ℕ) (u : ℝ → Space → E) (τ : ℝ) (y : Space) : E :=
  Real.exp (τ / 2) ^ k • u (Real.exp τ) (Real.exp (τ / 2) • y)

/-- `e^{(log t)/2} = √t` for `t > 0`. -/
theorem exp_half_log {t : ℝ} (ht : 0 < t) : Real.exp (Real.log t / 2) = √t := by
  rw [← Real.sqrt_sq (Real.exp_pos (Real.log t / 2)).le, sq, ← Real.exp_add, add_halves,
    Real.exp_log ht]

/-- The physical field is recovered from its similarity profile:
`u(t, x) = t^{-k/2} U(log t, x/√t)` for `t > 0` (library `Axi.selfSim`). -/
theorem selfSim_simProfile (k : ℕ) (u : ℝ → Space → E) {t : ℝ} (ht : 0 < t) (x : Space) :
    Axi.selfSim k (simProfile k u) x t = u t x := by
  have hs : 0 < √t := Real.sqrt_pos.2 ht
  rw [Axi.selfSim, simProfile, exp_half_log ht, Real.exp_log ht, smul_smul, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ hs.ne'), one_smul, mul_inv_cancel₀ hs.ne', one_smul]

/-- **DSS is periodicity in similarity time.** If `u(λ²t, λx) = λ^{-k} u(t, x)` for `t > 0`,
then `U(τ + 2 log λ) = U(τ)`. -/
theorem simProfile_periodic (k : ℕ) {u : ℝ → Space → E} {l : ℝ} (hl : 0 < l)
    (hu : ∀ t, 0 < t → ∀ y, u (l ^ 2 * t) (l • y) = (l ^ k)⁻¹ • u t y) (τ : ℝ) :
    simProfile k u (τ + 2 * Real.log l) = simProfile k u τ := by
  funext y
  have h1 : Real.exp (τ + 2 * Real.log l) = l ^ 2 * Real.exp τ := by
    rw [show τ + 2 * Real.log l = Real.log (l ^ 2) + τ by rw [Real.log_pow]; push_cast; ring,
      Real.exp_add, Real.exp_log (pow_pos hl 2)]
  have h2 : Real.exp ((τ + 2 * Real.log l) / 2) = l * Real.exp (τ / 2) := by
    rw [show (τ + 2 * Real.log l) / 2 = Real.log l + τ / 2 by ring, Real.exp_add,
      Real.exp_log hl]
  simp only [simProfile]
  rw [h1, h2, mul_smul l, hu _ (Real.exp_pos τ), smul_smul]
  congr 1
  rw [mul_pow, mul_right_comm, mul_inv_cancel₀ (pow_ne_zero k hl.ne'), one_mul]

/-- `2 log e^{c/R} = 2c/R`. -/
theorem two_log_ratio (c R : ℝ) : 2 * Real.log (Real.exp (c / R)) = 2 * c / R := by
  rw [Real.log_exp]
  ring

end Similarity

/-- **The period in similarity time is `2c/R`** (tex 2917), for the field. -/
theorem simProfile_liftVelocity_periodic {R c : ℝ} (hR : R ≠ 0) {ψ : ProfilePoint → ℝ}
    (hψ : QPeriodicOn c ψ) (τ : ℝ) :
    simProfile 1 (liftVelocity R ψ) (τ + 2 * c / R) = simProfile 1 (liftVelocity R ψ) τ := by
  have h := simProfile_periodic 1 (u := liftVelocity R ψ) (Real.exp_pos (c / R))
    (fun t ht y => by rw [pow_one]; exact liftVelocity_dss hR hψ ht y) τ
  rwa [two_log_ratio] at h

/-- **The period in similarity time is `2c/R`** (tex 2917), for the pressure. -/
theorem simProfile_liftPressure_periodic {R c : ℝ} (hR : R ≠ 0) {p : ProfilePoint → ℝ}
    (hp : QPeriodicOn c p) (τ : ℝ) :
    simProfile 2 (liftPressure R p) (τ + 2 * c / R) = simProfile 2 (liftPressure R p) τ := by
  have h := simProfile_periodic 2 (u := liftPressure R p) (Real.exp_pos (c / R))
    (fun t ht y => by rw [smul_eq_mul]; exact liftPressure_dss hR hp ht y) τ
  rwa [two_log_ratio] at h

/-- The period `2c/R` is the phase period `P = 2εc` of `eq:m3-ring-lift` (tex 2079, B0186). -/
theorem period_eq (R c : ℝ) : 2 * c / R = 2 * ringEps R * c := by
  simp only [ringEps]
  ring

/-- The meridional profile `b(s, (ξ, η)) = (v₁, v₂ + εH)(ξ, η, s)` of the lift, in the
age-first layout of the library ring lift `Axi.Nv` (`U_raw = √s[v₁e_r + (v₂ + εH)e_z]`,
`eq:m3-ring-lift`, tex 2077, unit B0186). -/
def merProfile (R : ℝ) (ψ : ProfilePoint → ℝ) (x : ℝ × (ℝ × ℝ)) : Axi.Merid :=
  streamV1 ψ (x.2.1, (x.2.2, x.1)) • Axi.m0 + axialProfile R ψ (x.2.1, (x.2.2, x.1)) • Axi.m1

/-- Off the axis and for `t > 0`, the B0185 lift is the physical field of the library ring lift
of `merProfile` (`Axi.physNv u = t^{-1/2} N_v b(log t, x/√t)`). -/
theorem liftVelocity_eq_physNv {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (ψ : ProfilePoint → ℝ)
    {x : Space} (hx : x ∉ Axi.axis) :
    liftVelocity R ψ t x = Axi.physNv R (merProfile R ψ) x t := by
  rw [Axi.physNv_eq hR ht _ hx, liftVelocity_apply, Axi.frameL_apply, liftUr_apply,
    liftUz_apply]
  simp only [merProfile, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Axi.m0_zero,
    Axi.m0_one, Axi.m1_zero, Axi.m1_one, mul_one, mul_zero, add_zero, zero_add, smul_add,
    smul_smul]
  rfl

theorem not_mem_axis_smul {l : ℝ} (hl : 0 < l) {y : Space} (hy : y ∉ Axi.axis) :
    l • y ∉ Axi.axis := by
  rw [Axi.mem_axis_iff, ϱ_dilate hl]
  exact mul_ne_zero hl.ne' (Axi.ϱ_ne_zero hy)

/-- **The similarity profile of the lift is the ring lift `U_raw = N_v b`** (B0186): off the
axis, `√t u(√t y, t) = N_v b(τ, y)` at `t = e^τ`, `b = merProfile R ψ`. -/
theorem simProfile_liftVelocity_eq_Nv {R : ℝ} (hR : 0 < R) (ψ : ProfilePoint → ℝ) (τ : ℝ)
    {y : Space} (hy : y ∉ Axi.axis) :
    simProfile 1 (liftVelocity R ψ) τ y = Axi.Nv R (merProfile R ψ) τ y := by
  have he : 0 < Real.exp (τ / 2) := Real.exp_pos _
  have hsq : √(Real.exp τ) = Real.exp (τ / 2) := by
    rw [← exp_half_log (Real.exp_pos τ), Real.log_exp]
  rw [simProfile, liftVelocity_eq_physNv hR (Real.exp_pos τ) ψ (not_mem_axis_smul he hy),
    Axi.physNv, Axi.selfSim, hsq, Real.log_exp, pow_one, smul_smul, smul_smul,
    mul_inv_cancel₀ he.ne', one_smul, inv_mul_cancel₀ he.ne', one_smul]

/-- **`U_raw` has period `2c/R = 2εc` in similarity time** (tex 2917, 2079): off the axis,
`N_v b(τ + 2c/R, y) = N_v b(τ, y)` for the lift of a `c`-periodic stream. -/
theorem Nv_merProfile_periodic {R c : ℝ} (hR : 0 < R) {ψ : ProfilePoint → ℝ}
    (hψ : QPeriodicOn c ψ) (τ : ℝ) {y : Space} (hy : y ∉ Axi.axis) :
    Axi.Nv R (merProfile R ψ) (τ + 2 * c / R) y = Axi.Nv R (merProfile R ψ) τ y := by
  rw [← simProfile_liftVelocity_eq_Nv hR ψ _ hy, ← simProfile_liftVelocity_eq_Nv hR ψ _ hy,
    simProfile_liftVelocity_periodic hR.ne' hψ]

/-! ## 5. The train -/

/-- A train field `f(s, (q, η))` (B0140's layout, `Units/B0140.lean`) as a profile on
B0184's profile space `(q, (η, s))`. -/
def trainProfile (f : ℝ → ℝ × ℝ → ℝ) (x : ProfilePoint) : ℝ := f x.2.2 (x.1, x.2.1)

/-- The decaying stream of the train is `c`-periodic in `q` (tex 2049–2051; proved in
`Cons/C03Background/RawLift.lean`, `stream_periodic_of_isTrain`). -/
theorem qPeriodicOn_trainStream {ν c : ℝ} (T : B0140.TrainSol ν c) :
    QPeriodicOn c (trainProfile T.ψ) := fun x hx =>
  Cons.C03.stream_periodic_of_isTrain T.isTrain hx.le (x.1, x.2.1)

/-- The train pressure is `c`-periodic in `q` (tex 2051, `IsTrain.periodic_p`). -/
theorem qPeriodicOn_trainPressure {ν c : ℝ} (T : B0140.TrainSol ν c) :
    QPeriodicOn c (trainProfile T.p) := fun x hx =>
  T.isTrain.periodic_p x.2.2 hx.le (x.1, x.2.1)

/-- The train velocity components are `c`-periodic in `q` (tex 2051, `IsTrain.periodic_v`). -/
theorem qPeriodicOn_trainVelocity {ν c : ℝ} (T : B0140.TrainSol ν c) (i : Fin 2) :
    QPeriodicOn c (trainProfile fun s z => T.v s z i) := fun x hx => by
  simp only [trainProfile]
  rw [T.isTrain.periodic_v x.2.2 hx.le (x.1, x.2.1)]

/-- B0185's `v₁ = −∂_ηψ` of the train stream is the train's first component wherever the
stream is differentiable (tex 2049: `v = ∇^⊥ψ`). -/
theorem streamV1_trainProfile {ν c : ℝ} (T : B0140.TrainSol ν c) {x : ProfilePoint}
    (hx : 0 ≤ x.2.2) (hd : DifferentiableAt ℝ (trainProfile T.ψ) x) :
    streamV1 (trainProfile T.ψ) x = T.v x.2.2 (x.1, x.2.1) 0 := by
  have hline : HasDerivAt (fun e : ℝ => ((x.1, (e, x.2.2)) : ProfilePoint)) eηDir x.2.1 :=
    (hasDerivAt_const _ _).prodMk ((hasDerivAt_id _).prodMk (hasDerivAt_const _ _))
  have h1 := hd.hasFDerivAt.comp_hasDerivAt x.2.1 hline
  have hY : GaussianVortex.partialY (T.ψ x.2.2) (x.1, x.2.1) = -(T.v x.2.2 (x.1, x.2.1) 0) := by
    rw [T.isTrain.stream x.2.2 hx (x.1, x.2.1)]
    exact (neg_neg _).symm
  rw [streamV1, partialEta, ← h1.deriv]
  rw [show GaussianVortex.partialY (T.ψ x.2.2) (x.1, x.2.1) =
    deriv (trainProfile T.ψ ∘ fun e : ℝ => ((x.1, (e, x.2.2)) : ProfilePoint)) x.2.1
    from rfl] at hY
  rw [hY, neg_neg]

/-- B0185's `v₂ = ∂_qψ` of the train stream is the train's second component wherever the
stream is differentiable (tex 2049: `v = ∇^⊥ψ`). -/
theorem streamV2_trainProfile {ν c : ℝ} (T : B0140.TrainSol ν c) {x : ProfilePoint}
    (hx : 0 ≤ x.2.2) (hd : DifferentiableAt ℝ (trainProfile T.ψ) x) :
    streamV2 (trainProfile T.ψ) x = T.v x.2.2 (x.1, x.2.1) 1 := by
  have hline : HasDerivAt (fun e : ℝ => ((e, (x.2.1, x.2.2)) : ProfilePoint)) eqDir x.1 :=
    (hasDerivAt_id _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_const _ _))
  have h1 := hd.hasFDerivAt.comp_hasDerivAt x.1 hline
  have hX : GaussianVortex.partialX (T.ψ x.2.2) (x.1, x.2.1) = T.v x.2.2 (x.1, x.2.1) 1 := by
    rw [T.isTrain.stream x.2.2 hx (x.1, x.2.1)]
    rfl
  rw [streamV2, partialQ, ← h1.deriv]
  rw [show GaussianVortex.partialX (T.ψ x.2.2) (x.1, x.2.1) =
    deriv (trainProfile T.ψ ∘ fun e : ℝ => ((e, (x.2.1, x.2.2)) : ProfilePoint)) x.1
    from rfl] at hX
  exact hX

/-! ## 6. The whole unit -/

/-- **Unit B0190** (tex 2916–2917, with the lift of tex 2838–2857). Let `R ≥ 2` and let
`T = (v, p, ψ)` be a train of period `c` (B0140). Put `ψ̃(q, η, s) = ψ(s, (q, η))`,
`p̃(q, η, s) = p(s, (q, η))` and `λ = e^{c/R}`. The lift of B0185 — `u_r = a_r v₁`,
`u_z = a_r (v₂ + εH)`, the Cartesian field `u = u_r e_r + u_z e_z` on `ℝ³`, and the pressure
`p_raw = a_r² p` — obeys the DSS scaling with ratio `λ`:
`u(λx, λ²t) = λ⁻¹ u(x, t)`, `p_raw(λx, λ²t) = λ⁻² p_raw(x, t)` for `t > 0`; in similarity time
`τ = log t` the similarity profiles `√t u(√t y, t)` and `t p_raw(√t y, t)` have period `2c/R`,
which is `P = 2εc`; off the axis the velocity profile is the ring lift `U_raw = N_v b` of B0186
(library `Axi.Nv`), so `U_raw(τ + 2c/R) = U_raw(τ)`. -/
theorem unit_B0190 {ν c R : ℝ} (hR : 2 ≤ R) (T : B0140.TrainSol ν c) :
    -- cylindrical components (tex 2855–2857)
    (∀ r z t : ℝ, 0 < t →
      liftUr R (trainProfile T.ψ) (Real.exp (c / R) * r) (Real.exp (c / R) * z)
          (Real.exp (c / R) ^ 2 * t) =
        (Real.exp (c / R))⁻¹ * liftUr R (trainProfile T.ψ) r z t) ∧
    (∀ r z t : ℝ, 0 < t →
      liftUz R (trainProfile T.ψ) (Real.exp (c / R) * r) (Real.exp (c / R) * z)
          (Real.exp (c / R) ^ 2 * t) =
        (Real.exp (c / R))⁻¹ * liftUz R (trainProfile T.ψ) r z t) ∧
    (∀ r z t : ℝ, 0 < t →
      rawPressure R (trainProfile T.p) (Real.exp (c / R) * r) (Real.exp (c / R) * z)
          (Real.exp (c / R) ^ 2 * t) =
        (Real.exp (c / R) ^ 2)⁻¹ * rawPressure R (trainProfile T.p) r z t) ∧
    -- the field and its pressure on `ℝ³` (tex 2916)
    (∀ t : ℝ, 0 < t → ∀ y : Space,
      liftVelocity R (trainProfile T.ψ) (Real.exp (c / R) ^ 2 * t) (Real.exp (c / R) • y) =
        (Real.exp (c / R))⁻¹ • liftVelocity R (trainProfile T.ψ) t y) ∧
    (∀ t : ℝ, 0 < t → ∀ y : Space,
      liftPressure R (trainProfile T.p) (Real.exp (c / R) ^ 2 * t) (Real.exp (c / R) • y) =
        (Real.exp (c / R) ^ 2)⁻¹ * liftPressure R (trainProfile T.p) t y) ∧
    -- similarity time `τ = log t`: period `2c/R = 2εc` (tex 2917)
    (∀ τ : ℝ, simProfile 1 (liftVelocity R (trainProfile T.ψ)) (τ + 2 * c / R) =
      simProfile 1 (liftVelocity R (trainProfile T.ψ)) τ) ∧
    (∀ τ : ℝ, simProfile 2 (liftPressure R (trainProfile T.p)) (τ + 2 * c / R) =
      simProfile 2 (liftPressure R (trainProfile T.p)) τ) ∧
    2 * c / R = 2 * ringEps R * c ∧
    (∀ τ : ℝ, ∀ y : Space, y ∉ Axi.axis →
      simProfile 1 (liftVelocity R (trainProfile T.ψ)) τ y =
        Axi.Nv R (merProfile R (trainProfile T.ψ)) τ y ∧
      Axi.Nv R (merProfile R (trainProfile T.ψ)) (τ + 2 * c / R) y =
        Axi.Nv R (merProfile R (trainProfile T.ψ)) τ y) := by
  have hR0 : 0 < R := by linarith
  have hψ := qPeriodicOn_trainStream T
  have hp := qPeriodicOn_trainPressure T
  exact ⟨fun r z _ ht => liftUr_dss hR0.ne' hψ r z ht,
    fun r z _ ht => liftUz_dss hR0.ne' hψ r z ht,
    fun r z _ ht => rawPressure_dss hR0.ne' hp r z ht,
    fun _ ht y => liftVelocity_dss hR0.ne' hψ ht y,
    fun _ ht y => liftPressure_dss hR0.ne' hp ht y,
    simProfile_liftVelocity_periodic hR0.ne' hψ,
    simProfile_liftPressure_periodic hR0.ne' hp,
    period_eq R c,
    fun τ _ hy => ⟨simProfile_liftVelocity_eq_Nv hR0 _ τ hy,
      Nv_merProfile_periodic hR0 hψ τ hy⟩⟩

end UnforcedLeray.B0190
