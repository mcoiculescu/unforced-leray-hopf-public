import UnforcedLeray.Short.PartIIa.StatementsRing
import UnforcedLeray.Lib.AxisymmetricB.DSS

/-!


Target: `ringResidual_eq_chart` (`Short/PartII-a/Tasks/R03ResidualChart.lean`). The chart point
`(phase, trans, age)` of the target is the explicit def `chartPtR03`; `!=` is read as `≠`, and
`Axi.rho` as `Axi.ϱ`.

Source: `the November 2 reference manuscript`, lines 1252-1263 (the physical
residual is `(R/r)^3 r`, and `F_R = s^{3/2} r`).

Mathematical content. With `e = exp(τ/2)`, the point `e • y` has `ϱ = e ϱ(y)`, `z = e y₃`, and
time `t = e^τ`. The chart of `(e ϱ(y), e y₃, e^τ)` is `(phase, trans, age)` of `y`, and
`e^{3} (R/(e ϱ))^3 = (R/ϱ)^3 = age^{3/2}`. The B0187 identity (`cylindricalResidual_eq_chart`)
needs `ψ` of class `C³` on all of `ℝ³`, but the target only gives `ContDiffAt` at the chart
point. So this file re-proves the B0187 identities pointwise, using only the germ of the profile
at the chart point (`eventually` arguments along the physical coordinate lines). The statements
are the B0187 ones with local hypotheses; nothing here is an assumption.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.RingLift UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187
  UnforcedLeray.B0188 UnforcedLeray.B0190

/-- The chart point of the target `ringResidual_eq_chart`: `(q, (η, s)) = (phase, (trans, age))`
at phase time `τ` (`Lib/Axisymmetric/RingChart.lean`). -/
def chartPtR03 (R tau : ℝ) (y : Space) : ProfilePoint :=
  (Axi.phase R tau y, (Axi.trans R y, Axi.age R y))

/-- The auxiliary profile `D_ε f − ε f` of B0187's second radial derivative (`k = 1`). -/
def ringResAux (R : ℝ) (f : ProfilePoint → ℝ) : ProfilePoint → ℝ :=
  fun X => ringD R f X - ((1 : ℕ) : ℝ) * ringEps R * f X

/-! ### Derivatives of profiles at a point -/

/-- `∂_v ψ` is `C²` at a point where `ψ` is `C³`. -/
theorem r03_fderiv_c2 {ψ : ProfilePoint → ℝ} {y : ProfilePoint} (hy : ContDiffAt ℝ 3 ψ y)
    (v : ProfilePoint) : ContDiffAt ℝ 2 (fun x => fderiv ℝ ψ x v) y :=
  (hy.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const

/-- `∂_v ψ` is `C¹` at a point where `ψ` is `C²`. -/
theorem r03_fderiv_c1 {ψ : ProfilePoint → ℝ} {y : ProfilePoint} (hy : ContDiffAt ℝ 2 ψ y)
    (v : ProfilePoint) : ContDiffAt ℝ 1 (fun x => fderiv ℝ ψ x v) y :=
  (hy.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const

/-- The stream component `v₁ = -∂_η ψ` is `C²` where `ψ` is `C³`. -/
theorem r03_streamV1_contDiffAt {ψ : ProfilePoint → ℝ} {y : ProfilePoint}
    (hy : ContDiffAt ℝ 3 ψ y) : ContDiffAt ℝ 2 (streamV1 ψ) y :=
  (r03_fderiv_c2 hy eηDir).neg

/-- The normalized axial profile `v₂ + εH` is `C²` where `ψ` is `C³`. -/
theorem r03_axialProfile_contDiffAt (R : ℝ) {ψ : ProfilePoint → ℝ} {y : ProfilePoint}
    (hy : ContDiffAt ℝ 3 ψ y) : ContDiffAt ℝ 2 (axialProfile R ψ) y := by
  have hQ := r03_fderiv_c2 hy eqDir
  have hE := r03_fderiv_c2 hy eηDir
  have hA := r03_fderiv_c2 hy esDir
  have hψ2 : ContDiffAt ℝ 2 ψ y := hy.of_le (by norm_num)
  unfold axialProfile streamV2 ageDefect ageOperator partialQ partialEta partialAge
  fun_prop

/-- `D_ε f` is differentiable at a point where `f` is `C²`. -/
theorem r03_differentiableAt_ringD (R : ℝ) {f : ProfilePoint → ℝ} {x : ProfilePoint}
    (hf : ContDiffAt ℝ 2 f x) : DifferentiableAt ℝ (ringD R f) x := by
  have hQ : DifferentiableAt ℝ (fun y => fderiv ℝ f y eqDir) x :=
    (r03_fderiv_c1 hf eqDir).differentiableAt (by norm_num)
  have hE : DifferentiableAt ℝ (fun y => fderiv ℝ f y eηDir) x :=
    (r03_fderiv_c1 hf eηDir).differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ (fun y => fderiv ℝ f y esDir) x :=
    (r03_fderiv_c1 hf esDir).differentiableAt (by norm_num)
  unfold ringD ageOperator partialQ partialEta partialAge
  fun_prop

/-! ### Pointwise first derivatives of normalized fields (B0187 rules, with `k` explicit) -/

theorem r03_physR_scaledLift (R : ℝ) (k : ℕ) (g : ProfilePoint → ℝ) {r z t : ℝ}
    (hR0 : R ≠ 0) (hr0 : r ≠ 0) (hg : DifferentiableAt ℝ g (profileChart R r z t)) :
    physR (scaledLift R k g) r z t =
      radialScale R r ^ (k + 1) * (ringD R g (profileChart R r z t) -
        (k : ℝ) * ringEps R * g (profileChart R r z t)) :=
  (hasDerivAt_scaledLift_radial R k g r z t hR0 hr0 hg).deriv

theorem r03_physZ_scaledLift (R : ℝ) (k : ℕ) (g : ProfilePoint → ℝ) {r z t : ℝ}
    (hg : DifferentiableAt ℝ g (profileChart R r z t)) :
    physZ (scaledLift R k g) r z t =
      radialScale R r ^ (k + 1) * partialEta g (profileChart R r z t) :=
  (hasDerivAt_scaledLift_axial R k g r z t hg).deriv

theorem r03_physT_scaledLift (R : ℝ) (k : ℕ) (g : ProfilePoint → ℝ) {r z t : ℝ}
    (hg : DifferentiableAt ℝ g (profileChart R r z t)) :
    physT (scaledLift R k g) r z t =
      radialScale R r ^ (k + 2) * partialAge g (profileChart R r z t) :=
  (hasDerivAt_scaledLift_time R k g r z t hg).deriv

/-! ### Second derivatives, via the germ of the profile along the coordinate line -/

/-- `∂_r² (a_r f) = a_r³ (D_ε² − 3ε D_ε + 2ε²) f` at a chart point, from `C²` near it
(pointwise form of B0187's `physR_physR_velocity`). -/
theorem r03_physR_physR (R : ℝ) (f : ProfilePoint → ℝ) {r z t : ℝ} (hR0 : R ≠ 0)
    (hr0 : r ≠ 0) (hfE : ∀ᶠ y in 𝓝 (profileChart R r z t), ContDiffAt ℝ 2 f y) :
    physR (physR (scaledLift R 1 f)) r z t =
      radialScale R r ^ 3 * (ringD R (ringD R f) (profileChart R r z t) -
        3 * ringEps R * ringD R f (profileChart R r z t) +
        2 * ringEps R ^ 2 * f (profileChart R r z t)) := by
  have hfx : ContDiffAt ℝ 2 f (profileChart R r z t) := hfE.self_of_nhds
  have hDf : DifferentiableAt ℝ f (profileChart R r z t) := hfx.differentiableAt (by norm_num)
  have hDR : DifferentiableAt ℝ (ringD R f) (profileChart R r z t) :=
    r03_differentiableAt_ringD R hfx
  have hcont : ContinuousAt (fun x => profileChart R x z t) r :=
    (hasDerivAt_profileChart_radial R r z t hR0 hr0).continuousAt
  have hC : ∀ᶠ x in 𝓝 r, ContDiffAt ℝ 2 f (profileChart R x z t) :=
    hcont.tendsto.eventually hfE
  have hA : (fun x => physR (scaledLift R 1 f) x z t) =ᶠ[𝓝 r]
      (fun x => scaledLift R 2 (ringResAux R f) x z t) := by
    filter_upwards [hC, eventually_ne_nhds hr0] with x hCx hx
    have hD : DifferentiableAt ℝ f (profileChart R x z t) := hCx.differentiableAt (by norm_num)
    rw [r03_physR_scaledLift R 1 f hR0 hx hD]
    simp only [scaledLift, cylinderLift, ringResAux, Nat.cast_one]
  have hg1 : DifferentiableAt ℝ (ringResAux R f) (profileChart R r z t) :=
    hDR.sub (hDf.const_mul (((1 : ℕ) : ℝ) * ringEps R))
  have h2 : physR (physR (scaledLift R 1 f)) r z t =
      deriv (fun x => scaledLift R 2 (ringResAux R f) x z t) r := by
    unfold physR
    exact hA.deriv_eq
  rw [h2, (hasDerivAt_scaledLift_radial R 2 (ringResAux R f) r z t hR0 hr0 hg1).deriv]
  have hlin : ringD R (ringResAux R f) (profileChart R r z t) =
      ringD R (ringD R f) (profileChart R r z t) -
        (((1 : ℕ) : ℝ) * ringEps R) * ringD R f (profileChart R r z t) :=
    ringD_sub_mul R (((1 : ℕ) : ℝ) * ringEps R) hDR hDf
  rw [hlin]
  simp only [ringResAux, Nat.cast_one, Nat.cast_ofNat]
  ring

/-- `∂_z² (a_r h) = a_r³ ∂_η² h` at a chart point, from `C²` near it. -/
theorem r03_physZ_physZ (R : ℝ) (h : ProfilePoint → ℝ) {r z t : ℝ}
    (hhE : ∀ᶠ y in 𝓝 (profileChart R r z t), ContDiffAt ℝ 2 h y) :
    physZ (physZ (scaledLift R 1 h)) r z t =
      radialScale R r ^ 3 * partialEta (partialEta h) (profileChart R r z t) := by
  have hhx : ContDiffAt ℝ 2 h (profileChart R r z t) := hhE.self_of_nhds
  have hDE : DifferentiableAt ℝ (partialEta h) (profileChart R r z t) :=
    (r03_fderiv_c1 hhx eηDir).differentiableAt (by norm_num)
  have hcont : ContinuousAt (fun y => profileChart R r y t) z :=
    (hasDerivAt_profileChart_axial R r z t).continuousAt
  have hC : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 h (profileChart R r y t) :=
    hcont.tendsto.eventually hhE
  have hA : (fun y => physZ (scaledLift R 1 h) r y t) =ᶠ[𝓝 z]
      (fun y => scaledLift R 2 (partialEta h) r y t) := by
    filter_upwards [hC] with y hCy
    rw [r03_physZ_scaledLift R 1 h (hCy.differentiableAt (by norm_num))]
    simp only [scaledLift, cylinderLift]
  have h2 : physZ (physZ (scaledLift R 1 h)) r z t =
      deriv (fun y => scaledLift R 2 (partialEta h) r y t) z := by
    unfold physZ
    exact hA.deriv_eq
  rw [h2, (hasDerivAt_scaledLift_axial R 2 (partialEta h) r z t hDE).deriv]

/-! ### The two residual lines, pointwise (B0187 `cylindricalResidual_eq_chart`, local form) -/

/-- Radial line: `cyl_radial(a_r f, a_r h, a_r² p) = a_r³ · chart_radial(f, h, p)` at a chart
point, with `f` of class `C²` near the point and `p` differentiable there. -/
theorem r03_cylRadial (R ν : ℝ) {r z t : ℝ} (hR0 : R ≠ 0) (hr0 : r ≠ 0)
    (f h p : ProfilePoint → ℝ)
    (hfE : ∀ᶠ y in 𝓝 (profileChart R r z t), ContDiffAt ℝ 2 f y)
    (hp : DifferentiableAt ℝ p (profileChart R r z t)) :
    cylRadialResidual ν (scaledLift R 1 f) (scaledLift R 1 h) (scaledLift R 2 p) r z t =
      radialScale R r ^ 3 * chartRadialResidual R ν f h p (profileChart R r z t) := by
  have hfx : ContDiffAt ℝ 2 f (profileChart R r z t) := hfE.self_of_nhds
  have hD : DifferentiableAt ℝ f (profileChart R r z t) := hfx.differentiableAt (by norm_num)
  have hT := r03_physT_scaledLift R 1 f hD
  have hRf := r03_physR_scaledLift R 1 f hR0 hr0 hD
  have hZf := r03_physZ_scaledLift R 1 f hD
  have hLap := r03_physR_physR R f hR0 hr0 hfE
  have hLapZ := r03_physZ_physZ R f hfE
  have hRp := r03_physR_scaledLift R 2 p hR0 hr0 hp
  have hd1 : ∀ x : ℝ, x / r = x * (ringEps R * radialScale R r) := fun x => by
    rw [div_eq_mul_one_div, inv_radius_eq R r hR0 hr0]
  have hd2 : ∀ x : ℝ, x / r ^ 2 = x * (ringEps R * radialScale R r) ^ 2 := fun x => by
    rw [div_eq_mul_one_div, ← one_div_pow, inv_radius_eq R r hR0 hr0]
  unfold cylRadialResidual radialVectorLaplacian
  rw [hT, hLap, hRf, hLapZ, hZf, hRp]
  simp only [hd1, hd2, scaledLift, cylinderLift, chartRadialResidual, ringDiffusionRadial,
    Nat.cast_one, Nat.cast_ofNat]
  ring

/-- Axial line: `cyl_axial(a_r f, a_r h, a_r² p) = a_r³ · chart_axial(f, h, p)` at a chart
point, with `h` of class `C²` near the point and `p` differentiable there. -/
theorem r03_cylAxial (R ν : ℝ) {r z t : ℝ} (hR0 : R ≠ 0) (hr0 : r ≠ 0)
    (f h p : ProfilePoint → ℝ)
    (hhE : ∀ᶠ y in 𝓝 (profileChart R r z t), ContDiffAt ℝ 2 h y)
    (hp : DifferentiableAt ℝ p (profileChart R r z t)) :
    cylAxialResidual ν (scaledLift R 1 f) (scaledLift R 1 h) (scaledLift R 2 p) r z t =
      radialScale R r ^ 3 * chartAxialResidual R ν f h p (profileChart R r z t) := by
  have hhx : ContDiffAt ℝ 2 h (profileChart R r z t) := hhE.self_of_nhds
  have hD : DifferentiableAt ℝ h (profileChart R r z t) := hhx.differentiableAt (by norm_num)
  have hT := r03_physT_scaledLift R 1 h hD
  have hRh := r03_physR_scaledLift R 1 h hR0 hr0 hD
  have hZh := r03_physZ_scaledLift R 1 h hD
  have hLap := r03_physR_physR R h hR0 hr0 hhE
  have hLapZ := r03_physZ_physZ R h hhE
  have hZp := r03_physZ_scaledLift R 2 p hp
  have hd1 : ∀ x : ℝ, x / r = x * (ringEps R * radialScale R r) := fun x => by
    rw [div_eq_mul_one_div, inv_radius_eq R r hR0 hr0]
  unfold cylAxialResidual axialVectorLaplacian
  rw [hT, hLap, hRh, hLapZ, hZh, hZp]
  simp only [hd1, scaledLift, cylinderLift, chartAxialResidual, ringDiffusionAxial,
    Nat.cast_one]
  ring

/-- The two residual lines for the lift `(liftUr, liftUz, rawPressure)` of a profile `ψ` and
pressure `p`, at a point `(r, z, t)` with `r ≠ 0` where `ψ` is `C³` and `p` is `C¹`. -/
theorem r03_scalar (R ν : ℝ) {r z t : ℝ} (hR0 : R ≠ 0) (hr0 : r ≠ 0)
    (ψ p : ProfilePoint → ℝ)
    (hψ : ContDiffAt ℝ 3 ψ (profileChart R r z t))
    (hp : ContDiffAt ℝ 1 p (profileChart R r z t)) :
    cylRadialResidual ν (liftUr R ψ) (liftUz R ψ) (rawPressure R p) r z t =
        radialScale R r ^ 3 * chartRadialResidual R ν (streamV1 ψ) (axialProfile R ψ) p
          (profileChart R r z t) ∧
    cylAxialResidual ν (liftUr R ψ) (liftUz R ψ) (rawPressure R p) r z t =
        radialScale R r ^ 3 * chartAxialResidual R ν (streamV1 ψ) (axialProfile R ψ) p
          (profileChart R r z t) := by
  have hψE : ∀ᶠ y in 𝓝 (profileChart R r z t), ContDiffAt ℝ 3 ψ y :=
    hψ.eventually (by norm_num)
  have hfE : ∀ᶠ y in 𝓝 (profileChart R r z t), ContDiffAt ℝ 2 (streamV1 ψ) y :=
    hψE.mono fun y hy => r03_streamV1_contDiffAt hy
  have hhE : ∀ᶠ y in 𝓝 (profileChart R r z t), ContDiffAt ℝ 2 (axialProfile R ψ) y :=
    hψE.mono fun y hy => r03_axialProfile_contDiffAt R hy
  have hpD : DifferentiableAt ℝ p (profileChart R r z t) := hp.differentiableAt (by norm_num)
  exact ⟨r03_cylRadial R ν hR0 hr0 (streamV1 ψ) (axialProfile R ψ) p hfE hpD,
    r03_cylAxial R ν hR0 hr0 (streamV1 ψ) (axialProfile R ψ) p hhE hpD⟩

/-! ### The physical chart of the similarity point -/

/-- The physical ring chart of `(e ϱ(y), e y₃, e^τ)`, `e = exp(τ/2)`, is the chart point
`(phase, trans, age)` of `y` (target line 1263; `Lib/Axisymmetric/RingChart.lean`). -/
theorem r03_profileChart_chartPt (R tau : ℝ) (y : Space) (hR0 : R ≠ 0) (hϱ : Axi.ϱ y ≠ 0) :
    profileChart R (Real.exp (tau / 2) * Axi.ϱ y) (Real.exp (tau / 2) * y 2) (Real.exp tau) =
      chartPtR03 R tau y := by
  have he : Real.exp (tau / 2) ≠ 0 := (Real.exp_pos _).ne'
  have hE : Real.exp tau = Real.exp (tau / 2) * Real.exp (tau / 2) := by
    rw [← Real.exp_add]
    ring_nf
  have hlog1 : Real.log (Real.exp (tau / 2) * Axi.ϱ y / R) =
      tau / 2 + (Real.log (Axi.ϱ y) - Real.log R) := by
    rw [Real.log_div (mul_ne_zero he hϱ) hR0, Real.log_mul he hϱ, Real.log_exp]
    ring
  have hlog2 : Real.log (R ^ 2 / Axi.ϱ y ^ 2) = 2 * (Real.log R - Real.log (Axi.ϱ y)) := by
    rw [Real.log_div (pow_ne_zero 2 hR0) (pow_ne_zero 2 hϱ), Real.log_pow, Real.log_pow]
    push_cast
    ring
  unfold profileChart chartPtR03 logRadius transverseCoordinate ageCoordinate radialScale
    Axi.phase Axi.trans Axi.age
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only
    rw [hlog1, hlog2]
    ring
  · simp only
    field_simp
  · simp only
    rw [hE]
    field_simp

/-! ### Main theorem -/

/-- **Target `PartII-a:R03`** (`Short/PartII-a/StatementsRing.lean`, lines 1252-1263): the
similarity residual of the ring lift is `s^{3/2}` times the chart residual at `(phase, trans, age)`,
with `R ≥ 2`, `ϱ(y) ≠ 0`, `ψ` of class `C³` and `p` of class `C¹` at the chart point. -/
theorem ringResidual_eq_chart (R nu : Real) (hR : 2 <= R) (psi p : ProfilePoint -> Real)
    (tau : Real) (y : Space) (hy : Axi.ϱ y ≠ 0)
    (hpsi : ContDiffAt Real 3 psi (chartPtR03 R tau y))
    (hp : ContDiffAt Real 1 p (chartPtR03 R tau y)) :
    ringResidual R nu psi p tau y =
      (Axi.age R y) ^ (3 / 2 : Real) •
        (chartRadialResidual R nu (streamV1 psi) (axialProfile R psi) p (chartPtR03 R tau y) •
            Axi.eR y +
          chartAxialResidual R nu (streamV1 psi) (axialProfile R psi) p (chartPtR03 R tau y) •
            Axi.e3) := by
  have hR0 : R ≠ 0 := ne_of_gt (by linarith)
  have hϱpos : 0 < Axi.ϱ y :=
    lt_of_le_of_ne (by unfold Axi.ϱ; exact Real.sqrt_nonneg _) (Ne.symm hy)
  have he : 0 < Real.exp (tau / 2) := Real.exp_pos _
  have hϱX : Axi.ϱ (Real.exp (tau / 2) • y) = Real.exp (tau / 2) * Axi.ϱ y := by
    rw [Axi.ϱ_smul, abs_of_pos he]
  have hX2 : (Real.exp (tau / 2) • y) 2 = Real.exp (tau / 2) * y 2 := by
    simp [PiLp.smul_apply, smul_eq_mul]
  have hEReR : Axi.eR (Real.exp (tau / 2) • y) = Axi.eR y := Axi.eR_smul he y
  have hr0 : Real.exp (tau / 2) * Axi.ϱ y ≠ 0 := mul_ne_zero he.ne' hy
  have hpt := r03_profileChart_chartPt R tau y hR0 hy
  have hψ' : ContDiffAt ℝ 3 psi
      (profileChart R (Real.exp (tau / 2) * Axi.ϱ y) (Real.exp (tau / 2) * y 2)
        (Real.exp tau)) := by
    rw [hpt]
    exact hpsi
  have hp' : ContDiffAt ℝ 1 p
      (profileChart R (Real.exp (tau / 2) * Axi.ϱ y) (Real.exp (tau / 2) * y 2)
        (Real.exp tau)) := by
    rw [hpt]
    exact hp
  obtain ⟨h1, h2⟩ := r03_scalar R nu hR0 hr0 psi p hψ' hp'
  rw [hpt] at h1 h2
  have hage : (Axi.age R y) ^ (3 / 2 : ℝ) = (R / Axi.ϱ y) ^ 3 := by
    have hx : 0 ≤ R / Axi.ϱ y := div_nonneg (by linarith) hϱpos.le
    have hA : Axi.age R y = (R / Axi.ϱ y) ^ (2 : ℝ) := by
      unfold Axi.age
      rw [Real.rpow_two, div_pow]
    rw [hA, ← Real.rpow_mul hx]
    rw [show (2 : ℝ) * (3 / 2) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have key : Real.exp (tau / 2) ^ 3 *
      radialScale R (Real.exp (tau / 2) * Axi.ϱ y) ^ 3 = (R / Axi.ϱ y) ^ 3 := by
    unfold radialScale
    field_simp
  have hsc : ∀ c : ℝ, Real.exp (tau / 2) ^ 3 *
      (radialScale R (Real.exp (tau / 2) * Axi.ϱ y) ^ 3 * c) =
        (Axi.age R y) ^ (3 / 2 : ℝ) * c := by
    intro c
    rw [hage, ← key]
    ring
  simp only [ringResidual, physResidualField]
  rw [hϱX, hX2, hEReR, h1, h2]
  simp only [smul_add, smul_smul, hsc]

end UnforcedLeray.Short.PartIIa
