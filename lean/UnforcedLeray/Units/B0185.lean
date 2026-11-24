import UnforcedLeray.Units.B0187
import UnforcedLeray.Lib.AxisymmetricB.Stream

/-!
# B0185 `eq:st18-t00188` (with `eq:st18-t00189`): physical stream, lift velocity, raw pressure
and exact solenoidality

Blueprint unit B0185, labels `eq:st18-t00188` and `eq:st18-t00189`, `paper/main.tex`
lines 2851–2865 (subsection "Coordinates and equations" of the exact solenoidal lift).

Statement in words (tex lines 2851–2865). Let `R ≥ 2`, `ε = R⁻¹`, and use the physical ring
chart `a_r = R/r`, `q = R log(r/R)`, `η = a_r z`, `s = a_r² t`, `D_ε = ∂_q − εK` of

`K = η∂_η + 2s∂_s` and `H = (1 − K)ψ` (tex line 2805). For the stream `ψ(q, η, s)` of the
planar field `v = ∇^⊥ψ = (−ψ_η, ψ_q)` (tex lines 2051, 2134–2138) and its pressure `p`, the
physical stream, velocity and pressure are
`𝒫(r,z,t) = r ψ(q,η,s)`, `u_r = a_r v₁`, `u_z = a_r (v₂ + εH)`, `p_raw = a_r² p`
(`eq:st18-t00188`). Using `u_r = −r⁻¹𝒫_z` and `u_z = r⁻¹𝒫_r` the field is exactly solenoidal;
equivalently `D_ε v₁ + ∂_η(v₂ + εH) = 0` (`eq:st18-t00189`).

Contents.
* Construction: `streamV1`, `streamV2` (`v = ∇^⊥ψ`), `ageDefect` (`H = (1 − K)ψ`),
  `axialProfile` (`v₂ + εH`), `physicalStream` (`𝒫`), `liftUr`, `liftUz`, `rawPressure`
  (normalized through B0187's `scaledLift`, so that B0187's residual identity applies verbatim
  with `f = v₁`, `h = v₂ + εH`, `Π = p`, as B0188 uses it).
* `liftUr_eq_stream`, `liftUz_eq_stream`: `u_r = −r⁻¹𝒫_z`, `u_z = r⁻¹𝒫_r` (tex 2858).
* `chartDivergence_stream_eq_zero`: `D_ε v₁ + ∂_η(v₂ + εH) = 0` (`eq:st18-t00189`), from the
  symmetry of second derivatives of a `C²` stream.
* `cylDivergence_scaledLift`, `cylDivergence_eq_zero_iff`: for normalized components
  `u_r = a_r f`, `u_z = a_r h`, the cylindrical divergence `∂_r u_r + r⁻¹u_r + ∂_z u_z` is
  `a_r² (D_ε f + ∂_η h)`, which is the "Equivalently" of tex line 2860.
* `streamForm_divergence_eq_zero`: `∂_r(r u_r) + ∂_z(r u_z) = 0`.
* `liftVelocity`, `liftVelocity_eq_streamLift`, `divergence_liftVelocity_eq_zero`: the
  Cartesian field `u_r e_r + u_z e_z` on `ℝ³` is the library stream lift
  (`Axi.streamLift`, AX06) of the physical stream, hence divergence free off the axis
  (Cartesian divergence of `Lib/Axisymmetric/Cylindrical.lean`).
* `exact_solenoidal_lift`: the unit (B0185) in one statement.
* `cylindricalResidual_lift`: B0187's identity specialised to this lift (bridge for B0188).

Hypotheses. The manuscript's train is smooth for `s > 0` (the physical domain `t > 0` maps to
`s > 0`). Pointwise statements assume only `ψ` differentiable, or `C²`, at the chart point;
the Cartesian statements assume `ψ` of class `C²` on the open age domain `{s > 0}`
(`ageDomain`). These rule out Lean's junk value `fderiv = 0` at non-differentiable points.
`r⁻¹` and `a_r = R/r` are Lean's `0` at `r = 0`; every identity is stated off the axis,
`r ≠ 0` or `y ∉ axis`. The bridge `cylindricalResidual_lift` inherits B0187's global
hypotheses (`ψ` of class `C³` on all of `ℝ³`, `p` differentiable).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.B0185

open Set Filter Topology
open UnforcedLeray.RingLift UnforcedLeray.B0184 UnforcedLeray.B0187

/-! ## The construction (`eq:st18-t00188`) -/

/-- First component `v₁ = −∂_η ψ` of the planar field `v = ∇^⊥ψ`, `∇^⊥ = (−∂_η, ∂_q)`
(tex lines 2051, 2138; blueprint B0140). -/
def streamV1 (ψ : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ := -partialEta ψ x

/-- Second component `v₂ = ∂_q ψ` of `v = ∇^⊥ψ` (tex lines 2051, 2138). -/
def streamV2 (ψ : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ := partialQ ψ x

/-- The age defect `H = (1 − K)ψ = ψ − ηψ_η − 2sψ_s` (tex line 2805). -/
def ageDefect (ψ : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ := ψ x - ageOperator ψ x

/-- The normalized axial profile `v₂ + εH` (tex line 2856). -/
def axialProfile (R : ℝ) (ψ : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ :=
  streamV2 ψ x + ringEps R * ageDefect ψ x

/-- The physical (Stokes) stream `𝒫(r, z, t) = r ψ(q, η, s)` (tex line 2854). -/
def physicalStream (R : ℝ) (ψ : ProfilePoint → ℝ) (r z t : ℝ) : ℝ :=
  r * cylinderLift R ψ r z t

/-- The physical radial velocity `u_r = a_r v₁` (tex line 2855), in B0187's normalization
`scaledLift R 1`. -/
def liftUr (R : ℝ) (ψ : ProfilePoint → ℝ) : ℝ → ℝ → ℝ → ℝ := scaledLift R 1 (streamV1 ψ)

/-- The physical axial velocity `u_z = a_r (v₂ + εH)` (tex line 2856). -/
def liftUz (R : ℝ) (ψ : ProfilePoint → ℝ) : ℝ → ℝ → ℝ → ℝ := scaledLift R 1 (axialProfile R ψ)

/-- The raw physical pressure `p_raw = a_r² p` (tex line 2857). -/
def rawPressure (R : ℝ) (p : ProfilePoint → ℝ) : ℝ → ℝ → ℝ → ℝ := scaledLift R 2 p

/-- Cylindrical divergence `∂_r u_r + r⁻¹ u_r + ∂_z u_z` of an axisymmetric no-swirl field
`u_r e_r + u_z e_z` (physical cylindrical coordinates; B0187's `physR`, `physZ`). -/
def cylDivergence (ur uz : ℝ → ℝ → ℝ → ℝ) (r z t : ℝ) : ℝ :=
  physR ur r z t + ur r z t / r + physZ uz r z t

/-- The chart divergence `D_ε f + ∂_η h` of normalized components `(f, h)`
(left side of `eq:st18-t00189` for `f = v₁`, `h = v₂ + εH`). -/
def chartDivergence (R : ℝ) (f h : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ :=
  ringD R f x + partialEta h x

theorem physicalStream_apply (R : ℝ) (ψ : ProfilePoint → ℝ) (r z t : ℝ) :
    physicalStream R ψ r z t = r * ψ (profileChart R r z t) := rfl

theorem liftUr_apply (R : ℝ) (ψ : ProfilePoint → ℝ) (r z t : ℝ) :
    liftUr R ψ r z t = radialScale R r * streamV1 ψ (profileChart R r z t) := by
  simp [liftUr, scaledLift, cylinderLift]

theorem liftUz_apply (R : ℝ) (ψ : ProfilePoint → ℝ) (r z t : ℝ) :
    liftUz R ψ r z t = radialScale R r * axialProfile R ψ (profileChart R r z t) := by
  simp [liftUz, scaledLift, cylinderLift]

theorem rawPressure_apply (R : ℝ) (p : ProfilePoint → ℝ) (r z t : ℝ) :
    rawPressure R p r z t = radialScale R r ^ 2 * p (profileChart R r z t) := rfl

/-- A planar field given with stream `ψ`, `v₁ = −ψ_η` (B0140, tex line 2051), is `streamV1 ψ`. -/
theorem streamV1_eq {ψ v₁ : ProfilePoint → ℝ} (h : ∀ x, v₁ x = -partialEta ψ x) :
    streamV1 ψ = v₁ :=
  funext fun x => (h x).symm

/-- A planar field given with stream `ψ`, `v₂ = ψ_q` (B0140, tex line 2051), is `streamV2 ψ`. -/
theorem streamV2_eq {ψ v₂ : ProfilePoint → ℝ} (h : ∀ x, v₂ x = partialQ ψ x) :
    streamV2 ψ = v₂ :=
  funext fun x => (h x).symm

/-- `H = ψ − (ηψ_η + 2sψ_s)` unfolded. -/
theorem ageDefect_apply (ψ : ProfilePoint → ℝ) (x : ProfilePoint) :
    ageDefect ψ x = ψ x - (x.2.1 * partialEta ψ x + 2 * x.2.2 * partialAge ψ x) := rfl

/-! ## `u_r = −r⁻¹𝒫_z`, `u_z = r⁻¹𝒫_r` -/

/-- `∂_z 𝒫 = r a_r ψ_η`. -/
theorem hasDerivAt_physicalStream_axial (R : ℝ) (ψ : ProfilePoint → ℝ) (r z t : ℝ)
    (hψ : DifferentiableAt ℝ ψ (profileChart R r z t)) :
    HasDerivAt (fun y => physicalStream R ψ r y t)
      (r * (radialScale R r * partialEta ψ (profileChart R r z t))) z :=
  (hasDerivAt_cylinderLift_axial_partialEta R r z t ψ hψ).const_mul r

/-- `∂_r 𝒫 = ψ + r a_r D_ε ψ`. -/
theorem hasDerivAt_physicalStream_radial (R : ℝ) (ψ : ProfilePoint → ℝ) (r z t : ℝ)
    (hR : R ≠ 0) (hr : r ≠ 0) (hψ : DifferentiableAt ℝ ψ (profileChart R r z t)) :
    HasDerivAt (fun x => physicalStream R ψ x z t)
      (ψ (profileChart R r z t) + r * (radialScale R r * ringD R ψ (profileChart R r z t))) r := by
  have h := (hasDerivAt_id' r).mul (hasDerivAt_cylinderLift_radial_ringD R r z t hR hr ψ hψ)
  refine h.congr_deriv ?_
  simp [cylinderLift]

/-- **`u_r = −r⁻¹𝒫_z`** (tex line 2858). -/
theorem liftUr_eq_stream (R : ℝ) (ψ : ProfilePoint → ℝ) {r : ℝ} (z t : ℝ) (hr : r ≠ 0)
    (hψ : DifferentiableAt ℝ ψ (profileChart R r z t)) :
    liftUr R ψ r z t = -(r⁻¹ * physZ (physicalStream R ψ) r z t) := by
  rw [physZ, (hasDerivAt_physicalStream_axial R ψ r z t hψ).deriv, liftUr_apply, streamV1]
  field_simp

/-- **`u_z = r⁻¹𝒫_r`** (tex line 2858): `r⁻¹𝒫_r = r⁻¹ψ + a_r D_εψ = a_r(ψ_q + ε(1 − K)ψ)`. -/
theorem liftUz_eq_stream (R : ℝ) (ψ : ProfilePoint → ℝ) {r : ℝ} (z t : ℝ) (hR : R ≠ 0)
    (hr : r ≠ 0) (hψ : DifferentiableAt ℝ ψ (profileChart R r z t)) :
    liftUz R ψ r z t = r⁻¹ * physR (physicalStream R ψ) r z t := by
  rw [physR, (hasDerivAt_physicalStream_radial R ψ r z t hR hr hψ).deriv, liftUz_apply]
  simp only [axialProfile, streamV2, ageDefect, ringD, ringEps, radialScale]
  field_simp
  ring

/-! ## Derivatives of the stream components -/

/-- The directional derivative `y ↦ Dψ(y) v` has derivative `w ↦ D²ψ(x) w v`. -/
theorem hasFDerivAt_fderiv_apply {f : ProfilePoint → ℝ} {x : ProfilePoint}
    (hd : DifferentiableAt ℝ (fderiv ℝ f) x) (v : ProfilePoint) :
    HasFDerivAt (fun y => fderiv ℝ f y v) ((fderiv ℝ (fderiv ℝ f) x).flip v) x := by
  have h := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  refine h.congr_fderiv ?_
  ext <;> simp

theorem differentiableAt_fderiv_of_contDiffAt {ψ : ProfilePoint → ℝ} {x : ProfilePoint}
    (hψ : ContDiffAt ℝ 2 ψ x) : DifferentiableAt ℝ (fderiv ℝ ψ) x :=
  (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero

/-- Derivative of `v₁ = −ψ_η` at a point where `ψ` is `C²`. -/
theorem hasFDerivAt_streamV1 {ψ : ProfilePoint → ℝ} {x : ProfilePoint}
    (hψ : ContDiffAt ℝ 2 ψ x) :
    HasFDerivAt (streamV1 ψ) (-((fderiv ℝ (fderiv ℝ ψ) x).flip eηDir)) x :=
  (hasFDerivAt_fderiv_apply (differentiableAt_fderiv_of_contDiffAt hψ) eηDir).neg

/-- Derivative of the coordinate `η`. -/
theorem hasFDerivAt_eta (x : ProfilePoint) :
    HasFDerivAt (fun y : ProfilePoint => y.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) x :=
  (hasFDerivAt_snd (p := x)).fst

/-- Derivative of the coordinate `s`. -/
theorem hasFDerivAt_age (x : ProfilePoint) :
    HasFDerivAt (fun y : ProfilePoint => y.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) x :=
  (hasFDerivAt_snd (p := x)).snd

/-- `v₁` is differentiable where `ψ` is `C²`. -/
theorem differentiableAt_streamV1 {ψ : ProfilePoint → ℝ} {x : ProfilePoint}
    (hψ : ContDiffAt ℝ 2 ψ x) : DifferentiableAt ℝ (streamV1 ψ) x :=
  (hasFDerivAt_streamV1 hψ).differentiableAt

/-- `v₂ + εH` is differentiable where `ψ` is `C²`. -/
theorem differentiableAt_axialProfile (R : ℝ) {ψ : ProfilePoint → ℝ} {x : ProfilePoint}
    (hψ : ContDiffAt ℝ 2 ψ x) : DifferentiableAt ℝ (axialProfile R ψ) x := by
  have hd := differentiableAt_fderiv_of_contDiffAt hψ
  have hψ1 : DifferentiableAt ℝ ψ x := hψ.differentiableAt (by norm_num)
  have hq := (hasFDerivAt_fderiv_apply hd eqDir).differentiableAt
  have he := (hasFDerivAt_fderiv_apply hd eηDir).differentiableAt
  have hs := (hasFDerivAt_fderiv_apply hd esDir).differentiableAt
  have hη := (hasFDerivAt_eta x).differentiableAt
  have hσ := (hasFDerivAt_age x).differentiableAt
  have hK : DifferentiableAt ℝ (ageOperator ψ) x :=
    (hη.fun_mul he).fun_add ((hσ.const_mul 2).fun_mul hs)
  exact hq.fun_add ((hψ1.fun_sub hK).const_mul (ringEps R))

/-! ## Exact solenoidality in the chart (`eq:st18-t00189`) -/

/-- **`eq:st18-t00189`** (tex lines 2859–2865): for a stream `ψ` of class `C²` at `x`,
`D_ε v₁ + ∂_η(v₂ + εH) = 0` at `x`. The two `O(1)` terms `−ψ_{ηq} + ψ_{qη}` and the two
`O(ε)` terms `2s(ψ_{ηs} − ψ_{sη})` cancel by symmetry of second derivatives. -/
theorem chartDivergence_stream_eq_zero (R : ℝ) {ψ : ProfilePoint → ℝ} {x : ProfilePoint}
    (hψ : ContDiffAt ℝ 2 ψ x) :
    chartDivergence R (streamV1 ψ) (axialProfile R ψ) x = 0 := by
  have hd := differentiableAt_fderiv_of_contDiffAt hψ
  have hψ1 : DifferentiableAt ℝ ψ x := hψ.differentiableAt (by norm_num)
  have hsym : IsSymmSndFDerivAt ℝ ψ x := hψ.isSymmSndFDerivAt (by simp)
  have hV1 := hasFDerivAt_streamV1 hψ
  have hq := hasFDerivAt_fderiv_apply hd eqDir
  have he := hasFDerivAt_fderiv_apply hd eηDir
  have hs := hasFDerivAt_fderiv_apply hd esDir
  have hK := ((hasFDerivAt_eta x).fun_mul he).fun_add
    (((hasFDerivAt_age x).const_mul 2).fun_mul hs)
  have hAx := hq.fun_add ((hψ1.hasFDerivAt.fun_sub hK).const_mul (ringEps R))
  have hAx' : HasFDerivAt (axialProfile R ψ) _ x := hAx
  have s1 := hsym eqDir eηDir
  have s2 := hsym esDir eηDir
  simp only [chartDivergence, ringD, ageOperator, partialQ, partialEta, partialAge, hV1.fderiv,
    hAx'.fderiv]
  simp only [_root_.add_apply, _root_.sub_apply, _root_.neg_apply, _root_.smul_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul] at s1 s2 ⊢
  simp only [eqDir, eηDir, esDir] at s1 s2 ⊢
  linear_combination (-1 : ℝ) * s1 + (2 * ringEps R * x.2.2) * s2

/-! ## The cylindrical divergence of normalized fields -/

/-- For normalized components `u_r = a_r f`, `u_z = a_r h`,
`∂_r u_r + r⁻¹u_r + ∂_z u_z = a_r² (D_ε f + ∂_η h)` off the axis
(from `∂_r(a_r f) = a_r²(D_ε − ε)f`, `r⁻¹ = εa_r`, `∂_z(a_r h) = a_r² h_η`). -/
theorem cylDivergence_scaledLift (R : ℝ) (hR : R ≠ 0) (f h : ProfilePoint → ℝ) {r : ℝ}
    (z t : ℝ) (hr : r ≠ 0) (hf : DifferentiableAt ℝ f (profileChart R r z t))
    (hh : DifferentiableAt ℝ h (profileChart R r z t)) :
    cylDivergence (scaledLift R 1 f) (scaledLift R 1 h) r z t =
      radialScale R r ^ 2 * chartDivergence R f h (profileChart R r z t) := by
  have h1 := (hasDerivAt_scaledLift_radial R 1 f r z t hR hr hf).deriv
  have h2 := (hasDerivAt_scaledLift_axial R 1 h r z t hh).deriv
  simp only [cylDivergence, physR, physZ]
  rw [h1, h2]
  simp only [chartDivergence, scaledLift, cylinderLift, radialScale, ringEps]
  push_cast
  field_simp
  ring

/-- **"Equivalently"** (tex line 2860): off the axis, the normalized field `(a_r f, a_r h)` is
divergence free exactly when `D_ε f + ∂_η h = 0` at the chart point. -/
theorem cylDivergence_eq_zero_iff (R : ℝ) (hR : R ≠ 0) (f h : ProfilePoint → ℝ) {r : ℝ}
    (z t : ℝ) (hr : r ≠ 0) (hf : DifferentiableAt ℝ f (profileChart R r z t))
    (hh : DifferentiableAt ℝ h (profileChart R r z t)) :
    cylDivergence (scaledLift R 1 f) (scaledLift R 1 h) r z t = 0 ↔
      chartDivergence R f h (profileChart R r z t) = 0 := by
  rw [cylDivergence_scaledLift R hR f h z t hr hf hh]
  have ha : radialScale R r ^ 2 ≠ 0 := pow_ne_zero 2 (div_ne_zero hR hr)
  constructor
  · intro h0
    exact (mul_eq_zero.1 h0).resolve_left ha
  · intro h0
    rw [h0, mul_zero]

/-- The lift is exactly solenoidal in cylindrical form: `∂_r u_r + r⁻¹u_r + ∂_z u_z = 0`
off the axis, for a stream of class `C²` at the chart point. -/
theorem cylDivergence_lift_eq_zero (R : ℝ) (hR : R ≠ 0) (ψ : ProfilePoint → ℝ) {r : ℝ}
    (z t : ℝ) (hr : r ≠ 0) (hψ : ContDiffAt ℝ 2 ψ (profileChart R r z t)) :
    cylDivergence (liftUr R ψ) (liftUz R ψ) r z t = 0 :=
  (cylDivergence_eq_zero_iff R hR _ _ z t hr (differentiableAt_streamV1 hψ)
    (differentiableAt_axialProfile R hψ)).2 (chartDivergence_stream_eq_zero R hψ)

/-- **Stream form of solenoidality** (tex line 2858): `∂_r(r u_r) + ∂_z(r u_z) = 0`, i.e.
`∂_r(−𝒫_z) + ∂_z(𝒫_r) = 0`, off the axis. -/
theorem streamForm_divergence_eq_zero (R : ℝ) (hR : R ≠ 0) (ψ : ProfilePoint → ℝ) {r : ℝ}
    (z t : ℝ) (hr : r ≠ 0) (hψ : ContDiffAt ℝ 2 ψ (profileChart R r z t)) :
    deriv (fun x => x * liftUr R ψ x z t) r + deriv (fun y => r * liftUz R ψ r y t) z = 0 := by
  have hur := hasDerivAt_scaledLift_radial R 1 (streamV1 ψ) r z t hR hr
    (differentiableAt_streamV1 hψ)
  have huz := hasDerivAt_scaledLift_axial R 1 (axialProfile R ψ) r z t
    (differentiableAt_axialProfile R hψ)
  have h1 := ((hasDerivAt_id' r).fun_mul hur).deriv
  have h2 := (huz.const_mul r).deriv
  have h0 := cylDivergence_lift_eq_zero R hR ψ z t hr hψ
  simp only [cylDivergence, physR, physZ, liftUr, liftUz, hur.deriv, huz.deriv] at h0
  simp only [liftUr, liftUz]
  rw [h1, h2]
  have e : 1 * scaledLift R 1 (streamV1 ψ) r z t +
      r * (radialScale R r ^ (1 + 1) * (ringD R (streamV1 ψ) (profileChart R r z t) -
        ((1 : ℕ) : ℝ) * ringEps R * streamV1 ψ (profileChart R r z t))) +
      r * (radialScale R r ^ (1 + 1) * partialEta (axialProfile R ψ) (profileChart R r z t)) =
      r * (radialScale R r ^ (1 + 1) * (ringD R (streamV1 ψ) (profileChart R r z t) -
        ((1 : ℕ) : ℝ) * ringEps R * streamV1 ψ (profileChart R r z t)) +
        scaledLift R 1 (streamV1 ψ) r z t / r +
        radialScale R r ^ (1 + 1) * partialEta (axialProfile R ψ) (profileChart R r z t)) := by
    field_simp
    ring
  rw [e, h0, mul_zero]

/-! ## The Cartesian lift on `ℝ³` -/

/-- The open age domain `{s > 0}` of profile space, the image of the physical domain
`r > 0`, `t > 0` under the chart. -/
def ageDomain : Set ProfilePoint := {x | 0 < x.2.2}

theorem isOpen_ageDomain : IsOpen ageDomain :=
  isOpen_lt continuous_const (continuous_snd.comp continuous_snd)

/-- The physical stream at fixed time as a function of the meridional point `(ρ, z)`. -/
def merStream (R : ℝ) (ψ : ProfilePoint → ℝ) (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  physicalStream R ψ p.1 p.2 t

/-- The meridional components `(u_r, u_z)` at fixed time. -/
def merVelocity (R : ℝ) (ψ : ProfilePoint → ℝ) (t : ℝ) (p : ℝ × ℝ) : Axi.Merid :=
  liftUr R ψ p.1 p.2 t • Axi.m0 + liftUz R ψ p.1 p.2 t • Axi.m1

/-- **The lift velocity on `ℝ³`**: `u(y, t) = u_r e_r + u_z e_z` at `(r, z) = (ϱ(y), y₃)`
(tex lines 2855–2856). Its Lean value on the axis is `0`. -/
def liftVelocity (R : ℝ) (ψ : ProfilePoint → ℝ) (t : ℝ) : Space → Space :=
  Axi.liftMer (merVelocity R ψ t)

/-- The raw physical pressure on `ℝ³`, `p_raw(y, t) = a_r² p` at `r = ϱ(y)`, `z = y₃`
(tex line 2857). -/
def liftPressure (R : ℝ) (p : ProfilePoint → ℝ) (t : ℝ) (y : Space) : ℝ :=
  rawPressure R p (Axi.ϱ y) (y 2) t

theorem liftVelocity_apply (R : ℝ) (ψ : ProfilePoint → ℝ) (t : ℝ) (y : Space) :
    liftVelocity R ψ t y =
      liftUr R ψ (Axi.ϱ y) (y 2) t • Axi.eR y + liftUz R ψ (Axi.ϱ y) (y 2) t • Axi.e3 := by
  simp [liftVelocity, Axi.liftMer, merVelocity, Axi.mer]

theorem isAxisymmetricNoSwirl_liftVelocity (R : ℝ) (ψ : ProfilePoint → ℝ) (t : ℝ) :
    IsAxisymmetricNoSwirl (liftVelocity R ψ t) :=
  Axi.isAxisymmetricNoSwirl_liftMer _

/-- The chart as a map of the meridional point. -/
theorem contDiffOn_profileChart_mer (R t : ℝ) (hR : R ≠ 0) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => profileChart R p.1 p.2 t) (Ioi 0 ×ˢ univ) := by
  have hinv : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (p.1)⁻¹) (Ioi 0 ×ˢ univ) :=
    contDiffOn_fst.inv fun p hp => ne_of_gt hp.1
  have hq : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => R * Real.log (p.1 / R)) (Ioi 0 ×ˢ univ) :=
    contDiffOn_const.mul ((contDiffOn_fst.div_const R).log fun p hp =>
      div_ne_zero (ne_of_gt hp.1) hR)
  have ha : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => R / p.1) (Ioi 0 ×ˢ univ) := by
    have h := contDiffOn_const (c := R).mul hinv
    refine h.congr fun p _ => ?_
    simp [div_eq_mul_inv]
  have hη : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => R / p.1 * p.2) (Ioi 0 ×ˢ univ) :=
    ha.mul contDiffOn_snd
  have hs : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (R / p.1) ^ 2 * t) (Ioi 0 ×ˢ univ) :=
    (ha.pow 2).mul contDiffOn_const
  exact hq.prodMk (hη.prodMk hs)

theorem mapsTo_profileChart_mer (R t : ℝ) (hR : R ≠ 0) (ht : 0 < t) :
    MapsTo (fun p : ℝ × ℝ => profileChart R p.1 p.2 t) (Ioi 0 ×ˢ univ) ageDomain := by
  intro p hp
  have hp1 : (0 : ℝ) < p.1 := hp.1
  show 0 < ageCoordinate R p.1 t
  simp only [ageCoordinate, radialScale]
  exact mul_pos (sq_pos_of_ne_zero (div_ne_zero hR hp1.ne')) ht

/-- The meridional physical stream is `C²` on the half-plane `ρ > 0` for `t > 0`. -/
theorem contDiffOn_merStream (R t : ℝ) (hR : R ≠ 0) (ht : 0 < t) {ψ : ProfilePoint → ℝ}
    (hψ : ContDiffOn ℝ 2 ψ ageDomain) :
    ContDiffOn ℝ 2 (merStream R ψ t) (Ioi 0 ×ˢ univ) := by
  have hc := hψ.comp (contDiffOn_profileChart_mer R t hR) (mapsTo_profileChart_mer R t hR ht)
  exact contDiffOn_fst.mul hc

theorem differentiableAt_merStream (R t : ℝ) (hR : R ≠ 0) (ht : 0 < t) {ψ : ProfilePoint → ℝ}
    (hψ : DifferentiableOn ℝ ψ ageDomain) {p : ℝ × ℝ} (hp : 0 < p.1) :
    DifferentiableAt ℝ (merStream R ψ t) p := by
  have hmem : p ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := ⟨hp, trivial⟩
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hch : DifferentiableAt ℝ (fun p : ℝ × ℝ => profileChart R p.1 p.2 t) p :=
    ((contDiffOn_profileChart_mer R t hR).contDiffAt (hopen.mem_nhds hmem)).differentiableAt
      (by norm_num)
  have hψp : DifferentiableAt ℝ ψ (profileChart R p.1 p.2 t) :=
    hψ.differentiableAt (isOpen_ageDomain.mem_nhds (mapsTo_profileChart_mer R t hR ht hmem))
  exact differentiableAt_fst.mul (hψp.comp p hch)

/-- Off the axis the library's stream profile of the physical stream is `(u_r, u_z)`. -/
theorem streamProfile_merStream (R t : ℝ) (hR : R ≠ 0) (ht : 0 < t) {ψ : ProfilePoint → ℝ}
    (hψ : DifferentiableOn ℝ ψ ageDomain) {p : ℝ × ℝ} (hp : 0 < p.1) :
    Axi.streamProfile (merStream R ψ t) p = merVelocity R ψ t p := by
  have hmem : p ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := ⟨hp, trivial⟩
  have hψp : DifferentiableAt ℝ ψ (profileChart R p.1 p.2 t) :=
    hψ.differentiableAt (isOpen_ageDomain.mem_nhds (mapsTo_profileChart_mer R t hR ht hmem))
  have hP := differentiableAt_merStream R t hR ht hψ hp
  have hz : Axi.dz (merStream R ψ t) p = physZ (physicalStream R ψ) p.1 p.2 t :=
    ((Axi.hasDerivAt_line_snd hP).deriv).symm
  have hρ : Axi.dρ (merStream R ψ t) p = physR (physicalStream R ψ) p.1 p.2 t :=
    ((Axi.hasDerivAt_line_fst hP).deriv).symm
  rw [Axi.streamProfile, hz, hρ, merVelocity, liftUr_eq_stream R ψ p.2 t hp.ne' hψp,
    liftUz_eq_stream R ψ p.2 t hR hp.ne' hψp]
  simp

/-- **The lift is the stream lift of `𝒫`** (tex line 2858): for `t > 0` and `ψ`
differentiable on `{s > 0}`, the Cartesian field `u_r e_r + u_z e_z` equals
`curl(𝒫 e_φ / r) = −r⁻¹𝒫_z e_r + r⁻¹𝒫_r e_z` on all of `ℝ³` (both are `0` on the axis). -/
theorem liftVelocity_eq_streamLift (R t : ℝ) (hR : R ≠ 0) (ht : 0 < t)
    {ψ : ProfilePoint → ℝ} (hψ : DifferentiableOn ℝ ψ ageDomain) :
    liftVelocity R ψ t = Axi.streamLift (merStream R ψ t) := by
  funext y
  by_cases hy : y ∈ Axi.axis
  · have h0 : Axi.ϱ y = 0 := (Axi.mem_axis_iff y).1 hy
    rw [liftVelocity_apply, Axi.streamLift_apply, h0]
    simp [Axi.eR, h0, liftUz_apply, radialScale]
  · rw [Axi.streamLift, liftVelocity]
    simp only [Axi.liftMer]
    rw [streamProfile_merStream R t hR ht hψ (Axi.ϱ_pos hy)]

/-- **Exact solenoidality on `ℝ³`** (tex line 2858): for `t > 0` and a stream of class `C²` on
`{s > 0}`, the Cartesian lift velocity is divergence free at every point off the axis. -/
theorem divergence_liftVelocity_eq_zero (R t : ℝ) (hR : R ≠ 0) (ht : 0 < t)
    {ψ : ProfilePoint → ℝ} (hψ : ContDiffOn ℝ 2 ψ ageDomain) {y : Space} (hy : y ∉ Axi.axis) :
    Axi.divergence (liftVelocity R ψ t) y = 0 := by
  rw [liftVelocity_eq_streamLift R t hR ht (hψ.differentiableOn (by norm_num))]
  exact Axi.div_streamLift_eq_zero (contDiffOn_merStream R t hR ht hψ) hy

/-! ## The unit -/

/-- **Unit B0185** (`eq:st18-t00188`, `eq:st18-t00189`, tex lines 2851–2865). Let `R ≥ 2`,
`ε = R⁻¹`, `r > 0`, `t > 0`, and let `ψ(q, η, s)` be a stream of class `C²` on `{s > 0}`
with `v = ∇^⊥ψ = (v₁, v₂)` and `H = (1 − K)ψ`. For the physical stream `𝒫 = rψ`, the lift
velocity `u_r = a_r v₁`, `u_z = a_r(v₂ + εH)`:
1. `u_r = −r⁻¹𝒫_z` and `u_z = r⁻¹𝒫_r`;
2. `∂_r u_r + r⁻¹u_r + ∂_z u_z = 0` (exact solenoidality, cylindrical form);
3. `D_ε v₁ + ∂_η(v₂ + εH) = 0` at the chart point `(q, η, s)` (`eq:st18-t00189`);
4. the Cartesian field `u_r e_r + u_z e_z` is divergence free off the axis of `ℝ³`.
The raw pressure is `rawPressure R p = a_r² p` (`rawPressure_apply`). -/
theorem exact_solenoidal_lift (R : ℝ) (hR : 2 ≤ R) {ψ : ProfilePoint → ℝ}
    (hψ : ContDiffOn ℝ 2 ψ ageDomain) {r t : ℝ} (z : ℝ) (hr : 0 < r) (ht : 0 < t) :
    liftUr R ψ r z t = -(r⁻¹ * physZ (physicalStream R ψ) r z t) ∧
    liftUz R ψ r z t = r⁻¹ * physR (physicalStream R ψ) r z t ∧
    cylDivergence (liftUr R ψ) (liftUz R ψ) r z t = 0 ∧
    ringD R (streamV1 ψ) (profileChart R r z t) +
      partialEta (axialProfile R ψ) (profileChart R r z t) = 0 ∧
    (∀ y : Space, y ∉ Axi.axis → Axi.divergence (liftVelocity R ψ t) y = 0) := by
  have hR0 : R ≠ 0 := by linarith
  have hmem : profileChart R r z t ∈ ageDomain :=
    mapsTo_profileChart_mer R t hR0 ht (x := (r, z)) ⟨hr, trivial⟩
  have hψx : ContDiffAt ℝ 2 ψ (profileChart R r z t) :=
    hψ.contDiffAt (isOpen_ageDomain.mem_nhds hmem)
  have hψd : DifferentiableAt ℝ ψ (profileChart R r z t) := hψx.differentiableAt (by norm_num)
  exact ⟨liftUr_eq_stream R ψ z t hr.ne' hψd, liftUz_eq_stream R ψ z t hR0 hr.ne' hψd,
    cylDivergence_lift_eq_zero R hR0 ψ z t hr.ne' hψx, chartDivergence_stream_eq_zero R hψx,
    fun y hy => divergence_liftVelocity_eq_zero R t hR0 ht hψ hy⟩

/-! ## Bridge to B0187 (used by B0188) -/

theorem contDiff_streamV1 {ψ : ProfilePoint → ℝ} (hψ : ContDiff ℝ 3 ψ) :
    ContDiff ℝ 2 (streamV1 ψ) :=
  ((hψ.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const).neg

theorem contDiff_axialProfile (R : ℝ) {ψ : ProfilePoint → ℝ} (hψ : ContDiff ℝ 3 ψ) :
    ContDiff ℝ 2 (axialProfile R ψ) := by
  have hD := hψ.fderiv_right (m := 2) (by norm_num)
  have hq : ContDiff ℝ 2 (fun y => fderiv ℝ ψ y eqDir) := hD.clm_apply contDiff_const
  have he : ContDiff ℝ 2 (fun y => fderiv ℝ ψ y eηDir) := hD.clm_apply contDiff_const
  have hs : ContDiff ℝ 2 (fun y => fderiv ℝ ψ y esDir) := hD.clm_apply contDiff_const
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by norm_num)
  have hη : ContDiff ℝ 2 (fun y : ProfilePoint => y.2.1) := contDiff_snd.fst
  have hσ : ContDiff ℝ 2 (fun y : ProfilePoint => y.2.2) := contDiff_snd.snd
  have hK : ContDiff ℝ 2 (ageOperator ψ) :=
    (hη.mul he).add ((contDiff_const.mul hσ).mul hs)
  exact hq.add (contDiff_const.mul (hψ2.sub hK))

/-- B0187's residual identity for this lift: with `f = v₁`, `h = v₂ + εH`, `Π = p`, the
cylindrical Navier–Stokes residual of `(u_r, u_z, p_raw)` divided by `a_r³` is the chart
expression `eq:st18-t00190`. The global hypotheses are B0187's. -/
theorem cylindricalResidual_lift (R ν : ℝ) (hR : 2 ≤ R) {ψ p : ProfilePoint → ℝ}
    (hψ : ContDiff ℝ 3 ψ) (hp : Differentiable ℝ p) (r z t : ℝ) (hr : 0 < r) (ht : 0 < t) :
    cylRadialResidual ν (liftUr R ψ) (liftUz R ψ) (rawPressure R p) r z t =
        radialScale R r ^ 3 *
          chartRadialResidual R ν (streamV1 ψ) (axialProfile R ψ) p (profileChart R r z t) ∧
    cylAxialResidual ν (liftUr R ψ) (liftUz R ψ) (rawPressure R p) r z t =
        radialScale R r ^ 3 *
          chartAxialResidual R ν (streamV1 ψ) (axialProfile R ψ) p (profileChart R r z t) :=
  cylindricalResidual_eq_chart R ν hR _ _ p (contDiff_streamV1 hψ) (contDiff_axialProfile R hψ)
    hp r z t hr ht

end UnforcedLeray.B0185
