import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult
import UnforcedLeray.Units.B0184

/-!
# B0187 `eq:st18-t00190`: the normalized cylindrical Navier–Stokes residual in the chart

Blueprint unit B0187, label `eq:st18-t00190`, `paper/main.tex` lines 2867–2888
(subsection "Coordinates and equations" of the exact solenoidal lift). The chart, the
operators `K = η∂_η + 2s∂_s` (tex line 2805) and `D_ε = ∂_q − εK` (tex line 2844), and the
differentiation rules `∂_r = a_r D_ε`, `∂_z = a_r ∂_η`, `∂_t = a_r² ∂_s` are the draft unit

declarations are reused here.

Statement in words (tex lines 2867–2888). Let `R ≥ 2`, `ε = R⁻¹`, and let `f, h, Π` be
profiles of `(q, η, s)`. Put the physical axisymmetric no-swirl fields
`u_r = a_r f`, `u_z = a_r h`, `p = a_r² Π` (the normalisation of `eq:st18-t00188`), where
each profile is evaluated at the chart image `(q, η, s)` of `(r, z, t)`. Then at every
`r > 0`, `z`, `t > 0` the cylindrical Navier–Stokes residual at viscosity `ν`, divided by
`a_r³`, is exactly
* radial:  `f_s + f D_ε f + h f_η − ε f² − ν(D_ε² − 2εD_ε + ∂_η²) f + (D_ε − 2ε) Π`,
* axial:   `h_s + f D_ε h + h h_η − ε f h − ν(D_ε² − 2εD_ε + ε² + ∂_η²) h + Π_η`.
Here `D_ε² = D_ε ∘ D_ε` contains the second age derivative (through `K`).

The cylindrical Navier–Stokes residual of an axisymmetric no-swirl field
`u = u_r e_r + u_z e_z` with pressure `p` (the manuscript's "cylindrical Navier–Stokes
residual") is, in physical cylindrical coordinates,
* radial: `∂_t u_r + u_r ∂_r u_r + u_z ∂_z u_r − ν(∂_r² + r⁻¹∂_r − r⁻² + ∂_z²) u_r + ∂_r p`,
* axial:  `∂_t u_z + u_r ∂_r u_z + u_z ∂_z u_z − ν(∂_r² + r⁻¹∂_r + ∂_z²) u_z + ∂_z p`,
with the vector-Laplacian term `−r⁻² u_r` in the radial component only (tex lines
2883–2885). These are `cylRadialResidual` and `cylAxialResidual` below, written with
one-variable derivatives `deriv` of the physical sections.

Proof (the manuscript's, tex lines 2881–2888). `∂_r(a_r^k g) = a_r^{k+1}(D_ε − kε) g`
(`∂_r a_r = −ε a_r²` and B0184), `∂_z(a_r^k g) = a_r^{k+1} g_η`, `∂_t(a_r^k g) = a_r^{k+2} g_s`,
and `r⁻¹ = ε a_r`. Hence `(∂_r² + r⁻¹∂_r − r⁻² + ∂_z²)(a_r f) = a_r³(D_ε² − 2εD_ε + ∂_η²) f`
and the axial Laplacian adds `ε² a_r³ h`; the frame transport terms give `−ε f²`, `−ε f h`.

Hypotheses. The manuscript's profiles are smooth. Here `f, h` are only assumed `C²` and
`Π` only differentiable (weaker); this rules out the junk value `fderiv = 0` at
non-differentiable points. The viscosity `ν` is arbitrary (the identity is algebraic in `ν`).

Not covered here: the identification of this cylindrical residual with the Cartesian
Navier–Stokes operator on `ℝ³` (the library's `SolvesUnforcedNavierStokes`) off the axis;
that is infrastructure INF23 (cylindrical coordinates on `ℝ³`), noted in the blueprint entry.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.B0187

open Filter Topology
open UnforcedLeray.RingLift UnforcedLeray.B0184

/-! ## Physical cylindrical derivatives and the cylindrical residual -/

/-- Physical radial derivative `∂_r F` of a function of `(r, z, t)`. -/
def physR (F : ℝ → ℝ → ℝ → ℝ) (r z t : ℝ) : ℝ := deriv (fun x => F x z t) r

/-- Physical axial derivative `∂_z F` of a function of `(r, z, t)`. -/
def physZ (F : ℝ → ℝ → ℝ → ℝ) (r z t : ℝ) : ℝ := deriv (fun y => F r y t) z

/-- Physical time derivative `∂_t F` of a function of `(r, z, t)`. -/
def physT (F : ℝ → ℝ → ℝ → ℝ) (r z t : ℝ) : ℝ := deriv (fun τ => F r z τ) t

/-- Radial component of the cylindrical vector Laplacian of an axisymmetric no-swirl field,
`(∂_r² + r⁻¹∂_r − r⁻² + ∂_z²) u_r` (tex lines 2883–2884). -/
def radialVectorLaplacian (u : ℝ → ℝ → ℝ → ℝ) (r z t : ℝ) : ℝ :=
  physR (physR u) r z t + physR u r z t / r - u r z t / r ^ 2 + physZ (physZ u) r z t

/-- Axial component of the cylindrical vector Laplacian, `(∂_r² + r⁻¹∂_r + ∂_z²) u_z`: no
`−r⁻²` term (tex lines 2884–2885). -/
def axialVectorLaplacian (u : ℝ → ℝ → ℝ → ℝ) (r z t : ℝ) : ℝ :=
  physR (physR u) r z t + physR u r z t / r + physZ (physZ u) r z t

/-- Radial cylindrical Navier–Stokes residual of the no-swirl field `(u_r, u_z)` with
pressure `p` at viscosity `ν`:
`∂_t u_r + u_r ∂_r u_r + u_z ∂_z u_r − ν(∂_r² + r⁻¹∂_r − r⁻² + ∂_z²)u_r + ∂_r p`. -/
def cylRadialResidual (ν : ℝ) (ur uz p : ℝ → ℝ → ℝ → ℝ) (r z t : ℝ) : ℝ :=
  physT ur r z t + ur r z t * physR ur r z t + uz r z t * physZ ur r z t
    - ν * radialVectorLaplacian ur r z t + physR p r z t

/-- Axial cylindrical Navier–Stokes residual of the no-swirl field `(u_r, u_z)` with
pressure `p` at viscosity `ν`:
`∂_t u_z + u_r ∂_r u_z + u_z ∂_z u_z − ν(∂_r² + r⁻¹∂_r + ∂_z²)u_z + ∂_z p`. -/
def cylAxialResidual (ν : ℝ) (ur uz p : ℝ → ℝ → ℝ → ℝ) (r z t : ℝ) : ℝ :=
  physT uz r z t + ur r z t * physR uz r z t + uz r z t * physZ uz r z t
    - ν * axialVectorLaplacian uz r z t + physZ p r z t

/-! ## Normalized fields and the chart residual -/

/-- The normalized physical field `a_r^k g(q, η, s)` attached to a profile `g`. With `k = 1`
it is a velocity component `u_r = a_r f`, `u_z = a_r h`; with `k = 2` the pressure
`a_r² Π` (tex lines 2852–2856, 2867–2868). -/
def scaledLift (R : ℝ) (k : ℕ) (g : ProfilePoint → ℝ) (r z t : ℝ) : ℝ :=
  radialScale R r ^ k * cylinderLift R g r z t

/-- Radial diffusion polynomial `(D_ε² − 2εD_ε + ∂_η²) f` (tex line 2873). -/
def ringDiffusionRadial (R : ℝ) (f : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ :=
  ringD R (ringD R f) x - 2 * ringEps R * ringD R f x + partialEta (partialEta f) x

/-- Axial diffusion polynomial `(D_ε² − 2εD_ε + ε² + ∂_η²) h` (tex lines 2876–2877). -/
def ringDiffusionAxial (R : ℝ) (h : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ :=
  ringD R (ringD R h) x - 2 * ringEps R * ringD R h x + ringEps R ^ 2 * h x +
    partialEta (partialEta h) x

/-- Radial line of `eq:st18-t00190` (tex lines 2872–2874):
`f_s + f D_ε f + h f_η − ε f² − ν(D_ε² − 2εD_ε + ∂_η²) f + (D_ε − 2ε) Π`. -/
def chartRadialResidual (R ν : ℝ) (f h pres : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ :=
  partialAge f x + f x * ringD R f x + h x * partialEta f x - ringEps R * f x ^ 2
    - ν * ringDiffusionRadial R f x + (ringD R pres x - 2 * ringEps R * pres x)

/-- Axial line of `eq:st18-t00190` (tex lines 2875–2878):
`h_s + f D_ε h + h h_η − ε f h − ν(D_ε² − 2εD_ε + ε² + ∂_η²) h + Π_η`. -/
def chartAxialResidual (R ν : ℝ) (f h pres : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ :=
  partialAge h x + f x * ringD R h x + h x * partialEta h x - ringEps R * f x * h x
    - ν * ringDiffusionAxial R h x + partialEta pres x

/-! ## Regularity of the profile operators -/

/-- A directional derivative of a `C²` profile is `C¹` (B0187 helper). -/
theorem contDiff_fderiv_apply {f : ProfilePoint → ℝ} (hf : ContDiff ℝ 2 f)
    (v : ProfilePoint) : ContDiff ℝ 1 (fun x => fderiv ℝ f x v) :=
  (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- For a `C²` profile, `∂_q f` is differentiable (B0187 helper). -/
theorem differentiable_partialQ {f : ProfilePoint → ℝ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (partialQ f) :=
  (contDiff_fderiv_apply hf eqDir).differentiable one_ne_zero

/-- For a `C²` profile, `∂_η f` is differentiable (B0187 helper). -/
theorem differentiable_partialEta {f : ProfilePoint → ℝ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (partialEta f) :=
  (contDiff_fderiv_apply hf eηDir).differentiable one_ne_zero

/-- For a `C²` profile, `∂_s f` is differentiable (B0187 helper). -/
theorem differentiable_partialAge {f : ProfilePoint → ℝ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (partialAge f) :=
  (contDiff_fderiv_apply hf esDir).differentiable one_ne_zero

/-- For a `C²` profile, `D_ε f` is differentiable. -/
theorem differentiable_ringD (R : ℝ) {f : ProfilePoint → ℝ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (ringD R f) := by
  have h1 := differentiable_partialQ hf
  have h2 := differentiable_partialEta hf
  have h3 := differentiable_partialAge hf
  have he : ringD R f = fun x => partialQ f x - ringEps R *
      (x.2.1 * partialEta f x + 2 * x.2.2 * partialAge f x) := rfl
  rw [he]
  fun_prop

/-- `D_ε` is linear: `D_ε(F − cG) = D_ε F − c D_ε G` at points of differentiability. -/
theorem ringD_sub_mul (R c : ℝ) {F G : ProfilePoint → ℝ} {x : ProfilePoint}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    ringD R (fun X => F X - c * G X) x = ringD R F x - c * ringD R G x := by
  have hfd : fderiv ℝ (fun X => F X - c * G X) x = fderiv ℝ F x - c • fderiv ℝ G x := by
    rw [fderiv_fun_sub hF (hG.const_mul c), fderiv_const_mul hG c]
  simp only [ringD, ageOperator, partialQ, partialEta, partialAge, hfd,
    _root_.sub_apply, _root_.smul_apply, smul_eq_mul]
  ring

/-! ## Differentiation of normalized fields -/

/-- `r⁻¹ = ε a_r` in the chart (so `r⁻² = ε² a_r²`). -/
theorem inv_radius_eq (R r : ℝ) (hR : R ≠ 0) (hr : r ≠ 0) :
    1 / r = ringEps R * radialScale R r := by
  simp only [ringEps, radialScale]
  field_simp

/-- `∂_r a_r^k = −kε a_r^{k+1}`, from `∂_r a_r = −ε a_r²`. -/
theorem hasDerivAt_radialScale_pow (R r : ℝ) (k : ℕ) (hR : R ≠ 0) (hr : r ≠ 0) :
    HasDerivAt (fun x => radialScale R x ^ k)
      (-(k : ℝ) * ringEps R * radialScale R r ^ (k + 1)) r := by
  have h : HasDerivAt (fun x => radialScale R x ^ k)
      ((k : ℝ) * radialScale R r ^ (k - 1) * (-radialScale R r / r)) r :=
    (hasDerivAt_radialScale R r hr).pow k
  refine h.congr_deriv ?_
  rcases k with _ | n
  · simp
  · have hinv := inv_radius_eq R r hR hr
    rw [Nat.add_sub_cancel, div_eq_mul_one_div, hinv]
    push_cast
    ring

/-- Radial rule for normalized fields: `∂_r(a_r^k g) = a_r^{k+1}(D_ε − kε) g`
(tex lines 2881–2882 for `k = 1`; `k = 2` is the pressure rule). -/
theorem hasDerivAt_scaledLift_radial (R : ℝ) (k : ℕ) (g : ProfilePoint → ℝ) (r z t : ℝ)
    (hR : R ≠ 0) (hr : r ≠ 0) (hg : DifferentiableAt ℝ g (profileChart R r z t)) :
    HasDerivAt (fun x => scaledLift R k g x z t)
      (radialScale R r ^ (k + 1) * (ringD R g (profileChart R r z t) -
        (k : ℝ) * ringEps R * g (profileChart R r z t))) r := by
  have h1 := hasDerivAt_radialScale_pow R r k hR hr
  have h2 := hasDerivAt_cylinderLift_radial_ringD R r z t hR hr g hg
  refine (h1.mul h2).congr_deriv ?_
  simp only [cylinderLift]
  ring

/-- Axial rule for normalized fields: `∂_z(a_r^k g) = a_r^{k+1} g_η`. -/
theorem hasDerivAt_scaledLift_axial (R : ℝ) (k : ℕ) (g : ProfilePoint → ℝ) (r z t : ℝ)
    (hg : DifferentiableAt ℝ g (profileChart R r z t)) :
    HasDerivAt (fun y => scaledLift R k g r y t)
      (radialScale R r ^ (k + 1) * partialEta g (profileChart R r z t)) z := by
  have h2 := hasDerivAt_cylinderLift_axial_partialEta R r z t g hg
  refine (h2.const_mul (radialScale R r ^ k)).congr_deriv ?_
  simp only [cylinderLift]
  ring

/-- Time rule for normalized fields: `∂_t(a_r^k g) = a_r^{k+2} g_s`. -/
theorem hasDerivAt_scaledLift_time (R : ℝ) (k : ℕ) (g : ProfilePoint → ℝ) (r z t : ℝ)
    (hg : DifferentiableAt ℝ g (profileChart R r z t)) :
    HasDerivAt (fun τ => scaledLift R k g r z τ)
      (radialScale R r ^ (k + 2) * partialAge g (profileChart R r z t)) t := by
  have h2 := hasDerivAt_cylinderLift_time_partialAge R r z t g hg
  refine (h2.const_mul (radialScale R r ^ k)).congr_deriv ?_
  simp only [cylinderLift]
  ring

/-- `∂_r(a_r^k g) = a_r^{k+1}(D_ε − kε)g` as an identity of normalized fields off the axis. -/
theorem physR_scaledLift (R : ℝ) (k : ℕ) {g : ProfilePoint → ℝ} (hR : R ≠ 0)
    (hg : Differentiable ℝ g) {r : ℝ} (z t : ℝ) (hr : r ≠ 0) :
    physR (scaledLift R k g) r z t =
      scaledLift R (k + 1) (fun X => ringD R g X - (k : ℝ) * ringEps R * g X) r z t :=
  (hasDerivAt_scaledLift_radial R k g r z t hR hr (hg _)).deriv

/-- `∂_z(a_r^k g) = a_r^{k+1} g_η` as an identity of normalized fields. -/
theorem physZ_scaledLift (R : ℝ) (k : ℕ) {g : ProfilePoint → ℝ} (hg : Differentiable ℝ g) :
    physZ (scaledLift R k g) = scaledLift R (k + 1) (partialEta g) := by
  funext r z t
  exact (hasDerivAt_scaledLift_axial R k g r z t (hg _)).deriv

/-- `∂_t(a_r^k g) = a_r^{k+2} g_s` as an identity of normalized fields. -/
theorem physT_scaledLift (R : ℝ) (k : ℕ) {g : ProfilePoint → ℝ} (hg : Differentiable ℝ g) :
    physT (scaledLift R k g) = scaledLift R (k + 2) (partialAge g) := by
  funext r z t
  exact (hasDerivAt_scaledLift_time R k g r z t (hg _)).deriv

/-- The manuscript's example (tex lines 2881–2882): differentiating `a_r f` radially gives
`a_r²(D_ε − ε) f`. -/
theorem physR_velocity (R : ℝ) {f : ProfilePoint → ℝ} (hR : R ≠ 0)
    (hf : Differentiable ℝ f) {r : ℝ} (z t : ℝ) (hr : r ≠ 0) :
    physR (scaledLift R 1 f) r z t =
      radialScale R r ^ 2 * (ringD R f (profileChart R r z t) -
        ringEps R * f (profileChart R r z t)) := by
  rw [physR_scaledLift R 1 hR hf z t hr]
  simp [scaledLift, cylinderLift]

/-- Second radial derivative of a velocity component:
`∂_r²(a_r f) = a_r³(D_ε² − 3εD_ε + 2ε²) f` off the axis. -/
theorem physR_physR_velocity (R : ℝ) {f : ProfilePoint → ℝ} (hR : R ≠ 0)
    (hf : ContDiff ℝ 2 f) {r : ℝ} (z t : ℝ) (hr : r ≠ 0) :
    physR (physR (scaledLift R 1 f)) r z t =
      radialScale R r ^ 3 * (ringD R (ringD R f) (profileChart R r z t) -
        3 * ringEps R * ringD R f (profileChart R r z t) +
        2 * ringEps R ^ 2 * f (profileChart R r z t)) := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hD : Differentiable ℝ (ringD R f) := differentiable_ringD R hf
  set g1 : ProfilePoint → ℝ := fun X => ringD R f X - ((1 : ℕ) : ℝ) * ringEps R * f X
    with hg1
  have hg1d : Differentiable ℝ g1 := by
    rw [hg1]
    fun_prop
  have hev : (fun x => physR (scaledLift R 1 f) x z t) =ᶠ[𝓝 r]
      (fun x => scaledLift R 2 g1 x z t) :=
    (eventually_ne_nhds hr).mono fun x hx => physR_scaledLift R 1 hR hf1 z t hx
  have h2 : physR (physR (scaledLift R 1 f)) r z t = physR (scaledLift R 2 g1) r z t :=
    hev.deriv_eq
  rw [h2, physR_scaledLift R 2 hR hg1d z t hr]
  have hlin : ringD R g1 (profileChart R r z t) =
      ringD R (ringD R f) (profileChart R r z t) -
        ((1 : ℕ) : ℝ) * ringEps R * ringD R f (profileChart R r z t) :=
    ringD_sub_mul R _ (hD _) (hf1 _)
  simp only [scaledLift, cylinderLift]
  rw [hlin]
  simp only [hg1]
  push_cast
  ring

/-- Second axial derivative of a normalized field: `∂_z²(a_r g) = a_r³ g_ηη`. -/
theorem physZ_physZ_velocity (R : ℝ) {f : ProfilePoint → ℝ} (hf : ContDiff ℝ 2 f) :
    physZ (physZ (scaledLift R 1 f)) = scaledLift R 3 (partialEta (partialEta f)) := by
  rw [physZ_scaledLift R 1 (hf.differentiable (by norm_num)),
    physZ_scaledLift R 2 (differentiable_partialEta hf)]

/-! ## The two diffusion polynomials -/

/-- Radial diffusion polynomial (tex lines 2883–2886): off the axis,
`(∂_r² + r⁻¹∂_r − r⁻² + ∂_z²)(a_r f) = a_r³(D_ε² − 2εD_ε + ∂_η²) f`. -/
theorem radialVectorLaplacian_velocity (R : ℝ) {f : ProfilePoint → ℝ} (hR : R ≠ 0)
    (hf : ContDiff ℝ 2 f) {r : ℝ} (z t : ℝ) (hr : r ≠ 0) :
    radialVectorLaplacian (scaledLift R 1 f) r z t =
      radialScale R r ^ 3 * ringDiffusionRadial R f (profileChart R r z t) := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hinv := inv_radius_eq R r hR hr
  simp only [radialVectorLaplacian]
  rw [physR_physR_velocity R hR hf z t hr, physR_velocity R hR hf1 z t hr,
    physZ_physZ_velocity R hf]
  simp only [ringDiffusionRadial, scaledLift, cylinderLift]
  rw [div_eq_mul_one_div _ r, div_eq_mul_one_div _ (r ^ 2), ← one_div_pow, hinv]
  ring

/-- Axial diffusion polynomial (tex lines 2884–2886): off the axis,
`(∂_r² + r⁻¹∂_r + ∂_z²)(a_r h) = a_r³(D_ε² − 2εD_ε + ε² + ∂_η²) h`. -/
theorem axialVectorLaplacian_velocity (R : ℝ) {h : ProfilePoint → ℝ} (hR : R ≠ 0)
    (hh : ContDiff ℝ 2 h) {r : ℝ} (z t : ℝ) (hr : r ≠ 0) :
    axialVectorLaplacian (scaledLift R 1 h) r z t =
      radialScale R r ^ 3 * ringDiffusionAxial R h (profileChart R r z t) := by
  have hh1 : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hinv := inv_radius_eq R r hR hr
  simp only [axialVectorLaplacian]
  rw [physR_physR_velocity R hR hh z t hr, physR_velocity R hR hh1 z t hr,
    physZ_physZ_velocity R hh]
  simp only [ringDiffusionAxial, scaledLift, cylinderLift]
  rw [div_eq_mul_one_div _ r, hinv]
  ring

/-! ## The residual in the chart -/

/-- **Unit B0187** (`eq:st18-t00190`, tex lines 2867–2888). Let `R ≥ 2`, `ε = R⁻¹`, and let
`f, h` be `C²` profiles and `Π` a differentiable profile of `(q, η, s)`. For the normalized
no-swirl fields `u_r = a_r f`, `u_z = a_r h` and pressure `p = a_r² Π`, at every `r > 0`, `z`
and `t > 0` the cylindrical Navier–Stokes residual at viscosity `ν`, divided by `a_r³`, is
exactly the chart expression `eq:st18-t00190`:
radial `f_s + f D_ε f + h f_η − ε f² − ν(D_ε² − 2εD_ε + ∂_η²) f + (D_ε − 2ε) Π`,
axial `h_s + f D_ε h + h h_η − ε f h − ν(D_ε² − 2εD_ε + ε² + ∂_η²) h + Π_η`,
all evaluated at the chart point `(q, η, s)` of `(r, z, t)`. -/
theorem cylindricalResidual_eq_chart (R ν : ℝ) (hR : 2 ≤ R) (f h pres : ProfilePoint → ℝ)
    (hf : ContDiff ℝ 2 f) (hh : ContDiff ℝ 2 h) (hp : Differentiable ℝ pres)
    (r z t : ℝ) (hr : 0 < r) (_ht : 0 < t) :
    cylRadialResidual ν (scaledLift R 1 f) (scaledLift R 1 h) (scaledLift R 2 pres) r z t =
        radialScale R r ^ 3 * chartRadialResidual R ν f h pres (profileChart R r z t) ∧
    cylAxialResidual ν (scaledLift R 1 f) (scaledLift R 1 h) (scaledLift R 2 pres) r z t =
        radialScale R r ^ 3 * chartAxialResidual R ν f h pres (profileChart R r z t) := by
  have hR0 : R ≠ 0 := by linarith
  have hr0 : r ≠ 0 := hr.ne'
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hh1 : Differentiable ℝ h := hh.differentiable (by norm_num)
  constructor
  · simp only [cylRadialResidual]
    rw [radialVectorLaplacian_velocity R hR0 hf z t hr0, physR_velocity R hR0 hf1 z t hr0,
      physR_scaledLift R 2 hR0 hp z t hr0, physZ_scaledLift R 1 hf1,
      physT_scaledLift R 1 hf1]
    simp only [chartRadialResidual, scaledLift, cylinderLift]
    push_cast
    ring
  · simp only [cylAxialResidual]
    rw [axialVectorLaplacian_velocity R hR0 hh z t hr0, physR_velocity R hR0 hh1 z t hr0,
      physZ_scaledLift R 2 hp, physZ_scaledLift R 1 hh1, physT_scaledLift R 1 hh1]
    simp only [chartAxialResidual, scaledLift, cylinderLift]
    ring

/-- **Unit B0187, operator form**: for `C²` profiles `f, h` and a differentiable `Π`, the
identity `eq:st18-t00190` holds at every point of the physical domain `r > 0`, `t > 0`. -/
theorem cylindricalResidual_eq_chart_on_domain (R ν : ℝ) (hR : 2 ≤ R)
    (f h pres : ProfilePoint → ℝ)
    (hf : ContDiff ℝ 2 f) (hh : ContDiff ℝ 2 h) (hp : Differentiable ℝ pres) :
    ∀ r z t : ℝ, 0 < r → 0 < t →
      cylRadialResidual ν (scaledLift R 1 f) (scaledLift R 1 h) (scaledLift R 2 pres) r z t =
          radialScale R r ^ 3 * chartRadialResidual R ν f h pres (profileChart R r z t) ∧
      cylAxialResidual ν (scaledLift R 1 f) (scaledLift R 1 h) (scaledLift R 2 pres) r z t =
          radialScale R r ^ 3 * chartAxialResidual R ν f h pres (profileChart R r z t) :=
  fun r z t hr ht => cylindricalResidual_eq_chart R ν hR f h pres hf hh hp r z t hr ht

end UnforcedLeray.B0187
