import UnforcedLeray.Units.B0185
import UnforcedLeray.Units.B0140

/-!
# B0188 `eq:st18-t00192` (with `eq:st18-t00191`): the exact residual polynomial of the lift

Blueprint unit B0188, labels `eq:st18-t00191` and `eq:st18-t00192`, `paper/main.tex`
lines 2890–2914 (subsection "Coordinates and equations" of the exact solenoidal lift);
infrastructure INF31 (the operator algebra with `[∂_q, K] = 0`).

Statement in words (tex lines 2890–2914). Take, in the chart residual `eq:st18-t00190`
(unit B0187), `f = v₁`, `h = v₂ + εH` and `Π = p`, where `v = ∇^⊥ψ = (−ψ_η, ψ_q)` is the
train with its stream `ψ` and pressure `p` (unit B0140) and `H = (1 − K)ψ` (unit B0185). The
residual `r = (r_r, r_z)` is the finite exact polynomial
`r_r = εA₁ + ε²B₁`, `r_z = εA₂ + ε²B₂ + ε³B₃` (`eq:st18-t00191`), with (`eq:st18-t00192`)
* `A₁ = −v₁Kv₁ + H(v₁)_η − v₁² + 2ν(K+1)(v₁)_q − (K+2)p`,
* `A₂ = (∂_s + v·∇ − νΔ)H + H(v₂)_η − v₁(K+1)v₂ + 2ν(K+1)(v₂)_q`,
* `B₁ = −νK(K+2)v₁`,
* `B₂ = −v₁(K+1)H + HH_η + 2ν(K+1)H_q − ν(K+1)²v₂`,
* `B₃ = −ν(K+1)²H`.
These follow by direct expansion of `eq:st18-t00190` and cancellation of the exact planar
equations; they hold at every age (no truncation).

Conventions. Profiles are functions of `ProfilePoint = ℝ × (ℝ × ℝ)`, `x = (q, (η, s))`
(unit B0184). `K = η∂_η + 2s∂_s` is `ageOperator`, `D_ε = ∂_q − εK` is `ringD`, `ε = R⁻¹` is
`ringEps R`; `v₁ = streamV1 ψ`, `v₂ = streamV2 ψ`, `H = ageDefect ψ`, `v₂ + εH = axialProfile R ψ`
(unit B0185); the chart residual lines are B0187's `chartRadialResidual`,
`chartAxialResidual`. The operator `K + a` is `ageShift a` (so `(K+1)`, `(K+2)`, and
`(K+1)² = (K+1)∘(K+1)`, `K(K+2) = K∘(K+2)` are written literally as compositions). The planar
Navier–Stokes residuals of the train in profile variables are `planarRadialResidual`,
`planarAxialResidual`: `v_s + v·∇v − νΔv + ∇p`, componentwise.

Contents.
* INF31: `partialQ_ageOperator` (`[∂_q, K] = 0` at a point where the profile is `C²`),
  `ringDiffusionRadial_eq` (`D_ε² − 2εD_ε + ∂_η² = Δ − 2ε(K+1)∂_q + ε²K(K+2)`),
  `ringDiffusionAxial_eq` (`… + ε² = Δ − 2ε(K+1)∂_q + ε²(K+1)²`).
* `radial_expansion`, `axial_expansion`: the exact expansions before the planar equations are
  used (`r_r = (planar radial residual) + εA₁ + ε²B₁`, and similarly for `r_z`).
* `residual_polynomial`: **the unit** in profile variables, at every profile point where the
  stream is `C³` and the planar equations hold.
* `cylindricalResidual_polynomial`: the same identity for the physical lift
  `u_r = a_r v₁`, `u_z = a_r(v₂ + εH)`, `p_raw = a_r²p` (B0185, B0187): the cylindrical
  Navier–Stokes residual divided by `a_r³` is `εA₁ + ε²B₁`, resp. `εA₂ + ε²B₂ + ε³B₃`.
* `train_planar_equations`: B0140's momentum equation, rewritten in profile variables
  (`planarRadialResidual = planarAxialResidual = 0` at every `s > 0`).
* `train_residual_polynomial`, `actualTrain_residual_polynomial`: the unit for the actual train
  of B0140 (`IsTrain`, resp. the chosen `B0140.train`), at every age `s > 0`, conditionally on
  the named hypothesis `TrainStreamC3` (the stream of the train is `C³` jointly in `(q, η, s)`
  on `s > 0`, part of INF16, not built).

Hypotheses. The manuscript's train is smooth. The algebraic identities are stated at a single
profile point `x` and need only `ψ` of class `C³` near `x` (`ContDiffAt ℝ 3 ψ x`): `D_ε²`
applied to `v₂ + εH` involves third derivatives of `ψ`, and `[∂_q, K] = 0` is the symmetry of
second derivatives. This rules out Lean's junk value `fderiv = 0` at non-differentiable points.
The pressure enters only through its first derivatives at `x`, which appear identically in the
chart residual and in the planar equation, so no hypothesis on `p` is needed for the profile
identities (the physical identity inherits B0187's `p` differentiable). The parameter `R` is
arbitrary (the manuscript's `R ≥ 2` is not used by the algebra; the physical identity keeps it,
as B0187 does).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.B0188

open Set Filter Topology
open UnforcedLeray.RingLift UnforcedLeray.B0184 UnforcedLeray.B0187 UnforcedLeray.B0185

/-! ## Planar operators and the coefficients (`eq:st18-t00192`) -/

/-- The planar Laplacian `Δg = ∂_q²g + ∂_η²g` of a profile. -/
def profileLap (g : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ :=
  partialQ (partialQ g) x + partialEta (partialEta g) x

/-- The operator `K + a` (tex lines 2898–2911 use `K + 1` and `K + 2`): `(K + a)g = Kg + ag`. -/
def ageShift (a : ℝ) (g : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ :=
  ageOperator g x + a * g x

/-- The planar transport–diffusion operator `(∂_s + v·∇ − νΔ)g` along the planar field
`v = ∇^⊥ψ = (v₁, v₂)` (tex line 2904). -/
def transportDiffusion (ν : ℝ) (ψ g : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ :=
  partialAge g x + streamV1 ψ x * partialQ g x + streamV2 ψ x * partialEta g x
    - ν * profileLap g x

/-- Radial component of the planar Navier–Stokes residual of `(v, p)`, `v = ∇^⊥ψ`, in profile
variables: `(v₁)_s + v·∇v₁ − νΔv₁ + p_q` (the train equation `eq:st18-t00140`, tex 2141). -/
def planarRadialResidual (ν : ℝ) (ψ p : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ :=
  transportDiffusion ν ψ (streamV1 ψ) x + partialQ p x

/-- Axial component of the planar Navier–Stokes residual: `(v₂)_s + v·∇v₂ − νΔv₂ + p_η`. -/
def planarAxialResidual (ν : ℝ) (ψ p : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ :=
  transportDiffusion ν ψ (streamV2 ψ) x + partialEta p x

/-- `A₁ = −v₁Kv₁ + H(v₁)_η − v₁² + 2ν(K+1)(v₁)_q − (K+2)p` (tex line 2902). -/
def coeffA₁ (ν : ℝ) (ψ p : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ :=
  -(streamV1 ψ x * ageOperator (streamV1 ψ) x) + ageDefect ψ x * partialEta (streamV1 ψ) x
    - streamV1 ψ x ^ 2 + 2 * ν * ageShift 1 (partialQ (streamV1 ψ)) x - ageShift 2 p x

/-- `A₂ = (∂_s + v·∇ − νΔ)H + H(v₂)_η − v₁(K+1)v₂ + 2ν(K+1)(v₂)_q` (tex lines 2904–2906). -/
def coeffA₂ (ν : ℝ) (ψ : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ :=
  transportDiffusion ν ψ (ageDefect ψ) x + ageDefect ψ x * partialEta (streamV2 ψ) x
    - streamV1 ψ x * ageShift 1 (streamV2 ψ) x + 2 * ν * ageShift 1 (partialQ (streamV2 ψ)) x

/-- `B₁ = −νK(K+2)v₁` (tex line 2907). -/
def coeffB₁ (ν : ℝ) (ψ : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ :=
  -ν * ageOperator (ageShift 2 (streamV1 ψ)) x

/-- `B₂ = −v₁(K+1)H + HH_η + 2ν(K+1)H_q − ν(K+1)²v₂` (tex lines 2908–2909). -/
def coeffB₂ (ν : ℝ) (ψ : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ :=
  -(streamV1 ψ x * ageShift 1 (ageDefect ψ) x) + ageDefect ψ x * partialEta (ageDefect ψ) x
    + 2 * ν * ageShift 1 (partialQ (ageDefect ψ)) x
    - ν * ageShift 1 (ageShift 1 (streamV2 ψ)) x

/-- `B₃ = −ν(K+1)²H` (tex line 2910). -/
def coeffB₃ (ν : ℝ) (ψ : ProfilePoint → ℝ) (x : ProfilePoint) : ℝ :=
  -ν * ageShift 1 (ageShift 1 (ageDefect ψ)) x

/-! ## Linearity of the profile operators at points of differentiability -/

theorem fderiv_add_mul_apply {F G : ProfilePoint → ℝ} {y : ProfilePoint}
    (hF : DifferentiableAt ℝ F y) (hG : DifferentiableAt ℝ G y) (c : ℝ) (w : ProfilePoint) :
    fderiv ℝ (fun X => F X + c * G X) y w = fderiv ℝ F y w + c * fderiv ℝ G y w := by
  rw [fderiv_fun_add hF (hG.const_mul c), fderiv_const_mul hG c]
  simp

theorem partialQ_add_mul {F G : ProfilePoint → ℝ} {y : ProfilePoint}
    (hF : DifferentiableAt ℝ F y) (hG : DifferentiableAt ℝ G y) (c : ℝ) :
    partialQ (fun X => F X + c * G X) y = partialQ F y + c * partialQ G y :=
  fderiv_add_mul_apply hF hG c eqDir

theorem partialEta_add_mul {F G : ProfilePoint → ℝ} {y : ProfilePoint}
    (hF : DifferentiableAt ℝ F y) (hG : DifferentiableAt ℝ G y) (c : ℝ) :
    partialEta (fun X => F X + c * G X) y = partialEta F y + c * partialEta G y :=
  fderiv_add_mul_apply hF hG c eηDir

theorem partialAge_add_mul {F G : ProfilePoint → ℝ} {y : ProfilePoint}
    (hF : DifferentiableAt ℝ F y) (hG : DifferentiableAt ℝ G y) (c : ℝ) :
    partialAge (fun X => F X + c * G X) y = partialAge F y + c * partialAge G y :=
  fderiv_add_mul_apply hF hG c esDir

theorem ageOperator_add_mul {F G : ProfilePoint → ℝ} {y : ProfilePoint}
    (hF : DifferentiableAt ℝ F y) (hG : DifferentiableAt ℝ G y) (c : ℝ) :
    ageOperator (fun X => F X + c * G X) y = ageOperator F y + c * ageOperator G y := by
  unfold ageOperator
  rw [partialEta_add_mul hF hG c, partialAge_add_mul hF hG c]
  ring

theorem ringD_add_mul (R : ℝ) {F G : ProfilePoint → ℝ} {y : ProfilePoint}
    (hF : DifferentiableAt ℝ F y) (hG : DifferentiableAt ℝ G y) (c : ℝ) :
    ringD R (fun X => F X + c * G X) y = ringD R F y + c * ringD R G y := by
  unfold ringD
  rw [partialQ_add_mul hF hG c, ageOperator_add_mul hF hG c]
  ring

/-- Second-order linearity: if a first-order operator `Op` is linear near `x` on `F + cG`, its
directional derivatives at `x` are linear as well. -/
theorem fderiv_op_add_mul (Op : (ProfilePoint → ℝ) → ProfilePoint → ℝ)
    {F G : ProfilePoint → ℝ} {x : ProfilePoint} (c : ℝ) (w : ProfilePoint)
    (hlin : ∀ᶠ y in 𝓝 x, Op (fun X => F X + c * G X) y = Op F y + c * Op G y)
    (hF : DifferentiableAt ℝ (Op F) x) (hG : DifferentiableAt ℝ (Op G) x) :
    fderiv ℝ (Op (fun X => F X + c * G X)) x w =
      fderiv ℝ (Op F) x w + c * fderiv ℝ (Op G) x w := by
  have h : Op (fun X => F X + c * G X) =ᶠ[𝓝 x] fun y => Op F y + c * Op G y := hlin
  rw [h.fderiv_eq]
  exact fderiv_add_mul_apply hF hG c w

/-! ## Regularity -/

theorem eventually_differentiableAt {g : ProfilePoint → ℝ} {x : ProfilePoint}
    (hg : ContDiffAt ℝ 2 g x) : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y :=
  (hg.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by norm_num)

theorem differentiableAt_partialQ {g : ProfilePoint → ℝ} {x : ProfilePoint}
    (hg : ContDiffAt ℝ 2 g x) : DifferentiableAt ℝ (partialQ g) x :=
  (hasFDerivAt_fderiv_apply (differentiableAt_fderiv_of_contDiffAt hg) eqDir).differentiableAt

theorem differentiableAt_partialEta {g : ProfilePoint → ℝ} {x : ProfilePoint}
    (hg : ContDiffAt ℝ 2 g x) : DifferentiableAt ℝ (partialEta g) x :=
  (hasFDerivAt_fderiv_apply (differentiableAt_fderiv_of_contDiffAt hg) eηDir).differentiableAt

theorem differentiableAt_partialAge {g : ProfilePoint → ℝ} {x : ProfilePoint}
    (hg : ContDiffAt ℝ 2 g x) : DifferentiableAt ℝ (partialAge g) x :=
  (hasFDerivAt_fderiv_apply (differentiableAt_fderiv_of_contDiffAt hg) esDir).differentiableAt

theorem differentiableAt_ageOperator {g : ProfilePoint → ℝ} {x : ProfilePoint}
    (hg : ContDiffAt ℝ 2 g x) : DifferentiableAt ℝ (ageOperator g) x := by
  have he := differentiableAt_partialEta hg
  have hs := differentiableAt_partialAge hg
  have hη := (hasFDerivAt_eta x).differentiableAt
  have hσ := (hasFDerivAt_age x).differentiableAt
  exact (hη.fun_mul he).fun_add ((hσ.const_mul 2).fun_mul hs)

theorem contDiffAt_streamV1 {ψ : ProfilePoint → ℝ} {x : ProfilePoint}
    (hψ : ContDiffAt ℝ 3 ψ x) : ContDiffAt ℝ 2 (streamV1 ψ) x :=
  ((hψ.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const).neg

theorem contDiffAt_streamV2 {ψ : ProfilePoint → ℝ} {x : ProfilePoint}
    (hψ : ContDiffAt ℝ 3 ψ x) : ContDiffAt ℝ 2 (streamV2 ψ) x :=
  (hψ.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const

theorem contDiffAt_ageDefect {ψ : ProfilePoint → ℝ} {x : ProfilePoint}
    (hψ : ContDiffAt ℝ 3 ψ x) : ContDiffAt ℝ 2 (ageDefect ψ) x := by
  have hD := hψ.fderiv_right (m := 2) (by norm_num)
  have he : ContDiffAt ℝ 2 (fun y => fderiv ℝ ψ y eηDir) x := hD.clm_apply contDiffAt_const
  have hs : ContDiffAt ℝ 2 (fun y => fderiv ℝ ψ y esDir) x := hD.clm_apply contDiffAt_const
  have hψ2 : ContDiffAt ℝ 2 ψ x := hψ.of_le (by norm_num)
  have hη : ContDiffAt ℝ 2 (fun y : ProfilePoint => y.2.1) x := contDiff_snd.fst.contDiffAt
  have hσ : ContDiffAt ℝ 2 (fun y : ProfilePoint => y.2.2) x := contDiff_snd.snd.contDiffAt
  have hK : ContDiffAt ℝ 2 (ageOperator ψ) x :=
    (hη.mul he).add ((contDiffAt_const.mul hσ).mul hs)
  exact hψ2.sub hK

/-! ## INF31: the operator algebra with `[∂_q, K] = 0` -/

/-- `[∂_q, K] = 0` at a point where the profile is `C²` (INF31): `∂_q(Kg) = K(∂_q g)`, since
`η, s` do not depend on `q` and the mixed second derivatives are symmetric. -/
theorem partialQ_ageOperator {g : ProfilePoint → ℝ} {x : ProfilePoint}
    (hg : ContDiffAt ℝ 2 g x) :
    partialQ (ageOperator g) x = ageOperator (partialQ g) x := by
  have hd := differentiableAt_fderiv_of_contDiffAt hg
  have hsym : IsSymmSndFDerivAt ℝ g x := hg.isSymmSndFDerivAt (by simp)
  have he := hasFDerivAt_fderiv_apply hd eηDir
  have hs := hasFDerivAt_fderiv_apply hd esDir
  have hq : HasFDerivAt (partialQ g) ((fderiv ℝ (fderiv ℝ g) x).flip eqDir) x :=
    hasFDerivAt_fderiv_apply hd eqDir
  have hK := ((hasFDerivAt_eta x).fun_mul he).fun_add
    (((hasFDerivAt_age x).const_mul 2).fun_mul hs)
  have hK' : HasFDerivAt (ageOperator g) _ x := hK
  have s1 := hsym eqDir eηDir
  have s2 := hsym eqDir esDir
  show fderiv ℝ (ageOperator g) x eqDir =
    x.2.1 * fderiv ℝ (partialQ g) x eηDir + 2 * x.2.2 * fderiv ℝ (partialQ g) x esDir
  rw [hK'.fderiv, hq.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul] at s1 s2 ⊢
  simp only [eqDir, eηDir, esDir] at s1 s2 ⊢
  linear_combination (x.2.1) * s1 + (2 * x.2.2) * s2

/-- `K(K + a)g = K(Kg) + aKg` at a point where `g` is `C²`. -/
theorem ageOperator_ageShift (a : ℝ) {g : ProfilePoint → ℝ} {x : ProfilePoint}
    (hg : ContDiffAt ℝ 2 g x) :
    ageOperator (ageShift a g) x = ageOperator (ageOperator g) x + a * ageOperator g x :=
  ageOperator_add_mul (differentiableAt_ageOperator hg) (hg.differentiableAt (by norm_num)) a

/-- `(K + b)(K + a)g = K(Kg) + (a + b)Kg + abg` at a point where `g` is `C²`. -/
theorem ageShift_ageShift (a b : ℝ) {g : ProfilePoint → ℝ} {x : ProfilePoint}
    (hg : ContDiffAt ℝ 2 g x) :
    ageShift b (ageShift a g) x =
      ageOperator (ageOperator g) x + (a + b) * ageOperator g x + a * b * g x := by
  rw [ageShift, ageOperator_ageShift a hg, ageShift]
  ring

/-- **INF31, radial diffusion polynomial**: at a point where `g` is `C²`,
`(D_ε² − 2εD_ε + ∂_η²)g = Δg − 2ε(K+1)∂_q g + ε²K(K+2)g`. -/
theorem ringDiffusionRadial_eq (R : ℝ) {g : ProfilePoint → ℝ} {x : ProfilePoint}
    (hg : ContDiffAt ℝ 2 g x) :
    ringDiffusionRadial R g x =
      profileLap g x - 2 * ringEps R * ageShift 1 (partialQ g) x +
        ringEps R ^ 2 * ageOperator (ageShift 2 g) x := by
  have hq := differentiableAt_partialQ hg
  have hK := differentiableAt_ageOperator hg
  have hD : ringD R g = fun X => partialQ g X - ringEps R * ageOperator g X := rfl
  have h1 : ringD R (ringD R g) x =
      ringD R (partialQ g) x - ringEps R * ringD R (ageOperator g) x := by
    rw [hD]
    exact ringD_sub_mul R _ hq hK
  have hc := partialQ_ageOperator hg
  rw [ringDiffusionRadial, h1, ageOperator_ageShift 2 hg]
  simp only [ringD, ageShift, profileLap]
  rw [hc]
  ring

/-- **INF31, axial diffusion polynomial**: at a point where `g` is `C²`,
`(D_ε² − 2εD_ε + ε² + ∂_η²)g = Δg − 2ε(K+1)∂_q g + ε²(K+1)²g`. -/
theorem ringDiffusionAxial_eq (R : ℝ) {g : ProfilePoint → ℝ} {x : ProfilePoint}
    (hg : ContDiffAt ℝ 2 g x) :
    ringDiffusionAxial R g x =
      profileLap g x - 2 * ringEps R * ageShift 1 (partialQ g) x +
        ringEps R ^ 2 * ageShift 1 (ageShift 1 g) x := by
  have h := ringDiffusionRadial_eq R hg
  have h' : ringDiffusionAxial R g x = ringDiffusionRadial R g x + ringEps R ^ 2 * g x := by
    simp only [ringDiffusionAxial, ringDiffusionRadial]
    ring
  rw [h', h, ageOperator_ageShift 2 hg, ageShift_ageShift 1 1 hg]
  ring

/-! ## Linearity of the diffusion polynomial on `v₂ + εH` -/

/-- The radial diffusion polynomial is linear on `F + cG` at a point where `F, G` are `C²`. -/
theorem ringDiffusionRadial_add_mul (R : ℝ) {F G : ProfilePoint → ℝ} {x : ProfilePoint}
    (hF : ContDiffAt ℝ 2 F x) (hG : ContDiffAt ℝ 2 G x) (c : ℝ) :
    ringDiffusionRadial R (fun X => F X + c * G X) x =
      ringDiffusionRadial R F x + c * ringDiffusionRadial R G x := by
  have hS : ContDiffAt ℝ 2 (fun X => F X + c * G X) x := hF.add (contDiffAt_const.mul hG)
  have hFd := eventually_differentiableAt hF
  have hGd := eventually_differentiableAt hG
  have hF1 : DifferentiableAt ℝ F x := hF.differentiableAt (by norm_num)
  have hG1 : DifferentiableAt ℝ G x := hG.differentiableAt (by norm_num)
  -- eventual linearity of the first-order operators
  have lq : ∀ᶠ y in 𝓝 x, partialQ (fun X => F X + c * G X) y = partialQ F y + c * partialQ G y :=
    (hFd.and hGd).mono fun y hy => partialQ_add_mul hy.1 hy.2 c
  have le : ∀ᶠ y in 𝓝 x,
      partialEta (fun X => F X + c * G X) y = partialEta F y + c * partialEta G y :=
    (hFd.and hGd).mono fun y hy => partialEta_add_mul hy.1 hy.2 c
  have lK : ∀ᶠ y in 𝓝 x,
      ageOperator (fun X => F X + c * G X) y = ageOperator F y + c * ageOperator G y :=
    (hFd.and hGd).mono fun y hy => ageOperator_add_mul hy.1 hy.2 c
  have qq : partialQ (partialQ (fun X => F X + c * G X)) x =
      partialQ (partialQ F) x + c * partialQ (partialQ G) x :=
    fderiv_op_add_mul partialQ c eqDir lq (differentiableAt_partialQ hF)
      (differentiableAt_partialQ hG)
  have ee : partialEta (partialEta (fun X => F X + c * G X)) x =
      partialEta (partialEta F) x + c * partialEta (partialEta G) x :=
    fderiv_op_add_mul partialEta c eηDir le (differentiableAt_partialEta hF)
      (differentiableAt_partialEta hG)
  have Kq : ageOperator (partialQ (fun X => F X + c * G X)) x =
      ageOperator (partialQ F) x + c * ageOperator (partialQ G) x := by
    unfold ageOperator
    have h1 := fderiv_op_add_mul partialQ c eηDir lq (differentiableAt_partialQ hF)
      (differentiableAt_partialQ hG)
    have h2 := fderiv_op_add_mul partialQ c esDir lq (differentiableAt_partialQ hF)
      (differentiableAt_partialQ hG)
    simp only [partialEta, partialAge]
    rw [h1, h2]
    ring
  have KK : ageOperator (ageOperator (fun X => F X + c * G X)) x =
      ageOperator (ageOperator F) x + c * ageOperator (ageOperator G) x := by
    have h1 := fderiv_op_add_mul ageOperator c eηDir lK (differentiableAt_ageOperator hF)
      (differentiableAt_ageOperator hG)
    have h2 := fderiv_op_add_mul ageOperator c esDir lK (differentiableAt_ageOperator hF)
      (differentiableAt_ageOperator hG)
    show x.2.1 * fderiv ℝ (ageOperator (fun X => F X + c * G X)) x eηDir +
        2 * x.2.2 * fderiv ℝ (ageOperator (fun X => F X + c * G X)) x esDir =
      (x.2.1 * fderiv ℝ (ageOperator F) x eηDir + 2 * x.2.2 * fderiv ℝ (ageOperator F) x esDir) +
        c * (x.2.1 * fderiv ℝ (ageOperator G) x eηDir +
          2 * x.2.2 * fderiv ℝ (ageOperator G) x esDir)
    rw [h1, h2]
    ring
  rw [ringDiffusionRadial_eq R hS, ringDiffusionRadial_eq R hF, ringDiffusionRadial_eq R hG,
    ageOperator_ageShift 2 hS, ageOperator_ageShift 2 hF, ageOperator_ageShift 2 hG]
  simp only [profileLap, ageShift]
  rw [qq, ee, Kq, KK, partialQ_add_mul hF1 hG1 c, ageOperator_add_mul hF1 hG1 c]
  ring

/-! ## The exact expansions -/

/-- **Radial expansion** (tex lines 2890–2902, before the planar equation is used): at a point
where the stream `ψ` is `C³`, with `f = v₁`, `h = v₂ + εH`, `Π = p`,
`r_r = (v₁)_s + v·∇v₁ − νΔv₁ + p_q + εA₁ + ε²B₁`. -/
theorem radial_expansion (R ν : ℝ) {ψ p : ProfilePoint → ℝ} {x : ProfilePoint}
    (hψ : ContDiffAt ℝ 3 ψ x) :
    chartRadialResidual R ν (streamV1 ψ) (axialProfile R ψ) p x =
      planarRadialResidual ν ψ p x + ringEps R * coeffA₁ ν ψ p x +
        ringEps R ^ 2 * coeffB₁ ν ψ x := by
  have h1 := contDiffAt_streamV1 hψ
  rw [chartRadialResidual, ringDiffusionRadial_eq R h1, ageOperator_ageShift 2 h1]
  simp only [planarRadialResidual, transportDiffusion, coeffA₁, coeffB₁, ageShift, ringD,
    axialProfile, profileLap]
  rw [ageOperator_ageShift 2 h1]
  ring

/-- **Axial expansion** (tex lines 2890–2911, before the planar equation is used): at a point
where the stream `ψ` is `C³`, with `f = v₁`, `h = v₂ + εH`, `Π = p`,
`r_z = (v₂)_s + v·∇v₂ − νΔv₂ + p_η + εA₂ + ε²B₂ + ε³B₃`. -/
theorem axial_expansion (R ν : ℝ) {ψ p : ProfilePoint → ℝ} {x : ProfilePoint}
    (hψ : ContDiffAt ℝ 3 ψ x) :
    chartAxialResidual R ν (streamV1 ψ) (axialProfile R ψ) p x =
      planarAxialResidual ν ψ p x + ringEps R * coeffA₂ ν ψ x +
        ringEps R ^ 2 * coeffB₂ ν ψ x + ringEps R ^ 3 * coeffB₃ ν ψ x := by
  have h2 := contDiffAt_streamV2 hψ
  have hH := contDiffAt_ageDefect hψ
  have h2d : DifferentiableAt ℝ (streamV2 ψ) x := h2.differentiableAt (by norm_num)
  have hHd : DifferentiableAt ℝ (ageDefect ψ) x := hH.differentiableAt (by norm_num)
  have hs : partialAge (axialProfile R ψ) x =
      partialAge (streamV2 ψ) x + ringEps R * partialAge (ageDefect ψ) x :=
    partialAge_add_mul h2d hHd _
  have hDh : ringD R (axialProfile R ψ) x =
      ringD R (streamV2 ψ) x + ringEps R * ringD R (ageDefect ψ) x :=
    ringD_add_mul R h2d hHd _
  have he : partialEta (axialProfile R ψ) x =
      partialEta (streamV2 ψ) x + ringEps R * partialEta (ageDefect ψ) x :=
    partialEta_add_mul h2d hHd _
  have hlin : ringDiffusionRadial R (axialProfile R ψ) x =
      ringDiffusionRadial R (streamV2 ψ) x + ringEps R * ringDiffusionRadial R (ageDefect ψ) x :=
    ringDiffusionRadial_add_mul R h2 hH _
  have hAx : ringDiffusionAxial R (axialProfile R ψ) x =
      ringDiffusionRadial R (axialProfile R ψ) x + ringEps R ^ 2 * axialProfile R ψ x := by
    simp only [ringDiffusionAxial, ringDiffusionRadial]
    ring
  rw [chartAxialResidual, hAx, hs, hDh, he, hlin, ringDiffusionRadial_eq R h2,
    ringDiffusionRadial_eq R hH, ageOperator_ageShift 2 h2, ageOperator_ageShift 2 hH]
  simp only [planarAxialResidual, transportDiffusion, coeffA₂, coeffB₂, coeffB₃, ringD,
    axialProfile, profileLap]
  rw [ageShift_ageShift 1 1 h2, ageShift_ageShift 1 1 hH]
  simp only [ageShift]
  ring

/-! ## The unit -/

/-- **Unit B0188** (`eq:st18-t00191`–`eq:st18-t00192`, tex lines 2890–2914), in profile
variables. Let `ψ` be a stream of class `C³` near the profile point `x = (q, η, s)`, `v = ∇^⊥ψ`,
`H = (1 − K)ψ`, and `p` a pressure, such that the exact planar equations
`v_s + v·∇v − νΔv + ∇p = 0` hold at `x`. Take `f = v₁`, `h = v₂ + εH`, `Π = p` in the chart
residual `eq:st18-t00190`. Then at `x`, exactly (no truncation),
`r_r = εA₁ + ε²B₁` and `r_z = εA₂ + ε²B₂ + ε³B₃`. -/
theorem residual_polynomial (R ν : ℝ) {ψ p : ProfilePoint → ℝ} {x : ProfilePoint}
    (hψ : ContDiffAt ℝ 3 ψ x) (hrad : planarRadialResidual ν ψ p x = 0)
    (hax : planarAxialResidual ν ψ p x = 0) :
    chartRadialResidual R ν (streamV1 ψ) (axialProfile R ψ) p x =
        ringEps R * coeffA₁ ν ψ p x + ringEps R ^ 2 * coeffB₁ ν ψ x ∧
    chartAxialResidual R ν (streamV1 ψ) (axialProfile R ψ) p x =
        ringEps R * coeffA₂ ν ψ x + ringEps R ^ 2 * coeffB₂ ν ψ x +
          ringEps R ^ 3 * coeffB₃ ν ψ x := by
  refine ⟨?_, ?_⟩
  · rw [radial_expansion R ν hψ, hrad]
    ring
  · rw [axial_expansion R ν hψ, hax]
    ring

/-- **Unit B0188 for the physical lift** (`eq:st18-t00188`, `eq:st18-t00190`–`eq:st18-t00192`):
for the lift `u_r = a_r v₁`, `u_z = a_r(v₂ + εH)`, `p_raw = a_r²p` of a stream `ψ` of class
`C³` and a differentiable pressure `p` (B0187's hypotheses), at every `r > 0`, `z`, `t > 0`
where the planar equations hold at the chart point `(q, η, s)`, the cylindrical Navier–Stokes
residual is `a_r³(εA₁ + ε²B₁)` (radial) and `a_r³(εA₂ + ε²B₂ + ε³B₃)` (axial), the
coefficients evaluated at `(q, η, s)`. -/
theorem cylindricalResidual_polynomial (R ν : ℝ) (hR : 2 ≤ R) {ψ p : ProfilePoint → ℝ}
    (hψ : ContDiff ℝ 3 ψ) (hp : Differentiable ℝ p) (r z t : ℝ) (hr : 0 < r) (ht : 0 < t)
    (hrad : planarRadialResidual ν ψ p (profileChart R r z t) = 0)
    (hax : planarAxialResidual ν ψ p (profileChart R r z t) = 0) :
    cylRadialResidual ν (liftUr R ψ) (liftUz R ψ) (rawPressure R p) r z t =
        radialScale R r ^ 3 * (ringEps R * coeffA₁ ν ψ p (profileChart R r z t) +
          ringEps R ^ 2 * coeffB₁ ν ψ (profileChart R r z t)) ∧
    cylAxialResidual ν (liftUr R ψ) (liftUz R ψ) (rawPressure R p) r z t =
        radialScale R r ^ 3 * (ringEps R * coeffA₂ ν ψ (profileChart R r z t) +
          ringEps R ^ 2 * coeffB₂ ν ψ (profileChart R r z t) +
          ringEps R ^ 3 * coeffB₃ ν ψ (profileChart R r z t)) := by
  obtain ⟨h1, h2⟩ := cylindricalResidual_lift R ν hR hψ hp r z t hr ht
  obtain ⟨k1, k2⟩ := residual_polynomial R ν hψ.contDiffAt hrad hax
  exact ⟨h1.trans (by rw [k1]), h2.trans (by rw [k2])⟩

/-! ## The actual train (B0140) -/

/-- The profile form `x = (q, (η, s)) ↦ g(s, (q, η))` of a time-dependent planar field: B0140
writes the train as `v s z`, `p s z`, `ψ s z` with `z = (q, η)`, while the profiles of B0184
are functions of `(q, (η, s))`. -/
def profileOf (g : ℝ → ℝ × ℝ → ℝ) (x : ProfilePoint) : ℝ := g x.2.2 (x.1, x.2.1)

/-- **Named hypothesis (not built; train theory INF16, T15 `TrainData`).** The decaying stream
`ψ` of the train (`v = ∇^⊥ψ`, tex lines 2049, 2138) is of class `C³` jointly in `(q, η, s)` on
the open age domain `s > 0`. The manuscript uses this tacitly in `eq:st18-t00188` and
`eq:st18-t00192` (tex lines 2851–2856, 2890–2911): `H = (1 − K)ψ` contains `ψ_s`, and
`D_ε²(v₂ + εH)` contains third derivatives of `ψ`. B0140's `IsTrain` gives the smoothness of
`v` and `p` but only the spatial differentiability of `ψ`; the joint regularity of the stream
is part of INF16, which is not built. -/
def TrainStreamC3 (ψ : ℝ → ℝ × ℝ → ℝ) : Prop := ContDiffOn ℝ 3 (profileOf ψ) ageDomain

/-- One-variable `q`-derivative of a profile along a line, at a point of differentiability. -/
theorem hasDerivAt_slice_q {G : ProfilePoint → ℝ} {q η s : ℝ}
    (hG : DifferentiableAt ℝ G (q, (η, s))) :
    HasDerivAt (fun q' => G (q', (η, s))) (partialQ G (q, (η, s))) q := by
  have hl : HasDerivAt (fun q' : ℝ => ((q', (η, s)) : ProfilePoint)) eqDir q :=
    (hasDerivAt_id q).prodMk (hasDerivAt_const q ((η, s) : ℝ × ℝ))
  exact hG.hasFDerivAt.comp_hasDerivAt q hl

/-- One-variable `η`-derivative of a profile along a line, at a point of differentiability. -/
theorem hasDerivAt_slice_eta {G : ProfilePoint → ℝ} {q η s : ℝ}
    (hG : DifferentiableAt ℝ G (q, (η, s))) :
    HasDerivAt (fun η' => G (q, (η', s))) (partialEta G (q, (η, s))) η := by
  have hl : HasDerivAt (fun η' : ℝ => ((q, (η', s)) : ProfilePoint)) eηDir η :=
    (hasDerivAt_const η q).prodMk ((hasDerivAt_id η).prodMk (hasDerivAt_const η s))
  exact hG.hasFDerivAt.comp_hasDerivAt η hl

/-- One-variable age derivative of a profile along a line, at a point of differentiability. -/
theorem hasDerivAt_slice_age {G : ProfilePoint → ℝ} {q η s : ℝ}
    (hG : DifferentiableAt ℝ G (q, (η, s))) :
    HasDerivAt (fun t => G (q, (η, t))) (partialAge G (q, (η, s))) s := by
  have hl : HasDerivAt (fun t : ℝ => ((q, (η, t)) : ProfilePoint)) esDir s :=
    (hasDerivAt_const s q).prodMk ((hasDerivAt_const s η).prodMk (hasDerivAt_id s))
  exact hG.hasFDerivAt.comp_hasDerivAt s hl

/-- The cylinder partial `Cyl.partialQ` (B0140's classical partials) of an age slice of a
profile is the profile partial `∂_q`, at a point of differentiability. -/
theorem cylPartialQ_slice {G : ProfilePoint → ℝ} {s : ℝ} {w : ℝ × ℝ}
    (hG : DifferentiableAt ℝ G (w.1, (w.2, s))) :
    Cyl.partialQ (fun w' : ℝ × ℝ => G (w'.1, (w'.2, s))) w = partialQ G (w.1, (w.2, s)) :=
  (hasDerivAt_slice_q hG).deriv

/-- The cylinder partial `Cyl.partialEta` of an age slice of a profile is the profile partial
`∂_η`, at a point of differentiability. -/
theorem cylPartialEta_slice {G : ProfilePoint → ℝ} {s : ℝ} {w : ℝ × ℝ}
    (hG : DifferentiableAt ℝ G (w.1, (w.2, s))) :
    Cyl.partialEta (fun w' : ℝ × ℝ => G (w'.1, (w'.2, s))) w = partialEta G (w.1, (w.2, s)) :=
  (hasDerivAt_slice_eta hG).deriv

/-- First and second planar partials of an age slice `u = g(·, ·, s)` of a profile that is `C²`
along the slice agree with the profile partials. -/
theorem slice_partials {g : ProfilePoint → ℝ} {s : ℝ} {u : ℝ × ℝ → ℝ}
    (hu : u = fun w => g (w.1, (w.2, s)))
    (hg : ∀ w : ℝ × ℝ, ContDiffAt ℝ 2 g (w.1, (w.2, s))) (q η : ℝ) :
    Cyl.partialQ u (q, η) = partialQ g (q, (η, s)) ∧
      Cyl.partialEta u (q, η) = partialEta g (q, (η, s)) ∧
      Cyl.partialQ (Cyl.partialQ u) (q, η) = partialQ (partialQ g) (q, (η, s)) ∧
      Cyl.partialEta (Cyl.partialEta u) (q, η) = partialEta (partialEta g) (q, (η, s)) := by
  subst hu
  have hd : ∀ w : ℝ × ℝ, DifferentiableAt ℝ g (w.1, (w.2, s)) :=
    fun w => (hg w).differentiableAt (by norm_num)
  have hq : Cyl.partialQ (fun w : ℝ × ℝ => g (w.1, (w.2, s))) =
      fun w => partialQ g (w.1, (w.2, s)) := funext fun w => cylPartialQ_slice (hd w)
  have he : Cyl.partialEta (fun w : ℝ × ℝ => g (w.1, (w.2, s))) =
      fun w => partialEta g (w.1, (w.2, s)) := funext fun w => cylPartialEta_slice (hd w)
  refine ⟨cylPartialQ_slice (hd (q, η)), cylPartialEta_slice (hd (q, η)), ?_, ?_⟩
  · rw [hq]
    exact cylPartialQ_slice (G := partialQ g) (w := (q, η)) (differentiableAt_partialQ (hg (q, η)))
  · rw [he]
    exact cylPartialEta_slice (G := partialEta g) (w := (q, η))
      (differentiableAt_partialEta (hg (q, η)))

section Train

variable {ν c : ℝ} {v : ℝ → ℝ × ℝ → Train.Vec} {p ψ : ℝ → ℝ × ℝ → ℝ}

theorem contDiffAt_profileOf (hψ : TrainStreamC3 ψ) {y : ProfilePoint} (hy : 0 < y.2.2) :
    ContDiffAt ℝ 3 (profileOf ψ) y :=
  hψ.contDiffAt (isOpen_ageDomain.mem_nhds hy)

/-- The train's first component is `v₁ = −ψ_η` in profile variables: `v(s, (q, η))₁ = v₁(q, η, s)`
for `s > 0` (tex lines 2049, 2138). -/
theorem train_v_zero (hT : B0140.IsTrain ν c v p ψ) (hψ : TrainStreamC3 ψ) {s : ℝ}
    (hs : 0 < s) (q η : ℝ) : v s (q, η) 0 = streamV1 (profileOf ψ) (q, (η, s)) := by
  have hd : DifferentiableAt ℝ (profileOf ψ) (q, (η, s)) :=
    (contDiffAt_profileOf hψ (y := (q, (η, s))) hs).differentiableAt (by norm_num)
  have h := (hasDerivAt_slice_eta hd).deriv
  rw [hT.stream s hs.le (q, η), Train.toVec_zero]
  simp only [GaussianVortex.perpendicularGradient, GaussianVortex.partialY, streamV1]
  rw [← h]
  rfl

/-- The train's second component is `v₂ = ψ_q` in profile variables (tex lines 2049, 2138). -/
theorem train_v_one (hT : B0140.IsTrain ν c v p ψ) (hψ : TrainStreamC3 ψ) {s : ℝ}
    (hs : 0 < s) (q η : ℝ) : v s (q, η) 1 = streamV2 (profileOf ψ) (q, (η, s)) := by
  have hd : DifferentiableAt ℝ (profileOf ψ) (q, (η, s)) :=
    (contDiffAt_profileOf hψ (y := (q, (η, s))) hs).differentiableAt (by norm_num)
  have h := (hasDerivAt_slice_q hd).deriv
  rw [hT.stream s hs.le (q, η), Train.toVec_one]
  simp only [GaussianVortex.perpendicularGradient, GaussianVortex.partialX, streamV2]
  rw [← h]
  rfl

theorem train_v_eq (hT : B0140.IsTrain ν c v p ψ) (hψ : TrainStreamC3 ψ) {s : ℝ}
    (hs : 0 < s) (q η : ℝ) :
    v s (q, η) = Train.toVec (streamV1 (profileOf ψ) (q, (η, s)),
      streamV2 (profileOf ψ) (q, (η, s))) :=
  Train.Vec.ext (by rw [train_v_zero hT hψ hs, Train.toVec_zero])
    (by rw [train_v_one hT hψ hs, Train.toVec_one])

/-- **The exact planar equations in profile variables.** For the train of B0140, under the
named hypothesis `TrainStreamC3`, the planar Navier–Stokes residuals `planarRadialResidual`,
`planarAxialResidual` of `(v₁, v₂) = ∇^⊥ψ` and `p` vanish at every profile point with `s > 0`
(B0140's `momentum`, tex lines 2141–2147). -/
theorem train_planar_equations (hT : B0140.IsTrain ν c v p ψ) (hψ : TrainStreamC3 ψ)
    {x : ProfilePoint} (hx : 0 < x.2.2) :
    planarRadialResidual ν (profileOf ψ) (profileOf p) x = 0 ∧
      planarAxialResidual ν (profileOf ψ) (profileOf p) x = 0 := by
  obtain ⟨q, η, s⟩ := x
  simp only at hx
  have hreg : ∀ w : ℝ × ℝ, ContDiffAt ℝ 3 (profileOf ψ) (w.1, (w.2, s)) :=
    fun w => contDiffAt_profileOf hψ (y := (w.1, (w.2, s))) hx
  have h1 : ∀ w : ℝ × ℝ, ContDiffAt ℝ 2 (streamV1 (profileOf ψ)) (w.1, (w.2, s)) :=
    fun w => contDiffAt_streamV1 (hreg w)
  have h2 : ∀ w : ℝ × ℝ, ContDiffAt ℝ 2 (streamV2 (profileOf ψ)) (w.1, (w.2, s)) :=
    fun w => contDiffAt_streamV2 (hreg w)
  have hv0 : (fun w => v s w 0) = fun w => streamV1 (profileOf ψ) (w.1, (w.2, s)) :=
    funext fun w => train_v_zero hT hψ hx w.1 w.2
  have hv1 : (fun w => v s w 1) = fun w => streamV2 (profileOf ψ) (w.1, (w.2, s)) :=
    funext fun w => train_v_one hT hψ hx w.1 w.2
  obtain ⟨a1, a2, a3, a4⟩ := slice_partials hv0 h1 q η
  obtain ⟨b1, b2, b3, b4⟩ := slice_partials hv1 h2 q η
  -- the age derivative
  have htime : HasDerivAt (fun t => v t (q, η))
      (Train.toVec (partialAge (streamV1 (profileOf ψ)) (q, (η, s)),
        partialAge (streamV2 (profileOf ψ)) (q, (η, s)))) s := by
    have hA := hasDerivAt_slice_age ((h1 (q, η)).differentiableAt (by norm_num))
    have hB := hasDerivAt_slice_age ((h2 (q, η)).differentiableAt (by norm_num))
    have hAB : HasDerivAt (fun t => Train.toVec (streamV1 (profileOf ψ) (q, (η, t)),
        streamV2 (profileOf ψ) (q, (η, t))))
        (Train.toVec (partialAge (streamV1 (profileOf ψ)) (q, (η, s)),
          partialAge (streamV2 (profileOf ψ)) (q, (η, s)))) s :=
      (Train.toVecL : (ℝ × ℝ) →L[ℝ] Train.Vec).hasFDerivAt.comp_hasDerivAt s (hA.prodMk hB)
    refine hAB.congr_of_eventuallyEq ?_
    filter_upwards [eventually_gt_nhds hx] with t ht
    exact train_v_eq hT hψ ht q η
  -- the pressure
  have hPd : DifferentiableAt ℝ (profileOf p) (q, (η, s)) := by
    have hmem : (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) ∈ 𝓝 (s, (q, η)) :=
      prod_mem_nhds (Ici_mem_nhds hx) univ_mem
    have hc : DifferentiableAt ℝ (fun x : ℝ × (ℝ × ℝ) => p x.1 x.2) (s, (q, η)) :=
      (hT.smooth_p.contDiffAt hmem).differentiableAt (by simp)
    have hφ : DifferentiableAt ℝ (fun y : ProfilePoint => (y.2.2, (y.1, y.2.1))) (q, (η, s)) := by
      fun_prop
    exact hc.comp (q, (η, s)) hφ
  have hps : p s = fun w : ℝ × ℝ => profileOf p (w.1, (w.2, s)) := funext fun _ => rfl
  have hpq : Cyl.partialQ (p s) (q, η) = partialQ (profileOf p) (q, (η, s)) := by
    rw [hps]
    exact cylPartialQ_slice (w := (q, η)) hPd
  have hpe : Cyl.partialEta (p s) (q, η) = partialEta (profileOf p) (q, (η, s)) := by
    rw [hps]
    exact cylPartialEta_slice (w := (q, η)) hPd
  -- the momentum equation, componentwise
  have hm := hT.momentum s hx (q, η)
  have hm0 := congrArg (fun V : Train.Vec => V 0) hm
  have hm1 := congrArg (fun V : Train.Vec => V 1) hm
  simp only [Train.momentumResidual, htime.deriv, Train.advection, Train.vecLaplacian,
    Train.gradS, Train.lapS, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    Train.toVec_zero, Train.toVec_one, smul_eq_mul, PiLp.zero_apply] at hm0 hm1
  rw [a1, a2, a3, a4, hpq, train_v_zero hT hψ hx, train_v_one hT hψ hx] at hm0
  rw [b1, b2, b3, b4, hpe, train_v_zero hT hψ hx, train_v_one hT hψ hx] at hm1
  refine ⟨?_, ?_⟩
  · simp only [planarRadialResidual, transportDiffusion, profileLap]
    linear_combination hm0
  · simp only [planarAxialResidual, transportDiffusion, profileLap]
    linear_combination hm1

/-- **Unit B0188 for the actual train** (tex lines 2890–2914, "they hold at every age"). Let
`(v, p)` be the train of B0140 with its decaying stream `ψ` (`IsTrain`), and assume the named
hypothesis `TrainStreamC3 ψ`. In profile variables `x = (q, η, s)` with `s > 0`, take `f = v₁`,
`h = v₂ + εH`, `Π = p` in the chart residual `eq:st18-t00190`. Then exactly
`r_r = εA₁ + ε²B₁` and `r_z = εA₂ + ε²B₂ + ε³B₃` at `x`. -/
theorem train_residual_polynomial (R : ℝ) (hT : B0140.IsTrain ν c v p ψ)
    (hψ : TrainStreamC3 ψ) {x : ProfilePoint} (hx : 0 < x.2.2) :
    chartRadialResidual R ν (streamV1 (profileOf ψ)) (axialProfile R (profileOf ψ))
        (profileOf p) x =
        ringEps R * coeffA₁ ν (profileOf ψ) (profileOf p) x +
          ringEps R ^ 2 * coeffB₁ ν (profileOf ψ) x ∧
    chartAxialResidual R ν (streamV1 (profileOf ψ)) (axialProfile R (profileOf ψ))
        (profileOf p) x =
        ringEps R * coeffA₂ ν (profileOf ψ) x + ringEps R ^ 2 * coeffB₂ ν (profileOf ψ) x +
          ringEps R ^ 3 * coeffB₃ ν (profileOf ψ) x :=
  let ⟨h1, h2⟩ := train_planar_equations hT hψ hx
  residual_polynomial R ν (contDiffAt_profileOf hψ hx) h1 h2

/-- The same for the chosen train `B0140.train` of the solvability hypothesis
`B0140.TrainIVPSolvable ν c` ("Use the single actual train", tex line 5199). -/
theorem actualTrain_residual_polynomial (R : ℝ) (h : B0140.TrainIVPSolvable ν c)
    (hψ : TrainStreamC3 (B0140.train h).ψ) {x : ProfilePoint} (hx : 0 < x.2.2) :
    chartRadialResidual R ν (streamV1 (profileOf (B0140.train h).ψ))
        (axialProfile R (profileOf (B0140.train h).ψ)) (profileOf (B0140.train h).p) x =
        ringEps R * coeffA₁ ν (profileOf (B0140.train h).ψ) (profileOf (B0140.train h).p) x +
          ringEps R ^ 2 * coeffB₁ ν (profileOf (B0140.train h).ψ) x ∧
    chartAxialResidual R ν (streamV1 (profileOf (B0140.train h).ψ))
        (axialProfile R (profileOf (B0140.train h).ψ)) (profileOf (B0140.train h).p) x =
        ringEps R * coeffA₂ ν (profileOf (B0140.train h).ψ) x +
          ringEps R ^ 2 * coeffB₂ ν (profileOf (B0140.train h).ψ) x +
          ringEps R ^ 3 * coeffB₃ ν (profileOf (B0140.train h).ψ) x :=
  train_residual_polynomial R (B0140.train h).isTrain hψ hx

end Train

end UnforcedLeray.B0188
