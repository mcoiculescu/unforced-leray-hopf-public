import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1_1.G.PhaseTest
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1_1.Weak

/-!
# `Sub/PartII-a_N05_1_1/G/ChainRule`: Pointwise chain rules on lifted meridional phase tests

Proves the two exact pointwise derivative identities on smooth lifted phase tests:
1. `dy_two_meridPhaseTest`:
   `dy 2 (meridPhaseTest ε P (ageScaleMerid 1 φ)) = meridPhaseTest ε P (ageScaleMerid (3 / 2) (pdEta φ))`
2. `dy_radial_meridPhaseTest`:
   `dy 0 (unitRTest 0 (meridPhaseTest ε P (ageScaleMerid 1 φ))) +
    dy 1 (unitRTest 1 (meridPhaseTest ε P (ageScaleMerid 1 φ))) =
    meridPhaseTest ε P (ageScaleMerid (3 / 2) (fun p => pdQ φ p - ε • (opK φ p + (2 : ℝ) • φ p)))`

Both identities are proved via 1D `HasDerivAt` along vertical lines and radial rays off the axis
(where `frameC` is constant along each ray), and by local vanishing near the axis.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace N05_1_1G

/-! ### 1. Continuous `ℝ`-linear frame map and 1D directional derivative helpers -/

/-- `frameC x` packaged as a continuous `ℝ`-linear map `MeridC →L[ℝ] SpaceC`. -/
def frameCLM (x : Space) : MeridC →L[ℝ] SpaceC :=
  (((ContinuousLinearMap.id ℂ ℂ).smulRight (unitRC x)).comp
    (EuclideanSpace.proj (0 : Fin 2) : MeridC →L[ℂ] ℂ) +
  ((ContinuousLinearMap.id ℂ ℂ).smulRight unitZC).comp
    (EuclideanSpace.proj (1 : Fin 2) : MeridC →L[ℂ] ℂ)).restrictScalars ℝ

theorem frameCLM_apply (x : Space) (v : MeridC) : frameCLM x v = frameC x v := rfl

theorem frameC_rsmul (x : Space) (r : ℝ) (v : MeridC) :
    frameC x (r • v) = r • frameC x v :=
  (frameCLM x).map_smul r v

private theorem hasDerivAt_line (q : ℝ × Space) (w : Space) :
    HasDerivAt (fun t : ℝ => (q.1, q.2 + t • w)) (0, w) 0 := by
  have h1 : HasDerivAt (fun _ : ℝ => q.1) 0 0 := hasDerivAt_const 0 q.1
  have h2 : HasDerivAt (fun t : ℝ => q.2 + t • w) w 0 := by
    have hd := ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add q.2
    rwa [one_smul] at hd
  exact h1.prodMk h2

private theorem hasDerivAt_rsmul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ → ℝ} {f : ℝ → E} {c' : ℝ} {f' : E} {x : ℝ}
    (hc : HasDerivAt c c' x) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t : ℝ => c t • f t) (c x • f' + c' • f x) x :=
  hc.smul hf

private theorem fderiv_snd_of_hasDerivAt {F : ℝ × Space → CVec3} {q : ℝ × Space} {w : Space}
    {v : CVec3} (hF : DifferentiableAt ℝ F q)
    (h : HasDerivAt (fun t : ℝ => F (q.1, q.2 + t • w)) v 0) :
    fderiv ℝ F q (0, w) = v := by
  have hc : HasDerivAt (fun t : ℝ => F (q.1, q.2 + t • w)) (fderiv ℝ F q (0, w)) 0 :=
    hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_line q w) (by simp)
  exact hc.unique h

private theorem fderiv_profile_decomp (φ : Profile → MeridC) (p : Profile) (a b d : ℝ) :
    fderiv ℝ φ p (a, b, d) = a • pdS φ p + b • pdQ φ p + d • pdEta φ p := by
  have heq : ((a, b, d) : Profile) =
      a • ((1, 0, 0) : Profile) + b • ((0, 1, 0) : Profile) + d • ((0, 0, 1) : Profile) := by
    ext <;> simp
  rw [heq, map_add, map_add, map_smul, map_smul, map_smul]
  rfl

private theorem ageS_rpow_three_halves {ε : ℝ} (hε : 0 < ε) {y : Space} (hr : 0 < radius y) :
    ageS (ε • y) ^ (3 / 2 : ℝ) = ageS (ε • y) * (ε * radius y)⁻¹ := by
  have hεr : 0 < ε * radius y := mul_pos hε hr
  have hs0 : 0 < ageS (ε • y) := by
    unfold ageS; rw [radius_smul_pos hε]; positivity
  have hhalf : ageS (ε • y) ^ (1 / 2 : ℝ) = (ε * radius y)⁻¹ := by
    rw [← Real.sqrt_eq_rpow]
    unfold ageS
    rw [radius_smul_pos hε, Real.sqrt_inv, Real.sqrt_sq hεr.le]
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hs0, Real.rpow_one, hhalf]

private theorem fderiv_zero_on_axis {F : ℝ × Space → CVec3} {q : ℝ × Space} {δ : ℝ}
    (hδ : 0 < δ) (hzero : ∀ p : ℝ × Space, p.2 0 ^ 2 + p.2 1 ^ 2 < δ → F p = 0)
    (hr : radius q.2 = 0) (hF : DifferentiableAt ℝ F q) (w : Space) :
    fderiv ℝ F q (0, w) = 0 := by
  refine fderiv_snd_of_hasDerivAt hF ((hasDerivAt_const (0 : ℝ) (0 : CVec3)).congr_of_eventuallyEq ?_)
  have hc : Continuous (fun t : ℝ => (q.2 + t • w) 0 ^ 2 + (q.2 + t • w) 1 ^ 2) := by
    have hline : Continuous (fun t : ℝ => q.2 + t • w) :=
      continuous_const.add (continuous_id.smul continuous_const)
    exact (((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).comp hline).pow 2).add
      (((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1).comp hline).pow 2)
  have hopen : IsOpen {t : ℝ | (q.2 + t • w) 0 ^ 2 + (q.2 + t • w) 1 ^ 2 < δ} :=
    isOpen_lt hc continuous_const
  have hmem : (q.2 + (0 : ℝ) • w) 0 ^ 2 + (q.2 + (0 : ℝ) • w) 1 ^ 2 < δ := by
    have hsq : q.2 0 ^ 2 + q.2 1 ^ 2 = radius q.2 ^ 2 := (Real.sq_sqrt (by positivity)).symm
    simp only [zero_smul, add_zero]
    rw [hsq, hr]
    simpa using hδ
  filter_upwards [hopen.mem_nhds hmem] with t ht
  exact hzero (q.1, q.2 + t • w) ht

/-! ### 2. Vertical chain rule `dy_two_meridPhaseTest` -/

theorem dy_two_meridPhaseTest {c ε P : ℝ} (hε : 0 < ε) (hP : P = 2 * ε * c)
    {φ : Profile → MeridC} (hφ : IsMeridTest c φ) :
    dy 2 (meridPhaseTest ε P (ageScaleMerid 1 φ)) =
      meridPhaseTest ε P (ageScaleMerid (3 / 2) (pdEta φ)) := by
  set ψ := ageScaleMerid 1 φ
  have hψ : IsMeridTest c ψ := isMeridTest_ageScaleMerid 1 hφ
  have hΦ : IsPhaseTest P (meridPhaseTest ε P ψ) := isPhaseTest_meridPhaseTest hε hP hψ
  obtain ⟨δ, hδ, hzero⟩ := meridPhaseTest_zero_near_axis hε P hψ
  funext q
  rcases q with ⟨τ, y⟩
  by_cases hr : radius y = 0
  · have hL : dy 2 (meridPhaseTest ε P ψ) (τ, y) = 0 :=
      fderiv_zero_on_axis hδ hzero hr (hΦ.smooth.differentiable (by simp) (τ, y))
        (coordinateVector 2)
    have hr' : radius (ε • y) = 0 := by rw [radius_smul_pos hε, hr, mul_zero]
    rw [hL]
    simp [meridPhaseTest, liftA, hr']
  · have hr0 : 0 < radius y :=
      lt_of_le_of_ne (by unfold radius; exact Real.sqrt_nonneg _) (Ne.symm hr)
    set p₀ := chart ε (ε • y, τ)
    have hrad_line : ∀ t : ℝ, radius (y + t • (coordinateVector 2 : Space)) = radius y := by
      intro t
      unfold radius
      have h0 : (y + t • (coordinateVector 2 : Space)) 0 = y 0 := by simp [coordinateVector]
      have h1 : (y + t • (coordinateVector 2 : Space)) 1 = y 1 := by simp [coordinateVector]
      rw [h0, h1]
    have hfr_line : ∀ t : ℝ,
        frameC (ε • (y + t • (coordinateVector 2 : Space))) = frameC (ε • y) := by
      intro t
      ext v
      have hu : unitRC (ε • (y + t • (coordinateVector 2 : Space))) = unitRC (ε • y) := by
        unfold unitRC
        rw [radius_smul_pos hε, radius_smul_pos hε, hrad_line t]
        have h0 : (ε • (y + t • (coordinateVector 2 : Space))) 0 = (ε • y) 0 := by
          simp [coordinateVector]
        have h1 : (ε • (y + t • (coordinateVector 2 : Space))) 1 = (ε • y) 1 := by
          simp [coordinateVector]
        rw [h0, h1]
      simp only [frameC_apply, hu]
    have hchart_line : ∀ t : ℝ,
        chart ε (ε • (y + t • (coordinateVector 2 : Space)), τ) =
          (p₀.1, p₀.2.1, p₀.2.2 + t * (ε * radius y)⁻¹) := by
      intro t
      have hr_t : radius (ε • (y + t • (coordinateVector 2 : Space))) = ε * radius y := by
        rw [radius_smul_pos hε, hrad_line t]
      have heta : etaCoord ε (ε • (y + t • (coordinateVector 2 : Space))) =
          etaCoord ε (ε • y) + t * (ε * radius y)⁻¹ := by
        unfold etaCoord
        rw [hr_t, radius_smul_pos hε]
        have h2 : (ε • (y + t • (coordinateVector 2 : Space))) 2 = ε * (y 2 + t) := by
          simp [coordinateVector, mul_add]
        have h2' : (ε • y) 2 = ε * y 2 := by simp
        rw [h2, h2']
        field_simp [hε.ne', hr]
      simp only [p₀, chart, ageS, cellQ, hr_t, radius_smul_pos hε, heta]
    have hc_deriv : HasDerivAt (fun t : ℝ => (p₀.1, p₀.2.1, p₀.2.2 + t * (ε * radius y)⁻¹))
        (0, 0, (ε * radius y)⁻¹) 0 := by
      have h3 : HasDerivAt (fun t : ℝ => p₀.2.2 + t * (ε * radius y)⁻¹) (ε * radius y)⁻¹ 0 := by
        have hd := ((hasDerivAt_id (0 : ℝ)).mul_const (ε * radius y)⁻¹).const_add p₀.2.2
        rwa [one_mul] at hd
      exact (hasDerivAt_const 0 p₀.1).prodMk ((hasDerivAt_const 0 p₀.2.1).prodMk h3)
    have hφ_deriv : HasDerivAt
        (fun t : ℝ => φ (p₀.1, p₀.2.1, p₀.2.2 + t * (ε * radius y)⁻¹))
        ((ε * radius y)⁻¹ • pdEta φ p₀) 0 := by
      have hc : HasDerivAt (fun t : ℝ => φ (p₀.1, p₀.2.1, p₀.2.2 + t * (ε * radius y)⁻¹))
          (fderiv ℝ φ p₀ (0, 0, (ε * radius y)⁻¹)) 0 :=
        (hφ.smooth.differentiable (by simp) p₀).hasFDerivAt.comp_hasDerivAt_of_eq 0 hc_deriv (by simp)
      rwa [fderiv_profile_decomp, zero_smul, zero_smul, zero_add, zero_add] at hc
    have hsc_deriv : HasDerivAt
        (fun t : ℝ => (liftPrefactor ε P * liftA (ε • y) * (p₀.1 ^ (1 : ℝ))) •
          φ (p₀.1, p₀.2.1, p₀.2.2 + t * (ε * radius y)⁻¹))
        ((liftPrefactor ε P * liftA (ε • y) * (p₀.1 ^ (1 : ℝ))) •
          ((ε * radius y)⁻¹ • pdEta φ p₀)) 0 :=
      hφ_deriv.const_smul (liftPrefactor ε P * liftA (ε • y) * (p₀.1 ^ (1 : ℝ)))
    have hL_deriv : HasDerivAt
        (fun t : ℝ => meridPhaseTest ε P ψ (τ, y + t • (coordinateVector 2 : Space)))
        (frameCLM (ε • y) ((liftPrefactor ε P * liftA (ε • y) * (p₀.1 ^ (1 : ℝ))) •
          ((ε * radius y)⁻¹ • pdEta φ p₀))) 0 := by
      have hcomp := (frameCLM (ε • y)).hasFDerivAt.comp_hasDerivAt 0 hsc_deriv
      refine hcomp.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
      simp only [Function.comp_apply, meridPhaseTest, frameCLM_apply, ψ, ageScaleMerid,
        hchart_line t, hfr_line t, liftA, radius_smul_pos hε, hrad_line t, frameC_rsmul]
      ext i
      simp only [PiLp.smul_apply, Complex.real_smul]
      push_cast
      ring
    have hdy : dy 2 (meridPhaseTest ε P ψ) (τ, y) =
        frameCLM (ε • y) ((liftPrefactor ε P * liftA (ε • y) * (p₀.1 ^ (1 : ℝ))) •
          ((ε * radius y)⁻¹ • pdEta φ p₀)) :=
      fderiv_snd_of_hasDerivAt (hΦ.smooth.differentiable (by simp) (τ, y)) hL_deriv
    rw [hdy]
    have hp1 : p₀.1 ^ (1 : ℝ) = ageS (ε • y) := Real.rpow_one _
    have hp32 : p₀.1 ^ (3 / 2 : ℝ) = ageS (ε • y) * (ε * radius y)⁻¹ :=
      ageS_rpow_three_halves hε hr0
    simp only [frameCLM_apply, meridPhaseTest, ageScaleMerid, frameC_rsmul]
    rw [hp1, hp32]
    ext i
    simp only [PiLp.smul_apply, Complex.real_smul, p₀]
    push_cast
    ring

/-! ### 3. Radial divergence chain rule `dy_radial_meridPhaseTest` -/

private theorem hasDerivAt_unitRScalar_zero {y : Space} (hr : 0 < radius y) :
    HasDerivAt (fun t : ℝ => unitRScalar 0 (y + t • (coordinateVector 0 : Space)))
      ((radius y - y 0 * (y 0 / radius y)) / radius y ^ 2) 0 := by
  have hr2 : y 0 ^ 2 + y 1 ^ 2 = radius y ^ 2 := (Real.sq_sqrt (by positivity)).symm
  have hlin : HasDerivAt (fun t : ℝ => y 0 + t) 1 0 := by
    have hd := (hasDerivAt_id (0 : ℝ)).const_add (y 0)
    exact hd
  have hsq : HasDerivAt (fun t : ℝ => (y 0 + t) ^ 2 + y 1 ^ 2) (2 * y 0) 0 := by
    have hp := (hlin.pow 2).add_const (y 1 ^ 2)
    have heq : ((2 : ℕ) : ℝ) * (y 0 + 0) ^ (2 - 1) * 1 = 2 * y 0 := by push_cast; ring
    rwa [heq] at hp
  have hne : (y 0 + (0 : ℝ)) ^ 2 + y 1 ^ 2 ≠ 0 := by
    rw [add_zero, hr2]
    exact pow_ne_zero 2 hr.ne'
  have h0 : Real.sqrt ((y 0 + (0 : ℝ)) ^ 2 + y 1 ^ 2) = radius y := by
    rw [add_zero]; rfl
  have hrad : HasDerivAt (fun t : ℝ => Real.sqrt ((y 0 + t) ^ 2 + y 1 ^ 2)) (y 0 / radius y) 0 := by
    have hs : HasDerivAt (fun t : ℝ => Real.sqrt ((y 0 + t) ^ 2 + y 1 ^ 2))
        (1 / (2 * Real.sqrt ((y 0 + 0) ^ 2 + y 1 ^ 2)) * (2 * y 0)) 0 :=
      (Real.hasDerivAt_sqrt hne).comp (0 : ℝ) hsq
    have heq : 1 / (2 * Real.sqrt ((y 0 + 0) ^ 2 + y 1 ^ 2)) * (2 * y 0) = y 0 / radius y := by
      rw [h0]; field_simp [hr.ne']
    rwa [heq] at hs
  have hdiv : HasDerivAt (fun t : ℝ => (y 0 + t) / Real.sqrt ((y 0 + t) ^ 2 + y 1 ^ 2))
      ((radius y - y 0 * (y 0 / radius y)) / radius y ^ 2) 0 := by
    have hd := hlin.div hrad (by rw [h0]; exact hr.ne')
    have heq : (1 * Real.sqrt ((y 0 + 0) ^ 2 + y 1 ^ 2) - (y 0 + 0) * (y 0 / radius y)) /
        Real.sqrt ((y 0 + 0) ^ 2 + y 1 ^ 2) ^ 2 =
        (radius y - y 0 * (y 0 / radius y)) / radius y ^ 2 := by
      rw [h0]; ring
    rwa [heq] at hd
  refine hdiv.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  have hc0 : (y + t • (coordinateVector 0 : Space)) 0 = y 0 + t := by simp [coordinateVector]
  have hc1 : (y + t • (coordinateVector 0 : Space)) 1 = y 1 := by simp [coordinateVector]
  simp only [unitRScalar, radius, hc0, hc1]

private theorem hasDerivAt_unitRScalar_one {y : Space} (hr : 0 < radius y) :
    HasDerivAt (fun t : ℝ => unitRScalar 1 (y + t • (coordinateVector 1 : Space)))
      ((radius y - y 1 * (y 1 / radius y)) / radius y ^ 2) 0 := by
  have hr2 : y 0 ^ 2 + y 1 ^ 2 = radius y ^ 2 := (Real.sq_sqrt (by positivity)).symm
  have hlin : HasDerivAt (fun t : ℝ => y 1 + t) 1 0 :=
    (hasDerivAt_id (0 : ℝ)).const_add (y 1)
  have hsq : HasDerivAt (fun t : ℝ => y 0 ^ 2 + (y 1 + t) ^ 2) (2 * y 1) 0 := by
    have hp := (hlin.pow 2).const_add (y 0 ^ 2)
    have heq : ((2 : ℕ) : ℝ) * (y 1 + 0) ^ (2 - 1) * 1 = 2 * y 1 := by push_cast; ring
    rwa [heq] at hp
  have hne : y 0 ^ 2 + (y 1 + (0 : ℝ)) ^ 2 ≠ 0 := by
    rw [add_zero, hr2]
    exact pow_ne_zero 2 hr.ne'
  have h0 : Real.sqrt (y 0 ^ 2 + (y 1 + (0 : ℝ)) ^ 2) = radius y := by
    rw [add_zero]; rfl
  have hrad : HasDerivAt (fun t : ℝ => Real.sqrt (y 0 ^ 2 + (y 1 + t) ^ 2)) (y 1 / radius y) 0 := by
    have hs : HasDerivAt (fun t : ℝ => Real.sqrt (y 0 ^ 2 + (y 1 + t) ^ 2))
        (1 / (2 * Real.sqrt (y 0 ^ 2 + (y 1 + 0) ^ 2)) * (2 * y 1)) 0 :=
      (Real.hasDerivAt_sqrt hne).comp (0 : ℝ) hsq
    have heq : 1 / (2 * Real.sqrt (y 0 ^ 2 + (y 1 + 0) ^ 2)) * (2 * y 1) = y 1 / radius y := by
      rw [h0]; field_simp [hr.ne']
    rwa [heq] at hs
  have hdiv : HasDerivAt (fun t : ℝ => (y 1 + t) / Real.sqrt (y 0 ^ 2 + (y 1 + t) ^ 2))
      ((radius y - y 1 * (y 1 / radius y)) / radius y ^ 2) 0 := by
    have hd := hlin.div hrad (by rw [h0]; exact hr.ne')
    have heq : (1 * Real.sqrt (y 0 ^ 2 + (y 1 + 0) ^ 2) - (y 1 + 0) * (y 1 / radius y)) /
        Real.sqrt (y 0 ^ 2 + (y 1 + 0) ^ 2) ^ 2 =
        (radius y - y 1 * (y 1 / radius y)) / radius y ^ 2 := by
      rw [h0]; ring
    rwa [heq] at hd
  refine hdiv.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  have hc0 : (y + t • (coordinateVector 1 : Space)) 0 = y 0 := by simp [coordinateVector]
  have hc1 : (y + t • (coordinateVector 1 : Space)) 1 = y 1 + t := by simp [coordinateVector]
  simp only [unitRScalar, radius, hc0, hc1]

private theorem dy_unitRTest_zero_offAxis {Φ : ℝ × Space → CVec3} {τ : ℝ} {y : Space}
    (hr : 0 < radius y) (hΦ : DifferentiableAt ℝ Φ (τ, y))
    (hU : DifferentiableAt ℝ (unitRTest 0 Φ) (τ, y)) :
    dy 0 (unitRTest 0 Φ) (τ, y) =
      unitRScalar 0 y • dy 0 Φ (τ, y) +
        ((radius y - y 0 * (y 0 / radius y)) / radius y ^ 2) • Φ (τ, y) := by
  have hΦ_d0 : HasDerivAt (fun t : ℝ => Φ (τ, y + t • (coordinateVector 0 : Space)))
      (dy 0 Φ (τ, y)) 0 :=
    hΦ.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_line (τ, y) (coordinateVector 0)) (by simp)
  have hp := hasDerivAt_rsmul (hasDerivAt_unitRScalar_zero hr) hΦ_d0
  rw [zero_smul, add_zero] at hp
  exact fderiv_snd_of_hasDerivAt hU hp

private theorem dy_unitRTest_one_offAxis {Φ : ℝ × Space → CVec3} {τ : ℝ} {y : Space}
    (hr : 0 < radius y) (hΦ : DifferentiableAt ℝ Φ (τ, y))
    (hU : DifferentiableAt ℝ (unitRTest 1 Φ) (τ, y)) :
    dy 1 (unitRTest 1 Φ) (τ, y) =
      unitRScalar 1 y • dy 1 Φ (τ, y) +
        ((radius y - y 1 * (y 1 / radius y)) / radius y ^ 2) • Φ (τ, y) := by
  have hΦ_d1 : HasDerivAt (fun t : ℝ => Φ (τ, y + t • (coordinateVector 1 : Space)))
      (dy 1 Φ (τ, y)) 0 :=
    hΦ.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_line (τ, y) (coordinateVector 1)) (by simp)
  have hp := hasDerivAt_rsmul (hasDerivAt_unitRScalar_one hr) hΦ_d1
  rw [zero_smul, add_zero] at hp
  exact fderiv_snd_of_hasDerivAt hU hp

private theorem hasDerivAt_inv_pow_two_ray {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => ((ε * (r + t)) ^ 2)⁻¹) (-2 * r⁻¹ * ((ε * r) ^ 2)⁻¹) 0 := by
  have hu : HasDerivAt (fun t : ℝ => ε * (r + t)) ε 0 := by
    have hd := ((hasDerivAt_id (0 : ℝ)).const_add r).const_mul ε
    rwa [mul_one] at hd
  have hu0 : ε * (r + (0 : ℝ)) ≠ 0 := by
    rw [add_zero]; exact mul_ne_zero hε.ne' hr.ne'
  have hd := (hu.pow 2).inv (pow_ne_zero 2 hu0)
  have heq : -(((2 : ℕ) : ℝ) * (ε * (r + 0)) ^ (2 - 1) * ε) /
      (((fun t : ℝ => ε * (r + t)) ^ 2) 0) ^ 2 = -2 * r⁻¹ * ((ε * r) ^ 2)⁻¹ := by
    simp only [Pi.pow_apply, add_zero]
    push_cast
    field_simp [hε.ne', hr.ne']
  rw [heq] at hd
  exact hd.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)

private theorem hasDerivAt_q_ray {ε r τ : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => ε⁻¹ * Real.log (ε * (r + t)) + τ / (2 * ε)) (ε * r)⁻¹ 0 := by
  have hu : HasDerivAt (fun t : ℝ => ε * (r + t)) ε 0 := by
    have hd := ((hasDerivAt_id (0 : ℝ)).const_add r).const_mul ε
    rwa [mul_one] at hd
  have hu0 : ε * (r + (0 : ℝ)) ≠ 0 := by
    rw [add_zero]; exact mul_ne_zero hε.ne' hr.ne'
  have hlog := (Real.hasDerivAt_log hu0).comp (0 : ℝ) hu
  have hd := (hlog.const_mul ε⁻¹).add_const (τ / (2 * ε))
  have heq : ε⁻¹ * ((ε * (r + 0))⁻¹ * ε) = (ε * r)⁻¹ := by
    rw [add_zero]
    field_simp [hε.ne', hr.ne']
  rw [heq] at hd
  exact hd.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)

private theorem hasDerivAt_eta_ray {ε r y2 : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => y2 / (ε * (r + t))) (-r⁻¹ * (y2 / (ε * r))) 0 := by
  have hu : HasDerivAt (fun t : ℝ => ε * (r + t)) ε 0 := by
    have hd := ((hasDerivAt_id (0 : ℝ)).const_add r).const_mul ε
    rwa [mul_one] at hd
  have hu0 : ε * (r + (0 : ℝ)) ≠ 0 := by
    rw [add_zero]; exact mul_ne_zero hε.ne' hr.ne'
  have hd := (hasDerivAt_const (0 : ℝ) y2).div hu hu0
  have heq : (0 * (ε * (r + 0)) - y2 * ε) / (ε * (r + 0)) ^ 2 = -r⁻¹ * (y2 / (ε * r)) := by
    rw [add_zero]
    field_simp [hε.ne', hr.ne']
    ring
  rw [heq] at hd
  exact hd.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)

private theorem hasDerivAt_pref_ray {ε r L : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => L * ((ε * (r + t)) ^ 3)⁻¹)
      (-3 * r⁻¹ * (L * (ε * r)⁻¹ * ((ε * r) ^ 2)⁻¹)) 0 := by
  have hu : HasDerivAt (fun t : ℝ => ε * (r + t)) ε 0 := by
    have hd := ((hasDerivAt_id (0 : ℝ)).const_add r).const_mul ε
    rwa [mul_one] at hd
  have hu0 : ε * (r + (0 : ℝ)) ≠ 0 := by
    rw [add_zero]; exact mul_ne_zero hε.ne' hr.ne'
  have hd := ((hu.pow 3).inv (pow_ne_zero 3 hu0)).const_mul L
  have heq : L * (-(((3 : ℕ) : ℝ) * (ε * (r + 0)) ^ (3 - 1) * ε) /
      (((fun t : ℝ => ε * (r + t)) ^ 3) 0) ^ 2) =
      -3 * r⁻¹ * (L * (ε * r)⁻¹ * ((ε * r) ^ 2)⁻¹) := by
    simp only [Pi.pow_apply, add_zero]
    push_cast
    field_simp [hε.ne', hr.ne']
  rw [heq] at hd
  exact hd.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)

theorem dy_radial_meridPhaseTest {c ε P : ℝ} (hε : 0 < ε) (hP : P = 2 * ε * c)
    {φ : Profile → MeridC} (hφ : IsMeridTest c φ) :
    dy 0 (unitRTest 0 (meridPhaseTest ε P (ageScaleMerid 1 φ))) +
      dy 1 (unitRTest 1 (meridPhaseTest ε P (ageScaleMerid 1 φ))) =
      meridPhaseTest ε P
        (ageScaleMerid (3 / 2) (fun p => pdQ φ p - ε • (opK φ p + (2 : ℝ) • φ p))) := by
  set ψ := ageScaleMerid 1 φ
  have hψ : IsMeridTest c ψ := isMeridTest_ageScaleMerid 1 hφ
  set Φ := meridPhaseTest ε P ψ
  have hΦ : IsPhaseTest P Φ := isPhaseTest_meridPhaseTest hε hP hψ
  have hU0 : IsPhaseTest P (unitRTest 0 Φ) := isPhaseTest_unitRTest_meridPhaseTest hε hP 0 hψ
  have hU1 : IsPhaseTest P (unitRTest 1 Φ) := isPhaseTest_unitRTest_meridPhaseTest hε hP 1 hψ
  obtain ⟨δ, hδ, hzero⟩ := meridPhaseTest_zero_near_axis hε P hψ
  funext q
  rcases q with ⟨τ, y⟩
  change dy 0 (unitRTest 0 Φ) (τ, y) + dy 1 (unitRTest 1 Φ) (τ, y) = _
  by_cases hr : radius y = 0
  · have hz0 : ∀ p : ℝ × Space, p.2 0 ^ 2 + p.2 1 ^ 2 < δ → unitRTest 0 Φ p = 0 :=
      fun p hp => by simp [unitRTest, Φ, hzero p hp]
    have hz1 : ∀ p : ℝ × Space, p.2 0 ^ 2 + p.2 1 ^ 2 < δ → unitRTest 1 Φ p = 0 :=
      fun p hp => by simp [unitRTest, Φ, hzero p hp]
    have h0 : dy 0 (unitRTest 0 Φ) (τ, y) = 0 :=
      fderiv_zero_on_axis hδ hz0 hr (hU0.smooth.differentiable (by simp) (τ, y))
        (coordinateVector 0)
    have h1 : dy 1 (unitRTest 1 Φ) (τ, y) = 0 :=
      fderiv_zero_on_axis hδ hz1 hr (hU1.smooth.differentiable (by simp) (τ, y))
        (coordinateVector 1)
    have hr' : radius (ε • y) = 0 := by rw [radius_smul_pos hε, hr, mul_zero]
    rw [h0, h1, add_zero]
    simp [meridPhaseTest, liftA, hr']
  · set r := radius y
    have hr0 : 0 < r := lt_of_le_of_ne (by unfold r radius; exact Real.sqrt_nonneg _) (Ne.symm hr)
    have hr2 : y 0 ^ 2 + y 1 ^ 2 = r ^ 2 := (Real.sq_sqrt (by positivity)).symm
    have hΦd : DifferentiableAt ℝ Φ (τ, y) := hΦ.smooth.differentiable (by simp) (τ, y)
    -- Step 1: 1D product rule for `dy 0 (unitRTest 0 Φ)` and `dy 1 (unitRTest 1 Φ)`.
    have hdy0 : dy 0 (unitRTest 0 Φ) (τ, y) =
        unitRScalar 0 y • dy 0 Φ (τ, y) + ((r - y 0 * (y 0 / r)) / r ^ 2) • Φ (τ, y) :=
      dy_unitRTest_zero_offAxis hr0 hΦd (hU0.smooth.differentiable (by simp) (τ, y))
    have hdy1 : dy 1 (unitRTest 1 Φ) (τ, y) =
        unitRScalar 1 y • dy 1 Φ (τ, y) + ((r - y 1 * (y 1 / r)) / r ^ 2) • Φ (τ, y) :=
      dy_unitRTest_one_offAxis hr0 hΦd (hU1.smooth.differentiable (by simp) (τ, y))
    set eR : Space :=
      unitRScalar 0 y • (coordinateVector 0 : Space) +
        unitRScalar 1 y • (coordinateVector 1 : Space)
    have hdiv_sum : (r - y 0 * (y 0 / r)) / r ^ 2 + (r - y 1 * (y 1 / r)) / r ^ 2 = r⁻¹ := by
      field_simp [hr0.ne']
      linarith [hr2]
    have hsplit : dy 0 (unitRTest 0 Φ) (τ, y) + dy 1 (unitRTest 1 Φ) (τ, y) =
        r⁻¹ • Φ (τ, y) + fderiv ℝ Φ (τ, y) (0, eR) := by
      rw [hdy0, hdy1]
      have hlin_f : unitRScalar 0 y • dy 0 Φ (τ, y) + unitRScalar 1 y • dy 1 Φ (τ, y) =
          fderiv ℝ Φ (τ, y) (0, eR) := by
        have heR : ((0, eR) : ℝ × Space) =
            unitRScalar 0 y • ((0, coordinateVector 0) : ℝ × Space) +
              unitRScalar 1 y • ((0, coordinateVector 1) : ℝ × Space) := by
          ext <;> simp [eR]
        rw [heR, map_add, map_smul, map_smul]
        rfl
      rw [← add_assoc, add_assoc (unitRScalar 0 y • dy 0 Φ (τ, y)),
        add_comm (((r - y 0 * (y 0 / r)) / r ^ 2) • Φ (τ, y)), ← add_assoc, hlin_f,
        add_assoc, ← add_smul, hdiv_sum, add_comm]
    -- Step 2: Evaluate `fderiv ℝ Φ (τ, y) (0, eR)` along the radial ray `t ↦ (τ, y + t • eR)`.
    have heR0 : eR 0 = y 0 / r := by simp [eR, unitRScalar, coordinateVector, r]
    have heR1 : eR 1 = y 1 / r := by simp [eR, unitRScalar, coordinateVector, r]
    have heR2 : eR 2 = 0 := by simp [eR, coordinateVector]
    have hy0_ray : ∀ t : ℝ, (y + t • eR) 0 = ((r + t) / r) * y 0 := by
      intro t
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, heR0]
      field_simp [hr0.ne']
    have hy1_ray : ∀ t : ℝ, (y + t • eR) 1 = ((r + t) / r) * y 1 := by
      intro t
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, heR1]
      field_simp [hr0.ne']
    have hy2_ray : ∀ t : ℝ, (y + t • eR) 2 = y 2 := by
      intro t
      simp [heR2]
    have hrad_ray : ∀ t : ℝ, 0 < r + t → radius (y + t • eR) = r + t := by
      intro t hrt
      unfold radius
      rw [hy0_ray t, hy1_ray t]
      have hsq : ((r + t) / r * y 0) ^ 2 + ((r + t) / r * y 1) ^ 2 = (r + t) ^ 2 := by
        have h1 : ((r + t) / r * y 0) ^ 2 + ((r + t) / r * y 1) ^ 2 =
            ((r + t) / r) ^ 2 * (y 0 ^ 2 + y 1 ^ 2) := by ring
        rw [h1, hr2]
        field_simp [hr0.ne']
      rw [hsq, Real.sqrt_sq hrt.le]
    have hfr_ray : ∀ t : ℝ, 0 < r + t → frameC (ε • (y + t • eR)) = frameC (ε • y) := by
      intro t hrt
      ext v
      have hu : unitRC (ε • (y + t • eR)) = unitRC (ε • y) := by
        unfold unitRC
        rw [radius_smul_pos hε, radius_smul_pos hε, hrad_ray t hrt]
        simp only [PiLp.smul_apply, smul_eq_mul, hy0_ray t, hy1_ray t]
        change (((ε * ((r + t) / r * y 0) / (ε * (r + t)) : ℝ) : ℂ) • EuclideanSpace.single 0 1 +
            ((ε * ((r + t) / r * y 1) / (ε * (r + t)) : ℝ) : ℂ) • EuclideanSpace.single 1 1) =
          (((ε * y 0 / (ε * r) : ℝ) : ℂ) • EuclideanSpace.single 0 1 +
            ((ε * y 1 / (ε * r) : ℝ) : ℂ) • EuclideanSpace.single 1 1)
        congr 2 <;> congr 1 <;> field_simp [hε.ne', hr0.ne', hrt.ne']
      simp only [frameC_apply, hu]
    set p₀ := chart ε (ε • y, τ)
    let chartRay : ℝ → Profile := fun t =>
      (((ε * (r + t)) ^ 2)⁻¹, ε⁻¹ * Real.log (ε * (r + t)) + τ / (2 * ε), y 2 / (ε * (r + t)))
    have hchart_ray0 : chartRay 0 = p₀ := by
      have heta0 : y 2 / (ε * (r + 0)) = etaCoord ε (ε • y) := by
        unfold etaCoord
        rw [radius_smul_pos hε, add_zero]
        simp only [PiLp.smul_apply, smul_eq_mul]
        change y 2 / (ε * r) = ε * y 2 / (ε * (ε * r))
        field_simp [hε.ne', hr0.ne']
      refine Prod.ext ?_ (Prod.ext ?_ heta0)
      · simp [chartRay, p₀, chart, ageS, radius_smul_pos hε, r]
      · simp [chartRay, p₀, chart, cellQ, radius_smul_pos hε, r]
    have hchart_ray_eq : ∀ t : ℝ, 0 < r + t →
        chart ε (ε • (y + t • eR), τ) = chartRay t := by
      intro t hrt
      have hr_t : radius (ε • (y + t • eR)) = ε * (r + t) := by
        rw [radius_smul_pos hε, hrad_ray t hrt]
      have heta : etaCoord ε (ε • (y + t • eR)) = y 2 / (ε * (r + t)) := by
        unfold etaCoord
        rw [hr_t]
        simp only [PiLp.smul_apply, smul_eq_mul, hy2_ray t]
        field_simp [hε.ne', hrt.ne']
      simp only [chart, ageS, cellQ, hr_t, heta, chartRay]
    have hp0_1 : p₀.1 = ((ε * r) ^ 2)⁻¹ := by
      rw [← hchart_ray0]
      simp [chartRay]
    have hp0_22 : p₀.2.2 = y 2 / (ε * r) := by
      rw [← hchart_ray0]
      simp [chartRay]
    have hs_deriv : HasDerivAt (fun t : ℝ => ((ε * (r + t)) ^ 2)⁻¹) (-2 * r⁻¹ * p₀.1) 0 := by
      rw [hp0_1]
      exact hasDerivAt_inv_pow_two_ray hε hr0
    have hq_deriv : HasDerivAt (fun t : ℝ => ε⁻¹ * Real.log (ε * (r + t)) + τ / (2 * ε))
        (ε * r)⁻¹ 0 :=
      hasDerivAt_q_ray hε hr0
    have heta_deriv : HasDerivAt (fun t : ℝ => y 2 / (ε * (r + t))) (-r⁻¹ * p₀.2.2) 0 := by
      rw [hp0_22]
      exact hasDerivAt_eta_ray hε hr0
    have hchart_deriv : HasDerivAt chartRay (-2 * r⁻¹ * p₀.1, (ε * r)⁻¹, -r⁻¹ * p₀.2.2) 0 :=
      hs_deriv.prodMk (hq_deriv.prodMk heta_deriv)
    have hφ_ray : HasDerivAt (fun t : ℝ => φ (chartRay t))
        (fderiv ℝ φ p₀ (-2 * r⁻¹ * p₀.1, (ε * r)⁻¹, -r⁻¹ * p₀.2.2)) 0 :=
      (hφ.smooth.differentiable (by simp) p₀).hasFDerivAt.comp_hasDerivAt_of_eq 0 hchart_deriv
        hchart_ray0.symm
    let prefRay : ℝ → ℝ := fun t => liftPrefactor ε P * ((ε * (r + t)) ^ 3)⁻¹
    have hpref_deriv : HasDerivAt prefRay
        (-3 * r⁻¹ * (liftPrefactor ε P * (ε * r)⁻¹ * p₀.1)) 0 := by
      rw [hp0_1]
      exact hasDerivAt_pref_ray hε hr0
    have hpref0 : prefRay 0 = liftPrefactor ε P * (ε * r)⁻¹ * p₀.1 := by
      simp only [prefRay, add_zero, hp0_1]
      field_simp [hε.ne', hr0.ne']
    have hprod_ray := hasDerivAt_rsmul hpref_deriv hφ_ray
    rw [hchart_ray0] at hprod_ray
    have hfderiv_eR : fderiv ℝ Φ (τ, y) (0, eR) =
        frameCLM (ε • y)
          (prefRay 0 • fderiv ℝ φ p₀ (-2 * r⁻¹ * p₀.1, (ε * r)⁻¹, -r⁻¹ * p₀.2.2) +
            (-3 * r⁻¹ * (liftPrefactor ε P * (ε * r)⁻¹ * p₀.1)) • φ p₀) := by
      refine fderiv_snd_of_hasDerivAt hΦd
        (((frameCLM (ε • y)).hasFDerivAt.comp_hasDerivAt 0 hprod_ray).congr_of_eventuallyEq ?_)
      have hopen : IsOpen {t : ℝ | 0 < r + t} :=
        isOpen_lt continuous_const (continuous_const.add continuous_id)
      have hmem : (0 : ℝ) < r + 0 := by simp [hr0]
      filter_upwards [hopen.mem_nhds hmem] with t hrt
      have hrt' : 0 < r + t := hrt
      simp only [Function.comp_apply, Φ, meridPhaseTest, ψ, ageScaleMerid, hchart_ray_eq t hrt',
        hfr_ray t hrt', frameCLM_apply, liftA, radius_smul_pos hε, hrad_ray t hrt', prefRay,
        chartRay]
      rw [Real.rpow_one, frameC_rsmul, frameC_rsmul]
      have hsc : liftPrefactor ε P * (ε * (r + t))⁻¹ * ((ε * (r + t)) ^ 2)⁻¹ =
          liftPrefactor ε P * ((ε * (r + t)) ^ 3)⁻¹ := by
        field_simp [hε.ne', hrt'.ne']
      ext i
      simp only [PiLp.smul_apply, Complex.real_smul]
      rw [← mul_assoc, ← Complex.ofReal_mul, hsc]
    -- Step 3: Combine `r⁻¹ • Φ (τ, y) + fderiv ℝ Φ (τ, y) (0, eR)` and match `WeakQWt`.
    rw [hsplit, hfderiv_eR, hpref0, fderiv_profile_decomp]
    have hp1 : p₀.1 ^ (1 : ℝ) = p₀.1 := Real.rpow_one _
    have hp32 : p₀.1 ^ (3 / 2 : ℝ) = p₀.1 * (ε * r)⁻¹ := ageS_rpow_three_halves hε hr0
    have hrinv : r⁻¹ = ε * (ε * r)⁻¹ := by field_simp [hε.ne', hr0.ne']
    have hliftA : liftA (ε • y) = (ε * r)⁻¹ := by simp [liftA, radius_smul_pos hε, r]
    change r⁻¹ • ((liftPrefactor ε P * liftA (ε • y)) • frameCLM (ε • y) ((p₀.1 ^ (1 : ℝ)) • φ p₀)) +
        frameCLM (ε • y) _ =
      (liftPrefactor ε P * liftA (ε • y)) •
        frameCLM (ε • y) ((p₀.1 ^ (3 / 2 : ℝ)) • (pdQ φ p₀ - ε • (opK φ p₀ + (2 : ℝ) • φ p₀)))
    rw [hp1, hp32, hliftA, hrinv, ← (frameCLM (ε • y)).map_smul, ← (frameCLM (ε • y)).map_smul,
      ← (frameCLM (ε • y)).map_add, ← (frameCLM (ε • y)).map_smul]
    congr 1
    ext k
    simp only [opK, opS, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, Complex.real_smul]
    push_cast
    ring

end N05_1_1G

end UnforcedLeray.Short.PartIIa
