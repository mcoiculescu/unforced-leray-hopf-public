import UnforcedLeray.Units.B0226.Rotation
import UnforcedLeray.Units.B0226.AxisCutoff
import UnforcedLeray.Units.B0226.Chain
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# B0226, part 8: axisymmetric tests suffice for axisymmetric fields

Blueprint unit B0226, `paper/main.tex` lines 3394–3402, proof outline ("for the distributional
version, pair with axisymmetric test functions and change variables").

`mem_physSolenoidal_of_meridional`: an axisymmetric meridional (no swirl) field
`V = B_r(r,z,τ) e_r + B_z(r,z,τ) e_z ∈ L²(dx dτ)` whose divergence vanishes against the
axisymmetric tests `Φ ∘ chart` (profile tests `Φ`) is divergence free against every test of
`ℝ³ × period`. This discharges the hypothesis `AxisTestReduction` of `B0226.lean`.

Proof. By `mem_physSolenoidal_of_offAxis` (file `B0226/AxisCutoff.lean`) it suffices to treat a
test `ψ` vanishing on `{x₀² + x₁² ≤ t}`. For each angle `θ` the function
`ψ_θ(x, τ) = ψ(rotPt θ (radius x) x₃, τ)` (`rotTest`) is `Φ_θ ∘ chart` for the profile test
`Φ_θ(s,q,η) = ψ(rotPt θ s^{-1/2} (εη s^{-1/2}), 2εq + log s)` (`rotProfile`,
`isProfileTest_rotProfile`, `rotProfile_chart`), so its pairing with `V` vanishes. Off the axis
`V · ∇ₓψ_θ (x,τ) = (V · ∇ₓψ)(rotPt θ r z, τ)` (`inner_frame_gradX_rotTest`: the chain rule, and
no swirl). Averaging over `θ` (`integral_eq_rotPt_average`, file `B0226/Rotation.lean`) gives
`∫ V · ∇ₓψ = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter Function
open scoped ENNReal Topology InnerProductSpace

namespace UnforcedLeray.B0226

open UnforcedLeray.B0220

/-! ### The rotated tests `ψ_θ` -/

/-- `ψ_θ(x, τ) = ψ(rotPt θ (radius x) x₃, τ)`: the values of `ψ` on the half plane at angle `θ`,
spread axisymmetrically. -/
def rotTest (θ : ℝ) (ψ : Space × ℝ → ℝ) (y : Space × ℝ) : ℝ :=
  ψ (rotPt θ (radius y.1) (y.1 2), y.2)

/-- The unit vector `u_θ = (cos θ, sin θ, 0)`. -/
def uTheta (θ : ℝ) : Space := rotPt θ 1 0

theorem rotPt_eq_smul (θ r z : ℝ) : rotPt θ r z = r • uTheta θ + z • unitZ := by
  have e0 : rotPt θ r z 0 = (r • uTheta θ + z • unitZ) 0 := by
    simp [uTheta, unitZ]
  have e1 : rotPt θ r z 1 = (r • uTheta θ + z • unitZ) 1 := by
    simp [uTheta, unitZ]
  have e2 : rotPt θ r z 2 = (r • uTheta θ + z • unitZ) 2 := by
    simp [uTheta, unitZ]
  ext i
  fin_cases i
  exacts [e0, e1, e2]

theorem frame_apply_zero (x : Space) (v : Merid) : frame x v 0 = v 0 * (x 0 / radius x) := by
  simp [frame_apply, unitR, unitZ]

theorem frame_apply_one (x : Space) (v : Merid) : frame x v 1 = v 0 * (x 1 / radius x) := by
  simp [frame_apply, unitR, unitZ]

theorem frame_apply_two (x : Space) (v : Merid) : frame x v 2 = v 1 := by
  simp [frame_apply, unitR, unitZ]

theorem ϱD_frame {x : Space} (hr : radius x ≠ 0) (v : Merid) : Axi.ϱD x (frame x v) = v 0 := by
  rw [Axi.ϱD_apply, frame_apply_zero, frame_apply_one]
  have h2 : radius x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := Axi.ϱ_sq x
  rw [← radius_eq_ϱ]
  field_simp
  linear_combination (-v 0) * h2

theorem unitR_rotPt {r : ℝ} (hr : 0 < r) (θ z : ℝ) : unitR (rotPt θ r z) = uTheta θ := by
  have hrad := radius_rotPt hr.le θ z
  have e0 : unitR (rotPt θ r z) 0 = uTheta θ 0 := by
    simp only [unitR, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hrad, rotPt_apply_zero,
      rotPt_apply_one, uTheta]
    simp
    field_simp
  have e1 : unitR (rotPt θ r z) 1 = uTheta θ 1 := by
    simp only [unitR, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hrad, rotPt_apply_zero,
      rotPt_apply_one, uTheta]
    simp
    field_simp
  have e2 : unitR (rotPt θ r z) 2 = uTheta θ 2 := by
    simp [unitR, uTheta]
  ext i
  fin_cases i
  exacts [e0, e1, e2]

/-- The derivative of `x ↦ rotPt θ (radius x) x₃` off the axis. -/
theorem hasFDerivAt_rotPt_param (θ : ℝ) {x : Space} (hr : radius x ≠ 0) :
    HasFDerivAt (fun x : Space => rotPt θ (radius x) (x 2))
      ((Axi.ϱD x).smulRight (uTheta θ) +
        (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).smulRight unitZ) x := by
  have hx : x ∉ Axi.axis := notMem_axis hr
  have hfun : (fun x : Space => rotPt θ (radius x) (x 2)) =
      fun x => radius x • uTheta θ + x 2 • unitZ := funext fun x => rotPt_eq_smul _ _ _
  rw [hfun]
  have h1 : HasFDerivAt (fun x : Space => radius x • uTheta θ)
      ((Axi.ϱD x).smulRight (uTheta θ)) x := (Axi.hasFDerivAt_ϱ hx).smul_const (uTheta θ)
  have h2 : HasFDerivAt (fun x : Space => x 2 • unitZ)
      ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).smulRight unitZ) x :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.smul_const unitZ
  exact h1.add h2

/-- **No swirl and the chain rule**: off the axis,
`(B_r e_r + B_z e_z) · ∇ₓψ_θ (x, τ) = (B_r e_r + B_z e_z)(rotPt θ r z) · ∇ₓψ (rotPt θ r z, τ)`. -/
theorem inner_frame_gradX_rotTest {θ : ℝ} {ψ : Space × ℝ → ℝ} {y : Space × ℝ}
    (hr : radius y.1 ≠ 0) (hψ : DifferentiableAt ℝ ψ (rotPt θ (radius y.1) (y.1 2), y.2))
    (v : Merid) :
    ⟪frame y.1 v, gradX (rotTest θ ψ) y⟫_ℝ =
      ⟪frame (rotPt θ (radius y.1) (y.1 2)) v, gradX ψ (rotPt θ (radius y.1) (y.1 2), y.2)⟫_ℝ := by
  rw [real_inner_comm, inner_gradX, real_inner_comm, inner_gradX]
  set L : Space →L[ℝ] Space := (Axi.ϱD y.1).smulRight (uTheta θ) +
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).smulRight unitZ with hL
  have hm : HasFDerivAt (fun y : Space × ℝ => ((rotPt θ (radius y.1) (y.1 2), y.2) : Space × ℝ))
      ((L.comp (ContinuousLinearMap.fst ℝ Space ℝ)).prod (ContinuousLinearMap.snd ℝ Space ℝ)) y :=
    ((hasFDerivAt_rotPt_param θ hr).comp y hasFDerivAt_fst).prodMk hasFDerivAt_snd
  have hcomp := hψ.hasFDerivAt.comp y hm
  have hfd : fderiv ℝ (rotTest θ ψ) y = (fderiv ℝ ψ (rotPt θ (radius y.1) (y.1 2), y.2)).comp
      ((L.comp (ContinuousLinearMap.fst ℝ Space ℝ)).prod (ContinuousLinearMap.snd ℝ Space ℝ)) :=
    hcomp.fderiv
  rw [hfd, ContinuousLinearMap.comp_apply]
  congr 1
  have hrpos : 0 < radius y.1 := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr)
  have hv : L (frame y.1 v) = frame (rotPt θ (radius y.1) (y.1 2)) v := by
    have h2 : (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ) (frame y.1 v) = v 1 :=
      frame_apply_two y.1 v
    rw [hL, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smulRight_apply, ϱD_frame hr, h2, frame_apply, unitR_rotPt hrpos]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', hv]

/-! ### The profile tests `Φ_θ` -/

/-- `Φ_θ(s,q,η) = ψ(rotPt θ s^{-1/2} (ε η s^{-1/2}), 2εq + log s)` for `s > 0`, and `0` for
`s ≤ 0`. -/
def rotProfile (ε θ : ℝ) (ψ : Space × ℝ → ℝ) (p : Profile) : ℝ :=
  if 0 < p.1 then
    ψ (rotPt θ (√(p.1⁻¹)) (ε * p.2.2 * √(p.1⁻¹)), 2 * ε * p.2.1 + Real.log p.1)
  else 0

theorem norm_sq_rotPt (θ r z : ℝ) : ‖rotPt θ r z‖ ^ 2 = r ^ 2 + z ^ 2 := by
  rw [norm_sq_eq_coords]
  simp only [rotPt_apply_zero, rotPt_apply_one, rotPt_apply_two]
  linear_combination r ^ 2 * sin_sq_add_cos_sq θ

/-- `Φ_θ ∘ chart = ψ_θ`, for `ψ` vanishing near the axis. -/
theorem rotProfile_chart {ε : ℝ} (hε : ε ≠ 0) (θ : ℝ) {ψ : Space × ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hψ0 : ∀ y : Space × ℝ, axisSq y.1 ≤ t → ψ y = 0) (y : Space × ℝ) :
    rotProfile ε θ ψ (chart ε y) = rotTest θ ψ y := by
  by_cases hr : radius y.1 = 0
  · have hs : (chart ε y).1 = 0 := by
      simp [chart, ageS, hr]
    rw [rotProfile, if_neg (by rw [hs]; exact lt_irrefl 0), rotTest, hr]
    symm
    apply hψ0
    have := axisSq_rotPt θ 0 (y.1 2)
    simp only [axisSq]
    rw [this]
    simpa using ht
  · have hrpos : 0 < radius y.1 := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr)
    have hs : (chart ε y).1 = (radius y.1 ^ 2)⁻¹ := rfl
    rw [rotProfile, if_pos (by rw [hs]; positivity)]
    have h1 : √((chart ε y).1⁻¹) = radius y.1 := by
      rw [hs, inv_inv, Real.sqrt_sq hrpos.le]
    have e1 : ε * (chart ε y).2.2 * radius y.1 = y.1 2 := by
      simp only [chart, etaCoord]
      field_simp
    have e2 : 2 * ε * (chart ε y).2.1 + Real.log (chart ε y).1 = y.2 := by
      simp only [chart, cellQ, ageS]
      rw [Real.log_inv, Real.log_pow]
      field_simp
      ring
    rw [h1, e1, e2, rotTest]

/-- `Φ_θ` is a profile test when `ψ` is a test of `ℝ³ × period` vanishing near the axis. -/
theorem isProfileTest_rotProfile {ε c t : ℝ} (hε : 0 < ε) (ht : 0 < t) (θ : ℝ)
    {ψ : Space × ℝ → ℝ} (hψ : IsPhysTest (2 * ε * c) ψ)
    (hψ0 : ∀ y : Space × ℝ, axisSq y.1 ≤ t → ψ y = 0) :
    IsProfileTest c (rotProfile ε θ ψ) := by
  obtain ⟨R0, hR0⟩ := hψ.bounded
  set R : ℝ := max R0 1 with hRdef
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have key : ∀ q : Profile, 0 < q.1 →
      ψ (rotPt θ (√(q.1⁻¹)) (ε * q.2.2 * √(q.1⁻¹)), 2 * ε * q.2.1 + Real.log q.1) ≠ 0 →
      q.1⁻¹ ≤ R ^ 2 ∧ |ε * q.2.2 * √(q.1⁻¹)| ≤ R ∧ t < q.1⁻¹ := by
    intro q hq hne
    set r := √(q.1⁻¹) with hr
    set z := ε * q.2.2 * r with hz
    have hr2 : r ^ 2 = q.1⁻¹ := Real.sq_sqrt (inv_nonneg.2 hq.le)
    have hb : ‖rotPt θ r z‖ ≤ R := (hR0 _ hne).trans (le_max_left _ _)
    have hn := norm_sq_rotPt θ r z
    have hb2 : ‖rotPt θ r z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    refine ⟨?_, ?_, ?_⟩
    · rw [← hr2]
      nlinarith [sq_nonneg z]
    · exact abs_le_of_sq_le_sq (by nlinarith [sq_nonneg r]) hR.le
    · by_contra hle
      apply hne
      apply hψ0
      have := axisSq_rotPt θ r z
      simp only [axisSq]
      rw [this, hr2]
      exact not_lt.1 hle
  refine ⟨?_, ?_, ?_⟩
  · -- smoothness
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : 0 < p.1
    · have heq : rotProfile ε θ ψ =ᶠ[𝓝 p] fun q : Profile =>
          ψ (rotPt θ (√(q.1⁻¹)) (ε * q.2.2 * √(q.1⁻¹)), 2 * ε * q.2.1 + Real.log q.1) := by
        filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp] with q hq
        simp only [rotProfile, if_pos (show 0 < q.1 from hq)]
      refine ContDiffAt.congr_of_eventuallyEq ?_ heq
      have hsq : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : Profile => √(q.1⁻¹)) p :=
        (Real.contDiffAt_sqrt (inv_ne_zero hp.ne')).comp p
          ((contDiffAt_inv ℝ hp.ne').comp p contDiffAt_fst)
      have hlog : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : Profile => Real.log q.1) p :=
        (Real.contDiffAt_log.2 hp.ne').comp p contDiffAt_fst
      have hη : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : Profile => q.2.2) p :=
        (contDiff_snd.comp contDiff_snd).contDiffAt
      have hq : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : Profile => q.2.1) p :=
        (contDiff_fst.comp contDiff_snd).contDiffAt
      have hfun : (fun q : Profile =>
          ((rotPt θ (√(q.1⁻¹)) (ε * q.2.2 * √(q.1⁻¹)), 2 * ε * q.2.1 + Real.log q.1) :
            Space × ℝ)) =
          fun q => ((√(q.1⁻¹) * cos θ) • coordinateVector 0 +
            (√(q.1⁻¹) * sin θ) • coordinateVector 1 +
              (ε * q.2.2 * √(q.1⁻¹)) • coordinateVector 2, 2 * ε * q.2.1 + Real.log q.1) := by
        funext q
        rw [rotPt_eq_comb]
      have hF : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : Profile =>
          ((rotPt θ (√(q.1⁻¹)) (ε * q.2.2 * √(q.1⁻¹)), 2 * ε * q.2.1 + Real.log q.1) :
            Space × ℝ)) p := by
        rw [hfun]
        exact ((((hsq.mul contDiffAt_const).smul contDiffAt_const).add
          ((hsq.mul contDiffAt_const).smul contDiffAt_const)).add
            (((contDiffAt_const.mul hη).mul hsq).smul contDiffAt_const)).prodMk
              ((contDiffAt_const.mul hq).add hlog)
      exact hψ.smooth.contDiffAt.comp p hF
    · have hR2 : 0 < (R ^ 2)⁻¹ := by positivity
      have heq : rotProfile ε θ ψ =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
        filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds
          (show p.1 < (R ^ 2)⁻¹ by linarith [not_lt.1 hp])] with q hq
        have hq' : q.1 < (R ^ 2)⁻¹ := hq
        unfold rotProfile
        split_ifs with hq0
        · by_contra hne
          have h1 := (key q hq0 hne).1
          have h2 : (R ^ 2)⁻¹ ≤ q.1 := inv_le_of_inv_le₀ hq0 h1
          linarith
        · rfl
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · -- periodicity in `q`
    intro p
    obtain ⟨s, q, η⟩ := p
    simp only [rotProfile]
    split_ifs with h
    · have : 2 * ε * (q + c) + Real.log s = (2 * ε * q + Real.log s) + 2 * ε * c := by ring
      rw [this, hψ.periodic]
    · rfl
  · -- support in a band
    refine ⟨(R ^ 2)⁻¹, t⁻¹, R / (ε * √t), by positivity, fun p hp => ?_⟩
    have hp1 : 0 < p.1 := by
      by_contra h
      exact hp (by simp only [rotProfile, if_neg h])
    have hne : ψ (rotPt θ (√(p.1⁻¹)) (ε * p.2.2 * √(p.1⁻¹)), 2 * ε * p.2.1 + Real.log p.1) ≠ 0 :=
      by simpa only [rotProfile, if_pos hp1] using hp
    obtain ⟨h1, h2, h3⟩ := key p hp1 hne
    refine ⟨⟨inv_le_of_inv_le₀ hp1 h1, (le_inv_comm₀ hp1 ht).2 h3.le⟩, ?_⟩
    have hsq : √t < √(p.1⁻¹) := Real.sqrt_lt_sqrt ht.le h3
    rw [abs_mul, abs_mul, abs_of_pos hε, abs_of_nonneg (Real.sqrt_nonneg _)] at h2
    have h4 : ε * |p.2.2| * √t ≤ R :=
      le_trans (mul_le_mul_of_nonneg_left hsq.le (by positivity)) h2
    have hst : 0 < √t := Real.sqrt_pos.2 ht
    rw [le_div_iff₀ (by positivity)]
    linarith [show |p.2.2| * (ε * √t) = ε * |p.2.2| * √t by ring]

/-! ### Axisymmetric tests suffice -/

/-- The meridional field `B_r(r,z,τ) e_r + B_z(r,z,τ) e_z` of a measurable `B`. -/
def merField (B : ℝ × ℝ × ℝ → Merid) (y : Space × ℝ) : Space :=
  frame y.1 (B (radius y.1, y.1 2, y.2))

theorem measurable_merField {B : ℝ × ℝ × ℝ → Merid} (hB : Measurable B) :
    Measurable (merField B) := by
  have hB' : Measurable fun y : Space × ℝ => B (radius y.1, y.1 2, y.2) :=
    hB.comp ((measurable_radius.comp measurable_fst).prodMk
      ((measurable_height.comp measurable_fst).prodMk measurable_snd))
  have h0 : Measurable fun y : Space × ℝ => B (radius y.1, y.1 2, y.2) 0 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).measurable.comp hB'
  have h1 : Measurable fun y : Space × ℝ => B (radius y.1, y.1 2, y.2) 1 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).measurable.comp hB'
  have hfun : merField B = fun y : Space × ℝ =>
      B (radius y.1, y.1 2, y.2) 0 • unitR y.1 + B (radius y.1, y.1 2, y.2) 1 • unitZ := by
    funext y
    rfl
  rw [hfun]
  exact (h0.smul (measurable_unitR.comp measurable_fst)).add (h1.smul_const _)

/-- **Axisymmetric tests suffice** (the hypothesis `AxisTestReduction` of `B0226.lean`): an
axisymmetric meridional field `V ∈ L²(dx dτ)` whose divergence vanishes against all the
axisymmetric tests `Φ ∘ chart` is divergence free on `ℝ³ × period`. -/
theorem mem_physSolenoidal_of_meridional {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) {V : PhysL2 ε c}
    (hV : V ∈ meridionalSubspace ε c)
    (hΦ : ∀ Φ : Profile → ℝ, IsProfileTest c Φ →
      ∫ y, ⟪V y, gradX (fun y => Φ (chart ε y)) y⟫_ℝ ∂physMeasure ε c = 0) :
    V ∈ physSolenoidal ε c := by
  obtain ⟨B, hBm, hVB⟩ := hV
  have hVB' : (V : Space × ℝ → Space) =ᵐ[physMeasure ε c] merField B := hVB
  have hP : 0 ≤ 2 * ε * c := by positivity
  refine mem_physSolenoidal_of_offAxis hP V fun ψ hψt => ?_
  obtain ⟨t, ht, hψ0⟩ := hψt
  have hGm : Measurable fun y => ⟪merField B y, gradX ψ.1 y⟫_ℝ :=
    (measurable_merField hBm).inner (continuous_gradX ψ.2.smooth).measurable
  have hVW : (fun y => ⟪V y, gradX ψ.1 y⟫_ℝ) =ᵐ[physMeasure ε c]
      fun y => ⟪merField B y, gradX ψ.1 y⟫_ℝ := by
    filter_upwards [hVB'] with y hy
    rw [hy]
  have hGint : Integrable (fun y => ⟪merField B y, gradX ψ.1 y⟫_ℝ) (physMeasure ε c) := by
    refine (L2.integrable_inner V (physGrad ε c ψ)).congr ?_
    filter_upwards [hVB', coeFn_physGrad ε c ψ] with y h1 h2
    rw [h1, h2]
  have hθ : ∀ θ : ℝ, ∫ y, ⟪merField B (rotPt θ (radius y.1) (y.1 2), y.2),
      gradX ψ.1 (rotPt θ (radius y.1) (y.1 2), y.2)⟫_ℝ ∂physMeasure ε c = 0 := by
    intro θ
    have h1 := hΦ (rotProfile ε θ ψ.1) (isProfileTest_rotProfile hε ht θ ψ.2 hψ0)
    have hfun : (fun y => rotProfile ε θ ψ.1 (chart ε y)) = rotTest θ ψ.1 :=
      funext (rotProfile_chart hε.ne' θ ht.le hψ0)
    rw [hfun] at h1
    rw [← h1]
    refine integral_congr_ae ?_
    filter_upwards [hVB', ae_physMeasure ε c] with y hy1 hy2
    rw [hy1]
    have hrpos : 0 ≤ radius y.1 := Real.sqrt_nonneg _
    have hd : DifferentiableAt ℝ ψ.1 (rotPt θ (radius y.1) (y.1 2), y.2) :=
      (ψ.2.smooth.differentiable (by simp)) _
    simp only [merField, radius_rotPt hrpos, rotPt_apply_two]
    rw [inner_frame_gradX_rotTest hy2.1 hd]
  rw [inner_physGrad, integral_congr_ae hVW, integral_eq_rotPt_average hGm hGint]
  simp only [hθ, integral_zero, mul_zero]

end UnforcedLeray.B0226
