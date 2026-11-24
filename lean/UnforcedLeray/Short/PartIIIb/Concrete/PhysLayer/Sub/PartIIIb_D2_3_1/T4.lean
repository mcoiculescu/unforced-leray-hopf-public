import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.WardYoungPointwise
import UnforcedLeray.Lib.Axisymmetric.RingChart

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! Helper lemmas for the stream-cutoff divergence (source 4180-4186). -/

theorem wsc_line (y v : Space) : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  simpa using h

theorem wsc_proj (j : Fin 3) {f : ℝ → Space} {f' : Space} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun t => f t j) (f' j) x := by
  have h2 := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt x h
  convert h2 using 1 <;> first | rfl | simp

theorem wsc_A_line {χy : ℝ → ℝ} (hχd : ∀ s, HasDerivAt χy (deriv χy s) s) (ν R : ℝ)
    {y : Space} (hy : y ∉ axis) (v : Space) :
    HasDerivAt (fun t : ℝ => χy (ν * age R (y + t • v)))
      ((deriv χy (ν * age R y) • (ν • ageD R y)) v) 0 :=
  ((hχd (ν * age R y)).comp_hasFDerivAt y ((hasFDerivAt_age R hy).const_mul ν)).comp_hasDerivAt_of_eq
    0 (wsc_line y v) (by simp)

theorem wsc_Z_line {Zf : Space → Space} {y : Space} (hZd : DifferentiableAt ℝ Zf y) (v : Space) :
    HasDerivAt (fun t : ℝ => Zf (y + t • v)) (fderiv ℝ Zf y v) 0 :=
  hZd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (wsc_line y v) (by simp)

theorem wsc_comp_low (ν R : ℝ) (χy : ℝ → ℝ) (Z : ℝ → Space → Space) (τ : ℝ) (y : Space)
    (j : Fin 3) (hj : j ≠ 2) (t : ℝ) :
    wardStreamCut ν R χy Z τ (y + t • coordinateVector j) j =
      χy (ν * age R (y + t • coordinateVector j)) * Z τ (y + t • coordinateVector j) j := by
  simp [wardStreamCut, coordinateVector, hj]

theorem wsc_phi (y : Space) (t : ℝ) : ϱ (y + t • coordinateVector 2) = ϱ y := by
  simp [ϱ, coordinateVector]

theorem wsc_age (R : ℝ) (y : Space) (t : ℝ) : age R (y + t • coordinateVector 2) = age R y := by
  simp [age, wsc_phi]

theorem wardStreamCutDivFree_of (ν R : ℝ) (χy : ℝ → ℝ) : WardStreamCutDivFree ν R χy := by
  intro hχy hν hR Z τ hZc hZd hAx hPrim y hy
  by_cases hin : y ∈ youngOpen ν R
  · have hyO : R * Real.sqrt (5 * ν / 6) < ϱ y := hin
    have hϱpos : 0 < ϱ y := ϱ_pos hy
    have hϱne : ϱ y ≠ 0 := hϱpos.ne'
    have hopen : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
    have hχd : ∀ s : ℝ, HasDerivAt χy (deriv χy s) s := fun s =>
      ((hχy.smooth.differentiable (by simp)) s).hasDerivAt
    have hZdiff : DifferentiableAt ℝ (Z τ) y :=
      (hZc.contDiffAt (hopen.mem_nhds hin)).differentiableAt (by norm_num)
    have hZ0 : Z τ y 0 = Z τ (meridPt y) 0 * (y 0 / ϱ y) := by
      rw [hAx τ y hin hy]; simp [frameL_apply, eR_apply_zero, e3_apply]
    have hZ1 : Z τ y 1 = Z τ (meridPt y) 0 * (y 1 / ϱ y) := by
      rw [hAx τ y hin hy]; simp [frameL_apply, eR_apply_one, e3_apply]
    have hzd : HasDerivAt (fun z' => outPrim Z τ (ϱ y) z') (-(ϱ y * Z τ (meridPt y) 0)) (y 2) :=
      (hPrim (ϱ y) (y 2) hyO).2
    have hz1 : HasDerivAt (fun t : ℝ => outPrim Z τ (ϱ y) (y 2 + t))
        (-(ϱ y * Z τ (meridPt y) 0)) 0 := by
      have h := hzd.comp_of_eq 0 ((hasDerivAt_id' (0 : ℝ)).const_add (y 2)) (by simp)
      convert h using 1 <;> first | rfl | simp
    have hfun2 : (fun t : ℝ => wardStreamCut ν R χy Z τ (y + t • coordinateVector 2) 2) =
        fun t => χy (ν * age R y) * Z τ (y + t • coordinateVector 2) 2 +
          deriv χy (ν * age R y) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y *
            outPrim Z τ (ϱ y) (y 2 + t) := by
      funext t
      unfold wardStreamCut
      simp only [wsc_age, wsc_phi]
      simp [coordinateVector]
    have hE2 : HasDerivAt (fun t : ℝ => wardStreamCut ν R χy Z τ (y + t • coordinateVector 2) 2)
        (χy (ν * age R y) * fderiv ℝ (Z τ) y (coordinateVector 2) 2 +
          deriv χy (ν * age R y) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y *
            (-(ϱ y * Z τ (meridPt y) 0))) 0 := by
      rw [hfun2]
      exact ((wsc_proj 2 (wsc_Z_line hZdiff (coordinateVector 2))).const_mul
        (χy (ν * age R y))).add (hz1.const_mul _)
    have hE0 : HasDerivAt (fun t : ℝ => wardStreamCut ν R χy Z τ (y + t • coordinateVector 0) 0)
        ((deriv χy (ν * age R y) • (ν • ageD R y)) (coordinateVector 0) * Z τ y 0 +
          χy (ν * age R y) * fderiv ℝ (Z τ) y (coordinateVector 0) 0) 0 := by
      have hfun : (fun t : ℝ => wardStreamCut ν R χy Z τ (y + t • coordinateVector 0) 0) =
          fun t => χy (ν * age R (y + t • coordinateVector 0)) *
            Z τ (y + t • coordinateVector 0) 0 :=
        funext fun t => wsc_comp_low ν R χy Z τ y 0 (by decide) t
      rw [hfun]
      have h := (wsc_A_line hχd ν R hy (coordinateVector 0)).mul
        (wsc_proj 0 (wsc_Z_line hZdiff (coordinateVector 0)))
      simp only [zero_smul, add_zero] at h
      exact h
    have hE1 : HasDerivAt (fun t : ℝ => wardStreamCut ν R χy Z τ (y + t • coordinateVector 1) 1)
        ((deriv χy (ν * age R y) • (ν • ageD R y)) (coordinateVector 1) * Z τ y 1 +
          χy (ν * age R y) * fderiv ℝ (Z τ) y (coordinateVector 1) 1) 0 := by
      have hfun : (fun t : ℝ => wardStreamCut ν R χy Z τ (y + t • coordinateVector 1) 1) =
          fun t => χy (ν * age R (y + t • coordinateVector 1)) *
            Z τ (y + t • coordinateVector 1) 1 :=
        funext fun t => wsc_comp_low ν R χy Z τ y 1 (by decide) t
      rw [hfun]
      have h := (wsc_A_line hχd ν R hy (coordinateVector 1)).mul
        (wsc_proj 1 (wsc_Z_line hZdiff (coordinateVector 1)))
      simp only [zero_smul, add_zero] at h
      exact h
    by_cases hFd : DifferentiableAt ℝ (wardStreamCut ν R χy Z τ) y
    · have key : ∀ (j : Fin 3) (E : ℝ),
          HasDerivAt (fun t : ℝ => wardStreamCut ν R χy Z τ (y + t • coordinateVector j) j) E 0 →
            physPd (wardStreamCut ν R χy Z τ) j y j = E := by
        intro j E hE
        have hj := wsc_proj j (hFd.hasFDerivAt.comp_hasDerivAt_of_eq 0
          (wsc_line y (coordinateVector j)) (by simp))
        exact hj.unique hE
      have hdiv : fderiv ℝ (Z τ) y (coordinateVector 0) 0 +
          fderiv ℝ (Z τ) y (coordinateVector 1) 1 + fderiv ℝ (Z τ) y (coordinateVector 2) 2 = 0 := by
        have h := hZd y hin
        simpa [physPd, Fin.sum_univ_three] using h
      have hA0 : (deriv χy (ν * age R y) • (ν • ageD R y)) (coordinateVector 0) =
          deriv χy (ν * age R y) * ν * (-(2 * R ^ 2 / ϱ y ^ 3)) * (y 0 / ϱ y) := by
        simp [ageD, ϱD_apply, coordinateVector]; ring
      have hA1 : (deriv χy (ν * age R y) • (ν • ageD R y)) (coordinateVector 1) =
          deriv χy (ν * age R y) * ν * (-(2 * R ^ 2 / ϱ y ^ 3)) * (y 1 / ϱ y) := by
        simp [ageD, ϱD_apply, coordinateVector]; ring
      have hq' : (y 0 ^ 2 + y 1 ^ 2) * (ϱ y ^ 2)⁻¹ = 1 := by
        rw [← ϱ_sq y]; exact mul_inv_cancel₀ (pow_ne_zero 2 hϱne)
      have hinv : ϱ y * (ϱ y)⁻¹ = 1 := mul_inv_cancel₀ hϱne
      rw [Fin.sum_univ_three, key 0 _ hE0, key 1 _ hE1, key 2 _ hE2]
      rw [hA0, hA1, hZ0, hZ1]
      linear_combination (χy (ν * age R y)) * hdiv
        + (deriv χy (ν * age R y) * ν * (-(2 * R ^ 2 / ϱ y ^ 3)) * Z τ (meridPt y) 0) * hq'
        - (deriv χy (ν * age R y) * ν * (-(2 * R ^ 2 / ϱ y ^ 3)) * Z τ (meridPt y) 0) * hinv
    · rw [Fin.sum_univ_three]
      simp [physPd, fderiv_zero_of_not_differentiableAt hFd]
  · have hin' : ¬ (R * Real.sqrt (5 * ν / 6) < ϱ y) := hin
    have hϱle : ϱ y ≤ R * Real.sqrt (5 * ν / 6) := not_lt.mp hin'
    have hϱpos : 0 < ϱ y := ϱ_pos hy
    have hν6 : 0 ≤ 5 * ν / 6 := by linarith
    have hsqrt : Real.sqrt (5 * ν / 6) ^ 2 = 5 * ν / 6 := Real.sq_sqrt hν6
    have hsq : ϱ y ^ 2 ≤ R ^ 2 * (5 * ν / 6) := by
      have h1 : ϱ y * ϱ y ≤ (R * Real.sqrt (5 * ν / 6)) * (R * Real.sqrt (5 * ν / 6)) :=
        mul_self_le_mul_self hϱpos.le hϱle
      nlinarith [hsqrt]
    have hage : 1 < ν * age R y := by
      unfold age
      rw [← mul_div_assoc, lt_div_iff₀ (pow_pos hϱpos 2)]
      nlinarith [sq_nonneg R, mul_pos hν hR]
    have hF := wyp_streamCut_near hχy Z τ hϱpos hage
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [(wyp_physPd_zero hF j).self_of_nhds]
    simp
