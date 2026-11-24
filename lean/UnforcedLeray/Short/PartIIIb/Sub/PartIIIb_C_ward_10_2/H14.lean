import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_2.H13
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Reg.Struct

/-!
# Helpers for `wardStreamCorrYoungL2_proved` (14): derivative of the stream correction

Source of record: `the November 2 reference manuscript` (73 pages), 4178-4186.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

section Ctx

variable {ν μ R c : ℝ} {g : Chart → Ten3}

theorem w2_hSm (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ) (hg : IsOldL2 c ν g)
    (τ : ℝ) : ContDiffOn ℝ 2 (wardX0 ν μ R c g τ) (youngOpen ν R) :=
  (w2_smooth hν hR hc hμ hg τ).of_le (WithTop.coe_le_coe.2 le_top)

theorem w2_hdiv (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ) (hg : IsOldL2 c ν g)
    (τ : ℝ) : ∀ y ∈ youngOpen ν R, ∑ j : Fin 3, physPd (wardX0 ν μ R c g τ) j y j = 0 := by
  intro y hy
  obtain ⟨hS, hM, -⟩ := w10_ctx hν hR hc hg
  rw [w10_X0_eq hν hR hc hg]
  exact tcr_divFree hν hμ (by positivity) (by positivity) hS hM τ hy

theorem w2_hdr (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ) (hg : IsOldL2 c ν g)
    (τ : ℝ) : ∀ r z : ℝ, R * Real.sqrt (5 * ν / 6) < r →
      HasDerivAt (fun r' => outPrim (wardX0 ν μ R c g) τ r' z)
          (r * wardX0 ν μ R c g τ !₂[r, 0, z] 2) r ∧
        HasDerivAt (fun z' => outPrim (wardX0 ν μ R c g) τ r z')
          (-(r * wardX0 ν μ R c g τ !₂[r, 0, z] 0)) z := fun r z hr =>
  ⟨outPrimDerivR ν R _ τ (w2_hSm hν hR hc hμ hg τ) (w2_streamDecay hν hR hc hμ hg τ) r z hr,
   outPrimDerivZ ν R _ τ (w2_hSm hν hR hc hμ hg τ) (w2_hdiv hν hR hc hμ hg τ)
     (w2_axi hν hR hc hμ hg) (w2_streamDecay hν hR hc hμ hg τ) r z hr⟩

theorem w2_psi_hasFDeriv (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    (hg : IsOldL2 c ν g) (τ : ℝ) {y : Space} (hy : y ∈ youngOpen ν R) :
    HasFDerivAt (fun x : Space => outPrim (wardX0 ν μ R c g) τ (ϱ x) (x 2))
      ((ϱ y * wardX0 ν μ R c g τ (meridPt y) 2) • ϱD y
        + (-(ϱ y * wardX0 ν μ R c g τ (meridPt y) 0)) •
          (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)) y := by
  have hSm := w2_hSm hν hR hc hμ hg τ
  have hdr := w2_hdr hν hR hc hμ hg τ
  have hS : IsOpen {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} :=
    isOpen_lt continuous_const continuous_fst
  have hφ : Continuous (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space)) := by fun_prop
  have hmaps : MapsTo (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space))
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} (youngOpen ν R) := by
    intro p hp
    have hp' : R * Real.sqrt (5 * ν / 6) < p.1 := hp
    show R * Real.sqrt (5 * ν / 6) < ϱ (!₂[p.1, 0, p.2] : Space)
    have hϱ : ϱ (!₂[p.1, 0, p.2] : Space) = |p.1| := by simp [ϱ, Real.sqrt_sq_eq_abs]
    rw [hϱ]
    exact lt_of_lt_of_le hp' (le_abs_self _)
  have hZc := hSm.continuousOn.comp hφ.continuousOn hmaps
  have hPc : ContinuousOn (fun p : ℝ × ℝ => p.1 * wardX0 ν μ R c g τ !₂[p.1, 0, p.2] 2)
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} :=
    continuousOn_fst.mul ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous.comp_continuousOn hZc)
  have hQc : ContinuousOn (fun p : ℝ × ℝ => -(p.1 * wardX0 ν μ R c g τ !₂[p.1, 0, p.2] 0))
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} :=
    (continuousOn_fst.mul ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).continuous.comp_continuousOn hZc)).neg
  have hyS : (ϱ y, y 2) ∈ {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} := hy
  have hD := t9_hasFDerivAt_of_partials _ hS (fun p : ℝ × ℝ => outPrim (wardX0 ν μ R c g) τ p.1 p.2)
    (fun p : ℝ × ℝ => p.1 * wardX0 ν μ R c g τ !₂[p.1, 0, p.2] 2)
    (fun p : ℝ × ℝ => -(p.1 * wardX0 ν μ R c g τ !₂[p.1, 0, p.2] 0))
    hPc hQc (fun p hp => (hdr p.1 p.2 hp).1) (fun p hp => (hdr p.1 p.2 hp).2) (ϱ y, y 2) hyS
  have hy' : y ∉ axis := t9_not_axis hν hR hy
  have hG : HasFDerivAt (fun x : Space => ((ϱ x, x 2) : ℝ × ℝ))
      ((ϱD y).prod (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)) y :=
    (hasFDerivAt_ϱ hy').prodMk (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt
  refine (hD.comp y hG).congr_fderiv ?_
  ext v
  simp [meridPt]

theorem w2_abs_ϱD (y : Space) (hy : y ∉ axis) (j : Fin 3) : |ϱD y (coordinateVector j)| ≤ 1 := by
  have hρ : 0 < ϱ y := ϱ_pos hy
  have h0 : |y 0| ≤ ϱ y := by
    unfold ϱ; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (y 1)])
  have h1 : |y 1| ≤ ϱ y := by
    unfold ϱ; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (y 0)])
  rw [ϱD_apply]
  fin_cases j <;> simp [coordinateVector] <;> rw [abs_div, abs_of_pos hρ, div_le_one hρ] <;> assumption

theorem w2_abs_cv2 (j : Fin 3) : |coordinateVector j 2| ≤ 1 := by
  fin_cases j <;> simp [coordinateVector]

theorem w2_corr_pd_bound {χy : ℝ → ℝ} (hχ : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    (hg : IsOldL2 c ν g) (τ : ℝ) (j : Fin 3) {y : Space} (hy : y ∈ youngOpen ν R) :
    ‖physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y‖ ≤
      |deriv (w2a ν R χy) (ϱ y)| * |outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2)| +
        |w2a ν R χy (ϱ y)| * (2 * ϱ y * ‖wardX0 ν μ R c g τ y‖) := by
  have hy' : y ∉ axis := t9_not_axis hν hR hy
  have hρ : 0 < ϱ y := ϱ_pos hy'
  have hΨ := w2_psi_hasFDeriv hν hR hc hμ hg τ hy
  have hwd : HasDerivAt (w2a ν R χy) (deriv (w2a ν R χy) (ϱ y)) (ϱ y) :=
    (((w2a_contDiffOn (ν := ν) (R := R) hχ).contDiffAt (Ioi_mem_nhds hρ)).differentiableAt
      one_ne_zero).hasDerivAt
  have hA := (hwd.comp_hasFDerivAt y (hasFDerivAt_ϱ hy')).mul hΨ
  have hC := hA.smul_const (coordinateVector 2)
  have hfun : wardStreamCorr ν R χy (wardX0 ν μ R c g) τ =
      fun x : Space => ((w2a ν R χy ∘ ϱ) x * outPrim (wardX0 ν μ R c g) τ (ϱ x) (x 2)) •
        coordinateVector 2 := by
    funext x; rfl
  unfold physPd
  rw [hfun]
  have hEq := congrArg (fun L : Space →L[ℝ] Space => ‖L (coordinateVector j)‖) hC.fderiv
  refine le_of_eq_of_le hEq ?_
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, norm_smul, wyl_norm_coordinateVector, mul_one,
    Real.norm_eq_abs, Function.comp]
  have hn := w2_norm_merid hν hR hc hμ hg τ y hy
  have hm2 : |wardX0 ν μ R c g τ (meridPt y) 2| ≤ ‖wardX0 ν μ R c g τ y‖ :=
    hn ▸ wyl_abs_apply_le _ 2
  have hm0 : |wardX0 ν μ R c g τ (meridPt y) 0| ≤ ‖wardX0 ν μ R c g τ y‖ :=
    hn ▸ wyl_abs_apply_le _ 0
  have hD := w2_abs_ϱD y hy' j
  have hE := w2_abs_cv2 j
  set Ψ := outPrim (wardX0 ν μ R c g) τ (ϱ y) (y 2)
  set w := w2a ν R χy (ϱ y)
  set w' := deriv (w2a ν R χy) (ϱ y)
  set d := ϱD y (coordinateVector j)
  set e := coordinateVector j 2
  set Z2 := wardX0 ν μ R c g τ (meridPt y) 2
  set Z0 := wardX0 ν μ R c g τ (meridPt y) 0
  set N := ‖wardX0 ν μ R c g τ y‖
  have hN : 0 ≤ N := norm_nonneg _
  have hPb : |ϱ y * Z2 * d| ≤ ϱ y * N := by
    rw [abs_mul, abs_mul, abs_of_pos hρ]
    calc ϱ y * |Z2| * |d| ≤ ϱ y * N * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hm2 hρ.le) hD (abs_nonneg _) (by positivity)
      _ = ϱ y * N := by ring
  have hQb : |-(ϱ y * Z0) * e| ≤ ϱ y * N := by
    rw [abs_mul, abs_neg, abs_mul, abs_of_pos hρ]
    calc ϱ y * |Z0| * |e| ≤ ϱ y * N * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hm0 hρ.le) hE (abs_nonneg _) (by positivity)
      _ = ϱ y * N := by ring
  have hsum : |ϱ y * Z2 * d + -(ϱ y * Z0) * e| ≤ 2 * ϱ y * N := by
    calc _ ≤ |ϱ y * Z2 * d| + |-(ϱ y * Z0) * e| := abs_add_le _ _
      _ ≤ 2 * ϱ y * N := by linarith
  have key : w * (ϱ y * Z2 * d + -(ϱ y * Z0) * e) + Ψ * (w' * d) =
      w * (ϱ y * Z2 * d + -(ϱ y * Z0) * e) + w' * d * Ψ := by ring
  calc |w * (ϱ y * Z2 * d + -(ϱ y * Z0) * e) + Ψ * (w' * d)|
      ≤ |w * (ϱ y * Z2 * d + -(ϱ y * Z0) * e)| + |Ψ * (w' * d)| := abs_add_le _ _
    _ ≤ |w'| * |Ψ| + |w| * (2 * ϱ y * N) := by
        rw [abs_mul, abs_mul, abs_mul]
        have h1 : |w| * |ϱ y * Z2 * d + -(ϱ y * Z0) * e| ≤ |w| * (2 * ϱ y * N) :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
        have h2 : |Ψ| * (|w'| * |d|) ≤ |w'| * |Ψ| := by
          calc |Ψ| * (|w'| * |d|) ≤ |Ψ| * (|w'| * 1) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD (abs_nonneg _)) (abs_nonneg _)
            _ = |w'| * |Ψ| := by ring
        linarith

end Ctx

end UnforcedLeray.Short.PartIIIb.Concrete
end
