import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_1.H6

/-!
# Helpers for `wardX0YoungL2_proved` (7): readings, smoothness and rotation of `sepWre`

Source of record: `the November 2 reference manuscript` (73 pages),
2683, 3611-3621, 4171-4174.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem w10_measurable_chartTau (R : ℝ) : Measurable (NearInst.chartTau R) := by
  unfold NearInst.chartTau
  fun_prop

theorem w10_measurable_chartY (R : ℝ) : Measurable (NearInst.chartY R) := by
  unfold NearInst.chartY
  have : Measurable fun p : Chart => (![R / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1] : Fin 3 → ℝ) := by
    refine measurable_pi_lambda _ fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp this

/-- The reading only sees the field on the young receiver region. -/
theorem w10_read_congr {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) {F F' : ℝ → Space → Space}
    (h : ∀ τ y, R * Real.sqrt ν ≤ ϱ y → F τ y = F' τ y) :
    wardYoungRead ν R F = wardYoungRead ν R F' := by
  funext q
  by_cases hq : ν * q.1 ≤ 1
  · rcases le_or_gt q.1 0 with hs | hs
    · rw [wyl_youngRead_zero_of_nonpos F hs, wyl_youngRead_zero_of_nonpos F' hs]
    · rw [wyl_youngRead_of_young F hq, wyl_youngRead_of_young F' hq,
        h _ _ (wyl_young_ϱ hν hR hs hq)]
  · have hqS : q ∉ wardYoungSet ν := hq
    unfold wardYoungRead
    rw [indicator_of_notMem hqS, indicator_of_notMem hqS]

theorem w10_read_meas {ν R : ℝ} {F : ℝ → Space → Space}
    (hF : Measurable (fun x : ℝ × Space => F x.1 x.2)) : Measurable (wardYoungRead ν R F) := by
  unfold wardYoungRead
  refine Measurable.indicator ?_ ?_
  · have hq : Measurable (fun p : Chart =>
        ((NearInst.chartTau R p, NearInst.chartY R p) : ℝ × Space)) :=
      (w10_measurable_chartTau R).prodMk (w10_measurable_chartY R)
    have hs : Measurable (fun p : Chart => (Real.sqrt p.1)⁻¹) :=
      (Real.continuous_sqrt.measurable.comp measurable_fst).inv
    exact hs.mul (hF.comp hq).norm
  · exact measurableSet_le (measurable_const.mul measurable_fst) measurable_const

section Single

variable {ν : ℝ}

theorem w10_diffA {m : ℝ} (hν : 0 < ν) (hm : -(1 / 4) < m) {P rOut : ℝ}
    {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) {y : Space} (hy : rOut < ϱ y) :
    DifferentiableAt ℝ (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y := by
  have hU : IsOpen {y : Space | rOut < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  have hW : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => IIIa.sepW ν (m : ℂ) T z τ)
      {y : Space | rOut < ϱ y} :=
    contDiffOn_pi.2 (fun i => sepW_contDiffOn_top ν (m : ℂ) rOut P T hν (by simpa using hm) hr hP
      hT hM τ i)
  exact (hW.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)

theorem w10_sepWre_eq (m : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) :
    sepWre ν m T τ = w10Re ∘ (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) := rfl

theorem w10_diffV {m : ℝ} (hν : 0 < ν) (hm : -(1 / 4) < m) {P rOut : ℝ}
    {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (τ : ℝ) {y : Space} (hy : rOut < ϱ y) :
    DifferentiableAt ℝ (sepWre ν m T τ) y := by
  rw [w10_sepWre_eq]
  exact w10Re.differentiableAt.comp y (w10_diffA hν hm hr hP hT hM τ hy)

theorem w10_norm0V (m : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space) :
    ‖sepWre ν m T τ y‖ ≤ ‖w10Re‖ * ‖IIIa.sepW ν (m : ℂ) T y τ‖ := by
  rw [w10_sepWre_eq]
  exact w10Re.le_opNorm _

theorem w10_norm1V (m : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space)
    (hA : DifferentiableAt ℝ (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y) :
    ‖fderiv ℝ (sepWre ν m T τ) y‖ ≤
      ‖w10Re‖ * ‖fderiv ℝ (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y‖ := by
  have h := (w10Re.hasFDerivAt.comp y hA.hasFDerivAt).fderiv
  rw [w10_sepWre_eq, h]
  exact ContinuousLinearMap.opNorm_comp_le _ _

/-- Rotation equivariance of `sepWre` off the source disk. -/
theorem w10_equivV {m : ℝ} (hν : 0 < ν) (hm : -(1 / 4) < m) {P rOut : ℝ}
    {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T)
    {M : Matrix (Fin 3) (Fin 3) ℝ} (hMo : M * M.transpose = 1)
    (hTM : ∀ τ z, T τ (actM M z) = M * T τ z * M.transpose) (τ : ℝ) (y : Space)
    (hy : rOut < ϱ y) : sepWre ν m T τ (actM M y) = actM M (sepWre ν m T τ y) := by
  have hI := sepIntegrableOfSource_all ν (m : ℂ) rOut P T hν (by simpa using hm) hr hP hT hM τ y hy
  exact sepWre_equivariant sepWEquivariance M hMo ν m T τ hTM y hI

end Single

end UnforcedLeray.Short.PartIIIb.Concrete
end
