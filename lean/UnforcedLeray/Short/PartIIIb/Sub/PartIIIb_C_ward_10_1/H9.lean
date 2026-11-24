import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_1.H8

/-!
# Helpers for `wardX0YoungL2_proved` (9): the single-`μ` young bounds

Source of record: `the November 2 reference manuscript` (73 pages),
3631-3646, 4171-4174, 4194-4196, 2683-2689.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem w10_single0 (m : ℝ) (hm : -(1 / 4) < m) (ν R c : ℝ) (hν : 0 < ν) (hR : 0 < R)
    (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Chart → Ten3, IsOldL2 c ν g →
      WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
        (wardYoungRead ν R (sepWre ν m (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g))) C := by
  obtain ⟨C0, hC0, hG⟩ := w10_gtl m hm 0
  set b : ℝ := C0 * (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-4 - ((0 : ℕ) : ℝ) + 3 / 1)
    with hb
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hb0 : 0 ≤ b := mul_nonneg hC0 (Real.rpow_nonneg (sub_pos.2 hrr).le _)
  refine ⟨‖w10Re‖ * b, mul_nonneg (norm_nonneg _) hb0, ?_⟩
  intro g hg
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g with hT
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hVm := sepWre_measurable ν m hν T hS.measurable
  have hNm : Measurable (fun x : ℝ × Space => ‖sepWre ν m T x.1 x.2‖) := hVm.norm
  refine ⟨(w10_read_meas hVm).aestronglyMeasurable, ?_⟩
  have hDom : ∀ τ y, R * Real.sqrt ν ≤ ϱ y →
      ENNReal.ofReal ‖sepWre ν m T τ (meridPt y)‖ ≤
        ENNReal.ofReal ‖w10Re‖ * IIIa.wDerivNorm ν (m : ℂ) T 0 τ y := by
    intro τ y hy
    have hy' : R * Real.sqrt (5 * ν / 6) < ϱ y := lt_of_lt_of_le hrr hy
    have hρ : 0 < ϱ y := lt_of_le_of_lt hr hy'
    obtain ⟨M, hMo, hTM, hmer, hMϱ⟩ := w10_rotdatum hAx hρ
    have hmU : R * Real.sqrt (5 * ν / 6) < ϱ (meridPt y) := by
      rw [w10_varrho_meridPt]; exact hy'
    have e := w10_equivV hν hm hr hP hS hM hMo hTM τ (meridPt y) hmU
    rw [hmer] at e
    have hn : ‖sepWre ν m T τ (meridPt y)‖ = ‖sepWre ν m T τ y‖ := by
      rw [e, norm_actM hMo]
    rw [hn]
    unfold IIIa.wDerivNorm
    rw [← ofReal_norm, norm_iteratedFDeriv_zero, ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (w10_norm0V m T τ y)
  have hI := hG ν R c hν hR hc T hS ‖w10Re‖ (fun τ y => ‖sepWre ν m T τ y‖) (norm_nonneg _) hNm
    (fun τ y => by simp only [sepWre_periodic ν m _ T hS.periodic]) (fun τ y => norm_nonneg _)
    hDom
  exact w10_final hν hR hc g hg.measurable _ (fun τ y => norm_nonneg _)
    (F := sepWre ν m T) (fun τ y _ => le_rfl) ‖w10Re‖ b (norm_nonneg _) hb0 hI

theorem w10_single1 (m : ℝ) (hm : -(1 / 4) < m) (ν R c : ℝ) (hν : 0 < ν) (hR : 0 < R)
    (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ k : Fin 3,
      WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
        (wardYoungRead ν R
          (fun τ => physPd (sepWre ν m (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ) k)) C := by
  obtain ⟨C0, hC0, hG⟩ := w10_gtl m hm 1
  set b : ℝ := C0 * (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-4 - ((1 : ℕ) : ℝ) + 3 / 1)
    with hb
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hb0 : 0 ≤ b := mul_nonneg hC0 (Real.rpow_nonneg (sub_pos.2 hrr).le _)
  refine ⟨‖w10Re‖ * b, mul_nonneg (norm_nonneg _) hb0, ?_⟩
  intro g hg k
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g with hT
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hVm := sepWre_measurable ν m hν T hS.measurable
  set U : Set Space := {y : Space | R * Real.sqrt (5 * ν / 6) < ϱ y} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_ϱ
  have hUm : MeasurableSet U := hUo.measurableSet
  have hperV : ∀ τ, sepWre ν m T (τ + 2 * c / R) = sepWre ν m T τ := fun τ =>
    funext (sepWre_periodic ν m _ T hS.periodic τ)
  have hdV : ∀ τ y, y ∈ U → DifferentiableAt ℝ (sepWre ν m T τ) y := fun τ y hy =>
    w10_diffV hν hm hr hP hS hM τ hy
  have hPd := w10_meas_pd hVm hUm hdV k
  set N : ℝ → Space → ℝ := fun τ y =>
    ‖if y ∈ U then physPd (sepWre ν m T τ) k y else 0‖ with hN
  have hNm : Measurable (fun x : ℝ × Space => N x.1 x.2) := hPd.norm
  have hFm : Measurable (fun x : ℝ × Space =>
      (if x.2 ∈ U then physPd (sepWre ν m T x.1) k x.2 else 0 : Space)) := hPd
  have hread : wardYoungRead ν R (fun τ => physPd (sepWre ν m T τ) k) =
      wardYoungRead ν R (fun τ y => if y ∈ U then physPd (sepWre ν m T τ) k y else 0) := by
    refine w10_read_congr hν hR fun τ y hy => ?_
    have : y ∈ U := lt_of_lt_of_le hrr hy
    simp [this]
  refine ⟨?_, ?_⟩
  · rw [hread]
    exact (w10_read_meas hFm).aestronglyMeasurable
  have hDom : ∀ τ y, R * Real.sqrt ν ≤ ϱ y →
      ENNReal.ofReal (N τ (meridPt y)) ≤
        ENNReal.ofReal ‖w10Re‖ * IIIa.wDerivNorm ν (m : ℂ) T 1 τ y := by
    intro τ y hy
    have hy' : R * Real.sqrt (5 * ν / 6) < ϱ y := lt_of_lt_of_le hrr hy
    have hρ : 0 < ϱ y := lt_of_le_of_lt hr hy'
    obtain ⟨M, hMo, hTM, hmer, hMϱ⟩ := w10_rotdatum hAx hρ
    have hmU : meridPt y ∈ U := by
      show R * Real.sqrt (5 * ν / 6) < ϱ (meridPt y)
      rw [w10_varrho_meridPt]; exact hy'
    have hyU : y ∈ U := hy'
    have hrot := w10_fderiv_rot (f := sepWre ν m T τ) hUo hMo
      (fun z hz => by
        show R * Real.sqrt (5 * ν / 6) < ϱ (actM M z)
        rw [hMϱ]; exact hz)
      (fun z hz => hdV τ z hz)
      (fun z hz => w10_equivV hν hm hr hP hS hM hMo hTM τ z hz) hmU (coordinateVector k)
    rw [hmer] at hrot
    have hA := w10_diffA (m := m) hν hm hr hP hS hM τ hy'
    have h1 := w10_norm1V m T τ y hA
    have hNn : N τ (meridPt y) = ‖physPd (sepWre ν m T τ) k (meridPt y)‖ := by
      simp only [hN, if_pos hmU]
    have hle : N τ (meridPt y) ≤ ‖w10Re‖ * ‖fderiv ℝ (fun y' => IIIa.sepW ν (m : ℂ) T y' τ) y‖ := by
      rw [hNn]
      refine le_trans hrot ?_
      rw [wyl_norm_coordinateVector, mul_one]
      exact h1
    unfold IIIa.wDerivNorm
    rw [← ofReal_norm, norm_iteratedFDeriv_one, ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hle
  have hI := hG ν R c hν hR hc T hS ‖w10Re‖ N (norm_nonneg _) hNm
    (fun τ y => by simp only [hN, hperV]) (fun τ y => norm_nonneg _)
    hDom
  rw [hread]
  exact w10_final hν hR hc g hg.measurable _ (fun τ y => norm_nonneg _)
    (F := fun τ y => if y ∈ U then physPd (sepWre ν m T τ) k y else 0)
    (fun τ y _ => le_rfl) ‖w10Re‖ b (norm_nonneg _) hb0 hI

end UnforcedLeray.Short.PartIIIb.Concrete
end
