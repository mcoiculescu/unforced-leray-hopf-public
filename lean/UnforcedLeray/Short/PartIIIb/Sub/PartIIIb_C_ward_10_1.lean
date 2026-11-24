import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_1.H9

/-!
# `PartIII-b:C/ward/10/1`: `WardX0YoungL2`

Source of record: `the November 2 reference manuscript` (73 pages), 4171-4174,
4194-4196, 3633-3648 (`sep:young`, `p = q = 2`, `b = 1`, `j ≤ 1`), 2683-2689, 4155-4166.

For old `L²` data `g`, `oldPhys R c g` agrees a.e. with the cut old source `T = oldCutSrc`, a
`2c/R`-periodic separated axisymmetric source with finite `Y₂` moment (`xa_oldReg`), so
`X₀ = W_μ - W_{μ+1}` is the same field built from `T` (`sepWCongrAE`).  For each single
`W_m = Re sepW`, `m > -1/4`, the helper files bound the young chart reading of `W_m` and of its
partials: the transfer field `1_{ϱ ≥ R√ν}N(τ, meridPt y)e_z` is axisymmetric swirl-free, its chart
coefficient is the reading, `ChartYoungTransport` converts the chart norm to the `L²_τL²` norm
over `ϱ ≥ R√ν`, rotation equivariance (`sepWEquivariance`) bounds `N` at the meridian point by
`|D^jW_m|` at the receiver, and `IIIa.sepYoung` (`b = 1`, `D = R√ν(1 - √(5/6))`) with the lift
identity bound it by `C‖g‖`.  The sum `W_μ - W_{μ+1}` is handled by Minkowski (`WylBd.add`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Pointwise domination of readings. -/
theorem w10_read_dom {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) {F A B : ℝ → Space → Space}
    (h : ∀ τ y, R * Real.sqrt ν ≤ ϱ y → ‖F τ y‖ ≤ ‖A τ y‖ + ‖B τ y‖) (q : Chart) :
    wardYoungRead ν R F q ≤ wardYoungRead ν R A q + wardYoungRead ν R B q := by
  by_cases hq : ν * q.1 ≤ 1
  · rcases le_or_gt q.1 0 with hs | hs
    · rw [wyl_youngRead_zero_of_nonpos F hs]
      exact add_nonneg (wyl_youngRead_nonneg ν R A q) (wyl_youngRead_nonneg ν R B q)
    · rw [wyl_youngRead_of_young F hq, wyl_youngRead_of_young A hq, wyl_youngRead_of_young B hq,
        ← mul_add]
      exact mul_le_mul_of_nonneg_left (h _ _ (wyl_young_ϱ hν hR hs hq))
        (inv_nonneg.2 (Real.sqrt_nonneg _))
  · have hqS : q ∉ wardYoungSet ν := hq
    have : wardYoungRead ν R F q = 0 := by
      unfold wardYoungRead
      rw [indicator_of_notMem hqS]
    rw [this]
    exact add_nonneg (wyl_youngRead_nonneg ν R A q) (wyl_youngRead_nonneg ν R B q)

theorem w10_young_of_sum {c ν R C K1 K2 : ℝ} {g : Chart → Ten3} {F A B : ℝ → Space → Space}
    (hFm : AEStronglyMeasurable (wardYoungRead ν R F) (ageμ c (-3 / 2)))
    (hA : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2))) (wardYoungRead ν R A) K1)
    (hB : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2))) (wardYoungRead ν R B) K2)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hC : K1 + K2 ≤ C)
    (hdom : ∀ q, wardYoungRead ν R F q ≤ wardYoungRead ν R A q + wardYoungRead ν R B q) :
    YoungL2Le c ν R C F g := by
  refine ⟨hFm, ?_⟩
  have hs := WylBd.add hA hB hK1 hK2
  refine (eLpNorm_mono_real (g := fun q => wardYoungRead ν R A q + wardYoungRead ν R B q)
    (fun q => ?_)).trans (hs.2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hC) le_rfl))
  rw [Real.norm_of_nonneg (wyl_youngRead_nonneg ν R F q)]
  exact hdom q

/-- `X₀` of old `L²` data is `W_μ - W_{μ+1}` of the cut old source. -/
theorem w10_X0_eq {ν μ R c : ℝ} (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) {g : Chart → Ten3}
    (hg : IsOldL2 c ν g) :
    wardX0 ν μ R c g = sepX0 ν μ (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) := by
  obtain ⟨-, -, hae⟩ := xa_oldReg hc hν hR hg
  rw [wardX0_eq_sepX0]
  exact sepX0_congr (fun μ' y τ => sepWCongrAE ν μ' _ _ hae y τ)

/-- **`X₀` and `∂_jX₀` on the young support** (source 4171-4174, 4194-4196; `sep:young` 3633-3648
with `p = q = 2`, `b = 1`, `j ≤ 1`, `D = R√ν(1 - √(5/6))`). -/
theorem wardX0YoungL2_proved : WardX0YoungL2 := by
  intro ν μ R c hν hR hc hμ
  have hμ1 : -(1 / 4) < μ + 1 := by linarith
  obtain ⟨C1, hC1, h1⟩ := w10_single0 μ hμ ν R c hν hR hc
  obtain ⟨C2, hC2, h2⟩ := w10_single0 (μ + 1) hμ1 ν R c hν hR hc
  obtain ⟨D1, hD1, d1⟩ := w10_single1 μ hμ ν R c hν hR hc
  obtain ⟨D2, hD2, d2⟩ := w10_single1 (μ + 1) hμ1 ν R c hν hR hc
  refine ⟨(C1 + C2) + (D1 + D2), ?_⟩
  intro g hg
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g with hT
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hX0 := w10_X0_eq (μ := μ) hν hR hc hg
  refine ⟨?_, fun j => ?_⟩
  · refine w10_young_of_sum (A := sepWre ν μ T) (B := sepWre ν (μ + 1) T) ?_ (h1 g hg) (h2 g hg)
      hC1 hC2 (by linarith) ?_
    · exact (w10_read_meas (wardX0_measurable_of_measurable ν μ R c g hg.measurable)).aestronglyMeasurable
    · refine w10_read_dom hν hR fun τ y _ => ?_
      rw [hX0, sepX0_eq_sub]
      exact norm_sub_le _ _
  · set U : Set Space := {y : Space | R * Real.sqrt (5 * ν / 6) < ϱ y} with hU
    have hUo : IsOpen U := isOpen_lt continuous_const continuous_ϱ
    have hdV : ∀ (m : ℝ), -(1 / 4) < m → ∀ τ y, y ∈ U → DifferentiableAt ℝ (sepWre ν m T τ) y :=
      fun m hm τ y hy => w10_diffV hν hm hr hP hS hM τ hy
    have hdX : ∀ τ y, y ∈ U → DifferentiableAt ℝ (wardX0 ν μ R c g τ) y := by
      intro τ y hy
      rw [hX0]
      have e : sepX0 ν μ T τ = fun z => sepWre ν μ T τ z - sepWre ν (μ + 1) T τ z := by
        funext z; exact sepX0_eq_sub ν μ T τ z
      rw [e]
      exact (hdV μ hμ τ y hy).sub (hdV (μ + 1) hμ1 τ y hy)
    have hPd := w10_meas_pd (wardX0_measurable_of_measurable ν μ R c g hg.measurable)
      hUo.measurableSet hdX j
    have hread : wardYoungRead ν R (fun τ => physPd (wardX0 ν μ R c g τ) j) =
        wardYoungRead ν R (fun τ y => if y ∈ U then physPd (wardX0 ν μ R c g τ) j y else 0) := by
      refine w10_read_congr hν hR fun τ y hy => ?_
      have : y ∈ U := lt_of_lt_of_le hrr hy
      simp [this]
    refine w10_young_of_sum
      (A := fun τ => physPd (sepWre ν μ T τ) j) (B := fun τ => physPd (sepWre ν (μ + 1) T τ) j)
      ?_ (d1 g hg j) (d2 g hg j) hD1 hD2 (by linarith) ?_
    · rw [hread]
      exact (w10_read_meas hPd).aestronglyMeasurable
    · refine w10_read_dom hν hR fun τ y hy => ?_
      have hyU : y ∈ U := lt_of_lt_of_le hrr hy
      have e : wardX0 ν μ R c g τ = fun z => sepWre ν μ T τ z - sepWre ν (μ + 1) T τ z := by
        funext z; rw [hX0]; exact sepX0_eq_sub ν μ T τ z
      have hp : physPd (wardX0 ν μ R c g τ) j y =
          physPd (sepWre ν μ T τ) j y - physPd (sepWre ν (μ + 1) T τ) j y := by
        unfold physPd
        rw [e, fderiv_fun_sub (hdV μ hμ τ y hyU) (hdV (μ + 1) hμ1 τ y hyU)]
        rfl
      rw [hp]
      exact norm_sub_le _ _

end UnforcedLeray.Short.PartIIIb.Concrete
end
