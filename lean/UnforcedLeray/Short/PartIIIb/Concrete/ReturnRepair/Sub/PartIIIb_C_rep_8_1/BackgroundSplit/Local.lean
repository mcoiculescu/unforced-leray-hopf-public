import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1_org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.RingChart
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.TrainMoment
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.RingSubst.Term2D1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.RingSubst.Term2D2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.RingSubst.Term3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.RingSubst.Term4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.ChgPt
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_org2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1.Sub

/-!
# Localized raw-train and entrance part of `BackgroundSplit` (`PartIII-b:C/rep/8/1/5`)

Source: `the November 2 reference manuscript` lines 5134-5139, 5225-5242,
5434-5436.  Here we define the localized background coefficient `bgBl L = coefSize L.ν L.V (liftP L)`
and its young-range envelope `bgBeta A s η = A (1 + |η|)⁻¹`, and prove both the uniform-in-phase
young-chart bound and the `(s, η)` square-integral bound unconditionally from `D.RepairStanding`
via `ringChartRules`, `trainMoment`, and `entWPt`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. Pointwise comparison of `coefSize` across backgrounds -/

/-- The localized background coefficient size `coefSize L.ν L.V (liftP L)`. -/
def bgBl (L : ReturnLevel) : ℝ → Space → ℝ := coefSize L.ν L.V (liftP L)

/-- The transverse envelope `A (1 + |η|)⁻¹` on the young range. -/
def bgBeta (A : ℝ) (_s η : ℝ) : ℝ := A * (1 + |η|)⁻¹

lemma gradSize_sub_le (u₁ u₂ : Space → Space) (y : Space) :
    gradSize u₁ y - gradSize u₂ y ≤ 3 * coefChgDens u₁ u₂ y := by
  have h := (chgPt_coef_bounds u₁ u₂ y).2.1
  have hstep : ∀ j : Fin 3, ‖physPd u₁ j y‖ ≤ ‖physPd u₂ j y‖ + coefChgDens u₁ u₂ y := fun j => by
    linarith [norm_le_insert' (physPd u₁ j y) (physPd u₂ j y), h j]
  unfold gradSize
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  linarith [hstep 0, hstep 1, hstep 2]

lemma hessSize_sub_le (u₁ u₂ : Space → Space) (y : Space) :
    hessSize u₁ y - hessSize u₂ y ≤ 9 * coefChgDens u₁ u₂ y := by
  have h := (chgPt_coef_bounds u₁ u₂ y).2.2
  have hstep : ∀ j l : Fin 3, ‖physPd2 u₁ j l y‖ ≤ ‖physPd2 u₂ j l y‖ + coefChgDens u₁ u₂ y :=
    fun j l => by linarith [norm_le_insert' (physPd2 u₁ j l y) (physPd2 u₂ j l y), h j l]
  unfold hessSize
  simp only [Fin.sum_univ_three]
  linarith [hstep 0 0, hstep 0 1, hstep 0 2, hstep 1 0, hstep 1 1, hstep 1 2,
    hstep 2 0, hstep 2 1, hstep 2 2]

lemma presGradSize_le_three_norm (q : Space → ℝ) (y : Space) :
    presGradSize q y ≤ 3 * ‖physGrad q y‖ := by
  have hstep : ∀ j : Fin 3, |fderiv ℝ q y (coordinateVector j)| ≤ ‖physGrad q y‖ := fun j => by
    simpa [physGrad] using chgPt_abs_coord_le (physGrad q y) j
  unfold presGradSize
  rw [Fin.sum_univ_three]
  linarith [hstep 0, hstep 1, hstep 2]

lemma presGradSize_sub_le (p₁ p₂ : Space → ℝ) (y : Space) :
    presGradSize p₁ y - presGradSize p₂ y ≤ 3 * presChgDens p₁ p₂ y := by
  have hstep : ∀ j : Fin 3, |fderiv ℝ p₁ y (coordinateVector j)| ≤
      |fderiv ℝ p₂ y (coordinateVector j)| + presChgDens p₁ p₂ y := fun j => by
    have h1 : |fderiv ℝ p₁ y (coordinateVector j) - fderiv ℝ p₂ y (coordinateVector j)| ≤
        presChgDens p₁ p₂ y := by
      simpa [presChgDens, physGrad] using chgPt_abs_coord_le (physGrad p₁ y - physGrad p₂ y) j
    linarith [abs_sub_abs_le_abs_sub (fderiv ℝ p₁ y (coordinateVector j))
      (fderiv ℝ p₂ y (coordinateVector j)), h1]
  unfold presGradSize
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  linarith [hstep 0, hstep 1, hstep 2]

lemma bg_coefSize_nonneg {ν : ℝ} (hν : 0 ≤ ν) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ)
    (τ : ℝ) (y : Space) : 0 ≤ coefSize ν U p τ y := by
  have hg : 0 ≤ gradSize (U τ) y := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hh : 0 ≤ hessSize (U τ) y :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hp : 0 ≤ presGradSize (p τ) y := Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold coefSize
  nlinarith [norm_nonneg (U τ y), sq_nonneg ‖U τ y‖, mul_nonneg hν hg, mul_nonneg hν hh]

/-- Pointwise change of `coefSize` between two velocity-pressure backgrounds. -/
theorem coefSize_sub_le {ν : ℝ} (hν : 0 ≤ ν) (U₁ U₂ : ℝ → SpatialField) (p₁ p₂ : ℝ → Space → ℝ)
    (τ : ℝ) (y : Space) :
    coefSize ν U₁ p₁ τ y ≤ coefSize ν U₂ p₂ τ y +
      (1 + 12 * ν + ‖U₁ τ y‖ + ‖U₂ τ y‖) * coefChgDens (U₁ τ) (U₂ τ) y +
      3 * presChgDens (p₁ τ) (p₂ τ) y := by
  set c := coefChgDens (U₁ τ) (U₂ τ) y
  have hc1 : ‖U₁ τ y - U₂ τ y‖ ≤ c := (chgPt_coef_bounds (U₁ τ) (U₂ τ) y).1
  have hU : ‖U₁ τ y‖ ≤ ‖U₂ τ y‖ + c := by
    linarith [norm_le_insert' (U₁ τ y) (U₂ τ y), hc1]
  have hUsq : ‖U₁ τ y‖ ^ 2 ≤ ‖U₂ τ y‖ ^ 2 + (‖U₁ τ y‖ + ‖U₂ τ y‖) * c := by
    have hsum : 0 ≤ ‖U₁ τ y‖ + ‖U₂ τ y‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hmul : (‖U₁ τ y‖ - ‖U₂ τ y‖) * (‖U₁ τ y‖ + ‖U₂ τ y‖) ≤ c * (‖U₁ τ y‖ + ‖U₂ τ y‖) :=
      mul_le_mul_of_nonneg_right (by linarith) hsum
    nlinarith
  have hg : ν * gradSize (U₁ τ) y ≤ ν * gradSize (U₂ τ) y + 3 * ν * c := by
    have := mul_le_mul_of_nonneg_left (gradSize_sub_le (U₁ τ) (U₂ τ) y) hν
    linarith
  have hh : ν * hessSize (U₁ τ) y ≤ ν * hessSize (U₂ τ) y + 9 * ν * c := by
    have := mul_le_mul_of_nonneg_left (hessSize_sub_le (U₁ τ) (U₂ τ) y) hν
    linarith
  have hp := presGradSize_sub_le (p₁ τ) (p₂ τ) y
  unfold coefSize
  linarith

/-- Bounding `coefSize ν V p` in terms of `coefSize ν U p` and `coefChgDens (V τ) (U τ) y`. -/
theorem coefSize_le_two_raw_add_chg {ν : ℝ} (hν : 0 ≤ ν) (V U : ℝ → SpatialField)
    (p : ℝ → Space → ℝ) (τ : ℝ) (y : Space) :
    coefSize ν V p τ y ≤ 2 * coefSize ν U p τ y +
      (1 + 12 * ν + 2 * coefChgDens (V τ) (U τ) y) * coefChgDens (V τ) (U τ) y := by
  set c := coefChgDens (V τ) (U τ) y
  have hc0 : 0 ≤ c := coefChgDens_nonneg (V τ) (U τ) y
  have hc1 : ‖V τ y - U τ y‖ ≤ c := (chgPt_coef_bounds (V τ) (U τ) y).1
  have hV : ‖V τ y‖ ≤ ‖U τ y‖ + c := by linarith [norm_le_insert' (V τ y) (U τ y), hc1]
  have hpz : presChgDens (p τ) (p τ) y = 0 := by unfold presChgDens; simp
  have hsub := coefSize_sub_le hν V U p p τ y
  rw [hpz, mul_zero, add_zero] at hsub
  have hg : 0 ≤ ν * gradSize (U τ) y :=
    mul_nonneg hν (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hh : 0 ≤ ν * hessSize (U τ) y :=
    mul_nonneg hν (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hp : 0 ≤ presGradSize (p τ) y := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hU0 : 0 ≤ ‖U τ y‖ := norm_nonneg _
  have hsq : (‖V τ y‖ + ‖U τ y‖) * c ≤ ‖U τ y‖ ^ 2 + 2 * c ^ 2 := by
    have h1 : (‖V τ y‖ + ‖U τ y‖) * c ≤ (2 * ‖U τ y‖ + c) * c :=
      mul_le_mul_of_nonneg_right (by linarith) hc0
    nlinarith [sq_nonneg (‖U τ y‖ - c)]
  have hcoef : coefSize ν U p τ y + ‖U τ y‖ ^ 2 ≤ 2 * coefSize ν U p τ y := by
    unfold coefSize; linarith
  linarith

/-! ## 2. Young-chart bound on `coefSize` for the raw background -/

lemma chart_reparam (R τ : ℝ) (hR : R ≠ 0) (p : Chart) :
    let p' : Chart := (p.1, (R * (τ - Real.log p.1) / 2, p.2.2))
    p'.1 = p.1 ∧ p'.2.2 = p.2.2 ∧
      NearInst.chartY R p' = NearInst.chartY R p ∧ NearInst.chartTau R p' = τ := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  unfold NearInst.chartTau
  dsimp only
  field_simp [hR]
  ring

lemma trainWeight_three_le_inv_eta (L : ReturnLevel) {B : ℝ} {p : Chart}
    (h4 : trainWeight 4 L p ≤ B) :
    trainWeight 3 L p ≤ B * (1 + |p.2.2|)⁻¹ := by
  have hpos : 0 < 1 + |p.2.2| := by linarith [abs_nonneg p.2.2]
  rw [le_mul_inv_iff₀ hpos]
  have heq : trainWeight 3 L p * (1 + |p.2.2|) = trainWeight 4 L p := by
    unfold trainWeight; ring
  linarith

/-- On the young range `0 < p.1 ≤ 1 / L.ν`, `RingChartRulesAt` and `TrainMomentAt` bound
`coefSize L.ν (rawU Pl L) (liftP L)` uniformly in phase by `P_ν (1 + |η|)⁻¹`. -/
theorem coefSize_rawU_chart_le (Pl : PlanarData) (L : ReturnLevel) {C1 C2 : ℝ} {k1 k2 : ℕ}
    (hν1 : L.ν ≤ 1) (hε1 : L.ε ≤ 1) (h1 : RingChartRulesAt Pl L C1 k1)
    (h2 : ∀ q : Chart, 0 < q.1 → q.1 ≤ 1 / L.ν → trainWeight 4 L q ≤ C2 * L.ν⁻¹ ^ k2)
    (τ : ℝ) {p : Chart} (hp : 0 < p.1) (hp1 : p.1 ≤ 1 / L.ν) :
    coefSize L.ν (rawU Pl L) (liftP L) τ (NearInst.chartY L.ε⁻¹ p) ≤
      (16 * (2 + |C1|) * max C2 0 + (2 + |C1|) ^ 2 * max C2 0 ^ 2) *
        L.ν⁻¹ ^ (2 * k1 + 2 * k2 + 3) * (1 + |p.2.2|)⁻¹ := by
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hR : L.ε⁻¹ ≠ 0 := inv_ne_zero hε.ne'
  set p' : Chart := (p.1, (L.ε⁻¹ * (τ - Real.log p.1) / 2, p.2.2))
  obtain ⟨hp'1, hp'2, hy, hτ⟩ := chart_reparam L.ε⁻¹ τ hR p
  have hp'pos : 0 < p'.1 := hp'1.symm ▸ hp
  have hp'le : p'.1 ≤ 1 / L.ν := hp'1.symm ▸ hp1
  rw [← hy, ← hτ]
  set τ' := NearInst.chartTau L.ε⁻¹ p'
  set y' := NearInst.chartY L.ε⁻¹ p'
  set W := trainWeight 3 L p'
  set P1 := L.ν⁻¹ ^ k1
  set A1 := (2 + |C1|) * P1
  have hW0 : 0 ≤ W := trainWeight_nonneg 3 L p'
  have hνinv1 : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hP1 : 1 ≤ P1 := one_le_pow₀ hνinv1
  have hA10 : 0 ≤ A1 := by positivity
  have hs0 : 0 ≤ p'.1 := hp'pos.le
  have hsqrt0 : 0 ≤ Real.sqrt p'.1 := Real.sqrt_nonneg _
  have hs32_0 : 0 ≤ p'.1 ^ (3 / 2 : ℝ) := Real.rpow_nonneg hs0 _
  -- Bounds on rawU, its derivatives, and liftP from RingChartRulesAt
  have hU : ‖rawU Pl L τ' y'‖ ≤ A1 * Real.sqrt p'.1 * W :=
    norm_rawU_le Pl L hν1 hε1 h1 hp'pos hp'le
  have hPd : ∀ j : Fin 3, ‖physPd (rawU Pl L τ') j y'‖ ≤ A1 * p'.1 * W := fun j =>
    bound_of_close _ (vecSp (flatD1 L p'.1 p'.2 j)) p'.1 W C1 P1 L.ε hs0 hW0 hP1 hε.le hε1
      ((norm_vecSp_le _).trans (mul_le_mul_of_nonneg_left (trainFlatD1Bound L p' hp'pos j)
        (by norm_num))) ((h1 p' hp'pos hp'le).2.1 j)
  have hPd2 : ∀ j l : Fin 3, ‖physPd2 (rawU Pl L τ') j l y'‖ ≤ A1 * p'.1 ^ (3 / 2 : ℝ) * W :=
    fun j l => bound_of_close _ (vecSp (flatD2 L p'.1 p'.2 j l)) (p'.1 ^ (3 / 2 : ℝ)) W C1 P1 L.ε
      hs32_0 hW0 hP1 hε.le hε1
      ((norm_vecSp_le _).trans (mul_le_mul_of_nonneg_left (trainFlatD2Bound L p' hp'pos j l)
        (by norm_num))) ((h1 p' hp'pos hp'le).2.2.1 j l)
  have hPr : ‖physGrad (liftP L τ') y'‖ ≤ A1 * p'.1 ^ (3 / 2 : ℝ) * W :=
    bound_of_close _ (vecSp (emb (mgrad (trainP L p'.1) p'.2))) (p'.1 ^ (3 / 2 : ℝ)) W C1 P1 L.ε
      hs32_0 hW0 hP1 hε.le hε1
      ((norm_vecSp_le _).trans (mul_le_mul_of_nonneg_left (norm_mgrad_trainP_le4 L hp'pos)
        (by norm_num))) (h1 p' hp'pos hp'le).2.2.2
  -- Bounds on s-powers on the young range s ≤ ν⁻¹
  have hs_le : p'.1 ≤ L.ν⁻¹ := by simpa [one_div] using hp'le
  have hsqrt_le : Real.sqrt p'.1 ≤ L.ν⁻¹ := by
    calc Real.sqrt p'.1 ≤ Real.sqrt L.ν⁻¹ := Real.sqrt_le_sqrt hs_le
      _ ≤ Real.sqrt (L.ν⁻¹ ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = L.ν⁻¹ := Real.sqrt_sq (by positivity)
  have hs32_le : p'.1 ^ (3 / 2 : ℝ) ≤ L.ν⁻¹ ^ 3 := by
    rw [rpow_three_half p'.1 hs0]
    exact pow_le_pow_left₀ hsqrt0 hsqrt_le 3
  have hsqrt_le3 : Real.sqrt p'.1 ≤ L.ν⁻¹ ^ 3 :=
    hsqrt_le.trans (by simpa using pow_le_pow_right₀ hνinv1 (by norm_num : 1 ≤ 3))
  have hs_le3 : p'.1 ≤ L.ν⁻¹ ^ 3 :=
    hs_le.trans (by simpa using pow_le_pow_right₀ hνinv1 (by norm_num : 1 ≤ 3))
  have hU' : ‖rawU Pl L τ' y'‖ ≤ A1 * L.ν⁻¹ ^ 3 * W := by
    calc ‖rawU Pl L τ' y'‖ ≤ A1 * Real.sqrt p'.1 * W := hU
      _ ≤ A1 * L.ν⁻¹ ^ 3 * W :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt_le3 hA10) hW0
  have hgrad' : L.ν * gradSize (rawU Pl L τ') y' ≤ 3 * A1 * L.ν⁻¹ ^ 3 * W := by
    have hg : gradSize (rawU Pl L τ') y' ≤ 3 * (A1 * L.ν⁻¹ ^ 3 * W) := by
      have h0 : ∀ j : Fin 3, ‖physPd (rawU Pl L τ') j y'‖ ≤ A1 * L.ν⁻¹ ^ 3 * W := fun j =>
        (hPd j).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs_le3 hA10) hW0)
      unfold gradSize; rw [Fin.sum_univ_three]; linarith [h0 0, h0 1, h0 2]
    calc L.ν * gradSize (rawU Pl L τ') y' ≤ 1 * (3 * (A1 * L.ν⁻¹ ^ 3 * W)) :=
          mul_le_mul hν1 hg (Finset.sum_nonneg fun _ _ => norm_nonneg _) zero_le_one
      _ = 3 * A1 * L.ν⁻¹ ^ 3 * W := by ring
  have hhess' : L.ν * hessSize (rawU Pl L τ') y' ≤ 9 * A1 * L.ν⁻¹ ^ 3 * W := by
    have hh : hessSize (rawU Pl L τ') y' ≤ 9 * (A1 * L.ν⁻¹ ^ 3 * W) := by
      have h0 : ∀ j l : Fin 3, ‖physPd2 (rawU Pl L τ') j l y'‖ ≤ A1 * L.ν⁻¹ ^ 3 * W := fun j l =>
        (hPd2 j l).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs32_le hA10) hW0)
      unfold hessSize; simp only [Fin.sum_univ_three]
      linarith [h0 0 0, h0 0 1, h0 0 2, h0 1 0, h0 1 1, h0 1 2, h0 2 0, h0 2 1, h0 2 2]
    calc L.ν * hessSize (rawU Pl L τ') y' ≤ 1 * (9 * (A1 * L.ν⁻¹ ^ 3 * W)) :=
          mul_le_mul hν1 hh (Finset.sum_nonneg fun _ _ =>
            Finset.sum_nonneg fun _ _ => norm_nonneg _) zero_le_one
      _ = 9 * A1 * L.ν⁻¹ ^ 3 * W := by ring
  have hpres' : presGradSize (liftP L τ') y' ≤ 3 * A1 * L.ν⁻¹ ^ 3 * W := by
    have h0 : ‖physGrad (liftP L τ') y'‖ ≤ A1 * L.ν⁻¹ ^ 3 * W :=
      hPr.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs32_le hA10) hW0)
    linarith [presGradSize_le_three_norm (liftP L τ') y', h0]
  have hUsq' : ‖rawU Pl L τ' y'‖ ^ 2 ≤ A1 ^ 2 * L.ν⁻¹ ^ 3 * W ^ 2 := by
    have hsq1 : ‖rawU Pl L τ' y'‖ ^ 2 ≤ (A1 * Real.sqrt p'.1 * W) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hU 2
    have hsq2 : (A1 * Real.sqrt p'.1 * W) ^ 2 = A1 ^ 2 * p'.1 * W ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hs0]
    rw [hsq2] at hsq1
    exact hsq1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs_le3 (sq_nonneg A1)) (sq_nonneg W))
  -- Bound W and W^2 using TrainMomentAt
  set B2 := max C2 0 * L.ν⁻¹ ^ k2
  have hB20 : 0 ≤ B2 := by positivity
  have hW4 : trainWeight 4 L p' ≤ B2 :=
    (h2 p' hp'pos hp'le).trans (mul_le_mul_of_nonneg_right (le_max_left C2 0) (by positivity))
  have hW_le : W ≤ B2 * (1 + |p.2.2|)⁻¹ := by
    rw [← hp'2]
    exact trainWeight_three_le_inv_eta L hW4
  have hinv_le1 : (1 + |p.2.2|)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [abs_nonneg p.2.2])
  have hinv0 : 0 ≤ (1 + |p.2.2|)⁻¹ := by positivity
  have hWsq_le : W ^ 2 ≤ B2 ^ 2 * (1 + |p.2.2|)⁻¹ := by
    calc W ^ 2 ≤ (B2 * (1 + |p.2.2|)⁻¹) ^ 2 := pow_le_pow_left₀ hW0 hW_le 2
      _ = B2 ^ 2 * (1 + |p.2.2|)⁻¹ * (1 + |p.2.2|)⁻¹ := by ring
      _ ≤ B2 ^ 2 * (1 + |p.2.2|)⁻¹ * 1 := mul_le_mul_of_nonneg_left hinv_le1 (by positivity)
      _ = B2 ^ 2 * (1 + |p.2.2|)⁻¹ := mul_one _
  have htot : coefSize L.ν (rawU Pl L) (liftP L) τ' y' ≤
      (16 * A1 * B2 + A1 ^ 2 * B2 ^ 2) * L.ν⁻¹ ^ 3 * (1 + |p.2.2|)⁻¹ := by
    have hlin : 16 * A1 * L.ν⁻¹ ^ 3 * W ≤ 16 * A1 * B2 * L.ν⁻¹ ^ 3 * (1 + |p.2.2|)⁻¹ := by
      calc 16 * A1 * L.ν⁻¹ ^ 3 * W ≤ 16 * A1 * L.ν⁻¹ ^ 3 * (B2 * (1 + |p.2.2|)⁻¹) :=
            mul_le_mul_of_nonneg_left hW_le (by positivity)
        _ = 16 * A1 * B2 * L.ν⁻¹ ^ 3 * (1 + |p.2.2|)⁻¹ := by ring
    have hquad : A1 ^ 2 * L.ν⁻¹ ^ 3 * W ^ 2 ≤ A1 ^ 2 * B2 ^ 2 * L.ν⁻¹ ^ 3 * (1 + |p.2.2|)⁻¹ := by
      calc A1 ^ 2 * L.ν⁻¹ ^ 3 * W ^ 2 ≤ A1 ^ 2 * L.ν⁻¹ ^ 3 * (B2 ^ 2 * (1 + |p.2.2|)⁻¹) :=
            mul_le_mul_of_nonneg_left hWsq_le (by positivity)
        _ = A1 ^ 2 * B2 ^ 2 * L.ν⁻¹ ^ 3 * (1 + |p.2.2|)⁻¹ := by ring
    unfold coefSize
    linarith
  refine htot.trans (mul_le_mul_of_nonneg_right ?_ hinv0)
  have hP_le1 : L.ν⁻¹ ^ (k1 + k2 + 3) ≤ L.ν⁻¹ ^ (2 * k1 + 2 * k2 + 3) :=
    pow_le_pow_right₀ hνinv1 (by omega)
  calc (16 * A1 * B2 + A1 ^ 2 * B2 ^ 2) * L.ν⁻¹ ^ 3
      = 16 * (2 + |C1|) * max C2 0 * L.ν⁻¹ ^ (k1 + k2 + 3) +
          (2 + |C1|) ^ 2 * max C2 0 ^ 2 * L.ν⁻¹ ^ (2 * k1 + 2 * k2 + 3) := by
        simp only [A1, B2, P1]
        ring
    _ ≤ 16 * (2 + |C1|) * max C2 0 * L.ν⁻¹ ^ (2 * k1 + 2 * k2 + 3) +
          (2 + |C1|) ^ 2 * max C2 0 ^ 2 * L.ν⁻¹ ^ (2 * k1 + 2 * k2 + 3) :=
        add_le_add (mul_le_mul_of_nonneg_left hP_le1 (by positivity)) le_rfl
    _ = (16 * (2 + |C1|) * max C2 0 + (2 + |C1|) ^ 2 * max C2 0 ^ 2) *
          L.ν⁻¹ ^ (2 * k1 + 2 * k2 + 3) := by ring

/-! ## 3. Exponential entrance tail and `(s, η)` square-integral bound -/

/-- `e^{-(m₁ ν²) |η|} ≤ (min 1 m₁)⁻¹ ν⁻² (1 + |η|)⁻¹` for `m₁ > 0` and `0 < ν ≤ 1`. -/
theorem exp_neg_abs_le_inv_one_add {m₁ ν : ℝ} (hm : 0 < m₁) (hν : 0 < ν) (hν1 : ν ≤ 1) (η : ℝ) :
    Real.exp (-(m₁ * ν ^ 2) * |η|) ≤ (min 1 m₁)⁻¹ * ν⁻¹ ^ 2 * (1 + |η|)⁻¹ := by
  set δ := min 1 m₁ * ν ^ 2
  have hmin : 0 < min 1 m₁ := lt_min one_pos hm
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    calc δ ≤ 1 * 1 ^ 2 := mul_le_mul (min_le_left 1 m₁)
          (pow_le_pow_left₀ hν.le hν1 2) (by positivity) zero_le_one
      _ = 1 := by ring
  have hδm : δ ≤ m₁ * ν ^ 2 := mul_le_mul_of_nonneg_right (min_le_right 1 m₁) (sq_nonneg ν)
  have h1 : δ * (1 + |η|) ≤ 1 + (m₁ * ν ^ 2) * |η| := by
    nlinarith [abs_nonneg η]
  have h2 : 1 + (m₁ * ν ^ 2) * |η| ≤ Real.exp ((m₁ * ν ^ 2) * |η|) := by
    linarith [Real.add_one_le_exp ((m₁ * ν ^ 2) * |η|)]
  have h3 : Real.exp (-(m₁ * ν ^ 2) * |η|) ≤ (δ * (1 + |η|))⁻¹ := by
    rw [show -(m₁ * ν ^ 2) * |η| = -((m₁ * ν ^ 2) * |η|) by ring, Real.exp_neg]
    exact inv_anti₀ (by positivity) (h1.trans h2)
  have h4 : (δ * (1 + |η|))⁻¹ = (min 1 m₁)⁻¹ * ν⁻¹ ^ 2 * (1 + |η|)⁻¹ := by
    simp only [δ, mul_inv, inv_pow]
  rwa [h4] at h3

/-- The `(s, η)` square integral of `bgBeta A` on `s ∈ Ioc 0 (1 / ν)` is at most `4 A² ν⁻⁴`. -/
theorem bgBeta_s_eta_lintegral_le {ν A : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) :
    ∫⁻ s in Ioc (0 : ℝ) (1 / ν), ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (5 / 2 : ℝ) * bgBeta A s η ^ 2) ≤
      ENNReal.ofReal (4 * A ^ 2 * ν⁻¹ ^ 4) := by
  have hνinv1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have heta : ∫⁻ η : ℝ, ENNReal.ofReal (((1 + |η|) ^ 2)⁻¹) ≤ ENNReal.ofReal 4 := by
    calc ∫⁻ η : ℝ, ENNReal.ofReal (((1 + |η|) ^ 2)⁻¹)
        ≤ ENNReal.ofReal Real.pi := by
          rw [← integral_univ_inv_one_add_sq, ofReal_integral_eq_lintegral_ofReal
            integrable_inv_one_add_sq (ae_of_all _ fun x => by positivity)]
          refine lintegral_mono fun η => ENNReal.ofReal_le_ofReal ?_
          exact inv_anti₀ (by positivity) (by nlinarith [abs_nonneg η, sq_abs η])
      _ ≤ ENNReal.ofReal 4 := ENNReal.ofReal_le_ofReal Real.pi_le_four
  have hinner : ∀ s ∈ Ioc (0 : ℝ) (1 / ν),
      ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (5 / 2 : ℝ) * bgBeta A s η ^ 2) ≤
        ENNReal.ofReal (4 * A ^ 2 * ν⁻¹ ^ 3) := by
    intro s hs
    have hs0 : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.1.le _
    have hs_le : s ^ (5 / 2 : ℝ) ≤ ν⁻¹ ^ 3 := by
      have hs1 : s ≤ ν⁻¹ := by simpa [one_div] using hs.2
      calc s ^ (5 / 2 : ℝ) ≤ (ν⁻¹) ^ (5 / 2 : ℝ) :=
            Real.rpow_le_rpow hs.1.le hs1 (by norm_num)
        _ ≤ (ν⁻¹) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hνinv1 (by norm_num)
        _ = ν⁻¹ ^ 3 := Real.rpow_natCast ν⁻¹ 3
    have hrew : (fun η : ℝ => ENNReal.ofReal (s ^ (5 / 2 : ℝ) * bgBeta A s η ^ 2)) =
        fun η : ℝ => ENNReal.ofReal (s ^ (5 / 2 : ℝ) * A ^ 2) *
          ENNReal.ofReal (((1 + |η|) ^ 2)⁻¹) := by
      funext η
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      unfold bgBeta
      rw [mul_pow, inv_pow]
      ring
    rw [hrew, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (s ^ (5 / 2 : ℝ) * A ^ 2) *
          ∫⁻ η : ℝ, ENNReal.ofReal (((1 + |η|) ^ 2)⁻¹)
        ≤ ENNReal.ofReal (ν⁻¹ ^ 3 * A ^ 2) * ENNReal.ofReal 4 :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hs_le (sq_nonneg A)))
            heta
      _ = ENNReal.ofReal (4 * A ^ 2 * ν⁻¹ ^ 3) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  calc ∫⁻ s in Ioc (0 : ℝ) (1 / ν), ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (5 / 2 : ℝ) * bgBeta A s η ^ 2)
      ≤ ∫⁻ _s in Ioc (0 : ℝ) (1 / ν), ENNReal.ofReal (4 * A ^ 2 * ν⁻¹ ^ 3) :=
        setLIntegral_mono' measurableSet_Ioc hinner
    _ = ENNReal.ofReal (4 * A ^ 2 * ν⁻¹ ^ 3) * volume (Ioc (0 : ℝ) (1 / ν)) :=
        setLIntegral_const _ _
    _ = ENNReal.ofReal (4 * A ^ 2 * ν⁻¹ ^ 4) := by
        rw [Real.volume_Ioc, sub_zero, one_div, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-! ## 4. Sequence-level localized background bound from `RepairStanding` -/

/-- Unconditional localized background bound (`bgBl`, `bgBeta`) along the sequence from
`D.RepairStanding`: proved from `ringChartRules`, `trainMoment`, and `entWPt`. -/
theorem bgLocal_eventually (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      let L := D.level n
      (∀ (τ : ℝ) (p : Chart), 0 < p.1 → p.1 ≤ 1 / L.ν →
        bgBl L τ (NearInst.chartY L.ε⁻¹ p) ≤ bgBeta (C * L.ν⁻¹ ^ k) p.1 p.2.2) ∧
      ∫⁻ s in Ioc (0 : ℝ) (1 / L.ν), ∫⁻ η : ℝ,
          ENNReal.ofReal (s ^ (5 / 2 : ℝ) * bgBeta (C * L.ν⁻¹ ^ k) s η ^ 2) ≤
        ENNReal.ofReal (4 * C ^ 2 * L.ν⁻¹ ^ (2 * k + 4)) := by
  obtain ⟨C1, k1, hrc⟩ := ringChartRules D hst
  obtain ⟨C2, k2, htm⟩ := trainMoment D hst
  obtain ⟨C3, k3, m1, hm1, hent⟩ := entWPt D hst
  have hle1 := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  have hρ1 := rhoRep_le_one_eventually D hst
  set Cr := 16 * (2 + |C1|) * max C2 0 + (2 + |C1|) ^ 2 * max C2 0 ^ 2
  set kr := 2 * k1 + 2 * k2 + 3
  set Ce := max C3 0
  set Cm := (min 1 m1)⁻¹
  set C := 2 * Cr + (13 + 2 * Ce) * Ce * Cm
  set k := max kr (2 * k3 + 2)
  have hC0 : 0 ≤ C := by
    have : 0 < min 1 m1 := lt_min one_pos hm1
    positivity
  refine ⟨C, k, hC0, ?_⟩
  filter_upwards [hrc, htm, hent, hle1, hρ1] with n hrc_n htm_n hent_n hle1_n hρ1_n
  intro L
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hν1 : L.ν ≤ 1 := hle1_n.1
  have hε1 : L.ε ≤ 1 := hle1_n.2
  have hνinv1 : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  refine ⟨?_, ?_⟩
  · intro τ p hp hp1
    have hR : L.ε⁻¹ ≠ 0 := inv_ne_zero hε.ne'
    set p' : Chart := (p.1, (L.ε⁻¹ * (τ - Real.log p.1) / 2, p.2.2))
    obtain ⟨hp'1, hp'2, hy, hτ⟩ := chart_reparam L.ε⁻¹ τ hR p
    have hp'pos : 0 < p'.1 := hp'1.symm ▸ hp
    have hraw := coefSize_rawU_chart_le D.Pl L hν1 hε1 hrc_n htm_n.2.1 τ hp hp1
    -- Bound coefChgDens (L.V τ) (rawU D.Pl L τ) at chartY L.ε⁻¹ p using entWPt
    have hent_p' := hent_n p' hp'pos
    rw [hy, hτ, hp'2] at hent_p'
    set c := coefChgDens (L.V τ) (rawU D.Pl L τ) (NearInst.chartY L.ε⁻¹ p)
    have hc0 : 0 ≤ c := coefChgDens_nonneg _ _ _
    have hε_le_ρ : Real.exp (D.K.m0 / L.ν) * L.ε ≤ 1 := by
      have hε311 : L.ε ≤ L.ε ^ (3 / 11 : ℝ) := by
        simpa using Real.rpow_le_rpow_of_exponent_ge hε hε1 (by norm_num : (3 / 11 : ℝ) ≤ 1)
      calc Real.exp (D.K.m0 / L.ν) * L.ε
          ≤ Real.exp (D.K.m0 / L.ν) * L.ε ^ (3 / 11 : ℝ) :=
            mul_le_mul_of_nonneg_left hε311 (Real.exp_pos _).le
        _ = rhoRep D.K L := by unfold rhoRep; ring
        _ ≤ 1 := hρ1_n
    have hc_exp : c ≤ Ce * L.ν⁻¹ ^ k3 * Real.exp (-(m1 * L.ν ^ 2) * |p.2.2|) := by
      calc c ≤ C3 * L.ν⁻¹ ^ k3 * (Real.exp (D.K.m0 / L.ν) * L.ε) *
              Real.exp (-(m1 * L.ν ^ 2) * |p.2.2|) := hent_p'
        _ ≤ Ce * L.ν⁻¹ ^ k3 * (Real.exp (D.K.m0 / L.ν) * L.ε) *
              Real.exp (-(m1 * L.ν ^ 2) * |p.2.2|) := by
            have : C3 ≤ Ce := le_max_left C3 0
            have h1 : C3 * L.ν⁻¹ ^ k3 * (Real.exp (D.K.m0 / L.ν) * L.ε) ≤
                Ce * L.ν⁻¹ ^ k3 * (Real.exp (D.K.m0 / L.ν) * L.ε) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (by positivity))
                (by positivity)
            exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ ≤ Ce * L.ν⁻¹ ^ k3 * 1 * Real.exp (-(m1 * L.ν ^ 2) * |p.2.2|) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hε_le_ρ (by positivity)) (Real.exp_pos _).le
        _ = Ce * L.ν⁻¹ ^ k3 * Real.exp (-(m1 * L.ν ^ 2) * |p.2.2|) := by ring
    have hc_rough : c ≤ Ce * L.ν⁻¹ ^ k3 := by
      have hpos : 0 ≤ m1 * L.ν ^ 2 * |p.2.2| := by positivity
      have hexp1 : Real.exp (-(m1 * L.ν ^ 2) * |p.2.2|) ≤ 1 :=
        Real.exp_le_one_iff.2 (by linarith)
      calc c ≤ Ce * L.ν⁻¹ ^ k3 * Real.exp (-(m1 * L.ν ^ 2) * |p.2.2|) := hc_exp
        _ ≤ Ce * L.ν⁻¹ ^ k3 * 1 := mul_le_mul_of_nonneg_left hexp1 (by positivity)
        _ = Ce * L.ν⁻¹ ^ k3 := mul_one _
    have hc_eta : c ≤ Ce * Cm * L.ν⁻¹ ^ (k3 + 2) * (1 + |p.2.2|)⁻¹ := by
      have hexp := exp_neg_abs_le_inv_one_add hm1 hν hν1 p.2.2
      calc c ≤ Ce * L.ν⁻¹ ^ k3 * ((min 1 m1)⁻¹ * L.ν⁻¹ ^ 2 * (1 + |p.2.2|)⁻¹) :=
            hc_exp.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
        _ = Ce * Cm * L.ν⁻¹ ^ (k3 + 2) * (1 + |p.2.2|)⁻¹ := by
            simp only [Cm]; ring
    have hchg_prod : (1 + 12 * L.ν + 2 * c) * c ≤
        (13 + 2 * Ce) * Ce * Cm * L.ν⁻¹ ^ (2 * k3 + 2) * (1 + |p.2.2|)⁻¹ := by
      have hfac : 1 + 12 * L.ν + 2 * c ≤ (13 + 2 * Ce) * L.ν⁻¹ ^ k3 := by
        have h13 : 1 + 12 * L.ν ≤ 13 * L.ν⁻¹ ^ k3 := by
          have : (13 : ℝ) = 13 * 1 := (mul_one 13).symm
          linarith [hν1, one_le_pow₀ hνinv1 (n := k3)]
        linarith [hc_rough]
      have hmin : 0 < min 1 m1 := lt_min one_pos hm1
      calc (1 + 12 * L.ν + 2 * c) * c
          ≤ ((13 + 2 * Ce) * L.ν⁻¹ ^ k3) * (Ce * Cm * L.ν⁻¹ ^ (k3 + 2) * (1 + |p.2.2|)⁻¹) :=
            mul_le_mul hfac hc_eta hc0 (by positivity)
        _ = (13 + 2 * Ce) * Ce * Cm * L.ν⁻¹ ^ (2 * k3 + 2) * (1 + |p.2.2|)⁻¹ := by ring
    have hsplit := coefSize_le_two_raw_add_chg hν.le L.V (rawU D.Pl L) (liftP L) τ
      (NearInst.chartY L.ε⁻¹ p)
    have hP_kr : L.ν⁻¹ ^ kr ≤ L.ν⁻¹ ^ k := pow_le_pow_right₀ hνinv1 (le_max_left _ _)
    have hP_ke : L.ν⁻¹ ^ (2 * k3 + 2) ≤ L.ν⁻¹ ^ k := pow_le_pow_right₀ hνinv1 (le_max_right _ _)
    have hmin : 0 < min 1 m1 := lt_min one_pos hm1
    have hinv0 : 0 ≤ (1 + |p.2.2|)⁻¹ := by positivity
    unfold bgBl bgBeta
    calc coefSize L.ν L.V (liftP L) τ (NearInst.chartY L.ε⁻¹ p)
        ≤ 2 * (Cr * L.ν⁻¹ ^ kr * (1 + |p.2.2|)⁻¹) +
            (13 + 2 * Ce) * Ce * Cm * L.ν⁻¹ ^ (2 * k3 + 2) * (1 + |p.2.2|)⁻¹ := by
          linarith [hsplit, hraw, hchg_prod]
      _ ≤ 2 * (Cr * L.ν⁻¹ ^ k * (1 + |p.2.2|)⁻¹) +
            (13 + 2 * Ce) * Ce * Cm * L.ν⁻¹ ^ k * (1 + |p.2.2|)⁻¹ := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP_kr (by positivity)) hinv0)
              (by norm_num)
          · exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hP_ke (by positivity)) hinv0
      _ = C * L.ν⁻¹ ^ k * (1 + |p.2.2|)⁻¹ := by simp only [C]; ring
  · refine (bgBeta_s_eta_lintegral_le hν hν1).trans ?_
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    ring

end UnforcedLeray.Short.PartIIIb.Concrete
