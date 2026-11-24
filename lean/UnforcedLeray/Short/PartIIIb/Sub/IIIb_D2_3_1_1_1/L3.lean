import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1

/-!
# `OldCutMeasurable` (PartIII-b:IIIb-D2/3/1/1/1, leaf L3)

Source of record: `the November 2 reference manuscript` 2666-2683.
`oldCutSrc R c r G τ z = if hRad z ≤ r then cartLift R c G τ z else 0`, and the entries of
`cartLift` are built from `chartOf` (measurable through `Real.log`, `⌊·⌋` and the cast
`ℤ → ℝ`), `cylFrame`, `nsSym` (coordinate maps of `Ten3`), by sums and products.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

lemma oldCut_measurable_coord (a : Fin 3) : Measurable fun z : Space => z a :=
  (measurable_pi_apply a).comp (PiLp.continuous_ofLp 2 _).measurable

lemma oldCut_measurable_coordTen (ab : Fin 3 × Fin 3) : Measurable fun T : Ten3 => T ab :=
  (measurable_pi_apply ab).comp (PiLp.continuous_ofLp 2 _).measurable

lemma oldCut_measurable_nsSym_entry (a b : Fin 3) :
    Measurable fun T : Ten3 => NearInst.nsSym T a b := by
  fin_cases a <;> fin_cases b <;> simp [NearInst.nsSym, NearInst.symRZ] <;>
    apply_rules [Measurable.add, Measurable.div_const, Measurable.mul, measurable_const,
      oldCut_measurable_coordTen]

lemma oldCut_measurable_hRad : Measurable fun z : Space => NearInst.hRad z :=
  Real.continuous_sqrt.measurable.comp
    (((oldCut_measurable_coord 0).pow_const 2).add ((oldCut_measurable_coord 1).pow_const 2))

lemma oldCut_measurable_coord_snd (a : Fin 3) : Measurable fun p : ℝ × Space => p.2 a :=
  (oldCut_measurable_coord a).comp measurable_snd

lemma oldCut_measurable_hRad_snd : Measurable fun p : ℝ × Space => NearInst.hRad p.2 :=
  oldCut_measurable_hRad.comp measurable_snd

lemma oldCut_measurable_floor_cast : Measurable fun x : ℝ => ((⌊x⌋ : ℤ) : ℝ) :=
  (Measurable.of_discrete (f := fun n : ℤ => (n : ℝ))).comp Int.measurable_floor

/-- The chart point `chartOf R c z τ` is jointly measurable in `(τ, z)`. -/
lemma oldCut_measurable_chartOf (R c : ℝ) :
    Measurable fun p : ℝ × Space => NearInst.chartOf R c p.2 p.1 := by
  have hrp : Measurable fun p : ℝ × Space => NearInst.hRad p.2 :=
    oldCut_measurable_hRad.comp measurable_snd
  have hQ : Measurable fun p : ℝ × Space =>
      R * Real.log (NearInst.hRad p.2 / R) + R * p.1 / 2 :=
    (measurable_const.mul (Real.measurable_log.comp (hrp.div_const R))).add
      ((measurable_const.mul measurable_fst).div_const 2)
  have hfl : Measurable fun p : ℝ × Space =>
      ((⌊(R * Real.log (NearInst.hRad p.2 / R) + R * p.1 / 2) / c + 1 / 2⌋ : ℤ) : ℝ) :=
    oldCut_measurable_floor_cast.comp ((hQ.div_const c).add_const (1 / 2))
  have hq : Measurable fun p : ℝ × Space =>
      R * Real.log (NearInst.hRad p.2 / R) + R * p.1 / 2
        - c * ((⌊(R * Real.log (NearInst.hRad p.2 / R) + R * p.1 / 2) / c + 1 / 2⌋ : ℤ) : ℝ) :=
    hQ.sub (measurable_const.mul hfl)
  have hη : Measurable fun p : ℝ × Space => R * p.2 2 / NearInst.hRad p.2 :=
    (measurable_const.mul ((oldCut_measurable_coord 2).comp measurable_snd)).div hrp
  unfold NearInst.chartOf
  exact (measurable_const.div (hrp.pow_const 2)).prodMk (hq.prodMk hη)

/-- The cut old source is jointly measurable (source 2666-2683). -/
theorem oldCutMeasurable : OldCutMeasurable := by
  intro R c r G hG i j
  have hχ := oldCut_measurable_chartOf R c
  have hT : Measurable fun p : ℝ × Space => G (NearInst.chartOf R c p.2 p.1) := hG.comp hχ
  have hs : Measurable fun p : ℝ × Space => (NearInst.chartOf R c p.2 p.1).1 :=
    measurable_fst.comp hχ
  have hN : ∀ a b : Fin 3, Measurable fun p : ℝ × Space =>
      NearInst.nsSym (G (NearInst.chartOf R c p.2 p.1)) a b :=
    fun a b => (oldCut_measurable_nsSym_entry a b).comp hT
  have hC : ∀ a b : Fin 3, Measurable fun p : ℝ × Space => NearInst.cylFrame p.2 a b := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [NearInst.cylFrame] <;>
      apply_rules [Measurable.add, Measurable.sub, Measurable.mul, Measurable.div,
        Measurable.neg, Measurable.inv, measurable_const, oldCut_measurable_coord_snd,
        oldCut_measurable_hRad_snd]
  have hfun : (fun p : ℝ × Space => oldCutSrc R c r G p.1 p.2 i j) =
      fun p => if NearInst.hRad p.2 ≤ r then (NearInst.cartLift R c G p.1 p.2) i j else 0 := by
    funext p
    simp only [oldCutSrc, oldPhys]
    split_ifs <;> simp
  rw [hfun]
  refine Measurable.ite (measurableSet_le (oldCut_measurable_hRad.comp measurable_snd)
    measurable_const) ?_ measurable_const
  unfold NearInst.cartLift
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.smul_apply,
    smul_eq_mul]
  repeat' first
    | exact hC _ _
    | exact hN _ _
    | exact hs
    | exact measurable_const
    | apply Measurable.add
    | apply Measurable.mul

end UnforcedLeray.Short.PartIIIb.Concrete
