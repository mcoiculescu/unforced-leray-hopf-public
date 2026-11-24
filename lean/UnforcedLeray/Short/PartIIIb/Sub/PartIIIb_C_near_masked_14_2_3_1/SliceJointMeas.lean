import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_1

/-!
# Joint measurability of the squared Cartesian slice (`PartIII-b:C/near/masked/14/2/3/1/3`)

Source: `the November 2 reference manuscript`
3996-4011.  The map `(τ, y) ↦ cartSliceOut … (liftNorm … (τ + 2 log l)) y ^ 2` is measurable:
the integrand in `(τ, y, z)` is measurable, and the parametric Lebesgue integral in `z` is measurable
(`Measurable.lintegral_prod_right'`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal Matrix

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- Joint measurability of the lift norm in `(τ, z)`. -/
lemma la_measurable_liftNorm_joint (R c : ℝ) (f : Chart → Ten3) (hf : Measurable f) :
    Measurable fun p : ℝ × Space => liftNorm R c f p.1 p.2 := by
  unfold liftNorm UnforcedLeray.Short.IIIa.tensorNorm
  apply Measurable.sqrt
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (T8_1.measurable_cartLift_entry R c f hf i j).pow_const 2

/-- The integrand of the slice, as a function of `((τ, y), z)`. -/
def laJointH (R c δ l : ℝ) (f : Chart → Ten3) (q : (ℝ × Space) × Space) : ℝ≥0∞ :=
  if Real.exp δ * (R ^ 2 / (q.1.2 0 ^ 2 + q.1.2 1 ^ 2)) < R ^ 2 / (q.2 0 ^ 2 + q.2 1 ^ 2) then
    ENNReal.ofReal (‖q.1.2 - l • q.2‖ ^ (-4 : ℝ) * liftNorm R c f (q.1.1 + 2 * Real.log l) q.2)
  else 0

lemma la_meas_y0 : Measurable fun q : (ℝ × Space) × Space => q.1.2 0 :=
  (T8_1.measurable_coord 0).comp (measurable_snd.comp measurable_fst)

lemma la_meas_y1 : Measurable fun q : (ℝ × Space) × Space => q.1.2 1 :=
  (T8_1.measurable_coord 1).comp (measurable_snd.comp measurable_fst)

lemma la_meas_z0 : Measurable fun q : (ℝ × Space) × Space => q.2 0 :=
  (T8_1.measurable_coord 0).comp measurable_snd

lemma la_meas_z1 : Measurable fun q : (ℝ × Space) × Space => q.2 1 :=
  (T8_1.measurable_coord 1).comp measurable_snd

lemma la_meas_diff (l : ℝ) : Measurable fun q : (ℝ × Space) × Space => ‖q.1.2 - l • q.2‖ :=
  ((measurable_snd.comp measurable_fst).sub (measurable_snd.const_smul l)).norm

lemma la_meas_lift (R c : ℝ) (f : Chart → Ten3) (hf : Measurable f) (l : ℝ) :
    Measurable fun q : (ℝ × Space) × Space =>
      liftNorm R c f (q.1.1 + 2 * Real.log l) q.2 := by
  have hτ : Measurable fun q : (ℝ × Space) × Space => q.1.1 + 2 * Real.log l :=
    (measurable_fst.comp measurable_fst).add_const _
  have hmap : Measurable fun q : (ℝ × Space) × Space => (q.1.1 + 2 * Real.log l, q.2) :=
    hτ.prodMk measurable_snd
  have hLN := la_measurable_liftNorm_joint R c f hf
  exact Measurable.comp (g := fun p : ℝ × Space => liftNorm R c f p.1 p.2)
    (f := fun q : (ℝ × Space) × Space => (q.1.1 + 2 * Real.log l, q.2)) hLN hmap

lemma la_meas_L (R δ : ℝ) : Measurable fun q : (ℝ × Space) × Space =>
    Real.exp δ * (R ^ 2 / (q.1.2 0 ^ 2 + q.1.2 1 ^ 2)) :=
  measurable_const.mul (measurable_const.div ((la_meas_y0.pow_const 2).add (la_meas_y1.pow_const 2)))

lemma la_meas_R (R : ℝ) : Measurable fun q : (ℝ × Space) × Space =>
    R ^ 2 / (q.2 0 ^ 2 + q.2 1 ^ 2) :=
  measurable_const.div ((la_meas_z0.pow_const 2).add (la_meas_z1.pow_const 2))

lemma la_measurable_laJointH (R c δ l : ℝ) (f : Chart → Ten3) (hf : Measurable f) :
    Measurable (laJointH R c δ l f) := by
  have hval : Measurable fun q : (ℝ × Space) × Space =>
      ENNReal.ofReal (‖q.1.2 - l • q.2‖ ^ (-4 : ℝ) * liftNorm R c f (q.1.1 + 2 * Real.log l) q.2) :=
    ENNReal.measurable_ofReal.comp ((la_meas_diff l).pow_const _ |>.mul (la_meas_lift R c f hf l))
  exact Measurable.ite (measurableSet_lt (la_meas_L R δ) (la_meas_R R)) hval measurable_const

theorem sliceJointMeas : UnforcedLeray.Short.PartIIIb.NearInst.Masked.SliceJointMeas := by
  intro R c δ S l f hf
  have hH := la_measurable_laJointH R c δ l f hf.measurable
  have hG : Measurable fun p : ℝ × Space => ∫⁻ z : Space, laJointH R c δ l f (p, z) :=
    hH.lintegral_prod_right'
  have hA : Measurable fun p : ℝ × Space => R ^ 2 / (p.2 0 ^ 2 + p.2 1 ^ 2) := by
    have h0 : Measurable fun p : ℝ × Space => p.2 0 := T8_1.measurable_coord 0 |>.comp measurable_snd
    have h1 : Measurable fun p : ℝ × Space => p.2 1 := T8_1.measurable_coord 1 |>.comp measurable_snd
    exact measurable_const.div ((h0.pow_const 2).add (h1.pow_const 2))
  have key : Measurable fun p : ℝ × Space =>
      (if R ^ 2 / (p.2 0 ^ 2 + p.2 1 ^ 2) < S then
        ENNReal.ofReal (Real.sqrt (R ^ 2 / (p.2 0 ^ 2 + p.2 1 ^ 2)))⁻¹ *
          ∫⁻ z : Space, laJointH R c δ l f (p, z)
      else 0) ^ (2 : ℝ) := by
    refine Measurable.pow_const ?_ _
    refine Measurable.ite (measurableSet_lt hA measurable_const) ?_ measurable_const
    exact (ENNReal.measurable_ofReal.comp (hA.sqrt.inv)).mul hG
  exact key

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
