import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
Hedberg near part (`HedbergNear`), source `the November 2 reference manuscript`
(Biot-Savart splitting, cf. lines 850 and 3054). Scalar layer-cake identity for `|w|⁻²`,
then Tonelli on the ball `B(y,R)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Scalar layer-cake identity: for `0 < a < R`,
`(a²)⁻¹ = (R²)⁻¹ + ∫_{(0,R)} 2 s⁻³ 1_{a<s} ds`. -/
private lemma inv_sq_repr (a R : ℝ) (ha : 0 < a) (haR : a < R) :
    ENNReal.ofReal ((a ^ 2)⁻¹) = ENNReal.ofReal ((R ^ 2)⁻¹) +
      ∫⁻ s in Ioo 0 R, (if a < s then ENNReal.ofReal (2 * (s ^ 3)⁻¹) else 0) := by
  have hind : ∀ s : ℝ, (if a < s then ENNReal.ofReal (2 * (s ^ 3)⁻¹) else 0)
      = (Ioi a).indicator (fun s => ENNReal.ofReal (2 * (s ^ 3)⁻¹)) s := by
    intro s
    simp [Set.indicator_apply]
  simp_rw [hind]
  rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  have hset : Ioi a ∩ Ioo 0 R = Ioo a R := by
    ext s
    simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨h1, _, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by linarith, h2⟩
  rw [hset]
  have hcont : ContinuousOn (fun s : ℝ => 2 * (s ^ 3)⁻¹) (Icc a R) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ (continuousOn_id.pow 3)
    intro s hs
    exact pow_ne_zero _ (lt_of_lt_of_le ha hs.1).ne'
  have hint : IntegrableOn (fun s : ℝ => 2 * (s ^ 3)⁻¹) (Ioo a R) :=
    (hcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo a R)] (fun s : ℝ => 2 * (s ^ 3)⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr (pow_nonneg (lt_trans ha hs.1).le 3))
  have hderiv : ∀ x ∈ uIcc a R, HasDerivAt (fun s : ℝ => -(s ^ 2)⁻¹) (2 * (x ^ 3)⁻¹) x := by
    intro x hx
    rw [uIcc_of_le haR.le] at hx
    have hx0 : x ≠ 0 := (lt_of_lt_of_le ha hx.1).ne'
    have h : HasDerivAt (fun s : ℝ => -(s ^ 2)⁻¹)
        (-(-(((2 : ℕ) : ℝ) * x ^ (2 - 1)) / (x ^ 2) ^ 2)) x :=
      ((hasDerivAt_pow 2 x).inv (pow_ne_zero 2 hx0)).neg
    refine h.congr_deriv ?_
    norm_num <;> field_simp <;> ring
  have hIoc : IntervalIntegrable (fun s : ℝ => 2 * (s ^ 3)⁻¹) volume a R :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le haR.le).mpr
      (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  have hval : ∫ s in Ioo a R, 2 * (s ^ 3)⁻¹ = (a ^ 2)⁻¹ - (R ^ 2)⁻¹ := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le haR.le]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => -(s ^ 2)⁻¹) (f' := fun s : ℝ => 2 * (s ^ 3)⁻¹) hderiv hIoc]
    show -(R ^ 2)⁻¹ - -(a ^ 2)⁻¹ = (a ^ 2)⁻¹ - (R ^ 2)⁻¹
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hval]
  have h1 : 0 ≤ (R ^ 2)⁻¹ := by positivity
  have h2 : 0 ≤ (a ^ 2)⁻¹ - (R ^ 2)⁻¹ :=
    sub_nonneg.mpr (inv_anti₀ (pow_pos ha 2) (by nlinarith))
  rw [← ENNReal.ofReal_add h1 h2]
  congr 1
  ring

theorem hedbergNear : HedbergNear := by
  intro G hG y R hR
  have hkernM : Measurable (fun s : ℝ => ENNReal.ofReal (2 * (s ^ 3)⁻¹)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul ((measurable_id.pow_const 3).inv))
  have hvol : ∀ s : ℝ, volume (ball y s) = ENNReal.ofReal s ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) :=
    fun s => EuclideanSpace.volume_ball_fin_three y s
  -- ball bound from the definition of the maximal function
  have hball : ∀ s : ℝ, 0 < s → ∫⁻ z in ball y s, G z ≤ volume (ball y s) * hlMax G y := by
    intro s hs
    have h0 : volume (ball y s) ≠ 0 := (measure_ball_pos volume y hs).ne'
    have ht : volume (ball y s) ≠ ⊤ := measure_ball_lt_top.ne
    have hle : (volume (ball y s))⁻¹ * ∫⁻ z in ball y s, G z ≤ hlMax G y := by
      unfold hlMax
      exact le_iSup (fun r : {r : ℝ // 0 < r} => (volume (ball y r.1))⁻¹ * ∫⁻ z in ball y r.1, G z)
        ⟨s, hs⟩
    calc ∫⁻ z in ball y s, G z
        = volume (ball y s) * ((volume (ball y s))⁻¹ * ∫⁻ z in ball y s, G z) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel h0 ht, one_mul]
      _ ≤ volume (ball y s) * hlMax G y := mul_le_mul_of_nonneg_left hle (by positivity)
  -- kernel identity
  have hpt : ∀ z ∈ ball y R, z ≠ y →
      G z * bsK2 (y - z) = ENNReal.ofReal ((4 * Real.pi)⁻¹) *
        (G z * ENNReal.ofReal ((R ^ 2)⁻¹) +
          ∫⁻ s in Ioo 0 R, G z * (if ‖y - z‖ < s then ENNReal.ofReal (2 * (s ^ 3)⁻¹) else 0)) := by
    intro z hz hzy
    have hpos : 0 < ‖y - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hzy))
    have hlt : ‖y - z‖ < R := by
      rw [mem_ball, dist_eq_norm] at hz
      rwa [norm_sub_rev]
    have hrep := inv_sq_repr ‖y - z‖ R hpos hlt
    have hmeas1 : Measurable (fun s : ℝ => if ‖y - z‖ < s then ENNReal.ofReal (2 * (s ^ 3)⁻¹) else 0) :=
      Measurable.ite (measurableSet_lt measurable_const measurable_id) hkernM measurable_const
    have hI : G z * ∫⁻ s in Ioo 0 R, (if ‖y - z‖ < s then ENNReal.ofReal (2 * (s ^ 3)⁻¹) else 0)
        = ∫⁻ s in Ioo 0 R, G z * (if ‖y - z‖ < s then ENNReal.ofReal (2 * (s ^ 3)⁻¹) else 0) :=
      (lintegral_const_mul _ hmeas1).symm
    rw [bsK2, ENNReal.ofReal_mul (by positivity), hrep]
    calc G z * (ENNReal.ofReal ((4 * Real.pi)⁻¹) *
          (ENNReal.ofReal ((R ^ 2)⁻¹) +
            ∫⁻ s in Ioo 0 R, (if ‖y - z‖ < s then ENNReal.ofReal (2 * (s ^ 3)⁻¹) else 0)))
        = ENNReal.ofReal ((4 * Real.pi)⁻¹) *
          (G z * ENNReal.ofReal ((R ^ 2)⁻¹) +
            G z * ∫⁻ s in Ioo 0 R, (if ‖y - z‖ < s then ENNReal.ofReal (2 * (s ^ 3)⁻¹) else 0)) := by
          ring
      _ = _ := by rw [hI]
  -- a.e. on the ball, the integrand has the representation
  have hae : ∀ᵐ z ∂(volume.restrict (ball y R)), G z * bsK2 (y - z) =
      ENNReal.ofReal ((4 * Real.pi)⁻¹) *
        (G z * ENNReal.ofReal ((R ^ 2)⁻¹) +
          ∫⁻ s in Ioo 0 R, G z * (if ‖y - z‖ < s then ENNReal.ofReal (2 * (s ^ 3)⁻¹) else 0)) := by
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume y), ae_restrict_mem measurableSet_ball]
      with z hz1 hz2
    exact hpt z hz2 hz1
  -- joint measurability for Tonelli
  have hmeasF : Measurable (fun p : Space × ℝ =>
      G p.1 * (if ‖y - p.1‖ < p.2 then ENNReal.ofReal (2 * (p.2 ^ 3)⁻¹) else 0)) := by
    apply Measurable.mul (hG.comp measurable_fst)
    exact Measurable.ite
      (measurableSet_lt ((continuous_const.sub continuous_fst).norm.measurable) measurable_snd)
      (hkernM.comp measurable_snd) measurable_const
  -- inner slice integral
  have hslice : ∀ s : ℝ, 0 < s → s < R →
      ∫⁻ z in ball y R, G z * (if ‖y - z‖ < s then ENNReal.ofReal (2 * (s ^ 3)⁻¹) else 0)
        = ENNReal.ofReal (2 * (s ^ 3)⁻¹) * ∫⁻ z in ball y s, G z := by
    intro s hs hsR
    have hind : ∀ z, G z * (if ‖y - z‖ < s then ENNReal.ofReal (2 * (s ^ 3)⁻¹) else 0)
        = (ball y s).indicator (fun z => ENNReal.ofReal (2 * (s ^ 3)⁻¹) * G z) z := by
      intro z
      by_cases h : ‖y - z‖ < s
      · have h' : z ∈ ball y s := by
          rw [mem_ball, dist_eq_norm, norm_sub_rev]
          exact h
        rw [if_pos h, Set.indicator_of_mem h']
        ring
      · have h' : z ∉ ball y s := by
          rw [mem_ball, dist_eq_norm, norm_sub_rev]
          exact h
        rw [if_neg h, Set.indicator_of_notMem h']
        ring
    simp only [hind]
    rw [lintegral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
      inter_eq_left.mpr (ball_subset_ball hsR.le)]
    exact lintegral_const_mul _ hG
  -- key constant identities
  have hkey : ENNReal.ofReal ((4 * Real.pi)⁻¹) * (3 * ENNReal.ofReal (Real.pi * 4 / 3)) = 1 := by
    have h3 : (3 : ENNReal) = ENNReal.ofReal 3 := (ENNReal.ofReal_ofNat 3).symm
    rw [h3, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (4 * Real.pi)⁻¹)]
    rw [show (4 * Real.pi)⁻¹ * (3 * (Real.pi * 4 / 3)) = 1 by
      field_simp]
    exact ENNReal.ofReal_one
  have hR3 : ENNReal.ofReal R ^ 3 * ENNReal.ofReal ((R ^ 2)⁻¹) = ENNReal.ofReal R := by
    rw [← ENNReal.ofReal_pow hR.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  -- assemble
  rw [lintegral_congr_ae hae, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_add_left (hG.mul_const _), lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
    lintegral_lintegral_swap (f := fun z s =>
      G z * (if ‖y - z‖ < s then ENNReal.ofReal (2 * (s ^ 3)⁻¹) else 0)) hmeasF.aemeasurable]
  have hI2 : ∫⁻ s in Ioo 0 R, ∫⁻ z in ball y R,
      G z * (if ‖y - z‖ < s then ENNReal.ofReal (2 * (s ^ 3)⁻¹) else 0)
      ≤ ∫⁻ s in Ioo 0 R, ENNReal.ofReal 2 * ENNReal.ofReal (Real.pi * 4 / 3) * hlMax G y := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [hslice s hs.1 hs.2]
    have hs0 : s ≠ 0 := hs.1.ne'
    have hsv : ENNReal.ofReal (2 * (s ^ 3)⁻¹) * volume (ball y s)
        = ENNReal.ofReal 2 * ENNReal.ofReal (Real.pi * 4 / 3) := by
      rw [hvol s, ← ENNReal.ofReal_pow hs.1.le]
      calc ENNReal.ofReal (2 * (s ^ 3)⁻¹) * (ENNReal.ofReal (s ^ 3) * ENNReal.ofReal (Real.pi * 4 / 3))
          = (ENNReal.ofReal (2 * (s ^ 3)⁻¹) * ENNReal.ofReal (s ^ 3)) *
              ENNReal.ofReal (Real.pi * 4 / 3) := by ring
        _ = ENNReal.ofReal 2 * ENNReal.ofReal (Real.pi * 4 / 3) := by
          rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (inv_nonneg.mpr (pow_nonneg hs.1.le 3))),
            show 2 * (s ^ 3)⁻¹ * s ^ 3 = 2 by field_simp]
    calc ENNReal.ofReal (2 * (s ^ 3)⁻¹) * ∫⁻ z in ball y s, G z
        ≤ ENNReal.ofReal (2 * (s ^ 3)⁻¹) * (volume (ball y s) * hlMax G y) :=
          mul_le_mul_of_nonneg_left (hball s hs.1) (by positivity)
      _ = (ENNReal.ofReal (2 * (s ^ 3)⁻¹) * volume (ball y s)) * hlMax G y := by ring
      _ = _ := by rw [hsv]
  have hconst : ∫⁻ s in Ioo 0 R, ENNReal.ofReal 2 * ENNReal.ofReal (Real.pi * 4 / 3) * hlMax G y
      = ENNReal.ofReal R * (ENNReal.ofReal 2 * ENNReal.ofReal (Real.pi * 4 / 3) * hlMax G y) := by
    rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
    ring
  have hfin : ENNReal.ofReal ((4 * Real.pi)⁻¹) *
      ((∫⁻ z in ball y R, G z) * ENNReal.ofReal ((R ^ 2)⁻¹) +
        ∫⁻ s in Ioo 0 R, ∫⁻ z in ball y R,
          G z * (if ‖y - z‖ < s then ENNReal.ofReal (2 * (s ^ 3)⁻¹) else 0))
      ≤ ENNReal.ofReal ((4 * Real.pi)⁻¹) *
        ((volume (ball y R) * hlMax G y) * ENNReal.ofReal ((R ^ 2)⁻¹) +
          ENNReal.ofReal R * (ENNReal.ofReal 2 * ENNReal.ofReal (Real.pi * 4 / 3) * hlMax G y)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine add_le_add ?_ ?_
    · exact mul_le_mul_of_nonneg_right (hball R hR) (by positivity)
    · exact hI2.trans hconst.le
  refine le_trans hfin (le_of_eq ?_)
  rw [hvol R, ENNReal.ofReal_ofNat]
  calc ENNReal.ofReal ((4 * Real.pi)⁻¹) *
        ((ENNReal.ofReal R ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) * hlMax G y) *
          ENNReal.ofReal ((R ^ 2)⁻¹) +
          ENNReal.ofReal R * (2 * ENNReal.ofReal (Real.pi * 4 / 3) * hlMax G y))
      = ENNReal.ofReal ((4 * Real.pi)⁻¹) *
          ((ENNReal.ofReal R ^ 3 * ENNReal.ofReal ((R ^ 2)⁻¹)) *
            (ENNReal.ofReal (Real.pi * 4 / 3) * hlMax G y) +
           ENNReal.ofReal R * (2 * ENNReal.ofReal (Real.pi * 4 / 3) * hlMax G y)) := by ring
    _ = ENNReal.ofReal ((4 * Real.pi)⁻¹) *
          (ENNReal.ofReal R * (ENNReal.ofReal (Real.pi * 4 / 3) * hlMax G y) +
           ENNReal.ofReal R * (2 * ENNReal.ofReal (Real.pi * 4 / 3) * hlMax G y)) := by
        rw [hR3]
    _ = ENNReal.ofReal R * hlMax G y *
          (ENNReal.ofReal ((4 * Real.pi)⁻¹) * (3 * ENNReal.ofReal (Real.pi * 4 / 3))) := by ring
    _ = ENNReal.ofReal R * hlMax G y := by rw [hkey, mul_one]

end UnforcedLeray.Short.PartIIIb.Concrete
