import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_12_3

/-!
# `PartIII-b:IIIb-D2/3/2/12/3/2` : comparison of the gain-weighted stress measures

Source of record: `the November 2 reference manuscript`,
lines 2683, 2698-2700, 4284-4286.  Target: `StrMeasureCmp` (props file
`Sub/PartIII-b_IIIb-D2_3_2_12_3.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `W² = (1 + (η/√(1+s))²)^{m_Z}`. -/
theorem transWeight_sq_eq' (mZ : ℝ) (p : ℝ × (ℝ × ℝ)) :
    UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2 =
      (1 + (p.2.2 / Real.sqrt (1 + p.1)) ^ 2) ^ mZ := by
  unfold UnforcedLeray.Short.IIIa.transWeight
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  ring

theorem transWeight_pos' (mZ : ℝ) (p : ℝ × (ℝ × ℝ)) :
    0 < UnforcedLeray.Short.IIIa.transWeight mZ p := by
  unfold UnforcedLeray.Short.IIIa.transWeight
  exact Real.rpow_pos_of_pos (by positivity) _

theorem measurable_transWeight' (mZ : ℝ) :
    Measurable fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.Short.IIIa.transWeight mZ p := by
  unfold UnforcedLeray.Short.IIIa.transWeight
  fun_prop

/-- On the region `|η| ≤ Y √(1+s)` with `s > 0`, the weight `W²` is bounded below by
`min 1 ((1+Y²)^{m_Z})`. -/
theorem transWeight_sq_lower (mZ Y : ℝ) (p : ℝ × (ℝ × ℝ)) (hp : 0 < p.1)
    (hY : |p.2.2| ≤ Y * Real.sqrt (1 + p.1)) :
    min 1 ((1 + Y ^ 2) ^ mZ) ≤ UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2 := by
  rw [transWeight_sq_eq']
  have hs0 : (0 : ℝ) ≤ 1 + p.1 := by linarith
  have hx2 : (p.2.2 / Real.sqrt (1 + p.1)) ^ 2 ≤ Y ^ 2 := by
    rw [div_pow, Real.sq_sqrt hs0]
    have h1 : |p.2.2| ^ 2 ≤ (Y * Real.sqrt (1 + p.1)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hY 2
    rw [sq_abs, mul_pow, Real.sq_sqrt hs0] at h1
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hsq0 : 0 ≤ (p.2.2 / Real.sqrt (1 + p.1)) ^ 2 := sq_nonneg _
  have ht1 : (1 : ℝ) ≤ 1 + (p.2.2 / Real.sqrt (1 + p.1)) ^ 2 := by linarith
  have ht2 : 1 + (p.2.2 / Real.sqrt (1 + p.1)) ^ 2 ≤ 1 + Y ^ 2 := by linarith
  rcases le_total 0 mZ with hm | hm
  · have h := Real.one_le_rpow ht1 hm
    exact (min_le_left _ _).trans h
  · have h := Real.rpow_le_rpow_of_nonpos (by linarith) ht2 hm
    exact (min_le_right _ _).trans h

/-- The gain-weighted `Z₁` density is measurable. -/
theorem measurable_W2' (mZ : ℝ) :
    Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) :=
  (measurable_transWeight' mZ).pow_const 2 |>.ennreal_ofReal

theorem measurable_G2' (γ ν : ℝ) :
    Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (ginv γ ν p ^ 2) :=
  ((NearInst.ginv_measurable' γ ν).pow_const 2).ennreal_ofReal

/-- Lower bound `g⁻¹ ≥ e^{-|γ|/ν}`. -/
theorem ginv_ge_exp (γ ν : ℝ) (hν : 0 < ν) (p : ℝ × (ℝ × ℝ)) :
    Real.exp (-(|γ| / ν)) ≤ ginv γ ν p :=
  ginv_lower_B hν p

/-- The `Z₁` gain measure: density `W² g⁻²` against `ageμ c (-1/2)`. -/
theorem gainZ1_apply' (c mZ γ ν : ℝ) {A : Set (ℝ × (ℝ × ℝ))} (hA : MeasurableSet A) :
    gainZ1Measure c mZ γ ν A =
      ∫⁻ p in A, ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) *
        ENNReal.ofReal (ginv γ ν p ^ 2) ∂ageμ c (-1 / 2) := by
  unfold gainZ1Measure z1Measure
  rw [withDensity_apply _ hA, setLIntegral_withDensity_eq_setLIntegral_mul _
    (measurable_W2' mZ) (measurable_G2' γ ν) hA]
  rfl

/-- The `H_T` gain measure: density `g⁻²` against `ρ_b⁻¹ ageμ c (-1/2)`. -/
theorem gainHT_apply' (c ρb γ ν : ℝ) {A : Set (ℝ × (ℝ × ℝ))} (hA : MeasurableSet A) :
    gainHTMeasure c ρb γ ν A =
      ENNReal.ofReal ρb⁻¹ * ∫⁻ p in A, ENNReal.ofReal (ginv γ ν p ^ 2) ∂ageμ c (-1 / 2) := by
  unfold gainHTMeasure htRhoMeasure
  rw [withDensity_apply _ hA, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]

/-- The age measure lives on `s > 0` (a.e.). -/
theorem ageμ_pos_ae' (c a : ℝ) : ∀ᵐ p ∂(ageμ c a), 0 < p.1 := by
  have h0 : ageμ c a {p : ℝ × (ℝ × ℝ) | p.1 ≤ 0} = 0 := by
    have hset : {p : ℝ × (ℝ × ℝ) | p.1 ≤ 0} = Iic (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by
      ext p
      simp
    have : SFinite (UnforcedLeray.Cyl.avgμ c) := by
      unfold UnforcedLeray.Cyl.avgμ
      infer_instance
    rw [ageμ, hset, Measure.prod_prod]
    have hI : ((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ a))
        (Iic 0) = 0 := by
      rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
        Set.Iic_inter_Ioi, Set.Ioc_self, Measure.restrict_empty, lintegral_zero_measure]
    rw [hI, zero_mul]
  rw [ae_iff]
  simpa [not_lt] using h0

/-- **`PartIII-b:IIIb-D2/3/2/12/3/2`**: the comparison `StrMeasureCmp`. -/
theorem strMeasureCmp_proved : UnforcedLeray.Short.PartIIIb.Concrete.StrMeasureCmp := by
  intro c mZ ρb γ ν hν hρ Y
  have he0 : 0 < Real.exp (-(|γ| / ν)) := Real.exp_pos _
  have hSm : MeasurableSet (StrRegion Y) := by
    unfold StrRegion
    exact measurableSet_le (by fun_prop) (by fun_prop)
  have hδW : 0 < min 1 ((1 + Y ^ 2) ^ mZ) :=
    lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  have hδ1pos : ENNReal.ofReal (min 1 ((1 + Y ^ 2) ^ mZ) * Real.exp (-(|γ| / ν)) ^ 2) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (mul_pos hδW (pow_pos he0 2))).ne'
  have hδ1top : ENNReal.ofReal (min 1 ((1 + Y ^ 2) ^ mZ) * Real.exp (-(|γ| / ν)) ^ 2) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have hδHpos : ENNReal.ofReal ρb⁻¹ * ENNReal.ofReal (Real.exp (-(|γ| / ν)) ^ 2) ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.2 (inv_pos.2 hρ)).ne' (ENNReal.ofReal_pos.2 (pow_pos he0 2)).ne'
  have hδHtop : ENNReal.ofReal ρb⁻¹ * ENNReal.ofReal (Real.exp (-(|γ| / ν)) ^ 2) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hK1 : (ENNReal.ofReal (min 1 ((1 + Y ^ 2) ^ mZ) * Real.exp (-(|γ| / ν)) ^ 2))⁻¹ ≤
      (ENNReal.ofReal (min 1 ((1 + Y ^ 2) ^ mZ) * Real.exp (-(|γ| / ν)) ^ 2))⁻¹ +
        (ENNReal.ofReal ρb⁻¹ * ENNReal.ofReal (Real.exp (-(|γ| / ν)) ^ 2))⁻¹ := le_self_add
  have hK2 : (ENNReal.ofReal ρb⁻¹ * ENNReal.ofReal (Real.exp (-(|γ| / ν)) ^ 2))⁻¹ ≤
      (ENNReal.ofReal (min 1 ((1 + Y ^ 2) ^ mZ) * Real.exp (-(|γ| / ν)) ^ 2))⁻¹ +
        (ENNReal.ofReal ρb⁻¹ * ENNReal.ofReal (Real.exp (-(|γ| / ν)) ^ 2))⁻¹ := le_add_self
  have hKtop : (ENNReal.ofReal (min 1 ((1 + Y ^ 2) ^ mZ) * Real.exp (-(|γ| / ν)) ^ 2))⁻¹ +
      (ENNReal.ofReal ρb⁻¹ * ENNReal.ofReal (Real.exp (-(|γ| / ν)) ^ 2))⁻¹ ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.inv_ne_top.2 hδ1pos, ENNReal.inv_ne_top.2 hδHpos⟩
  have hK0 : (ENNReal.ofReal (min 1 ((1 + Y ^ 2) ^ mZ) * Real.exp (-(|γ| / ν)) ^ 2))⁻¹ +
      (ENNReal.ofReal ρb⁻¹ * ENNReal.ofReal (Real.exp (-(|γ| / ν)) ^ 2))⁻¹ ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (ENNReal.inv_pos.2 hδ1top) hK1)
  refine ⟨_, hKtop, hK0, ?_, ?_, ?_⟩
  · -- first comparison, on the region
    rw [Measure.le_iff]
    intro A hA
    simp only [Measure.restrict_apply hA, Measure.smul_apply, smul_eq_mul]
    have hB : MeasurableSet (A ∩ StrRegion Y) := hA.inter hSm
    have hlow : ENNReal.ofReal (min 1 ((1 + Y ^ 2) ^ mZ) * Real.exp (-(|γ| / ν)) ^ 2) *
        ageμ c (-1 / 2) (A ∩ StrRegion Y) ≤
        ∫⁻ p in A ∩ StrRegion Y, ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) *
          ENNReal.ofReal (ginv γ ν p ^ 2) ∂ageμ c (-1 / 2) := by
      rw [← setLIntegral_const]
      apply setLIntegral_mono_ae' hB
      filter_upwards [ageμ_pos_ae' c (-1 / 2)] with p hp hpB
      have hY : |p.2.2| ≤ Y * Real.sqrt (1 + p.1) := hpB.2
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have h1 := transWeight_sq_lower mZ Y p hp hY
      have h2 : Real.exp (-(|γ| / ν)) ≤ ginv γ ν p := ginv_ge_exp γ ν hν p
      have h3 : Real.exp (-(|γ| / ν)) ^ 2 ≤ ginv γ ν p ^ 2 :=
        pow_le_pow_left₀ he0.le h2 2
      exact mul_le_mul h1 h3 (sq_nonneg _) (le_trans (le_min zero_le_one
        (Real.rpow_nonneg (by positivity) _)) h1)
    have hlow' : ENNReal.ofReal (min 1 ((1 + Y ^ 2) ^ mZ) * Real.exp (-(|γ| / ν)) ^ 2) *
        ageμ c (-1 / 2) (A ∩ StrRegion Y) ≤
        gainZ1Measure c mZ γ ν (A ∩ StrRegion Y) := by
      rw [gainZ1_apply' c mZ γ ν hB]
      exact hlow
    calc ageμ c (-1 / 2) (A ∩ StrRegion Y)
        = (ENNReal.ofReal (min 1 ((1 + Y ^ 2) ^ mZ) * Real.exp (-(|γ| / ν)) ^ 2))⁻¹ *
            (ENNReal.ofReal (min 1 ((1 + Y ^ 2) ^ mZ) * Real.exp (-(|γ| / ν)) ^ 2) *
              ageμ c (-1 / 2) (A ∩ StrRegion Y)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hδ1pos hδ1top, one_mul]
      _ ≤ (ENNReal.ofReal (min 1 ((1 + Y ^ 2) ^ mZ) * Real.exp (-(|γ| / ν)) ^ 2))⁻¹ *
            gainZ1Measure c mZ γ ν (A ∩ StrRegion Y) := mul_le_mul_of_nonneg_left hlow' zero_le
      _ ≤ _ := mul_le_mul_of_nonneg_right hK1 zero_le
  · -- second comparison, body measure
    rw [Measure.le_iff]
    intro A hA
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [gainHT_apply' c ρb γ ν hA]
    have hlow : ENNReal.ofReal (Real.exp (-(|γ| / ν)) ^ 2) * ageμ c (-1 / 2) A ≤
        ∫⁻ p in A, ENNReal.ofReal (ginv γ ν p ^ 2) ∂ageμ c (-1 / 2) := by
      have := setLIntegral_mono' (μ := ageμ c (-1 / 2)) hA
        (f := fun _ => ENNReal.ofReal (Real.exp (-(|γ| / ν)) ^ 2))
        (g := fun p => ENNReal.ofReal (ginv γ ν p ^ 2))
        (fun p _ => ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ he0.le (ginv_ge_exp γ ν hν p) 2))
      rwa [setLIntegral_const] at this
    have hH : (ENNReal.ofReal ρb⁻¹ * ENNReal.ofReal (Real.exp (-(|γ| / ν)) ^ 2)) *
        ageμ c (-1 / 2) A ≤
        ENNReal.ofReal ρb⁻¹ * ∫⁻ p in A, ENNReal.ofReal (ginv γ ν p ^ 2) ∂ageμ c (-1 / 2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hlow zero_le
    calc ageμ c (-1 / 2) A
        = (ENNReal.ofReal ρb⁻¹ * ENNReal.ofReal (Real.exp (-(|γ| / ν)) ^ 2))⁻¹ *
            ((ENNReal.ofReal ρb⁻¹ * ENNReal.ofReal (Real.exp (-(|γ| / ν)) ^ 2)) *
              ageμ c (-1 / 2) A) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hδHpos hδHtop, one_mul]
      _ ≤ (ENNReal.ofReal ρb⁻¹ * ENNReal.ofReal (Real.exp (-(|γ| / ν)) ^ 2))⁻¹ *
            (ENNReal.ofReal ρb⁻¹ * ∫⁻ p in A, ENNReal.ofReal (ginv γ ν p ^ 2)
              ∂ageμ c (-1 / 2)) := mul_le_mul_of_nonneg_left hH zero_le
      _ ≤ _ := mul_le_mul_of_nonneg_right hK2 zero_le
  · -- absolute continuity
    have h1 : ageμ c (-1 / 2) ≪ z1Measure c mZ := by
      unfold z1Measure
      exact withDensity_absolutelyContinuous' (measurable_W2' mZ).aemeasurable
        (ae_of_all _ fun p => (ENNReal.ofReal_pos.2 (pow_pos (transWeight_pos' mZ p) 2)).ne')
    have h2 : z1Measure c mZ ≪ gainZ1Measure c mZ γ ν := by
      unfold gainZ1Measure
      exact withDensity_absolutelyContinuous' (measurable_G2' γ ν).aemeasurable
        (ae_of_all _ fun p => (ENNReal.ofReal_pos.2
          (pow_pos (lt_of_lt_of_le he0 (ginv_ge_exp γ ν hν p)) 2)).ne')
    exact h1.trans h2

end UnforcedLeray.Short.PartIIIb.Concrete
