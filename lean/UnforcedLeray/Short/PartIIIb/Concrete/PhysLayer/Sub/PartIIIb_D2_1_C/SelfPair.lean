import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_1_3
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Group.Prod

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

theorem dotL_cjF_self (w : ℝ × Space → CVec3) (x : ℝ × Space) :
    dotL (cjF w x) (w x) = (((‖w x‖ ^ 2 : ℝ)) : ℂ) := by
  rw [dotL_apply, EuclideanSpace.norm_sq_eq]
  simp [cjF, Complex.conj_mul']

theorem pairF_cjF_self (P : ℝ) (w : ℝ × Space → CVec3) :
    pairF P (cjF w) w =
      (((P⁻¹ * ∫ t in Ioc (0 : ℝ) P, ∫ y, ‖w (t, y)‖ ^ 2 : ℝ)) : ℂ) := by
  unfold pairF phaseInt
  simp only [dotL_cjF_self]
  have key : ∀ t : ℝ, ∫ y, (((‖w (t, y)‖ ^ 2 : ℝ)) : ℂ)
      = (((∫ y, ‖w (t, y)‖ ^ 2 : ℝ)) : ℂ) := fun t => integral_complex_ofReal
  simp only [key]
  rw [integral_complex_ofReal, Complex.real_smul]
  push_cast
  ring

theorem htrans_shift (c : ℝ) :
    MeasurePreserving (fun z : ℝ × Space => (z.1 + c, z.2))
      (volume : Measure (ℝ × Space)) (volume : Measure (ℝ × Space)) := by
  rw [Measure.volume_eq_prod]
  exact (measurePreserving_add_right (volume : Measure ℝ) c).prod
    (MeasurePreserving.id (volume : Measure Space))

theorem fwuSelfPair : FWUSelfPair := by
  intro P hP w hw h0
  have hP0 : (P⁻¹ : ℝ) ≠ 0 := inv_ne_zero hP.ne'
  rw [pairF_cjF_self] at h0
  have hI : ∫ t in Ioc (0 : ℝ) P, ∫ y, ‖w (t, y)‖ ^ 2 = 0 := by
    have h1 := Complex.ofReal_eq_zero.mp h0
    exact (mul_eq_zero.mp h1).resolve_left hP0
  have hJ : ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y, ‖w (t, y)‖ₑ ^ (2 : ℝ) < ⊤ := by
    have h := hw.finite
    unfold UnforcedLeray.Short.IIb.phaseLpNorm at h
    have hc : ENNReal.ofReal P⁻¹ ≠ 0 := by
      simp [hP]
    by_contra hJt
    have hJeq := top_unique (not_lt.mp hJt)
    rw [hJeq, ENNReal.mul_top hc, ENNReal.top_rpow_of_pos (by norm_num)] at h
    exact lt_irrefl _ h
  have hac : ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)
      ≪ (volume : Measure (ℝ × Space)) := by
    rw [Measure.volume_eq_prod]
    exact Measure.AbsolutelyContinuous.prod Measure.restrict_le_self.absolutelyContinuous
      (le_refl (volume : Measure Space)).absolutelyContinuous
  have hFm : AEStronglyMeasurable (fun z : ℝ × Space => ‖w z‖ ^ 2)
      (((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)) :=
    ((hw.meas.mono_ac hac).norm).pow 2
  have hlint : ∫⁻ z, ‖‖w z‖ ^ 2‖ₑ ∂(((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod
      (volume : Measure Space)) < ⊤ := by
    rw [lintegral_prod _ (AEStronglyMeasurable.enorm hFm)]
    have hfun : ∀ x : ℝ, ∫⁻ y, ‖‖w (x, y)‖ ^ 2‖ₑ ∂(volume : Measure Space)
        = ∫⁻ y, ‖w (x, y)‖ₑ ^ (2 : ℝ) ∂(volume : Measure Space) := by
      intro x
      congr 1
      funext y
      rw [ENNReal.rpow_two, Real.enorm_eq_ofReal (by positivity), ← ofReal_norm_eq_enorm,
        ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [hfun]
    exact hJ
  have hint : Integrable (fun z : ℝ × Space => ‖w z‖ ^ 2)
      (((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)) :=
    ⟨hFm, hlint⟩
  have hintI : ∫ z, ‖w z‖ ^ 2 ∂(((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod
      (volume : Measure Space)) = 0 := by
    rw [integral_prod _ hint]
    exact hI
  have hae : (fun z : ℝ × Space => ‖w z‖ ^ 2) =ᵐ[((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod
      (volume : Measure Space)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg _) hint).mp hintI
  have hprodeq : ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)
      = (volume : Measure (ℝ × Space)).restrict (Ioc (0 : ℝ) P ×ˢ univ) := by
    have hu : (volume : Measure Space) = (volume : Measure Space).restrict univ :=
      Measure.restrict_univ.symm
    conv_lhs => rw [hu]
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hbase : ∀ᵐ z ∂(volume : Measure (ℝ × Space)), z.1 ∈ Ioc (0 : ℝ) P → w z = 0 := by
    have h1 : ∀ᵐ z ∂((volume : Measure (ℝ × Space)).restrict (Ioc (0 : ℝ) P ×ˢ univ)),
        ‖w z‖ ^ 2 = 0 := by
      rw [← hprodeq]
      exact hae
    rw [ae_restrict_iff' (measurableSet_Ioc.prod MeasurableSet.univ)] at h1
    filter_upwards [h1] with z hz hzI
    have h2 : ‖w z‖ ^ 2 = 0 := hz ⟨hzI, mem_univ _⟩
    simpa using h2
  have hshift : ∀ c : ℝ, ∀ᵐ z ∂(volume : Measure (ℝ × Space)),
      w (z.1 + c + P, z.2) = w (z.1 + c, z.2) := by
    intro c
    exact (htrans_shift c).quasiMeasurePreserving.ae hw.periodic
  have hper : ∀ n : ℤ, ∀ᵐ z ∂(volume : Measure (ℝ × Space)),
      w (z.1 + (n : ℝ) * P, z.2) = w z := by
    intro n
    induction n using Int.induction_on with
    | zero => exact Filter.Eventually.of_forall fun z => by simp
    | succ i ih =>
      filter_upwards [ih, hshift ((i : ℝ) * P)] with z h1 h2
      have e : z.1 + ((i + 1 : ℤ) : ℝ) * P = z.1 + (i : ℝ) * P + P := by push_cast; ring
      have e0 : z.1 + ((i : ℤ) : ℝ) * P = z.1 + (i : ℝ) * P := by push_cast; ring
      rw [e, h2, ← e0]
      exact h1
    | pred i ih =>
      filter_upwards [ih, hshift ((-(i : ℝ) - 1) * P)] with z h1 h2
      have e1 : z.1 + (-(i : ℝ) - 1) * P + P = z.1 + ((-(i : ℤ) : ℤ) : ℝ) * P := by
        push_cast; ring
      have e2 : z.1 + ((-(i : ℤ) - 1 : ℤ) : ℝ) * P = z.1 + (-(i : ℝ) - 1) * P := by
        push_cast; ring
      rw [e2, ← h2, e1]
      exact h1
  have hall : ∀ j : ℤ, ∀ᵐ z ∂(volume : Measure (ℝ × Space)),
      z.1 ∈ Ioc ((j : ℝ) * P) (((j : ℝ) + 1) * P) → w z = 0 := by
    intro j
    have h1 := (htrans_shift (-((j : ℝ) * P))).quasiMeasurePreserving.ae hbase
    filter_upwards [h1, hper (-j)] with z h1z h2z hz
    have e : z.1 + ((-j : ℤ) : ℝ) * P = z.1 + -((j : ℝ) * P) := by push_cast; ring
    rw [e] at h2z
    rw [← h2z]
    apply h1z
    rw [Set.mem_Ioc] at hz
    have hz2 : z.1 ≤ (j : ℝ) * P + P := by
      linarith [hz.2, show ((j : ℝ) + 1) * P = (j : ℝ) * P + P by ring]
    exact ⟨by linarith [hz.1], by linarith⟩
  have hcover : ∀ᵐ z ∂(volume : Measure (ℝ × Space)), ∀ j : ℤ,
      z.1 ∈ Ioc ((j : ℝ) * P) (((j : ℝ) + 1) * P) → w z = 0 :=
    ae_all_iff.2 hall
  have hfinal : w =ᵐ[(volume : Measure (ℝ × Space))] 0 := by
    filter_upwards [hcover] with z hz
    show w z = 0
    apply hz (⌈z.1 / P⌉ - 1)
    rw [Set.mem_Ioc]
    have ha : z.1 / P * P = z.1 := div_mul_cancel₀ _ hP.ne'
    have h1 : z.1 / P ≤ (⌈z.1 / P⌉ : ℝ) := Int.le_ceil _
    have h2 : (⌈z.1 / P⌉ : ℝ) < z.1 / P + 1 := Int.ceil_lt_add_one _
    have k1 : ((⌈z.1 / P⌉ : ℝ) - 1) * P < z.1 / P * P :=
      mul_lt_mul_of_pos_right (by linarith) hP
    have k2 : z.1 / P * P ≤ (⌈z.1 / P⌉ : ℝ) * P := mul_le_mul_of_nonneg_right h1 hP.le
    push_cast
    constructor
    · linarith
    · rw [show ((⌈z.1 / P⌉ : ℝ) - 1 + 1) * P = (⌈z.1 / P⌉ : ℝ) * P by ring]
      linarith
  exact hfinal

end UnforcedLeray.Short.PartIIIb.Concrete
