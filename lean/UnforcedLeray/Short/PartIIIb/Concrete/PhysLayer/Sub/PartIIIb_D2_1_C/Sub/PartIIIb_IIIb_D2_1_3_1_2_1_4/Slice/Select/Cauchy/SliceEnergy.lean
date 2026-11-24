import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_2_props
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.H1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Cauchy.Integ

/-!
# `cSliceEnergy`: one-slice energy bound (source 1351-1362, 1470-1480)

Apply `sliceH1` to `f` and `ν⁻¹ h`, identify the `L²` derivatives with `g j` by a.e. uniqueness of
weak derivatives (`ae_eq_zero_of_integral_contDiff_smul_eq_zero` applied to the components), and
convert `∫ ‖·‖²` to `∫⁻ ‖·‖ₑ ^ 2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The `L²` norm-squared identity `∫⁻ ‖g‖ₑ^2 = ofReal (∫ ‖g‖^2)` for `g ∈ L²`. -/
theorem lint_sq_eq {g : Space → CVec3} (hg : MemLp g 2 volume) :
    ∫⁻ y : Space, ‖g y‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (∫ y : Space, ‖g y‖ ^ 2) := by
  have hi : Integrable (fun y : Space => ‖g y‖ ^ 2) volume := by
    have := hg.integrable_norm_rpow (two_ne_zero) (by norm_num : (2 : ENNReal) ≠ ⊤)
    simpa [ENNReal.toReal_ofNat, Real.rpow_two] using this
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun y => sq_nonneg ‖g y‖)]
  refine lintegral_congr fun y => ?_
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]

/-- Test vector `φ(z) • e_k`. -/
def testVec (φ : Space → ℝ) (k : Fin 3) : Space → CVec3 :=
  fun z => φ z • (EuclideanSpace.single k (1 : ℂ) : CVec3)

theorem testVec_contDiff {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (k : Fin 3) :
    ContDiff ℝ ∞ (testVec φ k) :=
  hφ.smul contDiff_const

theorem testVec_cs {φ : Space → ℝ} (hφc : HasCompactSupport φ) (k : Fin 3) :
    HasCompactSupport (testVec φ k) :=
  hφc.smul_right

theorem testVec_dot (φ : Space → ℝ) (k : Fin 3) (D : Space → CVec3) (y : Space) :
    ∑ i : Fin 3, D y i * testVec φ k y i = φ y • D y k := by
  simp [testVec, PiLp.smul_apply, EuclideanSpace.single_apply, Complex.real_smul, mul_comm]

/-- Uniqueness of `L²` weak derivatives from the test identity. -/
theorem ae_eq_of_weak {g g' : Space → CVec3} (hg : MemLp g 2 volume) (hg' : MemLp g' 2 volume)
    (h : ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      ∫ y : Space, ∑ i : Fin 3, g y i * θ y i = ∫ y : Space, ∑ i : Fin 3, g' y i * θ y i) :
    g =ᵐ[volume] g' := by
  have hD : ∀ k : Fin 3, ∀ φ : Space → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ y : Space, φ y • ((g - g') y k) = 0 := by
    intro k φ hφ hφc
    have hθ := testVec_contDiff hφ k
    have hθc := testVec_cs hφc k
    have I1 : Integrable (fun y => ∑ i : Fin 3, g y i * testVec φ k y i) volume :=
      integrable_sum_L2 hg (fun i y => testVec φ k y i)
        (fun i => vcomp_cont hθ.continuous i) (fun i => vcomp_cs hθc i)
    have I2 : Integrable (fun y => ∑ i : Fin 3, g' y i * testVec φ k y i) volume :=
      integrable_sum_L2 hg' (fun i y => testVec φ k y i)
        (fun i => vcomp_cont hθ.continuous i) (fun i => vcomp_cs hθc i)
    have hsub : ∫ y : Space, ∑ i : Fin 3, (g - g') y i * testVec φ k y i
        = (∫ y : Space, ∑ i : Fin 3, g y i * testVec φ k y i)
          - ∫ y : Space, ∑ i : Fin 3, g' y i * testVec φ k y i := by
      rw [← integral_sub I1 I2]
      congr 1
      funext y
      simp only [Pi.sub_apply, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
    have hpt : (fun y : Space => φ y • ((g - g') y k))
        = fun y : Space => ∑ i : Fin 3, (g - g') y i * testVec φ k y i := by
      funext y
      rw [testVec_dot]
    rw [hpt, hsub, h _ hθ hθc, sub_self]
  have hae : ∀ k : Fin 3, ∀ᵐ y : Space, (g - g') y k = 0 := by
    intro k
    have hk : MemLp (fun y : Space => (g - g') y k) 2 volume :=
      (hg.sub hg').continuousLinearMap_comp (EuclideanSpace.proj k : CVec3 →L[ℂ] ℂ)
    exact ae_eq_zero_of_integral_contDiff_smul_eq_zero (hk.locallyIntegrable (by norm_num))
      (fun φ hφ hφc => hD k φ hφ hφc)
  have hall : ∀ᵐ y : Space, ∀ k : Fin 3, (g - g') y k = 0 := ae_all_iff.2 hae
  filter_upwards [hall] with y hy
  ext k
  have := hy k
  simp only [Pi.sub_apply, PiLp.sub_apply] at this
  exact sub_eq_zero.1 this

theorem cSliceEnergy : CSliceEnergy := by
  unfold CSliceEnergy
  intro ν hν f h g hf hh hg hid hw
  have hc : (0 : ℝ) ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have hνc : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  -- rescaled source `h' = ν⁻¹ h`
  have hlap : ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ y : Space, ∑ i : Fin 3, f y i * lapS θ y i)
        = ∫ y : Space, ∑ i : Fin 3, (((ν⁻¹ : ℝ) : ℂ) • h y) i * θ y i := by
    intro θ hθ hθc
    have e : (fun y : Space => ∑ i : Fin 3, (((ν⁻¹ : ℝ) : ℂ) • h y) i * θ y i)
        = fun y : Space => ((ν⁻¹ : ℝ) : ℂ) * ∑ i : Fin 3, h y i * θ y i := by
      funext y
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [PiLp.smul_apply, smul_eq_mul]
      ring
    rw [e, integral_const_mul]
    have H := hid θ hθ hθc
    calc (∫ y : Space, ∑ i : Fin 3, f y i * lapS θ y i)
        = ((ν⁻¹ : ℝ) : ℂ) * (((ν : ℝ) : ℂ) * ∫ y : Space, ∑ i : Fin 3, f y i * lapS θ y i) := by
          rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hν.ne', Complex.ofReal_one, one_mul]
      _ = ((ν⁻¹ : ℝ) : ℂ) * ∫ y : Space, ∑ i : Fin 3, h y i * θ y i := by rw [H]
  have hh' : MemLp (fun y : Space => ((ν⁻¹ : ℝ) : ℂ) • h y) 2 volume := hh.const_smul (((ν⁻¹ : ℝ) : ℂ))
  obtain ⟨g', hg'm, hg'w, hg'b⟩ := sliceH1 f (fun y : Space => ((ν⁻¹ : ℝ) : ℂ) • h y) hf hh' hlap
  have hgg : ∀ j : Fin 3, g j =ᵐ[volume] g' j := fun j =>
    ae_eq_of_weak (hg j) (hg'm j) (fun θ hθ hθc => (hw j θ hθ hθc).symm.trans (hg'w j θ hθ hθc))
  -- the squared norms
  have hlint : ∑ j : Fin 3, ∫⁻ y : Space, ‖g j y‖ₑ ^ (2 : ℝ)
      = ENNReal.ofReal (∑ j : Fin 3, ∫ y : Space, ‖g' j y‖ ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => integral_nonneg fun y => sq_nonneg _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : ∫⁻ y : Space, ‖g j y‖ₑ ^ (2 : ℝ) = ∫⁻ y : Space, ‖g' j y‖ₑ ^ (2 : ℝ) :=
      lintegral_congr_ae ((hgg j).mono fun y hy => by simp only [hy])
    rw [e1, lint_sq_eq (hg'm j)]
  have hJ : ∫ y : Space, ‖((ν⁻¹ : ℝ) : ℂ) • h y‖ ^ 2 = (ν⁻¹) ^ 2 * ∫ y : Space, ‖h y‖ ^ 2 := by
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc, mul_pow]
  have hbound := hg'b
  rw [hJ] at hbound
  have hsq : ((ν⁻¹) ^ 2 * ∫ y : Space, ‖h y‖ ^ 2) ^ (1 / 2 : ℝ)
      = ν⁻¹ * (∫ y : Space, ‖h y‖ ^ 2) ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (by positivity) (integral_nonneg fun y => sq_nonneg _),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq hc]
  rw [hsq] at hbound
  rw [lint_sq_eq hf, lint_sq_eq hh]
  calc ∑ j : Fin 3, ∫⁻ y : Space, ‖g j y‖ₑ ^ (2 : ℝ)
      = ENNReal.ofReal (∑ j : Fin 3, ∫ y : Space, ‖g' j y‖ ^ 2) := hlint
    _ ≤ ENNReal.ofReal ((∫ y : Space, ‖f y‖ ^ 2) ^ (1 / 2 : ℝ)
          * (ν⁻¹ * (∫ y : Space, ‖h y‖ ^ 2) ^ (1 / 2 : ℝ))) :=
        ENNReal.ofReal_le_ofReal (le_trans hbound (le_of_eq rfl))
    _ = ENNReal.ofReal ν⁻¹ * (ENNReal.ofReal (∫ y : Space, ‖f y‖ ^ 2)) ^ (1 / 2 : ℝ)
          * (ENNReal.ofReal (∫ y : Space, ‖h y‖ ^ 2)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hc,
          ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun y => sq_nonneg _) (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun y => sq_nonneg _) (by norm_num)]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
