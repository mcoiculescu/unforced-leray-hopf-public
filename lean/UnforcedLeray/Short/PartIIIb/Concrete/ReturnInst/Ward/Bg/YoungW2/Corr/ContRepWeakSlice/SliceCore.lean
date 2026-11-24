import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.ContRepWeakSlice.PeriodicFL
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.ContRepWeakSlice.ProdTest
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.ContRepWeakSlice.RePair

/-!
# Core of `bgContRepWeakSlice` (helper): periodic fundamental lemma applied to the slice integral
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem integrable_testMul (ψ : Space → ℝ) (hψs : HasCompactSupport ψ) (hψc : Continuous ψ)
    (f : Space → ℝ) (hf : Continuous f) : Integrable (fun y => ψ y * f y) :=
  (hψc.mul hf).integrable_of_hasCompactSupport (hψs.mul_right (f' := f))

theorem continuous_testMul (ψ : Space → ℝ) (hψs : HasCompactSupport ψ) (hψc : Continuous ψ)
    (F : ℝ → Space → Space) (hF : Continuous (fun x : ℝ × Space => F x.1 x.2)) (k : Fin 3) :
    Continuous (fun t => ∫ y, ψ y * F t y k) := by
  have hk : Continuous (fun x : ℝ × Space => F x.1 x.2 k) :=
    (EuclideanSpace.proj k).continuous.comp hF
  have hcont : Continuous (Function.uncurry fun (t : ℝ) (y : Space) => ψ y * F t y k) :=
    (hψc.comp continuous_snd).mul hk
  have := continuous_parametric_integral_of_continuous (μ := (volume : Measure Space)) hcont
    hψs.isCompact
  refine this.congr fun t => ?_
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
  have : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
  simp [this]

theorem trig_test (P : ℝ) (hP : P ≠ 0) (m : ℤ) :
    (ContDiff ℝ ∞ (fun t : ℝ => Real.cos (2 * π * m * t / P)) ∧
      ∀ t, Real.cos (2 * π * m * (t + P) / P) = Real.cos (2 * π * m * t / P)) ∧
    (ContDiff ℝ ∞ (fun t : ℝ => Real.sin (2 * π * m * t / P)) ∧
      ∀ t, Real.sin (2 * π * m * (t + P) / P) = Real.sin (2 * π * m * t / P)) := by
  have key : ∀ t, 2 * π * m * (t + P) / P = 2 * π * m * t / P + m * (2 * π) := by
    intro t
    field_simp
  refine ⟨⟨?_, fun t => ?_⟩, ⟨?_, fun t => ?_⟩⟩
  · exact Real.contDiff_cos.comp ((contDiff_const.mul contDiff_id).div_const _)
  · rw [key, Real.cos_add_int_mul_two_pi]
  · exact Real.contDiff_sin.comp ((contDiff_const.mul contDiff_id).div_const _)
  · rw [key, Real.sin_add_int_mul_two_pi]

/-- The slice integral vanishes at every phase. -/
theorem slice_core {P : ℝ} (hP : 0 < P) (F G : ℝ → Space → Space)
    (hFc : Continuous (fun x : ℝ × Space => F x.1 x.2))
    (hGc : Continuous (fun x : ℝ × Space => G x.1 x.2))
    (hFp : ∀ t, F (t + P) = F t) (hGp : ∀ t, G (t + P) = G t)
    (j : Fin 3) (φ : Space → ℝ) (hφ : UnforcedLeray.IsSpatialTest φ) (k : Fin 3)
    (hid : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → (∀ t, χ (t + P) = χ t) →
      ∫ t in Ioc (0 : ℝ) P, ∫ y, χ t * (-(UnforcedLeray.spatialTestDerivative j φ y)) * F t y k =
        ∫ t in Ioc (0 : ℝ) P, ∫ y, χ t * φ y * G t y k) :
    ∀ t, ∫ y, (UnforcedLeray.spatialTestDerivative j φ y * F t y k + φ y * G t y k) = 0 := by
  have hdφ := isSpatialTest_derivative hφ j
  set a : ℝ → ℝ := fun t => ∫ y, UnforcedLeray.spatialTestDerivative j φ y * F t y k with ha
  set b : ℝ → ℝ := fun t => ∫ y, φ y * G t y k with hb
  have hac : Continuous a :=
    continuous_testMul _ hdφ.compact hdφ.smooth.continuous F hFc k
  have hbc : Continuous b := continuous_testMul _ hφ.compact hφ.smooth.continuous G hGc k
  have hsl : ∀ t, ∫ y, (UnforcedLeray.spatialTestDerivative j φ y * F t y k + φ y * G t y k) =
      a t + b t := by
    intro t
    have hFk : Continuous (fun y => F t y k) :=
      (EuclideanSpace.proj k).continuous.comp (hFc.comp (Continuous.prodMk_right t))
    have hGk : Continuous (fun y => G t y k) :=
      (EuclideanSpace.proj k).continuous.comp (hGc.comp (Continuous.prodMk_right t))
    exact integral_add (integrable_testMul _ hdφ.compact hdφ.smooth.continuous _ hFk)
      (integrable_testMul _ hφ.compact hφ.smooth.continuous _ hGk)
  simp_rw [hsl]
  have hHc : Continuous (fun t => a t + b t) := hac.add hbc
  have hHp : ∀ t, a (t + P) + b (t + P) = a t + b t := by
    intro t; simp only [ha, hb, hFp t, hGp t]
  have horth : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → (∀ t, χ (t + P) = χ t) →
      ∫ t in Ioc (0 : ℝ) P, χ t * (a t + b t) = 0 := by
    intro χ hχ hχp
    have h := hid χ hχ hχp
    have e1 : ∀ t, ∫ y, χ t * (-(UnforcedLeray.spatialTestDerivative j φ y)) * F t y k =
        -(χ t * a t) := by
      intro t
      calc ∫ y, χ t * (-(UnforcedLeray.spatialTestDerivative j φ y)) * F t y k
          = ∫ y, -(χ t * (UnforcedLeray.spatialTestDerivative j φ y * F t y k)) := by
            congr 1; ext y; ring
        _ = -(χ t * a t) := by rw [integral_neg, integral_const_mul]
    have e2 : ∀ t, ∫ y, χ t * φ y * G t y k = χ t * b t := by
      intro t
      calc ∫ y, χ t * φ y * G t y k = ∫ y, χ t * (φ y * G t y k) := by
            congr 1; ext y; ring
        _ = χ t * b t := by rw [integral_const_mul]
    simp_rw [e1, e2] at h
    rw [integral_neg] at h
    have hχc : Continuous χ := hχ.continuous
    have i1 : IntegrableOn (fun t => χ t * a t) (Ioc 0 P) :=
      (hχc.mul hac).integrableOn_Ioc
    have i2 : IntegrableOn (fun t => χ t * b t) (Ioc 0 P) :=
      (hχc.mul hbc).integrableOn_Ioc
    simp_rw [mul_add]
    rw [integral_add i1 i2]
    linarith
  intro t
  refine periodic_eq_zero_of_trig hP hHc hHp (fun m => ?_) (fun m => ?_) t
  · obtain ⟨⟨h1, h2⟩, -⟩ := trig_test P hP.ne' m
    exact horth _ h1 h2
  · obtain ⟨-, ⟨h1, h2⟩⟩ := trig_test P hP.ne' m
    exact horth _ h1 h2

end UnforcedLeray.Short.PartIIIb.Concrete
