import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7.RotPl
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7.NewtonD3Rot
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7.SigmaMRot
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7.KerContractRot
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_3.Helpers
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_5
import UnforcedLeray.Loc.L09CompactDatum.ParamIntegral

/-!
# `NewtonInnerRot`: rotation covariance of the inner integral (task `PartIII-b:C/srcL/7/5`)

Source of record: `the November 2 reference manuscript`, lines 4776-4782, 4917-4937.
Substitute `x' = rotPl θ a` (measure preserving homeomorphism), then pointwise:
`rotAx θ x - t(rotPl θ a, 0) = rotAx θ (x - t(a,0))`, the kernel is rotation covariant
(`newtonD3Rot`), the Cartesian source is covariant (`sigmaMRot`), and the contraction is covariant
(`kerContractRot`).  Where `|a|² ≥ 5ν/6` both integrands vanish.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rotPl_continuous (θ : ℝ) : Continuous (rotPl θ) := by
  unfold rotPl
  fun_prop

theorem rotPl_neg_rotPl (θ : ℝ) (p : ℝ × ℝ) : rotPl (-θ) (rotPl θ p) = p := by
  obtain ⟨p1, p2⟩ := p
  simp only [rotPl, Real.cos_neg, Real.sin_neg, Prod.mk.injEq]
  constructor
  · linear_combination p1 * Real.sin_sq_add_cos_sq θ
  · linear_combination p2 * Real.sin_sq_add_cos_sq θ

theorem rotPl_rotPl_neg (θ : ℝ) (p : ℝ × ℝ) : rotPl θ (rotPl (-θ) p) = p := by
  obtain ⟨p1, p2⟩ := p
  simp only [rotPl, Real.cos_neg, Real.sin_neg, Prod.mk.injEq]
  constructor
  · linear_combination p1 * Real.sin_sq_add_cos_sq θ
  · linear_combination p2 * Real.sin_sq_add_cos_sq θ

/-- `rotPl θ` as a homeomorphism of the plane. -/
def rotPlHomeo (θ : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun := rotPl θ
  invFun := rotPl (-θ)
  left_inv p := rotPl_neg_rotPl θ p
  right_inv p := rotPl_rotPl_neg θ p
  continuous_toFun := rotPl_continuous θ
  continuous_invFun := rotPl_continuous (-θ)

theorem newtonInnerRot : NewtonInnerRot := by
  intro c ν χo M hc hν hχ hM θ t ht x hx i
  have hemb : MeasurableEmbedding (rotPl θ) := (rotPlHomeo θ).measurableEmbedding
  -- pointwise identity after the substitution `x' = rotPl θ a`
  have hpt : ∀ a : ℝ × ℝ,
      ∑ j, ∑ k, newtonD3 (rotAx θ x - t • embPlane (rotPl θ a)) i j k *
          sigmaM c ν χo M (rotPl θ a) j k =
        ∑ a' : Fin 3, rotMat θ i a' * NewtonFam.famF c ν χo M t a' a x := by
    intro a
    by_cases ha : a.1 ^ 2 + a.2 ^ 2 < 5 * ν / 6
    · have hw : x - t • embPlane a ≠ 0 :=
        NewtonFam.kernel_arg_ne_zero x a t (5 * ν / 6) ht.1.le ht.2 ha hx
      have hrw : rotAx θ x - t • embPlane (rotPl θ a) = rotAx θ (x - t • embPlane a) := by
        rw [rotAx_sub, rotAx_smul, rotAx_embPlane]
      have hS : ∀ j k, sigmaM c ν χo M (rotPl θ a) j k =
          ∑ p, ∑ q, rotMat θ j p * sigmaM c ν χo M a p q * rotMat θ k q :=
        fun j k => sigmaMRot c ν χo M θ a j k
      rw [hrw]
      simp only [newtonD3Rot θ (x - t • embPlane a) hw, hS]
      unfold NewtonFam.famF
      exact kerContractRot θ (fun p q r => newtonD3 (x - t • embPlane a) p q r)
        (fun p q => sigmaM c ν χo M a p q) i
    · have h0 : ∀ j k, sigmaM c ν χo M a j k = 0 := by
        intro j k
        rw [sigmaM_eq_zero_of_ge c ν χo M hν hχ a (not_lt.1 ha)]
        rfl
      have h1 : ∀ j k, sigmaM c ν χo M (rotPl θ a) j k = 0 := by
        intro j k
        rw [sigmaM_eq_zero_of_ge c ν χo M hν hχ (rotPl θ a)
          (by rw [rotPl_sq]; exact not_lt.1 ha)]
        rfl
      simp only [h0, h1, mul_zero, Finset.sum_const_zero, NewtonFam.famF]
  -- integrability of each `a ↦ famF t a' a x`
  have hint : ∀ a' : Fin 3,
      Integrable (fun a : ℝ × ℝ => NewtonFam.famF c ν χo M t a' a x) volume := by
    intro a'
    have hI := (NewtonFam.famF_locDom c ν χo M hν hχ hc hM t ht a').integrable
      (fun n y hy => NewtonFam.famF_aesm c ν χo M hc hν hχ hM t ht a' n y hy) 0 hx
    have hL := (continuousMultilinearCurryFin0 ℝ Vec3 ℝ).toContinuousLinearEquiv.toContinuousLinearMap
      |>.integrable_comp hI
    refine hL.congr (Eventually.of_forall fun a => ?_)
    simp
  calc ∫ x', ∑ j, ∑ k, newtonD3 (rotAx θ x - t • embPlane x') i j k *
          sigmaM c ν χo M x' j k
      = ∫ y, ∑ j, ∑ k, newtonD3 (rotAx θ x - t • embPlane (rotPl θ y)) i j k *
          sigmaM c ν χo M (rotPl θ y) j k :=
        ((rotPlMP θ).integral_comp hemb (fun x' => ∑ j, ∑ k, newtonD3 (rotAx θ x - t • embPlane x') i j k *
          sigmaM c ν χo M x' j k)).symm
    _ = ∫ y, ∑ a' : Fin 3, rotMat θ i a' * NewtonFam.famF c ν χo M t a' y x :=
        integral_congr_ae (ae_of_all _ fun a => hpt a)
    _ = ∑ a' : Fin 3, ∫ y, rotMat θ i a' * NewtonFam.famF c ν χo M t a' y x :=
        integral_finset_sum _ fun a' _ => (hint a').const_mul _
    _ = ∑ a, rotMat θ i a * ∫ x', ∑ j, ∑ k, newtonD3 (x - t • embPlane x') a j k *
          sigmaM c ν χo M x' j k :=
        Finset.sum_congr rfl fun a' _ => integral_const_mul _ _

end UnforcedLeray.Short.PartIIIb.Concrete
