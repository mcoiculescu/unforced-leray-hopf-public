import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromAgeJets
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanStress.FluctVelSliceBound.Calc

/-!
# `PartIII-b:C/rep/8/2/3/2/2`: the vector form of the joint age jet bound `jointAgeVec`

Source of record: `the November 2 reference manuscript` 5464-5465.
Vector form of the proved `PartI.jointFromAgeJets`: each coordinate is a scalar jointly smooth
field, the norm of a multilinear map into `EuclideanSpace ℝ (Fin 2)` is at most the sum of the
norms of its two coordinate maps, and each coordinate age jet is at most the vector age jet
(`PartIIa.fvs_ageJet_proj_le`).  The constant is `K = 2 K₀`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- A vector of `EuclideanSpace ℝ (Fin 2)` has norm at most the sum of the absolute coordinates. -/
theorem jav_norm_le (w : EuclideanSpace ℝ (Fin 2)) : ‖w‖ ≤ |w 0| + |w 1| := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  simp only [Fin.sum_univ_two, Real.norm_eq_abs]
  have e : (|w 0| + |w 1|) ^ 2 = w 0 ^ 2 + w 1 ^ 2 + 2 * (|w 0| * |w 1|) := by
    rw [add_sq, sq_abs, sq_abs]; ring
  rw [e]
  have := mul_nonneg (abs_nonneg (w 0)) (abs_nonneg (w 1))
  have h2 : ∀ x : ℝ, |x| ^ 2 = x ^ 2 := fun x => sq_abs x
  nlinarith [h2 (w 0), h2 (w 1)]

/-- The norm of a multilinear map into `EuclideanSpace ℝ (Fin 2)` is at most the sum of the norms
of its two coordinate maps. -/
theorem jav_multi_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {i : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin i => E) (EuclideanSpace ℝ (Fin 2))) :
    ‖M‖ ≤ ‖(EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).compContinuousMultilinearMap M‖
      + ‖(EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).compContinuousMultilinearMap M‖ := by
  set A := (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).compContinuousMultilinearMap M with hAdef
  set B := (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).compContinuousMultilinearMap M with hBdef
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro m
  have key : ‖M m‖ ≤ ‖A m‖ + ‖B m‖ := by
    have h := jav_norm_le (M m)
    have hA : A m = (M m) 0 := rfl
    have hB : B m = (M m) 1 := rfl
    rw [hA, hB, Real.norm_eq_abs, Real.norm_eq_abs]
    exact h
  have hA' := A.le_opNorm m
  have hB' := B.le_opNorm m
  calc ‖M m‖ ≤ ‖A m‖ + ‖B m‖ := key
    _ ≤ ‖A‖ * ∏ i, ‖m i‖ + ‖B‖ * ∏ i, ‖m i‖ := add_le_add hA' hB'
    _ = (‖A‖ + ‖B‖) * ∏ i, ‖m i‖ := by ring

/-- The coordinate of an iterated derivative: composing with the `k`-th projection. -/
theorem jav_iter_proj {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → EuclideanSpace ℝ (Fin 2)} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) {y : E} (hy : y ∈ U) (k : Fin 2) (i : ℕ) :
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).compContinuousMultilinearMap
        (iteratedFDeriv ℝ i f y) =
      iteratedFDeriv ℝ i (fun x => f x k) y := by
  have hcomp : (fun x => f x k) = (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) ∘ f :=
    rfl
  rw [hcomp, ← iteratedFDerivWithin_of_isOpen i hU hy,
    ← iteratedFDerivWithin_of_isOpen i hU hy]
  exact ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).iteratedFDerivWithin_comp_left
    (hf y hy) hU.uniqueDiffOn hy (by exact_mod_cast le_top)).symm

/-- **Target** `jointAgeVec`: the vector form of `PartI.jointFromAgeJets` (`JointAgeVec`). -/
theorem jointAgeVec : JointAgeVec := by
  intro i
  obtain ⟨K₀, hK₀, H⟩ := UnforcedLeray.Short.PartI.jointFromAgeJets i
  refine ⟨2 * K₀, by positivity, ?_⟩
  intro F hF y hy
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have hyU : y ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := ⟨hy, mem_univ _⟩
  have hcomp : ∀ k : Fin 2, ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2 k)
      (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := fun k => (contDiffOn_piLp 2).1 hF k
  have hA : ∀ k : Fin 2, ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => F x.1 x.2 k) y‖ ≤
      K₀ * ∑ ℓ ∈ Finset.range (i + 1), ‖UnforcedLeray.Short.PartI.ageJet ℓ (i - ℓ) F y.1 y.2‖ := by
    intro k
    refine (H (fun r w => F r w k) (hcomp k) y hy).trans ?_
    apply mul_le_mul_of_nonneg_left _ hK₀
    apply Finset.sum_le_sum
    intro ℓ _
    exact UnforcedLeray.Short.PartIIa.fvs_ageJet_proj_le (G := F) hF k (fun r w => F r w k)
      (fun _ _ _ => rfl) (i - ℓ) ℓ hy y.2
  have hmulti := jav_multi_le (iteratedFDeriv ℝ i (fun x : ℝ × Plane => F x.1 x.2) y)
  rw [jav_iter_proj hU hF hyU 0 i, jav_iter_proj hU hF hyU 1 i] at hmulti
  calc ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => F x.1 x.2) y‖
      ≤ ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => F x.1 x.2 0) y‖ +
        ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => F x.1 x.2 1) y‖ := hmulti
    _ ≤ K₀ * ∑ ℓ ∈ Finset.range (i + 1), ‖UnforcedLeray.Short.PartI.ageJet ℓ (i - ℓ) F y.1 y.2‖ +
        K₀ * ∑ ℓ ∈ Finset.range (i + 1), ‖UnforcedLeray.Short.PartI.ageJet ℓ (i - ℓ) F y.1 y.2‖ :=
          add_le_add (hA 0) (hA 1)
    _ = 2 * K₀ * ∑ ℓ ∈ Finset.range (i + 1), ‖UnforcedLeray.Short.PartI.ageJet ℓ (i - ℓ) F y.1 y.2‖ := by
          ring

end UnforcedLeray.Short.PartIIIb.Concrete
