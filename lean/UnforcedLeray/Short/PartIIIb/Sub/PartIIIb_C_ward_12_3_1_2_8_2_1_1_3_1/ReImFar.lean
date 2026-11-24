import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialSource
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialSourceCellL1
import UnforcedLeray.Lib.CZL2.TestProjection
import UnforcedLeray.Lib.CZL2.NewtonConv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_3_1.NewtonPairFar

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb

namespace ProjFar

/-- A Newton pairing of a spatial test is smooth (it is `-(N ∗ ∂ᵢf)`). -/
theorem contDiff_newtonPair_of_test (i : Fin 3) {f : UnforcedLeray.Space → ℝ}
    (hf : UnforcedLeray.IsSpatialTest f) :
    ContDiff ℝ ∞ (UnforcedLeray.RieszLp.newtonPair i f) := by
  have h : UnforcedLeray.RieszLp.newtonPair i f =
      fun y => -(UnforcedLeray.RieszLp.newtonConv (UnforcedLeray.spatialTestDerivative i f) y) := by
    funext y
    rw [UnforcedLeray.RieszLp.newtonConv_partial hf i y, neg_neg]
  rw [h]
  exact (UnforcedLeray.RieszLp.newtonConv_contDiff (hf.derivative i)).neg

/-- The `k`-th derivative of a negated finite sum of functions, bounded termwise. -/
theorem norm_iteratedFDeriv_neg_sum_le (k : ℕ) (F : Fin 3 → UnforcedLeray.Space → ℝ)
    (hF : ∀ j, ContDiff ℝ ∞ (F j)) (y : UnforcedLeray.Space) (B : Fin 3 → ℝ)
    (hB : ∀ j, ‖iteratedFDeriv ℝ k (F j) y‖ ≤ B j) :
    ‖iteratedFDeriv ℝ k (fun z => -∑ j : Fin 3, F j z) y‖ ≤ ∑ j : Fin 3, B j := by
  have hc : ∀ j ∈ (Finset.univ : Finset (Fin 3)), ContDiffAt ℝ k (F j) y := fun j _ =>
    (hF j).contDiffAt.of_le (by exact_mod_cast le_top)
  have h1 : iteratedFDeriv ℝ k (fun z => -∑ j : Fin 3, F j z) y =
      -∑ j : Fin 3, iteratedFDeriv ℝ k (F j) y := by
    change iteratedFDeriv ℝ k (-(fun z => ∑ j : Fin 3, F j z)) y = _
    rw [iteratedFDeriv_neg_apply, iteratedFDeriv_fun_sum_apply hc]
  rw [h1, norm_neg]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hB j)

/-- Product bound used termwise: `|c I e| ≤ |c| M e` when `0 ≤ I ≤ M` and `0 ≤ e`. -/
theorem mul_bound_aux (c I M e : ℝ) (hI : 0 ≤ I) (hIM : I ≤ M) (he : 0 ≤ e) :
    c * I * e ≤ |c| * M * e := by
  apply mul_le_mul_of_nonneg_right _ he
  exact (mul_le_mul_of_nonneg_right (le_abs_self c) hI).trans
    (mul_le_mul_of_nonneg_left hIM (abs_nonneg c))

/-- Real component: the slice is a finite Newton pairing of the real test components. -/
theorem fun_re_eq (Ψ : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3)
    {P : ℝ} (hΨ : UnforcedLeray.PhaseSpace.IsPhaseTest P Ψ) (τ : ℝ) :
    (fun z => UnforcedLeray.Cons.C03.Concrete.projectedPotentialRePath Ψ (τ, z)) =
      fun z => -∑ j : Fin 3,
        UnforcedLeray.RieszLp.newtonPair j
          (UnforcedLeray.Cons.C03.Concrete.projectedPotentialReTest Ψ τ j) z := by
  funext z
  show UnforcedLeray.RieszLp.lerayPotential
      (UnforcedLeray.Cons.C03.Concrete.projectedPotentialReTest Ψ τ) z = _
  exact UnforcedLeray.RieszLp.lerayPotential_eq
    (UnforcedLeray.Cons.C03.Concrete.isSpatialTest_projectedPotentialReTest hΨ τ) z

/-- Imaginary component: the slice is a finite Newton pairing of the imaginary test components. -/
theorem fun_im_eq (Ψ : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3)
    {P : ℝ} (hΨ : UnforcedLeray.PhaseSpace.IsPhaseTest P Ψ) (τ : ℝ) :
    (fun z => UnforcedLeray.Cons.C03.Concrete.projectedPotentialImPath Ψ (τ, z)) =
      fun z => -∑ j : Fin 3,
        UnforcedLeray.RieszLp.newtonPair j
          (UnforcedLeray.Cons.C03.Concrete.projectedPotentialImTest Ψ τ j) z := by
  funext z
  show UnforcedLeray.RieszLp.lerayPotential
      (UnforcedLeray.Cons.C03.Concrete.projectedPotentialImTest Ψ τ) z = _
  exact UnforcedLeray.RieszLp.lerayPotential_eq
    (UnforcedLeray.Cons.C03.Concrete.isSpatialTest_projectedPotentialImTest hΨ τ) z

end ProjFar

open ProjFar in
/-- Uniform-in-`τ` far-field derivative bound for the real and imaginary Newton path potentials. -/
theorem projectedPotentialPath_deriv_far {P : ℝ} [Fact (0 < P)]
    {Ψ : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3}
    (hΨ : UnforcedLeray.PhaseSpace.IsPhaseTest P Ψ) (k : ℕ) :
    ∃ ρ C : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) P, ∀ y : UnforcedLeray.Space, ρ ≤ ‖y‖ → 0 < ‖y‖ →
      ‖iteratedFDeriv ℝ k
          (fun z => UnforcedLeray.Cons.C03.Concrete.projectedPotentialRePath Ψ (τ, z)) y‖ ≤
        C * ‖y‖ ^ (-(2 + (k : ℝ))) ∧
      ‖iteratedFDeriv ℝ k
          (fun z => UnforcedLeray.Cons.C03.Concrete.projectedPotentialImPath Ψ (τ, z)) y‖ ≤
        C * ‖y‖ ^ (-(2 + (k : ℝ))) := by
  obtain ⟨R, hR⟩ := hΨ.bounded_support
  -- Newton far-field constants, one for each coordinate `i`.
  choose Cn hCn using fun i : Fin 3 => UnforcedLeray.Short.PartIIIb.Concrete.newtonPair_iteratedFDeriv_far i k
  -- Uniform spatial L¹ bounds for the real and imaginary coordinate tests.
  have hMRe : ∀ i : Fin 3, ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Icc (0 : ℝ) P,
      ∫ x, |UnforcedLeray.Cons.C03.Concrete.projectedPotentialReTest Ψ τ i x| ≤ M := fun i =>
    UnforcedLeray.Cons.C03.Concrete.exists_uniform_spatialL1_of_isPhaseTest
      (hΨ.clm_comp (UnforcedLeray.Cons.C03.Concrete.projectedPotentialReCoordCLM i))
  have hMIm : ∀ i : Fin 3, ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Icc (0 : ℝ) P,
      ∫ x, |UnforcedLeray.Cons.C03.Concrete.projectedPotentialImTest Ψ τ i x| ≤ M := fun i =>
    UnforcedLeray.Cons.C03.Concrete.exists_uniform_spatialL1_of_isPhaseTest
      (hΨ.clm_comp (UnforcedLeray.Cons.C03.Concrete.projectedPotentialImCoordCLM i))
  choose Mre hMre0 hMre using hMRe
  choose Mim hMim0 hMim using hMIm
  -- The far-field support radius is `max R 0`; take `ρ = 2 max R 0 + 1 > 0`.
  refine ⟨2 * max R 0 + 1, ∑ j : Fin 3, |Cn j| * (Mre j + Mim j), ?_⟩
  intro τ hτ y hρ hy0
  have hy2 : 2 * max R 0 ≤ ‖y‖ := by linarith
  have hy0' : y ≠ 0 := norm_pos_iff.1 hy0
  have he : (0 : ℝ) ≤ ‖y‖ ^ (-(2 + (k : ℝ))) := Real.rpow_nonneg (norm_nonneg y) _
  have hR' : ∀ j : Fin 3, ∀ x : UnforcedLeray.Space, max R 0 < ‖x‖ →
      UnforcedLeray.Cons.C03.Concrete.projectedPotentialReTest Ψ τ j x = 0 := by
    intro j x hx
    have hzero := hR τ x (lt_of_le_of_lt (le_max_left R 0) hx)
    simp [UnforcedLeray.Cons.C03.Concrete.projectedPotentialReTest, hzero]
  have hR'' : ∀ j : Fin 3, ∀ x : UnforcedLeray.Space, max R 0 < ‖x‖ →
      UnforcedLeray.Cons.C03.Concrete.projectedPotentialImTest Ψ τ j x = 0 := by
    intro j x hx
    have hzero := hR τ x (lt_of_le_of_lt (le_max_left R 0) hx)
    simp [UnforcedLeray.Cons.C03.Concrete.projectedPotentialImTest, hzero]
  constructor
  · rw [fun_re_eq Ψ hΨ τ]
    refine (norm_iteratedFDeriv_neg_sum_le k
      (fun j => UnforcedLeray.RieszLp.newtonPair j
        (UnforcedLeray.Cons.C03.Concrete.projectedPotentialReTest Ψ τ j))
      (fun j => contDiff_newtonPair_of_test j
        (UnforcedLeray.Cons.C03.Concrete.isSpatialTest_projectedPotentialReTest hΨ τ j))
      y (fun j => |Cn j| * (Mre j + Mim j) * ‖y‖ ^ (-(2 + (k : ℝ))))
      (fun j => ?_)).trans (le_of_eq ?_)
    · refine (hCn j (max R 0) (UnforcedLeray.Cons.C03.Concrete.projectedPotentialReTest Ψ τ j) ?_ (hR' j) y hy2 hy0').trans ?_
      · exact UnforcedLeray.Cons.C03.Concrete.isSpatialTest_projectedPotentialReTest hΨ τ j
      · refine mul_bound_aux _ _ _ _ (integral_nonneg fun x => abs_nonneg _) ?_ he
        exact (hMre j τ hτ).trans (le_add_of_nonneg_right (hMim0 j))
    · rw [Finset.sum_mul]
  · rw [fun_im_eq Ψ hΨ τ]
    refine (norm_iteratedFDeriv_neg_sum_le k
      (fun j => UnforcedLeray.RieszLp.newtonPair j
        (UnforcedLeray.Cons.C03.Concrete.projectedPotentialImTest Ψ τ j))
      (fun j => contDiff_newtonPair_of_test j
        (UnforcedLeray.Cons.C03.Concrete.isSpatialTest_projectedPotentialImTest hΨ τ j))
      y (fun j => |Cn j| * (Mre j + Mim j) * ‖y‖ ^ (-(2 + (k : ℝ))))
      (fun j => ?_)).trans (le_of_eq ?_)
    · refine (hCn j (max R 0) (UnforcedLeray.Cons.C03.Concrete.projectedPotentialImTest Ψ τ j) ?_ (hR'' j) y hy2 hy0').trans ?_
      · exact UnforcedLeray.Cons.C03.Concrete.isSpatialTest_projectedPotentialImTest hΨ τ j
      · refine mul_bound_aux _ _ _ _ (integral_nonneg fun x => abs_nonneg _) ?_ he
        exact (hMim j τ hτ).trans (le_add_of_nonneg_left (hMre0 j))
    · rw [Finset.sum_mul]

end UnforcedLeray.Short.PartIIIb
