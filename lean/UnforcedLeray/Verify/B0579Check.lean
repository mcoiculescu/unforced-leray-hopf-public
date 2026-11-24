import UnforcedLeray.Units.B0579
import UnforcedLeray.Units.B0656.Sobolev

/-!
# Verifier check for B0579 (not part of the unit)

* `#print axioms` on the headline declarations of `Units/B0579.lean`.
* Uniqueness of weak cylinder derivatives for `B0579.H1`: `value` is injective for `0 < c`,
  so the graph space `H1 c m` is the function space of `paper/main.tex:9374-9375`.
* `sourceCLM c m` is injective for `0 < c` (sources are determined by their distributions).

The periodization of compactly supported tests is reused from the WIP file

`isPeriodicTest_periodize`); the argument follows its `eq_zero_of_forall_test`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.B0579Check

open UnforcedLeray.B0579

#print axioms UnforcedLeray.B0579.memH1_iff
#print axioms UnforcedLeray.B0579.H1.norm_sq_eq_weighted
#print axioms UnforcedLeray.B0579.abs_integral_mul_le
#print axioms UnforcedLeray.B0579.sourceCLM_apply
#print axioms UnforcedLeray.B0579.norm_sourceCLM_le
#print axioms UnforcedLeray.B0579.derivSourceCLM_apply
#print axioms UnforcedLeray.B0579.norm_derivSourceCLM_le
#print axioms UnforcedLeray.B0579.integral_mul_pd
#print axioms UnforcedLeray.B0579.toDistribution_sourceCLM
#print axioms UnforcedLeray.B0579.toDistribution_derivSourceCLM
#print axioms UnforcedLeray.B0579.inner_eq_unweighted_conj
#print axioms UnforcedLeray.B0579.weightEquiv
#print axioms UnforcedLeray.B0579.pivot_equivalence
#print axioms UnforcedLeray.B0579.norm_sourceCLM_le_pivot
#print axioms UnforcedLeray.B0579.norm_pivot_le_sourceCLM

theorem isCylTest_of_periodicTest {c : ℝ} {φ : ℝ × ℝ → ℝ}
    (h : UnforcedLeray.B0656.IsPeriodicTest c φ) : IsCylTest c φ :=
  ⟨h.smooth, fun x => h.periodic x.1 x.2, h.bounded⟩

theorem openCell_subset (c : ℝ) : UnforcedLeray.B0656.cell c ⊆ cell c :=
  prod_mono Ioo_subset_Ico_self subset_rfl

theorem locallyIntegrableOn_X {c m : ℝ} (f : X c m) :
    LocallyIntegrableOn (f : Plane → ℝ) (UnforcedLeray.B0656.cell c) volume := by
  rw [locallyIntegrableOn_iff (UnforcedLeray.B0656.isOpen_cell c).isLocallyClosed]
  intro K hK hKc
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Plane)).1 hKc.isBounded
  refine (integrableOn_band_X f R).mono_set ?_
  intro x hx
  refine ⟨?_, openCell_subset c (hK hx)⟩
  have hmem := hR hx
  rw [Metric.mem_closedBall, dist_zero_right] at hmem
  show |x.2| ≤ R
  have := norm_snd_le x
  rw [Real.norm_eq_abs] at this
  linarith

theorem periodize_eq_on_Ico {c : ℝ} (hc : 0 < c) (g : Plane → ℝ) {x : Plane} (hx : x ∈ cell c) :
    UnforcedLeray.B0656.periodize hc g x = g x := by
  have h := (mem_prod.1 hx).1
  have hmod : toIcoMod hc (-(c / 2)) x.1 = x.1 :=
    (toIcoMod_eq_self hc).2 ⟨h.1, by linarith [h.2]⟩
  simp [UnforcedLeray.B0656.periodize, hmod]

/-- An element of `X_m` annihilating every cylinder test function vanishes. -/
theorem eq_zero_of_forall_test {c m : ℝ} (hc : 0 < c) (f : X c m)
    (h : ∀ φ : Plane → ℝ, IsCylTest c φ → ∫ x in cell c, f x * φ x = 0) : f = 0 := by
  have hzero := (UnforcedLeray.B0656.isOpen_cell c).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := volume) (locallyIntegrableOn_X f) (fun g hgs hgc hsub => by
      have hP := isCylTest_of_periodicTest
        (UnforcedLeray.B0656.isPeriodicTest_periodize hc hgs hgc hsub)
      rw [← h _ hP]
      have hvan : ∀ x, x ∉ cell c → g x = 0 := fun x hx => by
        by_contra hne
        exact hx (openCell_subset c (hsub (subset_tsupport g hne)))
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := cell c)
        (fun x hx => by simp [hvan x hx])]
      refine setIntegral_congr_fun (measurableSet_cell c) fun x hx => ?_
      simp only [smul_eq_mul]
      rw [periodize_eq_on_Ico hc g hx, mul_comm])
  have h2 : ∀ᵐ x ∂(volume.restrict (cell c)), (f : Plane → ℝ) x = 0 := by
    filter_upwards [ae_restrict_of_ae hzero, ae_cell_abs_fst_lt c] with x h1 h2
    exact h1 ⟨⟨(abs_lt.1 h2).1, (abs_lt.1 h2).2⟩, mem_univ _⟩
  apply Lp.ext
  filter_upwards [(cellMeasure_ac c m).ae_le h2, Lp.coeFn_zero ℝ 2 (cellMeasure c m)]
    with x hx h0
  rw [hx, h0, Pi.zero_apply]

/-- Weak cylinder derivatives are unique: `H1.value` is injective. -/
theorem H1_value_injective {c m : ℝ} (hc : 0 < c) :
    Function.Injective (fun F : H1 c m => F.value) := by
  intro F G hv
  simp only at hv
  refine H1.ext_comp hv fun j => ?_
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_test hc
  intro φ hφ
  have hF := F.hasWeakCellDeriv j φ hφ
  have hG := G.hasWeakCellDeriv j φ hφ
  rw [hv] at hF
  rw [← inner_testVec c m hφ (F.der j - G.der j), inner_sub_right, inner_testVec,
    inner_testVec]
  linarith

/-- Sources are determined by their action: `sourceCLM` is injective. -/
theorem sourceCLM_injective {c m : ℝ} (hc : 0 < c) : Function.Injective (sourceCLM c m) := by
  intro f g hfg
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_test hc
  intro φ hφ
  have e := congrArg (fun ℓ => toDistribution c m ℓ ⟨φ, hφ⟩) hfg
  simp only [toDistribution_sourceCLM] at e
  rw [← inner_testVec c m hφ (f - g), inner_sub_right, inner_testVec, inner_testVec, e, sub_self]

#print axioms H1_value_injective
#print axioms sourceCLM_injective

end UnforcedLeray.B0579Check
