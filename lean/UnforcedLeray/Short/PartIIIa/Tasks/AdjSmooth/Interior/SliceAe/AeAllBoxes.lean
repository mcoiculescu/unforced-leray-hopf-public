import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_1_9

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- Boxes `[-n, n]²` exhaust the plane. -/
lemma iUnion_sliceBox_nat : (⋃ n : ℕ, sliceBox (n : ℝ)) = univ := by
  refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
  obtain ⟨n, hn⟩ := exists_nat_ge (|x.1| + |x.2|)
  refine ⟨n, ?_⟩
  have h1 : |x.1| ≤ (n : ℝ) := by linarith [abs_nonneg x.2]
  have h2 : |x.2| ≤ (n : ℝ) := by linarith [abs_nonneg x.1]
  exact ⟨abs_le.1 h1, abs_le.1 h2⟩

theorem aeAllBoxes : UnforcedLeray.Short.IIIa.AeAllBoxes := by
  intro P h
  have key := (ae_restrict_iUnion_iff (fun n : ℕ => sliceBox (n : ℝ)) (fun x => P x)).2 h
  rwa [iUnion_sliceBox_nat, Measure.restrict_univ] at key

end UnforcedLeray.Short.IIIa
