import UnforcedLeray.Short.PartIIIa.Defs

/-!
# Part III-a long assembly, H3: triangle bounds for finite linear combinations

For `α i ∈ ℂ` and `g i` with `‖g i‖_{L²(μ)} ≤ k`, the norm of `Σ α i g i` is at most
`(Σ |α i|) k`, and `W - Σ α i g i` differs from `W` by at most that amount. These give the bounds
`‖compl‖ ≤ ‖W‖ + k Σ|α|` and `‖W‖ ≤ ‖compl‖ + k Σ|α|` of the moving frame.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

lemma aesm_finset_sum {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*}
    (s : Finset ι) (f : ι → X → ℂ) (hf : ∀ i, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun x => ∑ i ∈ s, f i x) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [aestronglyMeasurable_const]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a).add ih

lemma aesm_sum_smul {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]
    (α : ι → ℂ) (g : ι → X → ℂ) (hg : ∀ i, AEStronglyMeasurable (g i) μ) :
    AEStronglyMeasurable (fun x => ∑ i, α i * g i x) μ :=
  aesm_finset_sum Finset.univ (fun i x => α i * g i x) (fun i => (hg i).const_mul (α i))

lemma eLpNorm_sum_smul_le {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]
    (α : ι → ℂ) (g : ι → X → ℂ) (k : ℝ≥0∞) (hg : ∀ i, AEStronglyMeasurable (g i) μ)
    (hk : ∀ i, eLpNorm (g i) 2 μ ≤ k) :
    eLpNorm (fun x => ∑ i, α i * g i x) 2 μ ≤ (∑ i, ENNReal.ofReal ‖α i‖) * k := by
  have h1 : (fun x => ∑ i, α i * g i x) = ∑ i, (fun x => α i * g i x) := by
    funext x
    rw [Finset.sum_apply]
  rw [h1]
  refine (eLpNorm_sum_le (fun i _ => (hg i).const_mul (α i)) (by norm_num)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hsmul : (fun x => α i * g i x) = α i • g i := by
    funext x
    rfl
  rw [hsmul, eLpNorm_const_smul, ← ofReal_norm_eq_enorm]
  exact mul_le_mul_of_nonneg_left (hk i) zero_le

lemma eLpNorm_sub_sum_le {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]
    {W : X → ℂ} (α : ι → ℂ) (g : ι → X → ℂ) (k : ℝ≥0∞) (hW : AEStronglyMeasurable W μ)
    (hg : ∀ i, AEStronglyMeasurable (g i) μ) (hk : ∀ i, eLpNorm (g i) 2 μ ≤ k) :
    eLpNorm (fun x => W x - ∑ i, α i * g i x) 2 μ ≤
      eLpNorm W 2 μ + (∑ i, ENNReal.ofReal ‖α i‖) * k := by
  refine (eLpNorm_sub_le hW (aesm_sum_smul α g hg) (by norm_num)).trans ?_
  exact add_le_add le_rfl (eLpNorm_sum_smul_le α g k hg hk)

lemma eLpNorm_le_sub_sum_add {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*}
    [Fintype ι] {W : X → ℂ} (α : ι → ℂ) (g : ι → X → ℂ) (k : ℝ≥0∞)
    (hW : AEStronglyMeasurable W μ)
    (hg : ∀ i, AEStronglyMeasurable (g i) μ) (hk : ∀ i, eLpNorm (g i) 2 μ ≤ k) :
    eLpNorm W 2 μ ≤
      eLpNorm (fun x => W x - ∑ i, α i * g i x) 2 μ + (∑ i, ENNReal.ofReal ‖α i‖) * k := by
  have hsum := aesm_sum_smul α g hg
  have hcompl : AEStronglyMeasurable (fun x => W x - ∑ i, α i * g i x) μ := hW.sub hsum
  have hrec : (fun x => W x - ∑ i, α i * g i x) + (fun x => ∑ i, α i * g i x) = W := by
    funext x
    simp
  calc eLpNorm W 2 μ
      = eLpNorm ((fun x => W x - ∑ i, α i * g i x) + (fun x => ∑ i, α i * g i x)) 2 μ := by
        rw [hrec]
    _ ≤ eLpNorm (fun x => W x - ∑ i, α i * g i x) 2 μ
          + eLpNorm (fun x => ∑ i, α i * g i x) 2 μ :=
        eLpNorm_add_le hcompl hsum (by norm_num)
    _ ≤ eLpNorm (fun x => W x - ∑ i, α i * g i x) 2 μ + (∑ i, ENNReal.ofReal ‖α i‖) * k :=
        add_le_add le_rfl (eLpNorm_sum_smul_le α g k hg hk)

end UnforcedLeray.Short.IIIa
