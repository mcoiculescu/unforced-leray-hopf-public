import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Moving the outer `j, k` sums past the block `b, d, p, q`. -/
theorem swap6 (F : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) :
    ∑ j, ∑ k, ∑ b, ∑ d, ∑ p, ∑ q, F j k b d p q =
      ∑ b, ∑ d, ∑ p, ∑ q, ∑ j, ∑ k, F j k b d p q := by
  have L1 : ∀ f : Fin 3 → Fin 3 → Fin 3 → ℝ,
      ∑ j, ∑ k, ∑ x, f j k x = ∑ x, ∑ j, ∑ k, f j k x := by
    intro f
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_comm]
    exact Finset.sum_comm
  calc ∑ j, ∑ k, ∑ b, ∑ d, ∑ p, ∑ q, F j k b d p q
      = ∑ b, ∑ j, ∑ k, ∑ d, ∑ p, ∑ q, F j k b d p q :=
        L1 (fun j k b => ∑ d, ∑ p, ∑ q, F j k b d p q)
    _ = ∑ b, ∑ d, ∑ j, ∑ k, ∑ p, ∑ q, F j k b d p q :=
        Finset.sum_congr rfl fun b _ => L1 (fun j k d => ∑ p, ∑ q, F j k b d p q)
    _ = ∑ b, ∑ d, ∑ p, ∑ j, ∑ k, ∑ q, F j k b d p q :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ =>
          L1 (fun j k p => ∑ q, F j k b d p q)
    _ = ∑ b, ∑ d, ∑ p, ∑ q, ∑ j, ∑ k, F j k b d p q :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ =>
          Finset.sum_congr rfl fun p _ => L1 (fun j k q => F j k b d p q)

/-- Pure contraction identity: orthogonality of the columns collapses the rotated sums. -/
theorem kerContract_aux (R : Fin 3 → Fin 3 → ℝ)
    (hO : ∀ b p : Fin 3, ∑ j, R j b * R j p = if b = p then 1 else 0)
    (M S : Fin 3 → Fin 3 → ℝ) :
    ∑ j, ∑ k, (∑ b, ∑ d, M b d * R j b * R k d) * (∑ p, ∑ q, R j p * S p q * R k q) =
      ∑ b, ∑ d, M b d * S b d := by
  have e1 : ∀ j k : Fin 3, (∑ b, ∑ d, M b d * R j b * R k d) * (∑ p, ∑ q, R j p * S p q * R k q)
      = ∑ b, ∑ d, ∑ p, ∑ q, (M b d * S p q) * ((R j b * R j p) * (R k d * R k q)) := by
    intro j k
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  simp only [e1]
  refine (swap6 (fun j k b d p q => (M b d * S p q) * ((R j b * R j p) * (R k d * R k q)))).trans ?_
  have e2 : ∀ (c : ℝ) (b d p q : Fin 3),
      ∑ j, ∑ k, c * ((R j b * R j p) * (R k d * R k q)) =
        c * ((∑ j, R j b * R j p) * (∑ k, R k d * R k q)) := by
    intro c b d p q
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Finset.mul_sum]
  simp only [e2, hO]
  simp [mul_ite]

theorem kerContractRot : KerContractRot := by
  intro θ D S i
  have hL : ∀ j k : Fin 3,
      (∑ a, ∑ b, ∑ d, rotMat θ i a * rotMat θ j b * rotMat θ k d * D a b d) =
        ∑ b, ∑ d, (∑ a, rotMat θ i a * D a b d) * rotMat θ j b * rotMat θ k d := by
    intro j k
    simp only [Fin.sum_univ_three]
    ring
  simp only [hL]
  have h := kerContract_aux (rotMat θ) (rotMat_orth θ)
    (fun b d => ∑ a, rotMat θ i a * D a b d) S
  rw [h]
  simp only [Fin.sum_univ_three]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
