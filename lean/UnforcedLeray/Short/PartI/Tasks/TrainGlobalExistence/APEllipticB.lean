import UnforcedLeray.Short.PartI.Sub.PartI_T04_8
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.JetWord
import Mathlib.Algebra.Order.Chebyshev

/-!
# Part I, task `PartI:T04/8/2`, target `apEllipticB`: pointwise jet bound

`‖D^{j+1} f z‖² ≤ 2^{j+2} * wordGradSq j f z`.  Route:
* `‖x‖ ≤ Σ_k |x k|` on `Vec`, so `‖D^l f z‖ ≤ Σ_k ‖D^l f_k z‖` (multilinear `opNorm_le_bound`);
* `cylJetWord_proof` (second part) on each component `f_k`: `‖D^l f_k z‖ ≤ Σ_{|w|=l} |∂_w f_k z|`;
* Cauchy-Schwarz over the `2 · #wordsOfLength (j+1) ≤ 2^{j+2}` pairs `(k, w)`;
* `Σ_{|w'|=j+1} F w' = Σ_{|w|=j} (F (true::w) + F (false::w))`, and
  `wordComp (true::w) = ∂_q (wordComp w)`, `wordComp (false::w) = ∂_η (wordComp w)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

namespace APEllipticBaux

theorem vec_norm_le_sum (x : Vec) : ‖x‖ ≤ ∑ k : Fin 2, |x k| := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  nlinarith [sq_abs (x 0), sq_abs (x 1), mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 1))]

theorem iteratedFDeriv_vec_le {f : Plane → Vec} (hf : ContDiff ℝ ∞ f) (l : ℕ) (z : Plane) :
    ‖iteratedFDeriv ℝ l f z‖ ≤ ∑ k : Fin 2, ‖iteratedFDeriv ℝ l (fun x => f x k) z‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro m
  have key : ∀ k : Fin 2, (iteratedFDeriv ℝ l (fun x => f x k) z) m = (iteratedFDeriv ℝ l f z m) k := by
    intro k
    have hcomp : (fun x => f x k) = (EuclideanSpace.proj k : Vec →L[ℝ] ℝ) ∘ f := rfl
    rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_left _ hf.contDiffAt (by simp)]
    rfl
  calc ‖iteratedFDeriv ℝ l f z m‖ ≤ ∑ k : Fin 2, |iteratedFDeriv ℝ l f z m k| :=
        vec_norm_le_sum _
    _ = ∑ k : Fin 2, |(iteratedFDeriv ℝ l (fun x => f x k) z) m| := by
        apply Finset.sum_congr rfl
        intro k _
        rw [key k]
    _ ≤ ∑ k : Fin 2, ‖iteratedFDeriv ℝ l (fun x => f x k) z‖ * ∏ i, ‖m i‖ := by
        apply Finset.sum_le_sum
        intro k _
        rw [← Real.norm_eq_abs]
        exact ContinuousMultilinearMap.le_opNorm _ _
    _ = (∑ k : Fin 2, ‖iteratedFDeriv ℝ l (fun x => f x k) z‖) * ∏ i, ‖m i‖ :=
        (Finset.sum_mul _ _ _).symm

theorem card_wordsOfLength_le (j : ℕ) : (wordsOfLength j).card ≤ 2 ^ j := by
  unfold wordsOfLength
  calc _ ≤ (Finset.univ : Finset (Fin j → Bool)).card := Finset.card_image_le
    _ = 2 ^ j := by simp

theorem sum_wordsOfLength_succ (F : List Bool → ℝ) (j : ℕ) :
    ∑ w ∈ wordsOfLength (j + 1), F w = ∑ w ∈ wordsOfLength j, (F (true :: w) + F (false :: w)) := by
  have hcons : ∀ (b : Bool) (u : Fin j → Bool),
      List.ofFn (Fin.cons b u : Fin (j + 1) → Bool) = b :: List.ofFn u := by
    intro b u
    rw [List.ofFn_succ]
    simp
  unfold wordsOfLength
  rw [Finset.sum_image (fun _ _ _ _ h => List.ofFn_injective h),
    Finset.sum_image (fun _ _ _ _ h => List.ofFn_injective h)]
  calc ∑ v : Fin (j + 1) → Bool, F (List.ofFn v)
      = ∑ p : Bool × (Fin j → Bool), F (List.ofFn (Fin.cons p.1 p.2 : Fin (j + 1) → Bool)) :=
        (Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (j + 1) => Bool) _ _ (fun _ => rfl)).symm
    _ = ∑ u : Fin j → Bool, (F (true :: List.ofFn u) + F (false :: List.ofFn u)) := by
        rw [Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_add_distrib]
        simp only [hcons]

theorem wordComp_true (w : List Bool) (f : Plane → Vec) (k : Fin 2) :
    wordComp (true :: w) f k = Cyl.partialQ (wordComp w f k) :=
  rfl

theorem wordComp_false (w : List Bool) (f : Plane → Vec) (k : Fin 2) :
    wordComp (false :: w) f k = Cyl.partialEta (wordComp w f k) :=
  rfl

end APEllipticBaux

open APEllipticBaux in
/-- Target `apEllipticB`: `‖D^{j+1} f z‖² ≤ 2^{j+2} * wordGradSq j f z`. -/
theorem apEllipticB : APEllipticB := by
  intro j c f hdata z
  obtain ⟨-, hf, -, -, -, -⟩ := hdata
  have hcomp_smooth : ∀ k : Fin 2, ContDiff ℝ ∞ (fun x => f x k) := fun k =>
    (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp hf
  have h1 : ‖iteratedFDeriv ℝ (j + 1) f z‖ ≤
      ∑ p ∈ (Finset.univ : Finset (Fin 2)) ×ˢ wordsOfLength (j + 1), |wordComp p.2 f p.1 z| := by
    rw [Finset.sum_product]
    refine (iteratedFDeriv_vec_le hf (j + 1) z).trans (Finset.sum_le_sum fun k _ => ?_)
    exact (cylJetWord_proof (fun x => f x k) (hcomp_smooth k) (j + 1) z).2
  have hTN : ((Finset.univ : Finset (Fin 2)) ×ˢ wordsOfLength (j + 1)).card ≤ 2 ^ (j + 2) := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    have hc := card_wordsOfLength_le (j + 1)
    calc 2 * (wordsOfLength (j + 1)).card ≤ 2 * 2 ^ (j + 1) := Nat.mul_le_mul_left 2 hc
      _ = 2 ^ (j + 2) := by ring
  have hTR : (((Finset.univ : Finset (Fin 2)) ×ˢ wordsOfLength (j + 1)).card : ℝ) ≤ 2 ^ (j + 2) := by
    exact_mod_cast hTN
  have h3 : ∑ p ∈ (Finset.univ : Finset (Fin 2)) ×ˢ wordsOfLength (j + 1),
      |wordComp p.2 f p.1 z| ^ 2 = wordGradSq j f z := by
    rw [Finset.sum_product]
    simp only [sq_abs]
    unfold wordGradSq
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [sum_wordsOfLength_succ (fun y => wordComp y f k z ^ 2) j]
    refine Finset.sum_congr rfl fun w _ => ?_
    show wordComp (true :: w) f k z ^ 2 + wordComp (false :: w) f k z ^ 2 = _
    rw [wordComp_true, wordComp_false]
  calc ‖iteratedFDeriv ℝ (j + 1) f z‖ ^ 2
      ≤ (∑ p ∈ (Finset.univ : Finset (Fin 2)) ×ˢ wordsOfLength (j + 1), |wordComp p.2 f p.1 z|) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ ((((Finset.univ : Finset (Fin 2)) ×ˢ wordsOfLength (j + 1)).card : ℕ) : ℝ) *
          ∑ p ∈ (Finset.univ : Finset (Fin 2)) ×ˢ wordsOfLength (j + 1),
            |wordComp p.2 f p.1 z| ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ 2 ^ (j + 2) * ∑ p ∈ (Finset.univ : Finset (Fin 2)) ×ˢ wordsOfLength (j + 1),
            |wordComp p.2 f p.1 z| ^ 2 :=
        mul_le_mul_of_nonneg_right hTR (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = 2 ^ (j + 2) * wordGradSq j f z := by rw [h3]

end UnforcedLeray.Short.PartI
