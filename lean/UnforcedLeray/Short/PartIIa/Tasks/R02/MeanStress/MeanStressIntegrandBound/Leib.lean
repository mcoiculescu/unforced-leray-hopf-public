import UnforcedLeray.Short.PartIIa.Sub.R02_6
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanStress.MeanStressIntegrandBound.Term

/-!
# Part II-a, helper for `PartII-a:R02/MeanStress/MeanStressIntegrandBound`: the Leibniz sum

Source of record: `the November 2 reference manuscript`, lines 397-404 and 439-446.

Helper file for `Short/PartII-a/Tasks/R02/MeanStress/MeanStressIntegrandBound.lean`. It proves

* `leib_inst`: the Leibniz expansion `MixedLeibniz` applied to the two fluctuation components
  `ṽ_j = hfluct c (v_j)` (smooth for `s > 0` by `MeanStressSmooth`), reindexed by `meanPairs`;
* `abs_sum_mul_le`: the elementary bound `K |∑ F| ≤ ∑ K |F|`;
* `leib_abs_le`: the weighted absolute mixed derivative of `ṽ₁ṽ₂` is bounded by the sum over
  `meanPairs` of `|binomial coefficients| · termVal`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- **Leibniz expansion of the fluctuation product.** For `s > 0`,
`∂_η^a ∂_s^k (ṽ₁ṽ₂)(q, η) = ∑_{(i',l')} C(a,i') C(k,l') ∂_η^{i'}∂_s^{l'} ṽ₁ · ∂_η^{a-i'}∂_s^{k-l'} ṽ₂`,
with `ṽ_j = hfluct c (fun w => tr.v r w j)` at the point `(q, e)`. -/
theorem leib_inst (hL : MixedLeibniz) (hSm : MeanStressSmooth) (ρ ν : ℝ) (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ))) (hb : UnforcedLeray.Short.PartI.IsBUCTrain tr) (q s η : ℝ) (hs : 0 < s)
    (a k : ℕ) :
    iteratedDeriv a (fun e => iteratedDeriv k (fun r => fluctProd tr r (q, e)) s) η =
      ∑ p ∈ meanPairs a k, ((a.choose p.1 : ℝ) * (k.choose p.2 : ℝ)) *
        (iteratedDeriv p.1 (fun e => iteratedDeriv p.2
            (fun r => UnforcedLeray.Short.PartI.hfluct (ν ^ (-ρ)) (fun w => tr.v r w 0) (q, e)) s) η *
          iteratedDeriv (a - p.1) (fun e => iteratedDeriv (k - p.2)
            (fun r => UnforcedLeray.Short.PartI.hfluct (ν ^ (-ρ)) (fun w => tr.v r w 1) (q, e)) s) η) := by
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
  have hg : ContDiff ℝ ∞ (fun x : ℝ × ℝ => ((x.1, (q, x.2)) : ℝ × (ℝ × ℝ))) :=
    contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)
  have hA : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.hfluct (ν ^ (-ρ)) (fun w => tr.v x.1 w 0) (q, x.2))
      (Ioi 0 ×ˢ univ) :=
    ((hSm ν (ν ^ (-ρ)) hν hc tr hb).2.2 0).comp hg.contDiffOn
      (fun x hx => ⟨(Set.mem_prod.mp hx).1, Set.mem_univ _⟩)
  have hB : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.hfluct (ν ^ (-ρ)) (fun w => tr.v x.1 w 1) (q, x.2))
      (Ioi 0 ×ˢ univ) :=
    ((hSm ν (ν ^ (-ρ)) hν hc tr hb).2.2 1).comp hg.contDiffOn
      (fun x hx => ⟨(Set.mem_prod.mp hx).1, Set.mem_univ _⟩)
  have hL' := hL
    (fun r e => UnforcedLeray.Short.PartI.hfluct (ν ^ (-ρ)) (fun w => tr.v r w 0) (q, e))
    (fun r e => UnforcedLeray.Short.PartI.hfluct (ν ^ (-ρ)) (fun w => tr.v r w 1) (q, e))
    hA hB a k s η hs
  refine hL'.trans ?_
  unfold meanPairs
  rw [Finset.sum_product]

/-- Elementary: a constant times the absolute value of a finite sum is bounded termwise. -/
theorem abs_sum_mul_le {β : Type*} (S : Finset β) (K : ℝ) (hK : 0 ≤ K) (F G : β → ℝ)
    (hG : ∀ p ∈ S, K * |F p| ≤ G p) :
    K * |∑ p ∈ S, F p| ≤ ∑ p ∈ S, G p := by
  calc K * |∑ p ∈ S, F p| ≤ K * ∑ p ∈ S, |F p| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hK
    _ = ∑ p ∈ S, K * |F p| := by rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ S, G p := Finset.sum_le_sum hG

/-- **Leibniz sum bound.** The weighted absolute mixed derivative of `ṽ₁ṽ₂` at `s > 0` is bounded
by the sum over `meanPairs (i+a) k` of the absolute Leibniz coefficients times the term values
`termVal`. -/
theorem leib_abs_le (hL : MixedLeibniz) (hSm : MeanStressSmooth) (ρ ν : ℝ) (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ))) (hb : UnforcedLeray.Short.PartI.IsBUCTrain tr) (q s η : ℝ) (hs0 : 0 < s)
    (m i a k : ℕ) :
    (1 + η ^ 2 / s) ^ m * (|η| ^ i * s ^ k *
        |iteratedDeriv (i + a) (fun e => iteratedDeriv k (fun r => fluctProd tr r (q, e)) s) η|) ≤
      ∑ p ∈ meanPairs (i + a) k,
        |((i + a).choose p.1 : ℝ) * (k.choose p.2 : ℝ)| * termVal ρ m i a k p ν tr q η s := by
  rw [leib_inst hL hSm ρ ν hν tr hb q s η hs0 (i + a) k, ← mul_assoc]
  have hη : 0 ≤ 1 + η ^ 2 / s := by
    have := div_nonneg (sq_nonneg η) hs0.le
    linarith
  have hK : 0 ≤ (1 + η ^ 2 / s) ^ m * (|η| ^ i * s ^ k) :=
    mul_nonneg (pow_nonneg hη m) (mul_nonneg (pow_nonneg (abs_nonneg _) i) (pow_nonneg hs0.le k))
  refine le_trans (abs_sum_mul_le (meanPairs (i + a) k) _ hK _ _ fun p _ => ?_) le_rfl
  simp only [abs_mul]
  unfold termVal
  apply le_of_eq
  ring

end UnforcedLeray.Short.PartIIa
