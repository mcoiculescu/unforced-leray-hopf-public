import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GWQ.Calc4

/-!
# `PartII-b:T10/7/1/2/4` (`GWQ`) helper: the pointwise identity `Σ_j -∂_j Φ_j = (lift of Q_ε^T φ) e_i`
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.GWQ

open UnforcedLeray UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

theorem ctLift_comb {c ε b : ℝ} (hc : 0 < c) (hε : 0 < ε) {φ : Coord → ℝ} (hφ : IsCoordTest φ)
    {ψ : Coord → ℝ} (hψ : ∀ p, ψ p ≠ 0 → p ∈ tsupport φ) {x : ℝ × Space}
    (hy : x.2 ∉ Axi.axis) :
    ctLift c ε b ψ x + ε * ctLift c ε b φ x =
      ctLift c ε b (fun m => ψ m + ε * φ m) x := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  obtain ⟨N1, h1⟩ := finite_of_tsupport (a := b) hc hR hφ (ψ := ψ) hψ hy
  obtain ⟨N2, h2⟩ := finite_of_tsupport (a := b) hc hR hφ (ψ := φ) (fun p hp => subset_tsupport φ hp) hy
  have e1 := h1.self_of_nhds
  have e2 := h2.self_of_nhds
  have hlin : ∀ n, termR c ε⁻¹ b (fun m => ψ m + ε * φ m) n x =
      termR c ε⁻¹ b ψ n x + ε * termR c ε⁻¹ b φ n x := by
    intro n; unfold termR; ring
  have hz : ∀ n ∉ N1 ∪ N2, termR c ε⁻¹ b (fun m => ψ m + ε * φ m) n x = 0 := by
    intro n hn
    rw [hlin, e1 n (fun h => hn (Finset.mem_union_left _ h)),
      e2 n (fun h => hn (Finset.mem_union_right _ h))]
    ring
  rw [ctLift_eq_tsum, ctLift_eq_tsum, ctLift_eq_tsum,
    tsum_eq_sum (s := N1 ∪ N2) (fun n hn => hz n hn),
    tsum_eq_sum (s := N1 ∪ N2) (f := fun n => termR c ε⁻¹ b ψ n x)
      (fun n hn => e1 n (fun h => hn (Finset.mem_union_left _ h))),
    tsum_eq_sum (s := N1 ∪ N2) (f := fun n => termR c ε⁻¹ b φ n x)
      (fun n hn => e2 n (fun h => hn (Finset.mem_union_right _ h)))]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun n _ => (hlin n).symm)

theorem ctLift_neg {c ε b : ℝ} (ψ : Coord → ℝ) (x : ℝ × Space) :
    ctLift c ε b (fun m => -ψ m) x = -ctLift c ε b ψ x := by
  unfold ctLift
  rw [← tsum_neg]
  congr 1
  funext n
  ring

theorem sum_neg_dy_tst {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) {φ : Coord → ℝ} (hφ : IsCoordTest φ)
    (i : Fin 2) {x : ℝ × Space} (hy : x.2 ∉ Axi.axis) :
    ∑ j : Fin 3, (-(dy j (tst c ε (3 / 2) φ i j) x)) =
      (ctLift c ε 2 (coordTranspose (vQ ε) (dQ ε) φ) x) • realCL (Evec i x.2) := by
  rw [Finset.sum_neg_distrib, sum_dy_tst hc hε hφ i hy, ctLift_half hε φ hy]
  have hrad := ct_deriv_radial (a := 3 / 2) hc hε hφ x.1 x.2 hy
  have hψ : ∀ p : Coord, (cpd 1 φ p - ε * (2 * p.1 * cpd 0 φ p + p.2.2 * cpd 2 φ p) -
      2 * (3 / 2) * ε * φ p) ≠ 0 → p ∈ tsupport φ := by
    intro p hp
    by_contra hn
    obtain ⟨h1, h0, h2, hq⟩ := coordT_zero_of_out ε hn
    apply hp
    rw [h1, h0, h2, hq]; ring
  have hcomb := ctLift_comb (b := 3 / 2 + 1 / 2) hc hε hφ hψ hy
  have hT : (fun m : Coord => (cpd 1 φ m - ε * (2 * m.1 * cpd 0 φ m + m.2.2 * cpd 2 φ m) -
      2 * (3 / 2) * ε * φ m) + ε * φ m) =
      fun m => -coordTranspose (vQ ε) (dQ ε) φ m := by
    funext m
    rw [coordT_eq hφ ε]; ring
  rw [hT, ctLift_neg] at hcomb
  have h2 : (3 / 2 + 1 / 2 : ℝ) = 2 := by norm_num
  rw [h2] at hcomb hrad
  simp only [Prod.mk.eta] at hrad
  rw [h2, hrad, add_comm (ε * _), hcomb, neg_smul, neg_neg]

end UnforcedLeray.Short.IIb.GWQ
