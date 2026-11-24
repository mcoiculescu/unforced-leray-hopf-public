import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_2_2

/-!
# `PartIII-b:C/grad/3/5/2/2` task 1c: jet bounds of `exp(-f)`

Source `the November 2 reference manuscript`
5063-5079 (Gaussian jet bound).  Faà di Bruno (`norm_iteratedFDerivWithin_comp_le`) with the outer
map `t ↦ exp(-t)`, whose derivatives of all orders are bounded by `exp(-t)`, and the inner map `f`
with derivative bounds `D^i`, gives `‖D^k exp(-f)‖ ≤ k! exp(-T) D^k`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem expNegCompJets {U : Set Chart} (hUo : IsOpen U) (f : Chart → ℝ) (hf : ContDiffOn ℝ 3 f U) (T D : ℝ) (hD : 1 ≤ D) (hT : ∀ p ∈ U, T ≤ f p) (hDf : ∀ p ∈ U, ∀ i : ℕ, 1 ≤ i → i ≤ 3 → ‖iteratedFDerivWithin ℝ i f U p‖ ≤ D ^ i) : ∀ k : ℕ, k ≤ 3 → ∀ p ∈ U, ‖iteratedFDerivWithin ℝ k (fun q : Chart => Real.exp (-f q)) U p‖ ≤ (k.factorial : ℝ) * Real.exp (-T) * D ^ k := by
  -- derivatives of all orders of `t ↦ exp(-t)` on `ℝ`
  have hderiv : ∀ n : ℕ, ∀ x : ℝ,
      ‖iteratedFDerivWithin ℝ n (fun t : ℝ => Real.exp (-t)) univ x‖ ≤ Real.exp (-x) := by
    intro n x
    rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have h2 : (fun t : ℝ => Real.exp (-t)) = fun s => Real.exp ((-1 : ℝ) * s) := by
      funext s
      ring_nf
    have h := iteratedDeriv_exp_const_mul n (-1 : ℝ)
    rw [h2, h]
    simp [Real.norm_eq_abs, Real.abs_exp]
  have hg : ContDiff ℝ 3 (fun t : ℝ => Real.exp (-t)) := by fun_prop
  intro k hk p hp
  have hkN : (k : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  have hC : ∀ i : ℕ, i ≤ k →
      ‖iteratedFDerivWithin ℝ i (fun t : ℝ => Real.exp (-t)) univ (f p)‖ ≤ Real.exp (-T) := by
    intro i _
    refine (hderiv i (f p)).trans ?_
    exact Real.exp_le_exp.2 (neg_le_neg (hT p hp))
  have hD' : ∀ i : ℕ, 1 ≤ i → i ≤ k → ‖iteratedFDerivWithin ℝ i f U p‖ ≤ D ^ i :=
    fun i h1 h2 => hDf p hp i h1 (h2.trans hk)
  have key := norm_iteratedFDerivWithin_comp_le (g := fun t : ℝ => Real.exp (-t)) (f := f)
    (s := U) (t := univ) (x := p) (N := 3) hg.contDiffOn hf (hkN) uniqueDiffOn_univ
    hUo.uniqueDiffOn (mapsTo_univ f U) hp hC hD'
  exact key

end UnforcedLeray.Short.PartIIIb.Concrete
