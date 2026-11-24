import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1_5
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# `lipOffPoint` (`PartIII-b:C/rep/2/6/3/2/1/5/9`)

Source `shorter-proof-2026-11-02.tex` lines 3603-3626, 3800-3807, 4171-4200.

Lipschitz bound for a continuous function on an open interval whose derivative is bounded by `B`
off one point `s₀`. The segment `[x, y]` is split at `s₀` when `s₀ ∈ [x, y]`. The piece `[x, s₀]`
has its exceptional point at the right end, and the piece `[s₀, y]` has it at the left end. The
left-end piece is reduced to the right-end case by the reflection `u ↦ a - u`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Right-end version: the derivative bound holds on `[a, b)` with right derivatives. -/
theorem lipOffAux_right (f f' : ℝ → ℂ) (a b B : ℝ) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (hB : ∀ t ∈ Ico a b, ‖f' t‖ ≤ B) (hab : a ≤ b) :
    ‖f b - f a‖ ≤ B * (b - a) :=
  norm_image_sub_le_of_norm_deriv_right_le_segment hc hd hB b (right_mem_Icc.2 hab)

/-- Left-end version: the derivative bound holds on `(a, b]`; the point `a` is not needed. -/
theorem lipOffAux_left (f f' : ℝ → ℂ) (a b B : ℝ) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioc a b, HasDerivAt f (f' t) t)
    (hB : ∀ t ∈ Ioc a b, ‖f' t‖ ≤ B) (hab : a ≤ b) :
    ‖f a - f b‖ ≤ B * (b - a) := by
  have hcont0 : Continuous (fun u : ℝ => a - u) := by fun_prop
  have hcont : ContinuousOn (fun u : ℝ => a - u) (Icc (a - b) 0) := hcont0.continuousOn
  have hmap : MapsTo (fun u : ℝ => a - u) (Icc (a - b) 0) (Icc a b) := by
    intro u hu
    simp only [mem_Icc] at hu ⊢
    constructor <;> linarith [hu.1, hu.2]
  have hgc : ContinuousOn (fun u : ℝ => f (a - u)) (Icc (a - b) 0) := hc.comp hcont hmap
  have hmem : ∀ u ∈ Ico (a - b) 0, a - u ∈ Ioc a b := by
    intro u hu
    simp only [mem_Ico, mem_Ioc] at hu ⊢
    constructor <;> linarith [hu.1, hu.2]
  have hdg : ∀ u ∈ Ico (a - b) 0,
      HasDerivWithinAt (fun u : ℝ => f (a - u)) (-(f' (a - u))) (Ici u) u := by
    intro u hu
    exact (HasDerivAt.comp_const_sub a u (hd (a - u) (hmem u hu))).hasDerivWithinAt
  have hbg : ∀ u ∈ Ico (a - b) 0, ‖-(f' (a - u))‖ ≤ B := by
    intro u hu
    rw [norm_neg]
    exact hB _ (hmem u hu)
  have hA := norm_image_sub_le_of_norm_deriv_right_le_segment (f' := fun u => -(f' (a - u)))
    hgc hdg hbg 0 ⟨by linarith, le_rfl⟩
  simp only [sub_zero, sub_sub_cancel] at hA
  calc ‖f a - f b‖ ≤ B * (0 - (a - b)) := hA
    _ = B * (b - a) := by ring

/-- Lipschitz estimate on `[x, y] ⊆ (a, b)` for `x ≤ y`. -/
theorem lipOffAux_dist (f f' : ℝ → ℂ) (s₀ a b B : ℝ) (hB : 0 ≤ B)
    (hc : ContinuousOn f (Ioo a b))
    (hd : ∀ t ∈ Ioo a b, t ≠ s₀ → HasDerivAt f (f' t) t)
    (hbd : ∀ t ∈ Ioo a b, t ≠ s₀ → ‖f' t‖ ≤ B) (x y : ℝ)
    (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) (hxy : x ≤ y) :
    ‖f y - f x‖ ≤ B * (y - x) := by
  have hsub : Icc x y ⊆ Ioo a b := Icc_subset_Ioo hx.1 hy.2
  have hcI : ∀ p q : ℝ, x ≤ p → q ≤ y → ContinuousOn f (Icc p q) := by
    intro p q hp hq
    exact hc.mono (fun t ht => hsub ⟨le_trans hp ht.1, le_trans ht.2 hq⟩)
  by_cases hs : s₀ ∈ Icc x y
  · obtain ⟨hs1, hs2⟩ := hs
    have h1 : ‖f s₀ - f x‖ ≤ B * (s₀ - x) := by
      refine lipOffAux_right f f' x s₀ B (hcI x s₀ le_rfl hs2) ?_ ?_ hs1
      · intro t ht
        have htI : t ∈ Ioo a b := hsub ⟨ht.1, by linarith [ht.2]⟩
        exact (hd t htI ht.2.ne).hasDerivWithinAt
      · intro t ht
        exact hbd t (hsub ⟨ht.1, by linarith [ht.2]⟩) ht.2.ne
    have h2 : ‖f s₀ - f y‖ ≤ B * (y - s₀) := by
      refine lipOffAux_left f f' s₀ y B (hcI s₀ y hs1 le_rfl) ?_ ?_ hs2
      · intro t ht
        have htI : t ∈ Ioo a b := ⟨by linarith [ht.1, hx.1], by linarith [ht.2, hy.2]⟩
        exact hd t htI ht.1.ne'
      · intro t ht
        have htI : t ∈ Ioo a b := ⟨by linarith [ht.1, hx.1], by linarith [ht.2, hy.2]⟩
        exact hbd t htI ht.1.ne'
    have key : f y - f x = -(f s₀ - f y) + (f s₀ - f x) := by ring
    rw [key]
    calc ‖-(f s₀ - f y) + (f s₀ - f x)‖ ≤ ‖-(f s₀ - f y)‖ + ‖f s₀ - f x‖ := norm_add_le _ _
      _ = ‖f s₀ - f y‖ + ‖f s₀ - f x‖ := by rw [norm_neg]
      _ ≤ B * (y - s₀) + B * (s₀ - x) := add_le_add h2 h1
      _ = B * (y - x) := by ring
  · have hne : ∀ t ∈ Ico x y, t ≠ s₀ := fun t ht h =>
      hs ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine lipOffAux_right f f' x y B (hcI x y le_rfl le_rfl) ?_ ?_ hxy
    · intro t ht
      exact (hd t (hsub ⟨ht.1, ht.2.le⟩) (hne t ht)).hasDerivWithinAt
    · intro t ht
      exact hbd t (hsub ⟨ht.1, ht.2.le⟩) (hne t ht)

theorem lipOffPoint : LipOffPoint := by
  unfold LipOffPoint
  intro f f' s₀ a b B hB hc hd hbd
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro x hx y hy
  rw [Real.coe_nnabs, abs_of_nonneg hB, dist_eq_norm, dist_eq_norm]
  rcases le_total x y with hxy | hxy
  · have h := lipOffAux_dist f f' s₀ a b B hB hc hd hbd x y hx hy hxy
    rw [norm_sub_rev (f x) (f y), norm_sub_rev x y,
      Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ y - x)]
    exact h
  · have h := lipOffAux_dist f f' s₀ a b B hB hc hd hbd y x hy hx hxy
    rw [Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ x - y)]
    exact h

end UnforcedLeray.Short.PartIIIb.Concrete
