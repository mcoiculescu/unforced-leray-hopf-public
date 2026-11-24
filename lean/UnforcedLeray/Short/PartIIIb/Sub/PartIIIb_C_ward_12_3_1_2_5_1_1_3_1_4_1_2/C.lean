import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1_2

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1/1/3/1/4/1/2/3`: `zeroFromGrad`

Pure calculus. For `0 < s ≤ s₀`, compare `(s, q, η)` with the point `(s₀, q, 0)` along a segment
inside the convex open set `(0,∞) × ℝ²`; the distance is at most `s₀ + |η|`, and the value at the
comparison point is `f s₀ 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- **Target** `zeroFromGrad`: zero order from first order (mean value theorem on `s > 0`). -/
theorem zeroFromGrad : ZeroFromGrad := by
  intro f C₁ hf hC s₀ hs₀ y hy hys
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have hconv : Convex ℝ (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := (convex_Ioi 0).prod convex_univ
  have hcomp : ContDiff ℝ ∞ (fun x : ℝ × Plane => ((x.1, x.2.2) : ℝ × ℝ)) :=
    contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
  have hmaps : MapsTo (fun x : ℝ × Plane => ((x.1, x.2.2) : ℝ × ℝ))
      (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :=
    fun x hx => ⟨hx.1, mem_univ _⟩
  have hΦs : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => f x.1 x.2.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := hf.comp hcomp.contDiffOn hmaps
  have hdiff : ∀ x ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane),
      DifferentiableAt ℝ (fun x : ℝ × Plane => f x.1 x.2.2) x := fun x hx =>
    (hΦs.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hbound : ∀ x ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane),
      ‖fderiv ℝ (fun x : ℝ × Plane => f x.1 x.2.2) x‖ ≤ C₁ := fun x hx => by
    rw [← norm_iteratedFDeriv_one]
    exact hC x hx.1
  -- `C₁ ≥ 0`, from the bound at the point `(1, (0, 0))`
  have hC0 : 0 ≤ C₁ := by
    have h := hC (1, (0, 0)) (by norm_num)
    exact le_trans (norm_nonneg _) h
  -- the comparison point `(s₀, q, 0)`
  have hx0 : ((s₀, (y.2.1, (0 : ℝ))) : ℝ × Plane) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane) :=
    ⟨hs₀, mem_univ _⟩
  have hy' : y ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane) := ⟨hy, mem_univ _⟩
  have h1 : ‖f y.1 y.2.2 - f s₀ 0‖ ≤ C₁ * ‖y - ((s₀, (y.2.1, (0 : ℝ))) : ℝ × Plane)‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound hconv hx0 hy'
  have hnorm : ‖y - ((s₀, (y.2.1, (0 : ℝ))) : ℝ × Plane)‖ ≤ s₀ + |y.2.2| := by
    rw [Prod.norm_def]
    apply max_le
    · rw [Prod.fst_sub, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [abs_nonneg y.2.2, le_abs_self y.2.2, neg_abs_le y.2.2]
    · rw [Prod.snd_sub, Prod.norm_def]
      apply max_le
      · simp
        linarith [abs_nonneg y.2.2]
      · rw [Prod.snd_sub, Real.norm_eq_abs]
        simp only [sub_zero]
        linarith [abs_nonneg y.2.2, le_abs_self y.2.2]
  have h2 : C₁ * ‖y - ((s₀, (y.2.1, (0 : ℝ))) : ℝ × Plane)‖ ≤ C₁ * (s₀ + |y.2.2|) :=
    mul_le_mul_of_nonneg_left hnorm hC0
  have h3 := abs_sub_abs_le_abs_sub (f y.1 y.2.2) (f s₀ 0)
  rw [Real.norm_eq_abs] at h1
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete
