import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatMoments

/-!


Proves `HeatWBounds` (`Sub/T22_1/Stages.lean`). For `|g| cosh η ≤ B` and a kernel `k` with
`|k(z)| cosh z₂ ≤ G(z)`, `G` integrable, we have `cosh x₂ ≤ 2 cosh(x₂ - y₂) cosh y₂`, hence
`|k(x - y) g(y)| cosh x₂ ≤ 2 B G(x - y)`, and the convolution is bounded by `2 B ∫G` (translation
invariance of the integral). The two bounds then follow from `HeatKernelMoments`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.CylPDE

namespace HW

lemma cosh_split (s t : ℝ) : Real.cosh (s + t) ≤ 2 * (Real.cosh s * Real.cosh t) := by
  have h1 := Real.cosh_add s t
  have h2 := Real.cosh_sub s t
  have h3 := Real.cosh_pos (s - t)
  linarith

/-- Pointwise and integral bound for a convolution against the weight `cosh η`. -/
lemma conv_bound {k G g : Pl → ℝ} {B C : ℝ} (hB : 0 ≤ B) (hg : WB B g)
    (hG : ∀ z : Pl, |k z| * Real.cosh z.2 ≤ G z) (hGi : Integrable G) (hGC : ∫ z : Pl, G z ≤ C)
    (x : Pl) : |∫ y : Pl, k (x - y) * g y| * Real.cosh x.2 ≤ 2 * B * C := by
  have hc0 : ∀ t : ℝ, |Real.cosh t| = Real.cosh t := fun t => abs_of_pos (Real.cosh_pos t)
  have hpt : ∀ y : Pl, ‖k (x - y) * g y * Real.cosh x.2‖ ≤ 2 * B * G (x - y) := by
    intro y
    have hs : (x - y).2 = x.2 - y.2 := by simp
    have hcx : Real.cosh x.2 ≤ 2 * (Real.cosh (x - y).2 * Real.cosh y.2) := by
      rw [hs]
      have h := cosh_split (x.2 - y.2) y.2
      rw [sub_add_cancel] at h
      exact h
    have hA : 0 ≤ |k (x - y)| := abs_nonneg _
    have hgy : |g y| * Real.cosh y.2 ≤ B := hg y
    have h3 : |k (x - y)| * Real.cosh (x - y).2 ≤ G (x - y) := hG (x - y)
    have hcz : 0 < Real.cosh (x - y).2 := Real.cosh_pos _
    have hcy : 0 < Real.cosh y.2 := Real.cosh_pos _
    have h1 : |k (x - y)| * |g y| * Real.cosh x.2
        ≤ |k (x - y)| * |g y| * (2 * (Real.cosh (x - y).2 * Real.cosh y.2)) :=
      mul_le_mul_of_nonneg_left hcx (by positivity)
    have h2 : 2 * (|k (x - y)| * Real.cosh (x - y).2) * (|g y| * Real.cosh y.2)
        ≤ 2 * (|k (x - y)| * Real.cosh (x - y).2) * B :=
      mul_le_mul_of_nonneg_left hgy (by positivity)
    have h4 : 2 * (|k (x - y)| * Real.cosh (x - y).2) * B ≤ 2 * G (x - y) * B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by norm_num)) hB
    have heq : |k (x - y)| * |g y| * (2 * (Real.cosh (x - y).2 * Real.cosh y.2))
        = 2 * (|k (x - y)| * Real.cosh (x - y).2) * (|g y| * Real.cosh y.2) := by ring
    have heq2 : 2 * G (x - y) * B = 2 * B * G (x - y) := by ring
    simp only [norm_mul, Real.norm_eq_abs, hc0]
    linarith [h1, h2, h4, heq, heq2]
  have hM : Integrable (fun y : Pl => 2 * B * G (x - y)) :=
    (hGi.comp_sub_left x).const_mul (2 * B)
  calc |∫ y : Pl, k (x - y) * g y| * Real.cosh x.2
      = ‖∫ y : Pl, k (x - y) * g y * Real.cosh x.2‖ := by
        rw [integral_mul_const, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, hc0]
    _ ≤ ∫ y : Pl, 2 * B * G (x - y) :=
        norm_integral_le_of_norm_le hM (ae_of_all _ hpt)
    _ = 2 * B * ∫ y : Pl, G (x - y) := integral_const_mul _ _
    _ = 2 * B * ∫ y : Pl, G y := by rw [integral_sub_left_eq_self G]
    _ ≤ 2 * B * C := mul_le_mul_of_nonneg_left hGC (by linarith)

end HW

/-- **`T22/1/4`** The heat semigroup and the derivative kernel preserve the weight `cosh η`
(Stages.lean `HeatWBounds`). -/
theorem heatWBounds : UnforcedLeray.Short.IIb.CylPDE.HeatWBounds := by
  intro B g hg
  have hB : 0 ≤ B := by
    have h0 := hg 0
    simp only [Prod.snd_zero, Real.cosh_zero, mul_one] at h0
    exact le_trans (abs_nonneg _) h0
  constructor
  · intro a ha x
    unfold heatSG
    by_cases h : a ≤ 0
    · rw [if_pos h]
      have h1 : 1 ≤ Real.exp a := Real.one_le_exp ha
      have h2 : B ≤ 2 * Real.exp a * B := by nlinarith
      linarith [hg x]
    · rw [if_neg h]
      have ha' : 0 < a := not_le.1 h
      obtain ⟨hpos, hGi, _, hGc, hGint, _⟩ := heatKernelMoments a ha'
      have hG : ∀ z : Pl, |heatK a z| * Real.cosh z.2 ≤ (fun z : Pl => heatK a z * Real.cosh z.2) z :=
        fun z => le_of_eq (by simp only [abs_of_pos (hpos z)])
      have key := HW.conv_bound (k := heatK a) (G := fun z : Pl => heatK a z * Real.cosh z.2)
        (C := Real.exp a) hB hg hG hGc (le_of_eq hGint) x
      exact le_of_le_of_eq key (by ring)
  · intro a ha i x
    unfold heatSGd
    obtain ⟨_, _, _, _, _, hd⟩ := heatKernelMoments a ha
    obtain ⟨hHi, hHC⟩ := hd i
    have key := HW.conv_bound (k := heatKd i a) (G := fun z : Pl => |heatKd i a z| * Real.cosh z.2)
      (C := Real.exp a * (1 + a ^ (-(1 / 2 : ℝ)))) hB hg (fun z => le_refl _) hHi hHC x
    exact le_of_le_of_eq key (by ring)

end UnforcedLeray.Short.IIb.CylPDE
