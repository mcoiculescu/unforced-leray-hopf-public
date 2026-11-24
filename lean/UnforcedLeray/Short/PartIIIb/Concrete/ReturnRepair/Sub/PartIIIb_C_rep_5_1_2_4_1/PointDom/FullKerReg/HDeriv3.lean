import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.HDeriv2

/-!
# The `h`-derivative of the outward primitive along `w(h) = λ(h) z`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

theorem primPtH {K ρ₀ δ v b t Yq ν W : ℝ} (hK : 0 ≤ K) (hρ₀ : 0 ≤ ρ₀) (hδ : 0 < δ) (hv : δ ≤ v)
    (hν : 0 ≤ ν) (hY : 0 ≤ Yq) (ht : v ^ 2 + b ^ 2 ≤ t ^ 2) (ht0 : 0 ≤ t) (hW0 : 0 ≤ W) (hW : W ≤ t + Yq + v) :
    (ρ₀ + v) * (K * ((t ^ 4)⁻¹ + ν * (t ^ 6)⁻¹ + (t ^ 5)⁻¹ * W)) ≤
      ((ρ₀ / δ + 1) * (3 + ν * (δ ^ 2)⁻¹ + Yq / δ)) * K * (v * (((v ^ 2 + b ^ 2) ^ 2)⁻¹)) := by
  have hv0 : 0 < v := lt_of_lt_of_le hδ hv
  have hS0 : 0 < v ^ 2 + b ^ 2 := by positivity
  set S := v ^ 2 + b ^ 2 with hSdef
  have hSδ : δ ^ 2 ≤ S := by nlinarith [sq_nonneg b]
  have htδ : δ ≤ t := by
    by_contra hlt
    push Not at hlt
    nlinarith
  have htv : v ≤ t := by nlinarith [sq_nonneg b]
  have ht0' : 0 < t := lt_of_lt_of_le hδ htδ
  set m := ρ₀ / δ + 1 with hm
  have hρ : ρ₀ + v ≤ m * v := by
    have : ρ₀ ≤ ρ₀ / δ * v := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]; nlinarith
    rw [hm]; nlinarith
  have hS2 : 0 < S ^ 2 := by positivity
  have ht4 : S ^ 2 ≤ t ^ 4 := by nlinarith
  set P := (S ^ 2)⁻¹ with hP
  have hP0 : 0 < P := by positivity
  have i4 : (t ^ 4)⁻¹ ≤ P := inv_anti₀ hS2 ht4
  have t4pos : 0 < t ^ 4 := by positivity
  have i5 : (t ^ 5)⁻¹ ≤ P * δ⁻¹ := by
    have h5 : S ^ 2 * δ ≤ t ^ 5 := by
      have : t ^ 5 = t ^ 4 * t := by ring
      rw [this]; exact mul_le_mul ht4 htδ hδ.le (by positivity)
    refine (inv_anti₀ (by positivity) h5).trans (le_of_eq ?_)
    rw [mul_inv]
  have i6 : (t ^ 6)⁻¹ ≤ P * (δ ^ 2)⁻¹ := by
    have h6 : S ^ 2 * δ ^ 2 ≤ t ^ 6 := by
      have : t ^ 6 = t ^ 4 * t ^ 2 := by ring
      rw [this]; exact mul_le_mul ht4 (by nlinarith) (by positivity) (by positivity)
    refine (inv_anti₀ (by positivity) h6).trans (le_of_eq ?_)
    rw [mul_inv]
  have i5v : (t ^ 5)⁻¹ * v ≤ P := by
    calc (t ^ 5)⁻¹ * v ≤ (t ^ 5)⁻¹ * t := mul_le_mul_of_nonneg_left htv (by positivity)
      _ = (t ^ 4)⁻¹ := by field_simp
      _ ≤ P := i4
  have hW' : (t ^ 5)⁻¹ * W ≤ (t ^ 5)⁻¹ * (t + Yq + v) :=
    mul_le_mul_of_nonneg_left hW (by positivity)
  have e5 : (t ^ 5)⁻¹ * (t + Yq + v) = (t ^ 4)⁻¹ + Yq * (t ^ 5)⁻¹ + (t ^ 5)⁻¹ * v := by
    field_simp
  have b5 : Yq * (t ^ 5)⁻¹ ≤ Yq * (P * δ⁻¹) := mul_le_mul_of_nonneg_left i5 hY
  have tot : (t ^ 4)⁻¹ + ν * (t ^ 6)⁻¹ + (t ^ 5)⁻¹ * W ≤
      P * (3 + ν * (δ ^ 2)⁻¹ + Yq / δ) := by
    have : ν * (t ^ 6)⁻¹ ≤ ν * (P * (δ ^ 2)⁻¹) := mul_le_mul_of_nonneg_left i6 hν
    have hY' : Yq * (P * δ⁻¹) = P * (Yq / δ) := by field_simp
    nlinarith
  calc (ρ₀ + v) * (K * ((t ^ 4)⁻¹ + ν * (t ^ 6)⁻¹ + (t ^ 5)⁻¹ * W))
      ≤ (m * v) * (K * (P * (3 + ν * (δ ^ 2)⁻¹ + Yq / δ))) :=
        mul_le_mul hρ (mul_le_mul_of_nonneg_left tot hK) (by positivity) (by positivity)
    _ = (m * (3 + ν * (δ ^ 2)⁻¹ + Yq / δ)) * K * (v * P) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
