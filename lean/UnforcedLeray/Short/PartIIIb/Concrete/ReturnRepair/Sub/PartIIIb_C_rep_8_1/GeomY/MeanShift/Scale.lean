import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.MeanShift.Deriv
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.NewtonD3

/-!
# Homogeneity of the inner integral and the dilation derivative (source 4776-4782)

`G(t,y) = t⁻⁴ G(1, y/t)` (degree `-4` homogeneity of `newtonD3`), hence
`t ∂_t G(t,x) = -4 G(t,x) - x·∇_x G(t,x)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem cyl_smul_gt {ν t : ℝ} (hν : 0 < ν) (ht : t ∈ Ioc (0 : ℝ) 1) {y : Vec3}
    (hy : 5 * ν / 6 < y 0 ^ 2 + y 1 ^ 2) :
    5 * ν / 6 < (t⁻¹ • y) 0 ^ 2 + (t⁻¹ • y) 1 ^ 2 := by
  have h1 : (t⁻¹ • y) 0 ^ 2 + (t⁻¹ • y) 1 ^ 2 = (t⁻¹) ^ 2 * (y 0 ^ 2 + y 1 ^ 2) := by
    simp [mul_pow]; ring
  rw [h1]
  have hge : 1 ≤ (t⁻¹) ^ 2 := by
    have : 1 ≤ t⁻¹ := one_le_inv_iff₀.2 ⟨ht.1, ht.2⟩
    nlinarith
  have hpos : 0 < y 0 ^ 2 + y 1 ^ 2 := lt_trans (by positivity) hy
  nlinarith

theorem famF_scale {c ν : ℝ} {χo : ℝ → ℝ} {M : Chart → Mat3} (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (i : Fin 3) {y : Vec3}
    (hy : 5 * ν / 6 < y 0 ^ 2 + y 1 ^ 2) (a : ℝ × ℝ) :
    NewtonFam.famF c ν χo M t i a y =
      (t⁻¹ / t / t / t) * NewtonFam.famF c ν χo M 1 i a (t⁻¹ • y) := by
  by_cases ha : a.1 ^ 2 + a.2 ^ 2 < 5 * ν / 6
  · have hw : t⁻¹ • y - (1 : ℝ) • embPlane a ≠ 0 :=
      NewtonFam.kernel_arg_ne_zero (t⁻¹ • y) a 1 (5 * ν / 6) zero_le_one le_rfl ha
        (cyl_smul_gt hν ht hy)
    have e : y - t • embPlane a = t • (t⁻¹ • y - (1 : ℝ) • embPlane a) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ ht.1.ne', one_smul]
      simp
    unfold NewtonFam.famF
    rw [e]
    simp only [NewtonD3.newtonD3_smul ht.1 hw, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  · have h0 : sigmaM c ν χo M a = 0 :=
      sigmaM_eq_zero_of_ge c ν χo M hν hχ a (not_lt.1 ha)
    simp [NewtonFam.famF, h0]

theorem Gint_scale {c ν : ℝ} {χo : ℝ → ℝ} {M : Chart → Mat3} (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (i : Fin 3) {y : Vec3}
    (hy : 5 * ν / 6 < y 0 ^ 2 + y 1 ^ 2) :
    Gint c ν χo M t i y = (t ^ 4)⁻¹ * Gint c ν χo M 1 i (t⁻¹ • y) := by
  unfold Gint
  rw [← integral_const_mul]
  have hk : t⁻¹ / t / t / t = (t ^ 4)⁻¹ := by
    have := ht.1.ne'
    field_simp
  simp_rw [← hk]
  exact integral_congr_ae (Filter.Eventually.of_forall fun a => famF_scale hν hχ ht i hy a)

end UnforcedLeray.Short.PartIIIb.Concrete
