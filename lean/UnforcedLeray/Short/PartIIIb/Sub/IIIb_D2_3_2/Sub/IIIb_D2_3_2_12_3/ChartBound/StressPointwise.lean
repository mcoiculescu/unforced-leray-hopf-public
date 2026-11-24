import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_12_3_1_4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.ChartBound.Leaf1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.ChartBound.NsSymBound
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.ChartBound.DyBound

/-!
# `PartIII-b:IIIb-D2/3/2/12/3/1/4`: proof of `StressPointwise` (leaf A)

Source of record: `the November 2 reference manuscript`,
lines 2683, 2698-2700, 3256-3268, 4284-4286.

Uses `strPhysAbsLe_proved` (leaf 1), `nsSym_abs_le_norm` (`|nsSym T a b| ≤ C ‖T‖`), and
`dy_phaseTest_bound` (leaf 2: `‖dy j Φ x i‖ ≤ B'`, `dy j Φ x = 0` for `‖x.2‖ > Y`).
The constant is `B := 81 * |C| * B'`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **Leaf A** (source 2683, 2698-2700, 4284-4286): pointwise bound of the stress integrand. -/
theorem stressPointwise_proof : UnforcedLeray.Short.PartIIIb.Concrete.StressPointwise := by
  intro R c P Y Φ hR hc hP hY hΦ hsupp
  have hP0 : 0 < P := by
    rw [hP]
    exact div_pos (mul_pos two_pos hc) hR
  obtain ⟨C, hC⟩ := nsSym_abs_le_norm
  obtain ⟨B', hB'0, hB'dy, hB'zero⟩ := dy_phaseTest_bound P Y hP0 Φ hΦ hsupp
  refine ⟨81 * |C| * B', by positivity, ?_⟩
  intro g x
  by_cases hy : ‖x.2‖ ≤ Y
  · -- inside the ball: use the entrywise bound on `strPhys`
    have hs : 0 ≤ (NearInst.chartOf R c x.2 x.1).1 := by
      show 0 ≤ R ^ 2 / NearInst.hRad x.2 ^ 2
      positivity
    have hent : ∀ i j : Fin 3,
        |strPhys R c g x i j| ≤ (NearInst.chartOf R c x.2 x.1).1 *
          (9 * (|C| * ‖g (NearInst.chartOf R c x.2 x.1)‖)) := by
      intro i j
      have h1 := strPhysAbsLe_proved R c g x i j
      have each : ∀ a b : Fin 3,
          |NearInst.nsSym (g (NearInst.chartOf R c x.2 x.1)) a b| ≤
            |C| * ‖g (NearInst.chartOf R c x.2 x.1)‖ := fun a b =>
        (hC (g (NearInst.chartOf R c x.2 x.1)) a b).trans
          (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))
      have hsum : ∑ a : Fin 3, ∑ b : Fin 3, |NearInst.nsSym (g (NearInst.chartOf R c x.2 x.1)) a b|
          ≤ 9 * (|C| * ‖g (NearInst.chartOf R c x.2 x.1)‖) := by
        calc ∑ a : Fin 3, ∑ b : Fin 3, |NearInst.nsSym (g (NearInst.chartOf R c x.2 x.1)) a b|
            ≤ ∑ a : Fin 3, ∑ b : Fin 3, |C| * ‖g (NearInst.chartOf R c x.2 x.1)‖ :=
              Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => each a b
          _ = 9 * (|C| * ‖g (NearInst.chartOf R c x.2 x.1)‖) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              push_cast
              ring
      exact h1.trans (mul_le_mul_of_nonneg_left hsum hs)
    have hterm : ∀ i j : Fin 3,
        ‖((strPhys R c g x i j : ℝ) : ℂ) * dy j Φ x i‖ ≤
          (NearInst.chartOf R c x.2 x.1).1 * (9 * (|C| * ‖g (NearInst.chartOf R c x.2 x.1)‖)) * B' := by
      intro i j
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hent i j) (hB'dy x j i) (norm_nonneg _)
        (mul_nonneg hs (by positivity))
    have hball : stressBall R c Y g x =
        (NearInst.chartOf R c x.2 x.1).1 * ‖g (NearInst.chartOf R c x.2 x.1)‖ := by
      unfold stressBall
      rw [if_pos hy]
    rw [hball]
    calc ‖stressF R c g Φ x‖
        ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖((strPhys R c g x i j : ℝ) : ℂ) * dy j Φ x i‖ := by
          unfold stressF
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
            (NearInst.chartOf R c x.2 x.1).1 * (9 * (|C| * ‖g (NearInst.chartOf R c x.2 x.1)‖)) * B' :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = (81 * |C| * B') * ((NearInst.chartOf R c x.2 x.1).1 *
            ‖g (NearInst.chartOf R c x.2 x.1)‖) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  · -- outside the ball: `Φ` vanishes near `x`, so the integrand vanishes
    have hgt : Y < ‖x.2‖ := not_le.mp hy
    have hz : ∀ j : Fin 3, dy j Φ x = 0 := fun j => hB'zero x j hgt
    have h0 : stressF R c g Φ x = 0 := by
      unfold stressF
      simp [hz]
    rw [h0, stressBall, if_neg hy]
    simp
