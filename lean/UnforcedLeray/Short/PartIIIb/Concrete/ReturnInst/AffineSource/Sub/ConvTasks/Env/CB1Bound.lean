import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvEnvSub

/-!
# `CB1Bound`: pointwise bound of the `ε`-bracket `cB1` (source 5040-5044)

`cB1 F G = -[F_r(𝒦G+G) + G_r(𝒦F+F) + (𝒦F)_r G + (𝒦G)_r F]`; components are bounded by the
sup norm, giving `‖cB1 F G‖ ≤ 2(‖F‖‖𝒦G‖ + ‖G‖‖𝒦F‖ + ‖F‖‖G‖)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

theorem cb1Bound : CB1Bound := by
  intro F G s x
  have t1 : ‖(F s x).1 • (cK G s x + G s x)‖ ≤ ‖F s x‖ * (‖cK G s x‖ + ‖G s x‖) := by
    rw [norm_smul]
    exact mul_le_mul (norm_fst_le _) (norm_add_le _ _) (norm_nonneg _) (norm_nonneg _)
  have t2 : ‖(G s x).1 • (cK F s x + F s x)‖ ≤ ‖G s x‖ * (‖cK F s x‖ + ‖F s x‖) := by
    rw [norm_smul]
    exact mul_le_mul (norm_fst_le _) (norm_add_le _ _) (norm_nonneg _) (norm_nonneg _)
  have t3 : ‖(cK F s x).1 • G s x‖ ≤ ‖cK F s x‖ * ‖G s x‖ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (norm_fst_le _) (norm_nonneg _)
  have t4 : ‖(cK G s x).1 • F s x‖ ≤ ‖cK G s x‖ * ‖F s x‖ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (norm_fst_le _) (norm_nonneg _)
  have q1 := norm_add_le ((F s x).1 • (cK G s x + G s x) + (G s x).1 • (cK F s x + F s x) +
    (cK F s x).1 • G s x) ((cK G s x).1 • F s x)
  have q2 := norm_add_le ((F s x).1 • (cK G s x + G s x) + (G s x).1 • (cK F s x + F s x))
    ((cK F s x).1 • G s x)
  have q3 := norm_add_le ((F s x).1 • (cK G s x + G s x)) ((G s x).1 • (cK F s x + F s x))
  unfold cB1
  rw [norm_neg]
  nlinarith [q1, q2, q3, t1, t2, t3, t4]

end UnforcedLeray.Short.PartIIIb.Concrete
