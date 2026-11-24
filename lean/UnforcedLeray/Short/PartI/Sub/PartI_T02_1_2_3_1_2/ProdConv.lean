import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_2_3_1_2

/-!
# Part I, task `PartI:T02/1/2/3/1/2/1`: `L²` convergence of products with a bounded factor

Source of record: `the November 2 reference manuscript`, lines 261-288.

Proves the leaf `BdpProdConv` from `Short/PartI/Sub/PartI_T02_1_2_3_1_2.lean`:
`us n * vs n - u * v = (us n - u) * vs n + u * (vs n - v)`, and the first term is bounded
by `M ‖us n - u‖₂`, the second by `M ‖vs n - v‖₂`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

theorem bdp_prodConv : UnforcedLeray.Short.PartI.BdpProdConv := by
  intro c M u v us vs hu hv hus hvs bu bvs tus tvs
  have hA : ∀ n, AEStronglyMeasurable (fun z => (us n z - u z) * vs n z)
      (Sob.cylinder c).μ := fun n => ((hus n).sub hu).mul (hvs n)
  have hB : ∀ n, AEStronglyMeasurable (fun z => u z * (vs n z - v z))
      (Sob.cylinder c).μ := fun n => hu.mul ((hvs n).sub hv)
  have bA : ∀ n, eLpNorm (fun z => (us n z - u z) * vs n z) 2 (Sob.cylinder c).μ ≤
      ENNReal.ofReal M * eLpNorm (fun z => us n z - u z) 2 (Sob.cylinder c).μ := by
    intro n
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    filter_upwards [bvs n] with z hz
    rw [norm_mul, mul_comm (M : ℝ)]
    exact mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact hz) (norm_nonneg _)
  have bB : ∀ n, eLpNorm (fun z => u z * (vs n z - v z)) 2 (Sob.cylinder c).μ ≤
      ENNReal.ofReal M * eLpNorm (fun z => vs n z - v z) 2 (Sob.cylinder c).μ := by
    intro n
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    filter_upwards [bu] with z hz
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hz) (norm_nonneg _)
  have hdecomp : ∀ n, ((fun z => us n z * vs n z) - fun z => u z * v z) =
      (fun z => (us n z - u z) * vs n z) + (fun z => u z * (vs n z - v z)) := by
    intro n
    funext z
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hbound : ∀ n, eLpNorm ((fun z => us n z * vs n z) - fun z => u z * v z) 2
      (Sob.cylinder c).μ ≤ ENNReal.ofReal M * eLpNorm (fun z => us n z - u z) 2 (Sob.cylinder c).μ
        + ENNReal.ofReal M * eLpNorm (fun z => vs n z - v z) 2 (Sob.cylinder c).μ := by
    intro n
    rw [hdecomp n]
    exact (eLpNorm_add_le (hA n) (hB n) (by norm_num)).trans (add_le_add (bA n) (bB n))
  have h1 : Tendsto (fun n => eLpNorm (fun z => us n z - u z) 2 (Sob.cylinder c).μ)
      atTop (nhds 0) := tus
  have h2 : Tendsto (fun n => eLpNorm (fun z => vs n z - v z) 2 (Sob.cylinder c).μ)
      atTop (nhds 0) := tvs
  have hlim : Tendsto (fun n => ENNReal.ofReal M * eLpNorm (fun z => us n z - u z) 2
      (Sob.cylinder c).μ + ENNReal.ofReal M * eLpNorm (fun z => vs n z - v z) 2
      (Sob.cylinder c).μ) atTop (nhds (ENNReal.ofReal M * 0 + ENNReal.ofReal M * 0)) :=
    (ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofReal_ne_top)).add
      (ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofReal_ne_top))
  rw [mul_zero, add_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => zero_le) (fun n => hbound n)

end UnforcedLeray.Short.PartI
