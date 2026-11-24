import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.ThinRecv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L1
import UnforcedLeray.Short.PartIIIa.Tasks16.DomPointwise.Phase
import UnforcedLeray.Lib.Kernels.PlanarBS.P.Infra.ConvMinkowski.Minkowski

/-!
# `PartIII-b:C/rep/4/1/org/2/1` (a): Minkowski over the log-shift and the source disk

Source `the November 2 reference manuscript` 3611-3621 (`sep:resolvent`, the
`λ`-integral sweeps the phase by `2 log λ`), 5342-5355 (separated pointwise velocity).

For a fixed receiver `y` and the disk `D = {ϱ z < θ ϱ y}`, the phase `L²` norm over one period of
`τ ↦ ∫₀¹∫_D W(τ + 2 log λ, z) dz dλ` is at most `∫_D ‖W(·, z)‖_{L²_τ} dz`, `W = srcW` the
`P`-periodic source weight (`P = 2c/R`): Minkowski's integral inequality over the atoms `(λ, z)`
and the translation invariance of the `L²` norm of a periodic function over a period.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FTT

open UnforcedLeray.Short.PartIIIb.Concrete.WYCore

/-- The source weight is `2c/R`-periodic in the phase. -/
theorem srcW_periodic {R c : ℝ} (hR : 0 < R) (hc : 0 < c) (G : Chart → ℝ≥0∞) (z : Space)
    (σ : ℝ) : srcW R c G (σ + 2 * c / R) z = srcW R c G σ z := by
  have h1 := chartOf_add_int_period R c hR hc z σ 1
  simp only [Int.cast_one, one_mul] at h1
  unfold srcW
  rw [h1]

/-- **Minkowski over the atoms `(λ, z)`**: the `L²_τ((0,P])` norm of the shifted disk integral is at
most the integral over the disk of the `L²_τ` norms of the source weight. -/
theorem minkowski_shift_disk {R c : ℝ} (hR : 0 < R) (hc : 0 < c) {G : Chart → ℝ≥0∞}
    (hG : Measurable G) (Dk : Set Space) (hDk : MeasurableSet Dk) :
    (∫⁻ τ in Ioc 0 (2 * c / R),
        (∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z in Dk, srcW R c G (τ + 2 * Real.log l) z) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ) ≤
      ∫⁻ z in Dk, (∫⁻ τ in Ioc 0 (2 * c / R), srcW R c G τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hP : 0 < 2 * c / R := div_pos (mul_pos two_pos hc) hR
  have hW := measurable_srcW R c hG
  have hF : Measurable (Function.uncurry fun (τ : ℝ) (a : ℝ × Space) =>
      srcW R c G (τ + 2 * Real.log a.1) a.2) := by
    have : Measurable fun x : ℝ × (ℝ × Space) => (x.1 + 2 * Real.log x.2.1, x.2.2) :=
      ((measurable_fst.add (measurable_const.mul (Real.measurable_log.comp
        (measurable_fst.comp measurable_snd))))).prodMk (measurable_snd.comp measurable_snd)
    exact hW.comp this
  have hM := UnforcedLeray.PlanarBS.Conv.lintegral_lintegral_rpow_le
    (μ := volume.restrict (Ioc 0 (2 * c / R)))
    (ν := (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict Dk))
    (F := fun (τ : ℝ) (a : ℝ × Space) => srcW R c G (τ + 2 * Real.log a.1) a.2)
    hF.aemeasurable (p := 2) (by norm_num)
  have hK : ∀ τ : ℝ, (∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z in Dk, srcW R c G (τ + 2 * Real.log l) z) =
      ∫⁻ a : ℝ × Space, srcW R c G (τ + 2 * Real.log a.1) a.2
        ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict Dk)) := by
    intro τ
    rw [lintegral_prod]
    exact (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable
  simp only [hK]
  refine hM.trans (le_of_eq ?_)
  -- the inner `L²_τ` norm does not depend on the shift
  have hshift : ∀ (l : ℝ) (z : Space),
      (∫⁻ τ in Ioc 0 (2 * c / R), srcW R c G (τ + 2 * Real.log l) z ^ (2 : ℝ)) =
        ∫⁻ τ in Ioc 0 (2 * c / R), srcW R c G τ z ^ (2 : ℝ) := fun l z =>
    UnforcedLeray.Short.IIIa.lintegral_Ioc_shift (2 * c / R) hP
      (fun τ => srcW R c G τ z ^ (2 : ℝ))
      (fun τ => by simp only [srcW_periodic hR hc G z τ]) (2 * Real.log l)
  simp only [hshift]
  have hmeas : Measurable fun z : Space =>
      (∫⁻ τ in Ioc 0 (2 * c / R), srcW R c G τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    have h2 : Measurable fun x : ℝ × Space => srcW R c G x.1 x.2 ^ (2 : ℝ) :=
      hW.pow_const _
    exact (h2.lintegral_prod_left').pow_const _
  rw [lintegral_prod (μ := volume.restrict (Ioo (0 : ℝ) 1)) (ν := volume.restrict Dk)
    (fun a : ℝ × Space => (∫⁻ τ in Ioc 0 (2 * c / R), srcW R c G τ a.2 ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
    (hmeas.comp measurable_snd).aemeasurable]
  simp only [lintegral_const]
  rw [Measure.restrict_apply_univ, Real.volume_Ioo]
  simp

end UnforcedLeray.Short.PartIIIb.Concrete.FTT

end
