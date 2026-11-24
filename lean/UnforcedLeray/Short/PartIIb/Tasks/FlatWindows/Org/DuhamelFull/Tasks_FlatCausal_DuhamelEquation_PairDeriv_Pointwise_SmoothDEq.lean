import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.PairDeriv.Pointwise.SmoothDEq
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_PartIIb_T12_7_5_1

/-!
# Part II-b, task `PartII-b:T12/7/5/1/3` (`dfe_DeqpdSmoothDEq`): identification of the integral

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
For `s > t`, with `θ = ν(s - t) > 0` and `ψ y = Ψ_i(s, y)`, the integral
`∫ (ν (∂_θK)(θ, w) ψ(z - w) + K(θ, w) cpd0 Ψ_i(s, z - w)) dw` equals
`deqSmoothD ν Ψ i t s z`. The proof splits the integral, moves the age derivative onto
`planarLap ψ` by `deqhd_hval`, and expands the planar Laplacian by `dfe_DeqpdCptLap` (the hypothesis
`hlap`).

Helpers use the prefix `dsd`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:T12/7/5/1/3`**: the integral from `dfe_DeqpdJointDeriv` is `deqSmoothD`
(SP 1923-1927). Uses the chain rule `dfe_DeqpdCptLap` as the hypothesis `hlap`. -/
theorem dfe_deqpdSmoothDEq (hlap : UnforcedLeray.Short.IIb.dfe_DeqpdCptLap) :
    UnforcedLeray.Short.IIb.dfe_DeqpdSmoothDEq := by
  intro ν t hν Ψ hΨ i s hs z
  unfold UnforcedLeray.Short.IIb.deqSmoothD
  have hθ0 : 0 < ν * (s - t) := mul_pos hν (sub_pos.mpr hs)
  simp only [flatHeat_kernel_eq hθ0]
  set θ : ℝ := ν * (s - t) with hθe
  have hΦ : IsCoordTest (fun x => Ψ x i) := hΨ.smooth i
  have hT0 : IsCoordTest (cpd 0 (fun x => Ψ x i)) := dsd_cpd_test hΦ 0
  have hT1 : IsCoordTest (cpd 1 (fun x => Ψ x i)) := dsd_cpd_test hΦ 1
  have hT2 : IsCoordTest (cpd 2 (fun x => Ψ x i)) := dsd_cpd_test hΦ 2
  have hE1 : IsCoordTest (cpd 1 (cpd 1 (fun x => Ψ x i))) := dsd_cpd_test hT1 1
  have hE2 : IsCoordTest (cpd 2 (cpd 2 (fun x => Ψ x i))) := dsd_cpd_test hT2 2
  obtain ⟨hψd, hψk⟩ := dsd_slice hΦ s
  have hψc : Continuous (fun y : ℝ × ℝ => Ψ (s, y) i) := hψd.continuous
  obtain ⟨hψc', hBψ⟩ := dsd_slice_cb hΦ s
  have hc0 := (dsd_slice_cb hT0 s).1
  obtain ⟨B0, hB0⟩ := (dsd_slice_cb hT0 s).2
  have hc1 := (dsd_slice_cb hE1 s).1
  obtain ⟨B1, hB1⟩ := (dsd_slice_cb hE1 s).2
  have hc2 := (dsd_slice_cb hE2 s).1
  obtain ⟨B2, hB2⟩ := (dsd_slice_cb hE2 s).2
  obtain ⟨Bψ, hBψ'⟩ := hBψ
  -- integrability of the left integrand pieces
  have hIA : Integrable (fun w : ℝ × ℝ => UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w * Ψ (s, z - w) i) :=
    dsd_mul_bdd (UnforcedLeray.HeatCylinder.integrable_heatKernel2AgeDerivative hθ0) (dsd_comp_sub hψc z)
      (fun w => hBψ' (z - w))
  have hIK0 : Integrable (fun w : ℝ × ℝ =>
      UnforcedLeray.B0284.heatKernel2 θ w * cpd 0 (fun y => Ψ y i) (s, z - w)) :=
    dsd_int_slice hθ0 hc0 hB0 z
  have hIK1 : Integrable (fun w : ℝ × ℝ =>
      UnforcedLeray.B0284.heatKernel2 θ w *
        cpd 1 (fun y => cpd 1 (fun x => Ψ x i) y) (s, z - w)) :=
    dsd_int_slice hθ0 hc1 hB1 z
  have hIK2 : Integrable (fun w : ℝ × ℝ =>
      UnforcedLeray.B0284.heatKernel2 θ w *
        cpd 2 (fun y => cpd 2 (fun x => Ψ x i) y) (s, z - w)) :=
    dsd_int_slice hθ0 hc2 hB2 z
  -- planar heat equation: age derivative moved onto the planar Laplacian
  have hHD : ∫ w : ℝ × ℝ, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w * Ψ (s, z - w) i =
      ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w *
        planarLap (fun y => Ψ (s, y) i) (z - w) :=
    deqhd_hval hθ0 hψd hψk z
  -- chain rule for the planar Laplacian
  have hPL : ∀ w : ℝ × ℝ, planarLap (fun y => Ψ (s, y) i) (z - w) =
      cpd 1 (fun y => cpd 1 (fun x => Ψ x i) y) (s, z - w) +
        cpd 2 (fun y => cpd 2 (fun x => Ψ x i) y) (s, z - w) :=
    fun w => hlap Ψ hΨ i s (z - w)
  have hPLint : ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w *
        planarLap (fun y => Ψ (s, y) i) (z - w) =
      (∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w *
        cpd 1 (fun y => cpd 1 (fun x => Ψ x i) y) (s, z - w)) +
      (∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w *
        cpd 2 (fun y => cpd 2 (fun x => Ψ x i) y) (s, z - w)) := by
    rw [← integral_add hIK1 hIK2]
    congr 1
    funext w
    rw [hPL w]
    ring
  -- the right-hand integrand, regrouped
  have hRHS : ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 θ w *
        (cpd 0 (fun y => Ψ y i) (s, z - w) + ν *
          (cpd 1 (fun y => cpd 1 (fun x => Ψ x i) y) (s, z - w) +
            cpd 2 (fun y => cpd 2 (fun x => Ψ x i) y) (s, z - w))) =
      ∫ w : ℝ × ℝ, (UnforcedLeray.B0284.heatKernel2 θ w * cpd 0 (fun y => Ψ y i) (s, z - w) +
        ν * (UnforcedLeray.B0284.heatKernel2 θ w *
            cpd 1 (fun y => cpd 1 (fun x => Ψ x i) y) (s, z - w) +
          UnforcedLeray.B0284.heatKernel2 θ w *
            cpd 2 (fun y => cpd 2 (fun x => Ψ x i) y) (s, z - w))) := by
    congr 1
    funext w
    ring
  have hKEF : Integrable (fun w : ℝ × ℝ =>
      UnforcedLeray.B0284.heatKernel2 θ w * cpd 1 (fun y => cpd 1 (fun x => Ψ x i) y) (s, z - w) +
      UnforcedLeray.B0284.heatKernel2 θ w * cpd 2 (fun y => cpd 2 (fun x => Ψ x i) y) (s, z - w)) :=
    hIK1.add hIK2
  rw [hRHS, integral_add (hIA.const_mul ν) hIK0, integral_const_mul ν, hHD, hPLint,
    integral_add hIK0 (hKEF.const_mul ν), integral_const_mul ν, integral_add hIK1 hIK2]
  ring

end UnforcedLeray.Short.IIb
