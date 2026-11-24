import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_7_5_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatDeriv

/-!
# Part II-b, task `PartII-b:T12/7/5/1/3` (`DeqpdSmoothDEq`): identification of the integral

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
For `s > t`, with `θ = ν(s - t) > 0` and `ψ y = Ψ_i(s, y)`, the integral
`∫ (ν (∂_θK)(θ, w) ψ(z - w) + K(θ, w) cpd0 Ψ_i(s, z - w)) dw` equals
`deqSmoothD ν Ψ i t s z`. The proof splits the integral, moves the age derivative onto
`planarLap ψ` by `deqhd_hval`, and expands the planar Laplacian by `DeqpdCptLap` (the hypothesis
`hlap`).

Helpers use the prefix `dsd`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The slice of a coordinate test is a compactly supported smooth function of the plane. -/
theorem dsd_slice {φ : Coord → ℝ} (hφ : IsCoordTest φ) (s : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => φ (s, z)) ∧ HasCompactSupport (fun z : ℝ × ℝ => φ (s, z)) := by
  refine ⟨hφ.smooth.comp (contDiff_const.prodMk contDiff_id), ?_⟩
  refine HasCompactSupport.intro (hφ.compact.image continuous_snd) ?_
  intro z hz
  have : ((s, z) : Coord) ∉ tsupport φ := fun h => hz ⟨(s, z), h, rfl⟩
  exact image_eq_zero_of_notMem_tsupport this

/-- Partial derivative `cpd j Φ` of a coordinate test is a coordinate test. -/
theorem dsd_cpd_test {Φ : Coord → ℝ} (hΦ : IsCoordTest Φ) (j : Fin 3) : IsCoordTest (cpd j Φ) :=
  ⟨(ContDiff.fderiv_right (m := ∞) hΦ.smooth (by simp)).clm_apply contDiff_const,
    hΦ.compact.fderiv_apply (𝕜 := ℝ) (cdir j),
    (tsupport_fderiv_apply_subset (𝕜 := ℝ) (cdir j)).trans hΦ.supp⟩

/-- Slice `y ↦ Φ(s, y)` of a coordinate test: continuous and bounded. -/
theorem dsd_slice_cb {Φ : Coord → ℝ} (hΦ : IsCoordTest Φ) (s : ℝ) :
    Continuous (fun y : ℝ × ℝ => Φ (s, y)) ∧ ∃ B : ℝ, ∀ y : ℝ × ℝ, |Φ (s, y)| ≤ B := by
  obtain ⟨h1, h2⟩ := dsd_slice hΦ s
  obtain ⟨B, hB⟩ := deqhd_bdd_fn h1.continuous h2
  exact ⟨h1.continuous, B, fun y => by rw [← Real.norm_eq_abs]; exact hB y⟩

/-- Composition with `w ↦ z - w` preserves continuity. -/
theorem dsd_comp_sub {φ : ℝ × ℝ → ℝ} (hφ : Continuous φ) (z : ℝ × ℝ) :
    Continuous (fun w : ℝ × ℝ => φ (z - w)) :=
  hφ.comp (continuous_const.sub continuous_id)

/-- Product of an integrable function with a bounded continuous function is integrable. -/
theorem dsd_mul_bdd {f h : ℝ × ℝ → ℝ} {B : ℝ} (hf : Integrable f) (hh : Continuous h)
    (hhb : ∀ w, |h w| ≤ B) : Integrable (fun w => f w * h w) :=
  hf.mul_bdd hh.aestronglyMeasurable (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hhb w)

/-- Heat-kernel integrability against a bounded continuous slice `w ↦ φ(z - w)`. -/
theorem dsd_int_slice {θ : ℝ} (hθ : 0 < θ) {φ : ℝ × ℝ → ℝ} (hφ : Continuous φ) {B : ℝ}
    (hB : ∀ y, |φ y| ≤ B) (z : ℝ × ℝ) :
    Integrable (fun w : ℝ × ℝ => UnforcedLeray.B0284.heatKernel2 θ w * φ (z - w)) :=
  deqhd_int_K hθ (dsd_comp_sub hφ z) (fun w => hB (z - w))

/-- **Task `PartII-b:T12/7/5/1/3`**: the integral from `DeqpdJointDeriv` is `deqSmoothD`
(SP 1923-1927). Uses the chain rule `DeqpdCptLap` as the hypothesis `hlap`. -/
theorem deqpdSmoothDEq (hlap : UnforcedLeray.Short.IIb.DeqpdCptLap) :
    UnforcedLeray.Short.IIb.DeqpdSmoothDEq := by
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
