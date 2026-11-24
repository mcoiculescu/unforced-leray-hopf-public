import UnforcedLeray.Short.PartI.Sub.C09.RemOrigCut

/-!
# Helper: limits and estimates for the cutoff integrals (task PartI:C09)

* `tendsto_cut_integral`: `∫ cutG ε · base → 0` as `ε → 0⁺` for integrable `base` (dominated
  convergence; the cutoffs vanish at every point off the origin).
* `R_bound`: the cross term `∫ u · Tfun φ ε` is `O(ε)` when `|u z| ≤ C‖z‖` near the origin
  (the square `box ε` has volume `16 ε²`, `|Tfun| = O(ε⁻²)`, `|u| = O(ε)` on the box).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

namespace UnforcedLeray.Short.PartI.RemOrig

open UnforcedLeray.PlanarBS.Sob UnforcedLeray.B0121

theorem tendsto_cut_integral {base : ℝ × ℝ → ℂ} (hb : Integrable base volume) :
    Tendsto (fun ε : ℝ => ∫ z, cutG ε z * base z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hz : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), z ≠ 0 := by
    rw [ae_iff]
    simp
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (ℝ × ℝ))) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε z => cutG ε z * base z) (f := fun _ => (0 : ℂ))
    (fun z => ‖base z‖)
    (Filter.Eventually.of_forall fun ε =>
      ((cutG_contDiff ε).continuous.aestronglyMeasurable.mul hb.aestronglyMeasurable))
    (Filter.Eventually.of_forall fun ε => ae_of_all _ fun z => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (cutG_norm_le ε z))
    hb.norm
    (by
      filter_upwards [hz] with z hz0
      have hpos : (0 : ℝ) < ‖z‖ / 2 := half_pos (norm_pos_iff.2 hz0)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
      rw [cutG_eq_zero hε.1 (by linarith [hε.2]), zero_mul])
  simpa using h

/-- The square `[-2ε, 2ε]²`, which is the sup-norm ball of radius `2ε`. -/
def box (ε : ℝ) : Set (ℝ × ℝ) :=
  Icc (-(2 * ε)) (2 * ε) ×ˢ Icc (-(2 * ε)) (2 * ε)

theorem mem_box_iff (ε : ℝ) (z : ℝ × ℝ) : z ∈ box ε ↔ ‖z‖ ≤ 2 * ε := by
  simp only [box, Prod.norm_def, max_le_iff, Real.norm_eq_abs, mem_prod, mem_Icc, abs_le]

theorem volume_box_eq (ε : ℝ) :
    volume (box ε) = ENNReal.ofReal (4 * ε) * ENNReal.ofReal (4 * ε) := by
  unfold box
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
  have h4 : 2 * ε - -(2 * ε) = 4 * ε := by ring
  rw [h4]

theorem volume_box_lt_top (ε : ℝ) : volume (box ε) < ⊤ := by
  rw [volume_box_eq]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

theorem volume_real_box {ε : ℝ} (hε : 0 ≤ ε) : volume.real (box ε) = 16 * ε ^ 2 := by
  rw [measureReal_def, volume_box_eq, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]
  ring

theorem R_bound {u φ : ℝ × ℝ → ℂ} {C δ : ℝ} (hδ : 0 < δ)
    (hC : ∀ z : ℝ × ℝ, ‖z‖ < δ → ‖u z‖ ≤ C * ‖z‖) (hφ : IsTestFn univ φ) :
    ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → 2 * ε < δ → ε ≤ 1 →
      ‖∫ z, u z * Tfun φ ε z‖ ≤ K * ε := by
  obtain ⟨P0, hP0⟩ := hφ.smooth.continuous.bounded_above_of_compact_support hφ.compact
  obtain ⟨P1, hP1⟩ : ∃ P1 : ℝ, ∀ w, ‖dirDeriv (ev 0) φ w‖ ≤ P1 ∧ ‖dirDeriv (ev 1) φ w‖ ≤ P1 := by
    obtain ⟨a, ha⟩ := bdd_dir φ hφ.smooth hφ.compact (ev 0)
    obtain ⟨b, hb⟩ := bdd_dir φ hφ.smooth hφ.compact (ev 1)
    exact ⟨max a b, fun w => ⟨(ha w).trans (le_max_left _ _), (hb w).trans (le_max_right _ _)⟩⟩
  obtain ⟨B1, hB1⟩ : ∃ B1 : ℝ, ∀ w, ‖dirDeriv (ev 0) Gfun w‖ ≤ B1 ∧
      ‖dirDeriv (ev 1) Gfun w‖ ≤ B1 := by
    obtain ⟨a, ha⟩ := bdd_dir Gfun Gfun_contDiff Gfun_hcs (ev 0)
    obtain ⟨b, hb⟩ := bdd_dir Gfun Gfun_contDiff Gfun_hcs (ev 1)
    exact ⟨max a b, fun w => ⟨(ha w).trans (le_max_left _ _), (hb w).trans (le_max_right _ _)⟩⟩
  obtain ⟨B2, hB2⟩ : ∃ B2 : ℝ, ∀ w, ‖iterDirDeriv [ev 0, ev 0] Gfun w‖ ≤ B2 ∧
      ‖iterDirDeriv [ev 1, ev 1] Gfun w‖ ≤ B2 := by
    obtain ⟨a, ha⟩ := bdd_iter2 Gfun Gfun_contDiff Gfun_hcs (ev 0)
    obtain ⟨b, hb⟩ := bdd_iter2 Gfun Gfun_contDiff Gfun_hcs (ev 1)
    exact ⟨max a b, fun w => ⟨(ha w).trans (le_max_left _ _), (hb w).trans (le_max_right _ _)⟩⟩
  have hP0n : 0 ≤ P0 := (norm_nonneg _).trans (hP0 0)
  have hP1n : 0 ≤ P1 := (norm_nonneg _).trans (hP1 0).1
  have hB1n : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0).1
  have hB2n : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0).1
  refine ⟨128 * |C| * P1 * B1 + 64 * |C| * P0 * B2, fun ε hε h2δ hε1 => ?_⟩
  have hTb : ∀ z, ‖Tfun φ ε z‖ ≤ 2 * (P1 * (ε⁻¹ * B1) + P1 * (ε⁻¹ * B1))
      + P0 * (ε⁻¹ * (ε⁻¹ * B2) + ε⁻¹ * (ε⁻¹ * B2)) := by
    intro z
    unfold Tfun
    have a0 : ‖dirDeriv (ev 0) φ z‖ ≤ P1 := (hP1 z).1
    have a1 : ‖dirDeriv (ev 1) φ z‖ ≤ P1 := (hP1 z).2
    have b0 : ‖dirDeriv (ev 0) (cutG ε) z‖ ≤ ε⁻¹ * B1 :=
      cutG_dir_bound hε (ev 0) z (fun w => (hB1 w).1)
    have b1 : ‖dirDeriv (ev 1) (cutG ε) z‖ ≤ ε⁻¹ * B1 :=
      cutG_dir_bound hε (ev 1) z (fun w => (hB1 w).2)
    have l0 : ‖iterDirDeriv [ev 0, ev 0] (cutG ε) z‖ ≤ ε⁻¹ * (ε⁻¹ * B2) :=
      cutG_iter_bound hε (ev 0) z (fun w => (hB2 w).1)
    have l1 : ‖iterDirDeriv [ev 1, ev 1] (cutG ε) z‖ ≤ ε⁻¹ * (ε⁻¹ * B2) :=
      cutG_iter_bound hε (ev 1) z (fun w => (hB2 w).2)
    have hp : ‖φ z‖ ≤ P0 := hP0 z
    have hA : ‖dirDeriv (ev 0) φ z * dirDeriv (ev 0) (cutG ε) z
        + dirDeriv (ev 1) φ z * dirDeriv (ev 1) (cutG ε) z‖ ≤ P1 * (ε⁻¹ * B1) + P1 * (ε⁻¹ * B1) :=
      (norm_add_le _ _).trans (add_le_add
        (by rw [norm_mul]; exact mul_le_mul a0 b0 (norm_nonneg _) hP1n)
        (by rw [norm_mul]; exact mul_le_mul a1 b1 (norm_nonneg _) hP1n))
    have hL : ‖iterDirDeriv [ev 0, ev 0] (cutG ε) z + iterDirDeriv [ev 1, ev 1] (cutG ε) z‖
        ≤ ε⁻¹ * (ε⁻¹ * B2) + ε⁻¹ * (ε⁻¹ * B2) :=
      (norm_add_le _ _).trans (add_le_add l0 l1)
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    calc ‖2 * (dirDeriv (ev 0) φ z * dirDeriv (ev 0) (cutG ε) z
            + dirDeriv (ev 1) φ z * dirDeriv (ev 1) (cutG ε) z)
          + φ z * (iterDirDeriv [ev 0, ev 0] (cutG ε) z
            + iterDirDeriv [ev 1, ev 1] (cutG ε) z)‖
        ≤ ‖2 * (dirDeriv (ev 0) φ z * dirDeriv (ev 0) (cutG ε) z
            + dirDeriv (ev 1) φ z * dirDeriv (ev 1) (cutG ε) z)‖
          + ‖φ z * (iterDirDeriv [ev 0, ev 0] (cutG ε) z
            + iterDirDeriv [ev 1, ev 1] (cutG ε) z)‖ := norm_add_le _ _
      _ ≤ 2 * (P1 * (ε⁻¹ * B1) + P1 * (ε⁻¹ * B1))
          + P0 * (ε⁻¹ * (ε⁻¹ * B2) + ε⁻¹ * (ε⁻¹ * B2)) := by
        rw [norm_mul, norm_mul, h2]
        exact add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
          (mul_le_mul hp hL (norm_nonneg _) hP0n)
  have hM0 : 0 ≤ 2 * (P1 * (ε⁻¹ * B1) + P1 * (ε⁻¹ * B1))
      + P0 * (ε⁻¹ * (ε⁻¹ * B2) + ε⁻¹ * (ε⁻¹ * B2)) :=
    (norm_nonneg _).trans (hTb 0)
  have hzero : ∀ z : ℝ × ℝ, z ∉ box ε → u z * Tfun φ ε z = 0 := by
    intro z hz
    rw [mem_box_iff, not_le] at hz
    have d0 := (cutG_outside hε hz (ev 0)).1
    have d1 := (cutG_outside hε hz (ev 1)).1
    have i0 := (cutG_outside hε hz (ev 0)).2
    have i1 := (cutG_outside hε hz (ev 1)).2
    unfold Tfun
    rw [d0, d1, i0, i1]
    simp
  have hbound : ∀ z ∈ box ε, ‖u z * Tfun φ ε z‖ ≤
      |C| * (2 * ε) * (2 * (P1 * (ε⁻¹ * B1) + P1 * (ε⁻¹ * B1))
        + P0 * (ε⁻¹ * (ε⁻¹ * B2) + ε⁻¹ * (ε⁻¹ * B2))) := by
    intro z hz
    rw [mem_box_iff] at hz
    have hu : ‖u z‖ ≤ |C| * (2 * ε) := by
      have h1 : ‖z‖ < δ := by linarith
      have h2 := hC z h1
      have h3 : C * ‖z‖ ≤ |C| * ‖z‖ := mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg z)
      have h4 : |C| * ‖z‖ ≤ |C| * (2 * ε) := mul_le_mul_of_nonneg_left hz (abs_nonneg C)
      linarith
    rw [norm_mul]
    exact mul_le_mul hu (hTb z) (norm_nonneg _)
      (mul_nonneg (abs_nonneg C) (by linarith))
  have hnorm := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := box ε)
    (f := fun z => u z * Tfun φ ε z) (volume_box_lt_top ε) (fun x hx => hbound x hx)
  rw [volume_real_box hε.le, setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at hnorm
  have key : |C| * (2 * ε) * (2 * (P1 * (ε⁻¹ * B1) + P1 * (ε⁻¹ * B1))
        + P0 * (ε⁻¹ * (ε⁻¹ * B2) + ε⁻¹ * (ε⁻¹ * B2))) * (16 * ε ^ 2)
      = 128 * |C| * P1 * B1 * ε ^ 2 + 64 * |C| * P0 * B2 * ε := by
    field_simp
    ring
  have hpos : 0 ≤ |C| * P1 * B1 * (ε * (1 - ε)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg C) hP1n) hB1n)
      (mul_nonneg hε.le (sub_nonneg.2 hε1))
  calc ‖∫ z, u z * Tfun φ ε z‖
      ≤ |C| * (2 * ε) * (2 * (P1 * (ε⁻¹ * B1) + P1 * (ε⁻¹ * B1))
        + P0 * (ε⁻¹ * (ε⁻¹ * B2) + ε⁻¹ * (ε⁻¹ * B2))) * (16 * ε ^ 2) := hnorm
    _ = 128 * |C| * P1 * B1 * ε ^ 2 + 64 * |C| * P0 * B2 * ε := key
    _ ≤ (128 * |C| * P1 * B1 + 64 * |C| * P0 * B2) * ε := by nlinarith [hpos]

end UnforcedLeray.Short.PartI.RemOrig
