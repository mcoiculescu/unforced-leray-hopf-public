import UnforcedLeray.Short.PartI.Sub.T02_3_11
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.IntegrandDecomp

/-!
# Part I, task `PartI:T02/3/11` leaf: `ccStretchEstimate`

Source of record: `the November 2 reference manuscript`, lines 276-288 (the stretching
term, bounded by the gradient of `v'`).

With `w = v - v'`, `S = (w·∇)v'` and `φ = etaCutoff R`, the stretching term is
`ccStretch = -2 ∫_cell φ ⟨w, S⟩`.  The pointwise bound `‖S‖ ≤ K ‖w‖` (`CcStretchPointwise`) and
`φ ≥ 0` give `-2 φ ⟨w, S⟩ ≤ 2K (φ ‖w‖²)` pointwise, hence `ccStretch ≤ 2K F_R`.  Both integrands are
continuous and vanish for `|η| ≥ 2R`, so `CellIntegrableOfSupport` makes them integrable on the cell.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- Pointwise bound: if `‖S‖ ≤ K ‖w‖` and `φ ≥ 0`, then `-2 φ ⟨w, S⟩ ≤ 2 K (φ ‖w‖²)`. -/
theorem ccSEPointwise (φ K : ℝ) (hφ : 0 ≤ φ) (w S : Vec)
    (hSw : ‖S‖ ≤ K * ‖w‖) :
    -2 * (φ * inner ℝ w S) ≤ 2 * K * (φ * ‖w‖ ^ 2) := by
  have h1 : -(inner ℝ w S) ≤ ‖w‖ * ‖S‖ := by
    have h1a := neg_le_abs (inner ℝ w S)
    have h1b := abs_real_inner_le_norm w S
    linarith
  have h2 : -(inner ℝ w S) ≤ K * ‖w‖ ^ 2 := by
    calc -(inner ℝ w S) ≤ ‖w‖ * ‖S‖ := h1
      _ ≤ ‖w‖ * (K * ‖w‖) := mul_le_mul_of_nonneg_left hSw (norm_nonneg w)
      _ = K * ‖w‖ ^ 2 := by ring
  have h3 : 0 ≤ 2 * φ := by linarith
  calc -2 * (φ * inner ℝ w S) = (2 * φ) * (-(inner ℝ w S)) := by ring
    _ ≤ (2 * φ) * (K * ‖w‖ ^ 2) := mul_le_mul_of_nonneg_left h2 h3
    _ = 2 * K * (φ * ‖w‖ ^ 2) := by ring

/-- **Leaf `CcStretchEstimate`** (`PartI:T02/3/11`): the stretching term is bounded by `2K` times the
cutoff energy, where `K` comes from `CcStretchPointwise`. -/
theorem ccStretchEstimate (hI : CellIntegrableOfSupport) (hS : CcSliceSmooth)
    (hP : CcStretchPointwise) : CcStretchEstimate := by
  intro ν c T M v v' p p' h
  obtain ⟨K, hK0, hK⟩ := hP ν c T M v v' p p' h
  refine ⟨2 * K, by linarith, fun R hR s hs => ?_⟩
  have hRpos : 0 < R := by linarith
  have hc : 0 < c := by linarith [h.c_ge]
  obtain ⟨hv, -⟩ := hS ν c T v p h.cl s hs
  obtain ⟨hv', -⟩ := hS ν c T v' p' h.cl' s hs
  have hwd : ContDiff ℝ ∞ (ccDiffV v v' s) := hv.sub hv'
  have hwc : Continuous (ccDiffV v v' s) := hwd.continuous
  have hcφ : Continuous (fun z : Plane => etaCutoff R z.2) := cid_etaCutoff_cont R
  have hsupp : ∀ z : Plane, 2 * R ≤ |z.2| → etaCutoff R z.2 = 0 :=
    fun z hz => cid_etaCutoff_eq_zero hRpos hz
  have hcA : Continuous (fun z : Plane => -2 * (etaCutoff R z.2 *
      inner ℝ (ccDiffV v v' s z) (bilinAdv (ccDiffV v v' s) (v' s) z))) :=
    continuous_const.mul (hcφ.mul (hwc.inner (cid_bilin_cont hwd hv')))
  have hcG : Continuous (fun z : Plane => 2 * K * (etaCutoff R z.2 * ‖ccDiffV v v' s z‖ ^ 2)) :=
    continuous_const.mul (hcφ.mul (hwc.norm.pow 2))
  have iA : IntegrableOn (fun z : Plane => -2 * (etaCutoff R z.2 *
      inner ℝ (ccDiffV v v' s z) (bilinAdv (ccDiffV v v' s) (v' s) z))) (Cyl.cell c) :=
    hI c R hc hRpos _ hcA (fun z hz => by simp [hsupp z hz])
  have iG : IntegrableOn (fun z : Plane => 2 * K * (etaCutoff R z.2 * ‖ccDiffV v v' s z‖ ^ 2))
      (Cyl.cell c) :=
    hI c R hc hRpos _ hcG (fun z hz => by simp [hsupp z hz])
  have hpt : ∀ z : Plane, -2 * (etaCutoff R z.2 *
      inner ℝ (ccDiffV v v' s z) (bilinAdv (ccDiffV v v' s) (v' s) z)) ≤
      2 * K * (etaCutoff R z.2 * ‖ccDiffV v v' s z‖ ^ 2) := fun z =>
    ccSEPointwise (etaCutoff R z.2) K (etaCutoff_nonneg R z.2) (ccDiffV v v' s z)
      (bilinAdv (ccDiffV v v' s) (v' s) z) (hK s hs z)
  unfold ccStretch classicalCutoffEnergy
  calc -2 * ∫ z in Cyl.cell c, etaCutoff R z.2 *
        inner ℝ (ccDiffV v v' s z) (bilinAdv (ccDiffV v v' s) (v' s) z)
      = ∫ z in Cyl.cell c, -2 * (etaCutoff R z.2 *
        inner ℝ (ccDiffV v v' s z) (bilinAdv (ccDiffV v v' s) (v' s) z)) :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ z in Cyl.cell c, 2 * K * (etaCutoff R z.2 * ‖ccDiffV v v' s z‖ ^ 2) :=
        integral_mono iA iG (fun z => hpt z)
    _ = 2 * K * ∫ z in Cyl.cell c, etaCutoff R z.2 * ‖ccDiffV v v' s z‖ ^ 2 :=
        integral_const_mul _ _

end UnforcedLeray.Short.PartI
