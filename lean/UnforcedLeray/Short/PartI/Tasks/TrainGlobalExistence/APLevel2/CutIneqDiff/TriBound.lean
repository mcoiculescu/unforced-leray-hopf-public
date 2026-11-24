import UnforcedLeray.Short.PartI.Sub.PartI_T04_9_1_2_2
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnstrophy.HasDeriv

/-!
# Part I, `PartI:T04/9/1/2/2/3`: `APL2TriBound` (source lines 285-288)

Pointwise `|Σ_{ij} ∂_iω ∂_iv_j ∂_jω| ≤ 2 ‖Dv‖ eucJet1 ω`, integrated against `χ_R ≥ 0`
over the cell, gives `-2 X_R ≤ 8 ∫ χ_R eucJet1 ω ‖Dv‖ = 2 apCutTri`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff Interval

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- Real algebra: the trilinear sum is bounded by `2 D (P² + Q²)` when all entries are bounded
by `D ≥ 0`. -/
theorem tri_bound_real (P Q a b c d D : ℝ) (hD : 0 ≤ D) (ha : |a| ≤ D) (hb : |b| ≤ D)
    (hc : |c| ≤ D) (hd : |d| ≤ D) :
    |P * a * P + P * b * Q + Q * c * P + Q * d * Q| ≤ 2 * D * (P ^ 2 + Q ^ 2) := by
  have e1 : |P * a * P| ≤ D * P ^ 2 := by
    rw [show P * a * P = a * P ^ 2 by ring, abs_mul, abs_of_nonneg (sq_nonneg P)]
    exact mul_le_mul_of_nonneg_right ha (sq_nonneg P)
  have e4 : |Q * d * Q| ≤ D * Q ^ 2 := by
    rw [show Q * d * Q = d * Q ^ 2 by ring, abs_mul, abs_of_nonneg (sq_nonneg Q)]
    exact mul_le_mul_of_nonneg_right hd (sq_nonneg Q)
  have hPQ : |P| * |Q| ≤ (P ^ 2 + Q ^ 2) / 2 := by
    nlinarith [sq_abs P, sq_abs Q, sq_nonneg (|P| - |Q|), abs_nonneg P, abs_nonneg Q]
  have e2 : |P * b * Q| ≤ D * (P ^ 2 + Q ^ 2) / 2 := by
    rw [abs_mul, abs_mul]
    calc |P| * |b| * |Q| = |b| * (|P| * |Q|) := by ring
      _ ≤ D * (|P| * |Q|) :=
          mul_le_mul_of_nonneg_right hb (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ ≤ D * ((P ^ 2 + Q ^ 2) / 2) := mul_le_mul_of_nonneg_left hPQ hD
      _ = D * (P ^ 2 + Q ^ 2) / 2 := by ring
  have e3 : |Q * c * P| ≤ D * (P ^ 2 + Q ^ 2) / 2 := by
    rw [abs_mul, abs_mul]
    calc |Q| * |c| * |P| = |c| * (|P| * |Q|) := by ring
      _ ≤ D * (|P| * |Q|) :=
          mul_le_mul_of_nonneg_right hc (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ ≤ D * ((P ^ 2 + Q ^ 2) / 2) := mul_le_mul_of_nonneg_left hPQ hD
      _ = D * (P ^ 2 + Q ^ 2) / 2 := by ring
  have t1 := abs_add_le (P * a * P + P * b * Q + Q * c * P) (Q * d * Q)
  have t2 := abs_add_le (P * a * P + P * b * Q) (Q * c * P)
  have t3 := abs_add_le (P * a * P) (P * b * Q)
  have key : D * P ^ 2 + D * (P ^ 2 + Q ^ 2) / 2 + D * (P ^ 2 + Q ^ 2) / 2 + D * Q ^ 2
      = 2 * D * (P ^ 2 + Q ^ 2) := by ring
  linarith

/-- The partial derivative in `q` of a vector field as the directional derivative. -/
theorem tri_partialQ_eq {u : Plane → Vec} (hu : Differentiable ℝ u) (z : Plane) :
    Cyl.partialQ u z = fderiv ℝ u z eQ := by
  unfold Cyl.partialQ
  have h1 : HasDerivAt (fun q : ℝ => ((q, z.2) : Plane)) eQ z.1 :=
    HasDerivAt.prodMk (hasDerivAt_id z.1) (hasDerivAt_const z.1 z.2)
  have h2 : HasFDerivAt u (fderiv ℝ u z) ((z.1, z.2) : Plane) := (hu z).hasFDerivAt
  have := h2.comp_hasDerivAt z.1 h1
  exact this.deriv

/-- The partial derivative in `η` of a vector field as the directional derivative. -/
theorem tri_partialEta_eq {u : Plane → Vec} (hu : Differentiable ℝ u) (z : Plane) :
    Cyl.partialEta u z = fderiv ℝ u z eE := by
  unfold Cyl.partialEta
  have h1 : HasDerivAt (fun η : ℝ => ((z.1, η) : Plane)) eE z.2 :=
    HasDerivAt.prodMk (hasDerivAt_const z.2 z.1) (hasDerivAt_id z.2)
  have h2 : HasFDerivAt u (fderiv ℝ u z) ((z.1, z.2) : Plane) := (hu z).hasFDerivAt
  have := h2.comp_hasDerivAt z.2 h1
  exact this.deriv

/-- A component of a directional derivative of norm-one direction is bounded by the operator
norm. -/
theorem tri_abs_comp_le {u : Plane → Vec} (z e : Plane) (he : ‖e‖ ≤ 1) (i : Fin 2) :
    |fderiv ℝ u z e i| ≤ ‖fderiv ℝ u z‖ := by
  rw [← Real.norm_eq_abs]
  refine (PiLp.norm_apply_le (fderiv ℝ u z e) i).trans ?_
  calc ‖fderiv ℝ u z e‖ ≤ ‖fderiv ℝ u z‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ u z‖ * 1 := mul_le_mul_of_nonneg_left he (norm_nonneg _)
    _ = ‖fderiv ℝ u z‖ := mul_one _

/-- `PartI:T04/9/1/2/2/3`: the trilinear term is controlled by the cutoff trilinear majorant. -/
theorem aPL2TriBound : APL2TriBound := by
  intro ν c T v p hν hc hcls R hR s hs
  have hR0 : 0 < R := by linarith
  have hsI : s ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self hs
  have hv := hcls.classical.smooth_v
  have hvs : ContDiff ℝ ∞ (v s) := by
    have h := hv.comp_contDiff
      ((contDiff_const : ContDiff ℝ ∞ (fun _ : Plane => s)).prodMk contDiff_id :
        ContDiff ℝ ∞ (fun z : Plane => ((s, z) : ℝ × Plane)))
      (fun z => (⟨hsI, mem_univ z⟩ : ((s, z) : ℝ × Plane) ∈ Icc (0 : ℝ) T ×ˢ (univ : Set Plane)))
    exact h
  have hdv : Differentiable ℝ (v s) := hvs.differentiable (by simp)
  have hS : ContDiff ℝ ∞ (Cyl.curl (v s)) := APEllipticCaux.curl_contDiff hvs
  have hDc : Continuous (fun z : Plane => ‖iteratedFDeriv ℝ 1 (v s) z‖) :=
    (ContDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top) hvs).norm
  have hgc : Continuous (fun z : Plane =>
      etaCutoff R z.2 * (eucJet1 (Cyl.curl (v s)) z * ‖iteratedFDeriv ℝ 1 (v s) z‖)) :=
    ((apcc_eta_continuous R).comp continuous_snd).mul ((eucJet1_continuous hS).mul hDc)
  have hgI : IntegrableOn (fun z : Plane =>
      etaCutoff R z.2 * (eucJet1 (Cyl.curl (v s)) z * ‖iteratedFDeriv ℝ 1 (v s) z‖))
      (Cyl.cell c) :=
    apHD_integ (c := c) (R0 := 2 * R) hgc (fun z hz => by
      simp [apcc_eta_eq_zero hR0 hz.le])
  have hg0 : 0 ≤ ∫ z in Cyl.cell c, etaCutoff R z.2 *
      (eucJet1 (Cyl.curl (v s)) z * ‖iteratedFDeriv ℝ 1 (v s) z‖) :=
    integral_nonneg (fun z => mul_nonneg (apcc_eta_nonneg R z.2)
      (mul_nonneg (eucJet1_nonneg _ _) (norm_nonneg _)))
  have hpt : ∀ z : Plane,
      -(etaCutoff R z.2 * (Cyl.partialQ (Cyl.curl (v s)) z * Cyl.partialQ (v s) z 0
          * Cyl.partialQ (Cyl.curl (v s)) z
        + Cyl.partialQ (Cyl.curl (v s)) z * Cyl.partialQ (v s) z 1 *
            Cyl.partialEta (Cyl.curl (v s)) z
        + Cyl.partialEta (Cyl.curl (v s)) z * Cyl.partialEta (v s) z 0 *
            Cyl.partialQ (Cyl.curl (v s)) z
        + Cyl.partialEta (Cyl.curl (v s)) z * Cyl.partialEta (v s) z 1 *
            Cyl.partialEta (Cyl.curl (v s)) z))
        ≤ 2 * (etaCutoff R z.2 *
          (eucJet1 (Cyl.curl (v s)) z * ‖iteratedFDeriv ℝ 1 (v s) z‖)) := by
    intro z
    have hη := apcc_eta_nonneg R z.2
    have hD0 : 0 ≤ ‖iteratedFDeriv ℝ 1 (v s) z‖ := norm_nonneg _
    have ha : |Cyl.partialQ (v s) z 0| ≤ ‖iteratedFDeriv ℝ 1 (v s) z‖ := by
      rw [tri_partialQ_eq hdv z, norm_iteratedFDeriv_one]
      exact tri_abs_comp_le z eQ norm_eQ.le 0
    have hb : |Cyl.partialQ (v s) z 1| ≤ ‖iteratedFDeriv ℝ 1 (v s) z‖ := by
      rw [tri_partialQ_eq hdv z, norm_iteratedFDeriv_one]
      exact tri_abs_comp_le z eQ norm_eQ.le 1
    have hc' : |Cyl.partialEta (v s) z 0| ≤ ‖iteratedFDeriv ℝ 1 (v s) z‖ := by
      rw [tri_partialEta_eq hdv z, norm_iteratedFDeriv_one]
      exact tri_abs_comp_le z eE norm_eE.le 0
    have hd : |Cyl.partialEta (v s) z 1| ≤ ‖iteratedFDeriv ℝ 1 (v s) z‖ := by
      rw [tri_partialEta_eq hdv z, norm_iteratedFDeriv_one]
      exact tri_abs_comp_le z eE norm_eE.le 1
    have hT := tri_bound_real (Cyl.partialQ (Cyl.curl (v s)) z)
      (Cyl.partialEta (Cyl.curl (v s)) z) (Cyl.partialQ (v s) z 0) (Cyl.partialQ (v s) z 1)
      (Cyl.partialEta (v s) z 0) (Cyl.partialEta (v s) z 1) _ hD0 ha hb hc' hd
    have he : eucJet1 (Cyl.curl (v s)) z = Cyl.partialQ (Cyl.curl (v s)) z ^ 2
        + Cyl.partialEta (Cyl.curl (v s)) z ^ 2 := rfl
    rw [he]
    calc -(etaCutoff R z.2 * (Cyl.partialQ (Cyl.curl (v s)) z * Cyl.partialQ (v s) z 0
          * Cyl.partialQ (Cyl.curl (v s)) z
        + Cyl.partialQ (Cyl.curl (v s)) z * Cyl.partialQ (v s) z 1 *
            Cyl.partialEta (Cyl.curl (v s)) z
        + Cyl.partialEta (Cyl.curl (v s)) z * Cyl.partialEta (v s) z 0 *
            Cyl.partialQ (Cyl.curl (v s)) z
        + Cyl.partialEta (Cyl.curl (v s)) z * Cyl.partialEta (v s) z 1 *
            Cyl.partialEta (Cyl.curl (v s)) z))
        = etaCutoff R z.2 * (-(Cyl.partialQ (Cyl.curl (v s)) z * Cyl.partialQ (v s) z 0
          * Cyl.partialQ (Cyl.curl (v s)) z
        + Cyl.partialQ (Cyl.curl (v s)) z * Cyl.partialQ (v s) z 1 *
            Cyl.partialEta (Cyl.curl (v s)) z
        + Cyl.partialEta (Cyl.curl (v s)) z * Cyl.partialEta (v s) z 0 *
            Cyl.partialQ (Cyl.curl (v s)) z
        + Cyl.partialEta (Cyl.curl (v s)) z * Cyl.partialEta (v s) z 1 *
            Cyl.partialEta (Cyl.curl (v s)) z)) := by ring
      _ ≤ etaCutoff R z.2 * |Cyl.partialQ (Cyl.curl (v s)) z * Cyl.partialQ (v s) z 0
          * Cyl.partialQ (Cyl.curl (v s)) z
        + Cyl.partialQ (Cyl.curl (v s)) z * Cyl.partialQ (v s) z 1 *
            Cyl.partialEta (Cyl.curl (v s)) z
        + Cyl.partialEta (Cyl.curl (v s)) z * Cyl.partialEta (v s) z 0 *
            Cyl.partialQ (Cyl.curl (v s)) z
        + Cyl.partialEta (Cyl.curl (v s)) z * Cyl.partialEta (v s) z 1 *
            Cyl.partialEta (Cyl.curl (v s)) z| :=
          mul_le_mul_of_nonneg_left (neg_le_abs _) hη
      _ ≤ etaCutoff R z.2 * (2 * ‖iteratedFDeriv ℝ 1 (v s) z‖ *
          (Cyl.partialQ (Cyl.curl (v s)) z ^ 2 + Cyl.partialEta (Cyl.curl (v s)) z ^ 2)) :=
          mul_le_mul_of_nonneg_left hT hη
      _ = 2 * (etaCutoff R z.2 * ((Cyl.partialQ (Cyl.curl (v s)) z ^ 2
          + Cyl.partialEta (Cyl.curl (v s)) z ^ 2) * ‖iteratedFDeriv ℝ 1 (v s) z‖)) := by ring
  have hmain : -(∫ z in Cyl.cell c, etaCutoff R z.2 * (Cyl.partialQ (Cyl.curl (v s)) z
          * Cyl.partialQ (v s) z 0 * Cyl.partialQ (Cyl.curl (v s)) z
        + Cyl.partialQ (Cyl.curl (v s)) z * Cyl.partialQ (v s) z 1 *
            Cyl.partialEta (Cyl.curl (v s)) z
        + Cyl.partialEta (Cyl.curl (v s)) z * Cyl.partialEta (v s) z 0 *
            Cyl.partialQ (Cyl.curl (v s)) z
        + Cyl.partialEta (Cyl.curl (v s)) z * Cyl.partialEta (v s) z 1 *
            Cyl.partialEta (Cyl.curl (v s)) z))
      ≤ 2 * ∫ z in Cyl.cell c, etaCutoff R z.2 *
          (eucJet1 (Cyl.curl (v s)) z * ‖iteratedFDeriv ℝ 1 (v s) z‖) := by
    by_cases hfI : Integrable (fun z : Plane => etaCutoff R z.2 * (Cyl.partialQ (Cyl.curl (v s)) z
          * Cyl.partialQ (v s) z 0 * Cyl.partialQ (Cyl.curl (v s)) z
        + Cyl.partialQ (Cyl.curl (v s)) z * Cyl.partialQ (v s) z 1 *
            Cyl.partialEta (Cyl.curl (v s)) z
        + Cyl.partialEta (Cyl.curl (v s)) z * Cyl.partialEta (v s) z 0 *
            Cyl.partialQ (Cyl.curl (v s)) z
        + Cyl.partialEta (Cyl.curl (v s)) z * Cyl.partialEta (v s) z 1 *
            Cyl.partialEta (Cyl.curl (v s)) z)) (volume.restrict (Cyl.cell c))
    · have h := integral_mono hfI.neg (hgI.const_mul 2) (fun z => hpt z)
      simp only [Pi.neg_apply] at h
      rw [integral_neg, integral_const_mul] at h
      exact h
    · rw [integral_undef hfI, neg_zero]
      linarith
  unfold apL2X apCutTri
  linarith

end UnforcedLeray.Short.PartI
