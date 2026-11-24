import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-!
# A quadratic Banach-space contraction criterion

The general criterion quoted at `paper/main.tex`, lines 414--418. The bilinear
and linear maps are actual bounded maps of a complete real normed space.
This file proves the fixed-point implication; it does not establish the
Navier--Stokes operator estimates needed to instantiate the criterion.
-/

noncomputable section
open Set Metric
namespace UnforcedLeray.QuadraticContraction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The quadratic affine map appearing in the manuscript. -/
def quadraticMap (B : E →L[ℝ] E →L[ℝ] E) (L : E →L[ℝ] E) (G : E) (z : E) : E :=
  B z z + L z + G

theorem norm_bilinear_le (B : E →L[ℝ] E →L[ℝ] E) (x y : E) :
    ‖B x y‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ := by
  exact ((B x).le_opNorm y).trans
    (mul_le_mul_of_nonneg_right (B.le_opNorm x) (norm_nonneg y))

/-- Norm bound for the affine quadratic map on a closed ball. -/
theorem norm_quadraticMap_le (B : E →L[ℝ] E →L[ℝ] E) (L : E →L[ℝ] E)
    (G : E) {ρ : ℝ} (hρ : 0 ≤ ρ) {z : E} (hz : ‖z‖ ≤ ρ) :
    ‖quadraticMap B L G z‖ ≤ ‖B‖ * ρ ^ 2 + ‖L‖ * ρ + ‖G‖ := by
  have hb : ‖B z z‖ ≤ ‖B‖ * ρ ^ 2 := by
    calc
      ‖B z z‖ ≤ ‖B‖ * ‖z‖ * ‖z‖ := norm_bilinear_le B z z
      _ ≤ ‖B‖ * ρ * ρ := by gcongr
      _ = ‖B‖ * ρ ^ 2 := by ring
  have hl : ‖L z‖ ≤ ‖L‖ * ρ :=
    (L.le_opNorm z).trans (mul_le_mul_of_nonneg_left hz (norm_nonneg L))
  calc
    ‖quadraticMap B L G z‖ ≤ ‖B z z + L z‖ + ‖G‖ := norm_add_le _ _
    _ ≤ (‖B z z‖ + ‖L z‖) + ‖G‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ‖B‖ * ρ ^ 2 + ‖L‖ * ρ + ‖G‖ := by linarith

/-- Difference bound, with both bilinear contributions explicitly retained. -/
theorem norm_quadraticMap_sub_le (B : E →L[ℝ] E →L[ℝ] E) (L : E →L[ℝ] E)
    (G : E) {ρ : ℝ} (_hρ : 0 ≤ ρ) {x y : E} (hx : ‖x‖ ≤ ρ) (hy : ‖y‖ ≤ ρ) :
    ‖quadraticMap B L G x - quadraticMap B L G y‖ ≤
      (2 * ρ * ‖B‖ + ‖L‖) * ‖x - y‖ := by
  have heq : quadraticMap B L G x - quadraticMap B L G y =
      B (x - y) x + B y (x - y) + L (x - y) := by
    simp only [quadraticMap, map_sub, sub_apply]
    abel
  have hb1 : ‖B (x - y) x‖ ≤ ‖B‖ * ‖x - y‖ * ρ :=
    (norm_bilinear_le B (x - y) x).trans (by gcongr)
  have hb2 : ‖B y (x - y)‖ ≤ ‖B‖ * ρ * ‖x - y‖ :=
    (norm_bilinear_le B y (x - y)).trans (by gcongr)
  rw [heq]
  calc
    ‖B (x - y) x + B y (x - y) + L (x - y)‖ ≤
        ‖B (x - y) x + B y (x - y)‖ + ‖L (x - y)‖ := norm_add_le _ _
    _ ≤ (‖B (x - y) x‖ + ‖B y (x - y)‖) + ‖L (x - y)‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (‖B‖ * ‖x - y‖ * ρ + ‖B‖ * ρ * ‖x - y‖) + ‖L‖ * ‖x - y‖ :=
      add_le_add (add_le_add hb1 hb2) (L.le_opNorm (x - y))
    _ = (2 * ρ * ‖B‖ + ‖L‖) * ‖x - y‖ := by ring

/-- The manuscript's strict scalar criterion provides one unique fixed point
in the closed ball, by the Banach fixed-point theorem. -/
theorem existsUnique_fixedPoint [CompleteSpace E]
    (B : E →L[ℝ] E →L[ℝ] E) (L : E →L[ℝ] E) (G : E) {ρ : ℝ}
    (hρ : 0 < ρ) (hsmall : 2 * ρ * ‖B‖ + ‖L‖ + ‖G‖ / ρ < 1) :
    ∃! z : E, ‖z‖ ≤ ρ ∧ z = B z z + L z + G := by
  have hq : 2 * ρ * ‖B‖ + ‖L‖ < 1 := by
    have hg : 0 ≤ ‖G‖ / ρ := div_nonneg (norm_nonneg G) hρ.le
    linarith
  have hscaled := mul_lt_mul_of_pos_right hsmall hρ
  rw [add_mul, div_mul_cancel₀ _ hρ.ne', one_mul] at hscaled
  have hball : ‖B‖ * ρ ^ 2 + ‖L‖ * ρ + ‖G‖ < ρ := by
    nlinarith [mul_nonneg (norm_nonneg B) (sq_nonneg ρ)]
  let K : NNReal := ⟨2 * ρ * ‖B‖ + ‖L‖, by positivity⟩
  have hm : MapsTo (quadraticMap B L G) (closedBall (0 : E) ρ) (closedBall 0 ρ) := by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz ⊢
    exact (norm_quadraticMap_le B L G hρ.le hz).trans hball.le
  have hc : ContractingWith K (hm.restrict (quadraticMap B L G)
      (closedBall (0 : E) ρ) (closedBall 0 ρ)) := by
    constructor
    · exact hq
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      change dist (quadraticMap B L G x.val) (quadraticMap B L G y.val) ≤
        (K : ℝ) * dist x.val y.val
      simp only [dist_eq_norm]
      exact norm_quadraticMap_sub_le B L G hρ.le
        (mem_closedBall_zero_iff.mp x.property) (mem_closedBall_zero_iff.mp y.property)
  have hzero : (0 : E) ∈ closedBall (0 : E) ρ := by
    simp [hρ.le]
  obtain ⟨z, hz, hfix, _, _⟩ := ContractingWith.exists_fixedPoint'
    isClosed_closedBall.isComplete hm hc hzero (edist_ne_top _ _)
  have hznorm : ‖z‖ ≤ ρ := mem_closedBall_zero_iff.mp hz
  have hzfix : z = B z z + L z + G := hfix.symm
  refine ⟨z, ⟨hznorm, hzfix⟩, ?_⟩
  rintro w ⟨hw, hwfix⟩
  have hd := norm_quadraticMap_sub_le B L G hρ.le hw hznorm
  change ‖(B w w + L w + G) - (B z z + L z + G)‖ ≤
    (2 * ρ * ‖B‖ + ‖L‖) * ‖w - z‖ at hd
  rw [← hwfix, ← hzfix] at hd
  have hnorm : ‖w - z‖ = 0 := by nlinarith [norm_nonneg (w - z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end UnforcedLeray.QuadraticContraction
