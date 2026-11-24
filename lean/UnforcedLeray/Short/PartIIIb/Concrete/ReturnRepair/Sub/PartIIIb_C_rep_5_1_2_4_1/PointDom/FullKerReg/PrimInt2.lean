import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.PrimInt1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.ParamInt
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.RealIneq

/-!
# `primInt A w` is `C²` with sharp derivative bounds

For `A` of class `C²` with the decay `|A| ≤ K|x|^{-4}`, `|DA| ≤ K|x|^{-5}`, `|D²A| ≤ K|x|^{-6}` and a
shift `w` with `w₀ ≤ ρ₀`: on `{q₀ > ρ₀ + δ}` the primitive `primInt A w` is `C²`, and its value, first
and second derivative are `≤ Cp K / (2((q₀ - ρ₀)² + (q₂ - w₂)²))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

/-- The constant of `primInt_main`. -/
def primCp (ρ₀ δ : ℝ) : ℝ := (2 + (ρ₀ / δ + 1)) * (1 + (δ ^ 2)⁻¹)

theorem primCp_nonneg {ρ₀ δ : ℝ} (hρ₀ : 0 ≤ ρ₀) (hδ : 0 < δ) : 0 ≤ primCp ρ₀ δ := by
  unfold primCp; positivity

/-- Pointwise bound of the three integrand-derivative norms. -/
theorem prim_pt {A : Space → ℝ} (hA : ContDiff ℝ 2 A) (w q : Space) {K ρ₀ δ : ℝ} (hK : 0 ≤ K)
    (hρ₀ : 0 ≤ ρ₀) (hδ : 0 < δ) (hw : w 0 ≤ ρ₀)
    (b0 : ∀ x : Space, x ≠ 0 → |A x| ≤ K * (‖x‖ ^ 4)⁻¹)
    (b1 : ∀ x : Space, x ≠ 0 → ‖iteratedFDeriv ℝ 1 A x‖ ≤ K * (‖x‖ ^ 5)⁻¹)
    (b2 : ∀ x : Space, x ≠ 0 → ‖iteratedFDeriv ℝ 2 A x‖ ≤ K * (‖x‖ ^ 6)⁻¹)
    (u : ℝ) (hu : 0 ≤ u) (hq : ρ₀ + δ ≤ q 0) (b : ℝ) (hb : b ^ 2 ≤ (q 2 - w 2) ^ 2) :
    let v := q 0 + u - ρ₀
    ‖iteratedFDeriv ℝ 0 (fun q' => primF A w q' u) q‖ ≤ primCp ρ₀ δ * K * (v * (((v ^ 2 + b ^ 2) ^ 2)⁻¹)) ∧
    ‖iteratedFDeriv ℝ 1 (fun q' => primF A w q' u) q‖ ≤ primCp ρ₀ δ * K * (v * (((v ^ 2 + b ^ 2) ^ 2)⁻¹)) ∧
    ‖iteratedFDeriv ℝ 2 (fun q' => primF A w q' u) q‖ ≤ primCp ρ₀ δ * K * (v * (((v ^ 2 + b ^ 2) ^ 2)⁻¹)) := by
  intro v
  have hv : δ ≤ v := by simp only [v]; linarith
  have hlow := prim_shift_lower q w u ρ₀ hw (by linarith)
  have ht : v ^ 2 + b ^ 2 ≤ ‖q + (u • primE0 - w)‖ ^ 2 := by simp only [v]; nlinarith
  have hx : q + (u • primE0 - w) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at ht
    have : 0 < v ^ 2 := by have := lt_of_lt_of_le hδ hv; positivity
    nlinarith [sq_nonneg b]
  obtain ⟨h0, h1, h2⟩ := primF_iter_bound hA w q u
  have hqu : |q 0 + u| = ρ₀ + v := by
    rw [abs_of_nonneg (by linarith)]; simp only [v]; ring
  rw [hqu] at h0 h1 h2
  obtain ⟨p0, p1, p2⟩ := primPt hK hρ₀ hδ hv ht (norm_nonneg _) (abs_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (b0 _ hx) (b1 _ hx) (b2 _ hx)
  exact ⟨h0.trans p0, h1.trans p1, h2.trans p2⟩

theorem prim_dec {v c : ℝ} (hc : 0 < c) (hv : c ≤ v) :
    v * (((v ^ 2 + 0 ^ 2) ^ 2)⁻¹) ≤ c * (((c ^ 2 + 0 ^ 2) ^ 2)⁻¹) := by
  have hv0 : 0 < v := lt_of_lt_of_le hc hv
  have e1 : v * (((v ^ 2 + 0 ^ 2) ^ 2)⁻¹) = (v ^ 3)⁻¹ := by field_simp; ring
  have e2 : c * (((c ^ 2 + 0 ^ 2) ^ 2)⁻¹) = (c ^ 3)⁻¹ := by field_simp; ring
  rw [e1, e2]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hc.le hv 3)

end UnforcedLeray.Short.PartIIIb.Concrete

end
