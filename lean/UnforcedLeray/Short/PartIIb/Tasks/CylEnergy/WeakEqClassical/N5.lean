import UnforcedLeray.Short.PartIIb.Sub.T22_2

/-!


`CylRegularMem` (Sub/T22_2.lean): for `ν, c, m, s, T`, `0 < c`, `0 ≤ m`, a regular cylinder flow
`IsRegularCylFlow c ν v s T ω` and `σ ∈ [s, T]`, the slice `ω σ` lies in `L²(cellMeasure c m)`.

Route. The slice is `C²` (hence continuous) and, by the decay clause of `IsRegularCylFlow` with
exponent `m + 1`, satisfies `|ω σ x| · (1 + η²)^(m+1) ≤ C` uniformly. On the centered cell,
`jb ≤ (1 + c²/4)(1 + η²)` and `1 + q² ≤ 1 + c²/4`, so the density `jb^m` times `ω²` is bounded by
a constant times `(1 + q²)⁻¹ (1 + η²)⁻¹`, which is integrable on the plane (product of two
integrable one-variable functions). Source: `the November 2 reference manuscript`
lines 2074-2105 (the weighted `L²` of the regular solution in the duality argument).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIb

/-- On the centered cell, `jb ≤ (1 + c²/4)(1 + η²)`. -/
theorem jb_le_cell_aux {c : ℝ} (x : B0579.Plane) (hx : x ∈ B0579.cell c) :
    B0579.jb x ≤ (1 + c ^ 2 / 4) * (1 + x.2 ^ 2) := by
  have hx' : x ∈ Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ) := hx
  obtain ⟨h1, h2⟩ := Set.mem_Ico.mp (Set.mem_prod.mp hx').1
  have hsq : x.1 ^ 2 ≤ c ^ 2 / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.2 h2.le) (by linarith : (0 : ℝ) ≤ c / 2 + x.1)]
  unfold B0579.jb
  nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg x.2)]

/-- Pointwise weighted bound on the cell: `jb^m · g² ≤ K · (1 + q²)⁻¹ (1 + η²)⁻¹`, where `g`
has the decay `|g| · (1 + η²)^(m+1) ≤ C`. -/
theorem cyl_weight_pt {c m C : ℝ} (hm : 0 ≤ m) (g : B0579.Plane → ℝ) (x : B0579.Plane)
    (hx : x ∈ B0579.cell c) (hC : |g x| * (1 + x.2 ^ 2) ^ (m + 1) ≤ C) :
    B0579.jb x ^ m * (g x) ^ 2 ≤
      ((1 + c ^ 2 / 4) ^ m * (C ^ 2 * (1 + c ^ 2 / 4))) *
        ((1 + x.1 ^ 2)⁻¹ * (1 + x.2 ^ 2)⁻¹) := by
  have hx' : x ∈ Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ) := hx
  obtain ⟨h1, h2⟩ := Set.mem_Ico.mp (Set.mem_prod.mp hx').1
  have hsq : x.1 ^ 2 ≤ c ^ 2 / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.2 h2.le) (by linarith : (0 : ℝ) ≤ c / 2 + x.1)]
  have hwA : 1 + x.1 ^ 2 ≤ 1 + c ^ 2 / 4 := by linarith
  have hjb : B0579.jb x ≤ (1 + c ^ 2 / 4) * (1 + x.2 ^ 2) := jb_le_cell_aux x hx
  have hu1 : 1 ≤ 1 + x.2 ^ 2 := by nlinarith [sq_nonneg x.2]
  have hu0 : 0 < 1 + x.2 ^ 2 := by linarith
  have hw0 : 0 < 1 + x.1 ^ 2 := by nlinarith [sq_nonneg x.1]
  have hA0 : 0 < 1 + c ^ 2 / 4 := by nlinarith [sq_nonneg c]
  have hjb0 : 0 ≤ B0579.jb x := (B0579.jb_pos x).le
  -- `jb^m ≤ A^m · u^m`
  have hmpow : B0579.jb x ^ m ≤ (1 + c ^ 2 / 4) ^ m * (1 + x.2 ^ 2) ^ m := by
    calc B0579.jb x ^ m ≤ ((1 + c ^ 2 / 4) * (1 + x.2 ^ 2)) ^ m :=
          Real.rpow_le_rpow hjb0 hjb hm
      _ = (1 + c ^ 2 / 4) ^ m * (1 + x.2 ^ 2) ^ m :=
          Real.mul_rpow hA0.le hu0.le
  -- decay at exponent `m + 1` splits as `u^m · u`
  have hT : (1 + x.2 ^ 2) ^ (m + 1) = (1 + x.2 ^ 2) ^ m * (1 + x.2 ^ 2) := by
    rw [Real.rpow_add hu0, Real.rpow_one]
  have hT1 : 1 ≤ (1 + x.2 ^ 2) ^ (m + 1) := Real.one_le_rpow hu1 (by linarith)
  have hC0 : 0 ≤ C := by
    have h0 : 0 ≤ |g x| * (1 + x.2 ^ 2) ^ (m + 1) :=
      mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hu0.le _)
    linarith
  have hsq2 : (g x) ^ 2 * ((1 + x.2 ^ 2) ^ (m + 1)) ^ 2 ≤ C ^ 2 := by
    have h0 : 0 ≤ |g x| * (1 + x.2 ^ 2) ^ (m + 1) :=
      mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hu0.le _)
    have := mul_le_mul hC hC h0 hC0
    calc (g x) ^ 2 * ((1 + x.2 ^ 2) ^ (m + 1)) ^ 2
        = (|g x| * (1 + x.2 ^ 2) ^ (m + 1)) * (|g x| * (1 + x.2 ^ 2) ^ (m + 1)) := by
          rw [← sq_abs (g x)]; ring
      _ ≤ C * C := this
      _ = C ^ 2 := by ring
  -- `g² · u^m · u ≤ C²`
  have key : (1 + x.2 ^ 2) ^ m * (g x) ^ 2 * (1 + x.2 ^ 2) ≤ C ^ 2 := by
    have h3 : (g x) ^ 2 * (1 + x.2 ^ 2) ^ (m + 1) ≤ (g x) ^ 2 * ((1 + x.2 ^ 2) ^ (m + 1)) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
    rw [hT] at h3 hsq2
    nlinarith [sq_nonneg (g x)]
  -- inverses on the right-hand side
  obtain ⟨iu, hiu⟩ : ∃ z : ℝ, z = (1 + x.2 ^ 2)⁻¹ := ⟨_, rfl⟩
  obtain ⟨iw, hiw⟩ : ∃ z : ℝ, z = (1 + x.1 ^ 2)⁻¹ := ⟨_, rfl⟩
  rw [← hiu, ← hiw]
  have hiu0 : 0 < iu := by rw [hiu]; exact inv_pos.mpr hu0
  have hiw0 : 0 < iw := by rw [hiw]; exact inv_pos.mpr hw0
  have hiu1 : iu * (1 + x.2 ^ 2) = 1 := by rw [hiu]; exact inv_mul_cancel₀ hu0.ne'
  have hiw1 : iw * (1 + x.1 ^ 2) = 1 := by rw [hiw]; exact inv_mul_cancel₀ hw0.ne'
  -- `1 ≤ A · iw`
  have hwinv : 1 ≤ (1 + c ^ 2 / 4) * iw := by
    nlinarith [mul_nonneg (sub_nonneg.2 hwA) hiw0.le]
  -- `P g² ≤ C² iu`
  have hPg : (1 + x.2 ^ 2) ^ m * (g x) ^ 2 ≤ C ^ 2 * iu := by
    have e : (1 + x.2 ^ 2) ^ m * (g x) ^ 2
        = ((1 + x.2 ^ 2) ^ m * (g x) ^ 2 * (1 + x.2 ^ 2)) * iu := by
      have : (1 + x.2 ^ 2) ^ m * (g x) ^ 2 * (1 + x.2 ^ 2) * iu
          = (1 + x.2 ^ 2) ^ m * (g x) ^ 2 * (iu * (1 + x.2 ^ 2)) := by ring
      rw [this, hiu1, mul_one]
    rw [e]
    exact mul_le_mul_of_nonneg_right key hiu0.le
  have hPg0 : 0 ≤ (1 + x.2 ^ 2) ^ m * (g x) ^ 2 := by positivity
  calc B0579.jb x ^ m * (g x) ^ 2
      ≤ ((1 + c ^ 2 / 4) ^ m * (1 + x.2 ^ 2) ^ m) * (g x) ^ 2 :=
        mul_le_mul_of_nonneg_right hmpow (sq_nonneg _)
    _ = (1 + c ^ 2 / 4) ^ m * ((1 + x.2 ^ 2) ^ m * (g x) ^ 2) := by ring
    _ ≤ (1 + c ^ 2 / 4) ^ m * (C ^ 2 * iu) :=
        mul_le_mul_of_nonneg_left hPg (Real.rpow_nonneg hA0.le _)
    _ ≤ (1 + c ^ 2 / 4) ^ m * (C ^ 2 * (1 + c ^ 2 / 4)) * (iw * iu) := by
        have hC2 : 0 ≤ C ^ 2 * iu := mul_nonneg (sq_nonneg C) hiu0.le
        have hA' : 0 ≤ (1 + c ^ 2 / 4) ^ m := Real.rpow_nonneg hA0.le _
        nlinarith [mul_nonneg hA' (mul_nonneg hC2 (sub_nonneg.2 hwinv))]
    _ = ((1 + c ^ 2 / 4) ^ m * (C ^ 2 * (1 + c ^ 2 / 4))) * (iw * iu) := by ring

/-- The product weight `(1 + q²)⁻¹ (1 + η²)⁻¹` is integrable on the plane. -/
theorem integrable_inv_prod_aux :
    Integrable (fun z : B0579.Plane => (1 + z.1 ^ 2)⁻¹ * (1 + z.2 ^ 2)⁻¹) := by
  have h1 : Integrable (fun t : ℝ => (1 + t ^ 2)⁻¹) := integrable_inv_one_add_sq
  have h2 := h1.mul_prod h1
  rw [← Measure.volume_eq_prod] at h2
  exact h2

/-- **`PartII-b:T22/2/6`: slices of a regular flow lie in the weighted `L²`** (needed N5). -/
theorem cylRegularMem : UnforcedLeray.Short.IIb.CylRegularMem := by
  unfold CylRegularMem
  intro ν c m s T v ω hc hm hR σ hσ
  have hcont : Continuous (ω σ) := (hR.slice σ hσ).smooth.continuous
  obtain ⟨C, hC⟩ := hR.decay (m + 1)
  apply (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr
  unfold B0579.cellMeasure
  rw [integrable_withDensity_iff_integrable_coe_smul (B0579.measurable_density m)]
  have hH : Integrable (fun z : B0579.Plane =>
      (1 + c ^ 2 / 4) ^ m * (C ^ 2 * (1 + c ^ 2 / 4)) * ((1 + z.1 ^ 2)⁻¹ * (1 + z.2 ^ 2)⁻¹)) :=
    integrable_inv_prod_aux.const_mul _
  refine Integrable.mono' hH.integrableOn ?_ ?_
  · have hfc : Continuous (fun x : B0579.Plane =>
        ((B0579.density m x : ℝ≥0) : ℝ) • ‖ω σ x‖ ^ 2) := by
      simp only [B0579.coe_density, smul_eq_mul]
      exact (B0579.continuous_jb_rpow m).mul (hcont.norm.pow 2)
    exact hfc.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (B0579.measurableSet_cell c)] with x hx
    have hC' : |ω σ x| * (1 + x.2 ^ 2) ^ (m + 1) ≤ C := by
      have hp : 0 ≤ (1 + x.2 ^ 2) ^ (m + 1) := Real.rpow_nonneg (by nlinarith [sq_nonneg x.2]) _
      have hd := hC σ hσ x
      have hsum : 0 ≤ (|B0579.pd 0 (ω σ) x| + |B0579.pd 1 (ω σ) x| + |lapP (ω σ) x|) *
          (1 + x.2 ^ 2) ^ (m + 1) :=
        mul_nonneg (by positivity) hp
      nlinarith
    have hpt := cyl_weight_pt (c := c) hm (ω σ) x hx hC'
    have hnn : 0 ≤ B0579.jb x ^ m * (ω σ x) ^ 2 :=
      mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _)
    have hnn' : 0 ≤ B0579.jb x ^ m * ‖ω σ x‖ ^ 2 :=
      mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _)
    have hlhs : ‖((B0579.density m x : ℝ≥0) : ℝ) • ‖ω σ x‖ ^ 2‖ =
        B0579.jb x ^ m * (ω σ x) ^ 2 := by
      rw [B0579.coe_density, smul_eq_mul, Real.norm_of_nonneg hnn', Real.norm_eq_abs, sq_abs]
    rw [hlhs]
    exact hpt

end UnforcedLeray.Short.IIb
