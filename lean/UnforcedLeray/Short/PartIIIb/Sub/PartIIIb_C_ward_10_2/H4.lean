import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_2.H3

/-!
# Helpers for `wardStreamCorrYoungL2_proved` (4): the cylinder kernel and the radial integral

Source of record: `the November 2 reference manuscript` (73 pages), 3687-3697.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The translation-invariant cylinder majorant `M(x₃) 1_{|x₁|,|x₂| ≤ A}`. -/
def w2k (r0 D A : ℝ) (x : Space) : ℝ≥0∞ :=
  if |x 0| ≤ A ∧ |x 1| ≤ A then ENNReal.ofReal (w2M r0 D (x 2)) else 0

theorem w2k_measurable (r0 D A : ℝ) : Measurable (w2k r0 D A) := by
  unfold w2k
  refine Measurable.ite ?_ ?_ measurable_const
  · have h0 : Measurable (fun x : Space => x 0) := (EuclideanSpace.proj (0 : Fin 3)).continuous.measurable
    have h1 : Measurable (fun x : Space => x 1) := (EuclideanSpace.proj (1 : Fin 3)).continuous.measurable
    exact (measurableSet_le h0.abs measurable_const).inter (measurableSet_le h1.abs measurable_const)
  · exact ENNReal.measurable_ofReal.comp
      ((w2M_measurable r0 D).comp (EuclideanSpace.proj (2 : Fin 3)).continuous.measurable)

theorem w2k_lintegral_ne_top {r0 D : ℝ} (hD : 0 < D) (A : ℝ) :
    ∫⁻ x : Space, w2k r0 D A x ≠ ⊤ := by
  have h := w2_lintegral_cyl (fun w => ENNReal.ofReal (w2M r0 D w))
    (ENNReal.measurable_ofReal.comp (w2M_measurable r0 D)) A
  have h' : ∫⁻ x : Space, w2k r0 D A x = ENNReal.ofReal (2 * A) ^ 2 *
      ∫⁻ w, ENNReal.ofReal (w2M r0 D w) := h
  rw [h']
  refine ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ?_
  exact (w2M_integrable hD).lintegral_lt_top.ne

theorem w2_norm_sq (x : Space) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three]

/-- **The radial integral of the order-four kernel** (source 3687-3697): for a source point `z`
with `ϱ z ≤ r₀` and a receiver `y` with `ϱ y ≤ r₂`, the radial `ρ dρ` integral over the ray
`ρ ≥ r ≥ r₀ + D` of the gap-truncated order-four kernel is bounded by the cylinder majorant. -/
theorem w2_radial_kernel {r0 D r2 : ℝ} (hr0 : 0 ≤ r0) (hD : 0 < D) {y z : Space} {l : ℝ}
    (hl : 0 < l) (hl1 : l < 1) (hy : ϱ y ≤ r2) (hz : ϱ z ≤ r0) {r : ℝ} (hr : r0 + D ≤ r) :
    ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ * IIIa.sepKd 0 D ((!₂[ρ, 0, y 2] : Space) - l • z) ≤
      w2k r0 D (r2 + r0) (y - l • z) := by
  set w : ℝ := y 2 - l * z 2 with hw
  have hz0 : |z 0| ≤ ϱ z := by
    unfold ϱ; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (z 1)])
  have hz1 : |z 1| ≤ ϱ z := by
    unfold ϱ; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (z 0)])
  have hy0 : |y 0| ≤ ϱ y := by
    unfold ϱ; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (y 1)])
  have hy1 : |y 1| ≤ ϱ y := by
    unfold ϱ; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (y 0)])
  have hzz : z 0 ^ 2 + z 1 ^ 2 = ϱ z ^ 2 := by
    unfold ϱ; rw [Real.sq_sqrt (by positivity)]
  have hϱz0 : 0 ≤ ϱ z := ϱ_nonneg z
  have hlz : l * ϱ z ≤ r0 := by nlinarith
  calc ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ * IIIa.sepKd 0 D ((!₂[ρ, 0, y 2] : Space) - l • z)
      ≤ ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ * (((ρ - r0) ^ 2 + w ^ 2)⁻¹) ^ 2) := by
        refine setLIntegral_mono' measurableSet_Ioi fun ρ hρ => ?_
        have hρ' : r < ρ := hρ
        have hρ0 : 0 ≤ ρ := by linarith
        set x : Space := (!₂[ρ, 0, y 2] : Space) - l • z with hx
        have hx0 : x 0 = ρ - l * z 0 := by simp [hx]
        have hx1 : x 1 = - (l * z 1) := by simp [hx]
        have hx2 : x 2 = w := by simp [hx, hw]
        have hcomp : (ρ - l * ϱ z) ^ 2 ≤ x 0 ^ 2 + x 1 ^ 2 := by
          rw [hx0, hx1]
          have : z 0 ≤ ϱ z := (le_abs_self _).trans hz0
          have h3 : (ρ - l * z 0) ^ 2 + (-(l * z 1)) ^ 2 - (ρ - l * ϱ z) ^ 2 =
              2 * (ρ * l * (ϱ z - z 0)) + l ^ 2 * (z 0 ^ 2 + z 1 ^ 2 - ϱ z ^ 2) := by ring
          rw [hzz, sub_self, mul_zero, add_zero] at h3
          have h4 : 0 ≤ ρ * l * (ϱ z - z 0) :=
            mul_nonneg (mul_nonneg hρ0 hl.le) (sub_nonneg.2 this)
          linarith
        have hρl : ρ - r0 ≤ ρ - l * ϱ z := by linarith
        have hρpos : D ≤ ρ - r0 := by linarith
        have hsq : (ρ - r0) ^ 2 ≤ (ρ - l * ϱ z) ^ 2 := by
          apply pow_le_pow_left₀ (by linarith) hρl
        have hn2 : (ρ - r0) ^ 2 + w ^ 2 ≤ ‖x‖ ^ 2 := by
          rw [w2_norm_sq, hx2]; nlinarith
        have hDn : D ≤ ‖x‖ := by
          have : D ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [sq_nonneg w, mul_self_nonneg D]
          exact le_of_sq_le_sq this (norm_nonneg _)
        have hpos : 0 < (ρ - r0) ^ 2 + w ^ 2 := by
          have : 0 < ρ - r0 := by linarith
          positivity
        unfold IIIa.sepKd
        rw [if_pos hDn, ← ENNReal.ofReal_mul hρ0]
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ hρ0
        have hn0 : 0 < ‖x‖ := lt_of_lt_of_le hD hDn
        have e1 : ‖x‖ ^ (-4 - ((0 : ℕ) : ℝ)) = ((‖x‖ ^ 2)⁻¹) ^ 2 := by
          rw [show (-4 - ((0 : ℕ) : ℝ)) = -(4 : ℕ) by norm_num, Real.rpow_neg hn0.le,
            Real.rpow_natCast, inv_pow, ← pow_mul]
        rw [e1]
        gcongr
    _ ≤ ENNReal.ofReal (w2M r0 D w) := w2_radial hr0 hD hr w
    _ = w2k r0 D (r2 + r0) (y - l • z) := by
        unfold w2k
        have h0 : |(y - l • z) 0| ≤ r2 + r0 := by
          have : (y - l • z) 0 = y 0 - l * z 0 := by simp
          rw [this]
          calc |y 0 - l * z 0| ≤ |y 0| + |l * z 0| := abs_sub _ _
            _ ≤ r2 + r0 := by
              rw [abs_mul, abs_of_pos hl]
              nlinarith [abs_nonneg (z 0)]
        have h1 : |(y - l • z) 1| ≤ r2 + r0 := by
          have : (y - l • z) 1 = y 1 - l * z 1 := by simp
          rw [this]
          calc |y 1 - l * z 1| ≤ |y 1| + |l * z 1| := abs_sub _ _
            _ ≤ r2 + r0 := by
              rw [abs_mul, abs_of_pos hl]
              nlinarith [abs_nonneg (z 1)]
        rw [if_pos ⟨h0, h1⟩]
        congr 2

end UnforcedLeray.Short.PartIIIb.Concrete
end
