import UnforcedLeray.Short.PartIIa.Sub.N02_3_7

/-!


Proves `gCEMinkowski` (the Prop `GCEMinkowski` in `Sub/N02_3_7.lean`, namespace `ZeroGradCutErrorAux`).
Method: `eLpNorm_add_le` in `L²(μ)`, converted to the integral form `(∫ F²)^{1/2}` by
`MemLp.eLpNorm_eq_integral_rpow_norm`, plus monotonicity of the integral for `0 ≤ g ≤ H`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

namespace GCEMinkowskiAux

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The `L²` norm of a real function in integral form. -/
theorem gce_eLpNorm_two_eq {F : α → ℝ} (hF : MemLp F 2 μ) :
    eLpNorm F 2 μ = ENNReal.ofReal ((∫ p, F p ^ 2 ∂μ) ^ (1 / 2 : ℝ)) := by
  rw [hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  have hpt : ∀ a, ‖F a‖ ^ (2 : ℝ) = F a ^ 2 := fun a => by
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  simp_rw [hpt]
  norm_num

/-- Triangle inequality in integral form. -/
theorem gce_norm_add_le {F G : α → ℝ} (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    (∫ p, (F p + G p) ^ 2 ∂μ) ^ (1 / 2 : ℝ)
      ≤ (∫ p, F p ^ 2 ∂μ) ^ (1 / 2 : ℝ) + (∫ p, G p ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  have hFG : MemLp (fun p => F p + G p) 2 μ := hF.add hG
  have hsum : eLpNorm (fun p => F p + G p) 2 μ ≤ eLpNorm F 2 μ + eLpNorm G 2 μ :=
    eLpNorm_add_le hF.aestronglyMeasurable hG.aestronglyMeasurable (by norm_num)
  have n0 : 0 ≤ (∫ p, F p ^ 2 ∂μ) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (integral_nonneg fun p => sq_nonneg _) _
  have n1 : 0 ≤ (∫ p, G p ^ 2 ∂μ) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (integral_nonneg fun p => sq_nonneg _) _
  rw [gce_eLpNorm_two_eq hFG, gce_eLpNorm_two_eq hF, gce_eLpNorm_two_eq hG,
    ← ENNReal.ofReal_add n0 n1] at hsum
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg n0 n1)).1 hsum

/-- Scaling by a nonnegative constant. -/
theorem gce_norm_const_mul {F : α → ℝ} (k : ℝ) (hk : 0 ≤ k) :
    (∫ p, (k * F p) ^ 2 ∂μ) ^ (1 / 2 : ℝ) = k * (∫ p, F p ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  have hpt : ∀ p, (k * F p) ^ 2 = k ^ 2 * F p ^ 2 := fun p => by ring
  simp_rw [hpt]
  rw [integral_const_mul, Real.mul_rpow (sq_nonneg k) (integral_nonneg fun p => sq_nonneg _)]
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hk]

end GCEMinkowskiAux

open GCEMinkowskiAux in
/-- **Minkowski for four nonnegative terms** (`GCEMinkowski`). -/
theorem gCEMinkowski : UnforcedLeray.Short.PartIIa.ZeroGradCutErrorAux.GCEMinkowski := by
  unfold ZeroGradCutErrorAux.GCEMinkowski
  intro μ g a₁ a₂ a₃ a₄ k₁ k₂ k₃ k₄ hk₁ hk₂ hk₃ hk₄ hg ha₁ ha₂ ha₃ ha₄ hgm hm₁ hm₂ hm₃ hm₄ hle
  have m1 : MemLp (fun p => k₁ * a₁ p) 2 μ := hm₁.const_mul k₁
  have m2 : MemLp (fun p => k₂ * a₂ p) 2 μ := hm₂.const_mul k₂
  have m3 : MemLp (fun p => k₃ * a₃ p) 2 μ := hm₃.const_mul k₃
  have m4 : MemLp (fun p => k₄ * a₄ p) 2 μ := hm₄.const_mul k₄
  have s2 : MemLp (fun p => k₁ * a₁ p + k₂ * a₂ p) 2 μ := m1.add m2
  have s3 : MemLp (fun p => k₁ * a₁ p + k₂ * a₂ p + k₃ * a₃ p) 2 μ := s2.add m3
  have hH : MemLp (fun p => k₁ * a₁ p + k₂ * a₂ p + k₃ * a₃ p + k₄ * a₄ p) 2 μ := s3.add m4
  have step1 : (∫ p, g p ^ 2 ∂μ) ^ (1 / 2 : ℝ)
      ≤ (∫ p, (k₁ * a₁ p + k₂ * a₂ p + k₃ * a₃ p + k₄ * a₄ p) ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    apply Real.rpow_le_rpow (integral_nonneg fun p => sq_nonneg _) _ (by norm_num)
    apply integral_mono hgm.integrable_sq hH.integrable_sq
    intro p
    have h0 : 0 ≤ g p := hg p
    have h1 := hle p
    nlinarith
  have step2 := gce_norm_add_le s3 m4
  have step3 := gce_norm_add_le s2 m3
  have step4 := gce_norm_add_le m1 m2
  have e1 := gce_norm_const_mul (μ := μ) (F := a₁) k₁ hk₁
  have e2 := gce_norm_const_mul (μ := μ) (F := a₂) k₂ hk₂
  have e3 := gce_norm_const_mul (μ := μ) (F := a₃) k₃ hk₃
  have e4 := gce_norm_const_mul (μ := μ) (F := a₄) k₄ hk₄
  linarith

end UnforcedLeray.Short.PartIIa
