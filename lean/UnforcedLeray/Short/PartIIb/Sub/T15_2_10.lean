import UnforcedLeray.Short.PartIIb.Sub.T15_2
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogTranslateContinuous

/-!
# Part II-b, task `PartII-b:T15/2/10`: decomposition of `LogAvgConverges`

Source: `the November 2 reference manuscript`, lines 1975-1979.
Three leaves (a.e. slice integrability, joint measurability, pointwise Cauchy-Schwarz) and the
assembly `logAvgConverges_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- **Leaf `PartII-b:T15/2/10/1`** (a.e. slice integrability; SP 1975-1979). For `G ∈ L²(logMeas c)`
and each `h`, for a.e. `x` the slice `σ ↦ G(x.1 + σ, x.2)` is interval integrable on `[0, h]`.
Proof: `‖G(x.1+σ, x.2)‖ₑ²` integrated over `x` (Tonelli, translation invariance of `logMeas c` in
the first coordinate) and `σ ∈ uIoc 0 h` is `|h| ‖G‖²_{L²} < ∞`; so for a.e. `x` the slice is in
`L²(uIoc 0 h)`, hence in `L¹` of a finite-measure set. -/
def LogAcSlice : Prop :=
  ∀ (c : ℝ) (G : Coord → ℂ), 0 < c → MemLp G 2 (logMeas c) → ∀ h : ℝ,
    ∀ᵐ x ∂(logMeas c), IntervalIntegrable (fun σ : ℝ => G (x.1 + σ, x.2)) volume 0 h

/-- **Leaf `PartII-b:T15/2/10/2`** (joint measurability). For `G` a.e.-strongly measurable for
`logMeas c`, `(σ, x) ↦ ‖G(x.1 + σ, x.2) - G x‖ₑ²` is a.e.-measurable for `volume.prod (logMeas c)`.
Proof: `(σ, x) ↦ (x.1 + σ, x.2)` is quasi-measure-preserving
(`volume.prod (logMeas c) → logMeas c`, shear of a product with translation-invariant first
factor), so `G ∘ shear` is a.e.-strongly measurable. -/
def LogAcAEMeas : Prop :=
  ∀ (c : ℝ) (G : Coord → ℂ), AEStronglyMeasurable G (logMeas c) →
    AEMeasurable (fun p : ℝ × Coord => ‖G (p.2.1 + p.1, p.2.2) - G p.2‖ₑ ^ 2)
      (volume.prod (logMeas c))

/-- **Leaf `PartII-b:T15/2/10/3`** (pointwise Cauchy-Schwarz). For `f` interval integrable on
`[0, h]`: `‖h⁻¹ ∫_0^h f‖ₑ² ≤ |h|⁻¹ ∫⁻_{uIoc 0 h} ‖f‖ₑ²`. Proof: `enorm_integral_le_lintegral_enorm`
and `ENNReal.lintegral_mul_le_Lp_mul_Lq` with `p = q = 2`, `f₁ = 1`. -/
def LogAcCS : Prop :=
  ∀ (h : ℝ) (f : ℝ → ℂ), IntervalIntegrable f volume 0 h →
    ‖(h⁻¹ : ℝ) • ∫ σ in (0 : ℝ)..h, f σ‖ₑ ^ 2 ≤
      ENNReal.ofReal |h|⁻¹ * ∫⁻ σ in Set.uIoc (0 : ℝ) h, ‖f σ‖ₑ ^ 2

theorem logAvgConverges_of (h1 : LogAcSlice) (h2 : LogAcAEMeas) (h3 : LogAcCS)
    (hT : LogTranslateContinuous) : LogAvgConverges := by
  intro c G hc hG
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hω := hT c G hc hG
  rw [ENNReal.tendsto_nhds_zero] at hω
  obtain ⟨δ, hδ, hδω⟩ := Metric.eventually_nhds_iff.mp (hω ε hε)
  rw [Filter.Eventually, mem_nhdsWithin]
  refine ⟨Metric.ball 0 δ, Metric.isOpen_ball, by simpa using hδ, ?_⟩
  intro h ⟨hhball, hh0⟩
  have hh0' : h ≠ 0 := hh0
  have hhδ : |h| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hhball
  have habs : 0 < |h| := abs_pos.mpr hh0'
  -- pointwise bound
  have hpt : ∀ᵐ x ∂(logMeas c),
      ‖(h⁻¹ : ℝ) • (∫ σ in (0 : ℝ)..h, G (x.1 + σ, x.2)) - G x‖ₑ ^ 2 ≤
        ENNReal.ofReal |h|⁻¹ * ∫⁻ σ in Set.uIoc (0 : ℝ) h, ‖G (x.1 + σ, x.2) - G x‖ₑ ^ 2 := by
    filter_upwards [h1 c G hc hG h] with x hx
    have hsub : IntervalIntegrable (fun σ : ℝ => G (x.1 + σ, x.2) - G x) volume 0 h :=
      hx.sub intervalIntegrable_const
    have heq : (h⁻¹ : ℝ) • (∫ σ in (0 : ℝ)..h, G (x.1 + σ, x.2)) - G x =
        (h⁻¹ : ℝ) • ∫ σ in (0 : ℝ)..h, (G (x.1 + σ, x.2) - G x) := by
      rw [intervalIntegral.integral_sub hx intervalIntegrable_const,
        intervalIntegral.integral_const, smul_sub, sub_zero, smul_smul, inv_mul_cancel₀ hh0',
        one_smul]
    rw [heq]
    exact h3 h _ hsub
  -- integrate
  have hmeas : AEMeasurable
      (Function.uncurry fun (x : Coord) (σ : ℝ) => ‖G (x.1 + σ, x.2) - G x‖ₑ ^ 2)
      ((logMeas c).prod (volume.restrict (Set.uIoc (0 : ℝ) h))) := by
    have hm := h2 c G hG.1
    have hm2 : AEMeasurable (fun p : Coord × ℝ => ‖G (p.1.1 + p.2, p.1.2) - G p.1‖ₑ ^ 2)
        ((logMeas c).prod volume) := hm.prod_swap
    refine hm2.mono_measure ?_
    exact Measure.prod_mono le_rfl Measure.restrict_le_self
  calc ∫⁻ x, ‖(h⁻¹ : ℝ) • (∫ σ in (0 : ℝ)..h, G (x.1 + σ, x.2)) - G x‖ₑ ^ 2 ∂(logMeas c)
      ≤ ∫⁻ x, (ENNReal.ofReal |h|⁻¹ *
          ∫⁻ σ in Set.uIoc (0 : ℝ) h, ‖G (x.1 + σ, x.2) - G x‖ₑ ^ 2) ∂(logMeas c) :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal |h|⁻¹ *
          ∫⁻ x : Coord, (∫⁻ σ in Set.uIoc (0 : ℝ) h, ‖G (x.1 + σ, x.2) - G x‖ₑ ^ 2) ∂(logMeas c) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal |h|⁻¹ *
          ∫⁻ σ in Set.uIoc (0 : ℝ) h, (∫⁻ x : Coord, ‖G (x.1 + σ, x.2) - G x‖ₑ ^ 2 ∂(logMeas c)) := by
        rw [lintegral_lintegral_swap hmeas]
    _ ≤ ENNReal.ofReal |h|⁻¹ * ∫⁻ σ in Set.uIoc (0 : ℝ) h, ε := by
        refine mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_uIoc fun σ hσ => ?_)
        apply hδω
        rw [Real.dist_eq, sub_zero]
        have : |σ| ≤ |h| := by
          rcases Set.mem_uIoc.mp hσ with ⟨a, b⟩ | ⟨a, b⟩ <;>
            (rw [abs_le]; constructor <;> cases abs_cases h <;> linarith)
        exact lt_of_le_of_lt this hhδ
    _ = ε := by
        rw [setLIntegral_const, Real.volume_uIoc, sub_zero, mul_left_comm,
          ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ habs.ne', ENNReal.ofReal_one,
          mul_one]

end UnforcedLeray.Short.IIb
