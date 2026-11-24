import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FlatMembership.Env

/-!
# Part II-a, task `PartII-a:N02/4/3` helper: convergence in `L²` by dominated convergence

If `f n → g` pointwise and `‖f n - g‖ ≤ G` with `G ∈ L²(μ)`, then the classes `toLp (f n)` converge to
`toLp g` in `L²(μ)`. Proof: the squared norms are dominated by `G²`, so the integrals of `‖f n - g‖²`
tend to `0` by dominated convergence, and the `L²` norm is their square root.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

lemma nzfm_tendsto_toLp {μ : Measure Profile} {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → Profile → E) (g : Profile → E) (G : Profile → ℝ)
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ) (hG : MemLp G 2 μ)
    (hdom : ∀ n x, ‖f n x - g x‖ ≤ G x)
    (hpt : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have hsq : Integrable (fun x => G x ^ 2) μ := hG.integrable_sq
  have hint : ∀ n, MemLp (f n - g) 2 μ := fun n => (hf n).sub hg
  have hreal : Tendsto (fun n => ∫ x, ‖f n x - g x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n x => ‖f n x - g x‖ ^ 2) (f := fun _ => (0 : ℝ)) (fun x => G x ^ 2)
      (fun n => (((hint n).norm).integrable_sq).aestronglyMeasurable) hsq
      (fun n => ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hdom n x) 2)
      (ae_of_all _ fun x => by
        have h1 : Tendsto (fun n => ‖f n x - g x‖) atTop (𝓝 0) :=
          tendsto_iff_norm_sub_tendsto_zero.1 (hpt x)
        simpa using h1.pow 2)
    simpa using h
  have hfun : ∀ n, eLpNorm (f n - g) 2 μ =
      ENNReal.ofReal ((∫ x, ‖f n x - g x‖ ^ 2 ∂μ) ^ (2⁻¹ : ℝ)) := by
    intro n
    rw [(hint n).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Pi.sub_apply]
  have hlim2 : Tendsto (fun n => (∫ x, ‖f n x - g x‖ ^ 2 ∂μ) ^ (2⁻¹ : ℝ)) atTop (𝓝 0) := by
    have h := hreal.rpow_const (p := (2⁻¹ : ℝ)) (Or.inr (by norm_num))
    simpa [Real.zero_rpow (by norm_num : (2⁻¹ : ℝ) ≠ 0)] using h
  have hEL : Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0) := by
    simp_rw [hfun]
    have h := ENNReal.tendsto_ofReal hlim2
    simpa using h
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).2 hEL

end UnforcedLeray.Short.PartIIa
