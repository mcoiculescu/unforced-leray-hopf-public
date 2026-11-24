import UnforcedLeray.Short.PartIIb.Sub.T15_2
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogTranslationFormula
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogAvgConverges
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogCrossLimit
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogSquareLimit
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogSquareIdentity
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogTestBounds

/-!
# Part II-b, task `PartII-b:T15/2/13`: the scalar weak product rule in the logarithmic chart

Source of record: `the November 2 reference manuscript`, lines 1975-1979. The target
is the Prop `LogProductRuleScalar` (`Sub/T15_2.lean`, leaf `PartII-b:T15/2/13`), proved unchanged.

Proof outline. Put `G = g - u/4`, `u_h = u(· + h, ·)`, `D_h = h⁻¹(u_h - u)`.
1. `D_h → G` in `L²` along `𝓝[≠] 0` (`logTranslationFormula` identifies `D_h` a.e. with the
   average of `G`, and `logAvgConverges` gives the limit).
2. `logCrossLimit` gives `∫ D_h \bar{(u_h + u)} ψ → 2 ∫ G \bar u ψ`; take real parts.
3. `logSquareIdentity` identifies the real part of the same integrals with
   `∫ ((ψ(t - h) - ψ)/h) ‖u‖²`, which tends to `-∫ ∂_tψ ‖u‖²` (`logSquareLimit`).
   Uniqueness of limits gives `2 Re ∫ G \bar u ψ = -∫ ∂_tψ ‖u‖²`.
4. Pointwise `g \overline{ψ u} = G \bar u ψ + (1/4) ψ ‖u‖²`; integrate and take real parts.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:T15/2/13`**: the scalar weak product rule in the logarithmic chart. -/
theorem logProductRuleScalar : UnforcedLeray.Short.IIb.LogProductRuleScalar := by
  intro c u g hc hu hg hweak ψ hψ
  have hψc : Continuous ψ := hψ.smooth.continuous
  have hψb : ∃ C : ℝ, ∀ x : Coord, |ψ x| ≤ C := (logTestBounds c ψ hc hψ).1
  obtain ⟨C, hC⟩ := hψb
  have hu4 : MemLp (fun x : Coord => u x / 4) 2 (logMeas c) := by
    have h4 := hu.const_mul (4⁻¹ : ℂ)
    simpa only [div_eq_inv_mul] using h4
  have hG : MemLp (fun x : Coord => g x - u x / 4) 2 (logMeas c) := hg.sub hu4
  -- Step 1: the difference quotients of `u` converge to `G = g - u/4` in `L²`.
  have hD : Tendsto (fun h : ℝ => ∫⁻ x, ‖(h⁻¹ : ℝ) • (u (x.1 + h, x.2) - u x) -
      (g x - u x / 4)‖ₑ ^ 2 ∂(logMeas c)) (𝓝[≠] 0) (𝓝 0) := by
    refine Tendsto.congr (fun h => ?_) (logAvgConverges c (fun x : Coord => g x - u x / 4) hc hG)
    apply lintegral_congr_ae
    filter_upwards [logTranslationFormula c u g hc hu hg hweak h] with x hx
    rw [hx]
  -- Step 2: the cross term converges.
  have hcross : Tendsto (fun h : ℝ => ∫ x, ((h⁻¹ : ℝ) • (u (x.1 + h, x.2) - u x)) *
      (starRingEnd ℂ) (u (x.1 + h, x.2) + u x) * (ψ x : ℂ) ∂(logMeas c))
      (𝓝[≠] 0) (𝓝 (2 * ∫ x, (g x - u x / 4) * (starRingEnd ℂ) (u x) * (ψ x : ℂ)
        ∂(logMeas c))) :=
    logCrossLimit c u (fun x : Coord => g x - u x / 4) hc hu hG hD ψ hψc ⟨C, hC⟩
  have hre : Tendsto (fun h : ℝ => (∫ x, ((h⁻¹ : ℝ) • (u (x.1 + h, x.2) - u x)) *
      (starRingEnd ℂ) (u (x.1 + h, x.2) + u x) * (ψ x : ℂ) ∂(logMeas c)).re)
      (𝓝[≠] 0) (𝓝 ((2 * ∫ x, (g x - u x / 4) * (starRingEnd ℂ) (u x) * (ψ x : ℂ)
        ∂(logMeas c)).re)) :=
    (Complex.continuous_re.tendsto _).comp hcross
  -- Step 3: the same real parts tend to the square term.
  have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), h ≠ 0 :=
    eventually_nhdsWithin_of_forall fun h hh => by simpa using hh
  have hsq : Tendsto (fun h : ℝ => (∫ x, ((h⁻¹ : ℝ) • (u (x.1 + h, x.2) - u x)) *
      (starRingEnd ℂ) (u (x.1 + h, x.2) + u x) * (ψ x : ℂ) ∂(logMeas c)).re)
      (𝓝[≠] 0) (𝓝 (-∫ x, cpd 0 ψ x * ‖u x‖ ^ 2 ∂(logMeas c))) :=
    Tendsto.congr' (hev.mono fun h hh => (logSquareIdentity c u ψ hc hu hψ h hh).symm)
      (logSquareLimit c u ψ hc hu hψ)
  have hJ := tendsto_nhds_unique hre hsq
  have h2re : (2 : ℂ).re = 2 := by norm_num
  have h2im : (2 : ℂ).im = 0 := by norm_num
  rw [Complex.mul_re, h2re, h2im] at hJ
  -- Step 4: the pointwise identity and integration.
  have hpt : ∀ x : Coord, g x * (starRingEnd ℂ) ((ψ x : ℂ) * u x) =
      (g x - u x / 4) * (starRingEnd ℂ) (u x) * (ψ x : ℂ) +
        (((1 / 4 : ℝ) * (ψ x * ‖u x‖ ^ 2) : ℝ) : ℂ) := by
    intro x
    have hn : ((‖u x‖ : ℝ) : ℂ) ^ 2 = u x * (starRingEnd ℂ) (u x) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    linear_combination (-(1 / 4 : ℂ) * (ψ x : ℂ)) * hn
  have hcu : MemLp (fun x : Coord => (starRingEnd ℂ) (u x)) 2 (logMeas c) := hu.star
  have hA : Integrable (fun x : Coord => (g x - u x / 4) * (starRingEnd ℂ) (u x) * (ψ x : ℂ))
      (logMeas c) :=
    (logCL_holder (logMeas c) (fun x : Coord => g x - u x / 4) (fun x : Coord => (starRingEnd ℂ) (u x))
      ψ C hG hcu hψc hC).1
  have hsq2 : Integrable (fun x : Coord => ‖u x‖ ^ 2) (logMeas c) :=
    (memLp_two_iff_integrable_sq_norm hu.1).mp hu
  have hψm : AEStronglyMeasurable ψ (logMeas c) := hψc.aestronglyMeasurable
  have hK : Integrable (fun x : Coord => ψ x * ‖u x‖ ^ 2) (logMeas c) :=
    hsq2.bdd_mul hψm (ae_of_all _ fun x => show ‖ψ x‖ ≤ C by rw [Real.norm_eq_abs]; exact hC x)
  have hB : Integrable (fun x : Coord => (((1 / 4 : ℝ) * (ψ x * ‖u x‖ ^ 2) : ℝ) : ℂ))
      (logMeas c) :=
    (hK.const_mul (1 / 4 : ℝ)).ofReal
  have hsplit : ∫ x, g x * (starRingEnd ℂ) ((ψ x : ℂ) * u x) ∂(logMeas c) =
      (∫ x, (g x - u x / 4) * (starRingEnd ℂ) (u x) * (ψ x : ℂ) ∂(logMeas c)) +
        ((∫ x, (1 / 4 : ℝ) * (ψ x * ‖u x‖ ^ 2) ∂(logMeas c) : ℝ) : ℂ) := by
    rw [integral_congr_ae (ae_of_all _ hpt), integral_add hA hB, integral_complex_ofReal]
  have hK2 : ∫ x, (1 / 4 : ℝ) * (ψ x * ‖u x‖ ^ 2) ∂(logMeas c) =
      (1 / 4) * ∫ x, ψ x * ‖u x‖ ^ 2 ∂(logMeas c) :=
    integral_const_mul _ _
  rw [hsplit, Complex.add_re, Complex.ofReal_re, hK2]
  linarith

end UnforcedLeray.Short.IIb
