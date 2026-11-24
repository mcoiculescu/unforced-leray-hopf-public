import UnforcedLeray.Short.PartIIb.Sub.T15_2
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.ExpChartIntegral

/-!
# Part II-b, task `PartII-b:T15/2/2`: `H_2` membership gives `L²` of the pull-back

Source of record: `the November 2 reference manuscript`, lines 1975-1979 (the weak
product rule in the measure `s^{-3/2} ds`, read through the logarithmic chart `s = e^t`).
Target `LogUMemLp` (`Sub/T15_2.lean`): if `w ∈ H_2` then `u_i = logU w i ∈ L²(logMeas c)`.

Route: a strongly measurable representative `f` of `w` agrees with `w` `hMeas c 2`-a.e.; the
change of variable `expCoordE` (`ExpChartIntegral.lean`) carries `hMeas c 2` to the density
`e^{(a+1)t}` times `logMeas c` with `a = 2/2 - 5/2`, so `w ∘ expCoordE = f ∘ expCoordE` is
`logMeas c`-a.e. Then `‖logU w i x‖ₑ^2 = ofReal (e^{(a+1)t}) ‖f (e^t, y) i‖ₑ^2` pointwise a.e., and
`expChartIntegral` converts the lower integral to `∫⁻ ‖f i‖ₑ^2 d(hMeas c 2) ≤ ∫⁻ ‖w‖ₑ^2 d(hMeas c 2)
< ∞`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIb

/-- **Leaf `PartII-b:T15/2/2`** (`H_2` membership gives `L²` of the pull-back; uses `T15/2/1`).
If `w ∈ H_2` then `u_i = logU w i ∈ L²(logMeas c)`. -/
theorem logUMemLp : LogUMemLp := by
  intro c w hc hw i
  obtain ⟨_hper, hmeas, hfin⟩ := hw
  -- a strongly measurable representative `f` of `w`, `ageμ c (2/2 - 5/2)`-a.e.
  obtain ⟨f, hfsm, hwf⟩ : ∃ f : CProf, StronglyMeasurable f ∧
      ∀ᵐ y ∂(Axi.ageμ c (2 / 2 - 5 / 2)), w y = f y :=
    ⟨hmeas.mk w, hmeas.stronglyMeasurable_mk, hmeas.ae_eq_mk⟩
  have hfm : Measurable f := hfsm.measurable
  have hcoord : ∀ j : Fin 2, Measurable fun v : CMerid => v j := by
    intro j
    fun_prop
  -- the density of `expChartIntegral` for `a = 2/2 - 5/2`
  have hρ : Measurable fun x : Coord =>
      ENNReal.ofReal (Real.exp ((2 / 2 - 5 / 2 + 1) * x.1)) := by
    fun_prop
  -- transfer the a.e. equality from `ageμ` to `logMeas c` through the time change
  have hae : ∀ᵐ x ∂(logMeas c), w (Real.exp x.1, x.2) = f (Real.exp x.1, x.2) := by
    have h1 : ∀ᵐ y ∂(Axi.ageμ c (2 / 2 - 5 / 2)), w y = f y := hwf
    rw [← map_expCoordE_withDensity c (2 / 2 - 5 / 2)] at h1
    have h2 := measurableEmbedding_expCoordE.ae_map_iff.1 h1
    rw [ae_withDensity_iff hρ] at h2
    filter_upwards [h2] with x hx
    exact hx (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  -- `logU w i = e^{-t/4} f(e^t, y) i` almost everywhere
  have hlogU : logU w i =ᵐ[logMeas c] fun x : Coord =>
      ((Real.exp (-x.1 / 4) : ℝ) : ℂ) * f (Real.exp x.1, x.2) i := by
    filter_upwards [hae] with x hx
    show ((Real.exp (-x.1 / 4) : ℝ) : ℂ) * w (Real.exp x.1, x.2) i =
      ((Real.exp (-x.1 / 4) : ℝ) : ℂ) * f (Real.exp x.1, x.2) i
    rw [hx]
  -- measurability of the pulled-back component
  have hgm : Measurable fun x : Coord =>
      ((Real.exp (-x.1 / 4) : ℝ) : ℂ) * f (Real.exp x.1, x.2) i := by
    have hc1 : Measurable fun x : Coord => ((Real.exp (-x.1 / 4) : ℝ) : ℂ) := by
      fun_prop
    exact hc1.mul ((hcoord i).comp (hfm.comp measurable_expCoordE))
  have hlogUaesm : AEStronglyMeasurable (logU w i) (logMeas c) :=
    hgm.aestronglyMeasurable.congr hlogU.symm
  -- pointwise norm identity: `‖e^{-t/4} z‖ₑ^2 = e^{(a+1) t} ‖z‖ₑ^2` with `a + 1 = -1/2`
  have hcplx : ∀ r : ℝ, 0 ≤ r → ‖(r : ℂ)‖ₑ = ENNReal.ofReal r := by
    intro r hr
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hr]
  have hpt : ∀ (t : ℝ) (z : ℂ),
      ‖((Real.exp (-t / 4) : ℝ) : ℂ) * z‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal (Real.exp ((2 / 2 - 5 / 2 + 1) * t)) * ‖z‖ₑ ^ (2 : ℝ) := by
    intro t z
    have hr : (0 : ℝ) ≤ Real.exp (-t / 4) := (Real.exp_pos _).le
    rw [enorm_mul, hcplx _ hr, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_rpow_of_nonneg hr (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two, sq,
      ← Real.exp_add, show -t / 4 + -t / 4 = (2 / 2 - 5 / 2 + 1) * t by ring]
  -- measurability of the squared component on the `ageμ` side
  have hGm : Measurable fun y : Coord => ‖f y i‖ₑ ^ (2 : ℝ) :=
    ((hcoord i).comp hfm).enorm.pow_const (2 : ℝ)
  -- the component is dominated by the Euclidean norm, almost everywhere for `ageμ`
  have hle : ∀ᵐ y ∂(Axi.ageμ c (2 / 2 - 5 / 2)), ‖f y i‖ₑ ^ (2 : ℝ) ≤ ‖w y‖ₑ ^ (2 : ℝ) := by
    filter_upwards [hwf] with y hy
    rw [hy]
    exact ENNReal.rpow_le_rpow (PiLp.enorm_apply_le (f y) i) (by norm_num)
  -- finiteness of the `H_2` norm, read as a lower integral
  have hwfin : ∫⁻ y, ‖w y‖ₑ ^ (2 : ℝ) ∂(Axi.ageμ c (2 / 2 - 5 / 2)) < ⊤ := by
    have hfin' : eLpNorm w (ENNReal.ofReal 2) (Axi.ageμ c (2 / 2 - 5 / 2)) < ⊤ := hfin
    have hp0 : ENNReal.ofReal 2 ≠ 0 := (ENNReal.ofReal_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 ENNReal.ofReal_ne_top).1 hfin'
    rwa [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)] at h
  -- the pulled-back lower integral equals the `ageμ` lower integral
  have hlhs : ∫⁻ x, ‖logU w i x‖ₑ ^ (2 : ℝ) ∂(logMeas c) =
      ∫⁻ x, ENNReal.ofReal (Real.exp ((2 / 2 - 5 / 2 + 1) * x.1)) *
        ‖f (Real.exp x.1, x.2) i‖ₑ ^ (2 : ℝ) ∂(logMeas c) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hlogU] with x hx
    show ‖logU w i x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (Real.exp ((2 / 2 - 5 / 2 + 1) * x.1)) *
      ‖f (Real.exp x.1, x.2) i‖ₑ ^ (2 : ℝ)
    rw [hx]
    exact hpt x.1 (f (Real.exp x.1, x.2) i)
  have hbound : ∫⁻ x, ‖logU w i x‖ₑ ^ (2 : ℝ) ∂(logMeas c) < ⊤ := by
    rw [hlhs]
    calc ∫⁻ x, ENNReal.ofReal (Real.exp ((2 / 2 - 5 / 2 + 1) * x.1)) *
          ‖f (Real.exp x.1, x.2) i‖ₑ ^ (2 : ℝ) ∂(logMeas c)
        = ∫⁻ y, ‖f y i‖ₑ ^ (2 : ℝ) ∂(Axi.ageμ c (2 / 2 - 5 / 2)) :=
          ((expChartIntegral c (2 / 2 - 5 / 2) hc).1 (fun y => ‖f y i‖ₑ ^ (2 : ℝ)) hGm).symm
      _ ≤ ∫⁻ y, ‖w y‖ₑ ^ (2 : ℝ) ∂(Axi.ageμ c (2 / 2 - 5 / 2)) := lintegral_mono_ae hle
      _ < ⊤ := hwfin
  -- conclude `MemLp (logU w i) 2 (logMeas c)`
  have two0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have twoTop : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  show AEStronglyMeasurable (logU w i) (logMeas c) ∧ eLpNorm (logU w i) 2 (logMeas c) < ⊤
  refine ⟨hlogUaesm, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two0 twoTop,
    show (2 : ℝ≥0∞).toReal = 2 by norm_num]
  exact hbound

end UnforcedLeray.Short.IIb
