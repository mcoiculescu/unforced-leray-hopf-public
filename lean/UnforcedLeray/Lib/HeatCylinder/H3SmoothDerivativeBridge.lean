import UnforcedLeray.Lib.HeatCylinder.H3DerivativeOrbit
import UnforcedLeray.Lib.HeatCylinder.H3Output

/-!
# Actual derivative components of smooth Gaussian H³ outputs

This leaf identifies each centered-cell weak derivative component of the smooth H³ output with
the actual normalized-cell Gaussian orbit on the matching input derivative.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal
open scoped Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

private theorem heatDivH3_measure_eq_cell (c : ℝ) :
    UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
  rw [UnforcedLeray.Cyl.wμ_ρwW]
  simp [UnforcedLeray.Cyl.wμ]

/-- The centered-cell L² class of one actual Gaussian derivative field. -/
noncomputable def heatDivH3CenteredDerivativeOrbit {c : ℝ} (hc : 0 < c)
    {T : Plane → Plane × Plane} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (α : UnforcedLeray.Sob.Idx 2 3) (θ : ℝ) :
    Lp Vec 2 (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) :=
  if hθ : 0 < θ then
    (memLp_heatDivH3Field hc hθ hT α).toLp
      (heatDivH3Field (c := c) (θ := θ) T α)
  else 0

/-- The normalized vector orbit on the ordered input derivative is exactly the L² class of the
actual vector Gaussian derivative field. -/
theorem heatDivH3DerivativeL2Orbit_eq_actual {c θ : ℝ} (hc : 0 < c)
    (hθ : 0 < θ) {T : Plane → Plane × Plane}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (α : UnforcedLeray.Sob.Idx 2 3) :
    heatDivH3DerivativeL2Orbit hc hT α θ =
      heatDivVecL2CLM hc hθ
        ((memLp_tensor_iterD_cylSmooth_normalized hc
          (hT.iterD ((UnforcedLeray.Sob.cylinder c).word α)) []).toLp
            (UnforcedLeray.Sob.iterD ((UnforcedLeray.Sob.cylinder c).word α) T)) := by
  let v := (UnforcedLeray.Sob.cylinder c).word α
  let Tα := UnforcedLeray.Sob.iterD v T
  have hTα : UnforcedLeray.Sob.IsCylSmooth c Tα := hT.iterD v
  have hper : UnforcedLeray.B0284.IsQPeriodic c Tα := by
    intro z
    have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
    rw [hcoord]
    exact hTα.periodic z
  have hmeas : Measurable Tα := hTα.smooth.continuous.measurable
  have hmem : MemLp Tα 2 (UnforcedLeray.B0284.cellMeasure c) :=
    memLp_tensor_iterD_cylSmooth_normalized hc hTα []
  change heatDivVecL2Orbit hc hper hmeas hmem θ = _
  rw [heatDivVecL2Orbit, heatDivL2Orbit_eq_CLM hc hθ hper hmeas hmem]
  rfl

/-- The centered derivative class in `heatDivH3` is the same actual field used by its normalized
Gaussian orbit. -/
theorem heatDivH3CenteredDerivativeOrbit_eq_deriv {c θ : ℝ} (hc : 0 < c)
    (hθ : 0 < θ) {T : Plane → Plane × Plane}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (α : UnforcedLeray.Sob.Idx 2 3) :
    heatDivH3CenteredDerivativeOrbit hc hT α θ =
      UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α
        (heatDivH3 hc hθ hT) := by
  rw [heatDivH3CenteredDerivativeOrbit, dif_pos hθ, heatDivH3]
  exact UnforcedLeray.Sob.W.deriv_ofFields
    (D := UnforcedLeray.Sob.cylinder c)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec)
    (k := 3) (p := 2) (heatDivH3Field (c := c) (θ := θ) T)
    (memLp_heatDivH3Field hc hθ hT) (hasWeakDeriv_heatDivH3Field hc hθ hT) α

/-- Squared centered H³ derivative distance is exactly the period times the squared normalized
L² orbit distance. -/
theorem norm_sq_heatDivH3Derivative_centered_eq {c θ θ₀ : ℝ} (hc : 0 < c)
    (hθ : 0 < θ) (hθ₀ : 0 < θ₀) {T : Plane → Plane × Plane}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (α : UnforcedLeray.Sob.Idx 2 3) :
    ‖heatDivH3CenteredDerivativeOrbit hc hT α θ -
      heatDivH3CenteredDerivativeOrbit hc hT α θ₀‖ ^ 2 =
      c * ‖heatDivH3DerivativeL2Orbit hc hT α θ -
        heatDivH3DerivativeL2Orbit hc hT α θ₀‖ ^ 2 := by
  let v := (UnforcedLeray.Sob.cylinder c).word α
  let Tα := UnforcedLeray.Sob.iterD v T
  have hTα : UnforcedLeray.Sob.IsCylSmooth c Tα := hT.iterD v
  have hper : UnforcedLeray.B0284.IsQPeriodic c Tα := by
    intro z
    have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
    rw [hcoord]
    exact hTα.periodic z
  have hmeas : Measurable Tα := hTα.smooth.continuous.measurable
  have hmem : MemLp Tα 2 (UnforcedLeray.B0284.cellMeasure c) :=
    memLp_tensor_iterD_cylSmooth_normalized hc hTα []
  let g : ℝ → Plane → Vec := fun s z =>
    heatDivH3Field (c := c) (θ := s) T α z
  let f : Plane → Vec := fun z => g θ z - g θ₀ z
  have hmeasField (s : ℝ) (hs : 0 < s) : Measurable (g s) := by
    have h := differentiable_heatDiv_of_cylSmooth hc hs hTα
    exact (UnforcedLeray.Train.toVecL.continuous.comp h.continuous).measurable
  have hperField (s : ℝ) (hs : 0 < s) :
      UnforcedLeray.B0284.IsQPeriodic c (g s) := by
    intro z
    exact congrArg UnforcedLeray.Train.toVec
      (UnforcedLeray.B0296.heatDiv_periodic (θ := s) hper z)
  have hmeasF : Measurable f := (hmeasField θ hθ).sub (hmeasField θ₀ hθ₀)
  have hperF : UnforcedLeray.B0284.IsQPeriodic c f := by
    intro z
    change g θ (z.1 + c, z.2) - g θ₀ (z.1 + c, z.2) = _
    rw [hperField θ hθ z, hperField θ₀ hθ₀ z]
  have hcenter (s : ℝ) (hs : 0 < s) :
      (heatDivH3CenteredDerivativeOrbit hc hT α s : Plane → Vec) =ᵐ[
        UnforcedLeray.Cyl.cellμ c] g s := by
    change (heatDivH3CenteredDerivativeOrbit hc hT α s : Plane → Vec) =ᵐ[
      UnforcedLeray.Cyl.cellμ c] (heatDivH3Field (c := c) (θ := s) T α : Plane → Vec)
    rw [heatDivH3CenteredDerivativeOrbit, dif_pos hs]
    simpa only [heatDivH3_measure_eq_cell c] using
      (memLp_heatDivH3Field hc hs hT α).coeFn_toLp
  have hnormal (s : ℝ) (hs : 0 < s) :
      (heatDivH3DerivativeL2Orbit hc hT α s : Plane → Vec) =ᵐ[
        UnforcedLeray.B0284.cellMeasure c] g s := by
    rw [heatDivH3DerivativeL2Orbit_eq_actual hc hs hT α,
      heatDivVecL2CLM_apply_to_periodic hc hs hper hmeas.aestronglyMeasurable hmem]
    exact (periodicHeatDivVecMemLp hc hs Tα hper hmeas.aestronglyMeasurable hmem).coeFn_toLp
  have hcenterDiff :
      ((heatDivH3CenteredDerivativeOrbit hc hT α θ -
        heatDivH3CenteredDerivativeOrbit hc hT α θ₀ : Lp Vec 2
          (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
            (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)))) : Plane → Vec) =ᵐ[
        UnforcedLeray.Cyl.cellμ c] f := by
    have hsubW := Lp.coeFn_sub
      (heatDivH3CenteredDerivativeOrbit hc hT α θ)
      (heatDivH3CenteredDerivativeOrbit hc hT α θ₀)
    have hsubCell :
        ((heatDivH3CenteredDerivativeOrbit hc hT α θ -
          heatDivH3CenteredDerivativeOrbit hc hT α θ₀ : Lp Vec 2
            (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
              (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)))) : Plane → Vec) =ᵐ[
          UnforcedLeray.Cyl.cellμ c]
      ((heatDivH3CenteredDerivativeOrbit hc hT α θ : Plane → Vec) -
            (heatDivH3CenteredDerivativeOrbit hc hT α θ₀ : Plane → Vec)) := by
      simpa only [heatDivH3_measure_eq_cell c] using hsubW
    filter_upwards [hsubCell, hcenter θ hθ, hcenter θ₀ hθ₀] with z hsub hθz hθ₀z
    calc
      ((heatDivH3CenteredDerivativeOrbit hc hT α θ -
          heatDivH3CenteredDerivativeOrbit hc hT α θ₀ : Lp Vec 2
            (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
              (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)))) : Plane → Vec) z =
          (heatDivH3CenteredDerivativeOrbit hc hT α θ : Plane → Vec) z -
            (heatDivH3CenteredDerivativeOrbit hc hT α θ₀ : Plane → Vec) z := hsub
      _ = f z := by rw [hθz, hθ₀z]
  have hnormalDiff :
      ((heatDivH3DerivativeL2Orbit hc hT α θ -
        heatDivH3DerivativeL2Orbit hc hT α θ₀ : Lp Vec 2
          (UnforcedLeray.B0284.cellMeasure c)) : Plane → Vec) =ᵐ[
        UnforcedLeray.B0284.cellMeasure c] f := by
    filter_upwards [Lp.coeFn_sub
      (heatDivH3DerivativeL2Orbit hc hT α θ)
      (heatDivH3DerivativeL2Orbit hc hT α θ₀),
      hnormal θ hθ, hnormal θ₀ hθ₀] with z hsub hθz hθ₀z
    calc
      ((heatDivH3DerivativeL2Orbit hc hT α θ -
          heatDivH3DerivativeL2Orbit hc hT α θ₀ : Lp Vec 2
            (UnforcedLeray.B0284.cellMeasure c)) : Plane → Vec) z =
          (heatDivH3DerivativeL2Orbit hc hT α θ : Plane → Vec) z -
            (heatDivH3DerivativeL2Orbit hc hT α θ₀ : Plane → Vec) z := hsub
      _ = f z := by rw [hθz, hθ₀z]
  have hscale := eLpNorm_sq_cyl_eq_cellMeasure hc hmeasF hperF
  have hscaled :
      (eLpNorm (((heatDivH3CenteredDerivativeOrbit hc hT α θ -
        heatDivH3CenteredDerivativeOrbit hc hT α θ₀ : Lp Vec 2
          (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
            (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)))) : Plane → Vec)) 2
          (UnforcedLeray.Cyl.cellμ c)) ^ 2 =
      ENNReal.ofReal c *
        (eLpNorm (((heatDivH3DerivativeL2Orbit hc hT α θ -
          heatDivH3DerivativeL2Orbit hc hT α θ₀ : Lp Vec 2
            (UnforcedLeray.B0284.cellMeasure c)) : Plane → Vec)) 2
            (UnforcedLeray.B0284.cellMeasure c)) ^ 2 := by
    rw [eLpNorm_congr_ae hcenterDiff, hscale, eLpNorm_congr_ae hnormalDiff]
  rw [← heatDivH3_measure_eq_cell c] at hscaled
  have hreal := congrArg ENNReal.toReal hscaled
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt hc),
    ENNReal.toReal_pow] at hreal
  rw [Lp.norm_def, Lp.norm_def]
  exact hreal

/-- The centered and normalized derivative distances differ by exactly `sqrt c`. -/
theorem norm_heatDivH3Derivative_centered_eq {c θ θ₀ : ℝ} (hc : 0 < c)
    (hθ : 0 < θ) (hθ₀ : 0 < θ₀) {T : Plane → Plane × Plane}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (α : UnforcedLeray.Sob.Idx 2 3) :
    ‖heatDivH3CenteredDerivativeOrbit hc hT α θ -
      heatDivH3CenteredDerivativeOrbit hc hT α θ₀‖ =
      Real.sqrt c * ‖heatDivH3DerivativeL2Orbit hc hT α θ -
        heatDivH3DerivativeL2Orbit hc hT α θ₀‖ := by
  have hsq := norm_sq_heatDivH3Derivative_centered_eq hc hθ hθ₀ hT α
  have hleft : 0 ≤ ‖heatDivH3CenteredDerivativeOrbit hc hT α θ -
      heatDivH3CenteredDerivativeOrbit hc hT α θ₀‖ := norm_nonneg _
  have hright : 0 ≤ Real.sqrt c *
      ‖heatDivH3DerivativeL2Orbit hc hT α θ -
        heatDivH3DerivativeL2Orbit hc hT α θ₀‖ :=
    mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg _)
  have hsq' : ‖heatDivH3CenteredDerivativeOrbit hc hT α θ -
      heatDivH3CenteredDerivativeOrbit hc hT α θ₀‖ ^ 2 =
      (Real.sqrt c * ‖heatDivH3DerivativeL2Orbit hc hT α θ -
        heatDivH3DerivativeL2Orbit hc hT α θ₀‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hc)]
    exact hsq
  exact (sq_eq_sq₀ hleft hright).mp hsq'

/-- Every centered weak derivative component of a smooth Gaussian H³ output is strongly
continuous at positive heat age, with the exact normalized-cell scaling. -/
theorem continuousAt_heatDivH3CenteredDerivativeOrbit {c θ₀ : ℝ} (hc : 0 < c)
    (hθ₀ : 0 < θ₀) {T : Plane → Plane × Plane}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (α : UnforcedLeray.Sob.Idx 2 3) :
    ContinuousAt (heatDivH3CenteredDerivativeOrbit hc hT α) θ₀ := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hN := (continuousAt_heatDivH3DerivativeL2Orbit hc hθ₀ hT α).tendsto
  have hNdist := (tendsto_iff_dist_tendsto_zero).mp hN
  have htarget : Tendsto
      (fun θ : ℝ => Real.sqrt c * dist
        (heatDivH3DerivativeL2Orbit hc hT α θ)
        (heatDivH3DerivativeL2Orbit hc hT α θ₀)) (𝓝 θ₀) (𝓝 0) := by
    simpa using hNdist.const_mul (Real.sqrt c)
  have hcongr : (fun θ : ℝ => dist
      (heatDivH3CenteredDerivativeOrbit hc hT α θ)
      (heatDivH3CenteredDerivativeOrbit hc hT α θ₀)) =ᶠ[𝓝 θ₀]
      (fun θ : ℝ => Real.sqrt c * dist
        (heatDivH3DerivativeL2Orbit hc hT α θ)
        (heatDivH3DerivativeL2Orbit hc hT α θ₀)) := by
    filter_upwards [Ioi_mem_nhds hθ₀] with θ hθ
    rw [dist_eq_norm, dist_eq_norm]
    exact norm_heatDivH3Derivative_centered_eq hc hθ hθ₀ hT α
  exact htarget.congr' hcongr.symm

/-- Total H³ output orbit for a smooth tensor, extended by zero outside positive ages. -/
noncomputable def heatDivH3SmoothOrbit {c : ℝ} (hc : 0 < c)
    {T : Plane → Plane × Plane} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (θ : ℝ) : UnforcedLeray.TrainB.VectorH3 c :=
  if hθ : 0 < θ then heatDivH3 hc hθ hT else 0

/-- The actual smooth Gaussian heat-divergence output is continuous as a full H³ graph-valued
orbit on every positive-age interval. The proof sums the actual centered weak-derivative
components and uses their exact normalized-cell Gaussian orbit identities. -/
theorem continuousAt_heatDivH3SmoothOrbit {c θ₀ : ℝ} (hc : 0 < c)
    (hθ₀ : 0 < θ₀) {T : Plane → Plane × Plane}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    ContinuousAt (heatDivH3SmoothOrbit hc hT) θ₀ := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  let N : UnforcedLeray.Sob.Idx 2 3 → ℝ → ℝ := fun α θ =>
    ‖heatDivH3DerivativeL2Orbit hc hT α θ -
      heatDivH3DerivativeL2Orbit hc hT α θ₀‖ ^ 2
  have hN (α : UnforcedLeray.Sob.Idx 2 3) : Tendsto (N α) (𝓝 θ₀) (𝓝 0) := by
    have hcont := continuousAt_heatDivH3DerivativeL2Orbit hc hθ₀ hT α
    have hdist := (tendsto_iff_dist_tendsto_zero).mp hcont.tendsto
    have hpow : Tendsto (fun θ : ℝ => dist
        (heatDivH3DerivativeL2Orbit hc hT α θ)
        (heatDivH3DerivativeL2Orbit hc hT α θ₀) ^ 2) (𝓝 θ₀) (𝓝 0) := by
      simpa using hdist.pow 2
    simpa [N, dist_eq_norm] using hpow
  have hsumN : Tendsto (fun θ => ∑ α : UnforcedLeray.Sob.Idx 2 3, N α θ)
      (𝓝 θ₀) (𝓝 0) := by
    convert tendsto_finsetSum (s := Finset.univ)
      (f := fun α θ => N α θ) (x := 𝓝 θ₀) (a := fun _ : UnforcedLeray.Sob.Idx 2 3 => 0)
      (fun α hα => hN α) using 1 <;> simp
  let D : UnforcedLeray.Sob.Idx 2 3 → ℝ → ℝ := fun α θ =>
    ‖heatDivH3CenteredDerivativeOrbit hc hT α θ -
      heatDivH3CenteredDerivativeOrbit hc hT α θ₀‖ ^ 2
  have hsumD : Tendsto (fun θ => ∑ α : UnforcedLeray.Sob.Idx 2 3, D α θ)
      (𝓝 θ₀) (𝓝 0) := by
    have hscale : (fun θ => ∑ α : UnforcedLeray.Sob.Idx 2 3, D α θ) =ᶠ[𝓝 θ₀]
        (fun θ => c * ∑ α : UnforcedLeray.Sob.Idx 2 3, N α θ) := by
      filter_upwards [Ioi_mem_nhds hθ₀] with θ hθ
      dsimp [D, N]
      calc
        (∑ α : UnforcedLeray.Sob.Idx 2 3,
            ‖heatDivH3CenteredDerivativeOrbit hc hT α θ -
              heatDivH3CenteredDerivativeOrbit hc hT α θ₀‖ ^ 2) =
            ∑ α : UnforcedLeray.Sob.Idx 2 3,
              c * ‖heatDivH3DerivativeL2Orbit hc hT α θ -
                heatDivH3DerivativeL2Orbit hc hT α θ₀‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro α hα
          exact norm_sq_heatDivH3Derivative_centered_eq hc hθ hθ₀ hT α
        _ = c * ∑ α : UnforcedLeray.Sob.Idx 2 3,
            ‖heatDivH3DerivativeL2Orbit hc hT α θ -
              heatDivH3DerivativeL2Orbit hc hT α θ₀‖ ^ 2 := by rw [Finset.mul_sum]
    have hmul := hsumN.const_mul c
    simpa using hmul.congr' hscale.symm
  have hgraph : (fun θ : ℝ => ‖heatDivH3SmoothOrbit hc hT θ -
      heatDivH3SmoothOrbit hc hT θ₀‖ ^ 2) =ᶠ[𝓝 θ₀]
      (fun θ => ∑ α : UnforcedLeray.Sob.Idx 2 3, D α θ) := by
    filter_upwards [Ioi_mem_nhds hθ₀] with θ hθ
    have hderiv (s : ℝ) (hs : 0 < s) (α : UnforcedLeray.Sob.Idx 2 3) :
        UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ UnforcedLeray.Train.Vec 3 2 α
          (heatDivH3SmoothOrbit hc hT s) = heatDivH3CenteredDerivativeOrbit hc hT α s := by
      rw [heatDivH3SmoothOrbit, dif_pos hs]
      exact (heatDivH3CenteredDerivativeOrbit_eq_deriv hc hs hT α).symm
    rw [UnforcedLeray.Sob.W.norm_sq]
    apply Finset.sum_congr rfl
    intro α hα
    rw [map_sub, hderiv θ hθ α, hderiv θ₀ hθ₀ α]
  have hnormSq : Tendsto
      (fun θ : ℝ => ‖heatDivH3SmoothOrbit hc hT θ -
        heatDivH3SmoothOrbit hc hT θ₀‖ ^ 2) (𝓝 θ₀) (𝓝 0) :=
    hsumD.congr' hgraph.symm
  have hnorm : Tendsto
      (fun θ : ℝ => ‖heatDivH3SmoothOrbit hc hT θ -
        heatDivH3SmoothOrbit hc hT θ₀‖) (𝓝 θ₀) (𝓝 0) := by
    have hsqrt := Real.continuous_sqrt.tendsto 0 |>.comp hnormSq
    have heq : (fun θ : ℝ => Real.sqrt
        (‖heatDivH3SmoothOrbit hc hT θ -
          heatDivH3SmoothOrbit hc hT θ₀‖ ^ 2)) =
        (fun θ => ‖heatDivH3SmoothOrbit hc hT θ -
          heatDivH3SmoothOrbit hc hT θ₀‖) := by
      funext θ
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have hevent : (fun θ : ℝ => Real.sqrt
        (‖heatDivH3SmoothOrbit hc hT θ -
          heatDivH3SmoothOrbit hc hT θ₀‖ ^ 2)) =ᶠ[𝓝 θ₀]
        (fun θ => ‖heatDivH3SmoothOrbit hc hT θ -
          heatDivH3SmoothOrbit hc hT θ₀‖) :=
      Filter.Eventually.of_forall fun θ => congrFun heq θ
    simpa using hsqrt.congr' hevent
  simpa [dist_eq_norm] using hnorm

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatDivH3DerivativeL2Orbit_eq_actual
#print axioms UnforcedLeray.HeatCylinder.norm_sq_heatDivH3Derivative_centered_eq
#print axioms UnforcedLeray.HeatCylinder.continuousAt_heatDivH3CenteredDerivativeOrbit
#print axioms UnforcedLeray.HeatCylinder.continuousAt_heatDivH3SmoothOrbit

