import UnforcedLeray.Loc.L13PhysicalRemainder.Fields

/-!
# Step L13, helpers: symmetry and solenoidality of the background remainder `r_heat`

Support for `Loc/L13PhysicalRemainder.lean` (step L13 `PhysicalRemainderStep`,
`paper/main.tex` lines 159–168, 188–189, 536; blueprint units B0707, B0708, B1025, B1028).

`U_* = H_h[u_dss] + r_heat` (line 167). The remainder `t^{-1/2} r_heat(·/√t, log t)` is a
summand of the physical remainder, so its symmetry and solenoidality are needed.

* `heatProfile_rotate`: the heat profile of an `𝒪`-invariant field is `𝒪`-invariant at every
  point (the Gaussian kernel is radial and `𝒪` acts by measure-preserving isometries);
* `rheat_symmetric`: hence `r_heat(τ) = U_*(τ) - H_h[u_dss](τ)` is `𝒪`-invariant;
* `rheat_solenoidal_of`: `r_heat(τ)` is solenoidal once `H_h[u_dss](τ)` is.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.L13

/-- `g H_h[u](g⁻¹y) = H_h[u](y)` for `𝒪`-invariant `u` (lines 188–189, B1025). -/
theorem heatProfile_rotate {h τ : ℝ} {u : SpatialField} (hu : IsAxisymmetricNoSwirl u)
    {g : Space ≃ₗᵢ[ℝ] Space} (hg : FixesAxis g) (y : Space) :
    g (heatProfile h u τ (g.symm y)) = heatProfile h u τ y := by
  simp only [heatProfile_apply]
  rw [LinearIsometryEquiv.map_smul]
  congr 1
  have hc := LinearIsometry.integral_comp_comm (μ := volume) g.toLinearIsometry
    (fun z => Heat.kernel (h * Real.exp τ) z • u (Real.exp (τ / 2) • g.symm y - z))
  refine Eq.trans hc.symm ?_
  have hmp : MeasurePreserving (g.symm : Space → Space) volume volume :=
    g.symm.measurePreserving
  have hemb : MeasurableEmbedding (g.symm : Space → Space) :=
    g.symm.toHomeomorph.measurableEmbedding
  rw [← hmp.integral_comp hemb (fun z => g.toLinearIsometry (Heat.kernel (h * Real.exp τ) z •
    u (Real.exp (τ / 2) • g.symm y - z)))]
  have hrot : (fun z => g.toLinearIsometry (Heat.kernel (h * Real.exp τ) (g.symm z) •
      u (Real.exp (τ / 2) • g.symm y - g.symm z))) =
      fun z => Heat.kernel (h * Real.exp τ) z •
        rotateField g u (Real.exp (τ / 2) • y - z) := by
    funext z
    have hk : Heat.kernel (h * Real.exp τ) (g.symm z) = Heat.kernel (h * Real.exp τ) z := by
      simp only [Heat.kernel, Heat.Gaussian.kernel, LinearIsometryEquiv.norm_map]
    have harg : Real.exp (τ / 2) • g.symm y - g.symm z = g.symm (Real.exp (τ / 2) • y - z) := by
      rw [map_sub, map_smul]
    rw [hk, harg]
    simp only [rotateField, LinearIsometryEquiv.coe_toLinearIsometry, map_smul]
  rw [hrot]
  apply integral_congr_ae
  have hae := (Measure.measurePreserving_sub_left (volume : Measure Space)
    (Real.exp (τ / 2) • y)).quasiMeasurePreserving.ae_eq_comp
    (hu g hg)
  filter_upwards [hae] with z hz
  simp only [Function.comp_apply] at hz
  simp only [rotateField]
  rw [hz]

/-- `r_heat(τ)` is `𝒪`-invariant at every phase. -/
theorem rheat_symmetric {D : BackgroundData} (hD : IsUnstableBackground D) (τ : ℝ) :
    IsAxisymmetricNoSwirl ((D.rheat τ).value : SpatialField) := by
  intro g hg
  have hdec := hD.1.Ustar_decomposition τ
  have hr : ((D.rheat τ).value : SpatialField) =ᵐ[volume]
      fun y => D.Ustar τ y - heatProfile D.h D.udss τ y := by
    filter_upwards [hdec] with y hy
    rw [hy]
    abel
  have hUs := hD.1.Ustar_symmetric τ g hg
  have hr' := g.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp hr
  filter_upwards [hr', hUs, hr] with x h1 h2 h3
  simp only [Function.comp_apply] at h1
  rw [h1, map_sub, h2, heatProfile_rotate hD.1.udss_symmetric hg, h3]

theorem isSolenoidal_sub {f k : SpatialField} (hf : IsSolenoidal f) (hk : IsSolenoidal k) :
    IsSolenoidal (f - k) := by
  have he : ∀ φ : Space → ℝ, (fun x => ∑ i : Fin 3, ((f - k) x) i * spatialTestDerivative i φ x) =
      fun x => (∑ i : Fin 3, (f x) i * spatialTestDerivative i φ x) -
        ∑ i : Fin 3, (k x) i * spatialTestDerivative i φ x := by
    intro φ
    funext x
    simp only [Pi.sub_apply, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩
  · rw [he]
    exact (hf.integrable φ hφ).sub (hk.integrable φ hφ)
  · rw [he, integral_sub (hf.integrable φ hφ) (hk.integrable φ hφ), hf.identity φ hφ,
      hk.identity φ hφ, sub_zero]

/-- `r_heat(τ)` is solenoidal once the heat profile `H_h[u_dss](τ)` is. -/
theorem rheat_solenoidal_of {D : BackgroundData} (hD : IsUnstableBackground D) {τ : ℝ}
    (hH : IsSolenoidal (heatProfile D.h D.udss τ)) :
    (D.rheat τ).value ∈ Leray.solenoidalSubspace := by
  rw [Leray.mem_solenoidalSubspace_iff]
  have hdec := hD.1.Ustar_decomposition τ
  have hr : (D.Ustar τ - heatProfile D.h D.udss τ) =ᵐ[volume]
      ((D.rheat τ).value : SpatialField) := by
    filter_upwards [hdec] with y hy
    simp only [Pi.sub_apply, hy]
    abel
  exact Leray.solenoidal_congr_ae (isSolenoidal_sub (hD.1.Ustar_solenoidal τ) hH) hr

end UnforcedLeray.Blueprint.L13
