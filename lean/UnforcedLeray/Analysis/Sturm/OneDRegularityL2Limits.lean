import UnforcedLeray.Analysis.Sturm.L2TestPairing
import UnforcedLeray.Analysis.Sturm.FreeResolventEnergy

/-!
# L² limits from actual squared-integral errors

These lemmas convert concrete cutoff-error integrals into convergence in the
standard L² space and hence into convergence of actual weak test pairings.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace UnforcedLeray.Sturm
open NonUniqueEuler.Sob NonUniqueEuler.Sob.EnergyAux

theorem norm_toLp_sub_sq {f g : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, ‖f x - g x‖ ^ 2 := by
  rw [← MemLp.toLp_sub hf hg, Lp.norm_toLp]
  exact l2_sq_eq_integral (hf.sub hg)

theorem tendsto_toLp_of_integral_sq_sub {ι : Type*} {l : Filter ι}
    {f : ι → ℝ → ℂ} {g : ℝ → ℂ}
    (hf : ∀ i, MemLp (f i) 2 volume) (hg : MemLp g 2 volume)
    (herr : Tendsto (fun i => ∫ x, ‖f i x - g x‖ ^ 2) l (𝓝 0)) :
    Tendsto (fun i => (hf i).toLp (f i)) l (𝓝 (hg.toLp g)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp herr
  have heq : (fun i => Real.sqrt (∫ x, ‖f i x - g x‖ ^ 2)) =
      fun i => ‖(hf i).toLp (f i) - hg.toLp g‖ := by
    funext i
    rw [← norm_toLp_sub_sq (hf i) hg, Real.sqrt_sq (norm_nonneg _)]
  simpa only [Function.comp_def, heq, Real.sqrt_zero] using h

/-- Concrete L² cutoff errors imply convergence of all L² test pairings. -/
theorem tendsto_integral_mul_of_integral_sq_sub {ι : Type*} {l : Filter ι}
    {f : ι → ℝ → ℂ} {g u : ℝ → ℂ}
    (hf : ∀ i, MemLp (f i) 2 volume) (hg : MemLp g 2 volume)
    (hu : MemLp u 2 volume)
    (herr : Tendsto (fun i => ∫ x, ‖f i x - g x‖ ^ 2) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, u x * f i x) l (𝓝 (∫ x, u x * g x)) := by
  have h := (l2Pairing u hu).continuous.tendsto (hg.toLp g) |>.comp
    (tendsto_toLp_of_integral_sq_sub hf hg herr)
  have hp : ∀ (v : ℝ → ℂ) (hv : MemLp v 2 volume),
      l2Pairing u hu (hv.toLp v) = ∫ x, u x * v x := by
    intro v hv
    rw [l2Pairing_apply]
    apply integral_congr_ae
    filter_upwards [hv.coeFn_toLp] with x hx
    rw [hx, mul_comm]
  simpa only [Function.comp_def, hp] using h

end UnforcedLeray.Sturm
