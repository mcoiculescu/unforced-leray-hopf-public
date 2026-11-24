import UnforcedLeray.Analysis.Rayleigh.Compactness
import UnforcedLeray.Analysis.Sturm.L2TestPairing
import NonUniqueEuler.P.Infra.Sobolev.WeakDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Local-uniform limits and weak L² limits identify the same actual function:
compact smooth test pairings converge by a genuine integrable majorant, and
the fundamental lemma identifies the two representatives almost everywhere. -/
noncomputable section
open MeasureTheory Set Filter Topology
namespace UnforcedLeray.Rayleigh
open Sturm NonUniqueEuler.Sob

theorem tendsto_testPairing_of_locallyUniform
    (F : ℕ → ℝ → ℂ) {f : ℝ → ℂ} (hF : ∀ n, Continuous (F n))
    (M : ℝ) (hsup : ∀ n x, ‖F n x‖ ≤ M)
    (hu : TendstoLocallyUniformly F f atTop)
    (ψ : ℝ → ℂ) (hψ : IsTestFn univ ψ) :
    Tendsto (fun n => ∫ t, F n t * ψ t) atTop (𝓝 (∫ t, f t * ψ t)) := by
  apply tendsto_integral_of_dominated_convergence (fun t => M * ‖ψ t‖)
  · intro n
    exact ((hF n).mul hψ.continuous).aestronglyMeasurable
  · exact (hψ.continuous.integrable_of_hasCompactSupport hψ.compact).norm.const_mul M
  · intro n
    exact Eventually.of_forall fun t => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hsup n t) (norm_nonneg _)
  · exact Eventually.of_forall fun t => by
      have hp := ((tendstoLocallyUniformly_iff_forall_isCompact.mp hu) {t}
        isCompact_singleton).tendsto_at (mem_singleton t)
      exact hp.mul_const (ψ t)

/-- The actual local-uniform and L²-distributional limits agree a.e.; no equality
of limiting representatives is assumed in the annular construction. -/
theorem ae_eq_of_locallyUniform_and_pairing_limit
    (F : ℕ → ℝ → ℂ) {f g : ℝ → ℂ} (hF : ∀ n, Continuous (F n))
    (M : ℝ) (hsup : ∀ n x, ‖F n x‖ ≤ M)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hu : TendstoLocallyUniformly F f atTop)
    (hpair : ∀ ψ : ℝ → ℂ, MemLp ψ 2 volume →
      Tendsto (fun n => ∫ t, F n t * ψ t) atTop (𝓝 (∫ t, g t * ψ t))) :
    f =ᵐ[volume] g := by
  have he := WeakDerivAux.ae_eq_of_integral_testFn isOpen_univ
    ((hf.locallyIntegrable (by norm_num)).locallyIntegrableOn univ)
    ((hg.locallyIntegrable (by norm_num)).locallyIntegrableOn univ)
    (fun ψ hψ => tendsto_nhds_unique
      (tendsto_testPairing_of_locallyUniform F hF M hsup hu ψ hψ)
      (hpair ψ (testFn_memLp hψ)))
  filter_upwards [he] with t ht
  exact ht (mem_univ t)

end UnforcedLeray.Rayleigh
