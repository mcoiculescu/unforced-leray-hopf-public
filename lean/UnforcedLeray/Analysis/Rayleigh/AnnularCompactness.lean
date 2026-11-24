import UnforcedLeray.Analysis.Rayleigh.GaussianMode
import UnforcedLeray.Analysis.Rayleigh.UniformBound
import UnforcedLeray.Analysis.Rayleigh.CompactnessMass
import UnforcedLeray.Analysis.Rayleigh.CompactnessL2

/-!
# A genuine nonzero local limit of normalized Gaussian annular modes

Every compactness bound is derived from the actual Gaussian differential
boundary problem and normalization. The resulting full-line limit is
continuous, belongs to L², and is nonzero modulo null sets. This does not yet
assert its limiting differential equation or the existence of the input modes.
-/
noncomputable section
open MeasureTheory Set Filter Topology
namespace UnforcedLeray.Rayleigh

/-- Actual normalized Gaussian modes admit a nonzero L² local-uniform limit,
with no equicontinuity or compactness hypothesis added to the ODE assumptions. -/
theorem exists_nonzero_gaussian_annular_limit
    (c : ℕ → ℂ) (F : ℕ → ℝ → ℂ) (l r : ℕ → ℝ)
    (hmode : ∀ n, GaussianAnnularMode (c n) (F n) (l n) (r n))
    (hmass : ∀ n, (∫ t in Ioc (l n) (r n), ‖F n t‖ ^ 2) = 1) :
    ∃ (f : ℝ → ℂ) (φ : ℕ → ℕ), Continuous f ∧ StrictMono φ ∧
      TendstoLocallyUniformly
        (fun n => zeroExtension (l (φ n)) (r (φ n)) (F (φ n))) f atTop ∧
      MemLp f 2 volume ∧ (∫ t, ‖f t‖ ^ 2) ≤ 1 ∧
      ¬ f =ᵐ[volume] (0 : ℝ → ℂ) := by
  have hs := fun n => (hmode n).toShifted
  have hext : ∀ n, Continuous (zeroExtension (l n) (r n) (F n)) := by
    intro n
    exact zeroExtension_continuous (hmode n).regularity.continuous (hmode n).ordered
      (hmode n).left_endpoint (hmode n).right_endpoint
  obtain ⟨f, φ, hf, hφ, hu, hn⟩ := exists_nonzero_annular_limit
    (fun _ => gaussianOffset) (fun n => shiftedSpeed (c n)) F l r hs hmass hext 4 2
    (fun n => (hs n).normalized_zeroExtension_bound (hmass n))
    (fun n => (hs n).normalized_zeroExtension_holder (hmass n))
  have hp : ∀ t : ℝ,
      Tendsto (fun n => zeroExtension (l (φ n)) (r (φ n)) (F (φ n)) t)
        atTop (𝓝 (f t)) := by
    intro t
    exact ((tendstoLocallyUniformly_iff_forall_isCompact.mp hu) {t}
      isCompact_singleton).tendsto_at (mem_singleton t)
  have hL2 := normalized_zeroExtension_limit_memLp
    (fun n => F (φ n)) (fun n => l (φ n)) (fun n => r (φ n))
    (fun n => (hmode (φ n)).regularity.continuous) hf (fun n => hmass (φ n)) hp
  exact ⟨f, φ, hf, hφ, hu, hL2.1, hL2.2, hn⟩

/-- Restricting the sequence parameter to a strict subsequence preserves actual
local uniform convergence on the whole real line. -/
theorem locallyUniform_subseq {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    (hF : TendstoLocallyUniformly F f atTop) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    TendstoLocallyUniformly (fun n => F (φ n)) f atTop := by
  intro U hU x
  obtain ⟨S, hS, he⟩ := hF U hU x
  exact ⟨S, hS, hφ.tendsto_atTop.eventually he⟩

end UnforcedLeray.Rayleigh
