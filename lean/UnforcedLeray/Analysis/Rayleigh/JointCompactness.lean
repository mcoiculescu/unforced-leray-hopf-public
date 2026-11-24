import UnforcedLeray.Analysis.Rayleigh.AnnularCompactness
import UnforcedLeray.Analysis.Rayleigh.SpeedBound

/-!
# Simultaneous compactness of actual annular speeds and modes

The actual Rayleigh identities supply both compactness inputs. A common strict
subsequence has a bounded upper-half-plane-closure speed limit and a nonzero
full-line L² field limit. No speed bound, equicontinuity, or compactness premise
is imported from Lin's theorem.
-/
noncomputable section
open MeasureTheory Set Filter Topology
namespace UnforcedLeray.Rayleigh

theorem exists_joint_gaussian_annular_limit
    (c : ℕ → ℂ) (F : ℕ → ℝ → ℂ) (l r : ℕ → ℝ)
    (hmode : ∀ n, GaussianAnnularMode (c n) (F n) (l n) (r n))
    (hmass : ∀ n, (∫ t in Ioc (l n) (r n), ‖F n t‖ ^ 2) = 1) :
    ∃ (cLimit : ℂ) (f : ℝ → ℂ) (φ : ℕ → ℕ),
      StrictMono φ ∧ Continuous f ∧ MemLp f 2 volume ∧
      (∫ t, ‖f t‖ ^ 2) ≤ 1 ∧ ¬ f =ᵐ[volume] (0 : ℝ → ℂ) ∧
      Tendsto (fun n => c (φ n)) atTop (𝓝 cLimit) ∧
      0 ≤ cLimit.im ∧ ‖cLimit‖ ≤ 2 ∧
      TendstoLocallyUniformly
        (fun n => zeroExtension (l (φ n)) (r (φ n)) (F (φ n))) f atTop := by
  obtain ⟨f, φ, hf, hφ, hu, hmem, hmassf, hne⟩ :=
    exists_nonzero_gaussian_annular_limit c F l r hmode hmass
  have hbound : ∀ n, c (φ n) ∈ Metric.closedBall (0 : ℂ) 2 := by
    intro n
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      ((hmode (φ n)).normalized_speed_norm_lt_two (hmass (φ n))).le
  obtain ⟨cLimit, hcLimit, ψ, hψ, hlim⟩ := (isCompact_closedBall (0 : ℂ) 2).tendsto_subseq hbound
  have him : Tendsto (fun n => (c (φ (ψ n))).im) atTop (𝓝 cLimit.im) :=
    Complex.continuous_im.continuousAt.tendsto.comp hlim
  have hnonneg : 0 ≤ cLimit.im := ge_of_tendsto him
    (Eventually.of_forall fun n => (hmode (φ (ψ n))).upper_half_plane.le)
  have hnorm : ‖cLimit‖ ≤ 2 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hcLimit
  exact ⟨cLimit, f, φ ∘ ψ, hφ.comp hψ, hf, hmem, hmassf, hne, hlim,
    hnonneg, hnorm, locallyUniform_subseq hu hψ⟩

end UnforcedLeray.Rayleigh
