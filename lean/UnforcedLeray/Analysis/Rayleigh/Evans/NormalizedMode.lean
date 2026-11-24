import UnforcedLeray.Analysis.Rayleigh.Evans.Solution
import UnforcedLeray.Analysis.Rayleigh.Normalization

/-!
# From an actual Evans zero to a normalized Gaussian annular mode

The normalization is derived from the constructed solution's nonzero initial
slope and positive interval mass. Existence of an upper-half-plane Evans zero
remains the separate instability obligation.
-/

noncomputable section
open MeasureTheory Set
namespace UnforcedLeray.Rayleigh.Evans

theorem exists_normalized_annular_mode_of_evans_zero {a b : ℝ} (hab : a < b)
    {c : ℂ} (hc : 0 < c.im) (he : evansFunction 2 a b c = 0) :
    ∃ F : ℝ → ℂ, GaussianAnnularMode c F a b ∧
      (∫ t in Ioc a b, ‖F t‖ ^ 2) = 1 :=
  exists_normalized_gaussian_mode (gaussianAnnularMode_of_evans_zero hab hc he)
    hab (normalizedF_nonzero_on_interval 2 hab hc)

end UnforcedLeray.Rayleigh.Evans
