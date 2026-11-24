import UnforcedLeray.Analysis.Rayleigh.Evans.NormalizedMode
import UnforcedLeray.Analysis.Rayleigh.SpeedBound

/-!
# A nonzero value of the angular-two Evans function

The actual Gaussian energy estimate excludes every upper-half-plane zero
with speed norm at least two. In particular, the Evans function is not
identically zero. This excludes an identically vanishing holomorphic
function; it does not assert that any unstable zero exists.
-/

noncomputable section
namespace UnforcedLeray.Rayleigh.Evans

theorem evansFunction_ne_zero_of_two_le_norm {a b : ℝ} (hab : a < b)
    {c : ℂ} (hc : 0 < c.im) (hcnorm : 2 ≤ ‖c‖) :
    evansFunction 2 a b c ≠ 0 := by
  intro he
  obtain ⟨F, hF, hmass⟩ := exists_normalized_annular_mode_of_evans_zero hab hc he
  exact (not_lt_of_ge hcnorm) (hF.normalized_speed_norm_lt_two hmass)

theorem evansFunction_two_I_ne_zero {a b : ℝ} (hab : a < b) :
    evansFunction 2 a b ((2 : ℂ) * Complex.I) ≠ 0 := by
  apply evansFunction_ne_zero_of_two_le_norm hab
  · norm_num
  · norm_num [norm_mul]

theorem exists_upperHalfPlane_evansFunction_ne_zero {a b : ℝ} (hab : a < b) :
    ∃ c ∈ upperHalfPlane, evansFunction 2 a b c ≠ 0 := by
  refine ⟨(2 : ℂ) * Complex.I, ?_, evansFunction_two_I_ne_zero hab⟩
  norm_num [upperHalfPlane]

end UnforcedLeray.Rayleigh.Evans
