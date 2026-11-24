import UnforcedLeray.Analysis.Rayleigh.ZeroExtension
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Global L² control of an annular local limit

Fatou's theorem, through Mathlib's actual Lp seminorm, bounds the full-line
squared mass of a pointwise limit of normalized zero extensions. The argument
does not assert strong global L² convergence or preservation of all the mass.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace UnforcedLeray.Rayleigh

/-- Exact L¹ seminorm of the nonnegative square of a genuine L² field. -/
theorem eLpNorm_norm_sq_one_eq {F : ℝ → ℂ} (hF : MemLp F 2 volume) :
    eLpNorm (fun t => ‖F t‖ ^ 2) 1 volume =
      ENNReal.ofReal (∫ t, ‖F t‖ ^ 2) := by
  have hi : Integrable (fun t => ‖F t‖ ^ 2) := hF.integrable_norm_pow (by norm_num)
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm hi]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    change ‖‖F t‖ ^ 2‖ = ‖F t‖ ^ 2
    exact Real.norm_of_nonneg (sq_nonneg _)

/-- Fatou gives the actual finite L² membership and global mass bound for the limit. -/
theorem memLp_two_and_mass_le_of_pointwise_limit
    (F : ℕ → ℝ → ℂ) {f : ℝ → ℂ}
    (hF : ∀ n, MemLp (F n) 2 volume) (hf : Continuous f)
    (hmass : ∀ n, (∫ t, ‖F n t‖ ^ 2) ≤ 1)
    (hlim : ∀ t, Tendsto (fun n => F n t) atTop (𝓝 (f t))) :
    MemLp f 2 volume ∧ (∫ t, ‖f t‖ ^ 2) ≤ 1 := by
  have hs : ∀ n, AEStronglyMeasurable (fun t => ‖F n t‖ ^ 2) volume :=
    fun n => ((hF n).aestronglyMeasurable.norm.pow 2)
  have hb : ∀ᶠ n in atTop, eLpNorm (fun t => ‖F n t‖ ^ 2) 1 volume ≤ 1 := by
    apply Eventually.of_forall
    intro n
    rw [eLpNorm_norm_sq_one_eq (hF n)]
    exact (ENNReal.ofReal_le_ofReal (hmass n)).trans_eq (by simp)
  have ht : ∀ᵐ t ∂volume,
      Tendsto (fun n => ‖F n t‖ ^ 2) atTop (𝓝 (‖f t‖ ^ 2)) :=
    Eventually.of_forall fun t => (hlim t).norm.pow 2
  have hbound : eLpNorm (fun t => ‖f t‖ ^ 2) 1 volume ≤ 1 :=
    Lp.eLpNorm_le_of_ae_tendsto hb hs ht
  have h1 : MemLp (fun t => ‖f t‖ ^ 2) 1 volume :=
    ⟨(hf.norm.pow 2).aestronglyMeasurable, hbound.trans_lt (by simp)⟩
  have hi : Integrable (fun t => ‖f t‖ ^ 2) := memLp_one_iff_integrable.mp h1
  have h2 : MemLp f 2 volume :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr hi
  refine ⟨h2, ?_⟩
  rw [eLpNorm_norm_sq_one_eq h2] at hbound
  have htReal := ENNReal.toReal_mono (show (1 : ℝ≥0∞) ≠ ∞ by simp) hbound
  simpa only [ENNReal.toReal_one,
    ENNReal.toReal_ofReal (integral_nonneg fun t => sq_nonneg ‖f t‖)] using htReal

/-- The actual normalized annular zero extensions give a global L² limit
of mass at most one as soon as their local-uniform limit is identified pointwise. -/
theorem normalized_zeroExtension_limit_memLp
    (F : ℕ → ℝ → ℂ) (l r : ℕ → ℝ) {f : ℝ → ℂ}
    (hF : ∀ n, Continuous (F n)) (hf : Continuous f)
    (hmass : ∀ n, (∫ t in Ioc (l n) (r n), ‖F n t‖ ^ 2) = 1)
    (hlim : ∀ t, Tendsto (fun n => zeroExtension (l n) (r n) (F n) t)
      atTop (𝓝 (f t))) :
    MemLp f 2 volume ∧ (∫ t, ‖f t‖ ^ 2) ≤ 1 := by
  apply memLp_two_and_mass_le_of_pointwise_limit
    (fun n => zeroExtension (l n) (r n) (F n))
    (fun n => zeroExtension_memLp (hF n) (l n) (r n)) hf ?_ hlim
  intro n
  rw [integral_norm_sq_zeroExtension, hmass n]

end UnforcedLeray.Rayleigh
