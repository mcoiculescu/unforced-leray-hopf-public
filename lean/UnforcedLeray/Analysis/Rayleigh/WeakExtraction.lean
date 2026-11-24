import UnforcedLeray.Analysis.Rayleigh.ZeroExtension
import UnforcedLeray.Analysis.WeakCompactness
import UnforcedLeray.Analysis.Sturm.CompactL2

/-!
# Common weak L² extraction for actual annular modes

The three sequences are the actual zero-extended field, its first weak
spatial derivative, and its interior second-order residual. Their norms are
proved bounded by one, two and eight. A single strict subsequence converges
weakly for all three. The residual zero extension is not asserted to be the
global second derivative: endpoint derivative jumps are not discarded.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace UnforcedLeray.Rayleigh
open Sturm

lemma norm_toLp_sq_eq_integral (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 := by
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  have h0 : 0 ≤ ∫ t, ‖f t‖ ^ (2 : ENNReal).toReal :=
    integral_nonneg fun _ => by positivity
  rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul h0]
  simp

namespace ShiftedAnnularMode
variable {q : ℝ → ℝ} {z : ℂ} {F : ℝ → ℂ} {l r : ℝ}
  (h : ShiftedAnnularMode q z F l r)

/-- The actual zero-extended field as a Lebesgue L² class. -/
def fieldL2 : ComplexL2 :=
  (zeroExtension_memLp h.regularity.continuous l r).toLp (zeroExtension l r F)

/-- The actual weak first derivative of the zero extension. -/
def derivativeL2 : ComplexL2 :=
  (zeroExtension_memLp (h.regularity.continuous_deriv (by norm_num)) l r).toLp
    (zeroExtension l r (deriv F))

/-- Only the interior residual is extended by zero here. -/
def residualL2 : ComplexL2 :=
  (zeroExtension_memLp ((continuous_second_of_two h.regularity).sub
    (h.regularity.continuous.const_mul 4)) l r).toLp
    (zeroExtension l r (fun t => deriv (deriv F) t - 4 * F t))

lemma coeFn_fieldL2 : (h.fieldL2 : ℝ → ℂ) =ᵐ[volume] zeroExtension l r F :=
  (zeroExtension_memLp h.regularity.continuous l r).coeFn_toLp

lemma coeFn_derivativeL2 : (h.derivativeL2 : ℝ → ℂ) =ᵐ[volume]
    zeroExtension l r (deriv F) :=
  (zeroExtension_memLp (h.regularity.continuous_deriv (by norm_num)) l r).coeFn_toLp

lemma coeFn_residualL2 : (h.residualL2 : ℝ → ℂ) =ᵐ[volume]
    zeroExtension l r (fun t => deriv (deriv F) t - 4 * F t) :=
  (zeroExtension_memLp ((continuous_second_of_two h.regularity).sub
    (h.regularity.continuous.const_mul 4)) l r).coeFn_toLp

lemma fieldL2_norm_sq : ‖h.fieldL2‖ ^ 2 = ∫ t in Ioc l r, ‖F t‖ ^ 2 := by
  rw [fieldL2, norm_toLp_sq_eq_integral, integral_norm_sq_zeroExtension]

lemma derivativeL2_norm_sq :
    ‖h.derivativeL2‖ ^ 2 = ∫ t, ‖zeroExtension l r (deriv F) t‖ ^ 2 := by
  rw [derivativeL2, norm_toLp_sq_eq_integral]

lemma residualL2_norm_sq :
    ‖h.residualL2‖ ^ 2 = ∫ t in Ioc l r, ‖deriv (deriv F) t - 4 * F t‖ ^ 2 := by
  rw [residualL2, norm_toLp_sq_eq_integral, integral_norm_sq_zeroExtension]

/-- The L² normalization is preserved by the actual null-set quotient. -/
theorem fieldL2_norm_eq_one (hmass : (∫ t in Ioc l r, ‖F t‖ ^ 2) = 1) :
    ‖h.fieldL2‖ = 1 := by
  have hs := h.fieldL2_norm_sq
  rw [hmass] at hs
  nlinarith [norm_nonneg h.fieldL2]

theorem derivativeL2_norm_le_two (hmass : (∫ t in Ioc l r, ‖F t‖ ^ 2) = 1) :
    ‖h.derivativeL2‖ ≤ 2 := by
  have hb := h.normalized_zeroExtension_derivative_bound hmass
  rw [← h.derivativeL2_norm_sq] at hb
  nlinarith

theorem residualL2_norm_le_eight (hmass : (∫ t in Ioc l r, ‖F t‖ ^ 2) = 1) :
    ‖h.residualL2‖ ≤ 8 := by
  have hb := h.normalized_integral_freeResidual_sq_le hmass
  rw [← h.residualL2_norm_sq] at hb
  nlinarith

end ShiftedAnnularMode

/-- A single strict subsequence for all three actual bounded annular sequences. -/
theorem exists_common_weak_subsequence
    {q : ℕ → ℝ → ℝ} {z : ℕ → ℂ} {F : ℕ → ℝ → ℂ} {l r : ℕ → ℝ}
    (h : ∀ n, ShiftedAnnularMode (q n) (z n) (F n) (l n) (r n))
    (hmass : ∀ n, (∫ t in Ioc (l n) (r n), ‖F n t‖ ^ 2) = 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f g k : ComplexL2,
      ‖f‖ ≤ 1 ∧ ‖g‖ ≤ 2 ∧ ‖k‖ ≤ 8 ∧
      WeakL2.WeakTendsto (fun n => (h (φ n)).fieldL2) atTop f ∧
      WeakL2.WeakTendsto (fun n => (h (φ n)).derivativeL2) atTop g ∧
      WeakL2.WeakTendsto (fun n => (h (φ n)).residualL2) atTop k := by
  let u : ℕ → ℕ → ComplexL2 := fun i n =>
    match i with
    | 0 => (h n).fieldL2
    | 1 => (h n).derivativeL2
    | 2 => (h n).residualL2
    | _ => 0
  let M : ℕ → ℝ := fun i =>
    match i with
    | 0 => 1
    | 1 => 2
    | 2 => 8
    | _ => 0
  have hu : ∀ i n, ‖u i n‖ ≤ M i := by
    intro i n
    cases i with
    | zero => exact ((h n).fieldL2_norm_eq_one (hmass n)).le
    | succ i =>
      cases i with
      | zero => exact (h n).derivativeL2_norm_le_two (hmass n)
      | succ i =>
        cases i with
        | zero => exact (h n).residualL2_norm_le_eight (hmass n)
        | succ i => simp only [u, M, norm_zero, le_refl]
  obtain ⟨φ, hφ, x, hx⟩ := WeakL2.exists_subseq_weakTendsto_forall u M hu
  refine ⟨φ, hφ, x 0, x 1, x 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hx 0).1
  · exact (hx 1).1
  · exact (hx 2).1
  · exact (hx 0).2
  · exact (hx 1).2
  · exact (hx 2).2

end UnforcedLeray.Rayleigh
