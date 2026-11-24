import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_3_1.TestPairing
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayGradPerp.Cutoff
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Age and `η` cutoffs for the classical pairing
(helper of `PartIII-b:C/flatset/col/7/1/1/3/1`)

* `thetaS S s = 1 - smoothTransition (s - S)` : smooth decreasing age cutoff (`= 1` on `s ≤ S`,
  `= 0` on `s ≥ S + 1`, `deriv (thetaS S) s ≤ 0` everywhere).
* `chiR R η = GradPerpCut.chi (η / R)` : smooth symmetric `η`-cutoff (`= 1` on `|η| ≤ R`,
  `= 0` on `|η| ≥ 2R`, `|deriv (chiR R) η| ≤ B / R`).
* `zetaCut S R b p = (thetaS S p.1 * chiR R p.2.2) • bm b p` : satisfies `IsMeridTest c` and
  `‖zetaCut S R b p‖ ≤ vnorm2 (b p)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.IIIa (vnorm2)
open UnforcedLeray.Short.PartIIa (IsMeridTest)

/-- Smooth decreasing age cutoff equal to `1` for `s ≤ S` and `0` for `s ≥ S + 1`. -/
def thetaS (S s : ℝ) : ℝ := 1 - Real.smoothTransition (s - S)

theorem contDiff_thetaS (S : ℝ) : ContDiff ℝ ∞ (thetaS S) :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

theorem thetaS_nonneg (S s : ℝ) : 0 ≤ thetaS S s :=
  sub_nonneg.2 (Real.smoothTransition.le_one _)

theorem thetaS_le_one (S s : ℝ) : thetaS S s ≤ 1 :=
  sub_le_self 1 (Real.smoothTransition.nonneg _)

theorem thetaS_eq_one {S s : ℝ} (h : s ≤ S) : thetaS S s = 1 := by
  unfold thetaS
  rw [Real.smoothTransition.zero_of_nonpos (sub_nonpos.2 h), sub_zero]

theorem thetaS_eq_zero {S s : ℝ} (h : S + 1 ≤ s) : thetaS S s = 0 := by
  unfold thetaS
  rw [Real.smoothTransition.one_of_one_le (by linarith), sub_self]

theorem antitone_thetaS (S : ℝ) : Antitone (thetaS S) := by
  intro x y hxy
  exact sub_le_sub_left (Real.smoothTransition.monotone (sub_le_sub_right hxy S)) 1

theorem deriv_thetaS_nonpos (S s : ℝ) : deriv (thetaS S) s ≤ 0 :=
  (antitone_thetaS S).deriv_nonpos

/-- Smooth `η`-cutoff equal to `1` on `|η| ≤ R` and `0` on `|η| ≥ 2R`. -/
def chiR (R η : ℝ) : ℝ := GradPerpCut.chi (η / R)

theorem contDiff_chiR (R : ℝ) : ContDiff ℝ ∞ (chiR R) :=
  GradPerpCut.contDiff_chi.comp (contDiff_id.div_const R)

theorem chiR_nonneg (R η : ℝ) : 0 ≤ chiR R η :=
  GradPerpCut.chi_nonneg (η / R)

theorem chiR_le_one (R η : ℝ) : chiR R η ≤ 1 :=
  GradPerpCut.chi_le_one (η / R)

theorem chiR_eq_one {R η : ℝ} (hR : 0 < R) (h : |η| ≤ R) : chiR R η = 1 := by
  apply GradPerpCut.chi_one
  have h1 : |η / R| ≤ 1 := by
    rw [abs_div, abs_of_pos hR, div_le_one hR]
    exact h
  have h2 : (η / R) ^ 2 ≤ 1 ^ 2 := sq_le_sq.2 (by simpa using h1)
  linarith

theorem chiR_eq_zero {R η : ℝ} (hR : 0 < R) (h : 2 * R ≤ |η|) : chiR R η = 0 := by
  apply GradPerpCut.chi_zero
  have h1 : 2 ≤ |η / R| := by
    rw [abs_div, abs_of_pos hR, le_div_iff₀ hR]
    exact h
  have h2 : (2 : ℝ) ^ 2 ≤ |η / R| ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
  rw [sq_abs] at h2
  linarith

theorem hasDerivAt_chiR (R η : ℝ) :
    HasDerivAt (chiR R) (deriv GradPerpCut.chi (η / R) * R⁻¹) η := by
  have h1 : HasDerivAt GradPerpCut.chi (deriv GradPerpCut.chi (η / R)) (η / R) :=
    (GradPerpCut.contDiff_chi.differentiable (by simp) (η / R)).hasDerivAt
  have h2 : HasDerivAt (fun x : ℝ => x / R) R⁻¹ η := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id η).mul_const R⁻¹
  exact h1.comp η h2

theorem deriv_chiR_eq (R η : ℝ) :
    deriv (chiR R) η = deriv GradPerpCut.chi (η / R) * R⁻¹ :=
  (hasDerivAt_chiR R η).deriv

theorem abs_deriv_chiR_le {B : ℝ} (hB : ∀ t, |deriv GradPerpCut.chi t| ≤ B) {R : ℝ}
    (hR : 0 < R) (η : ℝ) : |deriv (chiR R) η| ≤ B / R := by
  rw [deriv_chiR_eq, abs_mul, abs_inv, abs_of_pos hR, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right (hB (η / R)) hR.le

/-- `bm b` is `ContDiff ℝ ∞` when each component of `b` is. -/
theorem contDiff_bm {b : Chart → Fin 2 → ℂ}
    (hb : ∀ i : Fin 2, ContDiff ℝ ∞ (fun p : Chart => b p i)) :
    ContDiff ℝ ∞ (bm b) := by
  have heq : bm b = fun p =>
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℂ)).symm (b p) := rfl
  rw [heq]
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℂ)).symm.contDiff.comp
    (contDiff_pi.2 hb)

/-- The cutoff test `ζ_{S,R}(p) = (thetaS S p.1 * chiR R p.2.2) • bm b p`. -/
def zetaCut (S R : ℝ) (b : Chart → Fin 2 → ℂ) (p : Profile) : MeridC :=
  (thetaS S p.1 * chiR R p.2.2) • bm b p

theorem zetaCut_isMeridTest {c s0 : ℝ} {b : Chart → Fin 2 → ℂ} (hb : SmoothRep c b)
    (hs0 : 0 < s0) (hz : ∀ p : Chart, p.1 < s0 → b p = 0) (S : ℝ) {R : ℝ} (hR : 0 < R) :
    IsMeridTest c (zetaCut S R b) := by
  have hbm : ContDiff ℝ ∞ (bm b) := contDiff_bm (smoothRep_contDiff hb hs0 hz)
  have hth : ContDiff ℝ ∞ (fun p : Profile => thetaS S p.1) :=
    (contDiff_thetaS S).comp contDiff_fst
  have hch : ContDiff ℝ ∞ (fun p : Profile => chiR R p.2.2) :=
    (contDiff_chiR R).comp (contDiff_snd.comp contDiff_snd)
  refine ⟨(hth.mul hch).smul hbm, ?_, ?_⟩
  · intro ⟨s, q, η⟩
    unfold zetaCut bm
    simp only [smoothRep_periodic hb s q η]
  · refine ⟨s0, max s0 (S + 1), 2 * R, hs0, fun p hp => ?_⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · by_contra hlt
      push_neg at hlt
      apply hp
      unfold zetaCut bm
      rw [hz p hlt]
      simp
    · by_contra hgt
      push_neg at hgt
      apply hp
      unfold zetaCut
      have hS1 : S + 1 ≤ p.1 := le_trans (le_max_right s0 (S + 1)) hgt.le
      rw [thetaS_eq_zero hS1, zero_mul, zero_smul]
    · by_contra hgt
      push_neg at hgt
      apply hp
      unfold zetaCut
      rw [chiR_eq_zero hR hgt.le, mul_zero, zero_smul]

theorem norm_zetaCut_le (S R : ℝ) (b : Chart → Fin 2 → ℂ) (p : Profile) :
    ‖zetaCut S R b p‖ ≤ vnorm2 (b p) := by
  unfold zetaCut
  have hw0 : 0 ≤ thetaS S p.1 * chiR R p.2.2 :=
    mul_nonneg (thetaS_nonneg S p.1) (chiR_nonneg R p.2.2)
  have hw1 : thetaS S p.1 * chiR R p.2.2 ≤ 1 :=
    mul_le_one₀ (thetaS_le_one S p.1) (chiR_nonneg R p.2.2) (chiR_le_one R p.2.2)
  rw [norm_smul, Real.norm_of_nonneg hw0, norm_bm]
  exact mul_le_of_le_one_left (by unfold vnorm2; positivity) hw1

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
