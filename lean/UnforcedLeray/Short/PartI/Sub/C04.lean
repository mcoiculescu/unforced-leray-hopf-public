import UnforcedLeray.Short.PartI.StatementsSeed
import UnforcedLeray.Lib.PlanarSpectralB.XGSpectrum

/-!
# Part I, task `PartI:C04`: deflated stability of `L - λ - P` (corrected rate)

Source of record: `the November 2 reference manuscript`, lines 1038-1046
("The inviscid complementary semigroup estimate, with any rate below `γ`, makes `L - λ - P`
exponentially stable").




for every `δ > 0`. This forces `Re λ ≤ 1`: `q` is an eigenvector with `P q = ℓ(q) q = q`, so
`(L₀ - λ - P) q = -q` and `‖exp(t(L₀ - λ - P))‖ ≥ e^{-t}`. The source never bounds `Re λ`
(it only records `γ = Re λ > 0`), and the library has no such bound for an abstract
`IsSeedXG` triple. The source's "any rate below `γ`" is correct as stated for `γ ≤ 1`; for
`γ > 1` the true rate is `1`. The only downstream use (source lines 1048-1052, task `PartI:C05`)
needs `‖e^{B(L-λ-P)}‖ → 0` as `B → ∞`, i.e. some positive rate.

The theorem below is the correct statement, with rate `min(Re λ, 1) - δ`. It is fully proved.
It reduces to the original target exactly when `Re λ ≤ 1` (`exp_deflated_decay_of_re_le_one_min`).

## Proof

With `P = rankOneProj ℓ q` and `A = L₀ - λ`: `A P = P A = 0`, `P² = P`, so
`exp(t(A - P)) = exp(tA)(1 - P) + e^{-t} P`. The first term is bounded by
`Planar.norm_exp_L0_sub_mul_one_sub_le` (rate `Re λ - δ ≥ min(Re λ,1) - δ`), the second by
`e^{-t} ‖P‖ ≤ e^{-(min(Re λ,1) - δ)t} ‖P‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology ComplexConjugate

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Infra.Dunford (IsSimpleSpectralProj rankOneProj)

/-- **`PartI:C04`, corrected rate** (source lines 1038-1046): the deflated semigroup
`exp(t(L₀ - λ - P))` decays at every rate below `min(Re λ, 1)`. -/
theorem exp_deflated_decay_minrate {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ}
    (hI : IsSeedXG lam q l) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp ((t : ℂ) • (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) -
        rankOneProj l q))‖ ≤ C * Real.exp (-(min lam.re 1 - δ) * t) := by
  obtain ⟨C, hC, hCb⟩ :=
    Planar.norm_exp_L0_sub_mul_one_sub_le hI.re_pos hI.ne_zero hI.eigen hI.proj hδ
  have hidem : rankOneProj l q * rankOneProj l q = rankOneProj l q := hI.proj.idem
  have hmul : Planar.L0 * rankOneProj l q = lam • rankOneProj l q := hI.proj.mul_proj
  have hpm : rankOneProj l q * Planar.L0 = lam • rankOneProj l q := hI.proj.proj_mul
  have hAP : (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG)) * rankOneProj l q = 0 := by
    rw [sub_mul, smul_mul_assoc, one_mul, hmul, sub_self]
  have hPA : rankOneProj l q * (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG)) = 0 := by
    rw [mul_sub, mul_smul_comm, mul_one, hpm, sub_self]
  have hAPc : Commute (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG))
      (rankOneProj l q) := by
    unfold Commute SemiconjBy
    rw [hAP, hPA]
  refine ⟨C + ‖rankOneProj l q‖, add_pos_of_pos_of_nonneg hC (norm_nonneg _), fun t ht => ?_⟩
  have hsplit : (t : ℂ) • (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) -
      rankOneProj l q) =
      (t : ℂ) • (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG)) +
        (-(t : ℂ)) • rankOneProj l q := by
    simp only [smul_sub, neg_smul]
    abel
  have hc : Commute ((t : ℂ) • (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG)))
      ((-(t : ℂ)) • rankOneProj l q) :=
    (hAPc.smul_left _).smul_right _
  have hX : NormedSpace.exp ((t : ℂ) • (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG))) *
      rankOneProj l q = rankOneProj l q := by
    have h0 : ((t : ℂ) • (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG))) *
        rankOneProj l q = (0 : ℂ) • rankOneProj l q := by
      rw [smul_mul_assoc, hAP, smul_zero, zero_smul]
    rw [Infra.Dunford.Deflation.exp_mul_of_mul_eq_smul h0, Complex.exp_zero, one_smul]
  have hY1 : NormedSpace.exp ((-(t : ℂ)) • rankOneProj l q) *
      (1 - rankOneProj l q) = 1 - rankOneProj l q := by
    have h0 : ((-(t : ℂ)) • rankOneProj l q) * (1 - rankOneProj l q) =
        (0 : ℂ) • (1 - rankOneProj l q) := by
      rw [smul_mul_assoc, mul_sub, mul_one, hidem, sub_self, smul_zero, zero_smul]
    rw [Infra.Dunford.Deflation.exp_mul_of_mul_eq_smul h0, Complex.exp_zero, one_smul]
  have hY2 : NormedSpace.exp ((-(t : ℂ)) • rankOneProj l q) * rankOneProj l q =
      Complex.exp (-(t : ℂ)) • rankOneProj l q := by
    have h0 : ((-(t : ℂ)) • rankOneProj l q) * rankOneProj l q =
        (-(t : ℂ)) • rankOneProj l q := by
      rw [smul_mul_assoc, hidem]
    exact Infra.Dunford.Deflation.exp_mul_of_mul_eq_smul h0
  have hYeq : NormedSpace.exp ((-(t : ℂ)) • rankOneProj l q) =
      (1 - rankOneProj l q) + Complex.exp (-(t : ℂ)) • rankOneProj l q := by
    have hsum : NormedSpace.exp ((-(t : ℂ)) • rankOneProj l q) =
        NormedSpace.exp ((-(t : ℂ)) • rankOneProj l q) * (1 - rankOneProj l q) +
          NormedSpace.exp ((-(t : ℂ)) • rankOneProj l q) * rankOneProj l q := by
      rw [← mul_add, sub_add_cancel, mul_one]
    rw [hsum, hY1, hY2]
  have hdecomp : NormedSpace.exp ((t : ℂ) • (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG)) +
      (-(t : ℂ)) • rankOneProj l q) =
      NormedSpace.exp ((t : ℂ) • (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG))) *
        (1 - rankOneProj l q) + Complex.exp (-(t : ℂ)) • rankOneProj l q := by
    rw [Infra.Dunford.Deflation.exp_add_of_commute hc, hYeq, mul_add, mul_smul_comm, hX]
  rw [hsplit, hdecomp]
  have hT := hCb t ht
  have hmin1 : min lam.re 1 ≤ lam.re := min_le_left _ _
  have hmin2 : min lam.re 1 ≤ 1 := min_le_right _ _
  have hE : Real.exp (-t) ≤ Real.exp (-(min lam.re 1 - δ) * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - min lam.re 1 + δ by linarith) ht]
  have hE' : Real.exp (-(lam.re - δ) * t) ≤ Real.exp (-(min lam.re 1 - δ) * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ lam.re - min lam.re 1 by linarith) ht]
  have hnormY : ‖Complex.exp (-(t : ℂ)) • rankOneProj l q‖ =
      Real.exp (-t) * ‖rankOneProj l q‖ := by
    rw [norm_smul, Complex.norm_exp]
    simp
  have hsumn := norm_add_le
    (NormedSpace.exp ((t : ℂ) • (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG))) *
      (1 - rankOneProj l q))
    (Complex.exp (-(t : ℂ)) • rankOneProj l q)
  have hEP : Real.exp (-t) * ‖rankOneProj l q‖ ≤
      Real.exp (-(min lam.re 1 - δ) * t) * ‖rankOneProj l q‖ :=
    mul_le_mul_of_nonneg_right hE (norm_nonneg _)
  have hTT : C * Real.exp (-(lam.re - δ) * t) ≤ C * Real.exp (-(min lam.re 1 - δ) * t) :=
    mul_le_mul_of_nonneg_left hE' hC.le
  have hid : (C + ‖rankOneProj l q‖) * Real.exp (-(min lam.re 1 - δ) * t) =
      C * Real.exp (-(min lam.re 1 - δ) * t) +
        Real.exp (-(min lam.re 1 - δ) * t) * ‖rankOneProj l q‖ := by
    ring
  linarith [hsumn, hT, hnormY, hEP, hid, hTT]

/---/
theorem exp_deflated_decay_of_re_le_one_min {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ}
    (hI : IsSeedXG lam q l) (hre : lam.re ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp ((t : ℂ) • (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) -
        rankOneProj l q))‖ ≤ C * Real.exp (-(lam.re - δ) * t) := by
  simpa [min_eq_left hre] using exp_deflated_decay_minrate hI hδ

end UnforcedLeray.Short.PartI
