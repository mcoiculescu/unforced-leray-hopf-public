import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.DuhamelSplit
import UnforcedLeray.Units.B0579

/-!
# Leaf (ii-b): `DualUniq` (`PartIII-a:T21/c3/3/1/1/2/2/1`)

Source `the November 2 reference manuscript` (SP) lines 2937-2958: an `X_{m,d}`
function is determined a.e. by its pairings with `X_{-m,d}`.  Take `Γ = conj(A - B) ⟨x⟩^{2m}`;
then `Γ ∈ X_{-m,d}` and the pairing of `A - B` with `Γ` is the weighted `L²` norm of `A - B`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

namespace ComplFreeRateSub

theorem dualUniq : DualUniq := by
  intro d m A B hA hB hAB
  -- the weight `⟨x⟩^{2m}` as a real function, positive on the plane
  have hJ : ∀ x : ℝ × ℝ, 0 < B0579.jb x ^ m := fun x => Real.rpow_pos_of_pos (B0579.jb_pos x) m
  have hsm : ∀ (k : ℝ) (x : ℝ × ℝ) (r : ℝ), B0579.density k x • r = B0579.jb x ^ k * r := by
    intro k x r
    rw [NNReal.smul_def, smul_eq_mul, B0579.coe_density]
  have hinv : ∀ x : ℝ × ℝ, B0579.jb x ^ (-m) * B0579.jb x ^ m = 1 := by
    intro x
    rw [B0579.jb_rpow_mul, neg_add_cancel, Real.rpow_zero]
  -- weighted integrability of `‖E‖²` on the cell
  have hw : ∀ E : ℝ × ℝ → ℂ, MemLp E 2 (B0579.cellMeasure d m) →
      IntegrableOn (fun x => B0579.density m x • ‖E x‖ ^ 2) (B0579.cell d) := by
    intro E hE
    have h := (memLp_two_iff_integrable_sq_norm hE.1).mp hE
    exact (B0579.integrable_cellMeasure_iff d m).mp h
  have hD : MemLp (fun x => A x - B x) 2 (B0579.cellMeasure d m) := hA.sub hB
  have hwD := hw (fun x => A x - B x) hD
  -- the test function `Γ = conj(A - B) ⟨x⟩^{2m}`
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℝ × ℝ → ℂ,
      ∀ x, Γ x = (starRingEnd ℂ) (A x - B x) * ((B0579.jb x ^ m : ℝ) : ℂ) :=
    ⟨fun x => (starRingEnd ℂ) (A x - B x) * ((B0579.jb x ^ m : ℝ) : ℂ), fun x => rfl⟩
  have hΓnorm : ∀ x, ‖Γ x‖ = ‖A x - B x‖ * B0579.jb x ^ m := by
    intro x
    rw [hΓ x, norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (hJ x).le, mul_comm]
  -- measurability on the cell
  have hDν : AEStronglyMeasurable (fun x => A x - B x) (volume.restrict (B0579.cell d)) :=
    (hA.1.sub hB.1).mono_ac (B0579.ac_cellMeasure d m)
  have hΓν : AEStronglyMeasurable Γ (volume.restrict (B0579.cell d)) := by
    have hfun : Γ = fun x => (starRingEnd ℂ) (A x - B x) * ((B0579.jb x ^ m : ℝ) : ℂ) :=
      funext hΓ
    rw [hfun]
    exact ((Complex.continuous_conj.comp_aestronglyMeasurable hDν).mul
      (Complex.continuous_ofReal.comp (B0579.continuous_jb_rpow m)).aestronglyMeasurable)
  -- `Γ ∈ X_{-m,d}`
  have hΓsq : Integrable (fun x => ‖Γ x‖ ^ 2) (B0579.cellMeasure d (-m)) := by
    refine (B0579.integrable_cellMeasure_iff d (-m)).mpr ?_
    refine hwD.congr (Eventually.of_forall fun x => ?_)
    show B0579.density m x • ‖A x - B x‖ ^ 2 = B0579.density (-m) x • ‖Γ x‖ ^ 2
    rw [hsm, hsm, hΓnorm x]
    linear_combination (-(B0579.jb x ^ m * ‖A x - B x‖ ^ 2)) * hinv x
  have hΓL2 : MemLp Γ 2 (B0579.cellMeasure d (-m)) :=
    (memLp_two_iff_integrable_sq_norm (hΓν.mono_ac (B0579.cellMeasure_ac d (-m)))).mpr hΓsq
  -- integrability of `E * Γ` for `E ∈ X_{m,d}`
  have hint : ∀ E : ℝ × ℝ → ℂ, MemLp E 2 (B0579.cellMeasure d m) →
      Integrable (fun x => E x * Γ x) (volume.restrict (B0579.cell d)) := by
    intro E hE
    have hwE := hw E hE
    have hG := (hwE.add hwD).div_const 2
    refine Integrable.mono' hG ?_ (Eventually.of_forall fun x => ?_)
    · exact (hE.1.mono_ac (B0579.ac_cellMeasure d m)).mul hΓν
    · show ‖E x * Γ x‖ ≤ (B0579.density m x • ‖E x‖ ^ 2 +
        B0579.density m x • ‖A x - B x‖ ^ 2) / 2
      rw [norm_mul, hΓnorm x, hsm, hsm]
      nlinarith [mul_nonneg (hJ x).le (sq_nonneg (‖E x‖ - ‖A x - B x‖))]
  -- the pairing identity
  have hzero : ∫ x in B0579.cell d, (A x * Γ x - B x * Γ x) = 0 := by
    rw [integral_sub (hint A hA) (hint B hB)]
    exact sub_eq_zero.mpr (hAB Γ hΓL2)
  have hpt : ∀ x, A x * Γ x - B x * Γ x =
      ((‖A x - B x‖ ^ 2 * B0579.jb x ^ m : ℝ) : ℂ) := by
    intro x
    have h1 : (starRingEnd ℂ) (A x - B x) * (A x - B x) = ((‖A x - B x‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hΓ x, Complex.ofReal_mul]
    linear_combination ((B0579.jb x ^ m : ℝ) : ℂ) * h1
  have hreal : ∫ x in B0579.cell d, ‖A x - B x‖ ^ 2 * B0579.jb x ^ m = 0 := by
    have h2 : ∫ x in B0579.cell d, (((‖A x - B x‖ ^ 2 * B0579.jb x ^ m : ℝ)) : ℂ) = 0 := by
      rw [← hzero]
      exact integral_congr_ae (Eventually.of_forall fun x => (hpt x).symm)
    rw [integral_complex_ofReal] at h2
    exact Complex.ofReal_eq_zero.mp h2
  have hfint : Integrable (fun x => ‖A x - B x‖ ^ 2 * B0579.jb x ^ m)
      (volume.restrict (B0579.cell d)) := by
    refine hwD.congr (Eventually.of_forall fun x => ?_)
    show B0579.density m x • ‖A x - B x‖ ^ 2 = ‖A x - B x‖ ^ 2 * B0579.jb x ^ m
    rw [hsm, mul_comm]
  have hnonneg : ∀ x, 0 ≤ ‖A x - B x‖ ^ 2 * B0579.jb x ^ m := fun x =>
    mul_nonneg (sq_nonneg _) (hJ x).le
  have hae0 : (fun x => ‖A x - B x‖ ^ 2 * B0579.jb x ^ m) =ᵐ[volume.restrict (B0579.cell d)] 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg hfint).mp hreal
  have hae : A =ᵐ[volume.restrict (B0579.cell d)] B := by
    filter_upwards [hae0] with x hx
    have hx' : ‖A x - B x‖ ^ 2 * B0579.jb x ^ m = 0 := hx
    have hD0 : ‖A x - B x‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp hx' with h | h
      · exact h
      · exact absurd h (hJ x).ne'
    exact sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hD0))
  exact (B0579.cellMeasure_ac d m).ae_le hae

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
