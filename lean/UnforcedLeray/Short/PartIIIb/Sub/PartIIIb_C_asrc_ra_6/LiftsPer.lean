import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_6
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RAPin
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.HhatAPeriodic

/-!
# `PartIII-b:C/asrc/ra/6/6` : `RALiftsPer` from the lattice periodicity

Source of record: `the November 2 reference manuscript` 2666-2668, 4995-4997.

The lifts `hLift`, `feLift` are `Nv ε⁻¹ (perExt c b)`, periodic under the phase shift
`2εc` by `nvPerExt_periodic`; the phase shift `2c/R = 2εc` is `div_inv_eq_mul`.
`sΨ_A = s · PsiA` is periodic: `chart_add_period` shifts the chart `q`-coordinate by `c`,
and `PsiA` is `c`-periodic in `q` by reindexing the `ℤ`-sum (`hper_tsum_shift`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem hper_pj_shift_ra6 (ν s : ℝ) (n j : ℤ) (y : ℝ × ℝ) :
    pj ν s j (y.1 + (n : ℝ) * cOf ν, y.2) = pj ν s (j - n) y := by
  unfold pj
  rw [hper_xj_shift]

theorem hper_mgrad_pj_shift_ra6 (ν s : ℝ) (n j : ℤ) (y : ℝ × ℝ) :
    mgrad (pj ν s j) (y.1 + (n : ℝ) * cOf ν, y.2) = mgrad (pj ν s (j - n)) y := by
  unfold mgrad
  rw [hper_fderiv_shift (pj ν s j) (pj ν s (j - n)) ((n : ℝ) * cOf ν)
    (hper_pj_shift_ra6 ν s n j) y]

/-- `PsiA` is `c`-periodic in `q` (reindex `j ↦ j - n` in the `ℤ`-sum). -/
theorem hper_PsiA_shift_ra6 (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (n : ℤ)
    (x : ℝ × ℝ) : PsiA ν χ A s (x.1 + (n : ℝ) * cOf ν, x.2) = PsiA ν χ A s x := by
  unfold PsiA
  refine hper_tsum_shift ((n : ℝ) * cOf ν) n
    (fun j y => (merApply (Ay ν χ A s) (xj ν j y)).1 * (mgrad (pj ν s j) y).1 +
      (merApply (Ay ν χ A s) (xj ν j y)).2 * (mgrad (pj ν s j) y).2) ?_ x
  intro j y
  rw [hper_xj_shift ν n j y, hper_mgrad_pj_shift_ra6 ν s n j y]

theorem raLiftsPer (as : ℝ) (χf : ℝ → ℝ) : RALiftsPer as χf := by
  intro hχ ν μ ε hν hε A hAe
  have hc : 0 < cOf ν := by unfold cOf; positivity
  have hper : 2 * cOf ν / ε⁻¹ = 2 * ε * cOf ν := by
    rw [div_inv_eq_mul]; ring
  rw [hper]
  refine ⟨?_, ?_, ?_⟩
  · intro τ y
    exact nvPerExt_periodic hε hc _ τ y
  · intro τ y
    exact nvPerExt_periodic hε hc _ τ y
  · intro τ y
    have hchart := chart_add_period (c := cOf ν) hε τ y
    have hPs := hper_PsiA_shift_ra6 ν χf A (chart ε⁻¹ τ y).1 1 (chart ε⁻¹ τ y).2
    simp only [Int.cast_one, one_mul] at hPs
    show (chart ε⁻¹ (τ + 2 * ε * cOf ν) y).1 *
          PsiA ν χf A (chart ε⁻¹ (τ + 2 * ε * cOf ν) y).1
            (chart ε⁻¹ (τ + 2 * ε * cOf ν) y).2 =
        (chart ε⁻¹ τ y).1 * PsiA ν χf A (chart ε⁻¹ τ y).1 (chart ε⁻¹ τ y).2
    rw [hchart]
    dsimp only
    rw [hPs]

end UnforcedLeray.Short.PartIIIb.Concrete
