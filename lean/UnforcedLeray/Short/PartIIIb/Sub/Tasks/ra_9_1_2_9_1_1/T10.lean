import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss

/-!


Source `the November 2 reference manuscript` lines 5063-5071, 5076-5079, 4963-4985.
The Gaussian part of the summand is `C⁴` (indeed smooth) on `s > 0` for `ν > 0` (the source
assumes `ν > 0`; for `ν < 0` the age `a = 1 + νs` vanishes at `s = -1/ν`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

private def t10_LE : (ℝ × ℝ) ≃ₗ[ℝ] Merid where
  toFun := toMer
  invFun := fun w => (w 0, w 1)
  map_add' := fun v w => by ext i; fin_cases i <;> simp [toMer]
  map_smul' := fun c v => by ext i; fin_cases i <;> simp [toMer]
  left_inv := fun v => by simp [toMer]
  right_inv := fun w => by ext i; fin_cases i <;> simp [toMer]

private lemma t10_toMer_cd : ContDiff ℝ 4 toMer := by
  have : (LinearEquiv.toContinuousLinearEquiv t10_LE : (ℝ × ℝ) → Merid) = toMer := rfl
  rw [← this]
  exact (LinearEquiv.toContinuousLinearEquiv t10_LE).contDiff

theorem hpGaussSmooth_pos (ν : ℝ) (hν : 0 < ν) (j : ℤ) (a b : Fin 2) :
    ContDiffOn ℝ 4 (hpGaussM ν j a b) UChart := by
  have hage : ∀ p ∈ UChart, ageA ν p.1 ≠ 0 := by
    intro p hp
    have : 0 < p.1 := hp.1
    unfold ageA; positivity
  have key : hpGaussM ν j a b = fun p => toMer (
      comp2 (Vj ν p.1 j p.2) b • ei a
      - comp2 (xj ν j p.2) b • (
        ((ageA ν p.1 ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1))) • Jrot (ei a)
        + ((ageA ν p.1 ^ 2)⁻¹ * (Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1)) *
            (-(2 * (xj ν j p.2).1 * (ei a).1 + 2 * (xj ν j p.2).2 * (ei a).2) / (4 * ageA ν p.1)))) •
          Jrot (xj ν j p.2))) := by
    funext p
    simp only [hpGaussM]
    rw [gp_fderiv_Vj]
  rw [key]
  refine t10_toMer_cd.comp_contDiffOn ?_
  have hA : ∀ p ∈ UChart, 1 + ν * p.1 ≠ 0 := hage
  fin_cases a <;> fin_cases b <;>
  · simp [comp2, Vj, xj, Jrot, sq2, ei, ageA, Fin.mk_one]
    refine ContDiffOn.prodMk ?_ ?_ <;>
    fun_prop (disch := (intro x hx; have h := hA x hx; simp [h]))

end UnforcedLeray.Short.PartIIIb.Concrete
