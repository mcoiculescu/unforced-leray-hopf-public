import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_1_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss

/-!
# `PartIII-b:C/grad/3/5/1/3` B3b: closed form of the lattice term `hpATm`

Source `shorter-proof-2026-11-02.tex` 4963-4980. With `M = A^y(s)` (meridional block),
`y = x_j = xj ν j x` and `a = 1 + ν s`, the term
`h^p_A` contribution `hpATm` equals
`a⁻² e^{-|y|²/(4a)} ((M J - J M) y + ((y·M y)/(2a)) J y)`, from `gp_fderiv_Vj` and linearity of
`merApply`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem merApply_smul_gauss (M : Mat3) (c : ℝ) (v : ℝ × ℝ) :
    merApply M (c • v) = c • merApply M v := by
  ext <;> simp [merApply] <;> ring

theorem hpATm_eq (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ) (p : Chart) :
    hpATm ν χ A j p =
      ((ageA ν p.1 ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j p.2)) / (4 * ageA ν p.1))) •
        (merApply (Ay ν χ A p.1) (Jrot (xj ν j p.2))
          - Jrot (merApply (Ay ν χ A p.1) (xj ν j p.2))
          + (((xj ν j p.2).1 * (merApply (Ay ν χ A p.1) (xj ν j p.2)).1
              + (xj ν j p.2).2 * (merApply (Ay ν χ A p.1) (xj ν j p.2)).2)
              / (2 * ageA ν p.1)) • Jrot (xj ν j p.2)) := by
  unfold hpATm
  rw [gp_fderiv_Vj]
  unfold Vj
  rw [merApply_smul_gauss]
  module

end UnforcedLeray.Short.PartIIIb.Concrete
