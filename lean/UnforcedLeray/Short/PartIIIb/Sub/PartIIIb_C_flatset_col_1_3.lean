import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1

/-!
# Periodicity of `f_A` in `q` (source 4594-4596)

`FlatForcePeriodic`: `fMer ... i (q + c, η) = fMer ... i (q, η)` for `c = cOf ν`.

Route: `xj ν j (q + c, η) = xj ν (j - 1) (q, η)`, so `Vj ν s j (y) = Vj ν s (j - 1) (y - (c, 0))`
as functions; hence the `j`-th term at `x + (c, 0)` is the `(j-1)`-th term at `x` (values and
`fderiv`, by `fderiv_comp_add_right`), and the `tsum` over `ℤ` is reindexed by `Equiv.subRight 1`.
No summability is needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The `j`-th term of `f_A` (before the sign), `(B_mer x_j)·∇V_j + B V_j` embedded. -/
def fpGT (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) (j : ℤ) : Vec3 :=
  emb (fderiv ℝ (Vj ν s j) x (merApply (Bmat ν μ χ A s) (xj ν j x)))
    + mv (Bmat ν μ χ A s) (emb (Vj ν s j x))

theorem fp_fA_eq (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    fA ν μ χ A s x = -(∑' j : ℤ, fpGT ν μ χ A s x j) := rfl

theorem fp_xj_sub_one (ν : ℝ) (j : ℤ) (y : ℝ × ℝ) :
    xj ν (j - 1) (y + ((-cOf ν, 0) : ℝ × ℝ)) = xj ν j y := by
  ext <;> simp [xj] <;> ring

theorem fp_Vj_shift (ν s : ℝ) (j : ℤ) :
    Vj ν s j = fun y => Vj ν s (j - 1) (y + ((-cOf ν, 0) : ℝ × ℝ)) := by
  funext y
  unfold Vj
  rw [fp_xj_sub_one]

theorem fp_xj_shift (ν : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    xj ν j (x.1 + cOf ν, x.2) = xj ν (j - 1) x := by
  ext <;> simp [xj] <;> ring

theorem fp_Vj_value_shift (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    Vj ν s j (x.1 + cOf ν, x.2) = Vj ν s (j - 1) x := by
  rw [congrFun (fp_Vj_shift ν s j) (x.1 + cOf ν, x.2)]
  congr 1
  ext <;> simp

theorem fp_fderiv_Vj_shift (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    fderiv ℝ (Vj ν s j) (x.1 + cOf ν, x.2) = fderiv ℝ (Vj ν s (j - 1)) x := by
  rw [fp_Vj_shift ν s j, fderiv_comp_add_right ((-cOf ν, 0) : ℝ × ℝ)]
  congr 1
  ext <;> simp

theorem fp_term_shift (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) (j : ℤ) :
    fpGT ν μ χ A s (x.1 + cOf ν, x.2) j = fpGT ν μ χ A s x (j - 1) := by
  unfold fpGT
  rw [fp_xj_shift, fp_fderiv_Vj_shift, fp_Vj_value_shift]

theorem fp_fA_shift (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    fA ν μ χ A s (x.1 + cOf ν, x.2) = fA ν μ χ A s x := by
  rw [fp_fA_eq, fp_fA_eq]
  congr 1
  simp only [fp_term_shift]
  exact Equiv.tsum_eq (Equiv.subRight (1 : ℤ)) (fun j => fpGT ν μ χ A s x j)

/-- **Periodicity of `f_A` in `q`** (source 4594: the lattice sum over `j ∈ ℤ` with
`x_j = (q - jc, η)`): `fMer ... i (q + c, η) = fMer ... i (q, η)` for `c = cOf ν`. -/
theorem flatForcePeriodic : FlatForcePeriodic := by
  intro ν μ χ A s _hν _hs i x
  unfold fMer
  rw [fp_fA_shift]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
