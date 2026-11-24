import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.Defs

/-!
# `hpSumDecomp` (task `PartIII-b:C/asrc/ra/9/1/2/9/1/1/1`)

Source `the November 2 reference manuscript` lines 4981-4985: `h^p_A` is the lattice
sum of the summands `toMer([V_j, A^y_mer x_j])`. `toMer` is a linear equivalence, so it commutes
with `tsum` (`ContinuousLinearEquiv.map_tsum`, no summability hypothesis needed).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `toMer` as a linear equivalence `ℝ × ℝ ≃ₗ[ℝ] Merid`. -/
def wsbToMerLin : (ℝ × ℝ) ≃ₗ[ℝ] Merid where
  toFun := toMer
  map_add' v w := by
    ext i
    fin_cases i <;> simp [toMer]
  map_smul' c v := by
    ext i
    fin_cases i <;> simp [toMer]
  invFun w := (w 0, w 1)
  left_inv v := by simp [toMer]
  right_inv w := by
    ext i
    fin_cases i <;> simp [toMer]

/-- `toMer` commutes with `tsum` (no summability hypothesis). -/
lemma wsb_toMer_tsum {ι : Type} (f : ι → ℝ × ℝ) :
    toMer (∑' i, f i) = ∑' i, toMer (f i) := by
  have h : wsbToMerLin.toContinuousLinearEquiv (∑' i, f i)
      = ∑' i, wsbToMerLin.toContinuousLinearEquiv (f i) :=
    ContinuousLinearEquiv.map_tsum _
  exact h

/-- **Lattice decomposition of `h^p_A`** (source 4981-4985). -/
theorem hpSumDecomp : HpSumDecomp := by
  intro ν χf A
  funext p
  exact wsb_toMer_tsum (fun j => merApply (Ay ν χf A p.1) (Vj ν p.1 j p.2)
    - fderiv ℝ (Vj ν p.1 j) p.2 (merApply (Ay ν χf A p.1) (xj ν j p.2)))

end UnforcedLeray.Short.PartIIIb.Concrete
