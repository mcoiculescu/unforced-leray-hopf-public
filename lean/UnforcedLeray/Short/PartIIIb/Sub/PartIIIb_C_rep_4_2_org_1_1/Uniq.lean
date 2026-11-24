import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_2_org_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Seq

/-!
# `PartIII-b:C/rep/4/2/org/1/1/1`: free weak uniqueness along the sequence

Source `the November 2 reference manuscript` 1571, 1580-1583 (free weak
uniqueness), 2031-2037 and 5926-5950 (large levels, through `inv_seq_large`).

The standing hypotheses of `SeqData.RepairStanding` give the level data needed by
`inv_seq_large`: `P = 2 ε_n c_n ≤ 1`, the period bound, and `μ_n(z) ∈ [σ₀/2, (σ₀ + 1/4)/2]`,
hence `0 < μ_n(z) + 1/4`. The uniform free weak uniqueness hypothesis `hU` is then applied at each
large `n` and each `z ∈ [-1, 1]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Free weak uniqueness along the sequence (the target, stated verbatim). -/
theorem freeWeakUniquenessThin (hU : ∀ (c γ ν ε μ : ℝ), 0 < c → 0 < ν → 0 < ε → 2 * ε * c ≤ 1 →
    0 < μ + 1 / 4 → FreeWeakUniqueness c γ ν ε μ) (dm dp : ℝ) (hdm : 0 < dm) :
    FreeWeakUniquenessThin dm dp := by
  intro D hst
  filter_upwards [inv_seq_large D hdm hst.omega_ne hst.sigma_pos hst.sigma_lt hst.actual]
    with n hn z hz
  obtain ⟨-, hP, -, hμ⟩ := hn
  have hμ' : 0 < D.mu n z + 1 / 4 := by
    linarith [(hμ z hz).1, hst.sigma_pos]
  exact hU _ _ _ _ _ (cOf_pos (retNu_pos D.Pl D.σ₀ n)) (retNu_pos D.Pl D.σ₀ n)
    (retEps_pos D.coeff_ne n) hP hμ'

end UnforcedLeray.Short.PartIIIb.Concrete
