import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_org

/-!
# `PartIII-b:C/rep/8/3` decomposition: `GaussianReplace`

Source `the November 2 reference manuscript` 5484-5498 (young-train comparison,
Gaussian train separation `c = ν⁻²`) and 5272-5289 (exact pressure / repair coefficient,
exponent `1 + 3/11 + 57/22 = 85/22`).

* `GRMeas`: measurability of `ringAff` (composition of `ringAffCoef` with the actual train).
* `GRBound`: the `L²(srcMeasure)` bound `P_ν N (ε³ δ_base + ε^{85/22} e^{m₀/ν})`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace SeqData

variable (D : SeqData)

/-- Measurability of `ringAff` along the sequence (needed for the triangle inequality). -/
def GRMeas : Prop :=
  IsSourceCutoffC D.K.χf →
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ T : LStr D.Pl D.K (D.level n),
    AEStronglyMeasurable (ringAff D.Pl D.K (D.level n) (D.mu n z) T)
      (srcMeasure (cOf (D.level n).ν))

/-- **Gaussian replacement bound** (source 5484-5498, 5272-5289): replacing the actual train and
its pressure by the summed Gaussian profiles and lifted pressure costs
`P_ν N (ε³ δ_base + ε^{85/22} e^{m₀/ν})` in `L²(srcMeasure)`. -/
def GRBound : Prop :=
  ∃ (C : ℝ) (k : ℕ) (Csig bsig : ℝ), 0 < bsig ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ T : LStr D.Pl D.K (D.level n),
      eLpNorm (ringAff D.Pl D.K (D.level n) (D.mu n z) T -
          EAcoef (D.level n).ν (D.mu n z) D.K.χf
            (LjFun (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K) (gRate D.Pl)
              (D.level n).ν (D.level n).ε (D.mu n z) D.K.χo D.K.χy T))
          2 (srcMeasure (cOf (D.level n).ν)) ≤
        ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k *
          ((D.level n).ε ^ 3 * deltaBase Csig bsig (D.level n).ν +
            (D.level n).ε ^ (85 / 22 : ℝ) * Real.exp (D.K.m0 / (D.level n).ν))) *
          oldN1 D.Pl D.K (D.level n) T

end SeqData

/-- The target from the two source facts. -/
theorem gaussianReplace_of (D : SeqData) (h1 : D.GRMeas) (h2 : D.GRBound)
    (hchi : IsSourceCutoffC D.K.χf) :
    D.GaussianReplace := by
  obtain ⟨C, k, Csig, bsig, hb, h2⟩ := h2
  refine ⟨C, k, Csig, bsig, hb, ?_⟩
  filter_upwards [h1 hchi, h2] with n a b z hz T
  exact ⟨a z hz T, b z hz T⟩

end UnforcedLeray.Short.PartIIIb.Concrete
