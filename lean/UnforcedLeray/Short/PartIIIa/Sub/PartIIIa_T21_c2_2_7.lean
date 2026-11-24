import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2
import UnforcedLeray.Short.PartI.StatementsTrain

/-!
# Part III-a, task `PartIII-a:T21/c2/2/7` (`FmrVelGap`): decomposition

Source of record: `the November 2 reference manuscript`, line 2955 ("the image and
actual-base velocity errors give `sup δ_ν → 0` on `θ ≥ b`") and lines 291-303 (`sct:comparison`).

The comparison estimate `sct:comparison` holds only for the Gallay-Slijepcevic train in `BUC`
(`IsBUCTrain`, see `Short/PartI/TrainClass.lean`: uniqueness, and hence the estimate, is not derivable
from `IsTrain`), so `FmrVelGap` (`Sub/T21_c2_2.lean`) carries `IsBUCTrain tr` after the train binder.
`FmrVelGapBUC` is that one statement, proved here from two leaves and the Part I comparison.
The leaves are instantiated in `Clock/FreeMoving/Rate/FmrVelGap/Conditional.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Short.IIb
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- `FmrVelGap` for trains of the `BUC` class (the train of the source): since
`ORG:train-class-IIIa/sub` the statement of `FmrVelGap` itself (SP 270-288, 2955). -/
def FmrVelGapBUC : Prop := FmrVelGap

/-- **Leaf (image vortices)**: the periodization `V_c` of the central Gaussian vortex differs on
the cell `|q| ≤ c/2` from the central vortex by at most `(ε/2) a^{-3/2}`, for `c = ν⁻²`, `ν` small
and `θ(s) ≥ b` (so `a = 1+νs ≤ 1/(νb)`): the other vortices lie at distance `≥ c/2` and carry the
factor `e^{-c²/(16 a)} ≤ e^{-b ν⁻³/16}` (SP 2955; cf. PartII-b `cylTrainGap`). -/
def FmrVelImage : Prop :=
  ∀ b : ℝ, 0 < b → ∀ ε : ℝ, 0 < ε → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ s : ℝ, 0 ≤ s → b ≤ clockTheta ν s → ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      |UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) s x 0 - (UnforcedLeray.B0146.isoVelocity ν s x).1| +
          |UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) s x 1 - (UnforcedLeray.B0146.isoVelocity ν s x).2|
        ≤ ε / 2 * clockA ν s ^ (-(3 / 2) : ℝ)

/-- **Leaf (comparison to pointwise)**: `sct:comparison` (`TrainComparison`, `j = 0`, `ρ = 2`,
sup norm: `‖v - V_c‖_∞ ≤ C ν⁻¹ a^{-5/2} e^{-b₀ c²/a}`) gives, on `θ(s) ≥ b` (`a ≤ 1/(νb) ≤ c²`)
and `c² = ν⁻⁴`, `C ν⁻¹ a^{-1} e^{-b₀ b ν⁻³} ≤ ε/4`, hence the pointwise bound
`|v - V_c|_1 + |v - V_c|_2 ≤ (ε/2) a^{-3/2}`; `supNormD 0` is `⨆ ‖f x‖ₑ` (B0277.supNormD, with
`iteratedFDeriv_zero_apply`). -/
def FmrVelCompSup : Prop :=
  UnforcedLeray.Short.PartI.TrainComparison →
  ∀ b : ℝ, 0 < b → ∀ ε : ℝ, 0 < ε → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ s : ℝ, 0 ≤ s → b ≤ clockTheta ν s → ∀ x : B0579.Plane,
        |tr.v s x 0 - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) s x 0| +
            |tr.v s x 1 - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) s x 1|
          ≤ ε / 2 * clockA ν s ^ (-(3 / 2) : ℝ)

theorem fmrVelGapBUC_of (hI : FmrVelImage) (hC : FmrVelCompSup)
    (hTC : UnforcedLeray.Short.PartI.TrainComparison) : FmrVelGapBUC := by
  intro b hb ε hε
  obtain ⟨ν₁, hν₁, H1⟩ := hI b hb ε hε
  obtain ⟨ν₂, hν₂, H2⟩ := hC hTC b hb ε hε
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun ν hν tr hbuc s hs hθ x hx => ?_⟩
  have h1 := H1 ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩ s hs hθ x hx
  have h2 := H2 ν ⟨hν.1, hν.2.trans (min_le_right _ _)⟩ tr hbuc s hs hθ x
  have e0 : |tr.v s x 0 - (UnforcedLeray.B0146.isoVelocity ν s x).1| ≤
      |tr.v s x 0 - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) s x 0| +
      |UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) s x 0 - (UnforcedLeray.B0146.isoVelocity ν s x).1| := by
    simpa using abs_add_le (tr.v s x 0 - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) s x 0)
      (UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) s x 0 - (UnforcedLeray.B0146.isoVelocity ν s x).1)
  have e1 : |tr.v s x 1 - (UnforcedLeray.B0146.isoVelocity ν s x).2| ≤
      |tr.v s x 1 - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) s x 1| +
      |UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) s x 1 - (UnforcedLeray.B0146.isoVelocity ν s x).2| := by
    simpa using abs_add_le (tr.v s x 1 - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) s x 1)
      (UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) s x 1 - (UnforcedLeray.B0146.isoVelocity ν s x).2)
  have hp : 0 ≤ clockA ν s ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg (by
    unfold clockA; have := mul_nonneg hν.1.le hs; linarith) _
  nlinarith

end UnforcedLeray.Short.IIIa
