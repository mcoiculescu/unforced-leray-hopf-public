import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.Pieces

/-!
# `PartIII-b:C/rep/8/1/1/2/3` (`yTermsDiff`): decomposition

Source `the November 2 reference manuscript`
lines 4178-4186 (separated kernels smooth away from the source, outward primitive converges),
5400-5406 (radial separation), 5438-5448.  `YTermsDiffAt` splits into the actual terms
(`actYA`, `actYB`) and the mean terms (`mnYA`, `mnYB`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.Sub8_1_1_2_3

open UnforcedLeray.Blueprint.Planar (PlanarData)

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- Actual terms differentiable off the axis (source 4178-4186, 5400-5406): `YA = 𝒞_y W_μ` and the
commutator `YB`, for a.e. phase. -/
def ActYDiffAt : Prop :=
  LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy → ∀ T : LStr Pl K L, ∀ᵐ τ : ℝ, ∀ y : Space, 0 < ϱ y →
    DifferentiableAt ℝ (actYA Pl K L μ T τ) y ∧ DifferentiableAt ℝ (actYB Pl K L μ T τ) y

/-- Mean (zero-width Newton) terms differentiable off the axis (source 4776-4791, 5400-5406). -/
def MeanYDiffAt : Prop :=
  LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy → ∀ T : LStr Pl K L, ∀ᵐ τ : ℝ, ∀ y : Space, 0 < ϱ y →
    DifferentiableAt ℝ (mnYA Pl K L μ T τ) y ∧ DifferentiableAt ℝ (mnYB Pl K L μ T τ) y

/-- Sequence form of `ActYDiffAt`. -/
def ActYDiff (D : SeqData) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ActYDiffAt D.Pl D.K (D.level n) (D.mu n z)

/-- Sequence form of `MeanYDiffAt`. -/
def MeanYDiff (D : SeqData) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, MeanYDiffAt D.Pl D.K (D.level n) (D.mu n z)

theorem yTermsDiff_of (D : SeqData) (h1 : ActYDiff D) (h2 : MeanYDiff D) : D.YTermsDiff := by
  filter_upwards [h1, h2] with n hn1 hn2 z hz hL T
  filter_upwards [hn1 z hz hL T, hn2 z hz hL T] with τ a b y hy
  exact ⟨(a y hy).1, (a y hy).2, (b y hy).1, (b y hy).2⟩

end UnforcedLeray.Short.PartIIIb.Concrete.Sub8_1_1_2_3
