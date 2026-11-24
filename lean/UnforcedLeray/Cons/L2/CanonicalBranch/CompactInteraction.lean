import UnforcedLeray.Cons.L2.CanonicalBranch

/-!
# Compact interaction in the small-diffusion complement equation

The finite-rank correction `R_f = -DP - PD + PDP + κP` in the proof of
`paper/main.tex`, equation `eq:st18-t00079`. This leaf turns the concrete domain
lemmas for the two canonical modes into compactness of the correction operator.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.G3b

open MeasureTheory
open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Infra.Dunford

/-- The bounded finite-rank correction in `Q(D - κ)Q = D - κI + R_f`. -/
def complementCorrection (P PD DP : XG →L[ℂ] XG) (κ : ℂ) : XG →L[ℂ] XG :=
  -DP - PD + P.comp DP + κ • P

/-- If the three rank-one maps `P`, `PD`, and `DP` are compact, then the correction assembled
from them is compact as well. -/
theorem isCompactOperator_complementCorrection
    {P PD DP : XG →L[ℂ] XG} {κ : ℂ}
    (hP : IsCompactOperator P) (hPD : IsCompactOperator PD)
    (hDP : IsCompactOperator DP) :
    IsCompactOperator (complementCorrection P PD DP κ) := by
  have hPDP : IsCompactOperator (P.comp DP) := hDP.clm_comp P
  change IsCompactOperator (-DP - PD + P.comp DP + κ • P)
  exact (((hDP.neg).sub hPD).add hPDP).add (hP.smul κ)

/-- The compact part of the B0112 bounded perturbation at coefficient `β`. -/
def compactInteraction (A P Rf : XG →L[ℂ] XG) (β : ℝ) : XG →L[ℂ] XG :=
  A - P + (β : ℂ) • Rf

/-- The time-dependent interaction remains compact when `A`, the spectral projection, and the
finite-rank correction are compact. -/
theorem isCompactOperator_compactInteraction
    {A P Rf : XG →L[ℂ] XG} {β : ℝ}
    (hA : IsCompactOperator A) (hP : IsCompactOperator P)
    (hRf : IsCompactOperator Rf) :
    IsCompactOperator (compactInteraction A P Rf β) := by
  change IsCompactOperator (A - P + (β : ℂ) • Rf)
  exact (hA.sub hP).add (hRf.smul (β : ℂ))

/-- The perturbation `β R_f` is small in operator norm, with the exact rank-one correction norm. -/
theorem norm_compactInteraction_sub_base
    (A P Rf : XG →L[ℂ] XG) (β : ℝ) :
    ‖compactInteraction A P Rf β - (A - P)‖ = |β| * ‖Rf‖ := by
  rw [compactInteraction, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs]

/-- Uniform smallness of the compact-interaction perturbation under `|β| ≤ βmax`. -/
theorem norm_compactInteraction_sub_base_le
    (A P Rf : XG →L[ℂ] XG) {β βmax : ℝ} (hβ : |β| ≤ βmax) :
    ‖compactInteraction A P Rf β - (A - P)‖ ≤ βmax * ‖Rf‖ := by
  rw [norm_compactInteraction_sub_base]
  exact mul_le_mul_of_nonneg_right hβ (norm_nonneg Rf)

/-- Package a measurable scalar coefficient times the compact finite-rank correction as a
bounded interaction on a fixed interval. -/
def compactInteractionPert (A P Rf : XG →L[ℂ] XG) (β : ℝ → ℝ) (a b : ℝ)
    (hβ : AEStronglyMeasurable β (volume.restrict (Set.Icc a b)))
    (hβb : ∃ B : ℝ, ∀ t ∈ Set.Icc a b, |β t| ≤ B) :
    UnforcedLeray.Evolution.BoundedPert XG a b := by
  let B : ℝ := Classical.choose hβb
  have hB : ∀ t ∈ Set.Icc a b, |β t| ≤ B := Classical.choose_spec hβb
  refine ⟨fun t => compactInteraction A P Rf (β t), ?_, ?_⟩
  · intro x
    have hβc : AEStronglyMeasurable (fun t => (β t : ℂ))
        (volume.restrict (Set.Icc a b)) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable hβ
    have hsm : AEStronglyMeasurable (fun t => (β t : ℂ) • Rf x)
        (volume.restrict (Set.Icc a b)) :=
      hβc.smul aestronglyMeasurable_const
    change AEStronglyMeasurable
      (fun t => (A - P) x + (β t : ℂ) • Rf x) (volume.restrict (Set.Icc a b))
    exact aestronglyMeasurable_const.add hsm
  · refine ⟨‖A‖ + ‖P‖ + max B 0 * ‖Rf‖, fun t ht => ?_⟩
    have hcoef : ‖(β t : ℂ)‖ ≤ max B 0 := by
      simpa [Complex.norm_real, Real.norm_eq_abs] using
        (hB t ht).trans (le_max_left B 0)
    calc
      ‖compactInteraction A P Rf (β t)‖ ≤ ‖A - P‖ + ‖(β t : ℂ) • Rf‖ :=
        norm_add_le _ _
      _ ≤ (‖A‖ + ‖P‖) + max B 0 * ‖Rf‖ := by
        gcongr
        · exact norm_sub_le _ _
        · rw [norm_smul]
          exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg Rf)

/-- The frozen limit interaction `A - P` on a block. -/
def baseCompactInteractionPert (A P : XG →L[ℂ] XG) (a b : ℝ) :
    UnforcedLeray.Evolution.BoundedPert XG a b where
  A := fun _ => A - P
  meas _ := aestronglyMeasurable_const
  bdd := ⟨‖A‖ + ‖P‖, fun _ _ => norm_sub_le _ _⟩

/-- A constant interaction has a norm-totally-bounded range on any parameter/time block. -/
theorem totallyBounded_baseCompactInteraction_range {α : Type*}
    (A P : XG →L[ℂ] XG) :
    TotallyBounded (Set.range (fun _ : α => A - P)) := by
  exact (Set.finite_singleton (A - P)).totallyBounded.subset
    (Set.range_subset_iff.2 fun _ => Set.mem_singleton _)

/-- The interaction family converges uniformly in time to its frozen compact limit whenever the
scalar coefficient is uniformly small. -/
theorem norm_compactInteractionPert_sub_base_le
    (A P Rf : XG →L[ℂ] XG) (β : ℝ → ℝ) {δ : ℝ}
    (hβ : ∀ t, |β t| ≤ δ) (t : ℝ) :
    ‖compactInteraction A P Rf (β t) - (A - P)‖ ≤ δ * ‖Rf‖ := by
  exact norm_compactInteraction_sub_base_le A P Rf (hβ t)

/-- The canonical bounded rank-one maps produce a compact complement correction. -/
theorem exists_compact_canonical_complementCorrection {c : ℂ} {F : ℝ → ℂ}
    (hF : WholeLineData c F) (κ : ℂ) :
    ∃ P PD DP : XG →L[ℂ] XG,
      (∀ x, P x = inner ℂ (qdagMode hF) x • qMode hF) ∧
      (∀ f : B0094.D.domain,
        PD f = inner ℂ (qdagMode hF) (B0094.D f) • qMode hF) ∧
      (∀ x, DP x = inner ℂ (qdagMode hF) x •
        B0094.D ⟨qMode hF, qMode_mem_Ddomain hF⟩) ∧
      IsCompactOperator P ∧ IsCompactOperator PD ∧ IsCompactOperator DP ∧
      IsCompactOperator (complementCorrection P PD DP κ) := by
  obtain ⟨PD, DP, hPD, hDP, hPDc, hDPc, -, -⟩ := exists_compact_cross_maps hF
  let P := UnforcedLeray.Infra.Dunford.rankOneProj (innerSL ℂ (qdagMode hF))
    (qMode hF)
  have hP : IsCompactOperator P := by
    change IsCompactOperator ((innerSL ℂ (qdagMode hF)).smulRight (qMode hF))
    exact UnforcedLeray.Infra.AnalyticFredholm.isCompactOperator_smulRight _ _
  have hPapply : ∀ x, P x = inner ℂ (qdagMode hF) x • qMode hF := by
    intro x
    simp [P, UnforcedLeray.Infra.Dunford.rankOneProj_apply, innerSL_apply_apply]
  exact ⟨P, PD, DP, hPapply, hPD, hDP, hP, hPDc, hDPc,
    isCompactOperator_complementCorrection hP hPDc hDPc⟩

end UnforcedLeray.Cons.G3b
