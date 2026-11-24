import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_12
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncMemY

/-!
# `TruncDriftBMem` (corrected copy of `DriftBMem`, coefficient of `dbmE` is `μ + 1/2`)

# `DriftBMem`: the weak drift `driftB` of `Φₙ` lies in `Y_2`

Source `the November 2 reference manuscript` lines 1351-1362, 1470-1480.
`driftB n ν μ D bΦ = χₙ bΦ - ½ (y·∇χₙ) Φ + crossB` splits into six pieces:

* `dbmA = χₙ bΦ` (bounded scalar times `Y_2`);
* `dbmB = -(½ radS χₙ) Φ` (bounded scalar times `Y_2`);
* `dbmC = -(∇χₙ × w)` and `dbmE = μ ∇χₙ × ψ` (Hardy: `|∇χₙ| ≤ 2C/|y|`, `w/|y|, ψ/|y| ∈ Y_2`);
* `dbmD = ν ∇χₙ × curlΦ` (bounded coefficient, `curlΦ = ∑ₖ eₖ × ∂ₖΦ ∈ Y_2`);
* `dbmF = -½ (∇(radS χₙ) - ∇χₙ) × ψ` (Hardy, coefficient `≤ 4C/|y|`).

Helpers (`isInYr_add2`, `isInYr_smul_of_bdd`, `isInYr_cross_hardy`, `isInYr_cross_bdd`,
`gradC_le_inv`, `crossC_norm_le`, ...) come from `AdjTruncOrg/TruncMemY.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Piece `χₙ bΦ` of `driftB`. -/
def dbmA (n : ℕ) (bΦ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun x => cutχ n x.2 • bΦ x

/-- Piece `-(½ radS χₙ) Φ` of `driftB`. -/
def dbmB (n : ℕ) (D : TruncData) : ℝ × Space → CVec3 :=
  fun x => (-(1 / 2 : ℝ) * radS (cutχ n) x.2) • D.Φ x

/-- Piece `-∇χₙ × w` of `driftB`. -/
def dbmC (n : ℕ) (D : TruncData) : ℝ × Space → CVec3 :=
  fun x => (-1 : ℝ) • crossC (gradC (cutχ n) x.2) (D.w x)

/-- Piece `ν ∇χₙ × curlΦ` of `driftB`. -/
def dbmD (n : ℕ) (ν : ℝ) (D : TruncData) : ℝ × Space → CVec3 :=
  fun x => ν • crossC (gradC (cutχ n) x.2) (curlD D x)

/-- Piece `μ ∇χₙ × ψ` of `driftB`. -/
def dbmE (n : ℕ) (μ : ℝ) (D : TruncData) : ℝ × Space → CVec3 :=
  fun x => (μ + 1 / 2 : ℝ) • crossC (gradC (cutχ n) x.2) (D.ψ x)

/-- Piece `-½ (∇(radS χₙ) - ∇χₙ) × ψ` of `driftB`. -/
def dbmF (n : ℕ) (D : TruncData) : ℝ × Space → CVec3 :=
  fun x => (-(1 / 2 : ℝ)) • crossC (gradC (radS (cutχ n)) x.2 - gradC (cutχ n) x.2) (D.ψ x)

/-- **Membership** `driftB ∈ Y_2` (source 1351-1362, 1470-1480): the six pieces above. -/
theorem driftBMemFix : DriftBMem := by
  intro hCut P ν μ hP hP1 hν hμ D hD n bΦ hbΦ
  unfold CutBounds at hCut
  obtain ⟨C, hC0, hb⟩ := hCut
  have hG1 : ∀ y : Space, ‖gradC (cutχ n) y‖ ≤ 2 * C * ‖y‖⁻¹ := fun y =>
    gradC_le_inv hC0 n _ y (fun h => ((hb n y).1 h).1) (hb n y).2.1
  have hG2 : ∀ y : Space, ‖gradC (radS (cutχ n)) y‖ ≤ 2 * C * ‖y‖⁻¹ := fun y =>
    gradC_le_inv hC0 n _ y (fun h => ((hb n y).1 h).2.1) (hb n y).2.2.1
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  have hGbdd : ∀ y : Space, ‖gradC (cutχ n) y‖ ≤ C := fun y =>
    (hb n y).2.1.trans (div_le_self hC0 hn1)
  have hR : ∀ y : Space, |radS (cutχ n) y| ≤ C := fun y => (hb n y).2.2.2.2.1
  have hc2 : ∀ y : Space, |(-(1 / 2 : ℝ) * radS (cutχ n) y)| ≤ C := fun y => by
    rw [abs_mul]
    have h1 := hR y
    have h2 := abs_nonneg (radS (cutχ n) y)
    norm_num
    linarith
  have hcb : ∀ y : Space, |cutχ n y| ≤ 1 := fun y => by
    have h0 : (0 : ℝ) ≤ unitBump (cutC n • y) := unitBump.nonneg
    have h1 : unitBump (cutC n • y) ≤ 1 := unitBump.le_one
    unfold cutχ
    exact abs_le.2 ⟨by linarith, h1⟩
  have hcutC : ContDiff ℝ ∞ (cutχ n) := contDiff_cutχ n
  have hradC : ContDiff ℝ ∞ (radS (cutχ n)) := contDiff_radS' hcutC
  have hcont_cut : Continuous (cutχ n) := hcutC.continuous
  have hcont_rad : Continuous (radS (cutχ n)) := hradC.continuous
  have hcont_gC : Continuous (gradC (cutχ n)) :=
    continuous_gradC' fun j => (contDiff_sd hcutC j).continuous
  have hcont_gR : Continuous (gradC (radS (cutχ n))) :=
    continuous_gradC' fun j => (contDiff_sd hradC j).continuous
  have hcont_G6 : Continuous (fun y : Space => gradC (radS (cutχ n)) y - gradC (cutχ n) y) :=
    hcont_gR.sub hcont_gC
  have hG6 : ∀ y : Space, ‖gradC (radS (cutχ n)) y - gradC (cutχ n) y‖ ≤ 4 * C * ‖y‖⁻¹ := fun y => by
    have h := norm_sub_le (gradC (radS (cutχ n)) y) (gradC (cutχ n) y)
    have h1 := hG2 y
    have h2 := hG1 y
    linarith
  -- the Y_2 inputs
  have hψH := hD.spΦ.hardy
  have hwH := hD.spg.hardy
  have hDΦ : ∀ k : Fin 3, UnforcedLeray.Short.IIb.IsInYr P 2 (D.DΦ k) := fun k => (hD.dΦ k).1
  have hcurl : UnforcedLeray.Short.IIb.IsInYr P 2 (curlD D) := by
    have hk : ∀ k : Fin 3, UnforcedLeray.Short.IIb.IsInYr P 2
        (fun x : ℝ × Space => crossC (EuclideanSpace.single k (1 : ℂ)) (D.DΦ k x)) := fun k =>
      isInYr_cross_bdd hP (A := fun _ : Space => EuclideanSpace.single k (1 : ℂ)) (M := 1)
        (by norm_num) (fun y => by simp) continuous_const (hDΦ k)
    have e : curlD D = fun x => (crossC (EuclideanSpace.single 0 (1 : ℂ)) (D.DΦ 0 x)
        + crossC (EuclideanSpace.single 1 (1 : ℂ)) (D.DΦ 1 x))
        + crossC (EuclideanSpace.single 2 (1 : ℂ)) (D.DΦ 2 x) := by
      funext x
      simp only [curlD, Fin.sum_univ_three]
    rw [e]
    exact isInYr_add2 hP (fun x => rfl)
      (isInYr_add2 hP (fun x => rfl) (hk 0) (hk 1)) (hk 2)
  -- the six pieces
  have hA : UnforcedLeray.Short.IIb.IsInYr P 2 (dbmA n bΦ) :=
    isInYr_smul_of_bdd hP (M := 1) (a := fun x : ℝ × Space => cutχ n x.2)
      ((hcont_cut.comp continuous_snd).aestronglyMeasurable) (fun x => hcb x.2)
      (Filter.Eventually.of_forall fun x => rfl) hbΦ
  have hB : UnforcedLeray.Short.IIb.IsInYr P 2 (dbmB n D) :=
    isInYr_smul_of_bdd hP (M := C) (a := fun x : ℝ × Space => (-(1 / 2 : ℝ) * radS (cutχ n) x.2))
      ((continuous_const.mul (hcont_rad.comp continuous_snd)).aestronglyMeasurable)
      (fun x => hc2 x.2) (Filter.Eventually.of_forall fun x => rfl) hD.dom.mem
  have hC : UnforcedLeray.Short.IIb.IsInYr P 2 (dbmC n D) :=
    isInYr_smul_of_bdd hP (M := 1) (a := fun _ : ℝ × Space => (-1 : ℝ)) aestronglyMeasurable_const
      (fun _ => by norm_num) (Filter.Eventually.of_forall fun x => rfl)
      (isInYr_cross_hardy hP (M := 2 * C) (by linarith) hG1 hcont_gC hD.spg.periodic hD.spg.meas
        hwH)
  have hD' : UnforcedLeray.Short.IIb.IsInYr P 2 (dbmD n ν D) :=
    isInYr_smul_of_bdd hP (M := |ν|) (a := fun _ : ℝ × Space => ν) aestronglyMeasurable_const
      (fun _ => le_rfl) (Filter.Eventually.of_forall fun x => rfl)
      (isInYr_cross_bdd hP (A := fun y : Space => gradC (cutχ n) y) (M := C) hC0 hGbdd hcont_gC
        hcurl)
  have hE : UnforcedLeray.Short.IIb.IsInYr P 2 (dbmE n μ D) :=
    isInYr_smul_of_bdd hP (M := |μ + 1 / 2|) (a := fun _ : ℝ × Space => μ + 1 / 2) aestronglyMeasurable_const
      (fun _ => le_rfl) (Filter.Eventually.of_forall fun x => rfl)
      (isInYr_cross_hardy hP (M := 2 * C) (by linarith) hG1 hcont_gC hD.spΦ.periodic
        hD.spΦ.meas hψH)
  have hF : UnforcedLeray.Short.IIb.IsInYr P 2 (dbmF n D) :=
    isInYr_smul_of_bdd hP (M := 1) (a := fun _ : ℝ × Space => (-(1 / 2 : ℝ)))
      aestronglyMeasurable_const (fun _ => by norm_num) (Filter.Eventually.of_forall fun x => rfl)
      (isInYr_cross_hardy hP (A := fun y : Space => gradC (radS (cutχ n)) y - gradC (cutχ n) y)
        (M := 4 * C) (by linarith) hG6 hcont_G6 hD.spΦ.periodic hD.spΦ.meas hψH)
  have hEq : driftB n ν μ D bΦ = fun x => dbmA n bΦ x + dbmB n D x + dbmC n D x
      + dbmD n ν D x + dbmE n μ D x + dbmF n D x := by
    funext x
    simp only [driftB, crossB, dbmA, dbmB, dbmC, dbmD, dbmE, dbmF]
    module
  rw [hEq]
  exact isInYr_add2 hP (fun x => rfl)
    (isInYr_add2 hP (fun x => rfl)
      (isInYr_add2 hP (fun x => rfl)
        (isInYr_add2 hP (fun x => rfl)
          (isInYr_add2 hP (fun x => rfl) hA hB) hC) hD') hE) hF

end UnforcedLeray.Short.PartIIIb.Concrete
