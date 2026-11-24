import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_11
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncMemY

/-!
# `LaplMem`: `νΔΦₙ = lapA n ν D aΦ ∈ Y_2`

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
`lapA = χₙ aΦ + 2ν ∑ₖ ∂ₖχₙ ∂ₖΦ + νΔχₙ Φ + lapCross` with `lapCross` a sum of cross products whose
coefficients are either bounded (`∇χₙ`, `∇∂ₖχₙ`, `∇Δχₙ` times `ψ` and `∂ₖψ`) or of Hardy type
(`∇Δχₙ × ψ`). Each summand is in `Y_2` by the helpers of `AdjTruncOrg/TruncMemY.lean`.
Helpers are local (prefix `wlap_`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- Equality of functions transfers `Y_r` membership. -/
theorem wlap_congr_fun {P r : ℝ} {f g : ℝ × Space → CVec3} (h : ∀ x, f x = g x)
    (hg : UnforcedLeray.Short.IIb.IsInYr P r g) : UnforcedLeray.Short.IIb.IsInYr P r f := by
  have e : f = g := funext h
  rw [e]
  exact hg

/-- Sum of three `Y_2` fields. -/
theorem wlap_sum3 {P : ℝ} (hP : 0 < P) {f0 f1 f2 : ℝ × Space → CVec3}
    (h0 : UnforcedLeray.Short.IIb.IsInYr P 2 f0) (h1 : UnforcedLeray.Short.IIb.IsInYr P 2 f1)
    (h2 : UnforcedLeray.Short.IIb.IsInYr P 2 f2) :
    UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => f0 x + f1 x + f2 x) :=
  isInYr_add2 hP (F := fun x => f0 x + f1 x + f2 x) (fun _ => rfl)
    (isInYr_add2 hP (F := fun x => f0 x + f1 x) (fun _ => rfl) h0 h1) h2

/-- Finite sum over `Fin 3` of `Y_2` fields. -/
theorem wlap_sum3' {P : ℝ} (hP : 0 < P) {g : Fin 3 → ℝ × Space → CVec3}
    (hg : ∀ k, UnforcedLeray.Short.IIb.IsInYr P 2 (g k)) :
    UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => ∑ k : Fin 3, g k x) := by
  have e : (fun x => ∑ k : Fin 3, g k x) = fun x => g 0 x + g 1 x + g 2 x :=
    funext fun x => Fin.sum_univ_three _
  rw [e]
  exact wlap_sum3 hP (hg 0) (hg 1) (hg 2)

/-- Sum of six `Y_2` fields (grouped as in `lapA`). -/
theorem wlap_sum6 {P : ℝ} (hP : 0 < P) {f1 f2 f3 f4 f5 f6 : ℝ × Space → CVec3}
    (h1 : UnforcedLeray.Short.IIb.IsInYr P 2 f1) (h2 : UnforcedLeray.Short.IIb.IsInYr P 2 f2)
    (h3 : UnforcedLeray.Short.IIb.IsInYr P 2 f3) (h4 : UnforcedLeray.Short.IIb.IsInYr P 2 f4)
    (h5 : UnforcedLeray.Short.IIb.IsInYr P 2 f5) (h6 : UnforcedLeray.Short.IIb.IsInYr P 2 f6) :
    UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => ((f1 x + f2 x) + f3 x) + ((f4 x + f5 x) + f6 x)) :=
  isInYr_add2 hP (F := fun x => ((f1 x + f2 x) + f3 x) + ((f4 x + f5 x) + f6 x)) (fun _ => rfl)
    (isInYr_add2 hP (F := fun x => (f1 x + f2 x) + f3 x) (fun _ => rfl)
      (isInYr_add2 hP (F := fun x => f1 x + f2 x) (fun _ => rfl) h1 h2) h3)
    (isInYr_add2 hP (F := fun x => (f4 x + f5 x) + f6 x) (fun _ => rfl)
      (isInYr_add2 hP (F := fun x => f4 x + f5 x) (fun _ => rfl) h4 h5) h6)

/-- **LaplMem** (source 1334-1337, 1351-1362, 1470-1480): `lapA ∈ Y_2`. -/
theorem laplMem : LaplMem := by
  intro hCut P ν μ hP hP1 hν hμ D hD n aΦ haΦ
  unfold CutBounds at hCut
  obtain ⟨C, hC0, hb⟩ := hCut
  -- scalar bounds on the cutoff (source 1470-1480)
  have hG0 : ∀ y : Space, ‖gradC (cutχ n) y‖ ≤ C := fun y =>
    ((hb n y).2.1).trans (div_le_self hC0 (by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith))
  have hG3 : ∀ y : Space, ‖gradC (lapS (cutχ n)) y‖ ≤ 2 * C * ‖y‖⁻¹ := fun y =>
    gradC_le_inv hC0 n _ y (fun h => ((hb n y).1 h).2.2.1) (hb n y).2.2.2.1
  have hKa : ∀ (k : Fin 3) (y : Space), |sd k (cutχ n) y| ≤ C :=
    fun k y => ((hb n y).2.2.2.2.2.2 k).1
  have hKg : ∀ (k : Fin 3) (y : Space), ‖gradC (sd k (cutχ n)) y‖ ≤ C :=
    fun k y => ((hb n y).2.2.2.2.2.2 k).2
  have hL : ∀ y : Space, |lapS (cutχ n) y| ≤ C := fun y => (hb n y).2.2.2.2.2.1
  have hcb : ∀ y : Space, |cutχ n y| ≤ 1 := fun y => by
    have h0 : (0 : ℝ) ≤ unitBump (cutC n • y) := unitBump.nonneg
    have h1 : unitBump (cutC n • y) ≤ 1 := unitBump.le_one
    unfold cutχ
    exact abs_le.2 ⟨by linarith, h1⟩
  -- smoothness and continuity
  have hcutC : ContDiff ℝ ∞ (cutχ n) := UnforcedLeray.PhaseSpace.contDiff_cutχ n
  have hlapC : ContDiff ℝ ∞ (lapS (cutχ n)) :=
    UnforcedLeray.Short.PartIIIb.Concrete.contDiff_lapS' hcutC
  have hcont_cut : Continuous (cutχ n) := hcutC.continuous
  have hcont_lap : Continuous (lapS (cutχ n)) := hlapC.continuous
  have hcont_gC : Continuous (gradC (cutχ n)) :=
    UnforcedLeray.Short.PartIIIb.Concrete.continuous_gradC' fun j =>
      (UnforcedLeray.Short.PartIIIb.Concrete.contDiff_sd hcutC j).continuous
  have hcont_gL : Continuous (gradC (lapS (cutχ n))) :=
    UnforcedLeray.Short.PartIIIb.Concrete.continuous_gradC' fun j =>
      (UnforcedLeray.Short.PartIIIb.Concrete.contDiff_sd hlapC j).continuous
  have hcont_K : ∀ k : Fin 3, Continuous (sd k (cutχ n)) := fun k =>
    (UnforcedLeray.Short.PartIIIb.Concrete.contDiff_sd hcutC k).continuous
  have hcont_gK : ∀ k : Fin 3, Continuous (gradC (sd k (cutχ n))) := fun k =>
    UnforcedLeray.Short.PartIIIb.Concrete.continuous_gradC' fun j =>
      (UnforcedLeray.Short.PartIIIb.Concrete.contDiff_sd
        (UnforcedLeray.Short.PartIIIb.Concrete.contDiff_sd hcutC k) j).continuous
  -- the Y_2 inputs
  have hΦ : UnforcedLeray.Short.IIb.IsInYr P 2 D.Φ := hD.dom.mem
  have hψper := hD.spΦ.periodic
  have hψm := hD.spΦ.meas
  have hψH := hD.spΦ.hardy
  -- the six summands of lapA
  have hT1 : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x : ℝ × Space => cutχ n x.2 • aΦ x) :=
    isInYr_smul_of_bdd hP (a := fun x : ℝ × Space => cutχ n x.2) (M := 1)
      (hcont_cut.comp continuous_snd).aestronglyMeasurable (fun x => hcb x.2)
      (Filter.Eventually.of_forall fun _ => rfl) haΦ
  have hT2 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => (2 * ν) • ∑ k : Fin 3, sd k (cutχ n) x.2 • D.DΦ k x) :=
    isInYr_smul_of_bdd hP (a := fun _ : ℝ × Space => 2 * ν) (M := |2 * ν|)
      aestronglyMeasurable_const (fun _ => le_refl _) (Filter.Eventually.of_forall fun _ => rfl)
      (wlap_sum3' hP (g := fun k (x : ℝ × Space) => sd k (cutχ n) x.2 • D.DΦ k x) fun k =>
        isInYr_smul_of_bdd hP (a := fun x : ℝ × Space => sd k (cutχ n) x.2) (M := C)
          ((hcont_K k).comp continuous_snd).aestronglyMeasurable (fun x => hKa k x.2)
          (Filter.Eventually.of_forall fun _ => rfl) (hD.dΦ k).1)
  have hT3 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => (ν * lapS (cutχ n) x.2) • D.Φ x) :=
    isInYr_smul_of_bdd hP (a := fun x : ℝ × Space => ν * lapS (cutχ n) x.2) (M := |ν| * C)
      (continuous_const.mul (hcont_lap.comp continuous_snd)).aestronglyMeasurable
      (fun x => by
        show |ν * lapS (cutχ n) x.2| ≤ |ν| * C
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hL x.2) (abs_nonneg ν))
      (Filter.Eventually.of_forall fun _ => rfl) hΦ
  have hXh : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => crossC (gradC (lapS (cutχ n)) x.2) (D.ψ x)) :=
    isInYr_cross_hardy hP (M := 2 * C) (by linarith) hG3 hcont_gL hψper hψm hψH
  have hL1 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => ν • crossC (gradC (lapS (cutχ n)) x.2) (D.ψ x)) :=
    isInYr_smul_of_bdd hP (a := fun _ : ℝ × Space => ν) (M := |ν|)
      aestronglyMeasurable_const (fun _ => le_refl _) (Filter.Eventually.of_forall fun _ => rfl) hXh
  have hL2 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => (2 * ν) • ∑ k : Fin 3,
        crossC (gradC (sd k (cutχ n)) x.2) (D.Dψ k x)) :=
    isInYr_smul_of_bdd hP (a := fun _ : ℝ × Space => 2 * ν) (M := |2 * ν|)
      aestronglyMeasurable_const (fun _ => le_refl _) (Filter.Eventually.of_forall fun _ => rfl)
      (wlap_sum3' hP (g := fun k (x : ℝ × Space) => crossC (gradC (sd k (cutχ n)) x.2) (D.Dψ k x))
        fun k => isInYr_cross_bdd hP (M := C) hC0 (fun y => hKg k y) (hcont_gK k)
          (hD.spΦ.grad k).1)
  have hG_sum : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => ∑ k : Fin 3, crossC (EuclideanSpace.single k (1 : ℂ)) (D.DΦ k x)) :=
    wlap_sum3' hP (g := fun k (x : ℝ × Space) => crossC (EuclideanSpace.single k (1 : ℂ)) (D.DΦ k x))
      fun k => isInYr_cross_bdd hP (A := fun _ : Space => (EuclideanSpace.single k (1 : ℂ) : CVec3))
        (M := 1) zero_le_one (fun _ => by simp) continuous_const (hD.dΦ k).1
  have hL3 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => (-ν) • crossC (gradC (cutχ n) x.2)
        (∑ k : Fin 3, crossC (EuclideanSpace.single k (1 : ℂ)) (D.DΦ k x))) :=
    isInYr_smul_of_bdd hP (a := fun _ : ℝ × Space => -ν) (M := |-ν|)
      aestronglyMeasurable_const (fun _ => le_refl _) (Filter.Eventually.of_forall fun _ => rfl)
      (isInYr_cross_bdd hP (M := C) hC0 hG0 hcont_gC hG_sum)
  refine wlap_congr_fun (fun x => ?_) (wlap_sum6 hP hT1 hT2 hT3 hL1 hL2 hL3)
  simp only [lapA, lapCross]
  module

end UnforcedLeray.Short.PartIIIb.Concrete
