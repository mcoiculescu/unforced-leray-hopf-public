import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.PhaseLpTri2

/-!
# `PhaseTranslateContinuous`: decomposition

Source `the November 2 reference manuscript`
lines 1556-1583 (continuity of translation in `L²` of the cell).  Strategy: truncate `g` to the
time box `[-(P+1), P+1] × ℝ³` (finite `L²` by periodicity), approximate by a compactly supported
continuous `φ` in `L²(box)`, and use uniform continuity of `φ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The time box `[-R, R] × ℝ³`. -/
def tBox (R : ℝ) : Set (ℝ × Space) := Icc (-R) R ×ˢ (univ : Set Space)

/-- Local `L²` (source 1556-1583): a `P`-periodic `g ∈ Y_2` is square integrable on every time box
`[-R,R] × ℝ³` (cover by finitely many periodic translates of the cell `(0,P] × ℝ³`; a.e.
periodicity gives equal integrals on each translate). -/
def PhaseLocalL2 : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ g : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 g →
    ∀ R : ℝ, ∫⁻ x in tBox R, ‖g x‖ₑ ^ (2 : ℝ) < ⊤

/-- Continuity of translation in `L²(ℝ × ℝ³)` for compactly supported continuous `φ`
(uniform continuity and bounded support: the integrand is at most `sup‖φ‖²·2`
on a bounded set of measure `vol(supp φ + closedBall 0 1)`). -/
def CcTranslateL2 : Prop :=
  ∀ φ : ℝ × Space → CVec3, Continuous φ → HasCompactSupport φ →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ × Space, ‖z‖ < δ →
      ∫⁻ x, ‖φ (x - z) - φ x‖ₑ ^ (2 : ℝ) < ENNReal.ofReal ε

/-- Density of `C_c` in `L²` of the time box (apply `MemLp.exists_hasCompactSupport_eLpNorm_sub_le`
to `1_box · g` on `ℝ × ℝ³`; the integral over the box is bounded by the global one). -/
def CcDensityBox : Prop :=
  ∀ (R : ℝ) (g : ℝ × Space → CVec3), AEStronglyMeasurable g volume →
    ∫⁻ x in tBox R, ‖g x‖ₑ ^ (2 : ℝ) < ⊤ → ∀ η : ℝ, 0 < η →
      ∃ φ : ℝ × Space → CVec3, Continuous φ ∧ HasCompactSupport φ ∧
        ∫⁻ x in tBox R, ‖g x - φ x‖ₑ ^ (2 : ℝ) < ENNReal.ofReal η

/-- Shifting the cell into the time box (source 1556-1583): for `|z₁| ≤ 1`,
`∫_{(0,P]×ℝ³} ‖h(x - z)‖² ≤ ∫_{[-(P+1),P+1]×ℝ³} ‖h‖²` (change of variables `x ↦ x - z`
via `lintegral_sub_right_eq_self` on the restricted measure; `x₁ - z₁ ∈ [-1, P+1]`). -/
def PhaseCellShift : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (h : ℝ × Space → CVec3) (z : ℝ × Space), |z.1| ≤ 1 →
    ∫⁻ x, ‖h (x - z)‖ₑ ^ (2 : ℝ) ∂(muP P) ≤ ∫⁻ x in tBox (P + 1), ‖h x‖ₑ ^ (2 : ℝ)

theorem muP_le_volume (P : ℝ) : muP P ≤ (volume : Measure (ℝ × Space)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod_mono Measure.restrict_le_self le_rfl

theorem phaseLpNorm_lt_of_lint {P e : ℝ} (hP : 0 < P) (he : 0 < e)
    {h : ℝ × Space → CVec3} (hh : AEStronglyMeasurable h volume)
    (hI : ∫⁻ x, ‖h x‖ₑ ^ (2 : ℝ) ∂(muP P) < ENNReal.ofReal (P * e ^ 2)) :
    UnforcedLeray.Short.IIb.phaseLpNorm P 2 h < ENNReal.ofReal e := by
  rw [phaseLpNorm_eq P h hh]
  have h1 : ENNReal.ofReal P⁻¹ * ∫⁻ x, ‖h x‖ₑ ^ (2 : ℝ) ∂(muP P) <
      ENNReal.ofReal P⁻¹ * ENNReal.ofReal (P * e ^ 2) :=
    (ENNReal.mul_lt_mul_iff_right (by simp [hP]) ENNReal.ofReal_ne_top).2 hI
  have h2 : ENNReal.ofReal P⁻¹ * ENNReal.ofReal (P * e ^ 2) = ENNReal.ofReal e ^ (2 : ℝ) := by
    rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_rpow_of_nonneg he.le (by norm_num)]
    congr 1
    field_simp
    norm_num
  rw [h2] at h1
  have h3 := ENNReal.rpow_lt_rpow h1 (by norm_num : (0 : ℝ) < 1 / 2)
  rwa [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one] at h3

theorem aesm_sub_right {h : ℝ × Space → CVec3} (hh : AEStronglyMeasurable h volume)
    (z : ℝ × Space) : AEStronglyMeasurable (fun x => h (x - z)) volume :=
  haveI : (volume : Measure (ℝ × Space)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  hh.comp_quasiMeasurePreserving (measurePreserving_sub_right volume z).quasiMeasurePreserving

theorem phaseTranslateContinuous_of (h1 : PhaseLocalL2) (h2 : CcTranslateL2)
    (h3 : CcDensityBox) (h4 : PhaseCellShift) : PhaseTranslateContinuous := by
  intro P hP g hg ε hε
  have he : (0 : ℝ) < ε / 3 := by positivity
  set e := ε / 3 with he_def
  have hη : (0 : ℝ) < P * e ^ 2 := by positivity
  obtain ⟨φ, hφc, hφs, hφ⟩ :=
    h3 (P + 1) g hg.meas (h1 P hP g hg (P + 1)) _ hη
  obtain ⟨δ1, hδ1, hT⟩ := h2 φ hφc hφs _ hη
  refine ⟨min δ1 1, lt_min hδ1 one_pos, fun z hz => ?_⟩
  have hz1 : ‖z‖ < δ1 := lt_of_lt_of_le hz (min_le_left _ _)
  have hz2 : |z.1| ≤ 1 := by
    have : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
    rw [Real.norm_eq_abs] at this
    have := lt_of_lt_of_le hz (min_le_right _ _)
    linarith
  have hgm := hg.meas
  have hφm : AEStronglyMeasurable φ volume := hφc.aestronglyMeasurable
  have hgz := aesm_sub_right hgm z
  have hφz := aesm_sub_right hφm z
  -- three pieces
  have T1 : UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => g (x - z) - φ (x - z))
      < ENNReal.ofReal e := by
    refine phaseLpNorm_lt_of_lint hP he (hgz.sub hφz) ?_
    exact lt_of_le_of_lt (h4 P hP (fun x => g x - φ x) z hz2) hφ
  have T2 : UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => φ (x - z) - φ x)
      < ENNReal.ofReal e := by
    refine phaseLpNorm_lt_of_lint hP he (hφz.sub hφm) ?_
    exact lt_of_le_of_lt (lintegral_mono' (muP_le_volume P) le_rfl) (hT z hz1)
  have T3 : UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => φ x - g x)
      < ENNReal.ofReal e := by
    refine phaseLpNorm_lt_of_lint hP he (hφm.sub hgm) ?_
    have := h4 P hP (fun x => g x - φ x) 0 (by simp)
    simp only [sub_zero] at this
    calc ∫⁻ x, ‖φ x - g x‖ₑ ^ (2 : ℝ) ∂(muP P)
        = ∫⁻ x, ‖g x - φ x‖ₑ ^ (2 : ℝ) ∂(muP P) := by simp_rw [enorm_sub_rev (φ _)]
      _ < _ := lt_of_le_of_lt this hφ
  have hA := phaseLpNorm_tri_aux P (fun x => g (x - z)) (fun x => φ (x - z)) g hgz hφz hgm
  have hB := phaseLpNorm_tri_aux P (fun x => φ (x - z)) φ g hφz hφm hgm
  have hsum : ENNReal.ofReal e + (ENNReal.ofReal e + ENNReal.ofReal e) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add he.le he.le, ← ENNReal.ofReal_add he.le (by positivity)]
    congr 1
    rw [he_def]; ring
  calc _ ≤ _ := hA
    _ ≤ UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => g (x - z) - φ (x - z)) +
        (UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => φ (x - z) - φ x) +
          UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => φ x - g x)) := by gcongr
    _ < ENNReal.ofReal e + (ENNReal.ofReal e + ENNReal.ofReal e) := by
        gcongr
    _ = _ := hsum

end UnforcedLeray.Short.PartIIIb.Concrete
