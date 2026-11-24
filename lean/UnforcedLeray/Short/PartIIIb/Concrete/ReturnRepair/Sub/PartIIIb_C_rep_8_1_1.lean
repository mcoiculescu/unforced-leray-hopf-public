import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1_org
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# `PartIII-b:C/rep/8/1/1` (`geomComparison`): decomposition into the `X` and `Y` parts

Source `the November 2 reference manuscript`
lines 5415-5432 (geometric comparison `‖D_yX₁-D_yX^mt‖_{L²_τ} + ‖D_yY₁-D_yY^mt‖_{L²_τ} ≤ P_ν ε⁴ s^{5/2} N`;
the `Y` part through the exact formula `Y = 𝒞_{χ_y}W_μ + [D_{μ+1},𝒞_{χ_y}](W_μ-W_{μ+1})`, 5427-5432,
`meanYFormula_of_shift` of `PartIII-b_C_rep_8_1_org`).

`cmpData = xcmp + ycmp` pointwise, so the `L²_τ` norm of the sum is at most the sum of the norms
(Minkowski); `GeomComparisonAt` follows from the two one-sided source facts `GeomXAt`, `GeomYAt`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- `|D_yX₁ - D_yX^mt|` (source 5419-5422). -/
def xcmp (T : LStr Pl K L) (τ : ℝ) (y : Space) : ℝ :=
  ‖fderiv ℝ (actX Pl K L μ T τ) y - fderiv ℝ (mnX Pl K L μ T τ) y‖

/-- `|D_yY₁ - D_yY^mt|` (source 5419-5422). -/
def ycmp (T : LStr Pl K L) (τ : ℝ) (y : Space) : ℝ :=
  ‖fderiv ℝ (actY Pl K L μ T τ) y - fderiv ℝ (mnY Pl K L μ T τ) y‖

theorem cmpData_eq (T : LStr Pl K L) :
    cmpData Pl K L μ T = fun τ y => xcmp Pl K L μ T τ y + ycmp Pl K L μ T τ y := rfl

/-- **`X` part of the geometric comparison** (source 5404-5427: the separated Newton kernels, one
phase primitive with its dilation-one boundary term, the finite transverse width and the
heat-to-Newton error by Taylor's formula with the strict radial gap along every Taylor segment,
5439-5443): `‖D_yX₁ - D_yX^mt‖_{L²_τ} ≤ P_ν ε⁴ s^{5/2} N` at young chart points, for swirl-free
thin stresses (`ThinAziZero`, source 5376, 5141-5142, 4772-4774). -/
def GeomXAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ThinAziZero Pl K L T → ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν), ∀ η : ℝ,
    AEMeasurable (fun q : ℝ => xcmp Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
        (NearInst.chartY L.ε⁻¹ (s, (q, η)))) (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2))) ∧
    cellL2 L.ε⁻¹ (cOf L.ν) (xcmp Pl K L μ T) s η ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) * oldN1 Pl K L T

/-- **`Y` part of the geometric comparison** (source 5427-5432: the exact formula
`Y^mt = 𝒞_{χ_y}W_μ + [D_{μ+1},𝒞_{χ_y}](W_μ-W_{μ+1})`, i.e. `meanYFormula_of_shift`, with the spatial
kernel comparison applied to the terms separately; no phase derivative is taken), for swirl-free
thin stresses (`ThinAziZero`). -/
def GeomYAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ThinAziZero Pl K L T → ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν), ∀ η : ℝ,
    AEMeasurable (fun q : ℝ => ycmp Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
        (NearInst.chartY L.ε⁻¹ (s, (q, η)))) (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2))) ∧
    cellL2 L.ε⁻¹ (cOf L.ν) (ycmp Pl K L μ T) s η ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) * oldN1 Pl K L T

/-- `cellL2` of a nonnegative function is the `L²` norm for the normalized phase measure. -/
theorem cellL2_eq_eLpNorm (R c : ℝ) (F : ℝ → Space → ℝ) (hF : ∀ τ y, 0 ≤ F τ y) (s η : ℝ) :
    cellL2 R c F s η = eLpNorm (fun q : ℝ => F (NearInst.chartTau R (s, (q, η)))
        (NearInst.chartY R (s, (q, η)))) 2
      (ENNReal.ofReal c⁻¹ • (volume.restrict (Ico (-c / 2) (c / 2)))) := by
  unfold cellL2
  rw [eLpNorm_two_eq, lintegral_smul_measure]
  congr 1
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  exact lintegral_congr fun q => by rw [Real.enorm_of_nonneg (hF _ _)]

theorem cellL2_add_le (R c : ℝ) (F G : ℝ → Space → ℝ) (hF : ∀ τ y, 0 ≤ F τ y)
    (hG : ∀ τ y, 0 ≤ G τ y) (s η : ℝ)
    (hFm : AEMeasurable (fun q : ℝ => F (NearInst.chartTau R (s, (q, η)))
        (NearInst.chartY R (s, (q, η)))) (volume.restrict (Ico (-c / 2) (c / 2))))
    (hGm : AEMeasurable (fun q : ℝ => G (NearInst.chartTau R (s, (q, η)))
        (NearInst.chartY R (s, (q, η)))) (volume.restrict (Ico (-c / 2) (c / 2)))) :
    cellL2 R c (fun τ y => F τ y + G τ y) s η ≤ cellL2 R c F s η + cellL2 R c G s η := by
  rw [cellL2_eq_eLpNorm R c _ (fun τ y => add_nonneg (hF τ y) (hG τ y)),
    cellL2_eq_eLpNorm R c F hF, cellL2_eq_eLpNorm R c G hG]
  exact eLpNorm_add_le (hFm.smul_measure _).aestronglyMeasurable
    (hGm.smul_measure _).aestronglyMeasurable (by norm_num)

theorem geomComparisonAt_of {C : ℝ} {k : ℕ} (hX : GeomXAt Pl K L μ C k)
    (hY : GeomYAt Pl K L μ C k) : GeomComparisonAt Pl K L μ (2 * C) k := by
  intro T hTz s hs η
  obtain ⟨hxm, hx⟩ := hX T hTz s hs η
  obtain ⟨hym, hy⟩ := hY T hTz s hs η
  have hxn : ∀ τ y, 0 ≤ xcmp Pl K L μ T τ y := fun _ _ => norm_nonneg _
  have hyn : ∀ τ y, 0 ≤ ycmp Pl K L μ T τ y := fun _ _ => norm_nonneg _
  have h := cellL2_add_le L.ε⁻¹ (cOf L.ν) _ _ hxn hyn s η hxm hym
  rw [cmpData_eq]
  refine h.trans ?_
  have e : ENNReal.ofReal (2 * C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) =
      2 * ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) := by
    rw [show 2 * C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) =
      2 * (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) by ring,
      ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [e, mul_assoc]
  calc _ ≤ _ := add_le_add hx hy
    _ = _ := by rw [← two_mul, mul_assoc]

theorem geomXAt_mono {C C' : ℝ} {k k' : ℕ} (hν1 : L.ν ≤ 1) (hC : C ≤ C')
    (hC' : 0 ≤ C') (hk : k ≤ k') (h : GeomXAt Pl K L μ C k) : GeomXAt Pl K L μ C' k' := by
  intro T hTz s hs η
  have hs0 : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.1.le _
  have he : 0 ≤ L.ε ^ 4 := by have := L.ε_pos; positivity
  exact ⟨(h T hTz s hs η).1,
    bound_mono L.ν_pos hν1 (mul_nonneg he hs0) hC hC' hk (h T hTz s hs η).2⟩

theorem geomYAt_mono {C C' : ℝ} {k k' : ℕ} (hν1 : L.ν ≤ 1) (hC : C ≤ C')
    (hC' : 0 ≤ C') (hk : k ≤ k') (h : GeomYAt Pl K L μ C k) : GeomYAt Pl K L μ C' k' := by
  intro T hTz s hs η
  have hs0 : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.1.le _
  have he : 0 ≤ L.ε ^ 4 := by have := L.ε_pos; positivity
  exact ⟨(h T hTz s hs η).1,
    bound_mono L.ν_pos hν1 (mul_nonneg he hs0) hC hC' hk (h T hTz s hs η).2⟩

end Regime

namespace SeqData

variable (D : SeqData)

/-- Sequence form of `GeomXAt`. -/
def GeomX : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    GeomXAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- Sequence form of `GeomYAt`. -/
def GeomY : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    GeomYAt D.Pl D.K (D.level n) (D.mu n z) C k

theorem geomComparison_of (hν : ∀ᶠ n : ℕ in atTop, (D.level n).ν ≤ 1) (hX : D.GeomX)
    (hY : D.GeomY) : D.GeomComparison := by
  obtain ⟨C₁, k₁, h₁⟩ := hX
  obtain ⟨C₂, k₂, h₂⟩ := hY
  refine ⟨2 * max |C₁| |C₂|, max k₁ k₂, ?_⟩
  filter_upwards [h₁, h₂, hν] with n hn₁ hn₂ hν1 z hz
  have hC0 : 0 ≤ max |C₁| |C₂| := le_trans (abs_nonneg _) (le_max_left _ _)
  have hX' := geomXAt_mono D.Pl D.K (D.level n) (D.mu n z) hν1 ((le_abs_self C₁).trans
    (le_max_left _ _)) hC0 (le_max_left k₁ k₂) (hn₁ z hz)
  have hY' := geomYAt_mono D.Pl D.K (D.level n) (D.mu n z) hν1 ((le_abs_self C₂).trans
    (le_max_right _ _)) hC0 (le_max_right k₁ k₂) (hn₂ z hz)
  exact geomComparisonAt_of D.Pl D.K (D.level n) (D.mu n z) hX' hY'

end SeqData

end UnforcedLeray.Short.PartIIIb.Concrete
