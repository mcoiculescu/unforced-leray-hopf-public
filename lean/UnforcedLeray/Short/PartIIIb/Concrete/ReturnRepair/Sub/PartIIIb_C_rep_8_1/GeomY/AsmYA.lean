import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.AsmYA.Gen
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.AsmYA.CutEq
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.AsmYA.AziDef
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.N0

/-!
# `PartIII-b:C/rep/8/1/1/2/4/org`: the kernel comparison of `Y_A = 𝒞_y W_μ` from its leaves

Source `the November 2 reference manuscript`
lines 5415-5432 ("For `Y` use the exact formula `Y = 𝒞_{χ_y}W_μ + [D_{μ+1},𝒞_{χ_y}](W_μ-W_{μ+1})`.
Apply the spatial kernel comparison to these terms separately"; one phase primitive in the
dilation variable with its dilation-one boundary term, the finite transverse width and the
heat-to-Newton error by Taylor's formula with the strict radial gap along every Taylor segment,
the age power `s³ ≤ P_ν s^{5/2}` on the young interval), 5400-5413 (separated kernels, gradient
Newton kernel of degree `-5`, ratio of radii `≤ 1/√1.2`, the outward stream primitive of the same
degree), 4178-4186 (outward primitive, stream cutoff), 4168-4171 (`W_μ` of the old source),
4783-4791 (`W^mt_μ`).

## The field triple of `Y_A`

* `zWAct = W_μ` of the old thin source (`thinWardW`; phase dependent, finite width), so that
  `actYA = 𝒞_y zWAct` definitionally;
* `zWMid`: the same response of the phase-mean chart tensor `meanQ c (thinG T)` (finite width, no
  phase);
* `zWMt = W^mt_μ` (zero width, phase mean, Newton) as a phase-free field on `Space`; off the axis
  `mnYA = 𝒞_y zWMt` (`mnYA_eq_wardStreamCut`, from the ray symmetry `YoungWRayAzi` of `W^mt_μ`).

## Leaves (each a source fact for the triple, at every level under `LHyp`)

* `PhasePrimitiveYAAt` (5415-5421): `‖D zWAct - D zWMid‖_{L²_τ} ≤ P_ν ε⁴ s^{5/2} N`;
* `TaylorWidthYAAt` (5422-5427): `|D zWMid - D zWMt| ≤ P_ν ε⁴ s^{5/2} N` at every phase;
* `ZRegularYAAt` (4178-4186, 5400-5413): `zWAct, zWMt` are `C¹` on the clear region, decay along
  outward rays and have convergent, differentiable outward primitives (`PrimData`);
* `MeasYAAt`: joint measurability of the phase part on the clear region and measurability of
  `dYA` along the cell.

`geomYAAt_of_leaves` proves `GeomYAAt` from the leaves, `YoungWRayAzi`, finiteness of the old
source and the two calculus statements `StreamCutAlgWith`, `RayFTCStmt` (`GeomX/Asm/Defs.lean`)
by the abstract stream-cut assembly `GeomYAGen.cellL2_le_of_leaves`; `geomYA_of_leaves` is the
sequence form.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)
open GeomXAsm

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- `W_μ` of the old thin source `χ_oT₁` (source 4168-4171, `sep:resolvent` 3611-3621): the
actual field of `Y_A`, `actYA = 𝒞_y zWAct`. -/
def zWAct (T : LStr Pl K L) : ℝ → Space → Space :=
  thinWardW Pl K L μ T

/-- `W_μ` with the phase-mean chart tensor `meanQ c (thinG T)` in place of `thinG T` (finite
transverse width retained, phase averaged away; source 5415-5427). -/
def zWMid (T : LStr Pl K L) : ℝ → Space → Space := fun τ y =>
  WithLp.toLp 2 fun i =>
    (IIIa.sepW L.ν (μ : ℂ) (oldPhys L.ε⁻¹ (cOf L.ν) (meanQ (cOf L.ν) (thinG Pl K L T))) y τ i).re

/-- `W^mt_μ` (source 4783-4791), phase free, as a field on `Space`. -/
def zWMt (T : LStr Pl K L) : ℝ → Space → Space :=
  mtField (youngW (cOf L.ν) L.ν L.ε μ K.χo (thinRep T))

/-- `|D_y zWAct - D_y zWMid|` (the phase part of `Y_A`). -/
def dPhaseW (T : LStr Pl K L) (τ : ℝ) (y : Space) : ℝ :=
  ‖fderiv ℝ (zWAct Pl K L μ T τ) y - fderiv ℝ (zWMid Pl K L μ T τ) y‖

/-- `|D_y zWMid - D_y zWMt|` (the width and heat-to-Newton part of `Y_A`). -/
def dWidthW (T : LStr Pl K L) (τ : ℝ) (y : Space) : ℝ :=
  ‖fderiv ℝ (zWMid Pl K L μ T τ) y - fderiv ℝ (zWMt Pl K L μ T τ) y‖

/-- **Phase primitive for `W_μ`** (source 5415-5421: "One phase primitive in the dilation variable,
with its dilation-one boundary term retained"; the oscillating part of the chart tensor has zero
phase mean; 5400-5413 for the separated kernels): at every young chart point
`‖D_y zWAct - D_y zWMid‖_{L²_τ} ≤ P_ν ε⁴ s^{5/2} N`. -/
def PhasePrimitiveYAAt (C : ℝ) (k : ℕ) : Prop :=
  LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy → ∀ T : LStr Pl K L, ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν), ∀ η : ℝ,
    AEMeasurable (fun q : ℝ => dPhaseW Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
        (NearInst.chartY L.ε⁻¹ (s, (q, η)))) (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2))) ∧
    cellL2 L.ε⁻¹ (cOf L.ν) (dPhaseW Pl K L μ T) s η ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) * oldN1 Pl K L T

/-- **Finite width and heat-to-Newton for `W_μ`** (source 5422-5427: Taylor's formula costs the
first transverse moment, the strict radial gap holds along every Taylor segment, the age power
`s³` is bounded by `P_ν s^{5/2}` on the young interval): both fields are phase free, so the bound
is pointwise in the phase.  It is stated for swirl-free thin stresses (`ThinAziZero`, source 5376,
5141-5142, 4772-4774): `zWMid` keeps a hoop entry `T(1,1)` (`oldPhys`, `NearInst.nsSym`) while
`zWMt` drops it (`phaseMean`), so for a hoop stress the difference is of order `ε³ s^{5/2} N`. -/
def TaylorWidthYAAt (C : ℝ) (k : ℕ) : Prop :=
  LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy → ∀ T : LStr Pl K L, ThinAziZero Pl K L T →
    ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν), ∀ η q : ℝ,
    ENNReal.ofReal (dWidthW Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
        (NearInst.chartY L.ε⁻¹ (s, (q, η)))) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) * oldN1 Pl K L T

/-- **Regularity, decay and outward primitive off the old source** (source 4178-4186: "The
separated-kernel estimates prove convergence of this primitive and its differentiated versions";
5400-5413: the receivers of the clear region `(εr)² > ν/1.1` are radially separated from the old
source `(εr)² ≤ ν/1.2`): for every `T` and phase, the actual field `zWAct = W_μ` and the mean field
`zWMt = W^mt_μ` are `C¹` on `clearSet`, tend to zero along every outward ray from `clearSet`, and
have `PrimData` at every point `(r, 0, z)` of the clear region. -/
def ZRegularYAAt : Prop :=
  LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy → ∀ T : LStr Pl K L, ∀ τ : ℝ,
    ∀ Z ∈ ({zWAct Pl K L μ T, zWMt Pl K L μ T} : Set (ℝ → Space → Space)),
      ContDiffOn ℝ 1 (Z τ) (clearSet L.ε L.ν) ∧
      (∀ y ∈ clearSet L.ε L.ν, Tendsto (fun t : ℝ => Z τ (outRay y t)) atTop (𝓝 0)) ∧
      ∀ r z : ℝ, 0 < r → L.ν / (11 / 10) < (L.ε * r) ^ 2 → PrimData Z τ r z

/-- **Measurability** (from the joint measurability of the separated-kernel responses of
measurable chart tensors and the differentiability on the open clear region): `(τ, y) ↦
1_clear(y) dPhaseW(τ, y)` is measurable, and `dYA` is a.e.-strongly measurable along the cell at
every young chart point. -/
def MeasYAAt : Prop :=
  LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy → ∀ T : LStr Pl K L,
    (Measurable fun p : ℝ × Space =>
      (clearSet L.ε L.ν).indicator (fun y => dPhaseW Pl K L μ T p.1 y) p.2) ∧
    ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν), ∀ η : ℝ,
      AEStronglyMeasurable (fun q : ℝ => dYA Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
        (NearInst.chartY L.ε⁻¹ (s, (q, η)))) (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2)))

/-- **`mnYA = 𝒞_y W^mt_μ` off the axis** (source 4178-4186, 4783-4791; the receiver cutoff reads
the outward primitive along the ray through `y`, the Ward cutoff on the half plane `φ = 0`, and
the vertical component of `W^mt_μ` is the same on both, `YoungWRayAzi`). -/
theorem mnYA_eq_wardStreamCut (hazi : YoungWRayAzi) (hL : LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy)
    (T : LStr Pl K L) (hfin : OldThinFinite (cOf L.ν) L.ν (thinRep T)) (τ : ℝ) (y : Space)
    (hy : 0 < ϱ y) :
    mnYA Pl K L μ T τ y = wardStreamCut L.ν L.ε⁻¹ K.χy (zWMt Pl K L μ T) τ y := by
  refine GeomYACut.mtField_streamCut_eq hL.nu_pos hL.eps_pos hL.chiY _ ?_ τ y hy
  intro w hw ρ hρ
  refine hazi _ _ _ _ _ _ hL.c_pos hL.nu_pos hL.mu_pos hL.chiO hfin w hw ρ ?_
  have := hL.nu_pos
  linarith

theorem zWAct_add_period (T : LStr Pl K L) (τ : ℝ) :
    zWAct Pl K L μ T (τ + 2 * cOf L.ν / L.ε⁻¹) = zWAct Pl K L μ T τ := by
  have hR : L.ε⁻¹ ≠ 0 := inv_ne_zero L.ε_pos.ne'
  have hc : cOf L.ν ≠ 0 := by unfold cOf; exact inv_ne_zero (pow_ne_zero 2 L.ν_pos.ne')
  have hT : ∀ t, oldPhys L.ε⁻¹ (cOf L.ν) (thinG Pl K L T) (t + 2 * cOf L.ν / L.ε⁻¹) =
      oldPhys L.ε⁻¹ (cOf L.ν) (thinG Pl K L T) t :=
    fun t => funext fun z => cartLift_add_period hR hc _ t z
  funext y
  unfold zWAct thinWardW
  rw [sepW_add_period _ _ hT]

theorem zWMid_add_period (T : LStr Pl K L) (τ : ℝ) :
    zWMid Pl K L μ T (τ + 2 * cOf L.ν / L.ε⁻¹) = zWMid Pl K L μ T τ := by
  have hR : L.ε⁻¹ ≠ 0 := inv_ne_zero L.ε_pos.ne'
  have hc : cOf L.ν ≠ 0 := by unfold cOf; exact inv_ne_zero (pow_ne_zero 2 L.ν_pos.ne')
  have hT : ∀ t, oldPhys L.ε⁻¹ (cOf L.ν) (meanQ (cOf L.ν) (thinG Pl K L T))
      (t + 2 * cOf L.ν / L.ε⁻¹) = oldPhys L.ε⁻¹ (cOf L.ν) (meanQ (cOf L.ν) (thinG Pl K L T)) t :=
    fun t => funext fun z => cartLift_add_period hR hc _ t z
  funext y
  unfold zWMid
  rw [sepW_add_period _ _ hT]

theorem phasePrimitiveYAAt_mono {C C' : ℝ} {k k' : ℕ} (hC : C ≤ C') (hC' : 0 ≤ C')
    (hk : k ≤ k') (h : PhasePrimitiveYAAt Pl K L μ C k) : PhasePrimitiveYAAt Pl K L μ C' k' := by
  intro hL T s hs η
  have hs0 : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.1.le _
  have he : 0 ≤ L.ε ^ 4 := by have := L.ε_pos; positivity
  exact ⟨(h hL T s hs η).1,
    bound_mono L.ν_pos hL.nu_le (mul_nonneg he hs0) hC hC' hk (h hL T s hs η).2⟩

theorem taylorWidthYAAt_mono {C C' : ℝ} {k k' : ℕ} (hC : C ≤ C') (hC' : 0 ≤ C')
    (hk : k ≤ k') (h : TaylorWidthYAAt Pl K L μ C k) : TaylorWidthYAAt Pl K L μ C' k' := by
  intro hL T hTz s hs η q
  have hs0 : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.1.le _
  have he : 0 ≤ L.ε ^ 4 := by have := L.ε_pos; positivity
  exact bound_mono L.ν_pos hL.nu_le (mul_nonneg he hs0) hC hC' hk (h hL T hTz s hs η q)

/-- **`GeomYAAt` from the leaves** (source 5415-5432): the abstract stream-cut assembly
`GeomYAGen.cellL2_le_of_leaves` for the triple `zWAct, zWMid, zWMt`. -/
theorem geomYAAt_of_leaves {C₀ C : ℝ} {k : ℕ} (hC₀ : 0 ≤ C₀) (hC : 0 ≤ C)
    (hAlg : StreamCutAlgWith K.χy C₀) (hF : RayFTCStmt) (hazi : YoungWRayAzi)
    (hfin : LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy →
      ∀ T : LStr Pl K L, OldThinFinite (cOf L.ν) L.ν (thinRep T))
    (hP : PhasePrimitiveYAAt Pl K L μ C k) (hT : TaylorWidthYAAt Pl K L μ C k)
    (hR : ZRegularYAAt Pl K L μ) (hm : MeasYAAt Pl K L μ) :
    GeomYAAt Pl K L μ (8 * C₀ * C) k := by
  intro hL T hTz s hs η
  refine ⟨(hm hL T).2 s hs η, ?_⟩
  have hcmp : ∀ (T : LStr Pl K L) (τ : ℝ) (y : Space), 0 < ϱ y →
      (fun T τ y => ‖dYA Pl K L μ T τ y‖) T τ y =
        ‖fderiv ℝ (wardStreamCut L.ν L.ε⁻¹ K.χy (zWAct Pl K L μ T) τ) y -
          fderiv ℝ (wardStreamCut L.ν L.ε⁻¹ K.χy (zWMt Pl K L μ T) τ) y‖ := by
    intro T τ y hy
    have he : mnYA Pl K L μ T τ =ᶠ[𝓝 y] wardStreamCut L.ν L.ε⁻¹ K.χy (zWMt Pl K L μ T) τ := by
      filter_upwards [(isOpen_lt continuous_const continuous_ϱ).mem_nhds hy] with y' hy'
      exact mnYA_eq_wardStreamCut Pl K L μ hazi hL T (hfin hL T) τ y' hy'
    show ‖fderiv ℝ (actYA Pl K L μ T τ) y - fderiv ℝ (mnYA Pl K L μ T τ) y‖ = _
    rw [he.fderiv_eq]
    rfl
  have hper : ∀ (T : LStr Pl K L) (τ : ℝ) (y : Space),
      dDiff (zWAct Pl K L μ T) (zWMid Pl K L μ T) (τ + 2 * cOf L.ν / L.ε⁻¹) y =
        dDiff (zWAct Pl K L μ T) (zWMid Pl K L μ T) τ y := by
    intro T τ y
    unfold dDiff
    rw [zWAct_add_period, zWMid_add_period]
  exact GeomYAGen.cellL2_le_of_leaves hC₀ hC (zWAct Pl K L μ) (zWMid Pl K L μ) (zWMt Pl K L μ)
    (fun T τ y => ‖dYA Pl K L μ T τ y‖) hAlg hF hcmp hper (hP hL) (hT hL) (hR hL)
    (fun T => (hm hL T).1) T hTz hs η

end Regime

namespace SeqData

variable (D : SeqData)

/-- Sequence form of `PhasePrimitiveYAAt`. -/
def PhasePrimitiveYA : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    PhasePrimitiveYAAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- Sequence form of `TaylorWidthYAAt`. -/
def TaylorWidthYA : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    TaylorWidthYAAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- Sequence form of `ZRegularYAAt`. -/
def ZRegularYA : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ZRegularYAAt D.Pl D.K (D.level n) (D.mu n z)

/-- Sequence form of `MeasYAAt`. -/
def MeasYA : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, MeasYAAt D.Pl D.K (D.level n) (D.mu n z)

end SeqData

/-- **`SeqData.GeomYA` from the leaves** (source 5415-5432): the finiteness of the old thin source
comes from `sourceLN0` (`RepairStanding`: `m_Z > 3/2`, `γ > 0`), `ν ≤ 1` and the other standing
hypotheses from `LHyp`. -/
theorem geomYA_of_leaves (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hA : StreamCutAlgStmt) (hF : RayFTCStmt) (hazi : YoungWRayAzi)
    (hP : D.PhasePrimitiveYA) (hT : D.TaylorWidthYA) (hR : D.ZRegularYA) (hm : D.MeasYA) :
    D.GeomYA := by
  obtain ⟨C₀, hC₀, hAlg⟩ := hA D.K.χy hst.chiY
  obtain ⟨C₁, k₁, h₁⟩ := hP
  obtain ⟨C₂, k₂, h₂⟩ := hT
  obtain ⟨Cf, kf, hCf⟩ := sourceLN0 D.K.mZ (gRate D.Pl) hst.mZ_gt hst.gamma_pos
  have hC : 0 ≤ max |C₁| |C₂| := le_trans (abs_nonneg _) (le_max_left _ _)
  refine ⟨8 * C₀ * max |C₁| |C₂|, max k₁ k₂, ?_⟩
  filter_upwards [h₁, h₂, hR, hm] with n hn₁ hn₂ hnR hnm z hz
  refine geomYAAt_of_leaves D.Pl D.K (D.level n) (D.mu n z) hC₀ hC hAlg hF hazi ?_
    (phasePrimitiveYAAt_mono _ _ _ _ ((le_abs_self C₁).trans (le_max_left _ _)) hC
      (le_max_left _ _) (hn₁ z hz))
    (taylorWidthYAAt_mono _ _ _ _ ((le_abs_self C₂).trans (le_max_right _ _)) hC
      (le_max_right _ _) (hn₂ z hz))
    (hnR z hz) (hnm z hz)
  intro hL T
  exact (hCf (cOf (D.level n).ν) (D.level n).ν ((D.level n).ρb D.Pl D.K) hL.c_pos hL.nu_pos
    hL.nu_le T).1

end UnforcedLeray.Short.PartIIIb.Concrete
