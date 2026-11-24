import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1_1

/-!
# `PartIII-b:C/rep/8/1/1/2` (`geomY`): the pieces of the `Y` part of the geometric comparison

Source `the November 2 reference manuscript`
lines 5415-5432 ("For `Y` use the exact formula `Y = 𝒞_{χ_y}W_μ + [D_{μ+1},𝒞_{χ_y}](W_μ-W_{μ+1})`.
Apply the spatial kernel comparison to these terms separately.  Thus no phase derivative of the
improved bound, or of the source, is taken"), 4171-4215 (`ward:cutoff-source`,
`Y = 𝒞_yW_μ + [D_{μ+1},𝒞_y]X₀`, from `D_{μ+1}X₀ = W_μ`), 5374-5387 (the same formula for `Y^mt`
from the shifted dilation identity of the harmonic uncut Newton fields).

## Decomposition

`Y₁ = actY = D_{μ+1}𝒞_y X₀ = YA + YB` with
* `YA = 𝒞_y W_μ` (the cutoff of the finite-width phase-dependent response `W_μ`, `wardStreamCut`),
* `YB = D_{μ+1}(𝒞_yX₀) - 𝒞_y(D_{μ+1}X₀)` (the commutator, `physDmu`);

`Y^mt = mnY = mnYA + mnYB` is the same with the zero-width Newton fields (`streamCut`, `dmuFree`),
`MeanYFormula` of `PartIII-b_C_rep_8_1_org`.  The comparison is then `D(YA - mnYA)` and
`D(YB - mnYB)`, each a spatial kernel comparison (`GeomYAAt`, `GeomYBAt`).  `ActYFormulaAt`,
`MeanYFormulaAt` are the two exact formulas (on the open set `ϱ y > 0`, where the cutoffs are
local), `YTermsDiffAt` says the four terms are differentiable there.  `actY` contains the phase
derivative `∂_τ` of `physDmu`, which exists for almost every phase; hence the formulas and
differentiability are stated for almost every `τ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- A phase-free field on `Vec3` as a field on `Space` (as in `Xmean`). -/
def mtField (F : Vec3 → Vec3) : ℝ → Space → Space :=
  fun _ y => WithLp.toLp 2 (F (WithLp.ofLp y))

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- `W_μ` of the old thin source `χ_oT₁` (source 4168-4171, `sep:resolvent` 3611-3621): the real
Cartesian components, as in `wardX0`. -/
def thinWardW (T : LStr Pl K L) : ℝ → Space → Space := fun τ y =>
  WithLp.toLp 2 fun i =>
    (IIIa.sepW L.ν (μ : ℂ) (oldPhys L.ε⁻¹ (cOf L.ν) (thinG Pl K L T)) y τ i).re

/-- `X₀ = W_μ - W_{μ+1}` (source 4171). -/
def zAct0 (T : LStr Pl K L) : ℝ → Space → Space :=
  wardX0 L.ν μ L.ε⁻¹ (cOf L.ν) (thinG Pl K L T)

/-- `YA = 𝒞_y W_μ` (source 5427-5432, 4195-4200). -/
def actYA (T : LStr Pl K L) : ℝ → Space → Space :=
  wardStreamCut L.ν L.ε⁻¹ K.χy (thinWardW Pl K L μ T)

/-- `YB = [D_{μ+1}, 𝒞_y]X₀ = D_{μ+1}(𝒞_yX₀) - 𝒞_y(D_{μ+1}X₀)` (source 4195-4200), `X₀ = W_μ - W_{μ+1}`. -/
def actYB (T : LStr Pl K L) : ℝ → Space → Space := fun τ y =>
  physDmu L.ν (μ + 1) (wardStreamCut L.ν L.ε⁻¹ K.χy (zAct0 Pl K L μ T)) τ y -
    wardStreamCut L.ν L.ε⁻¹ K.χy (physDmu L.ν (μ + 1) (zAct0 Pl K L μ T)) τ y

/-- `𝒞_{χ_y}W^mt_μ` (source 5427-5432), phase free, as a field on `Space`. -/
def mnYA (T : LStr Pl K L) : ℝ → Space → Space :=
  mtField (streamCut L.ν L.ε K.χy (youngW (cOf L.ν) L.ν L.ε μ K.χo (thinRep T)))

/-- `[D_{μ+1}, 𝒞_{χ_y}](W^mt_μ - W^mt_{μ+1})` (source 5427-5432), phase free. -/
def mnYB (T : LStr Pl K L) : ℝ → Space → Space :=
  mtField (fun y =>
    dmuFree L.ν (μ + 1) (streamCut L.ν L.ε K.χy
        (youngW (cOf L.ν) L.ν L.ε μ K.χo (thinRep T) - youngW (cOf L.ν) L.ν L.ε (μ + 1) K.χo (thinRep T))) y -
      streamCut L.ν L.ε K.χy (dmuFree L.ν (μ + 1)
        (youngW (cOf L.ν) L.ν L.ε μ K.χo (thinRep T) - youngW (cOf L.ν) L.ν L.ε (μ + 1) K.χo (thinRep T))) y)

/-- `D_y(YA - mnYA)`. -/
def dYA (T : LStr Pl K L) (τ : ℝ) (y : Space) : Space →L[ℝ] Space :=
  fderiv ℝ (actYA Pl K L μ T τ) y - fderiv ℝ (mnYA Pl K L μ T τ) y

/-- `D_y(YB - mnYB)`. -/
def dYB (T : LStr Pl K L) (τ : ℝ) (y : Space) : Space →L[ℝ] Space :=
  fderiv ℝ (actYB Pl K L μ T τ) y - fderiv ℝ (mnYB Pl K L μ T τ) y

/-- **The exact formula for `Y₁`** (source 4195-4200 `ward:cutoff-source`, 5427-5432):
`Y = 𝒞_yW_μ + [D_{μ+1},𝒞_y]X₀` for almost every phase, at every receiver off the axis. -/
def ActYFormulaAt : Prop :=
  ∀ T : LStr Pl K L, ∀ᵐ τ : ℝ, ∀ y : Space, 0 < ϱ y →
    actY Pl K L μ T τ y = actYA Pl K L μ T τ y + actYB Pl K L μ T τ y

/-- **The exact formula for `Y^mt`** (source 5383-5387, 5427-5432; `meanYFormula_of_shift` of
`PartIII-b_C_rep_8_1_org` from `MeanShiftIdentity`, the region below the young radius being
trivial because the stream cutoff and its derivative vanish there). -/
def MeanYFormulaAt : Prop :=
  LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy → ∀ T : LStr Pl K L, ∀ τ : ℝ, ∀ y : Space, 0 < ϱ y →
    mnY Pl K L μ T τ y = mnYA Pl K L μ T τ y + mnYB Pl K L μ T τ y

/-- **The four terms are differentiable** off the axis (source 4178-4186, 5400-5406: smooth
separated kernels, convergent outward primitive; the cutoff terms vanish identically in the old
region). -/
def YTermsDiffAt : Prop :=
  LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy → ∀ T : LStr Pl K L, ∀ᵐ τ : ℝ, ∀ y : Space, 0 < ϱ y →
    DifferentiableAt ℝ (actYA Pl K L μ T τ) y ∧ DifferentiableAt ℝ (actYB Pl K L μ T τ) y ∧
    DifferentiableAt ℝ (mnYA Pl K L μ T τ) y ∧ DifferentiableAt ℝ (mnYB Pl K L μ T τ) y

/-- **Kernel comparison of `𝒞_yW_μ`** (source 5427-5432: "apply the spatial kernel comparison to
these terms separately"; one phase primitive with the dilation-one boundary term, finite width,
heat-to-Newton error): `‖D_y(YA - mnYA)‖_{L²_τ} ≤ P_ν ε⁴ s^{5/2} N` at young chart points, for
swirl-free thin stresses (`ThinAziZero`, source 5376, 5141-5142, 4772-4774). -/
def GeomYAAt (C : ℝ) (k : ℕ) : Prop :=
  LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy → ∀ T : LStr Pl K L, ThinAziZero Pl K L T →
    ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν), ∀ η : ℝ,
    AEStronglyMeasurable (fun q : ℝ => dYA Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
        (NearInst.chartY L.ε⁻¹ (s, (q, η)))) (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2))) ∧
    cellL2 L.ε⁻¹ (cOf L.ν) (fun τ y => ‖dYA Pl K L μ T τ y‖) s η ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) * oldN1 Pl K L T

/-- **Kernel comparison of the commutator** `[D_{μ+1},𝒞_y]X₀` (source 5427-5432, same
mechanism; the Laplacian of the stream-cutoff field is retained, 5383-5387), for swirl-free thin
stresses (`ThinAziZero`). -/
def GeomYBAt (C : ℝ) (k : ℕ) : Prop :=
  LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy → ∀ T : LStr Pl K L, ThinAziZero Pl K L T →
    ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν), ∀ η : ℝ,
    AEStronglyMeasurable (fun q : ℝ => dYB Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
        (NearInst.chartY L.ε⁻¹ (s, (q, η)))) (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2))) ∧
    cellL2 L.ε⁻¹ (cOf L.ν) (fun τ y => ‖dYB Pl K L μ T τ y‖) s η ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) * oldN1 Pl K L T

end Regime

namespace SeqData

variable (D : SeqData)

/-- Sequence form of `ActYFormulaAt`. -/
def ActYFormula : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ActYFormulaAt D.Pl D.K (D.level n) (D.mu n z)

/-- Sequence form of `MeanYFormulaAt`. -/
def MeanYFormula : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, MeanYFormulaAt D.Pl D.K (D.level n) (D.mu n z)

/-- Sequence form of `YTermsDiffAt`. -/
def YTermsDiff : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, YTermsDiffAt D.Pl D.K (D.level n) (D.mu n z)

/-- Sequence form of `GeomYAAt`. -/
def GeomYA : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    GeomYAAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- Sequence form of `GeomYBAt`. -/
def GeomYB : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    GeomYBAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- The standing hypotheses `LHyp` at the levels (`SeqData.eventually_lHyp`). -/
def LHypSeq : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    LHyp (cOf (D.level n).ν) (D.level n).ν (D.level n).ε (D.mu n z) D.K.χo D.K.χy

end SeqData

end UnforcedLeray.Short.PartIIIb.Concrete
