import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.Pieces
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Pieces
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.Tools
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.Meas

/-!
# `PartIII-b:C/rep/8/1/1/2/5` (`geomYB`): reduction of the commutator comparison to two bounds

Source `the November 2 reference manuscript` lines 5427-5432 and 4195-4215,
5383-5387.  `YB = [D_{μ+1}, 𝒞_y]X₀` is split, through the phase-mean finite-width commutator
`YBmid` (the same expression with `zMid`, i.e. `X₀` of the phase-mean chart tensor), as

  `D(YB - mnYB) = D(YB - YBmid) + D(YBmid - mnYB)`,

the phase part (one phase primitive in the dilation variable, boundary term retained; the
`∂_τ` terms cancel in the commutator because `physDmu` applied to `X₀` is `W_μ`) and the width
and heat-to-Newton part (Taylor's formula in the transverse variables, strict radial gap,
`|D(K_t - K_0)| ≤ C t |x|⁻⁶`), both on the cutoff transition region and at Hessian level
(one derivative more than the `X` leaves).

## What is proved here

* `geomYBAt_of_leaves`: the triangle inequality through `actYBMid` and the cell-norm assembly;
* `SeqData.measYB` (`GeomYB/Meas.lean`): `dYB` is measurable along every young cell, from the
  exact formula `actYFormula` and the differentiability `yTermsDiff` (difference quotients of
  `Y₁ - 𝒞_yW_μ`, `measurable_deriv` for the phase derivative at a fixed receiver);
* `zMid_phase_free`, `actYBMid_phase_free`: the middle field does not depend on the phase
  (`meanQ` forgets the cell position), so the measurability conjuncts of the leaves hold
  (`phasePrimitiveYBAt_of_bound`, `taylorWidthYBAt_of_bound`);
* `SeqData.geomYB_of_leaves`, `SeqData.geomYB_of_bounds`: `GeomYB` from `RepairStanding` and the
  two analytic bounds `PhasePrimitiveYBBound`, `TaylorWidthYBBound`.

## What remains (the two analytic bounds)

`PhasePrimitiveYBBoundAt` (`‖D_y(YB - YBmid)‖_{L²_τ} ≤ P_ν ε⁴ s^{5/2} N`) and
`TaylorWidthYBBoundAt` (`|D_y(YBmid - mnYB)| ≤ P_ν ε⁴ s^{5/2} N`).  They are the Hessian-level
separated-kernel comparisons of 5427-5432 (as `PhasePrimitiveAt`, `TaylorWidthAt` of `GeomX` and
`PhasePrimitiveYAAt`, `TaylorWidthYAAt` of `GeomY/AsmYA`, which are also open).  They do not follow
from `HessianBound`: on the transition annulus each term of `D_y([D_{μ+1},𝒞_y]X₀)`, e.g.
`(y·∇χ_y) D_yX₀`, is of order `ε³ s^{5/2} N`; only the actual-minus-mean difference gains the
factor `ε`, whereas `HessianBound` bounds `D²X₁`, `D²X^mt` separately.
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

/-- `YB` with the phase-mean chart tensor in `X₀` (finite width, no phase). -/
def actYBMid (T : LStr Pl K L) : ℝ → Space → Space := fun τ y =>
  physDmu L.ν (μ + 1) (wardStreamCut L.ν L.ε⁻¹ K.χy (zMid Pl K L μ T)) τ y -
    wardStreamCut L.ν L.ε⁻¹ K.χy (physDmu L.ν (μ + 1) (zMid Pl K L μ T)) τ y

/-- `|D_y(YB - YBmid)|` (the phase part). -/
def dPhaseYB (T : LStr Pl K L) (τ : ℝ) (y : Space) : ℝ :=
  ‖fderiv ℝ (actYB Pl K L μ T τ) y - fderiv ℝ (actYBMid Pl K L μ T τ) y‖

/-- `|D_y(YBmid - mnYB)|` (the width and heat-to-Newton part). -/
def dWidthYB (T : LStr Pl K L) (τ : ℝ) (y : Space) : ℝ :=
  ‖fderiv ℝ (actYBMid Pl K L μ T τ) y - fderiv ℝ (mnYB Pl K L μ T τ) y‖

/-- **Phase primitive for the commutator** (source 5427-5432, Hessian level). -/
def PhasePrimitiveYBAt (C : ℝ) (k : ℕ) : Prop :=
  LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy → ∀ T : LStr Pl K L, ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν), ∀ η : ℝ,
    AEMeasurable (fun q : ℝ => dPhaseYB Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
        (NearInst.chartY L.ε⁻¹ (s, (q, η)))) (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2))) ∧
    cellL2 L.ε⁻¹ (cOf L.ν) (dPhaseYB Pl K L μ T) s η ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) * oldN1 Pl K L T

/-- **Finite width and heat-to-Newton for the commutator** (source 5427-5432, pointwise in the
phase because both fields are phase free), for swirl-free thin stresses (`ThinAziZero`, source
5376, 5141-5142, 4772-4774: `YBmid` keeps a hoop entry, `mnYB` drops it). -/
def TaylorWidthYBAt (C : ℝ) (k : ℕ) : Prop :=
  LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy → ∀ T : LStr Pl K L, ThinAziZero Pl K L T →
    ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν), ∀ η : ℝ,
    AEMeasurable (fun q : ℝ => dWidthYB Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
        (NearInst.chartY L.ε⁻¹ (s, (q, η)))) (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2))) ∧
    ∀ q : ℝ, ENNReal.ofReal (dWidthYB Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
        (NearInst.chartY L.ε⁻¹ (s, (q, η)))) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) * oldN1 Pl K L T

theorem dYB_le (T : LStr Pl K L) (τ : ℝ) (y : Space) :
    ‖dYB Pl K L μ T τ y‖ ≤ dPhaseYB Pl K L μ T τ y + dWidthYB Pl K L μ T τ y := by
  unfold dYB dPhaseYB dWidthYB
  calc ‖fderiv ℝ (actYB Pl K L μ T τ) y - fderiv ℝ (mnYB Pl K L μ T τ) y‖
      = ‖(fderiv ℝ (actYB Pl K L μ T τ) y - fderiv ℝ (actYBMid Pl K L μ T τ) y) +
          (fderiv ℝ (actYBMid Pl K L μ T τ) y - fderiv ℝ (mnYB Pl K L μ T τ) y)‖ := by
        congr 1; abel
    _ ≤ _ := norm_add_le _ _

/-- One regime: the commutator comparison from the two leaves and the measurability of `dYB`. -/
theorem geomYBAt_of_leaves {C : ℝ} {k : ℕ} (hC : 0 ≤ C)
    (hP : PhasePrimitiveYBAt Pl K L μ C k) (hT : TaylorWidthYBAt Pl K L μ C k)
    (hM : LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy → ∀ T : LStr Pl K L, ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν),
      ∀ η : ℝ, AEStronglyMeasurable (fun q : ℝ => dYB Pl K L μ T
        (NearInst.chartTau L.ε⁻¹ (s, (q, η))) (NearInst.chartY L.ε⁻¹ (s, (q, η))))
        (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2)))) :
    GeomYBAt Pl K L μ (2 * C) k := by
  intro hL T hTz s hs η
  refine ⟨hM hL T s hs η, ?_⟩
  have hc0 : 0 < cOf L.ν := by have := L.ν_pos; simp only [cOf]; positivity
  obtain ⟨hPm, hPb⟩ := hP hL T s hs η
  obtain ⟨hTm, hTb⟩ := hT hL T hTz s hs η
  set B : ℝ≥0∞ := ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) * oldN1 Pl K L T
    with hB
  have hμm : ∀ {f : ℝ → ℝ≥0∞}, AEMeasurable f (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2))) →
      AEMeasurable f (cellμ (cOf L.ν)) := by
    intro f hf
    unfold cellμ
    exact hf.smul_measure _
  rw [cellL2_eq_cellN]
  calc cellN (cOf L.ν) (fun q => ENNReal.ofReal
        (‖dYB Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η))) (NearInst.chartY L.ε⁻¹ (s, (q, η)))‖))
      ≤ cellN (cOf L.ν) (fun q => ENNReal.ofReal (dPhaseYB Pl K L μ T
            (NearInst.chartTau L.ε⁻¹ (s, (q, η))) (NearInst.chartY L.ε⁻¹ (s, (q, η)))) +
          ENNReal.ofReal (dWidthYB Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
            (NearInst.chartY L.ε⁻¹ (s, (q, η))))) := by
        refine cellN_mono fun q => ?_
        refine (ENNReal.ofReal_le_ofReal (dYB_le Pl K L μ T _ _)).trans ENNReal.ofReal_add_le
    _ ≤ cellN (cOf L.ν) (fun q => ENNReal.ofReal (dPhaseYB Pl K L μ T
            (NearInst.chartTau L.ε⁻¹ (s, (q, η))) (NearInst.chartY L.ε⁻¹ (s, (q, η))))) +
        cellN (cOf L.ν) (fun q => ENNReal.ofReal (dWidthYB Pl K L μ T
            (NearInst.chartTau L.ε⁻¹ (s, (q, η))) (NearInst.chartY L.ε⁻¹ (s, (q, η))))) :=
        cellN_add_le (hμm hPm.ennreal_ofReal) (hμm hTm.ennreal_ofReal)
    _ ≤ B + B := by
        gcongr
        · rw [← cellL2_eq_cellN]
          exact hPb
        · calc cellN (cOf L.ν) (fun q => ENNReal.ofReal (dWidthYB Pl K L μ T
                (NearInst.chartTau L.ε⁻¹ (s, (q, η))) (NearInst.chartY L.ε⁻¹ (s, (q, η)))))
              ≤ cellN (cOf L.ν) (fun _ => B) := cellN_mono fun q => hTb q
            _ = B := cellN_const hc0 B
    _ = ENNReal.ofReal (2 * C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) * oldN1 Pl K L T := by
        have h2 : ENNReal.ofReal (2 * C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) =
            2 * ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) := by
          rw [show (2 : ℝ) * C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) =
            2 * (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) by ring,
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        rw [h2, hB]
        ring

theorem phasePrimitiveYBAt_mono {C C' : ℝ} {k k' : ℕ} (hC : C ≤ C') (hC' : 0 ≤ C')
    (hk : k ≤ k') (h : PhasePrimitiveYBAt Pl K L μ C k) : PhasePrimitiveYBAt Pl K L μ C' k' := by
  intro hL T s hs η
  have hs0 : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.1.le _
  have he : 0 ≤ L.ε ^ 4 := by have := L.ε_pos; positivity
  exact ⟨(h hL T s hs η).1,
    bound_mono L.ν_pos hL.nu_le (mul_nonneg he hs0) hC hC' hk (h hL T s hs η).2⟩

theorem taylorWidthYBAt_mono {C C' : ℝ} {k k' : ℕ} (hC : C ≤ C') (hC' : 0 ≤ C')
    (hk : k ≤ k') (h : TaylorWidthYBAt Pl K L μ C k) : TaylorWidthYBAt Pl K L μ C' k' := by
  intro hL T hTz s hs η
  have hs0 : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.1.le _
  have he : 0 ≤ L.ε ^ 4 := by have := L.ε_pos; positivity
  exact ⟨(h hL T hTz s hs η).1, fun q =>
    bound_mono L.ν_pos hL.nu_le (mul_nonneg he hs0) hC hC' hk ((h hL T hTz s hs η).2 q)⟩

/-! ### The middle field is phase free; the leaves without their measurability conjuncts -/

/-- A phase-free field has a phase-free stream cutoff. -/
theorem wardStreamCut_phase_free {ν R : ℝ} {χ : ℝ → ℝ} {Z : ℝ → Space → Space}
    (hZ : ∀ t, Z t = Z 0) (t : ℝ) : wardStreamCut ν R χ Z t = wardStreamCut ν R χ Z 0 := by
  funext y
  unfold wardStreamCut outPrim
  rw [hZ t]

/-- `D_{μ'}` of a phase-free field is phase free (its phase derivative vanishes). -/
theorem physDmu_phase_free {ν μ' : ℝ} {Z : ℝ → Space → Space} (hZ : ∀ t, Z t = Z 0) (t : ℝ) :
    physDmu ν μ' Z t = physDmu ν μ' Z 0 := by
  funext y
  unfold physDmu
  have h1 : (fun s => Z s y) = fun _ => Z 0 y := funext fun s => by rw [hZ s]
  rw [h1, hZ t]
  simp only [deriv_const]

/-- `X₀` of the phase-mean chart tensor does not depend on the phase: `meanQ` forgets the cell
position `q`, the only phase-dependent chart coordinate. -/
theorem zMid_phase_free (T : LStr Pl K L) (τ : ℝ) : zMid Pl K L μ T τ = zMid Pl K L μ T 0 := by
  have hF : ∀ t, oldPhys L.ε⁻¹ (cOf L.ν) (meanQ (cOf L.ν) (thinG Pl K L T)) t =
      oldPhys L.ε⁻¹ (cOf L.ν) (meanQ (cOf L.ν) (thinG Pl K L T)) 0 := by
    intro t
    funext z
    simp only [oldPhys, NearInst.cartLift, NearInst.chartOf, meanQ]
  have hP : ∀ t, oldPhys L.ε⁻¹ (cOf L.ν) (meanQ (cOf L.ν) (thinG Pl K L T)) (t + τ) =
      oldPhys L.ε⁻¹ (cOf L.ν) (meanQ (cOf L.ν) (thinG Pl K L T)) t :=
    fun t => (hF (t + τ)).trans (hF t).symm
  funext y
  unfold zMid wardX0
  have e1 := sepW_add_period L.ν (μ : ℂ) hP y 0
  have e2 := sepW_add_period L.ν ((μ : ℂ) + 1) hP y 0
  rw [zero_add] at e1 e2
  rw [e1, e2]

/-- The middle commutator `YBmid` does not depend on the phase. -/
theorem actYBMid_phase_free (T : LStr Pl K L) (τ : ℝ) :
    actYBMid Pl K L μ T τ = actYBMid Pl K L μ T 0 := by
  have hz := zMid_phase_free Pl K L μ T
  have hc : ∀ t, wardStreamCut L.ν L.ε⁻¹ K.χy (zMid Pl K L μ T) t =
      wardStreamCut L.ν L.ε⁻¹ K.χy (zMid Pl K L μ T) 0 := wardStreamCut_phase_free hz
  have hd : ∀ t, physDmu L.ν (μ + 1) (zMid Pl K L μ T) t =
      physDmu L.ν (μ + 1) (zMid Pl K L μ T) 0 := physDmu_phase_free hz
  funext y
  unfold actYBMid
  rw [physDmu_phase_free hc τ, wardStreamCut_phase_free hd τ]

/-- **Phase primitive for the commutator, bound only** (source 5427-5432, 4195-4215 at Hessian
level): `‖D_y(YB - YBmid)‖_{L²_τ} ≤ P_ν ε⁴ s^{5/2} N` at young chart points. -/
def PhasePrimitiveYBBoundAt (C : ℝ) (k : ℕ) : Prop :=
  LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy → ∀ T : LStr Pl K L, ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν), ∀ η : ℝ,
    cellL2 L.ε⁻¹ (cOf L.ν) (dPhaseYB Pl K L μ T) s η ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) * oldN1 Pl K L T

/-- **Finite width and heat-to-Newton for the commutator, bound only** (source 5427-5432,
5383-5387): `|D_y(YBmid - mnYB)| ≤ P_ν ε⁴ s^{5/2} N` at young chart points (both fields are phase
free), for swirl-free thin stresses (`ThinAziZero`, source 5376, 5141-5142, 4772-4774). -/
def TaylorWidthYBBoundAt (C : ℝ) (k : ℕ) : Prop :=
  LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy → ∀ T : LStr Pl K L, ThinAziZero Pl K L T →
    ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν), ∀ η : ℝ,
    ∀ q : ℝ, ENNReal.ofReal (dWidthYB Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
        (NearInst.chartY L.ε⁻¹ (s, (q, η)))) ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) * oldN1 Pl K L T

/-- The measurability conjunct of `PhasePrimitiveYBAt` holds: `YBmid` is phase free and
`D_y(YB)` is a.e.-strongly measurable in the phase (`actYB_fderiv_aesm`). -/
theorem phasePrimitiveYBAt_of_bound {C : ℝ} {k : ℕ} (hmZ : 0 ≤ K.mZ) (hC0 : 0 < K.C0)
    (hF : ActYFormulaAt Pl K L μ) (hD : YTermsDiffAt Pl K L μ)
    (h : PhasePrimitiveYBBoundAt Pl K L μ C k) : PhasePrimitiveYBAt Pl K L μ C k := by
  intro hL T s hs η
  refine ⟨?_, h hL T s hs η⟩
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  refine (cell_aesm_of_phase hR.ne' (cOf L.ν) s η (F := dPhaseYB Pl K L μ T) ?_).aemeasurable
  have hA := actYB_fderiv_aesm Pl K L μ hmZ hC0 hF hD hL T hs.1 η
  have e : (fun τ : ℝ => dPhaseYB Pl K L μ T τ (NearInst.chartY L.ε⁻¹ (s, (0, η)))) = fun τ =>
      ‖fderiv ℝ (actYB Pl K L μ T τ) (NearInst.chartY L.ε⁻¹ (s, (0, η))) -
        fderiv ℝ (actYBMid Pl K L μ T 0) (NearInst.chartY L.ε⁻¹ (s, (0, η)))‖ := by
    funext τ
    unfold dPhaseYB
    rw [actYBMid_phase_free Pl K L μ T τ]
  rw [e]
  exact (hA.sub aestronglyMeasurable_const).norm

/-- The measurability conjunct of `TaylorWidthYBAt` holds: `dWidthYB` is constant along the cell. -/
theorem taylorWidthYBAt_of_bound {C : ℝ} {k : ℕ} (h : TaylorWidthYBBoundAt Pl K L μ C k) :
    TaylorWidthYBAt Pl K L μ C k := by
  intro hL T hTz s hs η
  refine ⟨?_, h hL T hTz s hs η⟩
  have e : (fun q : ℝ => dWidthYB Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
      (NearInst.chartY L.ε⁻¹ (s, (q, η)))) =
      fun _ => dWidthYB Pl K L μ T 0 (NearInst.chartY L.ε⁻¹ (s, (0, η))) := by
    funext q
    have hY : NearInst.chartY L.ε⁻¹ (s, (q, η)) = NearInst.chartY L.ε⁻¹ (s, (0, η)) := by
      simp [NearInst.chartY]
    unfold dWidthYB
    rw [hY, actYBMid_phase_free Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))]
    rfl
  rw [e]
  exact aemeasurable_const

end Regime

namespace SeqData

variable (D : SeqData)

/-- Sequence form of `PhasePrimitiveYBAt`. -/
def PhasePrimitiveYB : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    PhasePrimitiveYBAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- Sequence form of `TaylorWidthYBAt`. -/
def TaylorWidthYB : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    TaylorWidthYBAt D.Pl D.K (D.level n) (D.mu n z) C k


/-- **`SeqData.GeomYB` from the two analytic leaves** (source 4195-4215, 5383-5387, 5427-5432):
the measurability of `dYB` along the cells is `SeqData.measYB` (from `actYFormula` and
`yTermsDiff`), the triangle inequality through `actYBMid` is `geomYBAt_of_leaves`. -/
theorem geomYB_of_leaves {dm dp : ℝ} (hst : D.RepairStanding dm dp) (hP : D.PhasePrimitiveYB)
    (hT : D.TaylorWidthYB) : D.GeomYB := by
  obtain ⟨C₁, k₁, h₁⟩ := hP
  obtain ⟨C₂, k₂, h₂⟩ := hT
  have hC : 0 ≤ max |C₁| |C₂| := le_trans (abs_nonneg _) (le_max_left _ _)
  refine ⟨2 * max |C₁| |C₂|, max k₁ k₂, ?_⟩
  filter_upwards [h₁, h₂, D.measYB hst] with n hn₁ hn₂ hnm z hz
  exact geomYBAt_of_leaves D.Pl D.K (D.level n) (D.mu n z) hC
    (phasePrimitiveYBAt_mono _ _ _ _ ((le_abs_self C₁).trans (le_max_left _ _)) hC
      (le_max_left _ _) (hn₁ z hz))
    (taylorWidthYBAt_mono _ _ _ _ ((le_abs_self C₂).trans (le_max_right _ _)) hC
      (le_max_right _ _) (hn₂ z hz))
    (hnm z hz)


/-- Sequence form of `PhasePrimitiveYBBoundAt` (the analytic leaf, measurability discharged). -/
def PhasePrimitiveYBBound : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    PhasePrimitiveYBBoundAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- Sequence form of `TaylorWidthYBBoundAt` (the analytic leaf, measurability discharged). -/
def TaylorWidthYBBound : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    TaylorWidthYBBoundAt D.Pl D.K (D.level n) (D.mu n z) C k

theorem phasePrimitiveYB_of_bound {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h : D.PhasePrimitiveYBBound) : D.PhasePrimitiveYB := by
  obtain ⟨C, k, hC⟩ := h
  refine ⟨C, k, ?_⟩
  filter_upwards [hC, actYFormula D hst, Sub8_1_1_2_3.yTermsDiff D hst] with n hn hF hD z hz
  exact phasePrimitiveYBAt_of_bound D.Pl D.K (D.level n) (D.mu n z) (by linarith [hst.mZ_gt])
    hst.C0_pos (hF z hz) (hD z hz) (hn z hz)

theorem taylorWidthYB_of_bound (h : D.TaylorWidthYBBound) : D.TaylorWidthYB := by
  obtain ⟨C, k, hC⟩ := h
  refine ⟨C, k, ?_⟩
  filter_upwards [hC] with n hn z hz
  exact taylorWidthYBAt_of_bound D.Pl D.K (D.level n) (D.mu n z) (hn z hz)

/-- **`SeqData.GeomYB` from the two analytic bounds** (source 4195-4215, 5383-5387, 5427-5432):
all measurability is discharged (`measYB`, `phasePrimitiveYBAt_of_bound`,
`taylorWidthYBAt_of_bound`); what remains is the Hessian-level kernel comparison of the commutator,
split into its phase part and its width/heat-to-Newton part. -/
theorem geomYB_of_bounds {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hP : D.PhasePrimitiveYBBound) (hT : D.TaylorWidthYBBound) : D.GeomYB :=
  D.geomYB_of_leaves hst (D.phasePrimitiveYB_of_bound hst hP) (D.taylorWidthYB_of_bound hT)

end SeqData

end UnforcedLeray.Short.PartIIIb.Concrete
