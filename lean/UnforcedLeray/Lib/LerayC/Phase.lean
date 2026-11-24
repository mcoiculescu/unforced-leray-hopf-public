import UnforcedLeray.Lib.LerayC.ComplexComm
import UnforcedLeray.Lib.PhaseSpace.Test
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic

/-!
# The Leray projection on the phase space `Y_p` (INF01 T17)

Blueprint: INF01 target T17 (`lerayY`, `norm_lerayY_le`) of

decision D2 of `scoping/README.md` §3 (`Y_q := Lp (Lp CVec3 q volume) q (haarAddCircle)`, the
drafted `PhaseSpace.Yq`).

Manuscript: unit B0414 (`paper/main.tex` lines 7336–7344: `P_σ` is bounded on `L^q`, "hence on
`Y_q`", and commutes with phase translations), unit B0421 (eq:free-stress-10, lines 7427–7445:
`C_q = ‖P_σ‖_{q→q}`, uniform in the period), unit B0429 (lines 3616–3618: `P` is bounded on
`Y_p` and commutes with spatial heat and phase translation).

* `lerayY P p hp1 hp : Y_p →L[ℂ] Y_p`: the complex Leray projection `lerayC` applied slice by
  slice, `(𝔓f)(τ) = 𝔓(f(τ))` (`coeFn_lerayY`);
* `norm_lerayY_le` (**T17**): `‖𝔓‖_{Y_p → Y_p} ≤ ‖𝔓‖_{L^p(ℂ³) → L^p(ℂ³)}`, uniformly in the period
  `P`; `norm_lerayY_le_two`: `≤ 2 ‖𝔓‖_{L^p(R³) → L^p(R³)}`;
* `lerayY_phase`: `𝔓` commutes with every phase translation `f ↦ f(σ + ·)`;
* `lerayY_comm_slicewise`, `lerayY_heat`: `𝔓` commutes with every slice-wise operator commuting
  with `lerayC`, in particular with the spatial heat semigroup acting slice by slice.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.RieszLp

open UnforcedLeray.PhaseSpace (CVec3 Yq)

/-! ### Slice-wise operators and phase translation (generic) -/

section Generic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {X : Type*} [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] {q : ℝ≥0∞} [Fact (1 ≤ q)] {M α : Type*} [MeasurableSpace α] {μ : Measure α}
  [VAdd M α] [VAddInvariantMeasure M α μ] [MeasurableConstVAdd M α]

/-- A slice-wise operator `L.compLpL` commutes with every measure-preserving translation of the
phase variable (adapted from `B0420.compLpL_freeSemigroupLp_vadd`,
-/
theorem compLpL_vadd (L : X →L[𝕜] X) (c : DomAddAct M) (f : Lp X q μ) :
    L.compLpL q μ (c +ᵥ f) = c +ᵥ L.compLpL q μ f := by
  apply Lp.ext
  have h1 : (L.compLpL q μ (c +ᵥ f) : α → X) =ᵐ[μ] fun a => L ((c +ᵥ f : Lp X q μ) a) :=
    L.coeFn_compLpL (c +ᵥ f)
  have h2 : ((c +ᵥ f : Lp X q μ) : α → X) =ᵐ[μ] fun a => f (DomAddAct.mk.symm c +ᵥ a) :=
    DomAddAct.vadd_Lp_ae_eq c f
  have h3 : ((c +ᵥ L.compLpL q μ f : Lp X q μ) : α → X) =ᵐ[μ]
      fun a => (L.compLpL q μ f) (DomAddAct.mk.symm c +ᵥ a) :=
    DomAddAct.vadd_Lp_ae_eq c _
  have h4' : (L.compLpL q μ f : α → X) =ᵐ[μ] fun a => L (f a) := L.coeFn_compLpL f
  have hmp : MeasurePreserving (fun x : α => DomAddAct.mk.symm c +ᵥ x) μ μ :=
    measurePreserving_vadd (DomAddAct.mk.symm c) μ
  have h4 : (fun x => (L.compLpL q μ f) (DomAddAct.mk.symm c +ᵥ x)) =ᵐ[μ]
      fun x => L (f (DomAddAct.mk.symm c +ᵥ x)) :=
    h4'.comp_tendsto hmp.quasiMeasurePreserving.tendsto_ae
  refine h1.trans (EventuallyEq.trans ?_ h3.symm)
  refine EventuallyEq.trans ?_ h4.symm
  filter_upwards [h2] with x e2
  rw [e2]

end Generic

section GenericComm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {q : ℝ≥0∞} [Fact (1 ≤ q)]
  {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Slice-wise operators of commuting operators commute. -/
theorem compLpL_comm (L N : X →L[ℝ] X) (h : L.comp N = N.comp L) :
    (L.compLpL q μ).comp (N.compLpL q μ) = (N.compLpL q μ).comp (L.compLpL q μ) := by
  ext1 f
  apply Lp.ext
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have h1 := L.coeFn_compLpL (μ := μ) (p := q) (N.compLpL q μ f)
  have h2 := N.coeFn_compLpL (μ := μ) (p := q) f
  have h3 := N.coeFn_compLpL (μ := μ) (p := q) (L.compLpL q μ f)
  have h4 := L.coeFn_compLpL (μ := μ) (p := q) f
  filter_upwards [h1, h2, h3, h4] with x e1 e2 e3 e4
  rw [e1, e2, e3, e4]
  exact (congrArg (fun T : X →L[ℝ] X => T (f x)) h :)

end GenericComm

/-! ### The Leray projection on `Y_p` -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **INF01 T17 (`lerayY`).** The Leray projection on the phase space
`Y_p = L^p(ℝ/Pℤ; L^p(R³;ℂ³))` (decision D2), acting slice by slice:
`(𝔓f)(τ) = 𝔓(f(τ))`, `1 < p < ∞` (B0414, `paper/main.tex` lines 7336–7344). -/
def lerayY (P : ℝ) [Fact (0 < P)] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤) :
    Yq P p →L[ℂ] Yq P p :=
  (lerayC p hp1 hp).compLpL p (AddCircle.haarAddCircle (T := P))

variable {P : ℝ} [Fact (0 < P)]

theorem coeFn_lerayY (hp1 : 1 < p) (hp : p ≠ ⊤) (f : Yq P p) :
    (lerayY P p hp1 hp f : AddCircle P → Lp CVec3 p (volume : Measure Space))
      =ᵐ[AddCircle.haarAddCircle] fun τ => lerayC p hp1 hp (f τ) :=
  (lerayC p hp1 hp).coeFn_compLpL f

/-- **INF01 T17 (`norm_lerayY_le`).** `‖𝔓‖_{Y_p → Y_p} ≤ ‖𝔓‖_{L^p(R³;ℂ³) → L^p(R³;ℂ³)}`,
uniformly in the period `P` (B0421, `paper/main.tex` lines 7427–7445: `C_q = ‖P_σ‖_{q→q}`). -/
theorem norm_lerayY_le (hp1 : 1 < p) (hp : p ≠ ⊤) :
    ‖lerayY P p hp1 hp‖ ≤ ‖lerayC p hp1 hp‖ :=
  ContinuousLinearMap.norm_compLpL_le _

/-- `‖𝔓‖_{Y_p → Y_p} ≤ 2 ‖𝔓‖_{L^p(R³;R³) → L^p(R³;R³)}`, a constant depending on `p` only. -/
theorem norm_lerayY_le_two (hp1 : 1 < p) (hp : p ≠ ⊤) :
    ‖lerayY P p hp1 hp‖ ≤ 2 * ‖lerayLp p hp1 hp‖ :=
  (norm_lerayY_le hp1 hp).trans (norm_lerayC_le hp1 hp)

/-- **Phase translation (B0414, B0429).** `𝔓` commutes with `f ↦ f(σ + ·)` on `Y_p` for every
phase shift `σ ∈ ℝ/Pℤ`. -/
theorem lerayY_phase (hp1 : 1 < p) (hp : p ≠ ⊤) (σ : AddCircle P) (f : Yq P p) :
    lerayY P p hp1 hp (DomAddAct.mk σ +ᵥ f) = DomAddAct.mk σ +ᵥ lerayY P p hp1 hp f :=
  compLpL_vadd (lerayC p hp1 hp) _ f

/-- The real-scalar restriction of `lerayY` is the slice-wise real operator. -/
theorem lerayY_restrictScalars (hp1 : 1 < p) (hp : p ≠ ⊤) :
    (lerayY P p hp1 hp).restrictScalars ℝ =
      ((lerayC p hp1 hp).restrictScalars ℝ).compLpL p (AddCircle.haarAddCircle (T := P)) := by
  ext1 f
  apply Lp.ext
  filter_upwards [coeFn_lerayY hp1 hp f,
    ((lerayC p hp1 hp).restrictScalars ℝ).coeFn_compLpL
      (μ := AddCircle.haarAddCircle (T := P)) (p := p) f] with x h1 h2
  rw [ContinuousLinearMap.coe_restrictScalars', h1, h2]
  rfl

/-- `𝔓` commutes on `Y_p` with every slice-wise operator `N` commuting with `𝔓` on
`L^p(R³;ℂ³)`. -/
theorem lerayY_comm_slicewise (hp1 : 1 < p) (hp : p ≠ ⊤)
    (N : Lp CVec3 p (volume : Measure Space) →L[ℝ] Lp CVec3 p (volume : Measure Space))
    (hN : ((lerayC p hp1 hp).restrictScalars ℝ).comp N =
      N.comp ((lerayC p hp1 hp).restrictScalars ℝ)) :
    ((lerayY P p hp1 hp).restrictScalars ℝ).comp (N.compLpL p AddCircle.haarAddCircle) =
      (N.compLpL p AddCircle.haarAddCircle).comp ((lerayY P p hp1 hp).restrictScalars ℝ) := by
  rw [lerayY_restrictScalars]
  exact compLpL_comm _ _ hN

/-- **Spatial heat on `Y_p` (B0414 (iv), B0429).** `𝔓` commutes with the heat semigroup
`e^{θΔ}` acting slice by slice on `Y_p`, for every heat time `θ`. -/
theorem lerayY_heat (hp1 : 1 < p) (hp : p ≠ ⊤) (θ : ℝ) :
    ((lerayY P p hp1 hp).restrictScalars ℝ).comp
        ((Heat.heatLp (AddMonoidHom.id Space) continuous_id θ :
          Lp CVec3 p (volume : Measure Space) →L[ℝ] Lp CVec3 p volume).compLpL p
          AddCircle.haarAddCircle) =
      ((Heat.heatLp (AddMonoidHom.id Space) continuous_id θ :
          Lp CVec3 p (volume : Measure Space) →L[ℝ] Lp CVec3 p volume).compLpL p
          AddCircle.haarAddCircle).comp ((lerayY P p hp1 hp).restrictScalars ℝ) :=
  lerayY_comm_slicewise hp1 hp _ (lerayC_heat hp1 hp θ)

end UnforcedLeray.RieszLp
