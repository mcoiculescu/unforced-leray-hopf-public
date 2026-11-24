import UnforcedLeray.Lib.LerayC.Dilate
import UnforcedLeray.Lib.LerayC.Phase

/-!
# Dilations of vector-valued `L^p` fields; the complex and phase Leray projections commute with
them (INF01 T16 for `ℂ³` and `Y_p`)

Blueprint: INF01 targets T16 (`lerayLp_dilate`) and T17 (`ℂ³` version, `lerayY`) of


Manuscript: unit B0414 (`paper/main.tex` lines 7336–7344: `P_σ` on `L^q(R³;ℂ³)` and `Y_q`
"commutes with spatial dilations"), unit B0429 (lines 3616–3618: `P` commutes with isotropic
dilation on `Y_p`).

* `dilateLpE p hp hb`: `u ↦ u(b ·)` on `L^p(R³;E)` for any normed space `E`, `b ≠ 0`, `p < ∞`,
  with `‖u(b·)‖_p = |b|^{-3/p}‖u‖_p` (`norm_dilateLpE_apply`); at `E = R³` it is `dilateLp`;
* `compLpL_dilateLpE`: pointwise linear maps commute with dilations;
* `lerayC_dilate`: `𝔓 D_b = D_b 𝔓` on `L^p(R³;ℂ³)`, `b > 0`;
* `lerayY_dilate`: the same on `Y_p`, the dilation acting slice by slice.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.RieszLp

open UnforcedLeray.PhaseSpace (CVec3 Yq)

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem memLp_comp_smul {f : Space → E} {r : ℝ≥0∞} (hf : MemLp f r volume) {b : ℝ}
    (hb : b ≠ 0) : MemLp (fun x : Space => f (b • x)) r volume := by
  apply (SpatialScaling.dilation_measurableEmbedding hb).memLp_map_measure_iff.mp
  rw [SpatialScaling.map_dilation hb]
  exact hf.smul_measure ENNReal.ofReal_ne_top

theorem ae_eq_comp_smul {f g : Space → E} (h : f =ᵐ[volume] g) {b : ℝ} (hb : b ≠ 0) :
    (fun x : Space => f (b • x)) =ᵐ[volume] (fun x => g (b • x)) := by
  apply ((SpatialScaling.dilation_measurableEmbedding hb).ae_map_iff
    (μ := (volume : Measure Space)) (p := fun x => f x = g x)).mp
  rw [SpatialScaling.map_dilation hb]
  exact Measure.ae_smul_measure h _

theorem eLpNorm_comp_smul {r : ℝ≥0∞} (hr : r ≠ ⊤) {b : ℝ} (hb : b ≠ 0) (u : Space → E) :
    eLpNorm (fun x : Space => u (b • x)) r volume =
      (ENNReal.ofReal |(b ^ 3)⁻¹|) ^ (1 / r).toReal * eLpNorm u r volume := by
  change eLpNorm (u ∘ fun x : Space => b • x) r volume = _
  rw [← (SpatialScaling.dilation_measurableEmbedding hb).eLpNorm_map_measure,
    SpatialScaling.map_dilation hb, eLpNorm_smul_measure_of_ne_top hr]
  rfl

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- The dilation `u ↦ u(b ·)` on `L^p(R³;E)`, linear part. -/
def dilateLpELin {b : ℝ} (hb : b ≠ 0) :
    Lp E p (volume : Measure Space) →ₗ[ℝ] Lp E p (volume : Measure Space) where
  toFun u := (memLp_comp_smul (Lp.memLp u) hb).toLp (fun x => u (b • x))
  map_add' u v := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (ae_eq_comp_smul (Lp.coeFn_add u v) hb)
  map_smul' c u := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (ae_eq_comp_smul (Lp.coeFn_smul c u) hb)

theorem norm_dilateLpELin (hp : p ≠ ⊤) {b : ℝ} (hb : b ≠ 0)
    (u : Lp E p (volume : Measure Space)) :
    ‖dilateLpELin p hb u‖ = dilateConst p b * ‖u‖ := by
  change ‖(memLp_comp_smul (Lp.memLp u) hb).toLp (fun x => u (b • x))‖ = _
  rw [Lp.norm_toLp, eLpNorm_comp_smul hp hb, ENNReal.toReal_mul, Lp.norm_def, dilateConst]

variable (E p) in
/-- **INF01 T16.** The dilation `D_b u = u(b ·)` on `L^p(R³;E)`, `b ≠ 0`, `p < ∞`. -/
def dilateLpE (hp : p ≠ ⊤) {b : ℝ} (hb : b ≠ 0) :
    Lp E p (volume : Measure Space) →L[ℝ] Lp E p (volume : Measure Space) :=
  LinearMap.mkContinuous (dilateLpELin p hb) (dilateConst p b)
    (fun u => (norm_dilateLpELin hp hb u).le)

theorem coeFn_dilateLpE (hp : p ≠ ⊤) {b : ℝ} (hb : b ≠ 0)
    (u : Lp E p (volume : Measure Space)) :
    (dilateLpE E p hp hb u : Space → E) =ᵐ[volume] fun x => u (b • x) :=
  (memLp_comp_smul (Lp.memLp u) hb).coeFn_toLp

theorem norm_dilateLpE_apply (hp : p ≠ ⊤) {b : ℝ} (hb : b ≠ 0)
    (u : Lp E p (volume : Measure Space)) :
    ‖dilateLpE E p hp hb u‖ = dilateConst p b * ‖u‖ :=
  norm_dilateLpELin hp hb u

/-- At `E = R³`, `dilateLpE` is `dilateLp`. -/
theorem dilateLpE_space (hp : p ≠ ⊤) {b : ℝ} (hb : b ≠ 0) :
    dilateLpE Space p hp hb = dilateLp p hp hb := by
  ext1 u
  apply Lp.ext
  exact (coeFn_dilateLpE hp hb u).trans (coeFn_dilateLp hp hb u).symm

/-- Pointwise linear maps commute with dilations. -/
theorem compLpL_dilateLpE {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    (hp : p ≠ ⊤) {b : ℝ} (hb : b ≠ 0) (u : Lp E p (volume : Measure Space)) :
    L.compLpL p volume (dilateLpE E p hp hb u) = dilateLpE F p hp hb (L.compLpL p volume u) := by
  apply Lp.ext
  have h1 := L.coeFn_compLpL (μ := volume) (p := p) (dilateLpE E p hp hb u)
  have h2 := coeFn_dilateLpE hp hb u
  have h3 := coeFn_dilateLpE hp hb (L.compLpL p volume u)
  have h4 := ae_eq_comp_smul (L.coeFn_compLpL (μ := volume) (p := p) u) hb
  refine h1.trans (EventuallyEq.trans ?_ (h3.trans h4).symm)
  filter_upwards [h2] with x hx
  rw [hx]

end General

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

set_option maxHeartbeats 800000 in
/-- **INF01 T16 for `ℂ³` (dilations).** For `1 < p < ∞` and `b > 0`, the complex Leray projection
commutes with `u ↦ u(b ·)` on `L^p(R³;ℂ³)` (B0414 (iii), `paper/main.tex` lines 7342–7343). -/
theorem lerayC_dilate (hp1 : 1 < p) (hp : p ≠ ⊤) {b : ℝ} (hb : 0 < b) :
    ((lerayC p hp1 hp).restrictScalars ℝ).comp (dilateLpE CVec3 p hp hb.ne') =
      (dilateLpE CVec3 p hp hb.ne').comp ((lerayC p hp1 hp).restrictScalars ℝ) := by
  ext1 F
  change lerayC p hp1 hp (dilateLpE CVec3 p hp hb.ne' F) =
    dilateLpE CVec3 p hp hb.ne' (lerayC p hp1 hp F)
  rw [lerayC_apply, lerayC_apply, compLpL_dilateLpE reV hp hb.ne',
    compLpL_dilateLpE imV hp hb.ne', dilateLpE_space hp hb.ne',
    lerayLp_dilate_apply hp1 hp hb, lerayLp_dilate_apply hp1 hp hb,
    ← dilateLpE_space hp hb.ne', compLpL_dilateLpE ofReV hp hb.ne',
    compLpL_dilateLpE ofImV hp hb.ne', (dilateLpE CVec3 p hp hb.ne').map_add]

/-- **Isotropic dilation on `Y_p` (B0429, `paper/main.tex` lines 3616–3618).** The phase Leray
projection commutes with the dilation `f(τ) ↦ f(τ)(b ·)`, `b > 0`, acting slice by slice. -/
theorem lerayY_dilate {P : ℝ} [Fact (0 < P)] (hp1 : 1 < p) (hp : p ≠ ⊤) {b : ℝ} (hb : 0 < b) :
    ((lerayY P p hp1 hp).restrictScalars ℝ).comp
        ((dilateLpE CVec3 p hp hb.ne').compLpL p AddCircle.haarAddCircle) =
      ((dilateLpE CVec3 p hp hb.ne').compLpL p AddCircle.haarAddCircle).comp
        ((lerayY P p hp1 hp).restrictScalars ℝ) :=
  lerayY_comm_slicewise hp1 hp _ (lerayC_dilate hp1 hp hb)

end UnforcedLeray.RieszLp
