import UnforcedLeray.Lib.LerayC.Transfer
import UnforcedLeray.Units.B0420.Leray

/-!
# The `L^p` Leray projection commutes with isotropic dilations (INF01 T16)

Blueprint: INF01 target T16 (`lerayLp_dilate`) of


Manuscript: unit B0414 (`paper/main.tex` lines 7342–7343: "Its multiplier is homogeneous of
degree zero, so it commutes with spatial dilations"), unit B0429 (lines 3616–3618: `P`
"commutes with … isotropic dilation"), unit B0433 (lines 7550–7576: commutation with `T_0`,
whose spatial part `y·∇/2` generates the dilations).

* `dilateLp p hp hb`: the dilation `u ↦ u(b ·)` on `L^p(R³;R³)`, `b ≠ 0`, `p < ∞`, a bounded
  operator with `‖u(b·)‖_p = |b|^{-3/p} ‖u‖_p` (`norm_dilateLp_apply`);
* `lerayLp_dilate` (**T16**): `𝔓 D_b = D_b 𝔓` for every `b > 0`, `1 < p < ∞`.

Proof: no Fourier multiplier. On `L²` the orthogonal Leray projection commutes with
`f ↦ a f(b·)` (`B0420.projection_dilationL2`, `Units/B0420/Leray.lean`); the transfer
principle `lerayLp_comm_of_projection_comm` extends this to `L^p`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.RieszLp

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The dilation `u ↦ u(b ·)` on `L^p(R³;R³)`, as a linear map (`b ≠ 0`). -/
def dilateLpLin {b : ℝ} (hb : b ≠ 0) :
    Lp Space p (volume : Measure Space) →ₗ[ℝ] Lp Space p (volume : Measure Space) where
  toFun u := (SpatialScaling.memLp_comp_dilation (Lp.memLp u) hb).toLp (fun x => u (b • x))
  map_add' u v := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (SpatialScaling.ae_eq_comp_dilation (Lp.coeFn_add u v) hb)
  map_smul' c u := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (SpatialScaling.ae_eq_comp_dilation (Lp.coeFn_smul c u) hb)

variable {p}

theorem dilateLpLin_apply {b : ℝ} (hb : b ≠ 0) (u : Lp Space p (volume : Measure Space)) :
    dilateLpLin p hb u =
      (SpatialScaling.memLp_comp_dilation (Lp.memLp u) hb).toLp (fun x => u (b • x)) := rfl

/-- The Jacobian factor `|b|^{-3/p}` of the `L^p` dilation. -/
def dilateConst (p : ℝ≥0∞) (b : ℝ) : ℝ :=
  ((ENNReal.ofReal |(b ^ 3)⁻¹|) ^ (1 / p).toReal).toReal

theorem dilateConst_nonneg (b : ℝ) : 0 ≤ dilateConst p b := ENNReal.toReal_nonneg

/-- `‖u(b ·)‖_p = |b|^{-3/p} ‖u‖_p` for `p < ∞`. -/
theorem norm_dilateLpLin (hp : p ≠ ⊤) {b : ℝ} (hb : b ≠ 0)
    (u : Lp Space p (volume : Measure Space)) :
    ‖dilateLpLin p hb u‖ = dilateConst p b * ‖u‖ := by
  rw [dilateLpLin_apply, Lp.norm_toLp, B0418.eLpNorm_comp_dilation hp hb, ENNReal.toReal_mul,
    Lp.norm_def, dilateConst]

variable (p) in
/-- **INF01 T16.** The dilation `D_b u = u(b ·)` on `L^p(R³;R³)`, `b ≠ 0`, `p < ∞`, as a bounded
operator. -/
def dilateLp (hp : p ≠ ⊤) {b : ℝ} (hb : b ≠ 0) :
    Lp Space p (volume : Measure Space) →L[ℝ] Lp Space p (volume : Measure Space) :=
  LinearMap.mkContinuous (dilateLpLin p hb) (dilateConst p b)
    (fun u => (norm_dilateLpLin hp hb u).le)

theorem dilateLp_apply (hp : p ≠ ⊤) {b : ℝ} (hb : b ≠ 0)
    (u : Lp Space p (volume : Measure Space)) :
    dilateLp p hp hb u =
      (SpatialScaling.memLp_comp_dilation (Lp.memLp u) hb).toLp (fun x => u (b • x)) := rfl

theorem coeFn_dilateLp (hp : p ≠ ⊤) {b : ℝ} (hb : b ≠ 0)
    (u : Lp Space p (volume : Measure Space)) :
    (dilateLp p hp hb u : SpatialField) =ᵐ[volume] fun x => u (b • x) :=
  (SpatialScaling.memLp_comp_dilation (Lp.memLp u) hb).coeFn_toLp

theorem norm_dilateLp_apply (hp : p ≠ ⊤) {b : ℝ} (hb : b ≠ 0)
    (u : Lp Space p (volume : Measure Space)) :
    ‖dilateLp p hp hb u‖ = dilateConst p b * ‖u‖ :=
  norm_dilateLpLin hp hb u

/-- **INF01 T16 (dilations).** For `1 < p < ∞` and `b > 0`, the `L^p` Leray projection commutes
with the isotropic dilation `u ↦ u(b ·)` (B0414 (iii), `paper/main.tex` lines 7342–7343;
B0429, lines 3616–3618). -/
theorem lerayLp_dilate (hp1 : 1 < p) (hp : p ≠ ⊤) {b : ℝ} (hb : 0 < b) :
    (lerayLp p hp1 hp).comp (dilateLp p hp hb.ne') =
      (dilateLp p hp hb.ne').comp (lerayLp p hp1 hp) := by
  refine lerayLp_comp_eq_of_projection_comm hp1 hp _
    (B := ViscosityTransport.dilationL2 1 b) (fun u v huv => ?_)
    (fun v => B0420.projection_dilationL2 1 hb v)
  have hm := SpatialScaling.memLp_spatialScale (Lp.memLp v) 1 hb.ne'
  refine (coeFn_dilateLp hp hb.ne' u).trans ((SpatialScaling.ae_eq_comp_dilation huv hb.ne').trans ?_)
  refine (EventuallyEq.trans ?_ (coeFn_toL2 hm).symm)
  filter_upwards with x
  simp [SpatialScaling.spatialScale]

/-- Pointwise form of `lerayLp_dilate`. -/
theorem lerayLp_dilate_apply (hp1 : 1 < p) (hp : p ≠ ⊤) {b : ℝ} (hb : 0 < b)
    (F : Lp Space p (volume : Measure Space)) :
    lerayLp p hp1 hp (dilateLp p hp hb.ne' F) = dilateLp p hp hb.ne' (lerayLp p hp1 hp F) := by
  have h := congrArg (fun T : Lp Space p (volume : Measure Space) →L[ℝ]
    Lp Space p (volume : Measure Space) => T F) (lerayLp_dilate hp1 hp hb)
  simpa using h

end UnforcedLeray.RieszLp
