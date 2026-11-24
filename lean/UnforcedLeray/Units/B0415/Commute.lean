import UnforcedLeray.Units.B0415.Action
import UnforcedLeray.Units.B0414

/-!
# Unit B0415, helper: rotation, reflection and phase translation commute with spatial dilation,
heat evolution and Leray projection (claim (iii))

Blueprint unit `B0415` (`eq:free-stress-2`, `paper/main.tex` lines 7358–7360: "Rotation,
reflection, and phase translation commute with spatial dilation, heat evolution, and Leray
projection"). The operators are those of unit B0414 (`Units/B0414.lean`): the Leray projection
`RieszLp.lerayY P q` on `Y_q`, the heat semigroup `Heat.heatLp _ _ θ` slice by slice, the
dilation `u ↦ u(b ·)` (`RieszLp.dilateLpE`) slice by slice, and the phase translation
`f ↦ f(σ + ·)` (`DomAddAct.mk σ +ᵥ f`).

* `heatConv_isometry`: the Gaussian average commutes with `u ↦ A u(g⁻¹·)` for every linear
  isometry `g` of `ℝ³` and every invertible linear `A` (the Gaussian kernel is radial);
* `heatLp_actLp`, `dilateLpE_actLp` on `L^q(ℝ³;ℂ³)`; `heatY_actY`, `dilY_actY`, `lerayY_actY`
  on `Y_q` for every linear isometry `g` (in particular rotations `R_θ` and the reflection `J`);
* `phase_actY`, `phase_heatY`, `phase_dilY`, `phase_lerayY`: the phase translation commutes with
  all of them.

The heat operator `Heat.heatLp _ _ θ` is `e^{θΔ}` for `θ > 0` and the identity for `θ ≤ 0`
(`Lib/HeatR3/LpOp.lean`); the commutation is stated for every `θ`, trivially so for `θ ≤ 0`.
The amplitude factor of the manuscript's dilations is a scalar and commutes with the
complex-linear `actY` trivially; only `u ↦ u(b ·)` is stated, as in B0414.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.B0415

open UnforcedLeray.PhaseSpace (CVec3 Yq)
open UnforcedLeray.Gaussian (gaussKernel)

/-! ### The heat average is `O(3)`-equivariant -/

/-- The Gaussian kernel is invariant under linear isometries. -/
theorem gaussKernel_isometry (g : Space ≃ₗᵢ[ℝ] Space) (θ : ℝ) (z : Space) :
    gaussKernel 3 θ (g z) = gaussKernel 3 θ z := by
  simp only [gaussKernel, g.norm_map]

/-- **Heat equivariance (pointwise).** For a linear isometry `g` of `ℝ³` and an invertible
linear map `A`, `e^{θΔ}[A u(g⁻¹·)](x) = A (e^{θΔ}u)(g⁻¹x)` for every `x` (the Gaussian average
`Heat.heatConv`, every `θ`). -/
theorem heatConv_isometry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : Space ≃ₗᵢ[ℝ] Space) (A : E ≃L[ℝ] E) (θ : ℝ) (u : Space → E) (x : Space) :
    Heat.heatConv (AddMonoidHom.id Space) θ (fun y => A (u (g.symm y))) x =
      A (Heat.heatConv (AddMonoidHom.id Space) θ u (g.symm x)) := by
  simp only [Heat.heatConv, AddMonoidHom.id_apply]
  rw [← A.integral_comp_comm]
  have hmp : MeasurePreserving (g : Space → Space) volume volume := g.measurePreserving
  have h := hmp.integral_comp g.toHomeomorph.measurableEmbedding
    (fun y : Space => gaussKernel 3 θ y • A (u (g.symm (x - y))))
  rw [← h]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [gaussKernel_isometry, map_sub, LinearIsometryEquiv.symm_apply_apply, map_smul]

/-- `actV g` as a continuous linear equivalence (its inverse is `actV g⁻¹`). -/
def actVEquiv (g : Space ≃ₗᵢ[ℝ] Space) : CVec3 ≃L[ℝ] CVec3 :=
  ContinuousLinearEquiv.equivOfInverse ((actV g).restrictScalars ℝ)
    ((actV g.symm).restrictScalars ℝ)
    (fun z => by
      change actV g.symm (actV g z) = z
      rw [← actV_trans, LinearIsometryEquiv.self_trans_symm, actV_refl])
    (fun z => by
      change actV g (actV g.symm z) = z
      rw [← actV_trans, LinearIsometryEquiv.symm_trans_self, actV_refl])

theorem actVEquiv_apply (g : Space ≃ₗᵢ[ℝ] Space) (z : CVec3) : actVEquiv g z = actV g z := rfl

section LpEq

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- **Heat equivariance on `L^q(ℝ³;ℂ³)`.** `e^{θΔ}(g·F) = g·(e^{θΔ}F)` for every linear
isometry `g` and every `θ`. -/
theorem heatLp_actLp (g : Space ≃ₗᵢ[ℝ] Space) (θ : ℝ) (F : Lp CVec3 q (volume : Measure Space)) :
    Heat.heatLp (AddMonoidHom.id Space) continuous_id θ (actLp q g F) =
      actLp q g (Heat.heatLp (AddMonoidHom.id Space) continuous_id θ F) := by
  by_cases hθ : 0 < θ
  · apply Lp.ext
    have h1 := Heat.heatLp_rep (μ := (volume : Measure Space)) (AddMonoidHom.id Space)
      continuous_id hθ (actLp q g F)
    have h2 := Heat.heatConv_congr_ae (μ := (volume : Measure Space)) (AddMonoidHom.id Space)
      measurable_id θ (coeFn_actLp g F)
    have h3 := coeFn_actLp g (Heat.heatLp (AddMonoidHom.id Space) continuous_id θ F)
    have h4 := g.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp
      (Heat.heatLp_rep (μ := (volume : Measure Space)) (AddMonoidHom.id Space) continuous_id hθ F)
    refine h1.trans (h2.trans ?_)
    refine EventuallyEq.trans ?_ h3.symm
    filter_upwards [h4] with x hx
    simp only [Function.comp_apply] at hx
    rw [hx]
    exact heatConv_isometry g (actVEquiv g) θ F x
  · rw [Heat.heatLp_of_nonpos _ _ (not_lt.mp hθ)]
    rfl

/-- **Dilation equivariance on `L^q(ℝ³;ℂ³)`.** `D_b(g·F) = g·(D_bF)`, `D_bF = F(b ·)`, for every
linear isometry `g` (`q < ∞`, `b ≠ 0`). -/
theorem dilateLpE_actLp (hq : q ≠ ⊤) {b : ℝ} (hb : b ≠ 0) (g : Space ≃ₗᵢ[ℝ] Space)
    (F : Lp CVec3 q (volume : Measure Space)) :
    RieszLp.dilateLpE CVec3 q hq hb (actLp q g F) =
      actLp q g (RieszLp.dilateLpE CVec3 q hq hb F) := by
  apply Lp.ext
  have h1 := RieszLp.coeFn_dilateLpE hq hb (actLp q g F)
  have h2 := RieszLp.ae_eq_comp_smul (coeFn_actLp g F) hb
  have h3 := coeFn_actLp g (RieszLp.dilateLpE CVec3 q hq hb F)
  have h4 := g.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (RieszLp.coeFn_dilateLpE hq hb F)
  refine h1.trans (h2.trans ?_)
  refine EventuallyEq.trans ?_ h3.symm
  filter_upwards [h4] with x hx
  simp only [Function.comp_apply] at hx
  rw [hx, map_smul]

end LpEq

/-! ### The operators on `Y_q` -/

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

variable (P q) in
/-- The heat semigroup `e^{θΔ}` on `Y_q`, slice by slice (the operator of B0414 (iv)). -/
def heatY (θ : ℝ) : Yq P q →L[ℝ] Yq P q :=
  (Heat.heatLp (AddMonoidHom.id Space) continuous_id θ :
    Lp CVec3 q (volume : Measure Space) →L[ℝ] Lp CVec3 q volume).compLpL q
    AddCircle.haarAddCircle

variable (P) in
/-- The spatial dilation `w(τ) ↦ w(τ)(b ·)` on `Y_q`, slice by slice (B0414 (iii)). -/
def dilY (hq : q ≠ ⊤) {b : ℝ} (hb : b ≠ 0) : Yq P q →L[ℝ] Yq P q :=
  (RieszLp.dilateLpE CVec3 q hq hb).compLpL q AddCircle.haarAddCircle

/-- The phase translation `w ↦ w(σ + ·)` on `Y_q` (B0414 (iv)). -/
def phaseY (σ : AddCircle P) (w : Yq P q) : Yq P q := DomAddAct.mk σ +ᵥ w

set_option maxHeartbeats 1600000 in
/-- Slice-wise transfer: a slice operator commuting with `actLp q g` commutes on `Y_q` with
`actY P q g`. -/
theorem actY_comm_slicewise (g : Space ≃ₗᵢ[ℝ] Space)
    (N : Lp CVec3 q (volume : Measure Space) →L[ℝ] Lp CVec3 q (volume : Measure Space))
    (hN : ∀ F, N (actLp q g F) = actLp q g (N F)) (w : Yq P q) :
    N.compLpL q AddCircle.haarAddCircle (actY P q g w) =
      actY P q g (N.compLpL q AddCircle.haarAddCircle w) := by
  apply Lp.ext
  have h1 := N.coeFn_compLpL (μ := AddCircle.haarAddCircle (T := P)) (p := q) (actY P q g w)
  have h2 := coeFn_actY g w
  have h3 := coeFn_actY g (N.compLpL q AddCircle.haarAddCircle w)
  have h4 := N.coeFn_compLpL (μ := AddCircle.haarAddCircle (T := P)) (p := q) w
  filter_upwards [h1, h2, h3, h4] with τ e1 e2 e3 e4
  rw [e1, e2, e3, e4, hN]

/-- **(iii), heat.** Rotations and the reflection (every linear isometry `g`) commute with the
heat evolution on `Y_q`: `e^{θΔ}(g·w) = g·(e^{θΔ}w)`. -/
theorem heatY_actY (g : Space ≃ₗᵢ[ℝ] Space) (θ : ℝ) (w : Yq P q) :
    heatY P q θ (actY P q g w) = actY P q g (heatY P q θ w) :=
  actY_comm_slicewise g _ (heatLp_actLp g θ) w

/-- **(iii), dilation.** Rotations and the reflection commute with the spatial dilation on
`Y_q`: `D_b(g·w) = g·(D_b w)`. -/
theorem dilY_actY (hq : q ≠ ⊤) {b : ℝ} (hb : b ≠ 0) (g : Space ≃ₗᵢ[ℝ] Space) (w : Yq P q) :
    dilY P hq hb (actY P q g w) = actY P q g (dilY P hq hb w) :=
  actY_comm_slicewise g _ (dilateLpE_actLp hq hb g) w

/-- **(iii), Leray.** Rotations and the reflection commute with the Leray projection on `Y_q`,
`1 < q < ∞`: `P_σ(g·w) = g·(P_σw)` (from `RieszLp.lerayY_isometry`). -/
theorem lerayY_actY (hq1 : 1 < q) (hq : q ≠ ⊤) (g : Space ≃ₗᵢ[ℝ] Space) (w : Yq P q) :
    RieszLp.lerayY P q hq1 hq (actY P q g w) = actY P q g (RieszLp.lerayY P q hq1 hq w) := by
  apply Lp.ext
  have h1 := RieszLp.coeFn_lerayY (P := P) hq1 hq (actY P q g w)
  have h2 := coeFn_actY g w
  have h3 := coeFn_actY g (RieszLp.lerayY P q hq1 hq w)
  have h4 := RieszLp.coeFn_lerayY (P := P) hq1 hq w
  filter_upwards [h1, h2, h3, h4] with τ e1 e2 e3 e4
  rw [e1, e2, e3, e4, actLp_eq_rotLpC, actLp_eq_rotLpC, RieszLp.lerayC_isometry]

/-- **(iii), phase translation and rotation/reflection** commute on `Y_q`. -/
theorem phaseY_actY (σ : AddCircle P) (g : Space ≃ₗᵢ[ℝ] Space) (w : Yq P q) :
    phaseY σ (actY P q g w) = actY P q g (phaseY σ w) :=
  (RieszLp.compLpL_vadd (actLp q g) (DomAddAct.mk σ) w).symm

/-- **(iii), phase translation and heat** commute on `Y_q`. -/
theorem phaseY_heatY (σ : AddCircle P) (θ : ℝ) (w : Yq P q) :
    phaseY σ (heatY P q θ w) = heatY P q θ (phaseY σ w) :=
  (RieszLp.compLpL_vadd _ (DomAddAct.mk σ) w).symm

/-- **(iii), phase translation and dilation** commute on `Y_q`. -/
theorem phaseY_dilY (hq : q ≠ ⊤) {b : ℝ} (hb : b ≠ 0) (σ : AddCircle P) (w : Yq P q) :
    phaseY σ (dilY P hq hb w) = dilY P hq hb (phaseY σ w) :=
  (RieszLp.compLpL_vadd _ (DomAddAct.mk σ) w).symm

/-- **(iii), phase translation and Leray** commute on `Y_q` (B0414 (iv),
`RieszLp.lerayY_phase`). -/
theorem phaseY_lerayY (hq1 : 1 < q) (hq : q ≠ ⊤) (σ : AddCircle P) (w : Yq P q) :
    phaseY σ (RieszLp.lerayY P q hq1 hq w) = RieszLp.lerayY P q hq1 hq (phaseY σ w) :=
  (RieszLp.lerayY_phase hq1 hq σ w).symm

end UnforcedLeray.B0415
