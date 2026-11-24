import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3
import UnforcedLeray.Lib.Kernels.IterApply
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue

/-!
# `PartII-b:S3/1` decomposition (`Sub/PartII-b_S3_1.lean`, SP 2559-2562)

Source of record: `the November 2 reference manuscript`
(SP), lines 2519-2523 and 2559-2562:
"The projected equation is $A_0 U + \mathbb{P}(U \cdot \nabla U) = 0$ with zero residual. ...
On positive physical-time compact intervals the resulting $C_\tau W^{k,4}$ regularity and the
projected equation give all time derivatives, so $U$ is jointly smooth through the axis."

## Proved here (zero `sorry`)

1. `dirSpatialJet F ws` and `JointSmoothSub` spacetime calculus:
   - `JointSmoothSub.contDiff_infty_dirSpatialJet`, `JointSmoothSub.differentiable_dirSpatialJet`,
     `JointSmoothSub.norm_iteratedFDeriv_dirSpatialJet_le`, `JointSmoothSub.norm_dirSpatialJet_le`,
     `JointSmoothSub.contDiff_infty_bgField_slice`;
   - `JointSmoothSub.continuous_of_hasDerivAt_fst_bounded`: any map `F : ℝ × Space → Space` with
     continuous spatial slices and a globally bounded 1D `τ`-derivative `P` is jointly continuous on
     `ℝ × Space` (via the Mean Value Theorem `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`);
   - `JointSmoothSub.hasFDerivAt_spacetimeJetCLM_of_hasDerivAt_fst`: any map `F : ℝ × Space → Space`
     with a jointly continuous 1D `τ`-derivative `P` and differentiable spatial slices has joint
     spacetime Fréchet derivative `spacetimeJetCLM (P p) (fderiv ℝ (fun y => F (p.1, y)) p.2)` at `p`;
   - `JointSmoothSub.hasPhaseDerivJet_of_hasPhaseDerivTower`,
     `JointSmoothSub.contDiff_nat_dirSpatialJet_of_hasPhaseDerivJet`,
     `JointSmoothSub.contDiff_infty_of_hasPhaseDerivJet`,
     `JointSmoothSub.contDiff_infty_of_hasPhaseDerivTower`, and
     `JointSmoothSub.hasPhaseDerivTower_of_uniformSmoothL4`: induction on the regularity order `n : ℕ`
     (via `contDiff_succ_iff_fderiv` and `contDiff_clm_apply_iff`) upgrading a 1D phase-derivative
     tower `HasPhaseDerivTower U₀ U` to joint smoothness `ContDiff ℝ ∞ (fun x : ℝ × Space => U₀ x.1 x.2)`.
2. `jointSmoothnessFromSpatialAllOrders_of`: conditional assembly of
   `JointSmoothnessFromSpatialAllOrders` (`PartII-b:S3/1`) from:
   - `BgFirstOrderPhaseDeriv` (`PartII-b:S3/1/1`, SP 2519-2523, 2559-2562): weak-to-strong classical
     first-order 1D `τ`-derivative `U₁ = ∂_τ U` of `bgField p z` and its spatial directional jets;
   - `BgHigherOrderPhaseDerivTower` (`PartII-b:S3/1/2`, SP 2519-2523, 2559-2562): inductive
     higher-order 1D `τ`-derivative tower `U : ℕ → ℝ → SpatialField` (`U_m = ∂_τ^m U`) from the
     projected evolution and uniform `W^{k,4} ∩ W^{k,∞}` slice bounds.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.Blueprint

/-! ## 1. Iterated spatial directional jets on `Space` -/

/-- Iterated spatial directional derivative of a spatial vector field `F : SpatialField` along a
list of directions `ws : List Space`. -/
def dirSpatialJet (F : SpatialField) : List Space → SpatialField
  | [] => F
  | w :: ws => fun y => fderiv ℝ (dirSpatialJet F ws) y w

@[simp]
theorem dirSpatialJet_nil (F : SpatialField) :
    dirSpatialJet F [] = F := rfl

@[simp]
theorem dirSpatialJet_cons (F : SpatialField) (w : Space) (ws : List Space) (y : Space) :
    dirSpatialJet F (w :: ws) y = fderiv ℝ (dirSpatialJet F ws) y w := rfl

/-- Uniform spatial `C^∞`, bounded iterated Fréchet derivatives, and `W^{k,4}(Space)` regularity of
a phase-indexed spatial field `V : ℝ → SpatialField`. -/
structure IsUniformSmoothL4SliceFamily (V : ℝ → SpatialField) : Prop where
  slice_contDiff : ∀ (k : ℕ) (τ : ℝ), ContDiff ℝ k (V τ)
  iteratedFDeriv_bounded :
    ∀ k : ℕ, ∃ M : ℝ, ∀ (τ : ℝ) (y : Space), ‖iteratedFDeriv ℝ k (V τ) y‖ ≤ M
  l4_bounded :
    ∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ,
      eLpNorm (fun y => iteratedFDeriv ℝ k (V τ) y) 4 volume ≤ ENNReal.ofReal M

namespace JointSmoothSub

/-- If `F : SpatialField` is smooth (`ContDiff ℝ ∞`), then every iterated spatial directional
derivative `dirSpatialJet F ws` is smooth (`ContDiff ℝ ∞`). -/
theorem contDiff_infty_dirSpatialJet {F : SpatialField} (hF : ContDiff ℝ ∞ F) :
    ∀ ws : List Space, ContDiff ℝ ∞ (dirSpatialJet F ws)
  | [] => hF
  | w :: ws => by
      change ContDiff ℝ ∞ (fun y : Space => fderiv ℝ (dirSpatialJet F ws) y w)
      exact ((contDiff_infty_iff_fderiv.1 (contDiff_infty_dirSpatialJet hF ws)).2).clm_apply
        contDiff_const

/-- If `F : SpatialField` is smooth (`ContDiff ℝ ∞`), then every iterated spatial directional
derivative `dirSpatialJet F ws` is differentiable on `Space`. -/
theorem differentiable_dirSpatialJet {F : SpatialField} (hF : ContDiff ℝ ∞ F)
    (ws : List Space) :
    Differentiable ℝ (dirSpatialJet F ws) :=
  (contDiff_infty_iff_fderiv.1 (contDiff_infty_dirSpatialJet hF ws)).1

/-- If `F : SpatialField` is smooth (`ContDiff ℝ ∞`), then every iterated spatial directional
derivative `dirSpatialJet F ws` is continuous on `Space`. -/
theorem continuous_dirSpatialJet_of_contDiff_infty {F : SpatialField} (hF : ContDiff ℝ ∞ F)
    (ws : List Space) :
    Continuous (dirSpatialJet F ws) :=
  (contDiff_infty_dirSpatialJet hF ws).continuous

/-- Norm bound for the `j`-th spatial Fréchet derivative of an iterated directional jet
`dirSpatialJet F ws` in terms of `‖iteratedFDeriv ℝ (j + ws.length) F y‖` and `(ws.map norm).prod`. -/
theorem norm_iteratedFDeriv_dirSpatialJet_le {F : SpatialField} (hF : ContDiff ℝ ∞ F) :
    ∀ (ws : List Space) (j : ℕ) (y : Space),
      ‖iteratedFDeriv ℝ j (dirSpatialJet F ws) y‖ ≤
        ‖iteratedFDeriv ℝ (j + ws.length) F y‖ * (ws.map norm).prod
  | [], j, y => by
      simp
  | w :: ws, j, y => by
      have hfun : dirSpatialJet F (w :: ws) =
          (ContinuousLinearMap.apply ℝ Space w) ∘ (fderiv ℝ (dirSpatialJet F ws)) := rfl
      rw [hfun]
      have hws : ContDiff ℝ ∞ (dirSpatialJet F ws) := contDiff_infty_dirSpatialJet hF ws
      have hfws : ContDiffAt ℝ ∞ (fderiv ℝ (dirSpatialJet F ws)) y :=
        (hws.contDiffAt).fderiv_right UnforcedLeray.Kernels.infty_add_one_le
      have hap : ‖ContinuousLinearMap.apply ℝ Space w‖ ≤ ‖w‖ :=
        ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun L => by
          simpa [mul_comm] using L.le_opNorm w
      calc ‖iteratedFDeriv ℝ j ((ContinuousLinearMap.apply ℝ Space w) ∘
            (fderiv ℝ (dirSpatialJet F ws))) y‖
          ≤ ‖ContinuousLinearMap.apply ℝ Space w‖ *
            ‖iteratedFDeriv ℝ j (fderiv ℝ (dirSpatialJet F ws)) y‖ :=
            ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ hfws (by exact_mod_cast le_top)
        _ ≤ ‖w‖ * (‖iteratedFDeriv ℝ (j + 1 + ws.length) F y‖ * (ws.map norm).prod) := by
            gcongr
            rw [norm_iteratedFDeriv_fderiv]
            exact norm_iteratedFDeriv_dirSpatialJet_le hF ws (j + 1) y
        _ = ‖iteratedFDeriv ℝ (j + (w :: ws).length) F y‖ * ((w :: ws).map norm).prod := by
            simp only [List.length_cons, List.map_cons, List.prod_cons]
            rw [show j + 1 + ws.length = j + (ws.length + 1) by omega]
            ring

/-- Pointwise bound on `dirSpatialJet F ws y` by `‖iteratedFDeriv ℝ ws.length F y‖` times the
product of direction norms `(ws.map norm).prod`. -/
theorem norm_dirSpatialJet_le {F : SpatialField} (hF : ContDiff ℝ ∞ F)
    (ws : List Space) (y : Space) :
    ‖dirSpatialJet F ws y‖ ≤ ‖iteratedFDeriv ℝ ws.length F y‖ * (ws.map norm).prod := by
  have h0 := norm_iteratedFDeriv_dirSpatialJet_le hF ws 0 y
  rw [norm_iteratedFDeriv_zero, zero_add] at h0
  exact h0

/-- From the all-order spatial slice hypothesis of `StrongAllOrders`, every phase slice
`bgField p z τ` is `ContDiff ℝ ∞` on `Space`. -/
theorem contDiff_infty_bgField_slice {p : Params} {z : p.Z}
    (hSlice : ∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ, ContDiff ℝ k (bgField p z τ) ∧
      (∀ y : Space, ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ M) ∧
      eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal M)
    (τ : ℝ) :
    ContDiff ℝ ∞ (bgField p z τ) :=
  contDiff_infty.2 fun k => (hSlice k).choose_spec τ |>.1

/-- Every iterated spatial directional derivative of `bgField p z τ` is `ContDiff ℝ ∞` on `Space`. -/
theorem contDiff_infty_dirSpatialJet_bgField_slice {p : Params} {z : p.Z}
    (hSlice : ∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ, ContDiff ℝ k (bgField p z τ) ∧
      (∀ y : Space, ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ M) ∧
      eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal M)
    (τ : ℝ) (ws : List Space) :
    ContDiff ℝ ∞ (dirSpatialJet (bgField p z τ) ws) :=
  contDiff_infty_dirSpatialJet (contDiff_infty_bgField_slice hSlice τ) ws

/-! ## 2. Partial-to-joint spacetime calculus on `ℝ × Space` -/

/-- The spacetime linear map `(v.1, v.2) ↦ v.1 • dt + dy v.2` on `ℝ × Space`. -/
def spacetimeJetCLM (dt : Space) (dy : Space →L[ℝ] Space) : (ℝ × Space) →L[ℝ] Space :=
  (ContinuousLinearMap.fst ℝ ℝ Space).smulRight dt +
    dy.comp (ContinuousLinearMap.snd ℝ ℝ Space)

@[simp]
theorem spacetimeJetCLM_apply (dt : Space) (dy : Space →L[ℝ] Space) (v : ℝ × Space) :
    spacetimeJetCLM dt dy v = v.1 • dt + dy v.2 := rfl

/-- If `F : ℝ × Space → Space` has continuous spatial slices `y ↦ F (τ, y)` and a locally-in-time
bounded 1D phase derivative `P : ℝ × Space → Space` (`HasDerivAt (fun τ => F (τ, y)) (P (τ, y)) τ`),
then `F` is jointly continuous on `ℝ × Space`. -/
theorem continuous_of_hasDerivAt_fst_locally_bounded {F P : ℝ × Space → Space}
    (hτ : ∀ x : ℝ × Space, HasDerivAt (fun τ : ℝ => F (τ, x.2)) (P x) x.1)
    (hy : ∀ τ : ℝ, Continuous (fun y : Space => F (τ, y)))
    (hP : ∀ τ₀ : ℝ, ∃ M : ℝ, ∀ x : ℝ × Space, dist x.1 τ₀ ≤ 1 → ‖P x‖ ≤ M) :
    Continuous F := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨M, hM⟩ := hP p.1
  set L : ℝ := max M 0 + 1
  have hLpos : 0 < L := by positivity
  have hML : ∀ x : ℝ × Space, dist x.1 p.1 ≤ 1 → ‖P x‖ ≤ L := fun x hx =>
    le_trans (hM x hx) (le_trans (le_max_left M 0) (le_add_of_nonneg_right zero_le_one))
  obtain ⟨δy, hδy, hyδ⟩ := Metric.continuousAt_iff.1 (hy p.1).continuousAt (ε / 2) (half_pos hε)
  set δ : ℝ := min 1 (min δy ((ε / 2) / L))
  have hδpos : 0 < δ := lt_min zero_lt_one (lt_min hδy (div_pos (half_pos hε) hLpos))
  refine ⟨δ, hδpos, fun q hq => ?_⟩
  have hqp : max (dist q.1 p.1) (dist q.2 p.2) < δ := by rwa [← Prod.dist_eq]
  have hq1 : dist q.1 p.1 < δ := (max_lt_iff.1 hqp).1
  have hq2 : dist q.2 p.2 < δ := (max_lt_iff.1 hqp).2
  have hstep : ∀ s ∈ Metric.closedBall p.1 1,
      HasDerivWithinAt (fun τ : ℝ => F (τ, q.2)) (P (s, q.2)) (Metric.closedBall p.1 1) s :=
    fun s _ => (hτ (s, q.2)).hasDerivWithinAt
  have hbnd : ∀ s ∈ Metric.closedBall p.1 1, ‖P (s, q.2)‖ ≤ L :=
    fun s hs => hML (s, q.2) (Metric.mem_closedBall.1 hs)
  have hq1_ball : q.1 ∈ Metric.closedBall p.1 1 :=
    Metric.mem_closedBall.2 (le_of_lt (lt_of_lt_of_le hq1 (min_le_left _ _)))
  have e1 := (convex_closedBall p.1 1).norm_image_sub_le_of_norm_hasDerivWithin_le hstep hbnd
    (Metric.mem_closedBall_self zero_le_one) hq1_ball
  have e1' : ‖F (q.1, q.2) - F (p.1, q.2)‖ < ε / 2 := by
    have h1 : ‖q.1 - p.1‖ < (ε / 2) / L := by
      rw [← dist_eq_norm]
      exact lt_of_lt_of_le hq1 (le_trans (min_le_right _ _) (min_le_right _ _))
    calc ‖F (q.1, q.2) - F (p.1, q.2)‖
        ≤ L * ‖q.1 - p.1‖ := e1
      _ < L * ((ε / 2) / L) := mul_lt_mul_of_pos_left h1 hLpos
      _ = ε / 2 := mul_div_cancel₀ (ε / 2) (ne_of_gt hLpos)
  have e2' : ‖F (p.1, q.2) - F (p.1, p.2)‖ < ε / 2 := by
    rw [← dist_eq_norm]
    exact hyδ (lt_of_lt_of_le hq2 (le_trans (min_le_right _ _) (min_le_left _ _)))
  rw [dist_eq_norm]
  have hdecomp : F q - F p = (F (q.1, q.2) - F (p.1, q.2)) + (F (p.1, q.2) - F (p.1, p.2)) := by
    simp
  rw [hdecomp]
  calc ‖(F (q.1, q.2) - F (p.1, q.2)) + (F (p.1, q.2) - F (p.1, p.2))‖
      ≤ ‖F (q.1, q.2) - F (p.1, q.2)‖ + ‖F (p.1, q.2) - F (p.1, p.2)‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add e1' e2'
    _ = ε := add_halves ε

/-- If `F : ℝ × Space → Space` has continuous spatial slices `y ↦ F (τ, y)` and a globally bounded
1D phase derivative `P : ℝ × Space → Space` (`HasDerivAt (fun τ => F (τ, y)) (P (τ, y)) τ`), then
`F` is jointly continuous on `ℝ × Space`. -/
theorem continuous_of_hasDerivAt_fst_bounded {F P : ℝ × Space → Space}
    (hτ : ∀ x : ℝ × Space, HasDerivAt (fun τ : ℝ => F (τ, x.2)) (P x) x.1)
    (hy : ∀ τ : ℝ, Continuous (fun y : Space => F (τ, y)))
    (hP : ∃ M : ℝ, ∀ x : ℝ × Space, ‖P x‖ ≤ M) :
    Continuous F := by
  obtain ⟨M, hM⟩ := hP
  exact continuous_of_hasDerivAt_fst_locally_bounded hτ hy fun _ => ⟨M, fun x _ => hM x⟩

/-- If `F : ℝ × Space → Space` has a 1D phase derivative `P : ℝ × Space → Space` that is jointly
continuous at `p` and `y ↦ F (p.1, y)` is differentiable at `p.2`, then `F` has joint spacetime
Fréchet derivative `spacetimeJetCLM (P p) (fderiv ℝ (fun y => F (p.1, y)) p.2)` at `p`. -/
theorem hasFDerivAt_spacetimeJetCLM_of_hasDerivAt_fst {F P : ℝ × Space → Space}
    {p : ℝ × Space}
    (hP : ContinuousAt P p)
    (hτ : ∀ x : ℝ × Space, HasDerivAt (fun τ : ℝ => F (τ, x.2)) (P x) x.1)
    (hy : DifferentiableAt ℝ (fun y : Space => F (p.1, y)) p.2) :
    HasFDerivAt F (spacetimeJetCLM (P p) (fderiv ℝ (fun y : Space => F (p.1, y)) p.2)) p := by
  set Q : Space →L[ℝ] Space := fderiv ℝ (fun y : Space => F (p.1, y)) p.2
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ1, hδ1, hPδ⟩ := Metric.continuousAt_iff.1 hP (c / 2) (half_pos hc)
  have hyLittleO := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hy.hasFDerivAt)
  have hyBound := Asymptotics.isLittleO_iff.1 hyLittleO (half_pos hc)
  obtain ⟨δ2, hδ2, hyδ⟩ := Metric.eventually_nhds_iff_ball.1 hyBound
  set δ : ℝ := min δ1 δ2
  have hδpos : 0 < δ := lt_min hδ1 hδ2
  have hδ1' : δ ≤ δ1 := min_le_left _ _
  have hδ2' : δ ≤ δ2 := min_le_right _ _
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ × Space) hδpos] with h hh
  have hh' : ‖h‖ < δ := by simpa using hh
  have hhd1 : dist (p.1 + h.1) p.1 < δ := by
    rw [dist_eq_norm, add_sub_cancel_left]
    exact lt_of_le_of_lt (norm_fst_le h) hh'
  have hhd2 : dist (p.2 + h.2) p.2 < δ := by
    rw [dist_eq_norm, add_sub_cancel_left]
    exact lt_of_le_of_lt (norm_snd_le h) hh'
  have hstep1 : ∀ s ∈ Metric.ball p.1 δ,
      HasDerivWithinAt (fun τ : ℝ => F (τ, p.2 + h.2) - τ • P p)
        (P (s, p.2 + h.2) - P p) (Metric.ball p.1 δ) s := by
    intro s _
    have H1 : HasDerivAt (fun τ : ℝ => F (τ, p.2 + h.2)) (P (s, p.2 + h.2)) s :=
      hτ (s, p.2 + h.2)
    have H2 : HasDerivAt (fun τ : ℝ => τ • P p) (P p) s := by
      simpa using (hasDerivAt_id s).smul_const (P p)
    exact (H1.sub H2).hasDerivWithinAt
  have hb1 : ∀ s ∈ Metric.ball p.1 δ, ‖P (s, p.2 + h.2) - P p‖ ≤ c / 2 := by
    intro s hs
    have hsd : dist s p.1 < δ := Metric.mem_ball.1 hs
    have hdist : dist (s, p.2 + h.2) p < δ1 := by
      refine lt_of_lt_of_le ?_ hδ1'
      rw [Prod.dist_eq]
      exact max_lt hsd hhd2
    rw [← dist_eq_norm]
    exact (hPδ hdist).le
  have e1 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hstep1 hb1 (convex_ball _ _)
    (Metric.mem_ball_self hδpos) (Metric.mem_ball.2 hhd1)
  have e1' : ‖F (p.1 + h.1, p.2 + h.2) - F (p.1, p.2 + h.2) - h.1 • P p‖ ≤ c / 2 * ‖h.1‖ := by
    have heq :
        (F (p.1 + h.1, p.2 + h.2) - (p.1 + h.1) • P p) -
          (F (p.1, p.2 + h.2) - p.1 • P p) =
        F (p.1 + h.1, p.2 + h.2) - F (p.1, p.2 + h.2) - h.1 • P p := by
      rw [add_smul]
      abel
    simpa [heq, add_sub_cancel_left] using e1
  have hh2_ball : h.2 ∈ Metric.ball (0 : Space) δ2 := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (norm_snd_le h) (lt_of_lt_of_le hh' hδ2')
  have e2 : ‖F (p.1, p.2 + h.2) - F (p.1, p.2) - Q h.2‖ ≤ c / 2 * ‖h.2‖ :=
    hyδ h.2 hh2_ball
  have hdecomp :
      F (p + h) - F p - spacetimeJetCLM (P p) Q h =
        (F (p.1 + h.1, p.2 + h.2) - F (p.1, p.2 + h.2) - h.1 • P p) +
        (F (p.1, p.2 + h.2) - F (p.1, p.2) - Q h.2) := by
    simp only [spacetimeJetCLM_apply]
    have hFp : F p = F (p.1, p.2) := rfl
    have hFph : F (p + h) = F (p.1 + h.1, p.2 + h.2) := rfl
    rw [hFp, hFph]
    abel
  rw [hdecomp]
  have f1 : c / 2 * ‖h.1‖ ≤ c / 2 * ‖h‖ :=
    mul_le_mul_of_nonneg_left (norm_fst_le h) (half_pos hc).le
  have f2 : c / 2 * ‖h.2‖ ≤ c / 2 * ‖h‖ :=
    mul_le_mul_of_nonneg_left (norm_snd_le h) (half_pos hc).le
  calc ‖(F (p.1 + h.1, p.2 + h.2) - F (p.1, p.2 + h.2) - h.1 • P p) +
        (F (p.1, p.2 + h.2) - F (p.1, p.2) - Q h.2)‖
      ≤ ‖F (p.1 + h.1, p.2 + h.2) - F (p.1, p.2 + h.2) - h.1 • P p‖ +
        ‖F (p.1, p.2 + h.2) - F (p.1, p.2) - Q h.2‖ := norm_add_le _ _
    _ ≤ c / 2 * ‖h.1‖ + c / 2 * ‖h.2‖ := add_le_add e1' e2
    _ ≤ c / 2 * ‖h‖ + c / 2 * ‖h‖ := add_le_add f1 f2
    _ = c * ‖h‖ := by ring

/-! ## 3. Spacetime phase-derivative jet tower and joint `C^∞` bootstrap -/

/-- A sequence of phase-sliced vector fields `U : ℕ → ℝ → SpatialField` is a phase-derivative jet
tower for `U₀ : ℝ → SpatialField` if `U 0 = U₀` and for every time-derivative order `m : ℕ` and
spatial direction list `ws : List Space`, the spacetime map
`(τ, y) ↦ dirSpatialJet (U m τ) ws y` has Fréchet derivative with `τ`-component
`dirSpatialJet (U (m + 1) τ) ws y` and `y`-component `fderiv ℝ (dirSpatialJet (U m τ) ws) y`. -/
structure HasPhaseDerivJet (U₀ : ℝ → SpatialField) (U : ℕ → ℝ → SpatialField) : Prop where
  zero_eq : U 0 = U₀
  hasFDerivAt_jet :
    ∀ (m : ℕ) (ws : List Space) (x : ℝ × Space),
      HasFDerivAt (fun x' : ℝ × Space => dirSpatialJet (U m x'.1) ws x'.2)
        (spacetimeJetCLM (dirSpatialJet (U (m + 1) x.1) ws x.2)
          (fderiv ℝ (dirSpatialJet (U m x.1) ws) x.2)) x

/-- A sequence of phase-sliced vector fields `U : ℕ → ℝ → SpatialField` is a 1D phase-derivative
tower (`HasPhaseDerivTower U₀ U`) if `U 0 = U₀`, every slice `U m τ` is smooth on `Space`, every
spatial iterated Fréchet derivative `iteratedFDeriv ℝ k (U m τ) y` is globally bounded on
`ℝ × Space`, and `τ ↦ dirSpatialJet (U m τ) ws y` has 1D phase derivative
`dirSpatialJet (U (m + 1) τ) ws y`. -/
structure HasPhaseDerivTower (U₀ : ℝ → SpatialField) (U : ℕ → ℝ → SpatialField) : Prop where
  zero_eq : U 0 = U₀
  slice_contDiff : ∀ (m k : ℕ) (τ : ℝ), ContDiff ℝ k (U m τ)
  iteratedFDeriv_bounded :
    ∀ (m k : ℕ), ∃ M : ℝ, ∀ (τ : ℝ) (y : Space),
      ‖iteratedFDeriv ℝ k (U m τ) y‖ ≤ M
  hasDerivAt_phase :
    ∀ (m : ℕ) (ws : List Space) (τ : ℝ) (y : Space),
      HasDerivAt (fun τ' : ℝ => dirSpatialJet (U m τ') ws y)
        (dirSpatialJet (U (m + 1) τ) ws y) τ

/-- Every slice `U m τ` in a `HasPhaseDerivTower` is `ContDiff ℝ ∞` on `Space`. -/
theorem HasPhaseDerivTower.slice_contDiff_infty {U₀ : ℝ → SpatialField}
    {U : ℕ → ℝ → SpatialField} (hU : HasPhaseDerivTower U₀ U) (m : ℕ) (τ : ℝ) :
    ContDiff ℝ ∞ (U m τ) :=
  contDiff_infty.2 fun k => hU.slice_contDiff m k τ

/-- Every directional spatial jet `dirSpatialJet (U m τ) ws y` in a `HasPhaseDerivTower` is
globally bounded on `ℝ × Space`. -/
theorem HasPhaseDerivTower.jet_bounded {U₀ : ℝ → SpatialField}
    {U : ℕ → ℝ → SpatialField} (hU : HasPhaseDerivTower U₀ U) (m : ℕ) (ws : List Space) :
    ∃ M : ℝ, ∀ (τ : ℝ) (y : Space), ‖dirSpatialJet (U m τ) ws y‖ ≤ M := by
  obtain ⟨M, hM⟩ := hU.iteratedFDeriv_bounded m ws.length
  refine ⟨M * (ws.map norm).prod, fun τ y => ?_⟩
  have hprod : 0 ≤ (ws.map norm).prod :=
    List.prod_nonneg fun r hr => by
      obtain ⟨w, _, rfl⟩ := List.mem_map.1 hr
      exact norm_nonneg w
  exact le_trans (norm_dirSpatialJet_le (hU.slice_contDiff_infty m τ) ws y)
    (mul_le_mul_of_nonneg_right (hM τ y) hprod)

/-- Every node `(m, ws)` in a `HasPhaseDerivTower` is jointly continuous on `ℝ × Space`. -/
theorem HasPhaseDerivTower.continuous_dirSpatialJet {U₀ : ℝ → SpatialField}
    {U : ℕ → ℝ → SpatialField} (hU : HasPhaseDerivTower U₀ U) (m : ℕ) (ws : List Space) :
    Continuous (fun x : ℝ × Space => dirSpatialJet (U m x.1) ws x.2) := by
  refine continuous_of_hasDerivAt_fst_bounded
    (P := fun x : ℝ × Space => dirSpatialJet (U (m + 1) x.1) ws x.2)
    (fun x => hU.hasDerivAt_phase m ws x.1 x.2)
    (fun τ => continuous_dirSpatialJet_of_contDiff_infty (hU.slice_contDiff_infty m τ) ws) ?_
  obtain ⟨M, hM⟩ := hU.jet_bounded (m + 1) ws
  exact ⟨M, fun x => hM x.1 x.2⟩

/-- Any 1D phase-derivative tower `HasPhaseDerivTower U₀ U` automatically satisfies the full
spacetime Fréchet-derivative jet condition `HasPhaseDerivJet U₀ U`. -/
theorem hasPhaseDerivJet_of_hasPhaseDerivTower {U₀ : ℝ → SpatialField}
    {U : ℕ → ℝ → SpatialField} (hU : HasPhaseDerivTower U₀ U) :
    HasPhaseDerivJet U₀ U where
  zero_eq := hU.zero_eq
  hasFDerivAt_jet m ws x :=
    hasFDerivAt_spacetimeJetCLM_of_hasDerivAt_fst
      (hU.continuous_dirSpatialJet (m + 1) ws).continuousAt
      (fun x' => hU.hasDerivAt_phase m ws x'.1 x'.2)
      (differentiable_dirSpatialJet (hU.slice_contDiff_infty m x.1) ws x.2)

/-- Pointwise evaluation of the spacetime Fréchet derivative of a node `(m, ws)` in a
phase-derivative jet tower along a direction `v : ℝ × Space`: the `τ`-component advances
`m ↦ m + 1` and the `y`-component prepends `v.2` to `ws`. -/
theorem fderiv_dirSpatialJet_apply {U₀ : ℝ → SpatialField} {U : ℕ → ℝ → SpatialField}
    (hU : HasPhaseDerivJet U₀ U) (m : ℕ) (ws : List Space) (x v : ℝ × Space) :
    fderiv ℝ (fun x' : ℝ × Space => dirSpatialJet (U m x'.1) ws x'.2) x v =
      v.1 • dirSpatialJet (U (m + 1) x.1) ws x.2 +
        dirSpatialJet (U m x.1) (v.2 :: ws) x.2 := by
  rw [(hU.hasFDerivAt_jet m ws x).fderiv]
  rfl

/-- Every node `(m, ws)` in a phase-derivative jet tower is `ContDiff ℝ n` on `ℝ × Space` for
every finite order `n : ℕ`. -/
theorem contDiff_nat_dirSpatialJet_of_hasPhaseDerivJet
    {U₀ : ℝ → SpatialField} {U : ℕ → ℝ → SpatialField}
    (hU : HasPhaseDerivJet U₀ U) (n : ℕ) :
    ∀ (m : ℕ) (ws : List Space),
      ContDiff ℝ n (fun x : ℝ × Space => dirSpatialJet (U m x.1) ws x.2) := by
  induction n with
  | zero =>
      intro m ws
      rw [Nat.cast_zero, contDiff_zero]
      exact continuous_iff_continuousAt.2 fun x =>
        (hU.hasFDerivAt_jet m ws x).differentiableAt.continuousAt
  | succ n ih =>
      intro m ws
      rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
      refine ⟨fun x => (hU.hasFDerivAt_jet m ws x).differentiableAt,
        fun h => absurd h (by simp), ?_⟩
      rw [contDiff_clm_apply_iff]
      intro v
      have hfun :
          (fun x : ℝ × Space =>
            fderiv ℝ (fun x' : ℝ × Space => dirSpatialJet (U m x'.1) ws x'.2) x v) =
          (fun x : ℝ × Space =>
            v.1 • dirSpatialJet (U (m + 1) x.1) ws x.2 +
              dirSpatialJet (U m x.1) (v.2 :: ws) x.2) :=
        funext fun x => fderiv_dirSpatialJet_apply hU m ws x v
      rw [hfun]
      exact ((ih (m + 1) ws).const_smul v.1).add (ih m (v.2 :: ws))

/-- Every node `(m, ws)` in a phase-derivative jet tower is jointly smooth (`ContDiff ℝ ∞`) on
`ℝ × Space`. -/
theorem contDiff_infty_dirSpatialJet_of_hasPhaseDerivJet
    {U₀ : ℝ → SpatialField} {U : ℕ → ℝ → SpatialField}
    (hU : HasPhaseDerivJet U₀ U) (m : ℕ) (ws : List Space) :
    ContDiff ℝ ∞ (fun x : ℝ × Space => dirSpatialJet (U m x.1) ws x.2) :=
  contDiff_infty.2 fun n => contDiff_nat_dirSpatialJet_of_hasPhaseDerivJet hU n m ws

/-- If `U₀ : ℝ → SpatialField` has a phase-derivative jet tower `HasPhaseDerivJet U₀ U`, then
`(τ, y) ↦ U₀ τ y` is jointly smooth (`ContDiff ℝ ∞`) on `ℝ × Space`. -/
theorem contDiff_infty_of_hasPhaseDerivJet
    {U₀ : ℝ → SpatialField} {U : ℕ → ℝ → SpatialField}
    (hU : HasPhaseDerivJet U₀ U) :
    ContDiff ℝ ∞ (fun x : ℝ × Space => U₀ x.1 x.2) := by
  have h0 := contDiff_infty_dirSpatialJet_of_hasPhaseDerivJet hU 0 []
  simpa [dirSpatialJet, hU.zero_eq] using h0

/-- If `U₀ : ℝ → SpatialField` has a 1D phase-derivative tower `HasPhaseDerivTower U₀ U`, then
`(τ, y) ↦ U₀ τ y` is jointly smooth (`ContDiff ℝ ∞`) on `ℝ × Space`. -/
theorem contDiff_infty_of_hasPhaseDerivTower
    {U₀ : ℝ → SpatialField} {U : ℕ → ℝ → SpatialField}
    (hU : HasPhaseDerivTower U₀ U) :
    ContDiff ℝ ∞ (fun x : ℝ × Space => U₀ x.1 x.2) :=
  contDiff_infty_of_hasPhaseDerivJet (hasPhaseDerivJet_of_hasPhaseDerivTower hU)

/-- Construct a `HasPhaseDerivTower U₀ U` from `U 0 = U₀`, `IsUniformSmoothL4SliceFamily (U m)` for
every `m : ℕ`, and the 1D phase-derivative relation `HasDerivAt` for every directional spatial jet. -/
theorem hasPhaseDerivTower_of_uniformSmoothL4
    {U₀ : ℝ → SpatialField} {U : ℕ → ℝ → SpatialField}
    (hZero : U 0 = U₀)
    (hReg : ∀ m : ℕ, IsUniformSmoothL4SliceFamily (U m))
    (hDeriv : ∀ (m : ℕ) (ws : List Space) (τ : ℝ) (y : Space),
      HasDerivAt (fun τ' : ℝ => dirSpatialJet (U m τ') ws y)
        (dirSpatialJet (U (m + 1) τ) ws y) τ) :
    HasPhaseDerivTower U₀ U where
  zero_eq := hZero
  slice_contDiff m k τ := (hReg m).slice_contDiff k τ
  iteratedFDeriv_bounded m k := (hReg m).iteratedFDeriv_bounded k
  hasDerivAt_phase := hDeriv

/-! ### 3b. Comoving ray derivative tower (`T₀ = ∂_τ - (1/2) y · ∇_y`) -/

/-- Pullback of a phase-sliced vector field `V : ℝ → SpatialField` along the comoving spatial
scaling `x ↦ e^{-τ/2} • x` (corresponding to fixed physical position `x = e^{τ/2} • y`). -/
def comovingPullback (V : ℝ → SpatialField) : ℝ → SpatialField :=
  fun τ x => V τ (Real.exp (-τ / 2) • x)

/-- Chain rule for `dirSpatialJet` under spatial dilation `x' ↦ c • x'`. -/
theorem dirSpatialJet_comp_smul {F : SpatialField} (hF : ContDiff ℝ ∞ F) (c : ℝ) :
    ∀ (ws : List Space) (x : Space),
      dirSpatialJet (fun x' => F (c • x')) ws x =
        (c ^ ws.length) • dirSpatialJet F ws (c • x)
  | [], x => by simp
  | w :: ws, x => by
      have ih : dirSpatialJet (fun x' => F (c • x')) ws =
          fun x' => (c ^ ws.length) • dirSpatialJet F ws (c • x') :=
        funext (dirSpatialJet_comp_smul hF c ws)
      simp only [dirSpatialJet_cons, ih, List.length_cons, pow_succ]
      have hDiff : DifferentiableAt ℝ (dirSpatialJet F ws) (c • x) :=
        differentiable_dirSpatialJet hF ws (c • x)
      have hScale : HasFDerivAt (fun x' : Space => c • x')
          (c • ContinuousLinearMap.id ℝ Space) x :=
        (hasFDerivAt_id x).const_smul c
      have hComp : HasFDerivAt (fun x' : Space => (c ^ ws.length) • dirSpatialJet F ws (c • x'))
          ((c ^ ws.length) • ((fderiv ℝ (dirSpatialJet F ws) (c • x)).comp
            (c • ContinuousLinearMap.id ℝ Space))) x :=
        (hDiff.hasFDerivAt.comp x hScale).const_smul (c ^ ws.length)
      rw [hComp.fderiv]
      simp [mul_smul]

/-- If `F : SpatialField` is `ContDiff ℝ ∞`, then `x ↦ F (c • x)` is `ContDiff ℝ ∞`. -/
theorem contDiff_infty_comp_smul {F : SpatialField} (hF : ContDiff ℝ ∞ F) (c : ℝ) :
    ContDiff ℝ ∞ (fun x : Space => F (c • x)) :=
  hF.comp (contDiff_id.const_smul c)

end JointSmoothSub

/-- `V' : ℝ → SpatialField` is the 1D comoving phase-jet derivative (`T₀ = ∂_τ - (1/2) y · ∇_y`)
of `V : ℝ → SpatialField` if along every comoving ray `(τ + t, e^{-t/2} • y)`, every spatial
directional jet `dirSpatialJet (V (τ + t)) ws (e^{-t/2} • y)` has derivative at `t = 0` equal to
`dirSpatialJet (V' τ) ws y + (ws.length / 2) • dirSpatialJet (V τ) ws y`. -/
def HasComovingJetDeriv (V V' : ℝ → SpatialField) : Prop :=
  ∀ (ws : List Space) (τ : ℝ) (y : Space),
    HasDerivAt (fun t : ℝ => dirSpatialJet (V (τ + t)) ws (Real.exp (-t / 2) • y))
      (dirSpatialJet (V' τ) ws y + ((ws.length : ℝ) / 2) • dirSpatialJet (V τ) ws y) 0

namespace JointSmoothSub

/-- Under `HasComovingJetDeriv V V'`, the comoving pullback `comovingPullback V` has fixed-`x`
1D phase derivative `comovingPullback V'` on every spatial directional jet `ws : List Space`. -/
theorem hasDerivAt_comovingPullback_dirSpatialJet {V V' : ℝ → SpatialField}
    (hV : ∀ τ : ℝ, ContDiff ℝ ∞ (V τ))
    (hV' : ∀ τ : ℝ, ContDiff ℝ ∞ (V' τ))
    (hDeriv : HasComovingJetDeriv V V')
    (ws : List Space) (τ : ℝ) (x : Space) :
    HasDerivAt (fun τ' : ℝ => dirSpatialJet (comovingPullback V τ') ws x)
      (dirSpatialJet (comovingPullback V' τ) ws x) τ := by
  set y : Space := Real.exp (-τ / 2) • x
  set k : ℝ := (ws.length : ℝ)
  have hExp : HasDerivAt (fun t : ℝ => Real.exp (-(k / 2) * t)) (-(k / 2)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => -(k / 2) * t) (-(k / 2) * 1) 0 :=
      (hasDerivAt_id (0 : ℝ)).const_mul (-(k / 2))
    simpa using h1.exp
  have hRay := hDeriv ws τ y
  have hProd : HasDerivAt
      (fun t : ℝ => Real.exp (-(k / 2) * t) •
        dirSpatialJet (V (τ + t)) ws (Real.exp (-t / 2) • y))
      (dirSpatialJet (V' τ) ws y) 0 := by
    have hP := hExp.smul hRay
    simp only [zero_div, mul_zero, neg_zero, Real.exp_zero, add_zero, one_smul] at hP
    have hCancel :
        dirSpatialJet (V' τ) ws y + ((ws.length : ℝ) / 2) • dirSpatialJet (V τ) ws y +
          -(k / 2) • dirSpatialJet (V τ) ws y =
        dirSpatialJet (V' τ) ws y := by
      dsimp [k]
      rw [neg_smul, add_neg_cancel_right]
    rw [hCancel] at hP
    exact hP
  have hScaled : HasDerivAt
      (fun t : ℝ => (Real.exp (-τ / 2) ^ ws.length) •
        (Real.exp (-(k / 2) * t) •
          dirSpatialJet (V (τ + t)) ws (Real.exp (-t / 2) • y)))
      ((Real.exp (-τ / 2) ^ ws.length) • dirSpatialJet (V' τ) ws y) 0 :=
    hProd.const_smul (Real.exp (-τ / 2) ^ ws.length)
  have hComp : HasDerivAt
      (fun τ' : ℝ => (Real.exp (-τ / 2) ^ ws.length) •
        (Real.exp (-(k / 2) * (τ' - τ)) •
          dirSpatialJet (V (τ + (τ' - τ))) ws (Real.exp (-(τ' - τ) / 2) • y)))
      ((Real.exp (-τ / 2) ^ ws.length) • dirSpatialJet (V' τ) ws y) τ := by
    have hSub : HasDerivAt (fun τ' : ℝ => τ' - τ) 1 τ := by
      simpa using (hasDerivAt_id τ).sub_const τ
    have h := hScaled.scomp_of_eq τ hSub (sub_self τ).symm
    refine h.congr_deriv ?_
    simp
  have hFun :
      (fun τ' : ℝ => dirSpatialJet (comovingPullback V τ') ws x) =
      (fun τ' : ℝ => (Real.exp (-τ / 2) ^ ws.length) •
        (Real.exp (-(k / 2) * (τ' - τ)) •
          dirSpatialJet (V (τ + (τ' - τ))) ws (Real.exp (-(τ' - τ) / 2) • y))) := by
    funext τ'
    change dirSpatialJet (fun x' => V τ' (Real.exp (-τ' / 2) • x')) ws x = _
    rw [dirSpatialJet_comp_smul (hV τ') (Real.exp (-τ' / 2)) ws x]
    have hτ' : τ + (τ' - τ) = τ' := add_sub_cancel τ τ'
    have hy' : Real.exp (-(τ' - τ) / 2) • y = Real.exp (-τ' / 2) • x := by
      dsimp [y]
      rw [← mul_smul, ← Real.exp_add]
      congr 2
      ring
    have hpow :
        Real.exp (-τ / 2) ^ ws.length * Real.exp (-(k / 2) * (τ' - τ)) =
          Real.exp (-τ' / 2) ^ ws.length := by
      have hk : -(k / 2) * (τ' - τ) = (ws.length : ℝ) * (-(τ' - τ) / 2) := by
        dsimp [k]; ring
      rw [hk, Real.exp_nat_mul, ← mul_pow, ← Real.exp_add]
      congr 2
      ring
    rw [hτ', hy', smul_smul, hpow]
  have hVal :
      dirSpatialJet (comovingPullback V' τ) ws x =
        (Real.exp (-τ / 2) ^ ws.length) • dirSpatialJet (V' τ) ws y :=
    dirSpatialJet_comp_smul (hV' τ) (Real.exp (-τ / 2)) ws x
  rw [hFun, hVal]
  exact hComp

/-- A sequence of phase-sliced vector fields `U : ℕ → ℝ → SpatialField` is a 1D comoving
phase-derivative tower (`HasComovingDerivTower U₀ U`) if `U 0 = U₀`, every slice `U m τ` is smooth
on `Space`, every spatial iterated Fréchet derivative `iteratedFDeriv ℝ k (U m τ) y` is globally
bounded on `ℝ × Space`, and `HasComovingJetDeriv (U m) (U (m + 1))` holds for every `m : ℕ`. -/
structure HasComovingDerivTower (U₀ : ℝ → SpatialField) (U : ℕ → ℝ → SpatialField) : Prop where
  zero_eq : U 0 = U₀
  slice_contDiff : ∀ (m k : ℕ) (τ : ℝ), ContDiff ℝ k (U m τ)
  iteratedFDeriv_bounded :
    ∀ (m k : ℕ), ∃ M : ℝ, ∀ (τ : ℝ) (y : Space),
      ‖iteratedFDeriv ℝ k (U m τ) y‖ ≤ M
  hasComovingDeriv :
    ∀ m : ℕ, HasComovingJetDeriv (U m) (U (m + 1))

/-- Every slice `U m τ` in a `HasComovingDerivTower` is `ContDiff ℝ ∞` on `Space`. -/
theorem HasComovingDerivTower.slice_contDiff_infty {U₀ : ℝ → SpatialField}
    {U : ℕ → ℝ → SpatialField} (hU : HasComovingDerivTower U₀ U) (m : ℕ) (τ : ℝ) :
    ContDiff ℝ ∞ (U m τ) :=
  contDiff_infty.2 fun k => hU.slice_contDiff m k τ

/-- Every directional spatial jet `dirSpatialJet (U m τ) ws y` in a `HasComovingDerivTower` is
globally bounded on `ℝ × Space`. -/
theorem HasComovingDerivTower.jet_bounded {U₀ : ℝ → SpatialField}
    {U : ℕ → ℝ → SpatialField} (hU : HasComovingDerivTower U₀ U) (m : ℕ) (ws : List Space) :
    ∃ M : ℝ, ∀ (τ : ℝ) (y : Space), ‖dirSpatialJet (U m τ) ws y‖ ≤ M := by
  obtain ⟨M, hM⟩ := hU.iteratedFDeriv_bounded m ws.length
  refine ⟨M * (ws.map norm).prod, fun τ y => ?_⟩
  have hprod : 0 ≤ (ws.map norm).prod :=
    List.prod_nonneg fun r hr => by
      obtain ⟨w, _, rfl⟩ := List.mem_map.1 hr
      exact norm_nonneg w
  exact le_trans (norm_dirSpatialJet_le (hU.slice_contDiff_infty m τ) ws y)
    (mul_le_mul_of_nonneg_right (hM τ y) hprod)

/-- Every node `(m, ws)` of the comoving pullback `comovingPullback (U m)` in a
`HasComovingDerivTower` is locally-in-time bounded on `dist τ τ₀ ≤ 1`. -/
theorem HasComovingDerivTower.pullback_jet_locally_bounded {U₀ : ℝ → SpatialField}
    {U : ℕ → ℝ → SpatialField} (hU : HasComovingDerivTower U₀ U)
    (m : ℕ) (ws : List Space) (τ₀ : ℝ) :
    ∃ M : ℝ, ∀ x : ℝ × Space, dist x.1 τ₀ ≤ 1 →
      ‖dirSpatialJet (comovingPullback (U m) x.1) ws x.2‖ ≤ M := by
  obtain ⟨M₀, hM₀⟩ := hU.jet_bounded m ws
  set B : ℝ := max M₀ 0
  refine ⟨(Real.exp ((|τ₀| + 1) / 2) ^ ws.length) * B, fun x hx => ?_⟩
  have hEq :
      dirSpatialJet (comovingPullback (U m) x.1) ws x.2 =
        (Real.exp (-x.1 / 2) ^ ws.length) •
          dirSpatialJet (U m x.1) ws (Real.exp (-x.1 / 2) • x.2) :=
    dirSpatialJet_comp_smul (hU.slice_contDiff_infty m x.1) (Real.exp (-x.1 / 2)) ws x.2
  rw [hEq, norm_smul, Real.norm_of_nonneg (pow_nonneg (Real.exp_nonneg _) _)]
  have hExpLe : Real.exp (-x.1 / 2) ≤ Real.exp ((|τ₀| + 1) / 2) := by
    apply Real.exp_le_exp.2
    have h1 : |x.1 - τ₀| ≤ 1 := by rwa [Real.dist_eq] at hx
    have h2 : -1 ≤ x.1 - τ₀ := (abs_le.1 h1).1
    have h3 : -τ₀ ≤ |τ₀| := neg_le_abs τ₀
    linarith
  have hPowLe : Real.exp (-x.1 / 2) ^ ws.length ≤ Real.exp ((|τ₀| + 1) / 2) ^ ws.length :=
    pow_le_pow_left₀ (Real.exp_nonneg _) hExpLe ws.length
  have hJetLe : ‖dirSpatialJet (U m x.1) ws (Real.exp (-x.1 / 2) • x.2)‖ ≤ B :=
    le_trans (hM₀ x.1 _) (le_max_left M₀ 0)
  exact mul_le_mul hPowLe hJetLe (norm_nonneg _) (pow_nonneg (Real.exp_nonneg _) _)

/-- Every node `(m, ws)` of `comovingPullback (U m)` in a `HasComovingDerivTower` is jointly
continuous on `ℝ × Space`. -/
theorem HasComovingDerivTower.continuous_pullback_dirSpatialJet {U₀ : ℝ → SpatialField}
    {U : ℕ → ℝ → SpatialField} (hU : HasComovingDerivTower U₀ U) (m : ℕ) (ws : List Space) :
    Continuous (fun x : ℝ × Space => dirSpatialJet (comovingPullback (U m) x.1) ws x.2) := by
  refine continuous_of_hasDerivAt_fst_locally_bounded
    (P := fun x : ℝ × Space => dirSpatialJet (comovingPullback (U (m + 1)) x.1) ws x.2)
    (fun x => hasDerivAt_comovingPullback_dirSpatialJet
      (hU.slice_contDiff_infty m) (hU.slice_contDiff_infty (m + 1))
      (hU.hasComovingDeriv m) ws x.1 x.2)
    (fun τ => continuous_dirSpatialJet_of_contDiff_infty
      (contDiff_infty_comp_smul (hU.slice_contDiff_infty m τ) (Real.exp (-τ / 2))) ws)
    (fun τ₀ => hU.pullback_jet_locally_bounded (m + 1) ws τ₀)

/-- If `HasComovingDerivTower U₀ U` holds, then `fun m => comovingPullback (U m)` forms a
`HasPhaseDerivJet (comovingPullback U₀)` tower. -/
theorem hasPhaseDerivJet_comovingPullback {U₀ : ℝ → SpatialField}
    {U : ℕ → ℝ → SpatialField} (hU : HasComovingDerivTower U₀ U) :
    HasPhaseDerivJet (comovingPullback U₀) (fun m => comovingPullback (U m)) where
  zero_eq := by simp [hU.zero_eq]
  hasFDerivAt_jet m ws x :=
    hasFDerivAt_spacetimeJetCLM_of_hasDerivAt_fst
      (hU.continuous_pullback_dirSpatialJet (m + 1) ws).continuousAt
      (fun x' => hasDerivAt_comovingPullback_dirSpatialJet
        (hU.slice_contDiff_infty m) (hU.slice_contDiff_infty (m + 1))
        (hU.hasComovingDeriv m) ws x'.1 x'.2)
      (differentiable_dirSpatialJet
        (contDiff_infty_comp_smul (hU.slice_contDiff_infty m x.1) (Real.exp (-x.1 / 2))) ws x.2)

/-- If `U₀ : ℝ → SpatialField` has a 1D comoving derivative tower `HasComovingDerivTower U₀ U`,
then `(τ, y) ↦ U₀ τ y` is jointly smooth (`ContDiff ℝ ∞`) on `ℝ × Space`. -/
theorem contDiff_infty_of_hasComovingDerivTower
    {U₀ : ℝ → SpatialField} {U : ℕ → ℝ → SpatialField}
    (hU : HasComovingDerivTower U₀ U) :
    ContDiff ℝ ∞ (fun x : ℝ × Space => U₀ x.1 x.2) := by
  have hPull : ContDiff ℝ ∞ (fun x : ℝ × Space => comovingPullback U₀ x.1 x.2) :=
    contDiff_infty_of_hasPhaseDerivJet (hasPhaseDerivJet_comovingPullback hU)
  have hChart : ContDiff ℝ ∞ (fun x : ℝ × Space => (x.1, Real.exp (x.1 / 2) • x.2)) :=
    contDiff_fst.prodMk ((Real.contDiff_exp.comp (contDiff_fst.div_const 2)).smul contDiff_snd)
  have hComp : ContDiff ℝ ∞
      ((fun x : ℝ × Space => comovingPullback U₀ x.1 x.2) ∘
        (fun x : ℝ × Space => (x.1, Real.exp (x.1 / 2) • x.2))) :=
    hPull.comp hChart
  have hEq :
      ((fun x : ℝ × Space => comovingPullback U₀ x.1 x.2) ∘
        (fun x : ℝ × Space => (x.1, Real.exp (x.1 / 2) • x.2))) =
      (fun x : ℝ × Space => U₀ x.1 x.2) := by
    ext ⟨τ, y⟩
    dsimp [comovingPullback]
    rw [← mul_smul, ← Real.exp_add]
    have h0 : -τ / 2 + τ / 2 = 0 := by ring
    rw [h0, Real.exp_zero, one_smul]
  rwa [hEq] at hComp

/-- Construct a `HasComovingDerivTower U₀ U` from `U 0 = U₀`, `IsUniformSmoothL4SliceFamily (U m)`
for every `m : ℕ`, and `HasComovingJetDeriv (U m) (U (m + 1))` for every `m : ℕ`. -/
theorem hasComovingDerivTower_of_uniformSmoothL4
    {U₀ : ℝ → SpatialField} {U : ℕ → ℝ → SpatialField}
    (hZero : U 0 = U₀)
    (hReg : ∀ m : ℕ, IsUniformSmoothL4SliceFamily (U m))
    (hDeriv : ∀ m : ℕ, HasComovingJetDeriv (U m) (U (m + 1))) :
    HasComovingDerivTower U₀ U where
  zero_eq := hZero
  slice_contDiff m k τ := (hReg m).slice_contDiff k τ
  iteratedFDeriv_bounded m k := (hReg m).iteratedFDeriv_bounded k
  hasComovingDeriv := hDeriv

end JointSmoothSub

/-! ## 4. Decomposition of the PDE phase-derivative bootstrap (SP 2519-2523, 2559-2562) -/

/-- **`PartII-b:S3/1/1` (`BgFirstOrderPhaseDeriv`)**
(`the November 2 reference manuscript`,
lines 2519-2523 and 2559-2562): from `ProjectedEquation p z` (`A_0 U + 𝔓(U · ∇U) = 0`), the
maximal-graph membership of all iterated spatial derivatives of `p.wOf z` in
`B0411.D p.period p.ν q0E`, the uniform `W^{k,4}` slice bounds on `U = bgField p z` and `W^{k,∞}`
bounds on `p.corr z`, and the smooth bounded solenoidal hypotheses on `p.raw` and `p.inlet i`,
both `bgField p z` and its first comoving derivative `U₁ = T₀ U = (∂_τ - (1/2) y · ∇_y) U` lie in
`IsUniformSmoothL4SliceFamily`, and `HasComovingJetDeriv (bgField p z) U₁` holds along every
comoving ray `(τ + t, e^{-t/2} • y)`.
Composed by task `PartII-b:S3/1` via `jointSmoothnessFromSpatialAllOrders_of`. -/
def BgFirstOrderPhaseDeriv : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 → ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ z : p.Z, ProjectedEquation p z →
      ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) →
      (∀ k : ℕ, ∃ g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E,
        IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (g α : Yq p.period q0E))) →
      (∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ, ContDiff ℝ k (bgField p z τ) ∧
        (∀ y : Space, ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ M) ∧
        eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal M) →
      (IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ)) →
      (∀ i : Fin 2, IsBoundedBackground (p.inlet i) ∧ ∀ τ, IsSolenoidal (p.inlet i τ)) →
      IsUniformSmoothL4SliceFamily (bgField p z) ∧
      ∃ U₁ : ℝ → SpatialField,
        IsUniformSmoothL4SliceFamily U₁ ∧
        HasComovingJetDeriv (bgField p z) U₁

/-- **`PartII-b:S3/1/2` (`BgHigherOrderPhaseDerivTower`)**
(`the November 2 reference manuscript`,
lines 2519-2523 and 2559-2562): under the regime and all-order spatial regularity hypotheses of
`JointSmoothnessFromSpatialAllOrders`, given `IsUniformSmoothL4SliceFamily (bgField p z)` and its
first-order comoving derivative `U₁` in `IsUniformSmoothL4SliceFamily`, differentiating the
comoving projected evolution `T₀ U = ν ΔU + (1/2)U - 𝔓(U · ∇U)` along comoving rays by induction
on `m : ℕ` yields a full 1D comoving phase-derivative tower `U : ℕ → ℝ → SpatialField` with
`U 0 = bgField p z`, `U 1 = U₁`, `∀ m, IsUniformSmoothL4SliceFamily (U m)`, and
`HasComovingJetDeriv (U m) (U (m + 1))` for every `m : ℕ`.
Composed by task `PartII-b:S3/1` via `jointSmoothnessFromSpatialAllOrders_of`. -/
def BgHigherOrderPhaseDerivTower : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 → ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ z : p.Z, ProjectedEquation p z →
      ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) →
      (∀ k : ℕ, ∃ g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E,
        IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (g α : Yq p.period q0E))) →
      (∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ, ContDiff ℝ k (bgField p z τ) ∧
        (∀ y : Space, ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ M) ∧
        eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal M) →
      (IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ)) →
      (∀ i : Fin 2, IsBoundedBackground (p.inlet i) ∧ ∀ τ, IsSolenoidal (p.inlet i τ)) →
      IsUniformSmoothL4SliceFamily (bgField p z) →
      ∀ U₁ : ℝ → SpatialField,
        IsUniformSmoothL4SliceFamily U₁ →
        HasComovingJetDeriv (bgField p z) U₁ →
        ∃ U : ℕ → ℝ → SpatialField,
          U 0 = bgField p z ∧
          U 1 = U₁ ∧
          (∀ m_ord : ℕ, IsUniformSmoothL4SliceFamily (U m_ord)) ∧
          ∀ m_ord : ℕ, HasComovingJetDeriv (U m_ord) (U (m_ord + 1))

/-- Conditional assembly of `JointSmoothnessFromSpatialAllOrders` (`PartII-b:S3/1`, SP 2559-2562)
from `BgFirstOrderPhaseDeriv` (`PartII-b:S3/1/1`) and `BgHigherOrderPhaseDerivTower`
(`PartII-b:S3/1/2`) via `JointSmoothSub.hasComovingDerivTower_of_uniformSmoothL4` and
`JointSmoothSub.contDiff_infty_of_hasComovingDerivTower`. -/
theorem jointSmoothnessFromSpatialAllOrders_of
    (hFirst : BgFirstOrderPhaseDeriv)
    (hHigher : BgHigherOrderPhaseDerivTower) :
    JointSmoothnessFromSpatialAllOrders := by
  intro Sig lam q hSig hEig m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₁, hν₁, hFirst'⟩ := hFirst Sig lam q hSig hEig m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₂, hν₂, hHigher'⟩ := hHigher Sig lam q hSig hEig m hm dm dp hdm h2m C₁ k₁ hC₁
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, ?_⟩
  intro p d hReg hν hAge hMode z hProj hz hGraph hSlice hRaw hInlet
  have hν₁' : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hν₂' : p.ν ≤ ν₂ := hν.trans (min_le_right _ _)
  obtain ⟨hBgL4, U₁, hU₁L4, hU₁Deriv⟩ :=
    hFirst' p d hReg hν₁' hAge hMode z hProj hz hGraph hSlice hRaw hInlet
  obtain ⟨U, hU0, _, hUReg, hUDeriv⟩ :=
    hHigher' p d hReg hν₂' hAge hMode z hProj hz hGraph hSlice hRaw hInlet
      hBgL4 U₁ hU₁L4 hU₁Deriv
  exact JointSmoothSub.contDiff_infty_of_hasComovingDerivTower
    (JointSmoothSub.hasComovingDerivTower_of_uniformSmoothL4 hU0 hUReg hUDeriv)

end UnforcedLeray.Short.IIb

end
