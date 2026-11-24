import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_1_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_2_2
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.CorrSliceContDiff

/-!
# `PartII-b:S3/1/1/2/2` decomposition (`Sub/PartII-b_S3_1_1_2_2.lean`, SP 2519-2523, 2559-2562)

Source of record: `the November 2 reference manuscript`
(SP), lines 2519-2523 and 2559-2562.

## Proved here (zero `sorry`)

1. **Schwarz commutation of `dirSpatialJet` with `spatialLaplacian`, `spatialDiffReact`, and
   `spatialProjectedLin`
   (`dirSpatialJet_pair_comm`, `dirSpatialJet_singleton_comm`, `dirSpatialJet_double_comm`,
   `dirSpatialJet_spatialLaplacian`, `dirSpatialJet_spatialDiffReact`,
   `dirSpatialJet_spatialProjectedLin`)**:
   * By symmetry of second spatial Fréchet derivatives (`ContDiffAt.isSymmSndFDerivAt`), any two
     spatial directional derivatives `dirSpatialJet · [u]` and `dirSpatialJet · [v]` commute on
     `C^∞` spatial fields.
   * Consequently, `spatialLaplacian` and `spatialDiffReact ν` commute with `dirSpatialJet · ws`
     for every direction list `ws : List Space`.
   * Combining with `PhaseDerivStepSub.dirSpatialJet_spatialRadialDrift` yields the exact all-order
     commutator for `spatialProjectedLin ν`:
     `dirSpatialJet (spatialProjectedLin ν F) ws = spatialProjectedLin ν (dirSpatialJet F ws) + ((ws.length : ℝ) / 2) • dirSpatialJet F ws`.
2. **All-order directional spatial jet formula for `bgPhaseDerivTower ν U₀ 1`
   (`dirSpatialJet_smoothConvectiveLeray`, `dirSpatialJet_bgPhaseDerivTower_one`)**:
   * Using the proved `smoothLerayRepExists_proof : SmoothLerayRepExists` and
     `SmoothLeraySliceSub.smoothLeraySlice_dirSpatialJet`, `dirSpatialJet · ws` commutes past
     `smoothConvectiveLeray V W τ` for `V, W ∈ IsUniformSmoothL4SliceFamily`, giving the explicit
     all-order spatial-jet identity for `bgPhaseDerivTower ν U₀ 1 τ`.
3. **Exact identification of `dirSpatialJet (contRep u τ) (coordWord α)` with `contRep (g α) τ` and
   unconditional slice bounds for `p.corr z`
   (`dirSpatialJet_append_singleton`, `dirSpatialJet_coordWord_snoc`,
   `dirSpatialJet_contRep_coordWord_eq`, `corr_slice_contDiff_infty_of_period_le_one`,
   `corr_iteratedFDeriv_sup_bound_of_period_le_one`)**:
   * Using `corrSliceIteratedContDiff_proof` (`PartII-b:S2/2`), `bgContRepWeakSlice`, and
     `contRep_iterated_sum_sup_bound`, proves unconditionally that when `p.period ≤ 1` and `p.ν ≤ 1`,
     every spatial slice `p.corr z τ` is `C^∞(ℝ³)`, its iterated spatial derivatives are uniformly
     bounded in `(τ, y)`, and `dirSpatialJet (p.corr z τ) (coordWord α) y = contRep (g α : Yq p.period q0E) τ y`.
4. **Reduction of `BgFirstPhaseCoordDeriv` to `BgCorrCoordPhaseJetDeriv` (`PartII-b:S3/1/1/2/2/1`)
   (`hasDerivAt_coordWord_of_hasPhaseJetDeriv_and_eq`,
   `hasDerivAt_coordWord_of_corr_and_pointwise_evol`,
   `bgFirstPhaseCoordDeriv_of_corr_jet`, `bgFirstPhaseCoordDeriv_of`,
   `bgFirstPhaseCoordDeriv_of_corr_and_projected`,
   `bgFirstPhaseCoordDeriv_of_projected_and_corr_slice`)**.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.Blueprint

namespace CoordDerivSub

open PhaseDerivStepSub SmoothLeraySliceSub ProjectedEvolutionSub

/-! ## 1. Commutation of `dirSpatialJet` with `spatialLaplacian`, `spatialDiffReact`, and `spatialProjectedLin` -/

/-- Symmetry of second constant-direction spatial derivatives `dirSpatialJet F [u, v] = dirSpatialJet F [v, u]`
for any `C^∞` spatial field `F : SpatialField`. -/
theorem dirSpatialJet_pair_comm {F : SpatialField} (hF : ContDiff ℝ ∞ F) (u v : Space) :
    dirSpatialJet F [u, v] = dirSpatialJet F [v, u] := by
  funext y
  have hdF : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hd_v : fderiv ℝ (dirSpatialJet F [v]) y =
      (ContinuousLinearMap.apply ℝ Space v).comp (fderiv ℝ (fderiv ℝ F) y) :=
    (((ContinuousLinearMap.apply ℝ Space v).hasFDerivAt).comp y (hdF y).hasFDerivAt).fderiv
  have hd_u : fderiv ℝ (dirSpatialJet F [u]) y =
      (ContinuousLinearMap.apply ℝ Space u).comp (fderiv ℝ (fderiv ℝ F) y) :=
    (((ContinuousLinearMap.apply ℝ Space u).hasFDerivAt).comp y (hdF y).hasFDerivAt).fderiv
  change fderiv ℝ (dirSpatialJet F [v]) y u = fderiv ℝ (dirSpatialJet F [u]) y v
  rw [hd_v, hd_u]
  change fderiv ℝ (fderiv ℝ F) y u v = fderiv ℝ (fderiv ℝ F) y v u
  exact (hF.contDiffAt.isSymmSndFDerivAt (n := ∞) (by simp)).eq u v

/-- Single-direction spatial jet `dirSpatialJet · [u]` commutes with `dirSpatialJet · ws` for any
smooth `F : SpatialField` and `ws : List Space`. -/
theorem dirSpatialJet_singleton_comm {F : SpatialField} (hF : ContDiff ℝ ∞ F)
    (u : Space) (ws : List Space) :
    dirSpatialJet (dirSpatialJet F [u]) ws = dirSpatialJet (dirSpatialJet F ws) [u] := by
  induction ws with
  | nil =>
      rfl
  | cons w ws ih =>
      have hws : ContDiff ℝ ∞ (dirSpatialJet F ws) :=
        JointSmoothSub.contDiff_infty_dirSpatialJet hF ws
      change dirSpatialJet (dirSpatialJet (dirSpatialJet F [u]) ws) [w] =
        dirSpatialJet (dirSpatialJet F ws) [u, w]
      rw [ih]
      exact dirSpatialJet_pair_comm hws w u

/-- Two-direction spatial jet `dirSpatialJet · [u, v]` commutes with `dirSpatialJet · ws` for any
smooth `F : SpatialField` and `ws : List Space`. -/
theorem dirSpatialJet_double_comm {F : SpatialField} (hF : ContDiff ℝ ∞ F)
    (u v : Space) (ws : List Space) :
    dirSpatialJet (dirSpatialJet F [u, v]) ws = dirSpatialJet (dirSpatialJet F ws) [u, v] := by
  have hv : ContDiff ℝ ∞ (dirSpatialJet F [v]) :=
    JointSmoothSub.contDiff_infty_dirSpatialJet hF [v]
  change dirSpatialJet (dirSpatialJet (dirSpatialJet F [v]) [u]) ws =
    dirSpatialJet (dirSpatialJet (dirSpatialJet F ws) [v]) [u]
  rw [dirSpatialJet_singleton_comm hv u ws, dirSpatialJet_singleton_comm hF v ws]

/-- `spatialLaplacian` commutes with `dirSpatialJet · ws` on smooth spatial fields. -/
theorem dirSpatialJet_spatialLaplacian {F : SpatialField} (hF : ContDiff ℝ ∞ F)
    (ws : List Space) :
    dirSpatialJet (spatialLaplacian F) ws = spatialLaplacian (dirSpatialJet F ws) := by
  unfold spatialLaplacian
  rw [HigherPhaseSub.dirSpatialJet_sum Finset.univ
    (F := fun j : Fin 3 =>
      dirSpatialJet F [EuclideanSpace.single j 1, EuclideanSpace.single j 1])
    (fun j _ => JointSmoothSub.contDiff_infty_dirSpatialJet hF
      [EuclideanSpace.single j 1, EuclideanSpace.single j 1]) ws]
  funext y
  refine Finset.sum_congr rfl fun j _ => ?_
  exact congrFun
    (dirSpatialJet_double_comm hF (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) ws) y

/-- Smoothness of `spatialLaplacian F` for smooth `F : SpatialField`. -/
theorem contDiff_infty_spatialLaplacian {F : SpatialField} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (spatialLaplacian F) :=
  ContDiff.sum fun j _ =>
    JointSmoothSub.contDiff_infty_dirSpatialJet hF
      [EuclideanSpace.single j 1, EuclideanSpace.single j 1]

/-- Smoothness of `spatialDiffReact ν F` for smooth `F : SpatialField`. -/
theorem contDiff_infty_spatialDiffReact (ν : ℝ) {F : SpatialField} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (spatialDiffReact ν F) :=
  ((contDiff_infty_spatialLaplacian hF).const_smul ν).add (hF.const_smul (1 / 2 : ℝ))

/-- `spatialDiffReact ν` commutes with `dirSpatialJet · ws` on smooth spatial fields. -/
theorem dirSpatialJet_spatialDiffReact (ν : ℝ) {F : SpatialField} (hF : ContDiff ℝ ∞ F)
    (ws : List Space) :
    dirSpatialJet (spatialDiffReact ν F) ws = spatialDiffReact ν (dirSpatialJet F ws) := by
  unfold spatialDiffReact
  have hLap : ContDiff ℝ ∞ (spatialLaplacian F) := contDiff_infty_spatialLaplacian hF
  have h1 : ContDiff ℝ ∞ (ν • spatialLaplacian F) := hLap.const_smul ν
  have h2 : ContDiff ℝ ∞ ((1 / 2 : ℝ) • F) := hF.const_smul (1 / 2 : ℝ)
  rw [HigherPhaseSub.dirSpatialJet_add h1 h2 ws,
    HigherPhaseSub.dirSpatialJet_smul ν hLap ws,
    HigherPhaseSub.dirSpatialJet_smul (1 / 2 : ℝ) hF ws,
    dirSpatialJet_spatialLaplacian hF ws]

/-- All-order commutator between `dirSpatialJet · ws` and `spatialProjectedLin ν`:
`dirSpatialJet (spatialProjectedLin ν F) ws = spatialProjectedLin ν (dirSpatialJet F ws) + ((ws.length : ℝ) / 2) • dirSpatialJet F ws`. -/
theorem dirSpatialJet_spatialProjectedLin (ν : ℝ) {F : SpatialField} (hF : ContDiff ℝ ∞ F)
    (ws : List Space) :
    dirSpatialJet (spatialProjectedLin ν F) ws =
      spatialProjectedLin ν (dirSpatialJet F ws) +
        ((ws.length : ℝ) / 2) • dirSpatialJet F ws := by
  unfold spatialProjectedLin
  have hRad : ContDiff ℝ ∞ (spatialRadialDrift F) :=
    HigherPhaseSub.contDiff_infty_spatialRadialDrift hF
  have h1 : ContDiff ℝ ∞ ((1 / 2 : ℝ) • spatialRadialDrift F) := hRad.const_smul (1 / 2 : ℝ)
  have h2 : ContDiff ℝ ∞ (spatialDiffReact ν F) := contDiff_infty_spatialDiffReact ν hF
  rw [HigherPhaseSub.dirSpatialJet_add h1 h2 ws,
    HigherPhaseSub.dirSpatialJet_smul (1 / 2 : ℝ) hRad ws,
    PhaseDerivStepSub.dirSpatialJet_spatialRadialDrift hF ws,
    dirSpatialJet_spatialDiffReact ν hF ws]
  funext y
  simp only [Pi.add_apply, Pi.smul_apply, smul_add, smul_smul]
  have hcoeff : (1 / 2 : ℝ) * (ws.length : ℝ) = (ws.length : ℝ) / 2 := by ring
  rw [hcoeff, add_assoc, add_comm (((ws.length : ℝ) / 2) • dirSpatialJet F ws y), ← add_assoc]

/-! ## 2. All-order directional spatial jet formula for `bgPhaseDerivTower ν U₀ 1` -/

/-- `dirSpatialJet · ws` commutes with `smoothConvectiveLeray V W τ` for
`V, W ∈ IsUniformSmoothL4SliceFamily`, using the proved `smoothLerayRepExists_proof`. -/
theorem dirSpatialJet_smoothConvectiveLeray {V W : ℝ → SpatialField}
    (hV : IsUniformSmoothL4SliceFamily V) (hW : IsUniformSmoothL4SliceFamily W)
    (ws : List Space) (τ : ℝ) :
    dirSpatialJet (smoothConvectiveLeray V W τ) ws =
      smoothLerayProj (dirSpatialJet (spatialConvect (V τ) (W τ)) ws) := by
  have hConv : IsUniformSmoothL4SliceFamily (fun τ' => spatialConvect (V τ') (W τ')) :=
    HigherPhaseSub.sliceFamily_spatialConvect hV hW
  exact (SmoothLeraySliceSub.smoothLeraySlice_dirSpatialJet
    smoothLerayRepExists_proof hConv ws τ).symm

/-- Explicit all-order spatial-jet formula for the first-order projected evolution stage
`bgPhaseDerivTower ν U₀ 1 τ`. -/
theorem dirSpatialJet_bgPhaseDerivTower_one (ν : ℝ) {U₀ : ℝ → SpatialField}
    (hU₀ : IsUniformSmoothL4SliceFamily U₀) (ws : List Space) (τ : ℝ) :
    dirSpatialJet (bgPhaseDerivTower ν U₀ 1 τ) ws =
      (spatialProjectedLin ν (dirSpatialJet (U₀ τ) ws) +
         ((ws.length : ℝ) / 2) • dirSpatialJet (U₀ τ) ws) -
      smoothLerayProj (dirSpatialJet (spatialConvect (U₀ τ) (U₀ τ)) ws) := by
  have hF : ContDiff ℝ ∞ (U₀ τ) := HigherPhaseSub.sliceFamily_contDiff_infty hU₀ τ
  have hLin : ContDiff ℝ ∞ (spatialProjectedLin ν (U₀ τ)) :=
    HigherPhaseSub.contDiff_infty_spatialProjectedLin ν hF
  have hConvSlice : IsUniformSmoothL4SliceFamily (smoothConvectiveLeray U₀ U₀) :=
    PhaseDerivStepSub.sliceFamily_smoothConvectiveLeray_of_repExists
      smoothLerayRepExists_proof hU₀ hU₀
  have hConv : ContDiff ℝ ∞ (smoothConvectiveLeray U₀ U₀ τ) :=
    HigherPhaseSub.sliceFamily_contDiff_infty hConvSlice τ
  have hTower : bgPhaseDerivTower ν U₀ 1 τ =
      spatialProjectedLin ν (U₀ τ) - smoothConvectiveLeray U₀ U₀ τ :=
    congrFun (PhaseDerivStepSub.bgPhaseDerivTower_one ν U₀) τ
  rw [hTower, HigherPhaseSub.dirSpatialJet_sub hLin hConv ws,
    dirSpatialJet_spatialProjectedLin ν hF ws,
    dirSpatialJet_smoothConvectiveLeray hU₀ hU₀ ws τ]

/-! ## 3. Exact identification of `dirSpatialJet (contRep u τ) (coordWord α)` with `contRep (g α) τ` -/

/-- For any `C^∞` spatial field `F`, appending `[v]` to `ws` applies `fderiv ℝ · y v` to
`dirSpatialJet F ws`. -/
theorem dirSpatialJet_append_singleton {F : SpatialField} (hF : ContDiff ℝ ∞ F)
    (ws : List Space) (v : Space) :
    dirSpatialJet F (ws ++ [v]) = fun y => fderiv ℝ (dirSpatialJet F ws) y v := by
  rw [← HigherPhaseSub.dirSpatialJet_append F ws [v], dirSpatialJet_singleton_comm hF v ws]
  rfl

/-- For any `C^∞` spatial field `F`, `dirSpatialJet F (coordWord (Fin.snoc α j)) y` is the `j`-th
coordinate directional derivative of `dirSpatialJet F (coordWord α)` at `y`. -/
theorem dirSpatialJet_coordWord_snoc {F : SpatialField} (hF : ContDiff ℝ ∞ F)
    {k : ℕ} (α : Fin k → Fin 3) (j : Fin 3) (y : Space) :
    dirSpatialJet F (PhaseDerivStepSub.coordWord (Fin.snoc α j)) y =
      fderiv ℝ (dirSpatialJet F (PhaseDerivStepSub.coordWord α)) y (coordinateVector j) := by
  rw [PhaseDerivStepSub.coordWord_snoc, dirSpatialJet_append_singleton hF]

/-- For `P ≤ 1`, `0 < ν`, and `u : Yq P q0E` with all iterated distributional spatial derivatives in
`B0411.D P ν q0E`, every slice `contRep u τ` is `C^∞` (`ContDiff ℝ ∞`). -/
theorem contDiff_infty_contRep_of_iterated {P : ℝ} [Fact (0 < P)] (hP1 : P ≤ 1)
    {ν : ℝ} (hν : 0 < ν) {u : Yq P q0E}
    (hall : ∀ k : ℕ, ∃ g : (Fin k → Fin 3) → B0411.D P ν q0E,
      IsIteratedPhaseGrad P q0E k u (fun α => (g α : Yq P q0E)))
    (τ : ℝ) :
    ContDiff ℝ ∞ (contRep u τ) := by
  rw [contDiff_infty]
  intro k
  obtain ⟨g, hg⟩ := hall k
  exact (corrSliceIteratedContDiff_proof P hP1 ν hν u hall k g hg τ).1

/-- For `P ≤ 1`, `0 < ν`, and `u : Yq P q0E` with all iterated distributional spatial derivatives in
`B0411.D P ν q0E`, the coordinate directional jet `dirSpatialJet (contRep u τ) (coordWord α) y`
equals `contRep (g α : Yq P q0E) τ y`. -/
theorem dirSpatialJet_contRep_coordWord_eq {P : ℝ} [Fact (0 < P)] (hP1 : P ≤ 1)
    {ν : ℝ} (hν : 0 < ν) {u : Yq P q0E}
    (hall : ∀ k : ℕ, ∃ g : (Fin k → Fin 3) → B0411.D P ν q0E,
      IsIteratedPhaseGrad P q0E k u (fun α => (g α : Yq P q0E))) :
    ∀ (k : ℕ) (g : (Fin k → Fin 3) → B0411.D P ν q0E),
      IsIteratedPhaseGrad P q0E k u (fun α => (g α : Yq P q0E)) →
      ∀ (τ : ℝ) (α : Fin k → Fin 3) (y : Space),
        dirSpatialJet (contRep u τ) (PhaseDerivStepSub.coordWord α) y =
          contRep (g α : Yq P q0E) τ y := by
  have hsmooth : ∀ τ : ℝ, ContDiff ℝ ∞ (contRep u τ) :=
    contDiff_infty_contRep_of_iterated hP1 hν hall
  choose G hG using hall
  intro k
  induction k with
  | zero =>
    intro g hg τ α y
    have hα : α = Fin.elim0 := Subsingleton.elim α Fin.elim0
    have hg0 : (g Fin.elim0 : Yq P q0E) = u := hg
    rw [hα, PhaseDerivStepSub.coordWord_zero, dirSpatialJet_nil, hg0]
  | succ k ih =>
    intro g hg τ β y
    have hβ : β = Fin.snoc (Fin.init β) (β (Fin.last k)) := (Fin.snoc_init_self β).symm
    set α : Fin k → Fin 3 := Fin.init β
    set j : Fin 3 := β (Fin.last k)
    rw [hβ, dirSpatialJet_coordWord_snoc (hsmooth τ) α j y]
    have hfun_eq : dirSpatialJet (contRep u τ) (PhaseDerivStepSub.coordWord α) =
        contRep (G k α : Yq P q0E) τ :=
      funext fun y' => ih (G k) (hG k) τ α y'
    rw [hfun_eq]
    have hop_g : ∀ l : Fin 3,
        HasPhaseOp (fun Φ => -dy l Φ) (G k α : Yq P q0E) (g (Fin.snoc α l) : Yq P q0E) :=
      fun l => isIteratedPhaseGrad_hasPhaseOp_snoc (hG k) hg α l
    have hf : Continuous (contRep (G k α : Yq P q0E) τ) :=
      contRep_slice_continuous hP1 hν (G k α) τ
    have hgj : ∀ l : Fin 3, Continuous (contRep (g (Fin.snoc α l) : Yq P q0E) τ) :=
      fun l => contRep_slice_continuous hP1 hν (g (Fin.snoc α l)) τ
    have hw : ∀ l : Fin 3, UnforcedLeray.HasWeakSpatialDerivative l
        (contRep (G k α : Yq P q0E) τ)
        (contRep (g (Fin.snoc α l) : Yq P q0E) τ) :=
      fun l =>
        UnforcedLeray.Short.PartIIIb.Concrete.bgContRepWeakSlice P hP1 ν hν
          (G k α) (g (Fin.snoc α l)) l (hop_g l) τ
    exact fderiv_apply_coordinateVector_of_continuous_weakGrad hf hgj hw y j

/-- When `p.period ≤ 1` and all iterated spatial derivatives of `p.wOf z` lie in `B0411.D`,
every slice `p.corr z τ` is `C^∞(ℝ³)` (`ContDiff ℝ ∞`). -/
theorem corr_slice_contDiff_infty_of_period_le_one (p : Params) (hP1 : p.period ≤ 1) (z : p.Z)
    (hall : ∀ k : ℕ, ∃ g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E,
      IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (g α : Yq p.period q0E)))
    (τ : ℝ) :
    ContDiff ℝ ∞ (p.corr z τ) :=
  contDiff_infty_contRep_of_iterated hP1 p.ν_pos hall τ

/-- When `p.period ≤ 1`, `p.ν ≤ 1`, and all iterated spatial derivatives of `p.wOf z` lie in
`B0411.D`, every spatial derivative order `k` of `p.corr z τ` is uniformly bounded in `(τ, y)`. -/
theorem corr_iteratedFDeriv_sup_bound_of_period_le_one (p : Params) (hP1 : p.period ≤ 1)
    (hν1 : p.ν ≤ 1) (z : p.Z)
    (hall : ∀ k : ℕ, ∃ g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E,
      IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (g α : Yq p.period q0E)))
    (k : ℕ) :
    ∃ M : ℝ, ∀ (τ : ℝ) (y : Space), ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ M := by
  obtain ⟨g, hg⟩ := hall k
  obtain ⟨M, -, hM⟩ := contRep_iterated_sum_sup_bound p hP1 hν1 k g
  refine ⟨M, fun τ y => ?_⟩
  have hle := (corrSliceIteratedContDiff_proof p.period hP1 p.ν p.ν_pos (p.wOf z) hall k g hg τ).2 y
  exact hle.trans (hM τ y)

/-! ## 4. Transport of `HasDerivAt` along coordinate words -/

/-- If `HasPhaseJetDeriv U₀ U₁` holds and `U₁ = bgPhaseDerivTower ν U₀ 1`, then every coordinate
jet `dirSpatialJet (U₀ τ') (coordWord α) y` has phase derivative
`dirSpatialJet (bgPhaseDerivTower ν U₀ 1 τ) (coordWord α) y`. -/
theorem hasDerivAt_coordWord_of_hasPhaseJetDeriv_and_eq (ν : ℝ)
    {U₀ U₁ : ℝ → SpatialField}
    (hDeriv : HasPhaseJetDeriv U₀ U₁)
    (hEq : U₁ = bgPhaseDerivTower ν U₀ 1)
    {k : ℕ} (α : Fin k → Fin 3) (τ : ℝ) (y : Space) :
    HasDerivAt
      (fun τ' : ℝ => dirSpatialJet (U₀ τ') (coordWord α) y)
      (dirSpatialJet (bgPhaseDerivTower ν U₀ 1 τ) (coordWord α) y) τ := by
  rw [← hEq]
  exact hDeriv (coordWord α) τ y

/-- If `p.raw` and `p.inlet i` are jointly smooth, `p.corr z` satisfies
`HasPhaseJetDeriv (p.corr z) W_corr`, and the combined field `bgField p z` satisfies the pointwise
projected evolution `HasDerivAt (fun τ' => bgField p z τ' y) (spatialProjectedLin p.ν (bgField p z τ) y - smoothConvectiveLeray (bgField p z) (bgField p z) τ y) τ`
at every `(τ, y)`, then for every `k : ℕ` and `α : Fin k → Fin 3`,
`HasDerivAt (fun τ' => dirSpatialJet (bgField p z τ') (coordWord α) y) (dirSpatialJet (bgPhaseDerivTower p.ν (bgField p z) 1 τ) (coordWord α) y) τ`. -/
theorem hasDerivAt_coordWord_of_corr_and_pointwise_evol
    (p : Params) (z : p.Z)
    (hRaw : ContDiff ℝ ∞ (uncurriedField p.raw))
    (hInlet : ∀ i : Fin 2, ContDiff ℝ ∞ (uncurriedField (p.inlet i)))
    (hBg : IsUniformSmoothL4SliceFamily (bgField p z))
    {W_corr : ℝ → SpatialField}
    (hW_corr : ∀ τ, ContDiff ℝ ∞ (W_corr τ))
    (dCorr : HasPhaseJetDeriv (p.corr z) W_corr)
    (hEvol : ∀ (τ : ℝ) (y : Space),
      HasDerivAt (fun τ' : ℝ => bgField p z τ' y)
        (spatialProjectedLin p.ν (bgField p z τ) y -
          smoothConvectiveLeray (bgField p z) (bgField p z) τ y) τ)
    {k : ℕ} (α : Fin k → Fin 3) (τ : ℝ) (y : Space) :
    HasDerivAt
      (fun τ' : ℝ => dirSpatialJet (bgField p z τ') (coordWord α) y)
      (dirSpatialJet (bgPhaseDerivTower p.ν (bgField p z) 1 τ) (coordWord α) y) τ := by
  have hCorr : ∀ τ', ContDiff ℝ ∞ (p.corr z τ') := by
    intro τ'
    have heq : p.corr z τ' =
        bgField p z τ' - (p.raw τ' + fun y' => ∑ i : Fin 2, p.coord z i • p.inlet i τ' y') := by
      funext y'
      simp [bgField]
    rw [heq]
    exact (HigherPhaseSub.sliceFamily_contDiff_infty hBg τ').sub
      ((contDiff_slice_of_joint hRaw τ').add
        (ContDiff.sum fun i _ => (contDiff_slice_of_joint (hInlet i) τ').const_smul (p.coord z i)))
  have hJetDeriv := hasPhaseJetDeriv_bgField_of_corr p z hRaw hInlet hCorr hW_corr dCorr
  have hEq := ProjectedEvolutionSub.eq_bgPhaseDerivTower_one_of_hasDerivAt p.ν hJetDeriv hEvol
  exact hasDerivAt_coordWord_of_hasPhaseJetDeriv_and_eq p.ν hJetDeriv hEq α τ y

end CoordDerivSub

/-! ## 5. Atomic leaf definitions and conditional assemblies of `BgFirstPhaseCoordDeriv` -/

/-- **Leaf (`PartII-b:S3/1/1/2/2/1`, `BgCorrCoordPhaseJetDeriv`, SP 2519-2523, 2559-2562)**:
under the hypotheses of `BgFirstPhaseCoordDeriv`, for every `α : Fin k → Fin 3` and
`(τ, y) ∈ ℝ × Space`, the coordinate spatial jet
`τ' ↦ dirSpatialJet (p.corr z τ') (PhaseDerivStepSub.coordWord α) y`
(`= contRep (g α : Yq p.period q0E) τ' y` by `CoordDerivSub.dirSpatialJet_contRep_coordWord_eq`)
is differentiable at `τ` with derivative equal to the difference between the projected evolution jet
`dirSpatialJet (bgPhaseDerivTower p.ν (bgField p z) 1 τ) (PhaseDerivStepSub.coordWord α) y` and the
raw/inlet phase-partial jets.
Composed by `PartII-b:S3/1/1/2/2` via `bgFirstPhaseCoordDeriv_of`. -/
def BgCorrCoordPhaseJetDeriv : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 →
  ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) →
      (∀ i : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2)) →
      ∀ z : p.Z, ProjectedEquation p z →
      ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) →
      (∀ k : ℕ, ∃ g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E,
        IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (g α : Yq p.period q0E))) →
      IsUniformSmoothL4SliceFamily (bgField p z) →
      IsUniformSmoothL4SliceFamily (fun τ => spatialRadialDrift (bgField p z τ)) →
      (Blueprint.IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ)) →
      (∀ i : Fin 2, Blueprint.IsBoundedBackground (p.inlet i) ∧
        ∀ τ, IsSolenoidal (p.inlet i τ)) →
      ∀ (k : ℕ) (α : Fin k → Fin 3) (τ : ℝ) (y : Space),
        HasDerivAt
          (fun τ' => dirSpatialJet (p.corr z τ') (PhaseDerivStepSub.coordWord α) y)
          (dirSpatialJet (bgPhaseDerivTower p.ν (bgField p z) 1 τ)
              (PhaseDerivStepSub.coordWord α) y -
            (dirSpatialJet (PhaseDerivStepSub.phasePartial p.raw τ)
              (PhaseDerivStepSub.coordWord α) y +
              ∑ i : Fin 2, p.coord z i •
                dirSpatialJet (PhaseDerivStepSub.phasePartial (p.inlet i) τ)
                  (PhaseDerivStepSub.coordWord α) y)) τ

/-- **Existence of a smooth `W^{k,4}` first phase-jet derivative of `bgField p z`**:
under the hypotheses of `BgFirstPhaseCoordDeriv`, `p.corr z` admits a smooth slice family
`W_corr : ℝ → SpatialField` satisfying `HasPhaseJetDeriv (p.corr z) W_corr` such that the combined
phase derivative `U₁ = phasePartial p.raw + ∑ i, p.coord z i • phasePartial (p.inlet i) + W_corr`
lies in `IsUniformSmoothL4SliceFamily`. -/
def BgCorrSlicePhaseJetDeriv : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 →
  ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) →
      (∀ i : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2)) →
      ∀ z : p.Z, ProjectedEquation p z →
      ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) →
      (∀ k : ℕ, ∃ g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E,
        IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (g α : Yq p.period q0E))) →
      IsUniformSmoothL4SliceFamily (bgField p z) →
      IsUniformSmoothL4SliceFamily (fun τ => spatialRadialDrift (bgField p z τ)) →
      ∃ W_corr : ℝ → SpatialField,
        (∀ τ : ℝ, ContDiff ℝ ∞ (W_corr τ)) ∧
        HasPhaseJetDeriv (p.corr z) W_corr ∧
        IsUniformSmoothL4SliceFamily
          (PhaseDerivStepSub.phasePartial p.raw +
            (fun τ y => ∑ i : Fin 2, p.coord z i • PhaseDerivStepSub.phasePartial (p.inlet i) τ y) +
            W_corr)

/-- Reduction of `BgFirstPhaseCoordDeriv` (`PartII-b:S3/1/1/2/2`) to `BgCorrCoordPhaseJetDeriv`
(`PartII-b:S3/1/1/2/2/1`) by combining the proved joint-smoothness phase-jet derivatives of `p.raw`
and `p.inlet i` (`PhaseDerivStepSub.hasPhaseJetDeriv_phasePartial` and
`PhaseDerivStepSub.hasPhaseJetDeriv_inlet_sum`) with the coordinate-jet derivative of `p.corr z`. -/
theorem bgFirstPhaseCoordDeriv_of_corr_jet
    (hCorr : BgCorrCoordPhaseJetDeriv) :
    BgFirstPhaseCoordDeriv := by
  intro Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₀, hν₀, hC⟩ := hCorr Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  refine ⟨ν₀, hν₀, ?_⟩
  intro p d hReg hν hAge hMode hRawCD hInCD z hProj hz hGraph hBg hRad hRaw hInlet k α τ y
  let ws := PhaseDerivStepSub.coordWord α
  have hRawDeriv : HasDerivAt (fun τ' => dirSpatialJet (p.raw τ') ws y)
      (dirSpatialJet (PhaseDerivStepSub.phasePartial p.raw τ) ws y) τ :=
    PhaseDerivStepSub.hasPhaseJetDeriv_phasePartial (F := p.raw) hRawCD ws τ y
  have hInDeriv : HasDerivAt
      (fun τ' => dirSpatialJet (fun y' => ∑ i : Fin 2, p.coord z i • p.inlet i τ' y') ws y)
      (dirSpatialJet
        (fun y' => ∑ i : Fin 2, p.coord z i • PhaseDerivStepSub.phasePartial (p.inlet i) τ y')
        ws y) τ :=
    PhaseDerivStepSub.hasPhaseJetDeriv_inlet_sum p z hInCD ws τ y
  have hInJetEq :
      dirSpatialJet
        (fun y' => ∑ i : Fin 2, p.coord z i • PhaseDerivStepSub.phasePartial (p.inlet i) τ y')
        ws y =
      ∑ i : Fin 2, p.coord z i •
        dirSpatialJet (PhaseDerivStepSub.phasePartial (p.inlet i) τ) ws y := by
    have hsum := HigherPhaseSub.dirSpatialJet_sum Finset.univ
      (F := fun i y' => p.coord z i • PhaseDerivStepSub.phasePartial (p.inlet i) τ y')
      (fun i _ => (PhaseDerivStepSub.contDiff_slice_phasePartial (F := p.inlet i)
        (hInCD i) τ).const_smul (p.coord z i)) ws
    rw [congrFun hsum y]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact congrFun (HigherPhaseSub.dirSpatialJet_smul (p.coord z i)
      (PhaseDerivStepSub.contDiff_slice_phasePartial (F := p.inlet i) (hInCD i) τ) ws) y
  rw [hInJetEq] at hInDeriv
  have hCorrDeriv :=
    hC p d hReg hν hAge hMode hRawCD hInCD z hProj hz hGraph hBg hRad hRaw hInlet k α τ y
  have hComb : HasDerivAt
      (fun τ' => (dirSpatialJet (p.raw τ') ws y +
          dirSpatialJet (fun y' => ∑ i : Fin 2, p.coord z i • p.inlet i τ' y') ws y) +
        dirSpatialJet (p.corr z τ') ws y)
      ((dirSpatialJet (PhaseDerivStepSub.phasePartial p.raw τ) ws y +
        ∑ i : Fin 2, p.coord z i •
          dirSpatialJet (PhaseDerivStepSub.phasePartial (p.inlet i) τ) ws y) +
      (dirSpatialJet (bgPhaseDerivTower p.ν (bgField p z) 1 τ) ws y -
        (dirSpatialJet (PhaseDerivStepSub.phasePartial p.raw τ) ws y +
          ∑ i : Fin 2, p.coord z i •
            dirSpatialJet (PhaseDerivStepSub.phasePartial (p.inlet i) τ) ws y))) τ :=
    (hRawDeriv.add hInDeriv).add hCorrDeriv
  have hFunEq :
      (fun τ' => (dirSpatialJet (p.raw τ') ws y +
          dirSpatialJet (fun y' => ∑ i : Fin 2, p.coord z i • p.inlet i τ' y') ws y) +
        dirSpatialJet (p.corr z τ') ws y) =
      (fun τ' => dirSpatialJet (bgField p z τ') ws y) := by
    funext τ'
    have hRawSlice : ContDiff ℝ ∞ (p.raw τ') :=
      PhaseDerivStepSub.contDiff_slice_of_joint (F := p.raw) hRawCD τ'
    have hInSlice : ∀ i : Fin 2, ContDiff ℝ ∞ (p.inlet i τ') :=
      fun i => PhaseDerivStepSub.contDiff_slice_of_joint (F := p.inlet i) (hInCD i) τ'
    let sumIn : SpatialField := fun y' => ∑ i : Fin 2, p.coord z i • p.inlet i τ' y'
    have hSumSmooth : ContDiff ℝ ∞ sumIn :=
      ContDiff.sum fun i _ => (hInSlice i).const_smul (p.coord z i)
    have hRawSumSmooth : ContDiff ℝ ∞ (p.raw τ' + sumIn) := hRawSlice.add hSumSmooth
    have hCorrSlice : ContDiff ℝ ∞ (p.corr z τ') := by
      have heq : p.corr z τ' = bgField p z τ' - (p.raw τ' + sumIn) := by
        funext y'
        simp [bgField, sumIn]
      rw [heq]
      exact (HigherPhaseSub.sliceFamily_contDiff_infty hBg τ').sub hRawSumSmooth
    have hBgEq : bgField p z τ' = (p.raw τ' + sumIn) + p.corr z τ' := by
      funext y'
      rfl
    rw [hBgEq,
      congrFun (HigherPhaseSub.dirSpatialJet_add hRawSumSmooth hCorrSlice ws) y,
      Pi.add_apply,
      congrFun (HigherPhaseSub.dirSpatialJet_add hRawSlice hSumSmooth ws) y,
      Pi.add_apply]
  rwa [hFunEq, add_sub_cancel] at hComb

/-- Primary conditional assembly of `BgFirstPhaseCoordDeriv` (`PartII-b:S3/1/1/2/2`) from
`BgCorrCoordPhaseJetDeriv` (`PartII-b:S3/1/1/2/2/1`). -/
theorem bgFirstPhaseCoordDeriv_of
    (hCorr : BgCorrCoordPhaseJetDeriv) :
    BgFirstPhaseCoordDeriv :=
  bgFirstPhaseCoordDeriv_of_corr_jet hCorr

/-- Assembly of `BgFirstPhaseCoordDeriv` (`PartII-b:S3/1/1/2/2`) from `SmoothLeraySliceRegularity`
(`PartII-b:S3/1/2/1`), `BgProjectedPointwiseDeriv` (`PartII-b:S3/1/2/2/1`), and
`BgCorrSlicePhaseJetDeriv`. -/
theorem bgFirstPhaseCoordDeriv_of_corr_and_projected
    (hLeray : SmoothLeraySliceRegularity)
    (hProjDeriv : BgProjectedPointwiseDeriv)
    (hCorrJet : BgCorrSlicePhaseJetDeriv) :
    BgFirstPhaseCoordDeriv := by
  intro Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₁, hν₁, hP⟩ := hProjDeriv hLeray Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₂, hν₂, hC⟩ := hCorrJet Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₃, hν₃, hper⟩ := poly_exp_small 2 dm 2 hdm
  set ν₀ : ℝ := min (min ν₁ ν₂) (min ν₃ 1)
  have hν₀ : 0 < ν₀ := lt_min (lt_min hν₁ hν₂) (lt_min hν₃ zero_lt_one)
  refine ⟨ν₀, hν₀, ?_⟩
  intro p d hReg hν hAge hMode hRawCD hInCD z hProj hz hGraph hBg hRad hRaw hInlet k α τ y
  have hν₁' : p.ν ≤ ν₁ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν₂' : p.ν ≤ ν₂ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν₃' : p.ν ≤ ν₃ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν1 : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hP1 : p.period ≤ 1 := period_le_one_of hReg (hper p.ν p.ν_pos hν₃')
  obtain ⟨W_corr, hW_corr, dCorr, hU₁Smooth⟩ :=
    hC p d hReg hν₂' hAge hMode hRawCD hInCD z hProj hz hGraph hBg hRad
  let U₁ : ℝ → SpatialField :=
    PhaseDerivStepSub.phasePartial p.raw +
      (fun τ' y' => ∑ i : Fin 2, p.coord z i • PhaseDerivStepSub.phasePartial (p.inlet i) τ' y') +
      W_corr
  have hCorrSlice : ∀ τ', ContDiff ℝ ∞ (p.corr z τ') :=
    CoordDerivSub.corr_slice_contDiff_infty_of_period_le_one p hP1 z hGraph
  have hU₁Deriv : HasPhaseJetDeriv (bgField p z) U₁ :=
    PhaseDerivStepSub.hasPhaseJetDeriv_bgField_of_corr p z hRawCD hInCD hCorrSlice hW_corr dCorr
  have hSliceHyp : ∀ m_k : ℕ, ∃ M : ℝ, ∀ τ' : ℝ, ContDiff ℝ m_k (bgField p z τ') ∧
      (∀ y' : Space, ‖iteratedFDeriv ℝ m_k (p.corr z τ') y'‖ ≤ M) ∧
      eLpNorm (fun y' => iteratedFDeriv ℝ m_k (bgField p z τ') y') 4 volume ≤ ENNReal.ofReal M := by
    intro m_k
    obtain ⟨M_corr, hM_corr⟩ :=
      CoordDerivSub.corr_iteratedFDeriv_sup_bound_of_period_le_one p hP1 hν1 z hGraph m_k
    obtain ⟨M_l4, hM_l4⟩ := hBg.l4_bounded m_k
    refine ⟨max M_corr M_l4, fun τ' => ⟨hBg.slice_contDiff m_k τ', ?_, ?_⟩⟩
    · intro y'
      exact (hM_corr τ' y').trans (le_max_left M_corr M_l4)
    · exact (hM_l4 τ').trans (ENNReal.ofReal_le_ofReal (le_max_right M_corr M_l4))
  have hEvol := hP p d hReg hν₁' hAge hMode hRawCD hInCD z hProj hz hGraph hSliceHyp
    hRaw hInlet hBg U₁ hU₁Smooth hU₁Deriv
  exact CoordDerivSub.hasDerivAt_coordWord_of_corr_and_pointwise_evol
    p z hRawCD hInCD hBg hW_corr dCorr hEvol α τ y

/-- Conditional assembly of `BgFirstPhaseCoordDeriv` from `BgProjectedPointwiseDeriv` and
`BgCorrSlicePhaseJetDeriv`, discharging `SmoothLeraySliceRegularity` via the proved
`smoothLeraySliceRegularity_proof`. -/
theorem bgFirstPhaseCoordDeriv_of_projected_and_corr_slice
    (hProjDeriv : BgProjectedPointwiseDeriv)
    (hCorrJet : BgCorrSlicePhaseJetDeriv) :
    BgFirstPhaseCoordDeriv :=
  bgFirstPhaseCoordDeriv_of_corr_and_projected smoothLeraySliceRegularity_proof hProjDeriv hCorrJet

end UnforcedLeray.Short.IIb

end
