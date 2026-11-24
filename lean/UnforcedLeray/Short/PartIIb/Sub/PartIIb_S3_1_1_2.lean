import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_1
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.HigherOrderPhaseDeriv.SmoothLeraySlice
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.HigherOrderPhaseDeriv.SmoothLeraySlice.RepExists
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletJointSmooth
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_1_2

/-!
# `PartII-b:S3/1/1/2` decomposition (`Sub/PartII-b_S3_1_1_2.lean`, SP 2519-2523, 2559-2562)

Source of record: `the November 2 reference manuscript`,
lines 2519–2523 and 2559–2562:
> "The projected equation is $A_0 U + \mathbb{P}(U \cdot \nabla U) = 0$ with zero residual.
> ... On positive physical-time compact intervals the resulting $C_\tau W^{k,4}$ regularity and the
> projected equation give all time derivatives, hence joint smoothness."

## Proved here (zero `sorry`)
1. **Joint-smoothness to `HasPhaseJetDeriv` calculus**:
   For any jointly smooth phase-space field `F : ℝ → SpatialField`
   (`ContDiff ℝ ∞ (fun x : ℝ × Space => F x.1 x.2)`), its classical phase partial derivative
   `phasePartial F τ y := fderiv ℝ (fun x : ℝ × Space => F x.1 x.2) (τ, y) (1, 0)` is jointly
   smooth on `ℝ × Space`, has smooth spatial slices, commutes with all iterated spatial directional
   jets `dirSpatialJet · ws` by Schwarz symmetry (`ContDiffAt.isSymmSndFDerivAt`), and therefore
   satisfies `HasPhaseJetDeriv F (phasePartial F)`. Applied to `p.inlet i` (via `inletJointSmooth`)
   and `p.raw` (via `RawJointSmooth` / `rawJointSmooth_of`).
2. **Coordinate multi-index reduction for `dirSpatialJet` and `HasPhaseJetDeriv`**:
   Every spatial direction list `ws : List Space` expands linearly into standard coordinate basis
   words `coordWord k α` (`α : Fin k → Fin 3`), reducing `HasPhaseJetDeriv V V'` from arbitrary
   lists `ws : List Space` to standard multi-indices `α : Fin k → Fin 3` matching
   `IsIteratedPhaseGrad`.
3. **All-order radial drift commutator and Morrey-upgraded `IsUniformSmoothL4SliceFamily`**:
   `dirSpatialJet_spatialRadialDrift` proves `D_ws((y · ∇)F) = (y · ∇)(D_ws F) + |ws| • D_ws F`, and
   `sliceFamily_spatialRadialDrift_of_l4` upgrades `L⁴(ℝ³)` bounds on `iteratedFDeriv ℝ k (spatialRadialDrift (U₀ τ))`
   to `IsUniformSmoothL4SliceFamily (fun τ => spatialRadialDrift (U₀ τ))` via `smoothMorreyL4FieldBound_proof`.
4. **First-order projected evolution operator `bgPhaseDerivTower ν U₀ 1`**:
   Explicit formula `bgPhaseDerivTower ν U₀ 1 = (fun τ => spatialProjectedLin ν (U₀ τ)) -
   smoothConvectiveLeray U₀ U₀` and unconditional closure in `IsUniformSmoothL4SliceFamily` using
   the proved `smoothLerayRepExists_proof : SmoothLerayRepExists`.

The fixed-`y` leaves `BgFirstRadialDriftL4` and `BgFirstPhaseCoordDeriv` below belong to the
retired fixed-`y` design: the maximal graph controls `T₀w = (∂_τ - ½ y · ∇)w`, not `(y · ∇)w` in
`L⁴`. `BgFirstPhaseDerivStep` (`PartII-b:S3/1/1/2`) is now assembled along comoving rays by
`bgFirstPhaseDerivStep_of_comoving` in `Sub/PartII-b_S3_1_comoving.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.Blueprint

namespace PhaseDerivStepSub

open SmoothLeraySliceSub

/-! ## 1. Joint smoothness on `ℝ × Space` and Schwarz commutation with `dirSpatialJet` -/

/-- Uncurried phase-space representation `(τ, y) ↦ F τ y` of `F : ℝ → SpatialField`. -/
def uncurriedField (F : ℝ → SpatialField) (x : ℝ × Space) : Space :=
  F x.1 x.2

/-- Classical phase partial derivative `(∂_τ F)(τ, y) = D_{(1,0)} F(τ, y)` of a phase-indexed spatial
field `F : ℝ → SpatialField`. -/
def phasePartial (F : ℝ → SpatialField) : ℝ → SpatialField :=
  fun τ y => fderiv ℝ (uncurriedField F) (τ, y) (1, 0)

/-- Directional derivative of an uncurried field `G : ℝ × Space → Space` along a constant
direction `v : ℝ × Space` preserves `ContDiff ℝ ∞`. -/
theorem contDiff_fderiv_apply {G : ℝ × Space → Space}
    (hG : ContDiff ℝ ∞ G) (v : ℝ × Space) :
    ContDiff ℝ ∞ (fun x : ℝ × Space => fderiv ℝ G x v) :=
  ((ContinuousLinearMap.apply ℝ Space v).contDiff).comp
    (hG.fderiv_right (by exact_mod_cast le_top))

/-- If `F : ℝ → SpatialField` is jointly `C^∞` on `ℝ × Space`, then `phasePartial F` is jointly
`C^∞` on `ℝ × Space`. -/
theorem contDiff_joint_phasePartial {F : ℝ → SpatialField}
    (hF : ContDiff ℝ ∞ (uncurriedField F)) :
    ContDiff ℝ ∞ (uncurriedField (phasePartial F)) :=
  contDiff_fderiv_apply hF (1, 0)

/-- If `F : ℝ → SpatialField` is jointly `C^∞` on `ℝ × Space`, then every spatial slice `F τ` is
`C^∞` on `Space`. -/
theorem contDiff_slice_of_joint {F : ℝ → SpatialField}
    (hF : ContDiff ℝ ∞ (uncurriedField F)) (τ : ℝ) :
    ContDiff ℝ ∞ (F τ) :=
  hF.comp (contDiff_const.prodMk contDiff_id)

/-- If `F : ℝ → SpatialField` is jointly `C^∞` on `ℝ × Space`, then every spatial slice of
`phasePartial F` is `C^∞` on `Space`. -/
theorem contDiff_slice_phasePartial {F : ℝ → SpatialField}
    (hF : ContDiff ℝ ∞ (uncurriedField F)) (τ : ℝ) :
    ContDiff ℝ ∞ (phasePartial F τ) :=
  contDiff_slice_of_joint (contDiff_joint_phasePartial hF) τ

/-- Pointwise 1D phase derivative of a jointly smooth field `F`: for each `(τ, y) ∈ ℝ × Space`,
`τ' ↦ F τ' y` has derivative `phasePartial F τ y` at `τ`. -/
theorem hasDerivAt_phasePartial {F : ℝ → SpatialField}
    (hF : ContDiff ℝ ∞ (uncurriedField F)) (τ : ℝ) (y : Space) :
    HasDerivAt (fun τ' : ℝ => F τ' y) (phasePartial F τ y) τ := by
  have hd : HasFDerivAt (uncurriedField F) (fderiv ℝ (uncurriedField F) (τ, y)) (τ, y) :=
    (hF.differentiable (by simp) (τ, y)).hasFDerivAt
  have hpath : HasDerivAt (fun τ' : ℝ => (τ', y)) ((1 : ℝ), (0 : Space)) τ :=
    (hasDerivAt_id τ).prodMk (hasDerivAt_const τ y)
  exact hd.comp_hasDerivAt τ hpath

/-- Spatial directional derivative along `w : Space` of a jointly smooth field `F` agrees with the
joint Fréchet derivative along `(0, w) : ℝ × Space`. -/
theorem dirSpatialJet_singleton_eq_joint_fderiv {F : ℝ → SpatialField}
    (hF : ContDiff ℝ ∞ (uncurriedField F)) (w : Space) (τ : ℝ) (y : Space) :
    dirSpatialJet (F τ) [w] y = fderiv ℝ (uncurriedField F) (τ, y) (0, w) := by
  have hd : HasFDerivAt (uncurriedField F) (fderiv ℝ (uncurriedField F) (τ, y)) (τ, y) :=
    (hF.differentiable (by simp) (τ, y)).hasFDerivAt
  have hemb : HasFDerivAt (fun y' : Space => (τ, y'))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) y :=
    (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have hcomp : fderiv ℝ (F τ) y =
      (fderiv ℝ (uncurriedField F) (τ, y)).comp
        ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) :=
    (hd.comp y hemb).fderiv
  change fderiv ℝ (F τ) y w = _
  rw [hcomp]
  rfl

/-- Iterated spatial directional jets `dirSpatialJet · ws` preserve joint `C^∞` regularity on
`ℝ × Space`. -/
theorem contDiff_joint_dirSpatialJet {F : ℝ → SpatialField}
    (hF : ContDiff ℝ ∞ (uncurriedField F)) (ws : List Space) :
    ContDiff ℝ ∞ (uncurriedField (fun τ => dirSpatialJet (F τ) ws)) := by
  induction ws with
  | nil =>
      exact hF
  | cons w ws ih =>
      have heq : uncurriedField (fun τ => dirSpatialJet (F τ) (w :: ws)) =
          fun x : ℝ × Space =>
            fderiv ℝ (uncurriedField (fun τ => dirSpatialJet (F τ) ws)) x (0, w) := by
        funext ⟨τ, y⟩
        exact dirSpatialJet_singleton_eq_joint_fderiv ih w τ y
      rw [heq]
      exact contDiff_fderiv_apply ih (0, w)

/-- Symmetry of second constant-direction derivatives on `ℝ × Space` for a `C^∞` map
`G : ℝ × Space → Space`. -/
theorem fderiv_fderiv_apply_comm {G : ℝ × Space → Space}
    (hG : ContDiff ℝ ∞ G) (v₁ v₂ : ℝ × Space) (x : ℝ × Space) :
    fderiv ℝ (fun z : ℝ × Space => fderiv ℝ G z v₂) x v₁ =
      fderiv ℝ (fun z : ℝ × Space => fderiv ℝ G z v₁) x v₂ := by
  have hdG : Differentiable ℝ (fderiv ℝ G) :=
    (hG.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hd1 : fderiv ℝ (fun z : ℝ × Space => fderiv ℝ G z v₂) x =
      (ContinuousLinearMap.apply ℝ Space v₂).comp (fderiv ℝ (fderiv ℝ G) x) :=
    (((ContinuousLinearMap.apply ℝ Space v₂).hasFDerivAt).comp x (hdG x).hasFDerivAt).fderiv
  have hd2 : fderiv ℝ (fun z : ℝ × Space => fderiv ℝ G z v₁) x =
      (ContinuousLinearMap.apply ℝ Space v₁).comp (fderiv ℝ (fderiv ℝ G) x) :=
    (((ContinuousLinearMap.apply ℝ Space v₁).hasFDerivAt).comp x (hdG x).hasFDerivAt).fderiv
  rw [hd1, hd2]
  change fderiv ℝ (fderiv ℝ G) x v₁ v₂ = fderiv ℝ (fderiv ℝ G) x v₂ v₁
  have hsymm : IsSymmSndFDerivAt ℝ G x :=
    hG.contDiffAt.isSymmSndFDerivAt (n := ∞) (by simp)
  exact hsymm.eq v₁ v₂

/-- Schwarz commutation between `phasePartial` and `dirSpatialJet · ws` for any jointly smooth
field `F : ℝ → SpatialField`. -/
theorem phasePartial_dirSpatialJet {F : ℝ → SpatialField}
    (hF : ContDiff ℝ ∞ (uncurriedField F)) (ws : List Space) (τ : ℝ) (y : Space) :
    phasePartial (fun τ' => dirSpatialJet (F τ') ws) τ y =
      dirSpatialJet (phasePartial F τ) ws y := by
  induction ws generalizing τ y with
  | nil =>
      rfl
  | cons w ws ih =>
      have hws : ContDiff ℝ ∞ (uncurriedField (fun τ' => dirSpatialJet (F τ') ws)) :=
        contDiff_joint_dirSpatialJet hF ws
      have hstep : uncurriedField (fun τ' => dirSpatialJet (F τ') (w :: ws)) =
          fun x : ℝ × Space =>
            fderiv ℝ (uncurriedField (fun τ' => dirSpatialJet (F τ') ws)) x (0, w) := by
        funext ⟨τ', y'⟩
        exact dirSpatialJet_singleton_eq_joint_fderiv hws w τ' y'
      have hcomm : phasePartial (fun τ' => dirSpatialJet (F τ') (w :: ws)) τ y =
          fderiv ℝ (uncurriedField (phasePartial (fun τ' => dirSpatialJet (F τ') ws)))
            (τ, y) (0, w) := by
        dsimp [phasePartial]
        rw [hstep]
        exact fderiv_fderiv_apply_comm hws (1, 0) (0, w) (τ, y)
      have hih_fun : uncurriedField (phasePartial (fun τ' => dirSpatialJet (F τ') ws)) =
          uncurriedField (fun τ' => dirSpatialJet (phasePartial F τ') ws) := by
        funext ⟨τ', y'⟩
        exact ih τ' y'
      have hphase_ws : ContDiff ℝ ∞
          (uncurriedField (fun τ' => dirSpatialJet (phasePartial F τ') ws)) :=
        contDiff_joint_dirSpatialJet (contDiff_joint_phasePartial hF) ws
      rw [hcomm, hih_fun]
      exact (dirSpatialJet_singleton_eq_joint_fderiv hphase_ws w τ y).symm

/-- Any jointly smooth field `F : ℝ → SpatialField` satisfies `HasPhaseJetDeriv F (phasePartial F)`:
every iterated spatial directional jet `τ' ↦ dirSpatialJet (F τ') ws y` is differentiable in `τ'`
with derivative `dirSpatialJet (phasePartial F τ) ws y`. -/
theorem hasPhaseJetDeriv_phasePartial {F : ℝ → SpatialField}
    (hF : ContDiff ℝ ∞ (uncurriedField F)) :
    HasPhaseJetDeriv F (phasePartial F) := by
  intro ws τ y
  have hd := hasDerivAt_phasePartial (contDiff_joint_dirSpatialJet hF ws) τ y
  rwa [phasePartial_dirSpatialJet hF ws τ y] at hd

/-- If the inlet basis modes `p.inlet i` are jointly smooth, then the finite-rank affine inlet
combination `fun τ y => ∑ i : Fin 2, p.coord z i • p.inlet i τ y` satisfies `HasPhaseJetDeriv`
with derivative `fun τ y => ∑ i : Fin 2, p.coord z i • phasePartial (p.inlet i) τ y`. -/
theorem hasPhaseJetDeriv_inlet_sum (p : Params) (z : p.Z)
    (hInlet : ∀ i : Fin 2, ContDiff ℝ ∞ (uncurriedField (p.inlet i))) :
    HasPhaseJetDeriv
      (fun τ y => ∑ i : Fin 2, p.coord z i • p.inlet i τ y)
      (fun τ y => ∑ i : Fin 2, p.coord z i • phasePartial (p.inlet i) τ y) := by
  refine HigherPhaseSub.hasPhaseJetDeriv_sum Finset.univ
    (F := fun i τ y => p.coord z i • p.inlet i τ y)
    (F' := fun i τ y => p.coord z i • phasePartial (p.inlet i) τ y)
    (fun i _ τ => (contDiff_slice_of_joint (hInlet i) τ).const_smul (p.coord z i))
    (fun i _ τ => (contDiff_slice_phasePartial (hInlet i) τ).const_smul (p.coord z i))
    fun i _ => HigherPhaseSub.hasPhaseJetDeriv_smul (p.coord z i)
      (contDiff_slice_of_joint (hInlet i))
      (contDiff_slice_phasePartial (hInlet i))
      (hasPhaseJetDeriv_phasePartial (hInlet i))

/-- If both `p.raw` and `p.inlet i` are jointly smooth and `p.corr z` satisfies
`HasPhaseJetDeriv (p.corr z) W_corr`, then `bgField p z` satisfies `HasPhaseJetDeriv` with
derivative `phasePartial p.raw + (fun τ y => ∑ i : Fin 2, p.coord z i • phasePartial (p.inlet i) τ y) + W_corr`. -/
theorem hasPhaseJetDeriv_bgField_of_corr (p : Params) (z : p.Z)
    (hRaw : ContDiff ℝ ∞ (uncurriedField p.raw))
    (hInlet : ∀ i : Fin 2, ContDiff ℝ ∞ (uncurriedField (p.inlet i)))
    {W_corr : ℝ → SpatialField}
    (hCorr : ∀ τ, ContDiff ℝ ∞ (p.corr z τ))
    (hW_corr : ∀ τ, ContDiff ℝ ∞ (W_corr τ))
    (dCorr : HasPhaseJetDeriv (p.corr z) W_corr) :
    HasPhaseJetDeriv (bgField p z)
      (phasePartial p.raw +
        (fun τ y => ∑ i : Fin 2, p.coord z i • phasePartial (p.inlet i) τ y) +
        W_corr) := by
  have hBgEq : bgField p z =
      p.raw + (fun τ y => ∑ i : Fin 2, p.coord z i • p.inlet i τ y) + p.corr z := by
    funext τ y
    rfl
  rw [hBgEq]
  have hSumSmooth : ∀ τ, ContDiff ℝ ∞ (fun y => ∑ i : Fin 2, p.coord z i • p.inlet i τ y) :=
    fun τ => ContDiff.sum fun i _ => (contDiff_slice_of_joint (hInlet i) τ).const_smul (p.coord z i)
  have hSumSmooth' : ∀ τ,
      ContDiff ℝ ∞ (fun y => ∑ i : Fin 2, p.coord z i • phasePartial (p.inlet i) τ y) :=
    fun τ => ContDiff.sum fun i _ =>
      (contDiff_slice_phasePartial (hInlet i) τ).const_smul (p.coord z i)
  refine HigherPhaseSub.hasPhaseJetDeriv_add
    (fun τ => (contDiff_slice_of_joint hRaw τ).add (hSumSmooth τ))
    (fun τ => (contDiff_slice_phasePartial hRaw τ).add (hSumSmooth' τ))
    hCorr hW_corr
    (HigherPhaseSub.hasPhaseJetDeriv_add
      (contDiff_slice_of_joint hRaw) (contDiff_slice_phasePartial hRaw)
      hSumSmooth hSumSmooth'
      (hasPhaseJetDeriv_phasePartial hRaw)
      (hasPhaseJetDeriv_inlet_sum p z hInlet))
    dCorr

/-! ## 2. Coordinate multi-index reduction for `dirSpatialJet` and `HasPhaseJetDeriv` -/

/-- Standard basis direction list associated to a multi-index `α : Fin k → Fin 3`. -/
def coordWord : ∀ {k : ℕ}, (Fin k → Fin 3) → List Space
  | 0, _ => []
  | k + 1, α => coordWord (fun i : Fin k => α i.castSucc) ++ [coordinateVector (α (Fin.last k))]

@[simp]
theorem coordWord_zero (α : Fin 0 → Fin 3) :
    coordWord α = [] := rfl

@[simp]
theorem coordWord_succ {k : ℕ} (α : Fin (k + 1) → Fin 3) :
    coordWord α =
      coordWord (fun i : Fin k => α i.castSucc) ++ [coordinateVector (α (Fin.last k))] := rfl

/-- Appending a single coordinate vector `coordinateVector j` to `coordWord α` produces
`coordWord (Fin.snoc α j)`. -/
theorem coordWord_snoc {k : ℕ} (α : Fin k → Fin 3) (j : Fin 3) :
    coordWord (Fin.snoc α j) = coordWord α ++ [coordinateVector j] := by
  rw [coordWord_succ]
  congr 2
  · funext i
    simp [Fin.snoc_castSucc]
  · rw [Fin.snoc_last]

/-- Single-direction coordinate expansion of `dirSpatialJet F [w]`:
`dirSpatialJet F [w] y = ∑ j : Fin 3, (w j) • dirSpatialJet F [coordinateVector j] y`. -/
theorem dirSpatialJet_singleton_eq_sum_coord (F : SpatialField) (w : Space) :
    dirSpatialJet F [w] =
      fun y => ∑ j : Fin 3, (w j) • dirSpatialJet F [coordinateVector j] y := by
  funext y
  dsimp [dirSpatialJet, coordinateVector]
  have hw : w = ∑ j : Fin 3, (w j) • EuclideanSpace.single j (1 : ℝ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]

/-- Coordinate expansion of `dirSpatialJet F (ws ++ [w])` for a smooth spatial field `F`. -/
theorem dirSpatialJet_append_singleton_eq_sum_coord {F : SpatialField}
    (hF : ContDiff ℝ ∞ F) (ws : List Space) (w : Space) :
    dirSpatialJet F (ws ++ [w]) =
      fun y => ∑ j : Fin 3, (w j) • dirSpatialJet F (ws ++ [coordinateVector j]) y := by
  rw [← HigherPhaseSub.dirSpatialJet_append F ws [w],
    dirSpatialJet_singleton_eq_sum_coord F w]
  have hsum := HigherPhaseSub.dirSpatialJet_sum (Finset.univ : Finset (Fin 3))
    (F := fun j y => (w j) • dirSpatialJet F [coordinateVector j] y)
    (fun j _ => (JointSmoothSub.contDiff_infty_dirSpatialJet hF [coordinateVector j]).const_smul (w j))
    ws
  funext y
  rw [congrFun hsum y]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsm := congrFun (HigherPhaseSub.dirSpatialJet_smul (w j)
    (JointSmoothSub.contDiff_infty_dirSpatialJet hF [coordinateVector j]) ws) y
  have happ := congrFun (HigherPhaseSub.dirSpatialJet_append F ws [coordinateVector j]) y
  exact hsm.trans (congrArg ((w j) • ·) happ)

/-- Finite-sum rule for `HasDerivAt` over a `Finset`. -/
private theorem hasDerivAt_finset_sum {ι : Type*} (s : Finset ι)
    {f : ι → ℝ → Space} {f' : ι → Space} {τ : ℝ}
    (hf : ∀ i ∈ s, HasDerivAt (f i) (f' i) τ) :
    HasDerivAt (fun τ' => ∑ i ∈ s, f i τ') (∑ i ∈ s, f' i) τ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using hasDerivAt_const τ (0 : Space)
  | @insert a s ha ih =>
      have hfun : (fun τ' => ∑ i ∈ insert a s, f i τ') =
          fun τ' => f a τ' + ∑ i ∈ s, f i τ' := by
        funext τ'
        exact Finset.sum_insert ha
      rw [hfun, Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Coordinate multi-index reduction for `HasPhaseJetDeriv`: if `V, V' : ℝ → SpatialField` have
`C^∞` spatial slices and `τ' ↦ dirSpatialJet (V τ') (coordWord α) y` has derivative
`dirSpatialJet (V' τ) (coordWord α) y` for every multi-index `α : Fin k → Fin 3`, then
`HasPhaseJetDeriv V V'` holds for all direction lists `ws : List Space`. -/
theorem hasPhaseJetDeriv_of_coordWord {V V' : ℝ → SpatialField}
    (hV : ∀ τ, ContDiff ℝ ∞ (V τ)) (hV' : ∀ τ, ContDiff ℝ ∞ (V' τ))
    (hCoord : ∀ (k : ℕ) (α : Fin k → Fin 3) (τ : ℝ) (y : Space),
      HasDerivAt (fun τ' => dirSpatialJet (V τ') (coordWord α) y)
        (dirSpatialJet (V' τ) (coordWord α) y) τ) :
    HasPhaseJetDeriv V V' := by
  intro ws
  induction ws using List.reverseRecOn generalizing V V' with
  | nil =>
      intro τ y
      exact hCoord 0 Fin.elim0 τ y
  | append_singleton ws w ih =>
      intro τ y
      have hfun : (fun τ' => dirSpatialJet (V τ') (ws ++ [w]) y) =
          fun τ' => ∑ j : Fin 3, (w j) • dirSpatialJet (V τ') (ws ++ [coordinateVector j]) y := by
        funext τ'
        exact congrFun (dirSpatialJet_append_singleton_eq_sum_coord (hV τ') ws w) y
      have hval : dirSpatialJet (V' τ) (ws ++ [w]) y =
          ∑ j : Fin 3, (w j) • dirSpatialJet (V' τ) (ws ++ [coordinateVector j]) y :=
        congrFun (dirSpatialJet_append_singleton_eq_sum_coord (hV' τ) ws w) y
      rw [hfun, hval]
      refine hasDerivAt_finset_sum Finset.univ fun j _ => ?_
      have hd_j : HasDerivAt
          (fun τ' => dirSpatialJet (V τ') (ws ++ [coordinateVector j]) y)
          (dirSpatialJet (V' τ) (ws ++ [coordinateVector j]) y) τ := by
        have hfun_j : (fun τ' => dirSpatialJet (V τ') (ws ++ [coordinateVector j]) y) =
            fun τ' => dirSpatialJet (dirSpatialJet (V τ') [coordinateVector j]) ws y := by
          funext τ'
          exact (congrFun (HigherPhaseSub.dirSpatialJet_append (V τ') ws [coordinateVector j]) y).symm
        have hval_j : dirSpatialJet (V' τ) (ws ++ [coordinateVector j]) y =
            dirSpatialJet (dirSpatialJet (V' τ) [coordinateVector j]) ws y :=
          (congrFun (HigherPhaseSub.dirSpatialJet_append (V' τ) ws [coordinateVector j]) y).symm
        rw [hfun_j, hval_j]
        refine ih
          (fun τ' => JointSmoothSub.contDiff_infty_dirSpatialJet (hV τ') [coordinateVector j])
          (fun τ' => JointSmoothSub.contDiff_infty_dirSpatialJet (hV' τ') [coordinateVector j])
          (fun k α τ' y' => ?_) τ y
        have h1 : (fun s => dirSpatialJet (dirSpatialJet (V s) [coordinateVector j]) (coordWord α) y') =
            fun s => dirSpatialJet (V s) (coordWord (Fin.snoc α j)) y' := by
          funext s
          rw [HigherPhaseSub.dirSpatialJet_append (V s) (coordWord α) [coordinateVector j],
            coordWord_snoc]
        have h2 : dirSpatialJet (dirSpatialJet (V' τ') [coordinateVector j]) (coordWord α) y' =
            dirSpatialJet (V' τ') (coordWord (Fin.snoc α j)) y' := by
          rw [HigherPhaseSub.dirSpatialJet_append (V' τ') (coordWord α) [coordinateVector j],
            coordWord_snoc]
        rw [h1, h2]
        exact hCoord (k + 1) (Fin.snoc α j) τ' y'
      exact HasDerivAt.const_smul (w j) hd_j

/-! ## 3. Radial drift commutator and Morrey-upgraded `IsUniformSmoothL4SliceFamily` -/

/-- Single-direction commutator between `dirSpatialJet · [w]` and `spatialRadialDrift`:
`D_w ((y · ∇)F) = (y · ∇)(D_w F) + D_w F`. -/
theorem dirSpatialJet_spatialRadialDrift_singleton {F : SpatialField}
    (hF : ContDiff ℝ ∞ F) (w : Space) :
    dirSpatialJet (spatialRadialDrift F) [w] =
      spatialRadialDrift (dirSpatialJet F [w]) + dirSpatialJet F [w] := by
  funext y
  have hdF : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hrad : HasFDerivAt (spatialRadialDrift F)
      ((fderiv ℝ F y).comp (ContinuousLinearMap.id ℝ Space) +
        (fderiv ℝ (fderiv ℝ F) y).flip y) y :=
    (hdF y).hasFDerivAt.clm_apply (hasFDerivAt_id y)
  have h1 : dirSpatialJet (spatialRadialDrift F) [w] y =
      fderiv ℝ F y w + fderiv ℝ (fderiv ℝ F) y w y := by
    change fderiv ℝ (spatialRadialDrift F) y w = _
    rw [hrad.fderiv]
    rfl
  have hjet : HasFDerivAt (dirSpatialJet F [w])
      ((ContinuousLinearMap.apply ℝ Space w).comp (fderiv ℝ (fderiv ℝ F) y)) y :=
    ((ContinuousLinearMap.apply ℝ Space w).hasFDerivAt).comp y (hdF y).hasFDerivAt
  have h2 : spatialRadialDrift (dirSpatialJet F [w]) y =
      fderiv ℝ (fderiv ℝ F) y y w := by
    change fderiv ℝ (dirSpatialJet F [w]) y y = _
    rw [hjet.fderiv]
    rfl
  have hsymm : fderiv ℝ (fderiv ℝ F) y w y = fderiv ℝ (fderiv ℝ F) y y w :=
    (hF.contDiffAt.isSymmSndFDerivAt (n := ∞) (by simp)).eq w y
  change dirSpatialJet (spatialRadialDrift F) [w] y =
    spatialRadialDrift (dirSpatialJet F [w]) y + dirSpatialJet F [w] y
  rw [h1, h2, hsymm, add_comm]
  rfl

/-- All-order commutator between `dirSpatialJet · ws` and `spatialRadialDrift`:
`dirSpatialJet (spatialRadialDrift F) ws = spatialRadialDrift (dirSpatialJet F ws) + (ws.length : ℝ) • dirSpatialJet F ws`. -/
theorem dirSpatialJet_spatialRadialDrift {F : SpatialField}
    (hF : ContDiff ℝ ∞ F) (ws : List Space) :
    dirSpatialJet (spatialRadialDrift F) ws =
      spatialRadialDrift (dirSpatialJet F ws) + (ws.length : ℝ) • dirSpatialJet F ws := by
  induction ws with
  | nil =>
      funext y
      simp [dirSpatialJet]
  | cons w ws ih =>
      have hws : ContDiff ℝ ∞ (dirSpatialJet F ws) :=
        JointSmoothSub.contDiff_infty_dirSpatialJet hF ws
      have hrad_ws : ContDiff ℝ ∞ (spatialRadialDrift (dirSpatialJet F ws)) :=
        HigherPhaseSub.contDiff_infty_spatialRadialDrift hws
      have hcons : dirSpatialJet (spatialRadialDrift F) (w :: ws) =
          dirSpatialJet (dirSpatialJet (spatialRadialDrift F) ws) [w] := rfl
      rw [hcons, ih,
        HigherPhaseSub.dirSpatialJet_add hrad_ws
          (G := (ws.length : ℝ) • dirSpatialJet F ws)
          (hws.const_smul (ws.length : ℝ)) [w],
        HigherPhaseSub.dirSpatialJet_smul (ws.length : ℝ) hws [w],
        dirSpatialJet_spatialRadialDrift_singleton hws w]
      funext y
      simp only [Pi.add_apply, Pi.smul_apply, List.length_cons, Nat.cast_add, Nat.cast_one]
      change (spatialRadialDrift (dirSpatialJet F (w :: ws)) y + dirSpatialJet F (w :: ws) y) +
          (ws.length : ℝ) • dirSpatialJet F (w :: ws) y =
        spatialRadialDrift (dirSpatialJet F (w :: ws)) y +
          ((ws.length : ℝ) + 1) • dirSpatialJet F (w :: ws) y
      rw [add_smul, one_smul, add_assoc, add_comm (dirSpatialJet F (w :: ws) y)]

/-- Unconditional 3D Morrey upgrade: any slice-smooth family `V : ℝ → SpatialField` with uniform
`L⁴(ℝ³)` bounds on all spatial derivatives lies in `IsUniformSmoothL4SliceFamily`. -/
theorem sliceFamily_of_contDiff_and_l4 {V : ℝ → SpatialField}
    (hSmooth : ∀ (k : ℕ) (τ : ℝ), ContDiff ℝ k (V τ))
    (hL4 : ∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ,
      eLpNorm (fun y => iteratedFDeriv ℝ k (V τ) y) 4 volume ≤ ENNReal.ofReal M) :
    IsUniformSmoothL4SliceFamily V :=
  isUniformSmoothL4SliceFamily_of_morreyL4
    (smoothMorreyL4Bound_of_field smoothMorreyL4FieldBound_proof) V hSmooth hL4

/-- If `U₀ ∈ IsUniformSmoothL4SliceFamily` and `spatialRadialDrift (U₀ τ)` has uniform `L⁴(ℝ³)`
bounds on all iterated spatial derivatives, then `fun τ => spatialRadialDrift (U₀ τ)` lies in
`IsUniformSmoothL4SliceFamily`. -/
theorem sliceFamily_spatialRadialDrift_of_l4 {U₀ : ℝ → SpatialField}
    (hU₀ : IsUniformSmoothL4SliceFamily U₀)
    (hL4 : ∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ,
      eLpNorm (fun y => iteratedFDeriv ℝ k (spatialRadialDrift (U₀ τ)) y) 4 volume ≤
        ENNReal.ofReal M) :
    IsUniformSmoothL4SliceFamily (fun τ => spatialRadialDrift (U₀ τ)) :=
  sliceFamily_of_contDiff_and_l4
    (fun k τ =>
      (HigherPhaseSub.contDiff_infty_spatialRadialDrift
        (HigherPhaseSub.sliceFamily_contDiff_infty hU₀ τ)).of_le (by exact_mod_cast le_top))
    hL4

/-! ## 4. First-order projected evolution operator `bgPhaseDerivTower ν U₀ 1` -/

/-- At order `m = 0`, the binomial Leibniz sum `leibnizBilinearSum B U 0` reduces to `B (U 0) (U 0)`. -/
@[simp]
theorem leibnizBilinearSum_zero
    (B : (ℝ → SpatialField) → (ℝ → SpatialField) → (ℝ → SpatialField))
    (U : ℕ → ℝ → SpatialField) :
    leibnizBilinearSum B U 0 = B (U 0) (U 0) := by
  funext τ y
  simp [leibnizBilinearSum]

/-- Explicit formula for the first-order stage `bgPhaseDerivTower ν U₀ 1` of the concrete phase
derivative tower:
`bgPhaseDerivTower ν U₀ 1 = (fun τ => spatialProjectedLin ν (U₀ τ)) - smoothConvectiveLeray U₀ U₀`. -/
theorem bgPhaseDerivTower_one (ν : ℝ) (U₀ : ℝ → SpatialField) :
    bgPhaseDerivTower ν U₀ 1 =
      (fun τ => spatialProjectedLin ν (U₀ τ)) - smoothConvectiveLeray U₀ U₀ := by
  rw [HigherPhaseSub.bgPhaseDerivTower_succ ν U₀ 0,
    HigherPhaseSub.bgPhaseDerivTower_zero,
    leibnizBilinearSum_zero,
    HigherPhaseSub.bgPhaseDerivTower_zero]

/-- If `U₀` and its radial drift `fun τ => spatialRadialDrift (U₀ τ)` lie in
`IsUniformSmoothL4SliceFamily`, then the projected linear drift-diffusion-reaction term
`fun τ => spatialProjectedLin ν (U₀ τ)` lies in `IsUniformSmoothL4SliceFamily`. -/
theorem sliceFamily_spatialProjectedLin (ν : ℝ) {U₀ : ℝ → SpatialField}
    (hU₀ : IsUniformSmoothL4SliceFamily U₀)
    (hRad : IsUniformSmoothL4SliceFamily (fun τ => spatialRadialDrift (U₀ τ))) :
    IsUniformSmoothL4SliceFamily (fun τ => spatialProjectedLin ν (U₀ τ)) :=
  HigherPhaseSub.sliceFamily_add
    (HigherPhaseSub.sliceFamily_smul (1 / 2 : ℝ) hRad)
    (HigherPhaseSub.sliceFamily_spatialDiffReact ν hU₀)

/-- From `SmoothLerayRepExists` and the proved 3D Morrey embedding `smoothMorreyL4FieldBound_proof`,
`smoothConvectiveLeray V W` lies in `IsUniformSmoothL4SliceFamily` whenever `V` and `W` do. -/
theorem sliceFamily_smoothConvectiveLeray_of_repExists (hRep : SmoothLerayRepExists)
    {V W : ℝ → SpatialField}
    (hV : IsUniformSmoothL4SliceFamily V) (hW : IsUniformSmoothL4SliceFamily W) :
    IsUniformSmoothL4SliceFamily (smoothConvectiveLeray V W) :=
  (SmoothLeraySliceSub.sliceFamily_smoothLeraySlice_of_repExists hRep
    (fun τ => spatialConvect (V τ) (W τ))
    (HigherPhaseSub.sliceFamily_spatialConvect hV hW)).2

/-- From `SmoothLerayRepExists`, if `U₀` and `fun τ => spatialRadialDrift (U₀ τ)` lie in
`IsUniformSmoothL4SliceFamily`, then the first-order projected evolution field
`bgPhaseDerivTower ν U₀ 1` lies in `IsUniformSmoothL4SliceFamily`. -/
theorem sliceFamily_bgPhaseDerivTower_one (hRep : SmoothLerayRepExists)
    (ν : ℝ) {U₀ : ℝ → SpatialField}
    (hU₀ : IsUniformSmoothL4SliceFamily U₀)
    (hRad : IsUniformSmoothL4SliceFamily (fun τ => spatialRadialDrift (U₀ τ))) :
    IsUniformSmoothL4SliceFamily (bgPhaseDerivTower ν U₀ 1) := by
  rw [bgPhaseDerivTower_one]
  exact HigherPhaseSub.sliceFamily_sub
    (sliceFamily_spatialProjectedLin ν hU₀ hRad)
    (sliceFamily_smoothConvectiveLeray_of_repExists hRep hU₀ hU₀)

/-- Packaging lemma: any candidate first-order phase derivative `U₁ : ℝ → SpatialField` in
`IsUniformSmoothL4SliceFamily` that satisfies the coordinate-word phase derivative identity
for `bgField p z` witnesses the existential conclusion of `BgFirstPhaseDerivStep`. -/
theorem exists_firstPhaseDeriv_of_coordWord {p : Params} {z : p.Z}
    (hBg : IsUniformSmoothL4SliceFamily (bgField p z))
    {U₁ : ℝ → SpatialField}
    (hU₁ : IsUniformSmoothL4SliceFamily U₁)
    (hCoord : ∀ (k : ℕ) (α : Fin k → Fin 3) (τ : ℝ) (y : Space),
      HasDerivAt (fun τ' => dirSpatialJet (bgField p z τ') (coordWord α) y)
        (dirSpatialJet (U₁ τ) (coordWord α) y) τ) :
    ∃ U₁ : ℝ → SpatialField,
      (∀ (k : ℕ) (τ : ℝ), ContDiff ℝ k (U₁ τ)) ∧
      (∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ,
        eLpNorm (fun y => iteratedFDeriv ℝ k (U₁ τ) y) 4 volume ≤ ENNReal.ofReal M) ∧
      ∀ (ws : List Space) (τ : ℝ) (y : Space),
        HasDerivAt (fun τ' => dirSpatialJet (bgField p z τ') ws y)
          (dirSpatialJet (U₁ τ) ws y) τ :=
  ⟨U₁, hU₁.slice_contDiff, hU₁.l4_bounded,
    hasPhaseJetDeriv_of_coordWord
      (HigherPhaseSub.sliceFamily_contDiff_infty hBg)
      (HigherPhaseSub.sliceFamily_contDiff_infty hU₁)
      hCoord⟩

end PhaseDerivStepSub

/-! ## 5. Atomic PDE leaves and conditional assembly of `BgFirstPhaseDerivStep` -/

/-- **Leaf 1 (`PartII-b:S3/1/1/2/1`, `BgFirstRadialDriftL4`)**
(`the November 2 reference manuscript`,
lines 2519-2523 and 2559-2562: "The projected equation is $A_0 U + \mathbb{P}(U \cdot \nabla U) = 0$
with zero residual. ... On positive physical-time compact intervals the resulting $C_\tau W^{k,4}$
regularity and the projected equation give all time derivatives"): under the regime and all-order
spatial regularity hypotheses of `BgFirstPhaseDerivStep` (with joint smoothness of `p.raw` and
`p.inlet i`), every spatial derivative order `k : ℕ` of the radial drift
`spatialRadialDrift (bgField p z τ)` is bounded in `L⁴(ℝ³)` uniformly in `τ` (from the compact
support / weighted decay of `p.raw` and `p.inlet i` and the maximal-graph membership of all
iterated spatial derivatives `g α : B0411.D p.period p.ν q0E` of `p.wOf z`).
Retired fixed-`y` leaf: superseded by the comoving leaf `BgComovingFirstEquation`
(`PartII-b:S3/1/1/2/1`, `Sub/PartII-b_S3_1_comoving.lean`). -/
def BgFirstRadialDriftL4 : Prop :=
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
      (Blueprint.IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ)) →
      (∀ i : Fin 2, Blueprint.IsBoundedBackground (p.inlet i) ∧
        ∀ τ, IsSolenoidal (p.inlet i τ)) →
      ∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ,
        eLpNorm (fun y => iteratedFDeriv ℝ k (spatialRadialDrift (bgField p z τ)) y) 4 volume ≤
          ENNReal.ofReal M

/-- **Leaf 2 (`PartII-b:S3/1/1/2/2`, `BgFirstPhaseCoordDeriv`)**
(`the November 2 reference manuscript`,
lines 2519-2523 and 2559-2562: "The projected equation is $A_0 U + \mathbb{P}(U \cdot \nabla U) = 0$
with zero residual. ... On positive physical-time compact intervals the resulting $C_\tau W^{k,4}$
regularity and the projected equation give all time derivatives"): under the regime and all-order
spatial regularity hypotheses of `BgFirstPhaseDerivStep` (with joint smoothness of `p.raw` and
`p.inlet i` and `IsUniformSmoothL4SliceFamily (fun τ => spatialRadialDrift (bgField p z τ))`),
the coordinate spatial jets `PhaseDerivStepSub.coordWord α` (`α : Fin k → Fin 3`) of `bgField p z`
are differentiable in `τ` with derivative given by the concrete projected evolution field
`bgPhaseDerivTower p.ν (bgField p z) 1`.
Retired fixed-`y` leaf: superseded by the comoving leaf `BgComovingFirstEquation`
(`PartII-b:S3/1/1/2/1`, `Sub/PartII-b_S3_1_comoving.lean`). -/
def BgFirstPhaseCoordDeriv : Prop :=
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
          (fun τ' => dirSpatialJet (bgField p z τ') (PhaseDerivStepSub.coordWord α) y)
          (dirSpatialJet (bgPhaseDerivTower p.ν (bgField p z) 1 τ)
            (PhaseDerivStepSub.coordWord α) y) τ

end UnforcedLeray.Short.IIb

end
