import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletJointSmooth
import UnforcedLeray.Cons.L2.BackgroundConcrete.PhasePairF

/-!
# `PartII-b:S3/1/2/2` decomposition (`Sub/PartII-b_S3_1_2_2.lean`, SP 2519-2523, 2559-2562)

Source of record: `the November 2 reference manuscript`
(SP), lines 2519-2523 and 2559-2562:
"The projected equation is $A_0 U + \mathbb{P}(U \cdot \nabla U) = 0$ with zero residual. ...
On positive physical-time compact intervals the resulting $C_\tau W^{k,4}$ regularity and the
projected equation give all time derivatives, so $U$ is jointly smooth through the axis."

## Proved here (zero `sorry`)

1. **Stage-0 and stage-1 identities for `leibnizBilinearSum` and `bgPhaseDerivTower`**:
   - `leibnizBilinearSum_zero`: `leibnizBilinearSum B U 0 = B (U 0) (U 0)`;
   - `bgPhaseDerivTower_one`:
     `bgPhaseDerivTower ν U₀ 1 = (fun τ => spatialProjectedLin ν (U₀ τ)) - smoothConvectiveLeray U₀ U₀`;
   - `eq_bgPhaseDerivTower_one_of_hasDerivAt`: reduces `U₁ = bgPhaseDerivTower ν U₀ 1` under
     `HasPhaseJetDeriv U₀ U₁` to the `ws = []` pointwise phase derivative
     `HasDerivAt (fun τ' => U₀ τ' y) (spatialProjectedLin ν (U₀ τ) y - smoothConvectiveLeray U₀ U₀ τ y) τ`
     via `(hU₁ [] τ y).unique`.
2. **Linearity and PDE inversion of `spatialRadialDrift`**:
   - `spatialRadialDrift_zero`, `spatialRadialDrift_add`, `spatialRadialDrift_smul`,
     `spatialRadialDrift_neg`, `spatialRadialDrift_sub`, `spatialRadialDrift_sum`,
     `spatialRadialDrift_eq_sum_coord_spatialPartial`;
   - `spatialRadialDrift_eq_of_spatialProjectedLin`:
     `spatialRadialDrift F = (2 : ℝ) • (spatialProjectedLin ν F - spatialDiffReact ν F)`;
   - `spatialRadialDrift_bgPhaseDerivTower_eq`: for every stage `m : ℕ`,
     `(fun τ => spatialRadialDrift (bgPhaseDerivTower ν U₀ m τ)) = (2 : ℝ) • (bgPhaseDerivTower ν U₀ (m + 1) + leibnizBilinearSum smoothConvectiveLeray (bgPhaseDerivTower ν U₀) m - (fun τ => spatialDiffReact ν (bgPhaseDerivTower ν U₀ m τ)))`.
3. **Unconditional `m_ord = 0` radial-drift slice regularity and equivalence with higher tower stages**:
   - `sliceFamily_spatialRadialDrift_of_tower_le`: if `bgPhaseDerivTower ν U₀ j` lies in
     `IsUniformSmoothL4SliceFamily` for `j ≤ m + 1`, then
     `fun τ => spatialRadialDrift (bgPhaseDerivTower ν U₀ m τ)` lies in `IsUniformSmoothL4SliceFamily`;
   - `sliceFamily_spatialRadialDrift_bgPhaseDerivTower_zero`: proves the `m_ord = 0` case
     `IsUniformSmoothL4SliceFamily (fun τ => spatialRadialDrift (bgPhaseDerivTower ν U₀ 0 τ))`
     directly from `U₀, U₁ ∈ IsUniformSmoothL4SliceFamily`, `U₁ = bgPhaseDerivTower ν U₀ 1`, and
     `SmoothLeraySliceRegularity`;
   - `sliceFamily_spatialRadialDrift_all_of_succ` and
     `sliceFamily_spatialRadialDrift_all_iff_tower_succ_succ`: reduces all `m_ord : ℕ` to
     `m_ord = m + 1` (`m ≥ 0`), or equivalently `IsUniformSmoothL4SliceFamily (bgPhaseDerivTower ν U₀ (m + 2))`.
4. **Distributional unpacking of `ProjectedEquation p z` via `RawRel`, `OrdRel`, `QuadRel`, and `L0D`**:
   - `cΔ_eq_nuLapD`, `cT_eq_T0D`, `A0_eq_L0D`, `hasPhaseOp_A0`, `phasePair_A0_eq_pairF`:
     identifies `p.A0 z` with `B0411.L0D (B0412.XToD (p.graphX z))` and its test pairing with
     `pairF p.period (L0T p.ν Φ) (fun x => rep (p.wOf z) x.1 x.2)`;
   - `projectedEquation_solTest_identity` and `projectedEquation_solTest_pairF`: unpacks
     `ProjectedEquation p z` on every solenoidal phase test `Φ` (`IsSolTest p.period Φ`) into the
     combined `pairF` identity of `p.raw`, `p.inlet i`, `p.wOf z`, and `p.uOf z`.
5. **Conditional assembly `bgProjectedEvolutionTowerSlice_of_parts`** of
   `BgProjectedEvolutionTowerSlice` (`PartII-b:S3/1/2/2`) from `SmoothLeraySliceRegularity`
   (`PartII-b:S3/1/2/1`), `RawJointSmooth` (`PartII-b:G4/4/1/1/2`),
   `BgProjectedPointwiseDeriv` (`PartII-b:S3/1/2/2/1`), and
   `BgHigherOrderRadialDriftSlice` (`PartII-b:S3/1/2/2/2`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.Blueprint

namespace ProjectedEvolutionSub

/-! ## 1. Stage-0 and stage-1 identities for `leibnizBilinearSum` and `bgPhaseDerivTower` -/

@[simp]
theorem leibnizBilinearSum_zero
    (B : (ℝ → SpatialField) → (ℝ → SpatialField) → (ℝ → SpatialField))
    (U : ℕ → ℝ → SpatialField) :
    leibnizBilinearSum B U 0 = B (U 0) (U 0) := by
  funext τ y
  simp [leibnizBilinearSum]

/-- Explicit formula for the first stage `m = 1` of `bgPhaseDerivTower`:
`bgPhaseDerivTower ν U₀ 1 = (fun τ => spatialProjectedLin ν (U₀ τ)) - smoothConvectiveLeray U₀ U₀`. -/
theorem bgPhaseDerivTower_one (ν : ℝ) (U₀ : ℝ → SpatialField) :
    bgPhaseDerivTower ν U₀ 1 =
      (fun τ => spatialProjectedLin ν (U₀ τ)) - smoothConvectiveLeray U₀ U₀ := by
  rw [HigherPhaseSub.bgPhaseDerivTower_succ ν U₀ 0, leibnizBilinearSum_zero,
    HigherPhaseSub.bgPhaseDerivTower_zero]

/-- If `HasPhaseJetDeriv U₀ U₁` holds and `τ' ↦ U₀ τ' y` has 1D derivative
`spatialProjectedLin ν (U₀ τ) y - smoothConvectiveLeray U₀ U₀ τ y` at every `(τ, y) ∈ ℝ × Space`,
then `U₁ = bgPhaseDerivTower ν U₀ 1` by uniqueness of 1D derivatives at `ws = []`. -/
theorem eq_bgPhaseDerivTower_one_of_hasDerivAt (ν : ℝ) {U₀ U₁ : ℝ → SpatialField}
    (hU₁ : HasPhaseJetDeriv U₀ U₁)
    (hEvol : ∀ (τ : ℝ) (y : Space),
      HasDerivAt (fun τ' : ℝ => U₀ τ' y)
        (spatialProjectedLin ν (U₀ τ) y - smoothConvectiveLeray U₀ U₀ τ y) τ) :
    U₁ = bgPhaseDerivTower ν U₀ 1 := by
  rw [bgPhaseDerivTower_one]
  funext τ y
  exact (hU₁ [] τ y).unique (hEvol τ y)

/-! ## 2. Linearity and PDE inversion of `spatialRadialDrift` -/

@[simp]
theorem spatialRadialDrift_zero :
    spatialRadialDrift 0 = 0 := by
  funext y
  simp [spatialRadialDrift]

theorem spatialRadialDrift_add {F G : SpatialField}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    spatialRadialDrift (F + G) = spatialRadialDrift F + spatialRadialDrift G := by
  funext y
  have hdF : DifferentiableAt ℝ F y := (hF.differentiable (by simp)) y
  have hdG : DifferentiableAt ℝ G y := (hG.differentiable (by simp)) y
  simp only [spatialRadialDrift, Pi.add_apply]
  rw [fderiv_add hdF hdG, add_apply]

theorem spatialRadialDrift_smul (c : ℝ) {F : SpatialField} (hF : ContDiff ℝ ∞ F) :
    spatialRadialDrift (c • F) = c • spatialRadialDrift F := by
  funext y
  have hdF : DifferentiableAt ℝ F y := (hF.differentiable (by simp)) y
  simp only [spatialRadialDrift, Pi.smul_apply]
  rw [fderiv_const_smul hdF, smul_apply]

theorem spatialRadialDrift_neg {F : SpatialField} (hF : ContDiff ℝ ∞ F) :
    spatialRadialDrift (-F) = -spatialRadialDrift F := by
  simpa [neg_one_smul] using spatialRadialDrift_smul (-1 : ℝ) hF

theorem spatialRadialDrift_sub {F G : SpatialField}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    spatialRadialDrift (F - G) = spatialRadialDrift F - spatialRadialDrift G := by
  have hnegG : ContDiff ℝ ∞ (-G) := hG.neg
  rw [sub_eq_add_neg, spatialRadialDrift_add hF hnegG, spatialRadialDrift_neg hG,
    ← sub_eq_add_neg]

theorem spatialRadialDrift_sum {ι : Type*} (s : Finset ι) {F : ι → SpatialField}
    (hF : ∀ i ∈ s, ContDiff ℝ ∞ (F i)) :
    spatialRadialDrift (fun y => ∑ i ∈ s, F i y) =
      fun y => ∑ i ∈ s, spatialRadialDrift (F i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 : (fun _ : Space => (0 : Space)) = (0 : SpatialField) := rfl
      simp [h0]
  | @insert a s ha ih =>
      have haF : ContDiff ℝ ∞ (F a) := hF a (Finset.mem_insert_self a s)
      have hsF : ∀ i ∈ s, ContDiff ℝ ∞ (F i) :=
        fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have hsumF : ContDiff ℝ ∞ (fun y => ∑ i ∈ s, F i y) :=
        ContDiff.sum fun i hi => hsF i hi
      funext y
      have hsplit : (fun y' => ∑ i ∈ insert a s, F i y') =
          F a + (fun y' => ∑ i ∈ s, F i y') := by
        funext y'; simp [Finset.sum_insert ha]
      rw [hsplit]
      have hadd := congrFun (spatialRadialDrift_add haF hsumF) y
      rw [Pi.add_apply, ih hsF] at hadd
      simpa [Finset.sum_insert ha] using hadd

/-- Coordinate decomposition of `spatialRadialDrift`:
`spatialRadialDrift F y = ∑ j : Fin 3, (y j) • spatialPartial j F y`. -/
theorem spatialRadialDrift_eq_sum_coord_spatialPartial (F : SpatialField) (y : Space) :
    spatialRadialDrift F y = ∑ j : Fin 3, (y j) • spatialPartial j F y :=
  HigherPhaseSub.spatialConvect_eq_sum id F y

/-- Algebraic inversion of `spatialProjectedLin`:
since `spatialProjectedLin ν F = (1/2) • spatialRadialDrift F + spatialDiffReact ν F`,
`spatialRadialDrift F = 2 • (spatialProjectedLin ν F - spatialDiffReact ν F)`. -/
theorem spatialRadialDrift_eq_of_spatialProjectedLin (ν : ℝ) (F : SpatialField) :
    spatialRadialDrift F = (2 : ℝ) • (spatialProjectedLin ν F - spatialDiffReact ν F) := by
  funext y
  simp only [spatialProjectedLin, Pi.smul_apply, add_sub_cancel_right, smul_smul]
  norm_num

/-- At every stage `m : ℕ` of `bgPhaseDerivTower ν U₀`, the radial drift family
`fun τ => spatialRadialDrift (bgPhaseDerivTower ν U₀ m τ)` is expressed purely in terms of
`bgPhaseDerivTower ν U₀ (m + 1)`, `leibnizBilinearSum smoothConvectiveLeray (bgPhaseDerivTower ν U₀) m`,
and `spatialDiffReact ν (bgPhaseDerivTower ν U₀ m τ)`. -/
theorem spatialRadialDrift_bgPhaseDerivTower_eq (ν : ℝ) (U₀ : ℝ → SpatialField) (m : ℕ) :
    (fun τ => spatialRadialDrift (bgPhaseDerivTower ν U₀ m τ)) =
      (2 : ℝ) •
        (bgPhaseDerivTower ν U₀ (m + 1) +
          leibnizBilinearSum smoothConvectiveLeray (bgPhaseDerivTower ν U₀) m -
          (fun τ => spatialDiffReact ν (bgPhaseDerivTower ν U₀ m τ))) := by
  funext τ y
  rw [HigherPhaseSub.bgPhaseDerivTower_succ ν U₀ m,
    spatialRadialDrift_eq_of_spatialProjectedLin ν (bgPhaseDerivTower ν U₀ m τ)]
  simp only [Pi.smul_apply, Pi.sub_apply, sub_add_cancel]

/-! ## 3. Radial-drift slice regularity at `m_ord = 0` and reduction to higher tower stages -/

/-- If `SmoothLeraySliceRegularity` holds and `bgPhaseDerivTower ν U₀ j` lies in
`IsUniformSmoothL4SliceFamily` for all `j ≤ m + 1`, then
`fun τ => spatialRadialDrift (bgPhaseDerivTower ν U₀ m τ)` lies in `IsUniformSmoothL4SliceFamily`. -/
theorem sliceFamily_spatialRadialDrift_of_tower_le
    (hLeray : SmoothLeraySliceRegularity)
    (ν : ℝ) {U₀ : ℝ → SpatialField} {m : ℕ}
    (hTower : ∀ j ≤ m + 1, IsUniformSmoothL4SliceFamily (bgPhaseDerivTower ν U₀ j)) :
    IsUniformSmoothL4SliceFamily
      (fun τ => spatialRadialDrift (bgPhaseDerivTower ν U₀ m τ)) := by
  rw [spatialRadialDrift_bgPhaseDerivTower_eq ν U₀ m]
  have hSucc : IsUniformSmoothL4SliceFamily (bgPhaseDerivTower ν U₀ (m + 1)) :=
    hTower (m + 1) (le_refl (m + 1))
  have hConv : IsUniformSmoothL4SliceFamily
      (leibnizBilinearSum smoothConvectiveLeray (bgPhaseDerivTower ν U₀) m) :=
    HigherPhaseSub.sliceFamily_leibnizBilinearSum
      (HigherPhaseSub.sliceFamily_smoothConvectiveLeray hLeray)
      (fun j hj => hTower j (hj.trans (Nat.le_succ m)))
  have hDiff : IsUniformSmoothL4SliceFamily
      (fun τ => spatialDiffReact ν (bgPhaseDerivTower ν U₀ m τ)) :=
    HigherPhaseSub.sliceFamily_spatialDiffReact ν (hTower m (Nat.le_succ m))
  exact HigherPhaseSub.sliceFamily_smul (2 : ℝ)
    (HigherPhaseSub.sliceFamily_sub (HigherPhaseSub.sliceFamily_add hSucc hConv) hDiff)

/-- **Unconditional `m_ord = 0` radial-drift slice regularity**: once `U₁ = bgPhaseDerivTower ν U₀ 1`
is established and `U₀, U₁ ∈ IsUniformSmoothL4SliceFamily`, the stage-0 radial drift
`fun τ => spatialRadialDrift (bgPhaseDerivTower ν U₀ 0 τ)` lies in `IsUniformSmoothL4SliceFamily`
by `sliceFamily_spatialRadialDrift_of_tower_le` and `SmoothLeraySliceRegularity`. -/
theorem sliceFamily_spatialRadialDrift_bgPhaseDerivTower_zero
    (hLeray : SmoothLeraySliceRegularity)
    (ν : ℝ) {U₀ U₁ : ℝ → SpatialField}
    (hU₀ : IsUniformSmoothL4SliceFamily U₀)
    (hU₁ : IsUniformSmoothL4SliceFamily U₁)
    (hEq : U₁ = bgPhaseDerivTower ν U₀ 1) :
    IsUniformSmoothL4SliceFamily
      (fun τ => spatialRadialDrift (bgPhaseDerivTower ν U₀ 0 τ)) := by
  refine sliceFamily_spatialRadialDrift_of_tower_le hLeray ν (m := 0) fun j hj => ?_
  rcases Nat.of_le_succ hj with hj0 | rfl
  · have hj0' : j = 0 := Nat.le_zero.1 hj0
    subst hj0'
    exact hU₀
  · rwa [← hEq]

/-- Given the proved `m_ord = 0` base case, `IsUniformSmoothL4SliceFamily` for
`fun τ => spatialRadialDrift (bgPhaseDerivTower ν U₀ m_ord τ)` holds for all `m_ord : ℕ` if and only
if it holds for all positive orders `m_ord = m + 1` (`m : ℕ`). -/
theorem sliceFamily_spatialRadialDrift_all_of_succ
    (hLeray : SmoothLeraySliceRegularity)
    (ν : ℝ) {U₀ U₁ : ℝ → SpatialField}
    (hU₀ : IsUniformSmoothL4SliceFamily U₀)
    (hU₁ : IsUniformSmoothL4SliceFamily U₁)
    (hEq : U₁ = bgPhaseDerivTower ν U₀ 1)
    (hSucc : ∀ m : ℕ,
      IsUniformSmoothL4SliceFamily
        (fun τ => spatialRadialDrift (bgPhaseDerivTower ν U₀ (m + 1) τ))) :
    ∀ m_ord : ℕ,
      IsUniformSmoothL4SliceFamily
        (fun τ => spatialRadialDrift (bgPhaseDerivTower ν U₀ m_ord τ))
  | 0 => sliceFamily_spatialRadialDrift_bgPhaseDerivTower_zero hLeray ν hU₀ hU₁ hEq
  | m + 1 => hSucc m

/-- Equivalence between radial-drift slice regularity at all orders `m_ord : ℕ` and slice regularity
of the higher tower stages `bgPhaseDerivTower ν U₀ (m + 2)` (`m : ℕ`), once `U₀` and
`U₁ = bgPhaseDerivTower ν U₀ 1` lie in `IsUniformSmoothL4SliceFamily`. -/
theorem sliceFamily_spatialRadialDrift_all_iff_tower_succ_succ
    (hLeray : SmoothLeraySliceRegularity)
    (ν : ℝ) {U₀ U₁ : ℝ → SpatialField}
    (hU₀ : IsUniformSmoothL4SliceFamily U₀)
    (hU₁ : IsUniformSmoothL4SliceFamily U₁)
    (hEq : U₁ = bgPhaseDerivTower ν U₀ 1) :
    (∀ m_ord : ℕ,
      IsUniformSmoothL4SliceFamily
        (fun τ => spatialRadialDrift (bgPhaseDerivTower ν U₀ m_ord τ))) ↔
    (∀ m : ℕ, IsUniformSmoothL4SliceFamily (bgPhaseDerivTower ν U₀ (m + 2))) := by
  constructor
  · intro hRad m
    exact HigherPhaseSub.sliceFamily_bgPhaseDerivTower hLeray ν hU₀ hRad (m + 2)
  · intro hTower m_ord
    have hAll : ∀ j : ℕ, IsUniformSmoothL4SliceFamily (bgPhaseDerivTower ν U₀ j) := by
      intro j
      rcases j with _ | _ | m
      · exact hU₀
      · rwa [← hEq]
      · exact hTower m
    exact sliceFamily_spatialRadialDrift_of_tower_le hLeray ν (fun j _ => hAll j)

/-! ## 4. Distributional unpacking of `ProjectedEquation p z` -/

theorem cΔ_eq_nuLapD (p : Params) (z : p.Z) :
    cΔ p.period (z : Amb p.period) = B0411.nuLapD (B0412.XToD (p.graphX z)) := by
  obtain ⟨hw, ha, _⟩ := (mem_XGraph_iff (P := p.period) (ν := p.ν) (q := q0E)).1
    ((mem_graphSpace p.period).1 z.2).1
  have hX : (⟨cw p.period (z : Amb p.period), hw⟩ : X p.period p.ν q0E) = p.graphX z := rfl
  rw [← ha, hX]
  rfl

theorem cT_eq_T0D (p : Params) (z : p.Z) :
    cT p.period (z : Amb p.period) = B0411.T0D (B0412.XToD (p.graphX z)) := by
  obtain ⟨hw, _, hb⟩ := (mem_XGraph_iff (P := p.period) (ν := p.ν) (q := q0E)).1
    ((mem_graphSpace p.period).1 z.2).1
  have hX : (⟨cw p.period (z : Amb p.period), hw⟩ : X p.period p.ν q0E) = p.graphX z := rfl
  rw [← hb, hX]
  rfl

/-- For any state `z : p.Z`, `p.A0 z` coincides with `B0411.L0D (B0412.XToD (p.graphX z))`. -/
theorem A0_eq_L0D (p : Params) (z : p.Z) :
    p.A0 z = B0411.L0D (B0412.XToD (p.graphX z)) := by
  unfold Params.A0 B0411.L0D
  rw [cT_eq_T0D, cΔ_eq_nuLapD]
  have hsmul : ((1 / 2 : ℝ) • cw p.period (z : Amb p.period)) =
      (1 / 2 : ℂ) • ((B0412.XToD (p.graphX z) : B0411.D p.period p.ν q0E) : Yq p.period q0E) := by
    change ((1 / 2 : ℝ) : ℂ) •
      ((B0412.XToD (p.graphX z) : B0411.D p.period p.ν q0E) : Yq p.period q0E) = _
    push_cast
    rfl
  rw [hsmul]

/-- `p.A0 z` is the distributional `L0T p.ν` image of `p.wOf z`. -/
theorem hasPhaseOp_A0 (p : Params) (z : p.Z) :
    HasPhaseOp (L0T p.ν) (p.wOf z) (p.A0 z) := by
  rw [A0_eq_L0D]
  exact B0411.hasPhaseOp_L0D (B0412.XToD (p.graphX z))

/-- Pairing `p.A0 z` against any phase test `Φ` equals `pairF p.period (L0T p.ν Φ) (rep (p.wOf z))`. -/
theorem phasePair_A0_eq_pairF (p : Params) (z : p.Z) {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest p.period Φ) :
    phasePair p.period q0E Φ (p.A0 z) =
      pairF p.period (L0T p.ν Φ) (fun x => rep (p.wOf z) x.1 x.2) := by
  rw [← hasPhaseOp_A0 p z Φ hΦ, phasePair_eq_pairF_rep (isPhaseTest_L0T hΦ p.ν) (p.wOf z)]

/-- Unpacks `ProjectedEquation p z` (`∃ gF gL gQ, RawRel gF ∧ OrdRel z gL ∧ QuadRel z z gQ ∧ gF + gL + gQ = 0`)
into the vanishing of the combined pairing on every solenoidal phase test `Φ` (`IsSolTest p.period Φ`). -/
theorem projectedEquation_solTest_identity (p : Params) (z : p.Z)
    (hProj : ProjectedEquation p z) {Φ : ℝ × Space → CVec3} (hΦ : IsSolTest p.period Φ) :
    (pairF p.period (L0T p.ν Φ) p.Ufun - pairF p.period (advT p.Ufun Φ) p.Ufun) +
      (phasePair p.period q0E Φ (p.A0 z) +
        pairF p.period (convT p.raw Φ) (fun x => rep (p.wOf z) x.1 x.2) +
        ∑ i : Fin 2, (p.coord z i : ℂ) *
          (pairF p.period (L0T p.ν Φ) (p.Efun i) + pairF p.period (convT p.raw Φ) (p.Efun i))) -
      pairF p.period (advT (p.uOf z) Φ) (p.uOf z) = 0 := by
  obtain ⟨gF, gL, gQ, hRaw, hOrd, hQuad, hSum⟩ := hProj
  have hPairSum :
      phasePair p.period q0E Φ gF + phasePair p.period q0E Φ gL + phasePair p.period q0E Φ gQ = 0 := by
    rw [← map_add, ← map_add, hSum, map_zero]
  rw [hRaw Φ hΦ, hOrd Φ hΦ, hQuad Φ hΦ] at hPairSum
  linear_combination hPairSum

/-- Explicit `pairF` form of `ProjectedEquation p z` on every solenoidal phase test `Φ`: replaces
`phasePair p.period q0E Φ (p.A0 z)` by `pairF p.period (L0T p.ν Φ) (fun x => rep (p.wOf z) x.1 x.2)`. -/
theorem projectedEquation_solTest_pairF (p : Params) (z : p.Z)
    (hProj : ProjectedEquation p z) {Φ : ℝ × Space → CVec3} (hΦ : IsSolTest p.period Φ) :
    (pairF p.period (L0T p.ν Φ) p.Ufun - pairF p.period (advT p.Ufun Φ) p.Ufun) +
      (pairF p.period (L0T p.ν Φ) (fun x => rep (p.wOf z) x.1 x.2) +
        pairF p.period (convT p.raw Φ) (fun x => rep (p.wOf z) x.1 x.2) +
        ∑ i : Fin 2, (p.coord z i : ℂ) *
          (pairF p.period (L0T p.ν Φ) (p.Efun i) + pairF p.period (convT p.raw Φ) (p.Efun i))) -
      pairF p.period (advT (p.uOf z) Φ) (p.uOf z) = 0 := by
  rw [← phasePair_A0_eq_pairF p z hΦ.1]
  exact projectedEquation_solTest_identity p z hProj hΦ

end ProjectedEvolutionSub

/-! ## 5. Atomic PDE leaves and conditional assembly of `BgProjectedEvolutionTowerSlice` -/

/-- **Leaf 1 (`PartII-b:S3/1/2/2/1`, `BgProjectedPointwiseDeriv`)**
(`the November 2 reference manuscript`,
lines 2519-2523 and 2559-2562: "The projected equation is $A_0 U + \mathbb{P}(U \cdot \nabla U) = 0$
with zero residual"): under `SmoothLeraySliceRegularity` and the regime and all-order spatial
regularity hypotheses of `BgProjectedEvolutionTowerSlice` (including joint smoothness of `p.raw`
and `p.inlet i`), when `bgField p z` has a smooth `W^{k,4}` first phase-jet derivative `U₁`, its
pointwise 1D phase derivative at `(τ, y) ∈ ℝ × Space` satisfies the classical projected evolution
`∂_τ U = spatialProjectedLin p.ν U - smoothConvectiveLeray U U`.
Composed by task `PartII-b:S3/1/2/2` via `bgProjectedEvolutionTowerSlice_of_parts`. -/
def BgProjectedPointwiseDeriv : Prop :=
  SmoothLeraySliceRegularity →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 → ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) →
      (∀ i : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2)) →
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
        HasPhaseJetDeriv (bgField p z) U₁ →
        ∀ (τ : ℝ) (y : Space),
          HasDerivAt (fun τ' : ℝ => bgField p z τ' y)
            (spatialProjectedLin p.ν (bgField p z τ) y -
              smoothConvectiveLeray (bgField p z) (bgField p z) τ y) τ

/-- **Leaf 2 (`PartII-b:S3/1/2/2/2`, `BgHigherOrderRadialDriftSlice`, `m_ord ≥ 1`)**
(`the November 2 reference manuscript`,
lines 2559-2562: "On positive physical-time compact intervals the resulting $C_\tau W^{k,4}$
regularity and the projected equation give all time derivatives"): under `SmoothLeraySliceRegularity`
and the regime and all-order spatial regularity hypotheses of `BgProjectedEvolutionTowerSlice`
(including joint smoothness of `p.raw` and `p.inlet i`), once the `m_ord = 0` radial drift is
controlled by `sliceFamily_spatialRadialDrift_bgPhaseDerivTower_zero`, each higher radial drift
`fun τ => spatialRadialDrift (bgPhaseDerivTower p.ν (bgField p z) (m_ord + 1) τ)` (`m_ord : ℕ`)
lies in `IsUniformSmoothL4SliceFamily`.
Composed by task `PartII-b:S3/1/2/2` via `bgProjectedEvolutionTowerSlice_of_parts`. -/
def BgHigherOrderRadialDriftSlice : Prop :=
  SmoothLeraySliceRegularity →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 → ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) →
      (∀ i : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2)) →
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
        HasPhaseJetDeriv (bgField p z) U₁ →
        U₁ = bgPhaseDerivTower p.ν (bgField p z) 1 →
        ∀ m_ord : ℕ,
          IsUniformSmoothL4SliceFamily
            (fun τ => spatialRadialDrift (bgPhaseDerivTower p.ν (bgField p z) (m_ord + 1) τ))

/-- Conditional assembly of `BgProjectedEvolutionTowerSlice` (`PartII-b:S3/1/2/2`, SP 2519-2523,
2559-2562) from `SmoothLeraySliceRegularity` (`PartII-b:S3/1/2/1`), `RawJointSmooth`
(`PartII-b:G4/4/1/1/2`), `BgProjectedPointwiseDeriv` (`PartII-b:S3/1/2/2/1`), and
`BgHigherOrderRadialDriftSlice` (`PartII-b:S3/1/2/2/2`), proving `m_ord = 0` unconditionally via
`ProjectedEvolutionSub.sliceFamily_spatialRadialDrift_bgPhaseDerivTower_zero` and supplying
`inletJointSmooth` directly. -/
theorem bgProjectedEvolutionTowerSlice_of_parts
    (hLeray : SmoothLeraySliceRegularity)
    (hRawSmooth : RawJointSmooth)
    (hDeriv : BgProjectedPointwiseDeriv)
    (hRadSucc : BgHigherOrderRadialDriftSlice) :
    BgProjectedEvolutionTowerSlice := by
  intro Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₁, hν₁, hD⟩ := hDeriv hLeray Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₂, hν₂, hR⟩ := hRadSucc hLeray Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₃, hν₃, hRawS⟩ := hRawSmooth Sig lam q hSig hlam dm dp hdm
  obtain ⟨ν₄, hν₄, hInS⟩ := inletJointSmooth Sig lam q hSig hlam dm dp hdm
  refine ⟨min (min ν₁ ν₂) (min ν₃ ν₄), lt_min (lt_min hν₁ hν₂) (lt_min hν₃ hν₄), ?_⟩
  intro p d hReg hν hAge hMode z hProj hz hGraph hSlice hRaw hInlet hBg U₁ hU₁Smooth hU₁Deriv
  have hν₁' : p.ν ≤ ν₁ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν₂' : p.ν ≤ ν₂ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν₃' : p.ν ≤ ν₃ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν₄' : p.ν ≤ ν₄ := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hRawCD : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) :=
    hRawS p d hReg hν₃' hAge hMode 0
  have hInCD : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2) :=
    hInS p d hReg hν₄' hAge hMode
  have hEvol :=
    hD p d hReg hν₁' hAge hMode hRawCD hInCD z hProj hz hGraph hSlice hRaw hInlet hBg U₁
      hU₁Smooth hU₁Deriv
  have hU₁Eq : U₁ = bgPhaseDerivTower p.ν (bgField p z) 1 :=
    ProjectedEvolutionSub.eq_bgPhaseDerivTower_one_of_hasDerivAt p.ν hU₁Deriv hEvol
  have hSucc :=
    hR p d hReg hν₂' hAge hMode hRawCD hInCD z hProj hz hGraph hSlice hRaw hInlet hBg U₁
      hU₁Smooth hU₁Deriv hU₁Eq
  exact ⟨hU₁Eq,
    ProjectedEvolutionSub.sliceFamily_spatialRadialDrift_all_of_succ
      hLeray p.ν hBg hU₁Smooth hU₁Eq hSucc⟩

end UnforcedLeray.Short.IIb

end
