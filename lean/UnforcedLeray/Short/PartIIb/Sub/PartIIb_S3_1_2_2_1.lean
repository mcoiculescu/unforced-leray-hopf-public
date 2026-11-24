import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_2_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_1_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_2_1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3
import UnforcedLeray.Short.PartIIb.Bridge.Tasks.LerayPairSol
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedSchemeTotalLinear
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedSchemeTotalResidual
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedSchemeConvectionAE

/-!
# `PartII-b_S3_1_2_2_1`: Sub-module for `PartII-b:S3/1/2/2/1` (`BgProjectedPointwiseDeriv`, SP 2519-2523, 2559-2562)

Source of record: `the November 2 reference manuscript`
(SP), lines 2519-2523 and 2559-2562:
"The projected equation is $A_0 U + \mathbb{P}(U \cdot \nabla U) = 0$ with zero residual. ...
On positive physical-time compact intervals the resulting $C_\tau W^{k,4}$ regularity and the
projected equation give all time derivatives, so $U$ is jointly smooth through the axis."

## Proved here (zero `sorry`)

1. **Concrete scheme-field identification, periodicity, solenoidality, and a.e. decomposition**:
   - `defaultBudget`: canonical `Budget` witness `⟨1, 0, 1⟩`;
   - `schemeField_eq_bgField`: `(p.scheme B).field z = bgField p z`;
   - `bgField_eq_rawAddState_ae`: `(fun x => realC (bgField p z x.1 x.2)) =ᵐ[volume.prod volume] fun x => p.Ufun x + p.uOf z x`;
   - `bgField_periodic`: `Function.Periodic (bgField p z) p.period` from `Params.schemeField_periodic`;
   - `bgField_isSolenoidal`: `∀ τ, IsSolenoidal (bgField p z τ)` when `p.period ≤ 1`, from
     `Params.schemeField_isSolenoidal`;
   - `bgField_convectionPair_eq_rawAddState`: equates the compact-test convection pairing of
     `bgField p z` with that of `p.Ufun + p.uOf z`.
2. **Compact-solenoidal weak equation for `bgField p z` from `ProjectedEquation p z`**:
   - `projectedEquation_compactResidual_split`: removes the raw/inlet cross convection from
     `ProjectedEvolutionSub.projectedEquation_solTest_pairF` using
     `selectedState_rawInletCross_pairF_sum_eq_zero`;
   - `projectedEquation_compactResidual_totalConvection`: combines the remaining convection terms
     into `pairF p.period (advT (fun x => p.Ufun x + p.uOf z x) Φ) (fun x => p.Ufun x + p.uOf z x)`;
   - `bgField_compactSolenoidal_weakEquation`: proves that for every `Φ` with
     `IsSolTest p.period Φ`,
     `pairF p.period (L0T p.ν Φ) (fun x => realC (bgField p z x.1 x.2)) = pairF p.period (advT (fun x => realC (bgField p z x.1 x.2)) Φ) (fun x => realC (bgField p z x.1 x.2))`.
3. **Joint continuity of all spatial jets, slice Leray projection pairing, and solenoidality**:
   - `continuous_jet_of_hasPhaseJetDeriv`: every spatial jet `(τ, y) ↦ dirSpatialJet (V τ) ws y`
     is jointly continuous on `ℝ × Space`;
   - `integral_inner_smoothLeraySlice_eq` and `integral_inner_smoothConvectiveLeray_eq`: for any
     continuous compactly supported solenoidal spatial test `a : Space → Space`, pairing against
     `smoothLeraySlice G τ` (resp. `smoothConvectiveLeray V W τ`) equals pairing against `G τ`
     (resp. `spatialConvect (V τ) (W τ)`);
   - `isSolenoidal_smoothLeraySlice` and `isSolenoidal_smoothConvectiveLeray`: every slice
     `smoothLeraySlice G τ` and `smoothConvectiveLeray V W τ` is distributionally solenoidal;
   - `eq_zero_of_isSolenoidal_and_spatialSolTest_orth` and
     `eq_bgPhaseDerivTower_one_of_slice_solenoidal_and_orth`: reduces slice equality
     `U₁ = bgPhaseDerivTower ν U₀ 1` to slicewise solenoidality and orthogonality against
     `SpatialSolTest` via `solSepSpatial` (`PartII-b:T10/org/2/3`).
4. **Atomic leaf definitions (`BgSolTestWeakIBP`, `BgSolTestOrthEqZero`) and conditional
   assemblies `bgSolTestWeakToPointwiseEq_of` and `bgProjectedPointwiseDeriv_of`**.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.B0414 UnforcedLeray.Blueprint
  UnforcedLeray.RieszLp

namespace PointwiseDerivSub

local instance fact_one_le_four_ptw : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance fact_one_le_conj_q0E_ptw : Fact (1 ≤ conjExp q0E) := ⟨by
  norm_num [PhaseSpace.conjExp, q0E, B0281.q0]⟩

/-- Canonical `Budget` witness used to instantiate budget-independent `Params.scheme` lemmas. -/
def defaultBudget : Budget := ⟨1, 0, 1⟩

/-- The concrete scheme field `(p.scheme B).field z` is definitionally `bgField p z`. -/
theorem schemeField_eq_bgField (p : Params) (B : Budget) (z : p.Z) :
    (p.scheme B).field z = bgField p z :=
  rfl

/-- Product-a.e. identification of `realC (bgField p z x.1 x.2)` with `p.Ufun x + p.uOf z x`. -/
theorem bgField_eq_rawAddState_ae (p : Params) (z : p.Z) :
    (fun x : ℝ × Space => realC (bgField p z x.1 x.2)) =ᵐ[
      (volume : Measure ℝ).prod (volume : Measure Space)]
      fun x => p.Ufun x + p.uOf z x := by
  simpa only [schemeField_eq_bgField] using
    Params.schemeField_eq_rawAddState_ae p defaultBudget z

/-- Exact `p.period`-periodicity of `bgField p z` from `hRaw` and `hInlet`. -/
theorem bgField_periodic (p : Params) (z : p.Z)
    (hRaw : p.RawLiftRegular) (hInlet : p.InletRegular) :
    Function.Periodic (bgField p z) p.period := by
  have hraw : IsBackgroundPiece p.period p.raw :=
    isBackgroundPiece_raw p.ε_pos.ne' p.train
      (fun τ y hy => p.raw_eq_off_axis τ y hy) hRaw.1 hRaw.2
  have hP : p.period = 2 * p.c / p.R := p.period_eq
  have hinlet (i : Fin 2) : IsBackgroundPiece p.period (p.inlet i) :=
    isBackgroundPiece_of_lift p.R_pos.ne' hP
      (fun s hs ξ η => p.inletProfile_periodic i s ξ η)
      (fun τ y hy => rfl) (hInlet i).1 (hInlet i).2
  have hcorr : Function.Periodic (p.corr z) p.period := by
    change Function.Periodic (contRep (p.wOf z)) p.period
    exact contRep_periodic (p.wOf z)
  intro τ
  change p.raw (τ + p.period) +
      ∑ i : Fin 2, (p.coord z i) • p.inlet i (τ + p.period) +
        p.corr z (τ + p.period) =
    p.raw τ + ∑ i : Fin 2, (p.coord z i) • p.inlet i τ + p.corr z τ
  rw [hraw.periodic τ, hcorr τ]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [(hinlet i).periodic τ]

private theorem isSolenoidal_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → SpatialField) (hf : ∀ i ∈ s, IsSolenoidal (f i)) :
    IsSolenoidal (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      constructor <;> intro φ hφ <;> simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact UnforcedLeray.Cons.C03.isSolenoidal_add
        (hf i (Finset.mem_insert_self i s))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- Distributional solenoidality of every spatial slice `bgField p z τ` when `p.period ≤ 1`. -/
theorem bgField_isSolenoidal (p : Params) (hP1 : p.period ≤ 1) (z : p.Z)
    (hRaw : p.RawLiftRegular) (hInlet : p.InletRegular) :
    ∀ τ : ℝ, IsSolenoidal (bgField p z τ) := by
  intro τ
  have hraw : IsSolenoidal (p.raw τ) := hRaw.2 τ
  have hinlet (i : Fin 2) : IsSolenoidal (p.inlet i τ) := (hInlet i).2 τ
  have hsum : IsSolenoidal (∑ i : Fin 2, (p.coord z i) • p.inlet i τ) := by
    apply isSolenoidal_finset_sum Finset.univ
    intro i _
    exact UnforcedLeray.Cons.C03.isSolenoidal_const_smul (hinlet i) (p.coord z i)
  have hcorr : IsSolenoidal (p.corr z τ) := p.corr_isSolenoidal hP1 z τ
  change IsSolenoidal
    (p.raw τ + (∑ i : Fin 2, (p.coord z i) • p.inlet i τ) + p.corr z τ)
  exact UnforcedLeray.Cons.C03.isSolenoidal_add
    (UnforcedLeray.Cons.C03.isSolenoidal_add hraw hsum) hcorr

/-- Compact-test convection pairing of `bgField p z` equals that of `p.Ufun + p.uOf z`. -/
theorem bgField_convectionPair_eq_rawAddState (p : Params)
    (hRaw : p.RawLiftRegular) (hInlet : p.InletRegular) (z : p.Z)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest p.period Φ) :
    pairF p.period
      (advT (fun x => realC (bgField p z x.1 x.2)) Φ)
      (fun x => realC (bgField p z x.1 x.2)) =
    pairF p.period (advT (fun x => p.Ufun x + p.uOf z x) Φ)
      (fun x => p.Ufun x + p.uOf z x) := by
  simpa only [schemeField_eq_bgField] using
    Params.schemeField_convectionPair_eq_rawAddState p defaultBudget hRaw hInlet z hΦ

/-- From `ProjectedEquation p z`, `hRaw`, and `hInlet`, the raw/inlet cross convection vanishes on
every solenoidal phase test `Φ`, leaving the split residual identity. -/
theorem projectedEquation_compactResidual_split (p : Params)
    (hRaw : p.RawLiftRegular) (hInlet : p.InletRegular) (z : p.Z)
    (hProj : ProjectedEquation p z) {Φ : ℝ × Space → CVec3} (hΦ : IsSolTest p.period Φ) :
    (pairF p.period (L0T p.ν Φ) p.Ufun -
      pairF p.period (advT p.Ufun Φ) p.Ufun) +
      (pairF p.period (L0T p.ν Φ) (fun x => rep (p.wOf z) x.1 x.2) +
        ∑ i : Fin 2, (p.coord z i : ℂ) *
          pairF p.period (L0T p.ν Φ) (p.Efun i)) -
      (pairF p.period (advT (fun x => rep (p.wOf z) x.1 x.2) Φ) p.Ufun +
        pairF p.period (advT p.Ufun Φ)
          (fun x => rep (p.wOf z) x.1 x.2) +
        ∑ i : Fin 2, (p.coord z i : ℂ) *
          (pairF p.period (advT (p.Efun i) Φ) p.Ufun +
            pairF p.period (advT p.Ufun Φ) (p.Efun i))) -
      pairF p.period (advT (p.uOf z) Φ) (p.uOf z) = 0 := by
  have hagg := ProjectedEvolutionSub.projectedEquation_solTest_pairF p z hProj hΦ
  have hcross := selectedState_rawInletCross_pairF_sum_eq_zero p defaultBudget hRaw hInlet
    (z := z) hΦ.1
  simp_rw [mul_add] at hagg hcross
  simp_rw [Finset.sum_add_distrib] at hagg hcross
  simp_rw [mul_add, Finset.sum_add_distrib]
  linear_combination hagg - hcross

/-- Groups all convection terms in `projectedEquation_compactResidual_split` into the total
raw-plus-state convection pairing. -/
theorem projectedEquation_compactResidual_totalConvection (p : Params)
    (hRaw : p.RawLiftRegular) (hInlet : p.InletRegular) (z : p.Z)
    (hProj : ProjectedEquation p z) {Φ : SpaceTime → CVec3} (hΦ : IsSolTest p.period Φ) :
    pairF p.period (L0T p.ν Φ) p.Ufun +
      (pairF p.period (L0T p.ν Φ) (fun x => rep (p.wOf z) x.1 x.2) +
        ∑ i : Fin 2, (p.coord z i : ℂ) *
          pairF p.period (L0T p.ν Φ) (p.Efun i)) -
      pairF p.period (advT (fun x => p.Ufun x + p.uOf z x) Φ)
        (fun x => p.Ufun x + p.uOf z x) = 0 := by
  let W : SpaceTime → CVec3 := fun x => rep (p.wOf z) x.1 x.2
  let Bcross : ℂ :=
    pairF p.period (advT W Φ) p.Ufun +
      pairF p.period (advT p.Ufun Φ) W +
      ∑ i : Fin 2, (p.coord z i : ℂ) *
        (pairF p.period (advT (p.Efun i) Φ) p.Ufun +
          pairF p.period (advT p.Ufun Φ) (p.Efun i))
  have hsplit := projectedEquation_compactResidual_split p hRaw hInlet z hProj hΦ
  have hcross0 := selectedState_rawStateCross_pairF_expand hRaw hInlet
    (B := defaultBudget) (z := z) hΦ.1
  have hcross :
      pairF p.period (advT p.Ufun Φ) (p.uOf z) +
        pairF p.period (advT (p.uOf z) Φ) p.Ufun = Bcross := by
    simpa [Bcross, W, add_comm, add_left_comm, add_assoc] using hcross0
  have hfour := selectedFullBackground_pairF_rawState_fourTerm hRaw hInlet
    (B := defaultBudget) (z := z) hΦ.1
  have htotal :
      pairF p.period (advT (fun x => p.Ufun x + p.uOf z x) Φ)
        (fun x => p.Ufun x + p.uOf z x) =
      pairF p.period (advT p.Ufun Φ) p.Ufun + Bcross +
        pairF p.period (advT (p.uOf z) Φ) (p.uOf z) := by
    rw [hfour]
    rw [← hcross]
    ac_rfl
  linear_combination hsplit - htotal

/-- **Compact-solenoidal weak equation for `bgField p z`.** Under `ProjectedEquation p z`, `hRaw`,
and `hInlet`, `bgField p z` satisfies the projected weak equation on every solenoidal phase test
`Φ` (`IsSolTest p.period Φ`). -/
theorem bgField_compactSolenoidal_weakEquation (p : Params)
    (hRaw : p.RawLiftRegular) (hInlet : p.InletRegular) (z : p.Z)
    (hProj : ProjectedEquation p z) {Φ : SpaceTime → CVec3} (hΦ : IsSolTest p.period Φ) :
    pairF p.period (L0T p.ν Φ)
      (fun x => realC (bgField p z x.1 x.2)) =
    pairF p.period
      (advT (fun x => realC (bgField p z x.1 x.2)) Φ)
      (fun x => realC (bgField p z x.1 x.2)) := by
  let Uact : SpaceTime → CVec3 := fun x => realC (bgField p z x.1 x.2)
  let Uaff : SpaceTime → CVec3 := fun x => p.Ufun x + p.uOf z x
  let T : SpaceTime → CVec3 := L0T p.ν Φ
  have hlinAffine : pairF p.period T Uaff =
      pairF p.period T p.Ufun +
        (pairF p.period T (fun x => rep (p.wOf z) x.1 x.2) +
          ∑ i : Fin 2, (p.coord z i : ℂ) * pairF p.period T (p.Efun i)) :=
    selectedState_l0T_pairF_sum hRaw hInlet (z := z) hΦ.1
  have hres := projectedEquation_compactResidual_totalConvection p hRaw hInlet z hProj hΦ
  have hconvAffine : pairF p.period T Uaff =
      pairF p.period (advT Uaff Φ) Uaff := by
    dsimp [T, Uaff] at hlinAffine hres ⊢
    rw [hlinAffine]
    linear_combination hres
  have hfield : Uact =ᵐ[volume.prod volume] Uaff :=
    bgField_eq_rawAddState_ae p z
  let μ : Measure SpaceTime := volume.restrict (phaseCell p.period)
  have hfieldCell : Uact =ᵐ[μ] Uaff := by
    have hfieldVol : Uact =ᵐ[volume] Uaff := by
      rw [Measure.volume_eq_prod ℝ Space]
      exact hfield
    exact MeasureTheory.ae_restrict_of_ae hfieldVol
  have hT : IsPhaseTest p.period T := isPhaseTest_L0T hΦ.1 p.ν
  have hrawLin : Integrable (fun x => dotL (T x) (p.Ufun x)) μ := by
    change Integrable (fun x => dotL (T x) (realC (p.raw x.1 x.2))) μ
    exact integrable_phaseTest_boundedBackground_cell hT hRaw.1
  let V : ℝ → SpatialField := fun τ y =>
    ∑ i : Fin 2, (p.coord z i) • p.inlet i τ y
  have hV : IsBoundedBackground V := isBoundedBackground_affineInlet hInlet (p.coord z)
  have hE : Integrable (fun x => dotL (T x) (p.eFun (p.coord z) x)) μ := by
    change Integrable (fun x => dotL (T x) (realC (V x.1 x.2))) μ
    exact integrable_phaseTest_boundedBackground_cell hT hV
  have hWmem : MemLp (fun x : SpaceTime => rep (p.wOf z) x.1 x.2) q0E μ := by
    simpa [μ, phaseCell] using memLp_rep_periodCell q0E_ne_top (p.wOf z)
  have hW : Integrable
      (fun x => dotL (T x) (rep (p.wOf z) x.1 x.2)) μ :=
    integrable_dotL_of_memLp_holder
      (memLp_phaseTest_cell (P := p.period) (r := conjExp q0E)
        (T := T) (conjExp_ne_top one_lt_q0E) hT) hWmem
  have hStateInt : Integrable (fun x => dotL (T x) (p.uOf z x)) μ := by
    apply Integrable.congr (hE.add hW)
    filter_upwards [] with x
    simp [Params.uOf, dotL_apply, Finset.sum_add_distrib, mul_add]
  have hlinAffInt : Integrable (fun x => dotL (T x) (Uaff x)) μ := by
    apply Integrable.congr (hrawLin.add hStateInt)
    filter_upwards [] with x
    simp [Uaff, dotL_apply, Finset.sum_add_distrib, mul_add]
  have hlinAE :
      (fun x : SpaceTime => dotL (T x) (Uact x)) =ᵐ[μ]
        fun x => dotL (T x) (Uaff x) := by
    filter_upwards [hfieldCell] with x hx
    rw [hx]
  have hlinActInt : Integrable (fun x => dotL (T x) (Uact x)) μ :=
    Integrable.congr hlinAffInt hlinAE.symm
  have hlinAct : pairF p.period T Uact = pairF p.period T Uaff := by
    rw [pairF_eq_restrictedProductIntegral hlinActInt,
      pairF_eq_restrictedProductIntegral hlinAffInt]
    exact congrArg (fun x : ℂ => (p.period)⁻¹ * x) (integral_congr_ae hlinAE)
  have hconvAct := bgField_convectionPair_eq_rawAddState p hRaw hInlet z hΦ.1
  dsimp [Uact, T] at hlinAct hconvAct ⊢
  rw [hlinAct, hconvAct, hconvAffine]

/-- Under `hV : IsUniformSmoothL4SliceFamily V`, `hV' : IsUniformSmoothL4SliceFamily V'`,
and `hDeriv : HasPhaseJetDeriv V V'`, every directional spatial jet
`(τ, y) ↦ dirSpatialJet (V τ) ws y` is jointly continuous on `ℝ × Space`. -/
theorem continuous_jet_of_hasPhaseJetDeriv {V V' : ℝ → SpatialField}
    (hV : IsUniformSmoothL4SliceFamily V) (hV' : IsUniformSmoothL4SliceFamily V')
    (hDeriv : HasPhaseJetDeriv V V') (ws : List Space) :
    Continuous (PhaseDerivStepSub.uncurriedField (fun τ => dirSpatialJet (V τ) ws)) := by
  have hJetV' : IsUniformSmoothL4SliceFamily (fun τ => dirSpatialJet (V' τ) ws) :=
    HigherPhaseSub.sliceFamily_dirSpatialJet hV' ws
  obtain ⟨M, hM⟩ := hJetV'.iteratedFDeriv_bounded 0
  refine JointSmoothSub.continuous_of_hasDerivAt_fst_bounded
    (P := PhaseDerivStepSub.uncurriedField (fun τ => dirSpatialJet (V' τ) ws))
    (fun x => hDeriv ws x.1 x.2)
    (fun τ => (JointSmoothSub.contDiff_infty_dirSpatialJet
      (HigherPhaseSub.sliceFamily_contDiff_infty hV τ) ws).continuous)
    ⟨M, fun x => ?_⟩
  have h0 := hM x.1 x.2
  rwa [norm_iteratedFDeriv_zero] at h0

/-- For any continuous compactly supported solenoidal spatial test `a : Space → Space` and any
`G : ℝ → SpatialField` in `IsUniformSmoothL4SliceFamily`, pairing `a` against
`smoothLeraySlice G τ` equals pairing `a` against `G τ`. -/
theorem integral_inner_smoothLeraySlice_eq {a : Space → Space}
    (hcont : Continuous a) (hcs : HasCompactSupport a) (hsol : IsSolenoidal a)
    {G : ℝ → SpatialField} (hG : IsUniformSmoothL4SliceFamily G) (τ : ℝ) :
    ∫ y, inner ℝ (a y) (smoothLeraySlice G τ y) = ∫ y, inner ℝ (a y) (G τ y) := by
  have hRep : IsSmoothLerayRep (G τ) (smoothLeraySlice G τ) :=
    (SmoothLeraySliceSub.smoothLeraySlice_rep_and_memLp smoothLerayRepExists_proof hG τ).1
  obtain ⟨hMemG, hRep'⟩ := hRep
  have hae := hRep'.2
  have h1 : (1 : ℝ≥0∞) < 4 := by norm_num
  have h4 : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hLp := LerayPairSolAux.real_inner_lerayLp_eq hcont hcs hsol h1 h4 (hMemG.toLp (G τ))
  have haeG : (hMemG.toLp (G τ) : Space → Space) =ᵐ[volume] G τ := hMemG.coeFn_toLp
  calc
    ∫ y, inner ℝ (a y) (smoothLeraySlice G τ y)
        = ∫ y, inner ℝ (a y) (lerayLp 4 h1 h4 (hMemG.toLp (G τ)) y) := by
          apply integral_congr_ae
          filter_upwards [hae] with y hy
          rw [hy]
    _ = ∫ y, inner ℝ (a y) ((hMemG.toLp (G τ) : Space → Space) y) := hLp
    _ = ∫ y, inner ℝ (a y) (G τ y) := by
          apply integral_congr_ae
          filter_upwards [haeG] with y hy
          rw [hy]

/-- For any continuous compactly supported solenoidal spatial test `a : Space → Space` and any
`V, W : ℝ → SpatialField` in `IsUniformSmoothL4SliceFamily`, pairing `a` against
`smoothConvectiveLeray V W τ` equals pairing `a` against `spatialConvect (V τ) (W τ)`. -/
theorem integral_inner_smoothConvectiveLeray_eq {a : Space → Space}
    (hcont : Continuous a) (hcs : HasCompactSupport a) (hsol : IsSolenoidal a)
    {V W : ℝ → SpatialField}
    (hV : IsUniformSmoothL4SliceFamily V) (hW : IsUniformSmoothL4SliceFamily W) (τ : ℝ) :
    ∫ y, inner ℝ (a y) (smoothConvectiveLeray V W τ y) =
      ∫ y, inner ℝ (a y) (spatialConvect (V τ) (W τ) y) :=
  integral_inner_smoothLeraySlice_eq hcont hcs hsol
    (HigherPhaseSub.sliceFamily_spatialConvect hV hW) τ

/-- `IsSolenoidal` is invariant under almost-everywhere equality. -/
theorem isSolenoidal_congr_ae {f g : Space → Space} (hf : IsSolenoidal f)
    (hfg : f =ᵐ[volume] g) : IsSolenoidal g where
  integrable ψ hψ := (hf.integrable ψ hψ).congr (hfg.mono fun x hx => by simp only [hx])
  identity ψ hψ :=
    (integral_congr_ae (hfg.symm.mono fun x hx => by simp only [hx])).trans (hf.identity ψ hψ)

/-- Every slice `smoothLeraySlice G τ` of `G ∈ IsUniformSmoothL4SliceFamily` is distributionally
solenoidal (`IsSolenoidal`). -/
theorem isSolenoidal_smoothLeraySlice {G : ℝ → SpatialField}
    (hG : IsUniformSmoothL4SliceFamily G) (τ : ℝ) :
    IsSolenoidal (smoothLeraySlice G τ) := by
  have hRep : IsSmoothLerayRep (G τ) (smoothLeraySlice G τ) :=
    (SmoothLeraySliceSub.smoothLeraySlice_rep_and_memLp smoothLerayRepExists_proof hG τ).1
  obtain ⟨hMemG, _, hae⟩ := hRep
  have h1 : (1 : ℝ≥0∞) < 4 := by norm_num
  have h4 : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
  exact isSolenoidal_congr_ae (lerayLp_isSolenoidal h1 h4 (hMemG.toLp (G τ))) hae.symm

/-- Every slice `smoothConvectiveLeray V W τ` of `V, W ∈ IsUniformSmoothL4SliceFamily` is
distributionally solenoidal (`IsSolenoidal`). -/
theorem isSolenoidal_smoothConvectiveLeray {V W : ℝ → SpatialField}
    (hV : IsUniformSmoothL4SliceFamily V) (hW : IsUniformSmoothL4SliceFamily W) (τ : ℝ) :
    IsSolenoidal (smoothConvectiveLeray V W τ) :=
  isSolenoidal_smoothLeraySlice (HigherPhaseSub.sliceFamily_spatialConvect hV hW) τ

/-- `realC` coincides with the continuous linear map `RieszLp.ofReV`. -/
theorem realC_eq_ofReV (x : Space) : realC x = ofReV x := by
  ext i
  rw [realC_apply, ofReV_apply]

/-- Embedding a solenoidal real spatial field `F` via `realC` yields a complex solenoidal field
`IsSolenoidalC (fun y => realC (F y))`. -/
theorem isSolenoidalC_realC_of_isSolenoidal {F : SpatialField} (hF : IsSolenoidal F) :
    IsSolenoidalC (fun y => realC (F y)) := by
  rw [isSolenoidalC_iff]
  have hre : (fun x => RieszLp.reV (realC (F x))) = F := by
    funext x
    rw [realC_eq_ofReV, reV_ofReV]
  have him : (fun x => RieszLp.imV (realC (F x))) = (0 : SpatialField) := by
    funext x
    rw [realC_eq_ofReV, imV_ofReV]
    rfl
  rw [hre, him]
  exact ⟨hF, ⟨fun _ _ => by simp, fun _ _ => by simp⟩⟩

/-- By `solSepSpatial` (`PartII-b:T10/org/2/3`), any continuous `L⁴(ℝ³)` solenoidal spatial field
`F` whose complexified pairing against all `SpatialSolTest` vanishes is identically zero. -/
theorem eq_zero_of_isSolenoidal_and_spatialSolTest_orth {F : SpatialField}
    (hCont : Continuous F)
    (hMem : MemLp F 4 (volume : Measure Space))
    (hSol : IsSolenoidal F)
    (hOrth : ∀ Ψ : Space → CVec3, SpatialSolTest Ψ → ∫ y, dotL (Ψ y) (realC (F y)) = 0) :
    F = 0 := by
  have hEqOfReV : (fun y : Space => realC (F y)) = ofReV ∘ F := by
    funext y
    exact realC_eq_ofReV (F y)
  have hMemC : MemLp (fun y : Space => realC (F y)) 4 (volume : Measure Space) := by
    rw [hEqOfReV]
    exact ofReV.comp_memLp' hMem
  let w : Lp CVec3 4 (volume : Measure Space) := hMemC.toLp (fun y => realC (F y))
  have hae : (w : Space → CVec3) =ᵐ[volume] fun y => realC (F y) := hMemC.coeFn_toLp
  have hSolW : IsSolenoidalC (w : Space → CVec3) := by
    rw [isSolenoidalC_iff]
    have hre : (fun x => RieszLp.reV ((w : Space → CVec3) x)) =ᵐ[volume] F := by
      filter_upwards [hae] with x hx
      rw [hx, realC_eq_ofReV, reV_ofReV]
    have him : (fun x => RieszLp.imV ((w : Space → CVec3) x)) =ᵐ[volume] (0 : SpatialField) := by
      filter_upwards [hae] with x hx
      rw [hx, realC_eq_ofReV, imV_ofReV]
      rfl
    exact ⟨isSolenoidal_congr_ae hSol hre.symm,
      isSolenoidal_congr_ae ⟨fun _ _ => by simp, fun _ _ => by simp⟩ him.symm⟩
  have hOrthW : ∀ Ψ : Space → CVec3, SpatialSolTest Ψ → ∫ y, dotL (Ψ y) (w y) = 0 := by
    intro Ψ hΨ
    have hcongr : ∫ y, dotL (Ψ y) (w y) = ∫ y, dotL (Ψ y) (realC (F y)) := by
      apply integral_congr_ae
      filter_upwards [hae] with y hy
      rw [hy]
    rw [hcongr, hOrth Ψ hΨ]
  have hw0 : w = 0 :=
    solSepSpatial 4 (by norm_num) (by norm_num) w hSolW hOrthW
  have hae0 : (fun y : Space => realC (F y)) =ᵐ[volume] 0 := by
    refine hae.symm.trans ?_
    rw [hw0]
    exact Lp.coeFn_zero CVec3 4 volume
  have hFae : F =ᵐ[volume] (0 : SpatialField) := by
    filter_upwards [hae0] with y hy
    have hre := congrArg RieszLp.reV hy
    simpa [realC_eq_ofReV, reV_ofReV] using hre
  exact (Continuous.ae_eq_iff_eq volume hCont continuous_zero).1 hFae

/-- If `U₁` and `bgPhaseDerivTower ν U₀ 1` belong to `IsUniformSmoothL4SliceFamily` and on every
slice `τ : ℝ` their difference `U₁ τ - bgPhaseDerivTower ν U₀ 1 τ` is distributionally solenoidal
and orthogonal to all `SpatialSolTest`, then `U₁ = bgPhaseDerivTower ν U₀ 1`. -/
theorem eq_bgPhaseDerivTower_one_of_slice_solenoidal_and_orth (ν : ℝ)
    {U₀ U₁ : ℝ → SpatialField}
    (hU₁ : IsUniformSmoothL4SliceFamily U₁)
    (hTower₁ : IsUniformSmoothL4SliceFamily (bgPhaseDerivTower ν U₀ 1))
    (hSol : ∀ τ : ℝ, IsSolenoidal (U₁ τ - bgPhaseDerivTower ν U₀ 1 τ))
    (hOrth : ∀ (τ : ℝ) (Ψ : Space → CVec3), SpatialSolTest Ψ →
      ∫ y, dotL (Ψ y) (realC ((U₁ τ - bgPhaseDerivTower ν U₀ 1 τ) y)) = 0) :
    U₁ = bgPhaseDerivTower ν U₀ 1 := by
  have hDiff : IsUniformSmoothL4SliceFamily (U₁ - bgPhaseDerivTower ν U₀ 1) :=
    HigherPhaseSub.sliceFamily_sub hU₁ hTower₁
  funext τ
  have h0 : U₁ τ - bgPhaseDerivTower ν U₀ 1 τ = 0 :=
    eq_zero_of_isSolenoidal_and_spatialSolTest_orth
      (HigherPhaseSub.sliceFamily_contDiff_infty hDiff τ).continuous
      (SmoothLeraySliceSub.smoothLeraySlice_rep_and_memLp
        smoothLerayRepExists_proof hDiff τ).1.choose
      (hSol τ)
      (hOrth τ)
  exact sub_eq_zero.1 h0

/-- If `HasPhaseJetDeriv U₀ U₁` and `U₁ = bgPhaseDerivTower ν U₀ 1`, then at every `(τ, y)` the 1D
phase derivative of `U₀` is `spatialProjectedLin ν (U₀ τ) y - smoothConvectiveLeray U₀ U₀ τ y`. -/
theorem hasDerivAt_of_eq_bgPhaseDerivTower_one (ν : ℝ) {U₀ U₁ : ℝ → SpatialField}
    (hU₁ : HasPhaseJetDeriv U₀ U₁)
    (hEq : U₁ = bgPhaseDerivTower ν U₀ 1) (τ : ℝ) (y : Space) :
    HasDerivAt (fun τ' : ℝ => U₀ τ' y)
      (spatialProjectedLin ν (U₀ τ) y - smoothConvectiveLeray U₀ U₀ τ y) τ := by
  have hd := hU₁ [] τ y
  rw [hEq, ProjectedEvolutionSub.bgPhaseDerivTower_one] at hd
  exact hd

end PointwiseDerivSub

/-! ## 4. Atomic leaf definitions and conditional assemblies of `BgProjectedPointwiseDeriv` -/

/-- **Leaf 1 (`PartII-b:S3/1/2/2/1/1`, `BgSolTestWeakIBP`)**
(SP 2519-2523, 2559-2562): when `bgField p z` is `p.period`-periodic (`p.period ≤ 1`), slicewise
solenoidal (`∀ τ, IsSolenoidal (bgField p z τ)`), lies in `IsUniformSmoothL4SliceFamily` along with
`fun τ => spatialRadialDrift (bgField p z τ)` and `bgPhaseDerivTower p.ν (bgField p z) 1`, satisfies
the compact-solenoidal weak equation `bgField_compactSolenoidal_weakEquation` on all
`IsSolTest p.period Φ`, and has first phase-jet derivative `U₁` in `IsUniformSmoothL4SliceFamily`,
integration by parts in `τ ∈ (0, p.period]` (using `HasPhaseJetDeriv (bgField p z) U₁` and
`p.period`-periodicity) and in `y ∈ ℝ³` (using compact spatial support of `Φ` and
`PointwiseDerivSub.integral_inner_smoothConvectiveLeray_eq`) transforms the weak equation into
`pairF p.period Φ (fun x => realC ((U₁ x.1 - bgPhaseDerivTower p.ν (bgField p z) 1 x.1) x.2)) = 0`
for all `IsSolTest p.period Φ`.
Composed by task `PartII-b:S3/1/2/2/1` via `bgProjectedPointwiseDeriv_of`. -/
def BgSolTestWeakIBP : Prop :=
  SmoothLeraySliceRegularity →
  ∀ (p : Params), p.period ≤ 1 → p.ν ≤ 1 →
    ∀ z : p.Z,
      Function.Periodic (bgField p z) p.period →
      (∀ τ : ℝ, IsSolenoidal (bgField p z τ)) →
      (∀ Φ : SpaceTime → CVec3, IsSolTest p.period Φ →
        pairF p.period (L0T p.ν Φ) (fun x => realC (bgField p z x.1 x.2)) =
          pairF p.period (advT (fun x => realC (bgField p z x.1 x.2)) Φ)
            (fun x => realC (bgField p z x.1 x.2))) →
      IsUniformSmoothL4SliceFamily (bgField p z) →
      IsUniformSmoothL4SliceFamily (fun τ => spatialRadialDrift (bgField p z τ)) →
      IsUniformSmoothL4SliceFamily (bgPhaseDerivTower p.ν (bgField p z) 1) →
      ∀ U₁ : ℝ → SpatialField,
        IsUniformSmoothL4SliceFamily U₁ →
        HasPhaseJetDeriv (bgField p z) U₁ →
        ∀ Φ : SpaceTime → CVec3, IsSolTest p.period Φ →
          pairF p.period Φ
            (fun x => realC ((U₁ x.1 - bgPhaseDerivTower p.ν (bgField p z) 1 x.1) x.2)) = 0

/-- **Leaf 2 (`PartII-b:S3/1/2/2/1/2`, `BgSolTestOrthEqZero`)**
(SP 2519-2523, 2559-2562): when `bgField p z` is `p.period`-periodic (`p.period ≤ 1`), slicewise
solenoidal (`∀ τ, IsSolenoidal (bgField p z τ)`), lies in `IsUniformSmoothL4SliceFamily` along with
`fun τ => spatialRadialDrift (bgField p z τ)` and `bgPhaseDerivTower p.ν (bgField p z) 1`, and `U₁`
in `IsUniformSmoothL4SliceFamily` satisfies `HasPhaseJetDeriv (bgField p z) U₁` and
`pairF p.period Φ (fun x => realC ((U₁ x.1 - bgPhaseDerivTower p.ν (bgField p z) 1 x.1) x.2)) = 0`
for all `IsSolTest p.period Φ`, slicewise solenoidality and spatial solenoidal separation
(`PointwiseDerivSub.eq_bgPhaseDerivTower_one_of_slice_solenoidal_and_orth` / `solSepSpatial`)
identify `U₁ = bgPhaseDerivTower p.ν (bgField p z) 1`.
Composed by task `PartII-b:S3/1/2/2/1` via `bgProjectedPointwiseDeriv_of`. -/
def BgSolTestOrthEqZero : Prop :=
  SmoothLeraySliceRegularity →
  ∀ (p : Params), p.period ≤ 1 → p.ν ≤ 1 →
    ∀ z : p.Z,
      Function.Periodic (bgField p z) p.period →
      (∀ τ : ℝ, IsSolenoidal (bgField p z τ)) →
      IsUniformSmoothL4SliceFamily (bgField p z) →
      IsUniformSmoothL4SliceFamily (fun τ => spatialRadialDrift (bgField p z τ)) →
      IsUniformSmoothL4SliceFamily (bgPhaseDerivTower p.ν (bgField p z) 1) →
      ∀ U₁ : ℝ → SpatialField,
        IsUniformSmoothL4SliceFamily U₁ →
        HasPhaseJetDeriv (bgField p z) U₁ →
        (∀ Φ : SpaceTime → CVec3, IsSolTest p.period Φ →
          pairF p.period Φ
            (fun x => realC ((U₁ x.1 - bgPhaseDerivTower p.ν (bgField p z) 1 x.1) x.2)) = 0) →
        U₁ = bgPhaseDerivTower p.ν (bgField p z) 1

/-- **Combined weak-to-pointwise bridge (`BgSolTestWeakToPointwiseEq`)** with radial-drift and
stage-1 tower `L⁴(ℝ³)` slice regularity in force. -/
def BgSolTestWeakToPointwiseEq : Prop :=
  SmoothLeraySliceRegularity →
  ∀ (p : Params), p.period ≤ 1 → p.ν ≤ 1 →
    ∀ z : p.Z,
      Function.Periodic (bgField p z) p.period →
      (∀ τ : ℝ, IsSolenoidal (bgField p z τ)) →
      (∀ Φ : SpaceTime → CVec3, IsSolTest p.period Φ →
        pairF p.period (L0T p.ν Φ) (fun x => realC (bgField p z x.1 x.2)) =
          pairF p.period (advT (fun x => realC (bgField p z x.1 x.2)) Φ)
            (fun x => realC (bgField p z x.1 x.2))) →
      IsUniformSmoothL4SliceFamily (bgField p z) →
      IsUniformSmoothL4SliceFamily (fun τ => spatialRadialDrift (bgField p z τ)) →
      IsUniformSmoothL4SliceFamily (bgPhaseDerivTower p.ν (bgField p z) 1) →
      ∀ U₁ : ℝ → SpatialField,
        IsUniformSmoothL4SliceFamily U₁ →
        HasPhaseJetDeriv (bgField p z) U₁ →
        U₁ = bgPhaseDerivTower p.ν (bgField p z) 1

/-- Assembly of `BgSolTestWeakToPointwiseEq` from `BgSolTestWeakIBP` (`PartII-b:S3/1/2/2/1/1`) and
`BgSolTestOrthEqZero` (`PartII-b:S3/1/2/2/1/2`). -/
theorem bgSolTestWeakToPointwiseEq_of
    (hIBP : BgSolTestWeakIBP)
    (hOrth : BgSolTestOrthEqZero) :
    BgSolTestWeakToPointwiseEq := by
  intro hLeray p hP1 hν1 z hPer hSol hWeak hBg hRad hTower₁ U₁ hU₁Smooth hU₁Deriv
  exact hOrth hLeray p hP1 hν1 z hPer hSol hBg hRad hTower₁ U₁ hU₁Smooth hU₁Deriv
    (hIBP hLeray p hP1 hν1 z hPer hSol hWeak hBg hRad hTower₁ U₁ hU₁Smooth hU₁Deriv)

/-- Conditional assembly of `BgProjectedPointwiseDeriv` (`PartII-b:S3/1/2/2/1`) from
`BgFirstRadialDriftL4` (`PartII-b:S3/1/1/2/1`) and `BgSolTestWeakToPointwiseEq`. -/
theorem bgProjectedPointwiseDeriv_of_weakToPointwise
    (hRadL4 : BgFirstRadialDriftL4)
    (hWeakToPtw : BgSolTestWeakToPointwiseEq) :
    BgProjectedPointwiseDeriv := by
  intro hLeray Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν_per, hν_per, hper⟩ := poly_exp_small 2 dm 2 hdm
  obtain ⟨ν_rad, hν_rad, hRad⟩ := hRadL4 Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  refine ⟨min (min ν_per 1) ν_rad, lt_min (lt_min hν_per zero_lt_one) hν_rad, ?_⟩
  intro p d hReg hν hAge hMode hRawCD hInCD z hProj hz hGraph hSlice hRaw hInlet
    hBg U₁ hU₁Smooth hU₁Deriv
  have hν_per' : p.ν ≤ ν_per := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_1 : p.ν ≤ 1 := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_rad' : p.ν ≤ ν_rad := hν.trans (min_le_right _ _)
  have hP1 : p.period ≤ 1 := period_le_one_of hReg (hper p.ν p.ν_pos hν_per')
  have hRadSlice : IsUniformSmoothL4SliceFamily (fun τ => spatialRadialDrift (bgField p z τ)) :=
    PhaseDerivStepSub.sliceFamily_spatialRadialDrift_of_l4 hBg
      (hRad p d hReg hν_rad' hAge hMode hRawCD hInCD z hProj hz hGraph hBg hRaw hInlet)
  have hTower₁ : IsUniformSmoothL4SliceFamily (bgPhaseDerivTower p.ν (bgField p z) 1) :=
    PhaseDerivStepSub.sliceFamily_bgPhaseDerivTower_one
      smoothLerayRepExists_proof p.ν hBg hRadSlice
  have hU₁Eq : U₁ = bgPhaseDerivTower p.ν (bgField p z) 1 :=
    hWeakToPtw hLeray p hP1 hν_1 z
      (PointwiseDerivSub.bgField_periodic p z hRaw hInlet)
      (PointwiseDerivSub.bgField_isSolenoidal p hP1 z hRaw hInlet)
      (fun Φ hΦ => PointwiseDerivSub.bgField_compactSolenoidal_weakEquation p hRaw hInlet z hProj hΦ)
      hBg hRadSlice hTower₁ U₁ hU₁Smooth hU₁Deriv
  exact PointwiseDerivSub.hasDerivAt_of_eq_bgPhaseDerivTower_one p.ν hU₁Deriv hU₁Eq

/-- Complete conditional assembly of `BgProjectedPointwiseDeriv` (`PartII-b:S3/1/2/2/1`) from
`BgFirstRadialDriftL4` (`PartII-b:S3/1/1/2/1`), `BgSolTestWeakIBP` (`PartII-b:S3/1/2/2/1/1`),
and `BgSolTestOrthEqZero` (`PartII-b:S3/1/2/2/1/2`). -/
theorem bgProjectedPointwiseDeriv_of
    (hRadL4 : BgFirstRadialDriftL4)
    (hIBP : BgSolTestWeakIBP)
    (hOrth : BgSolTestOrthEqZero) :
    BgProjectedPointwiseDeriv :=
  bgProjectedPointwiseDeriv_of_weakToPointwise hRadL4 (bgSolTestWeakToPointwiseEq_of hIBP hOrth)

end UnforcedLeray.Short.IIb

end
