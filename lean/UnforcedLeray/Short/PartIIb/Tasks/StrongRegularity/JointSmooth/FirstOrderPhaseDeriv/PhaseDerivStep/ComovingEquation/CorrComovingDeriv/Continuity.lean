import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation.CorrComovingDeriv.Reduction

/-!
# Joint continuity of the jets of `T₀w` from that of the Leray term (helper of
`PartII-b:S3/1/1/2/1/2`)

Source of record: `the November 2 reference manuscript`,
lines 2519-2523, 2559-2562.

`corrRHSJetContinuous_of_leray : LerayJetContinuous → CorrRHSJetContinuous`. The jets of
`corrComovingRHS p z = νΔU + ½U - 𝔓(U·∇U) - T₀U_raw - E_ε T₀α` are jointly continuous once those
of the Leray term `smoothConvectiveLeray U U` are: the jets of `U_raw`, `E_i`, `T₀U_raw`, `T₀E_i`
are jointly smooth (joint smoothness of `p.raw`, `p.inlet i`), and the coordinate jets of
`w = p.corr z` are the continuous representatives `contRep (g α)` of the graph elements.

`bgCorrComovingJetDeriv_of_base_leray : CorrT0BaseRep → LerayJetContinuous →
BgCorrComovingJetDeriv`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.Blueprint

namespace CorrComovingSub

local instance fact_q0_ge_one_corrCont : Fact (1 ≤ ENNReal.ofReal B0281.q0) :=
  inferInstanceAs (Fact (1 ≤ q0E))

/-- Joint continuity of all jets from joint continuity of the coordinate jets. -/
theorem continuous_dirSpatialJet_of_coordWord {V : ℝ → SpatialField}
    (hV : ∀ τ, ContDiff ℝ ∞ (V τ))
    (hC : ∀ (k : ℕ) (α : Fin k → Fin 3),
      Continuous (fun x : ℝ × Space =>
        dirSpatialJet (V x.1) (PhaseDerivStepSub.coordWord α) x.2)) :
    ∀ ws : List Space, Continuous (fun x : ℝ × Space => dirSpatialJet (V x.1) ws x.2) := by
  intro ws
  induction ws using List.reverseRecOn generalizing V with
  | nil => exact hC 0 Fin.elim0
  | append_singleton ws w ih =>
      have hfun : (fun x : ℝ × Space => dirSpatialJet (V x.1) (ws ++ [w]) x.2) =
          fun x => ∑ j : Fin 3, (w j) •
            dirSpatialJet (dirSpatialJet (V x.1) [coordinateVector j]) ws x.2 := by
        funext x
        rw [congrFun (PhaseDerivStepSub.dirSpatialJet_append_singleton_eq_sum_coord
          (hV x.1) ws w) x.2]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [HigherPhaseSub.dirSpatialJet_append]
      rw [hfun]
      refine continuous_finsetSum _ fun j _ => ?_
      refine Continuous.const_smul (ih (V := fun τ => dirSpatialJet (V τ) [coordinateVector j])
        (fun τ => JointSmoothSub.contDiff_infty_dirSpatialJet (hV τ) _) fun k α => ?_) (w j)
      have hfun' : (fun x : ℝ × Space => dirSpatialJet (dirSpatialJet (V x.1) [coordinateVector j])
          (PhaseDerivStepSub.coordWord α) x.2) =
          fun x => dirSpatialJet (V x.1) (PhaseDerivStepSub.coordWord (Fin.snoc α j)) x.2 := by
        funext x
        rw [PhaseDerivStepSub.coordWord_snoc, HigherPhaseSub.dirSpatialJet_append]
      rw [hfun']
      exact hC (k + 1) (Fin.snoc α j)

/-- The jets of a jointly smooth phase field are jointly continuous. -/
theorem continuous_dirSpatialJet_of_joint {F : ℝ → SpatialField}
    (hF : ContDiff ℝ ∞ (fun x : ℝ × Space => F x.1 x.2)) (ws : List Space) :
    Continuous (fun x : ℝ × Space => dirSpatialJet (F x.1) ws x.2) :=
  (PhaseDerivStepSub.contDiff_joint_dirSpatialJet hF ws).continuous

/-- The classical comoving partial of a jointly smooth phase field is jointly smooth. -/
theorem contDiff_joint_comovingPartial {F : ℝ → SpatialField}
    (hF : ContDiff ℝ ∞ (fun x : ℝ × Space => F x.1 x.2)) :
    ContDiff ℝ ∞ (fun x : ℝ × Space => comovingPartial F x.1 x.2) := by
  have h1 := PhaseDerivStepSub.contDiff_joint_phasePartial hF
  have h2 : ContDiff ℝ ∞ (fun x : ℝ × Space => spatialRadialDrift (F x.1) x.2) := by
    have heq : (fun x : ℝ × Space => spatialRadialDrift (F x.1) x.2) =
        fun x => fderiv ℝ (fun x : ℝ × Space => F x.1 x.2) x ((0 : ℝ), x.2) := by
      funext x
      have h := PhaseDerivStepSub.dirSpatialJet_singleton_eq_joint_fderiv hF x.2 x.1 x.2
      rw [dirSpatialJet_cons, dirSpatialJet_nil] at h
      exact h
    rw [heq]
    exact ((contDiff_infty_iff_fderiv.1 hF).2).clm_apply (contDiff_const.prodMk contDiff_snd)
  exact h1.sub (h2.const_smul (1 / 2 : ℝ))

/-- **Joint continuity of the jets of the Leray term** (`PartII-b:S3/1/1/2/1/2/2`, SP
2552-2562). Under the hypotheses of `BgCorrComovingJetDeriv`, every spatial jet of
`𝔓(U·∇U) = smoothConvectiveLeray U U`, `U = bgField p z`, is jointly continuous on
`ℝ × ℝ³`. -/
def LerayJetContinuous : Prop :=
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
      (∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ, ContDiff ℝ k (bgField p z τ) ∧
        (∀ y : Space, ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ M) ∧
        eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal M) →
      IsUniformSmoothL4SliceFamily (bgField p z) →
      (Blueprint.IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ)) →
      (∀ i : Fin 2, Blueprint.IsBoundedBackground (p.inlet i) ∧
        ∀ τ, IsSolenoidal (p.inlet i τ)) →
      ∀ ws : List Space, Continuous (fun x : ℝ × Space =>
        dirSpatialJet (smoothConvectiveLeray (bgField p z) (bgField p z) x.1) ws x.2)

/-- **`CorrRHSJetContinuous` from `LerayJetContinuous`.** -/
theorem corrRHSJetContinuous_of_leray (hL : LerayJetContinuous) : CorrRHSJetContinuous := by
  intro Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₁, hν₁, hL'⟩ := hL Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₂, hν₂, hPer⟩ := exists_period_le_one_of_bgRegime (dp := dp) hdm
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, ?_⟩
  intro p d hReg hν hAge hMode hRawCD hInCD z hProj hz hGraph hSlice hBg hRaw hInlet ws
  have hν₁' : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hν₂' : p.ν ≤ ν₂ := hν.trans (min_le_right _ _)
  have hP1 : p.period ≤ 1 := hPer p d hReg hν₂'
  have hLer := hL' p d hReg hν₁' hAge hMode hRawCD hInCD z hProj hz hGraph hSlice hBg hRaw hInlet
  -- smoothness of the slices
  have hcorrS : ∀ τ, ContDiff ℝ ∞ (p.corr z τ) :=
    CoordDerivSub.corr_slice_contDiff_infty_of_period_le_one p hP1 z hGraph
  have hrawS : ∀ τ, ContDiff ℝ ∞ (p.raw τ) := PhaseDerivStepSub.contDiff_slice_of_joint hRawCD
  have hinS : ∀ (i : Fin 2) τ, ContDiff ℝ ∞ (p.inlet i τ) := fun i =>
    PhaseDerivStepSub.contDiff_slice_of_joint (hInCD i)
  have hUS : ∀ τ, ContDiff ℝ ∞ (bgField p z τ) := HigherPhaseSub.sliceFamily_contDiff_infty hBg
  have hLS : ∀ τ, ContDiff ℝ ∞ (smoothConvectiveLeray (bgField p z) (bgField p z) τ) :=
    HigherPhaseSub.sliceFamily_contDiff_infty
      (HigherPhaseSub.sliceFamily_smoothConvectiveLeray smoothLeraySliceRegularity_proof _ _ hBg hBg)
  have hDS : ∀ τ, ContDiff ℝ ∞ (spatialDiffReact p.ν (bgField p z τ)) := fun τ =>
    CoordDerivSub.contDiff_infty_spatialDiffReact p.ν (hUS τ)
  have hRP : ∀ τ, ContDiff ℝ ∞ (comovingPartial p.raw τ) :=
    ComovingTowerSub.contDiff_comovingPartial hRawCD
  have hIP : ∀ (i : Fin 2) τ, ContDiff ℝ ∞ (comovingPartial (p.inlet i) τ) := fun i =>
    ComovingTowerSub.contDiff_comovingPartial (hInCD i)
  have hSP : ∀ τ, ContDiff ℝ ∞ (fun y => ∑ i : Fin 2, p.coord z i • comovingPartial (p.inlet i) τ y) :=
    fun τ => ContDiff.sum fun i _ => (hIP i τ).const_smul (p.coord z i)
  have hES : ∀ τ, ContDiff ℝ ∞ (fun y => ∑ i : Fin 2, p.coord z i • p.inlet i τ y) :=
    fun τ => ContDiff.sum fun i _ => (hinS i τ).const_smul (p.coord z i)
  -- continuity of the jets of the pieces
  have hcorrC : ∀ vs : List Space,
      Continuous (fun x : ℝ × Space => dirSpatialJet (p.corr z x.1) vs x.2) := by
    refine continuous_dirSpatialJet_of_coordWord hcorrS fun k α => ?_
    obtain ⟨g, hg⟩ := hGraph k
    have hfun : (fun x : ℝ × Space =>
        dirSpatialJet (p.corr z x.1) (PhaseDerivStepSub.coordWord α) x.2) =
        fun x => contRep (g α : Yq p.period q0E) x.1 x.2 := by
      funext x
      exact CoordDerivSub.dirSpatialJet_contRep_coordWord_eq hP1 p.ν_pos hGraph k g hg x.1 α x.2
    rw [hfun]
    exact (isContRep_contRep_D hP1 p.ν_pos (g α)).1
  have hEC : ∀ vs : List Space, Continuous (fun x : ℝ × Space =>
      dirSpatialJet (fun y => ∑ i : Fin 2, p.coord z i • p.inlet i x.1 y) vs x.2) := by
    intro vs
    have hfun : (fun x : ℝ × Space =>
        dirSpatialJet (fun y => ∑ i : Fin 2, p.coord z i • p.inlet i x.1 y) vs x.2) =
        fun x => ∑ i : Fin 2, p.coord z i • dirSpatialJet (p.inlet i x.1) vs x.2 := by
      funext x
      rw [congrFun (HigherPhaseSub.dirSpatialJet_sum Finset.univ
        (F := fun i y => p.coord z i • p.inlet i x.1 y)
        (fun i _ => (hinS i x.1).const_smul (p.coord z i)) vs) x.2]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact congrFun (HigherPhaseSub.dirSpatialJet_smul (p.coord z i) (hinS i x.1) vs) x.2
    rw [hfun]
    exact continuous_finsetSum _ fun i _ =>
      (continuous_dirSpatialJet_of_joint (hInCD i) vs).const_smul (p.coord z i)
  have hUC : ∀ vs : List Space,
      Continuous (fun x : ℝ × Space => dirSpatialJet (bgField p z x.1) vs x.2) := by
    intro vs
    have hfun : (fun x : ℝ × Space => dirSpatialJet (bgField p z x.1) vs x.2) =
        fun x => dirSpatialJet (p.raw x.1) vs x.2 +
          dirSpatialJet (fun y => ∑ i : Fin 2, p.coord z i • p.inlet i x.1 y) vs x.2 +
          dirSpatialJet (p.corr z x.1) vs x.2 := by
      funext x
      have e : bgField p z x.1 =
          (p.raw x.1 + fun y => ∑ i : Fin 2, p.coord z i • p.inlet i x.1 y) + p.corr z x.1 := rfl
      have hA : ContDiff ℝ ∞ (p.raw x.1 + fun y => ∑ i : Fin 2, p.coord z i • p.inlet i x.1 y) :=
        (hrawS x.1).add (hES x.1)
      have hB : ContDiff ℝ ∞ (fun y => ∑ i : Fin 2, p.coord z i • p.inlet i x.1 y) := hES x.1
      rw [e, HigherPhaseSub.dirSpatialJet_add hA (hcorrS x.1) vs,
        HigherPhaseSub.dirSpatialJet_add (hrawS x.1) hB vs]
      rfl
    rw [hfun]
    exact ((continuous_dirSpatialJet_of_joint hRawCD vs).add (hEC vs)).add (hcorrC vs)
  have hDC : ∀ vs : List Space, Continuous (fun x : ℝ × Space =>
      dirSpatialJet (spatialDiffReact p.ν (bgField p z x.1)) vs x.2) := by
    intro vs
    have hfun : (fun x : ℝ × Space =>
        dirSpatialJet (spatialDiffReact p.ν (bgField p z x.1)) vs x.2) =
        fun x => p.ν • ∑ j : Fin 3, dirSpatialJet (bgField p z x.1)
            ([EuclideanSpace.single j 1, EuclideanSpace.single j 1] ++ vs) x.2 +
          (1 / 2 : ℝ) • dirSpatialJet (bgField p z x.1) vs x.2 := by
      funext x
      rw [CoordDerivSub.dirSpatialJet_spatialDiffReact p.ν (hUS x.1) vs]
      simp only [spatialDiffReact, spatialLaplacian, Pi.add_apply, Pi.smul_apply]
      congr 2
    rw [hfun]
    exact ((continuous_finsetSum _ fun j _ => hUC _).const_smul p.ν).add
      ((hUC vs).const_smul (1 / 2 : ℝ))
  have hSC : Continuous (fun x : ℝ × Space =>
      dirSpatialJet (fun y => ∑ i : Fin 2, p.coord z i • comovingPartial (p.inlet i) x.1 y)
        ws x.2) := by
    have hfun : (fun x : ℝ × Space =>
        dirSpatialJet (fun y => ∑ i : Fin 2, p.coord z i • comovingPartial (p.inlet i) x.1 y)
          ws x.2) =
        fun x => ∑ i : Fin 2, p.coord z i • dirSpatialJet (comovingPartial (p.inlet i) x.1) ws x.2 := by
      funext x
      rw [congrFun (HigherPhaseSub.dirSpatialJet_sum Finset.univ
        (F := fun i y => p.coord z i • comovingPartial (p.inlet i) x.1 y)
        (fun i _ => (hIP i x.1).const_smul (p.coord z i)) ws) x.2]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact congrFun (HigherPhaseSub.dirSpatialJet_smul (p.coord z i) (hIP i x.1) ws) x.2
    rw [hfun]
    exact continuous_finsetSum _ fun i _ =>
      (continuous_dirSpatialJet_of_joint (contDiff_joint_comovingPartial (hInCD i)) ws).const_smul
        (p.coord z i)
  -- assemble
  have hfun : (fun x : ℝ × Space => dirSpatialJet (corrComovingRHS p z x.1) ws x.2) =
      fun x => (dirSpatialJet (spatialDiffReact p.ν (bgField p z x.1)) ws x.2 -
          dirSpatialJet (smoothConvectiveLeray (bgField p z) (bgField p z) x.1) ws x.2) -
        (dirSpatialJet (comovingPartial p.raw x.1) ws x.2 +
          dirSpatialJet (fun y => ∑ i : Fin 2, p.coord z i • comovingPartial (p.inlet i) x.1 y)
            ws x.2) := by
    funext x
    have e : corrComovingRHS p z x.1 =
        (spatialDiffReact p.ν (bgField p z x.1) -
            smoothConvectiveLeray (bgField p z) (bgField p z) x.1) -
          (comovingPartial p.raw x.1 +
            fun y => ∑ i : Fin 2, p.coord z i • comovingPartial (p.inlet i) x.1 y) := rfl
    have hA : ContDiff ℝ ∞ (spatialDiffReact p.ν (bgField p z x.1) -
        smoothConvectiveLeray (bgField p z) (bgField p z) x.1) := (hDS x.1).sub (hLS x.1)
    have hB : ContDiff ℝ ∞ (comovingPartial p.raw x.1 +
        fun y => ∑ i : Fin 2, p.coord z i • comovingPartial (p.inlet i) x.1 y) :=
      (hRP x.1).add (hSP x.1)
    have hB' : ContDiff ℝ ∞
        (fun y => ∑ i : Fin 2, p.coord z i • comovingPartial (p.inlet i) x.1 y) := hSP x.1
    rw [e, HigherPhaseSub.dirSpatialJet_sub hA hB ws,
      HigherPhaseSub.dirSpatialJet_sub (hDS x.1) (hLS x.1) ws,
      HigherPhaseSub.dirSpatialJet_add (hRP x.1) hB' ws]
    rfl
  rw [hfun]
  exact ((hDC ws).sub (hLer ws)).sub
    ((continuous_dirSpatialJet_of_joint (contDiff_joint_comovingPartial hRawCD) ws).add hSC)

/-- **Conditional assembly of `BgCorrComovingJetDeriv` (`PartII-b:S3/1/1/2/1/2`)** from the base
identification `CorrT0BaseRep` (`/1`) and the joint continuity of the Leray term
`LerayJetContinuous` (`/2`). -/
theorem bgCorrComovingJetDeriv_of_base_leray (hB : CorrT0BaseRep) (hL : LerayJetContinuous) :
    BgCorrComovingJetDeriv :=
  bgCorrComovingJetDeriv_of_base hB (corrRHSJetContinuous_of_leray hL)

end CorrComovingSub

end UnforcedLeray.Short.IIb

end
