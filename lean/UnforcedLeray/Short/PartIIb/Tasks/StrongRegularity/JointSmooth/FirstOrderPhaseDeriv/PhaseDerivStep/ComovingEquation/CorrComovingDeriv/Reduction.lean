import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_comoving
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_1_2_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_1_2_1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation.CorrComovingDeriv.WeakToStrong
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation.CorrComovingDeriv.Jets

/-!
# Reduction of `PartII-b:S3/1/1/2/1/2` (`BgCorrComovingJetDeriv`) to the `T₀`-identification
of the jets of the correction

Source of record: `the November 2 reference manuscript`,
lines 2519-2523 ("The projected equation is $A_0U+\mathbb P(U\cdot\nabla U)=0$ with zero
residual") and 2559-2562 ("the resulting $C_\tau W^{k,4}$ regularity and the projected equation
give all time derivatives").

The graph hypothesis gives, for every coordinate multi-index `α`, the distributional comoving
derivative `T0D (g α) ∈ Y_{q₀}` of `∂^α w`, `w = p.wOf z`. The remaining analytic input is the
identification of `T0D (g α)` with the candidate field
`corrJetComovingRHS p z α = ∂^α(T₀w) + (|α|/2) ∂^α w`, `T₀w = corrComovingRHS p z`
(`comovingEvolRHS p.ν (bgField p z) - T₀U_raw - E_ε T₀α`), together with the joint continuity
of that field (`CorrJetT0Rep`). Given it, the proved weak-to-strong lemma
`CorrComovingSub.hasDerivAt_comoving_of_weak` gives the pointwise ray derivative of every
coordinate jet (`contRep (g α) = ∂^α(p.corr z)` by `CoordDerivSub.dirSpatialJet_contRep_coordWord_eq`),
and `hasComovingJetDeriv_of_coordWord` passes from coordinate words to all direction lists.

Proved here (zero `sorry`): `hasComovingJetDeriv_of_coordWord`, `isContRep_contRep_D`,
`bgCorrComovingJetDeriv_of_t0Rep : CorrJetT0Rep → BgCorrComovingJetDeriv`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.Blueprint

namespace CorrComovingSub

/-! ## 1. The candidate comoving derivatives -/

/-- The right side of `BgCorrComovingJetDeriv`: `T₀w = T₀U - T₀U_raw - E_ε T₀α` with
`T₀U = comovingEvolRHS p.ν (bgField p z) = νΔU + ½U - 𝔓(U·∇U)` (SP 2519-2523). -/
def corrComovingRHS (p : Params) (z : p.Z) : ℝ → SpatialField :=
  comovingEvolRHS p.ν (bgField p z) -
    (comovingPartial p.raw +
      fun τ y => ∑ i : Fin 2, p.coord z i • comovingPartial (p.inlet i) τ y)

/-- The comoving derivative of the coordinate jet `∂^α w`, `|α| = k`:
`T₀∂^α w = ∂^α T₀w + (k/2) ∂^α w`. -/
def corrJetComovingRHS (p : Params) (z : p.Z) {k : ℕ} (α : Fin k → Fin 3) :
    ℝ → SpatialField :=
  fun τ y => dirSpatialJet (corrComovingRHS p z τ) (PhaseDerivStepSub.coordWord α) y +
    ((k : ℝ) / 2) • dirSpatialJet (p.corr z τ) (PhaseDerivStepSub.coordWord α) y

/-! ## 2. Coordinate-word reduction for `HasComovingJetDeriv` -/

/-- Finite sums of `HasDerivAt` (local copy). -/
theorem hasDerivAt_finset_sum' {ι : Type*} (s : Finset ι)
    {f : ι → ℝ → Space} {f' : ι → Space} {t : ℝ}
    (hf : ∀ i ∈ s, HasDerivAt (f i) (f' i) t) :
    HasDerivAt (fun t' => ∑ i ∈ s, f i t') (∑ i ∈ s, f' i) t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using hasDerivAt_const t (0 : Space)
  | @insert a s ha ih =>
      have hfun : (fun t' => ∑ i ∈ insert a s, f i t') =
          fun t' => f a t' + ∑ i ∈ s, f i t' := by
        funext t'
        exact Finset.sum_insert ha
      rw [hfun, Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- **Coordinate-word reduction.** If `V, V'` have smooth slices and every coordinate jet of `V`
has, along every comoving ray, derivative `∂^α V' + (k/2) ∂^α V` at `t = 0`, then
`HasComovingJetDeriv V V'`. -/
theorem hasComovingJetDeriv_of_coordWord {V V' : ℝ → SpatialField}
    (hV : ∀ τ, ContDiff ℝ ∞ (V τ)) (hV' : ∀ τ, ContDiff ℝ ∞ (V' τ))
    (hCoord : ∀ (k : ℕ) (α : Fin k → Fin 3) (τ : ℝ) (y : Space),
      HasDerivAt (fun t : ℝ => dirSpatialJet (V (τ + t)) (PhaseDerivStepSub.coordWord α)
          (Real.exp (-t / 2) • y))
        (dirSpatialJet (V' τ) (PhaseDerivStepSub.coordWord α) y +
          ((k : ℝ) / 2) • dirSpatialJet (V τ) (PhaseDerivStepSub.coordWord α) y) 0) :
    HasComovingJetDeriv V V' := by
  intro ws
  induction ws using List.reverseRecOn generalizing V V' with
  | nil =>
      intro τ y
      have h0 := hCoord 0 Fin.elim0 τ y
      simpa using h0
  | append_singleton ws w ih =>
      intro τ y
      set c : ℝ := (((ws ++ [w]).length : ℕ) : ℝ) / 2 with hc
      have hfun : (fun t : ℝ => dirSpatialJet (V (τ + t)) (ws ++ [w]) (Real.exp (-t / 2) • y)) =
          fun t => ∑ j : Fin 3, (w j) •
            dirSpatialJet (V (τ + t)) (ws ++ [coordinateVector j]) (Real.exp (-t / 2) • y) := by
        funext t
        exact congrFun
          (PhaseDerivStepSub.dirSpatialJet_append_singleton_eq_sum_coord (hV (τ + t)) ws w) _
      have hval1 : dirSpatialJet (V' τ) (ws ++ [w]) y =
          ∑ j : Fin 3, (w j) • dirSpatialJet (V' τ) (ws ++ [coordinateVector j]) y :=
        congrFun (PhaseDerivStepSub.dirSpatialJet_append_singleton_eq_sum_coord (hV' τ) ws w) y
      have hval2 : dirSpatialJet (V τ) (ws ++ [w]) y =
          ∑ j : Fin 3, (w j) • dirSpatialJet (V τ) (ws ++ [coordinateVector j]) y :=
        congrFun (PhaseDerivStepSub.dirSpatialJet_append_singleton_eq_sum_coord (hV τ) ws w) y
      have hsum : dirSpatialJet (V' τ) (ws ++ [w]) y + c • dirSpatialJet (V τ) (ws ++ [w]) y =
          ∑ j : Fin 3, (w j) • (dirSpatialJet (V' τ) (ws ++ [coordinateVector j]) y +
            c • dirSpatialJet (V τ) (ws ++ [coordinateVector j]) y) := by
        rw [hval1, hval2, Finset.smul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_add, smul_comm c (w j)]
      rw [hfun, hsum]
      refine hasDerivAt_finset_sum' Finset.univ fun j _ => HasDerivAt.const_smul (w j) ?_
      -- the derived fields `∂_j V`, `∂_j V' + ½ ∂_j V`
      set e : Space := coordinateVector j with he
      have hVj : ∀ τ', ContDiff ℝ ∞ (dirSpatialJet (V τ') [e]) := fun τ' =>
        JointSmoothSub.contDiff_infty_dirSpatialJet (hV τ') [e]
      have hV'j : ∀ τ', ContDiff ℝ ∞ (dirSpatialJet (V' τ') [e]) := fun τ' =>
        JointSmoothSub.contDiff_infty_dirSpatialJet (hV' τ') [e]
      have hsm : ∀ τ', ContDiff ℝ ∞ ((1 / 2 : ℝ) • dirSpatialJet (V τ') [e]) := fun τ' => by
        have h := (hVj τ').const_smul (1 / 2 : ℝ)
        exact h
      have hjet : ∀ (τ' : ℝ) (vs : List Space),
          dirSpatialJet (dirSpatialJet (V' τ') [e] + (1 / 2 : ℝ) • dirSpatialJet (V τ') [e]) vs =
            dirSpatialJet (V' τ') (vs ++ [e]) + (1 / 2 : ℝ) • dirSpatialJet (V τ') (vs ++ [e]) := by
        intro τ' vs
        rw [HigherPhaseSub.dirSpatialJet_add (hV'j τ') (hsm τ') vs,
          HigherPhaseSub.dirSpatialJet_smul _ (hVj τ') vs,
          HigherPhaseSub.dirSpatialJet_append, HigherPhaseSub.dirSpatialJet_append]
      have hih := ih (V := fun τ' => dirSpatialJet (V τ') [e])
        (V' := fun τ' => dirSpatialJet (V' τ') [e] + (1 / 2 : ℝ) • dirSpatialJet (V τ') [e])
        hVj (fun τ' => (hV'j τ').add (hsm τ')) (fun k α τ' y' => ?_) τ y
      · -- conclude from the induction hypothesis
        rw [hjet τ ws] at hih
        simp only [HigherPhaseSub.dirSpatialJet_append] at hih
        have hlen : c = (1 / 2 : ℝ) + ((ws.length : ℕ) : ℝ) / 2 := by
          rw [hc]
          simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
          ring
        have hval : dirSpatialJet (V' τ) (ws ++ [e]) y + c • dirSpatialJet (V τ) (ws ++ [e]) y =
            (dirSpatialJet (V' τ) (ws ++ [e]) + (1 / 2 : ℝ) • dirSpatialJet (V τ) (ws ++ [e])) y +
              ((ws.length : ℝ) / 2) • dirSpatialJet (V τ) (ws ++ [e]) y := by
          rw [hlen, add_smul, Pi.add_apply, Pi.smul_apply, add_assoc]
        rw [hval]
        exact hih
      · -- the coordinate hypothesis for the derived fields
        have h1 := hCoord (k + 1) (Fin.snoc α j) τ' y'
        rw [PhaseDerivStepSub.coordWord_snoc] at h1
        rw [hjet τ']
        simp only [HigherPhaseSub.dirSpatialJet_append]
        convert h1 using 1
        rw [Pi.add_apply, Pi.smul_apply, add_assoc, ← add_smul]
        congr 2
        push_cast
        ring

/-! ## 3. The analytic leaf -/

/-- **`T₀`-identification of the correction jets** (SP 2519-2523, 2559-2562). Under the
hypotheses of `BgCorrComovingJetDeriv`, for every coordinate multi-index `α` the distributional
comoving derivative `T0D (g α) ∈ Y_{q₀}` of `∂^α w` (`w = p.wOf z`) is represented almost
everywhere on `ℝ × ℝ³` by the jointly continuous field `corrJetComovingRHS p z α`
(`∂^α T₀w + (|α|/2)∂^α w` with `T₀w = corrComovingRHS p z`). -/
def CorrJetT0Rep : Prop :=
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
      ∀ (k : ℕ) (g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E),
        IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (g α : Yq p.period q0E)) →
        ∀ α : Fin k → Fin 3,
          Continuous (fun x : ℝ × Space => corrJetComovingRHS p z α x.1 x.2) ∧
          ∀ᵐ x : ℝ × Space ∂volume,
            rep (B0411.T0D (g α)) x.1 x.2 = realC (corrJetComovingRHS p z α x.1 x.2)

/-- **Base `T₀`-identification** (`PartII-b:S3/1/1/2/1/2/1`, SP 2519-2523: "The projected
equation is $A_0U+\mathbb P(U\cdot\nabla U)=0$"). Under the hypotheses of
`BgCorrComovingJetDeriv`, every distributional comoving derivative `b` of `w = p.wOf z`
(`HasPhaseOp driftT (p.wOf z) b`; `b = T₀w ∈ Y_{q₀}` exists by the graph hypothesis) equals the
real field `corrComovingRHS p z = νΔU + ½U - 𝔓(U·∇U) - T₀U_raw - E_ε T₀α` almost everywhere on
`ℝ × ℝ³`. -/
def CorrT0BaseRep : Prop :=
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
      ∀ b : Yq p.period q0E, HasPhaseOp driftT (p.wOf z) b →
        ∀ᵐ x : ℝ × Space ∂volume, rep b x.1 x.2 = realC (corrComovingRHS p z x.1 x.2)

/-- **Joint continuity of the jets of `T₀w`** (`PartII-b:S3/1/1/2/1/2/2`, SP 2559-2562). Under
the hypotheses of `BgCorrComovingJetDeriv`, every spatial directional jet of
`corrComovingRHS p z` is jointly continuous on `ℝ × ℝ³`. -/
def CorrRHSJetContinuous : Prop :=
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
      ∀ ws : List Space,
        Continuous (fun x : ℝ × Space => dirSpatialJet (corrComovingRHS p z x.1) ws x.2)

/-! ## 4. Assembly -/

local instance fact_q0_ge_one_corrComoving : Fact (1 ≤ ENNReal.ofReal B0281.q0) :=
  inferInstanceAs (Fact (1 ≤ q0E))

/-- The selected representative of an element of the maximal graph is a jointly continuous
representative of its real part. -/
theorem isContRep_contRep_D {P : ℝ} [Fact (0 < P)] (hP1 : P ≤ 1) {ν : ℝ} (hν : 0 < ν)
    (u : B0411.D P ν q0E) : IsContRep (u : Yq P q0E) (contRep (u : Yq P q0E)) :=
  contRep_spec ⟨_, graph_globalRealChartRep_isContRep hP1 S1Sub.s1_q0_holder S1Sub.s1_q0_gt hν
    (hasPhaseOp_T0D u) (hasPhaseOp_nuLapD u)⟩

/-- **Conditional assembly of `BgCorrComovingJetDeriv` (`PartII-b:S3/1/1/2/1/2`)** from the
`T₀`-identification `CorrJetT0Rep`. -/
theorem bgCorrComovingJetDeriv_of_t0Rep (hT0 : CorrJetT0Rep) : BgCorrComovingJetDeriv := by
  intro Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₁, hν₁, hT⟩ := hT0 Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₂, hν₂, hPer⟩ := exists_period_le_one_of_bgRegime (dp := dp) hdm
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, ?_⟩
  intro p d hReg hν hAge hMode hRawCD hInCD z hProj hz hGraph hSlice hBg hRaw hInlet
  have hν₁' : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hν₂' : p.ν ≤ ν₂ := hν.trans (min_le_right _ _)
  have hP1 : p.period ≤ 1 := hPer p d hReg hν₂'
  have hT' := hT p d hReg hν₁' hAge hMode hRawCD hInCD z hProj hz hGraph hSlice hBg hRaw hInlet
  have hV : ∀ τ, ContDiff ℝ ∞ (p.corr z τ) :=
    CoordDerivSub.corr_slice_contDiff_infty_of_period_le_one p hP1 z hGraph
  have hU : ∀ τ, ContDiff ℝ ∞ (comovingEvolRHS p.ν (bgField p z) τ) :=
    HigherPhaseSub.sliceFamily_contDiff_infty (sliceFamily_comovingEvolRHS p.ν hBg)
  have hRawP : ∀ τ, ContDiff ℝ ∞ (comovingPartial p.raw τ) :=
    ComovingTowerSub.contDiff_comovingPartial hRawCD
  have hInP : ∀ (i : Fin 2) τ, ContDiff ℝ ∞ (comovingPartial (p.inlet i) τ) := fun i =>
    ComovingTowerSub.contDiff_comovingPartial (hInCD i)
  have hV' : ∀ τ, ContDiff ℝ ∞ (corrComovingRHS p z τ) := fun τ =>
    (hU τ).sub ((hRawP τ).add (ContDiff.sum fun i _ => (hInP i τ).const_smul (p.coord z i)))
  change HasComovingJetDeriv (p.corr z) (corrComovingRHS p z)
  refine hasComovingJetDeriv_of_coordWord hV hV' fun k α τ y => ?_
  obtain ⟨g, hg⟩ := hGraph k
  obtain ⟨hcont, hae⟩ := hT' k g hg α
  have hfun : (fun t : ℝ => dirSpatialJet (p.corr z (τ + t)) (PhaseDerivStepSub.coordWord α)
      (Real.exp (-t / 2) • y)) =
      fun t => contRep (g α : Yq p.period q0E) (τ + t) (Real.exp (-t / 2) • y) := by
    funext t
    exact CoordDerivSub.dirSpatialJet_contRep_coordWord_eq hP1 p.ν_pos hGraph k g hg (τ + t) α _
  rw [hfun]
  exact hasDerivAt_comoving_of_weak q0E_ne_top (hasPhaseOp_T0D (g α))
    (isContRep_contRep_D hP1 p.ν_pos (g α)) hcont hae τ y

/-- **Conditional assembly of `BgCorrComovingJetDeriv` (`PartII-b:S3/1/1/2/1/2`)** from the base
identification `CorrT0BaseRep` and the joint continuity `CorrRHSJetContinuous`: the weak-to-strong
identity `integral_identity_comoving_of_weak` for `w`, then all jets by
`hasComovingJetDeriv_of_integral_identity`. -/
theorem bgCorrComovingJetDeriv_of_base (hB : CorrT0BaseRep) (hC : CorrRHSJetContinuous) :
    BgCorrComovingJetDeriv := by
  intro Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₁, hν₁, hB'⟩ := hB Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₃, hν₃, hC'⟩ := hC Sig lam q hSig hlam m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₂, hν₂, hPer⟩ := exists_period_le_one_of_bgRegime (dp := dp) hdm
  refine ⟨min ν₁ (min ν₂ ν₃), lt_min hν₁ (lt_min hν₂ hν₃), ?_⟩
  intro p d hReg hν hAge hMode hRawCD hInCD z hProj hz hGraph hSlice hBg hRaw hInlet
  have hν₁' : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hν₂' : p.ν ≤ ν₂ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν₃' : p.ν ≤ ν₃ := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hP1 : p.period ≤ 1 := hPer p d hReg hν₂'
  have hbase := hB' p d hReg hν₁' hAge hMode hRawCD hInCD z hProj hz hGraph hSlice hBg hRaw hInlet
  have hjc := hC' p d hReg hν₃' hAge hMode hRawCD hInCD z hProj hz hGraph hSlice hBg hRaw hInlet
  have hV : ∀ τ, ContDiff ℝ ∞ (p.corr z τ) :=
    CoordDerivSub.corr_slice_contDiff_infty_of_period_le_one p hP1 z hGraph
  have hU : ∀ τ, ContDiff ℝ ∞ (comovingEvolRHS p.ν (bgField p z) τ) :=
    HigherPhaseSub.sliceFamily_contDiff_infty (sliceFamily_comovingEvolRHS p.ν hBg)
  have hRawP : ∀ τ, ContDiff ℝ ∞ (comovingPartial p.raw τ) :=
    ComovingTowerSub.contDiff_comovingPartial hRawCD
  have hInP : ∀ (i : Fin 2) τ, ContDiff ℝ ∞ (comovingPartial (p.inlet i) τ) := fun i =>
    ComovingTowerSub.contDiff_comovingPartial (hInCD i)
  have hV' : ∀ τ, ContDiff ℝ ∞ (corrComovingRHS p z τ) := fun τ =>
    (hU τ).sub ((hRawP τ).add (ContDiff.sum fun i _ => (hInP i τ).const_smul (p.coord z i)))
  obtain ⟨g, hg⟩ := hGraph 0
  have hg0 : (g Fin.elim0 : Yq p.period q0E) = p.wOf z := hg
  have hbu : HasPhaseOp driftT (p.wOf z) (B0411.T0D (g Fin.elim0)) := by
    rw [← hg0]
    exact hasPhaseOp_T0D (g Fin.elim0)
  have hFrep : IsContRep (p.wOf z) (p.corr z) := by
    have h := isContRep_contRep_D hP1 p.ν_pos (g Fin.elim0)
    rw [hg0] at h
    exact h
  have hI : ∀ (τ₀ t : ℝ) (x : Space),
      p.corr z (τ₀ + t) (Real.exp (-t / 2) • x) - p.corr z τ₀ x =
        ∫ r in (0 : ℝ)..t, corrComovingRHS p z (τ₀ + r) (Real.exp (-r / 2) • x) :=
    fun τ₀ t x => integral_identity_comoving_of_weak q0E_ne_top hbu hFrep (hjc [])
      (hbase _ hbu) τ₀ t x
  change HasComovingJetDeriv (p.corr z) (corrComovingRHS p z)
  exact hasComovingJetDeriv_of_integral_identity hV hV' hjc hI

end CorrComovingSub

end UnforcedLeray.Short.IIb

end
