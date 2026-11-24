import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org

/-!
# Part III-a, `PartIII-a:T21/c3/2/1/1/org/3/org`: corrected cell-block bound

Source: `the November 2 reference manuscript` (SP) 2920-2925, 2962-2982.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub

namespace BlockPropagatorInteriorSub

open OrgSplit
open scoped ComplexConjugate ContDiff InnerProductSpace InnerProduct ENNReal

namespace OrgSplit3

/-- The entrance cell `{z | cToPlane z ∈ B0579.cell d}` is measurable. -/
theorem measurableSet_cellC (d : ℝ) : MeasurableSet {z : ℂ | cToPlane z ∈ B0579.cell d} := by
  have : {z : ℂ | cToPlane z ∈ B0579.cell d} = {z : ℂ | z.re ∈ Ico (-d / 2) (d / 2)} := by
    ext z; simp [B0579.cell, cToPlane, neg_div]
  rw [this]
  exact measurableSet_Ico.preimage Complex.measurable_re

/-- Cell projection `1_{cell d}` on `Planar.L2w m` (the cell projection of SP 2962-2972). -/
def cellProjW (m d : ℝ) : Planar.L2w m →L[ℂ] Planar.L2w m :=
  LinearMap.mkContinuous
    { toFun := fun W => ((Lp.memLp W).indicator (measurableSet_cellC d)).toLp _
      map_add' := fun U V => by
        refine Lp.ext ?_
        have h1 := ((Lp.memLp U).indicator (measurableSet_cellC d)).coeFn_toLp
        have h2 := ((Lp.memLp V).indicator (measurableSet_cellC d)).coeFn_toLp
        have h3 := ((Lp.memLp (U + V)).indicator (measurableSet_cellC d)).coeFn_toLp
        have h4 := Lp.coeFn_add (((Lp.memLp U).indicator (measurableSet_cellC d)).toLp _)
          (((Lp.memLp V).indicator (measurableSet_cellC d)).toLp _)
        have h5 := Lp.coeFn_add U V
        filter_upwards [h1, h2, h3, h4, h5] with z a b c e f
        rw [e, Pi.add_apply, a, b, c]
        by_cases hz : z ∈ {z : ℂ | cToPlane z ∈ B0579.cell d}
        · simp only [Set.indicator_of_mem hz]; exact f
        · simp [Set.indicator_of_notMem hz]
      map_smul' := fun c U => by
        refine Lp.ext ?_
        have h1 := ((Lp.memLp U).indicator (measurableSet_cellC d)).coeFn_toLp
        have h3 := ((Lp.memLp (c • U)).indicator (measurableSet_cellC d)).coeFn_toLp
        have h4 := Lp.coeFn_smul c (((Lp.memLp U).indicator (measurableSet_cellC d)).toLp _)
        have h5 := Lp.coeFn_smul c U
        filter_upwards [h1, h3, h4, h5] with z a c' e f
        simp only [RingHom.id_apply]
        rw [e, Pi.smul_apply, a, c']
        by_cases hz : z ∈ {z : ℂ | cToPlane z ∈ B0579.cell d}
        · simp [Set.indicator_of_mem hz, f]
        · simp [Set.indicator_of_notMem hz] } 1 (fun W => by
        rw [one_mul]
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [Lp.norm_def, Lp.norm_def, ENNReal.toReal_le_toReal (Lp.eLpNorm_ne_top _)
          (Lp.eLpNorm_ne_top _)]
        rw [eLpNorm_congr_ae (((Lp.memLp W).indicator (measurableSet_cellC d)).coeFn_toLp)]
        exact eLpNorm_indicator_le _)


/-- Seed-projection bound (SP 2974-2979): the planar limit is `Q e^{t(L-λ)}Q + e^{-t}P`, and `P`
(the seed projection `f ↦ seedProjFun h_prof (xValue f)`) has norm at most `Cproj`.
`SeedCtx` bounds only the `Q` part. -/
def SeedProjBdd (κ : PlanarFrameKernels) (_P : PlanarData) (m Cproj : ℝ) : Prop :=
  ∃ (lam : ℂ) (h_prof : ℝ → ℂ) (hh : MemLp h_prof 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
      PartI.IsSeedXG lam (hh.toLp h_prof) ℓ ∧
      (∀ y, κ.e 0 y = PartI.seedPlanar h_prof (planeToC y)) ∧
      (∀ y, κ.e 1 y = conj (PartI.seedPlanar h_prof (planeToC y))) ∧
      (∀ f : B0008.XjM 0 m, ∃ u : Planar.L2w m,
        (⇑u =ᵐ[volume] fun y => PartI.seedProjFun h_prof (PartI.xValue f) y) ∧
        ‖u‖ ≤ Cproj * ‖f‖)

/-- Successive limit `ν → 0` after `b → ∞` of a property `Q` of a block (SP 2962-2963): there are
`b₀ ≥ 1`, and for `b ≥ b₀` a `ν₀ > 0`, so that `Q` holds for every `ν ≤ ν₀`, every train, every
entrance time and every block of moving length `B` ending at `clockTheta ≥ b`. -/
def SuccBlock (κ : PlanarFrameKernels) (m K B : ℝ)
    (Q : ∀ ν : ℝ, UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)) → ℝ → ℝ → Prop) : Prop :=
  ∃ b₀ : ℝ, 1 ≤ b₀ ∧ ∀ b : ℝ, b₀ ≤ b → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ ν ∈ Ioc 0 ν₀, PerFrameFacts κ ν m b K →
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
          movingZ ν t₂ - movingZ ν t₁ = B → Q ν tr t₁ t₂

/-- Limiting relative free evolution with the real damping rate: `e^{-γ(t-s)} T(t-s)`,
`γ = Re λ` (SP 2919, 2927). -/
def planarRelTransportRe (P : PlanarData) (m : ℝ) (t s : ℝ) :
    Planar.L2w m →L[ℂ] Planar.L2w m :=
  ((Real.exp (-P.eigenvalue.re * (t - s)) : ℝ) : ℂ) • Planar.transportGroupW m (t - s)

/-- **Leaf S (strong and adjoint-strong limits, SP 2962-2972)**: for each fixed `W` and `ε > 0`,
in the successive limit, uniformly in train, entrance time and `0 ≤ σ ≤ τ ≤ B`,
`F_rel τ σ ∘ (cell projection)` converges strongly, and its adjoint strongly, to the radial
transport `planarRelTransportRe`. -/
def RelStrongLimit (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m → ∀ K B : ℝ, 0 < B →
  ∀ ε : ℝ, 0 < ε → ∀ W : Planar.L2w m,
    SuccBlock κ m K B fun ν tr t₁ _t₂ =>
      ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
        IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
        ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ τ → τ ≤ B →
          ‖F_rel τ σ (cellProjW m (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) W) -
              planarRelTransportRe P m τ σ W‖ < ε ∧
          ‖ContinuousLinearMap.adjoint
                (F_rel τ σ ∘L cellProjW m (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁))) W -
              ContinuousLinearMap.adjoint (planarRelTransportRe P m τ σ) W‖ < ε

/-- **Leaf A (planar limit interaction, SP 2920-2925, 2972-2979)**: there is a compact damped planar
interaction `A0` (totally bounded range) such that the successive limit of `A_rel` is `A0` in
operator norm on `[0, B]`, and the Dyson solution `U0` of `(planarRelTransportRe, A0)` satisfies the
full planar bound `‖U0 B 0‖ ≤ C₀ e^{-hB} + Cproj e^{-B}`.  Free families are clamped to `[0,B]`
as in `clampF`, `clampA`. -/
def RelPlanarInteraction (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m → ∀ K C₀ h Cproj B : ℝ,
    0 < C₀ → 0 < h → h ≤ P.eigenvalue.re → 0 ≤ Cproj → 0 < B →
    SeedCtx κ P m C₀ h → SeedProjBdd κ P m Cproj →
    ∃ A0 : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
      (∀ r, IsCompactOperator (A0 r)) ∧
      TotallyBounded (range A0) ∧
      UnforcedLeray.B0104.DysonDefined (ι := Unit) B
        (fun _ => fun τ σ => planarRelTransportRe P m (clampB B τ) (clampB B σ))
        (fun _ r => A0 (clampB B r)) ∧
      (∀ U0 : Unit → ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
        UnforcedLeray.B0104.IsDysonSum B
          (fun _ => fun τ σ => planarRelTransportRe P m (clampB B τ) (clampB B σ))
          (fun _ r => A0 (clampB B r)) U0 →
        ‖U0 () B 0‖ ≤ C₀ * Real.exp (-h * B) + Cproj * Real.exp (-B)) ∧
      ∀ ε : ℝ, 0 < ε →
        SuccBlock κ m K B fun ν tr t₁ _t₂ =>
          ∀ A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
            IsDampedComplBlockInt κ P ν m tr t₁ B A_rel →
            ∀ r ∈ Icc (0 : ℝ) B, ‖A_rel r - A0 r‖ < ε

/-- **Corrected leaf 3 (SP 2962-2980)**: as `RelCellBlockBound`, with the planar full-limit term
`Cproj e^{-B}` (SP 2976-2980: `‖U0‖ + ‖F0‖ + ‖F_n‖`). Consumed by
`dampedComplBlockIntDuhamelInteriorEF_of`. -/
def RelCellBlockBoundF (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m → ∀ K C₀ h Cproj B M_free K_A δ_gap : ℝ,
    0 < C₀ → 0 < h → h ≤ P.eigenvalue.re → 0 ≤ Cproj → 0 < B → 0 ≤ M_free → 0 ≤ K_A →
    0 < δ_gap → SeedCtx κ P m C₀ h → SeedProjBdd κ P m Cproj →
    ∃ b_prop : ℝ, 1 ≤ b_prop ∧
      ∀ b : ℝ, b_prop ≤ b →
        ∃ ν_prop : ℝ, 0 < ν_prop ∧
          ∀ ν (_hν : ν ∈ Ioc 0 ν_prop), ∀ _hF : PerFrameFacts κ ν m b K,
            ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
              UnforcedLeray.Short.PartI.IsBUCTrain tr →
              ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
                movingZ ν t₂ - movingZ ν t₁ = B →
                ∀ (α' : ℝ), 0 ≤ α' → ∀ F_rel A_rel U_rel,
                  BlockTriple κ P ν m tr t₁ B M_free K_A α' F_rel A_rel U_rel →
                  ∀ W : Planar.L2w m,
                    IsCellSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) W →
                      ‖U_rel B 0 W‖ ≤
                        (C₀ * Real.exp (-h * B) + Cproj * Real.exp (-B) + α' +
                          Real.exp (-P.eigenvalue.re * B) + δ_gap) * ‖W‖

/-- **Corrected leaf (b)** (SP 2920-2925, 2962-2982): as `DampedComplBlockIntDuhamelInterior`, with the
full-block bound `‖U_rel B 0‖ ≤ C₀ e^{-hB} + α' + e^{-Re λ B} + δ_gap` (SP 2980: `C₀e^{-hB}+2e^{-γB}`),
the extra term being the norm of the planar limit free evolution. -/
def DampedComplBlockIntDuhamelInteriorEF (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K : ℝ,
  ∀ C₀ h Cproj B M_free b_free δ_gap : ℝ,
    0 < C₀ → 0 < h → h ≤ P.eigenvalue.re → 0 ≤ Cproj → 0 < B → 0 ≤ M_free → 1 ≤ b_free → 0 < δ_gap →
    SeedCtx κ P m C₀ h → SeedProjBdd κ P m Cproj →
    ∃ K_A b_prop : ℝ, 0 ≤ K_A ∧ b_free ≤ b_prop ∧
      ∀ b : ℝ, b_prop ≤ b →
        ∃ ν_prop : ℝ, 0 < ν_prop ∧
          ∀ ν (_hν : ν ∈ Ioc 0 ν_prop), ∀ _hF : PerFrameFacts κ ν m b K,
            ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
              UnforcedLeray.Short.PartI.IsBUCTrain tr →
              ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
                movingZ ν t₂ - movingZ ν t₁ = B →
                ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
                  IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
                  (∀ σ τ : ℝ, σ ≤ τ → τ ≤ σ + B → ‖F_rel τ σ‖ ≤ M_free) →
                  (∀ (τ : ℝ) (x : Planar.L2w m),
                    AEStronglyMeasurable (fun σ => F_rel τ σ x) (volume.restrict (Icc 0 B))) →
                  ∀ α' : ℝ, 0 ≤ α' →
                  (∀ W : Planar.L2w m, IsCellSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) W →
                    ‖F_rel B 0 W‖ ≤ α' * ‖W‖) →
                  ∃ (A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m)
                    (U_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m),
                    IsDampedComplBlockInt κ P ν m tr t₁ B A_rel ∧
                    UnforcedLeray.B0104.IsDuhamelEvolution (ι := Unit) B
                      (fun _ => clampF B F_rel) (fun _ => clampA B A_rel) (fun _ => U_rel) ∧
                    (∀ τ : ℝ, ‖A_rel τ‖ ≤ K_A) ∧
                    ‖U_rel B 0‖ ≤ C₀ * Real.exp (-h * B) + Cproj * Real.exp (-B) + α' + Real.exp (-P.eigenvalue.re * B)
                      + δ_gap

/-- **Assembly (R9)** of `DampedComplBlockIntDuhamelInteriorEF κ` from the four leaves. -/
theorem dampedComplBlockIntDuhamelInteriorEF_of (κ : PlanarFrameKernels)
    (h1 : RelInteractionDyson κ) (h2 : RelBlockDiagonal κ) (h3 : RelCellBlockBoundF κ)
    (h4 : RelExteriorBlockBound κ) : DampedComplBlockIntDuhamelInteriorEF κ := by
  intro hκ P hP m hm K C₀ h Cproj B M_free b_free δ_gap hC₀ hh hh_le hCp hB hM hb hδ hSeed hProj
  obtain ⟨K_A, b1, hK_A, hb1, hL1⟩ := h1 hκ P hP m hm K B M_free b_free hB hM hb
  obtain ⟨b2, hb2, hL2⟩ := h2 hκ P hP m hm K B M_free K_A hB hM hK_A
  obtain ⟨b3, hb3, hL3⟩ := h3 hκ P hP m hm K C₀ h Cproj B M_free K_A δ_gap hC₀ hh hh_le hCp hB hM hK_A
    hδ hSeed hProj
  obtain ⟨b4, hb4, hL4⟩ := h4 hκ P hP m hm K C₀ h B M_free K_A δ_gap hC₀ hh hh_le hB hM hK_A
    hδ hSeed
  refine ⟨K_A, max (max b1 b2) (max b3 b4), hK_A,
    hb1.trans ((le_max_left _ _).trans (le_max_left _ _)), fun b hbb => ?_⟩
  have hb1' : b1 ≤ b := ((le_max_left _ _).trans (le_max_left _ _)).trans hbb
  have hb2' : b2 ≤ b := ((le_max_right _ _).trans (le_max_left _ _)).trans hbb
  have hb3' : b3 ≤ b := ((le_max_left _ _).trans (le_max_right _ _)).trans hbb
  have hb4' : b4 ≤ b := ((le_max_right _ _).trans (le_max_right _ _)).trans hbb
  obtain ⟨ν1, hν1, hU1⟩ := hL1 b hb1'
  obtain ⟨ν2, hν2, hU2⟩ := hL2 b hb2'
  obtain ⟨ν3, hν3, hU3⟩ := hL3 b hb3'
  obtain ⟨ν4, hν4, hU4⟩ := hL4 b hb4'
  refine ⟨min (min ν1 ν2) (min ν3 ν4), lt_min (lt_min hν1 hν2) (lt_min hν3 hν4), ?_⟩
  intro ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hB_eq F_rel hF_rel hF_sub hF_meas α' hα' hα'bd
  have hν1' : ν ∈ Ioc 0 ν1 := ⟨hν.1, hν.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hν2' : ν ∈ Ioc 0 ν2 := ⟨hν.1, hν.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hν3' : ν ∈ Ioc 0 ν3 := ⟨hν.1, hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hν4' : ν ∈ Ioc 0 ν4 := ⟨hν.1, hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨A_rel, hA_rel, hA_bd, hD⟩ :=
    hU1 ν hν1' hF tr htr t₁ t₂ ht₁ h12 hbt hB_eq F_rel hF_rel hF_sub hF_meas
  have hFb : ∀ (p : Unit) (t s : ℝ), s ≤ t → t ≤ s + B →
      ‖(fun (_ : Unit) => clampF B F_rel) p t s‖ ≤ M_free := fun _ t s h1 h2 =>
    hF_sub _ _ (clampB_mono B h1)
      (by have := clampB_le B t hB.le; have := clampB_nonneg B s; linarith)
  have hAb : ∀ (p : Unit) (r : ℝ), ‖(fun (_ : Unit) => clampA B A_rel) p r‖ ≤ K_A :=
    fun _ r => hA_bd _
  obtain ⟨U, hU⟩ := UnforcedLeray.B0104.exists_isDysonSum (H := Planar.L2w m) hFb hAb hD
  have hDuh := hU.isDuhamelEvolution hFb hAb hD
  refine ⟨A_rel, fun t s => U () t s, hA_rel, hDuh, hA_bd, ?_⟩
  have htriple : BlockTriple κ P ν m tr t₁ B M_free K_A α' F_rel A_rel (fun t s => U () t s) :=
    ⟨hF_rel, hF_sub, hA_rel, hA_bd, hDuh, hα'bd⟩
  obtain ⟨hcell, hext⟩ := hU2 ν hν2' hF tr htr t₁ t₂ ht₁ h12 hbt hB_eq α' F_rel A_rel _ htriple
  have hce := hU3 ν hν3' hF tr htr t₁ t₂ ht₁ h12 hbt hB_eq α' hα' F_rel A_rel _ htriple
  have hex := hU4 ν hν4' hF tr htr t₁ t₂ ht₁ h12 hbt hB_eq α' hα' F_rel A_rel _ htriple
  have hexp1 : 0 ≤ Real.exp (-P.eigenvalue.re * B) := (Real.exp_pos _).le
  have hc0 : 0 ≤ C₀ * Real.exp (-h * B) := by positivity
  have hc1 : 0 ≤ Cproj * Real.exp (-B) := by positivity
  refine norm_le_of_blocks2 (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁))
    (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) (U () B 0)
    (c := C₀ * Real.exp (-h * B) + Cproj * Real.exp (-B) + α' + Real.exp (-P.eigenvalue.re * B) + δ_gap)
    (by positivity) ?_ ?_
  · exact fun W hW => ⟨hcell W hW, hce W hW⟩
  · intro W hW
    refine ⟨hext W hW, (hex W hW).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by nlinarith [hc1]) (norm_nonneg _)


end OrgSplit3
end BlockPropagatorInteriorSub
end UnforcedLeray.Short.IIIa
