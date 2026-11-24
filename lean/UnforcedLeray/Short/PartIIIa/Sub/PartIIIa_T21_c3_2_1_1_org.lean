import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.BlockPropagator.InteriorSplit
import UnforcedLeray.Units.B0104.Dyson
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1_b_org
import UnforcedLeray.Lib.PlanarSectorsB.DilationPlane

/-!
# Part III-a, `PartIII-a:T21/c3/2/1/1/org`: split of the singular-limit compact Duhamel leaf

Source of record: `the November 2 reference manuscript` (SP), lines 2937-2982.

Leaf (2) of `BlockPropagator/InteriorSplit.lean` (`DampedComplBlockIntDuhamelInterior κ`) is split into
four Prop leaves following SP 2962-2982:

* `RelInteractionDyson κ` (SP 2920-2925, 2974-2978): bounded `A_rel` (`IsDampedComplBlockInt`) with the
  Dyson iteration defined (hence `U_rel = ` Dyson sum, `IsDuhamelEvolution`);
* `RelBlockDiagonal κ` (SP 2943-2944, 2974-2977): `U_rel B 0` preserves data supported in the
  entrance cell and data supported outside it;
* `RelCellBlockBound κ` (SP 2962-2979): on cell-supported data, strong/adjoint-strong convergence of
  `F_rel` to the damped radial transport, norm convergence of `A_rel` to the compact planar damped
  interaction, `compact_duhamel_dyson` (`UnforcedLeray.B0104`), and the planar limit bound
  `‖U₀ B 0‖ ≤ C₀ e^{-hB}`, `‖F₀ B 0‖ ≤ e^{-Re λ B}`;
* `RelExteriorBlockBound κ` (SP 2979-2980): on exterior data `U_rel = F_rel`-exterior, bounded by
  `clockN⁻¹ e^{3B/(2b)} ≤ C₀ e^{-hB} + δ` (`norm_extDilW_cellLen_le_exp`; `C₀ ≥ 1`, `h ≤ Re λ`).

Correction of the constant: `U_n = F_n + (U_n - F_n)` and the norm limit of the remainder only gives
`‖U_n(B,0)|cell‖ ≤ ‖F_n‖ + ‖U₀ - F₀‖ + o(1) ≤ α' + C₀ e^{-hB} + e^{-Re λ B} + o(1)`, the
source's `C₀ e^{-hB} + 2 e^{-γ B}` (SP 2980).  The earlier bound `C₀ e^{-hB} + α' + δ_gap` has one
copy of the free norm too few: `DampedComplBlockIntDuhamelInteriorE` below carries the
extra `Real.exp (-P.eigenvalue.re * B)`.  The consumer (`DampedComplBlockPropagator`) must be


Also see the caution of the attempt: the planar limit is `Q e^{t(L-λ)}Q + e^{-t}P`, and
`hSeedDecay` bounds only the `Q` part, so `‖U₀(B,0)‖ ≤ C₀ e^{-hB}` (leaf `RelCellBlockBound`)
must be checked against SP 2976-2979 by its prover.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub

namespace BlockPropagatorInteriorSub

namespace OrgSplit

/-- `W` vanishes a.e. on the entrance cell `B0579.cell d`. -/
def IsExteriorSupportedW {m : ℝ} (d : ℝ) (W : Planar.L2w m) : Prop :=
  ∀ᵐ z ∂(volume : Measure ℂ), cToPlane z ∈ B0579.cell d → (W : ℂ → ℂ) z = 0

/-- The planar damped seed-complement decay hypothesis `hSeedDecay` of
`DampedComplBlockIntDuhamelInterior` (SP 2926-2935). -/
def SeedCtx (κ : PlanarFrameKernels) (P : PlanarData) (m C₀ h : ℝ) : Prop :=
  ∃ (lam : ℂ) (h_prof : ℝ → ℂ) (hh : MemLp h_prof 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
      PartI.IsSeedXG lam (hh.toLp h_prof) ℓ ∧
      (∀ y, κ.e 0 y = PartI.seedPlanar h_prof (planeToC y)) ∧
      (∀ y, κ.e 1 y = conj (PartI.seedPlanar h_prof (planeToC y))) ∧
      (∀ f : ℂ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
        ∫ y, κ.lamP 0 y * f (planeToC y) =
          PartI.seedEll h_prof (Planar.NUE.Polar.angularSector f 2) ∧
        ∫ y, κ.lamP 1 y * f (planeToC y) =
          conj (PartI.seedEll h_prof
            (fun r => conj (Planar.NUE.Polar.angularSector f (-2) r)))) ∧
      (∀ (hm1 : 1 < m) (t : ℝ), 0 ≤ t → ∀ f : B0008.XjM 0 m,
        ∃ (u : Planar.L2w m) (g : B0008.XjM 0 m),
          (⇑u =ᵐ[volume] fun y =>
            PartI.xValue f y - PartI.seedProjFun h_prof (PartI.xValue f) y) ∧
          PartI.xValue g =ᵐ[volume] ⇑(Planar.eulerGroupW hm1 t u) ∧
          Real.exp (-P.eigenvalue.re * t) * ‖g‖ ≤ C₀ * Real.exp (-h * t) * ‖f‖)

/-- Clamp of a time to the block `[0, B]`. -/
def clampB (B τ : ℝ) : ℝ := max 0 (min τ B)

/-- The clamped free family `Fc τ σ = F_rel (clamp τ) (clamp σ)`: it coincides with `F_rel` on the
block `0 ≤ σ ≤ τ ≤ B` (the only region constrained by `IsPeriodizedRelFreeBlockEvol`) and is
measurable in `σ` wherever `F_rel` is measurable on `Icc 0 B`. -/
def clampF {m : ℝ} (B : ℝ) (F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m) :
    ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m :=
  fun τ σ => F_rel (clampB B τ) (clampB B σ)

/-- The clamped interaction family `Ac τ = A_rel (clamp τ)`. -/
def clampA {m : ℝ} (B : ℝ) (A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m) :
    ℝ → Planar.L2w m →L[ℂ] Planar.L2w m :=
  fun τ => A_rel (clampB B τ)

theorem clampB_le (B τ : ℝ) (hB : 0 ≤ B) : clampB B τ ≤ B := by
  unfold clampB; exact max_le hB (min_le_right _ _)

theorem clampB_mono (B : ℝ) {a b : ℝ} (h : a ≤ b) : clampB B a ≤ clampB B b := by
  unfold clampB; exact max_le_max le_rfl (min_le_min_right _ h)

theorem clampB_nonneg (B τ : ℝ) : 0 ≤ clampB B τ := le_max_left _ _

/-- The data of a block: periodized relative free evolution `F_rel` bounded by `M_free`, damped
interaction `A_rel` bounded by `K_A`, the Duhamel evolution `U_rel`, and `α'` bounding `F_rel B 0`
on cell-supported data. -/
def BlockTriple (κ : PlanarFrameKernels) (P : PlanarData) (ν m : ℝ)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ B M_free K_A α' : ℝ)
    (F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m)
    (A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m)
    (U_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m) : Prop :=
  IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel ∧
  (∀ σ τ : ℝ, σ ≤ τ → τ ≤ σ + B → ‖F_rel τ σ‖ ≤ M_free) ∧
  IsDampedComplBlockInt κ P ν m tr t₁ B A_rel ∧
  (∀ τ : ℝ, ‖A_rel τ‖ ≤ K_A) ∧
  UnforcedLeray.B0104.IsDuhamelEvolution (ι := Unit) B (fun _ => clampF B F_rel)
    (fun _ => clampA B A_rel) (fun _ => U_rel) ∧
  (∀ W : Planar.L2w m, IsCellSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) W →
    ‖F_rel B 0 W‖ ≤ α' * ‖W‖)

/-- **Leaf 1 (SP 2920-2925, 2974-2978)**: the damped complement interaction `A_rel` exists as a
bounded operator family (the bounded extension of `movDampedComplInt`, uniformly in the train and
the entrance time, with `‖A_rel τ‖ ≤ K_A`), and the Dyson iteration of `(F_rel, A_rel)` is defined
for every bounded periodized relative free evolution `F_rel`. -/
def RelInteractionDyson (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m → ∀ K B M_free b_free : ℝ, 0 < B → 0 ≤ M_free → 1 ≤ b_free →
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
                  ∃ A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
                    IsDampedComplBlockInt κ P ν m tr t₁ B A_rel ∧
                    (∀ τ : ℝ, ‖A_rel τ‖ ≤ K_A) ∧
                    UnforcedLeray.B0104.DysonDefined (ι := Unit) B
                      (fun _ => clampF B F_rel) (fun _ => clampA B A_rel)

/-- **Leaf 2 (SP 2943-2944, 2974-2977)**: block diagonality.  `F_rel` maps cell data to cell data
and exterior data to exterior data; `A_rel` lands in the cell and `U_rel` is the Dyson sum, so
`U_rel B 0` maps cell-supported (entrance cell `d(t₁)`) data to cell-supported (exit cell `d(t₂)`)
data and likewise for exterior data (the exterior dilation changes the cell). -/
def RelBlockDiagonal (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m → ∀ K B M_free K_A : ℝ, 0 < B → 0 ≤ M_free → 0 ≤ K_A →
    ∃ b_prop : ℝ, 1 ≤ b_prop ∧
      ∀ b : ℝ, b_prop ≤ b →
        ∃ ν_prop : ℝ, 0 < ν_prop ∧
          ∀ ν (_hν : ν ∈ Ioc 0 ν_prop), ∀ _hF : PerFrameFacts κ ν m b K,
            ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
              UnforcedLeray.Short.PartI.IsBUCTrain tr →
              ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
                movingZ ν t₂ - movingZ ν t₁ = B →
                ∀ (α' : ℝ) F_rel A_rel U_rel,
                  BlockTriple κ P ν m tr t₁ B M_free K_A α' F_rel A_rel U_rel →
                  (∀ W : Planar.L2w m,
                    IsCellSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) W →
                      IsCellSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) (U_rel B 0 W)) ∧
                  (∀ W : Planar.L2w m,
                    IsExteriorSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) W →
                      IsExteriorSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) (U_rel B 0 W))

/-- **Leaf 3 (SP 2962-2979)**: the singular-limit compact Duhamel bound on cell-supported data. -/
def RelCellBlockBound (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m → ∀ K C₀ h B M_free K_A δ_gap : ℝ,
    0 < C₀ → 0 < h → h ≤ P.eigenvalue.re → 0 < B → 0 ≤ M_free → 0 ≤ K_A → 0 < δ_gap →
    SeedCtx κ P m C₀ h →
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
                        (C₀ * Real.exp (-h * B) + α' + Real.exp (-P.eigenvalue.re * B) + δ_gap) *
                          ‖W‖

/-- **Leaf 4 (SP 2979-2980)**: on data vanishing on the cell, `U_rel B 0` is the exterior
dilation `clockN⁻¹ S`, of norm at most `clockN⁻¹ e^{3B/(2b)} ≤ C₀ e^{-hB} + δ_gap` (using
`C₀ ≥ 1`, from `SeedCtx` at `t = 0`, and `h ≤ Re λ`). -/
def RelExteriorBlockBound (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m → ∀ K C₀ h B M_free K_A δ_gap : ℝ,
    0 < C₀ → 0 < h → h ≤ P.eigenvalue.re → 0 < B → 0 ≤ M_free → 0 ≤ K_A → 0 < δ_gap →
    SeedCtx κ P m C₀ h →
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
                    IsExteriorSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) W →
                      ‖U_rel B 0 W‖ ≤ (C₀ * Real.exp (-h * B) + δ_gap) * ‖W‖

/-! ### Pythagoras for disjoint supports and the block norm lemma -/

theorem norm_add_sq_of_disjoint {m : ℝ} (d : ℝ) (U V : Planar.L2w m)
    (hU : IsCellSupportedW d U) (hV : IsExteriorSupportedW d V) :
    ‖U + V‖ ^ 2 = ‖U‖ ^ 2 + ‖V‖ ^ 2 := by
  have hadd : ∀ᵐ z ∂(volume : Measure ℂ), ((U + V : Planar.L2w m) : ℂ → ℂ) z = U z + V z :=
    (Planar.volume_ac m).ae_le (Lp.coeFn_add U V)
  have hiU : Integrable (fun y => (B0008.density m y : ℝ) * ‖(U : ℂ → ℂ) y‖ ^ 2) volume :=
    Planar.integrable_density_sq (Lp.memLp U)
  have hiV : Integrable (fun y => (B0008.density m y : ℝ) * ‖(V : ℂ → ℂ) y‖ ^ 2) volume :=
    Planar.integrable_density_sq (Lp.memLp V)
  rw [Planar.norm_sq_L2w_eq, Planar.norm_sq_L2w_eq U, Planar.norm_sq_L2w_eq V,
    ← integral_add hiU hiV]
  refine integral_congr_ae ?_
  filter_upwards [hadd, hU, hV] with z hz hzU hzV
  rw [hz]
  by_cases hc : cToPlane z ∈ B0579.cell d
  · rw [hzV hc]; simp
  · rw [hzU hc]; simp

/-- Two-cell block norm lemma: if `T` maps `d_in`-cell-supported data to `d_out`-cell-supported
data and `d_in`-exterior data to `d_out`-exterior data, each with bound `c`, then `‖T‖ ≤ c`. -/
theorem norm_le_of_blocks2 {m : ℝ} (d_in d_out : ℝ) (T : Planar.L2w m →L[ℂ] Planar.L2w m)
    {c : ℝ} (hc : 0 ≤ c)
    (h1 : ∀ W, IsCellSupportedW d_in W → IsCellSupportedW d_out (T W) ∧ ‖T W‖ ≤ c * ‖W‖)
    (h2 : ∀ W, IsExteriorSupportedW d_in W →
      IsExteriorSupportedW d_out (T W) ∧ ‖T W‖ ≤ c * ‖W‖) :
    ‖T‖ ≤ c := by
  have hS : MeasurableSet {z : ℂ | cToPlane z ∈ B0579.cell d_in} := by
    have : {z : ℂ | cToPlane z ∈ B0579.cell d_in} = {z : ℂ | z.re ∈ Ico (-d_in / 2) (d_in / 2)} := by
      ext z; simp [B0579.cell, cToPlane, neg_div]
    rw [this]
    exact measurableSet_Ico.preimage Complex.measurable_re
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun W => ?_
  set S : Set ℂ := {z : ℂ | cToPlane z ∈ B0579.cell d_in} with hSdef
  have hmem : MemLp (S.indicator (W : ℂ → ℂ)) 2 (Planar.wMeasure m) :=
    (Lp.memLp W).indicator hS
  have hmem' : MemLp (Sᶜ.indicator (W : ℂ → ℂ)) 2 (Planar.wMeasure m) :=
    (Lp.memLp W).indicator hS.compl
  set Wc : Planar.L2w m := hmem.toLp _ with hWc
  set We : Planar.L2w m := hmem'.toLp _ with hWe
  have hWc_ae : (Wc : ℂ → ℂ) =ᵐ[Planar.wMeasure m] S.indicator (W : ℂ → ℂ) := hmem.coeFn_toLp
  have hWe_ae : (We : ℂ → ℂ) =ᵐ[Planar.wMeasure m] Sᶜ.indicator (W : ℂ → ℂ) := hmem'.coeFn_toLp
  have hWc' := (Planar.volume_ac m).ae_le hWc_ae
  have hWe' := (Planar.volume_ac m).ae_le hWe_ae
  have hcs : IsCellSupportedW d_in Wc := by
    filter_upwards [hWc'] with z hz hzc
    rw [hz]; exact Set.indicator_of_notMem (show z ∉ S from hzc) _
  have hes : IsExteriorSupportedW d_in We := by
    filter_upwards [hWe'] with z hz hzc
    rw [hz]; exact Set.indicator_of_notMem (show z ∉ Sᶜ from fun h => h hzc) _
  have hsum : W = Wc + We := by
    have h3 : (W : ℂ → ℂ) =ᵐ[Planar.wMeasure m] ⇑(Wc + We) := by
      filter_upwards [hWc_ae, hWe_ae, Lp.coeFn_add Wc We] with z a b c'
      rw [c', Pi.add_apply, a, b]
      by_cases hz : z ∈ S
      · simp [hz]
      · simp [hz]
    exact Lp.ext h3
  have hpy := norm_add_sq_of_disjoint d_in Wc We hcs hes
  rw [← hsum] at hpy
  obtain ⟨hTc, hTcn⟩ := h1 Wc hcs
  obtain ⟨hTe, hTen⟩ := h2 We hes
  have hpyT := norm_add_sq_of_disjoint d_out (T Wc) (T We) hTc hTe
  have hTW : T W = T Wc + T We := by rw [← map_add, ← hsum]
  have hsq : ‖T W‖ ^ 2 ≤ (c * ‖W‖) ^ 2 := by
    rw [hTW, hpyT, mul_pow, hpy, mul_add]
    nlinarith [mul_le_mul hTcn hTcn (norm_nonneg _) (mul_nonneg hc (norm_nonneg _)),
      mul_le_mul hTen hTen (norm_nonneg _) (mul_nonneg hc (norm_nonneg _)), sq_nonneg ‖Wc‖,
      sq_nonneg ‖We‖]
  exact abs_le_of_sq_le_sq' hsq (mul_nonneg hc (norm_nonneg _)) |>.2

/-- **Corrected leaf (b)** (SP 2920-2925, 2962-2982): as `DampedComplBlockIntDuhamelInterior`, with the
full-block bound `‖U_rel B 0‖ ≤ C₀ e^{-hB} + α' + e^{-Re λ B} + δ_gap` (SP 2980: `C₀e^{-hB}+2e^{-γB}`),
the extra term being the norm of the planar limit free evolution. -/
def DampedComplBlockIntDuhamelInteriorE (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K : ℝ,
  ∀ C₀ h B M_free b_free δ_gap : ℝ,
    0 < C₀ → 0 < h → h ≤ P.eigenvalue.re → 0 < B → 0 ≤ M_free → 1 ≤ b_free → 0 < δ_gap →
    SeedCtx κ P m C₀ h →
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
                    ‖U_rel B 0‖ ≤ C₀ * Real.exp (-h * B) + α' + Real.exp (-P.eigenvalue.re * B)
                      + δ_gap

/-- **Assembly (R9)** of `DampedComplBlockIntDuhamelInteriorE κ` from the four leaves. -/
theorem dampedComplBlockIntDuhamelInteriorE_of (κ : PlanarFrameKernels)
    (h1 : RelInteractionDyson κ) (h2 : RelBlockDiagonal κ) (h3 : RelCellBlockBound κ)
    (h4 : RelExteriorBlockBound κ) : DampedComplBlockIntDuhamelInteriorE κ := by
  intro hκ P hP m hm K C₀ h B M_free b_free δ_gap hC₀ hh hh_le hB hM hb hδ hSeed
  obtain ⟨K_A, b1, hK_A, hb1, hL1⟩ := h1 hκ P hP m hm K B M_free b_free hB hM hb
  obtain ⟨b2, hb2, hL2⟩ := h2 hκ P hP m hm K B M_free K_A hB hM hK_A
  obtain ⟨b3, hb3, hL3⟩ := h3 hκ P hP m hm K C₀ h B M_free K_A δ_gap hC₀ hh hh_le hB hM hK_A
    hδ hSeed
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
  refine norm_le_of_blocks2 (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁))
    (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) (U () B 0)
    (c := C₀ * Real.exp (-h * B) + α' + Real.exp (-P.eigenvalue.re * B) + δ_gap)
    (by positivity) ?_ ?_
  · exact fun W hW => ⟨hcell W hW, hce W hW⟩
  · intro W hW
    refine ⟨hext W hW, (hex W hW).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

/-! ### Joint-measurability variants (`DysonDefined` needs `(τ,σ)`-measurability of `F_rel`) -/

/-- **Leaf 1, joint-measurability form (SP 2920-2925, 2974-2978)**: the damped complement interaction `A_rel` exists as a
bounded operator family (the bounded extension of `movDampedComplInt`, uniformly in the train and
the entrance time, with `‖A_rel τ‖ ≤ K_A`), and the Dyson iteration of `(F_rel, A_rel)` is defined
for every bounded periodized relative free evolution `F_rel`. -/
def RelInteractionDysonJ (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m → ∀ K B M_free b_free : ℝ, 0 < B → 0 ≤ M_free → 1 ≤ b_free →
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
                  UnforcedLeray.Short.IIIa.DysonJointMeas.FJointMeas (clampF B F_rel) →
                  ∃ A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
                    IsDampedComplBlockInt κ P ν m tr t₁ B A_rel ∧
                    (∀ τ : ℝ, ‖A_rel τ‖ ≤ K_A) ∧
                    UnforcedLeray.B0104.DysonDefined (ι := Unit) B
                      (fun _ => clampF B F_rel) (fun _ => clampA B A_rel)

/-- **Joint-measurability form of leaf (b)** (SP 2920-2925, 2962-2982): as `DampedComplBlockIntDuhamelInterior`, with the
full-block bound `‖U_rel B 0‖ ≤ C₀ e^{-hB} + α' + e^{-Re λ B} + δ_gap` (SP 2980: `C₀e^{-hB}+2e^{-γB}`),
the extra term being the norm of the planar limit free evolution. -/
def DampedComplBlockIntDuhamelInteriorEJ (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K : ℝ,
  ∀ C₀ h B M_free b_free δ_gap : ℝ,
    0 < C₀ → 0 < h → h ≤ P.eigenvalue.re → 0 < B → 0 ≤ M_free → 1 ≤ b_free → 0 < δ_gap →
    SeedCtx κ P m C₀ h →
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
                  UnforcedLeray.Short.IIIa.DysonJointMeas.FJointMeas (clampF B F_rel) →
                  ∀ α' : ℝ, 0 ≤ α' →
                  (∀ W : Planar.L2w m, IsCellSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) W →
                    ‖F_rel B 0 W‖ ≤ α' * ‖W‖) →
                  ∃ (A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m)
                    (U_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m),
                    IsDampedComplBlockInt κ P ν m tr t₁ B A_rel ∧
                    UnforcedLeray.B0104.IsDuhamelEvolution (ι := Unit) B
                      (fun _ => clampF B F_rel) (fun _ => clampA B A_rel) (fun _ => U_rel) ∧
                    (∀ τ : ℝ, ‖A_rel τ‖ ≤ K_A) ∧
                    ‖U_rel B 0‖ ≤ C₀ * Real.exp (-h * B) + α' + Real.exp (-P.eigenvalue.re * B)
                      + δ_gap

/-- **Assembly (R9)** of `DampedComplBlockIntDuhamelInteriorE κ` from the four leaves. -/
theorem dampedComplBlockIntDuhamelInteriorEJ_of (κ : PlanarFrameKernels)
    (h1 : RelInteractionDysonJ κ) (h2 : RelBlockDiagonal κ) (h3 : RelCellBlockBound κ)
    (h4 : RelExteriorBlockBound κ) : DampedComplBlockIntDuhamelInteriorEJ κ := by
  intro hκ P hP m hm K C₀ h B M_free b_free δ_gap hC₀ hh hh_le hB hM hb hδ hSeed
  obtain ⟨K_A, b1, hK_A, hb1, hL1⟩ := h1 hκ P hP m hm K B M_free b_free hB hM hb
  obtain ⟨b2, hb2, hL2⟩ := h2 hκ P hP m hm K B M_free K_A hB hM hK_A
  obtain ⟨b3, hb3, hL3⟩ := h3 hκ P hP m hm K C₀ h B M_free K_A δ_gap hC₀ hh hh_le hB hM hK_A
    hδ hSeed
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
  intro ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hB_eq F_rel hF_rel hF_sub hF_meas hFj α' hα' hα'bd
  have hν1' : ν ∈ Ioc 0 ν1 := ⟨hν.1, hν.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hν2' : ν ∈ Ioc 0 ν2 := ⟨hν.1, hν.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hν3' : ν ∈ Ioc 0 ν3 := ⟨hν.1, hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hν4' : ν ∈ Ioc 0 ν4 := ⟨hν.1, hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨A_rel, hA_rel, hA_bd, hD⟩ :=
    hU1 ν hν1' hF tr htr t₁ t₂ ht₁ h12 hbt hB_eq F_rel hF_rel hF_sub hF_meas hFj
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
  refine norm_le_of_blocks2 (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁))
    (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) (U () B 0)
    (c := C₀ * Real.exp (-h * B) + α' + Real.exp (-P.eigenvalue.re * B) + δ_gap)
    (by positivity) ?_ ?_
  · exact fun W hW => ⟨hcell W hW, hce W hW⟩
  · intro W hW
    refine ⟨hext W hW, (hex W hW).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

end OrgSplit

end BlockPropagatorInteriorSub

end UnforcedLeray.Short.IIIa
