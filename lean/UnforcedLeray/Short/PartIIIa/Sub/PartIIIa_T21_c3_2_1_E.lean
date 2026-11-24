import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_E.PeriodizedFreeBlock
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.BlockPropagator.RelBlockDiagonal
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_final
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.BlockPropagator.RelExteriorBlockBound
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.RelLeafB34
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.CompactDuhamelGapReg
import UnforcedLeray.Short.PartI.Tasks.EulerComplementJ0.XjM0Bridge

/-!
# Part III-a, `ORG:T21-c3-2-1-E-switch`: E-version bridge for `T21/c3/2/1/1`, `T21/c3/2/1`, `T21/c3/2`

Source of record: `the November 2 reference manuscript` (SP), lines 2919-2928 and
2937-2982 (`eq:short-causal-damped-complement`, `eq:short-causal-free-moving`,
`eq:short-causal-stable-moving`).

Per Rule R11 (never modifying existing definitions used by accepted files), this module defines the
faithful full-block `*E` statements beside `DampedComplBlockPropagator` and
`BlockCompactDuhamelGap` with identical hypotheses and the full-block bound
`C₀ * e^{-h B} + (1 + C₀) * e^{-B} + α_free + e^{-Re λ B} + δ_gap` (SP 2925-2928, 2976-2980):
1. `seedProjBdd_of_seedCtx`: derives `SeedProjBdd κ P m (1 + C₀)` directly from `SeedCtx κ P m C₀ h`
   at `t = 0` (`Planar.eulerGroupW_zero`, `PartI.xjM0_norm_eq_value`).
2. `dampedComplBlockPropagatorE_of` and unconditional `dampedComplBlockPropagatorE_proved`:
   assembles `DampedComplBlockPropagatorE κ` (with unclamped `IsDuhamelEvolution`) from
   `periodizedRelFreeBlockInterior`, `_root_.relB4s_leaf κ` (via continuous triangle clamping
   `triClamp`), `OrgSplit.relInteractionDysonJ κ`, `relBlockDiagonal κ`,
   `OrgSplit3.relCellBlockBoundF κ`, and `relExteriorBlockBound κ`.
3. `blockCompactDuhamelGapRegE_of` (and `blockCompactDuhamelGapE_of`): assembles
   `BlockCompactDuhamelGapE κ` from `DampedComplBlockPropagatorE κ` and
   `ComplBlockDuhamelVoCReg κ` (or `ComplBlockDuhamelVoC κ`).
4. `frameBlockContraction_ofE`: assembles the **unchanged** `FrameBlockContraction κ` from
   `BlockCompactDuhamelGapE κ`, `ComplModeForceOscillator κ`, and `ComplModeForceEulerError κ` by
   choosing `B > 0` (`exists_block_length_contractionE`) so that
   `C₀ * e^{-h B} + (1 + C₀) * e^{-B} + 3 * e^{-γ B} ≤ 1 / 4`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub

/-! ## 1. `SeedProjBdd κ P m (1 + C₀)` directly from `SeedCtx κ P m C₀ h` at `t = 0` -/

/-- Evaluating `SeedCtx κ P m C₀ h` at `t = 0` yields `SeedProjBdd κ P m (1 + C₀)`: since
`u = f - 𝒫 f` has `‖u‖ = ‖g‖ ≤ C₀ ‖f‖` (`eulerGroupW hm1 0 = 1`), `𝒫 f = f - u` lies in
`Planar.L2w m` with `‖𝒫 f‖ ≤ (1 + C₀) ‖f‖` (SP 2925-2935, 2974-2979). -/
theorem seedProjBdd_of_seedCtx {κ : PlanarFrameKernels} {P : PlanarData} {m C₀ h : ℝ}
    (hm : 8 < m) (hS : BlockPropagatorInteriorSub.OrgSplit.SeedCtx κ P m C₀ h) :
    BlockPropagatorInteriorSub.OrgSplit3.SeedProjBdd κ P m (1 + C₀) := by
  obtain ⟨lam, h_prof, hh, ℓ, hSeed, he0, he1, _, hdec⟩ := hS
  have hm1 : 1 < m := by linarith
  refine ⟨lam, h_prof, hh, ℓ, hSeed, he0, he1, fun f => ?_⟩
  obtain ⟨u, g, hu, hg, hb⟩ := hdec hm1 0 le_rfl f
  rw [Planar.eulerGroupW_zero] at hg
  have hg_ae : PartI.xValue g =ᵐ[volume] ⇑u := hg
  have hg_eq_u : (g : B0008.HjM 0 m).value = u :=
    Lp.ext ((B0008.wMeasure_ac m).ae_le hg_ae)
  have hu_norm : ‖u‖ ≤ C₀ * ‖f‖ := by
    simp only [mul_zero, Real.exp_zero, one_mul, mul_one] at hb
    calc ‖u‖ = ‖(g : B0008.HjM 0 m).value‖ := congrArg norm hg_eq_u.symm
      _ = ‖(g : B0008.HjM 0 m)‖ := (PartI.xjM0_norm_eq_value _).symm
      _ = ‖g‖ := rfl
      _ ≤ C₀ * ‖f‖ := hb
  let fval : Planar.L2w m := (f : B0008.HjM 0 m).value
  have hf_norm : ‖fval‖ = ‖f‖ := by
    calc ‖fval‖ = ‖(f : B0008.HjM 0 m)‖ := (PartI.xjM0_norm_eq_value _).symm
      _ = ‖f‖ := rfl
  refine ⟨fval - u, ?_, ?_⟩
  · have hsub_ae : ⇑(fval - u) =ᵐ[volume] fun y => fval y - u y :=
      (B0008.volume_ac m).ae_le (Lp.coeFn_sub fval u)
    filter_upwards [hsub_ae, hu] with y h1 h2
    rw [h1, h2]
    change PartI.xValue f y - (PartI.xValue f y - PartI.seedProjFun h_prof (PartI.xValue f) y) =
      PartI.seedProjFun h_prof (PartI.xValue f) y
    ring
  · calc ‖fval - u‖ ≤ ‖fval‖ + ‖u‖ := norm_sub_le _ _
      _ ≤ ‖f‖ + C₀ * ‖f‖ := add_le_add (le_of_eq hf_norm) hu_norm
      _ = (1 + C₀) * ‖f‖ := by ring

/-! ## 2. Continuous clamping onto `blockTriangle B` -/

namespace BlockPropagatorESub

open BlockPropagatorInteriorSub BlockPropagatorInteriorSub.OrgSplit

/-- Continuous retraction of `ℝ × ℝ` onto `VariationOfConstantsMildSub.blockTriangle B`:
`p ↦ (clampB B p.1, min (clampB B p.1) (clampB B p.2))`. -/
def triClamp (B : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (clampB B p.1, min (clampB B p.1) (clampB B p.2))

theorem continuous_clampB (B : ℝ) : Continuous (clampB B) := by
  unfold clampB
  exact continuous_const.max (continuous_id.min continuous_const)

theorem continuous_triClamp (B : ℝ) : Continuous (triClamp B) := by
  unfold triClamp
  have hc := continuous_clampB B
  exact (hc.comp continuous_fst).prodMk
    ((hc.comp continuous_fst).min (hc.comp continuous_snd))

theorem triClamp_mem_blockTriangle {B : ℝ} (hB : 0 ≤ B) (p : ℝ × ℝ) :
    triClamp B p ∈ VariationOfConstantsMildSub.blockTriangle B :=
  ⟨le_min (clampB_nonneg B p.1) (clampB_nonneg B p.2),
    min_le_left _ _,
    clampB_le B p.1 hB⟩

theorem clampB_idem {B : ℝ} (hB : 0 ≤ B) (r : ℝ) :
    clampB B (clampB B r) = clampB B r :=
  clampB_eq_self_of_mem B _ ⟨clampB_nonneg B r, clampB_le B r hB⟩

/-- Extension of `F_raw` from `blockTriangle B` to all of `ℝ × ℝ` via `triClamp B`. -/
def clampTriF {m : ℝ} (B : ℝ) (F_raw : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m) :
    ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m :=
  fun τ σ => F_raw (triClamp B (τ, σ)).1 (triClamp B (τ, σ)).2

theorem clampTriF_eq_of_triangle {m : ℝ} {B : ℝ}
    (F_raw : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m)
    {σ τ : ℝ} (hσ0 : 0 ≤ σ) (hστ : σ ≤ τ) (hτB : τ ≤ B) :
    clampTriF B F_raw τ σ = F_raw τ σ := by
  have hcτ : clampB B τ = τ := clampB_eq_self_of_mem B τ ⟨hσ0.trans hστ, hτB⟩
  have hcσ : clampB B σ = σ := clampB_eq_self_of_mem B σ ⟨hσ0, hστ.trans hτB⟩
  simp [clampTriF, triClamp, hcτ, hcσ, min_eq_right hστ]

theorem clampF_clampTriF_eq {m : ℝ} {B : ℝ} (hB : 0 ≤ B)
    (F_raw : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m) :
    clampF B (clampTriF B F_raw) = clampTriF B F_raw := by
  funext τ σ
  simp [clampF, clampTriF, triClamp, clampB_idem hB]

end BlockPropagatorESub

/-! ## 3. `DampedComplBlockPropagatorE` and unconditional assembly (`PartIII-a:T21/c3/2/1/1`) -/

/-- **E-version of `DampedComplBlockPropagator`** (`PartIII-a:T21/c3/2/1/1`, SP 2925-2928,
2962-2982): identical hypotheses to `DampedComplBlockPropagator`, with the faithful full-block
Compact Duhamel contraction bound
`‖U_rel B 0‖ ≤ C₀ * Real.exp (-h * B) + (1 + C₀) * Real.exp (-B) + α_free + Real.exp (-P.eigenvalue.re * B) + δ_gap`. -/
def DampedComplBlockPropagatorE (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K : ℝ,
  ∀ C₀ h B α_free δ_gap : ℝ,
    0 < C₀ → 0 < h → h ≤ P.eigenvalue.re → 0 < B → 0 < α_free → 0 < δ_gap →
    BlockPropagatorInteriorSub.OrgSplit.SeedCtx κ P m C₀ h →
    (∃ b_f : ℝ, 1 ≤ b_f ∧ ∀ b : ℝ, b_f ≤ b → ∃ ν_f : ℝ, 0 < ν_f ∧
      ∀ ν ∈ Ioc 0 ν_f, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
          movingZ ν t₂ - movingZ ν t₁ = B →
          ∀ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
            ∀ ω₀ : ℝ → B0579.Plane → ℝ, UnforcedLeray.Short.IIb.IsFreeCylFlow m tr t₁ f ω₀ →
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m
                  (JscaleInv (clockA ν t₂) (fun x => ((ω₀ t₂ x : ℝ) : ℂ))) ≤
                ENNReal.ofReal (clockN P ν t₁ t₂) *
                  (ENNReal.ofReal α_free *
                    xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m
                      (JscaleInv (clockA ν t₁) (fun x => ((f x : ℝ) : ℂ))))) →
    ∃ M_free K_A b_prop : ℝ, 0 ≤ M_free ∧ 0 ≤ K_A ∧ 1 ≤ b_prop ∧
      ∀ b : ℝ, b_prop ≤ b →
        ∃ ν_prop : ℝ, 0 < ν_prop ∧
          ∀ ν (_hν : ν ∈ Ioc 0 ν_prop), ∀ _hF : PerFrameFacts κ ν m b K,
            ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
              UnforcedLeray.Short.PartI.IsBUCTrain tr →
              ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
                movingZ ν t₂ - movingZ ν t₁ = B →
                ∃ (F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m)
                  (A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m)
                  (U_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m),
                  IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel ∧
                  IsDampedComplBlockInt κ P ν m tr t₁ B A_rel ∧
                  UnforcedLeray.B0104.IsDuhamelEvolution (ι := Unit) B
                    (fun _ => F_rel) (fun _ => A_rel) (fun _ => U_rel) ∧
                  (∀ σ τ : ℝ, σ ≤ τ → τ ≤ σ + B → ‖F_rel τ σ‖ ≤ M_free) ∧
                  (∀ τ : ℝ, ‖A_rel τ‖ ≤ K_A) ∧
                  ‖U_rel B 0‖ ≤
                    C₀ * Real.exp (-h * B) + (1 + C₀) * Real.exp (-B) + α_free +
                      Real.exp (-P.eigenvalue.re * B) + δ_gap

/-- Conditional assembly of `DampedComplBlockPropagatorE κ` from `PeriodizedRelFreeBlockInterior`,
`RelInteractionDysonJ κ`, `RelBlockDiagonal κ`, `RelCellBlockBoundF κ`,
`RelExteriorBlockBound κ`, and `RelB4s κ`. -/
theorem dampedComplBlockPropagatorE_of (κ : PlanarFrameKernels)
    (hFree : BlockPropagatorInteriorSub.PeriodizedRelFreeBlockInterior)
    (h1 : BlockPropagatorInteriorSub.OrgSplit.RelInteractionDysonJ κ)
    (h2 : BlockPropagatorInteriorSub.OrgSplit.RelBlockDiagonal κ)
    (h3 : BlockPropagatorInteriorSub.OrgSplit3.RelCellBlockBoundF κ)
    (h4 : BlockPropagatorInteriorSub.OrgSplit.RelExteriorBlockBound κ)
    (hB4s : RelRegularityOrg2.RelB4s κ) :
    DampedComplBlockPropagatorE κ := by
  intro hκ P hP m hm K C₀ h B α_free δ_gap hC₀ hh hh_le hB hα hδ hSeed hFreeRel
  have hCp : 0 ≤ 1 + C₀ := by positivity
  have hProj : BlockPropagatorInteriorSub.OrgSplit3.SeedProjBdd κ P m (1 + C₀) :=
    seedProjBdd_of_seedCtx hm hSeed
  have hδ2 : 0 < δ_gap / 2 := half_pos hδ
  obtain ⟨M_free, b_free, hM_free, hb_free, hF_b⟩ :=
    hFree P hP m hm B α_free (δ_gap / 2) hB hα hδ2 hFreeRel
  obtain ⟨K_A, b1, hK_A, hb1_le, hL1⟩ := h1 hκ P hP m hm K B M_free b_free hB hM_free hb_free
  obtain ⟨b2, _hb2, hL2⟩ := h2 hκ P hP m hm K B M_free K_A hB hM_free hK_A
  obtain ⟨b3, _hb3, hL3⟩ := h3 hκ P hP m hm K C₀ h (1 + C₀) B M_free K_A (δ_gap / 2)
    hC₀ hh hh_le hCp hB hM_free hK_A hδ2 hSeed hProj
  obtain ⟨b4, _hb4, hL4⟩ := h4 hκ P hP m hm K C₀ h B M_free K_A (δ_gap / 2)
    hC₀ hh hh_le hB hM_free hK_A hδ2 hSeed
  set b_prop := max (max b1 b2) (max b3 b4)
  have hb_free_le : b_free ≤ b_prop :=
    hb1_le.trans ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨M_free, K_A, b_prop, hM_free, hK_A, hb_free.trans hb_free_le, fun b hbb => ?_⟩
  have hb_ge1 : 1 ≤ b := (hb_free.trans hb_free_le).trans hbb
  have hb_free' : b_free ≤ b := hb_free_le.trans hbb
  have hb1' : b1 ≤ b := ((le_max_left _ _).trans (le_max_left _ _)).trans hbb
  have hb2' : b2 ≤ b := ((le_max_right _ _).trans (le_max_left _ _)).trans hbb
  have hb3' : b3 ≤ b := ((le_max_left _ _).trans (le_max_right _ _)).trans hbb
  have hb4' : b4 ≤ b := ((le_max_right _ _).trans (le_max_right _ _)).trans hbb
  obtain ⟨ν_free, hν_free, hF_ν⟩ := hF_b b hb_free'
  obtain ⟨ν1, hν1, hU1⟩ := hL1 b hb1'
  obtain ⟨ν2, hν2, hU2⟩ := hL2 b hb2'
  obtain ⟨ν3, hν3, hU3⟩ := hL3 b hb3'
  obtain ⟨ν4, hν4, hU4⟩ := hL4 b hb4'
  set ν_prop := min ν_free (min (min ν1 ν2) (min ν3 ν4))
  have hν_prop : 0 < ν_prop :=
    lt_min hν_free (lt_min (lt_min hν1 hν2) (lt_min hν3 hν4))
  refine ⟨ν_prop, hν_prop, fun ν hν hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq => ?_⟩
  have hν_f : ν ∈ Ioc 0 ν_free := ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hν_rest : ν ≤ min (min ν1 ν2) (min ν3 ν4) := hν.2.trans (min_le_right _ _)
  have hν1' : ν ∈ Ioc 0 ν1 := ⟨hν.1, hν_rest.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hν2' : ν ∈ Ioc 0 ν2 := ⟨hν.1, hν_rest.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hν3' : ν ∈ Ioc 0 ν3 := ⟨hν.1, hν_rest.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hν4' : ν ∈ Ioc 0 ν4 := ⟨hν.1, hν_rest.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨F_raw, hF_raw, hF_raw_sub, hF_raw_int⟩ :=
    hF_ν ν hν_f tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
  -- Triangle-clamped free family `F_tri`
  let F_tri : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m :=
    BlockPropagatorESub.clampTriF B F_raw
  have hF_tri : IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_tri := by
    unfold IsPeriodizedRelFreeBlockEvol
    dsimp only
    intro σ τ hσ0 hστ hτB
    have heq : F_tri τ σ = F_raw τ σ :=
      BlockPropagatorESub.clampTriF_eq_of_triangle F_raw hσ0 hστ hτB
    rw [heq]
    exact hF_raw σ τ hσ0 hστ hτB
  have hF_tri_all : ∀ σ τ : ℝ, ‖F_tri τ σ‖ ≤ M_free := by
    intro σ τ
    have hq := BlockPropagatorESub.triClamp_mem_blockTriangle hB.le (τ, σ)
    exact hF_raw_sub _ _ hq.2.1 (by linarith [hq.1, hq.2.2])
  have hF_tri_sub : ∀ σ τ : ℝ, σ ≤ τ → τ ≤ σ + B → ‖F_tri τ σ‖ ≤ M_free :=
    fun σ τ _ _ => hF_tri_all σ τ
  have hF_tri_int : ∀ W : Planar.L2w m,
      BlockPropagatorInteriorSub.IsCellSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) W →
      ‖F_tri B 0 W‖ ≤ (α_free + δ_gap / 2) * ‖W‖ := by
    intro W hW
    rw [show F_tri B 0 = F_raw B 0 from
      BlockPropagatorESub.clampTriF_eq_of_triangle F_raw le_rfl hB.le le_rfl]
    exact hF_raw_int W hW
  -- Joint continuity & strong measurability of `F_tri` on `ℝ × ℝ` via `RelB4s`
  have hctx : RelRegularityOrg.RelCtx κ P m K B b ν tr t₁ t₂ :=
    ⟨hκ, hP, hm, hB, hb_ge1, hν.1, hF, htr, ht₁, h12, hbt₂, hB_eq⟩
  have hM_tri : ∃ M : ℝ, ∀ p ∈ VariationOfConstantsMildSub.blockTriangle B,
      ‖F_raw p.1 p.2‖ ≤ M :=
    ⟨M_free, fun p hp => hF_raw_sub p.2 p.1 hp.2.1 (by linarith [hp.1, hp.2.2])⟩
  have hcont_on : ∀ W : Planar.L2w m,
      ContinuousOn (fun p => F_raw p.1 p.2 W) (VariationOfConstantsMildSub.blockTriangle B) :=
    hB4s P m K B b ν tr t₁ t₂ hctx F_raw hF_raw hM_tri
  have hcont_F : ∀ W : Planar.L2w m, Continuous (fun p : ℝ × ℝ => F_tri p.1 p.2 W) := by
    intro W
    exact (hcont_on W).comp_continuous (BlockPropagatorESub.continuous_triClamp B)
      (BlockPropagatorESub.triClamp_mem_blockTriangle hB.le)
  have : SFinite (UnforcedLeray.Planar.wMeasure m) := by
    unfold UnforcedLeray.Planar.wMeasure
    infer_instance
  have : MeasureTheory.IsSeparable (UnforcedLeray.Planar.wMeasure m) := inferInstance
  have : SecondCountableTopology (Planar.L2w m) := MeasureTheory.Lp.SecondCountableTopology
  have hF_meas : ∀ (τ : ℝ) (x : Planar.L2w m),
      AEStronglyMeasurable (fun σ => F_tri τ σ x) (volume.restrict (Icc 0 B)) := by
    intro τ x
    exact ((hcont_F x).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hclampF_eq : BlockPropagatorInteriorSub.OrgSplit.clampF B F_tri = F_tri :=
    BlockPropagatorESub.clampF_clampTriF_eq hB.le F_raw
  have hFj : DysonJointMeas.FJointMeas
      (BlockPropagatorInteriorSub.OrgSplit.clampF B F_tri) := by
    rw [hclampF_eq]
    intro x
    exact (hcont_F x).stronglyMeasurable
  -- Apply `RelInteractionDysonJ` and build the Dyson sum `U`
  obtain ⟨A_raw, hA_raw, hA_bd, hD⟩ :=
    hU1 ν hν1' hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq F_tri hF_tri hF_tri_sub hF_meas hFj
  have hFb : ∀ (p : Unit) (t s : ℝ), s ≤ t → t ≤ s + B →
      ‖(fun (_ : Unit) => BlockPropagatorInteriorSub.OrgSplit.clampF B F_tri) p t s‖ ≤ M_free := by
    intro _ t s _ _
    rw [hclampF_eq]
    exact hF_tri_all s t
  have hAb : ∀ (p : Unit) (r : ℝ),
      ‖(fun (_ : Unit) => BlockPropagatorInteriorSub.OrgSplit.clampA B A_raw) p r‖ ≤ K_A :=
    fun _ _ => hA_bd _
  obtain ⟨U, hU⟩ := UnforcedLeray.B0104.exists_isDysonSum (H := Planar.L2w m) hFb hAb hD
  have hDuh := hU.isDuhamelEvolution hFb hAb hD
  -- Block diagonality + cell & exterior bounds for `U () B 0`
  set α' : ℝ := α_free + δ_gap / 2
  have hα'_nonneg : 0 ≤ α' := by positivity
  have htriple : BlockPropagatorInteriorSub.OrgSplit.BlockTriple
      κ P ν m tr t₁ B M_free K_A α' F_tri A_raw (fun t s => U () t s) :=
    ⟨hF_tri, hF_tri_sub, hA_raw, hA_bd, hDuh, hF_tri_int⟩
  obtain ⟨hcell, hext⟩ := hU2 ν hν2' hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq α' F_tri A_raw _ htriple
  have hce := hU3 ν hν3' hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq α' hα'_nonneg F_tri A_raw _ htriple
  have hex := hU4 ν hν4' hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq α' hα'_nonneg F_tri A_raw _ htriple
  have hU_norm : ‖U () B 0‖ ≤
      C₀ * Real.exp (-h * B) + (1 + C₀) * Real.exp (-B) + α_free +
        Real.exp (-P.eigenvalue.re * B) + δ_gap := by
    have hexp1 : 0 ≤ Real.exp (-P.eigenvalue.re * B) := (Real.exp_pos _).le
    have hc0 : 0 ≤ C₀ * Real.exp (-h * B) := by positivity
    have hc1 : 0 ≤ (1 + C₀) * Real.exp (-B) := by positivity
    have hblk := BlockPropagatorInteriorSub.OrgSplit.norm_le_of_blocks2
      (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁))
      (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) (U () B 0)
      (c := C₀ * Real.exp (-h * B) + (1 + C₀) * Real.exp (-B) + α' +
        Real.exp (-P.eigenvalue.re * B) + δ_gap / 2)
      (by positivity)
      (fun W hW => ⟨hcell W hW, hce W hW⟩)
      (fun W hW => ⟨hext W hW, (hex W hW).trans
        (mul_le_mul_of_nonneg_right (by linarith [hc1, hexp1, hα'_nonneg]) (norm_nonneg _))⟩)
    refine hblk.trans (le_of_eq ?_)
    dsimp [α']
    ring
  -- Unclamp `(clampF B F_tri, clampA B A_raw)` into `(F_tri, A_tri)`
  let A_tri : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m :=
    BlockPropagatorInteriorSub.OrgSplit.clampA B A_raw
  have hA_tri : IsDampedComplBlockInt κ P ν m tr t₁ B A_tri := by
    unfold IsDampedComplBlockInt
    dsimp only
    intro τ hτ
    have hA_eq : A_tri τ = A_raw τ :=
      congrArg A_raw (BlockPropagatorInteriorSub.OrgSplit.clampB_eq_self_of_mem B τ hτ)
    rw [hA_eq]
    exact hA_raw τ hτ
  have hA_tri_bd : ∀ τ : ℝ, ‖A_tri τ‖ ≤ K_A := fun τ => hA_bd _
  have hDuh_unclamped : UnforcedLeray.B0104.IsDuhamelEvolution (ι := Unit) B
      (fun _ => F_tri) (fun _ => A_tri) (fun _ => fun t s => U () t s) := by
    simpa only [hclampF_eq] using hDuh
  exact ⟨F_tri, A_tri, fun t s => U () t s, hF_tri, hA_tri, hDuh_unclamped,
    hF_tri_sub, hA_tri_bd, hU_norm⟩

/-- **Unconditional proof of `DampedComplBlockPropagatorE κ`** (`PartIII-a:T21/c3/2/1/1`),
combining `periodizedRelFreeBlockInterior`, `OrgSplit.relInteractionDysonJ`,
`relBlockDiagonal`, `OrgSplit3.relCellBlockBoundF`, `relExteriorBlockBound`, and
`_root_.relB4s_leaf`. -/
theorem dampedComplBlockPropagatorE_proved (κ : PlanarFrameKernels) :
    DampedComplBlockPropagatorE κ :=
  dampedComplBlockPropagatorE_of κ
    periodizedRelFreeBlockInterior
    (BlockPropagatorInteriorSub.OrgSplit.relInteractionDysonJ κ)
    (relBlockDiagonal κ)
    (BlockPropagatorInteriorSub.OrgSplit3.relCellBlockBoundF κ)
    (relExteriorBlockBound κ)
    (_root_.relB4s_leaf κ)

/-! ## 4. `BlockCompactDuhamelGapE` and assemblies (`PartIII-a:T21/c3/2/1`) -/

/-- **E-version of `BlockCompactDuhamelGap`** (`PartIII-a:T21/c3/2/1`, SP 2919-2928, 2962-2982):
identical hypotheses to `BlockCompactDuhamelGap`, with homogeneous factor
`C₀ * Real.exp (-h * B) + (1 + C₀) * Real.exp (-B) + α_free + Real.exp (-P.eigenvalue.re * B) + δ_gap`. -/
def BlockCompactDuhamelGapE (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K : ℝ,
  ∀ C₀ h B α_free δ_gap : ℝ,
    0 < C₀ → 0 < h → h ≤ P.eigenvalue.re → 0 < B → 0 < α_free → 0 < δ_gap →
    BlockPropagatorInteriorSub.OrgSplit.SeedCtx κ P m C₀ h →
    (∃ b_f : ℝ, 1 ≤ b_f ∧ ∀ b : ℝ, b_f ≤ b → ∃ ν_f : ℝ, 0 < ν_f ∧
      ∀ ν ∈ Ioc 0 ν_f, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
          movingZ ν t₂ - movingZ ν t₁ = B →
          ∀ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
            ∀ ω₀ : ℝ → B0579.Plane → ℝ, UnforcedLeray.Short.IIb.IsFreeCylFlow m tr t₁ f ω₀ →
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m
                  (JscaleInv (clockA ν t₂) (fun x => ((ω₀ t₂ x : ℝ) : ℂ))) ≤
                ENNReal.ofReal (clockN P ν t₁ t₂) *
                  (ENNReal.ofReal α_free *
                    xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m
                      (JscaleInv (clockA ν t₁) (fun x => ((f x : ℝ) : ℂ))))) →
    ∃ C_uh b_gap : ℝ, 0 ≤ C_uh ∧ 1 ≤ b_gap ∧
      ∀ b : ℝ, b_gap ≤ b →
        ∃ ν_gap : ℝ, 0 < ν_gap ∧
          ∀ ν (hν : ν ∈ Ioc 0 ν_gap), ∀ hF : PerFrameFacts κ ν m b K,
            ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
              UnforcedLeray.Short.PartI.IsBUCTrain tr →
              ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
                movingZ ν t₂ - movingZ ν t₁ = B →
                ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
                  HasZeroCirculation (ν ^ (-2 : ℝ)) f →
                  let F := periodizedFrame κ ν m b K hν.1 hF
                  xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m (compl F w t₂) ≤
                    ENNReal.ofReal (clockN P ν t₁ t₂) *
                        (ENNReal.ofReal
                          (C₀ * Real.exp (-h * B) + (1 + C₀) * Real.exp (-B) + α_free +
                            Real.exp (-P.eigenvalue.re * B) + δ_gap) *
                          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁)) +
                      ∫⁻ r in Ioc t₁ t₂,
                        ENNReal.ofReal
                            ((clockA ν r) ^ (-2 : ℝ) * (clockN P ν r t₂ * C_uh)) *
                          (∑ j : Fin 2,
                            ENNReal.ofReal ‖ampl F w r j‖ *
                              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                                (complModeForce κ P F tr r j))

/-- Regime assembly of `BlockCompactDuhamelGapE κ` from `DampedComplBlockPropagatorE κ` and
`VariationOfConstantsMildSub.ComplBlockDuhamelVoCReg κ` (SP 2962-2982). -/
theorem blockCompactDuhamelGapRegE_of (κ : PlanarFrameKernels)
    (hProp : DampedComplBlockPropagatorE κ)
    (hVoC : VariationOfConstantsMildSub.ComplBlockDuhamelVoCReg κ) :
    BlockCompactDuhamelGapE κ := by
  intro hκ P hP m hm K C₀ h B α_free δ_gap hC₀ hh hh_le hB hα hδ hSeedDecay hFreeRel
  obtain ⟨M_free, K_A, b_prop, hM_free, hK_A, hb_prop, hU_b⟩ :=
    hProp hκ P hP m hm K C₀ h B α_free δ_gap hC₀ hh hh_le hB hα hδ hSeedDecay hFreeRel
  set C_uh : ℝ := 2 * M_free * Real.exp ((2 * (M_free * K_A) + 1) * B)
  have hC_uh : 0 ≤ C_uh := by positivity
  obtain ⟨b₀, hb₀⟩ := hVoC hκ P hP m hm K B hB
  refine ⟨C_uh, max b_prop b₀, hC_uh, hb_prop.trans (le_max_left _ _), fun b hb => ?_⟩
  have hbp : b_prop ≤ b := (le_max_left _ _).trans hb
  obtain ⟨ν_prop, hν_prop, hU_ν⟩ := hU_b b hbp
  have hb1 : 1 ≤ b := hb_prop.trans hbp
  obtain ⟨ν₀, hν₀, hVν⟩ := hb₀ b ((le_max_right _ _).trans hb) hb1
  refine ⟨min ν_prop ν₀, lt_min hν_prop hν₀,
    fun ν hν hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq f w u hFlow hCirc => ?_⟩
  dsimp only
  set F := periodizedFrame κ ν m b K hν.1 hF
  obtain ⟨F_rel, A_rel, U_rel, hF_rel, hA_rel, hDuh, hF_bdd, hA_bdd, hU_B0⟩ :=
    hU_ν ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩ hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
  have hvoc := hVν ν hν.1 (hν.2.trans (min_le_right _ _)) hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
    F_rel A_rel U_rel hF_rel hA_rel hDuh f w u hFlow hCirc
  have hU_sub : ∀ σ : ℝ, 0 ≤ σ → σ ≤ B → ‖U_rel B σ‖ ≤ C_uh := by
    intro σ hσ0 hσB
    exact hDuh.norm_le (fun _ t s h1 h2 => hF_bdd s t h1 h2) (fun _ r => hA_bdd r)
      () B σ hσB (by linarith)
  have hN12_pos : 0 < clockN P ν t₁ t₂ := clockN_pos P hν.1 ht₁ (ht₁.trans h12)
  have hHom :
      ENNReal.ofReal (clockN P ν t₁ t₂ * ‖U_rel B 0‖) *
          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁) ≤
        ENNReal.ofReal (clockN P ν t₁ t₂) *
          (ENNReal.ofReal
            (C₀ * Real.exp (-h * B) + (1 + C₀) * Real.exp (-B) + α_free +
              Real.exp (-P.eigenvalue.re * B) + δ_gap) *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁)) := by
    rw [ENNReal.ofReal_mul hN12_pos.le, mul_assoc]
    refine mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hU_B0) zero_le) zero_le
  have hInt :
      (∫⁻ r in Ioc t₁ t₂,
        ENNReal.ofReal
            ((clockA ν r) ^ (-2 : ℝ) *
              (clockN P ν r t₂ * ‖U_rel B (movingZ ν r - movingZ ν t₁)‖)) *
          (∑ j : Fin 2,
            ENNReal.ofReal ‖ampl F w r j‖ *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                (complModeForce κ P F tr r j))) ≤
      ∫⁻ r in Ioc t₁ t₂,
        ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) * (clockN P ν r t₂ * C_uh)) *
          (∑ j : Fin 2,
            ENNReal.ofReal ‖ampl F w r j‖ *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                (complModeForce κ P F tr r j)) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 ≤ r := ht₁.trans hr.1.le
    have ha_pos : 0 < (clockA ν r) ^ (-2 : ℝ) := by
      have ha : 0 < clockA ν r := by
        have := one_le_clockA hν.1.le hr0
        linarith
      exact Real.rpow_pos_of_pos ha _
    have hN_pos : 0 < clockN P ν r t₂ := clockN_pos P hν.1 hr0 (ht₁.trans h12)
    have hz_mem := movingZ_sub_mem_Icc hν.1 ht₁ ⟨hr.1.le, hr.2⟩
    rw [hB_eq] at hz_mem
    have hU_r : ‖U_rel B (movingZ ν r - movingZ ν t₁)‖ ≤ C_uh :=
      hU_sub (movingZ ν r - movingZ ν t₁) hz_mem.1 hz_mem.2
    have hfactor :
        (clockA ν r) ^ (-2 : ℝ) * (clockN P ν r t₂ * ‖U_rel B (movingZ ν r - movingZ ν t₁)‖) ≤
          (clockA ν r) ^ (-2 : ℝ) * (clockN P ν r t₂ * C_uh) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU_r hN_pos.le) ha_pos.le
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hfactor) zero_le
  exact hvoc.trans (add_le_add hHom hInt)

/-- Non-regime wrapper `blockCompactDuhamelGapE_of` from `ComplBlockDuhamelVoC κ`. -/
theorem blockCompactDuhamelGapE_of (κ : PlanarFrameKernels)
    (hProp : DampedComplBlockPropagatorE κ)
    (hVoC : ComplBlockDuhamelVoC κ) :
    BlockCompactDuhamelGapE κ :=
  blockCompactDuhamelGapRegE_of κ hProp
    (fun hκ P hP m hm K B hB =>
      ⟨1, fun b _ hb1 => ⟨1, zero_lt_one, fun ν hν _ => hVoC hκ P hP m hm K B b hB hb1 ν hν⟩⟩)

/-! ## 5. Selection of `B > 0` and assembly of unchanged `FrameBlockContraction κ` (`PartIII-a:T21/c3/2`) -/

/-- Selection of moving block length `B > 0` so that the planar seed-complement decay
`C₀ * e^{-h B}`, the artificial seed-projection decay `Cproj * e^{-B}`, and the `3 * e^{-γ B}`
relative free moving terms sum to at most `1 / 4` (SP 2980-2981). -/
theorem exists_block_length_contractionE {C₀ Cproj h γ : ℝ}
    (hC₀ : 0 < C₀) (hCp : 0 ≤ Cproj) (hh : 0 < h) (hγ : 0 < γ) :
    ∃ B : ℝ, 0 < B ∧
      C₀ * Real.exp (-h * B) + Cproj * Real.exp (-B) + 3 * Real.exp (-γ * B) ≤ 1 / 4 := by
  have hCp1 : 0 < Cproj + 1 := by linarith
  set B := max 1 (max (Real.log (12 * C₀) / h)
    (max (Real.log (12 * (Cproj + 1))) (Real.log 36 / γ)))
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hB_h : Real.log (12 * C₀) / h ≤ B :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hB_p : Real.log (12 * (Cproj + 1)) ≤ B :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hB_γ : Real.log 36 / γ ≤ B :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have h1 : C₀ * Real.exp (-h * B) ≤ 1 / 12 := by
    have hlog : Real.log (12 * C₀) ≤ h * B := by
      have := (div_le_iff₀ hh).1 hB_h
      linarith
    have hneg : -h * B ≤ Real.log ((12 * C₀)⁻¹) := by
      rw [Real.log_inv]
      linarith
    have hexp : Real.exp (-h * B) ≤ (12 * C₀)⁻¹ := by
      calc Real.exp (-h * B) ≤ Real.exp (Real.log ((12 * C₀)⁻¹)) := Real.exp_le_exp.2 hneg
        _ = (12 * C₀)⁻¹ := Real.exp_log (by positivity)
    calc C₀ * Real.exp (-h * B) ≤ C₀ * (12 * C₀)⁻¹ :=
          mul_le_mul_of_nonneg_left hexp hC₀.le
      _ = 1 / 12 := by field_simp [hC₀.ne']
  have h2 : Cproj * Real.exp (-B) ≤ 1 / 12 := by
    have hneg : -B ≤ Real.log ((12 * (Cproj + 1))⁻¹) := by
      rw [Real.log_inv]
      linarith
    have hexp : Real.exp (-B) ≤ (12 * (Cproj + 1))⁻¹ := by
      calc Real.exp (-B) ≤ Real.exp (Real.log ((12 * (Cproj + 1))⁻¹)) := Real.exp_le_exp.2 hneg
        _ = (12 * (Cproj + 1))⁻¹ := Real.exp_log (by positivity)
    calc Cproj * Real.exp (-B)
        ≤ (Cproj + 1) * Real.exp (-B) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ ≤ (Cproj + 1) * (12 * (Cproj + 1))⁻¹ :=
          mul_le_mul_of_nonneg_left hexp hCp1.le
      _ = 1 / 12 := by field_simp [hCp1.ne']
  have h3 : 3 * Real.exp (-γ * B) ≤ 1 / 12 := by
    have hlog : Real.log 36 ≤ γ * B := by
      have := (div_le_iff₀ hγ).1 hB_γ
      linarith
    have hneg : -γ * B ≤ Real.log ((36 : ℝ)⁻¹) := by
      rw [Real.log_inv]
      linarith
    have hexp : Real.exp (-γ * B) ≤ (36 : ℝ)⁻¹ := by
      calc Real.exp (-γ * B) ≤ Real.exp (Real.log ((36 : ℝ)⁻¹)) := Real.exp_le_exp.2 hneg
        _ = (36 : ℝ)⁻¹ := Real.exp_log (by norm_num)
    linarith
  exact ⟨B, hB_pos, by linarith⟩

/-- Assembly of the **unchanged** `FrameBlockContraction κ` (`PartIII-a:T21/c3/2`, SP 2898-2982)
from `BlockCompactDuhamelGapE` (`PartIII-a:T21/c3/2/1`), `ComplModeForceOscillator`
(`PartIII-a:T21/c3/3/2`), and `ComplModeForceEulerError` (`PartIII-a:T21/c3/3/3`). -/
theorem frameBlockContraction_ofE (κ : PlanarFrameKernels)
    (hGap : BlockCompactDuhamelGapE κ)
    (hOsc : ComplModeForceOscillator κ)
    (hEul : ComplModeForceEulerError κ) :
    FrameBlockContraction κ := by
  intro hκ P hP m hm K
  -- 1. Planar seed-complement decay and block length B > 0
  obtain ⟨C₀, h, hC₀, hh, hh_le, hSeedDecay⟩ := planarDampedComplDecay hκ P hP hm
  have hCp : 0 ≤ 1 + C₀ := by positivity
  have hγ : 0 < P.eigenvalue.re := lt_of_lt_of_le hh hh_le
  obtain ⟨B, hB_pos, hB_contr⟩ := exists_block_length_contractionE hC₀ hCp hh hγ
  -- 2. Relative free moving bound <= 2 * exp(-γ * B) on blocks of length B
  set K_num := normGrowthConst m + |P.kappa.re|
  have hCm_pos : 0 < normGrowthConst m := by unfold normGrowthConst; positivity
  have hK_num_nonneg : 0 ≤ K_num := by
    have := abs_nonneg P.kappa.re
    positivity
  obtain ⟨ε, b_thr, hε_pos, hb_thr1, hb_thr_exp⟩ :=
    exists_b_free_rel_bound P.eigenvalue.re hB_pos hK_num_nonneg
  obtain ⟨b_f0, _hb_f0, hRelFree⟩ := relFreeMovingEnergy P hm hε_pos
  set α_free := 2 * Real.exp (-P.eigenvalue.re * B)
  have hα_free_pos : 0 < α_free := by positivity
  have hFreeHyp :
      ∃ b_f : ℝ, 1 ≤ b_f ∧ ∀ b : ℝ, b_f ≤ b → ∃ ν_f : ℝ, 0 < ν_f ∧
        ∀ ν ∈ Ioc 0 ν_f, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
            movingZ ν t₂ - movingZ ν t₁ = B →
            ∀ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
              ∀ ω₀ : ℝ → B0579.Plane → ℝ, UnforcedLeray.Short.IIb.IsFreeCylFlow m tr t₁ f ω₀ →
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m
                    (JscaleInv (clockA ν t₂) (fun x => ((ω₀ t₂ x : ℝ) : ℂ))) ≤
                  ENNReal.ofReal (clockN P ν t₁ t₂) *
                    (ENNReal.ofReal α_free *
                      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m
                        (JscaleInv (clockA ν t₁) (fun x => ((f x : ℝ) : ℂ)))) := by
    refine ⟨max b_thr b_f0, hb_thr1.trans (le_max_left _ _), fun b hb => ?_⟩
    have hb_t : b_thr ≤ b := (le_max_left _ _).trans hb
    have hb_0 : b_f0 ≤ b := (le_max_right _ _).trans hb
    obtain ⟨ν_f, hν_f, Hrel⟩ := hRelFree b hb_0
    refine ⟨ν_f, hν_f, fun ν hν tr htr t₁ t₂ ht₁ h12 hbs hZ f hf ω₀ hω₀ => ?_⟩
    have h1 := Hrel ν hν tr htr t₁ t₂ ht₁ h12 hbs f hf ω₀ hω₀
    rw [hZ] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ zero_le)
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
    exact hb_thr_exp b hb_t
  -- 3. Apply BlockCompactDuhamelGapE with δ_gap = 1 / 4 and mode-forcing leaves
  obtain ⟨C_uh, b_gap, hC_uh, hb_gap, hGapB⟩ :=
    hGap hκ P hP m hm K C₀ h B α_free (1 / 4) hC₀ hh hh_le hB_pos hα_free_pos
      (by norm_num) hSeedDecay hFreeHyp
  obtain ⟨C₁, b_osc, hC₁, _hb_osc, hOscB⟩ := hOsc hκ m hm
  obtain ⟨C₂, b_eul, hC₂, _hb_eul, hEulB⟩ := hEul hκ P hP m hm
  set C_force := (1 + 2 * max K 0 ^ 2) * max C₁ C₂
  have hC_force_nonneg : 0 ≤ C_force := by
    have : 0 ≤ max C₁ C₂ := le_trans hC₁ (le_max_left C₁ C₂)
    positivity
  set C_B := B * C_uh * C_force
  have hC_B_nonneg : 0 ≤ C_B := by positivity
  set b₁ := max b_gap (max b_osc b_eul)
  have hb₁_ge : 1 ≤ b₁ := hb_gap.trans (le_max_left _ _)
  refine ⟨B, C_B, b₁, hB_pos, hC_B_nonneg, hb₁_ge, fun b hb => ?_⟩
  have hb_gap' : b_gap ≤ b := (le_max_left _ _).trans hb
  have hb_osc' : b_osc ≤ b :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hb
  have hb_eul' : b_eul ≤ b :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hb
  obtain ⟨ν_gap, hν_gap, HGap⟩ := hGapB b hb_gap'
  obtain ⟨ν_osc, hν_osc, HOsc⟩ := hOscB b hb_osc'
  obtain ⟨ν_eul, hν_eul, HEul⟩ := hEulB b hb_eul'
  refine ⟨min ν_gap (min ν_osc ν_eul), lt_min hν_gap (lt_min hν_osc hν_eul),
    fun ν hν hF tr htr t₁ t₂ ht₁ h12 hbs hZ f w u hw hz => ?_⟩
  have hνpos : 0 < ν := hν.1
  have hν_g : ν ∈ Ioc 0 ν_gap := ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hν_o : ν ∈ Ioc 0 ν_osc :=
    ⟨hν.1, hν.2.trans (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  have hν_e : ν ∈ Ioc 0 ν_eul :=
    ⟨hν.1, hν.2.trans (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  set F := periodizedFrame κ ν m b K hν.1 hF
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  have hθt₂_pos : 0 < clockTheta ν t₂ := theta_pos hνpos ht₂
  -- 4. Single-block Duhamel inequality
  have hDuh := HGap ν hν_g hF tr htr t₁ t₂ ht₁ h12 hbs hZ f w u hw hz
  -- 5. Homogeneous factor C₀ * e^{-h B} + (1 + C₀) * e^{-B} + α_free + e^{-γ B} + 1/4 ≤ 1/2
  have hHom_half :
      C₀ * Real.exp (-h * B) + (1 + C₀) * Real.exp (-B) + α_free +
        Real.exp (-P.eigenvalue.re * B) + 1 / 4 ≤ 1 / 2 := by
    simp only [α_free]
    linarith [hB_contr]
  have hHom :
      ENNReal.ofReal (clockN P ν t₁ t₂) *
          (ENNReal.ofReal
            (C₀ * Real.exp (-h * B) + (1 + C₀) * Real.exp (-B) + α_free +
              Real.exp (-P.eigenvalue.re * B) + 1 / 4) *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁)) ≤
        ENNReal.ofReal (clockN P ν t₁ t₂) *
          (ENNReal.ofReal (1 / 2) *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁)) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hHom_half) zero_le) zero_le
  -- 6. Forcing integral bound on Ioc t₁ t₂
  set S : ℝ≥0∞ := ⨆ r ∈ Icc t₁ t₂, amplNorm F w r / ENNReal.ofReal (clockN P ν t₁ r)
  set η_t₂ : ℝ := C_force * (1 + ν ^ 3) / clockTheta ν t₂
  have hInt_pt : ∀ r ∈ Ioc t₁ t₂,
      ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) * (clockN P ν r t₂ * C_uh)) *
        (∑ j : Fin 2,
          ENNReal.ofReal ‖ampl F w r j‖ *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j)) ≤
      ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
        (ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal (C_uh * η_t₂) * S)) := by
    intro r hr
    have hr0 : 0 ≤ r := ht₁.trans hr.1.le
    have ha_pos : 0 < clockA ν r := by
      have := one_le_clockA hνpos.le hr0
      linarith
    have ha2_nonneg : 0 ≤ (clockA ν r) ^ (-2 : ℝ) := (Real.rpow_pos_of_pos ha_pos _).le
    have hθr_ge_t₂ : clockTheta ν t₂ ≤ clockTheta ν r := theta_anti hνpos hr0 hr.2
    have hbr : b ≤ clockTheta ν r := hbs.trans hθr_ge_t₂
    have hforce_r : ∀ j : Fin 2,
        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j) ≤
          ENNReal.ofReal η_t₂ := by
      intro j
      obtain ⟨hOm, hOb⟩ := HOsc ν hν_o r hr0 hbr j
      obtain ⟨hEm, hEb⟩ := HEul ν hν_e tr htr r hr0 hbr j
      refine (xNorm_complModeForce_le κ P F tr j hνpos hr0 hbr hC₁ hC₂ hOm hOb hEm hEb).trans ?_
      refine ENNReal.ofReal_le_ofReal ?_
      exact div_le_div_of_nonneg_left (by positivity) hθt₂_pos hθr_ge_t₂
    have hsum_r := sum_ampl_complModeForce_le κ P F tr w hforce_r
    have hN_r : 0 < clockN P ν t₁ r := clockN_pos P hνpos ht₁ hr0
    have hN_rt₂ : 0 < clockN P ν r t₂ := clockN_pos P hνpos hr0 ht₂
    have hN_ne0 : ENNReal.ofReal (clockN P ν t₁ r) ≠ 0 :=
      (ENNReal.ofReal_pos.2 hN_r).ne'
    have hN_netop : ENNReal.ofReal (clockN P ν t₁ r) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hampl_split :
        ENNReal.ofReal (clockN P ν r t₂) * amplNorm F w r ≤
          ENNReal.ofReal (clockN P ν t₁ t₂) * S := by
      have hdiv : amplNorm F w r =
          ENNReal.ofReal (clockN P ν t₁ r) *
            (amplNorm F w r / ENNReal.ofReal (clockN P ν t₁ r)) :=
        (ENNReal.mul_div_cancel hN_ne0 hN_netop).symm
      have hsup : amplNorm F w r / ENNReal.ofReal (clockN P ν t₁ r) ≤ S :=
        le_biSup (fun u => amplNorm F w u / ENNReal.ofReal (clockN P ν t₁ u)) ⟨hr.1.le, hr.2⟩
      rw [hdiv, ← mul_assoc, mul_comm (ENNReal.ofReal (clockN P ν r t₂)),
        ← FrameStableSub.ofReal_clockN_mul P hνpos ht₁ hr0 ht₂]
      exact mul_le_mul_of_nonneg_left hsup zero_le
    rw [ENNReal.ofReal_mul ha2_nonneg, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    calc ENNReal.ofReal (clockN P ν r t₂ * C_uh) *
          (∑ j : Fin 2,
            ENNReal.ofReal ‖ampl F w r j‖ *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j))
        ≤ (ENNReal.ofReal (clockN P ν r t₂) * ENNReal.ofReal C_uh) *
            (ENNReal.ofReal η_t₂ * amplNorm F w r) := by
          rw [ENNReal.ofReal_mul hN_rt₂.le]
          exact mul_le_mul_of_nonneg_left hsum_r zero_le
      _ = (ENNReal.ofReal C_uh * ENNReal.ofReal η_t₂) *
            (ENNReal.ofReal (clockN P ν r t₂) * amplNorm F w r) := by
          ring
      _ ≤ (ENNReal.ofReal C_uh * ENNReal.ofReal η_t₂) *
            (ENNReal.ofReal (clockN P ν t₁ t₂) * S) :=
          mul_le_mul_of_nonneg_left hampl_split zero_le
      _ = ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal (C_uh * η_t₂) * S) := by
          rw [← ENNReal.ofReal_mul hC_uh]
          ring
  have hInt :
      (∫⁻ r in Ioc t₁ t₂,
        ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) * (clockN P ν r t₂ * C_uh)) *
          (∑ j : Fin 2,
            ENNReal.ofReal ‖ampl F w r j‖ *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j))) ≤
        ENNReal.ofReal (clockN P ν t₁ t₂) *
          (ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν t₂) * S) := by
    calc (∫⁻ r in Ioc t₁ t₂,
          ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) * (clockN P ν r t₂ * C_uh)) *
            (∑ j : Fin 2,
              ENNReal.ofReal ‖ampl F w r j‖ *
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (complModeForce κ P F tr r j)))
        ≤ ∫⁻ r in Ioc t₁ t₂,
            ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
              (ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal (C_uh * η_t₂) * S)) :=
          setLIntegral_mono' measurableSet_Ioc hInt_pt
      _ = (∫⁻ r in Ioc t₁ t₂, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ))) *
            (ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal (C_uh * η_t₂) * S)) := by
          refine lintegral_mul_const _ ?_
          unfold clockA
          exact ENNReal.measurable_ofReal.comp
            ((measurable_const.add (measurable_const.mul measurable_id)).pow_const (-2 : ℝ))
      _ = ENNReal.ofReal B *
            (ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal (C_uh * η_t₂) * S)) := by
          rw [lintegral_clockA_inv_sq_eq hνpos ht₁ h12, hZ]
      _ = ENNReal.ofReal (clockN P ν t₁ t₂) *
            ((ENNReal.ofReal B * ENNReal.ofReal (C_uh * η_t₂)) * S) := by
          ring
      _ = ENNReal.ofReal (clockN P ν t₁ t₂) *
            (ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν t₂) * S) := by
          rw [← ENNReal.ofReal_mul hB_pos.le]
          congr 3
          simp only [C_B, η_t₂]
          ring
  calc xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m (compl F w t₂)
      ≤ ENNReal.ofReal (clockN P ν t₁ t₂) *
            (ENNReal.ofReal (1 / 2) *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁)) +
          ENNReal.ofReal (clockN P ν t₁ t₂) *
            (ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν t₂) * S) :=
        hDuh.trans (add_le_add hHom hInt)
    _ = ENNReal.ofReal (clockN P ν t₁ t₂) *
          (ENNReal.ofReal (1 / 2) *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁) +
            ENNReal.ofReal (C_B * (1 + ν ^ 3) / clockTheta ν t₂) * S) := by
        rw [← mul_add]

end UnforcedLeray.Short.IIIa

end
