import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1

/-!
# Part III-a, `PartIII-a:T21/c3/2/1/1`: interior/exterior split of `DampedComplBlockPropagator`

Source of record: `the November 2 reference manuscript` (SP), lines 2937-2982.

Replacement split for the two leaves of `Sub/PartIII-a_T21_c3_2_1_1.lean`.

`IsPeriodizedRelFreeBlockEvol` with `f = 0`, `ω₀ = 0` forces, for every `W` vanishing on
`B0579.cell d(t₁)`, `F_rel B 0 W = (clockN P ν t₁ t₂)⁻¹ • S(t₂, t₁) W` with the exterior dilation
`S f(y) = ρ⁴ f(ρ y)`, `ρ = d(t₁)/d(t₂)` (SP 2941-2944).  Its norm is not controlled by `α_free`
(an upper bound for the interior free flow only): the clause `‖F_rel B 0‖ ≤ α_free + δ_free` of
`BlockPropagatorSub.PeriodizedRelFreeBlockExists` needs a lower bound of `α_free` by the seam
weight ratio, i.e. nearly static free flows near the cell seam, which uses train velocity bounds
that `PartI.IsBUCTrain` does not give uniformly in `ν`.  The split below asks only for the
interior full-block bound; the exterior block is handled inside the compact Duhamel leaf, where
`U_rel` is block diagonal (`A_rel` kills and lands in the cell, `F_rel` maps cell to cell and
exterior to exterior) and the exterior norm is at most `(clockN)⁻¹ e^{3B/(2b)}`
(`norm_extDilW_cellLen_le_exp`), which is `≤ C₀ e^{-h B} + δ` for `b` large because `h ≤ Re λ` and
`C₀ ≥ 1` (seed hypothesis at `t = 0`).

* `PeriodizedRelFreeBlockInterior` (leaf a, SP 2937-2962): construction of `F_rel` from the
  actual free cylinder flow (`IIb.free_cyl_exists_approx`, `IIb.free_cyl_unique`,
  `IIb.IsFreeCylFlow.add/smul`, `IIb.free_cyl_test_approx`), the exterior dilation `extDilW`,
  the sub-block bound (`FrameBlockContractSub.relFreeMovingEnergy`,
  `norm_extDilW_cellLen_le_exp`) and the interior full-block bound (hypothesis, density).
* `DampedComplBlockIntDuhamelInterior` (leaf b, SP 2920-2925, 2962-2982): bounded extension
  `A_rel` of `movDampedComplInt`, Dyson evolution `U_rel`, and the compact Duhamel bound
  `‖U_rel B 0‖ ≤ C₀ e^{-hB} + α' + δ_gap` where `α'` bounds `F_rel B 0` on cell-supported data.
* `dampedComplBlockPropagator_of_interior`: assembly (proved).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub

namespace BlockPropagatorInteriorSub

/-- `W : Planar.L2w m` vanishes a.e. outside `B0579.cell d`. -/
def IsCellSupportedW {m : ℝ} (d : ℝ) (W : Planar.L2w m) : Prop :=
  ∀ᵐ z ∂(volume : Measure ℂ), cToPlane z ∉ B0579.cell d → (W : ℂ → ℂ) z = 0

/-- **Leaf a (`PeriodizedRelFreeBlockInterior`, SP 2937-2962)**: as
`BlockPropagatorSub.PeriodizedRelFreeBlockExists`, with the full-block clause restricted to data
supported in the entrance cell `B0579.cell d(t₁)`. -/
def PeriodizedRelFreeBlockInterior : Prop :=
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ B α_free δ_free : ℝ, 0 < B → 0 < α_free → 0 < δ_free →
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
    ∃ M_free b_free : ℝ, 0 ≤ M_free ∧ 1 ≤ b_free ∧
      ∀ b : ℝ, b_free ≤ b →
        ∃ ν_free : ℝ, 0 < ν_free ∧
          ∀ ν ∈ Ioc 0 ν_free, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
            UnforcedLeray.Short.PartI.IsBUCTrain tr →
            ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
              movingZ ν t₂ - movingZ ν t₁ = B →
              ∃ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
                IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel ∧
                (∀ σ τ : ℝ, σ ≤ τ → τ ≤ σ + B → ‖F_rel τ σ‖ ≤ M_free) ∧
                ∀ W : Planar.L2w m, IsCellSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) W →
                  ‖F_rel B 0 W‖ ≤ (α_free + δ_free) * ‖W‖

/-- **Leaf b (`DampedComplBlockIntDuhamelInterior`, SP 2920-2925, 2962-2982)**: as
`BlockPropagatorSub.DampedComplBlockIntAndDuhamel κ`, with `‖F_rel B 0‖` in the full-block bound
replaced by any bound `α'` of `F_rel B 0` on data supported in `B0579.cell d(t₁)`. -/
def DampedComplBlockIntDuhamelInterior (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K : ℝ,
  ∀ C₀ h B M_free b_free δ_gap : ℝ,
    0 < C₀ → 0 < h → h ≤ P.eigenvalue.re → 0 < B → 0 ≤ M_free → 1 ≤ b_free → 0 < δ_gap →
    (∃ (lam : ℂ) (h_prof : ℝ → ℂ) (hh : MemLp h_prof 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
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
          Real.exp (-P.eigenvalue.re * t) * ‖g‖ ≤ C₀ * Real.exp (-h * t) * ‖f‖)) →
    (∀ b : ℝ, b_free ≤ b →
      ∃ ν_free : ℝ, 0 < ν_free ∧
        ∀ ν ∈ Ioc 0 ν_free, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
            movingZ ν t₂ - movingZ ν t₁ = B →
            ∃ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
              IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel ∧
              (∀ σ τ : ℝ, σ ≤ τ → τ ≤ σ + B → ‖F_rel τ σ‖ ≤ M_free)) →
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
                  ∀ α' : ℝ, 0 ≤ α' →
                  (∀ W : Planar.L2w m, IsCellSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) W →
                    ‖F_rel B 0 W‖ ≤ α' * ‖W‖) →
                  ∃ (A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m)
                    (U_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m),
                    IsDampedComplBlockInt κ P ν m tr t₁ B A_rel ∧
                    UnforcedLeray.B0104.IsDuhamelEvolution (ι := Unit) B
                      (fun _ => F_rel) (fun _ => A_rel) (fun _ => U_rel) ∧
                    (∀ τ : ℝ, ‖A_rel τ‖ ≤ K_A) ∧
                    ‖U_rel B 0‖ ≤ C₀ * Real.exp (-h * B) + α' + δ_gap

/-- **Assembly of `DampedComplBlockPropagator κ`** from the interior split (zero sorry). -/
theorem dampedComplBlockPropagator_of_interior (κ : PlanarFrameKernels)
    (hFree : PeriodizedRelFreeBlockInterior)
    (hDuh : DampedComplBlockIntDuhamelInterior κ) :
    DampedComplBlockPropagator κ := by
  intro hκ P hP m hm K C₀ h B α_free δ_gap hC₀ hh hh_le hB hα hδ hSeedDecay hFreeRel
  have hδ2 : 0 < δ_gap / 2 := half_pos hδ
  obtain ⟨M_free, b_free, hM_free, hb_free, hF_b⟩ :=
    hFree P hP m hm B α_free (δ_gap / 2) hB hα hδ2 hFreeRel
  have hF_b_weak : ∀ b : ℝ, b_free ≤ b →
      ∃ ν_free : ℝ, 0 < ν_free ∧
        ∀ ν ∈ Ioc 0 ν_free, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
            movingZ ν t₂ - movingZ ν t₁ = B →
            ∃ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
              IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel ∧
              (∀ σ τ : ℝ, σ ≤ τ → τ ≤ σ + B → ‖F_rel τ σ‖ ≤ M_free) := by
    intro b hb
    obtain ⟨ν_free, hν_free, hF_ν⟩ := hF_b b hb
    refine ⟨ν_free, hν_free, fun ν hν tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq => ?_⟩
    obtain ⟨F_rel, hF_rel, hF_sub, _⟩ := hF_ν ν hν tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
    exact ⟨F_rel, hF_rel, hF_sub⟩
  obtain ⟨K_A, b_prop, hK_A, hb_prop_le, hU_b⟩ :=
    hDuh hκ P hP m hm K C₀ h B M_free b_free (δ_gap / 2)
      hC₀ hh hh_le hB hM_free hb_free hδ2 hSeedDecay hF_b_weak
  refine ⟨M_free, K_A, b_prop, hM_free, hK_A, hb_free.trans hb_prop_le, fun b hb => ?_⟩
  obtain ⟨ν_free, hν_free, hF_ν⟩ := hF_b b (hb_prop_le.trans hb)
  obtain ⟨ν_uh, hν_uh, hU_ν⟩ := hU_b b hb
  refine ⟨min ν_free ν_uh, lt_min hν_free hν_uh,
    fun ν hν hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq => ?_⟩
  have hν_f : ν ∈ Ioc 0 ν_free := ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hν_u : ν ∈ Ioc 0 ν_uh := ⟨hν.1, hν.2.trans (min_le_right _ _)⟩
  obtain ⟨F_rel, hF_rel, hF_sub, hF_int⟩ := hF_ν ν hν_f tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
  obtain ⟨A_rel, U_rel, hA_rel, hDuh_rel, hA_bdd, hU_B0⟩ :=
    hU_ν ν hν_u hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq F_rel hF_rel hF_sub
      (α_free + δ_gap / 2) (by linarith) hF_int
  refine ⟨F_rel, A_rel, U_rel, hF_rel, hA_rel, hDuh_rel, hF_sub, hA_bdd, ?_⟩
  linarith

end BlockPropagatorInteriorSub

end UnforcedLeray.Short.IIIa
