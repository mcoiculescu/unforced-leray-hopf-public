import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.Assembly
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1_a.Op
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_regime
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_L2_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.FramePairing2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.TrainBdd
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.DualBounds
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_1_B.RateInt
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.LinFree
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.FreeAdjExists
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.FreeCylDuality
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.CylDataDense

/-!
# `PartIII-a:T21/c3/2/1/2/3/3/1/1/2`: Leaf B `MovSolDuhamelOfSmall`, reduced to four shared leaves

Source of record: `the November 2 reference manuscript` (SP), lines 2861-2866
(`W_z = G(z)W`, `G = θ⁻¹D + L_{ν,c}(z)`), 2937-2945 (`\bar F(z,t) = I_z F(z,t) R_t + S(z,t)(I-Π_t)`),
3050-3054 (weighted train gradient bound for `ν ≤ ν₀(m)`).

Regime form (`movSolDuhamelOfSmall_of_leaves`): `Regime.MovSolDuhamelOfSmall` from the open leaves of
`ComplFreeRateSub` only, `LinFreeAdjPairing`, `FreeAdjExists`, `FreeCylDuality`, `CylDataDense`.
Leaf II at fixed small `ν` is proved from the physical pairing `LinFreeAdjPairing`
(`movLinFreeAdjDuhamelAt_of`: `pairingCoV`, `movingInteractionForm_proof`, `AmplMovingSub.cov`,
the train bound `ladTrainBddAll`, and the integrability of the rate `linFreeAdjRateInt`,
`B/RateInt.lean`); `ν₀(m) = min(ν₀, 1)` with `ν₀` from `ladTrainBddAll m trainWeightedJetPoly_all`.

The tested Duhamel identity of `V = N⁻¹ I_d W` relative to `F_rel` is the duality of the weak
equation of `w` with the backward free adjoint flow `φ` of the test `ψ`. Fix `τ`, the age
`t = s(τ)` and the moving cell datum `Γ_ψ = ⟨y⟩^{2m} conj ψ` (`testDatum`, so that
`⟪ψ, I_d Y⟫ = ∫_{C_d} Γ_ψ Y`, `inner_eq_cell`). Let `φ` be the free adjoint flow on `[t₁, t]` with
terminal datum `physAdj a(t) Γ_ψ` (`FreeAdjExists`, open leaf of `ComplFreeRateSub`).

* `RelFreeAdjRep` (leaf I): `⟪ψ, F_rel τ σ (I_{d(s)} Y)⟫ = N(s,t)⁻¹ ∫_{C_{d(s)}} Y Φ(s)`,
  `Φ = movingPhi φ`. This is the `F_rel` analogue of `FreeMovingDualityM`
  (`freeMovingDualityM_of`): on pinned data it is `pairingCoV` + `FreeCylDuality`, in general
  by `CylDataDense` and continuity.
* `MovLinFreeAdjDuhamel` (leaf II): the moving pairing `∫_{C_{d(s)}} W(s) Φ(s)` has increments
  `∫_0^τ ∫_{C_{d(s)}} L_int W(s) Φ(s) dσ` (the free analogue of `LinAdjDualityBUC` with the
  interaction as source, read in moving variables: `pairingCoV`, `L_int W = a² J_a⁻¹(-(u·∇E))`,
  `dσ = a⁻² ds`).

`relFreeAdjRep_of` proves (I) from `FreeCylDuality` and `CylDataDense`; `movSolDuhamelOf_of` proves
`MovSolDuhamelOf` from (I), (II) and `FreeAdjExists` (combined: `movSolDuhamelOf_of_leaves`):
`⟪ψ, V τ⟫ = N(t₁,t)⁻¹ ∫ Γ_ψ W(t)`, `⟪ψ, F_rel τ 0 (V 0)⟫ = N(t₁,t)⁻¹ ∫ W(t₁) Φ(t₁)` and
`⟪ψ, F_rel τ σ (LV σ)⟫ = N(t₁,t)⁻¹ ∫ L_int W(s) Φ(s)` (`N(t₁,s) N(s,t) = N(t₁,t)`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsSub VariationOfConstantsMildSub

namespace ComplMildTestedSplit

namespace MovSolDuhamelSub

/-- The moving cell datum of a test `ψ = Φψ ∘ cToPlane` for the `L²_m` pairing:
`⟪ψ, I_d Y⟫ = ∫_{C_d} testDatum m Φψ · Y`, `testDatum = ⟨y⟩^{2m} conj Φψ`. -/
def testDatum (m : ℝ) (Φψ : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  ((B0579.jb y ^ m : ℝ) : ℂ) * conj (Φψ y)

end MovSolDuhamelSub

open MovSolDuhamelSub ComplFreeRateSub

/-- **Leaf I (`F_rel` against the free adjoint flow, SP 2937-2945)**: for a free adjoint flow `φ`
on `[t₁, t]`, `t = s(τ)`, with terminal datum `physAdj a(t) Γ_ψ`, the pairing of `ψ` with
`F_rel τ σ` of a cell-supported datum `I_{d(s)} Y` is `N(s,t)⁻¹ ∫_{C_{d(s)}} Y · movingPhi φ s`. -/
def RelFreeAdjRep : Prop :=
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ B b : ℝ, 0 < B → 1 ≤ b →
  ∀ ν : ℝ, 0 < ν →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
          IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
          ∀ τ ∈ Icc (0 : ℝ) B, ∀ (ψ : Planar.L2w m) (Φψ : ℝ × ℝ → ℂ),
            ContDiff ℝ ∞ Φψ → HasCompactSupport Φψ →
            (⇑ψ =ᵐ[volume] fun z : ℂ => Φψ (cToPlane z)) →
            ∀ φ : ℝ → ℝ × ℝ → ℂ,
              IsFreeAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t₁ (ageAt ν t₁ τ)
                (physAdj (clockA ν (ageAt ν t₁ τ)) (testDatum m Φψ)) φ →
              ∀ σ ∈ Icc (0 : ℝ) τ, ∀ (X : Planar.L2w m) (Y : ℝ × ℝ → ℂ),
                (⇑X =ᵐ[volume] fun z : ℂ =>
                  cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) Y
                    (cToPlane z)) →
                ⟪ψ, F_rel τ σ X⟫_ℂ =
                  ((clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ) : ℝ) : ℂ)⁻¹ *
                    ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))),
                      Y y * movingPhi ν φ (ageAt ν t₁ σ) y

/-- **Leaf II (weak equation of `w` against the free adjoint, SP 2861-2866, 2937-2945)**: for a
moving terminal datum `G ∈ X_{-m,d(t)}`, `t = s(τ)`, and a free adjoint flow `φ` on `[t₁, t]`
with terminal datum `physAdj a(t) G`, the moving pairing obeys the Duhamel identity with the
localized interaction `L_int W` as source (`Φ = movingPhi φ`, `W = movingW w`). -/
def MovLinFreeAdjDuhamel : Prop :=
  ∀ m : ℝ, 8 < m →
  ∀ B b : ℝ, 0 < B → 1 ≤ b →
  ∀ ν : ℝ, 0 < ν →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
          ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
            HasZeroCirculation (ν ^ (-2 : ℝ)) f →
            ∀ τ ∈ Icc (0 : ℝ) B, ∀ G : ℝ × ℝ → ℂ,
              MemLp G 2
                (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) (-m)) →
              ∀ φ : ℝ → ℝ × ℝ → ℂ,
                IsFreeAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t₁ (ageAt ν t₁ τ)
                  (physAdj (clockA ν (ageAt ν t₁ τ)) G) φ →
                IntervalIntegrable (fun σ =>
                    ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))),
                      movLInt tr (ageAt ν t₁ σ) (movingW ν w (ageAt ν t₁ σ)) y *
                        movingPhi ν φ (ageAt ν t₁ σ) y) volume 0 τ ∧
                ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))),
                    G y * movingW ν w (ageAt ν t₁ τ) y =
                  (∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)),
                      movingW ν w t₁ y * movingPhi ν φ t₁ y) +
                    ∫ σ in (0 : ℝ)..τ,
                      ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))),
                        movLInt tr (ageAt ν t₁ σ) (movingW ν w (ageAt ν t₁ σ)) y *
                          movingPhi ν φ (ageAt ν t₁ σ) y

/-- `MovLinFreeAdjDuhamel` at fixed `m` and `ν` (the body of the leaf after `∀ m, ∀ ν`). -/
def MovLinFreeAdjDuhamelAt (m ν : ℝ) : Prop :=
  ∀ B b : ℝ, 0 < B → 1 ≤ b →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
          ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
            HasZeroCirculation (ν ^ (-2 : ℝ)) f →
            ∀ τ ∈ Icc (0 : ℝ) B, ∀ G : ℝ × ℝ → ℂ,
              MemLp G 2
                (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) (-m)) →
              ∀ φ : ℝ → ℝ × ℝ → ℂ,
                IsFreeAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t₁ (ageAt ν t₁ τ)
                  (physAdj (clockA ν (ageAt ν t₁ τ)) G) φ →
                IntervalIntegrable (fun σ =>
                    ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))),
                      movLInt tr (ageAt ν t₁ σ) (movingW ν w (ageAt ν t₁ σ)) y *
                        movingPhi ν φ (ageAt ν t₁ σ) y) volume 0 τ ∧
                ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))),
                    G y * movingW ν w (ageAt ν t₁ τ) y =
                  (∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)),
                      movingW ν w t₁ y * movingPhi ν φ t₁ y) +
                    ∫ σ in (0 : ℝ)..τ,
                      ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))),
                        movLInt tr (ageAt ν t₁ σ) (movingW ν w (ageAt ν t₁ σ)) y *
                          movingPhi ν φ (ageAt ν t₁ σ) y

/-- `MovSolDuhamelOf` at fixed `m` and `ν` (the body after `∀ P, ∀ m, ∀ B b, ∀ ν`). -/
def MovSolDuhamelAt (m ν : ℝ) : Prop :=
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ B b : ℝ, 0 < B → 1 ≤ b →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
          IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
          ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
            HasZeroCirculation (ν ^ (-2 : ℝ)) f →
            ∀ V LV : ℝ → Planar.L2w m, VRep P m B ν t₁ w V → LVRep P m B ν tr t₁ w LV →
              ∀ τ ∈ Icc (0 : ℝ) B, ∀ ψ ∈ RelRegularityOrg.relSmoothClass m,
                IntervalIntegrable (fun σ => ⟪ψ, F_rel τ σ (LV σ)⟫_ℂ) volume 0 τ ∧
                ⟪ψ, V τ⟫_ℂ = ⟪ψ, F_rel τ 0 (V 0)⟫_ℂ +
                  ∫ σ in (0 : ℝ)..τ, ⟪ψ, F_rel τ σ (LV σ)⟫_ℂ

namespace MovSolDuhamelSub

/-- The `L²_m` pairing of a smooth test with a normalised cell-supported datum is the cell pairing
with `testDatum`. -/
theorem inner_eq_cell (m d : ℝ) (c : ℂ) {ψ X : Planar.L2w m} {Φψ Y : ℝ × ℝ → ℂ}
    (hψ : ⇑ψ =ᵐ[volume] fun z : ℂ => Φψ (cToPlane z))
    (hX : ⇑X =ᵐ[volume] fun z : ℂ => c * cellZeroExt d Y (cToPlane z)) :
    ⟪ψ, X⟫_ℂ = c * ∫ y in B0579.cell d, testDatum m Φψ y * Y y := by
  have hψ' := (Planar.wMeasure_ac m).ae_le hψ
  have hX' := (Planar.wMeasure_ac m).ae_le hX
  rw [MeasureTheory.L2.inner_def]
  have h1 : (fun z => ⟪(ψ : ℂ → ℂ) z, (X : ℂ → ℂ) z⟫_ℂ) =ᵐ[Planar.wMeasure m]
      fun z => c * (conj (Φψ (cToPlane z)) * cellZeroExt d Y (cToPlane z)) := by
    filter_upwards [hψ', hX'] with z h1 h2
    rw [h1, h2, RCLike.inner_apply]
    ring
  rw [integral_congr_ae h1, integral_const_mul]
  congr 1
  have hmp := measurePreserving_cToPlane_wMeasure m
  have hemb : MeasurableEmbedding cToPlane := by
    rw [cToPlane_eq_equiv]
    exact Complex.measurableEquivRealProd.measurableEmbedding
  have h2 : (∫ z, conj (Φψ (cToPlane z)) * cellZeroExt d Y (cToPlane z) ∂Planar.wMeasure m) =
      ∫ y, conj (Φψ y) * cellZeroExt d Y y ∂(volume.withDensity
        fun y => (B0579.density m y : ℝ≥0∞)) :=
    hmp.integral_comp hemb (fun y => conj (Φψ y) * cellZeroExt d Y y)
  rw [h2, integral_withDensity_eq_integral_smul (B0579.measurable_density m)]
  have h3 : (fun y : ℝ × ℝ => B0579.density m y • (conj (Φψ y) * cellZeroExt d Y y)) =
      (B0579.cell d).indicator (fun y => testDatum m Φψ y * Y y) := by
    funext y
    unfold cellZeroExt testDatum
    by_cases hy : y ∈ B0579.cell d
    · rw [indicator_of_mem hy, indicator_of_mem hy, NNReal.smul_def, Complex.real_smul,
        B0579.coe_density]
      ring
    · rw [indicator_of_notMem hy, indicator_of_notMem hy]
      simp
  rw [h3, integral_indicator (B0579.measurableSet_cell d)]

/-- `testDatum` of a smooth compactly supported test lies in every `X_{-m,d}`. -/
theorem memLp_testDatum (d m : ℝ) {Φψ : ℝ × ℝ → ℂ} (hc : Continuous Φψ)
    (hs : HasCompactSupport Φψ) :
    MemLp (testDatum m Φψ) 2 (B0579.cellMeasure d (-m)) := by
  have hcont : Continuous (testDatum m Φψ) := by
    unfold testDatum
    exact (Complex.continuous_ofReal.comp (B0579.continuous_jb_rpow m)).mul
      (Complex.continuous_conj.comp hc)
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x : ℝ × ℝ, R < |x.2| → Φψ x = 0 := by
    obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
    refine ⟨R, fun x hx => ?_⟩
    by_contra hne
    have hx' : x ∈ tsupport Φψ := subset_tsupport _ hne
    have h1 := hR hx'
    rw [mem_closedBall, dist_zero_right] at h1
    have h2 : |x.2| ≤ ‖x‖ := by
      have := norm_snd_le x
      rwa [Real.norm_eq_abs] at this
    linarith
  have hg : Continuous fun x => ‖testDatum m Φψ x‖ := hcont.norm
  have hgR : ∀ x : ℝ × ℝ, R < |x.2| → ‖testDatum m Φψ x‖ = 0 := by
    intro x hx
    simp [testDatum, hR x hx]
  have h := B0579.memLp_cell_of_continuous (c := d)
    (g := fun x => B0579.jb x ^ ((-m) / 2) * ‖testDatum m Φψ x‖)
    ((B0579.continuous_jb_rpow ((-m) / 2)).mul hg)
    (B0579.isCompact_box d R) (fun x hx hxK => by
      have hx' : R < |x.2| := by
        by_contra h'
        exact hxK (B0579.mem_box_of_mem_cell hx (not_lt.1 h'))
      simp [hgR x hx'])
  have hn : MemLp (fun x => ‖testDatum m Φψ x‖) 2 (B0579.cellMeasure d (-m)) :=
    ⟨hg.aestronglyMeasurable, by rw [B0579.eLpNorm_cellMeasure]; exact h.2⟩
  exact (memLp_norm_iff hcont.aestronglyMeasurable).1 hn

/-- Zero extension commutes with scalar multiples. -/
theorem cellZeroExt_const_mul (d : ℝ) (c : ℂ) (W : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    c * cellZeroExt d W y = cellZeroExt d (fun x => c * W x) y := by
  unfold cellZeroExt
  by_cases hy : y ∈ B0579.cell d
  · rw [indicator_of_mem hy, indicator_of_mem hy]
  · rw [indicator_of_notMem hy, indicator_of_notMem hy, mul_zero]

/-- A scalar pulls out of the cell pairing. -/
theorem cell_integral_const_mul (S : Set (ℝ × ℝ)) (c : ℂ) (A Φ : ℝ × ℝ → ℂ) :
    ∫ y in S, (fun x => c * A x) y * Φ y = c * ∫ y in S, A y * Φ y := by
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

/-- `N(s,t)⁻¹ N(t₁,s)⁻¹ = N(t₁,t)⁻¹`. -/
theorem clockN_inv_mul_inv (P : PlanarData) {ν t₁ s t : ℝ} (hν : 0 < ν) (h1 : 0 ≤ t₁)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ((clockN P ν s t : ℝ) : ℂ)⁻¹ * ((clockN P ν t₁ s : ℝ) : ℂ)⁻¹ =
      ((clockN P ν t₁ t : ℝ) : ℂ)⁻¹ := by
  rw [FrameStableSub.clockN_mul P hν h1 hs ht]
  push_cast
  rw [mul_inv]
  ring

/-- The exterior part of the periodized extension of a cell-supported datum vanishes a.e. -/
theorem extDil_ae_zero {d_s d_t : ℝ} (hds : 0 < d_s) (hdt : 0 < d_t) {W V : ℝ × ℝ → ℂ}
    (hW : W =ᵐ[volume] cellZeroExt d_s V) :
    (fun z : ℂ => extDilCocycle d_s d_t (fun x => W x - cellZeroExt d_s W x) (cToPlane z))
      =ᵐ[volume] fun _ => (0 : ℂ) := by
  have hg : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), W x - cellZeroExt d_s W x = 0 := by
    filter_upwards [hW] with x hx
    by_cases hxc : x ∈ B0579.cell d_s
    · rw [cellZeroExt_apply_of_mem d_s W hxc, sub_self]
    · rw [cellZeroExt_compl_apply d_s W hxc, sub_zero, hx, cellZeroExt_compl_apply d_s V hxc]
  have hρ : 0 < d_s / d_t := div_pos hds hdt
  have hq := Measure.quasiMeasurePreserving_smul (volume : Measure (ℝ × ℝ)) hρ.ne'
  have hg' : ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)),
      W ((d_s / d_t) • y) - cellZeroExt d_s W ((d_s / d_t) • y) = 0 := hq.ae hg
  have hg'' : ∀ᵐ z ∂(volume : Measure ℂ),
      W ((d_s / d_t) • cToPlane z) - cellZeroExt d_s W ((d_s / d_t) • cToPlane z) = 0 :=
    measurePreserving_cToPlane_volume.quasiMeasurePreserving.ae hg'
  filter_upwards [hg''] with z hz
  have e : (d_s / d_t) • cToPlane z =
      ((d_s / d_t) * (cToPlane z).1, (d_s / d_t) * (cToPlane z).2) := by
    ext <;> simp [smul_eq_mul]
  rw [e] at hz
  show extDilCocycle d_s d_t (fun x => W x - cellZeroExt d_s W x) (cToPlane z) = 0
  unfold extDilCocycle
  simp only [hz, mul_zero]

/-- A cell representative of an `L²_m` datum lies in `X_{m,d}`. -/
theorem memLp_of_cellRep {m d : ℝ} {X : Planar.L2w m} {Y : ℝ × ℝ → ℂ}
    (hX : ⇑X =ᵐ[volume] fun z : ℂ => cellZeroExt d Y (cToPlane z)) :
    MemLp Y 2 (B0579.cellMeasure d m) := by
  have h1 := BlockPropagatorInteriorSub.OrgSplit.RelIntA.cylRep_ae_of (d := d)
    ((Planar.wMeasure_ac m).ae_le hX)
  have h2 : BlockPropagatorInteriorSub.OrgSplit.RelIntA.cylRep X
      =ᵐ[volume.restrict (B0579.cell d)] Y := by
    rw [Filter.EventuallyEq, ae_restrict_iff' (B0579.measurableSet_cell d)] at h1 ⊢
    filter_upwards [h1] with y hy hyc
    unfold BlockPropagatorInteriorSub.OrgSplit.RelIntA.cylRep
    rw [hy hyc, cToPlane_planeToC, cellZeroExt_apply_of_mem d Y hyc]
  exact (BlockPropagatorInteriorSub.OrgSplit.RelIntA.memLp_cylRep (d := d) X).ae_eq
    ((B0579.cellMeasure_ac d m).ae_le h2)

/-- Zero extension commutes with differences (pointwise). -/
theorem cellZeroExt_sub' (d : ℝ) (Y M : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    cellZeroExt d Y y - cellZeroExt d M y = cellZeroExt d (Y - M) y := by
  unfold cellZeroExt
  by_cases hy : y ∈ B0579.cell d
  · rw [indicator_of_mem hy, indicator_of_mem hy, indicator_of_mem hy, Pi.sub_apply]
  · rw [indicator_of_notMem hy, indicator_of_notMem hy, indicator_of_notMem hy, sub_zero]

/-- The `L²_m` norm of a cell-supported datum is the `X_{m,d}` norm of its cell representative. -/
theorem norm_eq_xNorm_of_rep {m d : ℝ} {X : Planar.L2w m} {Y : ℝ × ℝ → ℂ}
    (hX : ⇑X =ᵐ[volume] fun z : ℂ => cellZeroExt d Y (cToPlane z))
    (hY : AEStronglyMeasurable Y (B0579.cellMeasure d m)) :
    ‖X‖ = (xNorm d m Y).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae ((Planar.wMeasure_ac m).ae_le hX),
    eLpNorm_cellZeroExt_cToPlane d m hY]

end MovSolDuhamelSub

/-- **Leaf B at fixed `m`, `ν`, conditional on the two duality leaves and the free adjoint
existence** (SP 2861-2866, 2937-2945). -/
theorem movSolDuhamelAt_of (hRep : RelFreeAdjRep)
    (hEx : ∀ (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ : ℝ),
      Leaf2DualityNeeded.FreeAdjExists ν m tr t₁ t₂) {m ν : ℝ} (hm : 8 < m) (hν : 0 < ν)
    (hDuh : MovLinFreeAdjDuhamelAt m ν) : MovSolDuhamelAt m ν := by
  intro P hP B b hB0 hb tr htr t₁ t₂ h1 h12 hθ hZ F_rel hF f w u hfl hz V LV hV hLV τ hτ ψ hψ
  obtain ⟨Φψ, hΦs, hΦc, hψe⟩ := hψ
  have hτ0 : 0 ≤ τ := hτ.1
  have htmem : ageAt ν t₁ τ ∈ Icc t₁ t₂ := ageAt_mem_Icc hν h1 h12 hZ hτ
  have ht0 : 0 ≤ ageAt ν t₁ τ := h1.trans htmem.1
  -- the free adjoint flow of the test
  have hΓ := memLp_testDatum (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) m
    hΦs.continuous hΦc
  obtain ⟨φ, hφ⟩ := hEx ν m tr t₁ t₂ hm hν h1 h12 htr (ageAt ν t₁ τ) htmem _ hΓ
  have hR := hRep P hP m hm B b hB0 hb ν hν tr htr t₁ t₂ h1 h12 hθ hZ F_rel hF τ hτ ψ Φψ hΦs hΦc
    hψe φ hφ
  obtain ⟨hInt, hId⟩ := hDuh B b hB0 hb tr htr t₁ t₂ h1 h12 hθ hZ f w u hfl hz τ hτ
    (testDatum m Φψ) hΓ φ hφ
  set c : ℂ := ((clockN P ν t₁ (ageAt ν t₁ τ) : ℝ) : ℂ)⁻¹ with hc
  -- the pairing with `F_rel τ σ (LV σ)`
  have hLVσ : ∀ σ ∈ Icc (0 : ℝ) τ, ⟪ψ, F_rel τ σ (LV σ)⟫_ℂ =
      c * ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))),
        movLInt tr (ageAt ν t₁ σ) (movingW ν w (ageAt ν t₁ σ)) y *
          movingPhi ν φ (ageAt ν t₁ σ) y := by
    intro σ hσ
    have hσB : σ ∈ Icc (0 : ℝ) B := ⟨hσ.1, hσ.2.trans hτ.2⟩
    have hs0 : 0 ≤ ageAt ν t₁ σ := h1.trans (ageAt_mem_Icc hν h1 h12 hZ hσB).1
    have hX : ⇑(LV σ) =ᵐ[volume] fun z : ℂ =>
        cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
          (fun x => ((clockN P ν t₁ (ageAt ν t₁ σ) : ℝ) : ℂ)⁻¹ *
            movLInt tr (ageAt ν t₁ σ) (movingW ν w (ageAt ν t₁ σ)) x) (cToPlane z) := by
      filter_upwards [hLV σ hσB] with z hz'
      rw [hz', cellZeroExt_const_mul]
    rw [hR σ hσ (LV σ) _ hX, cell_integral_const_mul, ← mul_assoc,
      clockN_inv_mul_inv P hν h1 hs0 ht0]
  -- the pairing with `F_rel τ 0 (V 0)`
  have hV0 : ⟪ψ, F_rel τ 0 (V 0)⟫_ℂ =
      c * ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)),
        movingW ν w t₁ y * movingPhi ν φ t₁ y := by
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) B := ⟨le_rfl, hB0.le⟩
    have hX : ⇑(V 0) =ᵐ[volume] fun z : ℂ =>
        cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ 0)))
          (fun x => ((clockN P ν t₁ (ageAt ν t₁ 0) : ℝ) : ℂ)⁻¹ *
            movingW ν w (ageAt ν t₁ 0) x) (cToPlane z) := by
      filter_upwards [hV 0 h0] with z hz'
      rw [hz', cellZeroExt_const_mul]
    rw [hR 0 ⟨le_rfl, hτ0⟩ (V 0) _ hX, cell_integral_const_mul, ← mul_assoc,
      clockN_inv_mul_inv P hν h1 (h1.trans_eq (ageAt_zero hν h1).symm) ht0, ageAt_zero hν h1]
  -- the pairing with `V τ`
  have hVτ : ⟪ψ, V τ⟫_ℂ =
      c * ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))),
        testDatum m Φψ y * movingW ν w (ageAt ν t₁ τ) y :=
    inner_eq_cell m _ c hψe (hV τ hτ)
  -- the time integrand
  have hEq : EqOn (fun σ => c * ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ))
        (clockA ν (ageAt ν t₁ σ))), movLInt tr (ageAt ν t₁ σ) (movingW ν w (ageAt ν t₁ σ)) y *
          movingPhi ν φ (ageAt ν t₁ σ) y)
      (fun σ => ⟪ψ, F_rel τ σ (LV σ)⟫_ℂ) (Set.uIcc 0 τ) := by
    intro σ hσ
    rw [Set.uIcc_of_le hτ0] at hσ
    exact (hLVσ σ hσ).symm
  refine ⟨(intervalIntegrable_congr (hEq.mono Set.uIoc_subset_uIcc)).1 (hInt.const_mul c), ?_⟩
  rw [hVτ, hId, mul_add, hV0, ← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_congr hEq]

/-- **Leaf B, conditional on the two duality leaves and the free adjoint existence**
(SP 2861-2866, 2937-2945). -/
theorem movSolDuhamelOf_of (hRep : RelFreeAdjRep) (hDuh : MovLinFreeAdjDuhamel)
    (hEx : ∀ (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ : ℝ),
      Leaf2DualityNeeded.FreeAdjExists ν m tr t₁ t₂) :
    MovSolDuhamelOf := fun P hP m hm B b hB0 hb ν hν =>
  movSolDuhamelAt_of hRep hEx hm hν (fun B b hB hb => hDuh m hm B b hB hb ν hν) P hP B b hB0 hb

open MovSolDuhamelSub in
/-- **Leaf I from the free duality leaves** (SP 2937-2945): on pinned data `I_{d(s)} J⁻¹ f` the
pairing is `pairingCoV` + `FreeCylDuality` (the exterior term of the periodized extension
vanishes, `extDil_ae_zero`); in general by `CylDataDense` and the continuity of both sides. -/
theorem relFreeAdjRep_of
    (hCyl : ∀ (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ : ℝ),
      Leaf2DualityNeeded.FreeCylDuality ν m tr t₁ t₂)
    (hDense : Leaf2DualityNeeded.CylDataDense) : RelFreeAdjRep := by
  intro P hP m hm B b hB0 hb ν hν tr htr t₁ t₂ h1 h12 hθ hZ F_rel hF τ hτ ψ Φψ hΦs hΦc hψe φ hφ
    σ hσ X Y hX
  have hσB : σ ∈ Icc (0 : ℝ) B := ⟨hσ.1, hσ.2.trans hτ.2⟩
  have ht₂ : 0 ≤ t₂ := h1.trans h12
  have hsmem := ageAt_mem_Icc hν h1 h12 hZ hσB
  have htmem := ageAt_mem_Icc hν h1 h12 hZ hτ
  have hst : ageAt ν t₁ σ ≤ ageAt ν t₁ τ := ageAt_mono_on_block hν h1 ht₂ hZ hσ.1 hσ.2 hτ.2
  have hs0 : 0 ≤ ageAt ν t₁ σ := h1.trans hsmem.1
  have ht0 : 0 ≤ ageAt ν t₁ τ := h1.trans htmem.1
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hm0 : 0 ≤ m := by linarith
  have has1 : 1 ≤ clockA ν (ageAt ν t₁ σ) := one_le_clockA hν.le hs0
  have hat1 : 1 ≤ clockA ν (ageAt ν t₁ τ) := one_le_clockA hν.le ht0
  have has0 : 0 < clockA ν (ageAt ν t₁ σ) := by linarith
  have hat0 : 0 < clockA ν (ageAt ν t₁ τ) := by linarith
  have hds : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)) :=
    div_pos hc (Real.sqrt_pos.2 has0)
  have hdt : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)) :=
    div_pos hc (Real.sqrt_pos.2 hat0)
  set N : ℂ := ((clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ) : ℝ) : ℂ)⁻¹ with hN
  -- the moving adjoint at `s` lies in `X_{-m,d(s)}`
  have hΦ₁ : MemLp (movingPhi ν φ (ageAt ν t₁ σ)) 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) (-m)) := by
    rcases eq_or_lt_of_le hst with h | h
    · rw [h]
      have hae := (B0579.cellMeasure_ac _ (-m)).ae_le
        (Leaf2DualityNeeded.movingPhi_terminal_ae hν ht0 hφ)
      exact (memLp_testDatum _ m hΦs.continuous hΦc).ae_eq (Filter.EventuallyEq.symm hae)
    · have hcont : Continuous (φ (ageAt ν t₁ σ)) := (hφ.smooth _ ⟨hsmem.1, h⟩).continuous
      exact mpScaleMemLp m (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)) hc has0
        (clockA ν (ageAt ν t₁ σ))⁻¹ (φ (ageAt ν t₁ σ)) hcont (hφ.memX _ ⟨hsmem.1, hst⟩)
  have hYm : MemLp Y 2
      (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) m) :=
    memLp_of_cellRep hX
  -- pinned real cylinder data
  have hJ : ∀ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
      MemLp (JscaleInv (clockA ν (ageAt ν t₁ σ)) (fun x => ((f x : ℝ) : ℂ))) 2
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) m) :=
    fun f hf => ComplCouplingSub.memLp_JscaleInv hm0 has1 (hf.memLp m).ofReal
  have key : ∀ (f : B0579.Plane → ℝ) (hf : B0579.IsCylTest (ν ^ (-2 : ℝ)) f),
      ⟪ψ, F_rel τ σ ((memLp_cellZeroExt_cToPlane _ m (hJ f hf)).toLp _)⟫_ℂ =
        N * ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))),
          JscaleInv (clockA ν (ageAt ν t₁ σ)) (fun x => ((f x : ℝ) : ℂ)) y *
            movingPhi ν φ (ageAt ν t₁ σ) y := by
    intro f hf
    set Xf : Planar.L2w m := (memLp_cellZeroExt_cToPlane _ m (hJ f hf)).toLp _ with hXf_def
    have hXf : ⇑Xf =ᵐ[volume] fun z : ℂ =>
        cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
          (JscaleInv (clockA ν (ageAt ν t₁ σ)) (fun x => ((f x : ℝ) : ℂ))) (cToPlane z) :=
      (Planar.volume_ac m).ae_le (MemLp.coeFn_toLp _)
    obtain ⟨ωf, hωf, -, -⟩ := UnforcedLeray.Short.IIb.freeCylSmoothExists_proof m ν
      (ν ^ (-2 : ℝ)) hm hν hc tr htr _ hs0 f hf
    have hpin := hF σ τ hσ.1 hσ.2 hτ.2 f hf ωf hωf Xf (by
      filter_upwards [hXf] with z hz hzc
      rw [hz, cellZeroExt_apply_of_mem _ _ hzc])
    have hW : (fun y => (Xf : ℂ → ℂ) (planeToC y)) =ᵐ[volume]
        cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
          (JscaleInv (clockA ν (ageAt ν t₁ σ)) (fun x => ((f x : ℝ) : ℂ))) := by
      have := measurePreserving_planeToC_volume.quasiMeasurePreserving.ae_eq_comp hXf
      filter_upwards [this] with y hy
      simpa [Function.comp, cToPlane_planeToC] using hy
    have hout : ⇑(F_rel τ σ Xf) =ᵐ[volume] fun z : ℂ =>
        N * cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))
          (JscaleInv (clockA ν (ageAt ν t₁ τ)) (fun x => ((ωf (ageAt ν t₁ τ) x : ℝ) : ℂ)))
          (cToPlane z) := by
      filter_upwards [hpin, extDil_ae_zero hds hdt hW] with z hz hz0
      rw [hz]
      simp only [periodizedExt]
      rw [hz0, add_zero]
    rw [inner_eq_cell m _ N hψe hout]
    congr 1
    have e1 : ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))),
        testDatum m Φψ y *
          JscaleInv (clockA ν (ageAt ν t₁ τ)) (fun x => ((ωf (ageAt ν t₁ τ) x : ℝ) : ℂ)) y =
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), ((ωf (ageAt ν t₁ τ) x : ℝ) : ℂ) *
          physAdj (clockA ν (ageAt ν t₁ τ)) (testDatum m Φψ) x := by
      rw [← pairingCoV (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)) hc hat0]
      congr 1
      funext y
      ring
    have e2 := hCyl ν m tr t₁ t₂ hm hν h1 h12 htr (ageAt ν t₁ τ) htmem _ φ hφ
      (ageAt ν t₁ σ) ⟨hsmem.1, hst⟩ f hf ωf hωf
    have e3 : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), ((f x : ℝ) : ℂ) * φ (ageAt ν t₁ σ) x =
        ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))),
          JscaleInv (clockA ν (ageAt ν t₁ σ)) (fun x => ((f x : ℝ) : ℂ)) y *
            movingPhi ν φ (ageAt ν t₁ σ) y := by
      rw [pairingCoV (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)) hc has0]
      congr 1
      funext x
      rw [physAdj_movingPhi hν hs0 φ x]
    rw [e1, e2, e3]
  -- complex cylinder data
  have keyC : ∀ (f₁ f₂ : B0579.Plane → ℝ) (hf₁ : B0579.IsCylTest (ν ^ (-2 : ℝ)) f₁)
      (hf₂ : B0579.IsCylTest (ν ^ (-2 : ℝ)) f₂),
      ⇑((memLp_cellZeroExt_cToPlane _ m (hJ f₁ hf₁)).toLp _ +
          Complex.I • (memLp_cellZeroExt_cToPlane _ m (hJ f₂ hf₂)).toLp _ : Planar.L2w m)
        =ᵐ[volume] (fun z : ℂ => cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
          (movCx (clockA ν (ageAt ν t₁ σ)) f₁ f₂) (cToPlane z)) ∧
      ⟪ψ, F_rel τ σ ((memLp_cellZeroExt_cToPlane _ m (hJ f₁ hf₁)).toLp _ +
          Complex.I • (memLp_cellZeroExt_cToPlane _ m (hJ f₂ hf₂)).toLp _)⟫_ℂ =
        N * ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))),
          movCx (clockA ν (ageAt ν t₁ σ)) f₁ f₂ y * movingPhi ν φ (ageAt ν t₁ σ) y := by
    intro f₁ f₂ hf₁ hf₂
    refine ⟨?_, ?_⟩
    · have h1' := (Planar.volume_ac m).ae_le (MemLp.coeFn_toLp
        (memLp_cellZeroExt_cToPlane _ m (hJ f₁ hf₁)))
      have h2' := (Planar.volume_ac m).ae_le (MemLp.coeFn_toLp
        (memLp_cellZeroExt_cToPlane _ m (hJ f₂ hf₂)))
      have hadd := (Planar.volume_ac m).ae_le (Lp.coeFn_add
        ((memLp_cellZeroExt_cToPlane _ m (hJ f₁ hf₁)).toLp _)
        (Complex.I • (memLp_cellZeroExt_cToPlane _ m (hJ f₂ hf₂)).toLp _))
      have hsmul := (Planar.volume_ac m).ae_le (Lp.coeFn_smul Complex.I
        ((memLp_cellZeroExt_cToPlane _ m (hJ f₂ hf₂)).toLp _))
      filter_upwards [h1', h2', hadd, hsmul] with z hz1 hz2 hza hzs
      rw [hza, Pi.add_apply, hzs, Pi.smul_apply, hz1, hz2, smul_eq_mul]
      unfold cellZeroExt movCx
      by_cases hzc : cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
      · rw [indicator_of_mem hzc, indicator_of_mem hzc, indicator_of_mem hzc]
      · rw [indicator_of_notMem hzc, indicator_of_notMem hzc, indicator_of_notMem hzc]
        ring
    · rw [map_add, map_smul, inner_add_right, inner_smul_right, key f₁ hf₁, key f₂ hf₂]
      have i1 := (Leaf2DualityNeeded.pair_bound (hJ f₁ hf₁) hΦ₁).1
      have i2 := (Leaf2DualityNeeded.pair_bound (hJ f₂ hf₂) hΦ₁).1
      have h := integral_add i1 (i2.const_mul Complex.I)
      rw [integral_const_mul] at h
      have e : ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))),
          movCx (clockA ν (ageAt ν t₁ σ)) f₁ f₂ y * movingPhi ν φ (ageAt ν t₁ σ) y =
          ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))),
            (JscaleInv (clockA ν (ageAt ν t₁ σ)) (fun x => ((f₁ x : ℝ) : ℂ)) y *
                movingPhi ν φ (ageAt ν t₁ σ) y +
              Complex.I * (JscaleInv (clockA ν (ageAt ν t₁ σ)) (fun x => ((f₂ x : ℝ) : ℂ)) y *
                movingPhi ν φ (ageAt ν t₁ σ) y)) := by
        congr 1
        funext y
        unfold movCx
        ring
      rw [e, h]
      ring
  -- density
  set Pn : ℝ := (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) (-m)
    (movingPhi ν φ (ageAt ν t₁ σ))).toReal with hPn
  have hPn0 : 0 ≤ Pn := ENNReal.toReal_nonneg
  set K : ℝ := ‖ψ‖ * ‖F_rel τ σ‖ + ‖N‖ * Pn with hK
  have hK0 : 0 ≤ K := by positivity
  set D : ℂ := ⟪ψ, F_rel τ σ X⟫_ℂ -
    N * ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))),
      Y y * movingPhi ν φ (ageAt ν t₁ σ) y with hD
  have hbound : ∀ ε : ℝ, 0 < ε → ‖D‖ ≤ ε * K := by
    intro ε hε
    obtain ⟨f₁, f₂, hf₁, hf₂, hclose⟩ :=
      hDense (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)) m hc has1 hm0 Y hYm ε hε
    obtain ⟨hrep', hpair'⟩ := keyC f₁ f₂ hf₁ hf₂
    set X' : Planar.L2w m := (memLp_cellZeroExt_cToPlane _ m (hJ f₁ hf₁)).toLp _ +
      Complex.I • (memLp_cellZeroExt_cToPlane _ m (hJ f₂ hf₂)).toLp _ with hX'
    have hmov : MemLp (movCx (clockA ν (ageAt ν t₁ σ)) f₁ f₂) 2
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) m) := by
      have := (hJ f₁ hf₁).add ((hJ f₂ hf₂).const_mul Complex.I)
      exact this.ae_eq (Filter.Eventually.of_forall fun y => by simp [movCx])
    have hdiff : MemLp (Y - movCx (clockA ν (ageAt ν t₁ σ)) f₁ f₂) 2
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) m) :=
      hYm.sub hmov
    have hrepD : ⇑(X - X') =ᵐ[volume] fun z : ℂ =>
        cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
          (Y - movCx (clockA ν (ageAt ν t₁ σ)) f₁ f₂) (cToPlane z) := by
      filter_upwards [(Planar.volume_ac m).ae_le (Lp.coeFn_sub X X'), hX, hrep'] with z h0 h1' h2'
      rw [h0, Pi.sub_apply, h1', h2']
      exact cellZeroExt_sub' _ Y (movCx (clockA ν (ageAt ν t₁ σ)) f₁ f₂) (cToPlane z)
    have hnorm : ‖X - X'‖ = (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) m
        (Y - movCx (clockA ν (ageAt ν t₁ σ)) f₁ f₂)).toReal :=
      norm_eq_xNorm_of_rep hrepD hdiff.aestronglyMeasurable
    have hxn : (xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) m
        (Y - movCx (clockA ν (ageAt ν t₁ σ)) f₁ f₂)).toReal ≤ ε :=
      ENNReal.toReal_le_of_le_ofReal hε.le hclose.le
    have hDe : D = ⟪ψ, F_rel τ σ (X - X')⟫_ℂ -
        N * ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))),
          (Y - movCx (clockA ν (ageAt ν t₁ σ)) f₁ f₂) y * movingPhi ν φ (ageAt ν t₁ σ) y := by
      rw [hD, map_sub, inner_sub_right, hpair']
      have i1 := (Leaf2DualityNeeded.pair_bound hYm hΦ₁).1
      have i2 := (Leaf2DualityNeeded.pair_bound hmov hΦ₁).1
      have e : ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))),
          (Y - movCx (clockA ν (ageAt ν t₁ σ)) f₁ f₂) y * movingPhi ν φ (ageAt ν t₁ σ) y =
          (∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))),
            Y y * movingPhi ν φ (ageAt ν t₁ σ) y) -
          ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))),
            movCx (clockA ν (ageAt ν t₁ σ)) f₁ f₂ y * movingPhi ν φ (ageAt ν t₁ σ) y := by
        rw [← integral_sub i1 i2]
        congr 1
        funext y
        simp only [Pi.sub_apply]
        ring
      rw [e]
      ring
    have b1 : ‖⟪ψ, F_rel τ σ (X - X')⟫_ℂ‖ ≤ ‖ψ‖ * ‖F_rel τ σ‖ * ε := by
      calc ‖⟪ψ, F_rel τ σ (X - X')⟫_ℂ‖ ≤ ‖ψ‖ * ‖F_rel τ σ (X - X')‖ := norm_inner_le_norm _ _
        _ ≤ ‖ψ‖ * (‖F_rel τ σ‖ * ‖X - X'‖) :=
            mul_le_mul_of_nonneg_left ((F_rel τ σ).le_opNorm _) (norm_nonneg _)
        _ ≤ ‖ψ‖ * (‖F_rel τ σ‖ * ε) := by
            rw [hnorm]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hxn (norm_nonneg _)) (norm_nonneg _)
        _ = ‖ψ‖ * ‖F_rel τ σ‖ * ε := by ring
    have b2 := (Leaf2DualityNeeded.pair_bound hdiff hΦ₁).2
    rw [ENNReal.toReal_mul] at b2
    have b2' : ‖N * ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))),
        (Y - movCx (clockA ν (ageAt ν t₁ σ)) f₁ f₂) y * movingPhi ν φ (ageAt ν t₁ σ) y‖ ≤
        ‖N‖ * Pn * ε := by
      rw [norm_mul]
      calc ‖N‖ * ‖∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))),
            (Y - movCx (clockA ν (ageAt ν t₁ σ)) f₁ f₂) y * movingPhi ν φ (ageAt ν t₁ σ) y‖
          ≤ ‖N‖ * ((xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) m
              (Y - movCx (clockA ν (ageAt ν t₁ σ)) f₁ f₂)).toReal * Pn) :=
            mul_le_mul_of_nonneg_left b2 (norm_nonneg _)
        _ ≤ ‖N‖ * (ε * Pn) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxn hPn0) (norm_nonneg _)
        _ = ‖N‖ * Pn * ε := by ring
    calc ‖D‖ ≤ ‖⟪ψ, F_rel τ σ (X - X')⟫_ℂ‖ +
          ‖N * ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))),
            (Y - movCx (clockA ν (ageAt ν t₁ σ)) f₁ f₂) y * movingPhi ν φ (ageAt ν t₁ σ) y‖ := by
          rw [hDe]; exact norm_sub_le _ _
      _ ≤ ‖ψ‖ * ‖F_rel τ σ‖ * ε + ‖N‖ * Pn * ε := add_le_add b1 b2'
      _ = ε * K := by rw [hK]; ring
  have hD0 : ‖D‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖D‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have h1' := hbound (‖D‖ / (2 * (K + 1))) (by positivity)
    have h2' : ‖D‖ / (2 * (K + 1)) * K < ‖D‖ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  exact sub_eq_zero.1 (norm_eq_zero.1 hD0)

/-- **Leaf B from the open leaves**: the free duality leaves of `ComplFreeRateSub`
(`FreeAdjExists`, `FreeCylDuality`, `CylDataDense`, shared with `FreeMovingDuality`) and the
moving weak Duhamel identity `MovLinFreeAdjDuhamel`. -/
theorem movSolDuhamelOf_of_leaves (hDuh : MovLinFreeAdjDuhamel)
    (hEx : ∀ (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ : ℝ),
      Leaf2DualityNeeded.FreeAdjExists ν m tr t₁ t₂)
    (hCyl : ∀ (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ : ℝ),
      Leaf2DualityNeeded.FreeCylDuality ν m tr t₁ t₂)
    (hDense : Leaf2DualityNeeded.CylDataDense) : MovSolDuhamelOf :=
  movSolDuhamelOf_of (relFreeAdjRep_of hCyl hDense) hDuh hEx

/-! ## Leaf II in the small-viscosity regime from the physical pairing -/

/-- **Leaf II at fixed small `ν` from the physical pairing** (SP 2861-2866, 2937-2958): the
physical identity `LinFreeAdjPairing` (with `LadTrainBdd`, Part I for `ν ≤ ν₀(m)`), read in
moving variables: the pairings by `pairingCoV` and `physAdj_movingPhi`, the interaction by
`movingInteractionForm_proof` (`∫(u·∇E)φ = -a⁻² ∫ L_int W · Φ`), the time by `r = s(σ)`
(`AmplMovingSub.cov`, `dσ = a⁻² dr`), the integrability by `linFreeAdjRateInt`. -/
theorem movLinFreeAdjDuhamelAt_of {m ν : ℝ} (hm : 8 < m) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hPair : ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ : ℝ),
      Leaf2WeakEqNeeded.LinFreeAdjPairing ν m tr t₁ t₂)
    (hLad : ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) :
    MovLinFreeAdjDuhamelAt m ν := by
  intro B b hB0 hb tr htr t₁ t₂ h1 h12 hθ hZ f w u hfl hz τ hτ G hG φ hφ
  have htmem : ageAt ν t₁ τ ∈ Icc t₁ t₂ := ageAt_mem_Icc hν h1 h12 hZ hτ
  have ht0 : 0 ≤ ageAt ν t₁ τ := h1.trans htmem.1
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hat : 0 < clockA ν (ageAt ν t₁ τ) := by unfold clockA; positivity
  have ha1 : 0 < clockA ν t₁ := by unfold clockA; positivity
  set t := ageAt ν t₁ τ with ht_def
  set M : ℝ → ℂ := fun r => ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
      movLInt tr r (movingW ν w r) y * movingPhi ν φ r y with hM
  set I : ℝ → ℂ := fun r => ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
      (u r x 0 * ((B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) +
        u r x 1 * ((B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)) * φ r x with hIdef
  -- the physical identity and the moving interaction form
  have hP : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w t x * physAdj (clockA ν t) G x =
      (∫ x in B0579.cell (ν ^ (-2 : ℝ)), w t₁ x * φ t₁ x) - ∫ r in t₁..t, I r :=
    hPair tr t₁ t₂ hm hν h1 h12 htr (hLad tr htr) f w u hfl hz t htmem _ φ hφ t₁
      ⟨le_rfl, htmem.1⟩
  have hMIF := Leaf2WeakEqFrame.movingInteractionForm_proof ν m tr t₁ hm hν h1 htr f w u hfl hz
    t _ φ hφ
  have hEqOn : EqOn (fun r => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * M r) (fun r => -I r)
      (Ioo t₁ t) := by
    intro r hr
    have h := hMIF r ⟨hr.1.le, hr.2⟩
    simp only [hM, hIdef]
    rw [h, neg_neg]
    rfl
  have hI : IntegrableOn I (Ioc t₁ t) :=
    linFreeAdjRateInt ν m tr t₁ hm hν hν1 h1 htr (hLad tr htr) f w u hfl hz t _ φ hφ
  have hIntM : IntegrableOn (fun r => (((clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) * M r) (Ioc t₁ t) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo enorm_ne_top).2
      (((integrableOn_Ioc_iff_integrableOn_Ioo enorm_ne_top).1 hI).neg.congr_fun hEqOn.symm
        measurableSet_Ioo)
  obtain ⟨hcovI, hcovE⟩ := AmplMovingSub.cov hν h1 h12 hZ hτ M hIntM
  -- the time integral
  have hσ : ∫ σ in (0 : ℝ)..τ, M (ageAt ν t₁ σ) = -∫ r in t₁..t, I r := by
    rw [intervalIntegral.integral_of_le hτ.1, hcovE, intervalIntegral.integral_of_le htmem.1,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun measurableSet_Ioo hEqOn, integral_neg]
  -- the two pairings
  have hL : ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)), G y * movingW ν w t y =
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w t x * physAdj (clockA ν t) G x := by
    rw [← pairingCoV _ _ hc hat (w t) G]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [movingW]
    ring
  have hR1 : ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)),
      movingW ν w t₁ y * movingPhi ν φ t₁ y = ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w t₁ x * φ t₁ x := by
    rw [show movingW ν w t₁ = JscaleInv (clockA ν t₁) (w t₁) from rfl,
      pairingCoV _ _ hc ha1 (w t₁) _]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [physAdj_movingPhi hν h1 φ x]
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.1).2 hcovI, ?_⟩
  show ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)), G y * movingW ν w t y =
    (∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)),
      movingW ν w t₁ y * movingPhi ν φ t₁ y) + ∫ σ in (0 : ℝ)..τ, M (ageAt ν t₁ σ)
  rw [hL, hR1, hP, hσ, sub_eq_add_neg]

/-- **Leaf B in the small-viscosity regime from the open leaves** (SP 2861-2866, 2937-2945,
3050-3054): the free duality leaves of `ComplFreeRateSub` (`FreeAdjExists`, `FreeCylDuality`,
`CylDataDense`) and the physical weak pairing `LinFreeAdjPairing` (the integrability of its rate is
`linFreeAdjRateInt`, `B/RateInt.lean`); `ν₀(m) = min(ν₀ of ladTrainBddAll, 1)` (Part I weighted
train gradient bound, `CutFTCDual.trainWeightedJetPoly_all`). -/
theorem movSolDuhamelOfSmall_of_leaves
    (hPair : ∀ (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ : ℝ),
      Leaf2WeakEqNeeded.LinFreeAdjPairing ν m tr t₁ t₂)
    (hEx : ∀ (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ : ℝ),
      Leaf2DualityNeeded.FreeAdjExists ν m tr t₁ t₂)
    (hCyl : ∀ (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ : ℝ),
      Leaf2DualityNeeded.FreeCylDuality ν m tr t₁ t₂)
    (hDense : Leaf2DualityNeeded.CylDataDense) : Regime.MovSolDuhamelOfSmall := by
  intro m hm
  obtain ⟨ν₀, hν₀, hT⟩ := ladTrainBddAll m CutFTCDual.trainWeightedJetPoly_all
  refine ⟨min ν₀ 1, lt_min hν₀ one_pos, fun P hP B b hB0 hb ν hν hνs => ?_⟩
  have hνν₀ : ν ∈ Ioc 0 ν₀ := ⟨hν, hνs.trans (min_le_left _ _)⟩
  exact movSolDuhamelAt_of (relFreeAdjRep_of hCyl hDense) hEx hm hν
    (movLinFreeAdjDuhamelAt_of hm hν (hνs.trans (min_le_right _ _))
      (fun tr t₁ t₂ => hPair ν m tr t₁ t₂)
      (fun tr htr => hT ν hνν₀ tr htr)) P hP B b hB0 hb

theorem movSolDuhamelOfSmall : UnforcedLeray.Short.IIIa.ComplMildTestedSplit.Regime.MovSolDuhamelOfSmall :=
  movSolDuhamelOfSmall_of_leaves
    ComplFreeRateSub.Leaf2WeakEqNeeded.linFreeAdjPairing
    _root_.freeAdjExists
    ComplFreeRateSub.Leaf2DualityNeeded.freeCylDuality
    ComplFreeRateSub.Leaf2DualityNeeded.cylDataDense

end ComplMildTestedSplit

end UnforcedLeray.Short.IIIa
