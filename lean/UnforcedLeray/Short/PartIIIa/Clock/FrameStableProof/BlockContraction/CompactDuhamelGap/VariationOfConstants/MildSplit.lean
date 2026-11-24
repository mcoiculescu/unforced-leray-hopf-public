import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2

/-!
# Part III-a, `PartIII-a:T21/c3/2/1/2`: split of `ComplBlockDuhamelVoC` into three leaves

Source of record: `the November 2 reference manuscript` (SP), lines 2914-2925
and 2962-2982 (`eq:short-causal-damped-complement`, `eq:short-causal-stable-moving`).

`VariationOfConstantsSub.ComplBlockDuhamelSplit` is equivalent to the target.  This file splits
the target into an abstract operator lemma and two PDE leaves, and proves the assembly.

On a block `[t₁, t₂]` of moving length `B`, put `s(τ) = ageAt ν t₁ τ`,
`Y(τ) = N(t₁, s(τ))⁻¹ I_{s(τ)} r(s(τ))` (zero extension of the normalised complement
`r = W - E α`, SP 2914-2925) and `G(σ) = N(t₁, s(σ))⁻¹ I_{s(σ)} Σ_j α_j (1 - EΛ) K_{0,j}`.
Since `r' = (G - E H₀) r + (K₀ - E M₀) α` and `𝓑 = G - β₀ - E H₀ + [...] Λ` agrees with
`G - β₀ - E H₀` on `ker Λ`, the variable `Y` is a mild solution of
`Y' = (G_free - β₀) Y + A Y + G` (`F_rel` = relative free evolution, `A_rel` = `movDampedComplInt`).

* `DuhamelVoCAbstract` (leaf A, functional analysis): a mild solution relative to `F` of
  `Y' = (gen F) Y + A Y + G` satisfies `Y(B) = U(B,0) Y(0) + ∫₀^B U(B,σ) G(σ) dσ` for the Duhamel
  evolution `U` of `(F, A)`, under strong continuity of `F` on the block triangle and strong
  measurability and boundedness of `A` (Dyson series, Fubini, Gronwall).
* `RelBlockRegularity` (leaf B, PDE): the pinned `F_rel` is strongly continuous on the triangle
  and the pinned `A_rel` is strongly measurable and bounded on `[0, B]`.
* `ComplMovingMild` (leaf C, PDE, SP 2914-2925): `Y` and `G` above exist in `Planar.L2w m`, with
  the mild equation relative to `(F_rel, A_rel)` (weak-to-mild duality for `IsLinearisedFlow`,
  the amplitude identity `(ΛW)' = H₀ W`, density extension of the pinning predicates).
* `complBlockDuhamelSplit_of_mild`, `complBlockDuhamelVoC_of_mild`: assembly (proved):
  zero-extension isometry, `‖∫‖ₑ ≤ ∫⁻ ‖·‖ₑ`, the change of variables `σ = z(r) - z(t₁)` with
  Jacobian `a(r)^{-2}`, and `N(t₁, r)⁻¹ N(t₁, t₂) = N(r, t₂)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsSub

namespace VariationOfConstantsMildSub

/-- The closed block triangle `{(τ, σ) | 0 ≤ σ ≤ τ ≤ B}`. -/
def blockTriangle (B : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ B}

/-- **Leaf A (`DuhamelVoCAbstract`)**: inhomogeneous variation of constants for a
`B0104.IsDuhamelEvolution` on one block. -/
def DuhamelVoCAbstract : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : ℝ) (F : ℝ → ℝ → H →L[ℂ] H) (A : ℝ → H →L[ℂ] H) (U : ℝ → ℝ → H →L[ℂ] H),
    0 < B →
    UnforcedLeray.B0104.IsDuhamelEvolution (ι := Unit) B (fun _ => F) (fun _ => A)
      (fun _ => U) →
    (∀ x : H, ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2 x) (blockTriangle B)) →
    (∀ x : H, AEStronglyMeasurable (fun r => A r x) (volume.restrict (Icc (0 : ℝ) B))) →
    (∃ K_A : ℝ, ∀ r ∈ Icc (0 : ℝ) B, ‖A r‖ ≤ K_A) →
    ∀ Y G : ℝ → H,
      AEStronglyMeasurable Y (volume.restrict (Icc (0 : ℝ) B)) →
      (∃ C : ℝ, ∀ τ ∈ Icc (0 : ℝ) B, ‖Y τ‖ ≤ C) →
      IntegrableOn G (Icc (0 : ℝ) B) →
      (∀ τ ∈ Icc (0 : ℝ) B,
        Y τ = F τ 0 (Y 0) + ∫ σ in (0 : ℝ)..τ, F τ σ (A σ (Y σ) + G σ)) →
      Y B = U B 0 (Y 0) + ∫ σ in (0 : ℝ)..B, U B σ (G σ)

/-- **Leaf B (`RelBlockRegularity`)**: regularity of the pinned block operators. -/
def RelBlockRegularity (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K B b : ℝ, 0 < B → 1 ≤ b →
  ∀ ν : ℝ, 0 < ν → PerFrameFacts κ ν m b K →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ (F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m)
          (A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m),
          IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
          IsDampedComplBlockInt κ P ν m tr t₁ B A_rel →
          (∀ x : Planar.L2w m,
            ContinuousOn (fun p : ℝ × ℝ => F_rel p.1 p.2 x) (blockTriangle B)) ∧
          (∀ x : Planar.L2w m,
            AEStronglyMeasurable (fun r => A_rel r x) (volume.restrict (Icc (0 : ℝ) B))) ∧
          (∃ K_A : ℝ, ∀ r ∈ Icc (0 : ℝ) B, ‖A_rel r‖ ≤ K_A)

/-- **Leaf C (`ComplMovingMild`, SP 2914-2925)**: the normalised zero-extended moving complement
`Y` is a mild solution relative to `(F_rel, A_rel)` with the mode forcing `G`. -/
def ComplMovingMild (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m →
  ∀ K B b : ℝ, 0 < B → 1 ≤ b →
  ∀ ν : ℝ, ∀ (hν : 0 < ν), ∀ hF : PerFrameFacts κ ν m b K,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
        ∀ (F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m)
          (A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m),
          IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
          IsDampedComplBlockInt κ P ν m tr t₁ B A_rel →
          ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
            HasZeroCirculation (ν ^ (-2 : ℝ)) f →
            let F := periodizedFrame κ ν m b K hν hF
            ∃ Y G : ℝ → Planar.L2w m,
              (∀ τ ∈ Icc (0 : ℝ) B, ⇑(Y τ) =ᵐ[volume] fun z : ℂ =>
                ((clockN P ν t₁ (ageAt ν t₁ τ) : ℝ) : ℂ)⁻¹ *
                  cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))
                    (compl F w (ageAt ν t₁ τ)) (cToPlane z)) ∧
              (∀ σ ∈ Icc (0 : ℝ) B, ⇑(G σ) =ᵐ[volume] fun z : ℂ =>
                ((clockN P ν t₁ (ageAt ν t₁ σ) : ℝ) : ℂ)⁻¹ *
                  cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
                    (fun y => ∑ j : Fin 2, ampl F w (ageAt ν t₁ σ) j *
                      complModeForce κ P F tr (ageAt ν t₁ σ) j y) (cToPlane z)) ∧
              AEStronglyMeasurable Y (volume.restrict (Icc (0 : ℝ) B)) ∧
              (∃ C : ℝ, ∀ τ ∈ Icc (0 : ℝ) B, ‖Y τ‖ ≤ C) ∧
              IntegrableOn G (Icc (0 : ℝ) B) ∧
              (∀ τ ∈ Icc (0 : ℝ) B,
                Y τ = F_rel τ 0 (Y 0) +
                  ∫ σ in (0 : ℝ)..τ, F_rel τ σ (A_rel σ (Y σ) + G σ)) ∧
              AEStronglyMeasurable (compl F w t₁)
                (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m) ∧
              AEStronglyMeasurable (compl F w t₂)
                (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m) ∧
              ∀ r ∈ Icc t₁ t₂, ∀ j : Fin 2,
                AEStronglyMeasurable (complModeForce κ P F tr r j)
                  (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m)

/-! ## Bookkeeping lemmas -/

/-- `movingZ ν` is injective on `[0, ∞)`. -/
theorem movingZ_inj {ν r r' : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (h : movingZ ν r = movingZ ν r') : r = r' := by
  rw [← FrameStableSub.moveAgeOfZ_movingZ hν hr, ← FrameStableSub.moveAgeOfZ_movingZ hν hr', h]

/-- Zero-extension isometry with a positive scalar normaliser. -/
theorem ofReal_mul_norm_eq_xNorm {m d N : ℝ} (hN : 0 < N) {V : ℝ × ℝ → ℂ}
    (hV : AEStronglyMeasurable V (B0579.cellMeasure d m)) (Y : Planar.L2w m)
    (hY : ⇑Y =ᵐ[volume] fun z : ℂ => ((N : ℝ) : ℂ)⁻¹ * cellZeroExt d V (cToPlane z)) :
    ENNReal.ofReal N * ENNReal.ofReal ‖Y‖ = xNorm d m V := by
  have hac : Planar.wMeasure m ≪ (volume : Measure ℂ) := by
    unfold Planar.wMeasure
    exact withDensity_absolutelyContinuous _ _
  have hNc : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hW : ((((N : ℝ) : ℂ) • Y : Planar.L2w m) : ℂ → ℂ) =ᵐ[Planar.wMeasure m]
      fun z => cellZeroExt d V (cToPlane z) := by
    filter_upwards [Lp.coeFn_smul ((N : ℝ) : ℂ) Y, hac.ae_le hY] with z h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hNc, one_mul]
  rw [← ofReal_norm_eq_xNorm_of_ae_cellZeroExt hV _ hW, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg hN.le, ENNReal.ofReal_mul hN.le]

/-- Norm of the variation-of-constants right-hand side. -/
theorem ofReal_norm_voc_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (T₀ : H →L[ℂ] H) (T : ℝ → H →L[ℂ] H) (y₀ : H) (G : ℝ → H) {B : ℝ}
    (hB : 0 ≤ B) :
    ENNReal.ofReal ‖T₀ y₀ + ∫ σ in (0 : ℝ)..B, T σ (G σ)‖ ≤
      ENNReal.ofReal ‖T₀‖ * ENNReal.ofReal ‖y₀‖ +
        ∫⁻ σ in Ioc (0 : ℝ) B, ENNReal.ofReal ‖T σ‖ * ENNReal.ofReal ‖G σ‖ := by
  rw [intervalIntegral.integral_of_le hB]
  calc ENNReal.ofReal ‖T₀ y₀ + ∫ σ in Ioc (0 : ℝ) B, T σ (G σ)‖
      ≤ ENNReal.ofReal ‖T₀ y₀‖ + ENNReal.ofReal ‖∫ σ in Ioc (0 : ℝ) B, T σ (G σ)‖ := by
        rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ ≤ _ := by
        refine add_le_add ?_ ?_
        · rw [← ENNReal.ofReal_mul (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (T₀.le_opNorm y₀)
        · rw [ofReal_norm]
          refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun σ => ?_)
          rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal ((T σ).le_opNorm (G σ))

/-- Change of variables `σ = movingZ ν r - movingZ ν t₁` on a block of moving length `B`. -/
theorem lintegral_Ioc_block_eq {ν t₁ t₂ B : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂)
    (hB : movingZ ν t₂ - movingZ ν t₁ = B) (g : ℝ → ℝ≥0∞) :
    ∫⁻ σ in Ioc (0 : ℝ) B, g σ =
      ∫⁻ r in Ioc t₁ t₂, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
        g (movingZ ν r - movingZ ν t₁) := by
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  have hinj : InjOn (fun r => movingZ ν r - movingZ ν t₁) (Ioc t₁ t₂) := by
    intro r hr r' hr' h
    exact movingZ_inj hν (ht₁.trans hr.1.le) (ht₁.trans hr'.1.le) (by simpa using h)
  have himage : (fun r => movingZ ν r - movingZ ν t₁) '' Ioc t₁ t₂ = Ioc 0 B := by
    ext σ
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hmem := movingZ_sub_mem_Icc hν ht₁ ⟨hr.1.le, hr.2⟩
      rw [hB] at hmem
      refine ⟨lt_of_le_of_ne hmem.1 fun h0 => ?_, hmem.2⟩
      have := movingZ_inj hν ht₁ (ht₁.trans hr.1.le) (by linarith)
      linarith [hr.1]
    · rintro ⟨hσ0, hσB⟩
      have hmem := ageAt_mem_Icc hν ht₁ h12 hB ⟨hσ0.le, hσB⟩
      have hz := movingZ_ageAt_sub hν ht₂ hB hσB
      refine ⟨ageAt ν t₁ σ, ⟨lt_of_le_of_ne hmem.1 fun heq => ?_, hmem.2⟩, hz⟩
      rw [← heq, sub_self] at hz
      linarith
  have hderiv : ∀ r ∈ Ioc t₁ t₂, HasDerivWithinAt (fun r => movingZ ν r - movingZ ν t₁)
      ((clockA ν r) ^ (-2 : ℝ)) (Ioc t₁ t₂) r :=
    fun r hr => (hasDerivAt_movingZ_sub t₁ hν (ht₁.trans hr.1.le)).hasDerivWithinAt
  rw [← himage, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioc hderiv hinj g]
  refine setLIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  have hr0 : 0 ≤ r := ht₁.trans hr.1.le
  have ha : 0 ≤ clockA ν r := by unfold clockA; positivity
  rw [abs_of_nonneg (Real.rpow_nonneg ha _)]

/-! ## Assembly -/

/-- **Assembly**: the three leaves give `ComplBlockDuhamelSplit κ` (zero sorry). -/
theorem complBlockDuhamelSplit_of_mild (κ : PlanarFrameKernels)
    (hVoC : DuhamelVoCAbstract) (hReg : RelBlockRegularity κ) (hMild : ComplMovingMild κ) :
    ComplBlockDuhamelSplit κ := by
  intro hκ P hP m hm K B b hB hb1 ν hν hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
    F_rel A_rel U_rel hF_rel hA_rel hDuh f w u hFlow hCirc
  dsimp only
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  obtain ⟨hFc, hAm, hAb⟩ := hReg hκ P hP m hm K B b hB hb1 ν hν hF tr htr t₁ t₂ ht₁ h12 hbt₂
    hB_eq F_rel A_rel hF_rel hA_rel
  obtain ⟨Y, G, hYrep, hGrep, hYm, hYb, hGi, hYmild, hc₁, hc₂, hcmf⟩ :=
    hMild hκ P hP m hm K B b hB hb1 ν hν hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
      F_rel A_rel hF_rel hA_rel f w u hFlow hCirc
  have hid := hVoC (Planar.L2w m) B F_rel A_rel U_rel hB hDuh hFc hAm hAb Y G hYm hYb hGi
    hYmild
  have hN₁₂ : 0 < clockN P ν t₁ t₂ := clockN_pos P hν ht₁ ht₂
  -- terminal complement
  have hA :
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₂)) m
          (compl (periodizedFrame κ ν m b K hν hF) w t₂) =
        ENNReal.ofReal (clockN P ν t₁ t₂) * ENNReal.ofReal ‖Y B‖ := by
    have hrep := hYrep B ⟨hB.le, le_rfl⟩
    rw [ageAt_eq_of_movingZ_sub hν ht₂ hB_eq] at hrep
    exact (ofReal_mul_norm_eq_xNorm hN₁₂ hc₂ (Y B) hrep).symm
  -- entrance complement
  have hB0 : ENNReal.ofReal ‖Y 0‖ =
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m
        (compl (periodizedFrame κ ν m b K hν hF) w t₁) := by
    have hrep := hYrep 0 ⟨le_rfl, hB.le⟩
    rw [ageAt_zero hν ht₁, clockN_self P hν ht₁] at hrep
    have h1 := ofReal_mul_norm_eq_xNorm one_pos hc₁ (Y 0) hrep
    rwa [ENNReal.ofReal_one, one_mul] at h1
  -- forcing
  have hC : ∀ σ ∈ Ioc (0 : ℝ) B,
      ENNReal.ofReal ‖G σ‖ ≤ ENNReal.ofReal ((clockN P ν t₁ (ageAt ν t₁ σ))⁻¹) *
        ∑ j : Fin 2, ENNReal.ofReal ‖ampl (periodizedFrame κ ν m b K hν hF) w (ageAt ν t₁ σ) j‖ *
          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) m
            (complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr (ageAt ν t₁ σ) j) := by
    intro σ hσ
    have hs : ageAt ν t₁ σ ∈ Icc t₁ t₂ := ageAt_mem_Icc hν ht₁ h12 hB_eq ⟨hσ.1.le, hσ.2⟩
    have hrep := hGrep σ ⟨hσ.1.le, hσ.2⟩
    generalize ageAt ν t₁ σ = s at hs hrep ⊢
    have hs0 : 0 ≤ s := ht₁.trans hs.1
    have hNs : 0 < clockN P ν t₁ s := clockN_pos P hν ht₁ hs0
    set F := periodizedFrame κ ν m b K hν hF
    set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν s)
    have hmeas : ∀ j : Fin 2, AEStronglyMeasurable
        (fun y => ampl F w s j * complModeForce κ P F tr s j y) (B0579.cellMeasure d m) :=
      fun j => (hcmf s hs j).const_mul _
    have hV : AEStronglyMeasurable
        (fun y => ∑ j : Fin 2, ampl F w s j * complModeForce κ P F tr s j y)
        (B0579.cellMeasure d m) := by
      simp only [Fin.sum_univ_two]
      exact (hmeas 0).add (hmeas 1)
    have heq := ofReal_mul_norm_eq_xNorm hNs hV (G σ) hrep
    have htri : xNorm d m (fun y => ∑ j : Fin 2, ampl F w s j * complModeForce κ P F tr s j y) ≤
        ∑ j : Fin 2, ENNReal.ofReal ‖ampl F w s j‖ * xNorm d m (complModeForce κ P F tr s j) := by
      have h0 := xNorm_smul_complModeForce κ P F tr d s 0 (ampl F w s 0)
      have h1 := xNorm_smul_complModeForce κ P F tr d s 1 (ampl F w s 1)
      simp only [Fin.sum_univ_two]
      rw [← h0, ← h1]
      exact eLpNorm_add_le (hmeas 0) (hmeas 1) (by norm_num)
    have hone : ENNReal.ofReal (clockN P ν t₁ s)⁻¹ * ENNReal.ofReal (clockN P ν t₁ s) = 1 := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 hNs.le), inv_mul_cancel₀ hNs.ne',
        ENNReal.ofReal_one]
    calc ENNReal.ofReal ‖G σ‖
        = ENNReal.ofReal (clockN P ν t₁ s)⁻¹ *
            (ENNReal.ofReal (clockN P ν t₁ s) * ENNReal.ofReal ‖G σ‖) := by
          rw [← mul_assoc, hone, one_mul]
      _ ≤ _ := by
          rw [heq]
          gcongr
  refine ⟨ENNReal.ofReal (clockN P ν t₁ t₂) *
      (ENNReal.ofReal ‖U_rel B 0‖ * ENNReal.ofReal ‖Y 0‖),
    fun r => ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
      (ENNReal.ofReal ‖U_rel B (movingZ ν r - movingZ ν t₁)‖ *
        ENNReal.ofReal ‖G (movingZ ν r - movingZ ν t₁)‖)), ?_, ?_, ?_⟩
  · have hcv := lintegral_Ioc_block_eq hν ht₁ h12 hB_eq
      (fun σ => ENNReal.ofReal ‖U_rel B σ‖ * ENNReal.ofReal ‖G σ‖)
    rw [hA, hid, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hcv, ← mul_add]
    gcongr
    exact ofReal_norm_voc_le _ _ _ _ hB.le
  · rw [hB0, ← mul_assoc, ← ENNReal.ofReal_mul hN₁₂.le]
  · intro r hr
    have hr0 : 0 ≤ r := ht₁.trans hr.1.le
    have hmem := movingZ_sub_mem_Icc hν ht₁ ⟨hr.1.le, hr.2⟩
    rw [hB_eq] at hmem
    have hσ : movingZ ν r - movingZ ν t₁ ∈ Ioc (0 : ℝ) B := by
      refine ⟨lt_of_le_of_ne hmem.1 fun h0 => ?_, hmem.2⟩
      have := movingZ_inj hν ht₁ hr0 (by linarith)
      linarith [hr.1]
    have hGr := hC _ hσ
    rw [ageAt_movingZ_sub hν hr0] at hGr
    have hNr : 0 < clockN P ν t₁ r := clockN_pos P hν ht₁ hr0
    have hkey : (clockN P ν t₁ r)⁻¹ * clockN P ν t₁ t₂ = clockN P ν r t₂ :=
      clockN_inv_mul_clockN P hν ht₁ hr0 ht₂
    have ha : 0 ≤ (clockA ν r) ^ (-2 : ℝ) :=
      Real.rpow_nonneg (by unfold clockA; positivity) _
    have hNr₂ : 0 ≤ clockN P ν r t₂ := (clockN_pos P hν hr0 ht₂).le
    calc ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
          (ENNReal.ofReal ‖U_rel B (movingZ ν r - movingZ ν t₁)‖ *
            ENNReal.ofReal ‖G (movingZ ν r - movingZ ν t₁)‖))
        ≤ ENNReal.ofReal (clockN P ν t₁ t₂) * (ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
          (ENNReal.ofReal ‖U_rel B (movingZ ν r - movingZ ν t₁)‖ *
            (ENNReal.ofReal ((clockN P ν t₁ r)⁻¹) *
              ∑ j : Fin 2, ENNReal.ofReal ‖ampl (periodizedFrame κ ν m b K hν hF) w r j‖ *
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                  (complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j)))) := by
          gcongr
      _ = ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) *
            (clockN P ν r t₂ * ‖U_rel B (movingZ ν r - movingZ ν t₁)‖)) *
            ∑ j : Fin 2, ENNReal.ofReal ‖ampl (periodizedFrame κ ν m b K hν hF) w r j‖ *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                (complModeForce κ P (periodizedFrame κ ν m b K hν hF) tr r j) := by
          rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hNr₂, ← hkey,
            ENNReal.ofReal_mul (inv_nonneg.2 hNr.le)]
          ring

/-- **Assembly of `ComplBlockDuhamelVoC κ`** from the three leaves (zero sorry). -/
theorem complBlockDuhamelVoC_of_mild (κ : PlanarFrameKernels)
    (hVoC : DuhamelVoCAbstract) (hReg : RelBlockRegularity κ) (hMild : ComplMovingMild κ) :
    ComplBlockDuhamelVoC κ :=
  complBlockDuhamelVoC_of κ (complBlockDuhamelSplit_of_mild κ hVoC hReg hMild)

end VariationOfConstantsMildSub

end UnforcedLeray.Short.IIIa
