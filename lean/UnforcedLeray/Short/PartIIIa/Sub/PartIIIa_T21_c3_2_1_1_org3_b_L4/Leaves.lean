import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b0
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_2_2
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Leaf B4 (`PlanarDampedIntLimit`): the two convergence leaves and the assembly

Source: `the November 2 reference manuscript` (SP) 2898-2925, 2974-2978.

`A_rel(τ)` acts on smooth compactly supported `Φ` as the cell zero extension of
`movLInt + movFrameRankPert` (`eq:short-causal-damped-complement`), `A0` as
`couplingW + Σ_i (γ - 1 - λ_i) ℓ_i(·) e_i`. The difference splits into

* `IntLimitLeaf`: the localized Biot–Savart interaction `-(K_d W)·∇E_mov(r)` (zero extended from
  the cell) converges to `couplingW = -(K W)·∇E₀` (SP 2974-2976: image estimates, cell truncation);
* `RankLimitLeaf`: the finite-rank terms `-E H₀ + [-K₀ + (β₀ - 1)E + E M₀]Λ` converge to
  `Σ_i (γ - 1 - λ_i) ℓ_i(·) e_i` (SP 2898-2925: `E → e`, `Λ → ℓ`, `H₀ → λΛ`, `K₀ → λE`,
  `M₀ → diag λ`, `β₀ → γ`),

both with an error `ε ‖W‖` uniform in the successive limit. `planarDampedIntLimit_of` assembles
them: the two bounds hold on the dense class of smooth compactly supported fields
(`Lp.dense_hasCompactSupport_contDiff`), hence in operator norm.
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

namespace PlanarB

namespace L4

/-- **Interaction leaf** (SP 2974-2976): in the successive limit, uniformly in the train and the
age, the cell zero extension of the localized interaction `movLInt tr r Φ = -(K_{d(r)}Φ)·∇E_mov(r)`
is `ε ‖W‖`-close in `L²_m` to the planar coupling `couplingW W = -(K W)·∇E₀`, for every smooth
compactly supported `Φ` representing `W`. -/
def IntLimitLeaf : Prop :=
  ∀ (m : ℝ) (hm : 1 < m), 8 < m → ∀ ε : ℝ, 0 < ε →
  ∃ b₁ : ℝ, ∀ b : ℝ, b₁ ≤ b → ∃ ν₁ : ℝ, 0 < ν₁ ∧
    ∀ ν ∈ Ioc 0 ν₁, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ r : ℝ, 0 ≤ r → b ≤ clockTheta ν r →
    ∀ Φ : ℝ × ℝ → ℂ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
    ∀ W : Planar.L2w m, (⇑W =ᵐ[volume] fun z => Φ (cToPlane z)) →
      AEStronglyMeasurable (fun z => cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
        (movLInt tr r Φ) (cToPlane z)) (Planar.wMeasure m) ∧
      eLpNorm (fun z => cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
          (movLInt tr r Φ) (cToPlane z) - Planar.couplingW hm W z) 2 (Planar.wMeasure m) ≤
        ENNReal.ofReal (ε * ‖W‖)

/-- **Finite-rank leaf** (SP 2898-2925): in the successive limit, uniformly in the train and the
age, the cell zero extension of the finite-rank part `movFrameRankPert` of the damped complement
generator is `ε ‖W‖`-close in `L²_m` to `Σ_i (γ - 1 - λ_i) ℓ_i(Φ) e_i`, `γ = Re λ`,
`λ_i = modeEigen P i`, `ℓ_i(Φ) = ∫ λ_i Φ`. -/
def RankLimitLeaf (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ → ∀ (P : PlanarData), IsPlanarReference P →
  ∀ m : ℝ, 8 < m → ∀ K ε : ℝ, 0 < ε →
  ∃ b₁ : ℝ, ∀ b : ℝ, b₁ ≤ b → ∃ ν₁ : ℝ, 0 < ν₁ ∧
    ∀ ν ∈ Ioc 0 ν₁, PerFrameFacts κ ν m b K →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ r : ℝ, 0 ≤ r → b ≤ clockTheta ν r →
    ∀ Φ : ℝ × ℝ → ℂ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
    ∀ W : Planar.L2w m, (⇑W =ᵐ[volume] fun z => Φ (cToPlane z)) →
      eLpNorm (fun z => cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
          (movFrameRankPert κ P tr r Φ) (cToPlane z) -
          ∑ i : Fin 2, (((P.eigenvalue.re - 1 : ℝ) : ℂ) - modeEigen P i) *
            (∫ y, κ.lamP i y * Φ y) * κ.e i (cToPlane z)) 2 (Planar.wMeasure m) ≤
        ENNReal.ofReal (ε * ‖W‖)

/-! ## Density of the smooth class and the operator-norm bound -/

theorem planeToC_eq_clm : (planeToC : ℝ × ℝ → ℂ) = ⇑Complex.equivRealProdCLM.symm := by
  funext y
  apply Complex.ext <;> simp [planeToC]

theorem contDiff_planeToC' : ContDiff ℝ ∞ planeToC := by
  rw [planeToC_eq_clm]
  exact Complex.equivRealProdCLM.symm.contDiff

theorem hasCompactSupport_comp_planeToC {g : ℂ → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (fun y : ℝ × ℝ => g (planeToC y)) := by
  have h := hg.comp_homeomorph Complex.equivRealProdCLM.symm.toHomeomorph
  have he : (fun y : ℝ × ℝ => g (planeToC y)) =
      g ∘ ⇑Complex.equivRealProdCLM.symm.toHomeomorph := by
    funext y
    simp only [Function.comp_apply, ContinuousLinearEquiv.coe_toHomeomorph]
    rw [planeToC_eq_clm]
  rw [he]
  exact h

/-- A bound `‖T W‖ ≤ c ‖W‖` on the smooth compactly supported class gives `‖T‖ ≤ c`. -/
theorem opNorm_le_of_smooth {m : ℝ} (T : Planar.L2w m →L[ℂ] Planar.L2w m) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ W : Planar.L2w m, (∃ g : ℂ → ℂ, W =ᵐ[Planar.wMeasure m] g ∧ HasCompactSupport g ∧
      ContDiff ℝ ∞ g) → ‖T W‖ ≤ c * ‖W‖) :
    ‖T‖ ≤ c := by
  have : IsLocallyFiniteMeasure (Planar.wMeasure m) :=
    inferInstanceAs (IsLocallyFiniteMeasure (B0008.wMeasure m))
  have hd := MeasureTheory.Lp.dense_hasCompactSupport_contDiff (E := ℂ) (F := ℂ) (p := 2)
    (μ := Planar.wMeasure m) (by norm_num)
  have hcl : IsClosed {W : Planar.L2w m | ‖T W‖ ≤ c * ‖W‖} :=
    isClosed_le (continuous_norm.comp T.continuous) (continuous_const.mul continuous_norm)
  have hsub : {f : Planar.L2w m | ∃ g : ℂ → ℂ, f =ᵐ[Planar.wMeasure m] g ∧
      HasCompactSupport g ∧ ContDiff ℝ ∞ g} ⊆ {W : Planar.L2w m | ‖T W‖ ≤ c * ‖W‖} :=
    fun W hW => h W hW
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun W => ?_
  have hW : W ∈ closure {f : Planar.L2w m | ∃ g : ℂ → ℂ, f =ᵐ[Planar.wMeasure m] g ∧
      HasCompactSupport g ∧ ContDiff ℝ ∞ g} := by
    rw [hd.closure_eq]; exact mem_univ W
  exact closure_minimal hsub hcl hW

theorem theta_anti_L4 {ν r s : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (hrs : r ≤ s) :
    clockTheta ν s ≤ clockTheta ν r := by
  unfold clockTheta clockA
  have h1 : 0 < ν * (1 + ν * r) := mul_pos hν (by nlinarith)
  apply inv_anti₀ h1
  nlinarith [mul_le_mul_of_nonneg_left hrs hν.le]

theorem cellZeroExt_movDampedComplInt (κ : PlanarFrameKernels) (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (r d : ℝ) (Φ : ℝ × ℝ → ℂ)
    (y : ℝ × ℝ) :
    cellZeroExt d (movDampedComplInt κ P tr r Φ) y =
      cellZeroExt d (movLInt tr r Φ) y + cellZeroExt d (movFrameRankPert κ P tr r Φ) y := by
  unfold cellZeroExt
  by_cases hy : y ∈ B0579.cell d
  · simp only [Set.indicator_of_mem hy, movDampedComplInt]
  · simp only [Set.indicator_of_notMem hy, add_zero]

/-- **Assembly** of `PlanarDampedIntLimit κ` from the interaction and finite-rank leaves. -/
theorem planarDampedIntLimit_of (κ : PlanarFrameKernels) (hI : IntLimitLeaf)
    (hR : RankLimitLeaf κ) : PlanarDampedIntLimit κ := by
  intro hκ P hP m hm1 hm A0 hA0 K B ε hB hε
  obtain ⟨lam, h_prof, hh, ℓ, hIS, _he0, hform⟩ := hA0
  have hlam : P.eigenvalue = lam := DirectEulerSub.planar_eigenvalue_eq_seed P hP hIS
  obtain ⟨bI, hbI⟩ := hI m hm1 hm (ε / 4) (by positivity)
  obtain ⟨bR, hbR⟩ := hR hκ P hP m hm K (ε / 4) (by positivity)
  refine ⟨max 1 (max bI bR), le_max_left _ _, fun b hb => ?_⟩
  obtain ⟨νI, hνI, hI'⟩ := hbI b (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hb)
  obtain ⟨νR, hνR, hR'⟩ := hbR b (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hb)
  refine ⟨min νI νR, lt_min hνI hνR,
    fun ν hν hF tr htr t₁ t₂ ht₁ h12 hbt₂ hBdef A_rel hA τ hτ => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hνI' : ν ∈ Ioc 0 νI := ⟨hν0, hν.2.trans (min_le_left _ _)⟩
  have hνR' : ν ∈ Ioc 0 νR := ⟨hν0, hν.2.trans (min_le_right _ _)⟩
  have hrI := VariationOfConstantsSub.ageAt_mem_Icc hν0 ht₁ h12 hBdef hτ
  have hr0 : 0 ≤ ageAt ν t₁ τ := ht₁.trans hrI.1
  have hθ : b ≤ clockTheta ν (ageAt ν t₁ τ) := hbt₂.trans (theta_anti_L4 hν0 hr0 hrI.2)
  have hAτ := hA τ hτ
  set r := ageAt ν t₁ τ with hr
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r) with hd
  have hε2 : 0 ≤ ε / 2 := by positivity
  have key : ∀ W : Planar.L2w m, (∃ g : ℂ → ℂ, W =ᵐ[Planar.wMeasure m] g ∧
      HasCompactSupport g ∧ ContDiff ℝ ∞ g) → ‖(A_rel τ - A0) W‖ ≤ ε / 2 * ‖W‖ := by
    rintro W ⟨g, hWg, hgc, hgs⟩
    set Φ : ℝ × ℝ → ℂ := fun y => g (planeToC y) with hΦ
    have hΦs : ContDiff ℝ ∞ Φ := hgs.comp contDiff_planeToC'
    have hΦc : HasCompactSupport Φ := hasCompactSupport_comp_planeToC hgc
    have hΦg : (fun z : ℂ => Φ (cToPlane z)) = g := by
      funext z; simp [hΦ]
    have hWv : ⇑W =ᵐ[volume] g := (Planar.volume_ac m).ae_le hWg
    have hWΦ : ⇑W =ᵐ[volume] fun z => Φ (cToPlane z) := by rw [hΦg]; exact hWv
    obtain ⟨hmeasI, hIb⟩ := hI' ν hνI' tr htr r hr0 hθ Φ hΦs hΦc W hWΦ
    have hRb := hR' ν hνR' hF tr htr r hr0 hθ Φ hΦs hΦc W hWΦ
    have hArel := hAτ Φ hΦs hΦc W hWΦ
    have hA0W := hform g hgs hgc W hWv
    -- the pairing and the eigenvalues
    have hpair : ∀ i : Fin 2, planarLamPair κ i g = ∫ y, κ.lamP i y * Φ y := by
      intro i; rfl
    have heig : ∀ i : Fin 2, seedEigen lam i = modeEigen P i := by
      intro i; unfold seedEigen modeEigen; rw [hlam]
    set f₁ : ℂ → ℂ := fun z => cellZeroExt d (movLInt tr r Φ) (cToPlane z) -
      Planar.couplingW hm1 W z with hf₁
    set f₂ : ℂ → ℂ := fun z => cellZeroExt d (movFrameRankPert κ P tr r Φ) (cToPlane z) -
      ∑ i : Fin 2, (((P.eigenvalue.re - 1 : ℝ) : ℂ) - modeEigen P i) *
        (∫ y, κ.lamP i y * Φ y) * κ.e i (cToPlane z) with hf₂
    have hsum : ⇑((A_rel τ - A0) W) =ᵐ[Planar.wMeasure m] fun z => f₁ z + f₂ z := by
      have h1 : ⇑(A_rel τ W) =ᵐ[Planar.wMeasure m]
          fun z => cellZeroExt d (movDampedComplInt κ P tr r Φ) (cToPlane z) :=
        (Planar.wMeasure_ac m).ae_le hArel
      have h2 := (Planar.wMeasure_ac m).ae_le hA0W
      filter_upwards [ContinuousLinearMap.sub_apply (A_rel τ) A0 W ▸
        Lp.coeFn_sub (A_rel τ W) (A0 W), h1, h2] with z hz e1 e2
      rw [hz, Pi.sub_apply, e1, e2, hf₁, hf₂, cellZeroExt_movDampedComplInt]
      simp only [hpair, heig]
      ring
    have hmeas2 : AEStronglyMeasurable f₂ (Planar.wMeasure m) := by
      have hT : AEStronglyMeasurable (fun z => f₁ z + f₂ z) (Planar.wMeasure m) :=
        (Lp.aestronglyMeasurable ((A_rel τ - A0) W)).congr hsum
      have hm1' : AEStronglyMeasurable f₁ (Planar.wMeasure m) :=
        hmeasI.sub (Lp.aestronglyMeasurable (Planar.couplingW hm1 W))
      refine (hT.sub hm1').congr (Eventually.of_forall fun z => ?_)
      simp
    have hmeas1 : AEStronglyMeasurable f₁ (Planar.wMeasure m) :=
      hmeasI.sub (Lp.aestronglyMeasurable (Planar.couplingW hm1 W))
    have hnorm : ENNReal.ofReal ‖(A_rel τ - A0) W‖ ≤ ENNReal.ofReal (ε / 2 * ‖W‖) := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae hsum]
      calc eLpNorm (fun z => f₁ z + f₂ z) 2 (Planar.wMeasure m)
          ≤ eLpNorm f₁ 2 (Planar.wMeasure m) + eLpNorm f₂ 2 (Planar.wMeasure m) :=
            eLpNorm_add_le hmeas1 hmeas2 (by norm_num)
        _ ≤ ENNReal.ofReal (ε / 4 * ‖W‖) + ENNReal.ofReal (ε / 4 * ‖W‖) := add_le_add hIb hRb
        _ = ENNReal.ofReal (ε / 2 * ‖W‖) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; ring
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hnorm
  have hle : ‖A_rel τ - A0‖ ≤ ε / 2 := opNorm_le_of_smooth (A_rel τ - A0) hε2 key
  linarith

end L4

end PlanarB

end OrgSplit3
end BlockPropagatorInteriorSub
end UnforcedLeray.Short.IIIa
