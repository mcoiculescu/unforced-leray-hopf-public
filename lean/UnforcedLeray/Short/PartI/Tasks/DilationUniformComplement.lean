import UnforcedLeray.Short.PartI.StatementsSeed
import UnforcedLeray.Short.PartI.Tasks.EulerComplementJ0.SectorOne
import UnforcedLeray.Short.PartI.Tasks.EulerComplementJ0.GrowProjAgree
import UnforcedLeray.Lib.PlanarSectorsB.Dilation
import UnforcedLeray.Lib.PlanarSpectralB.Complement
import UnforcedLeray.Lib.Semigroups.Dunford.Defs

/-!
# Part I, task `PartI:S17`: `seedDilation_uniform_complement`

Source of record: `the November 2 reference manuscript`
lines 931-953 (frozen heat profiles; uniform complementary estimates for `1 ≤ a ≤ A`).

Statement: the projection `P` of the growing pair (the first conjunct of `SeedDilationProjection`,
`StatementsSeed.lean` line 241) together with the uniform bound
`‖e^{t𝓛_a}(1 - J_a P J_a⁻¹)‖ ≤ C e^{ηt}` for `1 ≤ a ≤ A`.

Proof: `P` is the growing projection of the growing pair from `seedGrowProjAgree`; the unscaled bound
is `eulerSemigroup_complement_bound`; conjugation `dilation_conj_X0` with `J_a⁻¹ J_a = 1` gives
`e^{t𝓛_a}(1 - P_a) = J_a e^{(t/a²)𝓛}(1 - P) J_a⁻¹`, and `‖J_a‖‖J_a⁻¹‖ ≤ A^{M/2}` on `[1,A]`
(`dilConst_mul_inv_le`), while `t/a² ≤ t`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ComplexConjugate ContDiff Topology

open UnforcedLeray.Infra.Dunford (rankOneProj)

namespace UnforcedLeray.Short.PartI

/-- Algebra: `J S J⁻¹ (1 - J Q J⁻¹) = J S (1 - Q) J⁻¹` when `J⁻¹ J = 1`. -/
theorem dilation_conj_complement_alg {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (J Ji S Q : X →L[ℂ] X) (hJ : Ji * J = 1) :
    J * S * Ji * (1 - J * (Q * Ji)) = J * (S * (1 - Q)) * Ji := by
  calc J * S * Ji * (1 - J * (Q * Ji)) = J * S * Ji - J * S * (Ji * J) * Q * Ji := by
        simp only [mul_sub, mul_one, mul_assoc]
    _ = J * S * Ji - J * S * Q * Ji := by
        rw [hJ]
        simp only [mul_one]
    _ = J * (S * (1 - Q)) * Ji := by
        simp only [mul_sub, sub_mul, mul_one, mul_assoc]

/-- Uniform bound, given the unscaled complement bound for the projection `P`. -/
theorem dilation_uniform_of_bound {M : ℝ} (hM : 1 < M) (P : Planar.X0 hM →L[ℂ] Planar.X0 hM)
    (A : ℝ) (hA1 : 1 ≤ A) (η : ℝ) (hη : 0 < η) (C : ℝ) (hC : 0 < C)
    (hCb : ∀ t : ℝ, 0 ≤ t →
      ‖Planar.eulerSemigroup hM t ∘L (1 - P)‖ ≤ C * Real.exp (η * t)) :
    ∀ (a : ℝ) (ha : 0 < a), 1 ≤ a → a ≤ A → ∀ t : ℝ, 0 ≤ t →
      ‖Planar.eulerSemigroupDil hM ha t ∘L
          (1 - Planar.dilX0 hM ha ∘L P ∘L Planar.dilX0 hM (inv_pos.2 ha))‖ ≤
        A ^ (M / 2) * C * Real.exp (η * t) := by
  intro a ha ha1 haA t ht
  simp only [← ContinuousLinearMap.mul_def] at hCb ⊢
  have hJ : Planar.dilX0 hM (inv_pos.2 ha) * Planar.dilX0 hM ha = 1 := by
    ext1 f
    apply Subtype.ext
    show (Planar.dilW hM (inv_pos.2 ha) ∘L Planar.dilW hM ha) f = f
    rw [Planar.dilW_inv_comp]
    rfl
  have hdc : Planar.eulerSemigroupDil hM ha t =
      Planar.dilX0 hM ha * Planar.eulerSemigroup hM (t / a ^ 2) *
        Planar.dilX0 hM (inv_pos.2 ha) := by
    rw [Planar.dilation_conj_X0]
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
  have hdiv : t / a ^ 2 ≤ t := div_le_self ht (one_le_pow₀ ha1)
  have hSb : ‖Planar.eulerSemigroup hM (t / a ^ 2) * (1 - P)‖ ≤ C * Real.exp (η * t) := by
    refine le_trans (hCb (t / a ^ 2) (div_nonneg ht (sq_nonneg a))) ?_
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hdiv hη.le))
      hC.le
  have hJn : ‖Planar.dilX0 hM ha‖ ≤ Planar.dilConst M a := Planar.norm_dilX0_le hM ha
  have hJin : ‖Planar.dilX0 hM (inv_pos.2 ha)‖ ≤ Planar.dilConst M a⁻¹ :=
    Planar.norm_dilX0_le hM (inv_pos.2 ha)
  have hmul := Planar.dilConst_mul_inv_le hM ha1 haA
  have hn : ∀ (X Y : Planar.X0 hM →L[ℂ] Planar.X0 hM), ‖X * Y‖ ≤ ‖X‖ * ‖Y‖ :=
    fun X Y => ContinuousLinearMap.opNorm_comp_le X Y
  have hCe : 0 ≤ C * Real.exp (η * t) := mul_nonneg hC.le (Real.exp_pos _).le
  have hB : 0 ≤ Planar.dilConst M a * (C * Real.exp (η * t)) :=
    mul_nonneg (Planar.dilConst_nonneg M a) hCe
  have hX : ‖Planar.dilX0 hM ha * (Planar.eulerSemigroup hM (t / a ^ 2) * (1 - P))‖ ≤
      Planar.dilConst M a * (C * Real.exp (η * t)) :=
    (hn _ _).trans (mul_le_mul hJn hSb (ContinuousLinearMap.opNorm_nonneg _)
      (Planar.dilConst_nonneg M a))
  have hfin : ‖Planar.dilX0 hM ha * (Planar.eulerSemigroup hM (t / a ^ 2) * (1 - P)) *
      Planar.dilX0 hM (inv_pos.2 ha)‖ ≤
        (Planar.dilConst M a * (C * Real.exp (η * t))) * Planar.dilConst M a⁻¹ :=
    (hn _ _).trans (mul_le_mul hX hJin (ContinuousLinearMap.opNorm_nonneg _) hB)
  rw [hdc, dilation_conj_complement_alg _ _ _ _ hJ]
  calc ‖Planar.dilX0 hM ha * (Planar.eulerSemigroup hM (t / a ^ 2) * (1 - P)) *
          Planar.dilX0 hM (inv_pos.2 ha)‖
      ≤ (Planar.dilConst M a * (C * Real.exp (η * t))) * Planar.dilConst M a⁻¹ := hfin
    _ = (Planar.dilConst M a * Planar.dilConst M a⁻¹) * (C * Real.exp (η * t)) := by ring
    _ ≤ A ^ (M / 2) * (C * Real.exp (η * t)) :=
        mul_le_mul_of_nonneg_right hmul hCe
    _ = A ^ (M / 2) * C * Real.exp (η * t) := by ring

theorem seedDilation_uniform_complement :
    ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
      IsSeedXG lam (hh.toLp h) ℓ → ∀ (M : ℝ) (hM : 1 < M) (A : ℝ), 1 ≤ A →
      ∃ P : Planar.X0 hM →L[ℂ] Planar.X0 hM,
        (∀ f : Planar.X0 hM, ⇑((P f : Planar.X0 hM) : Planar.L2w M) =ᵐ[volume]
          fun y => seedProjFun h (⇑((f : Planar.X0 hM) : Planar.L2w M)) y) ∧
        ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (ha : 0 < a), 1 ≤ a → a ≤ A →
          ∀ t : ℝ, 0 ≤ t →
            ‖Planar.eulerSemigroupDil hM ha t ∘L
                (1 - Planar.dilX0 hM ha ∘L P ∘L Planar.dilX0 hM (inv_pos.2 ha))‖ ≤
              C * Real.exp (η * t) := by
  intro lam h hh ℓ hs M hM A hA1
  obtain ⟨q', hq0, hq, hAg⟩ := seedGrowProjAgree lam h hh ℓ hs M hM
  obtain ⟨ℓ₂, ℓm, h2, hm, hP2, hPm, hbound⟩ :=
    Planar.eulerSemigroup_complement_bound hM (sectorOneStableAll M hM) hs.re_pos hq0 hq
  refine ⟨Planar.growingProj hM (rankOneProj ℓ₂ q') (rankOneProj ℓm (star q')), ?_, ?_⟩
  · intro f
    exact hAg ℓ₂ ℓm h2 hm hP2 hPm f (⇑((f : Planar.X0 hM) : Planar.L2w M))
      (Filter.EventuallyEq.refl _ _)
  · intro η hη
    obtain ⟨C, hC, hCb⟩ := hbound η hη
    refine ⟨A ^ (M / 2) * C, mul_pos (Real.rpow_pos_of_pos (by linarith) _) hC, ?_⟩
    exact dilation_uniform_of_bound hM _ A hA1 η hη C hC hCb

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.seedDilation_uniform_complement
