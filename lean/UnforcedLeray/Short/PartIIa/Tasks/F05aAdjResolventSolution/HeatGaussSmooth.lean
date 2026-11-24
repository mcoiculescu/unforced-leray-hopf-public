import UnforcedLeray.Short.PartIIa.Sub.F05_1
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.PhaseTestDerivBounded
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.ParamIntegralSmooth

/-!
# Part II-a, task `PartII-a:F05a`: smoothness and uniform derivative bounds of `heatGauss`

Target: `HeatGaussSmooth` (defined in `Short/PartII-a/Sub/F05_1.lean`).

Source of record: `the November 2 reference manuscript`, lines 1403-1413
(the smooth compact spatial test of the adjoint resolvent).

Proof. `heatGauss Φ₀ w p = ∫ ξ, γ ξ • Φ₀ (p.1, p.2 - w • ξ)` with `γ = Heat.kernel 1`.
Each integrand is `γ ξ • Φ₀ (L ξ q + c ξ)` with `L ξ` linear and `c ξ` constant in `q`.
Differentiation under the integral is `ParamIntegralSmooth`, applied to the family `fam`:
* `iteratedFDeriv_smul_comp`: chain rule (translate of `Φ₀` after a linear map);
* `norm_iteratedFDeriv_smul_comp_le`: `‖D^k‖ ≤ γ ξ * M_k * ‖L ξ‖^k`, with `M_k` from
  `PhaseTestDerivBounded`;
* `continuous_iteratedFDeriv_fam`: continuity in `ξ`, giving measurability;
* `fam_hyp`: integrable majorant `M_k γ ξ (1 + ‖ξ‖)^k` when `‖L ξ‖ ≤ 1 + ‖ξ‖`.
Joint smoothness uses `L ξ (w, (τ, z)) = (τ, z - w • ξ)`. The slices `heatGauss Φ₀ w` are
composites with `p ↦ (w, p)`; their derivative bounds use the translate
`q ↦ Φ₀ (q + (0, -(w • ξ)))`, whose linear part is the identity (`‖L‖ ≤ 1`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

namespace UnforcedLeray.Short.PartIIa

namespace HeatGaussSmoothAux

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The integrand family `ξ ↦ (q ↦ γ ξ • Φ₀ (L ξ q + c ξ))` with `γ = Heat.kernel 1`. -/
def fam (Φ₀ : ℝ × Space → CVec3) (L : Space → E →L[ℝ] (ℝ × Space))
    (c : Space → ℝ × Space) (ξ : Space) (q : E) : CVec3 :=
  UnforcedLeray.Heat.kernel 1 ξ • Φ₀ (L ξ q + c ξ)

/-- Chain rule at a fixed `ξ`: the `k`-th derivative of `q ↦ a • Φ₀ (L q + c)` is the `k`-th
derivative of `Φ₀` at `L q + c`, precomposed with `L`. -/
theorem iteratedFDeriv_smul_comp (Φ₀ : ℝ × Space → CVec3) (hΦ : ContDiff ℝ ∞ Φ₀)
    (c : ℝ × Space) (L : E →L[ℝ] (ℝ × Space)) (a : ℝ) (k : ℕ) (q : E) :
    iteratedFDeriv ℝ k (fun x => a • Φ₀ (L x + c)) q =
      a • (iteratedFDeriv ℝ k Φ₀ (L q + c)).compContinuousLinearMap (fun _ => L) := by
  have hf : ContDiff ℝ ∞ (fun z : ℝ × Space => Φ₀ (z + c)) :=
    hΦ.comp (contDiff_id.add contDiff_const)
  have hg : ContDiff ℝ ∞ ((fun z : ℝ × Space => Φ₀ (z + c)) ∘ L) := hf.comp L.contDiff
  have hgk : ContDiffAt ℝ (k : WithTop ℕ∞) ((fun z : ℝ × Space => Φ₀ (z + c)) ∘ L) q :=
    hg.contDiffAt.of_le (by exact_mod_cast le_top)
  have e1 : (fun x => a • Φ₀ (L x + c)) = a • ((fun z : ℝ × Space => Φ₀ (z + c)) ∘ L) := rfl
  rw [e1, iteratedFDeriv_const_smul_apply hgk,
    L.iteratedFDeriv_comp_right (i := k) hf q (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]

/-- Norm bound for the `k`-th derivative of `q ↦ a • Φ₀ (L q + c)` at `q`. -/
theorem norm_iteratedFDeriv_smul_comp_le (Φ₀ : ℝ × Space → CVec3) (hΦ : ContDiff ℝ ∞ Φ₀)
    (c : ℝ × Space) (L : E →L[ℝ] (ℝ × Space)) (a : ℝ) (k : ℕ) (M : ℝ)
    (hM : ∀ p : ℝ × Space, ‖iteratedFDeriv ℝ k Φ₀ p‖ ≤ M) (q : E) :
    ‖iteratedFDeriv ℝ k (fun x => a • Φ₀ (L x + c)) q‖ ≤ ‖a‖ * (M * ‖L‖ ^ k) := by
  rw [iteratedFDeriv_smul_comp Φ₀ hΦ c L a k q, norm_smul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg a)
  have h1 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k Φ₀ (L q + c)) (fun _ : Fin k => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (hM _) (pow_nonneg (norm_nonneg _) _))

/-- Continuity in `ξ` of the derivatives of the family (measurability for `ParamFamilyHyp`). -/
theorem continuous_iteratedFDeriv_fam (Φ₀ : ℝ × Space → CVec3) (hΦ : ContDiff ℝ ∞ Φ₀)
    {L : Space → E →L[ℝ] (ℝ × Space)} {c : Space → ℝ × Space}
    (hL : Continuous L) (hc : Continuous c) (k : ℕ) (q : E) :
    Continuous (fun ξ => iteratedFDeriv ℝ k (fam Φ₀ L c ξ) q) := by
  have hT : Continuous (iteratedFDeriv ℝ k Φ₀) :=
    hΦ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hS : Continuous (fun ξ => iteratedFDeriv ℝ k Φ₀ (L ξ q + c ξ)) :=
    hT.comp ((hL.clm_apply continuous_const).add hc)
  have hΨ : Continuous (fun ξ =>
      (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
        ℝ (fun _ : Fin k => E) (fun _ : Fin k => ℝ × Space) CVec3) (fun _ => L ξ)) :=
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      ℝ (fun _ : Fin k => E) (fun _ : Fin k => ℝ × Space) CVec3).cont.comp
        (continuous_pi fun _ => hL)
  have hκ : Continuous (fun ξ : Space => UnforcedLeray.Heat.kernel 1 ξ) :=
    UnforcedLeray.Heat.continuous_kernel 1
  have heq : (fun ξ => iteratedFDeriv ℝ k (fam Φ₀ L c ξ) q) =
      fun ξ => UnforcedLeray.Heat.kernel 1 ξ •
        (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
          ℝ (fun _ : Fin k => E) (fun _ : Fin k => ℝ × Space) CVec3) (fun _ => L ξ)
          (iteratedFDeriv ℝ k Φ₀ (L ξ q + c ξ)) := by
    funext ξ
    rw [show fam Φ₀ L c ξ = fun x => UnforcedLeray.Heat.kernel 1 ξ • Φ₀ (L ξ x + c ξ) from rfl,
      iteratedFDeriv_smul_comp Φ₀ hΦ (c ξ) (L ξ) _ k q]
    rfl
  rw [heq]
  exact hκ.smul (hΨ.clm_apply hS)

/-- The hypotheses of `ParamFamilyHyp` for the family `fam Φ₀ L c`: differentiation under the
integral in `q`, integration in `ξ` against `volume`. -/
theorem fam_hyp (Φ₀ : ℝ × Space → CVec3) (hΦ : ContDiff ℝ ∞ Φ₀) (M : ℕ → ℝ)
    (hM0 : ∀ k, 0 ≤ M k) (hM : ∀ (k : ℕ) (p : ℝ × Space), ‖iteratedFDeriv ℝ k Φ₀ p‖ ≤ M k)
    (L : Space → E →L[ℝ] (ℝ × Space)) (c : Space → ℝ × Space)
    (hL : Continuous L) (hc : Continuous c) (hLb : ∀ ξ, ‖L ξ‖ ≤ 1 + ‖ξ‖) :
    ParamFamilyHyp (volume : Measure Space) (fam Φ₀ L c) := by
  have hA : ∀ᵐ ξ ∂(volume : Measure Space), ContDiff ℝ ∞ (fam Φ₀ L c ξ) := by
    refine Filter.Eventually.of_forall fun ξ => ?_
    have hg : ContDiff ℝ ∞ (fun x => Φ₀ (L ξ x + c ξ)) :=
      hΦ.comp ((L ξ).contDiff.add contDiff_const)
    have hf : ContDiff ℝ ∞ (fun _ : E => UnforcedLeray.Heat.kernel 1 ξ) := contDiff_const
    exact hf.smul hg
  have hB : ∀ (k : ℕ) (p : E),
      AEStronglyMeasurable (fun ξ => iteratedFDeriv ℝ k (fam Φ₀ L c ξ) p) (volume : Measure Space) :=
    fun k p => (continuous_iteratedFDeriv_fam Φ₀ hΦ hL hc k p).aestronglyMeasurable
  have hC : ∀ k : ℕ, ∃ b : Space → ℝ, Integrable b (volume : Measure Space) ∧
      ∀ᵐ ξ ∂(volume : Measure Space), ∀ p : E,
        ‖iteratedFDeriv ℝ k (fam Φ₀ L c ξ) p‖ ≤ b ξ := by
    intro k
    refine ⟨fun ξ => M k * (UnforcedLeray.Heat.kernel 1 ξ * (1 + ‖ξ‖) ^ (k : ℝ)), ?_, ?_⟩
    · exact (UnforcedLeray.Heat.integrable_kernel_mul_weight (θ := 1) one_pos
        (b := (k : ℝ)) (Nat.cast_nonneg k)).const_mul (M k)
    · refine Filter.Eventually.of_forall fun ξ p => ?_
      have hk : 0 ≤ UnforcedLeray.Heat.kernel 1 ξ := UnforcedLeray.Heat.kernel_nonneg one_pos ξ
      have h1 := norm_iteratedFDeriv_smul_comp_le Φ₀ hΦ (c ξ) (L ξ)
        (UnforcedLeray.Heat.kernel 1 ξ) k (M k) (hM k) p
      rw [Real.norm_of_nonneg hk] at h1
      have hpow : ‖L ξ‖ ^ k ≤ (1 + ‖ξ‖) ^ k := pow_le_pow_left₀ (norm_nonneg _) (hLb ξ) k
      have hR : (1 + ‖ξ‖) ^ (k : ℝ) = (1 + ‖ξ‖) ^ k := Real.rpow_natCast _ k
      have h2 : UnforcedLeray.Heat.kernel 1 ξ * (M k * ‖L ξ‖ ^ k) ≤
          UnforcedLeray.Heat.kernel 1 ξ * (M k * (1 + ‖ξ‖) ^ k) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (hM0 k)) hk
      show ‖iteratedFDeriv ℝ k (fam Φ₀ L c ξ) p‖ ≤
        M k * (UnforcedLeray.Heat.kernel 1 ξ * (1 + ‖ξ‖) ^ (k : ℝ))
      rw [hR]
      calc ‖iteratedFDeriv ℝ k (fam Φ₀ L c ξ) p‖
          ≤ UnforcedLeray.Heat.kernel 1 ξ * (M k * ‖L ξ‖ ^ k) := h1
        _ ≤ UnforcedLeray.Heat.kernel 1 ξ * (M k * (1 + ‖ξ‖) ^ k) := h2
        _ = M k * (UnforcedLeray.Heat.kernel 1 ξ * (1 + ‖ξ‖) ^ k) := by ring
  exact ⟨hA, hB, hC⟩

/-- The coordinate projections on `ℝ × (ℝ × Space) ∋ q = (w, (τ, z))`. -/
def coordW : (ℝ × (ℝ × Space)) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × Space)

/-- The projection `q ↦ τ`. -/
def coordTau : (ℝ × (ℝ × Space)) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ Space).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × Space))

/-- The projection `q ↦ z`. -/
def coordZ : (ℝ × (ℝ × Space)) →L[ℝ] Space :=
  (ContinuousLinearMap.snd ℝ ℝ Space).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × Space))

/-- The linear part `(w, (τ, z)) ↦ (τ, z - w • ξ)` of the joint heat-flow slice map. -/
def heatL (ξ : Space) : (ℝ × (ℝ × Space)) →L[ℝ] (ℝ × Space) :=
  ContinuousLinearMap.prod coordTau (coordZ - coordW.smulRight ξ)

theorem heatL_apply (ξ : Space) (q : ℝ × (ℝ × Space)) :
    heatL ξ q = (q.2.1, q.2.2 - q.1 • ξ) := rfl

theorem continuous_heatL : Continuous heatL := by
  have hB : Continuous (fun ξ : Space => coordZ - coordW.smulRight ξ) :=
    continuous_const.sub
      (ContinuousLinearMap.smulRightL ℝ (ℝ × (ℝ × Space)) Space coordW).continuous
  exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp (continuous_const.prodMk hB)

theorem norm_heatL_le (ξ : Space) : ‖heatL ξ‖ ≤ 1 + ‖ξ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun q => ?_)
  have hq : 0 ≤ ‖q‖ := norm_nonneg q
  have hξ : 0 ≤ ‖ξ‖ := norm_nonneg ξ
  have h1 : ‖q.1‖ ≤ ‖q‖ := norm_fst_le q
  have h2 : ‖q.2‖ ≤ ‖q‖ := norm_snd_le q
  have h3 : ‖q.2.1‖ ≤ ‖q‖ := (norm_fst_le q.2).trans h2
  have h4 : ‖q.2.2‖ ≤ ‖q‖ := (norm_snd_le q.2).trans h2
  have h5 : ‖q.2.2 - q.1 • ξ‖ ≤ (1 + ‖ξ‖) * ‖q‖ := by
    calc ‖q.2.2 - q.1 • ξ‖ ≤ ‖q.2.2‖ + ‖q.1 • ξ‖ := norm_sub_le _ _
      _ = ‖q.2.2‖ + ‖q.1‖ * ‖ξ‖ := by rw [norm_smul]
      _ ≤ ‖q‖ + ‖q‖ * ‖ξ‖ := by gcongr
      _ = (1 + ‖ξ‖) * ‖q‖ := by ring
  have h6 : ‖q.2.1‖ ≤ (1 + ‖ξ‖) * ‖q‖ :=
    h3.trans (le_mul_of_one_le_left hq (by linarith))
  rw [heatL_apply]
  exact norm_prod_le_iff.2 ⟨h6, h5⟩

/-- The slice family: the identity linear part. -/
def sliceL : Space → (ℝ × Space) →L[ℝ] (ℝ × Space) :=
  fun _ => ContinuousLinearMap.id ℝ (ℝ × Space)

/-- The slice family: the translation vector `(0, -(w • ξ))`. -/
def sliceC (w : ℝ) : Space → ℝ × Space := fun x => (0, -(w • x))

theorem continuous_sliceC (w : ℝ) : Continuous (sliceC w) := by
  unfold sliceC
  exact continuous_const.prodMk (continuous_id.const_smul w).neg

theorem norm_sliceL_le_one (ξ : Space) : ‖sliceL ξ‖ ≤ 1 :=
  ContinuousLinearMap.norm_id_le

theorem norm_sliceL_le (ξ : Space) : ‖sliceL ξ‖ ≤ 1 + ‖ξ‖ :=
  (norm_sliceL_le_one ξ).trans (le_add_of_nonneg_right (norm_nonneg ξ))

end HeatGaussSmoothAux

open HeatGaussSmoothAux in
theorem heatGaussSmooth_proof : UnforcedLeray.Short.PartIIa.HeatGaussSmooth := by
  intro P hP Φ₀ hΦ
  have hM := phaseTestDerivBounded_proof P hP Φ₀ hΦ
  choose M hM0 hMb using hM
  have hΦs : ContDiff ℝ ∞ Φ₀ := hΦ.smooth
  -- Joint smoothness in `(w, τ, z)`, by differentiation under the integral.
  have h1 : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Space) => heatGauss Φ₀ q.1 q.2) := by
    have hyp1 := fam_hyp Φ₀ hΦs M hM0 hMb heatL (fun _ => (0 : ℝ × Space))
      continuous_heatL continuous_const norm_heatL_le
    convert (paramIntegralSmooth_proof _ Space volume _ hyp1).1 using 1
    funext q
    unfold heatGauss
    simp only [fam, add_zero, heatL_apply]
  -- Each slice is a composite of the joint map with `p ↦ (w, p)`.
  have h2 : ∀ w : ℝ, ContDiff ℝ ∞ (heatGauss Φ₀ w) := by
    intro w
    have hw : ContDiff ℝ ∞ (fun x : ℝ × Space => (w, x)) :=
      contDiff_const.prodMk contDiff_id
    exact h1.comp hw
  refine ⟨h1, h2, fun k => ⟨M k, hM0 k, fun w q => ?_⟩⟩
  -- Uniform bound on the `k`-th derivative of each slice.
  have hyp2 := fam_hyp Φ₀ hΦs M hM0 hMb sliceL (sliceC w) continuous_const
    (continuous_sliceC w) norm_sliceL_le
  have hkey : iteratedFDeriv ℝ k (heatGauss Φ₀ w) q =
      ∫ x, iteratedFDeriv ℝ k (fam Φ₀ sliceL (sliceC w) x) q ∂volume := by
    have hfun : heatGauss Φ₀ w = fun p => ∫ x, fam Φ₀ sliceL (sliceC w) x p ∂volume := by
      funext p
      unfold heatGauss
      congr 1
      funext x
      simp only [fam, sliceL, sliceC, ContinuousLinearMap.id_apply]
      have e : ((p.1, p.2 - w • x) : ℝ × Space) = p + (0, -(w • x)) :=
        Prod.ext (by simp) (by simp [sub_eq_add_neg])
      rw [e]
    rw [hfun]
    exact (paramIntegralSmooth_proof _ Space volume _ hyp2).2 k q
  rw [hkey]
  have hbound : ∀ x : Space,
      ‖iteratedFDeriv ℝ k (fam Φ₀ sliceL (sliceC w) x) q‖ ≤ M k * UnforcedLeray.Heat.kernel 1 x := by
    intro x
    have h := norm_iteratedFDeriv_smul_comp_le Φ₀ hΦs (sliceC w x) (sliceL x)
      (UnforcedLeray.Heat.kernel 1 x) k (M k) (hMb k) q
    have hk : 0 ≤ UnforcedLeray.Heat.kernel 1 x := UnforcedLeray.Heat.kernel_nonneg one_pos x
    rw [Real.norm_of_nonneg hk] at h
    have hpow : ‖sliceL x‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) (norm_sliceL_le_one x)
    calc ‖iteratedFDeriv ℝ k (fam Φ₀ sliceL (sliceC w) x) q‖
        ≤ UnforcedLeray.Heat.kernel 1 x * (M k * ‖sliceL x‖ ^ k) := h
      _ ≤ UnforcedLeray.Heat.kernel 1 x * M k :=
          mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (hM0 k) hpow) hk
      _ = M k * UnforcedLeray.Heat.kernel 1 x := mul_comm _ _
  calc ‖∫ x, iteratedFDeriv ℝ k (fam Φ₀ sliceL (sliceC w) x) q ∂volume‖
      ≤ ∫ x, M k * UnforcedLeray.Heat.kernel 1 x ∂volume :=
        norm_integral_le_of_norm_le
          ((UnforcedLeray.Heat.kernel_integrable one_pos).const_mul (M k))
          (Filter.Eventually.of_forall hbound)
    _ = M k := by rw [integral_const_mul, UnforcedLeray.Heat.integral_kernel one_pos, mul_one]

end UnforcedLeray.Short.PartIIa
