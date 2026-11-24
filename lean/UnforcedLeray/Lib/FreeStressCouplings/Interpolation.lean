import UnforcedLeray.Lib.FreeStressCouplings.MulRep
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# The mixed half-derivative bound `‖C₀^{1/2} 𝓡_μ D₀^{1/2}‖ ≤ C_μ` (INF10 F2)


§5 Level F, target **F2** (Wave 1, block 1J, bypass B9); blueprint unit **B0474**
(`eq:free-stress-28`, tex 7790-7812), including its duality step (tex 7790-7793, which rests
on the adjoint identification **B0473**, tex 7774-7788).

Setting (tex 7789-7812).  `C₀ = 1 + |B|` and `D₀ = 1 + A` are positive selfadjoint operators on
`Y₂`, here given by concrete spectral representations `C₀ D₀ : MulRep` (bypass B9: no general
spectral theorem; the two representations are unrelated, so no commutation between `A` and `B`
is assumed, tex 7807-7808).  The endpoint hypotheses are the graph estimates of the manuscript:

* `C₀ 𝓡_μ` is bounded by `M₁` (tex 7791): for every `x`, `𝓡_μ x ∈ dom C₀` and
  `‖C₀ 𝓡_μ x‖ ≤ M₁ ‖x‖`;
* `𝓡_μ D₀` extends boundedly with bound `M₀` (tex 7791-7793): `‖𝓡_μ D₀ x‖ ≤ M₀ ‖x‖` on
  `dom D₀`, or, in the dual form used by the manuscript, `D₀ 𝓡_μ*` is bounded by `M₀`.

Conclusion (`eq:free-stress-28`): `C₀^{1/2} 𝓡_μ D₀^{1/2}` maps `dom D₀^{1/2}` into
`dom C₀^{1/2}` with norm at most `C_μ = √(M₀ M₁)`, and extends to a bounded operator on `Y₂`
with the same norm (`exists_bounded_extension`).  The constant is the product of the endpoint
bounds, so it is uniform wherever `M₀` and `M₁` are (compact `μ`-sets, all `ν`), as the
blueprint note on B0474 requires.

Proof route.  The manuscript applies the three-lines lemma to scalar pairings of
`C₀^z 𝓡_μ D₀^{1-z}` after spectral cutoffs, then passes to the limit (tex 7795-7802).  Here
the cutoffs `P_N = C₀^{1/2} 1_{C₀ ≤ N}` and `Q_K = D₀^{1/2} 1_{D₀ ≤ K}` are bounded selfadjoint,
the midpoint bound `‖P_N 𝓡 Q_K‖ ≤ √(‖P_N² 𝓡‖ ‖𝓡 Q_K²‖)` is the C*-inequality
`norm_mul_mul_le_of_endpoints` (`Heinz.lean`), and the limits use strong convergence of cutoffs
on the domain and the Fatou closure of `dom C₀^{1/2}` (`MulRep.lean`).

Main results:
* `MulRep.exists_hasPow_half_of_endpoints`: the pointwise bound;
* `MulRep.exists_hasPow_half_of_adjoint`: the same with the dual endpoint `D₀ 𝓡_μ*`;
* `MulRep.exists_hasPow_half_comp`: the version for `R_μ = 𝓡_μ P_σ` with `P_σ` commuting with
  `D₀^{1/2}` (tex 7809-7811);
* `MulRep.exists_bounded_extension`: the bounded extension with norm `≤ √(M₀ M₁)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology InnerProductSpace

namespace UnforcedLeray.FreeStress

namespace MulRep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem half_nonneg' : (0 : ℝ) ≤ 1 / 2 := by norm_num

omit [CompleteSpace H] in
theorem cutOp_half_mul_half (T : MulRep H μ E) (N : ℝ) :
    T.cutOp (1 / 2) half_nonneg' N * T.cutOp (1 / 2) half_nonneg' N =
      T.cutOp 1 zero_le_one N := by
  rw [cutOp_mul_cutOp]
  congr 1
  norm_num

/-- **`eq:free-stress-28`, pointwise form** (B0474, tex 7790-7812).  If `C₀ R` is bounded by
`M₁` and `R D₀` is bounded by `M₀` on `dom D₀`, then for `x ∈ dom D₀^{1/2}` with
`D₀^{1/2} x = y`, `R y ∈ dom C₀^{1/2}` and `‖C₀^{1/2} R y‖ ≤ √(M₀ M₁) ‖x‖`. -/
theorem exists_hasPow_half_of_endpoints (C₀ : MulRep H μ E) (D₀ : MulRep H ν F)
    (R : H →L[ℂ] H) {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₁ : ∀ x, ∃ y, C₀.HasPow 1 (R x) y ∧ ‖y‖ ≤ M₁ * ‖x‖)
    (h₀ : ∀ x y, D₀.HasPow 1 x y → ‖R y‖ ≤ M₀ * ‖x‖)
    {x y : H} (hxy : D₀.HasPow (1 / 2) x y) :
    ∃ z, C₀.HasPow (1 / 2) (R y) z ∧ ‖z‖ ≤ Real.sqrt (M₀ * M₁) * ‖x‖ := by
  set P : ℕ → H →L[ℂ] H := fun N => C₀.cutOp (1 / 2) half_nonneg' N with hP
  set Q : ℕ → H →L[ℂ] H := fun K => D₀.cutOp (1 / 2) half_nonneg' K with hQ
  have hA : ∀ N : ℕ, ‖P N * P N * R‖ ≤ M₁ := by
    intro N
    rw [hP]
    simp only
    rw [cutOp_half_mul_half]
    refine ContinuousLinearMap.opNorm_le_bound _ hM₁ fun v => ?_
    obtain ⟨w, hw, hwn⟩ := h₁ v
    exact (C₀.norm_cutOp_apply_le_of_hasPow zero_le_one N hw).trans hwn
  have hB : ∀ K : ℕ, ‖R * (Q K * Q K)‖ ≤ M₀ := by
    intro K
    rw [hQ]
    simp only
    rw [cutOp_half_mul_half]
    refine ContinuousLinearMap.opNorm_le_bound _ hM₀ fun v => ?_
    have h := h₀ _ _ (D₀.hasPow_cutOp_zero zero_le_one K v)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hM₀)
    exact ((D₀.cutOp 0 le_rfl K).le_opNorm v).trans
      (mul_le_of_le_one_left (norm_nonneg _) (D₀.norm_cutOp_zero_le K))
  have hC : ∀ N K : ℕ, ‖P N * R * Q K‖ ≤ Real.sqrt (M₀ * M₁) := fun N K =>
    norm_mul_mul_le_of_endpoints (C₀.isSelfAdjoint_cutOp _ _) (D₀.isSelfAdjoint_cutOp _ _) R
      (hA N) (hB K)
  have hD : ∀ N : ℕ, ‖C₀.cutOp (1 / 2) half_nonneg' N (R y)‖ ≤
      Real.sqrt (M₀ * M₁) * ‖x‖ := by
    intro N
    have hlim : Tendsto (fun K : ℕ => (P N * R * Q K) x) atTop
        (𝓝 (C₀.cutOp (1 / 2) half_nonneg' N (R y))) :=
      (((P N).comp R).continuous.tendsto y).comp (D₀.tendsto_cutOp half_nonneg' hxy)
    refine le_of_tendsto' hlim.norm fun K => ?_
    exact ((P N * R * Q K).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hC N K) (norm_nonneg _))
  exact C₀.exists_hasPow_of_norm_cutOp_le half_nonneg' hD

/-- **`eq:free-stress-28` with the dual endpoint** (tex 7790-7802).  The manuscript obtains the
bound for `𝓡_μ D₀` as the dual of `D₀ 𝓡_μ*` (tex 7792-7793, B0473); this form takes that
hypothesis directly. -/
theorem exists_hasPow_half_of_adjoint (C₀ : MulRep H μ E) (D₀ : MulRep H ν F)
    (R : H →L[ℂ] H) {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₁ : ∀ x, ∃ y, C₀.HasPow 1 (R x) y ∧ ‖y‖ ≤ M₁ * ‖x‖)
    (h₀ : ∀ v, ∃ w, D₀.HasPow 1 (ContinuousLinearMap.adjoint R v) w ∧ ‖w‖ ≤ M₀ * ‖v‖)
    {x y : H} (hxy : D₀.HasPow (1 / 2) x y) :
    ∃ z, C₀.HasPow (1 / 2) (R y) z ∧ ‖z‖ ≤ Real.sqrt (M₀ * M₁) * ‖x‖ :=
  exists_hasPow_half_of_endpoints C₀ D₀ R hM₀ hM₁ h₁
    (fun _ _ h => D₀.norm_apply_le_of_adjoint R hM₀ h₀ h) hxy

/-- **Composition with a commuting projection** (tex 7809-7811: `P_σ` commutes with `A` and
`B`, so the estimate holds for `R_μ = 𝓡_μ P_σ`).  If `P` maps `dom D₀^{1/2}` into itself,
commuting with `D₀^{1/2}`, the bound for `R` gives the bound for `R ∘ P` with `‖P x‖` in place
of `‖x‖`. -/
theorem exists_hasPow_half_comp (C₀ : MulRep H μ E) (D₀ : MulRep H ν F)
    (R P : H →L[ℂ] H) {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₁ : ∀ x, ∃ y, C₀.HasPow 1 (R x) y ∧ ‖y‖ ≤ M₁ * ‖x‖)
    (h₀ : ∀ x y, D₀.HasPow 1 x y → ‖R y‖ ≤ M₀ * ‖x‖)
    (hP : ∀ x y, D₀.HasPow (1 / 2) x y → D₀.HasPow (1 / 2) (P x) (P y))
    {x y : H} (hxy : D₀.HasPow (1 / 2) x y) :
    ∃ z, C₀.HasPow (1 / 2) (R (P y)) z ∧ ‖z‖ ≤ Real.sqrt (M₀ * M₁) * ‖P x‖ :=
  exists_hasPow_half_of_endpoints C₀ D₀ R hM₀ hM₁ h₁ h₀ (hP x y hxy)

/-- **`eq:free-stress-28`, bounded-extension form** (B0474: "`C₀^{1/2} 𝓡_μ D₀^{1/2}` extends to
a bounded operator on `Y₂` with norm `≤ C_μ`").  There is a bounded operator `S` with
`‖S‖ ≤ √(M₀ M₁)` such that `S x = C₀^{1/2} R D₀^{1/2} x` for every `x ∈ dom D₀^{1/2}`. -/
theorem exists_bounded_extension (C₀ : MulRep H μ E) (D₀ : MulRep H ν F)
    (R : H →L[ℂ] H) {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₁ : ∀ x, ∃ y, C₀.HasPow 1 (R x) y ∧ ‖y‖ ≤ M₁ * ‖x‖)
    (h₀ : ∀ x y, D₀.HasPow 1 x y → ‖R y‖ ≤ M₀ * ‖x‖) :
    ∃ S : H →L[ℂ] H, ‖S‖ ≤ Real.sqrt (M₀ * M₁) ∧
      ∀ x y, D₀.HasPow (1 / 2) x y → C₀.HasPow (1 / 2) (R y) (S x) := by
  set M := Real.sqrt (M₀ * M₁) with hMdef
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have main := fun {x y : H} (h : D₀.HasPow (1 / 2) x y) =>
    exists_hasPow_half_of_endpoints C₀ D₀ R hM₀ hM₁ h₁ h₀ h
  -- `Pc K = 1_{D₀ ≤ K}`, `Q K = D₀^{1/2} 1_{D₀ ≤ K}`; `D₀^{1/2} (Pc K x) = Q K x`.
  set Pc : ℕ → H →L[ℂ] H := fun K => D₀.cutOp 0 le_rfl K with hPc
  set Q : ℕ → H →L[ℂ] H := fun K => D₀.cutOp (1 / 2) half_nonneg' K with hQ
  have hPcQ : ∀ K x, D₀.HasPow (1 / 2) (Pc K x) (Q K x) := fun K x =>
    D₀.hasPow_cutOp_zero half_nonneg' K x
  -- `S_K x = C₀^{1/2} R Q_K x`.
  let SK : ℕ → H → H := fun K x => Classical.choose (main (hPcQ K x))
  have hSK : ∀ K x, C₀.HasPow (1 / 2) (R (Q K x)) (SK K x) ∧ ‖SK K x‖ ≤ M * ‖Pc K x‖ :=
    fun K x => Classical.choose_spec (main (hPcQ K x))
  -- Linearity and the Lipschitz bound, from uniqueness of `C₀^{1/2}`.
  have hSK_sub : ∀ K L x, ‖SK K x - SK L x‖ ≤ M * ‖Pc K x - Pc L x‖ := by
    intro K L x
    obtain ⟨z, hz, hzn⟩ := main ((hPcQ K x).sub (hPcQ L x))
    have : C₀.HasPow (1 / 2) (R (Q K x - Q L x)) (SK K x - SK L x) := by
      rw [map_sub]
      exact (hSK K x).1.sub (hSK L x).1
    rw [HasPow.unique this hz]
    exact hzn
  have hSK_add : ∀ K x x', SK K (x + x') = SK K x + SK K x' := by
    intro K x x'
    have h1 : C₀.HasPow (1 / 2) (R (Q K (x + x'))) (SK K x + SK K x') := by
      rw [map_add, map_add]
      exact (hSK K x).1.add (hSK K x').1
    exact HasPow.unique (hSK K (x + x')).1 h1
  have hSK_smul : ∀ K (c : ℂ) x, SK K (c • x) = c • SK K x := by
    intro K c x
    have h1 : C₀.HasPow (1 / 2) (R (Q K (c • x))) (c • SK K x) := by
      rw [map_smul, map_smul]
      exact (hSK K x).1.smul c
    exact HasPow.unique (hSK K (c • x)).1 h1
  -- `Pc_K x → x`, hence `S_K x` is Cauchy.
  have hPclim : ∀ x, Tendsto (fun K : ℕ => Pc K x) atTop (𝓝 x) := fun x =>
    D₀.tendsto_cutOp le_rfl (D₀.hasPow_zero x)
  have hcauchy : ∀ x, CauchySeq fun K : ℕ => SK K x := by
    intro x
    have hc := (hPclim x).cauchySeq
    rw [Metric.cauchySeq_iff] at hc ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε / (M + 1)) (div_pos hε (by linarith))
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have h1 := hN m hm n hn
    rw [dist_eq_norm] at h1
    calc ‖SK m x - SK n x‖ ≤ M * ‖Pc m x - Pc n x‖ := hSK_sub m n x
      _ ≤ (M + 1) * ‖Pc m x - Pc n x‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (M + 1) * (ε / (M + 1)) := mul_lt_mul_of_pos_left h1 (by linarith)
      _ = ε := by field_simp
  set S₀ : H → H := fun x => limUnder atTop fun K : ℕ => SK K x with hS₀
  have hS₀lim : ∀ x, Tendsto (fun K : ℕ => SK K x) atTop (𝓝 (S₀ x)) := fun x =>
    tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hcauchy x))
  have hS₀_norm : ∀ x, ‖S₀ x‖ ≤ M * ‖x‖ := by
    intro x
    refine le_of_tendsto' (hS₀lim x).norm fun K => ?_
    refine (hSK K x).2.trans (mul_le_mul_of_nonneg_left ?_ hM)
    exact ((Pc K).le_opNorm x).trans
      (mul_le_of_le_one_left (norm_nonneg _) (D₀.norm_cutOp_zero_le K))
  let Slin : H →ₗ[ℂ] H :=
    { toFun := S₀
      map_add' := fun x x' => by
        refine tendsto_nhds_unique (hS₀lim (x + x')) ?_
        simp_rw [hSK_add]
        exact (hS₀lim x).add (hS₀lim x')
      map_smul' := fun c x => by
        refine tendsto_nhds_unique (hS₀lim (c • x)) ?_
        simp_rw [hSK_smul]
        exact (hS₀lim x).const_smul c }
  refine ⟨Slin.mkContinuous M hS₀_norm, LinearMap.mkContinuous_norm_le _ hM _, ?_⟩
  intro x y hxy
  change C₀.HasPow (1 / 2) (R y) (S₀ x)
  refine HasPow.of_tendsto C₀ half_nonneg' (xn := fun K => R (Q K x)) (yn := fun K => SK K x)
    ?_ (hS₀lim x) fun K => (hSK K x).1
  exact (R.continuous.tendsto y).comp (D₀.tendsto_cutOp half_nonneg' hxy)

end MulRep

end UnforcedLeray.FreeStress
