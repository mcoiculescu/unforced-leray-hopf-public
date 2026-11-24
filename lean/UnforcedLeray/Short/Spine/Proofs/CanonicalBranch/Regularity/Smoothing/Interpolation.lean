import UnforcedLeray.Short.Spine.Sub.SP_CAN4_1

/-!
# Spine: `XGjContinuousOfBounds` (leaf 5 of `Spine:SP-CAN/4/1`)

Source of record: `the November 2 reference manuscript`, lines 1134-1145.

Proof. Let `V` be continuous into `X_G` on `(0, ∞)` with `MildLevel V (j+1)`. Put
`U θ = (I - D)^{j/2} V θ` (`xgjInterpU`; `U θ = 0` where `V θ ∉ X_{G,j}`, which does not occur for
`θ > 0`).

* Interpolation (`xgjInterp_sq_le`): for `f ∈ X_{G,j+1}` and every `N : ℕ`,
  `‖f‖²_{X_{G,j}} ≤ 2(1+N)^j ‖f‖² + 2(1+N)^{-1} ‖f‖²_{X_{G,j+1}}`. It comes from the weighted
  series `B0123.hasSum_xgjNorm_sq` and the pointwise bound `xgjInterp_pointwise`.
* Continuity at `θ₀ > 0` (`xgjInterp_continuousAt`): for `f = V θ - V θ₀` and `θ` near `θ₀`,
  `‖f‖²_{X_{G,j+1}} ≤ ‖f‖² + (2K)²` where `K` is the `MildLevel` bound on `[θ₀/2, 2θ₀]`
  (`xgjInterp_sq_bound`). Since `‖V θ - V θ₀‖ → 0`, the interpolation with `N` large gives
  `‖U θ - U θ₀‖² → 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- Pointwise interpolation weight: `1 + (1+n)^j ≤ 2(1+N)^j + 2(1+N)^{-1}(1 + (1+n)^{j+1})`. -/
theorem xgjInterp_pointwise (j N n : ℕ) :
    1 + (1 + (n : ℝ)) ^ j ≤
      2 * (1 + (N : ℝ)) ^ j + 2 * (1 + (N : ℝ))⁻¹ * (1 + (1 + (n : ℝ)) ^ (j + 1)) := by
  have hN : (0 : ℝ) < 1 + (N : ℝ) := by positivity
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hNn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hx : (1 : ℝ) ≤ 1 + (n : ℝ) := by linarith
  have hxj : (1 : ℝ) ≤ (1 + (n : ℝ)) ^ j := one_le_pow₀ hx
  have hNj : (1 : ℝ) ≤ (1 + (N : ℝ)) ^ j := one_le_pow₀ (by linarith)
  have hA : 0 ≤ 2 * (1 + (N : ℝ)) ^ j := by positivity
  have hB : 0 ≤ 2 * (1 + (N : ℝ))⁻¹ * (1 + (1 + (n : ℝ)) ^ (j + 1)) := by positivity
  rcases le_total n N with hnN | hNn'
  · have hle : (1 + (n : ℝ)) ≤ 1 + (N : ℝ) := by
      have : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
      linarith
    have hpow : (1 + (n : ℝ)) ^ j ≤ (1 + (N : ℝ)) ^ j :=
      pow_le_pow_left₀ (by linarith) hle j
    linarith
  · have hle : (1 + (N : ℝ)) ≤ 1 + (n : ℝ) := by
      have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn'
      linarith
    have hsucc : (1 + (n : ℝ)) ^ j * (1 + (N : ℝ)) ≤ (1 + (n : ℝ)) ^ (j + 1) := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    have hinv : (1 + (N : ℝ))⁻¹ * ((1 + (n : ℝ)) ^ j * (1 + (N : ℝ))) = (1 + (n : ℝ)) ^ j := by
      rw [mul_comm ((1 + (n : ℝ)) ^ j), ← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul]
    have hPle : (1 + (n : ℝ)) ^ j ≤ (1 + (N : ℝ))⁻¹ * (1 + (n : ℝ)) ^ (j + 1) :=
      hinv.symm.trans_le (mul_le_mul_of_nonneg_left hsucc (by positivity))
    have hC : 0 ≤ 2 * (1 + (N : ℝ))⁻¹ := by positivity
    nlinarith

/-- **Interpolation.** For `f ∈ X_{G,j+1}` and `N : ℕ`,
`‖f‖²_{X_{G,j}} ≤ 2(1+N)^j ‖f‖² + 2(1+N)^{-1} ‖f‖²_{X_{G,j+1}}`. -/
theorem xgjInterp_sq_le (j N : ℕ) (f : XG) (hf : f ∈ B0123.XGj (j + 1)) :
    B0123.xgjNorm j ⟨f, B0123.XGj_succ_le j hf⟩ ^ 2 ≤
      2 * (1 + (N : ℝ)) ^ j * ‖f‖ ^ 2 +
        2 * (1 + (N : ℝ))⁻¹ * B0123.xgjNorm (j + 1) ⟨f, hf⟩ ^ 2 := by
  have h1 := B0123.hasSum_xgjNorm_sq j ⟨f, B0123.XGj_succ_le j hf⟩
  have h2 := (B0123.hasSum_norm_inner_sq B0094.oscBasis f).mul_left (2 * (1 + (N : ℝ)) ^ j)
  have h3 := (B0123.hasSum_xgjNorm_sq (j + 1) ⟨f, hf⟩).mul_left (2 * (1 + (N : ℝ))⁻¹)
  have hpt : ∀ n : ℕ, (1 + (1 + (n : ℝ)) ^ j) * ‖⟪B0094.oscBasis n, f⟫_ℂ‖ ^ 2 ≤
      2 * (1 + (N : ℝ)) ^ j * ‖⟪B0094.oscBasis n, f⟫_ℂ‖ ^ 2 +
        2 * (1 + (N : ℝ))⁻¹ * ((1 + (1 + (n : ℝ)) ^ (j + 1)) * ‖⟪B0094.oscBasis n, f⟫_ℂ‖ ^ 2) := by
    intro n
    have hm := mul_le_mul_of_nonneg_right (xgjInterp_pointwise j N n)
      (sq_nonneg ‖⟪B0094.oscBasis n, f⟫_ℂ‖)
    exact le_of_le_of_eq hm (by ring)
  exact hasSum_le hpt h1 (h2.add h3)

/-- `‖(I - D)^{k/2} y‖ ≤ ‖y‖_{X_{G,k}}` (local copy of the graph-norm bound). -/
theorem xgjInterp_norm_IDpow_le (k : ℕ) (y : XG) (hy : y ∈ B0123.XGj k) :
    ‖B0123.IDpow ((k : ℝ) / 2) ⟨y, hy⟩‖ ≤ B0123.xgjNorm k ⟨y, hy⟩ := by
  have h := Real.abs_le_sqrt (x := ‖B0123.IDpow ((k : ℝ) / 2) ⟨y, hy⟩‖)
    (y := ‖y‖ ^ 2 + ‖B0123.IDpow ((k : ℝ) / 2) ⟨y, hy⟩‖ ^ 2)
    (by nlinarith [sq_nonneg ‖y‖])
  rw [abs_norm] at h
  exact h

/-- The graph norm squared splits as `‖f‖² + ‖(I - D)^{k/2} f‖²`. -/
theorem xgjInterp_xgjNorm_sq (k : ℕ) (f : XG) (hf : f ∈ B0123.XGj k) :
    B0123.xgjNorm k ⟨f, hf⟩ ^ 2 = ‖f‖ ^ 2 + ‖B0123.IDpow ((k : ℝ) / 2) ⟨f, hf⟩‖ ^ 2 := by
  rw [B0123.xgjNorm, Real.sq_sqrt (by positivity)]

/-- `(I - D)^{k/2}` is linear on `X_{G,k}`. -/
theorem xgjInterp_idpow_sub (k : ℕ) (x y : XG) (hx : x ∈ B0123.XGj k) (hy : y ∈ B0123.XGj k)
    (hxy : x - y ∈ B0123.XGj k) :
    B0123.IDpow ((k : ℝ) / 2) ⟨x - y, hxy⟩ =
      B0123.IDpow ((k : ℝ) / 2) ⟨x, hx⟩ - B0123.IDpow ((k : ℝ) / 2) ⟨y, hy⟩ :=
  (B0123.IDpow ((k : ℝ) / 2)).map_sub ⟨x, hx⟩ ⟨y, hy⟩

open Classical in
/-- The candidate `U θ = (I - D)^{j/2} V θ` (with the value `0` where `V θ ∉ X_{G,j}`). -/
def xgjInterpU (V : ℝ → XG) (j : ℕ) (θ : ℝ) : XG :=
  if h : V θ ∈ B0123.XGj j then B0123.IDpow ((j : ℝ) / 2) ⟨V θ, h⟩ else 0

theorem xgjInterpU_pos (V : ℝ → XG) (j : ℕ) (θ : ℝ) (h : V θ ∈ B0123.XGj j) :
    xgjInterpU V j θ = B0123.IDpow ((j : ℝ) / 2) ⟨V θ, h⟩ := by
  unfold xgjInterpU
  simp only [h, ↓reduceDIte]

/-- Pointwise bound on `‖U θ - U θ₀‖²` in terms of `‖V θ - V θ₀‖²`, for `θ, θ₀ > 0` whose
`X_{G,j+1}` graph norms are at most `K`. -/
theorem xgjInterp_sq_bound (V : ℝ → XG) (j N : ℕ) (K θ θ0 : ℝ)
    (hmem : ∀ s : ℝ, 0 < s → V s ∈ B0123.XGj (j + 1))
    (hθ : 0 < θ) (hθ0 : 0 < θ0)
    (hKθ : B0123.xgjNorm (j + 1) ⟨V θ, hmem θ hθ⟩ ≤ K)
    (hKθ0 : B0123.xgjNorm (j + 1) ⟨V θ0, hmem θ0 hθ0⟩ ≤ K) :
    ‖xgjInterpU V j θ - xgjInterpU V j θ0‖ ^ 2 ≤
      2 * (1 + (N : ℝ)) ^ j * ‖V θ - V θ0‖ ^ 2 +
        2 * (1 + (N : ℝ))⁻¹ * (‖V θ - V θ0‖ ^ 2 + (2 * K) ^ 2) := by
  have hf1 : V θ - V θ0 ∈ B0123.XGj (j + 1) :=
    Submodule.sub_mem (B0123.XGj (j + 1)) (hmem θ hθ) (hmem θ0 hθ0)
  have hθj : V θ ∈ B0123.XGj j := B0123.XGj_succ_le j (hmem θ hθ)
  have hθ0j : V θ0 ∈ B0123.XGj j := B0123.XGj_succ_le j (hmem θ0 hθ0)
  have hfj : V θ - V θ0 ∈ B0123.XGj j := B0123.XGj_succ_le j hf1
  have hdiff : xgjInterpU V j θ - xgjInterpU V j θ0 =
      B0123.IDpow ((j : ℝ) / 2) ⟨V θ - V θ0, hfj⟩ := by
    rw [xgjInterpU_pos V j θ hθj, xgjInterpU_pos V j θ0 hθ0j,
      xgjInterp_idpow_sub j (V θ) (V θ0) hθj hθ0j hfj]
  have hT : ‖xgjInterpU V j θ - xgjInterpU V j θ0‖ ≤ B0123.xgjNorm j ⟨V θ - V θ0, hfj⟩ := by
    rw [hdiff]
    exact xgjInterp_norm_IDpow_le j (V θ - V θ0) hfj
  have hsqT : ‖xgjInterpU V j θ - xgjInterpU V j θ0‖ ^ 2 ≤
      B0123.xgjNorm j ⟨V θ - V θ0, hfj⟩ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hT 2
  have hsq1 : B0123.xgjNorm j ⟨V θ - V θ0, hfj⟩ ^ 2 ≤
      2 * (1 + (N : ℝ)) ^ j * ‖V θ - V θ0‖ ^ 2 +
        2 * (1 + (N : ℝ))⁻¹ * B0123.xgjNorm (j + 1) ⟨V θ - V θ0, hf1⟩ ^ 2 :=
    xgjInterp_sq_le j N (V θ - V θ0) hf1
  have hB : ‖B0123.IDpow (((j + 1 : ℕ) : ℝ) / 2) ⟨V θ - V θ0, hf1⟩‖ ≤ 2 * K := by
    rw [xgjInterp_idpow_sub (j + 1) (V θ) (V θ0) (hmem θ hθ) (hmem θ0 hθ0) hf1]
    have e1 := norm_sub_le (B0123.IDpow (((j + 1 : ℕ) : ℝ) / 2) ⟨V θ, hmem θ hθ⟩)
      (B0123.IDpow (((j + 1 : ℕ) : ℝ) / 2) ⟨V θ0, hmem θ0 hθ0⟩)
    have e2 := xgjInterp_norm_IDpow_le (j + 1) (V θ) (hmem θ hθ)
    have e3 := xgjInterp_norm_IDpow_le (j + 1) (V θ0) (hmem θ0 hθ0)
    linarith
  have hBsq : ‖B0123.IDpow (((j + 1 : ℕ) : ℝ) / 2) ⟨V θ - V θ0, hf1⟩‖ ^ 2 ≤ (2 * K) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hB 2
  have hXle : B0123.xgjNorm (j + 1) ⟨V θ - V θ0, hf1⟩ ^ 2 ≤
      ‖V θ - V θ0‖ ^ 2 + (2 * K) ^ 2 := by
    rw [xgjInterp_xgjNorm_sq (j + 1) (V θ - V θ0) hf1]
    linarith
  have hmul : 2 * (1 + (N : ℝ))⁻¹ * B0123.xgjNorm (j + 1) ⟨V θ - V θ0, hf1⟩ ^ 2 ≤
      2 * (1 + (N : ℝ))⁻¹ * (‖V θ - V θ0‖ ^ 2 + (2 * K) ^ 2) :=
    mul_le_mul_of_nonneg_left hXle (by positivity)
  linarith [hsqT, hsq1, hmul]

/-- **Continuity of `U` at `θ₀ > 0`.** -/
theorem xgjInterp_continuousAt (V : ℝ → XG) (j : ℕ) (hV : ContinuousOn V (Ioi 0))
    (hmem : ∀ s : ℝ, 0 < s → V s ∈ B0123.XGj (j + 1))
    (hbd : ∀ α β : ℝ, 0 < α → α ≤ β → ∃ K : ℝ, ∀ s ∈ Icc α β,
      ∀ h : V s ∈ B0123.XGj (j + 1), B0123.xgjNorm (j + 1) ⟨V s, h⟩ ≤ K)
    (θ0 : ℝ) (hθ0 : 0 < θ0) : ContinuousAt (xgjInterpU V j) θ0 := by
  obtain ⟨K, hK⟩ := hbd (θ0 / 2) (2 * θ0) (by linarith) (by linarith)
  have hIcc : Icc (θ0 / 2) (2 * θ0) ∈ 𝓝 θ0 := Icc_mem_nhds (by linarith) (by linarith)
  have hVc : Tendsto V (𝓝 θ0) (𝓝 (V θ0)) := hV.continuousAt (Ioi_mem_nhds hθ0)
  have hA : Tendsto (fun θ => ‖V θ - V θ0‖) (𝓝 θ0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hVc
  have hA2 : Tendsto (fun θ => ‖V θ - V θ0‖ ^ 2) (𝓝 θ0) (𝓝 0) := by
    have h := hA.pow 2
    rwa [show (0 : ℝ) ^ 2 = 0 by norm_num] at h
  have hKθ0 : B0123.xgjNorm (j + 1) ⟨V θ0, hmem θ0 hθ0⟩ ≤ K :=
    hK θ0 (Set.mem_Icc.2 ⟨by linarith, by linarith⟩) (hmem θ0 hθ0)
  have hF : Tendsto (fun θ => ‖xgjInterpU V j θ - xgjInterpU V j θ0‖ ^ 2) (𝓝 θ0) (𝓝 0) := by
    rw [tendsto_order]
    refine ⟨fun a ha => Filter.Eventually.of_forall fun θ => lt_of_lt_of_le ha (sq_nonneg _),
      fun a ha => ?_⟩
    obtain ⟨N, hN⟩ := exists_nat_gt (8 * K ^ 2 / a)
    have hNpos : (0 : ℝ) < 1 + (N : ℝ) := by positivity
    have hd : 2 * (1 + (N : ℝ))⁻¹ * (2 * K) ^ 2 < a := by
      rw [show 2 * (1 + (N : ℝ))⁻¹ * (2 * K) ^ 2 = (8 * K ^ 2) / (1 + (N : ℝ)) by ring,
        div_lt_iff₀ hNpos]
      rw [div_lt_iff₀ ha] at hN
      nlinarith
    have hlim := (hA2.const_mul (2 * (1 + (N : ℝ)) ^ j)).add
      ((hA2.add_const ((2 * K) ^ 2)).const_mul (2 * (1 + (N : ℝ))⁻¹))
    have hval : 2 * (1 + (N : ℝ)) ^ j * 0 + 2 * (1 + (N : ℝ))⁻¹ * (0 + (2 * K) ^ 2) < a := by
      rw [mul_zero, zero_add, zero_add]
      exact hd
    have hev := (tendsto_order.1 hlim).2 a hval
    filter_upwards [hIcc, hev] with θ hθI hθlt
    have hθpos : 0 < θ := by linarith [hθI.1]
    have hKθ : B0123.xgjNorm (j + 1) ⟨V θ, hmem θ hθpos⟩ ≤ K := hK θ hθI (hmem θ hθpos)
    exact lt_of_le_of_lt (xgjInterp_sq_bound V j N K θ θ0 hmem hθpos hθ0 hKθ hKθ0) hθlt
  show Tendsto (xgjInterpU V j) (𝓝 θ0) (𝓝 (xgjInterpU V j θ0))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hcomp := (Real.continuous_sqrt.tendsto 0).comp hF
  rw [Real.sqrt_zero] at hcomp
  refine Filter.Tendsto.congr (fun θ => ?_) hcomp
  simp only [Function.comp_apply, Real.sqrt_sq_eq_abs, abs_norm]

/-- **Leaf 5, `XGjContinuousOfBounds`** (shorter proof lines 1134-1145, interpolation). -/
theorem xgjContinuousOfBounds_proof : XGjContinuousOfBounds := by
  intro V j hV hML
  obtain ⟨hmem, hbd⟩ := hML
  refine ⟨xgjInterpU V j, ?_, ?_⟩
  · intro θ hθ
    have hθj : V θ ∈ B0123.XGj j := B0123.XGj_succ_le j (hmem θ hθ)
    exact ⟨hθj, (xgjInterpU_pos V j θ hθj).symm⟩
  · intro θ0 hθ0
    exact (xgjInterp_continuousAt V j hV hmem hbd θ0 (Set.mem_Ioi.1 hθ0)).continuousWithinAt

end UnforcedLeray.Short.Spine

end
