import UnforcedLeray.Cons.L2.CanonicalBranch.Evolution

/-!
# G3b, part 3: the canonical limit (B0118) and its backward continuation (B0119) in `X_G`

`paper/main.tex`, proof of G3b, lines 1809–1850 (`eq:st18-t00095`–`eq:st18-t00099`); blueprint
units B0118 (`eq:st18-t00096`: Cauchy property and the limit on `θ ≥ b₀`), B0119
(`eq:st18-t00097`–`t00098`: backward continuation and its bound), B0120 (`eq:st18-t00099`: exact
preparation), with the inputs B0116 (`eq:st18-t00093`) and B0117 (`eq:st18-t00094`).

Everything is stated for arbitrary `λ, κ ∈ ℂ` and `q ∈ X_G`, with the concrete backward evolution
`S` of `Evolution.lean`; the reference data `(λ, κ, q)` of G1–G3a are substituted in
`Cons/L2/CanonicalBranch.lean`.

## Objects (`eq:st18-t00095`)

* `gauge λ κ θ = e^{λθ}θ^κ`, `gaugeInv λ κ θ = e^{-λθ}θ^{-κ}` (principal powers of `θ > 0`, i.e.
  the real logarithm, line 760);
* `branchR λ κ q R θ = V_R(θ) = e^{-λR}R^{-κ} W_R(R - θ)`, where `W_R(R - θ) = S(θ, R)q` is the
  forward solution of `eq:st18-t00088` from `q` (`W_t = (L₀ + βD)W`, `β = 1/(R - t) = 1/θ`);
* `stateY λ κ q R θ = Y_R(θ) = e^{λθ}θ^κ V_R(θ)`, the normalized state `Aq + r`;
* `normProp λ κ θ θ' = e^{λθ}θ^κ S(θ, θ') e^{-λθ'}θ'^{-κ}`, the evolution of normalized states.

## Results

* `stateY_sub_stateY`: `Y_{R₂}(θ) - Y_{R₁}(θ) = N(θ, R₁)(Y_{R₂}(R₁) - q)` (the difference of two
  normalized states is propagated from `R₁` down, its initial value being `Y_{R₂}(R₁) - Y_{R₁}(R₁)`,
  line 1817);
* **`cauchy_bound`** (`eq:st18-t00096`): from B0116 (`‖Y_R(θ) - q‖ ≤ C/θ`) and B0117 (uniform
  propagation `‖N(θ, θ')‖ ≤ C`), `sup_{b₀ ≤ θ ≤ R₁}‖Y_{R₂}(θ) - Y_{R₁}(θ)‖ ≤ C/R₁`;
* `canonY` (the limit `Y_can`), `tendsto_canonY`, `norm_canonY_sub_le`
  (`‖Y_can(θ) - q‖ ≤ C/θ`, `eq:st18-t00013` on `θ ≥ b₀`), `canonTail_mild` (passing to the limit
  in the mild equation);
* `canonV` (the canonical branch on all `θ > 0`, continued below `b₀` by `S`, line 1838),
  `canonV_mild`, `norm_canonV_le` (`eq:st18-t00098`), `continuousOn_canonV`;
* **`exists_isXGCanonicalBranch`**: G3b at the level of `X_G` (B0118 + B0119);
* `prepared_exact` (`eq:st18-t00099`, B0120): the backward solution from
  `q_R = e^{λR}R^κV_can(R)` is exactly `e^{λR}R^κV_can(θ)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010

variable (lam κ : ℂ) (q : XG)

/-! ## Gauges and normalized states -/

/-- `e^{λθ}θ^κ`. -/
def gauge (θ : ℝ) : ℂ := Complex.exp (lam * θ) * (θ : ℂ) ^ κ

/-- `e^{-λθ}θ^{-κ}`. -/
def gaugeInv (θ : ℝ) : ℂ := Complex.exp (-(lam * θ)) * (θ : ℂ) ^ (-κ)

variable {lam κ} in
theorem gauge_mul_gaugeInv {θ : ℝ} (hθ : 0 < θ) : gauge lam κ θ * gaugeInv lam κ θ = 1 := by
  have h0 : (θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hθ.ne'
  unfold gauge gaugeInv
  rw [mul_mul_mul_comm, ← Complex.exp_add, ← Complex.cpow_add _ _ h0, add_neg_cancel,
    add_neg_cancel, Complex.exp_zero, Complex.cpow_zero, mul_one]

variable {lam κ} in
theorem gaugeInv_mul_gauge {θ : ℝ} (hθ : 0 < θ) : gaugeInv lam κ θ * gauge lam κ θ = 1 := by
  rw [mul_comm, gauge_mul_gaugeInv hθ]

/-- `V_R(θ) = e^{-λR}R^{-κ}W_R(R - θ)`, `W_R(R - θ) = S(θ, R)q` (`eq:st18-t00095`). -/
def branchR (R θ : ℝ) : XG := gaugeInv lam κ R • S θ R q

/-- The normalized state `Y_R(θ) = e^{λθ}θ^κV_R(θ)` (`eq:st18-t00095`). -/
def stateY (R θ : ℝ) : XG := gauge lam κ θ • branchR lam κ q R θ

/-- The evolution of normalized states, `N(θ, θ') = e^{λθ}θ^κ S(θ, θ') e^{-λθ'}θ'^{-κ}`: the
normalized state `Aq + r` at `θ` of the solution whose normalized state at `θ'` is `f`
(`eq:st18-t00089`, `eq:st18-t00094`). -/
def normProp (θ θ' : ℝ) : XG →L[ℂ] XG := (gauge lam κ θ * gaugeInv lam κ θ') • S θ θ'

variable {lam κ q}

theorem stateY_self {θ : ℝ} (hθ : 0 < θ) : stateY lam κ q θ θ = q := by
  rw [stateY, branchR, S_self hθ, ContinuousLinearMap.one_apply, smul_smul,
    gauge_mul_gaugeInv hθ, one_smul]

theorem normProp_apply (θ θ' : ℝ) (f : XG) :
    normProp lam κ θ θ' f = (gauge lam κ θ * gaugeInv lam κ θ') • S θ θ' f := rfl

theorem normProp_q (θ R : ℝ) : normProp lam κ θ R q = stateY lam κ q R θ := by
  rw [normProp_apply, stateY, branchR, smul_smul]

theorem normProp_stateY {θ R₁ R₂ : ℝ} (hθ : 0 < θ) (h1 : θ ≤ R₁) (h2 : R₁ ≤ R₂) :
    normProp lam κ θ R₁ (stateY lam κ q R₂ R₁) = stateY lam κ q R₂ θ := by
  have hR₁ : 0 < R₁ := hθ.trans_le h1
  simp only [normProp_apply, stateY, branchR, map_smul, S_comp_apply hθ h1 h2, smul_smul]
  congr 1
  have key := gaugeInv_mul_gauge (lam := lam) (κ := κ) hR₁
  linear_combination (gauge lam κ θ * gaugeInv lam κ R₂) * key

/-- The difference of two normalized states is the propagated initial difference
(`eq:st18-t00096`, line 1817: "at `θ = R₁` the two normalized states differ by `O(R₁⁻¹)` …
Apply `eq:st18-t00094` to that difference from `R₁` down to `b₀`"). -/
theorem stateY_sub_stateY {θ R₁ R₂ : ℝ} (hθ : 0 < θ) (h1 : θ ≤ R₁) (h2 : R₁ ≤ R₂) :
    stateY lam κ q R₂ θ - stateY lam κ q R₁ θ =
      normProp lam κ θ R₁ (stateY lam κ q R₂ R₁ - q) := by
  rw [map_sub, normProp_stateY hθ h1 h2, normProp_q]

/-! ## The Cauchy property (`eq:st18-t00096`) -/

section Cauchy

variable {b C₁ C₂ : ℝ}
  (hG : ∀ θ R : ℝ, b ≤ θ → θ ≤ R → ‖stateY lam κ q R θ - q‖ ≤ C₁ / θ)
  (hN : ∀ θ θ' : ℝ, b ≤ θ → θ ≤ θ' → ‖normProp lam κ θ θ'‖ ≤ C₂)

include hG hN in
/-- **B0118, `eq:st18-t00096`**: `‖Y_{R₂}(θ) - Y_{R₁}(θ)‖ ≤ C/R₁` for `b₀ ≤ θ ≤ R₁ ≤ R₂`, from the
relative growth bound of B0116 and the uniform propagation of differences of B0117. -/
theorem cauchy_bound (hb : 0 < b) {θ R₁ R₂ : ℝ} (hθ : b ≤ θ) (h1 : θ ≤ R₁) (h2 : R₁ ≤ R₂) :
    ‖stateY lam κ q R₂ θ - stateY lam κ q R₁ θ‖ ≤ C₂ * C₁ / R₁ := by
  rw [stateY_sub_stateY (hb.trans_le hθ) h1 h2]
  have hN' := hN θ R₁ hθ h1
  have hC₂ : 0 ≤ C₂ := (norm_nonneg _).trans hN'
  calc ‖normProp lam κ θ R₁ (stateY lam κ q R₂ R₁ - q)‖
      ≤ ‖normProp lam κ θ R₁‖ * ‖stateY lam κ q R₂ R₁ - q‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ C₂ * (C₁ / R₁) := mul_le_mul hN' (hG R₁ R₂ (hθ.trans h1) h2) (norm_nonneg _) hC₂
    _ = C₂ * C₁ / R₁ := by ring

include hG hN in
theorem cauchySeq_stateY (hb : 0 < b) {θ : ℝ} (hθ : b ≤ θ) :
    CauchySeq fun R => stateY lam κ q R θ := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  set K := max (C₂ * C₁) 0
  refine ⟨max θ (K / ε + 1), fun R hR => ?_⟩
  have hN0 : θ ≤ max θ (K / ε + 1) := le_max_left _ _
  have hNpos : 0 < max θ (K / ε + 1) := (hb.trans_le hθ).trans_le hN0
  rw [dist_eq_norm]
  calc ‖stateY lam κ q R θ - stateY lam κ q (max θ (K / ε + 1)) θ‖
      ≤ C₂ * C₁ / max θ (K / ε + 1) := cauchy_bound hG hN hb hθ hN0 hR
    _ ≤ K / max θ (K / ε + 1) := div_le_div_of_nonneg_right (le_max_left _ _) hNpos.le
    _ < ε := by
      rw [div_lt_iff₀ hNpos]
      have h1 : K / ε + 1 ≤ max θ (K / ε + 1) := le_max_right _ _
      have h2 : ε * (K / ε + 1) = K + ε := by field_simp
      nlinarith

end Cauchy

/-! ## The canonical limit `Y_can` and `V_can` on `θ ≥ b₀` -/

variable (lam κ q) in
/-- `Y_can(θ) = lim_{R→∞} Y_R(θ)` (line 1823: "The locally uniform limit `Y_can`"). -/
def canonY (θ : ℝ) : XG := limUnder atTop fun R => stateY lam κ q R θ

variable (lam κ q) in
/-- `V_can = e^{-λθ}θ^{-κ}Y_can` on `θ ≥ b₀` (line 1824). -/
def canonTail (θ : ℝ) : XG := gaugeInv lam κ θ • canonY lam κ q θ

section Limit

variable {b C₁ C₂ : ℝ} (hb : 0 < b)
  (hG : ∀ θ R : ℝ, b ≤ θ → θ ≤ R → ‖stateY lam κ q R θ - q‖ ≤ C₁ / θ)
  (hN : ∀ θ θ' : ℝ, b ≤ θ → θ ≤ θ' → ‖normProp lam κ θ θ'‖ ≤ C₂)
include hb hG hN

theorem tendsto_canonY {θ : ℝ} (hθ : b ≤ θ) :
    Tendsto (fun R => stateY lam κ q R θ) atTop (𝓝 (canonY lam κ q θ)) := by
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (cauchySeq_stateY hG hN hb hθ)
  exact tendsto_nhds_limUnder ⟨y, hy⟩

/-- `‖Y_can(θ) - Y_R(θ)‖ ≤ C/R` for `b₀ ≤ θ ≤ R` (the limit of `eq:st18-t00096`). -/
theorem norm_canonY_sub_stateY_le {θ R : ℝ} (hθ : b ≤ θ) (hR : θ ≤ R) :
    ‖canonY lam κ q θ - stateY lam κ q R θ‖ ≤ C₂ * C₁ / R := by
  have ht : Tendsto (fun R' => ‖stateY lam κ q R' θ - stateY lam κ q R θ‖) atTop
      (𝓝 ‖canonY lam κ q θ - stateY lam κ q R θ‖) :=
    ((tendsto_canonY hb hG hN hθ).sub_const _).norm
  refine le_of_tendsto ht ?_
  filter_upwards [eventually_ge_atTop R] with R' hR'
  exact cauchy_bound hG hN hb hθ hR hR'

/-- **`eq:st18-t00013` on `θ ≥ b₀`**: `‖Y_can(θ) - q‖ ≤ C/θ`, i.e.
`V_can(θ) = e^{-λθ}θ^{-κ}(q + O_{X_G}(θ⁻¹))` (B0118). -/
theorem norm_canonY_sub_le {θ : ℝ} (hθ : b ≤ θ) :
    ‖canonY lam κ q θ - q‖ ≤ C₂ * C₁ / θ := by
  have h := norm_canonY_sub_stateY_le hb hG hN hθ le_rfl
  rwa [stateY_self (hb.trans_le hθ)] at h

theorem tendsto_branchR {θ : ℝ} (hθ : b ≤ θ) :
    Tendsto (fun R => branchR lam κ q R θ) atTop (𝓝 (canonTail lam κ q θ)) := by
  have h := (tendsto_canonY hb hG hN hθ).const_smul (gaugeInv lam κ θ)
  refine h.congr fun R => ?_
  rw [stateY, smul_smul, gaugeInv_mul_gauge (hb.trans_le hθ), one_smul]

/-- **Passing to the limit in the mild equation** (line 1824): `V_can(θ) = S(θ, θ')V_can(θ')`
for `b₀ ≤ θ ≤ θ'`. -/
theorem canonTail_mild {θ θ' : ℝ} (hθ : b ≤ θ) (hθθ' : θ ≤ θ') :
    canonTail lam κ q θ = S θ θ' (canonTail lam κ q θ') := by
  have h1 := tendsto_branchR hb hG hN hθ
  have h2 := ((S θ θ').continuous.tendsto _).comp (tendsto_branchR hb hG hN (hθ.trans hθθ'))
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [eventually_ge_atTop θ'] with R hR
  simp only [Function.comp_apply, branchR, map_smul]
  rw [S_comp_apply (hb.trans_le hθ) hθθ' hR]

end Limit

/-! ## The canonical branch on all `θ > 0` (B0119) -/

variable (lam κ q) in
/-- **The canonical branch** `V_can` on `θ > 0`: the limit `canonTail` on `θ ≥ b₀`, continued to
`0 < θ < b₀` by the backward evolution, `V_can(θ) = S(θ, b₀)V_can(b₀)` (lines 1828–1840,
`eq:st18-t00097`: "This supplies the stated continuation"). -/
def canonV (b θ : ℝ) : XG := S θ (max θ b) (canonTail lam κ q (max θ b))

section Branch

variable {b C₁ C₂ : ℝ} (hb : 0 < b)
  (hG : ∀ θ R : ℝ, b ≤ θ → θ ≤ R → ‖stateY lam κ q R θ - q‖ ≤ C₁ / θ)
  (hN : ∀ θ θ' : ℝ, b ≤ θ → θ ≤ θ' → ‖normProp lam κ θ θ'‖ ≤ C₂)
include hb hG hN

omit hG hN in
theorem canonV_of_le {θ : ℝ} (hθ : b ≤ θ) : canonV lam κ q b θ = canonTail lam κ q θ := by
  rw [canonV, max_eq_left hθ, S_self (hb.trans_le hθ), ContinuousLinearMap.one_apply]

/-- **The canonical branch is a mild solution on `(0, ∞)`**: `V_can(θ) = S(θ, θ')V_can(θ')` for
`0 < θ ≤ θ'`. -/
theorem canonV_mild {θ θ' : ℝ} (hθ : 0 < θ) (hθθ' : θ ≤ θ') :
    canonV lam κ q b θ = S θ θ' (canonV lam κ q b θ') := by
  have hm : max θ b ≤ max θ' b := max_le_max hθθ' le_rfl
  rw [canonV, canonV, S_comp_apply hθ hθθ' (le_max_left θ' b),
    canonTail_mild hb hG hN (le_max_right θ b) hm,
    S_comp_apply hθ (le_max_left θ b) hm]

/-- **`eq:st18-t00098`** (B0119): `‖V_can(θ)‖ ≤ e^{b₀‖L₀‖}‖V_can(b₀)‖` for `0 < θ ≤ b₀`. -/
theorem norm_canonV_le {θ : ℝ} (hθ : 0 < θ) (hθb : θ ≤ b) :
    ‖canonV lam κ q b θ‖ ≤ Real.exp (b * ‖B0012.L0‖) * ‖canonV lam κ q b b‖ := by
  rw [canonV_mild hb hG hN hθ hθb]
  refine ((S θ b).le_opNorm _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  refine (norm_S_le hθ hθb).trans (Real.exp_le_exp.2 ?_)
  have := norm_nonneg B0012.L0
  nlinarith

/-- `θ ↦ V_can(θ)` is continuous into `X_G` on `(0, ∞)` ("smooth at every positive `θ`", line
745, at the level of `X_G`). -/
theorem continuousOn_canonV : ContinuousOn (canonV lam κ q b) (Ioi 0) := by
  intro θ₀ hθ₀
  have hθ₀' : (0 : ℝ) < θ₀ := hθ₀
  have hc := continuousOn_S_left (θ₁ := θ₀ + 1) (half_pos hθ₀') (canonV lam κ q b (θ₀ + 1))
  have heq : EqOn (fun θ => S θ (θ₀ + 1) (canonV lam κ q b (θ₀ + 1))) (canonV lam κ q b)
      (Icc (θ₀ / 2) (θ₀ + 1)) := fun θ hθ =>
    (canonV_mild hb hG hN (half_pos hθ₀' |>.trans_le hθ.1) hθ.2).symm
  have hmem : Icc (θ₀ / 2) (θ₀ + 1) ∈ 𝓝 θ₀ := Icc_mem_nhds (by linarith) (by linarith)
  exact ((hc.congr heq.symm).continuousAt hmem).continuousWithinAt

/-- The asymptotics `‖e^{λθ}θ^κV_can(θ) - q‖ ≤ C/θ` for `θ ≥ b₀` (`eq:st18-t00013`). -/
theorem norm_gauge_canonV_sub_le {θ : ℝ} (hθ : b ≤ θ) :
    ‖gauge lam κ θ • canonV lam κ q b θ - q‖ ≤ C₂ * C₁ / θ := by
  rw [canonV_of_le hb hθ, canonTail, smul_smul, gauge_mul_gaugeInv (hb.trans_le hθ),
    one_smul]
  exact norm_canonY_sub_le hb hG hN hθ

/-- **Exact preparation** (`eq:st18-t00099`, B0120): with `q_R = e^{λR}R^κV_can(R)`, the
backward solution from `q_R` at `R` is exactly `e^{λR}R^κV_can(θ)`, `0 < θ ≤ R`. -/
theorem prepared_exact {θ R : ℝ} (hθ : 0 < θ) (hR : θ ≤ R) :
    S θ R (gauge lam κ R • canonV lam κ q b R) = gauge lam κ R • canonV lam κ q b θ := by
  rw [map_smul, ← canonV_mild hb hG hN hθ hR]

/-- `q_R = q + O_{X_G}(R⁻¹)` for `R ≥ b₀` (`eq:st18-t00015`, first clause). -/
theorem norm_preparedDatum_sub_le {R : ℝ} (hR : b ≤ R) :
    ‖gauge lam κ R • canonV lam κ q b R - q‖ ≤ C₂ * C₁ / R :=
  norm_gauge_canonV_sub_le hb hG hN hR

end Branch

/-! ## G3b at the level of `X_G` -/

/-- **G3b in `X_G`** (`eq:st18-t00013`; lines 735–760): `V` is a mild solution of
`-∂_θV = (L₀ + θ⁻¹D)V` on `(0, ∞)` (through the concrete backward evolution `S`), continuous into
`X_G`, bounded in `X_G` near zero, and `‖e^{λθ}θ^κV(θ) - q‖ ≤ C/θ` at infinity. -/
structure IsXGCanonicalBranch (lam κ : ℂ) (q : XG) (V : ℝ → XG) : Prop where
  mild : ∀ θ θ' : ℝ, 0 < θ → θ ≤ θ' → V θ = S θ θ' (V θ')
  continuousOn : ContinuousOn V (Ioi 0)
  bounded_near_zero : ∃ C : ℝ, ∀ θ : ℝ, 0 < θ → θ ≤ 1 → ‖V θ‖ ≤ C
  asymptotic : ∃ C θ₁ : ℝ, 0 < θ₁ ∧ ∀ θ : ℝ, θ₁ ≤ θ → ‖gauge lam κ θ • V θ - q‖ ≤ C / θ

/-- **G3b in `X_G` from B0116 and B0117** (B0118 with B0119): if the normalized states satisfy the
relative growth bound `‖Y_R(θ) - q‖ ≤ C/θ` and the normalized evolution is uniformly bounded,
both on `θ ≥ b₀`, then the canonical branch exists. -/
theorem exists_isXGCanonicalBranch {b C₁ C₂ : ℝ}
    (hG : ∀ θ R : ℝ, b ≤ θ → θ ≤ R → ‖stateY lam κ q R θ - q‖ ≤ C₁ / θ)
    (hN : ∀ θ θ' : ℝ, b ≤ θ → θ ≤ θ' → ‖normProp lam κ θ θ'‖ ≤ C₂) :
    ∃ V : ℝ → XG, IsXGCanonicalBranch lam κ q V := by
  -- enlarge `b₀` to `max b₀ 1`, so that `(0, 1] ⊆ (0, b₀]`
  set b' := max b 1 with hb'
  have hb'0 : 0 < b' := lt_of_lt_of_le one_pos (le_max_right b 1)
  have hbb' : b ≤ b' := le_max_left b 1
  have hG' : ∀ θ R : ℝ, b' ≤ θ → θ ≤ R → ‖stateY lam κ q R θ - q‖ ≤ C₁ / θ :=
    fun θ R hθ hR => hG θ R (hbb'.trans hθ) hR
  have hN' : ∀ θ θ' : ℝ, b' ≤ θ → θ ≤ θ' → ‖normProp lam κ θ θ'‖ ≤ C₂ :=
    fun θ θ' hθ h => hN θ θ' (hbb'.trans hθ) h
  refine ⟨canonV lam κ q b', ⟨fun θ θ' hθ h => canonV_mild hb'0 hG' hN' hθ h,
    continuousOn_canonV hb'0 hG' hN', ?_, ⟨C₂ * C₁, b', hb'0, fun θ hθ =>
      norm_gauge_canonV_sub_le hb'0 hG' hN' hθ⟩⟩⟩
  refine ⟨Real.exp (b' * ‖B0012.L0‖) * ‖canonV lam κ q b' b'‖, fun θ hθ hθ1 => ?_⟩
  exact norm_canonV_le hb'0 hG' hN' hθ (hθ1.trans (le_max_right b 1))

end UnforcedLeray.Cons.G3b
