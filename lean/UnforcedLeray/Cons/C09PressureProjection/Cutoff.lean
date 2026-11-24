import UnforcedLeray.Cons.C09PressureProjection.Calculus

/-!
# C9 helper: the Hessian relation passes from tests to decaying smooth functions

Step C9 (`PressureProjectionStep`, blueprint unit B0708, `paper/main.tex` lines 107–110 and
13719–13733). At a fixed phase the unprojected equation gives, for every compact smooth
scalar test `Φ`, the relation `Σ_j ⟨G_j, ∇∂_jΦ⟩ = 0` with `G_j = (U⊗U)_{·j} + p e_j`
(that is `-Δp = ∂_i∂_j(U_iU_j)` in distributions). The Leray potential `Q = N ∗ div ψ` of a
test field is not compactly supported, but `Q`, `∇Q` and `∇²Q` decay like `(1+|y|)⁻²`.
This file proves that the relation then holds for `Q`: the cutoffs `χ_R Q` are tests and
`∇∂_j(χ_R Q) → ∇∂_jQ` in `L²` (`colPairing_hessL2_of_decay`). The cutoffs are
`NavierStokesR3.ComparisonCutoffs.cutoff`, and the argument follows the first-order version
`RieszLp.toL2_gradField_mem_orthogonal` (`Lib/CZL2/Decay.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology

namespace UnforcedLeray.Cons.C09

open UnforcedLeray.Blueprint UnforcedLeray.RieszLp

/-- The Hessian columns `(∇∂_jΦ)_j` of a scalar function as `L²` classes (junk `0` when a
column is not in `L²`; consumers prove membership). -/
def hessL2 (Φ : Space → ℝ) : Fin 3 → L2Space :=
  fun j => toL2 (gradField (spatialTestDerivative j Φ))

/-- The pairing `Σ_j ⟨G_j, h_j⟩_{L²}` of two triples of `L²` fields. -/
def colPairing (G h : Fin 3 → L2Space) : ℝ := ∑ j : Fin 3, inner ℝ (G j) (h j)

theorem continuous_colPairing (G : Fin 3 → L2Space) : Continuous (colPairing G) := by
  unfold colPairing
  exact continuous_finset_sum _ fun j _ => continuous_const.inner (continuous_apply j)

/-- `∇h - ∇k = Σ_i (∂_ih - ∂_ik) e_i`. -/
theorem gradField_sub_apply (h k : Space → ℝ) (x : Space) :
    gradField h x - gradField k x =
      ∑ i : Fin 3, (spatialTestDerivative i h x - spatialTestDerivative i k x) •
        coordinateVector i := by
  simp only [gradField, ← Finset.sum_sub_distrib, sub_smul]

/-- An elementary estimate for the product-rule remainder. -/
theorem abs_cutoff_remainder_le {χ a bj ci q e cj bi W C1 C2 r : ℝ} (_hχ0 : 0 ≤ χ)
    (hχ1 : χ ≤ 1) (ha : |a| ≤ W) (hbj : |bj| ≤ W) (hbi : |bi| ≤ W) (hq : |q| ≤ W)
    (hci : |ci| ≤ C1 * r) (hcj : |cj| ≤ C1 * r) (he : |e| ≤ C2 * r ^ 2) :
    |(χ - 1) * a + bj * ci + q * e + cj * bi| ≤ W * ((1 - χ) + 2 * C1 * r + C2 * r ^ 2) := by
  have hW : 0 ≤ W := (abs_nonneg _).trans ha
  have h1 : |(χ - 1) * a| ≤ (1 - χ) * W := by
    rw [abs_mul, abs_of_nonpos (by linarith : χ - 1 ≤ 0), neg_sub]
    exact mul_le_mul_of_nonneg_left ha (by linarith)
  have h2 : |bj * ci| ≤ W * (C1 * r) := by
    rw [abs_mul]; exact mul_le_mul hbj hci (abs_nonneg _) hW
  have h3 : |q * e| ≤ W * (C2 * r ^ 2) := by
    rw [abs_mul]; exact mul_le_mul hq he (abs_nonneg _) hW
  have h4 : |cj * bi| ≤ (C1 * r) * W := by
    rw [abs_mul]; exact mul_le_mul hcj hbi (abs_nonneg _) ((abs_nonneg _).trans hcj)
  calc |(χ - 1) * a + bj * ci + q * e + cj * bi|
      ≤ |(χ - 1) * a| + |bj * ci| + |q * e| + |cj * bi| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ (1 - χ) * W + W * (C1 * r) + W * (C2 * r ^ 2) + (C1 * r) * W := by gcongr
    _ = W * ((1 - χ) + 2 * C1 * r + C2 * r ^ 2) := by ring

/-- **Second-order cutoff approximation.** If `Q` is smooth and `Q`, `∂_iQ`, `∂_i∂_jQ` are
bounded by `M(1+|y|)⁻²`, then `∇∂_j(χ_R Q) → ∇∂_jQ` in `L²` along `R = n + 1`. -/
theorem tendsto_hessL2_cutoff {Q : Space → ℝ} (hQ : ContDiff ℝ ∞ Q) {M : ℝ}
    (h0 : ∀ x, |Q x| ≤ M * decayWeight x)
    (h1 : ∀ i x, |spatialTestDerivative i Q x| ≤ M * decayWeight x)
    (h2 : ∀ i j x, |spatialTestDerivative i (spatialTestDerivative j Q) x| ≤
      M * decayWeight x) (j : Fin 3) :
    Tendsto (fun n : ℕ => hessL2
        (fun x => NavierStokesR3.ComparisonCutoffs.cutoff ((n : ℝ) + 1) x * Q x) j)
      atTop (𝓝 (hessL2 Q j)) := by
  open NavierStokesR3.ComparisonCutoffs in
  have hM : 0 ≤ M := by
    have h := (abs_nonneg (Q 0)).trans (h0 0)
    exact nonneg_of_mul_nonneg_left h (decayWeight_pos 0)
  set C1 := derivativeConstant 1 with hC1def
  set C2 := derivativeConstant 2 with hC2def
  have hC1 : 0 < C1 := derivativeConstant_pos 1
  have hC2 : 0 < C2 := derivativeConstant_pos 2
  let χ : ℕ → Space → ℝ := fun n => cutoff ((n : ℝ) + 1)
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hR : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hr0 : ∀ n, 0 ≤ r n := fun n => by positivity
  have hr1 : ∀ n, r n ≤ 1 := fun n => by
    show 1 / ((n : ℝ) + 1) ≤ 1
    rw [div_le_one (hR n)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hχs : ∀ n, ContDiff ℝ ∞ (χ n) := fun n => cutoff_smooth _
  let θ : ℕ → Space → ℝ := fun n x => χ n x * Q x
  have hθ : ∀ n, IsSpatialTest (θ n) := fun n =>
    ⟨(hχs n).mul hQ, (cutoff_hasCompactSupport (hR n)).mul_right⟩
  -- derivative bounds for the cutoffs
  have hdχ : ∀ n i x, |spatialTestDerivative i (χ n) x| ≤ C1 * r n := by
    intro n i x
    have e1 := cutoff_fderiv_le (hR n) x
    have e2 := (fderiv ℝ (χ n) x).le_opNorm (coordinateVector i)
    rw [norm_coordinateVector, mul_one] at e2
    rw [← Real.norm_eq_abs]
    calc ‖spatialTestDerivative i (χ n) x‖ ≤ C1 / ((n : ℝ) + 1) := e2.trans e1
      _ = C1 * r n := by simp only [r]; ring
  have hddχ : ∀ n i k x, |spatialTestDerivative i (spatialTestDerivative k (χ n)) x| ≤
      C2 * r n ^ 2 := by
    intro n i k x
    rw [second_partial_eq (hχs n) i k x, ← Real.norm_eq_abs]
    have e1 := cutoff_second_fderiv_le (hR n) x
    have e2 := ((fderiv ℝ (fderiv ℝ (χ n)) x) (coordinateVector i)).le_opNorm
      (coordinateVector k)
    have e3 := (fderiv ℝ (fderiv ℝ (χ n)) x).le_opNorm (coordinateVector i)
    rw [norm_coordinateVector, mul_one] at e2 e3
    calc ‖fderiv ℝ (fderiv ℝ (χ n)) x (coordinateVector i) (coordinateVector k)‖
        ≤ ‖fderiv ℝ (fderiv ℝ (χ n)) x‖ := e2.trans e3
      _ ≤ C2 / ((n : ℝ) + 1) ^ 2 := e1
      _ = C2 * r n ^ 2 := by simp only [r]; rw [div_pow, one_pow, mul_one_div]
  -- the second derivatives of `θ n`
  have hdθ : ∀ n, spatialTestDerivative j (θ n) =
      fun x => χ n x * spatialTestDerivative j Q x + Q x * spatialTestDerivative j (χ n) x := by
    intro n; funext x; exact spatialTestDerivative_mul (hχs n) hQ j x
  have hddθ : ∀ n i x, spatialTestDerivative i (spatialTestDerivative j (θ n)) x =
      (χ n x * spatialTestDerivative i (spatialTestDerivative j Q) x +
        spatialTestDerivative j Q x * spatialTestDerivative i (χ n) x) +
      (Q x * spatialTestDerivative i (spatialTestDerivative j (χ n)) x +
        spatialTestDerivative j (χ n) x * spatialTestDerivative i Q x) := by
    intro n i x
    have hQj := PressureAnalysis.contDiff_spatialTestDerivative hQ j
    have hχj := PressureAnalysis.contDiff_spatialTestDerivative (hχs n) j
    rw [hdθ n, spatialTestDerivative_add ((hχs n).mul hQj) (hQ.mul hχj),
      spatialTestDerivative_mul (hχs n) hQj, spatialTestDerivative_mul hQ hχj]
  -- the difference field
  let D : ℕ → Space → Space := fun n x =>
    gradField (spatialTestDerivative j (θ n)) x - gradField (spatialTestDerivative j Q) x
  have hQj : ContDiff ℝ ∞ (spatialTestDerivative j Q) :=
    PressureAnalysis.contDiff_spatialTestDerivative hQ j
  have hDcont : ∀ n, Continuous (D n) := fun n =>
    (continuous_gradField ((hθ n).derivative j).smooth).sub (continuous_gradField hQj)
  have hDb : ∀ n x, ‖D n x‖ ≤
      3 * (M * decayWeight x * ((1 - χ n x) + 2 * C1 * r n + C2 * r n ^ 2)) := by
    intro n x
    have hw := decayWeight_pos x
    have h01 := cutoff_mem_Icc ((n : ℝ) + 1) x
    show ‖gradField (spatialTestDerivative j (θ n)) x -
      gradField (spatialTestDerivative j Q) x‖ ≤ _
    rw [gradField_sub_apply]
    refine (norm_sum_smul_coordinateVector_le _).trans ?_
    calc ∑ i : Fin 3, |spatialTestDerivative i (spatialTestDerivative j (θ n)) x -
          spatialTestDerivative i (spatialTestDerivative j Q) x|
        ≤ ∑ _i : Fin 3, M * decayWeight x * ((1 - χ n x) + 2 * C1 * r n + C2 * r n ^ 2) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [hddθ n i x]
          have := abs_cutoff_remainder_le (χ := χ n x)
            (a := spatialTestDerivative i (spatialTestDerivative j Q) x)
            (bj := spatialTestDerivative j Q x) (ci := spatialTestDerivative i (χ n) x)
            (q := Q x) (e := spatialTestDerivative i (spatialTestDerivative j (χ n)) x)
            (cj := spatialTestDerivative j (χ n) x) (bi := spatialTestDerivative i Q x)
            (W := M * decayWeight x) (C1 := C1) (C2 := C2) (r := r n) h01.1 h01.2
            (h2 i j x) (h1 j x) (h1 i x) (h0 x) (hdχ n i x) (hdχ n j x) (hddχ n i j x)
          refine (le_of_eq ?_).trans this
          congr 1
          ring
      _ = 3 * (M * decayWeight x * ((1 - χ n x) + 2 * C1 * r n + C2 * r n ^ 2)) := by
          simp
  have hDB : ∀ n x, ‖D n x‖ ≤ 3 * M * (1 + 2 * C1 + C2) * decayWeight x := by
    intro n x
    refine (hDb n x).trans ?_
    have hw := decayWeight_pos x
    have h01 := cutoff_mem_Icc ((n : ℝ) + 1) x
    have hrn := hr1 n
    have hr2 : r n ^ 2 ≤ 1 := pow_le_one₀ (hr0 n) hrn
    have : (1 - χ n x) + 2 * C1 * r n + C2 * r n ^ 2 ≤ 1 + 2 * C1 + C2 := by
      have := h01.1
      nlinarith
    have hMw : 0 ≤ M * decayWeight x := mul_nonneg hM hw.le
    calc 3 * (M * decayWeight x * ((1 - χ n x) + 2 * C1 * r n + C2 * r n ^ 2))
        ≤ 3 * (M * decayWeight x * (1 + 2 * C1 + C2)) := by gcongr
      _ = 3 * M * (1 + 2 * C1 + C2) * decayWeight x := by ring
  have hDlim : ∀ x, Tendsto (fun n => ‖D n x‖) atTop (𝓝 0) := by
    intro x
    have hev : ∀ᶠ n : ℕ in atTop, 1 - χ n x = 0 := by
      obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
      refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
      have : ‖x‖ ≤ (n : ℝ) + 1 := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      simp [χ, cutoff_eq_one (hR n) this]
    have e1 : Tendsto (fun n : ℕ => 1 - χ n x) atTop (𝓝 0) :=
      tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
    have e2 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have e3 : Tendsto (fun n : ℕ => 3 * (M * decayWeight x *
        ((1 - χ n x) + 2 * C1 * r n + C2 * r n ^ 2))) atTop (𝓝 0) := by
      have := ((e1.add (e2.const_mul (2 * C1))).add ((e2.pow 2).const_mul C2)).const_mul
        (M * decayWeight x)
      simpa [mul_assoc] using this.const_mul 3
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => hDb n x) e3
  have hBm : MemLp (fun x => 3 * M * (1 + 2 * C1 + C2) * decayWeight x) 2 volume :=
    memLp_decayWeight.const_mul _
  have hT := tendsto_eLpNorm_two_of_dominated (fun n => (hDcont n).aestronglyMeasurable)
    hBm hDB hDlim
  -- membership in `L²`
  have hlimL2 : MemLp (gradField (spatialTestDerivative j Q)) 2 volume :=
    memLp_gradField hQj fun i x => h2 i j x
  have hθL2 : ∀ n, MemLp (gradField (spatialTestDerivative j (θ n))) 2 volume := fun n =>
    (continuous_gradField ((hθ n).derivative j).smooth).memLp_of_hasCompactSupport
      (hasCompactSupport_gradField ((hθ n).derivative j))
  show Tendsto (fun n => toL2 (gradField (spatialTestDerivative j (θ n)))) atTop
    (𝓝 (toL2 (gradField (spatialTestDerivative j Q))))
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  refine hT.congr fun n => ?_
  apply eLpNorm_congr_ae
  filter_upwards [coeFn_toL2 (hθL2 n), coeFn_toL2 hlimL2] with x e1 e2
  rw [Pi.sub_apply, e1, e2]

/-- **The Hessian relation extends to decaying smooth functions.** If `Σ_j ⟨G_j, ∇∂_jΦ⟩ = 0`
for every compact smooth scalar test `Φ`, then the same holds for every smooth `Q` with
`Q`, `∂_iQ`, `∂_i∂_jQ` bounded by `M(1+|y|)⁻²`. -/
theorem colPairing_hessL2_of_decay {G : Fin 3 → L2Space}
    (hG : ∀ Φ, IsSpatialTest Φ → colPairing G (hessL2 Φ) = 0)
    {Q : Space → ℝ} (hQ : ContDiff ℝ ∞ Q) {M : ℝ}
    (h0 : ∀ x, |Q x| ≤ M * decayWeight x)
    (h1 : ∀ i x, |spatialTestDerivative i Q x| ≤ M * decayWeight x)
    (h2 : ∀ i j x, |spatialTestDerivative i (spatialTestDerivative j Q) x| ≤
      M * decayWeight x) :
    colPairing G (hessL2 Q) = 0 := by
  have hR : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hθ : ∀ n : ℕ, IsSpatialTest
      (fun x => NavierStokesR3.ComparisonCutoffs.cutoff ((n : ℝ) + 1) x * Q x) := fun n =>
    ⟨(NavierStokesR3.ComparisonCutoffs.cutoff_smooth _).mul hQ,
      (NavierStokesR3.ComparisonCutoffs.cutoff_hasCompactSupport (hR n)).mul_right⟩
  have hT : Tendsto (fun n : ℕ => hessL2
      (fun x => NavierStokesR3.ComparisonCutoffs.cutoff ((n : ℝ) + 1) x * Q x))
      atTop (𝓝 (hessL2 Q)) :=
    tendsto_pi_nhds.2 fun j => tendsto_hessL2_cutoff hQ h0 h1 h2 j
  have hlim := ((continuous_colPairing G).tendsto _).comp hT
  have hzero : (fun n : ℕ => colPairing G (hessL2
      (fun x => NavierStokesR3.ComparisonCutoffs.cutoff ((n : ℝ) + 1) x * Q x))) =
      fun _ => 0 := funext fun n => hG _ (hθ n)
  rw [Function.comp_def, hzero] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end UnforcedLeray.Cons.C09
