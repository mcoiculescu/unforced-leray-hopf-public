import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2_4_1

/-!
# Part II-b, leaf `PartII-b:T11/2/2/4/1/3` (`GenericCommBound`): decomposition

Source: `the November 2 reference manuscript`
lines 1923-1927.  Proved here: `genericCommBound_of` from three Props:
the exact Leibniz formula for the commutator (`CommFormula`), a bound of the derivatives of the
cutoff (`CutoffDerivBound`), and a bound of `cpdC`-iterates by `iteratedFDeriv` (`CommJetBound`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The rescaled cutoff derivative `L^{-k} φ^{(k)}(t)` as a complex number. -/
def commA (φ : ℝ → ℝ) (L : ℝ) (k : ℕ) (t : ℝ) : ℂ := ((L⁻¹ ^ k * iteratedDeriv k φ t : ℝ) : ℂ)

/-- Exact Leibniz formula for the commutator (SP 1923-1927).  With `Φ(y) = φ(y.2.2/L)` and
`P = Φ`, one has `∂_0 P = ∂_1 P = 0`, `∂_2 P = L⁻¹φ'(η/L)`, `∂_2∂_2 P = L⁻²φ''`, `∂_2³P = L⁻³φ'''`.
Writing `perpC (ΦΨ) = (Φ ∂_2Ψ + P_2 Ψ, -Φ ∂_1Ψ)`, all terms without a derivative of `Φ` cancel in
`T(∇^⊥(ΦΨ)) - Φ T(∇^⊥Ψ)` and what remains (with `a_k = commA φ L k (η/L)`) is the displayed sum.
Proof: product rule `cpdC j (P*Ψ) = P*cpdC j Ψ + cpdC j P*Ψ` (smooth `P`, `Ψ`; `fderiv_mul`),
applied to `P = φ_k(η/L)` for `φ_k = φ, φ', φ''`, three times inside `flatTransposeC (perpC ·)`. -/
def CommFormula : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → ∀ L : ℝ, 0 < L →
    ∀ Ψ : Coord → ℂ, ContDiff ℝ ∞ Ψ → ∀ x : Coord,
      flatTransposeC ν μ (perpC (fun y => (φ (y.2.2 / L) : ℂ) * Ψ y)) x 0 -
          (φ (x.2.2 / L) : ℂ) * flatTransposeC ν μ (perpC Ψ) x 0 =
        (μ - 1) * commA φ L 1 (x.2.2 / L) * Ψ x -
          (x.1 : ℂ) * commA φ L 1 (x.2.2 / L) * cpdC 0 Ψ x -
          (ν : ℂ) * (x.1 : ℂ) * (commA φ L 1 (x.2.2 / L) * cpdC 1 (cpdC 1 Ψ) x +
            commA φ L 3 (x.2.2 / L) * Ψ x + 3 * commA φ L 2 (x.2.2 / L) * cpdC 2 Ψ x +
            3 * commA φ L 1 (x.2.2 / L) * cpdC 2 (cpdC 2 Ψ) x) ∧
      flatTransposeC ν μ (perpC (fun y => (φ (y.2.2 / L) : ℂ) * Ψ y)) x 1 -
          (φ (x.2.2 / L) : ℂ) * flatTransposeC ν μ (perpC Ψ) x 1 =
        (ν : ℂ) * (x.1 : ℂ) * (2 * commA φ L 1 (x.2.2 / L) * cpdC 2 (cpdC 1 Ψ) x +
          commA φ L 2 (x.2.2 / L) * cpdC 1 Ψ x)

/-- Bounds of `φ', φ'', φ'''` for smooth compactly supported `φ`
(`iteratedDeriv k φ` is continuous with compact support:
`ContDiff.continuous_iteratedDeriv`, `HasCompactSupport.iteratedDeriv`,
`Continuous.bounded_above_of_compact_support`). -/
def CutoffDerivBound : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, 1 ≤ k → k ≤ 3 → ∀ t : ℝ, |iteratedDeriv k φ t| ≤ B

/-- `cpdC` iterates are bounded by iterated Fréchet derivatives: `cpdC j Ψ x = fderiv Ψ x (cdir j)`
and `‖cdir j‖ = 1` (sup norm on `ℝ × ℝ × ℝ`); `cpdC j (cpdC k Ψ) x = fderiv (fderiv Ψ) x (cdir j)
(cdir k)` (`fderiv_clm_apply`, `iteratedFDeriv_two_apply`). -/
def CommJetBound : Prop :=
  ∀ Ψ : Coord → ℂ, ContDiff ℝ ∞ Ψ → ∀ x : Coord,
    (∀ j : Fin 3, ‖cpdC j Ψ x‖ ≤ ‖iteratedFDeriv ℝ 1 Ψ x‖) ∧
    (∀ j k : Fin 3, ‖cpdC j (cpdC k Ψ) x‖ ≤ ‖iteratedFDeriv ℝ 2 Ψ x‖)

theorem commNorm_mul_le {u v : ℂ} {A N : ℝ} (hu : ‖u‖ ≤ A) (hv : ‖v‖ ≤ N) (hA : 0 ≤ A) :
    ‖u * v‖ ≤ A * N :=
  (norm_mul_le _ _).trans (mul_le_mul hu hv (norm_nonneg _) hA)

theorem commNorm_nat_mul_le {u : ℂ} {A : ℝ} (m : ℝ) (hm : ‖(m : ℂ)‖ = m) (hm0 : 0 ≤ m)
    (hu : ‖u‖ ≤ A) : ‖(m : ℂ) * u‖ ≤ m * A := by
  rw [norm_mul, hm]
  exact mul_le_mul_of_nonneg_left hu hm0

theorem genericCommBound_of (h1 : CommFormula) (h2 : CutoffDerivBound) (h3 : CommJetBound) :
    GenericCommBound := by
  intro ν μ φ hφ hφc R hR
  obtain ⟨B, hB0, hB⟩ := h2 φ hφ hφc
  refine ⟨B * (‖μ - 1‖ + R + 8 * |ν| * R), by positivity, ?_⟩
  intro L hL Ψ hΨ x hx i
  have hLp : 0 < L⁻¹ := inv_pos.2 hL
  have hLp2 : 0 ≤ L⁻¹ ^ 2 := by positivity
  have hLp3 : 0 ≤ L⁻¹ ^ 3 := by positivity
  have hE1 : L⁻¹ ≤ L⁻¹ + L⁻¹ ^ 2 + L⁻¹ ^ 3 := by linarith
  have hE2 : L⁻¹ ^ 2 ≤ L⁻¹ + L⁻¹ ^ 2 + L⁻¹ ^ 3 := by linarith
  have hE3 : L⁻¹ ^ 3 ≤ L⁻¹ + L⁻¹ ^ 2 + L⁻¹ ^ 3 := by linarith
  have hE0 : 0 ≤ L⁻¹ + L⁻¹ ^ 2 + L⁻¹ ^ 3 := by linarith
  generalize hEdef : L⁻¹ + L⁻¹ ^ 2 + L⁻¹ ^ 3 = E at *
  have ha : ∀ k : ℕ, 1 ≤ k → k ≤ 3 → L⁻¹ ^ k ≤ E →
      ‖commA φ L k (x.2.2 / L)‖ ≤ E * B := by
    intro k hk1 hk3 hu
    unfold commA
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul hu (hB k hk1 hk3 _) (abs_nonneg _) hE0
  have a1 := ha 1 le_rfl (by norm_num) (by simpa using hE1)
  have a2 := ha 2 (by norm_num) (by norm_num) hE2
  have a3 := ha 3 (by norm_num) (by norm_num) hE3
  obtain ⟨j1, j2⟩ := h3 Ψ hΨ x
  have hN0 : ‖Ψ x‖ = ‖iteratedFDeriv ℝ 0 Ψ x‖ := (norm_iteratedFDeriv_zero).symm
  have hn0 : 0 ≤ ‖iteratedFDeriv ℝ 0 Ψ x‖ := norm_nonneg _
  have hn1 : 0 ≤ ‖iteratedFDeriv ℝ 1 Ψ x‖ := norm_nonneg _
  have hn2 : 0 ≤ ‖iteratedFDeriv ℝ 2 Ψ x‖ := norm_nonneg _
  have hn3 : 0 ≤ ‖iteratedFDeriv ℝ 3 Ψ x‖ := norm_nonneg _
  have hSsum : ∑ n ∈ Finset.range 4, ‖iteratedFDeriv ℝ n Ψ x‖ =
      ‖iteratedFDeriv ℝ 0 Ψ x‖ + ‖iteratedFDeriv ℝ 1 Ψ x‖ + ‖iteratedFDeriv ℝ 2 Ψ x‖ +
        ‖iteratedFDeriv ℝ 3 Ψ x‖ := by
    simp [Finset.sum_range_succ]
  rw [hSsum]
  generalize hSdef : ‖iteratedFDeriv ℝ 0 Ψ x‖ + ‖iteratedFDeriv ℝ 1 Ψ x‖ +
    ‖iteratedFDeriv ℝ 2 Ψ x‖ + ‖iteratedFDeriv ℝ 3 Ψ x‖ = S
  have hS0 : ‖Ψ x‖ ≤ S := by rw [hN0]; linarith
  have hS1 : ‖iteratedFDeriv ℝ 1 Ψ x‖ ≤ S := by linarith
  have hS2 : ‖iteratedFDeriv ℝ 2 Ψ x‖ ≤ S := by linarith
  have hSn : 0 ≤ S := by linarith
  have hx1 : ‖(x.1 : ℂ)‖ ≤ R := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hx
  have hν : ‖(ν : ℂ)‖ = |ν| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hEB : 0 ≤ E * B := by positivity
  have hEBS : 0 ≤ E * B * S := by positivity
  have h3c : ‖(3 : ℂ)‖ = 3 := by simp
  have h2c : ‖(2 : ℂ)‖ = 2 := by simp
  obtain ⟨F0, F1⟩ := h1 ν μ φ hφ L hL Ψ hΨ x
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · rw [F0]
    have t1 : ‖(μ - 1) * commA φ L 1 (x.2.2 / L) * Ψ x‖ ≤ ‖μ - 1‖ * (E * B) * S :=
      commNorm_mul_le (commNorm_mul_le le_rfl a1 (norm_nonneg _)) hS0 (by positivity)
    have t2 : ‖(x.1 : ℂ) * commA φ L 1 (x.2.2 / L) * cpdC 0 Ψ x‖ ≤ R * (E * B) * S :=
      commNorm_mul_le (commNorm_mul_le hx1 a1 hR) ((j1 0).trans hS1) (by positivity)
    have c1 : ‖commA φ L 1 (x.2.2 / L) * cpdC 1 (cpdC 1 Ψ) x‖ ≤ E * B * S :=
      commNorm_mul_le a1 ((j2 1 1).trans hS2) hEB
    have c2 : ‖commA φ L 3 (x.2.2 / L) * Ψ x‖ ≤ E * B * S :=
      commNorm_mul_le a3 hS0 hEB
    have c3 : ‖3 * commA φ L 2 (x.2.2 / L) * cpdC 2 Ψ x‖ ≤ 3 * (E * B) * S :=
      commNorm_mul_le (commNorm_nat_mul_le 3 h3c (by norm_num) a2) ((j1 2).trans hS1)
        (by positivity)
    have c4 : ‖3 * commA φ L 1 (x.2.2 / L) * cpdC 2 (cpdC 2 Ψ) x‖ ≤ 3 * (E * B) * S :=
      commNorm_mul_le (commNorm_nat_mul_le 3 h3c (by norm_num) a1) ((j2 2 2).trans hS2)
        (by positivity)
    have hsum : ‖commA φ L 1 (x.2.2 / L) * cpdC 1 (cpdC 1 Ψ) x +
            commA φ L 3 (x.2.2 / L) * Ψ x + 3 * commA φ L 2 (x.2.2 / L) * cpdC 2 Ψ x +
            3 * commA φ L 1 (x.2.2 / L) * cpdC 2 (cpdC 2 Ψ) x‖ ≤ 8 * (E * B * S) := by
      have := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add c1 c2)) c3)) c4)
      linarith
    have t3 : ‖(ν : ℂ) * (x.1 : ℂ) * (commA φ L 1 (x.2.2 / L) * cpdC 1 (cpdC 1 Ψ) x +
            commA φ L 3 (x.2.2 / L) * Ψ x + 3 * commA φ L 2 (x.2.2 / L) * cpdC 2 Ψ x +
            3 * commA φ L 1 (x.2.2 / L) * cpdC 2 (cpdC 2 Ψ) x)‖ ≤
          |ν| * R * (8 * (E * B * S)) := by
      rw [norm_mul, norm_mul, hν]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hx1 (abs_nonneg ν)) hsum (norm_nonneg _)
        (by positivity)
    have hf := (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add t1 t2)) t3)
    refine hf.trans (le_of_eq ?_)
    ring
  · rw [F1]
    have c1 : ‖2 * commA φ L 1 (x.2.2 / L) * cpdC 2 (cpdC 1 Ψ) x‖ ≤ 2 * (E * B) * S :=
      commNorm_mul_le (commNorm_nat_mul_le 2 h2c (by norm_num) a1) ((j2 2 1).trans hS2)
        (by positivity)
    have c2 : ‖commA φ L 2 (x.2.2 / L) * cpdC 1 Ψ x‖ ≤ E * B * S :=
      commNorm_mul_le a2 ((j1 1).trans hS1) hEB
    have hsum := (norm_add_le _ _).trans (add_le_add c1 c2)
    rw [norm_mul, norm_mul, hν]
    have hm := mul_le_mul (mul_le_mul_of_nonneg_left hx1 (abs_nonneg ν)) hsum (norm_nonneg _)
      (by positivity)
    have hpos : 0 ≤ B * E * S * (‖μ - 1‖ + R + 5 * |ν| * R) := by positivity
    nlinarith [hm, hpos]

end UnforcedLeray.Short.IIb
