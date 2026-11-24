import UnforcedLeray.Short.PartIIa.Sub.F05_1
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.HeatGaussSmooth
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.HeatGaussDecay

/-!
# Part II-a, task `PartII-a:F05/1` (decay): `AdjIntegrandDecay`

Source of record: `the November 2 reference manuscript`, the adjoint semigroup
`S(t)^*h = e^{-t}[e^{ν(1-e^{-t})Δ}h](e^{-t/2}y)` and the factor `e^{-t/2}` per spatial derivative
(current extraction lines 1446-1450).

`F(t) = e^{-(μ+1)t} · H(w(t)) ∘ A_t` with `A_t(τ, y) = (τ + t, e^{-t/2} y)` and `w(t) = adjW ν t ∈ [0, √ν]`.
The spatial derivatives come from the affine chain rule: the linear part of `A_t` sends
`(v₁, v₂) ↦ (v₁, e^{-t/2} v₂)`, so each `∂_{y_j}` costs a factor of norm at most one.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

namespace AdjIntegrandDecayAux

/-- Chain rule for `q ↦ c • K (q.1 + t, s • q.2)`. -/
lemma fderiv_smul_aff (K : ℝ × Space → CVec3) (hK : Differentiable ℝ K) (c : ℂ) (t s : ℝ)
    (p v : ℝ × Space) :
    fderiv ℝ (fun q : ℝ × Space => c • K (q.1 + t, s • q.2)) p v
      = c • fderiv ℝ K (p.1 + t, s • p.2) (v.1, s • v.2) := by
  have hA : HasFDerivAt (fun q : ℝ × Space => (q.1 + t, s • q.2))
      ((ContinuousLinearMap.fst ℝ ℝ Space).prod (s • ContinuousLinearMap.snd ℝ ℝ Space)) p :=
    (hasFDerivAt_fst.add_const t).prodMk (hasFDerivAt_snd.const_smul s)
  have hKA : HasFDerivAt (fun q : ℝ × Space => c • K (q.1 + t, s • q.2))
      (c • (fderiv ℝ K (p.1 + t, s • p.2)).comp
        ((ContinuousLinearMap.fst ℝ ℝ Space).prod (s • ContinuousLinearMap.snd ℝ ℝ Space))) p :=
    ((hK (p.1 + t, s • p.2)).hasFDerivAt.comp p hA).const_smul c
  rw [hKA.fderiv]
  simp

/-- The spatial derivative of `c • K(A_t ·)` at `(τ, y)` is `c • ∇K` in the direction `(0, s e_j)`. -/
lemma dy_smul_aff (K : ℝ × Space → CVec3) (hK : Differentiable ℝ K) (c : ℂ) (t s : ℝ)
    (j : Fin 3) (p : ℝ × Space) :
    dy j (fun q : ℝ × Space => c • K (q.1 + t, s • q.2)) p
      = c • fderiv ℝ K (p.1 + t, s • p.2) (0, s • coordinateVector j) := by
  unfold dy
  rw [fderiv_smul_aff K hK c t s p (0, coordinateVector j)]

/-- Derivative of `r ↦ fderiv G r w` in the direction `u`. -/
lemma fderiv_apply_aux (G : ℝ × Space → CVec3) (hG : Differentiable ℝ (fderiv ℝ G))
    (w r u : ℝ × Space) :
    fderiv ℝ (fun r' : ℝ × Space => fderiv ℝ G r' w) r u
      = fderiv ℝ (fderiv ℝ G) r u w := by
  rw [((hG r).hasFDerivAt.clm_apply (hasFDerivAt_const w r)).fderiv]
  simp

/-- Bilinear bound for the second derivative. -/
lemma norm_fderiv_fderiv_le (G : ℝ × Space → CVec3) (r u v : ℝ × Space) :
    ‖fderiv ℝ (fderiv ℝ G) r u v‖ ≤ ‖iteratedFDeriv ℝ 2 G r‖ * ‖u‖ * ‖v‖ := by
  have h := (iteratedFDeriv ℝ 2 G r).le_opNorm ![u, v]
  simpa [iteratedFDeriv_two_apply, Fin.prod_univ_two, mul_assoc] using h

/-- The direction `(0, s e_j)` has norm at most one when `0 ≤ s ≤ 1`. -/
lemma norm_coord_pair_le (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (j : Fin 3) :
    ‖((0 : ℝ), s • coordinateVector j)‖ ≤ 1 := by
  have he : ‖coordinateVector j‖ = 1 := by simp [coordinateVector]
  rw [Prod.norm_def]
  dsimp only
  refine max_le (by simp) ?_
  rw [norm_smul, he, mul_one, Real.norm_of_nonneg hs0]
  exact hs1

/-- The phase factor `e^{-(μ+1)t}` has norm `e^{-(Re μ + 1)t}`. -/
lemma norm_exp_mu (μ : ℂ) (t : ℝ) :
    ‖Complex.exp (-((μ + 1) * (t : ℂ)))‖ = Real.exp (-(μ.re + 1) * t) := by
  rw [Complex.norm_exp]
  congr 1
  simp
  ring

/-- The heat parameter `w(t) = √(ν(1 - e^{-t}))` stays in `[0, √ν]`. -/
lemma abs_adjW_le (ν t : ℝ) (hν : 0 < ν) : |adjW ν t| ≤ Real.sqrt ν := by
  unfold adjW
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_sqrt
  nlinarith [Real.exp_pos (-t)]

/-- Core estimate for `c • G ∘ A_t` with `A_t(q) = (q.1 + t, s • q.2)`, `0 ≤ s ≤ 1`. -/
lemma aux_bounds (G : ℝ × Space → CVec3) (hGs : ContDiff ℝ ∞ G) (c : ℂ) (t s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (N : ℝ) (M0 M1 M2 : ℝ)
    (hb0 : ∀ q : ℝ × Space, ‖G q‖ ≤ M0 * (1 + ‖q.2‖) ^ (-N))
    (hb1 : ∀ q : ℝ × Space, ‖fderiv ℝ G q‖ ≤ M1 * (1 + ‖q.2‖) ^ (-N))
    (hb2 : ∀ q : ℝ × Space, ‖iteratedFDeriv ℝ 2 G q‖ ≤ M2 * (1 + ‖q.2‖) ^ (-N))
    (τ : ℝ) (y : Space) :
    ‖c • G (τ + t, s • y)‖ ≤ ‖c‖ * (M0 * (1 + ‖s • y‖) ^ (-N)) ∧
    (∀ j : Fin 3, ‖dy j (fun q : ℝ × Space => c • G (q.1 + t, s • q.2)) (τ, y)‖
      ≤ ‖c‖ * (M1 * (1 + ‖s • y‖) ^ (-N))) ∧
    ‖lapT (fun q : ℝ × Space => c • G (q.1 + t, s • q.2)) (τ, y)‖
      ≤ 3 * (‖c‖ * (M2 * (1 + ‖s • y‖) ^ (-N))) := by
  have hD : Differentiable ℝ G := hGs.differentiable (by simp)
  have hdG : Differentiable ℝ (fderiv ℝ G) :=
    (hGs.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hKj : ∀ j : Fin 3, Differentiable ℝ
      (fun r : ℝ × Space => fderiv ℝ G r (0, s • coordinateVector j)) :=
    fun j => hdG.clm_apply (differentiable_const _)
  have hw : ∀ j : Fin 3, ‖((0 : ℝ), s • coordinateVector j)‖ ≤ 1 :=
    fun j => norm_coord_pair_le s hs0 hs1 j
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (by simpa using hb0 (τ + t, s • y)) (norm_nonneg c)
  · intro j
    rw [dy_smul_aff G hD c t s j (τ, y)]
    dsimp only
    rw [norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg c)
    refine ((fderiv ℝ G (τ + t, s • y)).le_opNorm _).trans ?_
    exact (mul_le_of_le_one_right (norm_nonneg _) (hw j)).trans (by simpa using hb1 (τ + t, s • y))
  · have hlap : ∀ j : Fin 3,
        dy j (dy j (fun q : ℝ × Space => c • G (q.1 + t, s • q.2))) (τ, y)
          = c • fderiv ℝ (fderiv ℝ G) (τ + t, s • y) (0, s • coordinateVector j)
              (0, s • coordinateVector j) := by
      intro j
      have e1 : dy j (fun q : ℝ × Space => c • G (q.1 + t, s • q.2))
          = fun q : ℝ × Space =>
              c • (fun r : ℝ × Space => fderiv ℝ G r (0, s • coordinateVector j)) (q.1 + t, s • q.2) := by
        funext q
        exact dy_smul_aff G hD c t s j q
      rw [e1, dy_smul_aff (fun r : ℝ × Space => fderiv ℝ G r (0, s • coordinateVector j))
        (hKj j) c t s j (τ, y)]
      rw [fderiv_apply_aux G hdG]
    have hlapT : lapT (fun q : ℝ × Space => c • G (q.1 + t, s • q.2)) (τ, y)
        = ∑ j : Fin 3, c • fderiv ℝ (fderiv ℝ G) (τ + t, s • y) (0, s • coordinateVector j)
            (0, s • coordinateVector j) := by
      show ∑ j : Fin 3, dy j (dy j (fun q : ℝ × Space => c • G (q.1 + t, s • q.2))) (τ, y) = _
      exact Finset.sum_congr rfl (fun j _ => hlap j)
    rw [hlapT]
    have hterm : ∀ j : Fin 3,
        ‖c • fderiv ℝ (fderiv ℝ G) (τ + t, s • y) (0, s • coordinateVector j)
            (0, s • coordinateVector j)‖ ≤ ‖c‖ * (M2 * (1 + ‖s • y‖) ^ (-N)) := by
      intro j
      rw [norm_smul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg c)
      have hbil := norm_fderiv_fderiv_le G (τ + t, s • y) (0, s • coordinateVector j)
        (0, s • coordinateVector j)
      have hwj := hw j
      have hb := hb2 (τ + t, s • y)
      have hb' : ‖iteratedFDeriv ℝ 2 G (τ + t, s • y)‖ ≤ M2 * (1 + ‖s • y‖) ^ (-N) := hb
      have hn : 0 ≤ ‖iteratedFDeriv ℝ 2 G (τ + t, s • y)‖ := norm_nonneg _
      have hnw : ‖iteratedFDeriv ℝ 2 G (τ + t, s • y)‖ * ‖((0 : ℝ), s • coordinateVector j)‖
            * ‖((0 : ℝ), s • coordinateVector j)‖ ≤ ‖iteratedFDeriv ℝ 2 G (τ + t, s • y)‖ := by
        nlinarith [mul_nonneg hn (sub_nonneg.2 hwj), mul_nonneg (mul_nonneg hn (norm_nonneg ((0 : ℝ), s • coordinateVector j))) (sub_nonneg.2 hwj)]
      linarith
    calc ‖∑ j : Fin 3, c • fderiv ℝ (fderiv ℝ G) (τ + t, s • y) (0, s • coordinateVector j)
            (0, s • coordinateVector j)‖
        ≤ ∑ j : Fin 3, ‖c • fderiv ℝ (fderiv ℝ G) (τ + t, s • y) (0, s • coordinateVector j)
            (0, s • coordinateVector j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3, ‖c‖ * (M2 * (1 + ‖s • y‖) ^ (-N)) :=
          Finset.sum_le_sum (fun j _ => hterm j)
      _ = 3 * (‖c‖ * (M2 * (1 + ‖s • y‖) ^ (-N))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num

end AdjIntegrandDecayAux

open AdjIntegrandDecayAux in
/-- **Decay of the integrand and its operators** (`AdjIntegrandDecay`). -/
theorem adjIntegrandDecay_proof : UnforcedLeray.Short.PartIIa.AdjIntegrandDecay := by
  intro P ν hP hν μ hμ Φ₀ hΦ N
  obtain ⟨-, hGs, -⟩ := heatGaussSmooth_proof P hP Φ₀ hΦ
  obtain ⟨C0, hC0, h0⟩ := heatGaussDecay_proof P hP Φ₀ hΦ (Real.sqrt ν) 0 N
  obtain ⟨C1, hC1, h1⟩ := heatGaussDecay_proof P hP Φ₀ hΦ (Real.sqrt ν) 1 N
  obtain ⟨C2, hC2, h2⟩ := heatGaussDecay_proof P hP Φ₀ hΦ (Real.sqrt ν) 2 N
  refine ⟨C0 + C1 + 3 * C2, by linarith, ?_⟩
  intro t ht τ y
  have hw : |adjW ν t| ≤ Real.sqrt ν := abs_adjW_le ν t hν
  have hs0 : 0 ≤ Real.exp (-t / 2) := (Real.exp_pos _).le
  have hs1 : Real.exp (-t / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hb0 : ∀ q : ℝ × Space, ‖heatGauss Φ₀ (adjW ν t) q‖ ≤ C0 * (1 + ‖q.2‖) ^ (-(N : ℝ)) := by
    intro q
    have := h0 (adjW ν t) hw q
    rwa [norm_iteratedFDeriv_zero] at this
  have hb1 : ∀ q : ℝ × Space,
      ‖fderiv ℝ (heatGauss Φ₀ (adjW ν t)) q‖ ≤ C1 * (1 + ‖q.2‖) ^ (-(N : ℝ)) := by
    intro q
    have := h1 (adjW ν t) hw q
    rwa [norm_iteratedFDeriv_one] at this
  have hb2 : ∀ q : ℝ × Space,
      ‖iteratedFDeriv ℝ 2 (heatGauss Φ₀ (adjW ν t)) q‖ ≤ C2 * (1 + ‖q.2‖) ^ (-(N : ℝ)) :=
    fun q => h2 (adjW ν t) hw q
  obtain ⟨A0, A1, A2⟩ := aux_bounds (heatGauss Φ₀ (adjW ν t)) (hGs (adjW ν t))
    (Complex.exp (-((μ + 1) * (t : ℂ)))) t (Real.exp (-t / 2)) hs0 hs1 (N : ℝ) C0 C1 C2
    hb0 hb1 hb2 τ y
  have hX : ‖Real.exp (-t / 2) • y‖ = Real.exp (-t / 2) * ‖y‖ := by
    rw [norm_smul, Real.norm_of_nonneg hs0]
  have hEpos : 0 ≤ Real.exp (-(μ.re + 1) * t) := (Real.exp_pos _).le
  have hXnn : 0 ≤ (1 + Real.exp (-t / 2) * ‖y‖) ^ (-(N : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hEX : 0 ≤ Real.exp (-(μ.re + 1) * t) * (1 + Real.exp (-t / 2) * ‖y‖) ^ (-(N : ℝ)) :=
    mul_nonneg hEpos hXnn
  rw [hX, norm_exp_mu] at A0
  simp only [hX, norm_exp_mu] at A1 A2
  have hF : adjIntegrand ν μ Φ₀ t = fun q : ℝ × Space => Complex.exp (-((μ + 1) * (t : ℂ)))
      • heatGauss Φ₀ (adjW ν t) (q.1 + t, Real.exp (-t / 2) • q.2) := rfl
  unfold adjDecayBound
  rw [hF]
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans A0 ?_
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ C1 + 3 * C2) hEX]
  · intro j
    refine le_trans (A1 j) ?_
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ C0 + 3 * C2) hEX]
  · refine le_trans A2 ?_
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ C0 + C1) hEX]

end UnforcedLeray.Short.PartIIa
