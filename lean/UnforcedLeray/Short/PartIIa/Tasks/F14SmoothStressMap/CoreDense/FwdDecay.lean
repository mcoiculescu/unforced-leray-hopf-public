import UnforcedLeray.Short.PartIIa.Sub.F14_1_org.Defs
import UnforcedLeray.Short.PartIIa.Sub.F05_1
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.HeatGaussSmooth
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.HeatGaussDecay

/-!
# Part II-a, task `PartII-a:F14/1/1/3`: decay of the forward integrand

Target: `FwdIntegrandDecay` (defined in `Sub/F14_1_org/Defs.lean`).

Source of record: `the November 2 reference manuscript`, line 1458.

Proof. For `t ∈ [0, M]`, `fwdIntegrand ν μ f t (τ, y) = c(t) • G(τ - t, s • y)` with
`G = heatGauss f (fwdW ν t)`, `c(t) = exp(-(μ - 1/2) t)` and `s = exp(t/2) ≥ 1`. Since
`s ≥ 1`, `‖s • y‖ ≥ ‖y‖`, so the decay weights `(1 + ‖s • y‖)^{-E}` are at most `(1 + ‖y‖)^{-E}`.
The `(τ, y)`-operators are computed by the affine chain rule: `∂_τ` and `∂_{y_j}` carry the factor
`1` and `s ≤ exp(M/2)`, `Δ` carries `s² ≤ exp(M)`, and `radialT` equals `c • ∇G(q)(0, s • y)`,
where `‖(0, s • y)‖ = ‖s • y‖` absorbs one power of `1 + ‖s • y‖` into an exponent drop, using the
heat decay one order higher (`N + 1`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

namespace UnforcedLeray.Short.PartIIa

namespace FwdIntegrandDecayAux

theorem fderiv_smul_aff (K : ℝ × Space → CVec3) (hK : Differentiable ℝ K) (c : ℂ) (a s : ℝ)
    (p v : ℝ × Space) :
    fderiv ℝ (fun q : ℝ × Space => c • K (q.1 + a, s • q.2)) p v
      = c • fderiv ℝ K (p.1 + a, s • p.2) (v.1, s • v.2) := by
  have hA : HasFDerivAt (fun q : ℝ × Space => (q.1 + a, s • q.2))
      ((ContinuousLinearMap.fst ℝ ℝ Space).prod (s • ContinuousLinearMap.snd ℝ ℝ Space)) p :=
    (hasFDerivAt_fst.add_const a).prodMk (hasFDerivAt_snd.const_smul s)
  have hKA : HasFDerivAt (fun q : ℝ × Space => c • K (q.1 + a, s • q.2))
      (c • (fderiv ℝ K (p.1 + a, s • p.2)).comp
        ((ContinuousLinearMap.fst ℝ ℝ Space).prod (s • ContinuousLinearMap.snd ℝ ℝ Space))) p :=
    ((hK (p.1 + a, s • p.2)).hasFDerivAt.comp p hA).const_smul c
  rw [hKA.fderiv]
  simp

theorem dy_smul_aff (K : ℝ × Space → CVec3) (hK : Differentiable ℝ K) (c : ℂ) (a s : ℝ)
    (j : Fin 3) (p : ℝ × Space) :
    dy j (fun q : ℝ × Space => c • K (q.1 + a, s • q.2)) p
      = c • fderiv ℝ K (p.1 + a, s • p.2) (0, s • coordinateVector j) := by
  unfold dy
  rw [fderiv_smul_aff K hK c a s p (0, coordinateVector j)]

theorem fderiv_apply_aux (G : ℝ × Space → CVec3) (hG : Differentiable ℝ (fderiv ℝ G))
    (w r u : ℝ × Space) :
    fderiv ℝ (fun r' : ℝ × Space => fderiv ℝ G r' w) r u
      = fderiv ℝ (fderiv ℝ G) r u w := by
  rw [((hG r).hasFDerivAt.clm_apply (hasFDerivAt_const w r)).fderiv]
  simp

theorem norm_fderiv_fderiv_le (G : ℝ × Space → CVec3) (r u v : ℝ × Space) :
    ‖fderiv ℝ (fderiv ℝ G) r u v‖ ≤ ‖iteratedFDeriv ℝ 2 G r‖ * ‖u‖ * ‖v‖ := by
  have h := (iteratedFDeriv ℝ 2 G r).le_opNorm ![u, v]
  simpa [iteratedFDeriv_two_apply, Fin.prod_univ_two, mul_assoc] using h

theorem norm_coord_pair_le (s : ℝ) (hs0 : 0 ≤ s) (j : Fin 3) :
    ‖((0 : ℝ), s • coordinateVector j)‖ ≤ s := by
  have he : ‖coordinateVector j‖ = 1 := by simp [coordinateVector]
  rw [Prod.norm_def]
  exact max_le (by simpa using hs0) (le_of_eq (by rw [norm_smul, he, mul_one, Real.norm_of_nonneg hs0]))

theorem norm_zero_pair (z : Space) : ‖((0 : ℝ), z)‖ = ‖z‖ := by
  rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]

theorem norm_one_pair : ‖((1 : ℝ), (0 : Space))‖ ≤ 1 := by
  rw [Prod.norm_def]
  simp

theorem phase_norm (μ : ℂ) (t : ℝ) :
    ‖Complex.exp (-((μ - 1 / 2) * (t : ℂ)))‖ = Real.exp (-(μ.re - 1 / 2) * t) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_im, Complex.one_im, Complex.div_re, Complex.div_im]
  norm_num
  ring

theorem rpow_anti' {a b E : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hE : 0 ≤ E) :
    (1 + b) ^ (-E) ≤ (1 + a) ^ (-E) :=
  Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)

theorem rpow_succ_le (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    (1 + x) ^ (-((N : ℝ) + 1)) ≤ (1 + x) ^ (-(N : ℝ)) :=
  Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

theorem mul_rpow_succ_le (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    x * (1 + x) ^ (-((N : ℝ) + 1)) ≤ (1 + x) ^ (-(N : ℝ)) := by
  have hpos : (0 : ℝ) < 1 + x := by linarith
  have h1 : (1 + x) ^ (-((N : ℝ) + 1)) = (1 + x) ^ (-(N : ℝ)) * (1 + x)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hpos]
    congr 1
    ring
  rw [h1]
  have h2 : x * (1 + x)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hpos]
    linarith
  have hA : 0 ≤ (1 + x) ^ (-(N : ℝ)) := Real.rpow_nonneg hpos.le _
  calc x * ((1 + x) ^ (-(N : ℝ)) * (1 + x)⁻¹)
      = (1 + x) ^ (-(N : ℝ)) * (x * (1 + x)⁻¹) := by ring
    _ ≤ (1 + x) ^ (-(N : ℝ)) * 1 := mul_le_mul_of_nonneg_left h2 hA
    _ = (1 + x) ^ (-(N : ℝ)) := mul_one _

/-- Combination of the constants: `cn ≤ K`, `V ≤ D`, `Y ≤ X`. -/
theorem fin_bd {cn K V X Y D : ℝ} (hcn : cn ≤ K) (hK : 0 ≤ K) (hV : 0 ≤ V) (hVD : V ≤ D)
    (hX : 0 ≤ X) (hYX : Y ≤ X) (hY : 0 ≤ Y) :
    cn * (V * Y) ≤ K * D * X := by
  calc cn * (V * Y) ≤ K * (V * X) :=
        mul_le_mul hcn (mul_le_mul_of_nonneg_left hYX hV) (mul_nonneg hV hY) hK
    _ ≤ K * (D * X) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hVD hX) hK
    _ = K * D * X := by ring

/-- The radial operator of `c • G ∘ A` at `(τ, y)` is `c • ∇G(q)(0, s • y)`. -/
theorem radialT_form (G : ℝ × Space → CVec3) (hG : Differentiable ℝ G) (c : ℂ) (a s : ℝ)
    (τ : ℝ) (y : Space) :
    radialT (fun q : ℝ × Space => c • G (q.1 + a, s • q.2)) (τ, y)
      = c • fderiv ℝ G (τ + a, s • y) (0, s • y) := by
  have hv : y = ∑ j : Fin 3, y j • coordinateVector j := by
    ext k
    simp [coordinateVector, Pi.single_apply, mul_ite]
  have hsum : ((0 : ℝ), s • y) = ∑ j : Fin 3, y j • ((0 : ℝ), s • coordinateVector j) := by
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum]
    · simp only [Prod.snd_sum, Prod.smul_snd]
      conv_lhs => rw [hv]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact smul_comm _ _ _
  unfold radialT
  simp only [dy_smul_aff G hG c a s]
  rw [hsum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_smul]
  rw [smul_comm (y j) c]

/-- The bounds for `c • G ∘ A`, `A(q) = (q.1 + a, s • q.2)`, `1 ≤ s ≤ S`. -/
theorem aux_fwd (G : ℝ × Space → CVec3) (hGs : ContDiff ℝ ∞ G) (c : ℂ) (a s S : ℝ)
    (hs1 : 1 ≤ s) (hsS : s ≤ S) (N : ℕ) (M0 M1 M2 : ℝ) (_hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (_hM2 : 0 ≤ M2)
    (hb0 : ∀ q : ℝ × Space, ‖G q‖ ≤ M0 * (1 + ‖q.2‖) ^ (-((N : ℝ) + 1)))
    (hb1 : ∀ q : ℝ × Space, ‖fderiv ℝ G q‖ ≤ M1 * (1 + ‖q.2‖) ^ (-((N : ℝ) + 1)))
    (hb2 : ∀ q : ℝ × Space, ‖iteratedFDeriv ℝ 2 G q‖ ≤ M2 * (1 + ‖q.2‖) ^ (-((N : ℝ) + 1)))
    (τ : ℝ) (y : Space) :
    ‖c • G (τ + a, s • y)‖ ≤ ‖c‖ * (M0 * (1 + ‖s • y‖) ^ (-((N : ℝ) + 1))) ∧
    ‖dτ (fun q : ℝ × Space => c • G (q.1 + a, s • q.2)) (τ, y)‖
      ≤ ‖c‖ * (M1 * (1 + ‖s • y‖) ^ (-((N : ℝ) + 1))) ∧
    (∀ j : Fin 3, ‖dy j (fun q : ℝ × Space => c • G (q.1 + a, s • q.2)) (τ, y)‖
      ≤ ‖c‖ * (M1 * S * (1 + ‖s • y‖) ^ (-((N : ℝ) + 1)))) ∧
    ‖radialT (fun q : ℝ × Space => c • G (q.1 + a, s • q.2)) (τ, y)‖
      ≤ ‖c‖ * (M1 * (1 + ‖s • y‖) ^ (-(N : ℝ))) ∧
    ‖lapT (fun q : ℝ × Space => c • G (q.1 + a, s • q.2)) (τ, y)‖
      ≤ 3 * (‖c‖ * (M2 * S * S * (1 + ‖s • y‖) ^ (-((N : ℝ) + 1)))) := by
  have hD : Differentiable ℝ G := hGs.differentiable (by simp)
  have hdG : Differentiable ℝ (fderiv ℝ G) :=
    (hGs.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hKj : ∀ j : Fin 3, Differentiable ℝ
      (fun r : ℝ × Space => fderiv ℝ G r (0, s • coordinateVector j)) :=
    fun j => hdG.clm_apply (differentiable_const _)
  have hs0 : 0 ≤ s := by linarith
  have hS0 : 0 ≤ S := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- value
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (by simpa using hb0 (τ + a, s • y)) (norm_nonneg c)
  · -- `∂_τ`
    have hdτ : dτ (fun q : ℝ × Space => c • G (q.1 + a, s • q.2)) (τ, y)
        = c • fderiv ℝ G (τ + a, s • y) (1, 0) := by
      unfold dτ
      rw [fderiv_smul_aff G hD c a s (τ, y) (1, 0)]
      simp
    rw [hdτ, norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg c)
    calc ‖fderiv ℝ G (τ + a, s • y) (1, 0)‖
        ≤ ‖fderiv ℝ G (τ + a, s • y)‖ * ‖((1 : ℝ), (0 : Space))‖ :=
          (fderiv ℝ G (τ + a, s • y)).le_opNorm _
      _ ≤ ‖fderiv ℝ G (τ + a, s • y)‖ * 1 := mul_le_mul_of_nonneg_left norm_one_pair (norm_nonneg _)
      _ ≤ M1 * (1 + ‖s • y‖) ^ (-((N : ℝ) + 1)) := by
          rw [mul_one]
          exact hb1 (τ + a, s • y)
  · -- `∂_{y_j}`
    intro j
    rw [dy_smul_aff G hD c a s j (τ, y)]
    rw [norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg c)
    have hL : ‖fderiv ℝ G (τ + a, s • y) (0, s • coordinateVector j)‖
        ≤ (M1 * (1 + ‖s • y‖) ^ (-((N : ℝ) + 1))) * S := by
      calc ‖fderiv ℝ G (τ + a, s • y) (0, s • coordinateVector j)‖
          ≤ ‖fderiv ℝ G (τ + a, s • y)‖ * ‖((0 : ℝ), s • coordinateVector j)‖ :=
            (fderiv ℝ G (τ + a, s • y)).le_opNorm _
        _ ≤ (M1 * (1 + ‖s • y‖) ^ (-((N : ℝ) + 1))) * S :=
            mul_le_mul (hb1 (τ + a, s • y)) ((norm_coord_pair_le s hs0 j).trans hsS)
              (norm_nonneg _) ((norm_nonneg _).trans (hb1 (τ + a, s • y)))
    calc ‖fderiv ℝ G (τ + a, s • y) (0, s • coordinateVector j)‖
        ≤ (M1 * (1 + ‖s • y‖) ^ (-((N : ℝ) + 1))) * S := hL
      _ = M1 * S * (1 + ‖s • y‖) ^ (-((N : ℝ) + 1)) := by ring
  · -- radial
    rw [radialT_form G hD c a s τ y, norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg c)
    have hL : ‖fderiv ℝ G (τ + a, s • y) (0, s • y)‖
        ≤ (M1 * (1 + ‖s • y‖) ^ (-((N : ℝ) + 1))) * ‖s • y‖ := by
      calc ‖fderiv ℝ G (τ + a, s • y) (0, s • y)‖
          ≤ ‖fderiv ℝ G (τ + a, s • y)‖ * ‖((0 : ℝ), s • y)‖ :=
            (fderiv ℝ G (τ + a, s • y)).le_opNorm _
        _ = ‖fderiv ℝ G (τ + a, s • y)‖ * ‖s • y‖ := by rw [norm_zero_pair]
        _ ≤ (M1 * (1 + ‖s • y‖) ^ (-((N : ℝ) + 1))) * ‖s • y‖ :=
            mul_le_mul_of_nonneg_right (hb1 (τ + a, s • y)) (norm_nonneg _)
    calc ‖fderiv ℝ G (τ + a, s • y) (0, s • y)‖
        ≤ (M1 * (1 + ‖s • y‖) ^ (-((N : ℝ) + 1))) * ‖s • y‖ := hL
      _ = M1 * (‖s • y‖ * (1 + ‖s • y‖) ^ (-((N : ℝ) + 1))) := by ring
      _ ≤ M1 * (1 + ‖s • y‖) ^ (-(N : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_rpow_succ_le _ (norm_nonneg _) N) hM1
  · -- Laplacian
    have hlap : ∀ j : Fin 3,
        dy j (dy j (fun q : ℝ × Space => c • G (q.1 + a, s • q.2))) (τ, y)
          = c • fderiv ℝ (fderiv ℝ G) (τ + a, s • y) (0, s • coordinateVector j)
              (0, s • coordinateVector j) := by
      intro j
      have e1 : dy j (fun q : ℝ × Space => c • G (q.1 + a, s • q.2))
          = fun q : ℝ × Space =>
              c • (fun r : ℝ × Space => fderiv ℝ G r (0, s • coordinateVector j)) (q.1 + a, s • q.2) := by
        funext q
        exact dy_smul_aff G hD c a s j q
      rw [e1, dy_smul_aff (fun r : ℝ × Space => fderiv ℝ G r (0, s • coordinateVector j))
        (hKj j) c a s j (τ, y)]
      rw [fderiv_apply_aux G hdG]
    have hlapT : lapT (fun q : ℝ × Space => c • G (q.1 + a, s • q.2)) (τ, y)
        = ∑ j : Fin 3, c • fderiv ℝ (fderiv ℝ G) (τ + a, s • y) (0, s • coordinateVector j)
            (0, s • coordinateVector j) := by
      show ∑ j : Fin 3, dy j (dy j (fun q : ℝ × Space => c • G (q.1 + a, s • q.2))) (τ, y) = _
      exact Finset.sum_congr rfl (fun j _ => hlap j)
    rw [hlapT]
    have hterm : ∀ j : Fin 3,
        ‖c • fderiv ℝ (fderiv ℝ G) (τ + a, s • y) (0, s • coordinateVector j)
            (0, s • coordinateVector j)‖ ≤ ‖c‖ * (M2 * S * S * (1 + ‖s • y‖) ^ (-((N : ℝ) + 1))) := by
      intro j
      rw [norm_smul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg c)
      have hu : ‖((0 : ℝ), s • coordinateVector j)‖ ≤ S :=
        (norm_coord_pair_le s hs0 j).trans hsS
      have hbil := norm_fderiv_fderiv_le G (τ + a, s • y) (0, s • coordinateVector j)
        (0, s • coordinateVector j)
      have hB2 := hb2 (τ + a, s • y)
      have hBn : 0 ≤ M2 * (1 + ‖s • y‖) ^ (-((N : ℝ) + 1)) := (norm_nonneg _).trans hB2
      calc ‖fderiv ℝ (fderiv ℝ G) (τ + a, s • y) (0, s • coordinateVector j)
            (0, s • coordinateVector j)‖
          ≤ ‖iteratedFDeriv ℝ 2 G (τ + a, s • y)‖ * ‖((0 : ℝ), s • coordinateVector j)‖
              * ‖((0 : ℝ), s • coordinateVector j)‖ := hbil
        _ ≤ (M2 * (1 + ‖s • y‖) ^ (-((N : ℝ) + 1))) * S * S :=
            mul_le_mul (mul_le_mul hB2 hu (norm_nonneg _) hBn) hu (norm_nonneg _)
              (mul_nonneg hBn hS0)
        _ = M2 * S * S * (1 + ‖s • y‖) ^ (-((N : ℝ) + 1)) := by ring
    calc ‖∑ j : Fin 3, c • fderiv ℝ (fderiv ℝ G) (τ + a, s • y) (0, s • coordinateVector j)
            (0, s • coordinateVector j)‖
        ≤ ∑ j : Fin 3, ‖c • fderiv ℝ (fderiv ℝ G) (τ + a, s • y) (0, s • coordinateVector j)
            (0, s • coordinateVector j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3, ‖c‖ * (M2 * S * S * (1 + ‖s • y‖) ^ (-((N : ℝ) + 1))) :=
          Finset.sum_le_sum (fun j _ => hterm j)
      _ = 3 * (‖c‖ * (M2 * S * S * (1 + ‖s • y‖) ^ (-((N : ℝ) + 1)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num

end FwdIntegrandDecayAux

open FwdIntegrandDecayAux in
theorem fwdIntegrandDecay : FwdIntegrandDecay := by
  intro P ν hP hν μ f hf M N
  obtain ⟨-, hS, -⟩ := heatGaussSmooth_proof P hP f hf
  obtain ⟨C0, hC0, h0⟩ := heatGaussDecay_proof P hP f hf (Real.sqrt (ν * (Real.exp M - 1))) 0 (N + 1)
  obtain ⟨C1, hC1, h1⟩ := heatGaussDecay_proof P hP f hf (Real.sqrt (ν * (Real.exp M - 1))) 1 (N + 1)
  obtain ⟨C2, hC2, h2⟩ := heatGaussDecay_proof P hP f hf (Real.sqrt (ν * (Real.exp M - 1))) 2 (N + 1)
  push_cast at h0 h1 h2
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = Real.exp (|μ.re - 1 / 2| * M) := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = Real.exp (M / 2) := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = C0 + C1 + C1 * S + 3 * (C2 * S * S) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; exact (Real.exp_pos _).le
  have hS0 : 0 ≤ S := by rw [hSdef]; exact (Real.exp_pos _).le
  have hCS : 0 ≤ C1 * S := mul_nonneg hC1 hS0
  have hCSS : 0 ≤ C2 * S * S := mul_nonneg (mul_nonneg hC2 hS0) hS0
  have hC0D : C0 ≤ D := by rw [hDdef]; linarith
  have hC1D : C1 ≤ D := by rw [hDdef]; linarith
  have hC1SD : C1 * S ≤ D := by rw [hDdef]; linarith
  have hC2D : 3 * (C2 * S * S) ≤ D := by rw [hDdef]; linarith
  refine ⟨K * D, mul_nonneg hK0 (by rw [hDdef]; linarith), ?_⟩
  intro t ht τ y
  obtain ⟨ht0, htM⟩ := ht
  have hA : -(μ.re - 1 / 2) * t ≤ |μ.re - 1 / 2| * M := by
    have h1' := mul_le_mul_of_nonneg_right (neg_le_abs (μ.re - 1 / 2)) ht0
    have h2' := mul_le_mul_of_nonneg_left htM (abs_nonneg (μ.re - 1 / 2))
    linarith
  have hcK : ‖Complex.exp (-((μ - 1 / 2) * (t : ℂ)))‖ ≤ K := by
    rw [phase_norm, hKdef]
    exact Real.exp_le_exp.2 hA
  have hs1 : 1 ≤ Real.exp (t / 2) := Real.one_le_exp (by linarith)
  have hsS : Real.exp (t / 2) ≤ S := by
    rw [hSdef]
    exact Real.exp_le_exp.2 (by linarith)
  have hF : fwdIntegrand ν μ f t = fun q : ℝ × Space => Complex.exp (-((μ - 1 / 2) * (t : ℂ)))
      • heatGauss f (fwdW ν t) (q.1 + -t, Real.exp (t / 2) • q.2) := by
    funext q
    simp only [fwdIntegrand, sub_eq_add_neg]
  rw [hF]
  have hW : |fwdW ν t| ≤ Real.sqrt (ν * (Real.exp M - 1)) := by
    unfold fwdW
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left (by linarith [Real.exp_le_exp.2 htM]) hν.le
  have hb0 : ∀ q : ℝ × Space, ‖heatGauss f (fwdW ν t) q‖
      ≤ C0 * (1 + ‖q.2‖) ^ (-((N : ℝ) + 1)) := by
    intro q
    have := h0 (fwdW ν t) hW q
    rwa [norm_iteratedFDeriv_zero] at this
  have hb1 : ∀ q : ℝ × Space, ‖fderiv ℝ (heatGauss f (fwdW ν t)) q‖
      ≤ C1 * (1 + ‖q.2‖) ^ (-((N : ℝ) + 1)) := by
    intro q
    have := h1 (fwdW ν t) hW q
    rwa [norm_iteratedFDeriv_one] at this
  have hb2 : ∀ q : ℝ × Space, ‖iteratedFDeriv ℝ 2 (heatGauss f (fwdW ν t)) q‖
      ≤ C2 * (1 + ‖q.2‖) ^ (-((N : ℝ) + 1)) :=
    fun q => h2 (fwdW ν t) hW q
  obtain ⟨A0, A1, A2, A3, A4⟩ := aux_fwd (heatGauss f (fwdW ν t)) (hS (fwdW ν t))
    (Complex.exp (-((μ - 1 / 2) * (t : ℂ)))) (-t) (Real.exp (t / 2)) S hs1 hsS N C0 C1 C2
    hC0 hC1 hC2 hb0 hb1 hb2 τ y
  have hz : ‖y‖ ≤ ‖Real.exp (t / 2) • y‖ := by
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact le_mul_of_one_le_left (norm_nonneg y) hs1
  have hYE : (1 + ‖Real.exp (t / 2) • y‖) ^ (-((N : ℝ) + 1)) ≤ (1 + ‖y‖) ^ (-(N : ℝ)) :=
    (rpow_anti' (norm_nonneg y) hz (by positivity)).trans (rpow_succ_le _ (norm_nonneg y) N)
  have hYN : (1 + ‖Real.exp (t / 2) • y‖) ^ (-(N : ℝ)) ≤ (1 + ‖y‖) ^ (-(N : ℝ)) :=
    rpow_anti' (norm_nonneg y) hz (by positivity)
  have hYE0 : 0 ≤ (1 + ‖Real.exp (t / 2) • y‖) ^ (-((N : ℝ) + 1)) :=
    Real.rpow_nonneg (by positivity) _
  have hYN0 : 0 ≤ (1 + ‖Real.exp (t / 2) • y‖) ^ (-(N : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hX0 : 0 ≤ (1 + ‖y‖) ^ (-(N : ℝ)) := Real.rpow_nonneg (by positivity) _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact A0.trans (fin_bd hcK hK0 hC0 hC0D hX0 hYE hYE0)
  · exact A1.trans (fin_bd hcK hK0 hC1 hC1D hX0 hYE hYE0)
  · intro j
    exact (A2 j).trans (fin_bd hcK hK0 hCS hC1SD hX0 hYE hYE0)
  · exact A3.trans (fin_bd hcK hK0 hC1 hC1D hX0 hYN hYN0)
  · refine A4.trans (le_trans (le_of_eq ?_) (fin_bd hcK hK0 (mul_nonneg (by norm_num) hCSS) hC2D hX0 hYE hYE0))
    ring
end UnforcedLeray.Short.PartIIa
