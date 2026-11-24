import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3_1_1
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.Equation.AdjTestCalc
import UnforcedLeray.Units.B0424.Tests

/-!


Source `the November 2 reference manuscript` lines 1426-1442. Statement
`AdjWindowTestIdentity` (`Sub/PartII-a_F09_3_1_1.lean`), proved unchanged.

Proof. Write `Ψa = adjTest χ τ₀ φ c`, `Ψd = adjTest χ' τ₀ φ c`, `ΨB = adjTest χ τ₀ ψ c` with
`ψ(X) = (1 - X₁) (-tD φ - ν sLap φ)(X)`.
* `AdjTestCalc` and `AdjLocalIdentity` at `Ψa` give `∫ dotL((μ̄+1)Ψa - Ψd + ΨB)(W) = ∫ dotL(Ψa)(Fr)`.
* The reflection `τ = τ₀ - t` (measure preserving on `ℝ × Space`) turns the two target integrals into
  `∫ dotL(ΨB)(W)` and `∫ (dotL(Ψd)(W) - (1+μ̄) dotL(Ψa)(W) + dotL(Ψa)(Fr))`.
* Integrability of each piece comes from the hypotheses applied to `Ψa`, `Ψd`, `ΨB` (smooth, compactly
  supported), and the scalar identities are pointwise `ring` computations.
Helpers carry the prefix `awt`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Parabolic

/-- The derivative-free pulled-back coefficient `ψ(X) = (1 - X₁) (-tD φ - ν sLap φ)(X)`. -/
def awtPsi (ν : ℝ) (φ : PS 3 → ℝ) : PS 3 → ℝ :=
  fun X => (1 - X.1) * (-tD φ X - ν * sLap φ X)

theorem awt_dotL_single (c : Fin 3) (r : ℂ) (w : CVec3) :
    dotL (r • EuclideanSpace.single c (1 : ℂ)) w = r * w c := by
  rw [dotL_apply, Finset.sum_eq_single c]
  · simp [PiLp.single_apply]
  · intro b _ hb
    simp [PiLp.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem awt_psi_isST (ν : ℝ) {φ : PS 3 → ℝ} (hφ : IsSTTest φ) : IsSTTest (awtPsi ν φ) := by
  have hsL : IsSTTest (sLap φ) := by
    have h : sLap φ = sD2 0 0 φ + sD2 1 1 φ + sD2 2 2 φ := by
      funext X
      simp [sLap, Fin.sum_univ_three]
    rw [h]
    exact ((hφ.sD2 0 0).add (hφ.sD2 1 1)).add (hφ.sD2 2 2)
  have hT : IsSTTest (tD φ) := hφ.dirD tdir
  have hζ : IsSTTest (fun X : PS 3 => -tD φ X - ν * sLap φ X) := by
    have h2 : (fun X : PS 3 => -tD φ X - ν * sLap φ X) = (-1 : ℝ) • tD φ + (-ν) • sLap φ := by
      funext X
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h2]
    exact (hT.smul (-1)).add (hsL.smul (-ν))
  refine ⟨?_, ?_⟩
  · exact (contDiff_const.sub contDiff_fst).mul hζ.1
  · exact HasCompactSupport.mul_left (f := fun X : PS 3 => 1 - X.1) hζ.2

/-- Smoothness and compact support of `adjTest` for a smooth `χ` vanishing off `(-2, 2)`
(the proof of `adjTestSmooth`, with the cutoff hypotheses taken separately so that `χ'` is allowed). -/
theorem awt_adjTest_cs (χ : ℝ → ℝ) (hχs : ContDiff ℝ ∞ χ)
    (hχz : ∀ t : ℝ, ¬ (-2 < t ∧ t < 2) → χ t = 0) (τ₀ : ℝ) (φ : PS 3 → ℝ) (hφ : IsSTTest φ)
    (c : Fin 3) :
    ContDiff ℝ ∞ (adjTest χ τ₀ φ c) ∧ HasCompactSupport (adjTest χ τ₀ φ c) := by
  have hφs : ContDiff ℝ ∞ φ := hφ.1
  obtain ⟨R, hR0, hR⟩ := UnforcedLeray.B0424.exists_bound_space hφ.2
  have ht : ContDiff ℝ ∞ (fun p : ℝ × Space => τ₀ - p.1) := contDiff_const.sub contDiff_fst
  have hm : ContDiff ℝ ∞ (fun p : ℝ × Space =>
      ((1 - Real.exp (-(τ₀ - p.1)), Real.exp (-(τ₀ - p.1) / 2) • p.2) : PS 3)) :=
    ContDiff.prodMk (contDiff_const.sub (Real.contDiff_exp.comp ht.neg))
      ((Real.contDiff_exp.comp (ht.neg.div_const 2)).smul contDiff_snd)
  have hs : ContDiff ℝ ∞ (fun p : ℝ × Space => Real.exp (-(3 * (τ₀ - p.1) / 2)) * χ (τ₀ - p.1) *
      φ (1 - Real.exp (-(τ₀ - p.1)), Real.exp (-(τ₀ - p.1) / 2) • p.2)) := by
    have h0 : ContDiff ℝ ∞ (fun p : ℝ × Space => Real.exp (-(3 * (τ₀ - p.1) / 2))) :=
      Real.contDiff_exp.comp
        (((contDiff_const.mul ht : ContDiff ℝ ∞ (fun p : ℝ × Space => (3 : ℝ) * (τ₀ - p.1)))).div_const 2).neg
    have h1 : ContDiff ℝ ∞ (fun p : ℝ × Space => χ (τ₀ - p.1)) :=
      hχs.comp (contDiff_const.sub contDiff_fst)
    exact (h0.mul h1).mul (hφs.comp hm)
  refine ⟨?_, ?_⟩
  · unfold adjTest
    exact (Complex.ofRealCLM.contDiff.comp hs).smul contDiff_const
  · refine HasCompactSupport.intro
      (K := Icc (τ₀ - 2) (τ₀ + 2) ×ˢ Metric.closedBall (0 : Space) (R * Real.exp 1))
      ((isCompact_Icc).prod (isCompact_closedBall _ _)) fun p hp => ?_
    by_cases h1 : p.1 ∈ Icc (τ₀ - 2) (τ₀ + 2)
    · have hy : R * Real.exp 1 < ‖p.2‖ := by
        by_contra h
        exact hp ⟨h1, by rw [Metric.mem_closedBall, dist_zero_right]; exact not_lt.1 h⟩
      by_cases hc : -2 < τ₀ - p.1 ∧ τ₀ - p.1 < 2
      · have hexp : Real.exp (-1) ≤ Real.exp (-(τ₀ - p.1) / 2) :=
          Real.exp_le_exp.2 (by linarith [hc.2])
        have hnorm : R < ‖Real.exp (-(τ₀ - p.1) / 2) • p.2‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          have key : R * Real.exp 1 * Real.exp (-1) = R := by
            rw [mul_assoc, ← Real.exp_add]; simp
          calc R = R * Real.exp 1 * Real.exp (-1) := key.symm
            _ < ‖p.2‖ * Real.exp (-1) := mul_lt_mul_of_pos_right hy (Real.exp_pos _)
            _ = Real.exp (-1) * ‖p.2‖ := mul_comm _ _
            _ ≤ Real.exp (-(τ₀ - p.1) / 2) * ‖p.2‖ :=
              mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
        have hφz := hR (1 - Real.exp (-(τ₀ - p.1))) _ hnorm
        simp only [adjTest, hφz, mul_zero, Complex.ofReal_zero, zero_smul]
      · simp only [adjTest, hχz _ hc, mul_zero, zero_mul, Complex.ofReal_zero, zero_smul]
    · have hc : ¬ (-2 < τ₀ - p.1 ∧ τ₀ - p.1 < 2) := fun h =>
        h1 ⟨by linarith [h.2], by linarith [h.1]⟩
      simp only [adjTest, hχz _ hc, mul_zero, zero_mul, Complex.ofReal_zero, zero_smul]

/-- Reflection `τ ↦ τ₀ - τ` on `ℝ × Space` (measure preserving). -/
theorem awtRefl (τ₀ : ℝ) (k : ℝ × Space → ℂ) :
    ∫ p : ℝ × Space, k (τ₀ - p.1, p.2) = ∫ p : ℝ × Space, k p := by
  have hm : MeasurePreserving (fun p : ℝ × Space => (-p.1, p.2))
      ((volume : Measure ℝ).prod (volume : Measure Space))
      ((volume : Measure ℝ).prod (volume : Measure Space)) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (MeasurePreserving.id (volume : Measure Space))
  have hemb : MeasurableEmbedding (fun p : ℝ × Space => (-p.1, p.2)) :=
    measurableEmbedding_neg.prodMap MeasurableEmbedding.id
  have h1 : ∫ p : ℝ × Space, k (τ₀ - p.1, p.2) ∂((volume : Measure ℝ).prod (volume : Measure Space))
      = ∫ q : ℝ × Space, k ((τ₀, (0 : Space)) + q)
          ∂((volume : Measure ℝ).prod (volume : Measure Space)) := by
    have := hm.integral_comp hemb (fun q : ℝ × Space => k ((τ₀, (0 : Space)) + q))
    simpa [sub_eq_add_neg] using this
  have h2 := integral_add_left_eq_self
    (μ := ((volume : Measure ℝ).prod (volume : Measure Space))) k ((τ₀, (0 : Space)) : ℝ × Space)
  rw [Measure.volume_eq_prod]
  exact h1.trans h2

theorem awtReflEq (τ₀ : ℝ) (k k' : ℝ × Space → ℂ)
    (h : ∀ q : ℝ × Space, k (τ₀ - q.1, q.2) = k' q) :
    ∫ p : ℝ × Space, k p = ∫ p : ℝ × Space, k' p :=
  (awtRefl τ₀ k).symm.trans (integral_congr_ae (Eventually.of_forall h))

theorem awtE (t : ℝ) : Real.exp (-(5 * t / 2)) = Real.exp (-(3 * t / 2)) * Real.exp (-t) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- **Task `PartII-a:F09/3/1/1/8`**: the local identity at the pulled-back test (tex 1426-1442). -/
theorem adjWindowTestIdentity : AdjWindowTestIdentity := by
  intro ν μ W Fr hW hFr hI χ hχ τ₀ c φ hφ
  have hχs : ContDiff ℝ ∞ χ := hχ.smooth
  have hχ' : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχs).2
  have hχz : ∀ t : ℝ, ¬ (-2 < t ∧ t < 2) → χ t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport (fun h => ht (hχ.support h))
  have hχ'z : ∀ t : ℝ, ¬ (-2 < t ∧ t < 2) → deriv χ t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport (fun h => ht (hχ.support (tsupport_deriv_subset h)))
  have hψ := awt_psi_isST ν hφ
  obtain ⟨hΨa_s, hΨa_c⟩ := awt_adjTest_cs χ hχs hχz τ₀ φ hφ c
  obtain ⟨hΨd_s, hΨd_c⟩ := awt_adjTest_cs (deriv χ) hχ' hχ'z τ₀ φ hφ c
  obtain ⟨hΨB_s, hΨB_c⟩ := awt_adjTest_cs χ hχs hχz τ₀ (awtPsi ν φ) hψ c
  have hWa := hW _ hΨa_s.continuous hΨa_c
  have hWd := hW _ hΨd_s.continuous hΨd_c
  have hWB := hW _ hΨB_s.continuous hΨB_c
  have hFa := hFr _ hΨa_s.continuous hΨa_c
  have hI' := hI _ hΨa_s hΨa_c
  -- pointwise: the adjoint calculus split into three adjTest pieces
  have hII : ∀ q : ℝ × Space,
      dotL (((starRingEnd ℂ) μ • adjTest χ τ₀ φ c + L0 ν (adjTest χ τ₀ φ c)) q) (W q)
        = ((starRingEnd ℂ) μ + 1) * dotL (adjTest χ τ₀ φ c q) (W q)
          - dotL (adjTest (deriv χ) τ₀ φ c q) (W q)
          + dotL (adjTest χ τ₀ (awtPsi ν φ) c q) (W q) := by
    intro q
    rw [adjTestCalc ν μ χ hχ τ₀ φ hφ c q]
    simp only [adjTest, awtPsi, awt_dotL_single]
    push_cast
    ring
  have hSplit : ∫ q : ℝ × Space,
      dotL (((starRingEnd ℂ) μ • adjTest χ τ₀ φ c + L0 ν (adjTest χ τ₀ φ c)) q) (W q)
        = ((starRingEnd ℂ) μ + 1) * (∫ q : ℝ × Space, dotL (adjTest χ τ₀ φ c q) (W q))
          - (∫ q : ℝ × Space, dotL (adjTest (deriv χ) τ₀ φ c q) (W q))
          + (∫ q : ℝ × Space, dotL (adjTest χ τ₀ (awtPsi ν φ) c q) (W q)) := by
    have i1 : Integrable (fun q : ℝ × Space =>
        ((starRingEnd ℂ) μ + 1) * dotL (adjTest χ τ₀ φ c q) (W q)
          - dotL (adjTest (deriv χ) τ₀ φ c q) (W q)) volume :=
      (hWa.const_mul _).sub hWd
    have i2 : Integrable (fun q : ℝ × Space =>
        ((starRingEnd ℂ) μ + 1) * dotL (adjTest χ τ₀ φ c q) (W q)) volume :=
      hWa.const_mul _
    rw [integral_congr_ae (Eventually.of_forall hII), integral_add i1 hWB,
      integral_sub i2 hWd, integral_const_mul]
  -- the left side of the target, reflected
  have hL : ∫ p : ℝ × Space, ((Real.exp (-(5 * p.1 / 2)) * χ p.1 : ℝ) : ℂ) * W (τ₀ - p.1, p.2) c *
      ((-tD φ (1 - Real.exp (-p.1), Real.exp (-p.1 / 2) • p.2) -
        ν * sLap φ (1 - Real.exp (-p.1), Real.exp (-p.1 / 2) • p.2) : ℝ) : ℂ)
      = ∫ q : ℝ × Space, dotL (adjTest χ τ₀ (awtPsi ν φ) c q) (W q) := by
    refine awtReflEq τ₀ _ _ (fun q => ?_)
    simp only [sub_sub_cancel, adjTest, awtPsi, awt_dotL_single, Prod.mk.eta]
    rw [awtE (τ₀ - q.1)]
    push_cast
    ring
  -- the right side of the target, reflected
  have hR : ∫ p : ℝ × Space, ((Real.exp (-(3 * p.1 / 2)) : ℝ) : ℂ) *
      ((((deriv χ p.1 : ℝ) : ℂ) - (1 + (starRingEnd ℂ) μ) * (χ p.1 : ℂ)) *
          W (τ₀ - p.1, p.2) c + (χ p.1 : ℂ) * Fr (τ₀ - p.1, p.2) c) *
        (φ (1 - Real.exp (-p.1), Real.exp (-p.1 / 2) • p.2) : ℂ)
      = ∫ q : ℝ × Space, (dotL (adjTest (deriv χ) τ₀ φ c q) (W q)
          - (1 + (starRingEnd ℂ) μ) * dotL (adjTest χ τ₀ φ c q) (W q)
          + dotL (adjTest χ τ₀ φ c q) (Fr q)) := by
    refine awtReflEq τ₀ _ _ (fun q => ?_)
    simp only [sub_sub_cancel, adjTest, awt_dotL_single, Prod.mk.eta]
    push_cast
    ring
  have hRsplit : ∫ q : ℝ × Space, (dotL (adjTest (deriv χ) τ₀ φ c q) (W q)
          - (1 + (starRingEnd ℂ) μ) * dotL (adjTest χ τ₀ φ c q) (W q)
          + dotL (adjTest χ τ₀ φ c q) (Fr q))
      = (∫ q : ℝ × Space, dotL (adjTest (deriv χ) τ₀ φ c q) (W q))
          - (1 + (starRingEnd ℂ) μ) * (∫ q : ℝ × Space, dotL (adjTest χ τ₀ φ c q) (W q))
          + (∫ q : ℝ × Space, dotL (adjTest χ τ₀ φ c q) (Fr q)) := by
    have j1 : Integrable (fun q : ℝ × Space =>
        dotL (adjTest (deriv χ) τ₀ φ c q) (W q)
          - (1 + (starRingEnd ℂ) μ) * dotL (adjTest χ τ₀ φ c q) (W q)) volume :=
      hWd.sub (hWa.const_mul _)
    have j2 : Integrable (fun q : ℝ × Space =>
        (1 + (starRingEnd ℂ) μ) * dotL (adjTest χ τ₀ φ c q) (W q)) volume :=
      hWa.const_mul _
    rw [integral_add j1 hFa, integral_sub hWd j2, integral_const_mul]
  linear_combination hL - hR - hRsplit + hI' - hSplit

end UnforcedLeray.Short.PartIIa
