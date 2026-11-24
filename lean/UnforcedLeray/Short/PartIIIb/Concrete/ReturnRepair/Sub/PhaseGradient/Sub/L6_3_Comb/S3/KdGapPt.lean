import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S3.KdGapMeas

/-!
# `kdGapPt` (`PartIII-b:C/rep/2/6/3/3/5`, source 3603-3626, 3800-3807, 4171-4200, 5223)

Pointwise gap bound for the `y`-derivatives of `kerF (Kd) (h,z)`, `h > 0`: by `kdm_iteratedFDeriv`
the derivative is `-(l/2)` times a difference of `sepPhi`-derivatives, each bounded by
`sepGapPointwise` (for `μ` and `μ+1`) with the majorant `sepMajorant`; `gMaj` is exactly
`(l/2)(sepMajorant μ + sepMajorant (μ+1))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The explicit majorant is nonnegative for `l > 0`. -/
lemma kdp_sepMajorant_nonneg (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (n : ℕ)
    (p : ℝ × Space) (hp : 0 < p.1) : 0 ≤ sepMajorant μ T τ n p := by
  unfold sepMajorant
  have h1 : 0 ≤ p.1 ^ (2 * μ.re + 2) := Real.rpow_nonneg hp.le _
  have h2 : 0 ≤ (1 + p.1 * ‖p.2‖) ^ (-(4 + (n : ℝ))) :=
    Real.rpow_nonneg (by have := mul_nonneg hp.le (norm_nonneg p.2); linarith) _
  have h3 : 0 ≤ IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2) := by
    unfold IIIa.tensorNorm
    exact Real.sqrt_nonneg _
  exact mul_nonneg (mul_nonneg h1 h2) h3

/-- **(L5)** pointwise gap bound in `(h,z)`. -/
theorem kdGapPt : KdGapPt := by
  intro ν μ rOut P T hd τ y₀ hy₀ i
  obtain ⟨hν, hμ, hr, hP, hS, _⟩ := hd
  have ha : -(1 / 4) < ((μ : ℂ)).re := by
    rw [Complex.ofReal_re]; exact hμ
  have hb : -(1 / 4) < ((μ : ℂ) + 1).re := by
    rw [Complex.add_re, Complex.ofReal_re, Complex.one_re]; linarith
  obtain ⟨ε1, hε1, C1, hC1, hb1⟩ :=
    sepGapPointwise IIIa.sepKernelBounds ν (μ : ℂ) rOut P T hν ha hr hP hS τ i y₀ hy₀
  obtain ⟨ε2, hε2, C2, hC2, hb2⟩ :=
    sepGapPointwise IIIa.sepKernelBounds ν ((μ : ℂ) + 1) rOut P T hν hb hr hP hS τ i y₀ hy₀
  obtain ⟨ε3, hε3, hball⟩ := Metric.isOpen_iff.1 (isOpen_gap rOut) y₀ hy₀
  refine ⟨min (min ε1 ε2) ε3, lt_min (lt_min hε1 hε2) hε3, ?_, C1 + C2, add_nonneg hC1 hC2, ?_⟩
  · intro y hy
    exact hball (Metric.ball_subset_ball (min_le_right _ _) hy)
  · intro n hn p hp y hy
    have hy1 : y ∈ Metric.ball y₀ ε1 :=
      Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hy
    have hy2 : y ∈ Metric.ball y₀ ε2 :=
      Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hy
    have hl : Real.exp (-p.1 / 2) ∈ Ioo (0 : ℝ) 1 :=
      ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith)⟩
    have hk := kdm_iteratedFDeriv ν μ hν T τ i n hn p hp y
    have hM1 := kdp_sepMajorant_nonneg (μ : ℂ) T τ n (Real.exp (-p.1 / 2), p.2) (Real.exp_pos _)
    have hM2 := kdp_sepMajorant_nonneg ((μ : ℂ) + 1) T τ n (Real.exp (-p.1 / 2), p.2)
      (Real.exp_pos _)
    have e1 : ‖iteratedFDeriv ℝ n (fun y => sepPhi ν (μ : ℂ) T τ i (Real.exp (-p.1 / 2), p.2) y) y‖
        ≤ C1 * sepMajorant (μ : ℂ) T τ n (Real.exp (-p.1 / 2), p.2) :=
      hb1 y hy1 (Real.exp (-p.1 / 2)) hl p.2 n hn
    have e2 : ‖iteratedFDeriv ℝ n (fun y => sepPhi ν ((μ : ℂ) + 1) T τ i (Real.exp (-p.1 / 2), p.2) y) y‖
        ≤ C2 * sepMajorant ((μ : ℂ) + 1) T τ n (Real.exp (-p.1 / 2), p.2) :=
      hb2 y hy2 (Real.exp (-p.1 / 2)) hl p.2 n hn
    have hc : 0 < Real.exp (-p.1 / 2) / 2 := by positivity
    have hnorm : ‖(((-(Real.exp (-p.1 / 2) / 2)) : ℝ) : ℂ)‖ = Real.exp (-p.1 / 2) / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hc]
    have hfin := (norm_sub_le _ _).trans (add_le_add e1 e2)
    rw [hk, norm_smul, hnorm]
    unfold gMaj
    have hmul := mul_le_mul_of_nonneg_left hfin hc.le
    nlinarith [hmul, mul_nonneg (mul_nonneg hc.le hC1) hM2, mul_nonneg (mul_nonneg hc.le hC2) hM1]

end UnforcedLeray.Short.PartIIIb.Concrete
