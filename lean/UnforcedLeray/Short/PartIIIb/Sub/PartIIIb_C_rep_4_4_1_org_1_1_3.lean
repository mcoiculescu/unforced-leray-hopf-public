import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Defs
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16

/-!
# `PartIII-b:C/rep/4/4/1/org/1/1/3`: `sepWreYoungL2` from `sep:young`

Source `the November 2 reference manuscript`
3631-3646 (`sep:young`) and 3648-3668 (`sep:repair-energy`, `j = 0`), 4163-4166.
`sep:young` with `p = 22/19`, `q = 2`, `b = 11/7` (`1 + 1/2 = 19/22 + 7/11`) gives the exponent
`-4 + 3/b = -23/11`; the only input is `IIIa.SepYoung` (task `PartIII-a:T16`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

private theorem euclid_re_le (w : Fin 3 → ℂ) :
    ‖(WithLp.toLp 2 fun i => (w i).re : Space)‖ ≤ Real.sqrt 3 * ‖w‖ := by
  rw [EuclideanSpace.norm_eq]
  have h : ∀ i, ‖(WithLp.toLp 2 fun i => (w i).re : Space) i‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    intro i
    have h1 : ‖(WithLp.toLp 2 fun i => (w i).re : Space) i‖ ≤ ‖w i‖ := by
      simpa using Complex.abs_re_le_norm (w i)
    exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans (norm_le_pi_norm w i)) 2
  calc Real.sqrt (∑ i, ‖(WithLp.toLp 2 fun i => (w i).re : Space) i‖ ^ 2)
      ≤ Real.sqrt (∑ _i : Fin 3, ‖w‖ ^ 2) := Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => h i)
    _ = Real.sqrt 3 * ‖w‖ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]
      norm_num

theorem sepWreYoungL2_of (hY : UnforcedLeray.Short.IIIa.SepYoung) (a b : ℝ) (ha : -(1/4) < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν R P : ℝ, 0 < ν → 0 < R → 0 < P → ∀ μ ∈ Icc a b,
      ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
      IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T →
      IIIa.ltauLq P 2 (fun τ y => if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
          then ‖sepWre ν μ T τ y‖ₑ else 0) ≤
        ENNReal.ofReal (C * (R * Real.sqrt ν) ^ (-(23 / 11 : ℝ))) *
          IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) := by
  have hK : IsCompact ((fun x : ℝ => (x : ℂ)) '' Icc a b) :=
    isCompact_Icc.image Complex.continuous_ofReal
  have hKre : ∀ μ ∈ (fun x : ℝ => (x : ℂ)) '' Icc a b, -(1 / 4) < μ.re := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using lt_of_lt_of_le ha hx.1
  obtain ⟨C0, hC0, hC⟩ := hY _ hK hKre 0 (22 / 19) 2 (11 / 7) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by
      refine ⟨2 * a + 3 / (22 / 19), ?_, ?_⟩
      · have : (3 : ℝ) / (22 / 19) = 57 / 22 := by norm_num
        rw [this]; linarith
      · rintro _ ⟨x, hx, rfl⟩
        simp only [Complex.ofReal_re]
        linarith [hx.1])
  have hs : Real.sqrt (5 / 6) < 1 := by
    rw [Real.sqrt_lt' one_pos]; norm_num
  have hs0 : 0 < Real.sqrt (5 / 6) := Real.sqrt_pos.2 (by norm_num)
  set c : ℝ := 1 - Real.sqrt (5 / 6) with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  refine ⟨Real.sqrt 3 * C0 * c ^ (-(23 / 11 : ℝ)), by positivity, ?_⟩
  intro ν R P hν hR hP μ hμ T hT
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hrOut : Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6) * Real.sqrt ν := by
    rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
  have hrIn : 0 < R * Real.sqrt ν := mul_pos hR hsν
  have hD : R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6) = c * (R * Real.sqrt ν) := by
    rw [hrOut, hcdef]; ring
  have hlt : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν := by
    have : 0 < c * (R * Real.sqrt ν) := mul_pos hc hrIn
    linarith
  have hnn : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have h1 := hC ν hν (μ : ℂ) ⟨μ, hμ, rfl⟩ (R * Real.sqrt (5 * ν / 6)) (R * Real.sqrt ν) P
    hnn hlt hP T hT
  have he : (-4 - ((0 : ℕ) : ℝ) + 3 / (11 / 7) : ℝ) = -(23 / 11) := by norm_num
  rw [hD, he, Real.mul_rpow hc.le hrIn.le] at h1
  have hpt : ∀ τ y, (if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
        then ‖sepWre ν μ T τ y‖ₑ else 0) ≤
      ENNReal.ofReal (Real.sqrt 3) * IIIa.youngDerivNorm ν (μ : ℂ) T 0 (R * Real.sqrt ν) τ y := by
    intro τ y
    unfold IIIa.youngDerivNorm
    split_ifs with hy
    · unfold IIIa.wDerivNorm
      rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_zero,
        ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (euclid_re_le _)
    · simp
  calc IIIa.ltauLq P 2 (fun τ y => if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
          then ‖sepWre ν μ T τ y‖ₑ else 0)
      ≤ IIIa.ltauLq P 2 (fun τ y => ENNReal.ofReal (Real.sqrt 3) *
          IIIa.youngDerivNorm ν (μ : ℂ) T 0 (R * Real.sqrt ν) τ y) :=
        IIIa.ltauLq_mono P 2 (by norm_num) hpt
    _ = ENNReal.ofReal (Real.sqrt 3) *
          IIIa.ltauLq P 2 (IIIa.youngDerivNorm ν (μ : ℂ) T 0 (R * Real.sqrt ν)) :=
        IIIa.ltauLq_const_mul P 2 (by norm_num) _ ENNReal.ofReal_ne_top _
    _ ≤ ENNReal.ofReal (Real.sqrt 3) * (ENNReal.ofReal (C0 * (c ^ (-(23 / 11 : ℝ)) *
          (R * Real.sqrt ν) ^ (-(23 / 11 : ℝ)))) * IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T)) :=
        by gcongr
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
        congr 2
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
end
