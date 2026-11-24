import UnforcedLeray.Short.PartIIIb.Concrete.YoungFlat

/-!
# Flat all-moments, concrete version (source 4637-4640, proof 4686-4693)

Conditional on the tested source norm bound, the state bound at `H = 2/ν` and the later-output
bound, `FlatAllMomentsC` holds. Constants are taken in absolute value so that no sign is needed.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb

namespace ConcreteYF

/-- For `c = ν⁻²`, `ν^{3+2μ}/c = ν^{5+2μ}`. -/
theorem rpow_div_c_flat (ν μ : ℝ) (hν : 0 < ν) :
    ν ^ (3 + 2 * μ) / (ν⁻¹ ^ 2) = ν ^ (5 + 2 * μ) := by
  have h : (5 + 2 * μ) = (3 + 2 * μ) + 2 := by ring
  rw [h, Real.rpow_add hν (3 + 2 * μ) 2, Real.rpow_two]
  field_simp

/-- `‖F_+(2/ν, 0)‖ ≠ 0` (the base `a(2/ν)/a(0) = 3`). -/
theorem Fpm_true_two_ne_zero (lam κ : ℂ) (ν : ℝ) (hν : 0 < ν) :
    ‖Fpm true lam κ ν (2 / ν) 0‖ ≠ 0 := by
  have h2 : ν * (2 / ν) = 2 := by
    field_simp [hν.ne']
  have hb : aOf ν (2 / ν) / aOf ν 0 = 3 := by
    simp only [aOf, mul_zero, add_zero, h2]
    norm_num
  have hpow : (((3 : ℝ) : ℂ)) ^ κ ≠ 0 := by
    intro h
    have h3 := ((Complex.cpow_eq_zero_iff _ _).1 h).1
    norm_num at h3
  unfold Fpm
  simp only [↓reduceIte, hb]
  exact norm_ne_zero_iff.mpr (mul_ne_zero (Complex.exp_ne_zero _) hpow)

/-- The tested norm is nonnegative. -/
theorem testedNorm_nonneg_flat (pk : YoungPkg) (lam κ : ℂ) (ν : ℝ) (μ : ℂ) (Tf : ℝ)
    (f : ℝ → pk.X) : 0 ≤ testedNorm pk lam κ ν μ Tf f := by
  unfold testedNorm
  apply setIntegral_nonneg measurableSet_Ioc
  intro t ht
  have ht0 : 0 < t := ht.1
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (inv_nonneg.mpr (norm_nonneg _)))
    (norm_nonneg _)

/-- `flat-return:all-moments`, concrete (source 4637-4640, proof 4686-4693). -/
theorem flatAllMomentsC (S : ℕ → FlatSetting) (ν : ℕ → ℝ) (lam κ : ℂ) (μ a : ℝ) :
    FlatAllMomentsC S ν lam κ μ a := by
  intro hyp hT hSt hLo
  obtain ⟨CT, NT, hT⟩ := hT
  obtain ⟨CS, NS, hS⟩ := hSt
  obtain ⟨CL, NL, hL⟩ := hLo
  refine ⟨|CL| * |CS| * |CT|, max NT (max NS NL), ?_⟩
  intro n hn k hk B hB
  have hnT : NT ≤ n := by omega
  have hnS : NS ≤ n := by omega
  have hnL : NL ≤ n := by omega
  have hνpos : 0 < ν n := hyp.young.1 n
  have hc : (S n).c = (ν n)⁻¹ ^ 2 := hyp.c_eq n
  have hcpow : ‖Nnu lam κ (ν n)‖ * ν n ^ (3 + 2 * μ) / (S n).c
      = ‖Nnu lam κ (ν n)‖ * ν n ^ (5 + 2 * μ) := by
    rw [hc, mul_div_assoc, rpow_div_c_flat (ν n) μ hνpos]
  have hL' := hL n hnL k hk B hB
  rw [hcpow] at hL'
  have hS' := hS n hnS B hB
  have hT' := hT n hnT B hB
  have hbN0 : 0 ≤ bNorm a B := ENNReal.toReal_nonneg
  have hF : ‖Fpm true lam κ (ν n) (2 / ν n) 0‖ ≠ 0 := Fpm_true_two_ne_zero lam κ (ν n) hνpos
  have hTN0 : 0 ≤ testedNorm (S n).pk lam κ (ν n) (μ : ℂ) (1.1 / ν n) ((S n).gB B) :=
    testedNorm_nonneg_flat _ _ _ _ _ _ _
  -- the state bound, then absolute values
  have hDle : ‖duhamel (S n).pk (μ : ℂ) ((S n).gB B) (2 / ν n)‖ ≤
      |CS| * ‖Fpm true lam κ (ν n) (2 / ν n) 0‖ * (|CT| * bNorm a B) := by
    have h1 : CS * ‖Fpm true lam κ (ν n) (2 / ν n) 0‖ *
        testedNorm (S n).pk lam κ (ν n) (μ : ℂ) (1.1 / ν n) ((S n).gB B)
        ≤ |CS| * ‖Fpm true lam κ (ν n) (2 / ν n) 0‖ *
        testedNorm (S n).pk lam κ (ν n) (μ : ℂ) (1.1 / ν n) ((S n).gB B) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)) hTN0
    have h2 : testedNorm (S n).pk lam κ (ν n) (μ : ℂ) (1.1 / ν n) ((S n).gB B)
        ≤ |CT| * bNorm a B :=
      hT'.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hbN0)
    have h3 : |CS| * ‖Fpm true lam κ (ν n) (2 / ν n) 0‖ *
        testedNorm (S n).pk lam κ (ν n) (μ : ℂ) (1.1 / ν n) ((S n).gB B)
        ≤ |CS| * ‖Fpm true lam κ (ν n) (2 / ν n) 0‖ * (|CT| * bNorm a B) :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg (abs_nonneg _) (norm_nonneg _))
    exact hS'.trans (h1.trans h3)
  -- the normalised tested state: `‖F‖⁻¹ ‖duhamel‖ ≤ |CS||CT| ‖B‖_a`
  have hY : ‖Fpm true lam κ (ν n) (2 / ν n) 0‖⁻¹ * ‖duhamel (S n).pk (μ : ℂ) ((S n).gB B) (2 / ν n)‖
      ≤ |CS| * |CT| * bNorm a B := by
    have h4 := mul_le_mul_of_nonneg_left hDle (inv_nonneg.mpr (norm_nonneg
      (Fpm true lam κ (ν n) (2 / ν n) 0)))
    calc _ ≤ _ := h4
      _ = |CS| * |CT| * bNorm a B := by field_simp
  have hX : 0 ≤ ‖Nnu lam κ (ν n)‖ * ν n ^ (5 + 2 * μ) :=
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hνpos.le _)
  have hk0 : 0 ≤ ν n ^ k := pow_nonneg hνpos.le k
  have hY0 : 0 ≤ ‖Fpm true lam κ (ν n) (2 / ν n) 0‖⁻¹ *
      ‖duhamel (S n).pk (μ : ℂ) ((S n).gB B) (2 / ν n)‖ :=
    mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
  have hA : CL * (‖Nnu lam κ (ν n)‖ * ν n ^ (5 + 2 * μ)) * ν n ^ k ≤
      |CL| * (‖Nnu lam κ (ν n)‖ * ν n ^ (5 + 2 * μ)) * ν n ^ k :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) hX) hk0
  have hmain : (S n).momentC lam κ μ k B ≤
      |CL| * (‖Nnu lam κ (ν n)‖ * ν n ^ (5 + 2 * μ)) * ν n ^ k *
        (|CS| * |CT| * bNorm a B) := by
    refine hL'.trans ?_
    refine (mul_le_mul_of_nonneg_right hA hY0).trans ?_
    exact mul_le_mul_of_nonneg_left hY (mul_nonneg (mul_nonneg (abs_nonneg _) hX) hk0)
  show (S n).momentC lam κ μ k B ≤ _
  calc (S n).momentC lam κ μ k B
      ≤ _ := hmain
    _ = (|CL| * |CS| * |CT|) * (‖Nnu lam κ (ν n)‖ * ν n ^ (5 + 2 * μ)) * ν n ^ k * bNorm a B := by
      ring

end ConcreteYF

end UnforcedLeray.Short.PartIIIb
