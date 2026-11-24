import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_2_2_4_1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.RadOne.SqrtIterBound

/-!
# Part II-b, task `PartII-b:G4/2/2/4/1/4`: `GaussSqrtComp`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route: fix `k`. Uniform Gaussian constants `C`, `κ` for `g^{(j)}`, `j ≤ k`, on `[1,∞)`
(helper `gsc_uniform`). Uniform derivative bounds `D^i` for `√` on `Ioi (1/2)`, `1 ≤ i ≤ k`, at
`t ≥ 1`, from `SqrtIterBound` (`D = 1 + ∑ |D_j|`). Then the Faà di Bruno bound
`norm_iteratedFDerivWithin_comp_le` on `Ioi (1/2)` gives `m! · C e^{-κ t} · D^m`, and `m ≤ k`
turns this into the constant `k! · D^k · C`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

theorem gsc_exp_mono {κ' κ : ℝ} (h : κ' ≤ κ) (r : ℝ) :
    Real.exp (-(κ * r ^ 2)) ≤ Real.exp (-(κ' * r ^ 2)) := by
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_right h (sq_nonneg r)
  linarith

theorem gsc_uniform (g : ℝ → ℂ)
    (hG : ∀ j : ℕ, ∃ (C κ : ℝ), 0 < κ ∧ ∀ r : ℝ, 1 ≤ r →
      ‖iteratedDeriv j g r‖ ≤ C * Real.exp (-(κ * r ^ 2))) (k : ℕ) :
    ∃ (C κ : ℝ), 0 < κ ∧ 0 ≤ C ∧ ∀ j : ℕ, j ≤ k → ∀ r : ℝ, 1 ≤ r →
      ‖iteratedDeriv j g r‖ ≤ C * Real.exp (-(κ * r ^ 2)) := by
  choose C κ hκ hC using hG
  induction k with
  | zero =>
    refine ⟨|C 0|, κ 0, hκ 0, abs_nonneg _, fun j hj r hr => ?_⟩
    obtain rfl : j = 0 := Nat.le_zero.mp hj
    exact (hC 0 r hr).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
  | succ n ih =>
    obtain ⟨C0, κ0, hκ0, hC0, h0⟩ := ih
    refine ⟨max C0 |C (n + 1)|, min κ0 (κ (n + 1)), lt_min hκ0 (hκ (n + 1)),
      le_max_of_le_left hC0, fun j hj r hr => ?_⟩
    by_cases hjn : j ≤ n
    · exact (h0 j hjn r hr).trans (mul_le_mul (le_max_left _ _)
        (gsc_exp_mono (min_le_left _ _) r) (Real.exp_pos _).le (le_max_of_le_left hC0))
    · obtain rfl : j = n + 1 := by omega
      refine (hC (n + 1) r hr).trans ?_
      calc C (n + 1) * Real.exp (-(κ (n + 1) * r ^ 2))
          ≤ |C (n + 1)| * Real.exp (-(κ (n + 1) * r ^ 2)) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
        _ ≤ max C0 |C (n + 1)| * Real.exp (-(min κ0 (κ (n + 1)) * r ^ 2)) :=
            mul_le_mul (le_max_right _ _) (gsc_exp_mono (min_le_right _ _) r)
              (Real.exp_pos _).le (le_max_of_le_right (abs_nonneg _))

theorem gaussSqrtComp : UnforcedLeray.Short.IIb.GaussSqrtComp := by
  intro g hg hG k
  obtain ⟨C, κ, hκ, hC0, hGb⟩ := gsc_uniform g hG k
  have hS : ∀ i : ℕ, ∃ D : ℝ, ∀ t : ℝ, 1 ≤ t → ‖iteratedDeriv (i + 1) Real.sqrt t‖ ≤ D :=
    sqrtIterBound
  choose Dsq hDsq using hS
  obtain ⟨D, hD1, hDi⟩ : ∃ D : ℝ, 1 ≤ D ∧ ∀ i : ℕ, 1 ≤ i → i ≤ k → ∀ t : ℝ, 1 ≤ t →
      ‖iteratedFDerivWithin ℝ i Real.sqrt (Ioi (1 / 2 : ℝ)) t‖ ≤ D ^ i := by
    have hS0 : 0 ≤ ∑ l ∈ Finset.range (k + 1), |Dsq l| :=
      Finset.sum_nonneg (fun l _ => abs_nonneg _)
    refine ⟨1 + ∑ l ∈ Finset.range (k + 1), |Dsq l|, by linarith, ?_⟩
    intro i hi1 hik t ht1
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hmem : t ∈ Ioi (1 / 2 : ℝ) := by
      show (1 / 2 : ℝ) < t
      linarith
    have hEq := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := Real.sqrt) (j + 1)
      (isOpen_Ioi : IsOpen (Ioi (1 / 2 : ℝ))) hmem
    rw [hEq, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hsum : |Dsq j| ≤ ∑ l ∈ Finset.range (k + 1), |Dsq l| :=
      Finset.single_le_sum (f := fun l => |Dsq l|) (fun l _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega))
    calc ‖iteratedDeriv (j + 1) Real.sqrt t‖ ≤ Dsq j := hDsq j t ht1
      _ ≤ |Dsq j| := le_abs_self _
      _ ≤ 1 + ∑ l ∈ Finset.range (k + 1), |Dsq l| := by linarith
      _ ≤ (1 + ∑ l ∈ Finset.range (k + 1), |Dsq l|) ^ (j + 1) :=
          le_self_pow₀ (by linarith) (Nat.succ_ne_zero j)
  refine ⟨(Nat.factorial k : ℝ) * D ^ k * C, κ, hκ, fun m hmk t ht1 => ?_⟩
  have ht0 : (0 : ℝ) < t := by linarith
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht1
  have hmemHalf : t ∈ Ioi (1 / 2 : ℝ) := by
    show (1 / 2 : ℝ) < t
    linarith
  have hC' : ∀ i : ℕ, i ≤ m →
      ‖iteratedFDerivWithin ℝ i g (Ioi 0) (Real.sqrt t)‖ ≤ C * Real.exp (-(κ * t)) := by
    intro i hi
    have hmem : Real.sqrt t ∈ Ioi (0 : ℝ) := by
      show (0 : ℝ) < Real.sqrt t
      linarith
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := g) i
      (isOpen_Ioi : IsOpen (Ioi (0 : ℝ))) hmem, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    refine (hGb i (le_trans hi hmk) (Real.sqrt t) hsqrt1).trans (le_of_eq ?_)
    rw [Real.sq_sqrt ht0.le]
  have hfC : ContDiffOn ℝ ∞ Real.sqrt (Ioi (1 / 2 : ℝ)) := by
    intro x hx
    have hx' : (1 / 2 : ℝ) < x := hx
    have hx0 : x ≠ 0 := (lt_trans (by norm_num) hx').ne'
    exact (Real.contDiffAt_sqrt hx0).contDiffWithinAt
  have hst : MapsTo Real.sqrt (Ioi (1 / 2 : ℝ)) (Ioi (0 : ℝ)) := by
    intro x hx
    have hx' : (1 / 2 : ℝ) < x := hx
    show (0 : ℝ) < Real.sqrt x
    exact Real.sqrt_pos.mpr (lt_trans (by norm_num) hx')
  have hF := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := g) (f := Real.sqrt)
    (n := m) (s := Ioi (1 / 2 : ℝ)) (t := Ioi (0 : ℝ)) (x := t) hg hfC
    (by exact_mod_cast le_top) isOpen_Ioi.uniqueDiffOn isOpen_Ioi.uniqueDiffOn hst hmemHalf
    hC' (fun i hi him => hDi i hi (le_trans him hmk) t ht1)
  have hL : ‖iteratedDeriv m (g ∘ Real.sqrt) t‖
      = ‖iteratedFDerivWithin ℝ m (g ∘ Real.sqrt) (Ioi (1 / 2 : ℝ)) t‖ := by
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := g ∘ Real.sqrt) m
      (isOpen_Ioi : IsOpen (Ioi (1 / 2 : ℝ))) hmemHalf, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hE : 0 ≤ Real.exp (-(κ * t)) := (Real.exp_pos _).le
  have hCE : 0 ≤ C * Real.exp (-(κ * t)) := mul_nonneg hC0 hE
  have h1 : (Nat.factorial m : ℝ) ≤ (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_le hmk
  have h2 : D ^ m ≤ D ^ k := pow_le_pow_right₀ hD1 hmk
  have s1 : (Nat.factorial m : ℝ) * (C * Real.exp (-(κ * t)))
      ≤ (Nat.factorial k : ℝ) * (C * Real.exp (-(κ * t))) :=
    mul_le_mul_of_nonneg_right h1 hCE
  have s2 := mul_le_mul s1 h2 (pow_nonneg (by linarith) _)
    (mul_nonneg (Nat.cast_nonneg _) hCE)
  show ‖iteratedDeriv m (g ∘ Real.sqrt) t‖ ≤ _
  rw [hL]
  calc _ ≤ (Nat.factorial m : ℝ) * (C * Real.exp (-(κ * t))) * D ^ m := hF
    _ ≤ (Nat.factorial k : ℝ) * (C * Real.exp (-(κ * t))) * D ^ k := s2
    _ = (Nat.factorial k : ℝ) * D ^ k * C * Real.exp (-(κ * t)) := by ring

end
