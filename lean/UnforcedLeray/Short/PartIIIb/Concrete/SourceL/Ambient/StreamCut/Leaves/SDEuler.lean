import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5_5

/-!
# Part III-b, task `PartIII-b:C/srcL/9/5/5/2`: Euler operator bound `SDEuler` (source 4917-4937)

With `φ(s) = 1/√s` one has `s ∂_s (h ∘ φ) = -(1/2) (r ∂_r h) ∘ φ`. Writing `T f = r ∂_r f`,
`(s∂_s)^j (h∘φ) = (-1/2)^j (T^j h)∘φ` (`sdS_comp`), and `T^j h = Σ_{k≤j} c_{j,k} r^k h^{(k)}` with
`|c_{j,k}| ≤ (j+1)!` (`eulerT_coeff`). Each term is `≤ (j+1)! M r^{-5}` by the hypothesis on `h^{(k)}`,
and `r^{-5} = s^{5/2}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The Euler operator `f ↦ r ∂_r f` on real functions of `r`. -/
def eulerT (f : ℝ → ℝ) : ℝ → ℝ := fun r => r * deriv f r

theorem eulerT_cast_sub_succ (n : ℕ) (hn : n + 1 ≤ 6) :
    ((6 - (n + 1) : ℕ) : WithTop ℕ∞) + 1 = ((6 - n : ℕ) : WithTop ℕ∞) := by
  rw [← Nat.cast_succ, Nat.succ_eq_add_one, show 6 - (n + 1) + 1 = 6 - n by omega]

theorem eulerT_iteratedDeriv_reg (h : ℝ → ℝ) (hh : ContDiffOn ℝ 6 h (Ioi 0)) :
    ∀ k : ℕ, k ≤ 6 → ContDiffOn ℝ ((6 - k : ℕ) : WithTop ℕ∞) (iteratedDeriv k h) (Ioi 0) := by
  intro k
  induction k with
  | zero =>
    intro _
    have e : ((6 - 0 : ℕ) : WithTop ℕ∞) = 6 := by norm_num
    rw [e, iteratedDeriv_zero]
    exact hh
  | succ k ih =>
    intro hk
    rw [iteratedDeriv_succ]
    exact (ih (by omega)).deriv_of_isOpen isOpen_Ioi (eulerT_cast_sub_succ k hk).le

theorem eulerT_iter_reg (h : ℝ → ℝ) (hh : ContDiffOn ℝ 6 h (Ioi 0)) :
    ∀ j : ℕ, j ≤ 6 → ContDiffOn ℝ ((6 - j : ℕ) : WithTop ℕ∞) (eulerT^[j] h) (Ioi 0) := by
  intro j
  induction j with
  | zero =>
    intro _
    have e : ((6 - 0 : ℕ) : WithTop ℕ∞) = 6 := by norm_num
    rw [e]
    exact hh
  | succ j ih =>
    intro hj
    have hc := ih (by omega)
    have hd := hc.deriv_of_isOpen isOpen_Ioi (eulerT_cast_sub_succ j hj).le
    have hm : ContDiffOn ℝ ((6 - (j + 1) : ℕ) : WithTop ℕ∞)
        (fun t : ℝ => t * deriv (eulerT^[j] h) t) (Ioi 0) := contDiffOn_id.mul hd
    rw [Function.iterate_succ_apply']
    exact hm

theorem eulerT_hpowk (r : ℝ) : ∀ k : ℕ, r * ((k : ℝ) * r ^ (k - 1)) = (k : ℝ) * r ^ k := by
  intro k
  cases k with
  | zero => simp
  | succ n =>
    rw [Nat.add_sub_cancel]
    push_cast
    ring

/-- Coefficient representation of `T^j h` with bounded universal coefficients. -/
theorem eulerT_coeff (h : ℝ → ℝ) (hh : ContDiffOn ℝ 6 h (Ioi 0)) :
    ∀ j : ℕ, j ≤ 6 → ∃ c : ℕ → ℝ, (∀ k, j < k → c k = 0) ∧
      (∀ k, k ≤ j → |c k| ≤ ((j + 1).factorial : ℝ)) ∧
      ∀ r : ℝ, 0 < r → eulerT^[j] h r =
        ∑ k ∈ Finset.range (j + 1), c k * r ^ k * iteratedDeriv k h r := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun k => if k = 0 then 1 else 0, fun k hk => ?_, fun k hk => ?_, fun r _ => ?_⟩
    · simp [show k ≠ 0 by omega]
    · have : k = 0 := by omega
      subst this
      norm_num [Nat.factorial]
    · simp [iteratedDeriv_zero]
  | succ j ih =>
    intro hj
    obtain ⟨c, hc0, hcb, hcr⟩ := ih (by omega)
    have hall : ∀ m, m ≤ j + 1 → |c m| ≤ ((j + 1).factorial : ℝ) := by
      intro m hm
      by_cases hmj : m ≤ j
      · exact hcb m hmj
      · rw [hc0 m (by omega), abs_zero]
        positivity
    refine ⟨fun k => (k : ℝ) * c k + (if k = 0 then 0 else c (k - 1)), ?_, ?_, ?_⟩
    · intro k hk
      have h1 : c k = 0 := hc0 k (by omega)
      have h2 : c (k - 1) = 0 := hc0 (k - 1) (by omega)
      simp [h1, h2]
    · intro k hk
      have hfac : ((j + 1 + 1).factorial : ℝ) = ((j : ℝ) + 2) * ((j + 1).factorial : ℝ) := by
        rw [Nat.factorial_succ (j + 1)]
        push_cast
        ring
      show |(k : ℝ) * c k + (if k = 0 then 0 else c (k - 1))| ≤ ((j + 1 + 1).factorial : ℝ)
      rw [hfac]
      by_cases hk0 : k = 0
      · subst hk0
        rw [if_pos rfl]
        simp only [Nat.cast_zero, zero_mul, add_zero, abs_zero]
        positivity
      · rw [if_neg hk0]
        have h1 : |(k : ℝ) * c k| ≤ ((j : ℝ) + 1) * ((j + 1).factorial : ℝ) := by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
          have hkle : (k : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast hk
          exact mul_le_mul hkle (hall k hk) (abs_nonneg _) (by positivity)
        have h2 : |c (k - 1)| ≤ ((j + 1).factorial : ℝ) := hall (k - 1) (by omega)
        calc |(k : ℝ) * c k + c (k - 1)| ≤ |(k : ℝ) * c k| + |c (k - 1)| := abs_add_le _ _
          _ ≤ ((j : ℝ) + 1) * ((j + 1).factorial : ℝ) + ((j + 1).factorial : ℝ) :=
              add_le_add h1 h2
          _ = ((j : ℝ) + 2) * ((j + 1).factorial : ℝ) := by ring
    · intro r hr
      have hFd : ∀ k, k ≤ j → HasDerivAt (iteratedDeriv k h) (iteratedDeriv (k + 1) h r) r := by
        intro k hk
        have hreg := eulerT_iteratedDeriv_reg h hh k (by omega)
        have h1 : ContDiffOn ℝ 1 (iteratedDeriv k h) (Ioi 0) :=
          hreg.of_le (by exact_mod_cast (show 1 ≤ 6 - k by omega))
        have hdiff := (h1.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hr)
        have e : deriv (iteratedDeriv k h) r = iteratedDeriv (k + 1) h r := by
          rw [iteratedDeriv_succ]
        rw [← e]
        exact hdiff.hasDerivAt
      set S : ℝ → ℝ := fun t => ∑ k ∈ Finset.range (j + 1), c k * t ^ k * iteratedDeriv k h t
        with hS
      have hSd : HasDerivAt S (∑ k ∈ Finset.range (j + 1),
          (c k * ((k : ℝ) * r ^ (k - 1)) * iteratedDeriv k h r +
            c k * r ^ k * iteratedDeriv (k + 1) h r)) r := by
        apply HasDerivAt.fun_sum
        intro k hk
        have hk' : k ≤ j := by
          have := Finset.mem_range.mp hk
          omega
        exact ((hasDerivAt_pow k r).const_mul (c k)).mul (hFd k hk')
      have hiter : eulerT^[j + 1] h r = r * deriv (eulerT^[j] h) r := by
        rw [Function.iterate_succ_apply']
        rfl
      have hev : eulerT^[j] h =ᶠ[nhds r] S :=
        Filter.eventually_of_mem (Ioi_mem_nhds hr) fun t ht => hcr t ht
      rw [hiter, hev.deriv_eq, hSd.deriv]
      dsimp only
      rw [Finset.mul_sum]
      have hterm : ∀ k ∈ Finset.range (j + 1),
          r * (c k * ((k : ℝ) * r ^ (k - 1)) * iteratedDeriv k h r +
            c k * r ^ k * iteratedDeriv (k + 1) h r) =
          (k : ℝ) * c k * r ^ k * iteratedDeriv k h r +
            c k * r ^ (k + 1) * iteratedDeriv (k + 1) h r := by
        intro k _
        have hp := eulerT_hpowk r k
        linear_combination (c k * iteratedDeriv k h r) * hp
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      have e2 : ∑ k ∈ Finset.range (j + 1 + 1), (k : ℝ) * c k * r ^ k * iteratedDeriv k h r =
          ∑ k ∈ Finset.range (j + 1), (k : ℝ) * c k * r ^ k * iteratedDeriv k h r := by
        rw [Finset.sum_range_succ, hc0 (j + 1) (by omega)]
        simp
      have e3 : ∑ k ∈ Finset.range (j + 1 + 1),
          (if k = 0 then 0 else c (k - 1)) * r ^ k * iteratedDeriv k h r =
          ∑ k ∈ Finset.range (j + 1), c k * r ^ (k + 1) * iteratedDeriv (k + 1) h r := by
        rw [Finset.sum_range_succ']
        simp
      have e4 : ∑ k ∈ Finset.range (j + 1 + 1),
          ((k : ℝ) * c k + (if k = 0 then 0 else c (k - 1))) * r ^ k * iteratedDeriv k h r =
          ∑ k ∈ Finset.range (j + 1 + 1), (k : ℝ) * c k * r ^ k * iteratedDeriv k h r +
          ∑ k ∈ Finset.range (j + 1 + 1),
            (if k = 0 then 0 else c (k - 1)) * r ^ k * iteratedDeriv k h r := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [e4, e2, e3]

/-- `(s∂_s)^j` of `h ∘ φ`, `φ(s) = 1/√s`, is `(-1/2)^j (T^j h) ∘ φ`. -/
theorem eulerT_sdS_comp (h : ℝ → ℝ) (hh : ContDiffOn ℝ 6 h (Ioi 0)) :
    ∀ j : ℕ, j ≤ 6 → ∀ s : ℝ, 0 < s →
      sDerivIterS j (fun t : ℝ => if 0 < t then h ((1 : ℝ)⁻¹ / Real.sqrt t) else 0) s =
        (-1 / 2 : ℝ) ^ j * eulerT^[j] h ((1 : ℝ)⁻¹ / Real.sqrt s) := by
  intro j
  induction j with
  | zero =>
    intro _ s hs
    simp [sDerivIterS, hs]
  | succ j ih =>
    intro hj s hs
    have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
    have hφd : HasDerivAt (fun t : ℝ => (1 : ℝ)⁻¹ / Real.sqrt t)
        (-(1 / (2 * Real.sqrt s)) / (Real.sqrt s) ^ 2) s := by
      have h2 : (fun t : ℝ => (1 : ℝ)⁻¹ / Real.sqrt t) = fun t => (Real.sqrt t)⁻¹ := by
        funext t
        simp
      rw [h2]
      exact (Real.hasDerivAt_sqrt hs.ne').inv hsq.ne'
    have hFd : DifferentiableAt ℝ (eulerT^[j] h) ((1 : ℝ)⁻¹ / Real.sqrt s) := by
      have hreg := eulerT_iter_reg h hh j (by omega)
      have hpos : (0 : ℝ) < (1 : ℝ)⁻¹ / Real.sqrt s := by positivity
      have h1 : ContDiffOn ℝ 1 (eulerT^[j] h) (Ioi 0) :=
        hreg.of_le (by exact_mod_cast (show 1 ≤ 6 - j by omega))
      exact (h1.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hpos)
    have hcomp : HasDerivAt
        (fun t : ℝ => (-1 / 2 : ℝ) ^ j * eulerT^[j] h ((1 : ℝ)⁻¹ / Real.sqrt t))
        ((-1 / 2 : ℝ) ^ j * (deriv (eulerT^[j] h) ((1 : ℝ)⁻¹ / Real.sqrt s) *
          (-(1 / (2 * Real.sqrt s)) / (Real.sqrt s) ^ 2))) s :=
      (hFd.hasDerivAt.comp s hφd).const_mul _
    have hev : sDerivIterS j (fun t : ℝ => if 0 < t then h ((1 : ℝ)⁻¹ / Real.sqrt t) else 0)
        =ᶠ[nhds s] (fun t : ℝ => (-1 / 2 : ℝ) ^ j * eulerT^[j] h ((1 : ℝ)⁻¹ / Real.sqrt t)) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hs) fun t ht => ih (by omega) t ht
    have hsd : sDerivIterS (j + 1) (fun t : ℝ => if 0 < t then h ((1 : ℝ)⁻¹ / Real.sqrt t) else 0) s
        = s * deriv (sDerivIterS j (fun t : ℝ => if 0 < t then h ((1 : ℝ)⁻¹ / Real.sqrt t) else 0)) s :=
      rfl
    rw [hsd, hev.deriv_eq, hcomp.deriv]
    have hs0 : s ≠ 0 := hs.ne'
    have hsq0 : Real.sqrt s ≠ 0 := hsq.ne'
    have hkey : s * (-(1 / (2 * Real.sqrt s)) / (Real.sqrt s) ^ 2) =
        (-1 / 2 : ℝ) * ((1 : ℝ)⁻¹ / Real.sqrt s) := by
      rw [Real.sq_sqrt hs.le]
      field_simp <;> ring
    rw [Function.iterate_succ_apply']
    show s * ((-1 / 2 : ℝ) ^ j * (deriv (eulerT^[j] h) ((1 : ℝ)⁻¹ / Real.sqrt s) *
          (-(1 / (2 * Real.sqrt s)) / (Real.sqrt s) ^ 2))) =
        (-1 / 2 : ℝ) ^ (j + 1) * ((1 : ℝ)⁻¹ / Real.sqrt s * deriv (eulerT^[j] h) ((1 : ℝ)⁻¹ / Real.sqrt s))
    rw [pow_succ]
    linear_combination ((-1 / 2 : ℝ) ^ j * deriv (eulerT^[j] h) ((1 : ℝ)⁻¹ / Real.sqrt s)) * hkey

/-- Euler operator (source 4917-4937), with the absolute constant `C = 35280 = 7·7!`. -/
theorem sdEuler : SDEuler := by
  unfold SDEuler
  refine ⟨35280, fun h M hM hh hbd s hs j hj => ?_⟩
  obtain ⟨c, -, hcb, hcr⟩ := eulerT_coeff h hh j hj
  have hr : 0 < (1 : ℝ)⁻¹ / Real.sqrt s := by
    have := Real.sqrt_pos.2 hs
    positivity
  have hpk : ∀ k : ℕ, ((1 : ℝ)⁻¹ / Real.sqrt s) ^ k * ((1 : ℝ)⁻¹ / Real.sqrt s) ^ (-(5 : ℝ) - k) =
      ((1 : ℝ)⁻¹ / Real.sqrt s) ^ (-(5 : ℝ)) := by
    intro k
    rw [← Real.rpow_natCast, ← Real.rpow_add hr]
    congr 1
    ring
  have hFb : |eulerT^[j] h ((1 : ℝ)⁻¹ / Real.sqrt s)| ≤
      ((j : ℝ) + 1) * ((j + 1).factorial : ℝ) * M *
        ((1 : ℝ)⁻¹ / Real.sqrt s) ^ (-(5 : ℝ)) := by
    rw [hcr _ hr]
    calc |∑ k ∈ Finset.range (j + 1), c k * ((1 : ℝ)⁻¹ / Real.sqrt s) ^ k *
          iteratedDeriv k h ((1 : ℝ)⁻¹ / Real.sqrt s)|
        ≤ ∑ k ∈ Finset.range (j + 1), |c k * ((1 : ℝ)⁻¹ / Real.sqrt s) ^ k *
            iteratedDeriv k h ((1 : ℝ)⁻¹ / Real.sqrt s)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (j + 1), ((j + 1).factorial : ℝ) * M *
            ((1 : ℝ)⁻¹ / Real.sqrt s) ^ (-(5 : ℝ)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' : k ≤ j := by
            have := Finset.mem_range.mp hk
            omega
          have h1 : |c k| ≤ ((j + 1).factorial : ℝ) := hcb k hk'
          have h2 : |iteratedDeriv k h ((1 : ℝ)⁻¹ / Real.sqrt s)| ≤
              M * ((1 : ℝ)⁻¹ / Real.sqrt s) ^ (-(5 : ℝ) - k) := hbd k (by omega) _ hr
          calc |c k * ((1 : ℝ)⁻¹ / Real.sqrt s) ^ k * iteratedDeriv k h ((1 : ℝ)⁻¹ / Real.sqrt s)|
              = |c k| * ((1 : ℝ)⁻¹ / Real.sqrt s) ^ k *
                  |iteratedDeriv k h ((1 : ℝ)⁻¹ / Real.sqrt s)| := by
                rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hr.le k)]
            _ ≤ ((j + 1).factorial : ℝ) * ((1 : ℝ)⁻¹ / Real.sqrt s) ^ k *
                  (M * ((1 : ℝ)⁻¹ / Real.sqrt s) ^ (-(5 : ℝ) - k)) :=
                mul_le_mul (mul_le_mul_of_nonneg_right h1 (pow_nonneg hr.le k)) h2
                  (abs_nonneg _) (by positivity)
            _ = ((j + 1).factorial : ℝ) * M * ((1 : ℝ)⁻¹ / Real.sqrt s) ^ (-(5 : ℝ)) := by
                rw [← hpk k]
                ring
      _ = ((j : ℝ) + 1) * ((j + 1).factorial : ℝ) * M *
            ((1 : ℝ)⁻¹ / Real.sqrt s) ^ (-(5 : ℝ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hr5 : ((1 : ℝ)⁻¹ / Real.sqrt s) ^ (-(5 : ℝ)) = s ^ (5 / 2 : ℝ) := by
    rw [inv_one, one_div, Real.inv_rpow (Real.sqrt_nonneg s), Real.sqrt_eq_rpow, ← Real.rpow_mul hs.le]
    rw [← Real.rpow_neg hs.le]
    congr 1
    norm_num
  have hpow1 : |(-1 / 2 : ℝ) ^ j| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (by norm_num [abs_div])
  have hcomb : ((j : ℝ) + 1) * ((j + 1).factorial : ℝ) ≤ 35280 := by
    interval_cases j <;> norm_num [Nat.factorial]
  have hS0 : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.le _
  rw [eulerT_sdS_comp h hh j hj s hs, abs_mul]
  calc |(-1 / 2 : ℝ) ^ j| * |eulerT^[j] h ((1 : ℝ)⁻¹ / Real.sqrt s)|
      ≤ 1 * |eulerT^[j] h ((1 : ℝ)⁻¹ / Real.sqrt s)| :=
        mul_le_mul_of_nonneg_right hpow1 (abs_nonneg _)
    _ = |eulerT^[j] h ((1 : ℝ)⁻¹ / Real.sqrt s)| := one_mul _
    _ ≤ ((j : ℝ) + 1) * ((j + 1).factorial : ℝ) * M *
          ((1 : ℝ)⁻¹ / Real.sqrt s) ^ (-(5 : ℝ)) := hFb
    _ = ((j : ℝ) + 1) * ((j + 1).factorial : ℝ) * M * s ^ (5 / 2 : ℝ) := by rw [hr5]
    _ ≤ 35280 * M * s ^ (5 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcomb hM) hS0

end UnforcedLeray.Short.PartIIIb.Concrete
