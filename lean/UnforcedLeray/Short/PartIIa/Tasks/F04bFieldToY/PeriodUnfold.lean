import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F04_2

/-!


Source of record: `the November 2 reference manuscript`, lines 1478-1480.
Pure real analysis: for a `P`-periodic `G` integrable on a period and a periodic partition of unity
`∑_k ∑_j η_j(τ - kP) = 1` with compactly supported `η_j`, we have
`∫_0^P G = ∑_j ∫_ℝ η_j G`.

Proof. Let `M = 1 + ∑_j |c_j|` and `N = ⌈M/P⌉₊`, so `M ≤ NP`. On `[-NP, (N+1)P]` the
integrals over `ℝ` reduce to interval integrals, which split into the adjacent periods
`[(k-N)P, (k-N+1)P]`, `k = 0, …, 2N`. Each piece is a translate of `∫_0^P`, and periodicity of `G`
gives `∑_k ∑_j η_j(x + (k-N)P) = 1` for `x ∈ [0,P]` (the finite range of the partition identity).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

theorem periodUnfold_proof : UnforcedLeray.Short.PartIIa.PeriodUnfold := by
  intro P hP n c η hpart G hG hGi
  unfold IsPeriodPartition at hpart
  obtain ⟨hreg, hsum⟩ := hpart
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = 1 + ∑ j, |c j| := ⟨_, rfl⟩
  -- support bound: η_j vanishes where |s| ≥ M
  have hzero : ∀ j (s : ℝ), M ≤ |s| → η j s = 0 := by
    intro j s hs
    by_contra hne
    have hmem : s ∈ tsupport (η j) := subset_tsupport _ hne
    have h1 := (hreg j).2.2 hmem
    have hcj : |c j| ≤ ∑ i, |c i| :=
      Finset.single_le_sum (f := fun i => |c i|) (fun i _ => abs_nonneg (c i))
        (Finset.mem_univ j)
    have hd : |s - c j| < 1 := abs_sub_lt_iff.mpr ⟨by linarith [h1.2], by linarith [h1.1]⟩
    have h2 : |s| ≤ |s - c j| + |c j| := by
      calc |s| = |(s - c j) + c j| := by ring_nf
        _ ≤ |s - c j| + |c j| := abs_add_le _ _
    linarith
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈M / P⌉₊ := ⟨_, rfl⟩
  have hMN : M ≤ (N : ℝ) * P := by
    have h := (div_le_iff₀ hP).mp (Nat.le_ceil (M / P))
    rw [← hNdef] at h
    exact h
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ → ℝ, ∀ k : ℕ, A k = ((k : ℝ) - (N : ℝ)) * P :=
    ⟨fun k => ((k : ℝ) - (N : ℝ)) * P, fun k => rfl⟩
  have hA_succ : ∀ k : ℕ, A (k + 1) = A k + P := by
    intro k; rw [hAdef, hAdef]; push_cast; ring
  have hA0 : A 0 = -((N : ℝ) * P) := by
    rw [hAdef]; push_cast; ring
  have hA2 : A (2 * N + 1) = (N : ℝ) * P + P := by
    rw [hAdef]; push_cast; ring
  have hAcast : ∀ k : ℕ, A k = (((k : ℤ) - N : ℤ) : ℝ) * P := by
    intro k; rw [hAdef]; push_cast; ring
  have hGA : ∀ (k : ℕ) (x : ℝ), G (x + A k) = G x := by
    intro k x
    rw [hAcast k]
    exact hG.int_mul ((k : ℤ) - N) x
  have hGint : ∀ a b : ℝ, IntervalIntegrable G volume a b := by
    intro a b
    have h0 : IntervalIntegrable G volume 0 (0 + P) := by
      rw [zero_add]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hP.le).mpr hGi
    exact hG.intervalIntegrable hP.ne' h0 a b
  have hηint : ∀ (j : Fin n) (a b : ℝ),
      IntervalIntegrable (fun t => (η j t : ℂ) * G t) volume a b := by
    intro j a b
    have hc : Continuous (fun t => (η j t : ℂ)) :=
      Complex.continuous_ofReal.comp (hreg j).1.continuous
    exact (hGint a b).continuousOn_mul hc.continuousOn
  have hΦint : ∀ a b : ℝ, IntervalIntegrable (fun t => ∑ j, (η j t : ℂ) * G t) volume a b := by
    intro a b
    have h := IntervalIntegrable.sum (Finset.univ) (fun j (_ : j ∈ Finset.univ) => hηint j a b)
    have e : (fun t => ∑ j, (η j t : ℂ) * G t)
        = ∑ j, (fun t => (η j t : ℂ) * G t) := by
      funext t
      simp [Finset.sum_apply]
    rw [e]
    exact h
  -- Step 1: integrals over ℝ reduce to the interval [A 0, A (2N+1)]
  have hstep1 : ∀ j : Fin n,
      ∫ t, (η j t : ℂ) * G t = ∫ t in (A 0)..(A (2 * N + 1)), (η j t : ℂ) * G t := by
    intro j
    have hle : A 0 ≤ A (2 * N + 1) := by rw [hA0, hA2]; nlinarith [hMN, hP]
    rw [intervalIntegral.integral_of_le hle]
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro x hx
    have hbnd : M ≤ |x| := by
      rw [Set.mem_Ioc, not_and_or, not_lt] at hx
      rcases hx with h | h
      · exact le_abs.mpr (Or.inr (by rw [hA0] at h; linarith))
      · exact le_abs.mpr (Or.inl (by rw [hA2] at h; linarith))
    simp [hzero j x hbnd]
  -- Step 2: sum over j
  have hstep2 : ∑ j, ∫ t in (A 0)..(A (2 * N + 1)), (η j t : ℂ) * G t
      = ∫ t in (A 0)..(A (2 * N + 1)), ∑ j, (η j t : ℂ) * G t :=
    (intervalIntegral.integral_finsetSum (fun j _ => hηint j _ _)).symm
  -- Step 3: adjacent periods
  have hadj : ∫ t in (A 0)..(A (2 * N + 1)), ∑ j, (η j t : ℂ) * G t
      = ∑ k ∈ Finset.range (2 * N + 1), ∫ t in (A k)..(A (k + 1)), ∑ j, (η j t : ℂ) * G t :=
    (intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hΦint _ _)).symm
  -- Step 4: translate each period to [0, P]
  have hshift : ∀ k : ℕ, ∫ t in (A k)..(A (k + 1)), ∑ j, (η j t : ℂ) * G t
      = ∫ x in (0 : ℝ)..P, (∑ j, (η j (x + A k) : ℂ)) * G x := by
    intro k
    have h := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := P)
      (fun t => ∑ j, (η j t : ℂ) * G t) (A k)
    rw [zero_add, show P + A k = A (k + 1) by rw [hA_succ]; ring] at h
    rw [← h]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [hGA k x, Finset.sum_mul]
  have hint_k : ∀ k : ℕ, IntervalIntegrable
      (fun x => (∑ j, (η j (x + A k) : ℂ)) * G x) volume 0 P := by
    intro k
    have hcont : Continuous (fun x : ℝ => ∑ j, (η j (x + A k) : ℂ)) :=
      continuous_finset_sum _ (fun j _ =>
        Complex.continuous_ofReal.comp ((hreg j).1.continuous.comp (continuous_add_right _)))
    exact (hGint 0 P).continuousOn_mul hcont.continuousOn
  -- Step 5: the partition identity on the finite range
  have hfin : ∀ x ∈ Icc (0 : ℝ) P,
      ∑ k ∈ Finset.range (2 * N + 1), (∑ j, (η j (x + A k) : ℂ)) * G x = G x := by
    intro x hx
    have hT : ∑' m : ℤ, ∑ j, η j (x + (m : ℝ) * P) = 1 := by
      have h0 : ∑' m : ℤ, ∑ j, η j (x - ((-m : ℤ) : ℝ) * P)
          = ∑' k : ℤ, ∑ j, η j (x - (k : ℝ) * P) :=
        (Equiv.neg ℤ).tsum_eq (fun k : ℤ => ∑ j, η j (x - (k : ℝ) * P))
      rw [hsum x] at h0
      simp only [Int.cast_neg, neg_mul, sub_neg_eq_add] at h0
      exact h0
    have hvan : ∀ m : ℤ, m ∉ (Finset.range (2 * N + 1)).image (fun k : ℕ => (k : ℤ) - N) →
        ∑ j, η j (x + (m : ℝ) * P) = 0 := by
      intro m hm
      have hcases : m ≤ -(N : ℤ) - 1 ∨ (N : ℤ) + 1 ≤ m := by
        by_contra hc
        push_neg at hc
        exact hm (Finset.mem_image.mpr ⟨(m + N).toNat, Finset.mem_range.mpr (by omega), by omega⟩)
      apply Finset.sum_eq_zero
      intro j _
      apply hzero j
      rcases hcases with h | h
      · have hm' : (m : ℝ) ≤ -(N : ℝ) - 1 := by exact_mod_cast (by omega : m ≤ -(N : ℤ) - 1)
        have hmP : (m : ℝ) * P ≤ (-(N : ℝ) - 1) * P :=
          mul_le_mul_of_nonneg_right hm' hP.le
        apply le_abs.mpr
        right
        nlinarith [hMN, hP, hmP, hx.1, hx.2]
      · have hm' : (N : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h
        have hmP : ((N : ℝ) + 1) * P ≤ (m : ℝ) * P :=
          mul_le_mul_of_nonneg_right hm' hP.le
        apply le_abs.mpr
        left
        nlinarith [hMN, hP, hmP, hx.1, hx.2]
    have hreal : ∑ k ∈ Finset.range (2 * N + 1), ∑ j, η j (x + A k) = 1 := by
      have e1 : ∑ k ∈ Finset.range (2 * N + 1), ∑ j, η j (x + A k)
          = ∑ k ∈ Finset.range (2 * N + 1), ∑ j, η j (x + (((k : ℤ) - N : ℤ) : ℝ) * P) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hAcast k]
      have e2 : ∑ m ∈ (Finset.range (2 * N + 1)).image (fun k : ℕ => (k : ℤ) - N),
          ∑ j, η j (x + (m : ℝ) * P)
          = ∑ k ∈ Finset.range (2 * N + 1), ∑ j, η j (x + (((k : ℤ) - N : ℤ) : ℝ) * P) :=
        Finset.sum_image (fun a _ b _ h => by have h' : (a : ℤ) - N = (b : ℤ) - N := h; omega)
      have e3 : ∑' m : ℤ, ∑ j, η j (x + (m : ℝ) * P)
          = ∑ m ∈ (Finset.range (2 * N + 1)).image (fun k : ℕ => (k : ℤ) - N),
            ∑ j, η j (x + (m : ℝ) * P) :=
        tsum_eq_sum (fun m hm => hvan m hm)
      rw [e1, ← e2, ← e3, hT]
    have hc : (∑ k ∈ Finset.range (2 * N + 1), ∑ j, (η j (x + A k) : ℂ)) = 1 := by
      exact_mod_cast hreal
    rw [← Finset.sum_mul, hc, one_mul]
  -- Step 6: assemble
  symm
  calc ∑ j, ∫ t, (η j t : ℂ) * G t
      = ∑ j, ∫ t in (A 0)..(A (2 * N + 1)), (η j t : ℂ) * G t :=
        Finset.sum_congr rfl (fun j _ => hstep1 j)
    _ = ∫ t in (A 0)..(A (2 * N + 1)), ∑ j, (η j t : ℂ) * G t := hstep2
    _ = ∑ k ∈ Finset.range (2 * N + 1), ∫ t in (A k)..(A (k + 1)), ∑ j, (η j t : ℂ) * G t := hadj
    _ = ∑ k ∈ Finset.range (2 * N + 1), ∫ x in (0 : ℝ)..P, (∑ j, (η j (x + A k) : ℂ)) * G x :=
        Finset.sum_congr rfl (fun k _ => hshift k)
    _ = ∫ x in (0 : ℝ)..P, ∑ k ∈ Finset.range (2 * N + 1), (∑ j, (η j (x + A k) : ℂ)) * G x :=
        (intervalIntegral.integral_finsetSum (fun k _ => hint_k k)).symm
    _ = ∫ x in (0 : ℝ)..P, G x :=
        intervalIntegral.integral_congr (fun x hx => by
          rw [Set.uIcc_of_le hP.le] at hx
          exact hfin x hx)
    _ = ∫ t in Ioc (0 : ℝ) P, G t := intervalIntegral.integral_of_le hP.le

end UnforcedLeray.Short.PartIIa
