import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5.GaussMulAbsorb

/-!
# `PartIII-b:C/asrc/ra/5/5` : generic Gaussian times polynomial growth (source 4963-4968, 4978)

`G = e^{-|y|²/(κa)} • P` with `P` of polynomial growth is `C^n` on `s > 0`, and its derivatives
of order `≤ n` are bounded by `C e^{-a q²}` uniformly for `s` in compacts of `(0,∞)` and `η` in
compacts.  Proof: Leibniz on the open set `Ioi 0 ×ˢ univ`, `gauss_iterated_bound` for the factor,
polynomial growth of `P`, and `gaussMul_absorb` for `(1+|x|²)^M e^{-|x|²/b} ≤ C e^{-q²/(2b)}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gaussMulHbd_proof (n : ℕ) : GaussMulHbd n := by
  intro E _ _ κ ν hκ hν P hP
  obtain ⟨hcd, hb⟩ := hP
  have hSo : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hSu : UniqueDiffOn ℝ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := hSo.uniqueDiffOn
  have hageA : ∀ s : ℝ, 0 < s → 0 < κ * ageA ν s := by
    intro s hs
    unfold ageA
    have h1 : 0 < 1 + ν * s := by linarith [mul_pos hν hs]
    exact mul_pos hκ h1
  have hden : ∀ p ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))), κ * ageA ν p.1 ≠ 0 := by
    intro p hp
    exact (hageA p.1 hp.1).ne'
  have hgdiff : ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(sq2 p.2) / (κ * ageA ν p.1)))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
    apply ContDiffOn.exp
    apply ContDiffOn.div
    · unfold sq2
      fun_prop
    · unfold ageA
      fun_prop
    · exact fun p hp => hden p hp
  have hGdiff : ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(sq2 p.2) / (κ * ageA ν p.1)) • P p)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := hgdiff.smul hcd
  refine ⟨hGdiff, ?_⟩
  intro K hK hKc L hL
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨0, 1, one_pos, ?_⟩
    intro m _ s hs
    simp [hKe] at hs
  · obtain ⟨u0, hu0K, hmin⟩ := hKc.exists_isMinOn hKne continuousOn_id
    obtain ⟨u1, hu1K, hmax⟩ := hKc.exists_isMaxOn hKne continuousOn_id
    have hmin' : ∀ x ∈ K, u0 ≤ x := fun x hx => isMinOn_iff.1 hmin x hx
    have hmax' : ∀ x ∈ K, x ≤ u1 := fun x hx => isMaxOn_iff.1 hmax x hx
    have hu0 : 0 < u0 := hK hu0K
    have hu1 : 0 < u1 := hK hu1K
    have hu01 : u0 ≤ u1 := hmin' u1 hu1K
    obtain ⟨C0, hC0, hGb⟩ := gauss_iterated_bound κ ν u0 u1 hκ hν hu0 hu01 n
    obtain ⟨C1, N, hC1, hPb⟩ := hb u0 u1 hu0 hu01
    obtain ⟨R, hR⟩ := hL.exists_bound_of_continuousOn (continuousOn_id)
    have hR2 : ∀ η ∈ L, η ^ 2 ≤ R ^ 2 := by
      intro η hη
      have h1 : ‖η‖ ≤ R := hR η hη
      have h0 : 0 ≤ ‖η‖ := norm_nonneg η
      have h2 : ‖η‖ ^ 2 = η ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
      nlinarith
    have hb0 : 0 < κ * ageA ν u1 := hageA u1 hu1
    obtain ⟨Cab, hCab, hAbs⟩ := gaussMul_absorb (n + N) R (κ * ageA ν u1) hb0
    refine ⟨((n : ℝ) + 1) * (2 ^ n * C0 * C1) * Cab, 1 / (2 * (κ * ageA ν u1)),
      one_div_pos.2 (by linarith), ?_⟩
    intro m hm s hs q η hη
    have hsI : s ∈ Icc u0 u1 := ⟨hmin' s hs, hmax' s hs⟩
    have hs0 : 0 < s := hK hs
    have hz : (s, (q, η)) ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := ⟨hs0, mem_univ _⟩
    have hX0 : 0 ≤ 1 + sq2 (q, η) := by
      have : 0 ≤ sq2 (q, η) := by unfold sq2; positivity
      linarith
    have hEqR : ∀ i : ℕ, iteratedFDerivWithin ℝ i
        (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(sq2 p.2) / (κ * ageA ν p.1)))
        (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (s, (q, η))
        = iteratedFDeriv ℝ i
        (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(sq2 p.2) / (κ * ageA ν p.1))) (s, (q, η)) :=
      fun i => iteratedFDerivWithin_of_isOpen i hSo hz
    have hEqE : ∀ i : ℕ, iteratedFDerivWithin ℝ i P
        (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (s, (q, η))
        = iteratedFDeriv ℝ i P (s, (q, η)) :=
      fun i => iteratedFDerivWithin_of_isOpen i hSo hz
    have hEqG : ∀ i : ℕ, iteratedFDerivWithin ℝ i
        (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(sq2 p.2) / (κ * ageA ν p.1)) • P p)
        (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (s, (q, η))
        = iteratedFDeriv ℝ i
        (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(sq2 p.2) / (κ * ageA ν p.1)) • P p) (s, (q, η)) :=
      fun i => iteratedFDerivWithin_of_isOpen i hSo hz
    have hleib := norm_iteratedFDerivWithin_smul_le
      (f := fun p : ℝ × (ℝ × ℝ) => Real.exp (-(sq2 p.2) / (κ * ageA ν p.1))) (g := P)
      hgdiff hcd hSu hz (n := m) (by exact_mod_cast hm)
    simp only [hEqR, hEqE] at hleib
    have hT : 0 ≤ (2 ^ n : ℝ) * C0 * C1 * ((1 + sq2 (q, η)) ^ (n + N)
        * Real.exp (-(sq2 (q, η)) / (κ * ageA ν u1))) := by
      apply mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hC0) hC1)
      exact mul_nonneg (pow_nonneg hX0 _) (Real.exp_nonneg _)
    have hterm : ∀ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i
            (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(sq2 p.2) / (κ * ageA ν p.1))) (s, (q, η))‖
          * ‖iteratedFDeriv ℝ (m - i) P (s, (q, η))‖
        ≤ (2 ^ n : ℝ) * C0 * C1 * ((1 + sq2 (q, η)) ^ (n + N)
          * Real.exp (-(sq2 (q, η)) / (κ * ageA ν u1))) := by
      intro i hi
      have hi' : i ≤ m := by
        have := Finset.mem_range.1 hi
        omega
      have h1 : (m.choose i : ℝ) ≤ 2 ^ n := by
        exact_mod_cast ((Nat.choose_le_two_pow m i).trans (Nat.pow_le_pow_right (by norm_num) hm))
      have h2 := hGb i (by omega) s hsI (q, η)
      have h3 := hPb (m - i) (by omega) s hsI (q, η)
      have hA0 : 0 ≤ (m.choose i : ℝ) := Nat.cast_nonneg _
      have hG0 : 0 ≤ C0 * (1 + sq2 (q, η)) ^ n * Real.exp (-(sq2 (q, η)) / (κ * ageA ν u1)) :=
        mul_nonneg (mul_nonneg hC0 (pow_nonneg hX0 _)) (Real.exp_nonneg _)
      have hP0 : 0 ≤ C1 * (1 + sq2 (q, η)) ^ N := mul_nonneg hC1 (pow_nonneg hX0 _)
      calc (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i
            (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(sq2 p.2) / (κ * ageA ν p.1))) (s, (q, η))‖
            * ‖iteratedFDeriv ℝ (m - i) P (s, (q, η))‖
          ≤ 2 ^ n * (C0 * (1 + sq2 (q, η)) ^ n * Real.exp (-(sq2 (q, η)) / (κ * ageA ν u1)))
            * (C1 * (1 + sq2 (q, η)) ^ N) := by
            apply mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3
              (norm_nonneg _)
            positivity
        _ = (2 ^ n : ℝ) * C0 * C1 * ((1 + sq2 (q, η)) ^ (n + N)
            * Real.exp (-(sq2 (q, η)) / (κ * ageA ν u1))) := by
          ring
    have hmain : ‖iteratedFDeriv ℝ m
        (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(sq2 p.2) / (κ * ageA ν p.1)) • P p) (s, (q, η))‖
        ≤ ∑ i ∈ Finset.range (m + 1), (2 ^ n : ℝ) * C0 * C1 * ((1 + sq2 (q, η)) ^ (n + N)
          * Real.exp (-(sq2 (q, η)) / (κ * ageA ν u1))) := by
      rw [← hEqG m]
      exact le_trans hleib (Finset.sum_le_sum hterm)
    have hA := hAbs q η (hR2 η hη)
    have hsum : ∑ i ∈ Finset.range (m + 1), (2 ^ n : ℝ) * C0 * C1 * ((1 + sq2 (q, η)) ^ (n + N)
        * Real.exp (-(sq2 (q, η)) / (κ * ageA ν u1)))
        = ((m : ℝ) + 1) * ((2 ^ n : ℝ) * C0 * C1 * ((1 + sq2 (q, η)) ^ (n + N)
          * Real.exp (-(sq2 (q, η)) / (κ * ageA ν u1)))) := by
      simp [Finset.sum_const, Finset.card_range]
    have hmn : ((m : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hm
      linarith
    have hstep1 : ((m : ℝ) + 1) * ((2 ^ n : ℝ) * C0 * C1 * ((1 + sq2 (q, η)) ^ (n + N)
          * Real.exp (-(sq2 (q, η)) / (κ * ageA ν u1))))
        ≤ ((n : ℝ) + 1) * ((2 ^ n : ℝ) * C0 * C1 * ((1 + sq2 (q, η)) ^ (n + N)
          * Real.exp (-(sq2 (q, η)) / (κ * ageA ν u1)))) :=
      mul_le_mul_of_nonneg_right hmn hT
    have hnn : 0 ≤ ((n : ℝ) + 1) * (2 ^ n * C0 * C1) :=
      mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (by positivity) hC0) hC1)
    have hstep2 : ((n : ℝ) + 1) * ((2 ^ n : ℝ) * C0 * C1 * ((1 + sq2 (q, η)) ^ (n + N)
          * Real.exp (-(sq2 (q, η)) / (κ * ageA ν u1))))
        ≤ ((n : ℝ) + 1) * (2 ^ n * C0 * C1) * (Cab * Real.exp (-(1 / (2 * (κ * ageA ν u1))) * q ^ 2)) := by
      have h := mul_le_mul_of_nonneg_left hA hnn
      calc ((n : ℝ) + 1) * ((2 ^ n : ℝ) * C0 * C1 * ((1 + sq2 (q, η)) ^ (n + N)
            * Real.exp (-(sq2 (q, η)) / (κ * ageA ν u1))))
          = ((n : ℝ) + 1) * (2 ^ n * C0 * C1) * ((1 + sq2 (q, η)) ^ (n + N)
            * Real.exp (-(sq2 (q, η)) / (κ * ageA ν u1))) := by ring
        _ ≤ ((n : ℝ) + 1) * (2 ^ n * C0 * C1) * (Cab * Real.exp (-(1 / (2 * (κ * ageA ν u1))) * q ^ 2)) := h
    have hfin : ((n : ℝ) + 1) * (2 ^ n * C0 * C1) * (Cab * Real.exp (-(1 / (2 * (κ * ageA ν u1))) * q ^ 2))
        = ((n : ℝ) + 1) * (2 ^ n * C0 * C1) * Cab * Real.exp (-(1 / (2 * (κ * ageA ν u1))) * q ^ 2) := by
      ring
    refine le_trans hmain ?_
    rw [hsum]
    exact le_trans hstep1 (le_trans hstep2 (le_of_eq hfin))

end UnforcedLeray.Short.PartIIIb.Concrete
