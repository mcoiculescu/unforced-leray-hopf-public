import UnforcedLeray.Short.PartIIa.Sub.N02_2

/-!


Source of record: `the November 2 reference manuscript`, lines 1730-1732
(integration by parts in `η` and `s` with compact support). Target: `IntegralDerivZero`
(`Sub/N02_2.lean`). Proof: `h` vanishes on the open half-lines `Iio a` and `Ioi b`, so `deriv h`
does too; continuity of `deriv h` and `h` extends this to the closures `Iic a` and `Ici b`.
If `b < a` the support set is empty and both integrals vanish. If `a ≤ b`, the integral of
`deriv h` over `ℝ` equals `∫ t in a..b, deriv h t = h b - h a = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

theorem integralDerivZero : UnforcedLeray.Short.PartIIa.IntegralDerivZero := by
  intro h hh a b hsupp
  have hd : Differentiable ℝ h := hh.differentiable (by simp)
  have hcont : Continuous h := hh.continuous
  have hdc : Continuous (deriv h) := hh.continuous_deriv (by simp)
  -- `h` vanishes outside `[a, b]`, on the two open half-lines.
  have hL : ∀ t, t < a → h t = 0 := fun t ht => by
    by_contra hne
    have hmem := hsupp t hne
    exact absurd hmem.1 (not_le.2 ht)
  have hR : ∀ t, b < t → h t = 0 := fun t ht => by
    by_contra hne
    have hmem := hsupp t hne
    exact absurd hmem.2 (not_le.2 ht)
  -- `deriv h` vanishes on the same open half-lines.
  have hdL : ∀ t, t < a → deriv h t = 0 := fun t ht => by
    have hev : h =ᶠ[𝓝 t] fun _ => (0 : ℂ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact hL s hs
    rw [hev.deriv_eq]
    simp
  have hdR : ∀ t, b < t → deriv h t = 0 := fun t ht => by
    have hev : h =ᶠ[𝓝 t] fun _ => (0 : ℂ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact hR s hs
    rw [hev.deriv_eq]
    simp
  -- `deriv h` vanishes at `a` by continuity.
  have hda : deriv h a = 0 := by
    have hL' : EqOn (deriv h) (fun _ => (0 : ℂ)) (Iio a) := fun t ht => hdL t ht
    have hEq := hL'.closure hdc continuous_const
    rw [closure_Iio] at hEq
    have ha : a ∈ Iic a := Set.mem_Iic.2 le_rfl
    exact hEq ha
  -- `deriv h` vanishes outside `[a, b]`.
  have hcompl : ∀ t, t ∉ Icc a b → deriv h t = 0 := by
    intro t ht
    by_cases h1 : t < a
    · exact hdL t h1
    · have h2 : b < t := by
        by_contra h2
        exact ht ⟨not_lt.1 h1, not_lt.1 h2⟩
      exact hdR t h2
  -- The integral over `ℝ` vanishes.
  have hfirst : ∫ t, deriv h t = 0 := by
    rcases le_or_gt a b with hab | hab
    · -- Case `a ≤ b`: the integral is `h b - h a`, and `h a = h b = 0`.
      have hha : h a = 0 := by
        have hL' : EqOn h (fun _ => (0 : ℂ)) (Iio a) := fun t ht => hL t ht
        have hEq := hL'.closure hcont continuous_const
        rw [closure_Iio] at hEq
        have ha : a ∈ Iic a := Set.mem_Iic.2 le_rfl
        exact hEq ha
      have hhb : h b = 0 := by
        have hR' : EqOn h (fun _ => (0 : ℂ)) (Ioi b) := fun t ht => hR t ht
        have hEq := hR'.closure hcont continuous_const
        rw [closure_Ioi] at hEq
        have hb : b ∈ Ici b := Set.mem_Ici.2 le_rfl
        exact hEq hb
      have hkey : ∫ t in a..b, deriv h t = h b - h a :=
        intervalIntegral.integral_deriv_eq_sub (fun x _ => hd x) (hdc.intervalIntegrable _ _)
      have hint : ∫ t in a..b, deriv h t = ∫ t in Icc a b, deriv h t := by
        rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
      calc ∫ t, deriv h t = ∫ t in Icc a b, deriv h t :=
            (setIntegral_eq_integral_of_forall_compl_eq_zero hcompl).symm
        _ = ∫ t in a..b, deriv h t := hint.symm
        _ = h b - h a := hkey
        _ = 0 := by simp [hha, hhb]
    · -- Case `b < a`: the support set `Icc a b` is empty.
      have hempty : Icc a b = ∅ := Icc_eq_empty (not_le.2 hab)
      calc ∫ t, deriv h t = ∫ t in Icc a b, deriv h t :=
            (setIntegral_eq_integral_of_forall_compl_eq_zero hcompl).symm
        _ = 0 := by rw [hempty]; simp
  refine ⟨hfirst, fun r hr => ?_⟩
  -- For `r ≤ a`, `deriv h` vanishes outside `Ioi r`, so the integral reduces to the first claim.
  have hcompl2 : ∀ t, t ∉ Ioi r → deriv h t = 0 := by
    intro t ht
    have ht' : t ≤ r := by simpa using ht
    rcases lt_or_eq_of_le (ht'.trans hr) with h1 | h1
    · exact hdL t h1
    · rw [h1]
      exact hda
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero hcompl2).trans hfirst

end UnforcedLeray.Short.PartIIa
