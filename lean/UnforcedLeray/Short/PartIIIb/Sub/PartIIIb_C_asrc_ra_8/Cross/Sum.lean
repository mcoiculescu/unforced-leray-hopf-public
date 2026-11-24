import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Cross.Defs
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.CellLattice

/-!
# `PartIII-b:C/asrc/ra/8/2/org` : the double sum over distinct centers (spec item (b))

Source `the November 2 reference manuscript`
5029-5031 ("Gaussian summation"): from the separated pair bound
`|P_{jk}| ≤ K|B| e^{-c²/135} e^{-η²/34} w_j w_k` (`k ≠ j`) and the uniform lattice sum
`Σ_j w_j ≤ C₁` (`fAcLatticeWeight`, `c ≥ 1`, `1 ≤ a ≤ 2.1`), the double sum is bounded by
`K C₁² |B| e^{-c²/135} e^{-η²/34}` (`tsum_of_norm_bounded` for the inner and outer sums).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rcCrossPointwise_of (h : RcPairSeparated) : RcCrossPointwise := by
  obtain ⟨K, hK, hP⟩ := h
  obtain ⟨C1, hC1⟩ := fAcLatticeWeight
  refine ⟨K * C1 ^ 2, by positivity, ?_⟩
  intro ν s B x hν hν1 hs hsT
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have ha2 : ageA ν s ≤ 21 / 10 := by
    unfold ageA
    have : ν * s ≤ 11 / 10 := by rw [le_div_iff₀ hν] at hsT; linarith
    linarith
  have hc1 : 1 ≤ cOf ν := by
    unfold cOf
    rw [one_le_inv₀ (by positivity)]
    nlinarith
  set D := K * frob B * Real.exp (-(cOf ν ^ 2) / 135) * Real.exp (-(x.2 ^ 2) / 34) with hDdef
  have hF : 0 ≤ frob B := Real.sqrt_nonneg _
  have hD : 0 ≤ D := by positivity
  have hw0 : ∀ j, 0 ≤ rcW ν s j x := fun j => (Real.exp_pos _).le
  have hwS : Summable (fun j : ℤ => rcW ν s j x) := by
    have := gp_gauss_summable x.1 (1 / (8 * ageA ν s)) (cOf ν) (by positivity) (by linarith)
    refine this.congr (fun j => ?_)
    unfold rcW
    congr 1
    ring
  set W := ∑' j : ℤ, rcW ν s j x with hWdef
  have hW : W ≤ C1 := hC1 (cOf ν) x.1 (ageA ν s) hc1 ha1 ha2
  have hW0 : 0 ≤ W := tsum_nonneg hw0
  have hterm : ∀ j k : ℤ, ‖(if k = j then 0 else rcPair ν s B j k x)‖ ≤
      D * rcW ν s j x * rcW ν s k x := by
    intro j k
    split_ifs with hkj
    · rw [norm_zero]
      have := hw0 j
      have := hw0 k
      positivity
    · have := hP ν s B j k x hν hν1 hs hsT hkj
      calc _ ≤ _ := this
        _ = D * rcW ν s j x * rcW ν s k x := by rw [hDdef]; ring
  have hinner : ∀ j : ℤ, ‖∑' k : ℤ, (if k = j then 0 else rcPair ν s B j k x)‖ ≤
      D * rcW ν s j x * W := fun j =>
    tsum_of_norm_bounded (hwS.hasSum.mul_left (D * rcW ν s j x)) (hterm j)
  have houter : ‖rcCross ν s B x‖ ≤ D * W * W := by
    unfold rcCross
    refine tsum_of_norm_bounded ?_ hinner
    have := (hwS.hasSum.mul_left D).mul_right W
    exact this
  calc ‖rcCross ν s B x‖ ≤ D * W * W := houter
    _ ≤ D * C1 * C1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hW hD) hW hW0 (mul_nonneg hD (hW0.trans hW))
    _ = K * C1 ^ 2 * frob B * Real.exp (-(cOf ν ^ 2) / 135) * Real.exp (-(x.2 ^ 2) / 34) := by
        rw [hDdef]; ring

end UnforcedLeray.Short.PartIIIb.Concrete
