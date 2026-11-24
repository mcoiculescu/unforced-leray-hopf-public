import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Cross.PairCont
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss

/-!
# `PartIII-b:C/asrc/ra/8/2/org` : continuity of the distinct-center sum (spec item (d))

Source `the November 2 reference manuscript`
4963-4972, 5026-5031 (the sums converge by Gaussian decay).  On the strip `|q - q₀| < 1` the
lattice weight satisfies `w_j(x) ≤ e^{1/(8a)} e^{-(q₀ - jc)²/(16a)}` (since
`(q₀ - jc)² ≤ 2(q - jc)² + 2`), so the separated pair bound gives a summable majorant uniform on
the strip; `continuousOn_tsum` (inner sum over `k`, then outer sum over `j`) with the continuity
of the pair terms (`rcPairContinuous`) gives continuity of `rcCross`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rc_w_local (ν s : ℝ) (ha : 0 < ageA ν s) (j : ℤ) (x x0 : ℝ × ℝ)
    (hx : |x.1 - x0.1| < 1) :
    rcW ν s j x ≤ Real.exp (1 / (8 * ageA ν s)) *
      Real.exp (-(1 / (16 * ageA ν s)) * (x0.1 - j * cOf ν) ^ 2) := by
  unfold rcW
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  set a := ageA ν s with hadef
  set u := x.1 - j * cOf ν with hu
  set u0 := x0.1 - j * cOf ν with hu0
  have hd : (x.1 - x0.1) ^ 2 < 1 := by
    have h := abs_lt.mp hx
    nlinarith
  have key : u0 ^ 2 ≤ 2 * u ^ 2 + 2 * (x.1 - x0.1) ^ 2 := by
    have e : u0 = u - (x.1 - x0.1) := by rw [hu, hu0]; ring
    rw [e]
    nlinarith [sq_nonneg (u + (x.1 - x0.1))]
  have e2 : 1 / (8 * a) + -(1 / (16 * a)) * u0 ^ 2 - (-(u ^ 2) / (8 * a)) =
      (2 + 2 * u ^ 2 - u0 ^ 2) / (16 * a) := by
    field_simp
    ring
  have hnum : 0 ≤ (2 + 2 * u ^ 2 - u0 ^ 2) / (16 * a) := by
    apply div_nonneg _ (by positivity)
    linarith
  linarith

theorem rcCrossContinuous_of (h : RcPairSeparated) : RcCrossContinuous := by
  obtain ⟨K, hK, hP⟩ := h
  intro ν s B hν hν1 hs hsT
  have ha : 0 < ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hc : 0 < cOf ν := by unfold cOf; positivity
  set D0 := K * frob B * Real.exp (-(cOf ν ^ 2) / 135) with hD0def
  have hF : 0 ≤ frob B := Real.sqrt_nonneg _
  have hD0 : 0 ≤ D0 := by positivity
  rw [continuous_iff_continuousAt]
  intro x0
  set t : Set (ℝ × ℝ) := {x | |x.1 - x0.1| < 1} with htdef
  have ht : t ∈ 𝓝 x0 := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (continuous_abs.comp (continuous_fst.sub continuous_const))
        continuous_const
    · simp [htdef]
  set u : ℤ → ℝ := fun j => Real.exp (1 / (8 * ageA ν s)) *
    Real.exp (-(1 / (16 * ageA ν s)) * (x0.1 - j * cOf ν) ^ 2) with hudef
  have hu0 : ∀ j, 0 ≤ u j := fun j => by positivity
  have huS : Summable u :=
    (gp_gauss_summable x0.1 (1 / (16 * ageA ν s)) (cOf ν) (by positivity) hc).mul_left _
  set U := ∑' j, u j with hUdef
  have hwt : ∀ j, ∀ x ∈ t, rcW ν s j x ≤ u j := fun j x hx => rc_w_local ν s ha j x x0 hx
  have hterm : ∀ j k : ℤ, ∀ x ∈ t,
      ‖(if k = j then (0 : ℝ × ℝ) else rcPair ν s B j k x)‖ ≤ D0 * u j * u k := by
    intro j k x hx
    split_ifs with hkj
    · rw [norm_zero]
      have := hu0 j
      have := hu0 k
      positivity
    · have h1 := hP ν s B j k x hν hν1 hs hsT hkj
      have hE : Real.exp (-(x.2 ^ 2) / 34) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have := sq_nonneg x.2
        linarith [neg_div 34 (x.2 ^ 2)]
      have hwj := hwt j x hx
      have hwk := hwt k x hx
      have hw0j : 0 ≤ rcW ν s j x := (Real.exp_pos _).le
      have hw0k : 0 ≤ rcW ν s k x := (Real.exp_pos _).le
      have hE0 : 0 ≤ Real.exp (-(x.2 ^ 2) / 34) := (Real.exp_pos _).le
      calc _ ≤ _ := h1
        _ = D0 * Real.exp (-(x.2 ^ 2) / 34) * (rcW ν s j x * rcW ν s k x) := by
            rw [hD0def]
        _ ≤ D0 * 1 * (u j * u k) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hE hD0) (mul_le_mul hwj hwk hw0k (hu0 j))
              (by positivity) (by positivity)
        _ = D0 * u j * u k := by ring
  have hcont_ite : ∀ j k : ℤ,
      ContinuousOn (fun x => if k = j then (0 : ℝ × ℝ) else rcPair ν s B j k x) t := by
    intro j k
    by_cases hkj : k = j
    · simp only [hkj, if_true]
      exact continuousOn_const
    · simp only [hkj, if_false]
      exact (rcPairContinuous ν s B j k).continuousOn
  have hinner : ∀ j : ℤ,
      ContinuousOn (fun x => ∑' k : ℤ, if k = j then (0 : ℝ × ℝ) else rcPair ν s B j k x) t :=
    fun j => continuousOn_tsum (hcont_ite j) (huS.mul_left (D0 * u j))
      (fun k x hx => hterm j k x hx)
  have hinb : ∀ j : ℤ, ∀ x ∈ t,
      ‖∑' k : ℤ, (if k = j then (0 : ℝ × ℝ) else rcPair ν s B j k x)‖ ≤ D0 * U * u j := by
    intro j x hx
    have := tsum_of_norm_bounded (huS.hasSum.mul_left (D0 * u j)) (fun k => hterm j k x hx)
    calc _ ≤ D0 * u j * U := this
      _ = D0 * U * u j := by ring
  have hout : ContinuousOn (rcCross ν s B) t :=
    continuousOn_tsum hinner (huS.mul_left (D0 * U)) (fun j x hx => hinb j x hx)
  exact hout.continuousAt ht

end UnforcedLeray.Short.PartIIIb.Concrete
