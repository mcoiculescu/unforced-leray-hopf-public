import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_2

/-!
# Part II-b, task `PartII-b:G4/5/2/2/1` (`AgeCutoffJets`)

Source of record: `the November 2 reference manuscript`, lines 2347-2369, 2383-2385.
`ageCutoff H s = Real.smoothTransition (2 - 4 s / H)`. Its derivatives are `(-4/H)^l` times
derivatives of the smooth transition evaluated at an affine argument; the derivatives of
`Real.smoothTransition` are continuous and vanish outside `[0,1]` (order `≥ 1`), so they are bounded.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

/-- The smooth transition is constant (equal to `0`) near every point of `(-∞, 0)`. -/
theorem ageJets_eventually_zero {x : ℝ} (hx : x < 0) :
    Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact Real.smoothTransition.zero_of_nonpos (le_of_lt (Set.mem_Iio.mp hy))

/-- The smooth transition is constant (equal to `1`) near every point of `(1, ∞)`. -/
theorem ageJets_eventually_one {x : ℝ} (hx : 1 < x) :
    Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact Real.smoothTransition.one_of_one_le (le_of_lt (Set.mem_Ioi.mp hy))

/-- Derivatives of order `≥ 1` of the smooth transition vanish off `[0,1]`. -/
theorem ageJets_iteratedDeriv_off (k : ℕ) {x : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) :
    iteratedDeriv (k + 1) Real.smoothTransition x = 0 := by
  by_cases h0 : x < 0
  · rw [(ageJets_eventually_zero h0).iteratedDeriv_eq (k + 1), iteratedDeriv_const, if_neg (by omega)]
  · have h1 : 1 < x := by
      by_contra h
      exact hx ⟨not_lt.mp h0, not_lt.mp h⟩
    rw [(ageJets_eventually_one h1).iteratedDeriv_eq (k + 1), iteratedDeriv_const, if_neg (by omega)]

/-- Uniform bound on every derivative of the smooth transition. -/
theorem ageJets_bound (l : ℕ) : ∃ M : ℝ, ∀ x : ℝ, ‖iteratedDeriv l Real.smoothTransition x‖ ≤ M := by
  cases l with
  | zero =>
    refine ⟨1, fun x => ?_⟩
    rw [iteratedDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg x)]
    exact Real.smoothTransition.le_one x
  | succ k =>
    have hc : Continuous (iteratedDeriv (k + 1) Real.smoothTransition) :=
      ContDiff.continuous_iteratedDeriv' (k + 1) Real.smoothTransition.contDiff
    have hcs : HasCompactSupport (iteratedDeriv (k + 1) Real.smoothTransition) :=
      HasCompactSupport.intro isCompact_Icc (fun x hx => ageJets_iteratedDeriv_off k hx)
    exact hc.bounded_above_of_compact_support hcs

theorem ageCutoffJets : UnforcedLeray.Short.IIb.AgeCutoffJets := by
  intro j
  choose M hM using ageJets_bound
  refine ⟨1 + ∑ l ∈ Finset.range (j + 1), |4 ^ l * M l|, ?_, ?_⟩
  · have := Finset.sum_nonneg (fun l (_ : l ∈ Finset.range (j + 1)) => abs_nonneg (4 ^ l * M l))
    linarith
  intro H hH l hl s
  set c : ℝ := -(4 / H) with hc
  have hφ : ContDiff ℝ l (fun z : ℝ => Real.smoothTransition (z + 2)) :=
    Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)
  have hfun : ageCutoff H = fun x : ℝ => (fun z : ℝ => Real.smoothTransition (z + 2)) (c * x) := by
    funext x
    simp only [ageCutoff]
    congr 1
    rw [hc]
    ring
  have hit : iteratedDeriv l (fun z : ℝ => Real.smoothTransition (z + 2)) =
      fun t => iteratedDeriv l Real.smoothTransition (t + 2) :=
    iteratedDeriv_comp_add_const l Real.smoothTransition 2
  have habs : |c| = 4 * H⁻¹ := by
    rw [hc, abs_neg, abs_of_pos (div_pos (by norm_num : (0 : ℝ) < 4) hH), div_eq_mul_inv]
  have hD : ‖iteratedDeriv l Real.smoothTransition (c * s + 2)‖ ≤ M l := hM l _
  have h4 : 4 ^ l * M l ≤ 1 + ∑ l ∈ Finset.range (j + 1), |4 ^ l * M l| := by
    have hmem : l ∈ Finset.range (j + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hl)
    have hsum := Finset.single_le_sum (f := fun l => |4 ^ l * M l|)
      (fun i _ => abs_nonneg (4 ^ i * M i)) hmem
    have := le_abs_self (4 ^ l * M l)
    linarith
  have hHinv : 0 ≤ (H⁻¹) ^ l := pow_nonneg (inv_nonneg.mpr hH.le) l
  rw [hfun, iteratedDeriv_comp_const_mul hφ c, hit]
  rw [norm_mul, norm_pow, Real.norm_eq_abs, habs, mul_pow]
  calc (4 : ℝ) ^ l * (H⁻¹) ^ l * ‖iteratedDeriv l Real.smoothTransition (c * s + 2)‖
      ≤ (4 : ℝ) ^ l * (H⁻¹) ^ l * M l :=
        mul_le_mul_of_nonneg_left hD (by positivity)
    _ = (4 ^ l * M l) * (H⁻¹) ^ l := by ring
    _ ≤ (1 + ∑ l ∈ Finset.range (j + 1), |4 ^ l * M l|) * (H⁻¹) ^ l :=
        mul_le_mul_of_nonneg_right h4 hHinv

end UnforcedLeray.Short.IIb
