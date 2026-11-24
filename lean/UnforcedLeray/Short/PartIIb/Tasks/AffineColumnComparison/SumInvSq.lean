import UnforcedLeray.Short.PartIIb.Sub.G4
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Part II-b, task `PartII-b:G4/1a`: the periodized inverse-square sum `SumInvSqShift`

Source of record: `the November 2 reference manuscript`, lines 2347-2358
(SP 2349-2352): `Σ_{n∈ℤ}(q+nc+iη)^{-2} = (π/c)² csc²(π(q+iη)/c)`.

Proof. Differentiate Mathlib's `cot_series_rep'` (`π cot(π x) - 1/x = Σ' n:ℕ, cotTerm x n`) at a
point off `ℤ`, termwise on a ball avoiding `ℤ` (`hasDerivAt_tsum_of_isPreconnected`), and compare
with `d/dx π cot(π x) = -π²/sin²(π x)`. Split the `ℤ`-sum into its `n = 0` term and the two `ℕ`
halves (`HasSum.of_nat_of_neg_add_one`). Finally rescale by `w = z/c`.

Contains no proof escapes (checked by `scripts/wip_compile.py`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex

namespace UnforcedLeray.Short.IIb

/-- A point off the integers has a positive distance from them. -/
lemma sumInvSq_dist_int (w0 : ℂ) (hw0 : ∀ m : ℤ, w0 + m ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℤ, δ ≤ ‖w0 + m‖ := by
  have hmem : w0 ∈ (Set.range ((↑) : ℤ → ℂ))ᶜ := by
    rintro ⟨m, hm⟩
    exact hw0 (-m) (by push_cast; rw [← hm]; ring)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp Complex.isOpen_compl_range_intCast w0 hmem
  refine ⟨ε, hε, fun m => ?_⟩
  by_contra h
  have h' : ‖w0 + (m : ℂ)‖ < ε := not_le.mp h
  have hmem' : ((-m : ℤ) : ℂ) ∈ Metric.ball w0 ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    push_cast
    rw [show (-(m : ℂ)) - w0 = -(w0 + m) by ring, norm_neg]
    exact h'
  exact hball hmem' ⟨-m, rfl⟩

/-- A uniform linear lower bound `‖w0 + m‖ ≥ c (1 + |m|)` over all integers `m`. -/
lemma sumInvSq_lower (w0 : ℂ) (δ : ℝ) (hδ : 0 < δ) (hδm : ∀ m : ℤ, δ ≤ ‖w0 + m‖) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℤ, c * (1 + |(m : ℝ)|) ≤ ‖w0 + m‖ := by
  have hA : 0 ≤ ‖w0‖ := norm_nonneg _
  obtain ⟨c, hc0, hc1, hc2⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ c * (3 + 2 * ‖w0‖) ≤ δ :=
    ⟨min (1 / 2) (δ / (3 + 2 * ‖w0‖)),
      lt_min (by norm_num) (div_pos hδ (by positivity)),
      min_le_left _ _,
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)⟩
  refine ⟨c, hc0, fun m => ?_⟩
  have h1 : ‖(m : ℂ)‖ ≤ ‖w0 + m‖ + ‖w0‖ := by
    calc ‖(m : ℂ)‖ = ‖(w0 + m) - w0‖ := by congr 1; ring
      _ ≤ ‖w0 + m‖ + ‖w0‖ := norm_sub_le _ _
  have h2 : |(m : ℝ)| ≤ ‖w0 + m‖ + ‖w0‖ := by
    have e : ‖(m : ℂ)‖ = |(m : ℝ)| := by simp
    linarith
  rcases le_or_gt (2 * ‖w0‖ + 2) |(m : ℝ)| with hbig | hsmall
  · have h3 : c * (1 + |(m : ℝ)|) ≤ 1 / 2 * (1 + |(m : ℝ)|) :=
      mul_le_mul_of_nonneg_right hc1 (by positivity)
    linarith
  · have h3 : c * (1 + |(m : ℝ)|) ≤ c * (3 + 2 * ‖w0‖) :=
      mul_le_mul_of_nonneg_left (by linarith) hc0.le
    linarith [hδm m]

/-- Local uniform bounds near a point `w0` off `ℤ`: a ball on which `w + m ≠ 0` for all `m`,
and `‖(w+m)^{-2}‖ ≤ C/m²` for `m ≠ 0`. -/
lemma sumInvSq_key (w0 : ℂ) (hw0 : ∀ m : ℤ, w0 + m ≠ 0) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ w ∈ Metric.ball w0 r,
      (∀ m : ℤ, w + m ≠ 0) ∧ ∀ m : ℤ, m ≠ 0 → ‖((w + m) ^ 2)⁻¹‖ ≤ C / (m : ℝ) ^ 2 := by
  obtain ⟨δ, hδ, hδm⟩ := sumInvSq_dist_int w0 hw0
  obtain ⟨c, hc0, hlow⟩ := sumInvSq_lower w0 δ hδ hδm
  refine ⟨c / 2, 4 / c ^ 2, half_pos hc0, div_pos four_pos (pow_pos hc0 2),
    fun w hw => ?_⟩
  have hw' : ‖w - w0‖ < c / 2 := by
    rw [Metric.mem_ball, dist_eq_norm] at hw
    exact hw
  have hs : ∀ m : ℤ, c * (1 + |(m : ℝ)|) / 2 ≤ ‖w + m‖ := by
    intro m
    have htri : ‖w0 + m‖ ≤ ‖w + m‖ + ‖w - w0‖ := by
      calc ‖w0 + m‖ = ‖(w + m) - (w - w0)‖ := by congr 1; ring
        _ ≤ ‖w + m‖ + ‖w - w0‖ := norm_sub_le _ _
    have h1 := hlow m
    have h2 : 0 ≤ |(m : ℝ)| := abs_nonneg _
    have e : c * (1 + |(m : ℝ)|) = c + c * |(m : ℝ)| := by ring
    have hp : 0 ≤ c * |(m : ℝ)| := mul_nonneg hc0.le h2
    linarith
  refine ⟨fun m => ?_, fun m hm => ?_⟩
  · intro h
    have h1 := hs m
    rw [h, norm_zero] at h1
    have h2 : 0 ≤ |(m : ℝ)| := abs_nonneg _
    have h3 : 0 < c * (1 + |(m : ℝ)|) := mul_pos hc0 (by linarith)
    linarith
  · have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      have h := Int.one_le_abs hm
      rw [← Int.cast_abs]
      exact_mod_cast h
    have hmpos : 0 < |(m : ℝ)| := by linarith
    have hcne : c ≠ 0 := hc0.ne'
    have hmne : |(m : ℝ)| ≠ 0 := hmpos.ne'
    have hp2 : 0 < c * |(m : ℝ)| / 2 := div_pos (mul_pos hc0 hmpos) two_pos
    have hle : c * |(m : ℝ)| / 2 ≤ ‖w + m‖ := by
      have h1 := hs m
      have e : c * (1 + |(m : ℝ)|) = c + c * |(m : ℝ)| := by ring
      linarith
    calc ‖((w + m) ^ 2)⁻¹‖ = (‖w + m‖ ^ 2)⁻¹ := by rw [norm_inv, norm_pow]
      _ ≤ ((c * |(m : ℝ)| / 2) ^ 2)⁻¹ :=
          inv_anti₀ (pow_pos hp2 2) (pow_le_pow_left₀ hp2.le hle 2)
      _ = 4 / c ^ 2 / (m : ℝ) ^ 2 := by
          rw [← sq_abs (m : ℝ)]
          field_simp
          norm_num

/-- The summing majorant `n ↦ C/(n+1)²` is summable. -/
lemma sumInvSq_summable_bound (C : ℝ) : Summable (fun n : ℕ => C / ((n : ℝ) + 1) ^ 2) := by
  have h := ((summable_nat_add_iff 1).mpr
    (Real.summable_nat_pow_inv.mpr one_lt_two : Summable fun n : ℕ => ((n : ℝ) ^ 2)⁻¹)).mul_left C
  refine h.congr (fun n => ?_)
  simp [div_eq_mul_inv]

lemma sumInvSq_summable_plus (w0 : ℂ) (C : ℝ)
    (hb : ∀ m : ℤ, m ≠ 0 → ‖((w0 + m) ^ 2)⁻¹‖ ≤ C / (m : ℝ) ^ 2) :
    Summable (fun n : ℕ => ((w0 + ((n : ℂ) + 1)) ^ 2)⁻¹) := by
  refine Summable.of_norm_bounded (sumInvSq_summable_bound C) (fun n => ?_)
  have h := hb ((n : ℤ) + 1) (by omega)
  have e : w0 + (((n : ℤ) + 1 : ℤ) : ℂ) = w0 + ((n : ℂ) + 1) := by simp
  have e2 : (((n : ℤ) + 1 : ℤ) : ℝ) ^ 2 = ((n : ℝ) + 1) ^ 2 := by simp
  rw [e, e2] at h
  exact h

lemma sumInvSq_summable_minus (w0 : ℂ) (C : ℝ)
    (hb : ∀ m : ℤ, m ≠ 0 → ‖((w0 + m) ^ 2)⁻¹‖ ≤ C / (m : ℝ) ^ 2) :
    Summable (fun n : ℕ => ((w0 - ((n : ℂ) + 1)) ^ 2)⁻¹) := by
  refine Summable.of_norm_bounded (sumInvSq_summable_bound C) (fun n => ?_)
  have h := hb (-((n : ℤ) + 1)) (by omega)
  have e : w0 + ((-((n : ℤ) + 1) : ℤ) : ℂ) = w0 - ((n : ℂ) + 1) := by push_cast; ring
  have e2 : ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2 = ((n : ℝ) + 1) ^ 2 := by push_cast; ring
  rw [e, e2] at h
  exact h

/-- Derivative of `1 / φ x` when `φ` has derivative `φ'` and `φ w ≠ 0`. -/
lemma sumInvSq_inv_hasDerivAt {φ : ℂ → ℂ} {w φ' : ℂ} (hφ : HasDerivAt φ φ' w) (h : φ w ≠ 0) :
    HasDerivAt (fun x => 1 / φ x) (-φ' * (φ w ^ 2)⁻¹) w := by
  simp only [one_div]
  exact (hφ.inv h).congr_deriv (by ring)

/-- Termwise differentiation of the cotangent series at a point off `ℤ`. -/
lemma sumInvSq_series_hasDerivAt (w0 : ℂ) (hw0 : ∀ m : ℤ, w0 + m ≠ 0) :
    HasDerivAt (fun w : ℂ => ∑' n : ℕ, (1 / (w - ((n : ℂ) + 1)) + 1 / (w + ((n : ℂ) + 1))))
      (∑' n : ℕ, (-((w0 - ((n : ℂ) + 1)) ^ 2)⁻¹ + -((w0 + ((n : ℂ) + 1)) ^ 2)⁻¹)) w0 := by
  obtain ⟨r, C, hr, hC, hkey⟩ := sumInvSq_key w0 hw0
  have hmem : w0 ∈ (Set.range ((↑) : ℤ → ℂ))ᶜ := by
    rintro ⟨m, hm⟩
    exact hw0 (-m) (by push_cast; rw [← hm]; ring)
  have hmem' : w0 ∈ Complex.integerComplement := hmem
  have hsum0 : Summable (fun n : ℕ => 1 / (w0 - ((n : ℂ) + 1)) + 1 / (w0 + ((n : ℂ) + 1))) :=
    summable_cotTerm hmem'
  have hu : Summable (fun n : ℕ => 2 * (C / ((n : ℝ) + 1) ^ 2)) :=
    (sumInvSq_summable_bound C).mul_left 2
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun (n : ℕ) (w : ℂ) => 1 / (w - ((n : ℂ) + 1)) + 1 / (w + ((n : ℂ) + 1)))
    (g' := fun (n : ℕ) (w : ℂ) => -((w - ((n : ℂ) + 1)) ^ 2)⁻¹ + -((w + ((n : ℂ) + 1)) ^ 2)⁻¹)
    (u := fun n : ℕ => 2 * (C / ((n : ℝ) + 1) ^ 2))
    hu Metric.isOpen_ball (convex_ball w0 r).isPreconnected ?_ ?_
    (Metric.mem_ball_self hr) hsum0 (Metric.mem_ball_self hr)
  · intro n y hy
    obtain ⟨hy1, _⟩ := hkey y hy
    have h1 : y - ((n : ℂ) + 1) ≠ 0 := by
      intro h
      apply hy1 (-((n : ℤ) + 1))
      push_cast
      linear_combination h
    have h2 : y + ((n : ℂ) + 1) ≠ 0 := by
      intro h
      apply hy1 ((n : ℤ) + 1)
      push_cast
      linear_combination h
    have hd1 := sumInvSq_inv_hasDerivAt (φ := fun x => x - ((n : ℂ) + 1)) (φ' := 1)
      ((hasDerivAt_id' y).sub_const _) h1
    have hd2 := sumInvSq_inv_hasDerivAt (φ := fun x => x + ((n : ℂ) + 1)) (φ' := 1)
      ((hasDerivAt_id' y).add_const _) h2
    exact (hd1.add hd2).congr_deriv (by ring)
  · intro n y hy
    obtain ⟨_, hb⟩ := hkey y hy
    have b1 := hb (-((n : ℤ) + 1)) (by omega)
    have b2 := hb ((n : ℤ) + 1) (by omega)
    have e1 : y + ((-((n : ℤ) + 1) : ℤ) : ℂ) = y - ((n : ℂ) + 1) := by push_cast; ring
    have e2 : y + (((n : ℤ) + 1 : ℤ) : ℂ) = y + ((n : ℂ) + 1) := by simp
    have c1 : ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2 = ((n : ℝ) + 1) ^ 2 := by push_cast; ring
    have c2 : (((n : ℤ) + 1 : ℤ) : ℝ) ^ 2 = ((n : ℝ) + 1) ^ 2 := by simp
    rw [e1, c1] at b1
    rw [e2, c2] at b2
    calc ‖-((y - ((n : ℂ) + 1)) ^ 2)⁻¹ + -((y + ((n : ℂ) + 1)) ^ 2)⁻¹‖
        ≤ ‖-((y - ((n : ℂ) + 1)) ^ 2)⁻¹‖ + ‖-((y + ((n : ℂ) + 1)) ^ 2)⁻¹‖ := norm_add_le _ _
      _ = ‖((y - ((n : ℂ) + 1)) ^ 2)⁻¹‖ + ‖((y + ((n : ℂ) + 1)) ^ 2)⁻¹‖ := by
          rw [norm_neg, norm_neg]
      _ ≤ C / ((n : ℝ) + 1) ^ 2 + C / ((n : ℝ) + 1) ^ 2 := add_le_add b1 b2
      _ = 2 * (C / ((n : ℝ) + 1) ^ 2) := by ring

/-- The derivative of `π cot(π w) - 1/w` at a point off `ℤ`. -/
lemma sumInvSq_cot_hasDerivAt (w0 : ℂ) (hw0 : ∀ m : ℤ, w0 + m ≠ 0) :
    HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * cot ((Real.pi : ℂ) * w) - 1 / w)
      (-((Real.pi : ℂ) ^ 2 * (Complex.sin ((Real.pi : ℂ) * w0) ^ 2)⁻¹) + (w0 ^ 2)⁻¹) w0 := by
  have hmem : w0 ∈ (Set.range ((↑) : ℤ → ℂ))ᶜ := by
    rintro ⟨m, hm⟩
    exact hw0 (-m) (by push_cast; rw [← hm]; ring)
  have hmem' : w0 ∈ Complex.integerComplement := hmem
  have hsin : Complex.sin ((Real.pi : ℂ) * w0) ≠ 0 := sin_pi_mul_ne_zero hmem'
  have hw0z : w0 ≠ 0 := by simpa using hw0 0
  have hlin : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w) (Real.pi : ℂ) w0 := by
    simpa using (hasDerivAt_id' w0).const_mul (Real.pi : ℂ)
  have hcot : HasDerivAt (fun w : ℂ => Complex.cos ((Real.pi : ℂ) * w) / Complex.sin ((Real.pi : ℂ) * w))
      (((-Complex.sin ((Real.pi : ℂ) * w0) * (Real.pi : ℂ)) * Complex.sin ((Real.pi : ℂ) * w0)
        - Complex.cos ((Real.pi : ℂ) * w0) * (Complex.cos ((Real.pi : ℂ) * w0) * (Real.pi : ℂ)))
        / Complex.sin ((Real.pi : ℂ) * w0) ^ 2) w0 :=
    hlin.ccos.div hlin.csin hsin
  have hcot' : HasDerivAt (fun w : ℂ => cot ((Real.pi : ℂ) * w))
      (-(Real.pi : ℂ) * (Complex.sin ((Real.pi : ℂ) * w0) ^ 2)⁻¹) w0 := by
    have hfun : (fun w : ℂ => cot ((Real.pi : ℂ) * w))
        = (fun w : ℂ => Complex.cos ((Real.pi : ℂ) * w) / Complex.sin ((Real.pi : ℂ) * w)) := rfl
    rw [hfun]
    convert hcot using 1
    have hpy := Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * w0)
    have hi : (Complex.sin ((Real.pi : ℂ) * w0) ^ 2)⁻¹ * Complex.sin ((Real.pi : ℂ) * w0) ^ 2 = 1 :=
      inv_mul_cancel₀ (pow_ne_zero 2 hsin)
    rw [eq_div_iff (pow_ne_zero 2 hsin)]
    linear_combination (-(Real.pi : ℂ)) * hi + (Real.pi : ℂ) * hpy
  have hinv : HasDerivAt (fun w : ℂ => 1 / w) (-(w0 ^ 2)⁻¹) w0 := by
    simpa only [one_div] using hasDerivAt_inv hw0z
  have h2 := (hcot'.const_mul (Real.pi : ℂ)).sub hinv
  exact h2.congr_deriv (by ring)

/-- Shift of a `ℕ`-indexed sum: `HasSum F (F 0 + P)` from `HasSum (F (· + 1)) P`. -/
lemma sumInvSq_hasSum_succ' {F : ℕ → ℂ} {a P : ℂ} (h0 : F 0 = a)
    (h : HasSum (fun n => F (n + 1)) P) : HasSum F (a + P) := by
  have h2 : HasSum (fun n => F (n + 1)) (a + P - ∑ i ∈ Finset.range 1, F i) := by
    rw [Finset.sum_range_one, h0]
    simpa using h
  exact (hasSum_nat_add_iff' 1).mp h2

/-- The `ℤ`-sum `Σ_{m∈ℤ} (w+m)^{-2}` at a point `w` off `ℤ`. -/
theorem sumInvSq_core (w0 : ℂ) (hw0 : ∀ m : ℤ, w0 + m ≠ 0) :
    HasSum (fun m : ℤ => ((w0 + (m : ℂ)) ^ 2)⁻¹)
      ((Real.pi : ℂ) ^ 2 * (Complex.sin ((Real.pi : ℂ) * w0) ^ 2)⁻¹) := by
  obtain ⟨r, C, hr, hC, hkey⟩ := sumInvSq_key w0 hw0
  have hmem : w0 ∈ (Set.range ((↑) : ℤ → ℂ))ᶜ := by
    rintro ⟨m, hm⟩
    exact hw0 (-m) (by push_cast; rw [← hm]; ring)
  have hb : ∀ m : ℤ, m ≠ 0 → ‖((w0 + m) ^ 2)⁻¹‖ ≤ C / (m : ℝ) ^ 2 :=
    (hkey w0 (Metric.mem_ball_self hr)).2
  have hPs := sumInvSq_summable_plus w0 C hb
  have hMs := sumInvSq_summable_minus w0 C hb
  have hD1 := sumInvSq_cot_hasDerivAt w0 hw0
  have hD2 := sumInvSq_series_hasDerivAt w0 hw0
  have heq : (fun w : ℂ => (Real.pi : ℂ) * cot ((Real.pi : ℂ) * w) - 1 / w) =ᶠ[𝓝 w0]
      (fun w : ℂ => ∑' n : ℕ, (1 / (w - ((n : ℂ) + 1)) + 1 / (w + ((n : ℂ) + 1)))) := by
    filter_upwards [Complex.isOpen_compl_range_intCast.mem_nhds hmem] with w hw
    exact cot_series_rep' hw
  have hD2' := hD2.congr_of_eventuallyEq heq
  have hval := hD1.unique hD2'
  have hS : (∑' n : ℕ, (-((w0 - ((n : ℂ) + 1)) ^ 2)⁻¹ + -((w0 + ((n : ℂ) + 1)) ^ 2)⁻¹))
      = -(∑' n : ℕ, ((w0 - ((n : ℂ) + 1)) ^ 2)⁻¹) - ∑' n : ℕ, ((w0 + ((n : ℂ) + 1)) ^ 2)⁻¹ := by
    rw [Summable.tsum_add hMs.neg hPs.neg, tsum_neg, tsum_neg]
    ring
  have hval2 := hval.trans hS
  have hfirst : HasSum (fun n : ℕ => ((w0 + ((n : ℤ) : ℂ)) ^ 2)⁻¹)
      ((w0 ^ 2)⁻¹ + ∑' n : ℕ, ((w0 + ((n : ℂ) + 1)) ^ 2)⁻¹) := by
    have hPh : HasSum (fun n : ℕ => ((w0 + (((n + 1 : ℕ) : ℤ) : ℂ)) ^ 2)⁻¹)
        (∑' n : ℕ, ((w0 + ((n : ℂ) + 1)) ^ 2)⁻¹) := by
      have e : (fun n : ℕ => ((w0 + (((n + 1 : ℕ) : ℤ) : ℂ)) ^ 2)⁻¹)
          = fun n : ℕ => ((w0 + ((n : ℂ) + 1)) ^ 2)⁻¹ := by
        funext n
        simp
      rw [e]
      exact hPs.hasSum
    exact sumInvSq_hasSum_succ' (F := fun n : ℕ => ((w0 + ((n : ℤ) : ℂ)) ^ 2)⁻¹)
      (a := (w0 ^ 2)⁻¹) (by simp) hPh
  have hsecond : HasSum (fun n : ℕ => ((w0 + ((-((n : ℤ) + 1) : ℤ) : ℂ)) ^ 2)⁻¹)
      (∑' n : ℕ, ((w0 - ((n : ℂ) + 1)) ^ 2)⁻¹) := by
    have e : (fun n : ℕ => ((w0 + ((-((n : ℤ) + 1) : ℤ) : ℂ)) ^ 2)⁻¹)
        = fun n : ℕ => ((w0 - ((n : ℂ) + 1)) ^ 2)⁻¹ := by
      funext n
      simp [sub_eq_add_neg]
    rw [e]
    exact hMs.hasSum
  have hfull := HasSum.of_nat_of_neg_add_one
    (f := fun m : ℤ => ((w0 + (m : ℂ)) ^ 2)⁻¹) hfirst hsecond
  have hEq : (w0 ^ 2)⁻¹ + (∑' n : ℕ, ((w0 + ((n : ℂ) + 1)) ^ 2)⁻¹)
      + (∑' n : ℕ, ((w0 - ((n : ℂ) + 1)) ^ 2)⁻¹)
      = (Real.pi : ℂ) ^ 2 * (Complex.sin ((Real.pi : ℂ) * w0) ^ 2)⁻¹ := by
    linear_combination hval2
  rw [hEq] at hfull
  exact hfull

/-- **`SumInvSqShift`** (SP 2349-2352): for `c > 0` and `z` with `z + n c ≠ 0` for all `n ∈ ℤ`,
`Σ_{n∈ℤ} (z + nc)^{-2} = (π/c)² (sin(π z/c))^{-2}`. -/
theorem sumInvSqShift : SumInvSqShift := by
  intro c z hc hz
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hcz : (c : ℂ) * (z / (c : ℂ)) = z := by field_simp
  have e : ∀ m : ℤ, z + (m : ℂ) * (c : ℂ) = (c : ℂ) * (z / (c : ℂ) + m) := by
    intro m
    rw [mul_add, hcz]
    ring
  have hw0 : ∀ m : ℤ, z / (c : ℂ) + m ≠ 0 := by
    intro m h
    apply hz m
    rw [e m, h, mul_zero]
  have key := (sumInvSq_core (z / (c : ℂ)) hw0).mul_left (((c : ℂ) ^ 2)⁻¹)
  have hfun : (fun n : ℤ => ((z + (n : ℂ) * (c : ℂ)) ^ 2)⁻¹)
      = fun m : ℤ => ((c : ℂ) ^ 2)⁻¹ * ((z / (c : ℂ) + m) ^ 2)⁻¹ := by
    funext m
    rw [e m, mul_pow, mul_inv]
  have hval : ((Real.pi : ℂ) / (c : ℂ)) ^ 2 * (Complex.sin ((Real.pi : ℂ) * z / (c : ℂ)) ^ 2)⁻¹
      = ((c : ℂ) ^ 2)⁻¹
        * ((Real.pi : ℂ) ^ 2 * (Complex.sin ((Real.pi : ℂ) * (z / (c : ℂ))) ^ 2)⁻¹) := by
    rw [mul_div_assoc]
    ring
  rw [hfun, hval]
  exact key

end UnforcedLeray.Short.IIb
