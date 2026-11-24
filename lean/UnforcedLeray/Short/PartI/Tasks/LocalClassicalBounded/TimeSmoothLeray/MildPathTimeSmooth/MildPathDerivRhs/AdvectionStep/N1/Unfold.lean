import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_2_1

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

theorem cylTestUnfold : CylTestUnfold := by
  intro c hc φ hφ
  -- a one-variable bump, positive on `|w| < 2c`, zero for `|w| ≥ 2c`
  obtain ⟨ψ, hψs, hψnn, hψpos, hψz⟩ : ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ w, 0 ≤ ψ w) ∧
      (∀ w, |w| < 2 * c → 0 < ψ w) ∧ (∀ w, 2 * c ≤ |w| → ψ w = 0) := by
    let B : ContDiffBump (0 : ℝ) :=
      { rIn := c, rOut := 2 * c, rIn_pos := hc, rIn_lt_rOut := by linarith }
    refine ⟨B, B.contDiff, fun w => B.nonneg' w, fun w hw => B.pos_of_mem_ball ?_, fun w hw => ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact hw
    · by_contra h
      have hmem : w ∈ Function.support B := h
      rw [ContDiffBump.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hmem
      linarith
  -- periodicity of `φ` under all integer shifts
  have hper : ∀ (m : ℤ) (x : ℝ × ℝ), φ (x + ((m : ℝ) * c, 0)) = φ x := by
    intro m x
    have h1 := (show Function.Periodic φ ((c, 0) : ℝ × ℝ) from hφ.periodic).zsmul m x
    have h2 : m • ((c, 0) : ℝ × ℝ) = ((m : ℝ) * c, 0) := by
      ext <;> simp [zsmul_eq_mul]
    rw [h2] at h1
    exact h1
  -- the bump in the coordinates `(q, η)`
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ × ℝ → ℝ, b = fun z => ψ z.1 := ⟨_, rfl⟩
  have hbs : ContDiff ℝ ∞ b := by rw [hbdef]; exact hψs.comp contDiff_fst
  have hbnn : ∀ z, 0 ≤ b z := by intro z; rw [hbdef]; exact hψnn _
  have hbA : ∀ z, b z ≠ 0 → |z.1| ≤ 2 * c := by
    intro z hz
    by_contra h
    push_neg at h
    rw [hbdef] at hz
    exact hz (hψz _ h.le)
  have hbz : ∀ z : ℝ × ℝ, 2 * c ≤ |z.1| → b z = 0 := by
    intro z hz; rw [hbdef]; exact hψz _ hz
  have hPs : ContDiff ℝ ∞ (Sob.perSum c b) := Sob.contDiff_perSum hc hbs hbA
  -- the periodization of `b` is invariant under integer shifts
  have hPper : ∀ (m : ℤ) (z : ℝ × ℝ),
      Sob.perSum c b (z + ((m : ℝ) * c, 0)) = Sob.perSum c b z := by
    intro m z
    have e := finsum_comp_equiv (Equiv.addRight m) (f := fun k : ℤ => b (z + ((k : ℝ) * c, 0)))
    simp only [Equiv.coe_addRight] at e
    unfold Sob.perSum
    rw [← e]
    refine finsum_congr fun k => ?_
    congr 1
    ext <;> simp <;> ring
  -- every point is shifted into the window `|·| < 2c`
  have hfloor : ∀ z : ℝ × ℝ, ∃ m : ℤ, |z.1 + (m : ℝ) * c| < 2 * c := by
    intro z
    refine ⟨-⌊(z.1 + c / 2) / c⌋, ?_⟩
    have h1 := Int.floor_le ((z.1 + c / 2) / c)
    have h2 := Int.lt_floor_add_one ((z.1 + c / 2) / c)
    have e1 : ((⌊(z.1 + c / 2) / c⌋ : ℤ) : ℝ) * c ≤ z.1 + c / 2 := by
      have := mul_le_mul_of_nonneg_right h1 hc.le
      rwa [div_mul_cancel₀ _ hc.ne'] at this
    have e2 : z.1 + c / 2 < (((⌊(z.1 + c / 2) / c⌋ : ℤ) : ℝ) + 1) * c := by
      have := mul_lt_mul_of_pos_right h2 hc
      rwa [div_mul_cancel₀ _ hc.ne'] at this
    rw [abs_lt]
    push_cast
    constructor <;> nlinarith [hc]
  -- the periodization of `b` is strictly positive
  have hPpos : ∀ z : ℝ × ℝ, 0 < Sob.perSum c b z := by
    intro z
    obtain ⟨m, hm⟩ := hfloor z
    have hpos : 0 < b (z + ((m : ℝ) * c, 0)) := by
      rw [hbdef]
      simp only [Prod.fst_add]
      exact hψpos _ hm
    have hmem := Sob.mem_idx_of_ne_zero hc hbA (le_refl |z.1|) hpos.ne'
    have hle := Finset.single_le_sum (f := fun k : ℤ => b (z + ((k : ℝ) * c, 0)))
      (fun k _ => hbnn _) hmem
    rw [Sob.perSum_eq_sum hc hbA (le_refl |z.1|)]
    exact lt_of_lt_of_le hpos hle
  -- the candidate unfolding `χ = φ b / perSum b`
  obtain ⟨χ, hχdef⟩ : ∃ χ : ℝ × ℝ → ℝ, χ = fun z => φ z * b z / Sob.perSum c b z := ⟨_, rfl⟩
  have hχA : ∀ z, χ z ≠ 0 → |z.1| ≤ 2 * c := by
    intro z hz
    apply hbA
    intro hb
    apply hz
    rw [hχdef]
    simp only [hb, mul_zero, zero_div]
  have hχs : ContDiff ℝ ∞ χ := by
    rw [hχdef]
    exact (hφ.smooth.mul hbs).div hPs (fun z => (hPpos z).ne')
  have hcpt : HasCompactSupport χ := by
    obtain ⟨R, hR⟩ := hφ.bounded
    refine HasCompactSupport.intro
      ((isCompact_Icc (a := -(2 * c)) (b := 2 * c)).prod (isCompact_Icc (a := -R) (b := R))) ?_
    intro x hx
    rw [hχdef]
    by_cases h1 : |x.1| ≤ 2 * c
    · have h2 : R < |x.2| := by
        by_contra h2
        push_neg at h2
        exact hx ⟨abs_le.mp h1, abs_le.mp h2⟩
      simp only [hR x h2, zero_mul, zero_div]
    · have h3 : b x = 0 := hbz x (not_le.mp h1).le
      simp only [h3, mul_zero, zero_div]
  refine ⟨χ, hχs, hcpt, fun z => ?_⟩
  have hsumχ := Sob.perSum_eq_sum hc hχA (le_refl |z.1|)
  have hsumb := Sob.perSum_eq_sum hc hbA (le_refl |z.1|)
  have hterm : ∀ m : ℤ, χ (z + ((m : ℝ) * c, 0))
      = φ z * b (z + ((m : ℝ) * c, 0)) / Sob.perSum c b z := by
    intro m
    rw [hχdef]
    simp only [hper m z, hPper m z]
  rw [hsumχ]
  simp only [hterm]
  rw [← Finset.sum_div, ← Finset.mul_sum, ← hsumb, mul_div_assoc,
    div_self (hPpos z).ne', mul_one]

end UnforcedLeray.Short.PartI
