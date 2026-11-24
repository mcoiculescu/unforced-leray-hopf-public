import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2_1

/-!
# Part III-a, `PartIII-a:T21/2/2/1/1`: the age map `revAge` (Lemma A)

Source of record: `the November 2 reference manuscript` lines 2855-2857, 3077.

`revAge ν s ζ = ageOfZ ν (movingZ ν s - ζ)` with `ageOfZ ν z = z/(1-νz)` the inverse of
`movingZ ν r = r/(1+νr)`. On `[0, Δz]` the moving time runs over `[z_t, z_s]` and `νz < 1` there.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.IIIa

/-- `ageOfZ` inverts `movingZ` on `r ≥ 0`: `ageOfZ ν (movingZ ν r) = r`. -/
theorem ageOfZ_movingZ (ν r : ℝ) (hr : 0 < 1 + ν * r) :
    ageOfZ ν (movingZ ν r) = r := by
  have hne : (1 + ν * r) ≠ 0 := hr.ne'
  unfold ageOfZ movingZ clockA
  have h1 : 1 - ν * (r / (1 + ν * r)) = 1 / (1 + ν * r) := by
    field_simp
    ring
  rw [h1, div_div_eq_mul_div, div_one, div_mul_cancel₀ r hne]

/-- `ageOfZ` is strictly monotone on `{z | ν z < 1}` (for `ν > 0`). -/
theorem ageOfZ_strictMono_of (ν z₁ z₂ : ℝ) (hν : 0 < ν) (h12 : z₁ < z₂) (h2 : ν * z₂ < 1) :
    ageOfZ ν z₁ < ageOfZ ν z₂ := by
  unfold ageOfZ
  have hd1 : 0 < 1 - ν * z₁ := by nlinarith
  have hd2 : 0 < 1 - ν * z₂ := by linarith
  rw [div_lt_div_iff₀ hd1 hd2]
  nlinarith

theorem adjAgeMap : AdjAgeMap := by
  intro ν t s hν ht hts
  have hAs : 0 < 1 + ν * s := by nlinarith
  have hAt : 0 < 1 + ν * t := by nlinarith
  have hzs : ν * movingZ ν s < 1 := by
    have e : ν * movingZ ν s = ν * s / (1 + ν * s) := by
      unfold movingZ clockA
      rw [mul_div_assoc]
    rw [e, div_lt_one hAs]
    linarith
  have hzt : movingZ ν t ≤ movingZ ν s := by
    unfold movingZ clockA
    rw [div_le_div_iff₀ hAt hAs]
    nlinarith
  have hrs : ageOfZ ν (movingZ ν s) = s := ageOfZ_movingZ ν s hAs
  have hrt : ageOfZ ν (movingZ ν t) = t := ageOfZ_movingZ ν t hAt
  have hcont : ContinuousOn (revAge ν s) (Icc 0 (deltaZ ν t s)) := by
    have hfun : revAge ν s = fun ζ => (movingZ ν s - ζ) / (1 - ν * (movingZ ν s - ζ)) := by
      funext ζ
      rfl
    rw [hfun]
    apply ContinuousOn.div
    · exact (continuous_const.sub continuous_id).continuousOn
    · exact (continuous_const.sub
        (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
    · intro ζ hζ
      have h1 : ν * (movingZ ν s - ζ) ≤ ν * movingZ ν s :=
        mul_le_mul_of_nonneg_left (by linarith [hζ.1]) hν.le
      intro h0
      linarith
  have hmono : ∀ z₁ z₂ : ℝ, z₁ ≤ z₂ → ν * z₂ < 1 → ageOfZ ν z₁ ≤ ageOfZ ν z₂ := by
    intro z₁ z₂ h12 h2
    rcases eq_or_lt_of_le h12 with h | h
    · rw [h]
    · exact (ageOfZ_strictMono_of ν z₁ z₂ hν h h2).le
  have hmaps_closed : ∀ ζ ∈ Icc 0 (deltaZ ν t s), t ≤ revAge ν s ζ ∧ revAge ν s ζ ≤ s := by
    intro ζ hζ
    have hΔ' : deltaZ ν t s = movingZ ν s - movingZ ν t := rfl
    have hz1 : movingZ ν t ≤ movingZ ν s - ζ := by linarith [hζ.2]
    have hz2 : movingZ ν s - ζ ≤ movingZ ν s := by linarith [hζ.1]
    have hνz : ν * (movingZ ν s - ζ) ≤ ν * movingZ ν s :=
      mul_le_mul_of_nonneg_left hz2 hν.le
    constructor
    · have := hmono _ _ hz1 (by linarith)
      rw [hrt] at this
      exact this
    · have := hmono _ _ hz2 hzs
      rw [hrs] at this
      exact this
  refine ⟨hcont, ?_, ?_⟩
  · intro ζ hζ
    exact hmaps_closed ζ hζ
  · intro ζ hζ
    refine ⟨(hmaps_closed ζ ⟨hζ.1.le, hζ.2⟩).1, ?_⟩
    have hz2 : movingZ ν s - ζ < movingZ ν s := by linarith [hζ.1]
    have := ageOfZ_strictMono_of ν (movingZ ν s - ζ) (movingZ ν s) hν hz2 hzs
    rw [hrs] at this
    exact this

end UnforcedLeray.Short.IIIa
