import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.Defs

/-!
# `PartIII-a:T21/2/2/2/2/5`: differentiation of `ζ ↦ ∫ reyIntegrand` (`ReyDeriv`)

Source of record: `the November 2 reference manuscript` lines 2857-2860 (`dr/dζ`)
and 3060-3062. The proof is the chain rule through `revAge`, using the explicit inverse
`r ↦ movingZ s - movingZ r` of `ζ ↦ revAge ν s ζ`, so no smoothness of `φ` is needed: where the
pointwise `r`-derivative does not exist both sides vanish.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

theorem r5_movingZ_ageOfZ (ν z : ℝ) (hz : 1 - ν * z ≠ 0) :
    movingZ ν (ageOfZ ν z) = z := by
  unfold movingZ ageOfZ clockA
  have h1 : 1 + ν * (z / (1 - ν * z)) = 1 / (1 - ν * z) := by
    field_simp
    ring
  have hz' : 1 - z * ν ≠ 0 := by rw [mul_comm]; exact hz
  rw [h1]
  field_simp

theorem r5_ageOfZ_movingZ (ν r : ℝ) (hr : 1 + ν * r ≠ 0) :
    ageOfZ ν (movingZ ν r) = r := by
  unfold movingZ ageOfZ clockA
  have h1 : 1 - ν * (r / (1 + ν * r)) = 1 / (1 + ν * r) := by
    field_simp
    ring
  have hr' : 1 + r * ν ≠ 0 := by rw [mul_comm]; exact hr
  rw [h1]
  field_simp

theorem r5_movingZ_sub (ν a b : ℝ) (ha : 1 + ν * a ≠ 0) (hb : 1 + ν * b ≠ 0) :
    movingZ ν b - movingZ ν a = (b - a) / ((1 + ν * a) * (1 + ν * b)) := by
  unfold movingZ clockA
  rw [div_sub_div _ _ hb ha]
  congr 1 <;> ring

theorem r5_lt_of_movingZ_lt (ν a b : ℝ) (hν : 0 < ν) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (h : movingZ ν a < movingZ ν b) : a < b := by
  have ha : 0 < 1 + ν * a := by have := mul_nonneg hν.le ha0; linarith
  have hb : 0 < 1 + ν * b := by have := mul_nonneg hν.le hb0; linarith
  have key := r5_movingZ_sub ν a b ha.ne' hb.ne'
  have hd : 0 < (1 + ν * a) * (1 + ν * b) := mul_pos ha hb
  have hpos : 0 < (b - a) / ((1 + ν * a) * (1 + ν * b)) := by linarith
  exact sub_pos.mp ((div_pos_iff_of_pos_right hd).mp hpos)

theorem r5_revAge_inv (ν s r : ℝ) (hr : 1 + ν * r ≠ 0) :
    revAge ν s (movingZ ν s - movingZ ν r) = r := by
  unfold revAge
  rw [show movingZ ν s - (movingZ ν s - movingZ ν r) = movingZ ν r by ring]
  exact r5_ageOfZ_movingZ ν r hr

theorem r5_movingZ_revAge (ν s ζ : ℝ) (hz : 1 - ν * (movingZ ν s - ζ) ≠ 0) :
    movingZ ν s - movingZ ν (revAge ν s ζ) = ζ := by
  unfold revAge
  rw [r5_movingZ_ageOfZ ν _ hz]
  ring

theorem r5_deriv_comp (ν s ζ D : ℝ) (G : ℝ → ℝ)
    (hν : 0 < ν) (hD : HasDerivAt (revAge ν s) D ζ)
    (hr : 1 + ν * revAge ν s ζ ≠ 0) (hz : 1 - ν * (movingZ ν s - ζ) ≠ 0) :
    deriv (fun ζ' => G (revAge ν s ζ')) ζ = D * deriv G (revAge ν s ζ) := by
  by_cases hG : DifferentiableAt ℝ G (revAge ν s ζ)
  · have h := (HasDerivAt.scomp ζ hG.hasDerivAt hD).deriv
    rw [smul_eq_mul] at h
    exact h
  · have h0 : deriv G (revAge ν s ζ) = 0 := deriv_zero_of_not_differentiableAt hG
    rw [h0, mul_zero]
    apply deriv_zero_of_not_differentiableAt
    intro hF
    apply hG
    have hmz : DifferentiableAt ℝ (fun r' : ℝ => movingZ ν r') (revAge ν s ζ) := by
      unfold movingZ clockA
      exact ((hasDerivAt_id (revAge ν s ζ)).div
        (((hasDerivAt_id (revAge ν s ζ)).const_mul ν).const_add 1) hr).differentiableAt
    have hk : DifferentiableAt ℝ (fun r' : ℝ => movingZ ν s - movingZ ν r') (revAge ν s ζ) :=
      (differentiableAt_const _).sub hmz
    have hkr : movingZ ν s - movingZ ν (revAge ν s ζ) = ζ := r5_movingZ_revAge ν s ζ hz
    have hF2 : DifferentiableAt ℝ (fun ζ' => G (revAge ν s ζ'))
        (movingZ ν s - movingZ ν (revAge ν s ζ)) := by
      rw [hkr]; exact hF
    have hc2 := hF2.comp (revAge ν s ζ) hk
    have hcont : ContinuousAt (fun r' : ℝ => 1 + ν * r') (revAge ν s ζ) := by fun_prop
    have hpos : ∀ᶠ r' in 𝓝 (revAge ν s ζ), 1 + ν * r' ≠ 0 := hcont.eventually_ne hr
    have hev : G =ᶠ[𝓝 (revAge ν s ζ)]
        (fun r' => G (revAge ν s (movingZ ν s - movingZ ν r'))) := by
      filter_upwards [hpos] with r' hr'
      rw [r5_revAge_inv ν s r' hr']
    exact hc2.congr_of_eventuallyEq hev

theorem reyDeriv (m : ℝ) (hc : UnforcedLeray.Short.IIIa.E0.ReyChain)
    (h1 : UnforcedLeray.Short.IIIa.E0.ReyPhysDeriv m) :
    UnforcedLeray.Short.IIIa.E0.ReyDeriv m := by
  intro ν hν tr t s ht hts g φ hφ ζ hζ
  obtain ⟨hζ0, hζΔ⟩ := hζ
  have hD := (hc ν hν t s ht hts ζ ⟨hζ0, hζΔ⟩).1
  have hζΔ' : ζ < movingZ ν s - movingZ ν t := hζΔ
  have hs0 : 0 < s := by linarith
  have ht0' : 0 ≤ movingZ ν t := by
    unfold movingZ clockA
    apply div_nonneg ht
    have := mul_nonneg hν.le ht; linarith
  have hms : ν * movingZ ν s < 1 := by
    have key : 1 - ν * (s / (1 + ν * s)) = 1 / (1 + ν * s) := by
      have hne : 1 + ν * s ≠ 0 := by have := mul_pos hν hs0; linarith
      field_simp
      ring
    have hp : 0 < 1 / (1 + ν * s) := by
      apply div_pos one_pos
      have := mul_pos hν hs0; linarith
    have hm : movingZ ν s = s / (1 + ν * s) := rfl
    rw [hm]
    linarith
  -- the moving age `z = movingZ s - ζ` lies strictly between `movingZ t` and `movingZ s`
  have hz_lo : 0 < movingZ ν s - ζ := by linarith
  have hz_hi : movingZ ν s - ζ < movingZ ν s := by linarith
  have hνz : ν * (movingZ ν s - ζ) < 1 := by
    have := mul_le_mul_of_nonneg_left hz_hi.le hν.le
    linarith
  have hzpos : 0 < 1 - ν * (movingZ ν s - ζ) := by linarith
  have hz : 1 - ν * (movingZ ν s - ζ) ≠ 0 := hzpos.ne'
  have hr0 : 0 ≤ revAge ν s ζ := by
    have e : revAge ν s ζ = (movingZ ν s - ζ) / (1 - ν * (movingZ ν s - ζ)) := rfl
    rw [e]
    exact div_nonneg hz_lo.le hzpos.le
  have hr1 : 1 + ν * revAge ν s ζ ≠ 0 := by
    have := mul_nonneg hν.le hr0
    exact (by linarith : (0:ℝ) < 1 + ν * revAge ν s ζ).ne'
  have hmr : movingZ ν (revAge ν s ζ) = movingZ ν s - ζ := by
    have := r5_movingZ_revAge ν s ζ hz
    linarith
  have hrIcc : revAge ν s ζ ∈ Ioo t s := by
    constructor
    · apply r5_lt_of_movingZ_lt ν t _ hν ht hr0
      rw [hmr]; linarith
    · apply r5_lt_of_movingZ_lt ν _ s hν hr0 hs0.le
      rw [hmr]; linarith
  have hH := h1 ν hν tr t s ht hts g φ hφ (revAge ν s ζ) hrIcc
  have hcomp := HasDerivAt.scomp ζ hH hD
  have hpt : ∀ x : ℝ × ℝ,
      deriv (fun ζ' => reyIntegrand ν (ν ^ (-2 : ℝ)) m φ s ζ' x) ζ =
        (-(clockA ν (revAge ν s ζ)) ^ 2) *
          deriv (fun r' => physE0Integrand ν (ν ^ (-2 : ℝ)) m φ r' x) (revAge ν s ζ) :=
    fun x => r5_deriv_comp ν s ζ _ (fun r' => physE0Integrand ν (ν ^ (-2 : ℝ)) m φ r' x)
      hν hD hr1 hz
  have hint : (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
      deriv (fun ζ' => reyIntegrand ν (ν ^ (-2 : ℝ)) m φ s ζ' x) ζ) =
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
        (-(clockA ν (revAge ν s ζ)) ^ 2) *
          deriv (fun r' => physE0Integrand ν (ν ^ (-2 : ℝ)) m φ r' x) (revAge ν s ζ) := by
    simp only [hpt]
  rw [hint, integral_const_mul]
  have hc' := hcomp
  rw [smul_eq_mul] at hc'
  exact hc'

end UnforcedLeray.Short.IIIa.E0
