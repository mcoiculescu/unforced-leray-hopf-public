import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c2_2_7
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrVelImage.Tail

/-!
# Part III-a, task `PartIII-a:T21/c2/2/7/1`: `FmrVelImage`

Source of record: `the November 2 reference manuscript` line 2955 and lines
291-303. The image vortices of the periodization `V_c` of the central Gaussian vortex lie at
distance `≥ c/2` on the cell; the width-dependent lattice tail
(`FmrVelImage/Tail.lean`) gives the error `(2a+1) e^{-c²/(32a)} Λ`, and with `c² = ν⁻⁴`,
`a ≤ 1/(νb)` it is smaller than `(ε/4) a^{-3/2}` for small `ν`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Short.IIb
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem fmrVelImage : FmrVelImage := by
  intro b hb ε hε
  set D : ℝ := 12 * 720 * 32 ^ 6 * (fmrImageLam + 1) with hD
  have hΛ := fmrImageLam_nonneg
  have hDpos : 0 < D := by rw [hD]; positivity
  have hK : 0 < ε * b ^ 9 / D := by positivity
  refine ⟨min 1 (min b (ε * b ^ 9 / D)), lt_min one_pos (lt_min hb hK), ?_⟩
  intro ν hν s hs hθ x hx
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 := hν.2.trans (min_le_left _ _)
  have hνb : ν ≤ b := hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνD : ν ≤ ε * b ^ 9 / (12 * 720 * 32 ^ 6 * (fmrImageLam + 1)) :=
    hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  set c : ℝ := ν ^ (-2 : ℝ) with hcdef
  have hcν : c * ν ^ 2 = 1 := by
    rw [hcdef, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hν0.le, Real.rpow_natCast]
    field_simp
  have hc4 : c ^ 2 * ν ^ 4 = 1 := by
    have : c ^ 2 * ν ^ 4 = (c * ν ^ 2) ^ 2 := by ring
    rw [this, hcν]; norm_num
  have hc1 : 1 ≤ c := by
    have h2 : ν ^ 2 ≤ 1 := by nlinarith
    have hc0 : 0 ≤ c := by
      rw [hcdef]; exact (Real.rpow_pos_of_pos hν0 _).le
    nlinarith [mul_nonneg hc0 (sub_nonneg.mpr h2)]
  have hνs : 0 ≤ ν * s := mul_nonneg hν0.le hs
  have ha1 : 1 ≤ 1 + ν * s := by linarith
  have ha0 : 0 < 1 + ν * s := by linarith
  have hθ' : b ≤ 1 / (ν * (1 + ν * s)) := by
    simpa [clockTheta, clockA, one_div] using hθ
  have hab : (1 + ν * s) * ν * b ≤ 1 := by
    have := (le_div_iff₀ (mul_pos hν0 ha0)).mp hθ'
    nlinarith
  have hac : 1 + ν * s ≤ c ^ 2 := by
    have h3 : ν ^ 3 ≤ b := by
      have h2 : ν ^ 2 ≤ 1 := by nlinarith
      have : ν ^ 3 ≤ ν := by nlinarith
      linarith
    have key : (1 + ν * s) * ν ^ 4 ≤ 1 := by
      have h6 : (1 + ν * s) * ν * ν ^ 3 ≤ (1 + ν * s) * ν * b :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have h7 : (1 + ν * s) * ν ^ 4 = (1 + ν * s) * ν * ν ^ 3 := by ring
      linarith
    have : (1 + ν * s) * ν ^ 4 ≤ c ^ 2 * ν ^ 4 := by rw [hc4]; exact key
    exact le_of_mul_le_mul_right this (pow_pos hν0 4)
  have hx1 : |x.1| ≤ c / 2 := by
    have hx' : x.1 ∈ Ico (-(c / 2)) (c / 2) := (Set.mem_prod.mp hx).1
    obtain ⟨hl, hr⟩ := Set.mem_Ico.mp hx'
    exact abs_le.mpr ⟨hl, hr.le⟩
  have t1 := fmrImage_tail_u1 ha1 hac hc1 x hx1
  have t2 := fmrImage_tail_u2 ha1 hac hc1 x hx1
  rw [← trainGap_vc_fst hν0 hc1 hs x] at t1
  rw [← trainGap_vc_snd hν0 hc1 hs x] at t2
  rw [← trainGap_iso_fst ν s x] at t1
  rw [← trainGap_iso_snd ν s x] at t2
  have hsm := fmrImage_small hν0 hν1 hb hε ha1 hab hc4 hΛ hνD
  have hE : 0 ≤ Real.exp (-(c ^ 2 / (32 * (1 + ν * s)))) := (Real.exp_pos _).le
  have hX : 0 ≤ 6 * (1 + ν * s) * fmrImageLam * Real.exp (-(c ^ 2 / (32 * (1 + ν * s)))) := by
    positivity
  have hsum : |Train.Vc ν c s x 0 - (UnforcedLeray.B0146.isoVelocity ν s x).1| +
      |Train.Vc ν c s x 1 - (UnforcedLeray.B0146.isoVelocity ν s x).2| ≤
      6 * (1 + ν * s) * fmrImageLam * Real.exp (-(c ^ 2 / (32 * (1 + ν * s)))) := by
    have : 2 * ((2 * (1 + ν * s) + 1) * Real.exp (-(c ^ 2 / (32 * (1 + ν * s)))) * fmrImageLam)
        ≤ 6 * (1 + ν * s) * fmrImageLam * Real.exp (-(c ^ 2 / (32 * (1 + ν * s)))) := by
      have := mul_nonneg (mul_nonneg hE hΛ) (sub_nonneg.mpr ha1)
      nlinarith
    linarith
  refine hsum.trans ?_
  -- compare with `ε/2 · a^{-3/2}`
  have hr0 : 0 < (1 + ν * s) ^ ((3 / 2 : ℝ)) := Real.rpow_pos_of_pos ha0 _
  have hr2 : (1 + ν * s) ^ ((3 / 2 : ℝ)) ≤ (1 + ν * s) ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le ha1 (show (3 / 2 : ℝ) ≤ 2 by norm_num)
    simpa [Real.rpow_two] using this
  have hneg : clockA ν s ^ (-(3 / 2) : ℝ) = ((1 + ν * s) ^ ((3 / 2 : ℝ)))⁻¹ := by
    unfold clockA
    rw [Real.rpow_neg ha0.le]
  rw [hneg, ← div_eq_mul_inv, le_div_iff₀ hr0]
  calc 6 * (1 + ν * s) * fmrImageLam * Real.exp (-(c ^ 2 / (32 * (1 + ν * s)))) *
        (1 + ν * s) ^ ((3 / 2 : ℝ))
      ≤ 6 * (1 + ν * s) * fmrImageLam * Real.exp (-(c ^ 2 / (32 * (1 + ν * s)))) *
        (1 + ν * s) ^ 2 := mul_le_mul_of_nonneg_left hr2 hX
    _ = 6 * fmrImageLam * ((1 + ν * s) ^ 3 * Real.exp (-(c ^ 2 / (32 * (1 + ν * s))))) := by ring
    _ ≤ ε / 2 := hsm

end UnforcedLeray.Short.IIIa
