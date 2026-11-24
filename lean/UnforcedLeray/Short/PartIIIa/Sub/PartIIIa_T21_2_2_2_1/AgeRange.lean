import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1

/-!
# `PartIII-a:T21/2/2/2/1/0`: the reverse age lies in `(t, s)`

Source: `the November 2 reference manuscript` lines 2854-2865 (`eq:short-causal-moving`),
2857 (`z(r) = z_s - ζ ∈ (z_t, z_s)`). Proof: `ageOfZ` inverts `movingZ` and is strictly increasing on
`{ν z < 1}`; `z_s - ζ` lies strictly between `z_t` and `z_s`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.E0

/-- `ageOfZ` inverts `movingZ` on `1 + ν r > 0`. -/
theorem ageOfZ_movingZ_aux (ν r : ℝ) (hr : 0 < 1 + ν * r) :
    UnforcedLeray.Short.IIIa.ageOfZ ν (UnforcedLeray.Short.IIIa.movingZ ν r) = r := by
  have hne : (1 + ν * r) ≠ 0 := hr.ne'
  unfold UnforcedLeray.Short.IIIa.ageOfZ UnforcedLeray.Short.IIIa.movingZ UnforcedLeray.Short.IIIa.clockA
  have h1 : 1 - ν * (r / (1 + ν * r)) = 1 / (1 + ν * r) := by
    field_simp
    ring
  rw [h1, div_div_eq_mul_div, div_one, div_mul_cancel₀ r hne]

/-- `ageOfZ` is strictly monotone on `{ν z < 1}`. -/
theorem ageOfZ_mono_aux (ν z₁ z₂ : ℝ) (hν : 0 < ν) (h12 : z₁ < z₂) (h2 : ν * z₂ < 1) :
    UnforcedLeray.Short.IIIa.ageOfZ ν z₁ < UnforcedLeray.Short.IIIa.ageOfZ ν z₂ := by
  unfold UnforcedLeray.Short.IIIa.ageOfZ
  have hd1 : 0 < 1 - ν * z₁ := by nlinarith [mul_pos hν (sub_pos.2 h12)]
  have hd2 : 0 < 1 - ν * z₂ := by linarith
  rw [div_lt_div_iff₀ hd1 hd2]
  nlinarith [mul_pos hν (sub_pos.2 h12)]

theorem adjRangeAge : UnforcedLeray.Short.IIIa.E0.AdjRangeAge := by
  intro ν hν t s ht hts ζ hζ
  have hζ' := hζ
  unfold UnforcedLeray.Short.IIIa.deltaZ at hζ'
  obtain ⟨hζ0, hζΔ⟩ := hζ'
  have hAt : 0 < 1 + ν * t := by
    have := mul_nonneg hν.le ht
    linarith
  have hAs : 0 < 1 + ν * s := by
    have := mul_nonneg hν.le (ht.trans hts.le)
    have : 0 ≤ ν * s := by nlinarith
    linarith
  have hzs : ν * UnforcedLeray.Short.IIIa.movingZ ν s < 1 := by
    have e : ν * UnforcedLeray.Short.IIIa.movingZ ν s = ν * s / (1 + ν * s) := by
      unfold UnforcedLeray.Short.IIIa.movingZ UnforcedLeray.Short.IIIa.clockA
      ring
    rw [e, div_lt_one hAs]
    linarith
  have ht_age : UnforcedLeray.Short.IIIa.ageOfZ ν (UnforcedLeray.Short.IIIa.movingZ ν t) = t :=
    ageOfZ_movingZ_aux ν t hAt
  have hs_age : UnforcedLeray.Short.IIIa.ageOfZ ν (UnforcedLeray.Short.IIIa.movingZ ν s) = s :=
    ageOfZ_movingZ_aux ν s hAs
  set zs := UnforcedLeray.Short.IIIa.movingZ ν s with hzs_def
  set zt := UnforcedLeray.Short.IIIa.movingZ ν t with hzt_def
  have hz_lt_zs : zs - ζ < zs := by linarith
  have hz_gt_zt : zt < zs - ζ := by linarith
  have hνz : ν * (zs - ζ) < 1 := by nlinarith [mul_pos hν hζ0]
  unfold UnforcedLeray.Short.IIIa.revAge
  constructor
  · have h := ageOfZ_mono_aux ν zt (zs - ζ) hν hz_gt_zt hνz
    rw [ht_age] at h
    exact h
  · have h := ageOfZ_mono_aux ν (zs - ζ) zs hν hz_lt_zs hzs
    rw [hs_age] at h
    exact h

end UnforcedLeray.Short.IIIa.E0
