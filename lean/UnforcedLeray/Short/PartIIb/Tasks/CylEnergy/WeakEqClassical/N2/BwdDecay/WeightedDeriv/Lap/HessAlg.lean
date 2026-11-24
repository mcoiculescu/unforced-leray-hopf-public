import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_2

/-!


Source: `the November 2 reference manuscript` SP 2085-2105.
Pure real algebra for the Prop `HessAlg` (`Sub/PartIIb_T22_2_3_2_2_2.lean`).
With `ell = H00 + H11`, `G` the signed bracket of `L(Δφ)/(2 ell)`, `S = Σ H_kj²`,
`P = p0² + p1²`, the proof is the decomposition (a)-(f) of the task spec, split into
small lemmas so that each `nlinarith`/`linarith` runs in a small context.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem hessAlg_sq8 (t1 t2 t3 t4 t5 t6 t7 t8 : ℝ) :
    (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8) ^ 2 ≤
      8 * (t1 ^ 2 + t2 ^ 2 + t3 ^ 2 + t4 ^ 2 + t5 ^ 2 + t6 ^ 2 + t7 ^ 2 + t8 ^ 2) := by
  linarith [sq_nonneg (t1 - t2), sq_nonneg (t1 - t3), sq_nonneg (t1 - t4),
    sq_nonneg (t1 - t5), sq_nonneg (t1 - t6), sq_nonneg (t1 - t7), sq_nonneg (t1 - t8),
    sq_nonneg (t2 - t3), sq_nonneg (t2 - t4), sq_nonneg (t2 - t5), sq_nonneg (t2 - t6),
    sq_nonneg (t2 - t7), sq_nonneg (t2 - t8), sq_nonneg (t3 - t4), sq_nonneg (t3 - t5),
    sq_nonneg (t3 - t6), sq_nonneg (t3 - t7), sq_nonneg (t3 - t8), sq_nonneg (t4 - t5),
    sq_nonneg (t4 - t6), sq_nonneg (t4 - t7), sq_nonneg (t4 - t8), sq_nonneg (t5 - t6),
    sq_nonneg (t5 - t7), sq_nonneg (t5 - t8), sq_nonneg (t6 - t7), sq_nonneg (t6 - t8),
    sq_nonneg (t7 - t8)]

/-- (a): `2 ζ ℓ G ≥ -(ℓ² + G²)` for `0 ≤ ζ ≤ 1`. -/
theorem hessAlg_a (ζ ell G : ℝ) (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) :
    0 ≤ ζ * (2 * ell * G) + (ell ^ 2 + G ^ 2) := by
  nlinarith [mul_nonneg h0 (sq_nonneg (ell + G)),
    mul_nonneg (sub_nonneg.2 h1) (add_nonneg (sq_nonneg ell) (sq_nonneg G))]

/-- (b): `G² ≤ 16 V² P + 32 V² S`. -/
theorem hessAlg_G2 (V p0 p1 H00 H01 H10 H11 d00 d01 d10 d11 e00 e01 e10 e11 G : ℝ)
    (hG : G = (-(e00 * p0 + d00 * H00 + e01 * p1 + d01 * H01) - (d00 * H00 + d01 * H10)) +
        (-(e10 * p0 + d10 * H10 + e11 * p1 + d11 * H11) - (d10 * H01 + d11 * H11)))
    (he00 : |e00| ≤ V) (he01 : |e01| ≤ V) (he10 : |e10| ≤ V) (he11 : |e11| ≤ V)
    (hd00 : |d00| ≤ V) (hd01 : |d01| ≤ V) (hd10 : |d10| ≤ V) (hd11 : |d11| ≤ V) :
    G ^ 2 ≤ 16 * V ^ 2 * (p0 ^ 2 + p1 ^ 2) +
      32 * V ^ 2 * (H00 ^ 2 + H01 ^ 2 + H10 ^ 2 + H11 ^ 2) := by
  have key : ∀ x : ℝ, |x| ≤ V → x ^ 2 ≤ V ^ 2 :=
    fun x hx => sq_le_sq' (abs_le.mp hx).1 (abs_le.mp hx).2
  have hGe : G = -(e00 * p0 + e01 * p1 + e10 * p0 + e11 * p1 + 2 * d00 * H00 +
      d01 * (H01 + H10) + d10 * (H01 + H10) + 2 * d11 * H11) := by
    rw [hG]; ring
  have hGsq : G ^ 2 ≤ 8 * ((e00 * p0) ^ 2 + (e01 * p1) ^ 2 + (e10 * p0) ^ 2 +
      (e11 * p1) ^ 2 + (2 * d00 * H00) ^ 2 + (d01 * (H01 + H10)) ^ 2 +
      (d10 * (H01 + H10)) ^ 2 + (2 * d11 * H11) ^ 2) := by
    rw [hGe, neg_sq]
    exact hessAlg_sq8 _ _ _ _ _ _ _ _
  have q1 : (e00 * p0) ^ 2 ≤ V ^ 2 * p0 ^ 2 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right (key e00 he00) (sq_nonneg p0)
  have q2 : (e01 * p1) ^ 2 ≤ V ^ 2 * p1 ^ 2 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right (key e01 he01) (sq_nonneg p1)
  have q3 : (e10 * p0) ^ 2 ≤ V ^ 2 * p0 ^ 2 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right (key e10 he10) (sq_nonneg p0)
  have q4 : (e11 * p1) ^ 2 ≤ V ^ 2 * p1 ^ 2 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right (key e11 he11) (sq_nonneg p1)
  have q5 : (2 * d00 * H00) ^ 2 ≤ 4 * V ^ 2 * H00 ^ 2 := by
    have h := mul_le_mul_of_nonneg_right (key d00 hd00) (sq_nonneg H00)
    have e1 : (2 * d00 * H00) ^ 2 = 4 * (d00 ^ 2 * H00 ^ 2) := by ring
    have e2 : 4 * V ^ 2 * H00 ^ 2 = 4 * (V ^ 2 * H00 ^ 2) := by ring
    rw [e1, e2]; exact mul_le_mul_of_nonneg_left h (by norm_num)
  have q8 : (2 * d11 * H11) ^ 2 ≤ 4 * V ^ 2 * H11 ^ 2 := by
    have h := mul_le_mul_of_nonneg_right (key d11 hd11) (sq_nonneg H11)
    have e1 : (2 * d11 * H11) ^ 2 = 4 * (d11 ^ 2 * H11 ^ 2) := by ring
    have e2 : 4 * V ^ 2 * H11 ^ 2 = 4 * (V ^ 2 * H11 ^ 2) := by ring
    rw [e1, e2]; exact mul_le_mul_of_nonneg_left h (by norm_num)
  have q6 : (d01 * (H01 + H10)) ^ 2 ≤ 2 * V ^ 2 * (H01 ^ 2 + H10 ^ 2) := by
    have h := mul_le_mul_of_nonneg_right (key d01 hd01) (sq_nonneg (H01 + H10))
    have h2 := mul_nonneg (sq_nonneg V) (sq_nonneg (H01 - H10))
    have e1 : (d01 * (H01 + H10)) ^ 2 = d01 ^ 2 * (H01 + H10) ^ 2 := by ring
    have e2 : 2 * V ^ 2 * (H01 ^ 2 + H10 ^ 2) =
        V ^ 2 * (H01 + H10) ^ 2 + V ^ 2 * (H01 - H10) ^ 2 := by ring
    rw [e1, e2]; exact h.trans (le_add_of_nonneg_right h2)
  have q7 : (d10 * (H01 + H10)) ^ 2 ≤ 2 * V ^ 2 * (H01 ^ 2 + H10 ^ 2) := by
    have h := mul_le_mul_of_nonneg_right (key d10 hd10) (sq_nonneg (H01 + H10))
    have h2 := mul_nonneg (sq_nonneg V) (sq_nonneg (H01 - H10))
    have e1 : (d10 * (H01 + H10)) ^ 2 = d10 ^ 2 * (H01 + H10) ^ 2 := by ring
    have e2 : 2 * V ^ 2 * (H01 ^ 2 + H10 ^ 2) =
        V ^ 2 * (H01 + H10) ^ 2 + V ^ 2 * (H01 - H10) ^ 2 := by ring
    rw [e1, e2]; exact h.trans (le_add_of_nonneg_right h2)
  linarith [hGsq, q1, q2, q3, q4, q5, q6, q7, q8]

/-- (c): `ζ|g|² + 2 ℓ (z·g) + Cθ ℓ² ≥ 0`, from `|z|² ≤ Cθ ζ`. -/
theorem hessAlg_C (ζ ell g0 g1 z0 z1 Cθ : ℝ) (h0 : 0 ≤ ζ) (hCθ : 0 ≤ Cθ)
    (hZ : z0 ^ 2 + z1 ^ 2 ≤ Cθ * ζ) :
    0 ≤ ζ * (g0 ^ 2 + g1 ^ 2) + 2 * ell * (z0 * g0 + z1 * g1) + Cθ * ell ^ 2 := by
  rcases eq_or_lt_of_le h0 with h | hpos
  · subst h
    have hz0 : z0 ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg z1]) (sq_nonneg z0)
    have hz1 : z1 ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg z0]) (sq_nonneg z1)
    have hz0' : z0 = 0 := (pow_eq_zero_iff two_ne_zero).mp hz0
    have hz1' : z1 = 0 := (pow_eq_zero_iff two_ne_zero).mp hz1
    subst hz0' hz1'
    nlinarith [mul_nonneg hCθ (sq_nonneg ell)]
  · have hX : 0 ≤ ζ * (ζ * (g0 ^ 2 + g1 ^ 2) + 2 * ell * (z0 * g0 + z1 * g1) +
        Cθ * ell ^ 2) := by
      nlinarith [sq_nonneg (ζ * g0 + z0 * ell), sq_nonneg (ζ * g1 + z1 * ell),
        mul_nonneg (sq_nonneg ell) (sub_nonneg.2 hZ)]
    by_contra hneg
    have hlt := not_le.mp hneg
    have hm := mul_neg_of_pos_of_neg hpos hlt
    linarith

/-- (d): `ℓ² (ν lz + b·z) ≥ -ℓ² (ν Cθ + V (1 + Cθ))`. -/
theorem hessAlg_D (ν V Cθ ζ lz b0 b1 z0 z1 ell : ℝ) (hν : 0 < ν) (hV : 0 ≤ V)
    (hCθ : 0 ≤ Cθ) (hζ1 : ζ ≤ 1) (hZ : z0 ^ 2 + z1 ^ 2 ≤ Cθ * ζ) (hlz : |lz| ≤ Cθ)
    (hb0 : |b0| ≤ V) (hb1 : |b1| ≤ V) :
    0 ≤ ell ^ 2 * (ν * lz + (b0 * z0 + b1 * z1)) + ell ^ 2 * (ν * Cθ + V * (1 + Cθ)) := by
  have hh : 0 ≤ (1 + Cθ) / 2 := by linarith
  have hz2 : z0 ^ 2 ≤ ((1 + Cθ) / 2) ^ 2 := by
    nlinarith [sq_nonneg z1, sq_nonneg (1 - Cθ), mul_le_of_le_one_right hCθ hζ1]
  have hz2' : z1 ^ 2 ≤ ((1 + Cθ) / 2) ^ 2 := by
    nlinarith [sq_nonneg z0, sq_nonneg (1 - Cθ), mul_le_of_le_one_right hCθ hζ1]
  have hz0abs : |z0| ≤ (1 + Cθ) / 2 := abs_le.mpr (abs_le_of_sq_le_sq' hz2 hh)
  have hz1abs : |z1| ≤ (1 + Cθ) / 2 := abs_le.mpr (abs_le_of_sq_le_sq' hz2' hh)
  have hb0z0 : -(V * ((1 + Cθ) / 2)) ≤ b0 * z0 := by
    have h1 : |b0 * z0| ≤ V * ((1 + Cθ) / 2) := by
      rw [abs_mul]; exact mul_le_mul hb0 hz0abs (abs_nonneg _) hV
    linarith [neg_abs_le (b0 * z0)]
  have hb1z1 : -(V * ((1 + Cθ) / 2)) ≤ b1 * z1 := by
    have h1 : |b1 * z1| ≤ V * ((1 + Cθ) / 2) := by
      rw [abs_mul]; exact mul_le_mul hb1 hz1abs (abs_nonneg _) hV
    linarith [neg_abs_le (b1 * z1)]
  have hl : ν * (-Cθ) ≤ ν * lz := mul_le_mul_of_nonneg_left (abs_le.mp hlz).1 hν.le
  have hinner : -(ν * Cθ + V * (1 + Cθ)) ≤ ν * lz + (b0 * z0 + b1 * z1) := by
    linarith [hl, hb0z0, hb1z1]
  linarith [mul_le_mul_of_nonneg_left hinner (sq_nonneg ell)]

/-- (e): the `mu`-term is at least `mu (2 ν S - 4 V P)` (the `2νS` part is kept outside). -/
theorem hessAlg_Mu (V mu p0 p1 d00 d01 d10 d11 : ℝ) (hmu0 : 0 ≤ mu)
    (hd00 : |d00| ≤ V) (hd01 : |d01| ≤ V) (hd10 : |d10| ≤ V) (hd11 : |d11| ≤ V) :
    0 ≤ mu * ((2 * p0 * (-(d00 * p0 + d01 * p1)) + 2 * p1 * (-(d10 * p0 + d11 * p1))) +
      4 * V * (p0 ^ 2 + p1 ^ 2)) := by
  have hA0 : d00 * p0 ^ 2 ≤ V * p0 ^ 2 :=
    mul_le_mul_of_nonneg_right (abs_le.mp hd00).2 (sq_nonneg p0)
  have hA1 : d11 * p1 ^ 2 ≤ V * p1 ^ 2 :=
    mul_le_mul_of_nonneg_right (abs_le.mp hd11).2 (sq_nonneg p1)
  have hu1 : 0 ≤ 2 * V - (d01 + d10) := by
    linarith [(abs_le.mp hd01).2, (abs_le.mp hd10).2]
  have hu2 : 0 ≤ 2 * V + (d01 + d10) := by
    linarith [(abs_le.mp hd01).1, (abs_le.mp hd10).1]
  have hA2 : (d01 + d10) * (p0 * p1) ≤ V * (p0 ^ 2 + p1 ^ 2) := by
    nlinarith [mul_nonneg hu1 (sq_nonneg (p0 + p1)), mul_nonneg hu2 (sq_nonneg (p0 - p1))]
  have hMuX : 0 ≤ (2 * p0 * (-(d00 * p0 + d01 * p1)) + 2 * p1 * (-(d10 * p0 + d11 * p1))) +
      4 * V * (p0 ^ 2 + p1 ^ 2) := by
    linarith [hA0, hA1, hA2]
  exact mul_nonneg hmu0 hMuX

/-- `mu ≥ 0` from the coefficient hypothesis. -/
theorem hessAlg_mu0 (ν V Cθ mu : ℝ) (hν : 0 < ν) (hV : 0 ≤ V) (hCθ : 0 ≤ Cθ)
    (hmu : 32 * V ^ 2 + 2 + 6 * ν * Cθ + 2 * V + 2 * V * Cθ ≤ 2 * ν * mu) : 0 ≤ mu := by
  by_contra hneg
  have hlt := not_le.mp hneg
  nlinarith [mul_pos hν (neg_pos.2 hlt), sq_nonneg V, mul_nonneg hν.le hCθ,
    mul_nonneg hV hCθ]

/-- (f): `ℓ² ≤ 2 S`. -/
theorem hessAlg_l2 (H00 H01 H10 H11 : ℝ) :
    (H00 + H11) ^ 2 ≤ 2 * (H00 ^ 2 + H01 ^ 2 + H10 ^ 2 + H11 ^ 2) := by
  nlinarith [sq_nonneg (H00 - H11), sq_nonneg H01, sq_nonneg H10]

set_option maxHeartbeats 1000000 in
theorem hessAlg : UnforcedLeray.Short.IIb.HessAlg := by
  intro ν V Cθ mu kap ζ z0 z1 lz b0 b1 d00 d01 d10 d11 e00 e01 e10 e11 p0 p1 H00 H01 H10 H11
    g0 g1 hν hV hCθ hζ0 hζ1 hZ hlz hb0 hb1 hd00 hd01 hd10 hd11 he00 he01 he10 he11 hmu hkap
  obtain ⟨G, hG⟩ : ∃ G : ℝ,
      G = (-(e00 * p0 + d00 * H00 + e01 * p1 + d01 * H01) - (d00 * H00 + d01 * H10)) +
        (-(e10 * p0 + d10 * H10 + e11 * p1 + d11 * H11) - (d10 * H01 + d11 * H11)) :=
    ⟨_, rfl⟩
  obtain ⟨ell, hell⟩ : ∃ ell : ℝ, ell = H00 + H11 := ⟨_, rfl⟩
  have hA := hessAlg_a ζ ell G hζ0 hζ1
  have hGb := hessAlg_G2 V p0 p1 H00 H01 H10 H11 d00 d01 d10 d11 e00 e01 e10 e11 G hG
    he00 he01 he10 he11 hd00 hd01 hd10 hd11
  have hC := hessAlg_C ζ ell g0 g1 z0 z1 Cθ hζ0 hCθ hZ
  have hX2 : 0 ≤ 2 * ν * (ζ * (g0 ^ 2 + g1 ^ 2) + 2 * ell * (z0 * g0 + z1 * g1) +
      Cθ * ell ^ 2) := mul_nonneg (by linarith only [hν]) hC
  have hD := hessAlg_D ν V Cθ ζ lz b0 b1 z0 z1 ell hν hV hCθ hζ1 hZ hlz hb0 hb1
  have hmu0 := hessAlg_mu0 ν V Cθ mu hν hV hCθ hmu
  have hMu := hessAlg_Mu V mu p0 p1 d00 d01 d10 d11 hmu0 hd00 hd01 hd10 hd11
  have hl2 := hessAlg_l2 H00 H01 H10 H11
  have hcpos : 0 ≤ 1 + 3 * ν * Cθ + V + V * Cθ := by
    have h1 := mul_nonneg hν.le hCθ
    have h2 := mul_nonneg hV hCθ
    linarith only [h1, h2, hV]
  have hcS := mul_nonneg hcpos (sub_nonneg.2 hl2)
  have hSc : 0 ≤ (H00 ^ 2 + H01 ^ 2 + H10 ^ 2 + H11 ^ 2) *
      (2 * ν * mu - 32 * V ^ 2 - 2 * (1 + 3 * ν * Cθ + V + V * Cθ)) :=
    mul_nonneg (by positivity) (by linarith only [hmu])
  have hPc : 0 ≤ (p0 ^ 2 + p1 ^ 2) * (2 * ν * kap - 16 * V ^ 2 - 4 * V * mu) :=
    mul_nonneg (by positivity) (by linarith only [hkap])
  subst hell
  subst hG
  linarith only [hA, hX2, hD, hMu, hGb, hcS, hSc, hPc]

end UnforcedLeray.Short.IIb
