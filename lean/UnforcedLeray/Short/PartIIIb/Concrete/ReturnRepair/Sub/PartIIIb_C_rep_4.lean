import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThinProps
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateEarly

/-!
# `PartIII-b:C/rep/4`: `repair:age-error` reduced to four leaves

Source `the November 2 reference manuscript` 5301-5372 in the split form of the
closure 5607-5627, with the decomposition of the proof 5687-5689 ("The decomposition of
`S_farT + Y[T]` consists exactly of the early-source and late-output regions and the two stream
transitions").

## The split

`ageVel = (S_μ - S_N) + Y` (`Estimates.lean`).  Both summands contain the young-old rectangle
`χ_yS_μχ_o` with opposite signs: it lies in the far mask (5303-5306), and
`Y = -χ_yS_μχ_o + (𝒞_y-χ_y)W_μ + [D_{μ+1},𝒞_y]X₀` (4171, 4203-4214).  The rectangle is not small
(young receiver, old source with gain ratio up to `e^{γ/ν}`: about `e^{γ/(3ν)}` on thin sources,
`e^{γ/(22ν)}` on repair sources), and the source bounds only the regions that remain once the Ward
change cancels it.  The leaves therefore follow `ageVel_split` (`Org/YThinTrans.lean`):

`ageVel = lateEarlyOp + transOp`, `lateEarlyOp = S_far - χ_yS_μχ_o` (late output `(1-χ_y)F_far`
and early source `χ_yF_far(1-χ_o)`, 5303-5311), `transOp = Y + χ_yS_μχ_o` (the two stream
transitions `(𝒞_χ-χ)W_μ`, `[L_{free,μ+1},𝒞_χ](W_μ-W_{μ+1})`, 5312-5316).

Each is estimated on thin sources (margin `γ/15`) and on scaled repair sources (margin `19γ/66`)
by the table 5323-5340 with the gains `g(s)^{-1} ≤ e^{-4γ/(9ν)}`, `g(t) ≤ e^{3γ/(5ν)}` (5317-5321)
and the margins 5357-5365.  The four leaves (each with the `S`-degree `k₀` chosen before `b`,
`ω_b = k₀bγ/3`, 5607) are

* `AgeLateEarlyThin` (`Org/FarThinProps.lean`): `lateEarlyOp` on thin sources, `γ/15`;
* `AgeTransThin` (`Org/YThinTrans.lean`): `transOp` on thin sources, `γ/15`;
* `AgeLateEarlyRep` (`YRepStream/LateEarly.lean`): `lateEarlyOp` on scaled repair sources,
  `19γ/66`;
* `AgeTransRep` (`YRepStream/Trans.lean`): `transOp` on scaled repair sources, `19γ/66`.

They replace the earlier leaves `AgeFarThin`, `AgeYThin`, `AgeFarRep`, `AgeYRep` of this file,
which bounded `S_μ - S_N` and `Y` separately (each containing the rectangle) and are not source
statements.  `ageError_of` (proved) combines the four leaves into the parent target.
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Enlarge `ω_b` and replace the constant by its absolute value. -/
theorem age_lift {v x C P a c ωb ωb' ν : ℝ} (hν : 0 < ν) (hP : 0 ≤ P) (hx : 0 ≤ x)
    (hω : ωb ≤ ωb') (h : v ≤ C * P * Real.exp (-(a - ωb - c) / ν) * x) :
    v ≤ |C| * P * Real.exp (-(a - ωb' - c) / ν) * x :=
  h.trans (ef_mono hP (Real.exp_pos _).le
    (Real.exp_le_exp.2 (div_le_div_of_nonneg_right (by linarith) hν.le)) hx)

/-- Sum of two bounds with possibly different degrees `k₁, k₂ ≤ K` (`ν ≤ 1`). -/
theorem age_comb {a b ν E x C1 C2 Cb : ℝ} {k1 k2 K : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hk1 : k1 ≤ K) (hk2 : k2 ≤ K) (hE : 0 ≤ E) (hx : 0 ≤ x) (hC : |C1| + |C2| ≤ Cb)
    (ha : a ≤ C1 * ν⁻¹ ^ k1 * E * x) (hb : b ≤ C2 * ν⁻¹ ^ k2 * E * x) :
    a + b ≤ Cb * ν⁻¹ ^ K * E * x := by
  have h1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have p1 : ν⁻¹ ^ k1 ≤ ν⁻¹ ^ K := pow_le_pow_right₀ h1 hk1
  have p2 : ν⁻¹ ^ k2 ≤ ν⁻¹ ^ K := pow_le_pow_right₀ h1 hk2
  have pK : 0 ≤ ν⁻¹ ^ K := by positivity
  have q1 : C1 * ν⁻¹ ^ k1 ≤ |C1| * ν⁻¹ ^ K :=
    (mul_le_mul_of_nonneg_right (le_abs_self C1) (by positivity)).trans
      (mul_le_mul_of_nonneg_left p1 (abs_nonneg _))
  have q2 : C2 * ν⁻¹ ^ k2 ≤ |C2| * ν⁻¹ ^ K :=
    (mul_le_mul_of_nonneg_right (le_abs_self C2) (by positivity)).trans
      (mul_le_mul_of_nonneg_left p2 (abs_nonneg _))
  have hEx : 0 ≤ E * x := mul_nonneg hE hx
  calc a + b ≤ C1 * ν⁻¹ ^ k1 * E * x + C2 * ν⁻¹ ^ k2 * E * x := add_le_add ha hb
    _ = (C1 * ν⁻¹ ^ k1 + C2 * ν⁻¹ ^ k2) * (E * x) := by ring
    _ ≤ (|C1| * ν⁻¹ ^ K + |C2| * ν⁻¹ ^ K) * (E * x) :=
        mul_le_mul_of_nonneg_right (add_le_add q1 q2) hEx
    _ = (|C1| + |C2|) * ν⁻¹ ^ K * (E * x) := by ring
    _ ≤ Cb * ν⁻¹ ^ K * (E * x) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC pK) hEx
    _ = Cb * ν⁻¹ ^ K * E * x := by ring

/-- **`repair:age-error` from the four leaves** (source 5301-5372, closure 5607-5627, 5687-5689):
`ageVel = lateEarlyOp + transOp` (`ageVel_split`), each part bounded on thin sources (margin
`γ/15`) and on scaled repair sources (margin `19γ/66`). -/
theorem ageError_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (h1 : AgeLateEarlyThin Pl σ₀ mZ dm dp) (h2 : AgeTransThin Pl σ₀ mZ dm dp)
    (h3 : AgeLateEarlyRep Pl σ₀ mZ dm dp) (h4 : AgeTransRep Pl σ₀ mZ dm dp) :
    ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
      D.AgeError ((k₀ : ℝ) * D.K.b * (gRate D.Pl / 3)) := by
  obtain ⟨k1, H1⟩ := h1
  obtain ⟨k2, H2⟩ := h2
  obtain ⟨k3, H3⟩ := h3
  obtain ⟨k4, H4⟩ := h4
  refine ⟨max (max k1 k2) (max k3 k4), fun D hPl hσ hmZ hst => ?_⟩
  have hb := hst.b_pos
  have hg := hst.gamma_pos
  have hmono : ∀ j : ℕ, j ≤ max (max k1 k2) (max k3 k4) →
      (j : ℝ) * D.K.b * (gRate D.Pl / 3) ≤
        ((max (max k1 k2) (max k3 k4) : ℕ) : ℝ) * D.K.b * (gRate D.Pl / 3) := by
    intro j hj
    have : (j : ℝ) ≤ ((max (max k1 k2) (max k3 k4) : ℕ) : ℝ) := by exact_mod_cast hj
    have hbg : 0 ≤ D.K.b * (gRate D.Pl / 3) := by positivity
    nlinarith
  obtain ⟨C1, j1, e1⟩ := H1 D hPl hσ hmZ hst
  obtain ⟨C2, j2, e2⟩ := H2 D hPl hσ hmZ hst
  obtain ⟨C3, j3, e3⟩ := H3 D hPl hσ hmZ hst
  obtain ⟨C4, j4, e4⟩ := H4 D hPl hσ hmZ hst
  have hν1 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds one_pos)
  set kk := max (max k1 k2) (max k3 k4) with hkk
  refine ⟨|C1| + |C2| + |C3| + |C4|, max (max j1 j2) (max j3 j4), ?_⟩
  filter_upwards [e1, e2, e3, e4, hν1] with n m1 m2 m3 m4 hν z hz
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν1' : (D.level n).ν ≤ 1 := hν
  have hP : ∀ j : ℕ, 0 ≤ (D.level n).ν⁻¹ ^ j := fun j => by positivity
  have eadd : ∀ x : LStr D.Pl D.K (D.level n),
      multOp D.Pl D.K (D.level n) (ageVel D.Pl D.K (D.level n) (D.mu n z) x) =
        multOp D.Pl D.K (D.level n)
          (lateEarlyOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY x) +
        multOp D.Pl D.K (D.level n) (transOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY x) := by
    intro x
    rw [ageVel_split D.Pl D.K (D.level n) (D.mu n z) hst.chiY, add_apply, map_add]
  have hj1 : j1 ≤ max (max j1 j2) (max j3 j4) := le_trans (le_max_left _ _) (le_max_left _ _)
  have hj2 : j2 ≤ max (max j1 j2) (max j3 j4) := le_trans (le_max_right _ _) (le_max_left _ _)
  have hj3 : j3 ≤ max (max j1 j2) (max j3 j4) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hj4 : j4 ≤ max (max j1 j2) (max j3 j4) := le_trans (le_max_right _ _) (le_max_right _ _)
  have g1 : k1 ≤ kk := le_trans (le_max_left _ _) (le_max_left _ _)
  have g2 : k2 ≤ kk := le_trans (le_max_right _ _) (le_max_left _ _)
  have g3 : k3 ≤ kk := le_trans (le_max_left _ _) (le_max_right _ _)
  have g4 : k4 ≤ kk := le_trans (le_max_right _ _) (le_max_right _ _)
  have habs : |C1| + |C2| ≤ |C1| + |C2| + |C3| + |C4| := by
    have := abs_nonneg C3; have := abs_nonneg C4; linarith
  have habs' : |C3| + |C4| ≤ |C1| + |C2| + |C3| + |C4| := by
    have := abs_nonneg C1; have := abs_nonneg C2; linarith
  have habs2 : |(|C1|)| + |(|C2|)| ≤ |C1| + |C2| + |C3| + |C4| := by
    simpa only [abs_abs] using habs
  have habs3 : |(|C3|)| + |(|C4|)| ≤ |C1| + |C2| + |C3| + |C4| := by
    simpa only [abs_abs] using habs'
  refine ⟨fun T => ?_, fun w => ?_⟩
  · rw [eadd]
    refine (norm_add_le _ _).trans ?_
    have a1 := age_lift (a := gRate D.Pl / 15) (c := 3 * D.K.m0 / 2) hνp (hP j1)
      (norm_nonneg T) (hmono k1 g1) (m1 z hz T)
    have a2 := age_lift (a := gRate D.Pl / 15) (c := 3 * D.K.m0 / 2) hνp (hP j2)
      (norm_nonneg T) (hmono k2 g2) (m2 z hz T)
    exact age_comb hνp hν1' hj1 hj2 (Real.exp_pos _).le (norm_nonneg T) habs2 a1 a2
  · rw [eadd]
    refine (norm_add_le _ _).trans ?_
    have a1 := age_lift (a := 19 * gRate D.Pl / 66) (c := 3 * D.K.m0 / 2) hνp (hP j3)
      (norm_nonneg w) (hmono k3 g3) (m3 z hz w)
    have a2 := age_lift (a := 19 * gRate D.Pl / 66) (c := 3 * D.K.m0 / 2) hνp (hP j4)
      (norm_nonneg w) (hmono k4 g4) (m4 z hz w)
    exact age_comb hνp hν1' hj3 hj4 (Real.exp_pos _).le (norm_nonneg w) habs3 a1 a2

end UnforcedLeray.Short.PartIIIb.Concrete
