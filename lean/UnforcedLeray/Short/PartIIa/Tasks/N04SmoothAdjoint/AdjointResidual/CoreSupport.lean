import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_3_Org

/-!
# Support of axis-reaching core tests (`MeridCoreTestSupport`, leaf `PartII-a:N04/3/4`)

Source of record: `the November 2 reference manuscript`,
lines 3290-3295 (lift `U = a b`, `a = 1/r`, `s = r^-2`, `η = z/(ε r)`) and 1456-1466 (core fields
have bounded spatial support).

Proof outline. Take `R₀ ≥ 0` bounding the spatial support of the two Cartesian core fields. For a
profile point `p` with `s = p.1 > 0` and `u p ≠ 0`, the chart point `y = (x, τ)` with
`x = (s^{-1/2}, 0, ε η s^{-1/2})` and `τ = 2εq + log s` is sent to `p` by `B0220.chart`. There
`|x|² = s⁻¹ (1 + ε² η²)` and the lift is `liftA x • frame x (b p)` with `liftA x ≠ 0` and `frame x`
isometric. So a nonzero real or imaginary part of `u p` forces `|x| ≤ R₀`, which gives
`s⁻¹ ≤ R₀²` and `ε² η² ≤ R₀² s`; the constant `R = max (max (R₀²) (R₀/ε)) 1` works.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220
open UnforcedLeray.B0223

/-- A complex meridional value with vanishing real and imaginary meridional parts is zero. -/
theorem core_reMerid_imMerid_ne (u : Profile → MeridC) (p : Profile) (hu : u p ≠ 0) :
    reMerid u p ≠ 0 ∨ imMerid u p ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  apply hu
  ext i
  have a1 : (u p i).re = 0 := by
    have h := congrArg (fun w : Merid => w i) h1
    simpa [reMerid, UnforcedLeray.Short.PartIIIb.NearInst.Masked.merReL_apply] using h
  have a2 : (u p i).im = 0 := by
    have h := congrArg (fun w : Merid => w i) h2
    simpa [imMerid, UnforcedLeray.Short.PartIIIb.NearInst.Masked.merReL_apply] using h
  apply Complex.ext <;> simp [a1, a2]

/-- Support of core tests (leaf `PartII-a:N04/3/4`). -/
theorem meridCoreTestSupport : MeridCoreTestSupport := by
  unfold MeridCoreTestSupport
  intro ε c hε u hu
  obtain ⟨V1, hV1, hV1eq⟩ := hu.re_core
  obtain ⟨V2, hV2, hV2eq⟩ := hu.im_core
  obtain ⟨R1, hR1⟩ := hV1.bounded
  obtain ⟨R2, hR2⟩ := hV2.bounded
  obtain ⟨R0, hR0, hR1', hR2'⟩ : ∃ R0 : ℝ, 0 ≤ R0 ∧
      (∀ y : Space × ℝ, R0 < ‖y.1‖ → V1 y = 0) ∧ (∀ y : Space × ℝ, R0 < ‖y.1‖ → V2 y = 0) :=
    ⟨max (max R1 R2) 0, le_max_right _ _,
      fun y hy => hR1 y (lt_of_le_of_lt (le_trans (le_max_left R1 R2) (le_max_left _ 0)) hy),
      fun y hy => hR2 y (lt_of_le_of_lt (le_trans (le_max_right R1 R2) (le_max_left _ 0)) hy)⟩
  obtain ⟨R, hRA, hRB, hRpos⟩ : ∃ R : ℝ, R0 ^ 2 ≤ R ∧ R0 / ε ≤ R ∧ 0 < R :=
    ⟨max (max (R0 ^ 2) (R0 / ε)) 1, le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), lt_of_lt_of_le one_pos (le_max_right _ _)⟩
  refine ⟨R, hRpos, ?_⟩
  intro p hp hup
  have hpinv : 0 < p.1⁻¹ := inv_pos.2 hp
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = √(p.1⁻¹) := ⟨_, rfl⟩
  have hr_pos : 0 < r := by rw [hr]; exact Real.sqrt_pos.2 hpinv
  have hr2 : r ^ 2 = p.1⁻¹ := by rw [hr]; exact Real.sq_sqrt hpinv.le
  have hlogr : Real.log r = -Real.log p.1 / 2 := by
    rw [hr, Real.log_sqrt hpinv.le, Real.log_inv]
  obtain ⟨x, hx⟩ : ∃ x : Space, x = WithLp.toLp 2 ![r, 0, ε * p.2.2 * r] := ⟨_, rfl⟩
  have hx0 : x 0 = r := by simp [hx]
  have hx1 : x 1 = 0 := by simp [hx]
  have hx2 : x 2 = ε * p.2.2 * r := by simp [hx]
  have hrad : radius x = r := by
    unfold radius
    rw [hx0, hx1]
    rw [show r ^ 2 + 0 ^ 2 = r ^ 2 by ring]
    exact Real.sqrt_sq hr_pos.le
  have hne : radius x ≠ 0 := by rw [hrad]; exact hr_pos.ne'
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = 2 * ε * p.2.1 + Real.log p.1 := ⟨_, rfl⟩
  have hchart : chart ε (x, τ) = p := by
    have h1 : ageS x = p.1 := by
      unfold ageS
      rw [hrad, hr2, inv_inv]
    have h2 : cellQ ε x τ = p.2.1 := by
      unfold cellQ
      rw [hrad, hlogr, hτ]
      field_simp
      ring
    have h3 : etaCoord ε x = p.2.2 := by
      unfold etaCoord
      rw [hrad, hx2]
      field_simp
    unfold chart
    rw [h1, h2, h3]
  -- norm of the chart point
  have hnx : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [Real.norm_eq_abs, sq_abs]
  have hnx' : ‖x‖ ^ 2 = p.1⁻¹ + ε ^ 2 * p.2.2 ^ 2 * p.1⁻¹ := by
    rw [hnx, hx0, hx1, hx2]
    linear_combination (1 + ε ^ 2 * p.2.2 ^ 2) * hr2
  -- a core field bounded by R0 which is nonzero at the chart point forces |x| ≤ R0
  have aux : ∀ (V : Space × ℝ → Space) (G : Profile → Merid),
      (∀ y : Space × ℝ, R0 < ‖y.1‖ → V y = 0) →
      (∀ y : Space × ℝ, radius y.1 ≠ 0 → V y = fieldU ε G y) →
      G p ≠ 0 → ‖x‖ ≤ R0 := by
    intro V G hVb hVe hG
    by_contra hcon
    push Not at hcon
    have h0 : V (x, τ) = 0 := hVb (x, τ) hcon
    have he : V (x, τ) = fieldU ε G (x, τ) := hVe (x, τ) hne
    rw [h0] at he
    unfold fieldU at he
    rw [hchart] at he
    have hc : liftA x ≠ 0 := by
      unfold liftA
      exact inv_ne_zero hne
    have hw : frame x (G p) = 0 := (smul_eq_zero.1 he.symm).resolve_left hc
    have hn := norm_frame hne (G p)
    rw [hw, norm_zero] at hn
    exact hG (norm_eq_zero.1 hn.symm)
  have hxR : ‖x‖ ≤ R0 := by
    rcases core_reMerid_imMerid_ne u p hup with h | h
    · exact aux V1 (reMerid u) hR1' hV1eq h
    · exact aux V2 (imMerid u) hR2' hV2eq h
  -- algebra on the profile point
  have hxR2 : ‖x‖ ^ 2 ≤ R0 ^ 2 := by nlinarith [norm_nonneg x]
  have hle : p.1⁻¹ + ε ^ 2 * p.2.2 ^ 2 * p.1⁻¹ ≤ R0 ^ 2 := by linarith
  have hA : p.1⁻¹ ≤ R0 ^ 2 := by
    have hB : 0 ≤ ε ^ 2 * p.2.2 ^ 2 * p.1⁻¹ := by positivity
    linarith
  have e1 : p.1 * (p.1⁻¹ + ε ^ 2 * p.2.2 ^ 2 * p.1⁻¹) = 1 + ε ^ 2 * p.2.2 ^ 2 := by
    have h := mul_inv_cancel₀ hp.ne'
    linear_combination (1 + ε ^ 2 * p.2.2 ^ 2) * h
  have hC : ε ^ 2 * p.2.2 ^ 2 ≤ R0 ^ 2 * p.1 := by
    have := mul_le_mul_of_nonneg_left hle hp.le
    nlinarith
  -- the two bounds
  have hgoal1 : R⁻¹ ≤ p.1 := by
    have h := inv_anti₀ hpinv (le_trans hA hRA)
    rwa [inv_inv] at h
  have hs0 : 0 ≤ Real.sqrt p.1 := Real.sqrt_nonneg _
  have hs2 : Real.sqrt p.1 ^ 2 = p.1 := Real.sq_sqrt hp.le
  have hsq : (ε * p.2.2) ^ 2 ≤ (R0 * Real.sqrt p.1) ^ 2 := by
    have e2 : (ε * p.2.2) ^ 2 = ε ^ 2 * p.2.2 ^ 2 := by ring
    have e3 : (R0 * Real.sqrt p.1) ^ 2 = R0 ^ 2 * p.1 := by
      rw [mul_pow, hs2]
    rw [e2, e3]
    exact hC
  have habs : |ε * p.2.2| ≤ R0 * Real.sqrt p.1 :=
    abs_le_of_sq_le_sq hsq (mul_nonneg hR0 hs0)
  have habs' : ε * |p.2.2| ≤ R0 * Real.sqrt p.1 := by
    rw [abs_mul, abs_of_pos hε] at habs
    exact habs
  have hR0R : R0 ≤ R * ε := (div_le_iff₀ hε).1 hRB
  have h5 : ε * |p.2.2| ≤ ε * (R * Real.sqrt p.1) := by
    have := mul_le_mul_of_nonneg_right hR0R hs0
    nlinarith
  have hgoal2 : |p.2.2| ≤ R * Real.sqrt p.1 := le_of_mul_le_mul_left h5 hε
  exact ⟨hgoal1, hgoal2⟩

end UnforcedLeray.Short.PartIIa
