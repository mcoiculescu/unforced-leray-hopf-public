import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_1_7_4

/-!
# `PartIII-a:T21/2/7/1/7/4/2`: measurability of weak cell derivatives (`locWeakMeas`)

Source: `the November 2 reference manuscript` lines 3052-3057.

`HasWeakCellDerivC d j χ g` only gives integrability of `χ * pd j ψ` for cylinder tests `ψ`
(not of `χ * ψ`). So measurability is obtained from tests whose `j`-derivative does not vanish:
on the open set `{pd j ψ ≠ 0}`, `χ = (χ * pd j ψ) * (pd j ψ)⁻¹` is a.e.-strongly measurable.
A countable family of translates of two explicit tests has derivatives whose nonvanishing sets
cover every point of the plane, and `aestronglyMeasurable_iUnion_iff` finishes.

* `j = 1` (`η`-derivative): tests `bump (η - r)`, `r ∈ ℚ`.
* `j = 0` (`q`-derivative): tests `cos(2π q/d) bump(η - r)` and `sin(2π q/d) bump(η - r)`,
  `r ∈ ℚ`; at each point one of `sin`, `cos` is nonzero.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace LocWeakMeasAux

/-- The plane `ℝ × ℝ` (the carrier of `B0579.Plane`). -/
abbrev Plane : Type := ℝ × ℝ

/-- A smooth bump: `1` on `|t| ≤ 1`, `0` for `|t| ≥ 2`. -/
def bump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

theorem bump_one {t : ℝ} (ht : |t| ≤ 1) : bump t = 1 := by
  apply bump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  exact ht

theorem bump_zero {t : ℝ} (ht : 2 ≤ |t|) : bump t = 0 := by
  apply bump.zero_of_le_dist
  rw [Real.dist_eq, sub_zero]
  exact ht

theorem bump_shift_contDiff (r : ℝ) : ContDiff ℝ ∞ (fun t : ℝ => bump (t - r)) :=
  bump.contDiff.comp (contDiff_id.sub contDiff_const)

theorem bump_contDiff : ContDiff ℝ ∞ bump := bump.contDiff

/-- Cylinder test built from a `q`-factor and a shifted `η`-bump. -/
theorem isCylTest_of_fst_mul {c : ℝ} {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hper : ∀ t, F (t + c) = F t) (r : ℝ) :
    B0579.IsCylTest c (fun x => F x.1 * bump (x.2 - r)) where
  smooth := (hF.comp contDiff_fst).mul ((bump_shift_contDiff r).comp contDiff_snd)
  periodic x := by
    show F (x.1 + c) * bump (x.2 - r) = F x.1 * bump (x.2 - r)
    rw [hper]
  band := ⟨|r| + 2, fun x hx => by
    have h2 : 2 ≤ |x.2 - r| := by
      have := abs_sub_abs_le_abs_sub x.2 r
      linarith
    show F x.1 * bump (x.2 - r) = 0
    rw [bump_zero h2, mul_zero]⟩

/-- Cylinder test depending on `η` only. -/
theorem isCylTest_bump (c r : ℝ) : B0579.IsCylTest c (fun x => bump (x.2 - r)) where
  smooth := (bump_shift_contDiff r).comp contDiff_snd
  periodic _ := rfl
  band := ⟨|r| + 2, fun x hx => by
    have h2 : 2 ≤ |x.2 - r| := by
      have := abs_sub_abs_le_abs_sub x.2 r
      linarith
    exact bump_zero h2⟩

def cosF (c : ℝ) : ℝ → ℝ := fun t => Real.cos (2 * Real.pi * t / c)

def sinF (c : ℝ) : ℝ → ℝ := fun t => Real.sin (2 * Real.pi * t / c)

theorem cosF_contDiff (c : ℝ) : ContDiff ℝ ∞ (cosF c) := by
  unfold cosF
  exact Real.contDiff_cos.comp ((contDiff_const.mul contDiff_id).div_const c)

theorem sinF_contDiff (c : ℝ) : ContDiff ℝ ∞ (sinF c) := by
  unfold sinF
  exact Real.contDiff_sin.comp ((contDiff_const.mul contDiff_id).div_const c)

theorem cosF_per {c : ℝ} (hc : c ≠ 0) (t : ℝ) : cosF c (t + c) = cosF c t := by
  unfold cosF
  rw [show 2 * Real.pi * (t + c) / c = 2 * Real.pi * t / c + 2 * Real.pi by
    field_simp]
  exact Real.cos_add_two_pi _

theorem sinF_per {c : ℝ} (hc : c ≠ 0) (t : ℝ) : sinF c (t + c) = sinF c t := by
  unfold sinF
  rw [show 2 * Real.pi * (t + c) / c = 2 * Real.pi * t / c + 2 * Real.pi by
    field_simp]
  exact Real.sin_add_two_pi _

theorem hasDerivAt_cosF (c t : ℝ) :
    HasDerivAt (cosF c) (-Real.sin (2 * Real.pi * t / c) * (2 * Real.pi * 1 / c)) t := by
  have h1 := ((hasDerivAt_id' t).const_mul (2 * Real.pi)).div_const c
  exact h1.cos

theorem hasDerivAt_sinF (c t : ℝ) :
    HasDerivAt (sinF c) (Real.cos (2 * Real.pi * t / c) * (2 * Real.pi * 1 / c)) t := by
  have h1 := ((hasDerivAt_id' t).const_mul (2 * Real.pi)).div_const c
  exact h1.sin

/-- The two families for the `q`-derivative. -/
def cosT (c r : ℝ) : Plane → ℝ := fun x => cosF c x.1 * bump (x.2 - r)

def sinT (c r : ℝ) : Plane → ℝ := fun x => sinF c x.1 * bump (x.2 - r)

/-- Index `ℚ ⊕ ℚ`: `inl r ↦ cosT c r`, `inr r ↦ sinT c r`. -/
def famP0 (c : ℝ) : ℚ ⊕ ℚ → Plane → ℝ :=
  Sum.elim (fun r : ℚ => cosT c r) (fun r : ℚ => sinT c r)

theorem cosT_isCylTest {c : ℝ} (hc : c ≠ 0) (r : ℝ) : B0579.IsCylTest c (cosT c r) :=
  isCylTest_of_fst_mul (cosF_contDiff c) (cosF_per hc) r

theorem sinT_isCylTest {c : ℝ} (hc : c ≠ 0) (r : ℝ) : B0579.IsCylTest c (sinT c r) :=
  isCylTest_of_fst_mul (sinF_contDiff c) (sinF_per hc) r

/-- Slice derivative in `q` determines `pd 0`. -/
theorem pd0_eq {ψ : Plane → ℝ} (hψ : Differentiable ℝ ψ) (x : Plane) {D : ℝ}
    (h : HasDerivAt (fun t => ψ (t, x.2)) D x.1) : B0579.pd 0 ψ x = D := by
  have hc : HasDerivAt (fun t : ℝ => ((t, x.2) : Plane)) ((1 : ℝ), (0 : ℝ)) x.1 :=
    (hasDerivAt_id' x.1).prodMk (hasDerivAt_const x.1 x.2)
  have h2 := (hψ (x.1, x.2)).hasFDerivAt.comp_hasDerivAt x.1 hc
  have hdir : B0579.dir 0 = ((1 : ℝ), (0 : ℝ)) := by simp [B0579.dir]
  have h3 : HasDerivAt (fun t => ψ (t, x.2)) (fderiv ℝ ψ (x.1, x.2) ((1 : ℝ), (0 : ℝ))) x.1 := h2
  unfold B0579.pd
  rw [hdir]
  exact h3.unique h

/-- Slice derivative in `η` determines `pd 1`. -/
theorem pd1_eq {ψ : Plane → ℝ} (hψ : Differentiable ℝ ψ) (x : Plane) {D : ℝ}
    (h : HasDerivAt (fun s => ψ (x.1, s)) D x.2) : B0579.pd 1 ψ x = D := by
  have hc : HasDerivAt (fun s : ℝ => ((x.1, s) : Plane)) ((0 : ℝ), (1 : ℝ)) x.2 :=
    (hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id' x.2)
  have h2 := (hψ (x.1, x.2)).hasFDerivAt.comp_hasDerivAt x.2 hc
  have hdir : B0579.dir 1 = ((0 : ℝ), (1 : ℝ)) := by simp [B0579.dir]
  have h3 : HasDerivAt (fun s => ψ (x.1, s)) (fderiv ℝ ψ (x.1, x.2) ((0 : ℝ), (1 : ℝ))) x.2 := h2
  unfold B0579.pd
  rw [hdir]
  exact h3.unique h

theorem exists_deriv_bump_ne : ∃ t0 : ℝ, deriv bump t0 ≠ 0 := by
  obtain ⟨t0, _, ht0⟩ := exists_deriv_eq_slope bump (show (0 : ℝ) < 3 by norm_num)
    bump_contDiff.continuous.continuousOn
    (bump_contDiff.differentiable (by simp)).differentiableOn
  refine ⟨t0, ?_⟩
  rw [ht0, bump_zero (t := 3) (by norm_num), bump_one (t := 0) (by simp)]
  norm_num

/-- Rational translates of the `η`-derivative nonvanishing set cover the line. -/
theorem exists_rat_deriv_ne (s : ℝ) : ∃ r : ℚ, deriv bump (s - (r : ℝ)) ≠ 0 := by
  obtain ⟨t0, ht0⟩ := exists_deriv_bump_ne
  have hcont : ContinuousAt (deriv bump) t0 :=
    (bump_contDiff.continuous_deriv (by simp)).continuousAt
  have hev : ∀ᶠ t in 𝓝 t0, deriv bump t ≠ 0 := hcont.eventually_ne ht0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show s - t0 - ε < s - t0 + ε by linarith)
  refine ⟨r, hball ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Localized measurability: where `p ≠ 0`, `χ` is a.e.-strongly measurable. -/
theorem meas_on_nonzero {c : ℝ} (χ : Plane → ℂ) {p : Plane → ℝ} (hp : Continuous p)
    (hA : AEStronglyMeasurable (fun x => χ x * (p x : ℂ)) (volume.restrict (B0579.cell c))) :
    AEStronglyMeasurable χ (volume.restrict ({x | p x ≠ 0} ∩ B0579.cell c)) := by
  have hU : MeasurableSet {x | p x ≠ 0} := (isOpen_ne_fun hp continuous_const).measurableSet
  have hinvm : Measurable (fun x => (((p x)⁻¹ : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp hp.measurable.inv
  have hF : AEStronglyMeasurable (fun x => χ x * (p x : ℂ) * (((p x)⁻¹ : ℝ) : ℂ))
      (volume.restrict (B0579.cell c)) := hA.mul hinvm.aestronglyMeasurable
  have hF' : AEStronglyMeasurable (fun x => χ x * (p x : ℂ) * (((p x)⁻¹ : ℝ) : ℂ))
      ((volume.restrict (B0579.cell c)).restrict {x | p x ≠ 0}) :=
    hF.mono_measure Measure.restrict_le_self
  have heq : (fun x => χ x * (p x : ℂ) * (((p x)⁻¹ : ℝ) : ℂ)) =ᵐ[
      (volume.restrict (B0579.cell c)).restrict {x | p x ≠ 0}] χ := by
    filter_upwards [ae_restrict_mem hU] with x hx
    have hx' : p x ≠ 0 := hx
    have hone : (p x : ℂ) * (((p x)⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hx', Complex.ofReal_one]
    show χ x * (p x : ℂ) * (((p x)⁻¹ : ℝ) : ℂ) = χ x
    rw [mul_assoc, hone, mul_one]
  have h2 := hF'.congr heq
  rw [Measure.restrict_restrict hU] at h2
  exact h2

end LocWeakMeasAux

open LocWeakMeasAux in
/-- Weak cell derivatives are a.e.-strongly measurable on the cell (SP 3052-3057). -/
theorem locWeakMeas : LocWeakMeas := by
  intro d hd j χ g hχ
  have hd0 : 0 < d := by linarith
  have hdne : d ≠ 0 := hd0.ne'
  have hloc : ∀ ψ : Plane → ℝ, B0579.IsCylTest d ψ →
      AEStronglyMeasurable χ (volume.restrict ({x | B0579.pd j ψ x ≠ 0} ∩ B0579.cell d)) :=
    fun ψ hψ => meas_on_nonzero χ (hψ.pd j).continuous
      (hχ.1 ψ hψ).1.aestronglyMeasurable
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hj with rfl | rfl
  · -- the `q`-derivative
    have hfam : ∀ p : ℚ ⊕ ℚ, B0579.IsCylTest d (famP0 d p) := by
      intro p
      cases p with
      | inl r => exact cosT_isCylTest hdne r
      | inr r => exact sinT_isCylTest hdne r
    have hcover : ∀ x : Plane, ∃ p : ℚ ⊕ ℚ, B0579.pd 0 (famP0 d p) x ≠ 0 := by
      intro x
      have hpi : (2 * Real.pi * 1 / d) ≠ 0 := by
        have := Real.pi_pos
        exact div_ne_zero (by positivity) hdne
      obtain ⟨r, h1, h2⟩ := exists_rat_btwn (show x.2 - 1 < x.2 + 1 by linarith)
      have hb : bump (x.2 - (r : ℝ)) = 1 := bump_one (by rw [abs_le]; constructor <;> linarith)
      by_cases hcos : Real.cos (2 * Real.pi * x.1 / d) = 0
      · have hsin : Real.sin (2 * Real.pi * x.1 / d) ≠ 0 := by
          intro h0
          have := Real.sin_sq_add_cos_sq (2 * Real.pi * x.1 / d)
          rw [h0, hcos] at this
          norm_num at this
        refine ⟨Sum.inl r, ?_⟩
        have hD : B0579.pd 0 (cosT d (r : ℝ)) x =
            (-Real.sin (2 * Real.pi * x.1 / d) * (2 * Real.pi * 1 / d)) * bump (x.2 - (r : ℝ)) := by
          apply pd0_eq (cosT_isCylTest hdne (r : ℝ)).differentiable x
          exact (hasDerivAt_cosF d x.1).mul_const (bump (x.2 - (r : ℝ)))
        show B0579.pd 0 (cosT d (r : ℝ)) x ≠ 0
        rw [hD, hb, mul_one]
        exact mul_ne_zero (neg_ne_zero.2 hsin) hpi
      · refine ⟨Sum.inr r, ?_⟩
        have hD : B0579.pd 0 (sinT d (r : ℝ)) x =
            (Real.cos (2 * Real.pi * x.1 / d) * (2 * Real.pi * 1 / d)) * bump (x.2 - (r : ℝ)) := by
          apply pd0_eq (sinT_isCylTest hdne (r : ℝ)).differentiable x
          exact (hasDerivAt_sinF d x.1).mul_const (bump (x.2 - (r : ℝ)))
        show B0579.pd 0 (sinT d (r : ℝ)) x ≠ 0
        rw [hD, hb, mul_one]
        exact mul_ne_zero hcos hpi
    have hall : ∀ p : ℚ ⊕ ℚ,
        AEStronglyMeasurable χ (volume.restrict ({x | B0579.pd 0 (famP0 d p) x ≠ 0} ∩ B0579.cell d)) :=
      fun p => hloc _ (hfam p)
    have hU : (⋃ p : ℚ ⊕ ℚ, ({x | B0579.pd 0 (famP0 d p) x ≠ 0} ∩ B0579.cell d)) = B0579.cell d := by
      ext x
      simp only [mem_iUnion, mem_inter_iff, mem_setOf_eq]
      constructor
      · rintro ⟨p, _, hx⟩
        exact hx
      · intro hx
        obtain ⟨p, hp⟩ := hcover x
        exact ⟨p, hp, hx⟩
    rw [← hU]
    exact aestronglyMeasurable_iUnion_iff.2 hall
  · -- the `η`-derivative
    have hfam : ∀ r : ℚ, B0579.IsCylTest d (fun x : Plane => bump (x.2 - (r : ℝ))) :=
      fun r => isCylTest_bump d r
    have hcover : ∀ x : Plane, ∃ r : ℚ, B0579.pd 1 (fun y : Plane => bump (y.2 - (r : ℝ))) x ≠ 0 := by
      intro x
      obtain ⟨r, hr⟩ := exists_rat_deriv_ne x.2
      refine ⟨r, ?_⟩
      have hD : B0579.pd 1 (fun y : Plane => bump (y.2 - (r : ℝ))) x = deriv bump (x.2 - (r : ℝ)) := by
        apply pd1_eq (isCylTest_bump d r).differentiable x
        exact (((bump_contDiff.differentiable (by simp)) (x.2 - r)).hasDerivAt).comp_sub_const x.2 r
      rw [hD]
      exact hr
    have hall : ∀ r : ℚ,
        AEStronglyMeasurable χ (volume.restrict
          ({x | B0579.pd 1 (fun y : Plane => bump (y.2 - (r : ℝ))) x ≠ 0} ∩ B0579.cell d)) :=
      fun r => hloc _ (hfam r)
    have hU : (⋃ r : ℚ, ({x | B0579.pd 1 (fun y : Plane => bump (y.2 - (r : ℝ))) x ≠ 0} ∩
        B0579.cell d)) = B0579.cell d := by
      ext x
      simp only [mem_iUnion, mem_inter_iff, mem_setOf_eq]
      constructor
      · rintro ⟨r, _, hx⟩
        exact hx
      · intro hx
        obtain ⟨r, hr⟩ := hcover x
        exact ⟨r, hr, hx⟩
    rw [← hU]
    exact aestronglyMeasurable_iUnion_iff.2 hall

end UnforcedLeray.Short.IIIa
