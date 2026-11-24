import UnforcedLeray.Short.PartIIb.Sub.T12_7_4

/-!
# Part II-b, task `PartII-b:T12/7/4/4` (`DeqhpGaussInt`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1923-1927.

`deqhpGaussInt_of` proves `DeqhpGaussInt` from the single leaf `DeqhpPerGauss` (a nonnegative
`c`-periodic function with finite `L^r(avgμ c)` norm, `r > 1`, is integrable against `e^{-b|z|²}`).
The Gaussian envelope comparison and the passage from `g` to `‖g_i‖` are proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Leaf** (SP 1923-1927): `F ≥ 0` measurable, `c`-periodic in the first variable a.e., with
`‖F‖_{L^r(Cyl.avgμ c)} < ∞` for some `r > 1`. Then `F e^{-b(z₁²+z₂²)}` is integrable on the plane.
Proof: Hölder on each unit box gives `∫_{box} F ≤ C` uniformly (reduce the `q`-shift to the cell,
`redQ`/`qSh` in `Tasks/FlatCausal/DuhamelMeasurable/Periodic.lean`, `Tasks/FlatUnique/CellStream/HrBox.lean`);
the sup of the Gaussian over the box `[n,n+1]×[m,m+1]` is `≤ C' e^{-b'(|n|+|m|)²}`, summable over
`ℤ²`; conclude by `integrable_of_summable_norm_restrict`-type decomposition into unit boxes. -/
def DeqhpPerGauss : Prop :=
  ∀ (c r b : ℝ), 0 < c → 1 < r → 0 < b → ∀ F : ℝ × ℝ → ℝ, (∀ z, 0 ≤ F z) →
    AEStronglyMeasurable F volume → (∀ᵐ z : ℝ × ℝ ∂volume, F (z.1 + c, z.2) = F z) →
    eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) < ⊤ →
    Integrable (fun z : ℝ × ℝ => F z * Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2)))

lemma deqhp_envelope (a R : ℝ) (ha : 0 < a) (z : ℝ × ℝ) :
    Real.exp (-a * (max 0 (‖z‖ - R)) ^ 2) ≤
      Real.exp (a * R ^ 2) * Real.exp (-(a / 4) * (z.1 ^ 2 + z.2 ^ 2)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : (z.1 ^ 2 + z.2 ^ 2) ≤ 2 * ‖z‖ ^ 2 := by
    have a1 : |z.1| ≤ ‖z‖ := by
      have := norm_fst_le z; simpa [Real.norm_eq_abs] using this
    have a2 : |z.2| ≤ ‖z‖ := by
      have := norm_snd_le z; simpa [Real.norm_eq_abs] using this
    have b1 : z.1 ^ 2 ≤ ‖z‖ ^ 2 := by rw [← sq_abs z.1]; exact pow_le_pow_left₀ (abs_nonneg _) a1 2
    have b2 : z.2 ^ 2 ≤ ‖z‖ ^ 2 := by rw [← sq_abs z.2]; exact pow_le_pow_left₀ (abs_nonneg _) a2 2
    linarith
  have h2 : ‖z‖ ^ 2 / 2 - R ^ 2 ≤ (max 0 (‖z‖ - R)) ^ 2 := by
    have hn : 0 ≤ ‖z‖ := norm_nonneg z
    rcases le_total R ‖z‖ with h | h
    · rw [max_eq_right (by linarith)]; nlinarith [sq_nonneg (‖z‖ - 2 * R)]
    · rw [max_eq_left (by linarith)]; nlinarith
  nlinarith

theorem deqhpGaussInt_of (h : DeqhpPerGauss) : DeqhpGaussInt := by
  intro c r hc hr g hg i R a ha
  obtain ⟨hper, hmeas, hlp⟩ := hg
  set F : ℝ × ℝ → ℝ := fun z => ‖g z i‖ with hF
  have hgi : AEStronglyMeasurable (fun z => g z i) volume :=
    (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hmeas
  have hFm : AEStronglyMeasurable F volume := hgi.norm
  have hFp : ∀ᵐ z : ℝ × ℝ ∂volume, F (z.1 + c, z.2) = F z := by
    filter_upwards [hper] with z hz
    simp only [hF, hz]
  have hFl : eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) < ⊤ := by
    refine lt_of_le_of_lt ?_ hlp
    refine eLpNorm_mono_ae (Eventually.of_forall fun z => ?_)
    simp only [hF, norm_norm]
    exact PiLp.norm_apply_le (g z) i
  have hP := h c r (a / 4) hc hr (by positivity) F (fun z => norm_nonneg _) hFm hFp hFl
  refine (hP.const_mul (Real.exp (a * R ^ 2))).mono' ?_ ?_
  · exact hgi.norm.mul (by fun_prop : Continuous fun z : ℝ × ℝ =>
      Real.exp (-a * (max 0 (‖z‖ - R)) ^ 2)).aestronglyMeasurable
  · refine Eventually.of_forall fun z => ?_
    rw [norm_mul, norm_norm, Real.norm_of_nonneg (Real.exp_pos _).le]
    have := deqhp_envelope a R ha z
    have h0 : 0 ≤ ‖g z i‖ := norm_nonneg _
    calc ‖g z i‖ * Real.exp (-a * (max 0 (‖z‖ - R)) ^ 2)
        ≤ ‖g z i‖ * (Real.exp (a * R ^ 2) * Real.exp (-(a / 4) * (z.1 ^ 2 + z.2 ^ 2))) :=
          mul_le_mul_of_nonneg_left this h0
      _ = Real.exp (a * R ^ 2) * (F z * Real.exp (-(a / 4) * (z.1 ^ 2 + z.2 ^ 2))) := by
          simp only [hF]; ring

end UnforcedLeray.Short.IIb
