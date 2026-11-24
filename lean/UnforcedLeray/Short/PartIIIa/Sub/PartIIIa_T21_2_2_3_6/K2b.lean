import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K2a

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace K2bAux

open UnforcedLeray K2aAux

/-- Profile `η ↦ η · bump(η)`; its derivative equals `1` on `|η| ≤ |R|`. -/
def gR (R : ℝ) : ℝ → ℝ := fun η => η * bumpR R η

def psiS (d R : ℝ) : ℝ × ℝ → ℝ := fun y => Real.sin (2 * Real.pi * y.1 / d) * bumpR R y.2
def psiC (d R : ℝ) : ℝ × ℝ → ℝ := fun y => Real.cos (2 * Real.pi * y.1 / d) * bumpR R y.2
def psiS1 (d R : ℝ) : ℝ × ℝ → ℝ := fun y => Real.sin (2 * Real.pi * y.1 / d) * gR R y.2
def psiC1 (d R : ℝ) : ℝ × ℝ → ℝ := fun y => Real.cos (2 * Real.pi * y.1 / d) * gR R y.2

theorem hasDerivAt_sin_q (d q : ℝ) :
    HasDerivAt (fun q : ℝ => Real.sin (2 * Real.pi * q / d))
      (Real.cos (2 * Real.pi * q / d) * (2 * Real.pi / d)) q := by
  have h1 : HasDerivAt (fun q : ℝ => 2 * Real.pi * q / d) (2 * Real.pi / d) q := by
    simpa using ((hasDerivAt_id q).const_mul (2 * Real.pi)).div_const d
  exact h1.sin

theorem hasDerivAt_cos_q (d q : ℝ) :
    HasDerivAt (fun q : ℝ => Real.cos (2 * Real.pi * q / d))
      (-Real.sin (2 * Real.pi * q / d) * (2 * Real.pi / d)) q := by
  have h1 : HasDerivAt (fun q : ℝ => 2 * Real.pi * q / d) (2 * Real.pi / d) q := by
    simpa using ((hasDerivAt_id q).const_mul (2 * Real.pi)).div_const d
  exact h1.cos

theorem contDiff_gR (R : ℝ) : ContDiff ℝ ∞ (gR R) :=
  contDiff_id.mul (bumpR R).contDiff

theorem gR_zero (R : ℝ) (η : ℝ) (hη : (bumpR R).rOut < |η|) : gR R η = 0 := by
  show η * bumpR R η = 0
  rw [(bumpR R).zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hη.le), mul_zero]

theorem bumpR_zero (R : ℝ) (η : ℝ) (hη : (bumpR R).rOut < |η|) : bumpR R η = 0 :=
  (bumpR R).zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hη.le)

theorem deriv_gR (R η : ℝ) (hη : |η| ≤ |R|) : deriv (gR R) η = 1 := by
  have hev : (⇑(bumpR R)) =ᶠ[𝓝 η] fun _ => (1 : ℝ) := by
    filter_upwards [Metric.ball_mem_nhds η (by norm_num : (0 : ℝ) < 1 / 2)] with y hy
    apply (bumpR R).one_of_mem_closedBall
    rw [Metric.mem_ball, Real.dist_eq] at hy
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    show |y| ≤ |R| + 1 / 2
    have h1 : |y| ≤ |y - η| + |η| := by
      have := abs_add_le (y - η) η
      rw [sub_add_cancel] at this
      exact this
    linarith
  have hd : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 η := hasDerivAt_const η 1
  have hχ : HasDerivAt (⇑(bumpR R)) 0 η := hd.congr_of_eventuallyEq hev
  have hmul := (hasDerivAt_id η).mul hχ
  have hbη : bumpR R η = 1 := by
    apply (bumpR R).one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    show |η| ≤ |R| + 1 / 2
    linarith
  have hgd : deriv (gR R) η = 1 * bumpR R η + id η * 0 := hmul.deriv
  rw [hgd, hbη]
  simp

theorem pd0_prod (h g : ℝ → ℝ) (hh : Differentiable ℝ h) (hg : Differentiable ℝ g)
    (x : ℝ × ℝ) :
    UnforcedLeray.B0579.pd 0 (fun y => h y.1 * g y.2) x = deriv h x.1 * g x.2 := by
  have hφ : Differentiable ℝ (fun y : ℝ × ℝ => h y.1 * g y.2) :=
    (hh.comp differentiable_fst).mul (hg.comp differentiable_snd)
  have hγ : HasDerivAt (fun t : ℝ => ((x.1 + t, x.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_add x.1).prodMk (hasDerivAt_const (0 : ℝ) x.2)
  have h1 := HasFDerivAt.comp_hasDerivAt_of_eq (hl := (hφ x).hasFDerivAt) (hf := hγ)
    (hy := by simp)
  have hd : HasDerivAt h (deriv h x.1) (x.1 + 0) := by
    rw [add_zero]
    exact (hh x.1).hasDerivAt
  have hc := (hasDerivAt_id (0 : ℝ)).const_add x.1
  have hA := (hd.comp (0 : ℝ) hc)
  rw [mul_one] at hA
  have key := h1.unique (hA.mul_const (g x.2))
  show fderiv ℝ (fun y : ℝ × ℝ => h y.1 * g y.2) x (1, 0) = _
  exact key

theorem pd1_prod (h g : ℝ → ℝ) (hh : Differentiable ℝ h) (hg : Differentiable ℝ g)
    (x : ℝ × ℝ) :
    UnforcedLeray.B0579.pd 1 (fun y => h y.1 * g y.2) x = h x.1 * deriv g x.2 := by
  have hφ : Differentiable ℝ (fun y : ℝ × ℝ => h y.1 * g y.2) :=
    (hh.comp differentiable_fst).mul (hg.comp differentiable_snd)
  have hγ : HasDerivAt (fun t : ℝ => ((x.1, x.2 + t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) 0 :=
    (hasDerivAt_const (0 : ℝ) x.1).prodMk ((hasDerivAt_id (0 : ℝ)).const_add x.2)
  have h1 := HasFDerivAt.comp_hasDerivAt_of_eq (hl := (hφ x).hasFDerivAt) (hf := hγ)
    (hy := by simp)
  have hd : HasDerivAt g (deriv g x.2) (x.2 + 0) := by
    rw [add_zero]
    exact (hg x.2).hasDerivAt
  have hc := (hasDerivAt_id (0 : ℝ)).const_add x.2
  have hA := (hd.comp (0 : ℝ) hc)
  rw [mul_one] at hA
  have key := h1.unique ((hA.const_mul (h x.1)))
  show fderiv ℝ (fun y : ℝ × ℝ => h y.1 * g y.2) x (0, 1) = _
  exact key

theorem pd0_psiS (d R : ℝ) (x : ℝ × ℝ) :
    UnforcedLeray.B0579.pd 0 (psiS d R) x =
      Real.cos (2 * Real.pi * x.1 / d) * (2 * Real.pi / d) * bumpR R x.2 := by
  have hh : Differentiable ℝ (fun q : ℝ => Real.sin (2 * Real.pi * q / d)) :=
    fun q => (hasDerivAt_sin_q d q).differentiableAt
  have hcd : ContDiff ℝ ∞ (bumpR R) := (bumpR R).contDiff
  have hg : Differentiable ℝ (bumpR R) := hcd.differentiable (by simp)
  have e := pd0_prod (fun q : ℝ => Real.sin (2 * Real.pi * q / d)) (bumpR R) hh hg x
  rw [(hasDerivAt_sin_q d x.1).deriv] at e
  exact e

theorem pd0_psiC (d R : ℝ) (x : ℝ × ℝ) :
    UnforcedLeray.B0579.pd 0 (psiC d R) x =
      -Real.sin (2 * Real.pi * x.1 / d) * (2 * Real.pi / d) * bumpR R x.2 := by
  have hh : Differentiable ℝ (fun q : ℝ => Real.cos (2 * Real.pi * q / d)) :=
    fun q => (hasDerivAt_cos_q d q).differentiableAt
  have hcd : ContDiff ℝ ∞ (bumpR R) := (bumpR R).contDiff
  have hg : Differentiable ℝ (bumpR R) := hcd.differentiable (by simp)
  have e := pd0_prod (fun q : ℝ => Real.cos (2 * Real.pi * q / d)) (bumpR R) hh hg x
  rw [(hasDerivAt_cos_q d x.1).deriv] at e
  exact e

theorem pd1_psiS1 (d R : ℝ) (x : ℝ × ℝ) (hx : |x.2| ≤ |R|) :
    UnforcedLeray.B0579.pd 1 (psiS1 d R) x = Real.sin (2 * Real.pi * x.1 / d) := by
  have hh : Differentiable ℝ (fun q : ℝ => Real.sin (2 * Real.pi * q / d)) :=
    fun q => (hasDerivAt_sin_q d q).differentiableAt
  have hg : Differentiable ℝ (gR R) :=
    (contDiff_gR R).differentiable (by simp)
  have e := pd1_prod (fun q : ℝ => Real.sin (2 * Real.pi * q / d)) (gR R) hh hg x
  rw [deriv_gR R x.2 hx, mul_one] at e
  exact e

theorem pd1_psiC1 (d R : ℝ) (x : ℝ × ℝ) (hx : |x.2| ≤ |R|) :
    UnforcedLeray.B0579.pd 1 (psiC1 d R) x = Real.cos (2 * Real.pi * x.1 / d) := by
  have hh : Differentiable ℝ (fun q : ℝ => Real.cos (2 * Real.pi * q / d)) :=
    fun q => (hasDerivAt_cos_q d q).differentiableAt
  have hg : Differentiable ℝ (gR R) :=
    (contDiff_gR R).differentiable (by simp)
  have e := pd1_prod (fun q : ℝ => Real.cos (2 * Real.pi * q / d)) (gR R) hh hg x
  rw [deriv_gR R x.2 hx, mul_one] at e
  exact e

theorem bump_ne_zero_band {d R : ℝ} {x : ℝ × ℝ}
    (hx : x ∈ UnforcedLeray.Short.IIIa.AdjE1.bandSet d R) : bumpR R x.2 ≠ 0 := by
  have hxR : |x.2| ≤ R := hx.2
  have hmem : x.2 ∈ Metric.ball (0 : ℝ) (bumpR R).rOut := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    have h1 : R ≤ |R| := le_abs_self R
    show |x.2| < |R| + 1
    linarith
  exact ((bumpR R).pos_of_mem_ball hmem).ne'

/-- On a measurable set where a continuous function `φ` does not vanish, a field whose product
with `φ` is integrable on the cell is a.e. strongly measurable. -/
theorem aesm_of_ne_zero' {d : ℝ} {f : ℝ × ℝ → ℂ} {φ : ℝ × ℝ → ℝ}
    (hφm : Measurable φ)
    (hint : IntegrableOn (fun x => f x * (φ x : ℂ)) (B0579.cell d))
    {S : Set (ℝ × ℝ)} (hSm : MeasurableSet S) (hS : S ⊆ B0579.cell d)
    (hne : ∀ x ∈ S, φ x ≠ 0) :
    AEStronglyMeasurable f (volume.restrict S) := by
  have h1 : AEStronglyMeasurable (fun x => f x * (φ x : ℂ)) (volume.restrict S) :=
    hint.aestronglyMeasurable.mono_set hS
  have hinv : Measurable (fun x => ((φ x : ℂ))⁻¹) :=
    (Complex.measurable_ofReal.comp hφm).inv
  have h2 : AEStronglyMeasurable (fun x => f x * (φ x : ℂ) * ((φ x : ℂ))⁻¹)
      (volume.restrict S) :=
    h1.mul hinv.aestronglyMeasurable
  refine h2.congr ?_
  refine ae_restrict_of_forall_mem hSm (fun x hx => ?_)
  have hc : (φ x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hne x hx)
  exact mul_inv_cancel_right₀ hc (f x)

/-- Two test profiles whose values do not vanish simultaneously give a.e. measurability on
the band. -/
theorem aesm_two {d R : ℝ} {f : ℝ × ℝ → ℂ} {φ1 φ2 : ℝ × ℝ → ℝ}
    (hc1 : Continuous φ1) (hc2 : Continuous φ2)
    (hint1 : IntegrableOn (fun x => f x * (φ1 x : ℂ)) (B0579.cell d))
    (hint2 : IntegrableOn (fun x => f x * (φ2 x : ℂ)) (B0579.cell d))
    (hcov : ∀ x ∈ UnforcedLeray.Short.IIIa.AdjE1.bandSet d R, φ1 x ≠ 0 ∨ φ2 x ≠ 0) :
    AEStronglyMeasurable f (volume.restrict (UnforcedLeray.Short.IIIa.AdjE1.bandSet d R)) := by
  have hcov' : UnforcedLeray.Short.IIIa.AdjE1.bandSet d R ⊆
      (UnforcedLeray.Short.IIIa.AdjE1.bandSet d R ∩ {x | φ1 x ≠ 0}) ∪
        (UnforcedLeray.Short.IIIa.AdjE1.bandSet d R ∩ {x | φ2 x ≠ 0}) := by
    intro x hx
    rcases hcov x hx with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have hm1 : MeasurableSet (UnforcedLeray.Short.IIIa.AdjE1.bandSet d R ∩ {x | φ1 x ≠ 0}) :=
    (bandSet_measurable d R).inter
      (hc1.measurable (measurableSet_singleton (0 : ℝ)).compl)
  have hm2 : MeasurableSet (UnforcedLeray.Short.IIIa.AdjE1.bandSet d R ∩ {x | φ2 x ≠ 0}) :=
    (bandSet_measurable d R).inter
      (hc2.measurable (measurableSet_singleton (0 : ℝ)).compl)
  have hS1 := aesm_of_ne_zero' hc1.measurable hint1 hm1 (fun x hx => hx.1.1) (fun x hx => hx.2)
  have hS2 := aesm_of_ne_zero' hc2.measurable hint2 hm2 (fun x hx => hx.1.1) (fun x hx => hx.2)
  exact AEStronglyMeasurable.mono_set hcov' (aestronglyMeasurable_union_iff.2 ⟨hS1, hS2⟩)

end K2bAux

open K2aAux K2bAux UnforcedLeray in
/-- **Leaf B** (SP 3052-3058): as `TestMeasF`, with integrability against `∂_j ψ`. -/
theorem testMeasDeriv : UnforcedLeray.Short.IIIa.AdjE1.TestMeasDeriv := by
  intro d j f hd hint R
  have hR'b : ∀ η, (bumpR R).rOut < |η| → bumpR R η = 0 := fun η hη => bumpR_zero R η hη
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hj with rfl | rfl
  · have hS : B0579.IsCylTest d (psiS d R) :=
      isCylTest_mul (fun q : ℝ => Real.sin (2 * Real.pi * q / d)) (contDiff_sin_q d)
        (sin_periodic hd) (bumpR R) (bumpR R).contDiff (bumpR R).rOut hR'b
    have hC : B0579.IsCylTest d (psiC d R) :=
      isCylTest_mul (fun q : ℝ => Real.cos (2 * Real.pi * q / d)) (contDiff_cos_q d)
        (cos_periodic hd) (bumpR R) (bumpR R).contDiff (bumpR R).rOut hR'b
    have hdiv : (2 * Real.pi / d) ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hd.ne'
    refine aesm_two (φ1 := B0579.pd 0 (psiS d R)) (φ2 := B0579.pd 0 (psiC d R))
      (hc1 := (hS.pd 0).continuous) (hc2 := (hC.pd 0).continuous)
      (hint1 := hint _ hS) (hint2 := hint _ hC) ?_
    intro x hx
    have hb := bump_ne_zero_band hx
    by_cases hc : Real.cos (2 * Real.pi * x.1 / d) = 0
    · right
      have hs : Real.sin (2 * Real.pi * x.1 / d) ≠ 0 := by
        intro hs
        have := Real.sin_sq_add_cos_sq (2 * Real.pi * x.1 / d)
        rw [hs, hc] at this
        norm_num at this
      show B0579.pd 0 (psiC d R) x ≠ 0
      rw [pd0_psiC d R x]
      exact mul_ne_zero (mul_ne_zero (neg_ne_zero.2 hs) hdiv) hb
    · left
      show B0579.pd 0 (psiS d R) x ≠ 0
      rw [pd0_psiS d R x]
      exact mul_ne_zero (mul_ne_zero hc hdiv) hb
  · have hgR0 : ∀ η, (bumpR R).rOut < |η| → gR R η = 0 := fun η hη => gR_zero R η hη
    have hC1 : B0579.IsCylTest d (psiC1 d R) :=
      isCylTest_mul (fun q : ℝ => Real.cos (2 * Real.pi * q / d)) (contDiff_cos_q d)
        (cos_periodic hd) (gR R) (contDiff_gR R) (bumpR R).rOut hgR0
    have hS1 : B0579.IsCylTest d (psiS1 d R) :=
      isCylTest_mul (fun q : ℝ => Real.sin (2 * Real.pi * q / d)) (contDiff_sin_q d)
        (sin_periodic hd) (gR R) (contDiff_gR R) (bumpR R).rOut hgR0
    refine aesm_two (φ1 := B0579.pd 1 (psiC1 d R)) (φ2 := B0579.pd 1 (psiS1 d R))
      (hc1 := (hC1.pd 1).continuous) (hc2 := (hS1.pd 1).continuous)
      (hint1 := hint _ hC1) (hint2 := hint _ hS1) ?_
    intro x hx
    have hxR : |x.2| ≤ |R| := le_trans (show |x.2| ≤ R from hx.2) (le_abs_self R)
    by_cases hc : Real.cos (2 * Real.pi * x.1 / d) = 0
    · right
      have hs : Real.sin (2 * Real.pi * x.1 / d) ≠ 0 := by
        intro hs
        have := Real.sin_sq_add_cos_sq (2 * Real.pi * x.1 / d)
        rw [hs, hc] at this
        norm_num at this
      show B0579.pd 1 (psiS1 d R) x ≠ 0
      rw [pd1_psiS1 d R x hxR]
      exact hs
    · left
      show B0579.pd 1 (psiC1 d R) x ≠ 0
      rw [pd1_psiC1 d R x hxR]
      exact hc

#print axioms testMeasDeriv
