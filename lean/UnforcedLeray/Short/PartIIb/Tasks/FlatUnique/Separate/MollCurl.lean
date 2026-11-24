import UnforcedLeray.Short.PartIIb.Sub.T11_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.CutLocInt
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.MollSliceDeriv

/-!
# Leaf `MollCurl` (`PartII-b:T11/6/12`): the mollified slices are planar curl free

Proves `MollCurl` (defined in `Sub/T11_6.lean`). By `mollSliceDeriv` the curl is
`∫ ρ₁(s - x₁) [fd ρ₂(z - x₂) (0,1) · b₀ - fd ρ₂(z - x₂) (1,0) · b₁]` with the cut-off replaced by
`b` on the support `x₁ > δ`. With the time test `θ(t) = ρ₁(s - t)` and the planar test
`ψ(w) = ρ₂(z - w)` this integrand is the negative of `streamPair b θ ψ`, whose integral vanishes
by `FullOrth`. Source of record: `the November 2 reference manuscript`, SP 2618.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- An admissible planar mollifier vanishes outside the sup-norm ball of radius `δ`. -/
theorem mcu_rho2_val {δ : ℝ} {ρ₁ : ℝ → ℝ} {ρ₂ : ℝ × ℝ → ℝ} (hK : IsMollKer δ ρ₁ ρ₂)
    {w : ℝ × ℝ} (hw : w ∉ Metric.closedBall (0 : ℝ × ℝ) δ) : ρ₂ w = 0 := by
  apply hK.supp₂ w
  by_contra hc
  push_neg at hc
  apply hw
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  exact max_le (by rw [Real.norm_eq_abs]; exact hc.1) (by rw [Real.norm_eq_abs]; exact hc.2)

/-- A time mollifier vanishes outside `[s - δ, s + δ]`. -/
theorem mcu_rho1_zero {δ : ℝ} {ρ₁ : ℝ → ℝ} {ρ₂ : ℝ × ℝ → ℝ} (hK : IsMollKer δ ρ₁ ρ₂) {s t : ℝ}
    (ht : t ∉ Icc (s - δ) (s + δ)) : ρ₁ (s - t) = 0 := by
  apply hK.supp₁
  by_contra hc
  push_neg at hc
  exact ht ⟨by linarith [(abs_le.mp hc).2], by linarith [(abs_le.mp hc).1]⟩

/-- The support of the planar mollifier lies in the sup-norm ball of radius `δ`. -/
theorem mcu_tsupp {δ : ℝ} {ρ₁ : ℝ → ℝ} {ρ₂ : ℝ × ℝ → ℝ} (hK : IsMollKer δ ρ₁ ρ₂) :
    tsupport ρ₂ ⊆ Metric.closedBall (0 : ℝ × ℝ) δ := by
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro w hw
  by_contra hc
  exact (Function.mem_support.1 hw) (mcu_rho2_val hK hc)

/-- Reflecting a point outside the ball around `z` gives a point outside the ball around `0`. -/
theorem mcu_shift {δ : ℝ} {z x : ℝ × ℝ} (hx : x ∉ Metric.closedBall z δ) :
    z - x ∉ Metric.closedBall (0 : ℝ × ℝ) δ := by
  intro h
  apply hx
  rw [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm] at h
  rw [Metric.mem_closedBall, dist_comm]
  exact h

/-- The planar derivative of the mollifier vanishes outside the ball. -/
theorem mcu_fderiv_zero {δ : ℝ} {ρ₁ : ℝ → ℝ} {ρ₂ : ℝ × ℝ → ℝ} (hK : IsMollKer δ ρ₁ ρ₂)
    {z x : ℝ × ℝ} (hx : x ∉ Metric.closedBall z δ) : fderiv ℝ ρ₂ (z - x) = 0 :=
  fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => mcu_shift hx (mcu_tsupp hK h))

/-- Outside the box `[s - δ, s + δ] × ball(z, δ)` one of the two factors vanishes. -/
theorem mcu_outside {δ : ℝ} {ρ₁ : ℝ → ℝ} {ρ₂ : ℝ × ℝ → ℝ} (hK : IsMollKer δ ρ₁ ρ₂) {s : ℝ}
    {z : ℝ × ℝ} {x : Coord} (hx : x ∉ Icc (s - δ) (s + δ) ×ˢ Metric.closedBall z δ) :
    ρ₁ (s - x.1) = 0 ∨ x.2 ∉ Metric.closedBall z δ := by
  rw [Set.mem_prod, not_and_or] at hx
  rcases hx with h | h
  · exact Or.inl (mcu_rho1_zero hK h)
  · exact Or.inr h

/-- The reflected planar mollifier has derivative `-fd ρ₂(z - w) u`. -/
theorem mcu_psi_fd {δ : ℝ} {ρ₁ : ℝ → ℝ} {ρ₂ : ℝ × ℝ → ℝ} (hK : IsMollKer δ ρ₁ ρ₂)
    (z w u : ℝ × ℝ) : fderiv ℝ (fun w' : ℝ × ℝ => ρ₂ (z - w')) w u = -(fderiv ℝ ρ₂ (z - w) u) := by
  have hd : HasFDerivAt ρ₂ (fderiv ℝ ρ₂ (z - w)) (z - w) :=
    ((hK.smooth₂.differentiable (by simp)) (z - w)).hasFDerivAt
  have hl : HasFDerivAt (fun w' : ℝ × ℝ => z - w') (-ContinuousLinearMap.id ℝ (ℝ × ℝ)) w :=
    (hasFDerivAt_id w).const_sub z
  have hc := hd.comp w hl
  have h2 : fderiv ℝ (fun w' : ℝ × ℝ => ρ₂ (z - w')) w =
      (fderiv ℝ ρ₂ (z - w)).comp (-ContinuousLinearMap.id ℝ (ℝ × ℝ)) := hc.fderiv
  rw [h2]
  simp

/-- The slice-weighted cut integrand is integrable: a continuous compactly supported
coefficient times a locally integrable cut-off. -/
theorem mcu_integrable {δ : ℝ} {ρ₁ : ℝ → ℝ} {ρ₂ : ℝ × ℝ → ℝ} (hK : IsMollKer δ ρ₁ ρ₂) (s : ℝ)
    (z u : ℝ × ℝ) (g : Coord → ℂ) (hloc : LocallyIntegrable (cutC δ g) volume) :
    Integrable (fun x : Coord => ((ρ₁ (s - x.1) * fderiv ℝ ρ₂ (z - x.2) u : ℝ) : ℂ) * cutC δ g x)
      volume := by
  have hR : Continuous (fun x : Coord => ρ₁ (s - x.1) * fderiv ℝ ρ₂ (z - x.2) u) := by
    apply Continuous.mul
    · exact hK.smooth₁.continuous.comp (continuous_const.sub continuous_fst)
    · exact ((hK.smooth₂.continuous_fderiv (by simp)).comp
        (continuous_const.sub continuous_snd)).clm_apply continuous_const
  have hF : Continuous (fun x : Coord => ((ρ₁ (s - x.1) * fderiv ℝ ρ₂ (z - x.2) u : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hR
  have hKc : IsCompact (Icc (s - δ) (s + δ) ×ˢ Metric.closedBall z δ) :=
    isCompact_Icc.prod (isCompact_closedBall z δ)
  have hFc : HasCompactSupport
      (fun x : Coord => ((ρ₁ (s - x.1) * fderiv ℝ ρ₂ (z - x.2) u : ℝ) : ℂ)) := by
    refine HasCompactSupport.intro hKc (fun x hx => ?_)
    rcases mcu_outside hK hx with h | h
    · simp [h]
    · simp [mcu_fderiv_zero hK h]
  have hcs := hFc.mul_right (f' := cutC δ g)
  have hloc' : LocallyIntegrable
      (fun x : Coord => ((ρ₁ (s - x.1) * fderiv ℝ ρ₂ (z - x.2) u : ℝ) : ℂ) * cutC δ g x) volume :=
    LocallyIntegrable.continuous_mul hF hloc
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport _)).1
    (hloc'.integrableOn_isCompact hcs.isCompact)

/-- **Leaf `PartII-b:T11/6/12`** (the mollification is curl free). -/
theorem mollCurl : UnforcedLeray.Short.IIb.MollCurl := by
  intro c r b hc hr hb hFull δ ρ₁ ρ₂ hδ hK s hs z
  have hcut : ∀ i : Fin 2, LocallyIntegrable (cutC δ (fun x => b x i)) volume :=
    fun i => cutLocInt c r δ b hc hr hδ hb i
  have hcutEq : ∀ (i : Fin 2) (x : Coord), ρ₁ (s - x.1) ≠ 0 →
      cutC δ (fun y => b y i) x = b x i := by
    intro i x hx
    have hx' : |s - x.1| ≤ δ := by
      by_contra hc'
      push_neg at hc'
      exact hx (hK.supp₁ _ hc')
    have hmem : x ∈ {x : Coord | δ < x.1} := by
      show δ < x.1
      linarith [(abs_le.mp hx').2]
    unfold cutC
    rw [Set.indicator_of_mem hmem]
  have hG1 : Differentiable ℝ (fun t : ℝ => ρ₁ (s - t)) :=
    (hK.smooth₁.differentiable (by simp)).comp ((differentiable_const s).sub differentiable_id)
  have hθ : TimeTest (fun t : ℝ => ρ₁ (s - t)) := by
    have hIcc : IsCompact (Icc (s - δ) (s + δ)) := isCompact_Icc
    have hIccC : IsClosed (Icc (s - δ) (s + δ)) := isClosed_Icc
    refine ⟨?_, ?_, ?_⟩
    · exact hK.smooth₁.comp (contDiff_const.sub contDiff_id)
    · exact HasCompactSupport.intro hIcc (fun t ht => mcu_rho1_zero hK ht)
    · refine (closure_minimal ?_ hIccC).trans ?_
      · intro t ht
        by_contra hc'
        exact (Function.mem_support.1 ht) (mcu_rho1_zero hK hc')
      · intro t ht
        show (0 : ℝ) < t
        linarith [ht.1]
  have hψ : ContDiff ℝ ∞ (fun w : ℝ × ℝ => ρ₂ (z - w)) :=
    hK.smooth₂.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport (fun w : ℝ × ℝ => ρ₂ (z - w)) :=
    HasCompactSupport.intro (isCompact_closedBall z δ)
      (fun w hw => mcu_rho2_val hK (mcu_shift hw))
  have hFO := hFull (fun t => ρ₁ (s - t)) (fun w => ρ₂ (z - w)) hθ hψ hψc
  have hI0 := mcu_integrable hK s z (0, 1) (fun x => b x 0) (hcut 0)
  have hI1 := mcu_integrable hK s z (1, 0) (fun x => b x 1) (hcut 1)
  rw [mollSliceDeriv (fun x => b x 0) δ ρ₁ ρ₂ hδ hK (hcut 0) s z (0, 1),
    mollSliceDeriv (fun x => b x 1) δ ρ₁ ρ₂ hδ hK (hcut 1) s z (1, 0), ← integral_sub hI0 hI1]
  have key : ∀ x : Coord,
      ((ρ₁ (s - x.1) * fderiv ℝ ρ₂ (z - x.2) (0, 1) : ℝ) : ℂ) * cutC δ (fun y => b y 0) x -
        ((ρ₁ (s - x.1) * fderiv ℝ ρ₂ (z - x.2) (1, 0) : ℝ) : ℂ) * cutC δ (fun y => b y 1) x =
      -(streamPair b (fun t => ρ₁ (s - t)) (fun w => ρ₂ (z - w)) x) := by
    intro x
    by_cases hx : ρ₁ (s - x.1) = 0
    · simp [streamPair, hx]
    · rw [hcutEq 0 x hx, hcutEq 1 x hx]
      simp only [streamPair, perpGrad, Fin.sum_univ_two, mcu_psi_fd hK z, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, neg_neg]
      push_cast
      ring
  rw [integral_congr_ae (ae_of_all volume key), integral_neg, hFO, neg_zero]

end UnforcedLeray.Short.IIb
