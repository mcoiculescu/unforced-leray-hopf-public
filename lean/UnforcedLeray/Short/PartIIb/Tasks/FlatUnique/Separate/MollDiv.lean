import UnforcedLeray.Short.PartIIb.Sub.T11_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.CutLocInt
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.MollSliceDeriv

/-!
# Leaf `MollDiv` (`PartII-b:T11/6/9`): the mollified slices are planar divergence free

Proves `MollDiv` (defined in `Sub/T11_6.lean`). By `mollSliceDeriv` the divergence is
`∫ ρ₁(s - x₁) [fd ρ₂(z - x₂) (1,0) · b₀ + fd ρ₂(z - x₂) (0,1) · b₁]` with the cut-off replaced by
`b` (on the support `x₁ > δ`). The coordinate test `φ(x) = ρ₁(s - x₁) ρ₂(z - x₂)` has
`cpd 1 φ = -ρ₁ fd ρ₂(·)(1,0)`, `cpd 2 φ = -ρ₁ fd ρ₂(·)(0,1)`, so the integral is minus the
`WeakSolenoidal` integral, which vanishes. Source of record:
`the November 2 reference manuscript`, SP 2618 and 1923-1938.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- An admissible planar mollifier vanishes outside the sup-norm ball of radius `δ`. -/
theorem mdv_rho2_val {δ : ℝ} {ρ₁ : ℝ → ℝ} {ρ₂ : ℝ × ℝ → ℝ} (hK : IsMollKer δ ρ₁ ρ₂)
    {w : ℝ × ℝ} (hw : w ∉ Metric.closedBall (0 : ℝ × ℝ) δ) : ρ₂ w = 0 := by
  apply hK.supp₂ w
  by_contra hc
  push_neg at hc
  apply hw
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  exact max_le (by rw [Real.norm_eq_abs]; exact hc.1) (by rw [Real.norm_eq_abs]; exact hc.2)

/-- A time mollifier vanishes outside `[s - δ, s + δ]`. -/
theorem mdv_rho1_zero {δ : ℝ} {ρ₁ : ℝ → ℝ} {ρ₂ : ℝ × ℝ → ℝ} (hK : IsMollKer δ ρ₁ ρ₂) {s t : ℝ}
    (ht : t ∉ Icc (s - δ) (s + δ)) : ρ₁ (s - t) = 0 := by
  apply hK.supp₁
  by_contra hc
  push_neg at hc
  exact ht ⟨by linarith [(abs_le.mp hc).2], by linarith [(abs_le.mp hc).1]⟩

/-- The support of the planar mollifier lies in the sup-norm ball of radius `δ`. -/
theorem mdv_tsupp {δ : ℝ} {ρ₁ : ℝ → ℝ} {ρ₂ : ℝ × ℝ → ℝ} (hK : IsMollKer δ ρ₁ ρ₂) :
    tsupport ρ₂ ⊆ Metric.closedBall (0 : ℝ × ℝ) δ := by
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro w hw
  by_contra hc
  exact (Function.mem_support.1 hw) (mdv_rho2_val hK hc)

/-- Reflecting a point outside the ball around `z` gives a point outside the ball around `0`. -/
theorem mdv_shift {δ : ℝ} {z x : ℝ × ℝ} (hx : x ∉ Metric.closedBall z δ) :
    z - x ∉ Metric.closedBall (0 : ℝ × ℝ) δ := by
  intro h
  apply hx
  rw [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm] at h
  rw [Metric.mem_closedBall, dist_comm]
  exact h

/-- The planar derivative of the mollifier vanishes outside the ball. -/
theorem mdv_fderiv_zero {δ : ℝ} {ρ₁ : ℝ → ℝ} {ρ₂ : ℝ × ℝ → ℝ} (hK : IsMollKer δ ρ₁ ρ₂)
    {z x : ℝ × ℝ} (hx : x ∉ Metric.closedBall z δ) : fderiv ℝ ρ₂ (z - x) = 0 :=
  fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => mdv_shift hx (mdv_tsupp hK h))

/-- Outside the box `[s - δ, s + δ] × ball(z, δ)` one of the two factors vanishes. -/
theorem mdv_outside {δ : ℝ} {ρ₁ : ℝ → ℝ} {ρ₂ : ℝ × ℝ → ℝ} (hK : IsMollKer δ ρ₁ ρ₂) {s : ℝ}
    {z : ℝ × ℝ} {x : Coord} (hx : x ∉ Icc (s - δ) (s + δ) ×ˢ Metric.closedBall z δ) :
    ρ₁ (s - x.1) = 0 ∨ x.2 ∉ Metric.closedBall z δ := by
  rw [Set.mem_prod, not_and_or] at hx
  rcases hx with h | h
  · exact Or.inl (mdv_rho1_zero hK h)
  · exact Or.inr h

/-- Derivatives in the planar slot of a function of `x.2`. -/
theorem mdv_cpd_snd (G : ℝ × ℝ → ℝ) (hG : Differentiable ℝ G) (j : Fin 3) (x : Coord) :
    cpd j (fun y : Coord => G y.2) x = fderiv ℝ G x.2 (cdir j).2 := by
  unfold cpd
  have hL : HasFDerivAt (fun y : Coord => y.2) (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) x :=
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).hasFDerivAt
  have hc := (hG x.2).hasFDerivAt.comp x hL
  rw [show (fun y : Coord => G y.2) = G ∘ (fun y : Coord => y.2) from rfl, hc.fderiv]
  simp

/-- Derivatives in the `s`-slot of a function of `x.1`. -/
theorem mdv_cpd_fst (G : ℝ → ℝ) (hG : Differentiable ℝ G) (j : Fin 3) (x : Coord) :
    cpd j (fun y : Coord => G y.1) x = fderiv ℝ G x.1 (cdir j).1 := by
  unfold cpd
  have hL : HasFDerivAt (fun y : Coord => y.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt
  have hc := (hG x.1).hasFDerivAt.comp x hL
  rw [show (fun y : Coord => G y.1) = G ∘ (fun y : Coord => y.1) from rfl, hc.fderiv]
  simp

/-- The reflected planar mollifier has derivative `-fd ρ₂(z - w) u`. -/
theorem mdv_psi_fd {δ : ℝ} {ρ₁ : ℝ → ℝ} {ρ₂ : ℝ × ℝ → ℝ} (hK : IsMollKer δ ρ₁ ρ₂)
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

theorem mdv_cdir1_fst : (cdir 1).1 = 0 := by simp [cdir]
theorem mdv_cdir2_fst : (cdir 2).1 = 0 := by simp [cdir]
theorem mdv_cdir1_snd : (cdir 1).2 = (1, 0) := by simp [cdir]
theorem mdv_cdir2_snd : (cdir 2).2 = (0, 1) := by simp [cdir]

/-- The slice-weighted cut integrand is integrable: a continuous compactly supported
coefficient times a locally integrable cut-off. -/
theorem mdv_integrable {δ : ℝ} {ρ₁ : ℝ → ℝ} {ρ₂ : ℝ × ℝ → ℝ} (hK : IsMollKer δ ρ₁ ρ₂) (s : ℝ)
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
    rcases mdv_outside hK hx with h | h
    · simp [h]
    · simp [mdv_fderiv_zero hK h]
  have hcs := hFc.mul_right (f' := cutC δ g)
  have hloc' : LocallyIntegrable
      (fun x : Coord => ((ρ₁ (s - x.1) * fderiv ℝ ρ₂ (z - x.2) u : ℝ) : ℂ) * cutC δ g x) volume :=
    LocallyIntegrable.continuous_mul hF hloc
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport _)).1
    (hloc'.integrableOn_isCompact hcs.isCompact)

/-- **Leaf `PartII-b:T11/6/9`** (the mollification is divergence free). -/
theorem mollDiv : UnforcedLeray.Short.IIb.MollDiv := by
  intro c r b hc hr hb hW δ ρ₁ ρ₂ hδ hK s hs z
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
  have hG2 : Differentiable ℝ (fun w : ℝ × ℝ => ρ₂ (z - w)) :=
    (hK.smooth₂.differentiable (by simp)).comp ((differentiable_const z).sub differentiable_id)
  have hdf : Differentiable ℝ (fun y : Coord => ρ₁ (s - y.1)) :=
    hG1.comp differentiable_fst
  have hdg : Differentiable ℝ (fun y : Coord => ρ₂ (z - y.2)) :=
    hG2.comp differentiable_snd
  have hprod : ∀ (j : Fin 3) (x : Coord),
      cpd j (fun y : Coord => ρ₁ (s - y.1) * ρ₂ (z - y.2)) x =
        ρ₁ (s - x.1) * cpd j (fun y : Coord => ρ₂ (z - y.2)) x +
          ρ₂ (z - x.2) * cpd j (fun y : Coord => ρ₁ (s - y.1)) x := by
    intro j x
    unfold cpd
    rw [fderiv_fun_mul (hdf x) (hdg x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have hcpd_f1 : ∀ x : Coord, cpd 1 (fun y : Coord => ρ₁ (s - y.1)) x = 0 := by
    intro x
    rw [mdv_cpd_fst _ hG1 1 x, mdv_cdir1_fst, map_zero]
  have hcpd_f2 : ∀ x : Coord, cpd 2 (fun y : Coord => ρ₁ (s - y.1)) x = 0 := by
    intro x
    rw [mdv_cpd_fst _ hG1 2 x, mdv_cdir2_fst, map_zero]
  have hcpd_g : ∀ (j : Fin 3) (x : Coord),
      cpd j (fun y : Coord => ρ₂ (z - y.2)) x = -(fderiv ℝ ρ₂ (z - x.2) (cdir j).2) := by
    intro j x
    refine (mdv_cpd_snd (fun w => ρ₂ (z - w)) hG2 j x).trans ?_
    exact mdv_psi_fd hK z x.2 (cdir j).2
  have hφ : IsCoordTest (fun y : Coord => ρ₁ (s - y.1) * ρ₂ (z - y.2)) := by
    have hKc : IsCompact (Icc (s - δ) (s + δ) ×ˢ Metric.closedBall z δ) :=
      isCompact_Icc.prod (isCompact_closedBall z δ)
    refine ⟨?_, ?_, ?_⟩
    · exact (hK.smooth₁.comp (contDiff_const.sub contDiff_fst)).mul
        (hK.smooth₂.comp (contDiff_const.sub contDiff_snd))
    · refine HasCompactSupport.intro hKc (fun x hx => ?_)
      rcases mdv_outside hK hx with h | h
      · simp [h]
      · simp [mdv_rho2_val hK (mdv_shift h)]
    · refine (closure_minimal ?_ hKc.isClosed).trans (Set.prod_mono ?_ (subset_univ _))
      · intro x hx
        by_contra hc'
        refine Function.mem_support.1 hx ?_
        rcases mdv_outside hK hc' with h | h
        · simp [h]
        · simp [mdv_rho2_val hK (mdv_shift h)]
      · intro t ht
        show (0 : ℝ) < t
        linarith [ht.1]
  have hcpd1 : ∀ x : Coord, cpd 1 (fun y : Coord => ρ₁ (s - y.1) * ρ₂ (z - y.2)) x =
      -(ρ₁ (s - x.1) * fderiv ℝ ρ₂ (z - x.2) (1, 0)) := by
    intro x
    rw [hprod 1 x, hcpd_g 1 x, hcpd_f1 x, mdv_cdir1_snd]
    ring
  have hcpd2 : ∀ x : Coord, cpd 2 (fun y : Coord => ρ₁ (s - y.1) * ρ₂ (z - y.2)) x =
      -(ρ₁ (s - x.1) * fderiv ℝ ρ₂ (z - x.2) (0, 1)) := by
    intro x
    rw [hprod 2 x, hcpd_g 2 x, hcpd_f2 x, mdv_cdir2_snd]
    ring
  have hI0 := mdv_integrable hK s z (1, 0) (fun x => b x 0) (hcut 0)
  have hI1 := mdv_integrable hK s z (0, 1) (fun x => b x 1) (hcut 1)
  rw [mollSliceDeriv (fun x => b x 0) δ ρ₁ ρ₂ hδ hK (hcut 0) s z (1, 0),
    mollSliceDeriv (fun x => b x 1) δ ρ₁ ρ₂ hδ hK (hcut 1) s z (0, 1), ← integral_add hI0 hI1]
  have key : ∀ x : Coord,
      ((ρ₁ (s - x.1) * fderiv ℝ ρ₂ (z - x.2) (1, 0) : ℝ) : ℂ) * cutC δ (fun y => b y 0) x +
        ((ρ₁ (s - x.1) * fderiv ℝ ρ₂ (z - x.2) (0, 1) : ℝ) : ℂ) * cutC δ (fun y => b y 1) x =
      -(b x 0 * (cpd 1 (fun y : Coord => ρ₁ (s - y.1) * ρ₂ (z - y.2)) x : ℂ) +
        b x 1 * (cpd 2 (fun y : Coord => ρ₁ (s - y.1) * ρ₂ (z - y.2)) x : ℂ)) := by
    intro x
    rw [hcpd1 x, hcpd2 x]
    by_cases hx : ρ₁ (s - x.1) = 0
    · simp [hx]
    · rw [hcutEq 0 x hx, hcutEq 1 x hx]
      push_cast
      ring
  rw [integral_congr_ae (ae_of_all volume key), integral_neg, (hW _ hφ).2, neg_zero]

end UnforcedLeray.Short.IIb
