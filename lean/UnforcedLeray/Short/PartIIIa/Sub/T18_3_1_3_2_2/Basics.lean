import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2_2.Props
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.SmoothWeak

/-!
# Part III-a, `PartIII-a:T18/3/1/3/2/2/org`: pairing continuity, integration by parts, the test

Source of record: `the November 2 reference manuscript` lines 3427-3440, 3541-3552.
`lmIpTendstoRight`, `lmSmoothIBP`, `lmJWeakDiv`, `lmH1Test` (statements in `Props.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem lm_sq_integrable {c : ℝ} {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) :
    Integrable (fun y => ‖g y‖ ^ 2) (volume.restrict (B0579.cell c)) :=
  (memLp_two_iff_integrable_sq_norm hg.1).1 hg

theorem lm_vec_sq_integrable {c : ℝ} {g : LMSpField} (hg : LMCellL2 c g) :
    Integrable (fun x => ∑ i : Fin 2, ‖g x i‖ ^ 2) (volume.restrict (B0579.cell c)) :=
  integrable_finsetSum _ fun i _ => lm_sq_integrable (hg i)

/-- Young's inequality for the pairing: `2 l ‖⟨f, h⟩‖ ≤ l² ‖f‖² + ‖h‖²`. -/
theorem lmIp_young {c : ℝ} {f h : LMSpField} (hf : LMCellL2 c f) (hh : LMCellL2 c h) {l : ℝ}
    (hl : 0 < l) :
    2 * l * ‖LMIp c f h‖ ≤ l ^ 2 * (∫ x in B0579.cell c, ∑ i : Fin 2, ‖f x i‖ ^ 2) +
      ∫ x in B0579.cell c, ∑ i : Fin 2, ‖h x i‖ ^ 2 := by
  have hFi : Integrable (fun x => ∑ i : Fin 2, starRingEnd ℂ (f x i) * h x i)
      (volume.restrict (B0579.cell c)) :=
    integrable_finsetSum _ fun i _ => lmIp_integrable hf hh i
  have h1 : ‖LMIp c f h‖ ≤ ∫ x in B0579.cell c, ‖∑ i : Fin 2, starRingEnd ℂ (f x i) * h x i‖ :=
    norm_integral_le_integral_norm _
  have hpt : ∀ x, 2 * l * ‖∑ i : Fin 2, starRingEnd ℂ (f x i) * h x i‖ ≤
      l ^ 2 * (∑ i : Fin 2, ‖f x i‖ ^ 2) + ∑ i : Fin 2, ‖h x i‖ ^ 2 := by
    intro x
    have h2 : ‖∑ i : Fin 2, starRingEnd ℂ (f x i) * h x i‖ ≤ ∑ i : Fin 2, ‖f x i‖ * ‖h x i‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, RCLike.norm_conj]
    have h3 : ∀ i : Fin 2, 2 * l * (‖f x i‖ * ‖h x i‖) ≤ l ^ 2 * ‖f x i‖ ^ 2 + ‖h x i‖ ^ 2 := fun i => by
      nlinarith [sq_nonneg (l * ‖f x i‖ - ‖h x i‖)]
    calc 2 * l * ‖∑ i : Fin 2, starRingEnd ℂ (f x i) * h x i‖
        ≤ 2 * l * ∑ i : Fin 2, ‖f x i‖ * ‖h x i‖ :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ∑ i : Fin 2, 2 * l * (‖f x i‖ * ‖h x i‖) := by rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin 2, (l ^ 2 * ‖f x i‖ ^ 2 + ‖h x i‖ ^ 2) := Finset.sum_le_sum fun i _ => h3 i
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hA := lm_vec_sq_integrable hf
  have hB := lm_vec_sq_integrable hh
  have hR : Integrable (fun x => l ^ 2 * (∑ i : Fin 2, ‖f x i‖ ^ 2) + ∑ i : Fin 2, ‖h x i‖ ^ 2)
      (volume.restrict (B0579.cell c)) := (hA.const_mul (l ^ 2)).add hB
  have hint := integral_mono (hFi.norm.const_mul (2 * l)) hR hpt
  rw [integral_const_mul, integral_add (hA.const_mul _) hB, integral_const_mul] at hint
  calc 2 * l * ‖LMIp c f h‖
      ≤ 2 * l * ∫ x in B0579.cell c, ‖∑ i : Fin 2, starRingEnd ℂ (f x i) * h x i‖ :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ _ := hint

/-- **Continuity of the pairing in the second slot.** -/
theorem lmIpTendstoRight : LMIpTendstoRight := by
  intro c f g₀ g hf hg₀ hg hlim
  have hd : ∀ n, LMCellL2 c (fun x i => g n x i - g₀ x i) := fun n i => (hg n i).sub (hg₀ i)
  have hsub : ∀ n, LMIp c f (g n) - LMIp c f g₀ = LMIp c f (fun x i => g n x i - g₀ x i) := by
    intro n
    have hm : LMCellL2 c (fun x i => (-1 : ℂ) * g₀ x i) := fun i => (hg₀ i).const_mul _
    have e : (fun x i => g n x i - g₀ x i) = fun x i => g n x i + (-1 : ℂ) * g₀ x i := by
      funext x i; ring
    rw [e, lmIp_add_right hf (hg n) hm, lmIp_smul_right]
    ring
  set A : ℝ := ∫ x in B0579.cell c, ∑ i : Fin 2, ‖f x i‖ ^ 2 with hA
  have hA0 : 0 ≤ A := integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [tendsto_iff_norm_sub_tendsto_zero]
  rw [Metric.tendsto_nhds]
  intro ε hε
  set l : ℝ := ε / (A + 1) with hl
  have hlpos : 0 < l := div_pos hε (by linarith)
  have hlA : l * A ≤ ε := by
    rw [hl, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  filter_upwards [hlim.eventually (gt_mem_nhds (mul_pos hlpos hε))] with n hn
  have hY := lmIp_young hf (hd n) hlpos
  rw [hsub n, Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  have h2 : l ^ 2 * A ≤ l * ε := by nlinarith
  have h3 : 2 * l * ‖LMIp c f fun x i => g n x i - g₀ x i‖ < 2 * l * ε := by
    have h4 : ∫ x in B0579.cell c, ∑ i : Fin 2, ‖g n x i - g₀ x i‖ ^ 2 < l * ε := hn
    linarith
  exact lt_of_mul_lt_mul_left h3 (by positivity)

theorem lm_conj_differentiable {a : ℝ × ℝ → ℂ} (ha : Differentiable ℝ a) :
    Differentiable ℝ (fun x => starRingEnd ℂ (a x)) :=
  fun y => ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp y (ha y).hasFDerivAt).differentiableAt

lemma lm_partialQ_conj {a : ℝ × ℝ → ℂ} (ha : Differentiable ℝ a) (z : ℝ × ℝ) :
    Cyl.partialQ (fun x => starRingEnd ℂ (a x)) z = starRingEnd ℂ (Cyl.partialQ a z) := by
  have h := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt z.1
    (Cyl.hasDerivAt_sliceQ ha z.1 z.2)
  simp only [Prod.mk.eta] at h
  exact h.deriv

lemma lm_partialEta_conj {a : ℝ × ℝ → ℂ} (ha : Differentiable ℝ a) (z : ℝ × ℝ) :
    Cyl.partialEta (fun x => starRingEnd ℂ (a x)) z = starRingEnd ℂ (Cyl.partialEta a z) := by
  have h := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt z.2
    (Cyl.hasDerivAt_sliceEta ha z.1 z.2)
  simp only [Prod.mk.eta] at h
  exact h.deriv

/-- **Integration by parts for smooth periodic `H¹` scalars.** -/
theorem lmSmoothIBP : LMSmoothIBP := by
  intro c hc j a b ha hb hap hbp hLa hLb hLa' hLb'
  have had : Differentiable ℝ a := ha.differentiable (by simp)
  have hbd : Differentiable ℝ b := hb.differentiable (by simp)
  have hfd := lm_conj_differentiable had
  have hcell : B0579.cell c = Cyl.cell c := by
    unfold B0579.cell Cyl.cell
    rw [neg_div]
  have hi1 : Integrable (fun x => starRingEnd ℂ (LMPd j a x) * b x)
      (volume.restrict (B0579.cell c)) := hLa'.star.integrable_mul hLb
  have hi2 : Integrable (fun x => starRingEnd ℂ (a x) * LMPd j b x)
      (volume.restrict (B0579.cell c)) := hLa.star.integrable_mul hLb'
  have hi0 : Integrable (fun x => starRingEnd ℂ (a x) * b x)
      (volume.restrict (B0579.cell c)) := hLa.star.integrable_mul hLb
  have hj : j = 0 ∨ j = 1 := by
    fin_cases j <;> simp
  rcases hj with rfl | rfl
  · have ea : ∀ z, Cyl.partialQ (fun x => starRingEnd ℂ (a x)) z = starRingEnd ℂ (LMPd 0 a z) :=
      fun z => by rw [lm_partialQ_conj had, lmSW_LMPd0 had]
    have eb : ∀ z, Cyl.partialQ b z = LMPd 0 b z := fun z => (lmSW_LMPd0 hbd z).symm
    have hper : Cyl.IsPeriodic c (fun x => starRingEnd ℂ (a x)) := fun z => by
      show starRingEnd ℂ (a (z.1 + c, z.2)) = starRingEnd ℂ (a z)
      rw [hap z]
    have IBP := Cyl.integral_cell_partialQ_mul hc hfd hbd hper hbp
      (by simp only [ea]; rw [← hcell]; exact hi1) (by simp only [eb]; rw [← hcell]; exact hi2)
    simp only [ea, eb] at IBP
    rw [← hcell] at IBP
    rw [IBP, neg_neg]
  · have ea : ∀ z, Cyl.partialEta (fun x => starRingEnd ℂ (a x)) z = starRingEnd ℂ (LMPd 1 a z) :=
      fun z => by rw [lm_partialEta_conj had, lmSW_LMPd1 had]
    have eb : ∀ z, Cyl.partialEta b z = LMPd 1 b z := fun z => (lmSW_LMPd1 hbd z).symm
    have IBP := Cyl.integral_cell_partialEta_mul hfd hbd (by rw [← hcell]; exact hi0)
      (by simp only [ea]; rw [← hcell]; exact hi1) (by simp only [eb]; rw [← hcell]; exact hi2)
    simp only [ea, eb] at IBP
    rw [← hcell] at IBP
    rw [IBP, neg_neg]

/-- **`J_k f` is weakly divergence free when `f` is.** -/
theorem lmJWeakDiv : LMJWeakDiv := by
  intro c hc J hJ hX k f hf hfd ψ hψ
  obtain ⟨C, hC⟩ := hX.gradL2 k
  have hd := hX.divFreeWeak k f hf hfd
  have hw : ∀ j : Fin 2, LMWeakPd c j (fun x => J k f x j) (LMPd j (fun x => J k f x j)) := fun j =>
    lmSmoothWeakPd c hc j _ (hJ.smooth k f hf j) (fun x => hJ.periodic k f hf x j)
      (hJ.memL2 k f hf j) (hC f hf j j).1
  obtain ⟨R, hR⟩ := hψ.band
  have hi0 : ∀ j : Fin 2, Integrable (fun x => J k f x j * (B0579.pd j ψ x : ℂ))
      (volume.restrict (B0579.cell c)) := fun j => by
    obtain ⟨R', hR'⟩ := (hψ.pd j).band
    exact lmSW_integrableOn (R := R') (hJ.memL2 k f hf j)
      (Complex.continuous_ofReal.comp (hψ.pd j).continuous) (fun x hx => by simp [hR' x hx])
  have hi1 : ∀ j : Fin 2, Integrable (fun x => LMPd j (fun y => J k f y j) x * (ψ x : ℂ))
      (volume.restrict (B0579.cell c)) := fun j =>
    lmSW_integrableOn (R := R) (hC f hf j j).1 (Complex.continuous_ofReal.comp hψ.continuous)
      (fun x hx => by simp [hR x hx])
  have e : ∀ j : Fin 2, ∫ x in B0579.cell c, J k f x j * (B0579.pd j ψ x : ℂ) =
      -∫ x in B0579.cell c, LMPd j (fun y => J k f y j) x * (ψ x : ℂ) := fun j =>
    (hw j).2.2 ψ hψ.smooth hψ.periodic hψ.band
  rw [integral_add (hi0 0) (hi0 1), e 0, e 1, ← neg_add, ← integral_add (hi1 0) (hi1 1)]
  have hz : ∀ x : ℝ × ℝ, LMPd 0 (fun y => J k f y 0) x * (ψ x : ℂ) +
      LMPd 1 (fun y => J k f y 1) x * (ψ x : ℂ) = 0 := fun x => by
    rw [← add_mul, hd x, zero_mul]
  simp only [hz, integral_zero, neg_zero]

/-- `∂ⱼ` of the real part is the real part of `LMPd`. -/
theorem lmPd_re (j : Fin 2) (g : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    B0579.pd j (fun y => (g y).re) x = (LMPd j g x).re := by
  simp [LMPd]

/-- `∂ⱼ` of the imaginary part is the imaginary part of `LMPd`. -/
theorem lmPd_im (j : Fin 2) (g : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    B0579.pd j (fun y => (g y).im) x = (LMPd j g x).im := by
  simp [LMPd]

/-- **The real and imaginary parts of `J_k f` are `H¹` divergence-free tests.** -/
theorem lmH1Test : LMH1Test := by
  intro c hc J hJ hX k f hf hfd
  obtain ⟨C, hC⟩ := hX.gradL2 k
  have hd := hX.divFreeWeak k f hf hfd
  refine ⟨⟨fun i => Complex.reCLM.contDiff.comp (hJ.smooth k f hf i), fun x i => ?_, fun x => ?_,
      fun i => (hJ.memL2 k f hf i).re, fun i j => ?_⟩,
    ⟨fun i => Complex.imCLM.contDiff.comp (hJ.smooth k f hf i), fun x i => ?_, fun x => ?_,
      fun i => (hJ.memL2 k f hf i).im, fun i j => ?_⟩⟩
  · show (J k f (x.1 + c, x.2) i).re = (J k f x i).re
    rw [hJ.periodic k f hf x i]
  · rw [lmPd_re, lmPd_re, ← Complex.add_re, hd x, Complex.zero_re]
  · have e : (fun x => B0579.pd j (fun y => (J k f y i).re) x) =
        fun x => (LMPd j (fun y => J k f y i) x).re := funext fun x => lmPd_re j _ x
    show MemLp (fun x => B0579.pd j (fun y => (J k f y i).re) x) 2 _
    rw [e]
    exact (hC f hf i j).1.re
  · show (J k f (x.1 + c, x.2) i).im = (J k f x i).im
    rw [hJ.periodic k f hf x i]
  · rw [lmPd_im, lmPd_im, ← Complex.add_im, hd x, Complex.zero_im]
  · have e : (fun x => B0579.pd j (fun y => (J k f y i).im) x) =
        fun x => (LMPd j (fun y => J k f y i) x).im := funext fun x => lmPd_im j _ x
    show MemLp (fun x => B0579.pd j (fun y => (J k f y i).im) x) 2 _
    rw [e]
    exact (hC f hf i j).1.im

end UnforcedLeray.Short.IIIa
