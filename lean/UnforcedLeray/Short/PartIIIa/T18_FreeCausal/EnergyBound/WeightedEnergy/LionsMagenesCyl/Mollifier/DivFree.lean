import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.Mollifier.Conv
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.SmoothWeak

/-!
# Part III-a, `PartIII-a:T18/3/1/3/1`: preservation of smooth periodic divergence-free fields

Source of record: `the November 2 reference manuscript` lines 3427-3440 and
3541-3552. For a smooth `c`-periodic `f` the derivative of `J_k f` is `J_k` of the derivative of `f`
(integration by parts on the cell; periodicity removes the seam term), so `J_k` preserves
`∂_q f₀ + ∂_η f₁ = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIIa

/-- A continuous function vanishing for `|η|` large is integrable on the cell. -/
theorem lm_integrableOn_band {c R : ℝ} {ψ : ℝ × ℝ → ℂ} (hψ : Continuous ψ)
    (hR : ∀ x : ℝ × ℝ, R < |x.2| → ψ x = 0) : IntegrableOn ψ (B0579.cell c) := by
  have hK : IsCompact (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) := isCompact_Icc.prod isCompact_Icc
  have h1 : IntegrableOn ψ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) :=
    hψ.continuousOn.integrableOn_compact hK
  have h2 : IntegrableOn ψ (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) :=
    h1.mono_set (prod_mono Ico_subset_Icc_self subset_rfl)
  refine h2.of_forall_sdiff_eq_zero (B0579.measurableSet_cell c) ?_
  rintro y ⟨hy1, hy2⟩
  have hgt : R < |y.2| := by
    by_contra hcon
    push Not at hcon
    exact hy2 ⟨hy1.1, abs_le.mp hcon⟩
  exact hR y hgt

/-- Integration by parts on the cell against a cylinder test function, for a smooth periodic field
(no integrability of the field is needed, the test function is compactly supported in `η`). -/
theorem lm_smooth_ibp' {c : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hper : ∀ y : ℝ × ℝ, f (y.1 + c, y.2) = f y) {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ)
    (j : Fin 2) :
    -∫ y in B0579.cell c, f y * (B0579.pd j φ y : ℂ) =
      ∫ y in B0579.cell c, (φ y : ℂ) * LMPd j f y := by
  obtain ⟨R, hR⟩ := hφ.band
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hφC : Differentiable ℝ (fun x => (φ x : ℂ)) :=
    fun x => (Complex.ofRealCLM.hasFDerivAt.comp x (hφd x).hasFDerivAt).differentiableAt
  have hψc : Continuous (fun x => (φ x : ℂ)) := Complex.continuous_ofReal.comp hφ.continuous
  have hψR : ∀ x : ℝ × ℝ, R < |x.2| → (φ x : ℂ) = 0 := fun x hx => by simp [hR x hx]
  have hpf : Cyl.IsPeriodic c f := hper
  have hper' : Cyl.IsPeriodic c (fun x => (φ x : ℂ)) := by
    intro z
    show ((φ (z.1 + c, z.2) : ℝ) : ℂ) = ((φ z : ℝ) : ℂ)
    rw [hφ.periodic z]
  have hcontφ := Cyl.C1_partial_of_contDiff hφ1
  have hcontf := Cyl.C1_partial_of_contDiff hf1
  have hQc : Continuous (fun x => ((Cyl.partialQ φ x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hcontφ.1
  have hEc : Continuous (fun x => ((Cyl.partialEta φ x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hcontφ.2
  have hQz : ∀ x : ℝ × ℝ, R < |x.2| → ((Cyl.partialQ φ x : ℝ) : ℂ) = 0 := fun x hx => by
    simp [lmSW_partialQ_zero (fun y hy => hR y hy) x hx]
  have hEz : ∀ x : ℝ × ℝ, R < |x.2| → ((Cyl.partialEta φ x : ℝ) : ℂ) = 0 := fun x hx => by
    simp [lmSW_partialEta_zero (fun y hy => hR y hy) x hx]
  have hcell : B0579.cell c = Cyl.cell c := by
    unfold B0579.cell Cyl.cell
    rw [neg_div]
  have hmulz : ∀ {A B : ℝ × ℝ → ℂ}, (∀ x : ℝ × ℝ, R < |x.2| → B x = 0) →
      ∀ x : ℝ × ℝ, R < |x.2| → A x * B x = 0 := fun hB x hx => by simp [hB x hx]
  have hj : j = 0 ∨ j = 1 := by
    fin_cases j <;> simp
  rcases hj with rfl | rfl
  · have h1 : IntegrableOn (fun z => Cyl.partialQ f z * (φ z : ℂ)) (B0579.cell c) :=
      lm_integrableOn_band (hcontf.1.mul hψc) (hmulz hψR)
    have h2 : IntegrableOn (fun z => f z * Cyl.partialQ (fun x => (φ x : ℂ)) z)
        (B0579.cell c) := by
      simp only [lmSW_partialQ_ofReal hφd]
      exact lm_integrableOn_band (hf.continuous.mul hQc) (hmulz hQz)
    rw [hcell] at h1 h2
    have IBP := Cyl.integral_cell_partialQ_mul hc hfd hφC hpf hper' h1 h2
    rw [← hcell] at IBP
    simp only [lmSW_partialQ_ofReal hφd] at IBP
    simp only [lmSW_pd0_eq hφd, lmSW_LMPd0 hfd]
    rw [← IBP]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    exact mul_comm _ _
  · have h0 : IntegrableOn (fun z => f z * (φ z : ℂ)) (B0579.cell c) :=
      lm_integrableOn_band (hf.continuous.mul hψc) (hmulz hψR)
    have h1 : IntegrableOn (fun z => Cyl.partialEta f z * (φ z : ℂ)) (B0579.cell c) :=
      lm_integrableOn_band (hcontf.2.mul hψc) (hmulz hψR)
    have h2 : IntegrableOn (fun z => f z * Cyl.partialEta (fun x => (φ x : ℂ)) z)
        (B0579.cell c) := by
      simp only [lmSW_partialEta_ofReal hφd]
      exact lm_integrableOn_band (hf.continuous.mul hEc) (hmulz hEz)
    rw [hcell] at h0 h1 h2
    have IBP := Cyl.integral_cell_partialEta_mul hfd hφC h0 h1 h2
    rw [← hcell] at IBP
    simp only [lmSW_partialEta_ofReal hφd] at IBP
    simp only [lmSW_pd1_eq hφd, lmSW_LMPd1 hfd]
    rw [← IBP]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    exact mul_comm _ _

theorem lm_smooth_ibp {c : ℝ} (hc : 0 < c) (k : ℕ) {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hper : ∀ y : ℝ × ℝ, f (y.1 + c, y.2) = f y) (j : Fin 2) (x : ℝ × ℝ) :
    -∫ y in B0579.cell c, f y * (B0579.pd j (fun y => lmK c k (x - y)) y : ℂ) =
      ∫ y in B0579.cell c, (lmK c k (x - y) : ℂ) * LMPd j f y :=
  lm_smooth_ibp' hc hf hper (lmK_test hc k x).1 j

theorem lmJ_divFree {c : ℝ} (hc : 0 < c) (k : ℕ) (f : LMSpField)
    (hsm : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x => f x i))
    (hper : ∀ (x : ℝ × ℝ) (i : Fin 2), f (x.1 + c, x.2) i = f x i) (hL2 : LMCellL2 c f)
    (hdiv : ∀ x : ℝ × ℝ, LMPd 0 (fun y => f y 0) x + LMPd 1 (fun y => f y 1) x = 0)
    (x : ℝ × ℝ) : LMPd 0 (fun y => lmJ c k f y 0) x + LMPd 1 (fun y => lmJ c k f y 1) x = 0 := by
  have e : ∀ (j i : Fin 2), LMPd j (fun y => lmJ c k f y i) x =
      ∫ y in B0579.cell c, (lmK c k (x - y) : ℂ) * LMPd j (fun y => f y i) y := fun j i => by
    have h1 : (fun y => lmJ c k f y i) = lmJs c k (fun y => f y i) := rfl
    rw [h1, lmJs_pd hc k (hL2 i) j x, lm_smooth_ibp hc k (hsm i) (fun y => hper y i) j x]
  have hint : ∀ (j i : Fin 2), Integrable
      (fun y => (lmK c k (x - y) : ℂ) * LMPd j (fun y => f y i) y)
      (volume.restrict (B0579.cell c)) := fun j i => by
    have hcontP : Continuous (LMPd j (fun y => f y i)) := by
      have heq : LMPd j (fun y => f y i) = fun y => fderiv ℝ (fun y => f y i) y (B0579.dir j) :=
        funext fun y => lmPd_eq_fderiv (((hsm i).differentiable (by simp)) y) j
      rw [heq]
      exact ((hsm i).continuous_fderiv (by simp)).clm_apply continuous_const
    have htest := (lmK_test hc k x).1
    obtain ⟨R, hR⟩ := htest.band
    refine lm_integrableOn_band (R := R)
      ((Complex.continuous_ofReal.comp htest.continuous).mul hcontP) fun y hy => ?_
    have : lmK c k (x - y) = 0 := hR y hy
    simp [this]
  rw [e, e, ← integral_add (hint 0 0) (hint 1 1)]
  have hz : ∀ y : ℝ × ℝ, (lmK c k (x - y) : ℂ) * LMPd 0 (fun y => f y 0) y +
      (lmK c k (x - y) : ℂ) * LMPd 1 (fun y => f y 1) y = 0 := fun y => by
    rw [← mul_add, hdiv y, mul_zero]
  simp only [hz, integral_zero]

end UnforcedLeray.Short.IIIa
