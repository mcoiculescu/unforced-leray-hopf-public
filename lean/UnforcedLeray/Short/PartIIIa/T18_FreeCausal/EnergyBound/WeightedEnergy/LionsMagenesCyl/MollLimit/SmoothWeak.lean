import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_3

/-!
# Part III-a, `PartIII-a:T18/3/1/3/3/1` (`MollLimit`): classical derivatives are weak derivatives

Source of record: `the November 2 reference manuscript` lines 3427-3440 and
3541-3552. A smooth `c`-periodic `f` with `f` and `∂_j f` in `L²(cell)` satisfies the weak
identity `∫_cell f ∂_j φ = -∫_cell (∂_j f) φ` for every smooth `c`-periodic `φ` vanishing for
large `|η|`.

Proof: integration by parts on the cell (`Cyl.integral_cell_partialQ_mul` for `j = 0`,
`Cyl.integral_cell_partialEta_mul` for `j = 1`). Integrability of `L²(cell)` fields against
bounded compactly supported (in `η`) continuous functions: they are integrable on the finite
measure set `[-c/2, c/2) × [-R, R]` and vanish outside it.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

lemma lmSW_pd0_eq {g : ℝ × ℝ → ℝ} (hg : Differentiable ℝ g) (x : ℝ × ℝ) :
    B0579.pd 0 g x = Cyl.partialQ g x := by
  rw [Cyl.partialQ_eq_fderiv hg x]
  simp [B0579.pd, B0579.dir]

lemma lmSW_pd1_eq {g : ℝ × ℝ → ℝ} (hg : Differentiable ℝ g) (x : ℝ × ℝ) :
    B0579.pd 1 g x = Cyl.partialEta g x := by
  rw [Cyl.partialEta_eq_fderiv hg x]
  simp [B0579.pd, B0579.dir]

lemma lmSW_re_diff {f : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) :
    Differentiable ℝ (fun y => (f y).re) :=
  fun y => (Complex.reCLM.hasFDerivAt.comp y (hf y).hasFDerivAt).differentiableAt

lemma lmSW_im_diff {f : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) :
    Differentiable ℝ (fun y => (f y).im) :=
  fun y => (Complex.imCLM.hasFDerivAt.comp y (hf y).hasFDerivAt).differentiableAt

lemma lmSW_partialQ_re {f : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) (z : ℝ × ℝ) :
    Cyl.partialQ (fun y => (f y).re) z = (Cyl.partialQ f z).re := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt z.1 (Cyl.hasDerivAt_sliceQ hf z.1 z.2)
  simp only [Complex.reCLM_apply, Prod.mk.eta] at h
  exact h.deriv

lemma lmSW_partialQ_im {f : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) (z : ℝ × ℝ) :
    Cyl.partialQ (fun y => (f y).im) z = (Cyl.partialQ f z).im := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt z.1 (Cyl.hasDerivAt_sliceQ hf z.1 z.2)
  simp only [Complex.imCLM_apply, Prod.mk.eta] at h
  exact h.deriv

lemma lmSW_partialEta_re {f : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) (z : ℝ × ℝ) :
    Cyl.partialEta (fun y => (f y).re) z = (Cyl.partialEta f z).re := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt z.2 (Cyl.hasDerivAt_sliceEta hf z.1 z.2)
  simp only [Complex.reCLM_apply, Prod.mk.eta] at h
  exact h.deriv

lemma lmSW_partialEta_im {f : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) (z : ℝ × ℝ) :
    Cyl.partialEta (fun y => (f y).im) z = (Cyl.partialEta f z).im := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt z.2 (Cyl.hasDerivAt_sliceEta hf z.1 z.2)
  simp only [Complex.imCLM_apply, Prod.mk.eta] at h
  exact h.deriv

/-- `LMPd 0 f = ∂_q f` for a differentiable complex field. -/
lemma lmSW_LMPd0 {f : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) (x : ℝ × ℝ) :
    LMPd 0 f x = Cyl.partialQ f x := by
  unfold LMPd
  rw [lmSW_pd0_eq (lmSW_re_diff hf) x, lmSW_pd0_eq (lmSW_im_diff hf) x,
    lmSW_partialQ_re hf x, lmSW_partialQ_im hf x, mul_comm]
  exact Complex.re_add_im _

/-- `LMPd 1 f = ∂_η f` for a differentiable complex field. -/
lemma lmSW_LMPd1 {f : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) (x : ℝ × ℝ) :
    LMPd 1 f x = Cyl.partialEta f x := by
  unfold LMPd
  rw [lmSW_pd1_eq (lmSW_re_diff hf) x, lmSW_pd1_eq (lmSW_im_diff hf) x,
    lmSW_partialEta_re hf x, lmSW_partialEta_im hf x, mul_comm]
  exact Complex.re_add_im _

lemma lmSW_partialQ_ofReal {φ : ℝ × ℝ → ℝ} (hφ : Differentiable ℝ φ) (z : ℝ × ℝ) :
    Cyl.partialQ (fun y => (φ y : ℂ)) z = ((Cyl.partialQ φ z : ℝ) : ℂ) := by
  have h := (Cyl.hasDerivAt_sliceQ hφ z.1 z.2).ofReal_comp
  exact h.deriv

lemma lmSW_partialEta_ofReal {φ : ℝ × ℝ → ℝ} (hφ : Differentiable ℝ φ) (z : ℝ × ℝ) :
    Cyl.partialEta (fun y => (φ y : ℂ)) z = ((Cyl.partialEta φ z : ℝ) : ℂ) := by
  have h := (Cyl.hasDerivAt_sliceEta hφ z.1 z.2).ofReal_comp
  exact h.deriv

lemma lmSW_partialQ_zero {φ : ℝ × ℝ → ℝ} {R : ℝ} (hR : ∀ y : ℝ × ℝ, R < |y.2| → φ y = 0)
    (x : ℝ × ℝ) (hx : R < |x.2|) : Cyl.partialQ φ x = 0 := by
  have h : (fun q : ℝ => φ (q, x.2)) = fun _ => (0 : ℝ) := funext fun q => hR (q, x.2) hx
  unfold Cyl.partialQ
  rw [h, deriv_const]

lemma lmSW_partialEta_zero {φ : ℝ × ℝ → ℝ} {R : ℝ} (hR : ∀ y : ℝ × ℝ, R < |y.2| → φ y = 0)
    (x : ℝ × ℝ) (hx : R < |x.2|) : Cyl.partialEta φ x = 0 := by
  have hopen : IsOpen {η : ℝ | R < |η|} := isOpen_lt continuous_const continuous_abs
  have hev : (fun η : ℝ => φ (x.1, η)) =ᶠ[𝓝 x.2] (fun _ => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds (show x.2 ∈ {η : ℝ | R < |η|} from hx)] with η hη
    exact hR (x.1, η) hη
  unfold Cyl.partialEta
  rw [hev.deriv_eq, deriv_const]

/-- **Integrability against a compactly supported (in `η`) continuous factor**: an `L²(cell)`
field times a continuous `ψ` vanishing for `|η| > R` is integrable on the cell. -/
lemma lmSW_integrableOn {c R : ℝ} {F ψ : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (B0579.cell c))) (hψc : Continuous ψ)
    (hψR : ∀ x : ℝ × ℝ, R < |x.2| → ψ x = 0) :
    IntegrableOn (fun z => F z * ψ z) (B0579.cell c) := by
  set S : Set (ℝ × ℝ) := Set.Ico (-(c / 2)) (c / 2) ×ˢ Set.Icc (-R) R with hS
  have hSsub : S ⊆ B0579.cell c := fun z hz => ⟨hz.1, Set.mem_univ _⟩
  have hSmeas : MeasurableSet S := measurableSet_Ico.prod measurableSet_Icc
  have hK : IsCompact (Set.Icc (-(c / 2)) (c / 2) ×ˢ Set.Icc (-R) R) :=
    isCompact_Icc.prod isCompact_Icc
  have hSK : S ⊆ Set.Icc (-(c / 2)) (c / 2) ×ˢ Set.Icc (-R) R :=
    Set.prod_mono Set.Ico_subset_Icc_self subset_rfl
  have hSfin : volume S < ⊤ := lt_of_le_of_lt (measure_mono hSK) hK.measure_lt_top
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hψc.continuousOn
  haveI : IsFiniteMeasure (volume.restrict S) := ⟨by rw [Measure.restrict_apply_univ]; exact hSfin⟩
  have hFS : MemLp F 2 (volume.restrict S) := hF.mono_measure (Measure.restrict_mono hSsub le_rfl)
  have hFint : Integrable F (volume.restrict S) := hFS.integrable (by norm_num)
  have hbd : Integrable (fun z => F z * ψ z) (volume.restrict S) := by
    refine Integrable.mono' (hFint.norm.const_mul (max C 0))
      (hFS.aestronglyMeasurable.mul hψc.aestronglyMeasurable) ?_
    refine ae_restrict_of_forall_mem hSmeas (fun z hz => ?_)
    show ‖F z * ψ z‖ ≤ max C 0 * ‖F z‖
    have h1 : ‖ψ z‖ ≤ max C 0 := (hC z (hSK hz)).trans (le_max_left _ _)
    rw [norm_mul, mul_comm (max C 0)]
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  have hind : Integrable (S.indicator (fun z => F z * ψ z)) (volume.restrict (B0579.cell c)) := by
    rw [integrable_indicator_iff hSmeas]
    show Integrable (fun z => F z * ψ z) ((volume.restrict (B0579.cell c)).restrict S)
    rw [Measure.restrict_restrict_of_subset hSsub]
    exact hbd
  show Integrable (fun z => F z * ψ z) (volume.restrict (B0579.cell c))
  refine hind.congr (ae_restrict_of_forall_mem (B0579.measurableSet_cell c) (fun z hz => ?_))
  by_cases hzS : z ∈ S
  · simp [Set.indicator, hzS]
  · have hR : R < |z.2| := by
      by_contra hcon
      push_neg at hcon
      exact hzS ⟨hz.1, abs_le.mp hcon⟩
    simp [Set.indicator, hzS, hψR z hR]

/-- **Smooth periodic fields have weak `η`- and `q`-derivatives** (SP 3427-3440, 3541-3552):
integration by parts on the cell. -/
theorem lmSmoothWeakPd : LMSmoothWeakPd := by
  unfold LMSmoothWeakPd
  intro c hc j f hf hper hL hG
  unfold LMWeakPd
  refine ⟨hL, hG, fun φ hφ hφper hφR => ?_⟩
  obtain ⟨R, hR⟩ := hφR
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hφC : Differentiable ℝ (fun x => (φ x : ℂ)) :=
    fun x => (Complex.ofRealCLM.hasFDerivAt.comp x (hφd x).hasFDerivAt).differentiableAt
  have hψc : Continuous (fun x => (φ x : ℂ)) := Complex.continuous_ofReal.comp hφ.continuous
  have hψR : ∀ x : ℝ × ℝ, R < |x.2| → (φ x : ℂ) = 0 := fun x hx => by
    simp [hR x hx]
  have hpf : Cyl.IsPeriodic c f := hper
  have hper' : Cyl.IsPeriodic c (fun x => (φ x : ℂ)) := by
    intro z
    show ((φ (z.1 + c, z.2) : ℝ) : ℂ) = ((φ z : ℝ) : ℂ)
    rw [hφper z]
  have hcont := Cyl.C1_partial_of_contDiff hφ1
  have hQc : Continuous (fun x => ((Cyl.partialQ φ x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hcont.1
  have hEc : Continuous (fun x => ((Cyl.partialEta φ x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hcont.2
  have hQz : ∀ x : ℝ × ℝ, R < |x.2| → ((Cyl.partialQ φ x : ℝ) : ℂ) = 0 := fun x hx => by
    simp [lmSW_partialQ_zero (fun y hy => hR y hy) x hx]
  have hEz : ∀ x : ℝ × ℝ, R < |x.2| → ((Cyl.partialEta φ x : ℝ) : ℂ) = 0 := fun x hx => by
    simp [lmSW_partialEta_zero (fun y hy => hR y hy) x hx]
  have hh0 : IntegrableOn (fun z => f z * (φ z : ℂ)) (B0579.cell c) :=
    lmSW_integrableOn hL hψc hψR
  have hcell : B0579.cell c = Cyl.cell c := by
    unfold B0579.cell Cyl.cell
    rw [neg_div]
  have hj : j = 0 ∨ j = 1 := by
    fin_cases j <;> simp
  rcases hj with rfl | rfl
  · -- `j = 0`: the `q`-derivative
    have hL' : MemLp (Cyl.partialQ f) 2 (volume.restrict (B0579.cell c)) := by
      have e : Cyl.partialQ f = LMPd 0 f := funext fun x => (lmSW_LMPd0 hfd x).symm
      rw [e]
      exact hG
    have h1 : IntegrableOn (fun z => Cyl.partialQ f z * (φ z : ℂ)) (B0579.cell c) :=
      lmSW_integrableOn hL' hψc hψR
    have h2 : IntegrableOn (fun z => f z * Cyl.partialQ (fun x => (φ x : ℂ)) z)
        (B0579.cell c) := by
      simp only [lmSW_partialQ_ofReal hφd]
      exact lmSW_integrableOn hL hQc hQz
    rw [hcell] at h1 h2
    have IBP := Cyl.integral_cell_partialQ_mul hc hfd hφC hpf hper' h1 h2
    rw [← hcell] at IBP
    simp only [lmSW_partialQ_ofReal hφd] at IBP
    simp only [lmSW_pd0_eq hφd, lmSW_LMPd0 hfd]
    rw [IBP, neg_neg]
  · -- `j = 1`: the `η`-derivative
    have hL' : MemLp (Cyl.partialEta f) 2 (volume.restrict (B0579.cell c)) := by
      have e : Cyl.partialEta f = LMPd 1 f := funext fun x => (lmSW_LMPd1 hfd x).symm
      rw [e]
      exact hG
    have h1 : IntegrableOn (fun z => Cyl.partialEta f z * (φ z : ℂ)) (B0579.cell c) :=
      lmSW_integrableOn hL' hψc hψR
    have h2 : IntegrableOn (fun z => f z * Cyl.partialEta (fun x => (φ x : ℂ)) z)
        (B0579.cell c) := by
      simp only [lmSW_partialEta_ofReal hφd]
      exact lmSW_integrableOn hL hEc hEz
    rw [hcell] at hh0 h1 h2
    have IBP := Cyl.integral_cell_partialEta_mul hfd hφC hh0 h1 h2
    rw [← hcell] at IBP
    simp only [lmSW_partialEta_ofReal hφd] at IBP
    simp only [lmSW_pd1_eq hφd, lmSW_LMPd1 hfd]
    rw [IBP, neg_neg]

end UnforcedLeray.Short.IIIa
