import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_3_3

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- A continuous complex function vanishing on the cell outside a compact set is integrable on
the cell. -/
theorem ibpIntegrableC {c : ℝ} {F : ℝ × ℝ → ℂ} (hF : Continuous F) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hv : ∀ x ∈ B0579.cell c, x ∉ K → F x = 0) :
    IntegrableOn F (B0579.cell c) :=
  (hF.continuousOn.integrableOn_compact hK).of_forall_sdiff_eq_zero (B0579.measurableSet_cell c)
    (fun x hx => hv x hx.1 hx.2)

/-- Real product of a continuous function with a cylinder test is integrable on the cell. -/
theorem ibpIntegrableRealC {c : ℝ} {F : ℝ × ℝ → ℝ} (hF : Continuous F)
    {χ : ℝ × ℝ → ℝ} (hχ : B0579.IsCylTest c χ) :
    IntegrableOn (fun x => F x * χ x) (B0579.cell c) := by
  obtain ⟨R, hR⟩ := hχ.vanish
  exact B0579.integrableOn_cell_of_continuous (hF.mul hχ.continuous) (B0579.isCompact_box c R)
    (fun x hx hxK => by simp [hR x hx hxK])

/-- Complex product of a continuous function with a real cylinder test is integrable on the cell. -/
theorem ibpIntegrableCplx {c : ℝ} {F : ℝ × ℝ → ℂ} (hF : Continuous F)
    {χ : ℝ × ℝ → ℝ} (hχ : B0579.IsCylTest c χ) :
    IntegrableOn (fun x => F x * (χ x : ℂ)) (B0579.cell c) := by
  obtain ⟨R, hR⟩ := hχ.vanish
  have hc : Continuous (fun x => (χ x : ℂ)) := Complex.continuous_ofReal.comp hχ.continuous
  exact ibpIntegrableC (hF.mul hc) (B0579.isCompact_box c R)
    (fun x hx hxK => by simp [hR x hx hxK])

/-- Real integration by parts on the cell for a smooth `c`-periodic `u` and a cylinder test `ψ`. -/
theorem ibpRealCell {c : ℝ} {u ψ : ℝ × ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hup : ∀ x : ℝ × ℝ, u (x.1 + c, x.2) = u x) (hψ : B0579.IsCylTest c ψ) (j : Fin 2) :
    ∫ x in B0579.cell c, u x * B0579.pd j ψ x = -∫ x in B0579.cell c, B0579.pd j u x * ψ x := by
  obtain ⟨R, hR⟩ := hψ.band
  have hF : B0579.IsCylTest c (fun x => u x * ψ x) :=
    { smooth := hu.mul hψ.smooth
      periodic := fun x => by simp only [hup x, hψ.periodic x]
      band := ⟨R, fun x hx => by simp [hR x hx]⟩ }
  have hd : Differentiable ℝ u := hu.differentiable (by simp)
  have h0 := B0579.integral_pd_eq_zero hF j
  have e : ∀ x, B0579.pd j (fun y => u y * ψ y) x =
      B0579.pd j u x * ψ x + u x * B0579.pd j ψ x :=
    fun x => B0579.pd_mul hd hψ.differentiable j x
  simp only [e] at h0
  have hcu : Continuous (B0579.pd j u) := by
    have h : ContDiff ℝ ∞ (B0579.pd j u) :=
      ((contDiff_infty_iff_fderiv.1 hu).2).clm_apply contDiff_const
    exact h.continuous
  have hi1 : IntegrableOn (fun x => B0579.pd j u x * ψ x) (B0579.cell c) :=
    ibpIntegrableRealC hcu hψ
  have hi2 : IntegrableOn (fun x => u x * B0579.pd j ψ x) (B0579.cell c) :=
    ibpIntegrableRealC hu.continuous (hψ.pd j)
  rw [integral_add hi1 hi2] at h0
  linarith

/-- The real part of the classical derivative of `f`. -/
theorem reCLM_fderiv_pd {f : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) (k : Fin 2) (x : ℝ × ℝ) :
    B0579.pd k (fun y => (f y).re) x = (pdCx k f x).re := by
  have hd : HasFDerivAt (fun y => (f y).re) (Complex.reCLM.comp (fderiv ℝ f x)) x :=
    Complex.reCLM.hasFDerivAt.comp x (hf x).hasFDerivAt
  unfold B0579.pd pdCx
  rw [hd.fderiv]
  simp

/-- The imaginary part of the classical derivative of `f`. -/
theorem imCLM_fderiv_pd {f : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) (k : Fin 2) (x : ℝ × ℝ) :
    B0579.pd k (fun y => (f y).im) x = (pdCx k f x).im := by
  have hd : HasFDerivAt (fun y => (f y).im) (Complex.imCLM.comp (fderiv ℝ f x)) x :=
    Complex.imCLM.hasFDerivAt.comp x (hf x).hasFDerivAt
  unfold B0579.pd pdCx
  rw [hd.fderiv]
  simp

/-- **Leaf**: a smooth `c`-periodic function `g` has weak cell derivative `pdCx j g` (integration by
parts against a cylinder test, applied to real and imaginary parts). -/
theorem ibpPdCxWeak : UnforcedLeray.Short.IIIa.IbpPdCxWeak := by
  intro c j g hc hg hper
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hgc : Continuous g := hg.continuous
  have hpc : Continuous (pdCx j g) := (contDiff_pdCx hg j).continuous
  have hu : ContDiff ℝ ∞ (fun y => (g y).re) := Complex.reCLM.contDiff.comp hg
  have hv : ContDiff ℝ ∞ (fun y => (g y).im) := Complex.imCLM.contDiff.comp hg
  have hupre : ∀ x : ℝ × ℝ, (fun y => (g y).re) (x.1 + c, x.2) = (fun y => (g y).re) x :=
    fun x => by simp only [hper x]
  have hvpre : ∀ x : ℝ × ℝ, (fun y => (g y).im) (x.1 + c, x.2) = (fun y => (g y).im) x :=
    fun x => by simp only [hper x]
  have hcre : Continuous (B0579.pd j (fun y => (g y).re)) := by
    have e : B0579.pd j (fun y => (g y).re) = fun x => (pdCx j g x).re :=
      funext (reCLM_fderiv_pd hgd j)
    rw [e]
    exact Complex.continuous_re.comp hpc
  have hcim : Continuous (B0579.pd j (fun y => (g y).im)) := by
    have e : B0579.pd j (fun y => (g y).im) = fun x => (pdCx j g x).im :=
      funext (imCLM_fderiv_pd hgd j)
    rw [e]
    exact Complex.continuous_im.comp hpc
  refine ⟨fun ψ hψ => ⟨ibpIntegrableCplx hgc (hψ.pd j), ibpIntegrableCplx hpc hψ⟩, fun ψ hψ => ?_⟩
  have R1 : ∫ x in B0579.cell c, (g x).re * B0579.pd j ψ x =
      -∫ x in B0579.cell c, B0579.pd j (fun y => (g y).re) x * ψ x :=
    ibpRealCell hu hupre hψ j
  have R2 : ∫ x in B0579.cell c, (g x).im * B0579.pd j ψ x =
      -∫ x in B0579.cell c, B0579.pd j (fun y => (g y).im) x * ψ x :=
    ibpRealCell hv hvpre hψ j
  have ptL : ∀ x : ℝ × ℝ, g x * ((B0579.pd j ψ x : ℝ) : ℂ) =
      (((g x).re * B0579.pd j ψ x : ℝ) : ℂ) + (((g x).im * B0579.pd j ψ x : ℝ) : ℂ) * Complex.I := by
    intro x
    conv_lhs => rw [← Complex.re_add_im (g x)]
    push_cast
    ring
  have ptR : ∀ x : ℝ × ℝ, pdCx j g x * ((ψ x : ℝ) : ℂ) =
      (((B0579.pd j (fun y => (g y).re) x * ψ x : ℝ)) : ℂ) +
        (((B0579.pd j (fun y => (g y).im) x * ψ x : ℝ)) : ℂ) * Complex.I := by
    intro x
    rw [reCLM_fderiv_pd hgd j x, imCLM_fderiv_pd hgd j x]
    conv_lhs => rw [← Complex.re_add_im (pdCx j g x)]
    push_cast
    ring
  have iA : IntegrableOn (fun x => (((g x).re * B0579.pd j ψ x : ℝ) : ℂ)) (B0579.cell c) :=
    Integrable.ofReal (ibpIntegrableRealC hu.continuous (hψ.pd j))
  have iB : IntegrableOn (fun x => (((g x).im * B0579.pd j ψ x : ℝ) : ℂ) * Complex.I)
      (B0579.cell c) :=
    Integrable.mul_const (Integrable.ofReal (ibpIntegrableRealC hv.continuous (hψ.pd j))) _
  have iC : IntegrableOn (fun x => (((B0579.pd j (fun y => (g y).re) x * ψ x : ℝ)) : ℂ))
      (B0579.cell c) :=
    Integrable.ofReal (ibpIntegrableRealC hcre hψ)
  have iD : IntegrableOn (fun x => (((B0579.pd j (fun y => (g y).im) x * ψ x : ℝ)) : ℂ) * Complex.I)
      (B0579.cell c) :=
    Integrable.mul_const (Integrable.ofReal (ibpIntegrableRealC hcim hψ)) _
  simp only [ptL, ptR]
  rw [integral_add iA iB, integral_add iC iD, integral_mul_const, integral_mul_const]
  simp only [integral_complex_ofReal]
  rw [R1, R2]
  push_cast
  ring

end UnforcedLeray.Short.IIIa
