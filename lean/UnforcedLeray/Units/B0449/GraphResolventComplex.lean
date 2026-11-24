import UnforcedLeray.Units.B0449.GraphResolventTest

/-!
# Complex compact tests for the B0449 cutoff resolvent

This leaf lifts the real cutoff graph identity to compactly supported complex Schwartz tests.
The only additional analytic input is local integrability of compact real coefficients against
the actual chart representatives, which follows from their phase-space `L^q` paths.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory SchwartzMap Set
open scoped ENNReal NNReal ContDiff SchwartzMap

namespace UnforcedLeray.B0449

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- A compact real coefficient times any actual chart scalar is integrable. -/
theorem integrable_compact_real_mul_chartJ {ν : ℝ} (hν : 0 < ν) (hq : q ≠ ⊤)
    {f : ℝ × Space → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (g : Yq P q) (τ₀ : ℝ) (e : CVec3) :
    Integrable (fun p => (f p : ℂ) * dotL e (chartJ g ν τ₀ p)) volume := by
  obtain ⟨Rz, hRz⟩ := exists_spaceRadius_support hfc
  let Kt : Set ℝ := Prod.fst '' tsupport f
  have hKt : IsCompact Kt := hfc.isCompact.image continuous_fst
  obtain ⟨Rt, hRt⟩ := hKt.isBounded.subset_closedBall (0 : ℝ)
  have hsupp : Function.support f ⊆ Icc (-Rt) Rt ×ˢ Metric.closedBall (0 : Space) Rz := by
    intro p hp
    have htmem : p.1 ∈ Kt := ⟨p, subset_tsupport f hp, rfl⟩
    have htball := hRt htmem
    have htabs : |p.1| ≤ Rt := by simpa [Real.dist_eq] using Metric.mem_closedBall.mp htball
    exact ⟨abs_le.mp htabs, (hRz hp).2⟩
  have hsuppC : Function.support (fun p => (f p : ℂ)) ⊆
      Icc (-Rt) Rt ×ˢ Metric.closedBall (0 : Space) Rz := by
    intro p hp
    exact hsupp (by simpa using hp)
  obtain ⟨M, hM, hbound⟩ := exists_compactCylinder_bound
    (Complex.continuous_ofReal.comp hf) (hfc.comp_left Complex.ofReal_zero) hsuppC
  have hJ : MeasurableSet (Icc (-Rt) Rt) := measurableSet_Icc
  have hpath := integrableOn_chartLp (ν := ν) (q := q) hq g τ₀ (-Rt) Rt
  exact integrable_scalar_mul_chartJ hν g τ₀ e hJ hpath
    (Complex.continuous_ofReal.comp hf).stronglyMeasurable hM hbound

def reSchwartz (ψ : 𝓢(ℝ × Space, ℂ)) : 𝓢(ℝ × Space, ℝ) :=
  ψ.postcompCLM Complex.reCLM

def imSchwartz (ψ : 𝓢(ℝ × Space, ℂ)) : 𝓢(ℝ × Space, ℝ) :=
  ψ.postcompCLM Complex.imCLM

theorem reSchwartz_apply (ψ : 𝓢(ℝ × Space, ℂ)) (p : ℝ × Space) :
    reSchwartz ψ p = (ψ p).re := by simp [reSchwartz]

theorem imSchwartz_apply (ψ : 𝓢(ℝ × Space, ℂ)) (p : ℝ × Space) :
    imSchwartz ψ p = (ψ p).im := by simp [imSchwartz]

/-- Real projection commutes with a directional derivative of a smooth complex map. -/
theorem fderiv_re_apply {f : ℝ × Space → ℂ} {p v}
    (hf : DifferentiableAt ℝ f p) :
    fderiv ℝ (fun x => (f x).re) p v = (fderiv ℝ f p v).re := by
  have h := (Complex.reCLM.hasFDerivAt.comp p hf.hasFDerivAt).fderiv
  have hv := congrArg (fun L : (ℝ × Space) →L[ℝ] ℝ => L v) h
  simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using hv

theorem fderiv_im_apply {f : ℝ × Space → ℂ} {p v}
    (hf : DifferentiableAt ℝ f p) :
    fderiv ℝ (fun x => (f x).im) p v = (fderiv ℝ f p v).im := by
  have h := (Complex.imCLM.hasFDerivAt.comp p hf.hasFDerivAt).fderiv
  have hv := congrArg (fun L : (ℝ × Space) →L[ℝ] ℝ => L v) h
  simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using hv

def productTimeDerivativeComplex (f : ℝ × Space → ℂ) (p : ℝ × Space) : ℂ :=
  fderiv ℝ f p (1, 0)

def productSpatialLaplacianComplex (f : ℝ × Space → ℂ) (p : ℝ × Space) : ℂ :=
  ∑ i : Fin 3, fderiv ℝ (fun x => fderiv ℝ f x (0, coordinateVector i)) p
    (0, coordinateVector i)

theorem re_productTimeDerivativeComplex (ψ : 𝓢(ℝ × Space, ℂ)) (p : ℝ × Space) :
    productTimeDerivative (reSchwartz ψ) p =
      (productTimeDerivativeComplex ψ p).re := by
  have hψ : DifferentiableAt ℝ (ψ : ℝ × Space → ℂ) p :=
    ((ψ.smooth ⊤).differentiable (by norm_num)).differentiableAt
  change fderiv ℝ (fun x => (ψ x).re) p (1, 0) =
    (fderiv ℝ (ψ : ℝ × Space → ℂ) p (1, 0)).re
  exact fderiv_re_apply (v := (1, 0)) hψ

theorem im_productTimeDerivativeComplex (ψ : 𝓢(ℝ × Space, ℂ)) (p : ℝ × Space) :
    productTimeDerivative (imSchwartz ψ) p =
      (productTimeDerivativeComplex ψ p).im := by
  have hψ : DifferentiableAt ℝ (ψ : ℝ × Space → ℂ) p :=
    ((ψ.smooth ⊤).differentiable (by norm_num)).differentiableAt
  change fderiv ℝ (fun x => (ψ x).im) p (1, 0) =
    (fderiv ℝ (ψ : ℝ × Space → ℂ) p (1, 0)).im
  exact fderiv_im_apply (v := (1, 0)) hψ

theorem re_second_direction {f : ℝ × Space → ℂ} {p v w}
    (hf : ContDiff ℝ ∞ f) :
    fderiv ℝ (fun x => fderiv ℝ (fun y => (f y).re) x v) p w =
      (fderiv ℝ (fun x => fderiv ℝ f x v) p w).re := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfun : (fun x => fderiv ℝ (fun y => (f y).re) x v) =
      (fun x => (fderiv ℝ f x v).re) := by
    funext x
    exact fderiv_re_apply (v := v) (hdiff x)
  rw [hfun]
  let g : ℝ × Space → ℂ := fun x => fderiv ℝ f x v
  have hg : ContDiff ℝ ∞ g := by
    dsimp [g]
    exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact fderiv_re_apply (v := w) ((hg.differentiable (by norm_num)) p)

theorem im_second_direction {f : ℝ × Space → ℂ} {p v w}
    (hf : ContDiff ℝ ∞ f) :
    fderiv ℝ (fun x => fderiv ℝ (fun y => (f y).im) x v) p w =
      (fderiv ℝ (fun x => fderiv ℝ f x v) p w).im := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfun : (fun x => fderiv ℝ (fun y => (f y).im) x v) =
      (fun x => (fderiv ℝ f x v).im) := by
    funext x
    exact fderiv_im_apply (v := v) (hdiff x)
  rw [hfun]
  let g : ℝ × Space → ℂ := fun x => fderiv ℝ f x v
  have hg : ContDiff ℝ ∞ g := by
    dsimp [g]
    exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact fderiv_im_apply (v := w) ((hg.differentiable (by norm_num)) p)

theorem re_productSpatialLaplacianComplex (ψ : 𝓢(ℝ × Space, ℂ)) (p : ℝ × Space) :
    productSpatialLaplacian (reSchwartz ψ) p =
      (productSpatialLaplacianComplex ψ p).re := by
  unfold productSpatialLaplacian productSpatialLaplacianComplex
  calc
    (∑ i : Fin 3, fderiv ℝ (fun x => fderiv ℝ (reSchwartz ψ) x
        (0, coordinateVector i)) p (0, coordinateVector i))
        = ∑ i : Fin 3, (fderiv ℝ (fun x => fderiv ℝ (ψ : ℝ × Space → ℂ) x
          (0, coordinateVector i)) p (0, coordinateVector i)).re := by
          apply Finset.sum_congr rfl
          intro i hi
          change fderiv ℝ (fun x => fderiv ℝ (fun y => (ψ y).re) x
              (0, coordinateVector i)) p (0, coordinateVector i) = _
          exact re_second_direction (f := (ψ : ℝ × Space → ℂ)) (hf := ψ.smooth ⊤)
            (p := p) (v := (0, coordinateVector i)) (w := (0, coordinateVector i))
    _ = (∑ i : Fin 3, fderiv ℝ (fun x => fderiv ℝ (ψ : ℝ × Space → ℂ) x
          (0, coordinateVector i)) p (0, coordinateVector i)).re := by
          change (∑ i : Fin 3, Complex.reCLM (fderiv ℝ (fun x =>
            fderiv ℝ (ψ : ℝ × Space → ℂ) x (0, coordinateVector i)) p
              (0, coordinateVector i))) =
            Complex.reCLM (∑ i : Fin 3, fderiv ℝ (fun x =>
              fderiv ℝ (ψ : ℝ × Space → ℂ) x (0, coordinateVector i)) p
                (0, coordinateVector i))
          rw [map_sum]

theorem im_productSpatialLaplacianComplex (ψ : 𝓢(ℝ × Space, ℂ)) (p : ℝ × Space) :
    productSpatialLaplacian (imSchwartz ψ) p =
      (productSpatialLaplacianComplex ψ p).im := by
  unfold productSpatialLaplacian productSpatialLaplacianComplex
  calc
    (∑ i : Fin 3, fderiv ℝ (fun x => fderiv ℝ (imSchwartz ψ) x
        (0, coordinateVector i)) p (0, coordinateVector i))
        = ∑ i : Fin 3, (fderiv ℝ (fun x => fderiv ℝ (ψ : ℝ × Space → ℂ) x
          (0, coordinateVector i)) p (0, coordinateVector i)).im := by
          apply Finset.sum_congr rfl
          intro i hi
          change fderiv ℝ (fun x => fderiv ℝ (fun y => (ψ y).im) x
              (0, coordinateVector i)) p (0, coordinateVector i) = _
          exact im_second_direction (f := (ψ : ℝ × Space → ℂ)) (hf := ψ.smooth ⊤)
            (p := p) (v := (0, coordinateVector i)) (w := (0, coordinateVector i))
    _ = (∑ i : Fin 3, fderiv ℝ (fun x => fderiv ℝ (ψ : ℝ × Space → ℂ) x
          (0, coordinateVector i)) p (0, coordinateVector i)).im := by
          change (∑ i : Fin 3, Complex.imCLM (fderiv ℝ (fun x =>
            fderiv ℝ (ψ : ℝ × Space → ℂ) x (0, coordinateVector i)) p
              (0, coordinateVector i))) =
            Complex.imCLM (∑ i : Fin 3, fderiv ℝ (fun x =>
              fderiv ℝ (ψ : ℝ × Space → ℂ) x (0, coordinateVector i)) p
                (0, coordinateVector i))
          rw [map_sum]

set_option maxHeartbeats 8000000 in
/-- The actual cutoff graph identities imply the product-coordinate resolvent equation for every
compactly supported complex Schwartz test. -/
theorem chartJ_cutoff_complexTest_resolvent {ν : ℝ} (hν : 0 < ν)
    (hq : q ≠ ⊤) (hq1 : 1 < q) {w a b : Yq P q}
    (hTime : HasPhaseOp driftT w b) (hLap : HasPhaseOp (nuLapT ν) w a)
    (τ₀ : ℝ) (e : CVec3) {ψ : 𝓢(ℝ × Space, ℂ)}
    (hψc : HasCompactSupport (ψ : ℝ × Space → ℂ)) :
    ∫ p : ℝ × Space,
      ((-productTimeDerivativeComplex ψ p - productSpatialLaplacianComplex ψ p + ψ p) *
        ((resolventTimeCutoff p.1 : ℂ) * dotL e (chartJ w ν τ₀ p))) =
    ∫ p, ψ p * ((resolventTimeCutoffDeriv p.1 : ℂ) * dotL e (chartJ w ν τ₀ p) +
      (resolventTimeCutoff p.1 : ℂ) * dotL e (chartJ b ν τ₀ p) -
      (resolventTimeCutoff p.1 : ℂ) * (Real.exp (-p.1) : ℂ) *
        dotL e (chartJ a ν τ₀ p) +
      (resolventTimeCutoff p.1 : ℂ) * dotL e (chartJ w ν τ₀ p)) := by
  let ψR : 𝓢(ℝ × Space, ℝ) := reSchwartz ψ
  let ψI : 𝓢(ℝ × Space, ℝ) := imSchwartz ψ
  let LR : ℝ × Space → ℝ := fun p =>
    -productTimeDerivative ψR p - productSpatialLaplacian ψR p + ψR p
  let LI : ℝ × Space → ℝ := fun p =>
    -productTimeDerivative ψI p - productSpatialLaplacian ψI p + ψI p
  let χ : ℝ → ℝ := resolventTimeCutoff
  let χt : ℝ → ℝ := resolventTimeCutoffDeriv
  let U : ℝ × Space → ℂ := fun p => dotL e (chartJ w ν τ₀ p)
  let B : ℝ × Space → ℂ := fun p => dotL e (chartJ b ν τ₀ p)
  let A : ℝ × Space → ℂ := fun p => dotL e (chartJ a ν τ₀ p)
  let G : ℝ × Space → ℂ := fun p => (χt p.1 : ℂ) * U p +
    (χ p.1 : ℂ) * B p - (χ p.1 : ℂ) * (Real.exp (-p.1) : ℂ) * A p +
    (χ p.1 : ℂ) * U p
  have hψRc : HasCompactSupport ψR := by
    exact hψc.comp_left Complex.zero_re
  have hψIc : HasCompactSupport ψI := by
    exact hψc.comp_left Complex.zero_im
  have hψRs : ContDiff ℝ ∞ ψR := ψR.smooth ⊤
  have hψIs : ContDiff ℝ ∞ ψI := ψI.smooth ⊤
  have hLRcont : Continuous LR := by
    apply Continuous.add
    · exact (contDiff_productTimeDerivative hψRs).continuous.neg.add
        (contDiff_productSpatialLaplacian hψRs).continuous.neg
    · exact hψRs.continuous
  have hLIcont : Continuous LI := by
    apply Continuous.add
    · exact (contDiff_productTimeDerivative hψIs).continuous.neg.add
        (contDiff_productSpatialLaplacian hψIs).continuous.neg
    · exact hψIs.continuous
  have hLRc : HasCompactSupport LR := by
    exact ((hasCompactSupport_productTimeDerivative hψRc).neg.add
      (hasCompactSupport_productSpatialLaplacian hψRc).neg).add hψRc
  have hLIc : HasCompactSupport LI := by
    exact ((hasCompactSupport_productTimeDerivative hψIc).neg.add
      (hasCompactSupport_productSpatialLaplacian hψIc).neg).add hψIc
  have hχcont : Continuous (fun p : ℝ × Space => χ p.1) :=
    continuous_resolventTimeCutoff.comp continuous_fst
  have hχtcont : Continuous (fun p : ℝ × Space => χt p.1) :=
    continuous_resolventTimeCutoffDeriv.comp continuous_fst
  have hExpcont : Continuous (fun p : ℝ × Space => Real.exp (-p.1)) :=
    Real.continuous_exp.comp (continuous_neg.comp continuous_fst)
  have hR := chartJ_cutoff_realTest_resolvent hν hq hq1 hTime hLap τ₀ e
    (ψ := ψR) (by simpa [ψR] using hψRc)
  have hI := chartJ_cutoff_realTest_resolvent hν hq hq1 hTime hLap τ₀ e
    (ψ := ψI) (by simpa [ψI] using hψIc)
  have hLRU : Integrable (fun p => ((LR p : ℝ) : ℂ) *
      ((χ p.1 : ℂ) * U p)) volume := by
    have hcoef : Continuous (fun p => LR p * χ p.1) := hLRcont.mul hχcont
    have hcompact : HasCompactSupport (fun p => LR p * χ p.1) := hLRc.mul_right
    have hbase := integrable_compact_real_mul_chartJ hν hq hcoef hcompact w τ₀ e
    exact hbase.congr (Filter.Eventually.of_forall fun p => by
      simp [U, mul_assoc])
  have hLIU : Integrable (fun p => ((LI p : ℝ) : ℂ) *
      ((χ p.1 : ℂ) * U p)) volume := by
    have hcoef : Continuous (fun p => LI p * χ p.1) := hLIcont.mul hχcont
    have hcompact : HasCompactSupport (fun p => LI p * χ p.1) := hLIc.mul_right
    have hbase := integrable_compact_real_mul_chartJ hν hq hcoef hcompact w τ₀ e
    exact hbase.congr (Filter.Eventually.of_forall fun p => by
      simp [U, mul_assoc])
  have hRrhs : Integrable (fun p => ((ψR p : ℝ) : ℂ) * G p) volume := by
    have h1 : Integrable (fun p => ((ψR p * χt p.1 : ℝ) : ℂ) * U p) volume :=
      integrable_compact_real_mul_chartJ hν hq (hψRs.continuous.mul hχtcont)
        hψRc.mul_right w τ₀ e
    have h2 : Integrable (fun p => ((ψR p * χ p.1 : ℝ) : ℂ) * B p) volume :=
      integrable_compact_real_mul_chartJ hν hq (hψRs.continuous.mul hχcont)
        hψRc.mul_right b τ₀ e
    have h3 : Integrable (fun p =>
        ((ψR p * χ p.1 * Real.exp (-p.1) : ℝ) : ℂ) * A p) volume :=
      integrable_compact_real_mul_chartJ hν hq
        ((hψRs.continuous.mul hχcont).mul hExpcont)
        (hψRc.mul_right.mul_right) a τ₀ e
    have h4 : Integrable (fun p => ((ψR p * χ p.1 : ℝ) : ℂ) * U p) volume :=
      integrable_compact_real_mul_chartJ hν hq (hψRs.continuous.mul hχcont)
        hψRc.mul_right w τ₀ e
    exact (h1.add h2).sub h3 |>.add h4 |>.congr
      (Filter.Eventually.of_forall fun p => by simp [G, U, B, A, ψR, χ, χt]; ring)
  have hIrhs : Integrable (fun p => ((ψI p : ℝ) : ℂ) * G p) volume := by
    have h1 : Integrable (fun p => ((ψI p * χt p.1 : ℝ) : ℂ) * U p) volume :=
      integrable_compact_real_mul_chartJ hν hq (hψIs.continuous.mul hχtcont)
        hψIc.mul_right w τ₀ e
    have h2 : Integrable (fun p => ((ψI p * χ p.1 : ℝ) : ℂ) * B p) volume :=
      integrable_compact_real_mul_chartJ hν hq (hψIs.continuous.mul hχcont)
        hψIc.mul_right b τ₀ e
    have h3 : Integrable (fun p =>
        ((ψI p * χ p.1 * Real.exp (-p.1) : ℝ) : ℂ) * A p) volume :=
      integrable_compact_real_mul_chartJ hν hq
        ((hψIs.continuous.mul hχcont).mul hExpcont)
        (hψIc.mul_right.mul_right) a τ₀ e
    have h4 : Integrable (fun p => ((ψI p * χ p.1 : ℝ) : ℂ) * U p) volume :=
      integrable_compact_real_mul_chartJ hν hq (hψIs.continuous.mul hχcont)
        hψIc.mul_right w τ₀ e
    exact (h1.add h2).sub h3 |>.add h4 |>.congr
      (Filter.Eventually.of_forall fun p => by simp [G, U, B, A, ψI, χ, χt]; ring)
  have hLdecomp : ∀ p, -productTimeDerivativeComplex ψ p -
      productSpatialLaplacianComplex ψ p + ψ p = (LR p : ℂ) + Complex.I * (LI p : ℂ) := by
    intro p
    apply Complex.ext
    · simp [LR, LI, ψR, ψI, re_productTimeDerivativeComplex,
        re_productSpatialLaplacianComplex, reSchwartz_apply]
    · simp [LR, LI, ψR, ψI, im_productTimeDerivativeComplex,
        im_productSpatialLaplacianComplex, imSchwartz_apply]
  have hψdecomp : ∀ p, ψ p = (ψR p : ℂ) + Complex.I * (ψI p : ℂ) := by
    intro p
    apply Complex.ext <;> simp [ψR, ψI, reSchwartz_apply, imSchwartz_apply]
  have hG_eq : ∀ p, G p =
      (χt p.1 : ℂ) * U p + (χ p.1 : ℂ) * B p -
      (χ p.1 : ℂ) * (Real.exp (-p.1) : ℂ) * A p +
      (χ p.1 : ℂ) * U p := by intro p; rfl
  calc
    ∫ p : ℝ × Space,
      ((-productTimeDerivativeComplex ψ p - productSpatialLaplacianComplex ψ p + ψ p) *
        ((χ p.1 : ℂ) * U p))
        = (∫ p, ((LR p : ℝ) : ℂ) * ((χ p.1 : ℂ) * U p)) +
          Complex.I * (∫ p, ((LI p : ℝ) : ℂ) * ((χ p.1 : ℂ) * U p)) := by
          calc
            _ = ∫ p, ((LR p : ℝ) : ℂ) * ((χ p.1 : ℂ) * U p) +
                Complex.I * (((LI p : ℝ) : ℂ) * ((χ p.1 : ℂ) * U p)) := by
                  apply integral_congr_ae
                  filter_upwards [] with p
                  rw [hLdecomp p]
                  ring
            _ = (∫ p, ((LR p : ℝ) : ℂ) * ((χ p.1 : ℂ) * U p)) +
                ∫ p, Complex.I * (((LI p : ℝ) : ℂ) * ((χ p.1 : ℂ) * U p)) :=
                  integral_add hLRU (hLIU.const_mul Complex.I)
            _ = _ := by rw [integral_const_mul]
    _ = (∫ p, ((ψR p : ℝ) : ℂ) * G p) +
          Complex.I * (∫ p, ((ψI p : ℝ) : ℂ) * G p) := by
          rw [← hR, ← hI]
    _ = ∫ p, ψ p * G p := by
          calc
            (∫ p, ((ψR p : ℝ) : ℂ) * G p) +
                Complex.I * (∫ p, ((ψI p : ℝ) : ℂ) * G p) =
                (∫ p, ((ψR p : ℝ) : ℂ) * G p) +
                ∫ p, Complex.I * (((ψI p : ℝ) : ℂ) * G p) := by rw [integral_const_mul]
            _ = ∫ p, ((ψR p : ℝ) : ℂ) * G p +
                Complex.I * (((ψI p : ℝ) : ℂ) * G p) :=
                  (integral_add hRrhs (hIrhs.const_mul Complex.I)).symm
            _ = ∫ p, ψ p * G p := by
                  apply integral_congr_ae
                  filter_upwards [] with p
                  rw [hψdecomp p]
                  ring
    _ = _ := by simpa [G, U, B, A, χ, χt] using rfl

end UnforcedLeray.B0449
