import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1_8
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_1_8.L1

/-!
# `slice_weak_ae`: the weak `y_j`-identity holds for a.e. `τ` (source 2562-2564, phase tests 2525-2531)

Test the weak identity `WeakDyS` against `θ(τ) ψ(y)` with `θ` periodic and smooth, obtain
`∫_{(0,P]} θ(τ) h(τ) dτ = 0` with `h(τ) = ∫_{B(0,R)} (∂_jψ f + ψ Df)(τ,y) dy`, and conclude
`h = 0` a.e. by `ae_zero_of_periodic_tests` (file L1).  Slice integrability of `f`, `Df` (a.e. `τ`)
splits `h(τ)` into the two integrals of the statement.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal
open UnforcedLeray.PhaseSpace
open UnforcedLeray.Cons.C03.Concrete (phaseInt)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem slWeak_radius {E : Type*} [NormedAddCommGroup E]
    (g : UnforcedLeray.Space → E) (hg : HasCompactSupport g) :
    ∃ R : ℝ, ∀ y, R < ‖y‖ → g y = 0 := by
  obtain ⟨R, hR⟩ := hg.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun y hy => ?_⟩
  by_contra hne
  have h1 := hR (subset_tsupport _ hne)
  rw [mem_closedBall_zero_iff] at h1
  linarith

/-- Spatial derivative of the product test `θ(τ) ψ(y)`. -/
theorem slWeak_dy_prod (θ : ℝ → ℂ) (hθ : ContDiff ℝ ∞ θ) (ψ : UnforcedLeray.Space → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (j : Fin 3) (τ : ℝ) (y : UnforcedLeray.Space) :
    dy j (fun x : ℝ × UnforcedLeray.Space => θ x.1 * ((ψ x.2 : ℝ) : ℂ)) (τ, y) =
      θ τ * ((fderiv ℝ ψ y (UnforcedLeray.coordinateVector j) : ℝ) : ℂ) := by
  have hθd : HasDerivAt θ (deriv θ τ) τ := ((hθ.differentiable (by simp)) τ).hasDerivAt
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ y) y := ((hψ.differentiable (by simp)) y).hasFDerivAt
  have hcd : DifferentiableAt ℝ (fun x : ℝ × UnforcedLeray.Space => θ x.1) (τ, y) :=
    ((hθ.differentiable (by simp)).comp differentiable_fst) (τ, y)
  have hdd : DifferentiableAt ℝ (fun x : ℝ × UnforcedLeray.Space => ((ψ x.2 : ℝ) : ℂ)) (τ, y) :=
    (Complex.ofRealCLM.differentiable.comp ((hψ.differentiable (by simp)).comp differentiable_snd))
      (τ, y)
  have hC : fderiv ℝ (fun x : ℝ × UnforcedLeray.Space => θ x.1) (τ, y) (0, UnforcedLeray.coordinateVector j) = 0 := by
    have hfst : HasFDerivAt (Prod.fst : ℝ × UnforcedLeray.Space → ℝ)
        (ContinuousLinearMap.fst ℝ ℝ UnforcedLeray.Space) (τ, y) := hasFDerivAt_fst
    have h := (hθd.hasFDerivAt.comp (τ, y) hfst).fderiv
    rw [show (fun x : ℝ × UnforcedLeray.Space => θ x.1) = θ ∘ Prod.fst from rfl, h]
    simp
  have hsnd : HasFDerivAt (Prod.snd : ℝ × UnforcedLeray.Space → UnforcedLeray.Space)
      (ContinuousLinearMap.snd ℝ ℝ UnforcedLeray.Space) (τ, y) := hasFDerivAt_snd
  have hD : fderiv ℝ (fun x : ℝ × UnforcedLeray.Space => ((ψ x.2 : ℝ) : ℂ)) (τ, y) =
      Complex.ofRealCLM.comp ((fderiv ℝ ψ y).comp (ContinuousLinearMap.snd ℝ ℝ UnforcedLeray.Space)) :=
    (Complex.ofRealCLM.hasFDerivAt.comp (τ, y) (hψd.comp (τ, y) hsnd)).fderiv
  unfold dy
  rw [fderiv_fun_mul hcd hdd, add_apply, smul_apply, smul_apply, hD, hC]
  simp

/-- The phase test `θ(τ) ψ(y)`. -/
theorem slWeak_isPhaseTest (P : ℝ) (θ : ℝ → ℂ) (hθ : ContDiff ℝ ∞ θ) (hθp : ∀ τ, θ (τ + P) = θ τ)
    (ψ : UnforcedLeray.Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) (R : ℝ) (hR : ∀ y, R < ‖y‖ → ψ y = 0) :
    IsPhaseTest P (fun x : ℝ × UnforcedLeray.Space => θ x.1 * ((ψ x.2 : ℝ) : ℂ)) where
  smooth := (hθ.comp contDiff_fst).mul (Complex.ofRealCLM.contDiff.comp (hψ.comp contDiff_snd))
  periodic := fun τ y => by simp only [hθp τ]
  bounded_support := ⟨R, fun τ y hy => by simp [hR y hy]⟩

/-- The spatial integrand `∂_jψ · f + ψ · Df`. -/
def slWeak_G (ψ : UnforcedLeray.Space → ℝ) (j : Fin 3) (f Df : ℝ × UnforcedLeray.Space → ℂ) :
    ℝ × UnforcedLeray.Space → ℂ :=
  fun x => ((fderiv ℝ ψ x.2 (UnforcedLeray.coordinateVector j) : ℝ) : ℂ) * f x +
    ((ψ x.2 : ℝ) : ℂ) * Df x

/-- Phase-cell integral as an iterated phase average (cf. `phaseInt_reduce`). -/
theorem slWeak_phaseInt_eq_cell (P R : ℝ) [Fact (0 < P)] (G : ℝ × UnforcedLeray.Space → ℂ)
    (hsupp : ∀ τ y, R < ‖y‖ → G (τ, y) = 0) (hG : Integrable G (cellMeas P R)) :
    phaseInt P G = P⁻¹ • ∫ x, G x ∂(cellMeas P R) := by
  unfold phaseInt
  congr 1
  rw [cellMeas, integral_prod _ hG]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  symm
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
  rw [hsupp t y (by simpa [not_le] using hy)]

/-- Bounded continuous compactly supported multiplier times an integrable function. -/
theorem slWeak_integrable_mul {μ : Measure UnforcedLeray.Space} (g : UnforcedLeray.Space → ℂ)
    (hg : Continuous g) (hgc : HasCompactSupport g) {F : UnforcedLeray.Space → ℂ}
    (hF : Integrable F μ) : Integrable (fun y => g y * F y) μ := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  exact hF.bdd_mul hg.aestronglyMeasurable (Eventually.of_forall fun y => hC y)

theorem slice_weak_ae (P : ℝ) [Fact (0 < P)] (j : Fin 3) (f Df : ℝ × UnforcedLeray.Space → ℂ)
    (hf : MemLpLoc P f 1) (hDf : MemLpLoc P Df 1) (hW : WeakDyS P j f Df)
    (ψ : UnforcedLeray.Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    ∀ᵐ τ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) P)),
      ∫ z, fderiv ℝ ψ z (UnforcedLeray.coordinateVector j) * f (τ, z) =
        -∫ z, (ψ z : ℂ) * Df (τ, z) := by
  have hP : 0 < P := Fact.out
  obtain ⟨R1, hR1⟩ := slWeak_radius ψ hψc
  have hg1c : HasCompactSupport
      (fun y : UnforcedLeray.Space => fderiv ℝ ψ y (UnforcedLeray.coordinateVector j)) :=
    hψc.fderiv_apply (𝕜 := ℝ) (UnforcedLeray.coordinateVector j)
  obtain ⟨R2, hR2⟩ := slWeak_radius _ hg1c
  obtain ⟨R, hRa, hRb⟩ : ∃ R : ℝ, R1 ≤ R ∧ R2 ≤ R := ⟨max R1 R2, le_max_left _ _, le_max_right _ _⟩
  have hψR : ∀ y, R < ‖y‖ → ψ y = 0 := fun y hy => hR1 y (lt_of_le_of_lt hRa hy)
  have hg1R : ∀ y, R < ‖y‖ → fderiv ℝ ψ y (UnforcedLeray.coordinateVector j) = 0 :=
    fun y hy => hR2 y (lt_of_le_of_lt hRb hy)
  have hfI : Integrable f (cellMeas P R) := memLp_one_iff_integrable.1 (hf R)
  have hDfI : Integrable Df (cellMeas P R) := memLp_one_iff_integrable.1 (hDf R)
  -- the periodic test argument
  have key : ∀ θ : ℝ → ℂ, ContDiff ℝ ∞ θ → (∀ τ, θ (τ + P) = θ τ) →
      Integrable (fun x : ℝ × UnforcedLeray.Space => θ x.1 * slWeak_G ψ j f Df x) (cellMeas P R) ∧
      ∫ x, θ x.1 * slWeak_G ψ j f Df x ∂(cellMeas P R) = 0 := by
    intro θ hθ hθp
    have hφ := slWeak_isPhaseTest P θ hθ hθp ψ hψ R hψR
    have hdφ := hφ.dy j
    have ia := integrable_phase_mul P R _ hdφ f hfI
    have ib := integrable_phase_mul P R _ hφ Df hDfI
    have hsum : ∀ x : ℝ × UnforcedLeray.Space,
        dy j (fun x : ℝ × UnforcedLeray.Space => θ x.1 * ((ψ x.2 : ℝ) : ℂ)) x * f x +
          (θ x.1 * ((ψ x.2 : ℝ) : ℂ)) * Df x = θ x.1 * slWeak_G ψ j f Df x := by
      rintro ⟨τ, y⟩
      rw [slWeak_dy_prod θ hθ ψ hψ j τ y]
      simp only [slWeak_G]
      ring
    have hint : Integrable (fun x => θ x.1 * slWeak_G ψ j f Df x) (cellMeas P R) := by
      refine (ia.add ib).congr (Eventually.of_forall fun x => ?_)
      exact hsum x
    refine ⟨hint, ?_⟩
    have hsA : ∀ τ y, R < ‖y‖ → dy j (fun x : ℝ × UnforcedLeray.Space => θ x.1 * ((ψ x.2 : ℝ) : ℂ)) (τ, y) * f (τ, y) = 0 := by
      intro τ y hy
      rw [slWeak_dy_prod θ hθ ψ hψ j τ y, hg1R y hy]
      simp
    have hsB : ∀ τ y, R < ‖y‖ → (θ τ * ((ψ y : ℝ) : ℂ)) * Df (τ, y) = 0 := by
      intro τ y hy
      simp [hψR y hy]
    have eA := slWeak_phaseInt_eq_cell P R _ hsA ia
    have eB := slWeak_phaseInt_eq_cell P R _ hsB ib
    have hW' := hW _ hφ
    rw [eA, eB] at hW'
    have hsumI : ∫ x, θ x.1 * slWeak_G ψ j f Df x ∂(cellMeas P R) =
        (∫ x, dy j (fun x : ℝ × UnforcedLeray.Space => θ x.1 * ((ψ x.2 : ℝ) : ℂ)) x * f x ∂(cellMeas P R)) +
          ∫ x, θ x.1 * ((ψ x.2 : ℝ) : ℂ) * Df x ∂(cellMeas P R) := by
      rw [← integral_add ia ib]
      exact integral_congr_ae (Eventually.of_forall fun x => (hsum x).symm)
    rw [hsumI]
    set A := ∫ x, dy j (fun x : ℝ × UnforcedLeray.Space => θ x.1 * ((ψ x.2 : ℝ) : ℂ)) x * f x ∂(cellMeas P R) with hA
    set B := ∫ x, θ x.1 * ((ψ x.2 : ℝ) : ℂ) * Df x ∂(cellMeas P R) with hB
    have h3 : P⁻¹ • (A + B) = 0 := by rw [smul_add, hW', neg_add_cancel]
    exact (smul_eq_zero.1 h3).resolve_left (inv_ne_zero hP.ne')
  have hG1 : Integrable (slWeak_G ψ j f Df) (cellMeas P R) := by
    have := (key (fun _ => (1:ℂ)) contDiff_const (fun _ => rfl)).1
    simpa only [one_mul] using this
  have hG1' := hG1
  rw [cellMeas] at hG1'
  have hint1 : IntegrableOn (fun τ : ℝ => ∫ y in Metric.closedBall (0 : UnforcedLeray.Space) R,
      slWeak_G ψ j f Df (τ, y)) (Ioc (0 : ℝ) P) :=
    hG1'.integral_prod_left
  have h0 : ∀ θ : ℝ → ℂ, ContDiff ℝ ∞ θ → (∀ τ, θ (τ + P) = θ τ) →
      ∫ τ in Ioc (0 : ℝ) P, θ τ * (∫ y in Metric.closedBall (0 : UnforcedLeray.Space) R,
        slWeak_G ψ j f Df (τ, y)) = 0 := by
    intro θ hθ hθp
    obtain ⟨hint, hz⟩ := key θ hθ hθp
    have hEq : ∫ x, θ x.1 * slWeak_G ψ j f Df x ∂(cellMeas P R) =
        ∫ τ in Ioc (0 : ℝ) P, θ τ * (∫ y in Metric.closedBall (0 : UnforcedLeray.Space) R,
          slWeak_G ψ j f Df (τ, y)) := by
      rw [cellMeas, integral_prod _ hint]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp [integral_const_mul]
    rw [← hEq]
    exact hz
  have hae := ae_zero_of_periodic_tests P (fun τ : ℝ => ∫ y in Metric.closedBall (0 : UnforcedLeray.Space) R,
    slWeak_G ψ j f Df (τ, y)) hint1 h0
  have hsf : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)),
      Integrable (fun y : UnforcedLeray.Space => f (τ, y)) (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R)) := by
    have := hfI
    rw [cellMeas] at this
    exact this.prod_right_ae
  have hsD : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)),
      Integrable (fun y : UnforcedLeray.Space => Df (τ, y)) (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R)) := by
    have := hDfI
    rw [cellMeas] at this
    exact this.prod_right_ae
  have hg1cont : Continuous (fun y : UnforcedLeray.Space => ((fderiv ℝ ψ y (UnforcedLeray.coordinateVector j) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hg1cc : HasCompactSupport (fun y : UnforcedLeray.Space => ((fderiv ℝ ψ y (UnforcedLeray.coordinateVector j) : ℝ) : ℂ)) :=
    hg1c.comp_left Complex.ofReal_zero
  have hψcont : Continuous (fun y : UnforcedLeray.Space => ((ψ y : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hψ.continuous
  have hψcc : HasCompactSupport (fun y : UnforcedLeray.Space => ((ψ y : ℝ) : ℂ)) :=
    hψc.comp_left Complex.ofReal_zero
  filter_upwards [hae, hsf, hsD] with τ hz hf1 hD1
  have int1 : Integrable (fun y : UnforcedLeray.Space => ((fderiv ℝ ψ y (UnforcedLeray.coordinateVector j) : ℝ) : ℂ) * f (τ, y))
      (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R)) :=
    slWeak_integrable_mul _ hg1cont hg1cc hf1
  have int2 : Integrable (fun y : UnforcedLeray.Space => ((ψ y : ℝ) : ℂ) * Df (τ, y))
      (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R)) :=
    slWeak_integrable_mul _ hψcont hψcc hD1
  have e1 : ∫ y in Metric.closedBall (0 : UnforcedLeray.Space) R, ((fderiv ℝ ψ y (UnforcedLeray.coordinateVector j) : ℝ) : ℂ) * f (τ, y) =
      ∫ y, ((fderiv ℝ ψ y (UnforcedLeray.coordinateVector j) : ℝ) : ℂ) * f (τ, y) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      have hy' : R < ‖y‖ := by simpa [not_le] using hy
      simp [hg1R y hy']
  have e2 : ∫ y in Metric.closedBall (0 : UnforcedLeray.Space) R, ((ψ y : ℝ) : ℂ) * Df (τ, y) =
      ∫ y, ((ψ y : ℝ) : ℂ) * Df (τ, y) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      have hy' : R < ‖y‖ := by simpa [not_le] using hy
      simp [hψR y hy']
  have hz' : (∫ y in Metric.closedBall (0 : UnforcedLeray.Space) R, ((fderiv ℝ ψ y (UnforcedLeray.coordinateVector j) : ℝ) : ℂ) * f (τ, y)) +
      (∫ y in Metric.closedBall (0 : UnforcedLeray.Space) R, ((ψ y : ℝ) : ℂ) * Df (τ, y)) = 0 := by
    rw [← integral_add int1 int2]
    exact hz
  rw [e1, e2] at hz'
  exact eq_neg_of_add_eq_zero_left hz'

end UnforcedLeray.Short.PartIIIb.Concrete
