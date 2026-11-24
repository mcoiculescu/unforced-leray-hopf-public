import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Defs
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductHilbert
import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators

/-!
# `GEQIbp` helpers: integrability on the phase cell and linearity of `phaseInt`

Helper file for `GEQIbp.lean` (source 2525-2533). Phase tests are bounded and supported in
`‖y‖ ≤ R`, so a test times a product of two `L²`-locally functions is integrable on the cell.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF advT phaseInt phaseCell)

theorem phaseCell_measurableSet (P : ℝ) : MeasurableSet (phaseCell P) :=
  measurableSet_Ioc.prod MeasurableSet.univ

/-- Lowering the exponent of a local `L^q` bound on a finite measure set. -/
theorem memLpLoc_mono {P : ℝ} {f : ℝ × UnforcedLeray.Space → ℂ} {q r : ENNReal}
    (hq : MemLpLoc P f q) (hr : r ≤ q) : MemLpLoc P f r := by
  intro R
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) P)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  exact (hq R).mono_exponent hr

/-- A bounded phase test times a product of two locally `L²` functions is integrable on the
phase cell. -/
theorem integrable_test_mul2 {P : ℝ} [Fact (0 < P)] {ψ f g : ℝ × UnforcedLeray.Space → ℂ}
    (hψ : IsPhaseTest P ψ) (hf : MemLpLoc P f 2) (hg : MemLpLoc P g 2) :
    Integrable (fun x => ψ x * (f x * g x)) (volume.restrict (phaseCell P)) := by
  obtain ⟨R, hR⟩ := hψ.bounded_support
  set K : Set (ℝ × UnforcedLeray.Space) :=
    Ioc (0 : ℝ) P ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) R with hKdef
  have hKm : MeasurableSet K := measurableSet_Ioc.prod measurableSet_closedBall
  have hKc : K ⊆ phaseCell P := fun x hx => ⟨hx.1, trivial⟩
  obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ K, ‖ψ x‖ ≤ C := by
    have hcpt : IsCompact (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) R) :=
      isCompact_Icc.prod (isCompact_closedBall _ _)
    obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hψ.continuous.continuousOn
    exact ⟨C, fun x hx => hC x ⟨Ioc_subset_Icc_self hx.1, hx.2⟩⟩
  have hμK : volume.restrict K = (volume.restrict (Ioc (0 : ℝ) P)).prod
      (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R)) := by
    rw [hKdef, Measure.volume_eq_prod, Measure.prod_restrict]
  have hae : (fun x => ψ x * (f x * g x)) =ᵐ[volume.restrict (phaseCell P)]
      K.indicator (fun x => ψ x * (f x * g x)) := by
    refine ae_restrict_of_forall_mem (phaseCell_measurableSet P) ?_
    intro x hx
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem hxK]
    · rw [Set.indicator_of_notMem hxK]
      have hψ0 : ψ x = 0 := by
        obtain ⟨τ, y⟩ := x
        rcases lt_or_ge R ‖y‖ with h | h
        · exact hR τ y h
        · exact absurd ⟨hx.1, by rw [Metric.mem_closedBall, dist_zero_right]; exact h⟩ hxK
      show ψ x * (f x * g x) = 0
      rw [hψ0, zero_mul]
  have hInd : Integrable (K.indicator (fun x => ψ x * (f x * g x)))
      (volume.restrict (phaseCell P)) := by
    rw [integrable_indicator_iff hKm, IntegrableOn, Measure.restrict_restrict hKm,
      Set.inter_eq_left.mpr hKc, hμK]
    have hfg : Integrable (f * g) ((volume.restrict (Ioc (0 : ℝ) P)).prod
        (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R))) :=
      MemLp.integrable_mul (hf R) (hg R)
    refine Integrable.bdd_mul (c := C) hfg hψ.continuous.aestronglyMeasurable ?_
    rw [← hμK]
    exact ae_restrict_of_forall_mem hKm (fun x hx => hC x hx)
  exact hInd.congr hae.symm

/-- `phaseInt` of an integrable function as an integral over the phase cell. -/
theorem phaseInt_eq_cell {P : ℝ} [Fact (0 < P)] {F : ℝ × UnforcedLeray.Space → ℂ}
    (hF : Integrable F (volume.restrict (phaseCell P))) :
    phaseInt P F = P⁻¹ • ∫ x, F x ∂(volume.restrict (phaseCell P)) := by
  let μ : Measure ℝ := volume
  let ν : Measure UnforcedLeray.Space := volume
  have hprod : (volume : Measure (ℝ × UnforcedLeray.Space)).restrict (phaseCell P) =
      (μ.restrict (Ioc (0 : ℝ) P)).prod ν := by
    simpa [μ, ν, phaseCell, Measure.volume_eq_prod] using
      (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
        (ν := (volume : Measure UnforcedLeray.Space)) (Ioc (0 : ℝ) P)).symm
  rw [hprod] at hF ⊢
  unfold phaseInt
  rw [integral_prod F hF]

/-- Additivity of `phaseInt` over two integrable integrands. -/
theorem phaseInt_add_cell {P : ℝ} [Fact (0 < P)] {F G : ℝ × UnforcedLeray.Space → ℂ}
    (hF : Integrable F (volume.restrict (phaseCell P)))
    (hG : Integrable G (volume.restrict (phaseCell P))) :
    phaseInt P (fun x => F x + G x) = phaseInt P F + phaseInt P G := by
  have hFG : Integrable (fun x => F x + G x) (volume.restrict (phaseCell P)) := hF.add hG
  rw [phaseInt_eq_cell hFG, phaseInt_eq_cell hF, phaseInt_eq_cell hG,
    integral_add hF hG, smul_add]

/-- Finite additivity of `phaseInt`. -/
theorem phaseInt_sum_cell {P : ℝ} [Fact (0 < P)] {ι : Type*} (s : Finset ι)
    {F : ι → ℝ × UnforcedLeray.Space → ℂ}
    (hF : ∀ i ∈ s, Integrable (F i) (volume.restrict (phaseCell P))) :
    phaseInt P (fun x => ∑ i ∈ s, F i x) = ∑ i ∈ s, phaseInt P (F i) := by
  have hfun : (fun x => ∑ i ∈ s, F i x) = ∑ i ∈ s, F i := by
    funext x
    simp [Finset.sum_apply]
  rw [hfun]
  rw [phaseInt_eq_cell (integrable_finsetSum' s hF)]
  simp only [Finset.sum_apply]
  rw [integral_finset_sum s hF, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [phaseInt_eq_cell (hF i hi)]


/-- Pointwise sums of integrable functions on the phase cell. -/
theorem integrable_sum_cell {P : ℝ} {ι : Type*} (s : Finset ι)
    {F : ι → ℝ × UnforcedLeray.Space → ℂ}
    (hF : ∀ i ∈ s, Integrable (F i) (volume.restrict (phaseCell P))) :
    Integrable (fun x => ∑ i ∈ s, F i x) (volume.restrict (phaseCell P)) := by
  have hfun : (fun x => ∑ i ∈ s, F i x) = ∑ i ∈ s, F i := by
    funext x
    simp [Finset.sum_apply]
  rw [hfun]
  exact integrable_finsetSum' s hF

/-- `phaseInt` of a negated integrand. -/
theorem phaseInt_neg_cell {P : ℝ} [Fact (0 < P)] {F : ℝ × UnforcedLeray.Space → ℂ}
    (hF : Integrable F (volume.restrict (phaseCell P))) :
    phaseInt P (fun x => -F x) = -phaseInt P F := by
  have hF' : Integrable (fun x => -F x) (volume.restrict (phaseCell P)) := hF.neg
  rw [phaseInt_eq_cell hF', phaseInt_eq_cell hF, integral_neg, smul_neg]

/-- A phase test times a sum of two products of locally `L²` functions. -/
theorem integrable_test_mul_sum2 {P : ℝ} [Fact (0 < P)] {ψ a b c d : ℝ × UnforcedLeray.Space → ℂ}
    (hψ : IsPhaseTest P ψ) (ha : MemLpLoc P a 2) (hb : MemLpLoc P b 2)
    (hc : MemLpLoc P c 2) (hd : MemLpLoc P d 2) :
    Integrable (fun x => ψ x * (a x * b x + c x * d x)) (volume.restrict (phaseCell P)) := by
  have h := (integrable_test_mul2 hψ ha hb).add (integrable_test_mul2 hψ hc hd)
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply, mul_add]

/-- A phase test times a sum of four products of locally `L²` functions. -/
theorem integrable_test_mul_sum4 {P : ℝ} [Fact (0 < P)]
    {ψ a b c d e f g h : ℝ × UnforcedLeray.Space → ℂ}
    (hψ : IsPhaseTest P ψ) (ha : MemLpLoc P a 2) (hb : MemLpLoc P b 2)
    (hc : MemLpLoc P c 2) (hd : MemLpLoc P d 2) (he : MemLpLoc P e 2)
    (hf : MemLpLoc P f 2) (hg : MemLpLoc P g 2) (hh : MemLpLoc P h 2) :
    Integrable (fun x => ψ x * (a x * b x + c x * d x + e x * f x + g x * h x))
      (volume.restrict (phaseCell P)) := by
  have h1 := integrable_test_mul_sum2 hψ ha hb hc hd
  have h2 := integrable_test_mul_sum2 hψ he hf hg hh
  have h := h1.add h2
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply]
  ring

/-- Coordinates of a phase test are phase tests. -/
theorem isPhaseTest_comp_coord {P : ℝ} {Φ : ℝ × UnforcedLeray.Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (i : Fin 3) : IsPhaseTest P (fun x => Φ x i) := by
  have h := hΦ.clm_comp ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ)
  simpa using h

/-- The `y`-derivative commutes with taking a coordinate. -/
theorem dy_comp_coord {V : ℝ × UnforcedLeray.Space → CVec3} (hV : ContDiff ℝ ∞ V)
    (k i : Fin 3) (x : ℝ × UnforcedLeray.Space) :
    dy k (fun y => V y i) x = dy k V x i := by
  unfold dy
  let L : CVec3 →L[ℝ] ℂ := (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ
  have hfun : (fun y => V y i) = fun y => L (V y) := by
    funext y
    simp [L]
  have hd : HasFDerivAt (fun y => L (V y)) (L.comp (fderiv ℝ V x)) x :=
    L.hasFDerivAt.comp x (hV.differentiable (by simp) x).hasFDerivAt
  rw [hfun, hd.fderiv]
  simp [L]

end UnforcedLeray.Short.PartIIIb.Concrete
