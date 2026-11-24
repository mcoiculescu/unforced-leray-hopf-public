import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3
import UnforcedLeray.Units.B0414.PhaseOrthogonal
import UnforcedLeray.Units.B0005.Bridge.Solenoidal

/-!
# `PartII-b:T10/org/3/1`: distributionally solenoidal fields of `Y_2` are fixed by `𝐏`

Source `the November 2 reference manuscript` lines 1358-1361, 1498-1500.

Proof. Let `a ∈ Y_2` be phase-solenoidal. The argument of
`UnforcedLeray.B0005.IsY2.ae_isSolenoidal_of_phase` (Bridge/Solenoidal.lean, `Ksol` section)
uses only the phase-test identity and the local integrability of `t ↦ a(t mod P)`, not the real
structure of the field. Its generalisation to an arbitrary `a` (lemmas `ysf_integral_mem_Ksol`,
`ysf_ae_mem_Ksol`) gives `a(τ) ∈ Ksol` for a.e. `τ`. Haar-a.e. transfer from the line
(`ysf_ae_circle_mem`), and `Ksol` membership gives distributional solenoidality of each slice
(`ysf_isSolenoidalC_of_mem_Ksol`). Then `mem_solenoidalY_iff` and `lerayY_two_eq_self_iff`
give `𝐏 a = a`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.B0005

/-- Generalised `integral_mem_Ksol`: for any phase-solenoidal `a ∈ Y_2`. -/
theorem ysf_integral_mem_Ksol {P : ℝ} [hT : Fact (0 < P)] (a : Yq P 2)
    (h : IsPhaseSolenoidal a) {θ : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) :
    ∫ t, θ t • (a (t : AddCircle P) : Lp CVec3 2 (volume : Measure Space)) ∈ Ksol := by
  intro φ hφ
  have hloc := locallyIntegrable_comp_mk a
  have hint : Integrable (fun t => θ t • (a (t : AddCircle P) :
      Lp CVec3 2 (volume : Measure Space))) :=
    hloc.integrable_smul_left_of_hasCompactSupport hθ.continuous hθc
  have e1 : ellS hφ (∫ t, θ t • (a (t : AddCircle P) : Lp CVec3 2 (volume : Measure Space))) =
      ∫ t, θ t • ellS hφ (a (t : AddCircle P)) := by
    have := ((ellS hφ).restrictScalars ℝ).integral_comp_comm hint
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul_of_tower]
      at this
    exact this.symm
  rw [e1]
  obtain ⟨A, B, hAB, hθAB⟩ := exists_Icc_of_hasCompactSupport hθc
  have hΨ0 := isPhaseTest_scalarTest hθ hφ
  have hΨT : TimeSupp A B (scalarTest θ φ) := fun τ y hτ => by simp [scalarTest, hθAB τ hτ]
  have hG0 : IsPhaseTest 0 (gradT (scalarTest θ φ)) := hΨ0.gradT
  have hGT : TimeSupp A B (gradT (scalarTest θ φ)) := fun τ y hτ => by
    simp [gradT, timeSupp_dy hΨT _ τ y hτ]
  have hz := h _ (isPhaseTest_perT hT.out hΨT hΨ0)
  rw [gradT_perT hT.out hΨT hΨ0.smooth, PhaseTrace.phasePair_perT hG0 hAB hGT] at hz
  have hz' : ∫ t, pairH hG0 a t = 0 := by
    rcases smul_eq_zero.mp hz with h0 | h0
    · exact absurd h0 (inv_ne_zero hT.out.ne')
    · exact h0
  rw [← hz']
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [pairH_eq, ellS_apply, Complex.real_smul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [dotL_gradT_scalarTest hθ hφ.smooth]

/-- Generalised `ae_mem_Ksol`: for any phase-solenoidal `a ∈ Y_2`, `a(t) ∈ Ksol` for a.e. `t`. -/
theorem ysf_ae_mem_Ksol {P : ℝ} [Fact (0 < P)] (a : Yq P 2) (h : IsPhaseSolenoidal a) :
    ∀ᵐ t : ℝ, (a (t : AddCircle P) : Lp CVec3 2 (volume : Measure Space)) ∈ Ksol := by
  have hloc := locallyIntegrable_comp_mk a
  set C := compKsol.restrictScalars ℝ with hC
  have hlocC : LocallyIntegrable (fun t : ℝ => C (a (t : AddCircle P))) volume :=
    locallyIntegrableOn_univ.mp (C.locallyIntegrableOn_comp (locallyIntegrableOn_univ.mpr hloc))
  have hzero : ∀ᵐ t : ℝ, C (a (t : AddCircle P)) = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocC fun θ hθ hθc => ?_
    have hint : Integrable (fun t => θ t • (a (t : AddCircle P) :
        Lp CVec3 2 (volume : Measure Space))) :=
      hloc.integrable_smul_left_of_hasCompactSupport hθ.continuous hθc
    have := C.integral_comp_comm hint
    simp only [ContinuousLinearMap.map_smul] at this
    rw [this, hC, ContinuousLinearMap.coe_restrictScalars', compKsol_eq_zero_iff]
    exact ysf_integral_mem_Ksol a h hθ hθc
  filter_upwards [hzero] with t ht
  exact (compKsol_eq_zero_iff _).mp ht

/-- Haar-a.e. transfer from the line: if `a(t mod P) ∈ S` for a.e. `t ∈ ℝ`, with `S` closed and
nonempty, then `a(τ) ∈ S` for haar-a.e. `τ` on the circle. The membership is encoded through the
real-valued continuous function `infDist · S`, so that measurability is available. -/
theorem ysf_ae_circle_mem {P : ℝ} [Fact (0 < P)] (a : Yq P 2)
    {S : Set (Lp CVec3 2 (volume : Measure Space))} (hS : IsClosed S) (hne : S.Nonempty)
    (h : ∀ᵐ t : ℝ, (a (t : AddCircle P) : Lp CVec3 2 (volume : Measure Space)) ∈ S) :
    ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), a τ ∈ S := by
  set g : AddCircle P → Lp CVec3 2 (volume : Measure Space) :=
    (Lp.aestronglyMeasurable a).mk (a : AddCircle P → Lp CVec3 2 (volume : Measure Space))
    with hgdef
  have hg : (a : AddCircle P → Lp CVec3 2 (volume : Measure Space)) =ᵐ[AddCircle.haarAddCircle (T := P)] g :=
    (Lp.aestronglyMeasurable a).ae_eq_mk
  have hgm : StronglyMeasurable g := (Lp.aestronglyMeasurable a).stronglyMeasurable_mk
  have hGm : StronglyMeasurable (fun τ : AddCircle P => Metric.infDist (g τ) S) :=
    (Metric.continuous_infDist_pt S).comp_stronglyMeasurable hgm
  have hmeasS : MeasurableSet {τ : AddCircle P | Metric.infDist (g τ) S = 0} :=
    hGm.measurable (measurableSet_singleton (0 : ℝ))
  have hmp := AddCircle.measurePreserving_mk P 0
  have h5 : ∀ᵐ t : ℝ, Metric.infDist (a (t : AddCircle P) : Lp CVec3 2 (volume : Measure Space)) S = 0 := by
    filter_upwards [h] with t ht
    exact (hS.mem_iff_infDist_zero hne).mp ht
  have hL : ∀ᵐ t : ℝ, Metric.infDist (g (t : AddCircle P)) S = 0 := by
    filter_upwards [PhaseTrace.ae_comp_mk (p := fun x => (a x : Lp CVec3 2 (volume : Measure Space)) = g x) hg, h5] with t h1 h2
    rw [← h1]
    exact h2
  have hmapped : ∀ᵐ x ∂(Measure.map (QuotientAddGroup.mk : ℝ → AddCircle P)
      (volume.restrict (Ioc (0 : ℝ) (0 + P)))), Metric.infDist (g x) S = 0 := by
    rw [ae_map_iff hmp.measurable.aemeasurable hmeasS]
    exact ae_restrict_of_ae hL
  have h3 : ∀ᵐ x ∂(volume : Measure (AddCircle P)), Metric.infDist (g x) S = 0 := by
    rwa [hmp.map_eq] at hmapped
  have hc : ENNReal.ofReal P ≠ 0 := (ENNReal.ofReal_pos.mpr (Fact.out : (0 : ℝ) < P)).ne'
  have h4 : ∀ᵐ x ∂(AddCircle.haarAddCircle (T := P)), Metric.infDist (g x) S = 0 := by
    rw [AddCircle.volume_eq_smul_haarAddCircle] at h3
    have h6 := Measure.ae_smul_measure h3 ((ENNReal.ofReal P)⁻¹)
    rwa [smul_smul, ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top, one_smul] at h6
  filter_upwards [hg, h4] with τ h1 h2
  rw [h1]
  exact (hS.mem_iff_infDist_zero hne).mpr h2

/-- An element of `Ksol` has distributionally solenoidal components. -/
theorem ysf_isSolenoidalC_of_mem_Ksol {v : Lp CVec3 2 (volume : Measure Space)}
    (hv : v ∈ Ksol) : UnforcedLeray.B0414.IsSolenoidalC (v : Space → CVec3) := by
  have hdot : ∀ (φ : Space → ℝ) (y : Space) (w : CVec3),
      dotL (gvec φ y) w = ∑ i : Fin 3, w i * (spatialTestDerivative i φ y : ℂ) := by
    intro φ y w
    rw [dotL_apply]
    simp [gvec, Pi.single_apply, mul_comm]
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩
  · refine integrable_finsetSum _ fun i _ => ?_
    have hm : MemLp (fun x => (v : Space → CVec3) x i) 2 (volume : Measure Space) := by
      have := (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).comp_memLp' (Lp.memLp v)
      exact this
    have hder : MemLp (fun x => (spatialTestDerivative i φ x : ℂ)) 2 (volume : Measure Space) :=
      (((hφ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hφ.compact.fderiv_apply (𝕜 := ℝ) _)).ofReal
    exact hm.integrable_mul hder
  · have h0 : ∫ y, dotL (gvec φ y) ((v : Space → CVec3) y) = 0 := by
      rw [← ellS_apply hφ v]
      exact hv φ hφ
    calc (∫ x, ∑ i : Fin 3, (v : Space → CVec3) x i * (spatialTestDerivative i φ x : ℂ))
        = ∫ y, dotL (gvec φ y) ((v : Space → CVec3) y) :=
          integral_congr_ae (Eventually.of_forall fun y => (hdot φ y _).symm)
      _ = 0 := h0

/-- **Distributionally solenoidal fields of `Y_2` are fixed by `𝐏`** (line 1358-1361, 1498-1500). -/
theorem ysigmaFixedByLeray : UnforcedLeray.Short.IIb.YsigmaFixedByLeray := by
  intro P _ F hF
  have hF' : IsPhaseSolenoidal F := hF
  have hslice : ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
      UnforcedLeray.B0414.IsSolenoidalC ((F τ : Lp CVec3 2 (volume : Measure Space)) : Space → CVec3) := by
    filter_upwards [ysf_ae_circle_mem F isClosed_Ksol ⟨0, Submodule.zero_mem _⟩ (ysf_ae_mem_Ksol F hF')] with τ hτ
    exact ysf_isSolenoidalC_of_mem_Ksol hτ
  exact (UnforcedLeray.B0414.lerayY_two_eq_self_iff F).mpr
    ((UnforcedLeray.B0414.mem_solenoidalY_iff F).mpr hslice)

end UnforcedLeray.Short.IIb
