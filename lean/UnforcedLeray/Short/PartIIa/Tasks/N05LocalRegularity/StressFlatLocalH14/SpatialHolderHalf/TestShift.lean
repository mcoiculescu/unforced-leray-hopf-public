import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressFlatLocalH14.SpatialHolderHalf.Periodize

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIa
open UnforcedLeray.B0220 UnforcedLeray.B0223 N05_4Aux N05_4_1Aux

namespace SHH

theorem integral_inner_right {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → MeridC}
    (hf : Integrable f ν) (x : MeridC) :
    ∫ t, inner ℂ (f t) x ∂ν = inner ℂ (∫ t, f t ∂ν) x := by
  have h1 : ∀ t, inner ℂ (f t) x = conj (inner ℂ x (f t)) := fun t => (inner_conj_symm (f t) x).symm
  simp_rw [h1]
  rw [integral_conj, integral_inner hf, inner_conj_symm]

theorem sj_eta_abs (j : Fin 2) (t : ℝ) (p : Profile) : |(sj j t p).2.2 - p.2.2| ≤ |t| := by
  fin_cases j <;> simp [sj, UnforcedLeray.B0579.dir]

theorem isMeridTest_comp_sj {c : ℝ} {φ : Profile → MeridC} (hφ : IsMeridTest c φ) (j : Fin 2)
    (t : ℝ) : IsMeridTest c (fun p => φ (sj j t p)) := by
  refine ⟨?_, periodic_sj_comp j t hφ.periodic, ?_⟩
  · exact hφ.smooth.comp (by show ContDiff ℝ ∞ (fun p : Profile => p + t • ((0 : ℝ), UnforcedLeray.B0579.dir j)); fun_prop)
  · obtain ⟨s0, s1, L, hs0, hb⟩ := hφ.band
    refine ⟨s0, s1, L + |t|, hs0, fun p hp => ?_⟩
    obtain ⟨h1, h2⟩ := hb _ hp
    rw [sj_fst] at h1
    refine ⟨h1, ?_⟩
    have := sj_eta_abs j t p
    have h3 : |p.2.2| ≤ |(sj j t p).2.2| + |(sj j t p).2.2 - p.2.2| := by
      calc |p.2.2| = |(sj j t p).2.2 - ((sj j t p).2.2 - p.2.2)| := by ring_nf
        _ ≤ |(sj j t p).2.2| + |(sj j t p).2.2 - p.2.2| := abs_sub _ _
    linarith

theorem pdSpatial_comp_sj (j : Fin 2) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : Profile → E) (t : ℝ) (p : Profile) :
    pdSpatial j (fun q => φ (sj j t q)) p = pdSpatial j φ (sj j t p) := by
  rw [pdSpatial_eq_fderiv, pdSpatial_eq_fderiv]
  have : (fun q => φ (sj j t q)) = fun q => φ (q + t • ((0 : ℝ), UnforcedLeray.B0579.dir j)) := rfl
  rw [this, fderiv_comp_add_right]
  rfl

theorem ftc_sj (j : Fin 2) {φ : Profile → MeridC} (hφ : ContDiff ℝ ∞ φ) (h : ℝ) (p : Profile) :
    φ (sj j (-h) p) - φ p = -∫ t in (0 : ℝ)..h, pdSpatial j φ (sj j (-t) p) := by
  set v : Profile := ((0 : ℝ), UnforcedLeray.B0579.dir j) with hv
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => φ (sj j (-t) p))
      (-(pdSpatial j φ (sj j (-t) p))) t := by
    intro t
    have hl : HasDerivAt (fun t : ℝ => p + (-t) • v) (-v) t := by
      have := ((hasDerivAt_neg t).smul_const v).const_add p
      simpa using this
    have hd : HasFDerivAt φ (fderiv ℝ φ (p + (-t) • v)) (p + (-t) • v) :=
      ((hφ.differentiable (by decide)) _).hasFDerivAt
    have := hd.comp_hasDerivAt t hl
    rw [map_neg] at this
    rw [pdSpatial_eq_fderiv]
    exact this
  have hcont : Continuous fun t : ℝ => -(pdSpatial j φ (sj j (-t) p)) := by
    have : Continuous fun t : ℝ => pdSpatial j φ (sj j (-t) p) := by
      simp_rw [pdSpatial_eq_fderiv]
      have h1 : Continuous fun q : Profile => fderiv ℝ φ q := hφ.continuous_fderiv (by simp)
      have h2 : Continuous fun t : ℝ => sj j (-t) p := by unfold sj; fun_prop
      exact (h1.comp h2).clm_apply continuous_const
    exact this.neg
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    (hcont.intervalIntegrable 0 h)
  rw [intervalIntegral.integral_neg] at this
  have h0 : sj j (-0) p = p := by simp [sj]
  rw [h0] at this
  exact this.symm

end SHH
end UnforcedLeray.Short.PartIIa
