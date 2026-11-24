import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.Of
import UnforcedLeray.Short.PartIIa.Sub.N02_4_11

/-!
# `L²` membership of smooth meridional tests and of `A₀*ζ` (sub-lemma of `R0TransposeIdentity`)

Source `the November 2 reference manuscript` 1650-1656.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa (IsMeridTest pdS pdQ pdEta nztc_memLp)

theorem isMeridTest_pdS_aux {c : ℝ} {ζ : Profile → MeridC} (h : IsMeridTest c ζ) :
    ContDiff ℝ ∞ (pdS ζ) := by
  unfold pdS
  exact (h.smooth.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

theorem isMeridTest_pdQ_aux {c : ℝ} {ζ : Profile → MeridC} (h : IsMeridTest c ζ) :
    ContDiff ℝ ∞ (pdQ ζ) := by
  unfold pdQ
  exact (h.smooth.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

theorem isMeridTest_pdEta_aux {c : ℝ} {ζ : Profile → MeridC} (h : IsMeridTest c ζ) :
    ContDiff ℝ ∞ (pdEta ζ) := by
  unfold pdEta
  exact (h.smooth.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

theorem fderiv_periodic_aux {c : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Profile → E} (hf : UnforcedLeray.B0220.QPeriodic c f) (p : Profile) :
    fderiv ℝ f (p.1, p.2.1 + c, p.2.2) = fderiv ℝ f p := by
  have h1 : (fun x : Profile => f (x + (0, c, 0))) = f := by
    funext x
    have e : x + ((0 : ℝ), c, (0 : ℝ)) = (x.1, x.2.1 + c, x.2.2) := by
      ext <;> simp
    rw [e]
    exact hf x
  have h2 : fderiv ℝ (fun x : Profile => f (x + (0, c, 0))) p = fderiv ℝ f (p + (0, c, 0)) :=
    fderiv_comp_add_right _
  rw [h1] at h2
  have e : p + ((0 : ℝ), c, (0 : ℝ)) = (p.1, p.2.1 + c, p.2.2) := by
    ext <;> simp
  rw [e] at h2
  exact h2.symm

theorem pd_periodic_aux {c : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Profile → E} (hf : UnforcedLeray.B0220.QPeriodic c f) (v : Profile) :
    UnforcedLeray.B0220.QPeriodic c (fun p => fderiv ℝ f p v) := fun p => by
  simp only [fderiv_periodic_aux hf p]

theorem isMeridTest_A0adj {c : ℝ} (ν : ℝ) {ζ : Profile → MeridC} (h : IsMeridTest c ζ) :
    IsMeridTest c (A0adj ν ζ) := by
  have hS := isMeridTest_pdS_aux h
  have hQ := isMeridTest_pdQ_aux h
  have hE := isMeridTest_pdEta_aux h
  have hQQ : ContDiff ℝ ∞ (pdQ (pdQ ζ)) := by
    unfold pdQ
    exact ((hQ.fderiv_right (m := ∞) le_rfl)).clm_apply contDiff_const
  have hEE : ContDiff ℝ ∞ (pdEta (pdEta ζ)) := by
    unfold pdEta
    exact ((hE.fderiv_right (m := ∞) le_rfl)).clm_apply contDiff_const
  have hperS : UnforcedLeray.B0220.QPeriodic c (pdS ζ) := pd_periodic_aux h.periodic _
  have hperQ : UnforcedLeray.B0220.QPeriodic c (pdQ ζ) := pd_periodic_aux h.periodic _
  have hperE : UnforcedLeray.B0220.QPeriodic c (pdEta ζ) := pd_periodic_aux h.periodic _
  have hperQQ : UnforcedLeray.B0220.QPeriodic c (pdQ (pdQ ζ)) := pd_periodic_aux hperQ _
  have hperEE : UnforcedLeray.B0220.QPeriodic c (pdEta (pdEta ζ)) := pd_periodic_aux hperE _
  obtain ⟨s0, s1, L, hs0, hb⟩ := h.band
  have hK : IsClosed (Icc s0 s1 ×ˢ (univ : Set (ℝ × ℝ)) ∩ {p : Profile | |p.2.2| ≤ L}) := by
    refine (isClosed_Icc.prod isClosed_univ).inter ?_
    exact isClosed_le (by fun_prop) continuous_const
  have hsub : tsupport ζ ⊆ Icc s0 s1 ×ˢ (univ : Set (ℝ × ℝ)) ∩ {p : Profile | |p.2.2| ≤ L} := by
    refine closure_minimal (fun p hp => ?_) hK
    obtain ⟨h1, h2⟩ := hb p hp
    exact ⟨⟨h1, trivial⟩, h2⟩
  have hts : ∀ (g : Profile → MeridC) (v : Profile), tsupport g ⊆ tsupport ζ →
      tsupport (fun p => fderiv ℝ g p v) ⊆ tsupport ζ := fun g v hg => by
    refine closure_minimal (fun p hp => ?_) isClosed_closure
    have : fderiv ℝ g p ≠ 0 := fun h0 => hp (by simp [h0])
    exact hg (support_fderiv_subset ℝ this)
  have h1 : tsupport (pdS ζ) ⊆ tsupport ζ := hts ζ _ subset_rfl
  have h2 : tsupport (pdQ ζ) ⊆ tsupport ζ := hts ζ _ subset_rfl
  have h3 : tsupport (pdEta ζ) ⊆ tsupport ζ := hts ζ _ subset_rfl
  have h4 : tsupport (pdQ (pdQ ζ)) ⊆ tsupport ζ := hts _ _ h2
  have h5 : tsupport (pdEta (pdEta ζ)) ⊆ tsupport ζ := hts _ _ h3
  refine ⟨?_, ?_, ?_⟩
  · have hs1 : ContDiff ℝ ∞ (fun p : Profile => p.1) := contDiff_fst
    have t1 : ContDiff ℝ ∞ (fun p : Profile => p.1 • pdS ζ p) := hs1.smul hS
    have t2 : ContDiff ℝ ∞ (fun p : Profile => (1 / 2 : ℝ) • ζ p) :=
      (contDiff_const (c := (1 / 2 : ℝ))).smul h.smooth
    have t3 : ContDiff ℝ ∞ (fun p : Profile => (ν * p.1) • (pdQ (pdQ ζ) p + pdEta (pdEta ζ) p)) :=
      (contDiff_const.mul hs1).smul (hQQ.add hEE)
    exact (t1.sub t2).add t3
  · intro p
    simp only [A0adj, h.periodic p, hperS p, hperQQ p, hperEE p]
  · refine ⟨s0, s1, L, hs0, fun p hp => ?_⟩
    by_contra hcon
    have hn : p ∉ tsupport ζ := fun hm => hcon (by
      have := hsub hm
      exact ⟨this.1.1, this.2⟩)
    apply hp
    simp only [A0adj, image_eq_zero_of_notMem_tsupport hn,
      image_eq_zero_of_notMem_tsupport (fun hm => hn (h1 hm)),
      image_eq_zero_of_notMem_tsupport (fun hm => hn (h4 hm)),
      image_eq_zero_of_notMem_tsupport (fun hm => hn (h5 hm))]
    simp

/-- `NeedMemLpTest`: smooth meridional tests and their `A₀*`-images lie in `L²(measureH c)`. -/
theorem memLp_test_A0adj (c ν : ℝ) (ζ : Profile → MeridC) (hζ : IsMeridTest c ζ) :
    MemLp ζ 2 (measureH c) ∧ MemLp (A0adj ν ζ) 2 (measureH c) :=
  ⟨nztc_memLp hζ, nztc_memLp (isMeridTest_A0adj ν hζ)⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
