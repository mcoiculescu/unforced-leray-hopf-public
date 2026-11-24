import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas

/-!
# `tensorTestDivMem`: `s div_ε M ∈ H` for a smooth tensor test (source 1660-1665, 1678)

Route. For a smooth tensor test `M` (`PartIIa.IsTensorTest`), the function
`p ↦ (p.1 : ℂ) • divEps ε M p` is continuous (the derivatives of a smooth map are continuous).
It vanishes off the closed band `{s₀ ≤ s ≤ s₁, |η| ≤ L}`, since `M` vanishes on the open
complement of that band, hence so do all its derivatives there. On the compact box
`[s₀,s₁] × [0,c] × [-L,L]` it is bounded, and the cell measure `s^{-3/2} ds dq dη` of that box is
finite because the weight is bounded there. So the function is `L²` on the restriction to the box,
and it agrees `measureH c`-a.e. with its indicator of the box (points of the cell outside the box
lie outside the band).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar
open UnforcedLeray.Short.PartIIa

/-- The closed band `{s₀ ≤ s ≤ s₁, |η| ≤ L}` of a tensor test. -/
def dtdBand (s0 s1 L : ℝ) : Set UnforcedLeray.B0220.Profile :=
  {p | s0 ≤ p.1 ∧ p.1 ≤ s1 ∧ |p.2.2| ≤ L}

/-- The compact box `[s₀,s₁] × [0,c] × [-L,L]`. -/
def dtdBox (s0 s1 c L : ℝ) : Set UnforcedLeray.B0220.Profile :=
  Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)

theorem dtdBand_closed (s0 s1 L : ℝ) : IsClosed (dtdBand s0 s1 L) := by
  have h1 : IsClosed {p : UnforcedLeray.B0220.Profile | s0 ≤ p.1} :=
    isClosed_le continuous_const continuous_fst
  have h2 : IsClosed {p : UnforcedLeray.B0220.Profile | p.1 ≤ s1} :=
    isClosed_le continuous_fst continuous_const
  have h3 : IsClosed {p : UnforcedLeray.B0220.Profile | |p.2.2| ≤ L} :=
    isClosed_le (by fun_prop) continuous_const
  exact h1.inter (h2.inter h3)

theorem dtdBox_compact (s0 s1 c L : ℝ) : IsCompact (dtdBox s0 s1 c L) :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

/-- A function vanishing near a point has zero Fréchet derivative there. -/
theorem dtd_fderiv_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℂ) (x : E) (h : ∀ᶠ y in nhds x, g y = 0) (v : E) : fderiv ℝ g x v = 0 := by
  have h' : g =ᶠ[nhds x] fun _ => (0 : ℂ) := h
  rw [h'.fderiv_eq]
  simp

/-- `div_ε M` vanishes at a point near which `M` vanishes. -/
theorem dtd_divEps_eq_zero (ε : ℝ) (M : UnforcedLeray.B0220.Profile → TensorVal)
    (x : UnforcedLeray.B0220.Profile) (h : ∀ᶠ y in nhds x, M y = 0) :
    divEps ε M x = 0 := by
  have hMx : M x = 0 := h.self_of_nhds
  have hc : ∀ j : Fin 4, ∀ v : UnforcedLeray.B0220.Profile,
      fderiv ℝ (fun y => M y j) x v = 0 := fun j v =>
    dtd_fderiv_zero _ x (h.mono fun y hy => by simp [hy]) v
  unfold divEps
  ext i
  fin_cases i <;> simp [opQ, opK, opS, pdQ, pdS, pdEta, hc, hMx]

theorem dtd_cont_pd {g : UnforcedLeray.B0220.Profile → ℂ} (hg : ContDiff ℝ ∞ g)
    (v : UnforcedLeray.B0220.Profile) : Continuous fun p => fderiv ℝ g p v :=
  (hg.continuous_fderiv (by simp)).clm_apply continuous_const

theorem dtd_cont_opQ (ε : ℝ) {f : UnforcedLeray.B0220.Profile → ℂ} (hf : ContDiff ℝ ∞ f) :
    Continuous fun p => opQ ε f p := by
  have h1 := dtd_cont_pd hf (0, 1, 0)
  have h2 := dtd_cont_pd hf (1, 0, 0)
  have h3 := dtd_cont_pd hf (0, 0, 1)
  have h4 := hf.continuous
  unfold opQ opK opS pdQ pdS pdEta
  fun_prop

theorem dtd_cont_pdEta {g : UnforcedLeray.B0220.Profile → ℂ} (hg : ContDiff ℝ ∞ g) :
    Continuous fun p => pdEta g p :=
  dtd_cont_pd hg (0, 0, 1)

/-- The tensor divergence of a smooth tensor test is continuous. -/
theorem dtd_cont_divEps (ε : ℝ) (M : UnforcedLeray.B0220.Profile → TensorVal)
    (hM : ContDiff ℝ ∞ M) : Continuous fun p => divEps ε M p := by
  have hcomp : ∀ j : Fin 4, ContDiff ℝ ∞ (fun p => M p j) := fun j =>
    ((EuclideanSpace.proj j : TensorVal →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hM
  have ha : Continuous fun p => opQ ε (fun x => M x 0) p + pdEta (fun x => M x 1) p
      - (ε : ℂ) * M p 3 :=
    ((dtd_cont_opQ ε (hcomp 0)).add (dtd_cont_pdEta (hcomp 1))).sub
      (continuous_const.mul (hcomp 3).continuous)
  have hb : Continuous fun p => opQ ε (fun x => M x 1) p + pdEta (fun x => M x 2) p :=
    (dtd_cont_opQ ε (hcomp 1)).add (dtd_cont_pdEta (hcomp 2))
  unfold divEps
  refine (PiLp.continuous_toLp 2 _).comp ?_
  exact Continuous.matrixVecCons ha (Continuous.matrixVecCons hb continuous_const)

theorem tensorTestDivMem : TensorTestDivMem := by
  intro c ε hc M hM
  obtain ⟨s0, s1, L, hs0, hband⟩ := hM.band
  -- the function vanishes off the closed band
  have hsupp : ∀ p, p ∉ dtdBand s0 s1 L → (p.1 : ℂ) • divEps ε M p = 0 := by
    intro p hp
    have hev : ∀ᶠ y in nhds p, M y = 0 := by
      filter_upwards [(dtdBand_closed s0 s1 L).isOpen_compl.mem_nhds hp] with y hy
      by_contra hne
      exact hy ⟨(hband y hne).1.1, (hband y hne).1.2, (hband y hne).2⟩
    rw [dtd_divEps_eq_zero ε M p hev, smul_zero]
  have hfc : Continuous fun p : UnforcedLeray.B0220.Profile => (p.1 : ℂ) • divEps ε M p :=
    (Complex.continuous_ofReal.comp continuous_fst).smul (dtd_cont_divEps ε M hM.smooth)
  obtain ⟨Bd, hBd⟩ := (dtdBox_compact s0 s1 c L).exists_bound_of_continuousOn
    hfc.continuousOn
  have hdm : MeasurableSet (dtdBox s0 s1 c L) :=
    (dtdBox_compact s0 s1 c L).isClosed.measurableSet
  have hfin : UnforcedLeray.B0220.measureH c (dtdBox s0 s1 c L) < ⊤ := by
    unfold UnforcedLeray.B0220.measureH
    rw [withDensity_apply _ hdm]
    have hmono : ∫⁻ x in dtdBox s0 s1 c L, UnforcedLeray.B0220.weightH x
        ∂(UnforcedLeray.B0220.cellMeasure c)
        ≤ ∫⁻ x in dtdBox s0 s1 c L, ENNReal.ofReal (s0 ^ (-(3 / 2 : ℝ)))
          ∂(UnforcedLeray.B0220.cellMeasure c) := by
      apply setLIntegral_mono' hdm
      intro x hx
      have hx1 : s0 ≤ x.1 := by
        simp only [dtdBox, Set.mem_prod, Set.mem_Icc] at hx
        exact hx.1.1
      unfold UnforcedLeray.B0220.weightH
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hs0 hx1 (by norm_num))
    refine lt_of_le_of_lt hmono ?_
    rw [setLIntegral_const]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    unfold UnforcedLeray.B0220.cellMeasure
    exact lt_of_le_of_lt (Measure.le_iff'.mp Measure.restrict_le_self _)
      (dtdBox_compact s0 s1 c L).measure_lt_top
  have hcellm : MeasurableSet (UnforcedLeray.B0220.cell c) :=
    measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  have hcell : ∀ᵐ x ∂(UnforcedLeray.B0220.measureH c), x ∈ UnforcedLeray.B0220.cell c := by
    unfold UnforcedLeray.B0220.measureH UnforcedLeray.B0220.cellMeasure
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hcellm)
  have hMem : MemLp (fun p : UnforcedLeray.B0220.Profile => (p.1 : ℂ) • divEps ε M p) 2
      ((UnforcedLeray.B0220.measureH c).restrict (dtdBox s0 s1 c L)) := by
    have : IsFiniteMeasure ((UnforcedLeray.B0220.measureH c).restrict (dtdBox s0 s1 c L)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
    exact MemLp.of_bound hfc.aestronglyMeasurable Bd
      (ae_restrict_of_forall_mem hdm fun x hx => hBd x hx)
  have hind : (fun p : UnforcedLeray.B0220.Profile => (p.1 : ℂ) • divEps ε M p)
      =ᵐ[UnforcedLeray.B0220.measureH c]
        (dtdBox s0 s1 c L).indicator (fun p : UnforcedLeray.B0220.Profile => (p.1 : ℂ) • divEps ε M p) := by
    filter_upwards [hcell] with x hx
    by_cases hxC : x ∈ dtdBox s0 s1 c L
    · rw [Set.indicator_of_mem hxC]
    · rw [Set.indicator_of_notMem hxC]
      apply hsupp x
      intro hB
      apply hxC
      obtain ⟨h1, h2, h3⟩ := hB
      simp only [UnforcedLeray.B0220.cell, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioc,
        Set.mem_univ] at hx
      exact ⟨⟨h1, h2⟩, ⟨hx.2.1.1.le, hx.2.1.2⟩, abs_le.mp h3⟩
  exact ((memLp_indicator_iff_restrict hdm).mpr hMem).ae_eq hind.symm

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
