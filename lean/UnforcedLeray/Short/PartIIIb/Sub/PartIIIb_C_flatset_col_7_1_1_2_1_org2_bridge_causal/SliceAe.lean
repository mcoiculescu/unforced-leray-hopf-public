import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge_causal

/-!
# `causalSliceAe`: a.e. slicing and `c`-periodicity

Source `the November 2 reference manuscript` 1650-1656. The `measureHg` a.e.
identity gives an everywhere-on-the-cell identity `Gh = G ∘ cellPt` Lebesgue-a.e. (the densities
are positive on the cell). Both `periodize Gh` and `G` are `c`-periodic in `q`, so the bad set in
`{s > 0}` is a countable union of `q`-translates of a null set, hence null; Fubini then gives the
slice statement.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Translation of a profile by `-n c` in the `q` coordinate. -/
def sliceShift (c : ℝ) (n : ℤ) : UnforcedLeray.B0220.Profile :=
  (0, (-((n : ℝ) * c), 0))

theorem causalSliceAe : CausalSliceAe := by
  intro c hc G hG Gh hGh i
  obtain ⟨-, hper, -, -⟩ := hG
  -- integer `q`-periodicity of each component
  have hGint : ∀ (s q η : ℝ) (n : ℤ),
      G (s, (q - (n : ℝ) * c, η)) i = G (s, (q, η)) i := by
    intro s q η n
    have hp : Function.Periodic (fun x : ℝ => G (s, (x, η)) i) c := by
      intro x
      show G (s, (x + c, η)) i = G (s, (x, η)) i
      rw [hper s x η]
    exact hp.sub_int_mul_eq n
  have hcellG : ∀ p : UnforcedLeray.B0220.Profile,
      G (NearInst.cellPt c p) i = G p i := by
    intro p
    unfold NearInst.cellPt
    split_ifs
    · rfl
    · have h := hGint p.1 p.2.1 p.2.2 1
      rw [Int.cast_one, one_mul] at h
      exact h
  have hcellM : MeasurableSet (UnforcedLeray.B0220.cell c) :=
    measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  have hWg : Measurable UnforcedLeray.B0220.weightHg := by
    unfold UnforcedLeray.B0220.weightHg
    fun_prop
  -- a.e. on the cell (Lebesgue), `Gh = G`
  have hAll : ∀ᵐ p ∂(volume : Measure UnforcedLeray.B0220.Profile),
      p ∈ UnforcedLeray.B0220.cell c →
        (Gh : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p i
          = ((G p i : ℝ) : ℂ) := by
    have h1 : ∀ᵐ p ∂(volume.restrict (UnforcedLeray.B0220.cell c)),
        (Gh : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p
          = WithLp.toLp 2 (fun j : Fin 2 => ((G (NearInst.cellPt c p) j : ℝ) : ℂ)) := by
      have h0 : ∀ᵐ p ∂((volume.restrict (UnforcedLeray.B0220.cell c)).withDensity
          UnforcedLeray.B0220.weightHg),
          (Gh : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p
            = WithLp.toLp 2 (fun j : Fin 2 => ((G (NearInst.cellPt c p) j : ℝ) : ℂ)) := hGh
      rw [ae_withDensity_iff hWg] at h0
      filter_upwards [h0, ae_restrict_mem hcellM] with p hp hpc
      apply hp
      have hpos : 0 < p.1 := hpc.1
      exact ne_of_gt (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hpos _))
    have h2 := (ae_restrict_iff' hcellM).1 h1
    filter_upwards [h2] with p hp hpc
    rw [hp hpc]
    simp [hcellG]
  have hnull0 : volume {p : UnforcedLeray.B0220.Profile |
      ¬ (p ∈ UnforcedLeray.B0220.cell c →
        (Gh : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p i
          = ((G p i : ℝ) : ℂ))} = 0 :=
    ae_iff.1 hAll
  -- the bad set in `{s > 0}` is covered by countably many translates of the null set
  have hS : volume {p : UnforcedLeray.B0220.Profile |
      0 < p.1 ∧ ¬ (UnforcedLeray.B0220.periodize c (⇑Gh) p i = ((G p i : ℝ) : ℂ))} = 0 := by
    refine measure_mono_null (t := ⋃ n : ℤ,
      (fun x : UnforcedLeray.B0220.Profile => x + sliceShift c n) ⁻¹'
        {p : UnforcedLeray.B0220.Profile |
          ¬ (p ∈ UnforcedLeray.B0220.cell c →
            (Gh : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p i
              = ((G p i : ℝ) : ℂ))}) ?_ ?_
    · rintro p ⟨hpos, hnot⟩
      rw [Set.mem_iUnion]
      refine ⟨⌈p.2.1 / c⌉ - 1, ?_⟩
      have hred : p + sliceShift c (⌈p.2.1 / c⌉ - 1)
          = (p.1, (UnforcedLeray.B0220.reduceIoc c p.2.1, p.2.2)) := by
        rw [UnforcedLeray.B0220.reduceIoc_eq_sub]
        ext <;> simp [sliceShift] <;> ring
      show p + sliceShift c (⌈p.2.1 / c⌉ - 1) ∈
        {p : UnforcedLeray.B0220.Profile |
          ¬ (p ∈ UnforcedLeray.B0220.cell c →
            (Gh : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p i
              = ((G p i : ℝ) : ℂ))}
      rw [hred]
      intro h
      apply hnot
      have hAc := h (show (p.1, (UnforcedLeray.B0220.reduceIoc c p.2.1, p.2.2)) ∈
          UnforcedLeray.B0220.cell c from
        ⟨hpos, UnforcedLeray.B0220.reduceIoc_mem hc _, Set.mem_univ _⟩)
      show Gh (p.1, (UnforcedLeray.B0220.reduceIoc c p.2.1, p.2.2)) i = ((G p i : ℝ) : ℂ)
      rw [hAc, UnforcedLeray.B0220.reduceIoc_eq_sub]
      congr 1
      exact hGint _ _ _ _
    · have : (volume : Measure UnforcedLeray.B0220.Profile).IsAddRightInvariant := by
        rw [Measure.volume_eq_prod]
        infer_instance
      refine measure_iUnion_null (fun n => ?_)
      refine (measure_preimage_add_right (volume : Measure UnforcedLeray.B0220.Profile)
        (sliceShift c n) _).trans ?_
      exact hnull0
  have hae : ∀ᵐ p ∂(volume : Measure UnforcedLeray.B0220.Profile),
      ¬ (0 < p.1 ∧ ¬ (UnforcedLeray.B0220.periodize c (⇑Gh) p i = ((G p i : ℝ) : ℂ))) := by
    rw [ae_iff]
    simpa [not_not] using hS
  have hprod : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))),
      ¬ (0 < x.1 ∧ ¬ (UnforcedLeray.B0220.periodize c (⇑Gh) x i = ((G x i : ℝ) : ℂ))) := by
    rw [← Measure.volume_eq_prod]
    exact hae
  have h2 := Measure.ae_ae_of_ae_prod hprod
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [h2] with σ hσ hσpos
  filter_upwards [hσ] with z hz
  by_contra hne
  exact hz ⟨hσpos, hne⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
