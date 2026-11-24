import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1

/-!
# `T0gAe`: the dilated heat flow depends only on the `measureH c`-class of its section

Helpers are prefixed `t0g_`. The argument: `f =ᵐ[measureH c] g` gives a Lebesgue a.e. equality on
the cell; by Fubini, for a.e. `s` the section `(q, η) ↦ f(s,q,η)` agrees with `g` a.e.; the
dilation `s ↦ e^t s` preserves null sets; the `q`-reduction is a countable union of translates.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile QPeriodic)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.B0226 (ProfileTest IsProfileTest)

/-- From the `measureH`-a.e. equality to a Lebesgue a.e. equality on the cell. -/
theorem t0g_ae_volume {c : ℝ} {f g : Profile → MeridC} (hfg : f =ᵐ[measureH c] g) :
    ∀ᵐ p ∂(volume : Measure Profile), p ∈ UnforcedLeray.B0220.cell c → f p = g p := by
  have h1 : ∀ᵐ p ∂(UnforcedLeray.B0220.cellMeasure c),
      UnforcedLeray.B0220.weightH p ≠ 0 → f p = g p :=
    (ae_withDensity_iff' (UnforcedLeray.B0220.measurable_weightH.aemeasurable)).1 hfg
  have h2 : ∀ᵐ p ∂(volume : Measure Profile),
      p ∈ UnforcedLeray.B0220.cell c → UnforcedLeray.B0220.weightH p ≠ 0 → f p = g p := by
    have h := h1
    rw [UnforcedLeray.B0220.cellMeasure] at h
    exact (ae_restrict_iff' (UnforcedLeray.B0220.measurableSet_cell c)).1 h
  filter_upwards [h2] with p hp hpc
  refine hp hpc ?_
  exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hpc.1 _)).ne'

/-- Fubini: for a.e. `s`, the slice agrees a.e. on the `(q, η)` plane. -/
theorem t0g_ae_slice {c : ℝ} {f g : Profile → MeridC}
    (hV : ∀ᵐ p ∂(volume : Measure Profile), p ∈ UnforcedLeray.B0220.cell c → f p = g p) :
    ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ w ∂(volume : Measure (ℝ × ℝ)),
      (s, w) ∈ UnforcedLeray.B0220.cell c → f (s, w) = g (s, w) := by
  rw [Measure.volume_eq_prod] at hV
  exact Measure.ae_ae_of_ae_prod hV

/-- For fixed `s > 0`, the `q`-periodization of `f` agrees a.e. with the periodic `g`. -/
theorem t0g_periodize_ae {c : ℝ} (hc : 0 < c) {f g : Profile → MeridC} (hg : QPeriodic c g)
    {s : ℝ} (hs : 0 < s)
    (hR : ∀ᵐ w ∂(volume : Measure (ℝ × ℝ)),
      (s, w) ∈ UnforcedLeray.B0220.cell c → f (s, w) = g (s, w)) :
    ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), UnforcedLeray.B0220.periodize c f (s, z) = g (s, z) := by
  have hT : ∀ k : ℤ, ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      (s, z - ((k : ℝ) * c, (0 : ℝ))) ∈ UnforcedLeray.B0220.cell c →
        f (s, z - ((k : ℝ) * c, (0 : ℝ))) = g (s, z - ((k : ℝ) * c, (0 : ℝ))) := by
    intro k
    exact (measurePreserving_sub_right (volume : Measure (ℝ × ℝ))
      ((k : ℝ) * c, (0 : ℝ))).quasiMeasurePreserving.ae hR
  filter_upwards [ae_all_iff.2 hT] with z hz
  have hmem : UnforcedLeray.B0220.reduceIoc c z.1 ∈ Ioc 0 c :=
    UnforcedLeray.B0220.reduceIoc_mem hc z.1
  have hcell : (s, (UnforcedLeray.B0220.reduceIoc c z.1, z.2)) ∈ UnforcedLeray.B0220.cell c :=
    ⟨hs, hmem, trivial⟩
  have hzeq : z - (((⌈z.1 / c⌉ - 1 : ℤ) : ℝ) * c, (0 : ℝ)) =
      (UnforcedLeray.B0220.reduceIoc c z.1, z.2) := by
    rw [UnforcedLeray.B0220.reduceIoc_eq_sub]
    ext <;> simp
  have h1 := hz (⌈z.1 / c⌉ - 1)
  rw [hzeq] at h1
  have h2 := h1 hcell
  show f (s, UnforcedLeray.B0220.reduceIoc c z.1, z.2) = g (s, z.1, z.2)
  rw [h2]
  exact UnforcedLeray.B0220.periodic_reduceIoc_eq g hg s z.1 z.2

/-- Translation `y ↦ x - ι y` on the Euclidean plane is measure preserving. -/
theorem t0g_planeι_mp (x : ℝ × ℝ) :
    MeasurePreserving (fun y : UnforcedLeray.Gaussian.Euc 2 => x - UnforcedLeray.B0224.planeι y)
      volume volume := by
  have h1 : MeasurePreserving (WithLp.ofLp : UnforcedLeray.Gaussian.Euc 2 → (Fin 2 → ℝ))
      volume volume := PiLp.volume_preserving_ofLp (Fin 2)
  have h2 := MeasureTheory.volume_preserving_finTwoArrow ℝ
  have h3 : MeasurePreserving (fun y : UnforcedLeray.Gaussian.Euc 2 => (y 0, y 1)) volume volume :=
    h2.comp h1
  have h4 : MeasurePreserving (fun y : ℝ × ℝ => x - y) volume volume := by
    have h := (MeasureTheory.measurePreserving_add_right (volume : Measure (ℝ × ℝ)) x).comp
      (MeasureTheory.Measure.measurePreserving_neg (volume : Measure (ℝ × ℝ)))
    have e : (fun y : ℝ × ℝ => x - y) = (fun y => y + x) ∘ Neg.neg := by
      funext y
      simp [sub_eq_add_neg, add_comm]
    rw [e]
    exact h
  exact h4.comp h3

/-- **`T0gAe`** (source 1640-1656): the dilated heat of the periodization depends only on the
`measureH c`-class of the section. -/
theorem t0gAe_proof : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gAe := by
  intro c ν t hc g hg f hfg
  have hV := t0g_ae_volume (c := c) hfg
  have hslice := t0g_ae_slice hV
  have hQall : ∀ᵐ s ∂(volume : Measure ℝ), 0 < s → ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      UnforcedLeray.B0220.periodize c f (s, z) = g (s, z) := by
    filter_upwards [hslice] with s hsR hs
    exact t0g_periodize_ae hc hg hs hsR
  have hQ : Measure.QuasiMeasurePreserving (fun s : ℝ => Real.exp t * s)
      (volume : Measure ℝ) volume := by
    have h := Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
      (Real.exp_ne_zero t)
    simpa [smul_eq_mul] using h
  have hdil := hQ.ae hQall
  have hfstQ : Measure.QuasiMeasurePreserving (Prod.fst : Profile → ℝ)
      (volume : Measure Profile) volume := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_fst
  have hAe := hfstQ.ae hdil
  have hD : Measure.QuasiMeasurePreserving (fun p : Profile => (Real.exp t * p.1, p.2))
      (volume : Measure Profile) volume := by
    rw [Measure.volume_eq_prod]
    exact MeasureTheory.QuasiMeasurePreserving.prodMap hQ (Measure.QuasiMeasurePreserving.id _)
  have hA2 := hD.ae hV
  have hacH : measureH c ≪ (volume : Measure Profile) :=
    (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hmH := UnforcedLeray.B0220.ae_cell_measureH c
  have hPH := hacH.ae_le hAe
  have hDH := hacH.ae_le hA2
  filter_upwards [hmH, hPH, hDH] with p hp hP1 hD1
  have hs : 0 < p.1 := hp.1
  have hpos : 0 < Real.exp t * p.1 := mul_pos (Real.exp_pos t) hs
  have hcellD : (Real.exp t * p.1, p.2) ∈ UnforcedLeray.B0220.cell c := ⟨hpos, hp.2⟩
  by_cases hθ : 0 < ν * p.1 * (Real.exp t - 1)
  · rw [UnforcedLeray.B0224.planeHeat_of_pos hθ, UnforcedLeray.B0224.planeHeat_of_pos hθ]
    refine integral_congr_ae ?_
    filter_upwards [(t0g_planeι_mp p.2).quasiMeasurePreserving.ae (hP1 hpos)] with y hy
    have hy' : UnforcedLeray.B0220.periodize c f (Real.exp t * p.1, p.2 - UnforcedLeray.B0224.planeι y)
        = g (Real.exp t * p.1, p.2 - UnforcedLeray.B0224.planeι y) := hy
    simp only [hy']
  · rw [UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 hθ),
      UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 hθ)]
    show UnforcedLeray.B0220.periodize c f (Real.exp t * p.1, p.2) = g (Real.exp t * p.1, p.2)
    rw [UnforcedLeray.B0220.periodize_of_mem hc f hcellD]
    exact hD1 hcellD

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
