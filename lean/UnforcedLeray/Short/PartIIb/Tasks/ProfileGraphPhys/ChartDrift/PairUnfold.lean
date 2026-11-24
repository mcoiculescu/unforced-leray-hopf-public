import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.Lift
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.PerSmooth
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.PerVanish
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.PerPeriodic
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.LocalIntegrable
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.LiftDriftProfile
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.HrBox
import UnforcedLeray.Lib.CylinderB.Periodize

/-!
# `PartII-b:T10/6/3/1/2c`: unfolding the periodization against the cell

Source of record: `the November 2 reference manuscript`
lines 1912-1915 and 1900-1906.

`ageμ c a` is the density `c⁻¹ s^a` on `(0,∞) × cell`; on `s > 0` the factors `s^{-5/2} s^{5/2}`
cancel, the periodization vanishes for `s ≤ 0`, and the periodized test unfolds against the
periodic `b` slice by slice (`Cyl.integral_cell_periodize_mul`, Fubini in `s`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.ChartLift

open UnforcedLeray.Short.IIb

/-- `ageμ` is the density `c⁻¹ s^a` against Lebesgue measure on `(0,∞) × cell`. -/
theorem pu_ageμ_eq_wd {c : ℝ} (hc : 0 < c) (a : ℝ) :
    Axi.ageμ c a = (volume.restrict (Ioi (0 : ℝ) ×ˢ Cyl.cell c)).withDensity
      (fun x : Coord => ENNReal.ofReal (c⁻¹ * x.1 ^ a)) := by
  ext s hs
  rw [withDensity_apply _ hs, ← lintegral_indicator hs, ← lintegral_indicator_one hs,
    Axi.lintegral_ageμ hc a (measurable_one.indicator hs)]
  refine lintegral_congr fun p => ?_
  by_cases hp : p ∈ s <;> simp [Set.indicator, hp]

lemma pu_meas_density (c a : ℝ) :
    Measurable (fun x : Coord => ENNReal.ofReal (c⁻¹ * x.1 ^ a)) :=
  ENNReal.measurable_ofReal.comp
    (measurable_const.mul ((measurable_fst).pow_const a))

/-- On `s > 0`, `s^{-5/2} · s^{5/2}` cancels. -/
lemma pu_pointwise (c ε : ℝ) (hc : 0 < c) (φ : Coord → ℝ) (i : Fin 2) (b : CProf) (x : Coord)
    (hx : 0 < x.1) :
    (ENNReal.ofReal (c⁻¹ * x.1 ^ (-(5 / 2 : ℝ)))).toReal • pairG c ε φ i b x =
      ((ε ^ 2 / Real.pi : ℝ) : ℂ) * ((perCoord c φ x : ℝ) : ℂ) * b x i := by
  have h0 : 0 ≤ c⁻¹ * x.1 ^ (-(5 / 2 : ℝ)) :=
    mul_nonneg (inv_nonneg.2 hc.le) (Real.rpow_nonneg hx.le _)
  rw [ENNReal.toReal_ofReal h0, Complex.real_smul]
  unfold pairG
  have h1 : x.1 ^ (-(5 / 2 : ℝ)) * x.1 ^ ((5 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hx]; norm_num
  have h2 : ((c⁻¹ * x.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) *
      ((c * ε ^ 2 / Real.pi * x.1 ^ ((5 : ℝ) / 2) * perCoord c φ x : ℝ) : ℂ) =
      ((ε ^ 2 / Real.pi : ℝ) : ℂ) * ((perCoord c φ x : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    have hc' : c ≠ 0 := hc.ne'
    calc c⁻¹ * x.1 ^ (-(5 / 2 : ℝ)) * (c * ε ^ 2 / Real.pi * x.1 ^ ((5 : ℝ) / 2) * perCoord c φ x)
        = (c⁻¹ * c) * (x.1 ^ (-(5 / 2 : ℝ)) * x.1 ^ ((5 : ℝ) / 2)) * (ε ^ 2 / Real.pi) *
            perCoord c φ x := by ring
      _ = ε ^ 2 / Real.pi * perCoord c φ x := by
          rw [h1, inv_mul_cancel₀ hc']; ring
  rw [← mul_assoc, h2]

lemma pu_perCoord_cont {c : ℝ} (hc : 0 < c) {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    Continuous (perCoord c φ) := (perSmooth_proof c φ hc hφ).continuous

lemma pu_G_meas {c : ℝ} (hc : 0 < c) {φ : Coord → ℝ} (hφ : IsCoordTest φ) (i : Fin 2)
    (b : CProf) (hb : Measurable b) :
    Measurable (fun x : Coord => ((perCoord c φ x : ℝ) : ℂ) * b x i) := by
  have hbi : Measurable (fun x : Coord => b x i) :=
    (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ).continuous.measurable.comp hb
  exact (Complex.measurable_ofReal.comp (pu_perCoord_cont hc hφ).measurable).mul hbi

/-- Integrability of `P b_i` on `ℝ × cell`. -/
lemma pu_integrableOn_cell {c r : ℝ} {φ : Coord → ℝ} {i : Fin 2} {b : CProf}
    (hc : 0 < c) (hr : 1 < r) (hφ : IsCoordTest φ) (hb : InHr c r b) :
    IntegrableOn (fun x : Coord => ((perCoord c φ x : ℝ) : ℂ) * b x i)
      (univ ×ˢ Cyl.cell c) volume := by
  obtain ⟨s₀, s₁, L, hs₀, hv⟩ := perVanish_proof c φ hc hφ
  have hbox := hrBoxIntegrable c r b hc hr hb s₀ s₁ c L hs₀ i
  have hK : IsCompact (Icc s₀ s₁ ×ˢ (Icc (-c) c ×ˢ Icc (-L) L)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hcont : ContinuousOn (fun x : Coord => ((perCoord c φ x : ℝ) : ℂ))
      (Icc s₀ s₁ ×ˢ (Icc (-c) c ×ˢ Icc (-L) L)) :=
    (Complex.continuous_ofReal.comp (pu_perCoord_cont hc hφ)).continuousOn
  have h1 := hbox.mul_continuousOn hcont hK
  have h2 : IntegrableOn (fun x : Coord => ((perCoord c φ x : ℝ) : ℂ) * b x i)
      (Icc s₀ s₁ ×ˢ (Icc (-c) c ×ˢ Icc (-L) L)) volume := by
    refine h1.congr_fun (fun x _ => mul_comm _ _) hK.measurableSet
  refine h2.of_forall_diff_eq_zero (MeasurableSet.univ.prod (by
    unfold Cyl.cell
    exact measurableSet_Ico.prod MeasurableSet.univ)) ?_
  intro x hx
  have hxc : x.2.1 ∈ Ico (-c / 2) (c / 2) := hx.1.2.1
  by_cases hs : s₀ ≤ x.1 ∧ x.1 ≤ s₁ ∧ |x.2.2| ≤ L
  · exfalso
    apply hx.2
    refine ⟨⟨hs.1, hs.2.1⟩, ⟨?_, ?_⟩, ?_⟩
    · linarith [hxc.1]
    · linarith [hxc.2]
    · exact abs_le.1 hs.2.2
  · have : perCoord c φ x = 0 := by
      apply hv
      by_contra hcon
      simp only [not_or, not_lt] at hcon
      exact hs ⟨hcon.1, hcon.2.1, hcon.2.2⟩
    simp [this]

/-- Unfolding of the periodization against the cell. -/
lemma pu_unfold {c r : ℝ} {φ : Coord → ℝ} {i : Fin 2} {b : CProf}
    (hc : 0 < c) (hr : 1 < r) (hφ : IsCoordTest φ) (hb : InHr c r b) (hbm : Measurable b)
    (hper : ∀ s q η, b (s, (q + c, η)) = b (s, (q, η))) :
    ∫ x in univ ×ˢ Cyl.cell c, ((perCoord c φ x : ℝ) : ℂ) * b x i =
      ∫ x, b x i * (φ x : ℂ) := by
  have H1 := pu_integrableOn_cell (i := i) hc hr hφ hb
  have hF := hrLocalIntegrable_proof c r b φ i hc hr hb hφ
  have hmeasEq : (volume : Measure Coord).restrict (univ ×ˢ Cyl.cell c) =
      (volume : Measure ℝ).prod ((volume : Measure Cyl.Plane).restrict (Cyl.cell c)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hbi : Measurable (fun x : Coord => b x i) :=
    (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ).continuous.measurable.comp hbm
  have H1' : Integrable (fun x : Coord => ((perCoord c φ x : ℝ) : ℂ) * b x i)
      ((volume : Measure ℝ).prod ((volume : Measure Cyl.Plane).restrict (Cyl.cell c))) := by
    rw [← hmeasEq]; exact H1
  have hF' : Integrable (fun x : Coord => b x i * (φ x : ℂ))
      ((volume : Measure ℝ).prod (volume : Measure Cyl.Plane)) := by
    rw [← Measure.volume_eq_prod]; exact hF
  rw [hmeasEq, integral_prod _ H1']
  have hR : ∫ x, b x i * (φ x : ℂ) = ∫ s : ℝ, ∫ z : Cyl.Plane, b (s, z) i * (φ (s, z) : ℂ) := by
    rw [Measure.volume_eq_prod, integral_prod _ (by rw [← Measure.volume_eq_prod]; exact hF)]
  rw [hR]
  refine integral_congr_ae ?_
  filter_upwards [hF'.prod_right_ae] with s hs
  have hf : StronglyMeasurable (fun z : Cyl.Plane => ((φ (s, z) : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (hφ.smooth.continuous.comp (Continuous.prodMk_right s))).stronglyMeasurable
  have hg : StronglyMeasurable (fun z : Cyl.Plane => b (s, z) i) :=
    (hbi.comp measurable_prodMk_left).stronglyMeasurable
  have hgp : Cyl.IsPeriodic c (fun z : Cyl.Plane => b (s, z) i) := fun z => by
    simp only; rw [hper s z.1 z.2]
  have hfg : Integrable (fun z : Cyl.Plane =>
      ((φ (s, z) : ℝ) : ℂ) * b (s, z) i) := by
    refine hs.congr (Eventually.of_forall fun z => ?_)
    simp only [mul_comm]
  have key := UnforcedLeray.Cyl.integral_cell_periodize_mul hc hf hg hgp hfg
  have hper2 : ∀ z : Cyl.Plane, ((perCoord c φ (s, z) : ℝ) : ℂ) =
      Cyl.periodize c (fun z : Cyl.Plane => ((φ (s, z) : ℝ) : ℂ)) z := by
    intro z
    unfold perCoord Cyl.periodize
    rw [Complex.ofReal_tsum, ← (Equiv.neg ℤ).tsum_eq]
    refine tsum_congr fun n => ?_
    simp [sub_eq_add_neg]
  have lhs : ∫ z in Cyl.cell c, ((perCoord c φ (s, z) : ℝ) : ℂ) * b (s, z) i =
      ∫ z in Cyl.cell c, Cyl.periodize c (fun z : Cyl.Plane => ((φ (s, z) : ℝ) : ℂ)) z *
        b (s, z) i := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hper2]
  rw [lhs, key]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [mul_comm]

/-- **Leaf `T10/6/3/1/2c`.** -/
theorem pairUnfold_proof : UnforcedLeray.Short.IIb.ChartLift.PairUnfold := by
  intro c ε r φ i b hc hε hr hφ hb hbm hper
  have hcell : MeasurableSet (Ioi (0 : ℝ) ×ˢ Cyl.cell c) :=
    measurableSet_Ioi.prod (by unfold Cyl.cell; exact measurableSet_Ico.prod MeasurableSet.univ)
  have H1 := pu_integrableOn_cell (i := i) hc hr hφ hb
  have H2 : IntegrableOn (fun x : Coord => ((perCoord c φ x : ℝ) : ℂ) * b x i)
      (Ioi (0 : ℝ) ×ˢ Cyl.cell c) volume :=
    H1.mono_set (prod_mono (subset_univ _) subset_rfl)
  have hwd := pu_ageμ_eq_wd hc (-(5 / 2 : ℝ))
  have hdlt : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ Cyl.cell c)),
      ENNReal.ofReal (c⁻¹ * x.1 ^ (-(5 / 2 : ℝ))) < ∞ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hpos : ∀ x ∈ Ioi (0 : ℝ) ×ˢ Cyl.cell c, 0 < x.1 := fun x hx => hx.1
  have heq : ∀ x ∈ Ioi (0 : ℝ) ×ˢ Cyl.cell c,
      (ENNReal.ofReal (c⁻¹ * x.1 ^ (-(5 / 2 : ℝ)))).toReal • pairG c ε φ i b x =
        ((ε ^ 2 / Real.pi : ℝ) : ℂ) * (((perCoord c φ x : ℝ) : ℂ) * b x i) := fun x hx => by
    rw [pu_pointwise c ε hc φ i b x (hpos x hx), mul_assoc]
  have hint : Integrable (pairG c ε φ i b) (Axi.ageμ c (-(5 / 2 : ℝ))) := by
    rw [hwd, integrable_withDensity_iff_integrable_smul' (pu_meas_density c _) hdlt]
    have h3 := H2.const_mul ((ε ^ 2 / Real.pi : ℝ) : ℂ)
    exact (integrableOn_congr_fun (fun x hx => (heq x hx).symm) hcell).1 h3
  refine ⟨hint, ?_⟩
  rw [hwd, integral_withDensity_eq_integral_toReal_smul₀
    (pu_meas_density c _).aemeasurable hdlt]
  rw [setIntegral_congr_fun hcell heq, integral_const_mul]
  congr 1
  rw [← pu_unfold (i := i) hc hr hφ hb hbm hper]
  symm
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero ?_ ?_ ?_
  · exact MeasurableSet.univ.prod (by unfold Cyl.cell; exact measurableSet_Ico.prod MeasurableSet.univ)
  · exact prod_mono (subset_univ _) subset_rfl
  · intro x hx
    have hx1 : x.1 ≤ 0 := by
      by_contra h
      exact hx.2 ⟨not_le.1 h, hx.1.2⟩
    simp [(ldp_perCoord_zero_left φ hφ c x hx1).1]

end UnforcedLeray.Short.IIb.ChartLift

end
