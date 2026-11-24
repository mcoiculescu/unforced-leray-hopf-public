import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5.NewtonOrg

/-!
# Polar-coordinate evaluation of `sigmaInt 2 2 - sigmaInt 0 0` (`PartIII-b:IIIb-D3/2/G5/2/2`)

Source of record: `the November 2 reference manuscript`, lines 4859-4862, 4584-4587.
Proves `sigmaIntPolar`: given `sigmaInt c ν chio M 0 0 = sigmaInt c ν chio M 1 1`, evaluates
`sigmaInt c ν chio M 2 2 - sigmaInt c ν chio M 0 0` in polar coordinates via `planePolar_bochner`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5

/-- Entrywise integrability of `sigmaM` on `ℝ × ℝ` from `sigmaM_l1W`. -/
theorem integrable_sigmaM_entry {c ν : ℝ} {chio : ℝ → ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hχ : IsOutwardCutoff chio) {M : Chart → Mat3} (hM : OldThinFinite c ν M) (a b : Fin 3) :
    Integrable (fun y : ℝ × ℝ => sigmaM c ν chio M y a b) := by
  obtain ⟨-, hint, -⟩ := sigmaM_l1W c ν chio hc hν hχ M hM
  refine hint.norm.mono' (sigmaM_entry_aesm hν hχ M hM a b) (Eventually.of_forall fun y => ?_)
  exact (norm_le_pi_norm (sigmaM c ν chio M y a) b).trans (norm_le_pi_norm (sigmaM c ν chio M y) a)

/-- For a.e. `u ∈ Ioi (6 / 5 / ν)`, every entry `p ↦ M (u, p) i j` is integrable on `Cyl.avgμ c`. -/
theorem ae_integrable_entry_slice {c ν : ℝ} (hν : 0 < ν) {M : Chart → Mat3}
    (hM : OldThinFinite c ν M) :
    ∀ᵐ u ∂volume, u ∈ Ioi (6 / 5 / ν) →
      ∀ i j : Fin 3, Integrable (fun p => M (u, p) i j) (Cyl.avgμ c) := by
  obtain ⟨hmeas, hint⟩ := hM
  unfold oldMeasure at hmeas hint
  have h1 := hint.prod_right_ae
  have h2 := hmeas.prodMk_left
  rw [ae_restrict_iff' measurableSet_Ioi] at h1 h2
  filter_upwards [h1, h2] with u hu1 hu2 hu i j
  have hpos : 0 < u := lt_trans (div_pos (by norm_num) hν) hu
  have hg : Integrable (fun p => u ^ (3 / 2 : ℝ) * (u ^ (-(3 / 2 : ℝ)) * frob (M (u, p))))
      (Cyl.avgμ c) :=
    (hu1 hu).const_mul _
  have hmeasE : AEStronglyMeasurable (fun p => M (u, p) i j) (Cyl.avgμ c) :=
    (show Continuous fun A : Mat3 => A i j by fun_prop).comp_aestronglyMeasurable (hu2 hu)
  refine hg.mono' hmeasE (Eventually.of_forall fun p => ?_)
  have hid : u ^ (3 / 2 : ℝ) * (u ^ (-(3 / 2 : ℝ)) * frob (M (u, p))) = frob (M (u, p)) := by
    rw [← mul_assoc, ← Real.rpow_add hpos]
    norm_num
  rw [hid, Real.norm_eq_abs]
  exact NewtonVGeom.abs_le_frob (M (u, p)) i j

/-- Pointwise diagonal combination identity on all of `ℝ × ℝ` (including `y = 0`). -/
theorem sigmaM_diag_combo_all (c ν : ℝ) (chio : ℝ → ℝ) (M : Chart → Mat3) (y : ℝ × ℝ) :
    sigmaM c ν chio M y 2 2 - (sigmaM c ν chio M y 0 0 + sigmaM c ν chio M y 1 1) / 2 =
      (1 / 2 : ℝ) * ((Real.sqrt (y.1 ^ 2 + y.2 ^ 2))⁻¹ *
        (2 * phaseMean c ν chio M (y.1 ^ 2 + y.2 ^ 2)⁻¹ 2 2 -
          phaseMean c ν chio M (y.1 ^ 2 + y.2 ^ 2)⁻¹ 0 0)) := by
  by_cases hy : y = 0
  · subst hy
    simp [sigmaM_zero_zero, sigmaM_one_one, sigmaM_two_two]
  · exact sigmaM_diag_combo c ν chio M hy

/-- Polar-coordinate evaluation of `sigmaInt c ν chio M 2 2 - sigmaInt c ν chio M 0 0`
(source 4859-4862, 4584-4587). -/
theorem sigmaIntPolar (chio : ℝ → ℝ) : FlatUnif.G5.SigmaIntPolar chio := by
  intro c ν hc hν hχ M hM h01
  have hI00 := integrable_sigmaM_entry hc hν hχ hM 0 0
  have hI11 := integrable_sigmaM_entry hc hν hχ hM 1 1
  have hI22 := integrable_sigmaM_entry hc hν hχ hM 2 2
  have hsub : sigmaInt c ν chio M 2 2 - sigmaInt c ν chio M 0 0 =
      ∫ y : ℝ × ℝ, (sigmaM c ν chio M y 2 2 -
        (sigmaM c ν chio M y 0 0 + sigmaM c ν chio M y 1 1) / 2) := by
    have h1 : (∫ y : ℝ × ℝ, (sigmaM c ν chio M y 0 0 + sigmaM c ν chio M y 1 1) / 2) =
        (sigmaInt c ν chio M 0 0 + sigmaInt c ν chio M 1 1) / 2 := by
      rw [integral_div, integral_add hI00 hI11]
      rfl
    have h2 : (∫ y : ℝ × ℝ, (sigmaM c ν chio M y 2 2 -
        (sigmaM c ν chio M y 0 0 + sigmaM c ν chio M y 1 1) / 2)) =
        sigmaInt c ν chio M 2 2 -
          ∫ y : ℝ × ℝ, (sigmaM c ν chio M y 0 0 + sigmaM c ν chio M y 1 1) / 2 :=
      integral_sub hI22 ((hI00.add hI11).div_const 2)
    linarith
  set H : ℝ → ℝ := fun u =>
    2 * phaseMean c ν chio M u 2 2 - phaseMean c ν chio M u 0 0 with hH_def
  have hHm : AEStronglyMeasurable H (volume.restrict (Ioi (0 : ℝ))) :=
    ((phaseMean_entry_aesm hν hχ M hM 2 2).const_mul 2).sub
      (phaseMean_entry_aesm hν hχ M hM 0 0)
  have ha : (0 : ℝ) < 6 / 5 / ν := div_pos (by norm_num) hν
  have hH_zero : ∀ u : ℝ, u ∉ Ioi (6 / 5 / ν) → H u = 0 := by
    intro u hu
    have hle : u ≤ 6 / 5 / ν := not_lt.1 hu
    have hνu : ν * u ≤ 6 / 5 := by
      calc ν * u ≤ ν * (6 / 5 / ν) := mul_le_mul_of_nonneg_left hle hν.le
        _ = 6 / 5 := by field_simp
    simp [hH_def, phaseMean, hχ.zero _ hνu]
  have hH_ae : ∀ᵐ u ∂volume,
      H u = chio (ν * u) * ConcreteYF.cellInt c (fun p => 2 * M (u, p) 2 2 - M (u, p) 0 0) := by
    filter_upwards [ae_integrable_entry_slice hν hM] with u hu
    by_cases hmem : u ∈ Ioi (6 / 5 / ν)
    · have h22 := hu hmem 2 2
      have h00 := hu hmem 0 0
      have hpm22 : phaseMean c ν chio M u 2 2 =
          chio (ν * u) * ∫ x, M (u, x) 2 2 ∂(Cyl.avgμ c) := by simp [phaseMean]
      have hpm00 : phaseMean c ν chio M u 0 0 =
          chio (ν * u) * ∫ x, M (u, x) 0 0 ∂(Cyl.avgμ c) := by simp [phaseMean]
      dsimp only [H]
      rw [cellInt_eq_integral_avgμ hc.le, integral_sub (h22.const_mul 2) h00, integral_const_mul,
        hpm22, hpm00]
      ring
    · have hle : u ≤ 6 / 5 / ν := not_lt.1 hmem
      have hνu : ν * u ≤ 6 / 5 := by
        calc ν * u ≤ ν * (6 / 5 / ν) := mul_le_mul_of_nonneg_left hle hν.le
          _ = 6 / 5 := by field_simp
      rw [hH_zero u hmem, hχ.zero _ hνu, zero_mul]
  have hHint_old : Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ)) * H u)
      (volume.restrict (Ioi (6 / 5 / ν))) := by
    have hp : Measurable (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) := measurable_id.pow_const _
    have hHm_old : AEStronglyMeasurable H (volume.restrict (Ioi (6 / 5 / ν))) :=
      hHm.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi ha.le) le_rfl)
    refine Integrable.mono' ((w_int hν hχ M hM).const_mul 3)
      (hp.aestronglyMeasurable.mul hHm_old) ?_
    filter_upwards [ae_restrict_of_ae hH_ae, ae_integrable_frob_slice hν hM,
      ae_restrict_mem measurableSet_Ioi] with u hu_eq hu_frob hu_mem
    have hu0 : 0 < u := ha.trans hu_mem
    have hχ0 : 0 ≤ chio (ν * u) := (hχ.range _).1
    have hr0 : 0 ≤ u ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hu0.le _
    have hcell : |ConcreteYF.cellInt c (fun p => 2 * M (u, p) 2 2 - M (u, p) 0 0)| ≤
        3 * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c) := by
      rw [cellInt_eq_integral_avgμ hc.le, ← Real.norm_eq_abs, ← integral_const_mul]
      refine norm_integral_le_of_norm_le (hu_frob.const_mul 3) (Eventually.of_forall fun p => ?_)
      rw [Real.norm_eq_abs]
      exact abs_two_zz_sub_rr_le (M (u, p))
    rw [Real.norm_eq_abs, hu_eq, abs_mul, abs_mul, abs_of_nonneg hr0, abs_of_nonneg hχ0]
    calc u ^ (-(3 / 2 : ℝ)) * (chio (ν * u) *
          |ConcreteYF.cellInt c (fun p => 2 * M (u, p) 2 2 - M (u, p) 0 0)|)
        ≤ u ^ (-(3 / 2 : ℝ)) * (chio (ν * u) * (3 * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcell hχ0) hr0
      _ = 3 * (u ^ (-(3 / 2 : ℝ)) * (chio (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c))) := by ring
  have hHint : Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ)) * H u)
      (volume.restrict (Ioi (0 : ℝ))) := by
    have hind : (fun u : ℝ => u ^ (-(3 / 2 : ℝ)) * H u) =
        (Ioi (6 / 5 / ν)).indicator (fun u : ℝ => u ^ (-(3 / 2 : ℝ)) * H u) := by
      funext u
      by_cases hu : u ∈ Ioi (6 / 5 / ν)
      · rw [Set.indicator_of_mem hu]
      · rw [Set.indicator_of_notMem hu, hH_zero u hu, mul_zero]
    rw [hind, integrable_indicator_iff measurableSet_Ioi]
    unfold IntegrableOn
    rw [Measure.restrict_restrict measurableSet_Ioi, Set.Ioi_inter_Ioi, sup_eq_left.2 ha.le]
    exact hHint_old
  obtain ⟨_, hPol⟩ := planePolar_bochner H hHm hHint
  have hfun : (fun y : ℝ × ℝ => sigmaM c ν chio M y 2 2 -
      (sigmaM c ν chio M y 0 0 + sigmaM c ν chio M y 1 1) / 2) =
      fun y : ℝ × ℝ => (1 / 2 : ℝ) * ((Real.sqrt (y.1 ^ 2 + y.2 ^ 2))⁻¹ *
        H ((y.1 ^ 2 + y.2 ^ 2)⁻¹)) := by
    funext y
    exact sigmaM_diag_combo_all c ν chio M y
  have hI_congr : (∫ u in Ioi (0 : ℝ), u ^ (-(3 / 2 : ℝ)) * H u) =
      ∫ u in Ioi (0 : ℝ),
        chio (ν * u) * u ^ (-(3 / 2 : ℝ)) *
          ConcreteYF.cellInt c (fun p => 2 * M (u, p) 2 2 - M (u, p) 0 0) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hH_ae] with u hu
    rw [hu]
    ring
  rw [hsub, hfun, integral_const_mul, hPol, hI_congr]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5
