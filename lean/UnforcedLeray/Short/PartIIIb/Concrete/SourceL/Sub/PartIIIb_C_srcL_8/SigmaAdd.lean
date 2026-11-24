import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_8
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtCongr

/-!
# Almost-everywhere additivity of `Σ_M` (`SigmaAddAE`, source 4766-4775, 4917-4937)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

open UnforcedLeray UnforcedLeray.Short.PartIIIb.Concrete

theorem abs_entry_le_frob_aux (A : Mat3) (i j : Fin 3) : |A i j| ≤ frob A := by
  unfold frob
  apply Real.abs_le_sqrt
  calc A i j ^ 2 ≤ ∑ j', A i j' ^ 2 :=
        Finset.single_le_sum (f := fun j' => A i j' ^ 2) (fun j' _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', A i' j' ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', A i' j' ^ 2)
          (fun i' _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)

/-- For a.e. old age `u > 6/(5ν)` the cell-slices of the entries are integrable. -/
theorem slice_entry_aux (c ν : ℝ) (hν : 0 < ν) (F : Chart → Mat3) (hF : OldThinFinite c ν F) :
    ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Ioi (6 / 5 / ν) →
      ∀ i j, Integrable (fun x => F (u, x) i j) (Cyl.avgμ c) := by
  obtain ⟨hmeas, hint⟩ := hF
  have hSF : SFinite (Cyl.avgμ c) := by unfold Cyl.avgμ Cyl.cellμ; infer_instance
  unfold oldMeasure at hmeas hint
  have h1 := hint.prod_right_ae
  have h2 := hmeas.prodMk_left
  rw [ae_restrict_iff' measurableSet_Ioi] at h1 h2
  filter_upwards [h1, h2] with u hu1 hu2 hu
  intro i j
  have hpos : 0 < u := lt_trans (div_pos (by norm_num) hν) (Set.mem_Ioi.mp hu)
  have hid : ∀ x, u ^ (3 / 2 : ℝ) * (u ^ (-(3 / 2) : ℝ) * frob (F (u, x))) = frob (F (u, x)) := by
    intro x
    rw [← mul_assoc, ← Real.rpow_add hpos]
    norm_num
  have hg : Integrable (fun x => u ^ (3 / 2 : ℝ) * (u ^ (-(3 / 2) : ℝ) * frob (F (u, x)))) (Cyl.avgμ c) :=
    (hu1 hu).const_mul _
  have hmeasE : AEStronglyMeasurable (fun x => F (u, x) i j) (Cyl.avgμ c) :=
    (show Continuous fun A : Mat3 => A i j by fun_prop).comp_aestronglyMeasurable (hu2 hu)
  refine hg.mono' hmeasE (Filter.Eventually.of_forall fun x => ?_)
  rw [hid x, Real.norm_eq_abs]
  exact abs_entry_le_frob_aux _ i j

/-- Phase-mean additivity for a.e. old age. -/
theorem phaseMean_add_ae_aux (c ν : ℝ) (χo : ℝ → ℝ) (hχo : IsOutwardCutoff χo) (hν : 0 < ν)
    (M M' : Chart → Mat3) (hM : OldThinFinite c ν M) (hM' : OldThinFinite c ν M') :
    ∀ᵐ u ∂(volume : Measure ℝ),
      phaseMean c ν χo (M + M') u = phaseMean c ν χo M u + phaseMean c ν χo M' u := by
  filter_upwards [slice_entry_aux c ν hν M hM, slice_entry_aux c ν hν M' hM'] with u h1 h2
  by_cases hu : u ∈ Ioi (6 / 5 / ν)
  · funext i j
    unfold phaseMean
    by_cases hij : i = 1 ∨ j = 1
    · simp [hij]
    · simp only [hij, ite_false, Pi.add_apply]
      rw [integral_add (h1 hu i j) (h2 hu i j), mul_add]
  · funext i j
    have hle : ν * u ≤ 6 / 5 := by
      have : u ≤ 6 / 5 / ν := not_lt.mp hu
      rw [le_div_iff₀ hν] at this
      linarith
    unfold phaseMean
    simp [hχo.zero _ hle]

/-- The Cartesian source is additive almost everywhere (source 4766-4775). -/
theorem sigmaM_add_ae_aux : UnforcedLeray.Short.PartIIIb.Concrete.SigmaAddAE := by
  intro c ν χo hc hν hχo M M' hM hM'
  have hadd := phaseMean_add_ae_aux c ν χo hχo hν M M' hM hM'
  have hN0 : volume {u : ℝ | ¬ (phaseMean c ν χo (M + M') u =
      phaseMean c ν χo M u + phaseMean c ν χo M' u)} = 0 := ae_iff.mp hadd
  have hx : ∀ᵐ x' ∂(volume : Measure (ℝ × ℝ)), sigmaM c ν χo (M + M') x' =
      sigmaM c ν χo M x' + sigmaM c ν χo M' x' := by
    refine ae_iff.mpr (measure_mono_null (fun x' hx' => ?_) (vol_preimage_radius_sq_null _ hN0))
    intro hh
    apply hx'
    funext a b
    simp only [sigmaM, Pi.add_apply]
    simp only [hh, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  filter_upwards [hx] with x' hx'
  exact hx'

theorem sigmaM_add_ae : UnforcedLeray.Short.PartIIIb.Concrete.SigmaAddAE :=
  sigmaM_add_ae_aux
