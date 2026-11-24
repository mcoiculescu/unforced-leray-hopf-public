import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.LiftRead
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.OfLift
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth.WeakS

/-!
# `PartII-b:T10/7/2` (`GradBound`): gradient bound in `Y_r`

Source of record: `the November 2 reference manuscript`, lines 1912-1921
(`∂_ρ(√s b) = s Q_ε b`, `∂_z(√s b) = s ∂_η b`) and 1639-1668 (chart, `Q_ε`).

Proof outline:
1. `gradLiftRead` and `gradWeakOfLift` construct profiles `Qb', Eb'` whose lifts equal the radial
   combination `radComb g` and `g 2` a.e. and which satisfy `HasWeakVec` for `Q_ε b` and `∂_η b`.
2. Uniqueness of weak derivatives on `{s > 0}` (`hasWeakVec_unique`, via
   `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) identifies `Qb = Qb'` and `Eb = Eb'`
   a.e. on `{s > 0}`, hence `phaseLpNorm` of `NvC ε⁻¹ (sqrtS Qb)` and `NvC ε⁻¹ (sqrtS Eb)` agree
   with those of `Qb'` and `Eb'` (`phaseLpNorm_NvC`).
3. Monotonicity (`|y_j / ϱ| ≤ 1`) and Minkowski (`eLpNorm_add_le`) on the phase measure `gleMu`
   bound the norms by `∑ j, phaseLpNorm (2 * ε * c) r (g j)` with `K = 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

namespace GradBoundHelp

/-- Uniqueness of scalar weak first-order derivatives on `{s > 0}`. -/
lemma hasWeakFO_unique {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {u g g' : Coord → ℂ}
    (hw : HasWeakFO v d u g) (hw' : HasWeakFO v d u g') :
    ∀ᵐ x : Coord, 0 < x.1 → g x = g' x := by
  have : (volume : Measure Coord).IsAddHaarMeasure := DriftWeakSHelp.instIsAddHaarVolCoord
  have hloc : LocallyIntegrableOn (fun x => g x - g' x) DriftWeakSHelp.Upos volume :=
    (DriftWeakSHelp.locInt_of_tests g (fun φ hφ => (hw.1 φ hφ).2)).sub
      (DriftWeakSHelp.locInt_of_tests g' (fun φ hφ => (hw'.1 φ hφ).2))
  have htest : ∀ φ : Coord → ℝ, IsCoordTest φ →
      ∫ x, (g x - g' x) * (φ x : ℂ) = 0 := by
    intro φ hφ
    have hA : Integrable (fun x => g x * (φ x : ℂ)) := (hw.1 φ hφ).2
    have hB : Integrable (fun x => g' x * (φ x : ℂ)) := (hw'.1 φ hφ).2
    have hsub : ∫ x, (g x - g' x) * (φ x : ℂ) =
        (∫ x, g x * (φ x : ℂ)) - ∫ x, g' x * (φ x : ℂ) := by
      rw [← integral_sub hA hB]
      congr 1; funext x; ring
    rw [hsub, hw.2 φ hφ, hw'.2 φ hφ, sub_self]
  have hae := (isOpen_Ioi.prod isOpen_univ).ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (by
    intro χ hχs hχc hχU
    have hχt : IsCoordTest χ := ⟨hχs, hχc, hχU⟩
    have hχ := htest χ hχt
    simp only [Complex.real_smul]
    convert hχ using 2
    funext x; ring)
  filter_upwards [hae] with x hx hpos
  exact sub_eq_zero.1 (hx (DriftWeakSHelp.mem_Upos.2 hpos))

/-- Uniqueness of vector weak first-order derivatives on `{s > 0}`. -/
lemma hasWeakVec_unique {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {b G G' : CProf}
    (hw : HasWeakVec v d b G) (hw' : HasWeakVec v d b G') :
    ∀ᵐ x : Coord, 0 < x.1 → G x = G' x := by
  have h0 := hasWeakFO_unique (hw 0) (hw' 0)
  have h1 := hasWeakFO_unique (hw 1) (hw' 1)
  filter_upwards [h0, h1] with x hx0 hx1 hpos
  ext i
  fin_cases i
  · exact hx0 hpos
  · exact hx1 hpos

/-- Profiles agreeing a.e. on `{s > 0}` have the same lifted `phaseLpNorm` after `sqrtS`. -/
lemma phaseLpNorm_NvC_sqrtS_eq {c ε r : ℝ} (hc : 0 < c) (hε : 0 < ε) (hr : 0 < r)
    {G G' : CProf} (hGp : QPeriodic c (sqrtS G)) (hGm : AEStronglyMeasurable (sqrtS G) (hMeas c r))
    (hG'p : QPeriodic c (sqrtS G')) (hG'm : AEStronglyMeasurable (sqrtS G') (hMeas c r))
    (hae : ∀ᵐ x : Coord, 0 < x.1 → G x = G' x) :
    phaseLpNorm (2 * ε * c) r (NvC ε⁻¹ (sqrtS G)) =
      phaseLpNorm (2 * ε * c) r (NvC ε⁻¹ (sqrtS G')) := by
  rw [phaseLpNorm_NvC hc hr hε (sqrtS G) hGp hGm,
      phaseLpNorm_NvC hc hr hε (sqrtS G') hG'p hG'm]
  congr 1
  unfold hNorm
  refine eLpNorm_congr_ae ?_
  filter_upwards [ageμ_ae_pos c (r / 2 - 5 / 2),
      (ageμ_ac_volume c (r / 2 - 5 / 2)).ae_le hae] with x hxpos hx
  simp only [sqrtS, hx hxpos]

/-- `phaseLpNorm` expressed via `eLpNorm` on `gleMu P`. -/
lemma phaseLpNorm_eq_eLpNorm (P r : ℝ) (hr : 0 < r) (f : ℝ × Space → CVec3)
    (hf : AEStronglyMeasurable f volume) :
    phaseLpNorm P r f = (ENNReal.ofReal P⁻¹) ^ (1 / r) * eLpNorm f (ENNReal.ofReal r) (gleMu P) := by
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr).ne'
  have hptop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [gle_phaseLpNorm_eq P r f hf,
      ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.2 hr.le),
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop,
      ENNReal.toReal_ofReal hr.le]

/-- Triangle + radial weight bound for `radComb g`. -/
lemma phaseLpNorm_radComb_le (P r : ℝ) (hr1 : 1 < r) (g : Fin 3 → ℝ × Space → CVec3)
    (hg0 : AEStronglyMeasurable (g 0) volume) (hg1 : AEStronglyMeasurable (g 1) volume) :
    phaseLpNorm P r (radComb g) ≤ phaseLpNorm P r (g 0) + phaseLpNorm P r (g 1) := by
  have hr0 : 0 < r := by linarith
  have hr1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := ENNReal.one_le_ofReal.2 hr1.le
  set f0 : ℝ × Space → CVec3 := fun x =>
    (((x.2 0 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) • g 0 x
  set f1 : ℝ × Space → CVec3 := fun x =>
    (((x.2 1 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) • g 1 x
  have hθ0 : Measurable fun x : ℝ × Space =>
      (((x.2 0 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) := by fun_prop
  have hθ1 : Measurable fun x : ℝ × Space =>
      (((x.2 1 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) := by fun_prop
  have hf0m : AEStronglyMeasurable f0 volume := hθ0.aestronglyMeasurable.smul hg0
  have hf1m : AEStronglyMeasurable f1 volume := hθ1.aestronglyMeasurable.smul hg1
  have hradm : AEStronglyMeasurable (radComb g) volume := hf0m.add hf1m
  rw [phaseLpNorm_eq_eLpNorm P r hr0 (radComb g) hradm,
      phaseLpNorm_eq_eLpNorm P r hr0 (g 0) hg0,
      phaseLpNorm_eq_eLpNorm P r hr0 (g 1) hg1, ← mul_add]
  gcongr
  have hadd : eLpNorm (radComb g) (ENNReal.ofReal r) (gleMu P) ≤
      eLpNorm f0 (ENNReal.ofReal r) (gleMu P) + eLpNorm f1 (ENNReal.ofReal r) (gleMu P) :=
    eLpNorm_add_le (hf0m.mono_ac (gleMu_ac P)) (hf1m.mono_ac (gleMu_ac P)) hr1'
  refine hadd.trans (add_le_add ?_ ?_)
  · refine eLpNorm_mono_enorm fun z => ?_
    rw [enorm_smul]
    calc _ ≤ 1 * ‖g 0 z‖ₑ := by
          gcongr
          have := GWQ.theta_le (z.2 0) (z.2 1)
          simpa [enorm_eq_nnnorm] using this
      _ = ‖g 0 z‖ₑ := one_mul _
  · refine eLpNorm_mono_enorm fun z => ?_
    rw [enorm_smul]
    calc _ ≤ 1 * ‖g 1 z‖ₑ := by
          gcongr
          have := GWQ.theta_le (z.2 1) (z.2 0)
          simpa [enorm_eq_nnnorm, add_comm] using this
      _ = ‖g 1 z‖ₑ := one_mul _

end GradBoundHelp

open GradBoundHelp in
theorem gradBound_proof : UnforcedLeray.Short.IIb.GradBound := by
  intro r hr1 hr3
  have hr0 : 0 < r := by linarith
  refine ⟨1, zero_lt_one, ?_⟩
  intro c ε b g Qb Eb hc hε hb hgY hgp hQ hE hQp hQm hEp hEm
  obtain ⟨Qb', Eb', hQp', hQm', hEp', hEm', hE_ae, hQ_ae⟩ :=
    gradLiftRead c ε r b g hc hε hr1 hr3 hb hgY hgp
  obtain ⟨hQ', hE'⟩ :=
    gradWeakOfLift c ε r b g Qb' Eb' hc hε hr1 hr3 hb hgY hgp hQp' hQm' hEp' hEm' hE_ae hQ_ae
  have hQ_eq := phaseLpNorm_NvC_sqrtS_eq hc hε hr0 hQp hQm hQp' hQm' (hasWeakVec_unique hQ hQ')
  have hE_eq := phaseLpNorm_NvC_sqrtS_eq hc hε hr0 hEp hEm hEp' hEm' (hasWeakVec_unique hE hE')
  rw [hQ_eq, hE_eq, phaseLpNorm_congr_ae hQ_ae, phaseLpNorm_congr_ae hE_ae,
      ENNReal.ofReal_one, one_mul, Fin.sum_univ_three]
  gcongr
  exact phaseLpNorm_radComb_le (2 * ε * c) r hr1 g (hgY 0).meas (hgY 1).meas

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.gradBound_proof
