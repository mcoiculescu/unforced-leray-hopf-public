import UnforcedLeray.Short.PartIIb.Defs
import UnforcedLeray.Short.PartIIa.Tasks.F04bFieldToY.PeriodicFieldToYq
import UnforcedLeray.Short.PartIIa.Sub.F03Rep
import UnforcedLeray.Cons.L2.BackgroundConcrete.PhasePairF

/-!
# Bridge Part II-a / Part II-b: pointwise fields and elements of `Y_r` (general exponent)

Source of record: `the November 2 reference manuscript`, lines 1339-1349
(`Y_r`, `D_r`), 1409-1440 and 1478-1480 (Fubini packaging).

`HasRepY F W` : the pointwise field `W` is a jointly measurable representative of `F ∈ Y_q`.
* `exists_hasRepY` : `IsInYr P r W → ∃ F : Y_r, HasRepY F W ∧ ‖F‖ = (phaseLpNorm P r W).toReal`;
* `phasePair_eq_pairF_of_hasRepY` : the abstract phase pairing is `pairF` on a representative;
* `hasRepY_unique` : representatives determine the element of `Y_r` (a.e. class).
General-exponent version of `Sub/YqOfFields_{a,b,c}.lean` (which treat `r = 11/4` only).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Cons.C03.Concrete

/-- `W` is a jointly measurable representative of `F ∈ Y_q` (general exponent). -/
structure HasRepY {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] (F : Yq P q)
    (W : ℝ × Space → CVec3) : Prop where
  meas : AEStronglyMeasurable W volume
  slice : ∀ᵐ τ : ℝ, (fun y => W (τ, y)) =ᵐ[volume] (F (τ : AddCircle P) : Space → CVec3)

theorem exists_stronglyMeasurable_periodic (P : ℝ) [Fact (0 < P)] (r : ℝ) (hr : 0 < r)
    (W : ℝ × Space → CVec3) (hW : IsInYr P r W) :
    ∃ W' : ℝ × Space → CVec3, StronglyMeasurable W' ∧ W' =ᵐ[volume] W ∧
      (∀ᵐ τ : ℝ, (fun y => W' (τ + P, y)) =ᵐ[volume] fun y => W' (τ, y)) ∧
      phaseLpNorm P r W' = phaseLpNorm P r W ∧
      ∫⁻ τ in Ioc (0:ℝ) P, ∫⁻ y, ‖W' (τ, y)‖ₑ ^ r < ⊤ := by
  set W' := hW.meas.mk W with hW'def
  have hsm : StronglyMeasurable W' := hW.meas.stronglyMeasurable_mk
  have hE : W' =ᵐ[volume] W := hW.meas.ae_eq_mk.symm
  have hE' : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure Space)), W' x = W x := by
    rw [← Measure.volume_eq_prod]
    exact hE
  have hT : MeasurePreserving (fun x : ℝ × Space => (x.1 + P, x.2))
      ((volume : Measure ℝ).prod (volume : Measure Space))
      ((volume : Measure ℝ).prod (volume : Measure Space)) :=
    (measurePreserving_add_right (volume : Measure ℝ) P).prod
      (MeasurePreserving.id (volume : Measure Space))
  have hShift : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure Space)),
      W' (x.1 + P, x.2) = W' x := by
    have hper : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure Space)),
        W (x.1 + P, x.2) = W x := by
      rw [← Measure.volume_eq_prod]
      exact hW.periodic
    filter_upwards [hT.quasiMeasurePreserving.ae hE', hper, hE'] with x h1 h2 h3
    exact h1.trans (h2.trans h3.symm)
  have hperiod : ∀ᵐ τ : ℝ, (fun y => W' (τ + P, y)) =ᵐ[volume] fun y => W' (τ, y) :=
    Measure.ae_ae_of_ae_prod (p := fun z : ℝ × Space => W' (z.1 + P, z.2) = W' z) hShift
  have h2 : ∀ᵐ τ : ℝ, ∀ᵐ y : Space, W' (τ, y) = W (τ, y) :=
    Measure.ae_ae_of_ae_prod (p := fun z : ℝ × Space => W' z = W z) hE'
  have hnorm_eq : ∀ s : ℝ, ∫⁻ τ in Ioc (0:ℝ) P, ∫⁻ y : Space, ‖W' (τ, y)‖ₑ ^ s
      = ∫⁻ τ in Ioc (0:ℝ) P, ∫⁻ y : Space, ‖W (τ, y)‖ₑ ^ s := by
    intro s
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae h2] with τ hτ
    refine lintegral_congr_ae ?_
    filter_upwards [hτ] with y hy
    rw [hy]
  refine ⟨W', hsm, hE, hperiod, ?_, ?_⟩
  · unfold phaseLpNorm
    rw [hnorm_eq r]
  · rw [hnorm_eq r]
    have hfin := hW.finite
    unfold phaseLpNorm at hfin
    have hI : ENNReal.ofReal P⁻¹ * ∫⁻ τ in Ioc (0:ℝ) P, ∫⁻ y : Space, ‖W (τ, y)‖ₑ ^ r < ⊤ :=
      (ENNReal.rpow_lt_top_iff_of_pos (by positivity)).1 hfin
    have hPne : ENNReal.ofReal P⁻¹ ≠ 0 :=
      (ENNReal.ofReal_pos.2 (inv_pos.2 (inferInstance : Fact (0 < P)).out)).ne'
    exact ENNReal.lt_top_of_mul_ne_top_right hI.ne hPne

/-- The `Y_q` norm of an element with a strongly measurable representative is the phase `L^r`
norm (extended-valued); general exponent `q` with `q.toReal = r`. -/
theorem phaseLpNorm_eq_enorm_q {P : ℝ} [Fact (0 < P)] (r : ℝ) (hr : 0 < r) {q : ℝ≥0∞}
    [Fact (1 ≤ q)] (hq : q ≠ ⊤) (hp : q.toReal = r) (W' : ℝ × Space → CVec3) (F : Yq P q)
    (hF : UnforcedLeray.Short.PartIIa.Rep.IsRep F W') :
    phaseLpNorm P r W' = ‖F‖ₑ := by
  have hI : ∫⁻ t in Ioc (0:ℝ) P, ‖F (t : AddCircle P)‖ₑ ^ q.toReal
      = ∫⁻ t in Ioc (0:ℝ) P, ∫⁻ y : Space, ‖W' (t, y)‖ₑ ^ q.toReal := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hF.slice] with t ht
    rw [← lintegral_enorm_rpow_Lp (F (t : AddCircle P)) hq]
    refine lintegral_congr_ae ?_
    filter_upwards [ht] with y hy
    rw [hy]
  have hmain : ‖F‖ₑ ^ q.toReal
      = ENNReal.ofReal P⁻¹ *
        ∫⁻ t in Ioc (0:ℝ) P, ∫⁻ y : Space, ‖W' (t, y)‖ₑ ^ q.toReal := by
    rw [B0411.enorm_rpow_Yq F hq, hI]
  rw [hp] at hmain
  unfold phaseLpNorm
  rw [← hmain, one_div]
  exact ENNReal.rpow_rpow_inv hr.ne' _

/-- The `Y_q` norm of an element with a strongly measurable representative is the phase `L^r`
norm (extended-valued). -/
theorem phaseLpNorm_eq_enorm {P : ℝ} [Fact (0 < P)] (r : ℝ) (hr : 0 < r)
    [Fact (1 ≤ ENNReal.ofReal r)] (W' : ℝ × Space → CVec3) (F : Yq P (ENNReal.ofReal r))
    (hF : UnforcedLeray.Short.PartIIa.Rep.IsRep F W') :
    phaseLpNorm P r W' = ‖F‖ₑ :=
  phaseLpNorm_eq_enorm_q r hr ENNReal.ofReal_ne_top (ENNReal.toReal_ofReal hr.le) W' F hF

/-- **(a)** Every `f ∈ Y_r` (pointwise) is represented by an element of `Y_q` (`q.toReal = r`) of
the same norm. -/
theorem exists_hasRepY_q (P : ℝ) [Fact (0 < P)] (r : ℝ) (hr : 0 < r) {q : ℝ≥0∞}
    [Fact (1 ≤ q)] (hq : q ≠ ⊤) (hp : q.toReal = r) (f : ℝ × Space → CVec3) (hf : IsInYr P r f) :
    ∃ F : Yq P q, HasRepY F f ∧ ‖F‖ = (phaseLpNorm P r f).toReal := by
  obtain ⟨W', hsm, hE, hper, hnorm, hfin⟩ := exists_stronglyMeasurable_periodic P r hr f hf
  have hfin' : ∫⁻ τ in Ioc (0:ℝ) P, ∫⁻ y, ‖W' (τ, y)‖ₑ ^ q.toReal < ⊤ := by
    rw [hp]; exact hfin
  obtain ⟨F, hF⟩ := UnforcedLeray.Short.PartIIa.periodicFieldToYq_proof q hq P W' hsm hper hfin'
  have h2 : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure Space)), W' x = f x := by
    rw [← Measure.volume_eq_prod]; exact hE
  have h3 : ∀ᵐ τ : ℝ, ∀ᵐ y : Space, W' (τ, y) = f (τ, y) :=
    Measure.ae_ae_of_ae_prod (p := fun z : ℝ × Space => W' z = f z) h2
  refine ⟨F, ⟨hf.meas, ?_⟩, ?_⟩
  · filter_upwards [hF.slice, h3] with τ h1 h4
    exact (by filter_upwards [h4] with y hy using hy.symm : (fun y => f (τ, y)) =ᵐ[volume]
      fun y => W' (τ, y)).trans h1
  · have := phaseLpNorm_eq_enorm_q r hr hq hp W' F hF
    rw [← hnorm, this, toReal_enorm]

/-- **(a)** Every `f ∈ Y_r` (pointwise) is represented by an element of `Y_r` of the same norm. -/
theorem exists_hasRepY (P : ℝ) [Fact (0 < P)] (r : ℝ) (hr : 0 < r)
    [Fact (1 ≤ ENNReal.ofReal r)] (f : ℝ × Space → CVec3) (hf : IsInYr P r f) :
    ∃ F : Yq P (ENNReal.ofReal r), HasRepY F f ∧ ‖F‖ = (phaseLpNorm P r f).toReal :=
  exists_hasRepY_q P r hr ENNReal.ofReal_ne_top (ENNReal.toReal_ofReal hr.le) f hf

/-- The abstract phase pairing against a representative is `pairF`. -/
theorem phasePair_eq_pairF_of_hasRepY {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (F : Yq P q) (W : ℝ × Space → CVec3) (hW : HasRepY F W) {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) : phasePair P q Φ F = pairF P Φ W := by
  rw [phasePair_eq_periodIntegral hΦ F]
  simp only [zero_add, pairF, phaseInt]
  congr 1
  have h2 : ∀ᵐ τ : ℝ, ∫ y, dotL (Φ (τ, y)) ((F (τ : AddCircle P) : Space → CVec3) y) =
      ∫ y, dotL (Φ (τ, y)) (W (τ, y)) := by
    filter_upwards [hW.slice] with τ hτ
    apply integral_congr_ae
    filter_upwards [hτ] with y hy
    rw [← hy]
  exact setIntegral_congr_ae measurableSet_Ioc (by
    filter_upwards [h2] with τ hτ _ using hτ)

end UnforcedLeray.Short.IIb
