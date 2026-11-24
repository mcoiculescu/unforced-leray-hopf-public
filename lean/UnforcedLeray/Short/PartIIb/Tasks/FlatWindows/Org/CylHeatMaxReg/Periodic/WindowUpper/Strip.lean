import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_2

/-!
# Helpers for `ChmWindowUpper` / `ChmWindowLower`: strip identity for a.e. `q`-periodic functions.

Source `the November 2 reference manuscript` lines 1933-1935.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace WinStrip

lemma qShift_eq (c : ℝ) (x : Coord) : qShift c x = x + (0, (c, 0)) := by
  simp [qShift, Prod.ext_iff]

lemma cylMeas_ac (c : ℝ) : cylMeas c ≪ (volume : Measure Coord) := by
  have h : cylMeas c ≪ (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) := by
    refine Measure.AbsolutelyContinuous.prod (Measure.AbsolutelyContinuous.refl _) ?_
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    exact Measure.smul_absolutelyContinuous.trans Measure.restrict_le_self.absolutelyContinuous
  simpa [Measure.volume_eq_prod] using h

/-- Integer translates of an a.e.-periodic function agree a.e. -/
lemma ae_shift_int (c : ℝ) {F : Coord → ℝ≥0∞} (hper : ∀ᵐ x : Coord ∂volume, F (qShift c x) = F x)
    (n : ℤ) : ∀ᵐ x : Coord ∂volume, F (x + (0, ((n : ℝ) * c, 0))) = F x := by
  have hper' : ∀ᵐ x : Coord ∂volume, F (x + (0, (c, 0))) = F x := by
    simpa [qShift_eq] using hper
  have hnat : ∀ k : ℕ, ∀ᵐ x : Coord ∂volume, F (x + (0, ((k : ℝ) * c, 0))) = F x := by
    intro k
    induction k with
    | zero =>
      refine Filter.Eventually.of_forall fun x => ?_
      have e : x + (0, (((0 : ℕ) : ℝ) * c, 0)) = x := by ext <;> simp
      rw [e]
    | succ k ih =>
      have h2 : ∀ᵐ x : Coord ∂volume, F ((x + (0, ((k : ℝ) * c, 0))) + (0, (c, 0))) =
          F (x + (0, ((k : ℝ) * c, 0))) :=
        (measurePreserving_add_right (volume : Measure Coord)
          ((0, ((k : ℝ) * c, 0)) : Coord)).quasiMeasurePreserving.ae hper'
      filter_upwards [ih, h2] with x h1 h2
      have e : x + (0, (((k + 1 : ℕ) : ℝ) * c, 0)) =
          (x + (0, ((k : ℝ) * c, 0))) + (0, (c, 0)) := by
        ext <;> simp <;> ring
      rw [e, h2, h1]
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · simpa using hnat k
  · have h3 : ∀ᵐ x : Coord ∂volume, F ((x - (0, ((k : ℝ) * c, 0))) + (0, ((k : ℝ) * c, 0))) =
        F (x - (0, ((k : ℝ) * c, 0))) :=
      (measurePreserving_sub_right (volume : Measure Coord)
        ((0, ((k : ℝ) * c, 0)) : Coord)).quasiMeasurePreserving.ae (hnat k)
    filter_upwards [h3] with x h
    have e : x + (0, (((-(k : ℤ) : ℤ) : ℝ) * c, 0)) = x - (0, ((k : ℝ) * c, 0)) := by
      ext <;> simp <;> ring
    rw [e]
    simpa using h.symm

/-- Reduction of the `q`-coordinate to `[0, c)`. -/
def red (c : ℝ) (x : Coord) : Coord := (x.1, (x.2.1 - c * (⌊x.2.1 / c⌋ : ℝ), x.2.2))

lemma measurable_red (c : ℝ) : Measurable (red c) := by
  unfold red
  refine measurable_fst.prodMk ((?_ : Measurable fun x : Coord => x.2.1 - c * (⌊x.2.1 / c⌋ : ℝ)).prodMk
    (measurable_snd.comp measurable_snd))
  have h1 : Measurable fun x : Coord => x.2.1 := measurable_fst.comp measurable_snd
  exact h1.sub (measurable_const.mul
    ((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp (Int.measurable_floor.comp (h1.div_const c))))

lemma red_qShift {c : ℝ} (hc : 0 < c) (x : Coord) : red c (qShift c x) = red c x := by
  have : ⌊(x.2.1 + c) / c⌋ = ⌊x.2.1 / c⌋ + 1 := by
    rw [add_div, div_self hc.ne', Int.floor_add_one]
  simp only [red, qShift, this]
  push_cast
  ext <;> simp
  ring

/-- A measurable a.e.-periodic function agrees a.e. with a genuinely periodic one. -/
lemma ae_red {c : ℝ} {F : Coord → ℝ≥0∞}
    (hper : ∀ᵐ x : Coord ∂volume, F (qShift c x) = F x) :
    (fun x => F (red c x)) =ᵐ[volume] F := by
  have h := ae_all_iff.2 (ae_shift_int c hper)
  filter_upwards [h] with x hx
  have := hx (-⌊x.2.1 / c⌋)
  have e : red c x = x + (0, (((-⌊x.2.1 / c⌋ : ℤ) : ℝ) * c, 0)) := by
    ext <;> simp [red] <;> ring
  rw [e, this]

/-- Strip identity for a.e.-periodic measurable functions on `Coord`. -/
theorem lintegral_coord_strip {c : ℝ} (hc : 0 < c) (m : ℕ) (a : ℝ) {F : Coord → ℝ≥0∞}
    (hF : AEMeasurable F volume) (hper : ∀ᵐ x : Coord ∂volume, F (qShift c x) = F x) :
    ∫⁻ x in {x : Coord | x.2.1 ∈ Ico a (a + (m : ℝ) * c)}, F x ∂volume =
      ((m : ℝ≥0∞) * ENNReal.ofReal c) * ∫⁻ x, F x ∂(cylMeas c) := by
  set F0 : Coord → ℝ≥0∞ := hF.mk F with hF0
  have hm0 : Measurable F0 := hF.measurable_mk
  have he0 : F =ᵐ[volume] F0 := hF.ae_eq_mk
  have hper0 : ∀ᵐ x : Coord ∂volume, F0 (qShift c x) = F0 x := by
    have hq : ∀ᵐ x : Coord ∂volume, F (qShift c x) = F0 (qShift c x) := by
      have hmp : MeasurePreserving (qShift c) (volume : Measure Coord) volume := by
        have : qShift c = fun x => x + (0, (c, 0)) := funext (qShift_eq c)
        rw [this]; exact measurePreserving_add_right _ _
      exact hmp.quasiMeasurePreserving.ae he0
    filter_upwards [hq, hper, he0] with x h1 h2 h3
    rw [← h1, h2, h3]
  set G : Coord → ℝ≥0∞ := fun x => F0 (red c x) with hG
  have hGm : Measurable G := hm0.comp (measurable_red c)
  have hGe : G =ᵐ[volume] F := (ae_red hper0).trans he0.symm
  have hGper : ∀ x, G (qShift c x) = G x := fun x => by simp only [hG, red_qShift hc]
  have hac := cylMeas_ac c
  have hGe' : G =ᵐ[cylMeas c] F := hac.ae_eq hGe
  have hE : MeasurableSet {x : Coord | x.2.1 ∈ Ico a (a + (m : ℝ) * c)} :=
    (measurableSet_Ico).preimage (measurable_fst.comp measurable_snd)
  have h1 : ∫⁻ x in {x : Coord | x.2.1 ∈ Ico a (a + (m : ℝ) * c)}, F x ∂volume =
      ∫⁻ x in {x : Coord | x.2.1 ∈ Ico a (a + (m : ℝ) * c)}, G x ∂volume :=
    lintegral_congr_ae (ae_restrict_of_ae hGe.symm)
  rw [h1, ← lintegral_congr_ae hGe']
  have hset : {x : Coord | x.2.1 ∈ Ico a (a + (m : ℝ) * c)} =
      (univ : Set ℝ) ×ˢ (Ico a (a + (m : ℝ) * c) ×ˢ (univ : Set ℝ)) := by
    ext x; simp
  have hvol : (volume : Measure Coord).restrict {x : Coord | x.2.1 ∈ Ico a (a + (m : ℝ) * c)} =
      (volume : Measure ℝ).prod ((volume : Measure (ℝ × ℝ)).restrict
        (Ico a (a + (m : ℝ) * c) ×ˢ (univ : Set ℝ))) := by
    rw [hset, Measure.volume_eq_prod, ← Measure.restrict_univ (μ := (volume : Measure ℝ)),
      Measure.prod_restrict]
    simp [Measure.volume_eq_prod]
  have hslice : ∀ s : ℝ, UnforcedLeray.Cyl.IsPeriodic c (fun z : ℝ × ℝ => G (s, z)) := fun s z => by
    have := hGper (s, z)
    simpa [qShift] using this
  rw [hvol, lintegral_prod _ hGm.aemeasurable]
  unfold cylMeas
  rw [lintegral_prod _ hGm.aemeasurable]
  have hs : ∀ s : ℝ, ∫⁻ z in Ico a (a + (m : ℝ) * c) ×ˢ (univ : Set ℝ), G (s, z) =
      (m : ℝ≥0∞) * ∫⁻ z in UnforcedLeray.Cyl.cell c, G (s, z) := fun s =>
    lintegral_strips_eq hc (hslice s) m a
  have ha : ∀ s : ℝ, ∫⁻ z, G (s, z) ∂(UnforcedLeray.Cyl.avgμ c) =
      ENNReal.ofReal c⁻¹ * ∫⁻ z in UnforcedLeray.Cyl.cell c, G (s, z) := fun s =>
    UnforcedLeray.Cyl.lintegral_avgμ _
  simp_rw [hs, ha]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ (ENNReal.natCast_ne_top m)]
  have key : ENNReal.ofReal c * ENNReal.ofReal c⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one]
  rw [mul_comm (m : ℝ≥0∞) (ENNReal.ofReal c), mul_assoc, mul_left_comm (ENNReal.ofReal c) (m : ℝ≥0∞),
    ← mul_assoc (ENNReal.ofReal c), key, one_mul]

end WinStrip

end UnforcedLeray.Short.IIb
