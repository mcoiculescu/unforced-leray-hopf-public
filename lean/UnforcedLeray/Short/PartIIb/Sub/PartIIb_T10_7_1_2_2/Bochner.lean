import UnforcedLeray.Lib.AxisymmetricB.Lift
import Mathlib.MeasureTheory.Function.Floor

/-!
# `PartII-b:T10/7/1/2/2/2` helpers: Bochner version of the ring-chart phase average

Source of record: `the November 2 reference manuscript` lines 1639-1668
(chart `s = R²/ϱ²`, `q = R log(ϱ/R) + Rτ/2`, `η = Rz/ϱ`; `H = L²(s^{-3/2} ds dq/c dη)`,
`P = 2εc = 2c/R`).

* `qRed c` reduces the phase coordinate `q` into the cell `[-c/2, c/2)` (a shift by `k c`, `k ∈ ℤ`).
* `map_chartRed`: the image of `dτ|_{(0,P]} ⊗ dy` under `qRed c ∘ chart R` is
  `P π R² · ageμ c (-5/2)` (from `Axi.phaseAvg_ringChart` and `Axi.lintegral_ageμ`).
* `integral_chartRed`: Bochner form of the same identity for `ageμ c (-5/2)`-integrable `g`.
* `phase_chart_integral`: for `G` integrable for `ageμ c (-5/2)` and a.e. `q`-periodic on `s > 0`,
  `P⁻¹ ∫_0^P ∫ G(chart R τ y) dy dτ = π R² ∫ G dageμ c (-5/2)`. The exceptional set of the
  periodicity is saturated under the shifts by `k c`; its `qRed`-image is `ageμ`-null, hence its
  chart preimage is null for the phase measure.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.PhaseChartBochnerAux

open UnforcedLeray

/-- Translation by `k c` in the phase coordinate. -/
def shk (c : ℝ) (k : ℤ) (x : ℝ × (ℝ × ℝ)) : ℝ × (ℝ × ℝ) := (x.1, (x.2.1 + (k : ℝ) * c, x.2.2))

/-- Reduction of the phase coordinate into the cell `[-c/2, c/2)`. -/
def qRed (c : ℝ) (x : ℝ × (ℝ × ℝ)) : ℝ × (ℝ × ℝ) := shk c (-⌊(x.2.1 + c / 2) / c⌋) x

theorem measurable_shk (c : ℝ) (k : ℤ) : Measurable (shk c k) :=
  measurable_fst.prodMk ((measurable_snd.fst.add_const _).prodMk measurable_snd.snd)

theorem measurable_qRed (c : ℝ) : Measurable (qRed c) := by
  have hm : Measurable fun x : ℝ × (ℝ × ℝ) => (((-⌊(x.2.1 + c / 2) / c⌋ : ℤ)) : ℝ) :=
    (measurable_of_countable (fun n : ℤ => ((-n : ℤ) : ℝ))).comp
      (Measurable.floor ((measurable_snd.fst.add_const _).div_const c))
  exact measurable_fst.prodMk ((measurable_snd.fst.add (hm.mul_const c)).prodMk measurable_snd.snd)

theorem shk_zero (c : ℝ) (x : ℝ × (ℝ × ℝ)) : shk c 0 x = x := by
  simp [shk]

theorem shk_shk (c : ℝ) (k l : ℤ) (x : ℝ × (ℝ × ℝ)) : shk c k (shk c l x) = shk c (k + l) x := by
  simp only [shk, Prod.mk.injEq, true_and, and_true]
  push_cast
  ring

theorem shk_succ (c : ℝ) (k : ℤ) (x : ℝ × (ℝ × ℝ)) :
    shk c (k + 1) x = ((shk c k x).1, ((shk c k x).2.1 + c, (shk c k x).2.2)) := by
  simp only [shk, Prod.mk.injEq, true_and, and_true]
  push_cast
  ring

theorem qRed_mem {c : ℝ} (hc : 0 < c) (x : ℝ × (ℝ × ℝ)) :
    (qRed c x).2.1 ∈ Ico (-c / 2) (c / 2) := by
  simp only [qRed, shk]
  have h1 := mul_le_mul_of_nonneg_right (Int.floor_le ((x.2.1 + c / 2) / c)) hc.le
  have h2 := mul_lt_mul_of_pos_right (Int.lt_floor_add_one ((x.2.1 + c / 2) / c)) hc
  have hy : (x.2.1 + c / 2) / c * c = x.2.1 + c / 2 := by field_simp
  push_cast
  constructor <;> nlinarith

theorem qRed_of_mem {c : ℝ} (hc : 0 < c) {x : ℝ × (ℝ × ℝ)} (hx : x.2.1 ∈ Ico (-c / 2) (c / 2)) :
    qRed c x = x := by
  have h0 : ⌊(x.2.1 + c / 2) / c⌋ = 0 := by
    rw [Int.floor_eq_zero_iff, Set.mem_Ico]
    constructor
    · exact div_nonneg (by linarith [hx.1]) hc.le
    · rw [div_lt_one hc]; linarith [hx.2]
  simp [qRed, shk, h0]

theorem qRed_qRed {c : ℝ} (hc : 0 < c) (x : ℝ × (ℝ × ℝ)) : qRed c (qRed c x) = qRed c x :=
  qRed_of_mem hc (qRed_mem hc x)

theorem qRed_add {c : ℝ} (hc : 0 < c) (s q η : ℝ) :
    qRed c (s, (q + c, η)) = qRed c (s, (q, η)) := by
  have h : (q + c + c / 2) / c = (q + c / 2) / c + 1 := by
    field_simp
    ring
  simp only [qRed, shk, h, Int.floor_add_one, Prod.mk.injEq, true_and, and_true]
  push_cast
  ring

/-! ### The age measure lives on `s > 0` and on the cell; it is absolutely continuous -/

theorem ae_pos (c a : ℝ) : ∀ᵐ x ∂(Axi.ageμ c a), 0 < x.1 := by
  rw [ae_iff]
  have h : {x : ℝ × (ℝ × ℝ) | ¬ 0 < x.1} = Iic (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by
    ext x; simp
  have : SFinite (Cyl.avgμ c) := by unfold Cyl.avgμ; infer_instance
  have hI : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by
    ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and,
      not_lt]; exact id
  rw [h, Axi.ageμ, Measure.prod_prod, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, hI]
  simp

theorem ae_mem (c a : ℝ) : ∀ᵐ x ∂(Axi.ageμ c a), x.2.1 ∈ Ico (-c / 2) (c / 2) := by
  rw [ae_iff]
  unfold Axi.ageμ
  have : SFinite (Cyl.avgμ c) := by unfold Cyl.avgμ; infer_instance
  have heq : {x : ℝ × (ℝ × ℝ) | ¬ x.2.1 ∈ Ico (-c / 2) (c / 2)} =
      (univ : Set ℝ) ×ˢ ((Ico (-c / 2) (c / 2))ᶜ ×ˢ (univ : Set ℝ)) := by
    ext x; simp
  rw [heq, Measure.prod_prod]
  have : Cyl.avgμ c ((Ico (-c / 2) (c / 2))ᶜ ×ˢ (univ : Set ℝ)) = 0 := by
    rw [Cyl.avgμ, Measure.smul_apply, Cyl.cellμ, Measure.restrict_apply
      (measurableSet_Ico.compl.prod MeasurableSet.univ)]
    have : (Ico (-c / 2) (c / 2))ᶜ ×ˢ (univ : Set ℝ) ∩ Cyl.cell c = ∅ := by
      ext x; simp [Cyl.cell]
    simp [this]
  simp [this]

theorem ac_volume (c a : ℝ) : Axi.ageμ c a ≪ (volume : Measure (ℝ × (ℝ × ℝ))) := by
  rw [Axi.ageμ, Measure.volume_eq_prod]
  refine Measure.AbsolutelyContinuous.prod ?_ ?_
  · exact (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  · unfold Cyl.avgμ
    exact (Measure.smul_absolutelyContinuous).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

theorem volume_shk_preimage (c : ℝ) (k : ℤ) (N : Set (ℝ × (ℝ × ℝ))) :
    (volume : Measure (ℝ × (ℝ × ℝ))) (shk c k ⁻¹' N) = volume N := by
  have h : shk c k = fun x => ((0 : ℝ), ((k : ℝ) * c, (0 : ℝ))) + x := by
    funext x
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [shk, add_comm]
  have : (volume : Measure (ℝ × (ℝ × ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure (ℝ × ℝ))
  rw [h]
  exact measure_preimage_add _ _ _

/-! ### The phase measure and its image under the reduced chart -/

/-- The phase measure `dτ|_{(0,P]} ⊗ dy`. -/
abbrev phμ (P : ℝ) : Measure (ℝ × Space) := (volume.restrict (Ioc (0 : ℝ) P)).prod volume

/-- The chart followed by the reduction of the phase into the cell. -/
def chartRed (R c : ℝ) (z : ℝ × Space) : ℝ × (ℝ × ℝ) := qRed c (Axi.chart R z.1 z.2)

theorem measurable_chart (R : ℝ) : Measurable fun z : ℝ × Space => Axi.chart R z.1 z.2 :=
  ((Axi.measurable_age R).comp measurable_snd).prodMk
    ((Axi.measurable_phase R).prodMk ((Axi.measurable_trans R).comp measurable_snd))

theorem measurable_chartRed (R c : ℝ) : Measurable (chartRed R c) :=
  (measurable_qRed c).comp (measurable_chart R)

/-- The image of the phase measure under the reduced chart is `P π R² · ageμ c (-5/2)`. -/
theorem map_chartRed {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R) :
    (phμ P).map (chartRed R c) =
      ENNReal.ofReal (P * (Real.pi * R ^ 2)) • Axi.ageμ c (-(5 / 2)) := by
  have hP0 : 0 < P := by rw [hP]; positivity
  ext A hA
  rw [Measure.map_apply (measurable_chartRed R c) hA, Measure.smul_apply, smul_eq_mul]
  set H : ℝ × (ℝ × ℝ) → ℝ≥0∞ := fun p => A.indicator 1 (qRed c p) with hHdef
  have hH : Measurable H := (measurable_one.indicator hA).comp (measurable_qRed c)
  have hHper : ∀ s q η, H (s, (q + c, η)) = H (s, (q, η)) := fun s q η => by
    simp only [hHdef, qRed_add hc]
  have h1 := Axi.phaseAvg_ringChart hR hc hP H hH hHper
  rw [← Axi.lintegral_ageμ hc (-(5 / 2)) hH] at h1
  have h2 : ∫⁻ p, H p ∂Axi.ageμ c (-(5 / 2)) = Axi.ageμ c (-(5 / 2)) A := by
    rw [← lintegral_indicator_one hA]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mem c (-(5 / 2))] with p hp
    simp only [hHdef, qRed_of_mem hc hp]
  rw [h2] at h1
  have h3 : phμ P (chartRed R c ⁻¹' A) =
      ∫⁻ τ in Ioc 0 P, ∫⁻ y, H (Axi.age R y, (Axi.phase R τ y, Axi.trans R y)) := by
    rw [← lintegral_indicator_one ((measurable_chartRed R c) hA),
      lintegral_prod _ ((measurable_one.indicator ((measurable_chartRed R c) hA)).aemeasurable)]
    rfl
  rw [h3]
  have hPne : ENNReal.ofReal P ≠ 0 := (ENNReal.ofReal_pos.2 hP0).ne'
  calc ∫⁻ τ in Ioc 0 P, ∫⁻ y, H (Axi.age R y, (Axi.phase R τ y, Axi.trans R y))
      = ENNReal.ofReal P * ((ENNReal.ofReal P)⁻¹ *
          ∫⁻ τ in Ioc 0 P, ∫⁻ y, H (Axi.age R y, (Axi.phase R τ y, Axi.trans R y))) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hPne ENNReal.ofReal_ne_top, one_mul]
    _ = ENNReal.ofReal (P * (Real.pi * R ^ 2)) * Axi.ageμ c (-(5 / 2)) A := by
        rw [h1, ← mul_assoc, ← ENNReal.ofReal_mul hP0.le]

/-- Bochner form: for `g` integrable for `ageμ c (-5/2)`, `g ∘ qRed c ∘ chart R` is integrable for
the phase measure and `∫ g ∘ qRed c ∘ chart R = P π R² ∫ g dageμ c (-5/2)`. -/
theorem integral_chartRed {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    {g : ℝ × (ℝ × ℝ) → ℂ} (hg : Integrable g (Axi.ageμ c (-(5 / 2)))) :
    Integrable (fun z => g (chartRed R c z)) (phμ P) ∧
      ∫ z, g (chartRed R c z) ∂phμ P =
        (P * (Real.pi * R ^ 2)) • ∫ x, g x ∂(Axi.ageμ c (-(5 / 2))) := by
  have hP0 : 0 < P := by rw [hP]; positivity
  have hmap := map_chartRed hR hc hP
  have hgm : Integrable g ((phμ P).map (chartRed R c)) := by
    rw [hmap]; exact hg.smul_measure ENNReal.ofReal_ne_top
  have hm : AEMeasurable (chartRed R c) (phμ P) := (measurable_chartRed R c).aemeasurable
  refine ⟨(integrable_map_measure hgm.1 hm).1 hgm, ?_⟩
  rw [← integral_map hm hgm.1, hmap, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]

/-- **Bochner version of the phase average** (SP 1639-1668). For `G` integrable for
`ageμ c (-5/2)` and `c`-periodic in `q` for a.e. point with `s > 0`,
`P⁻¹ ∫_{(0,P]} ∫ G(chart R τ y) dy dτ = π R² ∫ G dageμ c (-5/2)`. -/
theorem phase_chart_integral {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    {G : ℝ × (ℝ × ℝ) → ℂ} (hG : Integrable G (Axi.ageμ c (-(5 / 2))))
    (hper : ∀ᵐ x ∂(volume : Measure (ℝ × (ℝ × ℝ))), 0 < x.1 →
      G (x.1, (x.2.1 + c, x.2.2)) = G x) :
    P⁻¹ • ∫ t in Ioc (0 : ℝ) P, ∫ y, G (Axi.chart R t y) =
      ((Real.pi * R ^ 2 : ℝ) : ℂ) * ∫ x, G x ∂(Axi.ageμ c (-(5 / 2))) := by
  have hP0 : 0 < P := by rw [hP]; positivity
  -- the exceptional set of the periodicity and its saturation under the shifts by `k c`
  set N3 := toMeasurable (volume : Measure (ℝ × (ℝ × ℝ)))
    {x | ¬ (0 < x.1 → G (x.1, (x.2.1 + c, x.2.2)) = G x)} with hN3
  have hN3m : MeasurableSet N3 := measurableSet_toMeasurable _ _
  have hN3v : (volume : Measure (ℝ × (ℝ × ℝ))) N3 = 0 := by
    rw [hN3, measure_toMeasurable]; exact ae_iff.1 hper
  set B : Set (ℝ × (ℝ × ℝ)) := {x | x.1 ≤ 0} ∪ ⋃ k : ℤ, shk c k ⁻¹' N3 with hB
  have hBm : MeasurableSet B :=
    (measurableSet_le measurable_fst measurable_const).union
      (MeasurableSet.iUnion fun k => measurable_shk c k hN3m)
  have hBν : Axi.ageμ c (-(5 / 2)) B = 0 := by
    refine measure_union_null ?_ (measure_iUnion_null fun k => ?_)
    · exact measure_mono_null (fun x hx => not_lt.2 hx) (ae_iff.1 (ae_pos c (-(5 / 2))))
    · exact ac_volume c _ (by rw [volume_shk_preimage]; exact hN3v)
  have hsat : ∀ x, x ∈ B → qRed c x ∈ B := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · right
      obtain ⟨k, hk⟩ := mem_iUnion.1 hx
      refine mem_iUnion.2 ⟨k + ⌊(x.2.1 + c / 2) / c⌋, ?_⟩
      show shk c _ (shk c _ x) ∈ N3
      rw [shk_shk]
      have hk' : k + ⌊(x.2.1 + c / 2) / c⌋ + -⌊(x.2.1 + c / 2) / c⌋ = k := by ring
      rw [hk']
      exact hk
  have hcov : ∀ x, x ∉ B → G x = G (qRed c x) := by
    intro x hx
    have hx1 : 0 < x.1 := by
      by_contra h
      exact hx (Or.inl (not_lt.1 h))
    have hstep : ∀ k : ℤ, G (shk c (k + 1) x) = G (shk c k x) := by
      intro k
      have h' : shk c k x ∉ {x : ℝ × (ℝ × ℝ) | ¬ (0 < x.1 → G (x.1, (x.2.1 + c, x.2.2)) = G x)} :=
        fun h'' => hx (Or.inr (mem_iUnion.2 ⟨k, subset_toMeasurable _ _ h''⟩))
      simp only [Set.mem_ofPred_eq, not_not] at h'
      rw [shk_succ]
      exact h' hx1
    have hall : ∀ k : ℤ, G (shk c k x) = G x := by
      intro k
      refine Int.induction_on k ?_ ?_ ?_
      · rw [shk_zero]
      · intro i ih
        rw [hstep, ih]
      · intro i ih
        rw [← hstep (-(i : ℤ) - 1)]
        have hi : -(i : ℤ) - 1 + 1 = -(i : ℤ) := by ring
        rw [hi, ih]
    rw [qRed, hall]
  -- the chart preimage of `B` is null for the phase measure
  have hmap := map_chartRed hR hc hP
  have hnull : phμ P (chartRed R c ⁻¹' B) = 0 := by
    rw [← Measure.map_apply (measurable_chartRed R c) hBm, hmap, Measure.smul_apply, hBν,
      smul_zero]
  have hae : ∀ᵐ z ∂phμ P, G (Axi.chart R z.1 z.2) = G (chartRed R c z) := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) hnull
    by_contra hzB
    exact hz (hcov _ (fun h => hzB (hsat _ h)))
  obtain ⟨hint, hval⟩ := integral_chartRed hR hc hP hG
  have hit : ∫ t in Ioc (0 : ℝ) P, ∫ y, G (Axi.chart R t y) = ∫ z, G (chartRed R c z) ∂phμ P := by
    rw [integral_prod _ hint]
    refine integral_congr_ae ?_
    filter_upwards [Measure.ae_ae_of_ae_prod hae] with t ht
    exact integral_congr_ae ht
  rw [hit, hval, smul_smul, inv_mul_cancel_left₀ hP0.ne', Complex.real_smul]

end UnforcedLeray.Short.IIb.PhaseChartBochnerAux
