import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Pieces

/-!
# Jensen for the phase mean `meanQ` (helper for `GeomX.ZRegular`)

Source `shorter-proof-2026-11-02.tex` 5415-5427 (the phase mean of the chart tensor).
`‖ḡ‖² ≤ c⁻¹∫_cell ‖g‖²` fibrewise, hence `∫ w(s) ‖ḡ‖² dageμ ≤ ∫ w(s) ‖g‖² dageμ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace ZRegAux

theorem enorm_sq_mean_le (c : ℝ) (hc : 0 < c) (h : ℝ → Ten3) (hh : Measurable h) :
    ‖c⁻¹ • ∫ q in Ico (-c / 2) (c / 2), h q‖ₑ ^ 2 ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ q in Ico (-c / 2) (c / 2), ‖h q‖ₑ ^ 2 := by
  set m : Measure ℝ := volume.restrict (Ico (-c / 2) (c / 2)) with hm
  have hmu : m univ = ENNReal.ofReal c := by
    rw [hm, Measure.restrict_apply_univ, Real.volume_Ico]
    congr 1; ring
  have h1 : ‖∫ q, h q ∂m‖ₑ ≤ ∫⁻ q, ‖h q‖ₑ ∂m := enorm_integral_le_lintegral_enorm _
  have h2 : ∫⁻ q, ‖h q‖ₑ ∂m ≤ (∫⁻ q, ‖h q‖ₑ ^ (2 : ℝ) ∂m) ^ (1 / (2 : ℝ)) *
      (∫⁻ q, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂m) ^ (1 / (2 : ℝ)) := by
    have := ENNReal.lintegral_mul_le_Lp_mul_Lq m Real.HolderConjugate.two_two
      (f := fun q => ‖h q‖ₑ) (g := fun _ => (1 : ℝ≥0∞)) hh.enorm.aemeasurable
      aemeasurable_const
    simpa using this
  have h3 : (∫⁻ q, ‖h q‖ₑ ∂m) ^ 2 ≤ (∫⁻ q, ‖h q‖ₑ ^ 2 ∂m) * ENNReal.ofReal c := by
    have e1 : ∫⁻ q, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂m = ENNReal.ofReal c := by
      simp [hmu]
    have e2 : ∫⁻ q, ‖h q‖ₑ ^ (2 : ℝ) ∂m = ∫⁻ q, ‖h q‖ₑ ^ 2 ∂m := by
      simp
    rw [e1, e2] at h2
    calc (∫⁻ q, ‖h q‖ₑ ∂m) ^ 2 ≤ ((∫⁻ q, ‖h q‖ₑ ^ 2 ∂m) ^ (1 / (2 : ℝ)) *
        ENNReal.ofReal c ^ (1 / (2 : ℝ))) ^ 2 := by gcongr
      _ = (∫⁻ q, ‖h q‖ₑ ^ 2 ∂m) * ENNReal.ofReal c := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (ENNReal.ofReal c ^ _),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num
  have h4 : ‖c⁻¹ • ∫ q, h q ∂m‖ₑ = ENNReal.ofReal c⁻¹ * ‖∫ q, h q ∂m‖ₑ := by
    rw [enorm_smul]
    congr 1
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc)]
  rw [h4, mul_pow]
  calc ENNReal.ofReal c⁻¹ ^ 2 * ‖∫ q, h q ∂m‖ₑ ^ 2
      ≤ ENNReal.ofReal c⁻¹ ^ 2 * ((∫⁻ q, ‖h q‖ₑ ^ 2 ∂m) * ENNReal.ofReal c) := by
        gcongr
        exact (pow_le_pow_left' h1 2).trans h3
    _ = (ENNReal.ofReal c⁻¹ * ENNReal.ofReal c) * ENNReal.ofReal c⁻¹ * (∫⁻ q, ‖h q‖ₑ ^ 2 ∂m) := by
        ring
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ q, ‖h q‖ₑ ^ 2 ∂m := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne']
        simp

theorem avg_lintegral (c : ℝ) (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂(Cyl.avgμ c) =
      ENNReal.ofReal c⁻¹ * ∫⁻ q in Ico (-c / 2) (c / 2), ∫⁻ η, F (q, η) := by
  unfold Cyl.avgμ
  rw [lintegral_smul_measure, smul_eq_mul]
  congr 1
  have : Cyl.cellμ c = (volume.restrict (Ico (-c / 2) (c / 2))).prod (volume : Measure ℝ) := by
    unfold Cyl.cellμ Cyl.cell
    have h := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (Ico (-c / 2) (c / 2)) univ
    rw [Measure.restrict_univ] at h
    rw [Measure.volume_eq_prod, ← h]
  rw [this, lintegral_prod _ hF.aemeasurable]

theorem measurable_meanQ' (c : ℝ) {g : Chart → Ten3} (hg : Measurable g) :
    Measurable (meanQ c g) := by
  unfold meanQ
  have hm : Measurable fun x : Chart × ℝ => g (x.1.1, (x.2, x.1.2.2)) :=
    hg.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp (measurable_snd.comp measurable_fst))))
  have h : StronglyMeasurable fun p : Chart => ∫ q in Ico (-c / 2) (c / 2), g (p.1, (q, p.2.2)) :=
    StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ico (-c / 2) (c / 2)))
      (f := fun x : Chart × ℝ => g (x.1.1, (x.2, x.1.2.2))) hm.stronglyMeasurable
  exact h.measurable.const_smul c⁻¹

theorem mean_fiber_le (c : ℝ) (hc : 0 < c) (g : Chart → Ten3) (hg : Measurable g) (w : ℝ≥0∞)
    (hw : w ≠ ⊤) (s : ℝ) :
    ∫⁻ x, w * ‖meanQ c g (s, x)‖ₑ ^ 2 ∂(Cyl.avgμ c) ≤
      ∫⁻ x, w * ‖g (s, x)‖ₑ ^ 2 ∂(Cyl.avgμ c) := by
  have hgs : Measurable fun x : ℝ × ℝ => g (s, x) := hg.comp (measurable_const.prodMk measurable_id)
  have hmQ : Measurable fun x : ℝ × ℝ => w * ‖meanQ c g (s, x)‖ₑ ^ 2 :=
    measurable_const.mul (((measurable_meanQ' c hg).comp
      (measurable_const.prodMk measurable_id)).enorm.pow_const 2)
  have hG : Measurable fun x : ℝ × ℝ => w * ‖g (s, x)‖ₑ ^ 2 :=
    measurable_const.mul (hgs.enorm.pow_const 2)
  rw [avg_lintegral c _ hmQ, avg_lintegral c _ hG]
  have hmean : ∀ η : ℝ, ∀ q : ℝ, ‖meanQ c g (s, (q, η))‖ₑ ^ 2 ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ q' in Ico (-c / 2) (c / 2), ‖g (s, (q', η))‖ₑ ^ 2 := by
    intro η q
    have := enorm_sq_mean_le c hc (fun q' => g (s, (q', η)))
      (hg.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
    simpa [meanQ] using this
  have hvol : volume (Ico (-c / 2) (c / 2)) = ENNReal.ofReal c := by
    rw [Real.volume_Ico]; congr 1; ring
  -- the left side is constant in `q`
  have hL : ∫⁻ q in Ico (-c / 2) (c / 2), ∫⁻ η, w * ‖meanQ c g (s, (q, η))‖ₑ ^ 2 =
      ENNReal.ofReal c * ∫⁻ η, w * ‖meanQ c g (s, (0, η))‖ₑ ^ 2 := by
    have : ∀ q : ℝ, ∫⁻ η, w * ‖meanQ c g (s, (q, η))‖ₑ ^ 2 =
        ∫⁻ η, w * ‖meanQ c g (s, (0, η))‖ₑ ^ 2 := fun q => rfl
    simp only [this, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, hvol]
    ring
  rw [hL]
  have hswap : ∫⁻ q in Ico (-c / 2) (c / 2), ∫⁻ η, w * ‖g (s, (q, η))‖ₑ ^ 2 =
      ∫⁻ η, ∫⁻ q in Ico (-c / 2) (c / 2), w * ‖g (s, (q, η))‖ₑ ^ 2 := by
    refine lintegral_lintegral_swap ?_
    exact (measurable_const.mul ((hg.comp (measurable_const.prodMk measurable_id)).enorm.pow_const 2)).aemeasurable
  rw [hswap]
  calc ENNReal.ofReal c⁻¹ * (ENNReal.ofReal c * ∫⁻ η, w * ‖meanQ c g (s, (0, η))‖ₑ ^ 2)
      = ∫⁻ η, w * ‖meanQ c g (s, (0, η))‖ₑ ^ 2 := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne']
        simp
    _ ≤ ∫⁻ η, w * (ENNReal.ofReal c⁻¹ * ∫⁻ q' in Ico (-c / 2) (c / 2), ‖g (s, (q', η))‖ₑ ^ 2) := by
        refine lintegral_mono fun η => ?_
        gcongr
        exact hmean η 0
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ η, ∫⁻ q in Ico (-c / 2) (c / 2), w * ‖g (s, (q, η))‖ₑ ^ 2 := by
        have hin : ∀ η : ℝ, ∫⁻ q in Ico (-c / 2) (c / 2), w * ‖g (s, (q, η))‖ₑ ^ 2 =
            w * ∫⁻ q in Ico (-c / 2) (c / 2), ‖g (s, (q, η))‖ₑ ^ 2 :=
          fun η => lintegral_const_mul' w _ hw
        simp only [hin]
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun η => ?_
        ring

theorem mean_ageμ_le (c a : ℝ) (hc : 0 < c) (g : Chart → Ten3) (hg : Measurable g)
    (w : ℝ → ℝ≥0∞) (hwm : Measurable w) (hw : ∀ s, w s ≠ ⊤) :
    ∫⁻ p, w p.1 * ‖meanQ c g p‖ₑ ^ 2 ∂(ageμ c a) ≤ ∫⁻ p, w p.1 * ‖g p‖ₑ ^ 2 ∂(ageμ c a) := by
  unfold ageμ
  have h1 : Measurable fun p : Chart => w p.1 * ‖meanQ c g p‖ₑ ^ 2 :=
    (hwm.comp measurable_fst).mul ((measurable_meanQ' c hg).enorm.pow_const 2)
  have h2 : Measurable fun p : Chart => w p.1 * ‖g p‖ₑ ^ 2 :=
    (hwm.comp measurable_fst).mul (hg.enorm.pow_const 2)
  rw [lintegral_prod _ h1.aemeasurable, lintegral_prod _ h2.aemeasurable]
  exact lintegral_mono fun s => mean_fiber_le c hc g hg (w s) (hw s) s

theorem mean_moment_le (c a : ℝ) (hc : 0 < c) (g : Chart → Ten3) (hg : Measurable g) :
    ∫⁻ p, ‖meanQ c g p‖ₑ ^ 2 ∂(ageμ c a) ≤ ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ c a) := by
  have := mean_ageμ_le c a hc g hg (fun _ => 1) measurable_const (fun _ => ENNReal.one_ne_top)
  simpa using this

theorem mean_ae_zero (c a ν : ℝ) (hc : 0 < c) (g : Chart → Ten3) (hg : Measurable g)
    (hz : ∀ᵐ p ∂(ageμ c a), ν * p.1 ≤ 6 / 5 → g p = 0) :
    ∀ᵐ p ∂(ageμ c a), ν * p.1 ≤ 6 / 5 → meanQ c g p = 0 := by
  classical
  set w : ℝ → ℝ≥0∞ := fun s => if ν * s ≤ 6 / 5 then 1 else 0 with hwdef
  have hwm : Measurable w := by
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_le (measurable_const.mul measurable_id) measurable_const
  have hle := mean_ageμ_le c a hc g hg w hwm (fun s => by simp only [hwdef]; split_ifs <;> simp)
  have hR : ∫⁻ p, w p.1 * ‖g p‖ₑ ^ 2 ∂(ageμ c a) = 0 := by
    have hm1 : Measurable fun p : Chart => w p.1 * ‖g p‖ₑ ^ 2 :=
      (hwm.comp measurable_fst).mul (hg.enorm.pow_const 2)
    rw [lintegral_eq_zero_iff hm1]
    filter_upwards [hz] with p hp
    simp only [hwdef, Pi.zero_apply]
    split_ifs with h
    · simp [hp h]
    · simp
  have hL : ∫⁻ p, w p.1 * ‖meanQ c g p‖ₑ ^ 2 ∂(ageμ c a) = 0 := le_antisymm (hR ▸ hle) bot_le
  have hm2 : Measurable fun p : Chart => w p.1 * ‖meanQ c g p‖ₑ ^ 2 :=
    (hwm.comp measurable_fst).mul ((measurable_meanQ' c hg).enorm.pow_const 2)
  rw [lintegral_eq_zero_iff hm2] at hL
  filter_upwards [hL] with p hp h
  simp only [hwdef, Pi.zero_apply, if_pos h, one_mul] at hp
  simpa using hp

end ZRegAux

end UnforcedLeray.Short.PartIIIb.Concrete
