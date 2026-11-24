import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.Lift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Bridge (1), mean part: the phase mean commutes with the lift (helper for `GeomX.PhasePrimitive`)

Source `the November 2 reference manuscript`
lines 3753-3757 (`phaseMean`), 4764-4770, 5415-5427.

* `integral_redQ`, `lintegral_redQ`: a function of the reduced phase integrates over one period
  `(0, c]` as over the cell `[-c/2, c/2)`;
* `phaseMean_plift`: at a chart point whose phase slice is integrable,
  `F̄ = phaseMean c (plift c g) = plift c (meanQ c g)` (the lift is linear in the tensor);
* `slice_null`: the slices of a chart tensor with finite `s^{-1/2}`-moment of `|g|²` are
  integrable off an `ageμ`-null set;
* `sepW_cut`, `sepW_mean`: the responses of the two thin sources are those of the old sources
  `oldPhys g`, `oldPhys (meanQ g)` (null sets of chart points pull back to null sets of `(τ,z)`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace PhasePrim

theorem redQ_of_mem (c : ℝ) (hc : 0 < c) {q : ℝ} (hq : q ∈ Ioo (-c / 2) (c / 2)) :
    redQ c q = q := by
  unfold redQ
  have h : ⌊q / c + 1 / 2⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    obtain ⟨h1, h2⟩ := hq
    constructor
    · have : -(1 / 2 : ℝ) < q / c := by
        rw [lt_div_iff₀ hc]; linarith
      linarith
    · have : q / c < 1 / 2 := by
        rw [div_lt_iff₀ hc]; linarith
      linarith
  rw [h]
  simp

theorem integral_redQ (c : ℝ) (hc : 0 < c) (h : ℝ → ℝ) :
    ∫ q in Ioc 0 c, h (redQ c q) = ∫ q in Ico (-c / 2) (c / 2), h q := by
  have hper : Function.Periodic (fun q => h (redQ c q)) c := fun q => by
    simp only [redQ_add c hc.ne']
  have hsh := hper.intervalIntegral_add_eq 0 (-c / 2)
  rw [zero_add, show -c / 2 + c = c / 2 by ring] at hsh
  have e4 : ∫ q in Ioo (-c / 2) (c / 2), h (redQ c q) = ∫ q in Ioo (-c / 2) (c / 2), h q :=
    setIntegral_congr_fun measurableSet_Ioo (fun q hq => by simp only [redQ_of_mem c hc hq])
  rw [← intervalIntegral.integral_of_le hc.le, hsh,
    intervalIntegral.integral_of_le (by linarith : -c / 2 ≤ c / 2),
    setIntegral_congr_set (Ioo_ae_eq_Ioc (a := -c / 2) (b := c / 2)).symm, e4,
    setIntegral_congr_set (Ioo_ae_eq_Ico (a := -c / 2) (b := c / 2))]

theorem lintegral_periodic {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ≥0∞} (hf : Function.Periodic f T)
    (t s : ℝ) : ∫⁻ x in Ioc t (t + T), f x = ∫⁻ x in Ioc s (s + T), f x := by
  haveI : Fact (0 < T) := ⟨hT⟩
  have e : ∀ u : ℝ, ∫⁻ x in Ioc u (u + T), f x = ∫⁻ b : AddCircle T, hf.lift b := by
    intro u
    rw [← AddCircle.lintegral_preimage T u hf.lift]
    simp only [Function.Periodic.lift_coe]
  rw [e t, e s]

theorem lintegral_redQ (c : ℝ) (hc : 0 < c) (h : ℝ → ℝ≥0∞) :
    ∫⁻ q in Ioc 0 c, h (redQ c q) = ∫⁻ q in Ico (-c / 2) (c / 2), h q := by
  have hper : Function.Periodic (fun q => h (redQ c q)) c := fun q => by
    simp only [redQ_add c hc.ne']
  have hsh := lintegral_periodic hc hper 0 (-c / 2)
  rw [zero_add, show -c / 2 + c = c / 2 by ring] at hsh
  have e4 : ∫⁻ q in Ioo (-c / 2) (c / 2), h (redQ c q) = ∫⁻ q in Ioo (-c / 2) (c / 2), h q :=
    setLIntegral_congr_fun measurableSet_Ioo (fun q hq => by simp only [redQ_of_mem c hc hq])
  rw [hsh, setLIntegral_congr (Ioo_ae_eq_Ioc (a := -c / 2) (b := c / 2)).symm, e4,
    setLIntegral_congr (Ioo_ae_eq_Ico (a := -c / 2) (b := c / 2))]

/-! ## Linearity of the lift -/

theorem nsSym_add (A B : Ten3) : NearInst.nsSym (A + B) = NearInst.nsSym A + NearInst.nsSym B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [NearInst.nsSym, NearInst.symRZ] <;> ring

theorem nsSym_smul (a : ℝ) (A : Ten3) : NearInst.nsSym (a • A) = a • NearInst.nsSym A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [NearInst.nsSym, NearInst.symRZ] <;> ring

/-- The entry `(i,j)` of the lift at `x'`, as a linear functional of the chart tensor. -/
def psiL (x' : ℝ × ℝ) (i j : Fin 3) : Ten3 →ₗ[ℝ] ℝ where
  toFun T := (plFrame x' * (plS x' • NearInst.nsSym T) * (plFrame x').transpose) i j
  map_add' A B := by
    simp only [nsSym_add, smul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
  map_smul' a A := by
    simp only [nsSym_smul, smul_comm (plS x') a, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]

/-- **The phase mean commutes with the lift** at a chart point with integrable phase slice. -/
theorem phaseMean_plift (c : ℝ) (hc : 0 < c) (g : Chart → Ten3) (x' : ℝ × ℝ) (Y : ℝ)
    (hint : IntegrableOn (fun q => g (plS x', (q, Y * Real.sqrt (plS x')))) (Ico (-c / 2) (c / 2)))
    (q0 : ℝ) : IIIa.phaseMean c (plift c g) x' Y = plift c (meanQ c g) x' Y q0 := by
  have key : ∀ i j : Fin 3, c⁻¹ * ∫ q in Ioc 0 c, plift c g x' Y q i j =
      plift c (meanQ c g) x' Y q0 i j := by
    intro i j
    set Ψ : Ten3 →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (psiL x' i j) with hΨ
    have e1 : ∀ q, plift c g x' Y q i j = Ψ (g (plS x', (redQ c q, Y * Real.sqrt (plS x')))) :=
      fun q => rfl
    have e0 : ∫ q in Ioc 0 c, plift c g x' Y q i j =
        ∫ q in Ioc 0 c, Ψ (g (plS x', (redQ c q, Y * Real.sqrt (plS x')))) :=
      integral_congr_ae (Eventually.of_forall e1)
    have e2 := integral_redQ c hc (fun q => Ψ (g (plS x', (q, Y * Real.sqrt (plS x')))))
    have e3 := Ψ.integral_comp_comm hint
    have e4 : plift c (meanQ c g) x' Y q0 i j =
        Ψ (c⁻¹ • ∫ q in Ico (-c / 2) (c / 2), g (plS x', (q, Y * Real.sqrt (plS x')))) := rfl
    rw [e0, e2, e3, e4, map_smul, smul_eq_mul]
  exact Matrix.ext fun i j => key i j

theorem phaseMean_cutLift (c ρo : ℝ) (g : Chart → Ten3) (x' : ℝ × ℝ) (Y : ℝ) :
    IIIa.phaseMean c (cutLift c ρo g) x' Y =
      if Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) ≤ ρo then IIIa.phaseMean c (plift c g) x' Y else 0 := by
  by_cases h : Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) ≤ ρo
  · rw [if_pos h]
    funext i j
    simp only [IIIa.phaseMean, cutLift, if_pos h]
  · rw [if_neg h]
    funext i j
    simp [IIIa.phaseMean, cutLift, if_neg h]

/-! ## Integrable slices -/

theorem slice_null (c : ℝ) (hc : 0 < c) (g : Chart → Ten3) (hg : Measurable g)
    (hmom : ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) < ⊤) :
    ageμ c (-1 / 2) {p : Chart | ¬ IntegrableOn (fun q => g (p.1, (q, p.2.2)))
      (Ico (-c / 2) (c / 2))} = 0 := by
  set Φ : Chart → ℝ≥0∞ := fun p => ∫⁻ q in Ico (-c / 2) (c / 2), ‖g (p.1, (q, p.2.2))‖ₑ ^ 2
    with hΦ
  have hm2 : Measurable fun x : Chart × ℝ => ‖g (x.1.1, (x.2, x.1.2.2))‖ₑ ^ 2 :=
    (hg.comp (by fun_prop)).enorm.pow_const 2
  have hΦm : Measurable Φ := hm2.lintegral_prod_right'
  have hgm2 : Measurable fun p : Chart => ‖g p‖ₑ ^ 2 := hg.enorm.pow_const 2
  have hvol : volume (Ico (-c / 2) (c / 2)) = ENNReal.ofReal c := by
    rw [Real.volume_Ico]; congr 1; ring
  have hfib : ∀ s : ℝ, ∫⁻ x, Φ (s, x) ∂(Cyl.avgμ c) =
      ENNReal.ofReal c * ∫⁻ x, ‖g (s, x)‖ₑ ^ 2 ∂(Cyl.avgμ c) := by
    intro s
    have hF1 : Measurable fun x : ℝ × ℝ => Φ (s, x) :=
      hΦm.comp (measurable_const.prodMk measurable_id)
    have hF2 : Measurable fun x : ℝ × ℝ => ‖g (s, x)‖ₑ ^ 2 :=
      hgm2.comp (measurable_const.prodMk measurable_id)
    rw [ZRegAux.avg_lintegral c _ hF1, ZRegAux.avg_lintegral c _ hF2]
    have hconst : ∫⁻ q in Ico (-c / 2) (c / 2), ∫⁻ η, Φ (s, (q, η)) =
        ENNReal.ofReal c * ∫⁻ η, Φ (s, (0, η)) := by
      have : ∀ q : ℝ, ∫⁻ η, Φ (s, (q, η)) = ∫⁻ η, Φ (s, (0, η)) := fun q => rfl
      simp only [this, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, hvol]
      ring
    have hswap : ∫⁻ q in Ico (-c / 2) (c / 2), ∫⁻ η, ‖g (s, (q, η))‖ₑ ^ 2 =
        ∫⁻ η, ∫⁻ q in Ico (-c / 2) (c / 2), ‖g (s, (q, η))‖ₑ ^ 2 :=
      lintegral_lintegral_swap
        ((hgm2.comp (measurable_const.prodMk measurable_id)).aemeasurable)
    rw [hconst, hswap]
    ring
  have hint : ∫⁻ p, Φ p ∂(ageμ c (-1 / 2)) = ENNReal.ofReal c * ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) := by
    unfold ageμ
    rw [lintegral_prod _ hΦm.aemeasurable, lintegral_prod _ hgm2.aemeasurable,
      ← lintegral_const_mul _ (hgm2.lintegral_prod_right')]
    exact lintegral_congr fun s => hfib s
  have hfin : ∫⁻ p, Φ p ∂(ageμ c (-1 / 2)) ≠ ⊤ := by
    rw [hint]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmom.ne
  have hae := ae_lt_top hΦm hfin
  refine measure_mono_null (fun p hp => ?_) (ae_iff.1 hae)
  simp only [mem_setOf_eq] at hp ⊢
  intro hlt
  apply hp
  haveI : IsFiniteMeasure (volume.restrict (Ico (-c / 2) (c / 2))) :=
    isFiniteMeasure_restrict.2 (by rw [hvol]; exact ENNReal.ofReal_ne_top)
  have hmeas : AEStronglyMeasurable (fun q => g (p.1, (q, p.2.2)))
      (volume.restrict (Ico (-c / 2) (c / 2))) :=
    (hg.comp (by fun_prop)).aestronglyMeasurable
  have hL : MemLp (fun q => g (p.1, (q, p.2.2))) 2 (volume.restrict (Ico (-c / 2) (c / 2))) := by
    refine ⟨hmeas, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
    have e : ∀ q, ‖g (p.1, (q, p.2.2))‖ₑ ^ (2 : ℝ≥0∞).toReal = ‖g (p.1, (q, p.2.2))‖ₑ ^ 2 := by
      intro q
      rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    simp only [e]
    exact hlt
  exact hL.integrable one_le_two

/-! ## The two responses -/

/-- The cut old source agrees a.e. with the old source (copy of the step `hagree` of
`ZRegAux.sepSrc_of_chart`). -/
theorem oldCut_ae (c ν ε : ℝ) (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε) (G : Chart → Ten3)
    (hz : ∀ᵐ p ∂(ageμ c (-1 / 2)), ν * p.1 ≤ 6 / 5 → G p = 0) :
    ∀ᵐ x : ℝ × Space ∂volume, oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) G x.1 x.2 =
      oldPhys ε⁻¹ c G x.1 x.2 := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hpull := chartOfNullPullback ε⁻¹ c hR hc _ (ae_iff.1 hz)
  filter_upwards [hpull] with x hx
  simp only [not_not] at hx
  unfold oldCutSrc
  split_ifs with hz'
  · rfl
  · have h0r : 0 ≤ ε⁻¹ * Real.sqrt (5 * ν / 6) := by positivity
    have hlt := not_le.1 hz'
    have hpos : 0 < NearInst.hRad x.2 := lt_of_le_of_lt h0r hlt
    have hsq : (ε⁻¹ * Real.sqrt (5 * ν / 6)) ^ 2 = ε⁻¹ ^ 2 * (5 * ν / 6) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hlt2 : (ε⁻¹ * Real.sqrt (5 * ν / 6)) ^ 2 < NearInst.hRad x.2 ^ 2 := by
      nlinarith
    have hs : ν * (NearInst.chartOf ε⁻¹ c x.2 x.1).1 ≤ 6 / 5 := by
      show ν * (ε⁻¹ ^ 2 / NearInst.hRad x.2 ^ 2) ≤ 6 / 5
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    have hG0 := hx hs
    simp only [oldPhys, NearInst.cartLift, hG0, osr_nsSym_zero, smul_zero, Matrix.mul_zero,
      Matrix.zero_mul]

/-- The response of the cut thin source is the response of the old source. -/
theorem sepW_cut (c ν ε : ℝ) (μ : ℂ) (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε) (g : Chart → Ten3)
    (hz : ∀ᵐ p ∂(ageμ c (-1 / 2)), ν * p.1 ≤ 6 / 5 → g p = 0) (y : Space) (τ : ℝ) :
    IIIa.sepW ν μ (IIIa.thinSource ε (cutLift c (Real.sqrt (5 * ν / 6)) g)) y τ =
      IIIa.sepW ν μ (oldPhys ε⁻¹ c g) y τ := by
  have e : IIIa.thinSource ε (cutLift c (Real.sqrt (5 * ν / 6)) g) =
      oldCutSrc ε⁻¹ c (ε⁻¹ * Real.sqrt (5 * ν / 6)) g := by
    funext τ z
    exact thinSource_cutLift ε c _ hε g τ z
  rw [e]
  exact sepWCongrAE ν μ _ _ (oldCut_ae c ν ε hc hν hε g hz) y τ

/-- The thin source of the phase mean of the cut lift agrees a.e. with the old source of the
phase mean `meanQ c g`. -/
theorem mean_ae (c ν ε : ℝ) (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε) (g : Chart → Ten3)
    (hg : Measurable g) (hmom : ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) < ⊤)
    (hz' : ∀ᵐ p ∂(ageμ c (-1 / 2)), ν * p.1 ≤ 6 / 5 → meanQ c g p = 0) :
    ∀ᵐ x : ℝ × Space ∂volume,
      IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c (cutLift c (Real.sqrt (5 * ν / 6)) g)))
        x.1 x.2 = oldPhys ε⁻¹ c (meanQ c g) x.1 x.2 := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have h1 := chartOfNullPullback ε⁻¹ c hR hc _ (slice_null c hc g hg hmom)
  have h2 := chartOfNullPullback ε⁻¹ c hR hc _ (ae_iff.1 hz')
  filter_upwards [h1, h2] with x hx1 hx2
  simp only [mem_setOf_eq, not_not] at hx1 hx2
  rw [chartOf_eps ε c hε] at hx1
  unfold IIIa.thinSource IIIa.meanLift
  rw [phaseMean_cutLift]
  dsimp only
  rw [sqrt_eps ε hε.le]
  by_cases hcut : ε * Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) ≤ Real.sqrt (5 * ν / 6)
  · rw [if_pos hcut, phaseMean_plift c hc g _ _ hx1
      (ε⁻¹ * Real.log (ε * Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2)) + x.1 / (2 * ε))]
    exact plift_eps ε c hε (meanQ c g) x.1 x.2
  · rw [if_neg hcut]
    have hlt := not_le.1 hcut
    have hA : 5 * ν / 6 < (ε * x.2 0) ^ 2 + (ε * x.2 1) ^ 2 := by
      rw [← sqrt_eps ε hε.le] at hlt
      exact (Real.sqrt_lt_sqrt_iff (by positivity)).1 hlt
    have hApos : 0 < (ε * x.2 0) ^ 2 + (ε * x.2 1) ^ 2 := lt_of_le_of_lt (by positivity) hA
    have hs : ν * (NearInst.chartOf ε⁻¹ c x.2 x.1).1 ≤ 6 / 5 := by
      rw [chartOf_eps ε c hε]
      show ν * ((ε * x.2 0) ^ 2 + (ε * x.2 1) ^ 2)⁻¹ ≤ 6 / 5
      rw [← div_eq_mul_inv, div_le_iff₀ hApos]
      linarith
    have hG0 := hx2 hs
    simp only [oldPhys, NearInst.cartLift, hG0, osr_nsSym_zero, smul_zero, Matrix.mul_zero,
      Matrix.zero_mul]

/-- The response of the mean thin source is the response of the phase-mean old source. -/
theorem sepW_mean (c ν ε : ℝ) (μ : ℂ) (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε) (g : Chart → Ten3)
    (hg : Measurable g) (hmom : ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) < ⊤)
    (hz' : ∀ᵐ p ∂(ageμ c (-1 / 2)), ν * p.1 ≤ 6 / 5 → meanQ c g p = 0) (y : Space) (τ : ℝ) :
    IIIa.sepW ν μ
        (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c (cutLift c (Real.sqrt (5 * ν / 6)) g))))
        y τ = IIIa.sepW ν μ (oldPhys ε⁻¹ c (meanQ c g)) y τ :=
  sepWCongrAE ν μ _ _ (mean_ae c ν ε hc hν hε g hg hmom hz') y τ

end PhasePrim

end UnforcedLeray.Short.PartIIIb.Concrete
