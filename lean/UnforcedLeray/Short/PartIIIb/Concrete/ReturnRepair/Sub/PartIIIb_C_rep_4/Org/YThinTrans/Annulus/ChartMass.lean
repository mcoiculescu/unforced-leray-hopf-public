import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.Annulus.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.AxisNull
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.PolarReduction
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChangeSE
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.CartLiftNormOffAxis
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.GAxFacts

/-!
# `ChartMassLe`: the physical mass of the lift from the chart phase bound

Source `the November 2 reference manuscript` 2685-2687 (the physical Jacobian
after azimuthal integration is `πR²s^{-5/2}ds dη`), 3730 (physical phase-averaged mass `R²N₀`),
5571-5576 (old physical mass divided by `πR²` is `N₀(a)`).

Proof: off the axis (a null set) the lift has phase norm `gAx(·, z)` (`CartLiftNormOffAxis`);
`PolarReduction` (lo = 0) turns `∫_{ℝ³}` into `2π∫ρ∫_t`, and `ChartChangeSE` (lo = 0) moves
this to the chart `(s, η)`, where `ChartPhaseNorm` bounds each receiver by `s · G(s, η)`.
The Jacobian `s^{-5/2} · s = s^{-3/2}` and the constant `2π · R²/2 = πR²` give `πR² N₀(0)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- The phase norm of the source tensor profile `gAx` at a point `z`. -/
private def cmH (R c : ℝ) (f : Chart → Ten3) (z : UnforcedLeray.Space) : ℝ≥0∞ :=
  UnforcedLeray.Short.IIIa.ltauAt (2 * c / R) (fun τ => gAx R c f τ z)

private lemma cm_ptOf_meas : Measurable (fun u : ℝ × ℝ => ptOf u.1 u.2) := by
  apply Continuous.measurable
  unfold ptOf
  have h3 : Continuous (fun u : ℝ × ℝ => (![u.1, 0, u.2] : Fin 3 → ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp 2 _).comp h3

private lemma cm_meas (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (f : Chart → Ten3)
    (hf : Measurable f) : Measurable (cmH R c f) := by
  obtain ⟨_, _, hgm⟩ := gAxFacts_holds R c f hR hc hf
  have hF : Measurable (fun p : UnforcedLeray.Space × ℝ => gAx R c f p.2 p.1 ^ (2 : ℝ)) :=
    (hgm.comp (measurable_snd.prodMk measurable_fst)).pow_const _
  have hI : Measurable (fun z : UnforcedLeray.Space =>
      ∫⁻ τ in Ioc 0 (2 * c / R), gAx R c f τ z ^ (2 : ℝ)) :=
    hF.lintegral_prod_right'
  unfold cmH UnforcedLeray.Short.IIIa.ltauAt
  exact (measurable_const.mul hI).pow_const _

private lemma cm_hRad_zero (y : UnforcedLeray.Space) (h : hRad y = 0) : y 0 = 0 ∧ y 1 = 0 := by
  unfold hRad at h
  have hle := Real.sqrt_eq_zero'.1 h
  have h0 : y 0 ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg (y 1)]) (sq_nonneg _)
  have h1 : y 1 ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg (y 0)]) (sq_nonneg _)
  exact ⟨by simpa using h0, by simpa using h1⟩

private lemma cm_ext (y y' : UnforcedLeray.Space) (h0 : y 0 = y' 0) (h1 : y 1 = y' 1)
    (h2 : y 2 = y' 2) : y = y' := by
  ext i
  fin_cases i <;> simp [h0, h1, h2]

private lemma cm_axisym (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (f : Chart → Ten3)
    (hf : Measurable f) :
    ∀ y y' : UnforcedLeray.Space, hRad y = hRad y' → y 2 = y' 2 → cmH R c f y = cmH R c f y' := by
  intro y y' h1 h2
  by_cases hy : hRad y = 0
  · have hy' : hRad y' = 0 := by rw [← h1]; exact hy
    obtain ⟨a0, a1⟩ := cm_hRad_zero y hy
    obtain ⟨b0, b1⟩ := cm_hRad_zero y' hy'
    have hyy : y = y' := cm_ext y y' (by rw [a0, b0]) (by rw [a1, b1]) h2
    rw [hyy]
  · obtain ⟨hax, _, _⟩ := gAxFacts_holds R c f hR hc hf
    have hfun : (fun τ => gAx R c f τ y) = fun τ => gAx R c f τ y' :=
      funext fun τ => hax τ y y' h1 h2
    unfold cmH
    rw [hfun]

private lemma cm_hRad_chart (R : ℝ) (hR : 0 < R) (p : Chart) (hs : 0 < p.1) :
    hRad (chartY R p) ≠ 0 := by
  have h0 : (chartY R p) 0 = R / Real.sqrt p.1 := by simp [chartY]
  have h1 : (chartY R p) 1 = 0 := by simp [chartY]
  unfold hRad
  rw [h0, h1, show (R / Real.sqrt p.1) ^ 2 + (0 : ℝ) ^ 2 = (R / Real.sqrt p.1) ^ 2 by ring,
    Real.sqrt_sq (div_nonneg hR.le (Real.sqrt_nonneg _))]
  exact (div_pos hR (Real.sqrt_pos.2 hs)).ne'

/-- The pointwise receiver bound at `chartY R (s, (0, η))`. -/
private lemma cm_point (h : ChartPhaseNorm) (R c : ℝ) (hR : 0 < R) (hc : 0 < c)
    (f : Chart → Ten3) (hf : Measurable f) (s η : ℝ) (hs : 0 < s) :
    cmH R c f (ptOf (R / Real.sqrt s) (η / Real.sqrt s)) ≤
      ENNReal.ofReal s * (∫⁻ q in Ico (-(c / 2)) (c / 2),
        ENNReal.ofReal c⁻¹ * ENNReal.ofReal
          (UnforcedLeray.Short.IIIa.frobSq (Ten3.toMatrix (f (s, (q, η))))))
          ^ (1 / 2 : ℝ) := by
  have hY : ptOf (R / Real.sqrt s) (η / Real.sqrt s) = chartY R (s, (0, η)) := rfl
  have hz : hRad (chartY R (s, (0, η))) ≠ 0 := cm_hRad_chart R hR (s, (0, η)) hs
  have hfun : (fun τ => gAx R c f τ (chartY R (s, (0, η)))) =
      fun τ => UnforcedLeray.Short.IIIa.srcNorm (cartLift R c f) τ (chartY R (s, (0, η))) :=
    funext fun τ => (cartLiftNormOffAxis_holds R c f τ (chartY R (s, (0, η))) hz).symm
  rw [hY]
  unfold cmH
  rw [hfun]
  exact h R c hR hc f hf (s, (0, η)) hs

/-- **The physical mass of the lift** (source 2685-2687, 3730, 5571-5576). -/
theorem chartMassLe_of (h : ChartPhaseNorm) : ChartMassLe := by
  intro R c hR hc f hf
  have hae0 : ∀ᵐ z ∂(volume : Measure UnforcedLeray.Space), hRad z ≠ 0 := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) axisNull_holds
    exact not_not.1 hz
  -- Step 1: off the axis the lift is `gAx`
  have e1 : (∫⁻ z : UnforcedLeray.Space, UnforcedLeray.Short.IIIa.ltauAt (2 * c / R)
      (fun τ => UnforcedLeray.Short.IIIa.srcNorm (cartLift R c f) τ z)) =
      ∫⁻ z : UnforcedLeray.Space, cmH R c f z := by
    refine lintegral_congr_ae (hae0.mono fun z hz => ?_)
    have hfun : (fun τ => UnforcedLeray.Short.IIIa.srcNorm (cartLift R c f) τ z) =
        fun τ => gAx R c f τ z :=
      funext fun τ => cartLiftNormOffAxis_holds R c f τ z hz
    beta_reduce
    unfold cmH
    rw [hfun]
  -- Step 2: restrict to the half-space `hRad > 0`
  have hpos : ∀ᵐ z ∂(volume : Measure UnforcedLeray.Space), z ∈ {y : UnforcedLeray.Space | (0 : ℝ) < hRad y} :=
    hae0.mono fun z hz => lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
  have e2 : (∫⁻ z : UnforcedLeray.Space, cmH R c f z) =
      ∫⁻ z in {y : UnforcedLeray.Space | (0 : ℝ) < hRad y}, cmH R c f z := by
    rw [Measure.restrict_eq_self_of_ae_mem hpos]
  -- Step 3: polar reduction
  have hPR := polarReduction_holds (cmH R c f) (cm_meas R c hR hc f hf)
    (cm_axisym R c hR hc f hf) 0 le_rfl
  -- Step 4: chart change on `(ρ, t) ↦ (s, η)`
  have hΨm : Measurable (Function.uncurry (fun ρ t => cmH R c f (ptOf ρ t))) :=
    (cm_meas R c hR hc f hf).comp cm_ptOf_meas
  have hCSE := chartChangeSE_holds R 0 hR le_rfl (fun ρ t => cmH R c f (ptOf ρ t)) hΨm
  beta_reduce at hCSE
  have hS : {s : ℝ | 0 < s ∧ (0 : ℝ) < R / Real.sqrt s} = Ioi 0 := by
    ext s
    simp only [mem_setOf_eq, mem_Ioi]
    constructor
    · exact fun hh => hh.1
    · intro hs
      exact ⟨hs, div_pos hR (Real.sqrt_pos.2 hs)⟩
  rw [hS] at hCSE
  -- Step 5: the Jacobian and the pointwise bound
  have hmain : (∫⁻ s in Ioi (0 : ℝ), ∫⁻ η : ℝ,
        ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * cmH R c f (ptOf (R / Real.sqrt s) (η / Real.sqrt s))) ≤
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
        (∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal c⁻¹ *
          ENNReal.ofReal (UnforcedLeray.Short.IIIa.frobSq (Ten3.toMatrix (f (s, (q, η))))))
          ^ (1 / 2 : ℝ) := by
    refine setLIntegral_mono' measurableSet_Ioi (fun s hs => ?_)
    have hs' : (0 : ℝ) < s := hs
    refine lintegral_mono (fun η => ?_)
    have hpt := cm_point h R c hR hc f hf s η hs'
    have hexp : ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * ENNReal.ofReal s =
        ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs'.le _)]
      congr 1
      calc s ^ (-5 / 2 : ℝ) * s = s ^ (-5 / 2 : ℝ) * s ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = s ^ ((-5 / 2 : ℝ) + 1) := (Real.rpow_add hs' _ _).symm
        _ = s ^ (-3 / 2 : ℝ) := by norm_num
    calc ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * cmH R c f (ptOf (R / Real.sqrt s) (η / Real.sqrt s))
        ≤ ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * (ENNReal.ofReal s * (∫⁻ q in Ico (-(c / 2)) (c / 2),
            ENNReal.ofReal c⁻¹ * ENNReal.ofReal
              (UnforcedLeray.Short.IIIa.frobSq (Ten3.toMatrix (f (s, (q, η))))))
              ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hpt (by positivity)
      _ = ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * (∫⁻ q in Ico (-(c / 2)) (c / 2),
            ENNReal.ofReal c⁻¹ * ENNReal.ofReal
              (UnforcedLeray.Short.IIIa.frobSq (Ten3.toMatrix (f (s, (q, η))))))
              ^ (1 / 2 : ℝ) := by
        rw [← hexp, mul_assoc, mul_left_comm]
  -- Step 6: the constants `2π · R²/2 = πR²`
  have hc2 : ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (R ^ 2 / 2) =
      ENNReal.ofReal (Real.pi * R ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hM : oldMassAt c 0 (fun p => Ten3.toMatrix (f p)) =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
        (∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal c⁻¹ *
          ENNReal.ofReal (UnforcedLeray.Short.IIIa.frobSq (Ten3.toMatrix (f (s, (q, η))))))
          ^ (1 / 2 : ℝ) := by
    unfold oldMassAt
    refine lintegral_congr fun s => ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hc3 : ∀ X : ℝ≥0∞, ENNReal.ofReal (2 * Real.pi) * (ENNReal.ofReal (R ^ 2 / 2) * X) =
      ENNReal.ofReal (Real.pi * R ^ 2) * X := fun X => by rw [← mul_assoc, hc2]
  have final := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hmain (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (R ^ 2 / 2)))
    (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * Real.pi))
  rw [hc3, hc3] at final
  rw [e1, e2, hPR, hCSE, hM, hc3]
  exact final

end UnforcedLeray.Short.PartIIIb.Concrete
