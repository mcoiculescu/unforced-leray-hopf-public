import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_12_3_1_4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.ChartBound.ChartQFixed

/-!
# `PartIII-b:IIIb-D2/3/2/12/3/1/4/2`: `StressBallLintegral` (leaf C)

Source of record: `the November 2 reference manuscript`,
lines 2683, 2698-2700, 3256-3268, 4284-4286.

Cauchy-Schwarz on the phase cell with the ball `{‖y‖ ≤ Y}`, followed by the ring change of variables
`RingChartRegionLintegral` applied to the `q`-periodic integrand
`G'(s,(q,η)) = 1_{StrRegion Y} s^{1/2·4} ‖g(s,(cellRep c q,η))‖ₑ^{2}` (here `s^2 ‖g‖^2` in the
rpow form `ENNReal.ofReal (s^(2:ℝ)) * ‖g‖ₑ^(2:ℝ)`), and `Axi.lintegral_ageμ` with `a = -1/2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete (phaseCell)
open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Short.PartIIIb

/-- The ball `{y | ‖y‖ ≤ Y}` in the chart-phase product. -/
def sblBall (Y : ℝ) : Set (ℝ × UnforcedLeray.Space) := {x | ‖x.2‖ ≤ Y}

theorem sblBall_meas (Y : ℝ) : MeasurableSet (sblBall Y) :=
  measurableSet_le (measurable_norm.comp measurable_snd) measurable_const

theorem sbl_norm_le (z : UnforcedLeray.Space) (Y : ℝ) (h : ‖z‖ ≤ Y) : |z 2| ≤ Y := by
  have h2 := PiLp.norm_apply_le z (2 : Fin 3)
  rw [Real.norm_eq_abs] at h2
  linarith

theorem sbl_vol_lt_top (P Y : ℝ) :
    volume (sblBall Y ∩ phaseCell P) < ⊤ := by
  have hsub : sblBall Y ∩ phaseCell P ⊆
      Ioc (0 : ℝ) P ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) Y := by
    rintro x ⟨hx2, hx1⟩
    have hx1' : x ∈ Ioc (0 : ℝ) P ×ˢ (univ : Set UnforcedLeray.Space) := hx1
    refine Set.mem_prod.2 ⟨(Set.mem_prod.1 hx1').1, Metric.mem_closedBall.2 ?_⟩
    rw [dist_zero_right]
    exact hx2
  have hfin : volume (Ioc (0 : ℝ) P ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) Y) < ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
  exact lt_of_le_of_lt (measure_mono hsub) hfin

/-- The Cauchy-Schwarz weight integral over the ball (independent of `g`). -/
def sblV (P Y : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in phaseCell P, ((sblBall Y).indicator (1 : ℝ × UnforcedLeray.Space → ℝ≥0∞) x) ^ (2:ℝ)

theorem sbl_indicator_one_rpow (Y : ℝ) (x : ℝ × UnforcedLeray.Space) :
    ((sblBall Y).indicator (1 : ℝ × UnforcedLeray.Space → ℝ≥0∞) x) ^ (2:ℝ)
      = (sblBall Y).indicator (1 : ℝ × UnforcedLeray.Space → ℝ≥0∞) x := by
  rw [ENNReal.rpow_two]
  by_cases hx : x ∈ sblBall Y
  · simp [hx]
  · simp [hx]

theorem sblV_lt_top (P Y : ℝ) : sblV P Y < ⊤ := by
  unfold sblV
  simp only [sbl_indicator_one_rpow]
  rw [lintegral_indicator_one (sblBall_meas Y), Measure.restrict_apply (sblBall_meas Y)]
  exact sbl_vol_lt_top P Y

/-- The chart-side integrand of `stressBall`, as an `ENNReal`-valued function. -/
def sblH (R c : ℝ) (g : Chart → Ten3) (x : ℝ × UnforcedLeray.Space) : ℝ≥0∞ :=
  ENNReal.ofReal ((NearInst.chartOf R c x.2 x.1).1) * ‖g (NearInst.chartOf R c x.2 x.1)‖ₑ

theorem sbl_s_nonneg (R c : ℝ) (x : ℝ × UnforcedLeray.Space) :
    0 ≤ (NearInst.chartOf R c x.2 x.1).1 := by
  show 0 ≤ R ^ 2 / NearInst.hRad x.2 ^ 2
  positivity

theorem sbl_ofReal_stressBall (R c Y : ℝ) (g : Chart → Ten3) (x : ℝ × UnforcedLeray.Space) :
    ENNReal.ofReal (stressBall R c Y g x) = (sblBall Y).indicator (sblH R c g) x := by
  unfold sblH
  by_cases hx : x ∈ sblBall Y
  · have hx' : ‖x.2‖ ≤ Y := hx
    simp only [Set.indicator_of_mem hx]
    unfold stressBall
    rw [if_pos hx', ENNReal.ofReal_mul (sbl_s_nonneg R c x), ofReal_norm_eq_enorm]
  · have hx' : ¬ ‖x.2‖ ≤ Y := hx
    simp only [Set.indicator_of_notMem hx]
    unfold stressBall
    rw [if_neg hx', ENNReal.ofReal_zero]

theorem sbl_indicator_mul (Y : ℝ) (H : ℝ × UnforcedLeray.Space → ℝ≥0∞) :
    (sblBall Y).indicator (1 : ℝ × UnforcedLeray.Space → ℝ≥0∞) * (sblBall Y).indicator H
      = (sblBall Y).indicator H := by
  funext x
  by_cases hx : x ∈ sblBall Y
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

theorem sbl_chartOf_meas (R c : ℝ) :
    Measurable fun x : ℝ × UnforcedLeray.Space => NearInst.chartOf R c x.2 x.1 := by
  unfold NearInst.chartOf NearInst.hRad
  have hz2 : Measurable fun z : UnforcedLeray.Space => z 2 :=
    (EuclideanSpace.proj (2 : Fin 3) : UnforcedLeray.Space →L[ℝ] ℝ).continuous.measurable
  fun_prop

theorem sbl_H_meas (R c : ℝ) (g : Chart → Ten3) (hg : Measurable g) :
    Measurable (sblH R c g) := by
  unfold sblH
  exact (ENNReal.measurable_ofReal.comp (measurable_fst.comp (sbl_chartOf_meas R c))).mul
    ((hg.comp (sbl_chartOf_meas R c)).enorm)

theorem strRegion_meas (Y : ℝ) : MeasurableSet (StrRegion Y) := by
  unfold StrRegion
  exact (isClosed_le (by fun_prop) (by fun_prop)).measurableSet

/-- The periodised integrand `G'` on the ring chart. -/
def sblG (c Y : ℝ) (g : Chart → Ten3) : Chart → ℝ≥0∞ :=
  (StrRegion Y).indicator (fun p => ENNReal.ofReal (p.1 ^ (2:ℝ)) *
    ‖g (p.1, (Axi.cellRep c p.2.1, p.2.2))‖ₑ ^ (2:ℝ))

theorem sblG_per (c Y : ℝ) (hc : 0 < c) (g : Chart → Ten3) :
    ∀ s q η : ℝ, sblG c Y g (s, (q + c, η)) = sblG c Y g (s, (q, η)) := by
  intro s q η
  unfold sblG
  by_cases hm : ((s, (q, η)) : Chart) ∈ StrRegion Y
  · have hm' : ((s, (q + c, η)) : Chart) ∈ StrRegion Y := hm
    simp only [Set.indicator_of_mem hm, Set.indicator_of_mem hm', Axi.cellRep_add hc.ne']
  · have hm' : ((s, (q + c, η)) : Chart) ∉ StrRegion Y := hm
    simp only [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm']

theorem sblG_meas (c Y : ℝ) (g : Chart → Ten3) (hg : Measurable g) :
    Measurable (sblG c Y g) := by
  have hcomp : Measurable fun p : Chart => (p.1, (Axi.cellRep c p.2.1, p.2.2)) :=
    Measurable.prodMk measurable_fst
      (Measurable.prodMk ((Axi.measurable_cellRep c).comp (measurable_fst.comp measurable_snd))
        (measurable_snd.comp measurable_snd))
  have h1 : Measurable fun p : Chart => ENNReal.ofReal (p.1 ^ (2:ℝ)) :=
    ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)
  have h2 : Measurable fun p : Chart => ‖g (p.1, (Axi.cellRep c p.2.1, p.2.2))‖ₑ ^ (2:ℝ) :=
    ((hg.comp hcomp).enorm).pow_const _
  unfold sblG
  exact (h1.mul h2).indicator (strRegion_meas Y)

theorem sbl_pointwise (R c Y : ℝ) (hR : 0 < R) (hc : 0 < c) (hY : 0 ≤ Y) (g : Chart → Ten3)
    (x : ℝ × UnforcedLeray.Space) :
    ((sblBall Y).indicator (sblH R c g) x) ^ (2:ℝ) ≤ sblG c Y g (NearInst.chartOf R c x.2 x.1) := by
  by_cases hx : x ∈ sblBall Y
  · have hx' : ‖x.2‖ ≤ Y := hx
    have hmem : NearInst.chartOf R c x.2 x.1 ∈ StrRegion Y :=
      chartOfMemStrRegion_proved R Y c hR hY x.2 x.1 (sbl_norm_le x.2 Y hx')
    simp only [Set.indicator_of_mem hx]
    unfold sblG sblH
    simp only [Set.indicator_of_mem hmem]
    rw [chartOf_q_fixed_by_cellRep R c hR hc x.2 x.1]
    simp only [Prod.mk.eta]
    refine le_of_eq ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (sbl_s_nonneg R c x) (by norm_num)]
  · simp only [Set.indicator_of_notMem hx]
    exact (ENNReal.zero_rpow_of_pos (by norm_num)).trans_le bot_le

theorem sbl_key_pt (c Y : ℝ) (hc : 0 < c) (g : Chart → Ten3) (p : Chart)
    (hp : p ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c) :
    ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2) : ℝ)) * sblG c Y g p
      = ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) *
          (StrRegion Y).indicator (fun p => ‖g p‖ₑ ^ (2:ℝ)) p := by
  have hs : 0 < p.1 := (Set.mem_prod.1 hp).1
  have hq : p.2 ∈ Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ) := (Set.mem_prod.1 hp).2
  have hcell : Axi.cellRep c p.2.1 = p.2.1 := Axi.cellRep_of_mem hc (Set.mem_prod.1 hq).1
  have hpe : (p.1, (Axi.cellRep c p.2.1, p.2.2)) = p := Prod.ext rfl (Prod.ext hcell rfl)
  have key : ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2) : ℝ)) * ENNReal.ofReal (p.1 ^ (2:ℝ))
      = ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) := by
    rw [← ENNReal.ofReal_mul
      (mul_nonneg (inv_nonneg.2 hc.le) (Real.rpow_nonneg hs.le _))]
    congr 1
    have hr : p.1 ^ (-(5 / 2) : ℝ) * p.1 ^ (2:ℝ) = p.1 ^ (-1 / 2 : ℝ) := by
      rw [← Real.rpow_add hs]
      norm_num
    calc c⁻¹ * p.1 ^ (-(5 / 2) : ℝ) * p.1 ^ (2:ℝ)
        = c⁻¹ * (p.1 ^ (-(5 / 2) : ℝ) * p.1 ^ (2:ℝ)) := by ring
      _ = c⁻¹ * p.1 ^ (-1 / 2 : ℝ) := by rw [hr]
  unfold sblG
  by_cases hm : p ∈ StrRegion Y
  · simp only [Set.indicator_of_mem hm, hpe]
    rw [← mul_assoc, key]
  · simp only [Set.indicator_of_notMem hm, mul_zero]

theorem sbl_W_le (R c P Y : ℝ) (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R) (hY : 0 ≤ Y)
    (g : Chart → Ten3) (hg : Measurable g) :
    ∫⁻ x in phaseCell P, ((sblBall Y).indicator (sblH R c g) x) ^ (2:ℝ)
      ≤ ENNReal.ofReal P * ENNReal.ofReal (Real.pi * R ^ 2) *
          ∫⁻ p in StrRegion Y, ‖g p‖ₑ ^ (2:ℝ) ∂(Axi.ageμ c (-1 / 2)) := by
  have hRC := ringChartRegionLintegral_proved R c P hR hc hP (sblG c Y g)
    (sblG_meas c Y g hg) (sblG_per c Y hc g)
  have e1 : ∫⁻ p in StrRegion Y, ‖g p‖ₑ ^ (2:ℝ) ∂(Axi.ageμ c (-1 / 2))
      = ∫⁻ p, (StrRegion Y).indicator (fun p => ‖g p‖ₑ ^ (2:ℝ)) p ∂(Axi.ageμ c (-1 / 2)) :=
    (lintegral_indicator (strRegion_meas Y) _).symm
  have hfm : Measurable ((StrRegion Y).indicator (fun p => ‖g p‖ₑ ^ (2:ℝ))) :=
    (hg.enorm.pow_const (2:ℝ)).indicator (strRegion_meas Y)
  have e2 := Axi.lintegral_ageμ hc (-1 / 2) hfm
  calc ∫⁻ x in phaseCell P, ((sblBall Y).indicator (sblH R c g) x) ^ (2:ℝ)
      ≤ ∫⁻ x in phaseCell P, sblG c Y g (NearInst.chartOf R c x.2 x.1) :=
        lintegral_mono fun x => sbl_pointwise R c Y hR hc hY g x
    _ = ENNReal.ofReal P * ENNReal.ofReal (Real.pi * R ^ 2) *
          ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c, ENNReal.ofReal (c⁻¹ * p.1 ^ (-(5 / 2) : ℝ)) * sblG c Y g p :=
        hRC
    _ = ENNReal.ofReal P * ENNReal.ofReal (Real.pi * R ^ 2) *
          ∫⁻ p in Ioi (0 : ℝ) ×ˢ Axi.qCell c, ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) *
            (StrRegion Y).indicator (fun p => ‖g p‖ₑ ^ (2:ℝ)) p := by
        congr 1
        exact setLIntegral_congr_fun (Axi.measurableSet_halfCell c)
          (fun p hp => sbl_key_pt c Y hc g p hp)
    _ = ENNReal.ofReal P * ENNReal.ofReal (Real.pi * R ^ 2) *
          ∫⁻ p in StrRegion Y, ‖g p‖ₑ ^ (2:ℝ) ∂(Axi.ageμ c (-1 / 2)) := by
        rw [e1, e2]

theorem stressBallLintegral_proof : UnforcedLeray.Short.PartIIIb.Concrete.StressBallLintegral := by
  intro R c P Y hR hc hP hY
  have hP0 : 0 < P := by
    rw [hP]
    exact div_pos (mul_pos two_pos hc) hR
  have hX : 0 ≤ (sblV P Y).toReal * (P * (Real.pi * R ^ 2)) :=
    mul_nonneg ENNReal.toReal_nonneg (mul_nonneg hP0.le (by positivity))
  refine ⟨((sblV P Y).toReal * (P * (Real.pi * R ^ 2))) ^ (1 / 2 : ℝ),
    Real.rpow_nonneg hX _, ?_⟩
  intro g hg
  have hHolder : ∫⁻ x in phaseCell P, (sblBall Y).indicator (sblH R c g) x
      ≤ sblV P Y ^ (1 / 2 : ℝ) *
        (∫⁻ x in phaseCell P, ((sblBall Y).indicator (sblH R c g) x) ^ (2:ℝ)) ^ (1 / 2 : ℝ) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (phaseCell P))
      Real.HolderConjugate.two_two
      (f := (sblBall Y).indicator (1 : ℝ × UnforcedLeray.Space → ℝ≥0∞))
      (g := (sblBall Y).indicator (sblH R c g))
      (measurable_const.indicator (sblBall_meas Y)).aemeasurable
      ((sbl_H_meas R c g hg).indicator (sblBall_meas Y)).aemeasurable
    rw [sbl_indicator_mul] at h
    exact h
  have hL : ∫⁻ x in phaseCell P, ENNReal.ofReal (stressBall R c Y g x)
      = ∫⁻ x in phaseCell P, (sblBall Y).indicator (sblH R c g) x :=
    lintegral_congr fun x => sbl_ofReal_stressBall R c Y g x
  have hW := sbl_W_le R c P Y hR hc hP hY g hg
  have h12 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hmul : sblV P Y ^ (1 / 2 : ℝ) *
      (ENNReal.ofReal P * ENNReal.ofReal (Real.pi * R ^ 2) *
        ∫⁻ p in StrRegion Y, ‖g p‖ₑ ^ (2:ℝ) ∂(Axi.ageμ c (-1 / 2))) ^ (1 / 2 : ℝ)
      = (sblV P Y * (ENNReal.ofReal P * ENNReal.ofReal (Real.pi * R ^ 2))) ^ (1 / 2 : ℝ) *
        (∫⁻ p in StrRegion Y, ‖g p‖ₑ ^ (2:ℝ) ∂(Axi.ageμ c (-1 / 2))) ^ (1 / 2 : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal P * ENNReal.ofReal (Real.pi * R ^ 2))
        (∫⁻ p in StrRegion Y, ‖g p‖ₑ ^ (2:ℝ) ∂(Axi.ageμ c (-1 / 2))) h12,
      ENNReal.mul_rpow_of_nonneg (sblV P Y) (ENNReal.ofReal P * ENNReal.ofReal (Real.pi * R ^ 2)) h12]
    ring
  have hVQ : sblV P Y * (ENNReal.ofReal P * ENNReal.ofReal (Real.pi * R ^ 2))
      = ENNReal.ofReal ((sblV P Y).toReal * (P * (Real.pi * R ^ 2))) := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_mul hP0.le,
      ENNReal.ofReal_toReal (sblV_lt_top P Y).ne]
  calc ∫⁻ x in phaseCell P, ENNReal.ofReal (stressBall R c Y g x)
      = ∫⁻ x in phaseCell P, (sblBall Y).indicator (sblH R c g) x := hL
    _ ≤ _ := hHolder
    _ ≤ sblV P Y ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal P * ENNReal.ofReal (Real.pi * R ^ 2) *
          ∫⁻ p in StrRegion Y, ‖g p‖ₑ ^ (2:ℝ) ∂(Axi.ageμ c (-1 / 2))) ^ (1 / 2 : ℝ) := by
        gcongr
    _ = (sblV P Y * (ENNReal.ofReal P * ENNReal.ofReal (Real.pi * R ^ 2))) ^ (1 / 2 : ℝ) *
        (∫⁻ p in StrRegion Y, ‖g p‖ₑ ^ (2:ℝ) ∂(Axi.ageμ c (-1 / 2))) ^ (1 / 2 : ℝ) := hmul
    _ = ENNReal.ofReal ((sblV P Y).toReal * (P * (Real.pi * R ^ 2))) ^ (1 / 2 : ℝ) *
        (∫⁻ p in StrRegion Y, ‖g p‖ₑ ^ (2:ℝ) ∂(Axi.ageμ c (-1 / 2))) ^ (1 / 2 : ℝ) := by
        rw [hVQ]
    _ = ENNReal.ofReal (((sblV P Y).toReal * (P * (Real.pi * R ^ 2))) ^ (1 / 2 : ℝ)) *
        (∫⁻ p in StrRegion Y, ‖g p‖ₑ ^ (2:ℝ) ∂(Axi.ageμ c (-1 / 2))) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hX h12]
