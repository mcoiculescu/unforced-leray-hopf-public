import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.AsmYA.Meas

/-!
# `PartIII-b:C/rep/8/1/1/2/4/1` (`phasePrimitiveYA`): reduction to the phase-primitive kernel bound

Source `the November 2 reference manuscript`
lines 5415-5421 ("One phase primitive in the dilation variable, with its dilation-one boundary
term retained"), 5400-5413 (separated kernels; the gradient Newton kernel has degree `-5`; the
ratio of the old source radius to the young receiver radius is at most `1/√1.2`), 4168-4171
(`W_μ = -S_μ(χ_oT)`), SP 2747-2752 (the first moment `N₁`).

**Status: partial.**  Proved here:

* the measurability conjunct of `PhasePrimitiveYAAt` (`dPhaseW_cell_aemeas`: the receiver
  `chartY R (s,(q,η))` does not depend on `q` and lies in the clear region for `0 < s ≤ 1/ν`, the
  phase `chartTau` is measurable in `q`, and `1_clear dPhaseW` is jointly measurable, `Meas.lean`);
* the identity `dPhaseW T = dOsc ν ε μ (thinG T)` (definitional) and the reduction
  `phasePrimitiveYA_of` of the target to two leaves;
* leaf 2, `thinMomentBridge`; hence `phasePrimitiveYA_of_kernel : PhaseOscKernel →
  D.PhasePrimitiveYA`.  The only missing fact is `PhaseOscKernel`.

The two leaves (statements below):

* `PhaseOscKernel` (the analytic content of 5415-5421): for every measurable chart tensor `g`
  vanishing a.e. on `νs ≤ 6/5`, at every young chart point `0 < s ≤ 1/ν`,
  `‖D_yW_μ(g) - D_yW_μ(meanQ g)‖_{L²_τ} ≤ C ν^{-k} ε⁴ s^{5/2} N₁(g)`.
  NB: the factor `s^{5/2} = (R/r)⁵` (receiver radius `r = R/√s`) is the degree `-5` homogeneity of
  the gradient kernel; it is *not* a consequence of a bound polynomial in the receiver radius
  `ρ_i = 1/√s` such as `IIIa.SepMeanComparison`/`IIIa.SepOscPart` (their factor
  `(1 + ρ_i)^k` grows as `s → 0`), so those statements cannot be used as they stand.
* `ThinMomentBridge`: `N₁(thinG T) ≤ oldN1 T` (the chart representative `thinG T` of `χ_oT₁`
  equals `χ_o(νs) thinRep T` a.e. for `ageμ c (-1/2)`; `chiOStrApply`, `thinPart`,
  `NearInst.ae_gainZ1Measure`, `NearInst.ae_z1Measure`, `NearInst.ae_gainHTMeasure`,
  `NearInst.ae_htRhoMeasure`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace PhasePrimYA

open GeomXAsm MeasYAAux ZRegAux

/-- The age-weighted first transverse moment `N₁` of a chart tensor (`IIIa.firstMoment` of its
matrix field, SP 2747-2752; `oldN1 T = N₁(χ_o thinRep T)`). -/
def tenN1 (c : ℝ) (g : Chart → Ten3) : ℝ≥0∞ :=
  IIIa.firstMoment c 0 (fun p => Ten3.toMatrix (g p))

/-- The phase part `|D_yW_μ(g) - D_yW_μ(meanQ g)|` of the response of a chart tensor `g`
(`dPhaseW T = dOsc ν ε μ (thinG T)`). -/
def dOsc (ν ε μ : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) : ℝ :=
  ‖fderiv ℝ (sepWre ν μ (oldPhys ε⁻¹ (cOf ν) g) τ) y -
    fderiv ℝ (sepWre ν μ (oldPhys ε⁻¹ (cOf ν) (meanQ (cOf ν) g)) τ) y‖

/-- **Leaf 1: the phase-primitive kernel bound** (source 5415-5421, 5400-5413; mechanism SP
3768-3790): `g - meanQ g` has zero `q`-mean on the cell, the phase `q = R log(ρ/R) + Rτ/2`
enters the separated kernel through the dilation variable (`τ + 2 log λ`, so `∂_{log λ} = ε⁻¹∂_q`),
one primitive `J = ∂_q⁻¹` in `λ` with the boundary term at `λ = 1` kept gains one power of `ε`;
the gradient kernel has degree `-5` and the receiver radius `r = R/√s` is at least `√1.2` times
the old-source radius, which gives `(R/r)⁵ = s^{5/2}`; the source mass in outer coordinates is
`π ε⁻² ∫ s^{-3/2}|g| ds dη ≤ N₁(g)`. -/
def PhaseOscKernel : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ ν ε μ : ℝ, 0 < ν → ν ≤ 1 → 0 < ε → ε ≤ 1 → 0 < μ → μ < 1 / 4 →
    ∀ g : Chart → Ten3, Measurable g →
      ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ (cOf ν) (-1 / 2)) < ⊤ →
      (∀ᵐ p ∂(ageμ (cOf ν) (-1 / 2)), ν * p.1 ≤ 6 / 5 → g p = 0) →
      ∀ s ∈ Ioc (0 : ℝ) (1 / ν), ∀ η : ℝ,
        cellL2 ε⁻¹ (cOf ν) (dOsc ν ε μ g) s η ≤
          ENNReal.ofReal (C * ν⁻¹ ^ k * (ε ^ 4 * s ^ (5 / 2 : ℝ))) * tenN1 (cOf ν) g

/-- **Leaf 2: the first moment of the old thin source** (source 5400; `oldN1`): the chart
representative `thinG T = strSum (chiOStr (thinPart T))` agrees `ageμ c (-1/2)`-a.e. with
`χ_o(νs) • T₁`, so `N₁(thinG T) ≤ N₁(χ_o thinRep T) = oldN1 T`. -/
def ThinMomentBridge : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel), 0 < K.C0 → ∀ T : LStr Pl K L,
    tenN1 (cOf L.ν) (thinG Pl K L T) ≤ oldN1 Pl K L T

/-! ## Leaf 2 is proved: the first moment of the old thin source -/

/-- Two chart matrix fields that agree `ageμ c (-1/2)`-a.e. have the same first moment. -/
theorem firstMoment_congr_ae {c : ℝ} (hc : 0 < c) {F G : Chart → Matrix (Fin 3) (Fin 3) ℝ}
    (hFm : Measurable fun p => IIIa.frobSq (F p)) (hGm : Measurable fun p => IIIa.frobSq (G p))
    (h : ∀ᵐ p ∂(ageμ c (-1 / 2)), F p = G p) :
    IIIa.firstMoment c 0 F = IIIa.firstMoment c 0 G := by
  have h' : ∀ᵐ p ∂(ageμ c (-1 / 2)), IIIa.frobSq (F p) = IIIa.frobSq (G p) := by
    filter_upwards [h] with p hp
    rw [hp]
  rw [ageμ] at h'
  have hA := Measure.ae_ae_of_ae_prod h'
  rw [ae_withDensity_iff (measurable_ofReal_rpow _)] at hA
  have hB : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ η : ℝ,
      ∀ᵐ q ∂(volume.restrict (Ico (-(c / 2)) (c / 2))),
        IIIa.frobSq (F (s, (q, η))) = IIIa.frobSq (G (s, (q, η))) := by
    filter_upwards [hA, ae_restrict_mem measurableSet_Ioi] with s hs hs0
    have hw : ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact Real.rpow_pos_of_pos hs0 _
    have h1 := hs hw
    have hc' : ENNReal.ofReal c⁻¹ ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact inv_pos.2 hc
    rw [UnforcedLeray.Cyl.avgμ, Measure.ae_ennreal_smul_measure_iff hc', UnforcedLeray.Cyl.cellμ,
      UnforcedLeray.Cyl.cell, Measure.volume_eq_prod, ← Measure.prod_restrict,
      Measure.restrict_univ] at h1
    have h2 := Measure.ae_ae_of_ae_prod h1
    have hmeas : MeasurableSet {x : ℝ × ℝ |
        IIIa.frobSq (F (s, (x.1, x.2))) = IIIa.frobSq (G (s, (x.1, x.2)))} :=
      measurableSet_eq_fun (hFm.comp (by fun_prop)) (hGm.comp (by fun_prop))
    rw [Measure.ae_ae_comm hmeas] at h2
    simpa [neg_div] using h2
  unfold IIIa.firstMoment
  refine lintegral_congr_ae ?_
  filter_upwards [hB] with s hs
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [hs] with η hη
  congr 1
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [hη] with q hq
  rw [hq]

/-- The chart representative of `χ_oT₁` is `χ_o(νs) T₁` a.e. (`chiOStrApply`, `thinPart`). -/
theorem thinG_toMatrix_ae (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (hC0 : 0 < K.C0)
    (T : LStr Pl K L) :
    ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)),
      Ten3.toMatrix (thinG Pl K L T p) = K.χo (L.ν * p.1) • thinRep T p := by
  have hρb := rho_b_pos' Pl K L hC0
  obtain ⟨h1, h2⟩ := chiOStrApply (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.χo K.hχo
    (thinPart T)
  have h0 : ∀ᵐ p ∂(gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν),
      ((thinPart T).snd : Chart → Ten3) p = 0 := by
    have e : (thinPart T).snd = 0 := by simp [thinPart]
    rw [e]
    exact Lp.coeFn_zero _ _ _
  rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at h1
  rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρb] at h2 h0
  filter_upwards [h1, h2, h0] with p e1 e2 e0
  have ef : (thinPart T).fst = T.fst := by simp [thinPart]
  have e : thinG Pl K L T p = cutFun K.χo L.ν p • (T.fst : Chart → Ten3) p := by
    simp only [thinG, Pi.add_apply, e1, e2, e0, smul_zero, add_zero, ef]
  rw [e]
  ext a b
  simp [Ten3.toMatrix, thinRep, cutFun]
  rfl

theorem continuous_frobSq_toMatrix :
    Continuous fun x : Ten3 => IIIa.frobSq (Ten3.toMatrix x) := by
  unfold IIIa.frobSq Ten3.toMatrix
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_
  exact ((EuclideanSpace.proj (a, b) : Ten3 →L[ℝ] ℝ).continuous).pow 2

/-- **Leaf 2** (`ThinMomentBridge`), proved. -/
theorem thinMomentBridge : ThinMomentBridge := by
  intro Pl K L hC0 T
  have hc := cOf_pos L.ν_pos
  show IIIa.firstMoment (cOf L.ν) 0 _ ≤ IIIa.firstMoment (cOf L.ν) 0 _
  refine le_of_eq (firstMoment_congr_ae hc ?_ ?_ (thinG_toMatrix_ae Pl K L hC0 T))
  · exact continuous_frobSq_toMatrix.measurable.comp (DPhaseMeasAux.measurable_thinG Pl K L T)
  · have hG : (fun p : Chart => IIIa.frobSq (K.χo (L.ν * p.1) • thinRep T p)) = fun p =>
        IIIa.frobSq (Ten3.toMatrix (cutFun K.χo L.ν p • ((WithLp.ofLp T).1 : Chart → Ten3) p)) := by
      funext p
      congr 1
    rw [hG]
    exact continuous_frobSq_toMatrix.measurable.comp
      ((cutFun_measurable K.hχo L.ν).smul (Lp.stronglyMeasurable _).measurable)

theorem dPhaseW_eq_dOsc (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (T : LStr Pl K L) : dPhaseW Pl K L μ T = dOsc L.ν L.ε μ (thinG Pl K L T) := rfl

/-- A young chart point `0 < s ≤ 1/ν` lies in the clear region. -/
theorem chartY_mem_clearSet {ε ν s : ℝ} (hε : 0 < ε) (hν : 0 < ν) (hs : s ∈ Ioc (0 : ℝ) (1 / ν))
    (q η : ℝ) : NearInst.chartY ε⁻¹ (s, (q, η)) ∈ clearSet ε ν := by
  have hs0 : 0 < s := hs.1
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hρ : 0 < ε⁻¹ / Real.sqrt s := div_pos (inv_pos.2 hε) hsq
  rw [chartY_eq_hpt]
  refine ⟨?_, ?_⟩
  · show 0 < ϱ (hpt (ε⁻¹ / Real.sqrt s) (η / Real.sqrt s))
    rw [ZPrimKernel.ϱ_hpt hρ]
    exact hρ
  · show ν / (11 / 10) < (ε * ϱ (hpt (ε⁻¹ / Real.sqrt s) (η / Real.sqrt s))) ^ 2
    rw [ZPrimKernel.ϱ_hpt hρ]
    have h1 : ε * (ε⁻¹ / Real.sqrt s) = (Real.sqrt s)⁻¹ := by
      field_simp
    have h2 : ((Real.sqrt s)⁻¹) ^ 2 = s⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hs0.le]
    rw [h1, h2]
    have h3 : ν ≤ s⁻¹ := by
      rw [le_inv_comm₀ hν hs0, ← one_div]
      exact hs.2
    have h4 : ν / (11 / 10) < ν := div_lt_self hν (by norm_num)
    linarith

/-- **The measurability conjunct** of `PhasePrimitiveYAAt`. -/
theorem dPhaseW_cell_aemeas (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) (hμ : -(1 / 4) < μ) (T : LStr Pl K L) {s : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) (1 / L.ν)) (η : ℝ) :
    AEMeasurable (fun q : ℝ => dPhaseW Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
        (NearInst.chartY L.ε⁻¹ (s, (q, η))))
      (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2))) := by
  set y₀ : Space := NearInst.chartY L.ε⁻¹ (s, (0, η)) with hy₀def
  have hy : ∀ q : ℝ, NearInst.chartY L.ε⁻¹ (s, (q, η)) = y₀ := fun q => rfl
  have hmem : y₀ ∈ clearSet L.ε L.ν := chartY_mem_clearSet L.ε_pos L.ν_pos hs 0 η
  have hτ : Measurable fun q : ℝ => NearInst.chartTau L.ε⁻¹ (s, (q, η)) := by
    unfold NearInst.chartTau
    fun_prop
  have hm := (dPhaseW_measurable Pl K L μ hC0 hmZ hμ T).comp
    (hτ.prodMk (measurable_const (a := y₀)))
  have hfun : (fun q : ℝ => dPhaseW Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
      (NearInst.chartY L.ε⁻¹ (s, (q, η)))) =
      (fun p : ℝ × Space => (clearSet L.ε L.ν).indicator (fun y => dPhaseW Pl K L μ T p.1 y) p.2) ∘
        fun q : ℝ => (NearInst.chartTau L.ε⁻¹ (s, (q, η)), y₀) := by
    funext q
    simp only [Function.comp_apply, hy q]
    rw [Set.indicator_of_mem hmem]
  rw [hfun]
  exact hm.aemeasurable

/-- **Reduction** of `PartIII-b:C/rep/8/1/1/2/4/1` to the two leaves. -/
theorem phasePrimitiveYA_of (hK : PhaseOscKernel) (hB : ThinMomentBridge) (D : SeqData)
    {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.PhasePrimitiveYA := by
  obtain ⟨C, k, hC, hKer⟩ := hK
  refine ⟨C, k, ?_⟩
  filter_upwards [retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne] with n hn
    z _
  intro hL T s hs η
  have hμ : -(1 / 4) < D.mu n z := by linarith [hL.mu_pos]
  have hmZ : 0 ≤ D.K.mZ := by linarith [hst.mZ_gt]
  refine ⟨dPhaseW_cell_aemeas D.Pl D.K (D.level n) (D.mu n z) hst.C0_pos hmZ hμ T hs η, ?_⟩
  have hρb := rho_b_pos' D.Pl D.K (D.level n) hst.C0_pos
  have hg := DPhaseMeasAux.measurable_thinG D.Pl D.K (D.level n) T
  have hz0 : ∀ᵐ p ∂(ageμ (cOf (D.level n).ν) (-1 / 2)), (D.level n).ν * p.1 ≤ 6 / 5 →
      thinG D.Pl D.K (D.level n) T p = 0 :=
    strSum_zero_young _ _ _ _ _ D.K.hχo hρb _
  have hmom : ∫⁻ p, ‖thinG D.Pl D.K (D.level n) T p‖ₑ ^ 2
      ∂(ageμ (cOf (D.level n).ν) (-1 / 2)) < ⊤ :=
    strChartL2 (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K) (gRate D.Pl) (D.level n).ν
      hρb (by linarith [hst.mZ_gt]) (D.level n).ν_pos _
  have h1 := hKer (D.level n).ν (D.level n).ε (D.mu n z) (D.level n).ν_pos hL.nu_le
    (D.level n).ε_pos hn.2 hL.mu_pos hL.mu_lt (thinG D.Pl D.K (D.level n) T) hg hmom hz0 s hs η
  rw [dPhaseW_eq_dOsc]
  refine h1.trans ?_
  gcongr
  exact hB D.Pl D.K (D.level n) hst.C0_pos T

/-- **`PartIII-b:C/rep/8/1/1/2/4/1` from the phase-primitive kernel bound alone** (the moment
bridge is proved, `thinMomentBridge`). -/
theorem phasePrimitiveYA_of_kernel (hK : PhaseOscKernel) (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) : D.PhasePrimitiveYA :=
  phasePrimitiveYA_of hK thinMomentBridge D hst

end PhasePrimYA

end UnforcedLeray.Short.PartIIIb.Concrete
