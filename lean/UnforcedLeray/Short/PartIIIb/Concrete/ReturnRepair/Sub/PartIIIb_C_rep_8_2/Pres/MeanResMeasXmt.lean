import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanResMeasDefs

/-!
# Measurability of the Newton field `Xmt` (task `PartIII-b:C/rep/8/2/pres/6/1`)

Source `the November 2 reference manuscript`
lines 1205-1225, 4139-4141, 4776-4791, 5272-5289.  `thinRep T` is the strongly measurable
representative of an `Lp` class (`Lp.stronglyMeasurable`), so `phaseMean`, `sigmaM`, `newtonV`
(parametric integrals), `youngW`, `streamPsi`, `streamCut` and `Xmt` are measurable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal Classical

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem thinRep_measurable {c mZ ρb γ ν : ℝ} (T : StrG c mZ ρb γ ν) :
    Measurable (thinRep T) := by
  unfold thinRep
  have h : Measurable (fun p => ((WithLp.ofLp T).1 : Chart → Ten3) p) :=
    (Lp.stronglyMeasurable _).measurable
  unfold Ten3.toMatrix
  exact measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b =>
    ((EuclideanSpace.proj (𝕜 := ℝ) (a, b)).continuous.measurable).comp h

theorem phaseMean_measurable (c ν : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) {M : Chart → Mat3}
    (hM : Measurable M) : Measurable (phaseMean c ν χo M) := by
  have hχ : Measurable χo := hχo.smooth.continuous.measurable
  have : SFinite (Cyl.avgμ c) := by unfold Cyl.avgμ Cyl.cellμ; infer_instance
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  unfold phaseMean
  by_cases h : i = 1 ∨ j = 1
  · simp only [h, ite_true]; exact measurable_const
  · simp only [h, ite_false]
    have hm : Measurable (fun p : ℝ × (ℝ × ℝ) => M p i j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hM)
    refine (hχ.comp (measurable_const.mul measurable_id)).mul ?_
    exact (hm.stronglyMeasurable.integral_prod_right' (ν := Cyl.avgμ c)).measurable

theorem newtonD3_measurable (i j k : Fin 3) : Measurable (fun x => newtonD3 x i j k) := by
  unfold newtonD3
  exact measurable_fderiv_apply_const ℝ _ _

theorem rotQ_measurable (a i : Fin 3) : Measurable (fun x' : ℝ × ℝ => rotQ x' a i) := by
  fin_cases a <;> fin_cases i <;> simp [rotQ] <;> fun_prop

theorem sigmaM_measurable (c ν : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) {M : Chart → Mat3}
    (hM : Measurable M) (a b : Fin 3) : Measurable (fun x' => sigmaM c ν χo M x' a b) := by
  have hp := phaseMean_measurable c ν hχo hM
  unfold sigmaM
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  have hu : Measurable (fun x' : ℝ × ℝ => (x'.1 ^ 2 + x'.2 ^ 2)⁻¹) := by fun_prop
  have h1 : Measurable (fun x' : ℝ × ℝ => phaseMean c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (hp.comp hu))
  refine ((rotQ_measurable a i).mul (Measurable.mul ?_ h1)).mul (rotQ_measurable b j)
  fun_prop

theorem embPlane_measurable : Measurable embPlane := by
  refine measurable_pi_lambda _ fun a => ?_
  fin_cases a <;> simp [embPlane] <;> fun_prop

theorem newtonV_measurable (c ν μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    {M : Chart → Mat3} (hM : Measurable M) : Measurable (newtonV c ν μ χo M) := by
  refine measurable_pi_lambda _ fun i => ?_
  unfold newtonV
  refine Measurable.const_mul ?_ _
  have hG : Measurable (fun q : (Vec3 × ℝ) × (ℝ × ℝ) =>
      ∑ j, ∑ k, newtonD3 (q.1.1 - q.1.2 • embPlane q.2) i j k * sigmaM c ν χo M q.2 j k) := by
    refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_
    refine ((newtonD3_measurable i j k).comp ?_).mul
      ((sigmaM_measurable c ν hχo hM j k).comp measurable_snd)
    exact (measurable_fst.comp measurable_fst).sub
      ((measurable_snd.comp measurable_fst).smul (embPlane_measurable.comp measurable_snd))
  have hI : Measurable (fun p : Vec3 × ℝ => ∫ x' : ℝ × ℝ,
      ∑ j, ∑ k, newtonD3 (p.1 - p.2 • embPlane x') i j k * sigmaM c ν χo M x' j k) :=
    (hG.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (ℝ × ℝ)))).measurable
  have hF : Measurable (fun p : Vec3 × ℝ => p.2 ^ (2 * μ + 2) * ∫ x' : ℝ × ℝ,
      ∑ j, ∑ k, newtonD3 (p.1 - p.2 • embPlane x') i j k * sigmaM c ν χo M x' j k) :=
    ((measurable_snd.pow_const _).mul hI)
  exact (hF.stronglyMeasurable.integral_prod_right'
    (ν := (volume.restrict (Ioc (0 : ℝ) 1)))).measurable

theorem cylR_measurable : Measurable cylR := by unfold cylR; fun_prop

theorem rayPt_measurable : Measurable (fun q : Vec3 × ℝ => rayPt q.1 q.2) := by
  refine measurable_pi_lambda _ fun a => ?_
  have := cylR_measurable
  fin_cases a <;> simp [rayPt] <;> fun_prop

theorem streamPsi_measurable {Z : Vec3 → Vec3} (hZ : Measurable Z) :
    Measurable (streamPsi Z) := by
  unfold streamPsi
  refine Measurable.neg ?_
  have hset : MeasurableSet {q : Vec3 × ℝ | cylR q.1 < q.2} :=
    measurableSet_lt (cylR_measurable.comp measurable_fst) measurable_snd
  have hf : Measurable (fun q : Vec3 × ℝ => q.2 * Z (rayPt q.1 q.2) 2) :=
    measurable_snd.mul ((measurable_pi_apply 2).comp (hZ.comp rayPt_measurable))
  have hI := (hf.indicator hset).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ))
  have e : (fun y : Vec3 => ∫ ρ in Ioi (cylR y), ρ * Z (rayPt y ρ) 2) =
      fun y => ∫ ρ : ℝ, (Set.indicator {q : Vec3 × ℝ | cylR q.1 < q.2}
        (fun q : Vec3 × ℝ => q.2 * Z (rayPt q.1 q.2) 2)) (y, ρ) := by
    funext y
    rw [← integral_indicator measurableSet_Ioi]
    congr 1
  rw [e]
  exact hI.measurable

theorem chiYr_measurable (ν ε : ℝ) {χy : ℝ → ℝ} (hχy : Continuous χy) :
    Measurable (chiYr ν ε χy) := by
  unfold chiYr
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  exact hχy.measurable.comp (by fun_prop)

theorem streamCut_measurable (ν ε : ℝ) {χy : ℝ → ℝ} (hχy : Continuous χy) {Z : Vec3 → Vec3}
    (hZ : Measurable Z) : Measurable (streamCut ν ε χy Z) := by
  unfold streamCut
  have h1 := (chiYr_measurable ν ε hχy)
  have h2 : Measurable (deriv (chiYr ν ε χy)) := measurable_deriv _
  have hA : Measurable (fun y : Vec3 => chiYr ν ε χy (cylR y) • Z y) :=
    Measurable.smul (h1.comp cylR_measurable) hZ
  have hs : Measurable (fun y : Vec3 =>
      deriv (chiYr ν ε χy) (cylR y) / cylR y * streamPsi Z y) :=
    (((h2.comp cylR_measurable).div cylR_measurable).mul (streamPsi_measurable hZ))
  have hB : Measurable (fun y : Vec3 =>
      (deriv (chiYr ν ε χy) (cylR y) / cylR y * streamPsi Z y) • (![0, 0, 1] : Vec3)) :=
    Measurable.smul hs measurable_const
  exact hA.add hB

theorem youngW_measurable (c ν ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    {M : Chart → Mat3} (hM : Measurable M) : Measurable (youngW c ν ε μ χo M) := by
  unfold youngW
  have h1 : Measurable (fun y : Vec3 => ε • y) := Measurable.const_smul measurable_id ε
  have h2 := (newtonV_measurable c ν μ hχo hM).comp h1
  exact Measurable.const_smul h2 (ε ^ 2)

theorem xmt_measurable (c ν ε μ : ℝ) {χo χy : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    (hχy : IsStreamCutoff χy) {M : Chart → Mat3} (hM : Measurable M) :
    Measurable (Xmt c ν ε μ χo χy M) := by
  unfold Xmt
  exact streamCut_measurable ν ε hχy.smooth.continuous
    ((youngW_measurable c ν ε μ hχo hM).sub (youngW_measurable c ν ε (μ + 1) hχo hM))

/-- Measurability of the Newton field `X^mt` of a stress `T` (source 4776-4791, 5380-5382). -/
theorem xmtMeasAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ) :
    XmtMeasAt Pl K L μ := fun hχy T =>
  xmt_measurable _ _ _ _ K.hχo hχy (thinRep_measurable T)

end UnforcedLeray.Short.PartIIIb.Concrete
