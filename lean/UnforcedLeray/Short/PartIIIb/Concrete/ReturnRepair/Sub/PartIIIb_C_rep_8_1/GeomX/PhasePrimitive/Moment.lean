import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.Mean
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.ThinMoment
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.FarBridge
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.EarlyThinRepOrg
import UnforcedLeray.Short.PartIIIa.T11_OuterMoment
import UnforcedLeray.Short.PartIIIa.T03_PlaneRadialInv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.ZRegular

/-!
# Bridge (1), moment part: `N₁(F) ≤ π N` (helper for `GeomX.PhasePrimitive`)

Source `the November 2 reference manuscript`
lines 5400 (`N = N₁(χ_oT₁)`), 2683 (`|𝒩_TT| = s|T|`), SP 2747-2752, 2790-2795 (outer-coordinate
moment identity `∫(1+|Y|)‖F‖ dx'dY = π𝒩₁(T)`).

* `thinMoment_cutLift_le`: the first transverse moment of the cut planar lift is at most
  `π N₁(g)`;
* `firstMoment_thinG`: for the old thin source `g = thinG T`, `N₁(g) = oldN1 T` (the chart
  representative is `χ_o(νs) T₁` almost everywhere).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace PhasePrim

/-- The chart point of the planar point `(x', Y, q)` at unit scale. -/
theorem chartOf_one (c : ℝ) (x' : ℝ × ℝ) (Y q : ℝ) :
    NearInst.chartOf 1⁻¹ c (WithLp.toLp 2 ![x'.1, x'.2, Y])
        (2 * (q - Real.log (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2)))) =
      (plS x', (redQ c q, Y * Real.sqrt (plS x'))) := by
  rw [chartOf_eps 1 c one_pos]
  have h0 : (WithLp.toLp 2 ![x'.1, x'.2, Y] : Space) 0 = x'.1 := rfl
  have h1 : (WithLp.toLp 2 ![x'.1, x'.2, Y] : Space) 1 = x'.2 := rfl
  have h2 : (WithLp.toLp 2 ![x'.1, x'.2, Y] : Space) 2 = Y := rfl
  rw [h0, h1, h2]
  simp only [one_mul, inv_one]
  have hq : Real.log (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2)) +
      2 * (q - Real.log (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))) / 2 = q := by ring
  rw [show (2 : ℝ) * 1 = 2 by norm_num, hq]

/-- `|F(x',Y,q)| ≤ s |g(s, redQ q, η)|` (source 2683). -/
theorem tensorNorm_cutLift_le (c ρo : ℝ) (g : Chart → Ten3) (x' : ℝ × ℝ) (Y q : ℝ) :
    IIIa.tensorNorm (cutLift c ρo g x' Y q) ≤
      plS x' * ‖g (plS x', (redQ c q, Y * Real.sqrt (plS x')))‖ := by
  rw [cutLift_eq_one]
  unfold oldCutSrc
  split_ifs
  · have h := cartLiftFrobBound 1⁻¹ c g (2 * (q - Real.log (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))))
      (WithLp.toLp 2 ![x'.1, x'.2, Y])
    rw [chartOf_one] at h
    exact h
  · have h0 : IIIa.tensorNorm (0 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
      simp [IIIa.tensorNorm]
    rw [h0]
    have : 0 ≤ plS x' := by unfold plS; positivity
    positivity

/-- **The moment of the cut lift** (SP 2790-2795): `N₁(F) ≤ π 𝒩₁(g)`. -/
theorem thinMoment_cutLift_le (c ρo : ℝ) (hc : 0 < c) (g : Chart → Ten3) (hg : Measurable g) :
    IIIa.thinMoment c (cutLift c ρo g) ≤
      ENNReal.ofReal Real.pi * IIIa.firstMoment c 0 (fun p => Ten3.toMatrix (g p)) := by
  have hT : ∀ a b, Measurable fun p => (fun p => Ten3.toMatrix (g p)) p a b := fun a b =>
    (EuclideanSpace.proj (a, b) : Ten3 →L[ℝ] ℝ).continuous.measurable.comp hg
  rw [← IIIa.outerMoment_of_parts IIIa.planeRadialInv c hc _ hT]
  unfold IIIa.thinMoment
  rw [Measure.volume_eq_prod]
  refine le_trans (lintegral_prod_le _) ?_
  refine lintegral_mono fun x' => lintegral_mono fun Y => ?_
  dsimp only
  refine mul_le_mul_right (ENNReal.rpow_le_rpow ?_ (by norm_num)) _
  set H : ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal c⁻¹ * ENNReal.ofReal ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ^ 2 *
        IIIa.frobSq (Ten3.toMatrix (g ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹,
          (q, Y * Real.sqrt ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)))))) with hH
  have hpt : ∀ q, ENNReal.ofReal c⁻¹ *
      ENNReal.ofReal (IIIa.tensorNorm (cutLift c ρo g x' Y q) ^ 2) ≤ H (redQ c q) := by
    intro q
    rw [hH]
    dsimp only
    gcongr
    rw [tm_frobSq_toMatrix]
    have h1 := tensorNorm_cutLift_le c ρo g x' Y q
    have h0 : 0 ≤ IIIa.tensorNorm (cutLift c ρo g x' Y q) := Real.sqrt_nonneg _
    have h2 := pow_le_pow_left₀ h0 h1 2
    unfold plS at h2
    nlinarith [h2]
  have e := lintegral_redQ c hc H
  rw [neg_div] at e
  exact le_trans (lintegral_mono hpt) (le_of_eq e)

/-- The cut of a scalar acts on `toMatrix` entrywise. -/
theorem toMatrix_smul (a : ℝ) (x : Ten3) : Ten3.toMatrix (a • x) = a • Ten3.toMatrix x := by
  ext i j
  simp [Ten3.toMatrix]

theorem ageμ_slice (c : ℝ) (hc : 0 < c) (S : Set Chart) (hS : MeasurableSet S)
    (hae : ∀ᵐ p ∂(ageμ c (-1 / 2)), p ∈ S) :
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ η ∂(volume : Measure ℝ),
      ∀ᵐ q ∂(volume.restrict (Ico (-(c / 2)) (c / 2))), (s, (q, η)) ∈ S := by
  unfold ageμ at hae
  have : SFinite (Cyl.avgμ c) := by
    unfold Cyl.avgμ
    infer_instance
  have h1 := Measure.ae_ae_of_ae_prod hae
  have hac : volume.restrict (Ioi (0 : ℝ)) ≪
      (volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) := by
    refine withDensity_absolutelyContinuous' (measurable_ofReal_rpow _).aemeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have : 0 < s ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
    simpa using this
  filter_upwards [hac.ae_le h1] with s hs
  have hc' : ENNReal.ofReal c⁻¹ ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact inv_pos.2 hc
  have hs2 := hs
  unfold Cyl.avgμ at hs2
  rw [Cyl.cellμ_eq_prod, neg_div] at hs2
  have hs3 := (Measure.absolutelyContinuous_smul hc').ae_le hs2
  have hq := Measure.ae_ae_of_ae_prod hs3
  have hset : MeasurableSet {x : ℝ × ℝ | (s, (x.1, x.2)) ∈ S} :=
    hS.preimage (measurable_const.prodMk measurable_id)
  exact (Measure.ae_ae_comm (μ := volume.restrict (Ico (-(c / 2)) (c / 2)))
    (ν := (volume : Measure ℝ)) (p := fun a b => (s, (a, b)) ∈ S) hset).1 hq

/-- `firstMoment` sees only the `ageμ`-class of the tensor. -/
theorem firstMoment_congr (c : ℝ) (hc : 0 < c) (T₁ T₂ : Chart → Matrix (Fin 3) (Fin 3) ℝ)
    (h : ∀ᵐ p ∂(ageμ c (-1 / 2)), T₁ p = T₂ p) :
    IIIa.firstMoment c 0 T₁ = IIIa.firstMoment c 0 T₂ := by
  obtain ⟨S, hS, hSsub, hSae⟩ := tm_ae_measurable h
  have hslice := ageμ_slice c hc S hS hSae
  rw [tm_firstMoment_eq, tm_firstMoment_eq]
  apply lintegral_congr_ae
  filter_upwards [hslice] with s hs
  apply tmInt_congr
  filter_upwards [hs] with η hη
  filter_upwards [hη] with q hq
  exact hSsub _ hq

/-- **`N₁` of the old thin source** (source 5400): `𝒩₁(thinG T) = oldN1 T`. -/
theorem firstMoment_thinG (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (hC0 : 0 < K.C0) (T : LStr Pl K L) :
    IIIa.firstMoment (cOf L.ν) 0 (fun p => Ten3.toMatrix (thinG Pl K L T p)) = oldN1 Pl K L T := by
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  have hρ : 0 < L.ρb Pl K := ZRegAux.rho_b_pos' Pl K L hC0
  set Tc := chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo T with hTc
  have hGdef : thinG Pl K L T = strSum (thinPart Tc) := by
    show strSum (chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (thinPart T)) = _
    rw [ftk_chiO_thinPart K.hχo T]
  have h1 := FarBridge.strSum_thinPart hρ Tc
  have hc1 : ((Tc.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν)) :
      Chart → Ten3) =ᵐ[gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν]
      cutFun K.χo L.ν • ((T.fst : Lp (α := Chart) Ten3 2
        (gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν)) : Chart → Ten3) :=
    NearInst.mulBdd_apply_ae (cutFun K.χo L.ν) (cutFun_measurable K.hχo L.ν) 1
      (cutFun_bound K.hχo L.ν) T.fst
  rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at hc1
  apply firstMoment_congr (cOf L.ν) hc
  filter_upwards [h1, hc1] with p hp1 hp2
  rw [hGdef, hp1, hp2]
  show Ten3.toMatrix (cutFun K.χo L.ν p • (T.fst : Chart → Ten3) p) = _
  rw [toMatrix_smul]
  rfl

end PhasePrim

end UnforcedLeray.Short.PartIIIb.Concrete
