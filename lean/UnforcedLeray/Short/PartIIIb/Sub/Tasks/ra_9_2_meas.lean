import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp.RawSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.HpAC2

/-!
# `PartIII-b:C/asrc/ra/9/2` : reduction of `GeoConvMeas` to regularity and support leaves

Source of record: `the November 2 reference manuscript` (5040-5044, 2076-2077).

`GeoConvMeas as χf` is `GeoPieceMeas` for `geoConvPiece`. Its two halves reduce to:
* continuity of the chart coefficient `geoConvPiece p μ χf A` on `posU` (gives a.e. strong
  measurability on `srcMeasure` and on the cell sections, through `aestronglyMeasurable_of_continuousOn_pos`);
* support: `geoConvPiece p μ χf A (s, x) = 0` for `11/10 < p.ν * s`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The reduction of `GeoConvMeas` to a continuity leaf on `posU` and a support leaf. -/
theorem ConvMeas_of (as : ℝ) (χf : ℝ → ℝ)
    (hC : IsSourceCutoffC χf → ∀ (p : Params) (μ : ℝ) (A : ℝ → Mat3), IsAffElem as A →
      ContinuousOn (geoConvPiece p μ χf A) posU)
    (hS : IsSourceCutoffC χf → ∀ (p : Params) (μ : ℝ) (A : ℝ → Mat3), IsAffElem as A →
      ∀ s : ℝ, 11 / 10 < p.ν * s → ∀ x : ℝ × ℝ, geoConvPiece p μ χf A (s, x) = 0) :
    GeoConvMeas as χf := by
  unfold GeoConvMeas GeoPieceMeas
  intro hχ K hK hKs dm dp hdm
  refine ⟨1, one_pos, fun p d hreg hν μ hμ A hA => ⟨?_, ?_, ?_⟩⟩
  · exact aestronglyMeasurable_of_continuousOn_pos (hC hχ p μ A hA)
  · intro s hs x
    have hpos : 0 < p.ν := p.ν_pos
    have h2 : 11 / 10 < p.ν * s := by
      rw [mul_comm]
      exact (div_lt_iff₀ hpos).1 hs
    exact hS hχ p μ A hA s h2 x
  · intro s hs
    have hcont : ContinuousOn (fun x : ℝ × ℝ => geoConvPiece p μ χf A (s, x)) univ := by
      refine (hC hχ p μ A hA).comp (continuous_const.prodMk continuous_id).continuousOn ?_
      intro x _
      exact mem_posU.2 hs
    have h := hcont.aestronglyMeasurable (μ := UnforcedLeray.Cyl.avgμ p.c) MeasurableSet.univ
    rwa [Measure.restrict_univ] at h

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem conv_contMer : Continuous (fun v : Space => (!₂[v 0, v 2] : Merid)) := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp (continuous_pi fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

theorem conv_physDivSym_congr {a a' b b' : Space → Space} {y : Space}
    (ha : a =ᶠ[nhds y] a') (hb : b =ᶠ[nhds y] b') :
    physDivSym a b y = physDivSym a' b' y := by
  unfold physDivSym
  congr 1
  funext i
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hf : (fun z => a z j * b z i + b z j * a z i) =ᶠ[nhds y]
      (fun z => a' z j * b' z i + b' z j * a' z i) := by
    filter_upwards [ha, hb] with z hz1 hz2
    simp only [hz1, hz2]
  rw [hf.fderiv_eq]

theorem conv_physDivSym_zero (a : Space → Space) (y : Space) :
    physDivSym a (fun _ => (0 : Space)) y = 0 := by
  unfold physDivSym
  have : (fun (i : Fin 3) => ∑ j : Fin 3, fderiv ℝ (fun y' => a y' j * (0 : Space) i +
      (0 : Space) j * a y' i) y (coordinateVector j)) = fun _ => 0 := by
    funext i
    simp
  simp only [PiLp.zero_apply, mul_zero, zero_mul, add_zero, fderiv_fun_const]
  ext i
  simp

/-- First term of `geoConvPiece` is continuous on `posU`. -/
theorem conv_term1_cont (p : Params) (d dm dp : ℝ) (hreg : UnforcedLeray.Short.IIb.BgRegime p d dm dp)
    (H : ℝ → Space → Space) (hH : ContDiff ℝ 1 (fun x : ℝ × Space => H x.1 x.2)) :
    ContinuousOn (coefOf p.ε⁻¹ (fun τ y => physDivSym (p.raw τ) (H τ) y)) posU := by
  have hR : 0 < p.ε⁻¹ := inv_pos.2 p.ε_pos
  set W : Set (ℝ × Space) := {x : ℝ × Space | x.2 ∉ axis} with hW
  have hWo : IsOpen W := isOpen_compl_axis.preimage continuous_snd
  have hψ3 : ContDiffOn ℝ 3 (fun x : ℝ × UnforcedLeray.Cyl.Plane => p.train.ψ x.1 x.2)
      (Ioi 0 ×ˢ univ) := hreg.train_stream_smooth.of_le (WithTop.coe_le_coe.2 (le_top : (3 : ℕ∞) ≤ ⊤))
  have hraw := PwSplitRaw.rawProfile_contDiffOn (ε := p.ε) p.train.isTrain hψ3
  have hU : ContDiffOn ℝ 1 (fun x : ℝ × Space =>
      Nv p.ε⁻¹ (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) x.1 x.2) W :=
    contDiffOn_Nv_offAxis hR 1 (hraw.of_le (by norm_num))
  set U : ℝ × Space → Space := fun x =>
    Nv p.ε⁻¹ (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) x.1 x.2 with hUdef
  set V : ℝ × Space → Space := fun x => H x.1 x.2 with hVdef
  set G : Fin 3 → Fin 3 → ℝ × Space → ℝ := fun i j x => U x j * V x i + V x j * U x i with hGdef
  have hG : ∀ i j, ContDiffOn ℝ 1 (G i j) W := by
    intro i j
    have hUc : ∀ k : Fin 3, ContDiffOn ℝ 1 (fun x => U x k) W := fun k =>
      ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn hU)
    have hVc : ∀ k : Fin 3, ContDiffOn ℝ 1 (fun x => V x k) W := fun k =>
      ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn hH.contDiffOn)
    exact ((hUc j).mul (hVc i)).add ((hVc j).mul (hUc i))
  set F : ℝ × Space → Space := fun x => WithLp.toLp 2 fun i => ∑ j : Fin 3,
    fderiv ℝ (G i j) x (0, coordinateVector j) with hFdef
  have hFc : ContinuousOn F W := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp_continuousOn
      (continuousOn_pi.2 fun i => continuousOn_finsetSum _ fun j _ => ?_)
    exact ((hG i j).continuousOn_fderiv_of_isOpen hWo le_rfl).clm_apply continuousOn_const
  have hFeq : ∀ x ∈ W, physDivSym (p.raw x.1) (H x.1) x.2 = F x := by
    intro x hx
    have hxa : x.2 ∉ axis := hx
    have hev : p.raw x.1 =ᶠ[𝓝 x.2] (fun y => Nv p.ε⁻¹
        (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) x.1 y) := by
      filter_upwards [isOpen_compl_axis.mem_nhds hxa] with y hy
      exact p.raw_eq_off_axis x.1 y hy
    rw [conv_physDivSym_congr hev (Filter.EventuallyEq.refl _ (H x.1))]
    unfold physDivSym
    simp only [hFdef]
    congr 1
    funext i
    refine Finset.sum_congr rfl fun j _ => ?_
    have hd : DifferentiableAt ℝ (G i j) (x.1, x.2) :=
      ((hG i j).differentiableOn one_ne_zero).differentiableAt (hWo.mem_nhds hx)
    have := congrArg (fun L => L (coordinateVector j))
      (UnforcedLeray.B0005.fderiv_slice_space hd)
    simpa using this
  -- the chart map
  set Φ : Chart → ℝ × Space := fun q => (NearInst.chartTau p.ε⁻¹ q, NearInst.chartY p.ε⁻¹ q) with hΦ
  have hsq : ∀ q ∈ posU, Real.sqrt q.1 ≠ 0 := fun q hq => (Real.sqrt_pos.2 (mem_posU.1 hq)).ne'
  have hΦc : ContinuousOn Φ posU := by
    refine ContinuousOn.prodMk ?_ ?_
    · unfold NearInst.chartTau
      refine ContinuousOn.add ?_ ?_
      · exact ((continuousOn_const.mul (continuous_fst.comp continuous_snd).continuousOn).div_const _)
      · exact Real.continuousOn_log.comp continuousOn_fst
          (fun q hq => (mem_posU.1 hq).ne')
    · unfold NearInst.chartY
      refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp_continuousOn
        (continuousOn_pi.2 fun i => ?_)
      have hs : ContinuousOn (fun q : Chart => Real.sqrt q.1) posU :=
        Real.continuous_sqrt.comp_continuousOn continuousOn_fst
      fin_cases i
      · exact continuousOn_const.div hs hsq
      · exact continuousOn_const
      · exact (continuous_snd.comp continuous_snd).continuousOn.div hs hsq
  have hΦW : MapsTo Φ posU W := by
    intro q hq
    have hs := mem_posU.1 hq
    show NearInst.chartY p.ε⁻¹ q ∉ axis
    intro h
    have h0 : (NearInst.chartY p.ε⁻¹ q) 0 = 0 := h.1
    have : p.ε⁻¹ / Real.sqrt q.1 = 0 := by simpa [NearInst.chartY] using h0
    have hp : 0 < p.ε⁻¹ / Real.sqrt q.1 := div_pos hR (Real.sqrt_pos.2 hs)
    linarith
  have hFΦ : ContinuousOn (fun q => F (Φ q)) posU := hFc.comp hΦc hΦW
  have hmain : ContinuousOn (fun q : Chart => (Real.sqrt q.1)⁻¹ • (!₂[F (Φ q) 0, F (Φ q) 2] : Merid)) posU := by
    have h1 : ContinuousOn (fun q : Chart => (Real.sqrt q.1)⁻¹) posU :=
      (Real.continuous_sqrt.comp_continuousOn continuousOn_fst).inv₀ hsq
    exact h1.smul (conv_contMer.comp_continuousOn hFΦ)
  refine hmain.congr fun q hq => ?_
  unfold coefOf
  have := hFeq (Φ q) (hΦW hq)
  simp only [hΦ] at this
  simp only [hΦ]
  rw [this]

/-- Second term of `geoConvPiece` is continuous on `posU`. -/
theorem conv_term2_cont (p : Params) (χf : ℝ → ℝ)
    (A : ℝ → Mat3)
    (h1 : ContDiffOn ℝ 2 (fun q : Chart => hpA p.ν χf A q.1 q.2) posU) :
    ContinuousOn (fun q : Chart => q.1 • toMer (fderiv ℝ (hpA p.ν χf A q.1) q.2
      (trainPl p.train q.1 q.2) + fderiv ℝ (trainPl p.train q.1) q.2 (hpA p.ν χf A q.1 q.2))) posU := by
  set H : Chart → ℝ × ℝ := fun q => hpA p.ν χf A q.1 q.2 with hHdef
  set T : Chart → ℝ × ℝ := fun q => trainPl p.train q.1 q.2 with hTdef
  have hU := isOpen_posU
  have hD : ContDiffOn ℝ 1 (fderiv ℝ H) posU := h1.fderiv_of_isOpen hU (by norm_num)
  have hDc : ContinuousOn (fderiv ℝ H) posU := hD.continuousOn
  have hdiff : ∀ q ∈ posU, DifferentiableAt ℝ H q := fun q hq =>
    (h1.contDiffAt (hU.mem_nhds hq)).differentiableAt (by norm_num)
  have hT1 := trainPl_contDiffOn p.train
  have hTc : ContinuousOn T posU := hT1.continuousOn
  have hTdiff : ∀ q ∈ posU, DifferentiableAt ℝ T q := fun q hq =>
    (hT1.contDiffAt (hU.mem_nhds hq)).differentiableAt (by norm_num)
  have hDT : ContinuousOn (fderiv ℝ T) posU := hT1.continuousOn_fderiv_of_isOpen hU le_rfl
  have hHc : ContinuousOn H posU := h1.continuousOn
  have a4 : ContinuousOn (fun q : Chart => fderiv ℝ H q (0, T q)) posU :=
    hDc.clm_apply (continuousOn_const.prodMk hTc)
  have a5 : ContinuousOn (fun q : Chart => fderiv ℝ T q (0, H q)) posU :=
    hDT.clm_apply (continuousOn_const.prodMk hHc)
  have hin := a4.add a5
  have : ContinuousOn (fun q : Chart => q.1 • toMer (fderiv ℝ H q (0, T q) + fderiv ℝ T q (0, H q))) posU :=
    continuousOn_fst.smul (continuous_toMer.comp_continuousOn hin)
  refine this.congr fun q hq => ?_
  have e4 : fderiv ℝ (hpA p.ν χf A q.1) q.2 (trainPl p.train q.1 q.2) = fderiv ℝ H q (0, T q) :=
    fderiv_slice (H := H) (s := q.1) (x := q.2) (hdiff q hq) _
  have e5 : fderiv ℝ (trainPl p.train q.1) q.2 (hpA p.ν χf A q.1 q.2) = fderiv ℝ T q (0, H q) :=
    fderiv_slice (H := T) (s := q.1) (x := q.2) (hTdiff q hq) _
  simp only [hHdef, hTdef] at e4 e5 ⊢
  rw [e4, e5]

/-- **Lemma 1** (measurability and support of the convection piece), unconditional form. -/
theorem ConvMeas_proof (as : ℝ) (χf : ℝ → ℝ) : GeoConvMeas as χf := by
  have h1 := affineLiftReg as χf
  have h2 := hpAC2 as χf
  unfold GeoConvMeas GeoPieceMeas
  intro hχ K hK hKs dm dp hdm
  refine ⟨1, one_pos, fun p d hreg hν μ hμ A hA => ?_⟩
  have hc : p.c = cOf p.ν := hreg.c_eq
  have hν0 : 0 < p.ν := p.ν_pos
  have hε0 : 0 < p.ε := p.ε_pos
  have hLC : ContDiff ℝ 2 (fun x : ℝ × Space => hLift p.ν p.ε p.c χf A x.1 x.2) := by
    rw [hc]; exact (h1 hχ p.ν μ p.ε hν0 hε0 A hA).1
  have hH : ContDiffOn ℝ 2 (fun q : Chart => hpA p.ν χf A q.1 q.2) posU := h2 hχ p.ν hν0 A hA
  have hC : ContinuousOn (geoConvPiece p μ χf A) posU := by
    unfold geoConvPiece
    exact (conv_term1_cont p d dm dp hreg _ (hLC.of_le (by norm_num))).sub
      (conv_term2_cont p χf A hH)
  have hS : ∀ s : ℝ, 11 / 10 < p.ν * s → ∀ x : ℝ × ℝ, geoConvPiece p μ χf A (s, x) = 0 := by
    intro s hs x
    have hs' : (11 / 10) / p.ν < s := by
      rw [div_lt_iff₀ hν0, mul_comm]; exact hs
    have hs0 : 0 < s := lt_trans (by positivity) hs'
    have hage : (11 / 10) / p.ν < age p.ε⁻¹ (NearInst.chartY p.ε⁻¹ (s, x)) := by
      rw [age_chartY_ra _ _ (inv_pos.2 hε0) hs0]; exact hs'
    set y := NearInst.chartY p.ε⁻¹ (s, x) with hy
    have hϱ : ϱ y ^ 2 ≠ 0 := by
      intro h0
      unfold age at hage
      rw [h0, div_zero] at hage
      have : 0 < (11 / 10) / p.ν := by positivity
      linarith
    have hcont : ContinuousAt (fun y' : Space => age p.ε⁻¹ y') y := by
      unfold age
      have : Continuous fun y' : Space => ϱ y' := by unfold ϱ; fun_prop
      exact continuousAt_const.div ((this.pow 2).continuousAt) hϱ
    have hev : ∀ᶠ y' in 𝓝 y, (11 / 10) / p.ν < age p.ε⁻¹ y' := hcont.eventually (lt_mem_nhds hage)
    have hloc : ∀ t, hLift p.ν p.ε p.c χf A t =ᶠ[𝓝 y] (fun _ => (0 : Space)) := fun t => by
      filter_upwards [hev] with y' hy'
      exact hLift_eq_zero_of_age p.ν p.ε p.c χf hχ hν0 A t y' hy'
    have hz : physDivSym (p.raw (NearInst.chartTau p.ε⁻¹ (s, x))) (hLift p.ν p.ε p.c χf A
        (NearInst.chartTau p.ε⁻¹ (s, x))) y = 0 := by
      rw [conv_physDivSym_congr (Filter.EventuallyEq.refl _ _)
        (hloc (NearInst.chartTau p.ε⁻¹ (s, x)))]
      exact conv_physDivSym_zero _ _
    have h1z : coefOf p.ε⁻¹ (fun τ y => physDivSym (p.raw τ) (hLift p.ν p.ε p.c χf A τ) y) (s, x)
        = 0 := by
      unfold coefOf
      simp only [← hy]
      rw [hz]
      have : (!₂[(0 : Space) 0, (0 : Space) 2] : Merid) = 0 := by
        ext i; fin_cases i <;> rfl
      rw [this, smul_zero]
    have hAy : ∀ s' : ℝ, (11 / 10) / p.ν < s' → ∀ x' : ℝ × ℝ, hpA p.ν χf A s' x' = 0 :=
      fun s' hs' x' => hAc_hpA_zero p.ν χf A s' x' (hAc_ay_zero χf hχ p.ν hν0 A s' hs')
    have hfun : hpA p.ν χf A s = fun _ => (0 : ℝ × ℝ) := funext fun x' => hAy s hs' x'
    have h2z : (s • toMer (fderiv ℝ (hpA p.ν χf A s) x (trainPl p.train s x) +
        fderiv ℝ (trainPl p.train s) x (hpA p.ν χf A s x))) = 0 := by
      rw [hfun]
      simp [show toMer 0 = 0 by ext i; fin_cases i <;> rfl]
    unfold geoConvPiece
    simp only [Pi.sub_apply]
    rw [h1z, h2z, sub_zero]
  refine ⟨aestronglyMeasurable_of_continuousOn_pos hC, fun s hs x => ?_, ?_⟩
  · have h2 : 11 / 10 < p.ν * s := by
      rw [mul_comm]
      exact (div_lt_iff₀ hν0).1 hs
    exact hS s h2 x
  · intro s hs
    have hcont : ContinuousOn (fun x : ℝ × ℝ => geoConvPiece p μ χf A (s, x)) univ := by
      refine hC.comp (continuous_const.prodMk continuous_id).continuousOn ?_
      intro x _
      exact mem_posU.2 hs
    have h := hcont.aestronglyMeasurable (μ := UnforcedLeray.Cyl.avgμ p.c) MeasurableSet.univ
    rwa [Measure.restrict_univ] at h

end UnforcedLeray.Short.PartIIIb.Concrete
