import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.IBPContC
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_9
import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.Reg
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.Defs
import UnforcedLeray.Short.PartIIIa.Compose

/-!
# `PartIII-b:C/asrc/ra/9/1/1` : `GeoDMeas` from `AffineLiftReg` and `HpAC2`

Source of record: `the November 2 reference manuscript`
lines 5034-5039, 4979-4980.

`geoDPiece = coefOf ε⁻¹ (D_μ ĥ_A) - s·toMer(...)`.  The first term is continuous because the
physical lift `ĥ_A` is `C²` (`AffineLiftReg`, task `PartIII-b:C/asrc/ra/5`); it vanishes for
`s > 1.1/ν` by locality (`hLift` vanishes on the open set `age > 1.1/ν`).  The second term is
continuous on `{s > 0}` because `h^p_A` is `C²` there (`HpAC2`, task `PartIII-b:C/asrc/ra/5/5`) and
vanishes for `s > 1.1/ν` because `A^y = 0` there.  Proved here: `DMeas_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

/-! ## 1. Calculus on the half chart -/

theorem dmeas_slice_y {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Chart → F)
    (s : ℝ) (x v : ℝ × ℝ) (hf : DifferentiableAt ℝ f (s, x)) :
    fderiv ℝ (fun y => f (s, y)) x v = fderiv ℝ f (s, x) (0, v) := by
  have hg : HasFDerivAt (fun y : ℝ × ℝ => ((s, y) : Chart))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) x :=
    (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x)
  have hc := hf.hasFDerivAt.comp x hg
  have he : (fun y => f (s, y)) = f ∘ (fun y : ℝ × ℝ => ((s, y) : Chart)) := rfl
  rw [he, hc.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]

theorem dmeas_deriv_s {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Chart → F)
    (s : ℝ) (x : ℝ × ℝ) (hf : DifferentiableAt ℝ f (s, x)) :
    deriv (fun s' => f (s', x)) s = fderiv ℝ f (s, x) (1, 0) := by
  have hg : HasDerivAt (fun s' : ℝ => ((s', x) : Chart)) ((1 : ℝ), (0 : ℝ × ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  exact (hf.hasFDerivAt.comp_hasDerivAt s hg).deriv

theorem dmeas_isOpen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
  isOpen_Ioi.prod isOpen_univ

theorem dmeas_diffAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {H : Chart → F}
    (hH : ContDiffOn ℝ 2 H (Ioi (0 : ℝ) ×ˢ univ)) {q : Chart} (hq : q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :
    DifferentiableAt ℝ H q :=
  (hH.differentiableOn (by norm_num)).differentiableAt (dmeas_isOpen.mem_nhds hq)

theorem dmeas_C1 (H : Chart → ℝ × ℝ) (hH : ContDiffOn ℝ 2 H (Ioi (0 : ℝ) ×ˢ univ)) :
    ContinuousOn (fun q : Chart => deriv (fun s' => H (s', q.2)) q.1)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  have hd : ContinuousOn (fun q : Chart => fderiv ℝ H q) (Ioi (0 : ℝ) ×ˢ univ) :=
    hH.continuousOn_fderiv_of_isOpen dmeas_isOpen (by norm_num)
  refine (hd.clm_apply (continuousOn_const (c := ((1 : ℝ), (0 : ℝ × ℝ))))).congr (fun q hq => ?_)
  exact dmeas_deriv_s H q.1 q.2 (dmeas_diffAt hH hq)

theorem dmeas_C2 (H : Chart → ℝ × ℝ) (hH : ContDiffOn ℝ 2 H (Ioi (0 : ℝ) ×ˢ univ)) :
    ContinuousOn (fun q : Chart => lapPl (fun x => H (q.1, x)) q.2) (Ioi (0 : ℝ) ×ˢ univ) := by
  have hD2 : ContDiffOn ℝ 1 (fun q : Chart => fderiv ℝ H q) (Ioi (0 : ℝ) ×ˢ univ) :=
    hH.fderiv_of_isOpen dmeas_isOpen (by norm_num)
  have hG : ∀ a : Fin 2, ContDiffOn ℝ 1 (fun q : Chart => fderiv ℝ H q (0, ei a))
      (Ioi (0 : ℝ) ×ˢ univ) := fun a => hD2.clm_apply contDiffOn_const
  have hGd : ∀ a : Fin 2, ContinuousOn
      (fun q : Chart => fderiv ℝ (fun q' : Chart => fderiv ℝ H q' (0, ei a)) q)
      (Ioi (0 : ℝ) ×ˢ univ) := fun a =>
    (hG a).continuousOn_fderiv_of_isOpen dmeas_isOpen le_rfl
  have hsum : ContinuousOn (fun q : Chart => ∑ a : Fin 2,
      fderiv ℝ (fun q' : Chart => fderiv ℝ H q' (0, ei a)) q (0, ei a)) (Ioi (0 : ℝ) ×ˢ univ) :=
    continuousOn_finsetSum _ fun a _ => (hGd a).clm_apply continuousOn_const
  refine hsum.congr (fun q hq => ?_)
  unfold lapPl
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hin : (fun y => fderiv ℝ (fun x => H (q.1, x)) y (ei a)) =
      fun y => fderiv ℝ H (q.1, y) (0, ei a) := by
    funext y
    exact dmeas_slice_y H q.1 y (ei a)
      (dmeas_diffAt hH (show (q.1, y) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) from ⟨hq.1, trivial⟩))
  rw [hin]
  have := dmeas_slice_y (fun q' : Chart => fderiv ℝ H q' (0, ei a)) q.1 q.2 (ei a)
    (((hG a).differentiableOn (by norm_num)).differentiableAt (dmeas_isOpen.mem_nhds hq))
  exact this

theorem continuous_toMer : Continuous toMer := by
  unfold toMer
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp (continuous_pi fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

/-- The second term of `geoDPiece` is continuous on `{s > 0}` when `h^p_A` is `C²` there. -/
theorem dmeas_second_cont (ν μ : ℝ) (H : Chart → ℝ × ℝ)
    (hH : ContDiffOn ℝ 2 H (Ioi (0 : ℝ) ×ˢ univ)) :
    ContinuousOn (fun q : Chart => q.1 • toMer (deriv (fun s' => H (s', q.2)) q.1 +
      (μ / q.1) • H q - ν • lapPl (fun x => H (q.1, x)) q.2)) (Ioi (0 : ℝ) ×ˢ univ) := by
  have hq0 : ∀ q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)), q.1 ≠ 0 := fun q hq => (ne_of_gt hq.1)
  have hfst : ContinuousOn (fun q : Chart => q.1) (Ioi (0 : ℝ) ×ˢ univ) := continuousOn_fst
  have hdiv : ContinuousOn (fun q : Chart => μ / q.1) (Ioi (0 : ℝ) ×ˢ univ) :=
    continuousOn_const.div hfst hq0
  have hin : ContinuousOn (fun q : Chart => deriv (fun s' => H (s', q.2)) q.1 +
      (μ / q.1) • H q - ν • lapPl (fun x => H (q.1, x)) q.2) (Ioi (0 : ℝ) ×ˢ univ) :=
    ((dmeas_C1 H hH).add (hdiv.smul hH.continuousOn)).sub ((dmeas_C2 H hH).const_smul ν)
  exact hfst.smul (continuous_toMer.comp_continuousOn hin)

/-! ## 2. Locality of the lift -/

theorem age_chartY_ra (R s : ℝ) (hR : 0 < R) (hs : 0 < s) (x : ℝ × ℝ) :
    age R (NearInst.chartY R (s, x)) = s := by
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hsp : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hϱ : ϱ (NearInst.chartY R (s, x)) = R / Real.sqrt s := by
    unfold ϱ NearInst.chartY
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (R / Real.sqrt s) ^ 2 + (0:ℝ) ^ 2 = (R / Real.sqrt s) ^ 2 by ring]
    exact Real.sqrt_sq (div_nonneg hR.le hsp.le)
  unfold age
  rw [hϱ, div_pow, hsq]
  field_simp

theorem hLift_eq_zero_of_age (ν ε c : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (hν : 0 < ν)
    (A : ℝ → Mat3) (τ : ℝ) (y : Space) (h : (11 / 10) / ν < age ε⁻¹ y) :
    hLift ν ε c χf A τ y = 0 := by
  unfold hLift Nv
  have h0 : perExt c (hAcoef ν ε χf A) (chart ε⁻¹ τ y) = 0 := by
    show hAcoef ν ε χf A (age ε⁻¹ y, (cellRep c (phase ε⁻¹ τ y), trans ε⁻¹ y)) = 0
    exact hAcSupport χf hχ ν ε hν A _ h _
  rw [h0, map_zero, smul_zero]

theorem physDmu_hLift_zero (ν ε c μ : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (hν : 0 < ν)
    (A : ℝ → Mat3) (τ : ℝ) (y : Space) (h : (11 / 10) / ν < age ε⁻¹ y) :
    physDmu ν μ (hLift ν ε c χf A) τ y = 0 := by
  have hthr : 0 < (11 / 10) / ν := by positivity
  have hϱ : ϱ y ^ 2 ≠ 0 := by
    intro h0
    unfold age at h
    rw [h0, div_zero] at h
    linarith
  have hcont : ContinuousAt (fun y' : Space => age ε⁻¹ y') y := by
    unfold age
    have : Continuous fun y' : Space => ϱ y' := by unfold ϱ; fun_prop
    exact continuousAt_const.div ((this.pow 2).continuousAt) hϱ
  have hev : ∀ᶠ y' in 𝓝 y, (11 / 10) / ν < age ε⁻¹ y' := hcont.eventually (lt_mem_nhds h)
  have hloc : ∀ t, hLift ν ε c χf A t =ᶠ[𝓝 y] (fun _ => (0 : Space)) := fun t => by
    filter_upwards [hev] with y' hy'
    exact hLift_eq_zero_of_age ν ε c χf hχ hν A t y' hy'
  have h1 := physDmu_congr_nhds (ν := ν) (μ := μ) (X₁ := hLift ν ε c χf A)
    (X₂ := fun _ _ => (0 : Space)) (y := y) hloc τ
  rw [h1]
  have hl : physLap (fun _ : Space => (0 : Space)) y = 0 := physLap_zero_fun y
  unfold physDmu
  rw [hl]
  simp

/-! ## 3. The theorem -/

theorem DMeas_of (as : ℝ) (χf : ℝ → ℝ) (h1 : AffineLiftReg as χf) (h2 : HpAC2 as χf) :
    GeoDMeas as χf := by
  intro hχ K hK hKs dm dp hdm
  refine ⟨1, one_pos, fun p d hreg hν μ hμ A hA => ?_⟩
  have hc : p.c = cOf p.ν := hreg.c_eq
  have hν0 : 0 < p.ν := p.ν_pos
  have hε0 : 0 < p.ε := p.ε_pos
  have hF1 : Continuous (fun x : ℝ × Space => physDmu p.ν μ (hLift p.ν p.ε p.c χf A) x.1 x.2) := by
    rw [hc]
    exact ibpcC_dmu_cont (Ψ := fun x : ℝ × Space => hLift p.ν p.ε (cOf p.ν) χf A x.1 x.2)
      (h1 hχ p.ν μ p.ε hν0 hε0 A hA).1
  have hg1 : Measurable (coefOf p.ε⁻¹ (physDmu p.ν μ (hLift p.ν p.ε p.c χf A))) :=
    measurable_coefOf _ _ hF1
  have hH : ContDiffOn ℝ 2 (fun q : Chart => hpA p.ν χf A q.1 q.2) (Ioi (0 : ℝ) ×ˢ univ) :=
    h2 hχ p.ν hν0 A hA
  have hg2 := dmeas_second_cont p.ν μ (fun q : Chart => hpA p.ν χf A q.1 q.2) hH
  set g2 : Chart → Merid := fun q : Chart => q.1 • toMer (deriv (fun s' => hpA p.ν χf A s' q.2) q.1 +
      (μ / q.1) • hpA p.ν χf A q.1 q.2 - p.ν • lapPl (hpA p.ν χf A q.1) q.2) with hg2def
  have hg : geoDPiece p μ χf A = coefOf p.ε⁻¹ (physDmu p.ν μ (hLift p.ν p.ε p.c χf A)) - g2 := rfl
  have hpos : ∀ᵐ q ∂(srcMeasure p.c), 0 < q.1 := by
    unfold srcMeasure
    exact Measure.ae_smul_measure (UnforcedLeray.Short.IIIa.ae_pos_ageμ p.c (-3 / 2)) _
  show AEStronglyMeasurable (geoDPiece p μ χf A) (srcMeasure p.c) ∧
    (∀ s : ℝ, (11 / 10) / p.ν < s → ∀ x : ℝ × ℝ, geoDPiece p μ χf A (s, x) = 0) ∧
    (∀ s : ℝ, 0 < s →
      AEStronglyMeasurable (fun x : ℝ × ℝ => geoDPiece p μ χf A (s, x)) (UnforcedLeray.Cyl.avgμ p.c))
  refine ⟨?_, ?_, ?_⟩
  · -- measurability on the source measure
    rw [hg]
    refine hg1.aestronglyMeasurable.sub ?_
    have hU : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := dmeas_isOpen.measurableSet
    have hr : AEStronglyMeasurable g2 ((srcMeasure p.c).restrict (Ioi (0 : ℝ) ×ˢ univ)) :=
      hg2.aestronglyMeasurable hU
    have hnull : (srcMeasure p.c).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))ᶜ = 0 := by
      rw [Measure.restrict_eq_zero]
      rw [ae_iff] at hpos
      convert hpos using 2
      ext q
      simp
    have hcompl : AEStronglyMeasurable g2
        ((srcMeasure p.c).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))ᶜ) := by
      rw [hnull]
      exact aestronglyMeasurable_zero_measure _
    have hall := aestronglyMeasurable_union_iff.2 ⟨hr, hcompl⟩
    rwa [union_compl_self, Measure.restrict_univ] at hall
  · -- support
    intro s hs x
    have hs0 : 0 < s := lt_trans (by positivity) hs
    have hage : (11 / 10) / p.ν < age p.ε⁻¹ (NearInst.chartY p.ε⁻¹ (s, x)) := by
      rw [age_chartY_ra _ _ (inv_pos.2 hε0) hs0]; exact hs
    have hz := physDmu_hLift_zero p.ν p.ε p.c μ χf hχ hν0 A (NearInst.chartTau p.ε⁻¹ (s, x))
      (NearInst.chartY p.ε⁻¹ (s, x)) hage
    have h1z : coefOf p.ε⁻¹ (physDmu p.ν μ (hLift p.ν p.ε p.c χf A)) (s, x) = 0 := by
      unfold coefOf
      rw [hz]
      have : (!₂[(0 : Space) 0, (0 : Space) 2] : Merid) = 0 := by
        ext i; fin_cases i <;> rfl
      rw [this, smul_zero]
    have hAy : ∀ s' : ℝ, (11 / 10) / p.ν < s' → ∀ x' : ℝ × ℝ, hpA p.ν χf A s' x' = 0 :=
      fun s' hs' x' => hAc_hpA_zero p.ν χf A s' x' (hAc_ay_zero χf hχ p.ν hν0 A s' hs')
    have hd : deriv (fun s' => hpA p.ν χf A s' x) s = 0 := by
      have : (fun s' => hpA p.ν χf A s' x) =ᶠ[𝓝 s] fun _ => (0 : ℝ × ℝ) := by
        filter_upwards [isOpen_Ioi.mem_nhds (show s ∈ Ioi ((11 / 10) / p.ν) from hs)] with s' hs'
        exact hAy s' hs' x
      rw [this.deriv_eq, deriv_const]
    have hl : lapPl (hpA p.ν χf A s) x = 0 := by
      have : hpA p.ν χf A s = fun _ => (0 : ℝ × ℝ) := funext fun x' => hAy s hs x'
      rw [this]
      unfold lapPl
      simp
    have h2z : g2 (s, x) = 0 := by
      simp only [hg2def]
      rw [hd, hAy s hs x, hl]
      simp [show toMer 0 = 0 by ext i; fin_cases i <;> rfl]
    rw [hg]
    simp [h1z, h2z]
  · -- sections
    intro s hs
    rw [hg]
    refine (hg1.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable.sub ?_
    have hc2 : Continuous (fun x : ℝ × ℝ => g2 (s, x)) := by
      have hm : ∀ x : ℝ × ℝ, ((s, x) : Chart) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
        fun x => ⟨hs, trivial⟩
      exact hg2.comp_continuous (continuous_const.prodMk continuous_id) hm
    exact hc2.aestronglyMeasurable

end UnforcedLeray.Short.PartIIIb.Concrete
