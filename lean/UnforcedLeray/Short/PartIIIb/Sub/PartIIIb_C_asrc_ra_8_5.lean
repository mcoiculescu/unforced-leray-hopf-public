import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5

/-!
# `PartIII-b:C/asrc/ra/8/5` : `RPerMeas` from the regularity leaves

Source of record: `the November 2 reference manuscript` 5023-5028, 4978.

`s·r_per` is continuous on the open set `s > 0` (joint `C²` of `h^p_A`, `C¹` of `sΨ_A`, continuity
of `F_A + E_A`, smoothness of the train), the source measure `π s^{-3/2} dς` is carried by `s > 0`,
hence `s·r_per` is a.e. strongly measurable.  Leaves: `HpAC2`, `AffPsiC1`, `AffFECont`
(tasks `ra/5/5`, `ra/5/3`, `ra/5/4`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The open half-space `s > 0` of the chart space. -/
abbrev posU : Set Chart := Ioi (0 : ℝ) ×ˢ univ

theorem isOpen_posU : IsOpen posU := isOpen_Ioi.prod isOpen_univ

theorem mem_posU {p : Chart} : p ∈ posU ↔ 0 < p.1 := by simp [posU]

theorem hasFDerivAt_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Chart → E}
    {H' : Chart →L[ℝ] E} {s : ℝ} {x : ℝ × ℝ} (h : HasFDerivAt H H' (s, x)) :
    HasFDerivAt (fun y : ℝ × ℝ => H (s, y)) (H'.comp ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ _))) x := by
  have h2 : HasFDerivAt (fun y : ℝ × ℝ => (s, y))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) x :=
    (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x)
  exact HasFDerivAt.comp x (by simpa using h) h2

theorem fderiv_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Chart → E}
    {s : ℝ} {x : ℝ × ℝ} (h : DifferentiableAt ℝ H (s, x)) (v : ℝ × ℝ) :
    fderiv ℝ (fun y : ℝ × ℝ => H (s, y)) x v = fderiv ℝ H (s, x) (0, v) := by
  rw [(hasFDerivAt_slice h.hasFDerivAt).fderiv]
  rfl

theorem deriv_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Chart → E}
    {s : ℝ} {x : ℝ × ℝ} (h : DifferentiableAt ℝ H (s, x)) :
    deriv (fun s' : ℝ => H (s', x)) s = fderiv ℝ H (s, x) (1, 0) := by
  have h2 : HasDerivAt (fun s' : ℝ => (s', x)) ((1 : ℝ), (0 : ℝ × ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  have := h.hasFDerivAt.comp_hasDerivAt s h2
  exact this.deriv

theorem toMer_continuous : Continuous toMer := by
  unfold toMer
  have : (fun v : ℝ × ℝ => (!₂[v.1, v.2] : Merid)) =
      fun v => (WithLp.toLp 2 ![v.1, v.2] : Merid) := rfl
  refine (PiLp.continuous_toLp 2 _).comp ?_
  exact continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop

theorem ofMer_continuous : Continuous (fun m : Merid => (m 0, m 1)) := by
  fun_prop


theorem trainPl_contDiffOn {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) :
    ContDiffOn ℝ 1 (fun p : Chart => trainPl tr p.1 p.2) posU := by
  have h := tr.isTrain.smooth_v
  have h1 : ContDiffOn ℝ 1 (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2) posU :=
    (h.of_le (by exact_mod_cast le_top)).mono (fun p hp => ⟨le_of_lt (mem_posU.1 hp), trivial⟩)
  have c0 : ContDiffOn ℝ 1 (fun p : Chart => tr.v p.1 p.2 0) posU :=
    ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn h1)
  have c1 : ContDiffOn ℝ 1 (fun p : Chart => tr.v p.1 p.2 1) posU :=
    ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn h1)
  exact c0.prodMk c1


theorem rPer_continuousOn {ν c : ℝ} (μ : ℝ) (χ : ℝ → ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (A : ℝ → Mat3)
    (h1 : ContDiffOn ℝ 2 (fun p : Chart => hpA ν χ A p.1 p.2) posU)
    (h2 : ContDiffOn ℝ 1 (fun p : Chart => p.1 * PsiA ν χ A p.1 p.2) posU)
    (h3 : ContinuousOn (FAcoef ν μ χ A + EAcoef ν μ χ A) posU) :
    ContinuousOn (fun p : Chart => rPer μ χ tr A p.1 p.2) posU := by
  set H : Chart → ℝ × ℝ := fun p => hpA ν χ A p.1 p.2 with hHdef
  set G : Chart → ℝ := fun p => p.1 * PsiA ν χ A p.1 p.2 with hGdef
  set T : Chart → ℝ × ℝ := fun p => trainPl tr p.1 p.2 with hTdef
  have hU := isOpen_posU
  have hD : ContDiffOn ℝ 1 (fderiv ℝ H) posU := h1.fderiv_of_isOpen hU (by norm_num)
  have hDc : ContinuousOn (fderiv ℝ H) posU := hD.continuousOn
  have hdiff : ∀ p ∈ posU, DifferentiableAt ℝ H p := fun p hp =>
    (h1.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)
  have hT1 := trainPl_contDiffOn tr
  have hTc : ContinuousOn T posU := hT1.continuousOn
  have hTdiff : ∀ p ∈ posU, DifferentiableAt ℝ T p := fun p hp =>
    (hT1.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)
  have hDT : ContinuousOn (fderiv ℝ T) posU := hT1.continuousOn_fderiv_of_isOpen hU le_rfl
  have hGdiff : ∀ p ∈ posU, DifferentiableAt ℝ G p := fun p hp =>
    (h2.contDiffAt (hU.mem_nhds hp)).differentiableAt one_ne_zero
  have hDG : ContinuousOn (fderiv ℝ G) posU := h2.continuousOn_fderiv_of_isOpen hU le_rfl
  have hHc : ContinuousOn H posU := h1.continuousOn
  -- second derivatives
  set K : Fin 2 → Chart → ℝ × ℝ := fun a q => fderiv ℝ H q (0, ei a) with hKdef
  have hK : ∀ a, ContDiffOn ℝ 1 (K a) posU := fun a => hD.clm_apply contDiffOn_const
  have hKdiff : ∀ a, ∀ p ∈ posU, DifferentiableAt ℝ (K a) p := fun a p hp =>
    ((hK a).contDiffAt (hU.mem_nhds hp)).differentiableAt one_ne_zero
  have hDK : ∀ a, ContinuousOn (fderiv ℝ (K a)) posU := fun a =>
    (hK a).continuousOn_fderiv_of_isOpen hU le_rfl
  set FE := FAcoef ν μ χ A + EAcoef ν μ χ A with hFE
  -- the continuous model
  set F : Chart → ℝ × ℝ := fun p =>
    fderiv ℝ H p (1, 0) + (μ / p.1) • H p - ν • (∑ a : Fin 2, fderiv ℝ (K a) p (0, ei a)) +
      fderiv ℝ H p (0, T p) + fderiv ℝ T p (0, H p) - p.1⁻¹ • (FE p 0, FE p 1) -
      p.1⁻¹ • (fderiv ℝ G p (0, ei 0), fderiv ℝ G p (0, ei 1)) with hF
  have hs0 : ∀ p ∈ posU, p.1 ≠ 0 := fun p hp => (mem_posU.1 hp).ne'
  have hFc : ContinuousOn F posU := by
    have a1 : ContinuousOn (fun p : Chart => fderiv ℝ H p (1, 0)) posU :=
      hDc.clm_apply continuousOn_const
    have a2 : ContinuousOn (fun p : Chart => (μ / p.1) • H p) posU :=
      (continuousOn_const.div continuousOn_fst hs0).smul hHc
    have a3 : ContinuousOn (fun p : Chart => ν • (∑ a : Fin 2, fderiv ℝ (K a) p (0, ei a))) posU :=
      ContinuousOn.const_smul (continuousOn_finsetSum _ fun a _ =>
        (hDK a).clm_apply continuousOn_const) ν
    have a4 : ContinuousOn (fun p : Chart => fderiv ℝ H p (0, T p)) posU :=
      hDc.clm_apply (continuousOn_const.prodMk hTc)
    have a5 : ContinuousOn (fun p : Chart => fderiv ℝ T p (0, H p)) posU :=
      hDT.clm_apply (continuousOn_const.prodMk hHc)
    have a6 : ContinuousOn (fun p : Chart => p.1⁻¹ • (FE p 0, FE p 1)) posU :=
      (continuousOn_fst.inv₀ hs0).smul (ofMer_continuous.comp_continuousOn h3)
    have a7 : ContinuousOn (fun p : Chart =>
        p.1⁻¹ • (fderiv ℝ G p (0, ei 0), fderiv ℝ G p (0, ei 1))) posU :=
      (continuousOn_fst.inv₀ hs0).smul
        ((hDG.clm_apply continuousOn_const).prodMk (hDG.clm_apply continuousOn_const))
    exact ((((((a1.add a2).sub a3).add a4).add a5).sub a6).sub a7)
  refine hFc.congr ?_
  intro p hp
  have hp0 : 0 < p.1 := mem_posU.1 hp
  have hpe : ((p.1, p.2) : Chart) = p := rfl
  have hHd : DifferentiableAt ℝ H (p.1, p.2) := hdiff p hp
  -- the individual identities
  have e1 : deriv (fun s' => hpA ν χ A s' p.2) p.1 = fderiv ℝ H p (1, 0) := deriv_slice hHd
  have e3 : lapPl (hpA ν χ A p.1) p.2 = ∑ a : Fin 2, fderiv ℝ (K a) p (0, ei a) := by
    unfold lapPl
    refine Finset.sum_congr rfl fun a _ => ?_
    have hin : (fun y : ℝ × ℝ => fderiv ℝ (hpA ν χ A p.1) y (ei a)) =
        fun y => K a (p.1, y) := by
      funext y
      exact fderiv_slice (H := H) (s := p.1) (x := y) (hdiff (p.1, y) (mem_posU.2 hp0)) _
    rw [hin]
    exact fderiv_slice (H := K a) (s := p.1) (x := p.2) (hKdiff a p hp) _
  have e4 : fderiv ℝ (hpA ν χ A p.1) p.2 (trainPl tr p.1 p.2) = fderiv ℝ H p (0, T p) :=
    fderiv_slice (H := H) (s := p.1) (x := p.2) hHd _
  have e5 : fderiv ℝ (trainPl tr p.1) p.2 (hpA ν χ A p.1 p.2) = fderiv ℝ T p (0, H p) :=
    fderiv_slice (H := T) (s := p.1) (x := p.2) (hTdiff p hp) _
  have e6 : merPl (fA ν μ χ A p.1 p.2) + merPl (eA ν μ χ A p.1 p.2) =
      p.1⁻¹ • (FE p 0, FE p 1) := by
    have hq : (Real.sqrt p.1)⁻¹ * p.1 ^ (3 / 2 : ℝ) = p.1 := by
      have : p.1 ^ (3 / 2 : ℝ) = p.1 * Real.sqrt p.1 := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hp0.le (by norm_num)]
        norm_num
      rw [this]
      have : Real.sqrt p.1 ≠ 0 := (Real.sqrt_pos.2 hp0).ne'
      field_simp
    have hq' : ∀ y : ℝ, (Real.sqrt p.1)⁻¹ * (p.1 ^ (3 / 2 : ℝ) * y) = p.1 * y := by
      intro y; rw [← mul_assoc, hq]
    simp only [hFE, Pi.add_apply, FAcoef, EAcoef, FA, EA, merOf, merPl]
    ext
    · simp [hq']
      field_simp
    · simp [hq']
      field_simp
  have e7 : mgrad (PsiA ν χ A p.1) p.2 =
      p.1⁻¹ • (fderiv ℝ G p (0, ei 0), fderiv ℝ G p (0, ei 1)) := by
    have hPs : PsiA ν χ A p.1 = fun y => p.1⁻¹ * G (p.1, y) := by
      funext y; simp only [hGdef]; field_simp
    have hGs : DifferentiableAt ℝ (fun y : ℝ × ℝ => G (p.1, y)) p.2 :=
      (hasFDerivAt_slice (hGdiff p hp).hasFDerivAt).differentiableAt
    have key : ∀ v, fderiv ℝ (PsiA ν χ A p.1) p.2 v = p.1⁻¹ * fderiv ℝ G p (0, v) := by
      intro v
      rw [hPs, fderiv_const_mul hGs]
      simp only [smul_apply, smul_eq_mul]
      rw [fderiv_slice (H := G) (s := p.1) (x := p.2) (hGdiff p hp)]
    simp only [mgrad, key]
    rfl
  simp only [rPer]
  rw [e1, e3, e4, e5]
  have e67 := e6
  have e7' := e7
  simp only [hF, hHdef]
  rw [sub_sub, sub_sub, ← e6, ← e7]
  simp only [smul_eq_mul, hTdef]
  abel


theorem ae_srcMeasure_pos (c : ℝ) : ∀ᵐ p ∂(srcMeasure c), 0 < p.1 := by
  have h1 : ∀ᵐ s ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
      fun s => ENNReal.ofReal (s ^ (-3 / 2 : ℝ))), 0 < s :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  have h2 : ∀ᵐ p ∂(ageμ c (-3 / 2)), 0 < p.1 := by
    unfold ageμ
    exact Measure.quasiMeasurePreserving_fst.ae h1
  unfold srcMeasure
  exact Measure.ae_smul_measure h2 _

theorem aestronglyMeasurable_of_continuousOn_pos {c : ℝ} {E : Type*} [NormedAddCommGroup E]
    {f : Chart → E} (hf : ContinuousOn f posU) : AEStronglyMeasurable f (srcMeasure c) := by
  have h := hf.aestronglyMeasurable (μ := srcMeasure c) isOpen_posU.measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem] at h
  filter_upwards [ae_srcMeasure_pos c] with p hp using mem_posU.2 hp

/-- **`RPerMeas` from the three regularity leaves.** -/
theorem rPerMeas_of (as : ℝ) (χf : ℝ → ℝ) (h1 : HpAC2 as χf) (h2 : AffPsiC1 as χf)
    (h3 : AffFECont as χf) : RPerMeas as χf := by
  intro hχ p d dm dp hreg μ A hA
  have hν : 0 < p.ν := p.ν_pos
  have hc := rPer_continuousOn μ χf p.train A (h1 hχ p.ν hν A hA) (h2 hχ p.ν hν A hA)
    (h3 hχ p.ν μ hν A hA)
  refine aestronglyMeasurable_of_continuousOn_pos ?_
  unfold rPerCoef
  exact continuousOn_fst.smul (toMer_continuous.comp_continuousOn hc)

end UnforcedLeray.Short.PartIIIb.Concrete
