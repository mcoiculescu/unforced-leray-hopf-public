import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.GeoDTasks
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_3
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_4
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_5
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_6

/-!
# `PartIII-b:C/asrc/ra/9/1/2/7` : `GeoDChartId`

Source: `the November 2 reference manuscript` lines 5034-5039, 4979-4980.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

namespace GeoDChartIdAux

theorem physDmu_congr (ν μ : ℝ) (X Y : ℝ → Space → Space)
    (h : ∀ t, ∀ z, z ∉ axis → X t z = Y t z) (τ : ℝ) (y : Space) (hy : y ∉ axis) :
    physDmu ν μ X τ y = physDmu ν μ Y τ y := by
  have hev : ∀ t, ∀ z, z ∉ axis → X t =ᶠ[𝓝 z] Y t := fun t z hz =>
    Filter.mem_of_superset (mem_nhds_compl_axis hz) (fun w hw => h t w hw)
  have hpd : ∀ t, ∀ z, z ∉ axis → ∀ l, physPd (X t) l z = physPd (Y t) l z := by
    intro t z hz l
    unfold physPd
    rw [(hev t z hz).fderiv_eq]
  have hlap : ∀ t, physLap (X t) y = physLap (Y t) y := by
    intro t
    unfold physLap physPd2
    refine Finset.sum_congr rfl fun j _ => ?_
    have : (fun y' => physPd (X t) j y') =ᶠ[𝓝 y] fun y' => physPd (Y t) j y' :=
      Filter.mem_of_superset (mem_nhds_compl_axis hy) (fun w hw => hpd t w hw j)
    show fderiv ℝ (fun y' => physPd (X t) j y') y (coordinateVector j) =
      fderiv ℝ (fun y' => physPd (Y t) j y') y (coordinateVector j)
    rw [this.fderiv_eq (𝕜 := ℝ)]
  have hder : deriv (fun t => X t y) τ = deriv (fun t => Y t y) τ := by
    congr 1; funext t; exact h t y hy
  unfold physDmu
  rw [hder, (hev τ y hy).fderiv_eq, hlap τ, h τ y hy]

theorem thetaM_c2 (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν : ℝ) (hν : 0 < ν)
    (A : ℝ → Mat3) (hA : IsAffElem as A) :
    ContDiffOn ℝ 2 (thetaM ν χf A) (Ioi 0 ×ˢ univ) := by
  obtain ⟨hP, hΨ⟩ := latSmooth as χf hχ ν hν A hA
  have hK : ContDiffOn ℝ 3 (fun p : Chart => p.2.2 * fderiv ℝ (psiM ν χf A) p (0, (0, 1))
      + 2 * p.1 * fderiv ℝ (psiM ν χf A) p (1, (0, 0))) (Ioi 0 ×ˢ univ) := by
    have d : ContDiffOn ℝ 3 (fun y => fderiv ℝ (psiM ν χf A) y) (Ioi 0 ×ˢ univ) :=
      hΨ.fderiv_of_isOpen DcSplitAux.openU (by norm_num)
    have d1 := d.clm_apply (contDiffOn_const (c := ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))))
    have d2 := d.clm_apply (contDiffOn_const (c := ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))))
    exact ((contDiff_snd.comp contDiff_snd).contDiffOn.mul d1).add
      (((contDiffOn_const.mul contDiffOn_fst)).mul d2)
  have hT3 : ContDiffOn ℝ 3 (thetaM ν χf A) (Ioi 0 ×ˢ univ) := by
    have hΨ3 : ContDiffOn ℝ 3 (psiM ν χf A) (Ioi 0 ×ˢ univ) := hΨ.of_le (by norm_num)
    have hc : ContDiffOn ℝ 3 (fun p : Chart => toMer (0, psiM ν χf A p - (p.2.2 *
        fderiv ℝ (psiM ν χf A) p (0, (0, 1)) + 2 * p.1 * fderiv ℝ (psiM ν χf A) p (1, (0, 0)))))
        (Ioi 0 ×ˢ univ) :=
      DcSplitAux.Lm.contDiff.comp_contDiffOn (contDiffOn_const.prodMk (hΨ3.sub hK))
    refine hc.congr ?_
    intro p hp
    have hd : DifferentiableAt ℝ (psiM ν χf A) p :=
      (DcSplitAux.cdAt hΨ hp.1).differentiableAt (by norm_num)
    have e1 := DcSplitAux.slice_fderiv (psiM ν χf A) p.1 p.2 (ei 1) hd
    have e2 := DcSplitAux.slice_deriv (psiM ν χf A) p.1 p.2 hd
    simp only [thetaM, Kop]
    congr 2
    have e1' : fderiv ℝ (fun y => psipA ν χf A p.1 y) p.2 (ei 1) =
        fderiv ℝ (psiM ν χf A) p (0, (0, 1)) := e1
    have e2' : deriv (fun s' => psipA ν χf A s' p.2) p.1 =
        fderiv ℝ (psiM ν χf A) p (1, (0, 0)) := e2
    rw [e1', e2']
    rfl
  exact hT3.of_le (by norm_num)

end GeoDChartIdAux

open GeoDChartIdAux in
theorem geoDChartId (as : ℝ) (χf : ℝ → ℝ) : GeoDChartId as χf := by
  intro hχ p hc μ A hA q hq
  have hε : 0 < p.ε := p.ε_pos
  have hν : 0 < p.ν := p.ν_pos
  have hR : 0 < p.ε⁻¹ := inv_pos.2 hε
  obtain ⟨hP, _⟩ := latSmooth as χf hχ p.ν hν A hA
  have hb2 : ContDiffOn ℝ 2 (hbM p.ν p.ε χf A) (Ioi 0 ×ˢ univ) :=
    (hP.of_le (by norm_num)).add ((thetaM_c2 as χf hχ p.ν hν A hA).const_smul p.ε)
  obtain ⟨_, _, hϱ, _⟩ := fe_chartY_facts hR q hq
  have hyax : NearInst.chartY p.ε⁻¹ q ∉ axis := fun h => by
    have := (mem_axis_iff _).1 h
    rw [hϱ] at this
    exact (div_ne_zero hR.ne' (Real.sqrt_pos.2 hq).ne') this
  have hphys : physDmu p.ν μ (hLift p.ν p.ε p.c χf A) (NearInst.chartTau p.ε⁻¹ q)
      (NearInst.chartY p.ε⁻¹ q) =
      physDmu p.ν μ (Nv p.ε⁻¹ (hbM p.ν p.ε χf A)) (NearInst.chartTau p.ε⁻¹ q)
        (NearInst.chartY p.ε⁻¹ q) := by
    refine physDmu_congr _ _ _ _ (fun t z hz => ?_) _ _ hyax
    rw [hc]
    exact hLiftIsNv as χf hχ p.ν p.ε hν hε A hA t z hz
  have hcoef : coefOf p.ε⁻¹ (physDmu p.ν μ (hLift p.ν p.ε p.c χf A)) q =
      coefOf p.ε⁻¹ (physDmu p.ν μ (Nv p.ε⁻¹ (hbM p.ν p.ε χf A))) q := by
    unfold coefOf
    rw [hphys]
  have hrule := ringDmuRule p.ε⁻¹ p.ν μ hR _ hb2 q hq
  have hsplit := dcSplit as χf hχ p.ν μ p.ε hν A hA q hq
  simp only [geoDPiece, geoDG, Pi.sub_apply]
  rw [hcoef, hrule, inv_inv, hsplit]
  simp only [toMer_sub, toMer_add, toMer_smul] at *
  simp only [smul_add, smul_sub, smul_smul, mul_comm]
  abel

end UnforcedLeray.Short.PartIIIb.Concrete
