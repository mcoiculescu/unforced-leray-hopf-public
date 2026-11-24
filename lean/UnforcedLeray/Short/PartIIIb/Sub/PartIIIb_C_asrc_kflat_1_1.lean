import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_3.FlatBSmall
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_3.FlatBContinuous
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_3.FlatXiContinuous
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4.KcJointMeasurable
import UnforcedLeray.Short.PartIIIb.NearInst.FlatTrain.Measurable
import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# `PartIII-b:C/asrc/kflat/1/1` : measurability of `𝔗A` on the old region (`FrakTMeasProp`)

Source of record: `the November 2 reference manuscript` 4605-4612.

Route.  `frakT (levelFlat …) ν μ χf A p = symOuter (NearInst.trainMer tr p) (kcMer (ξ p.1) p.2)` with
`ξ = xiD FI μ (Bmat ν μ χf A)` (`frakT_levelFlat_apply`, definitional).
* `B = Bmat ν μ χf A` is continuous on `(0,∞)` and `|B s| ≤ C s^{3/2}` on `(0,1]`
  (`flatBContinuous`, `flatBSmall`);
* `ξ` is continuous on `(0,∞)` and vanishes on `s ≤ 0` (`xiD_contOn_nonneg`, below, the proof of
  `flatXiContinuous` with `0 ≤ μ` in place of `0 < μ`; `xiD_nonpos`);
* the joint measurability of `(s,x) ↦ K_cξ(s)(x)` is `kcJointMeasurable`;
* `trainMer tr` is measurable (`trainMerMeasurable`), and `symOuter` is a polynomial in the
  coordinates, so the composite is measurable on all of `Chart`, hence a.e. strongly measurable for
  any measure.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

/-- **Continuity of `ξ_B` on `(0,∞)` for `0 ≤ μ`.** This is `flatXiContinuous` (which assumes
`0 < μ`); the proof is the same, with `(t:ℂ)^μ` continuous at `t > 0` for every real `μ`. -/
theorem xiD_contOn_nonneg {κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels} {ν c m : ℝ}
    [Fact (1 < m)] [Fact (0 < c)] {tr : UnforcedLeray.B0140.TrainSol ν c}
    (D : FlatInstData κ ν c m tr) (μ : ℝ) (hμ : 0 ≤ μ)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (C : ℝ) (hB : ContinuousOn B (Ioi 0))
    (hbd : ∀ s ∈ Ioc (0 : ℝ) 1, ∀ i j, |B s i j| ≤ C * s ^ (3 / 2 : ℝ)) :
    ContinuousOn (xiD D (μ : ℂ) B) (Ioi 0) := by
  intro s0 hs0
  apply ContinuousAt.continuousWithinAt
  have hs0' : (0 : ℝ) < s0 := hs0
  have hgc : ContinuousOn (gBD D B) (Ioi 0) := gBD_contOn D B hB
  obtain ⟨K, hK0, hKb⟩ := gBD_bound D B C hbd hgc (s0 + 1)
  obtain ⟨Cs, hCs⟩ := D.ev.locBdd (s0 + 1)
  have hCs0 : 0 ≤ Cs := (norm_nonneg (D.ev.U 0 0)).trans (hCs 0 0 le_rfl le_rfl (by linarith))
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ → Xmc c m, ∀ s t, G s t =
      (Ioc 0 s).indicator (fun t => ((t : ℂ) ^ (μ : ℂ)) • (D.ev.U s t) (gBD D B t)) t :=
    ⟨_, fun _ _ => rfl⟩
  have hS : s0 < s0 + 1 := by linarith
  have hint : Integrable (fun t : ℝ => (Cs * K) * t ^ (μ + 3 / 2)) (volume.restrict (Ioc 0 (s0 + 1))) := by
    have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := s0 + 1)
      (show -1 < μ + 3 / 2 by linarith)
    have h2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0:ℝ) ≤ s0 + 1)).1 h
    exact Integrable.const_mul h2 (Cs * K)
  have hF_meas : ∀ᶠ s in 𝓝 s0, AEStronglyMeasurable (G s) (volume.restrict (Ioc 0 (s0 + 1))) := by
    filter_upwards [Ioo_mem_nhds hs0' hS] with s hs
    have h1 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (μ : ℂ)) (Ioc 0 s) := fun t ht =>
      (Complex.continuousAt_ofReal_cpow_const t μ (Or.inr ht.1.ne')).continuousWithinAt
    have h2 : ContinuousOn (fun t : ℝ => D.ev.U s t (gBD D B t)) (Ioc 0 s) := by
      have hmap : ContinuousOn (fun t : ℝ => ((s, t) : ℝ × ℝ)) (Ioc 0 s) :=
        (continuous_const.prodMk continuous_id).continuousOn
      exact (jointG_contOn D.ev (gBD D B) hgc).comp hmap (fun t ht => ⟨ht.1, ht.2⟩)
    have hfc : ContinuousOn (fun t : ℝ => ((t : ℂ) ^ (μ : ℂ)) • D.ev.U s t (gBD D B t)) (Ioc 0 s) :=
      h1.smul h2
    have hGs : G s = (Ioc 0 s).indicator (fun t => ((t : ℂ) ^ (μ : ℂ)) • (D.ev.U s t) (gBD D B t)) :=
      funext fun t => hG s t
    rw [hGs]
    exact (aestronglyMeasurable_indicator_iff measurableSet_Ioc).2
      (hfc.aestronglyMeasurable measurableSet_Ioc)
  have hbound : ∀ᶠ s in 𝓝 s0, ∀ᵐ t ∂(volume.restrict (Ioc 0 (s0 + 1))),
      ‖G s t‖ ≤ (Cs * K) * t ^ (μ + 3 / 2) := by
    filter_upwards [Ioo_mem_nhds hs0' hS] with s hs
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t => fun ht => ?_)
    by_cases hts : t ≤ s
    · have htI : t ∈ Ioc 0 s := ⟨ht.1, hts⟩
      rw [hG s t, indicator_of_mem htI, norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
      simp only [Complex.ofReal_re]
      have hU : ‖D.ev.U s t (gBD D B t)‖ ≤ Cs * (K * t ^ (3 / 2 : ℝ)) :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (hCs s t ht.1.le hts hs.2.le) (hKb t ht) (norm_nonneg _) hCs0)
      calc t ^ μ * ‖D.ev.U s t (gBD D B t)‖ ≤ t ^ μ * (Cs * (K * t ^ (3 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hU (Real.rpow_nonneg ht.1.le _)
        _ = (Cs * K) * t ^ (μ + 3 / 2) := by rw [Real.rpow_add ht.1]; ring
    · have hnot : t ∉ Ioc 0 s := fun h => hts h.2
      rw [hG s t, indicator_of_notMem hnot, norm_zero]
      exact mul_nonneg (mul_nonneg hCs0 hK0) (Real.rpow_nonneg ht.1.le _)
  have hcont_pt : ∀ᵐ t ∂(volume.restrict (Ioc 0 (s0 + 1))), ContinuousAt (fun s => G s t) s0 := by
    have hae : ∀ᵐ t ∂(volume.restrict (Ioc 0 (s0 + 1))), t ≠ s0 :=
      ae_restrict_of_ae (((Set.countable_singleton s0).ae_notMem volume).mono fun t ht => ht)
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hae] with t ht hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hopen : {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} ∈ 𝓝 (s0, t) := by
        apply IsOpen.mem_nhds
        · exact (isOpen_lt continuous_const continuous_snd).inter
            (isOpen_lt continuous_snd continuous_fst)
        · exact ⟨ht.1, hlt⟩
      have hK_nhds : {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1} ∈ 𝓝 (s0, t) :=
        Filter.mem_of_superset hopen (fun p hp => ⟨hp.1, hp.2.le⟩)
      have hjc : ContinuousAt (fun p : ℝ × ℝ => D.ev.U p.1 p.2 (gBD D B p.2)) (s0, t) :=
        (jointG_contOn D.ev (gBD D B) hgc).continuousAt hK_nhds
      have hcs : ContinuousAt (fun s : ℝ => D.ev.U s t (gBD D B t)) s0 :=
        hjc.comp (f := fun s : ℝ => (s, t)) (continuous_id.prodMk continuous_const).continuousAt
      refine (hcs.const_smul ((t : ℂ) ^ (μ : ℂ))).congr ?_
      filter_upwards [eventually_gt_nhds hlt] with s hs
      rw [hG s t, indicator_of_mem (show t ∈ Ioc 0 s from ⟨ht.1, hs.le⟩)]
      rfl
    · have hev : ∀ᶠ s in 𝓝 s0, s < t := eventually_lt_nhds hgt
      refine (continuousAt_const (y := (0 : Xmc c m))).congr ?_
      filter_upwards [hev] with s hs
      rw [hG s t, indicator_of_notMem (fun h => absurd h.2 (not_le.2 hs))]
  have hcontI : ContinuousAt (fun s => ∫ t, G s t ∂(volume.restrict (Ioc 0 (s0 + 1)))) s0 :=
    continuousAt_of_dominated hF_meas hbound hint hcont_pt
  have hEv : (fun s => xiD D (μ : ℂ) B s) =ᶠ[𝓝 s0]
      (fun s => ((s : ℂ) ^ (-(μ : ℂ))) • ∫ t, G s t ∂(volume.restrict (Ioc 0 (s0 + 1)))) := by
    filter_upwards [Ioo_mem_nhds hs0' hS] with s hs
    have hint_eq : ∫ t, G s t ∂(volume.restrict (Ioc 0 (s0 + 1)))
        = ∫ t in Ioc 0 s, ((t : ℂ) ^ (μ : ℂ)) • (D.ev.U s t) (gBD D B t) := by
      simp_rw [hG s]
      rw [setIntegral_indicator measurableSet_Ioc,
        Set.inter_eq_right.2 (Ioc_subset_Ioc_right hs.2.le)]
    show xiD D (μ : ℂ) B s = _
    rw [xiD_apply, hint_eq]
  have hcpow : ContinuousAt (fun s : ℝ => (s : ℂ) ^ (-(μ : ℂ))) s0 :=
    Complex.continuousAt_ofReal_cpow_const s0 (-(μ : ℂ)) (Or.inr hs0'.ne')
  exact ((hcpow.smul hcontI).congr hEv.symm)

/-- **`𝔗A` is a.e. strongly measurable on the old region** (source 4605-4612; leaf 4 of
`PartIII-b:C/asrc/kflat/1`). -/
theorem frakTMeas (as : ℝ) (χf : ℝ → ℝ) (m : ℝ) [Fact (1 < m)] : FrakTMeasProp as χf m := by
  intro hχ κ ν μ ε χo hν hν1 hμ0 hμ1 tr FI A hA
  have hc : Fact (0 < cOf ν) := ⟨UnforcedLeray.Short.PartIIIb.Concrete.cOf_pos hν⟩
  -- the regularity of `B = B_{μ,ν}[A]` and of `ξ_B`
  have hBc : ContinuousOn (Bmat ν μ χf A) (Ioi 0) := flatBContinuous ν μ as χf A hν hχ hA
  obtain ⟨C, hC⟩ := flatBSmall ν μ as χf A hν hχ hA
  have hξc : ContinuousOn (xiD FI (μ : ℂ) (Bmat ν μ χf A)) (Ioi 0) :=
    xiD_contOn_nonneg FI μ hμ0 (Bmat ν μ χf A) C hBc hC
  have hξ0 : ∀ s : ℝ, s ≤ 0 → xiD FI (μ : ℂ) (Bmat ν μ χf A) s = 0 :=
    fun s hs => xiD_nonpos FI (μ : ℂ) (Bmat ν μ χf A) hs
  -- joint measurability of `(s,x) ↦ K_c ξ(s)(x)` in each coordinate
  have hK := kcJointMeasurable (cOf ν) m (xiD FI (μ : ℂ) (Bmat ν μ χf A)) hξc hξ0
  have hKi : ∀ i : Fin 2, Measurable fun p : Chart =>
      kcMer (xiD FI (μ : ℂ) (Bmat ν μ χf A) p.1) p.2 i := by
    intro i
    have h := Complex.measurable_re.comp (hK i)
    exact h
  -- the flat coefficient is measurable
  have hT : Measurable (NearInst.trainMer tr) := NearInst.trainMerMeasurable ν (cOf ν) tr
  -- coordinates of the meridional vectors
  have hP : ∀ i : Fin 2, Measurable fun a : Merid => a i := fun i =>
    (EuclideanSpace.proj i : Merid →L[ℝ] ℝ).continuous.measurable
  have hemb : ∀ k : Fin 3, Measurable fun a : Merid => UnforcedLeray.Short.IIIa.embedMerid a k := by
    intro k
    fin_cases k
    · exact hP 0
    · exact measurable_const
    · exact hP 1
  have hTe : ∀ k : Fin 3, Measurable fun p : Chart =>
      UnforcedLeray.Short.IIIa.embedMerid (NearInst.trainMer tr p) k := fun k => (hemb k).comp hT
  have hKe : ∀ k : Fin 3, Measurable fun p : Chart =>
      UnforcedLeray.Short.IIIa.embedMerid (kcMer (xiD FI (μ : ℂ) (Bmat ν μ χf A) p.1) p.2) k := by
    intro k
    fin_cases k
    · exact hKi 0
    · exact measurable_const
    · exact hKi 1
  -- the stress readout is measurable, as a map into the pi type `Fin 3 → Fin 3 → ℝ`
  have hPi : Measurable fun p : Chart => fun i j : Fin 3 =>
      UnforcedLeray.Short.IIIa.symOuter (NearInst.trainMer tr p)
        (kcMer (xiD FI (μ : ℂ) (Bmat ν μ χf A) p.1) p.2) i j := by
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    exact ((hTe i).mul (hKe j)).add ((hKe i).mul (hTe j))
  -- the identity `Fin 3 → Fin 3 → ℝ → Matrix (Fin 3) (Fin 3) ℝ` is continuous (same topology)
  have hcont : Continuous (fun x : Fin 3 → Fin 3 → ℝ => (x : Matrix (Fin 3) (Fin 3) ℝ)) :=
    continuous_id
  have e : frakT (levelFlat hν FI χo ε) ν μ χf A =
      (fun x : Fin 3 → Fin 3 → ℝ => (x : Matrix (Fin 3) (Fin 3) ℝ)) ∘ (fun p : Chart => fun i j : Fin 3 =>
        UnforcedLeray.Short.IIIa.symOuter (NearInst.trainMer tr p)
          (kcMer (xiD FI (μ : ℂ) (Bmat ν μ χf A) p.1) p.2) i j) := rfl
  rw [e]
  exact hcont.comp_aestronglyMeasurable hPi.aestronglyMeasurable

end UnforcedLeray.Short.PartIIIb.Concrete
