import UnforcedLeray.Short.PartI.Sub.PartI_T04_9_1
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutCont
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.Static

/-!
# `PartI:T04/9/1/3`: qualitative integrability `APLevel2Integ` (lines 285-288)

Both `r ↦ vortJet c 2 v r` and `r ↦ triJet1 c v r` are bounded on `[0,T]` (through the
`L²`-jet bounds `jet_l2`, the uniform bound `hcls.bounded 1`, and the curl estimate
`APEllipticCaux.iteratedFDeriv_curl_le`), and they are pointwise limits of the continuous cutoff
jets of `apLevel2CutCont`, hence a.e. strongly measurable on `[0,T]`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- A pointwise limit (along `R → ∞`) of functions continuous on `[0,T]` is a.e. strongly
measurable on `[0,T]`. -/
theorem apint_meas_of_lim (F : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (T : ℝ)
    (hF : ∀ R : ℝ, 1 ≤ R → ContinuousOn (F R) (Icc (0 : ℝ) T))
    (hlim : ∀ r ∈ Icc (0 : ℝ) T, Tendsto (fun R => F R r) atTop (nhds (f r))) :
    AEStronglyMeasurable f (volume.restrict (Icc (0 : ℝ) T)) := by
  refine aestronglyMeasurable_of_tendsto_ae (μ := volume.restrict (Icc (0 : ℝ) T))
    (f := fun n : ℕ => F ((n : ℝ) + 1)) atTop ?_ ?_
  · intro n
    exact (hF _ (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)).aestronglyMeasurable
      measurableSet_Icc
  · refine ae_restrict_of_forall_mem measurableSet_Icc (fun r hr => ?_)
    exact (hlim r hr).comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

theorem apLevel2Integ : APLevel2Integ := by
  intro ν c T v p hν hc hcls
  have hT : 0 < T := hcls.pos
  have hT0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  -- slice facts
  have hu : ∀ r ∈ Icc (0 : ℝ) T, ContDiff ℝ ∞ (v r) := fun r hr => by
    have h := hcls.classical.smooth_v.comp_contDiff
      ((contDiff_const : ContDiff ℝ ∞ (fun _ : Plane => r)).prodMk contDiff_id :
        ContDiff ℝ ∞ (fun z : Plane => ((r, z) : ℝ × Plane)))
      (fun z => (⟨hr, mem_univ z⟩ : ((r, z) : ℝ × Plane) ∈ Icc (0 : ℝ) T ×ˢ univ))
    exact h
  have hL : ∀ r ∈ Icc (0 : ℝ) T, ∀ i : ℕ,
      IntegrableOn (fun z => ‖iteratedFDeriv ℝ i (v r) z‖ ^ 2) (Cyl.cell c) := fun r hr i => by
    obtain ⟨K, hK⟩ := hcls.jet_l2 i
    exact (hK r hr).1
  have hcurlL : ∀ r ∈ Icc (0 : ℝ) T, ∀ j : ℕ,
      IntegrableOn (fun z => ‖iteratedFDeriv ℝ j (Cyl.curl (v r)) z‖ ^ 2) (Cyl.cell c) :=
    fun r hr j => apL2s_curl_integrableOn (hu r hr) (hL r hr) j
  obtain ⟨M1, hM1⟩ := hcls.bounded 1
  have hM0 : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0 hT0 0)
  have hTriI : ∀ r ∈ Icc (0 : ℝ) T, IntegrableOn (fun z =>
      ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2 * ‖iteratedFDeriv ℝ 1 (v r) z‖) (Cyl.cell c) :=
    fun r hr => by
      refine Integrable.mono' ((hcurlL r hr 1).const_mul M1) ?_
        (Filter.Eventually.of_forall fun z => ?_)
      · exact ((((APEllipticCaux.curl_contDiff (hu r hr)).continuous_iteratedFDeriv (m := 1)
          (by exact_mod_cast le_top)).norm.pow 2).mul
          (((hu r hr).continuous_iteratedFDeriv (m := 1)
            (by exact_mod_cast le_top)).norm)).aestronglyMeasurable
      · have hn : 0 ≤ ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2 := sq_nonneg _
        rw [Real.norm_of_nonneg (mul_nonneg hn (norm_nonneg _))]
        calc ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2 * ‖iteratedFDeriv ℝ 1 (v r) z‖
            ≤ ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2 * M1 :=
              mul_le_mul_of_nonneg_left (hM1 r hr z) hn
          _ = M1 * ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2 := mul_comm _ _
  -- comparison of the vorticity jets with the velocity jets (curl estimate)
  have hcmpJ : ∀ r ∈ Icc (0 : ℝ) T, ∀ j : ℕ,
      vortJet c j v r ≤ ‖APEllipticCaux.lam‖ ^ 2 * velJet c (j + 1) v r := by
    intro r hr j
    unfold vortJet velJet
    rw [← integral_const_mul (‖APEllipticCaux.lam‖ ^ 2)]
    refine integral_mono (hcurlL r hr j) ((hL r hr (j + 1)).const_mul _) (fun z => ?_)
    have h1 := APEllipticCaux.iteratedFDeriv_curl_le (hu r hr) j z
    calc ‖iteratedFDeriv ℝ j (Cyl.curl (v r)) z‖ ^ 2
        ≤ (‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ (j + 1) (v r) z‖) ^ 2 := by gcongr
      _ = ‖APEllipticCaux.lam‖ ^ 2 * ‖iteratedFDeriv ℝ (j + 1) (v r) z‖ ^ 2 := by ring
  -- uniform bounds on [0,T]
  obtain ⟨K2, hK2⟩ := hcls.jet_l2 2
  obtain ⟨K3, hK3⟩ := hcls.jet_l2 3
  have hV1 : ∀ r ∈ Icc (0 : ℝ) T, vortJet c 1 v r ≤ ‖APEllipticCaux.lam‖ ^ 2 * K2 := fun r hr =>
    (hcmpJ r hr 1).trans (mul_le_mul_of_nonneg_left ((hK2 r hr).2) (sq_nonneg _))
  have hV2 : ∀ r ∈ Icc (0 : ℝ) T, vortJet c 2 v r ≤ ‖APEllipticCaux.lam‖ ^ 2 * K3 := fun r hr =>
    (hcmpJ r hr 2).trans (mul_le_mul_of_nonneg_left ((hK3 r hr).2) (sq_nonneg _))
  have hVnn : ∀ (j : ℕ) (r : ℝ), 0 ≤ vortJet c j v r := fun j r => by
    unfold vortJet
    exact integral_nonneg fun z => sq_nonneg _
  have hTriLe : ∀ r ∈ Icc (0 : ℝ) T, triJet1 c v r ≤ 4 * (M1 * vortJet c 1 v r) := by
    intro r hr
    have hint : ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2 *
        ‖iteratedFDeriv ℝ 1 (v r) z‖ ≤ ∫ z in Cyl.cell c, M1 * ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2 :=
      integral_mono (hTriI r hr) ((hcurlL r hr 1).const_mul M1) (fun z => by
        have hn : 0 ≤ ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2 := sq_nonneg _
        calc ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2 * ‖iteratedFDeriv ℝ 1 (v r) z‖
            ≤ ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2 * M1 :=
              mul_le_mul_of_nonneg_left (hM1 r hr z) hn
          _ = M1 * ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2 := mul_comm _ _)
    rw [integral_const_mul] at hint
    unfold triJet1 vortJet
    linarith
  have hTriNn : ∀ r : ℝ, 0 ≤ triJet1 c v r := fun r => by
    unfold triJet1
    exact mul_nonneg (by norm_num) (integral_nonneg fun z => by positivity)
  -- measurability (pointwise limits of the continuous cutoff jets)
  have hmV : AEStronglyMeasurable (fun r => vortJet c 2 v r) (volume.restrict (Icc (0 : ℝ) T)) :=
    apint_meas_of_lim (fun R r => ∫ z in Cyl.cell c, etaCutoff R z.2 *
        ‖iteratedFDeriv ℝ 2 (Cyl.curl (v r)) z‖ ^ 2) _ T
      (fun R hR => (apcc_op_cont hcls R hR).1)
      (fun r hr => tendsto_cutoff_integral etaCutoffFacts c _ (hcurlL r hr 2))
  have hmT : AEStronglyMeasurable (fun r => triJet1 c v r) (volume.restrict (Icc (0 : ℝ) T)) :=
    apint_meas_of_lim (fun R r => 4 * ∫ z in Cyl.cell c, etaCutoff R z.2 *
        (‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2 * ‖iteratedFDeriv ℝ 1 (v r) z‖)) _ T
      (fun R hR => (apcc_op_cont hcls R hR).2)
      (fun r hr => (tendsto_cutoff_integral etaCutoffFacts c _ (hTriI r hr)).const_mul 4)
  have hconst : ∀ C : ℝ, IntegrableOn (fun _ : ℝ => C) (Icc (0 : ℝ) T) :=
    fun C => continuous_const.integrableOn_Icc
  refine ⟨?_, ?_⟩
  · refine Integrable.mono' (hconst (‖APEllipticCaux.lam‖ ^ 2 * K3)) hmV
      (ae_restrict_of_forall_mem measurableSet_Icc (fun r hr => ?_))
    rw [Real.norm_of_nonneg (hVnn 2 r)]
    exact hV2 r hr
  · refine Integrable.mono' (hconst (4 * (M1 * (‖APEllipticCaux.lam‖ ^ 2 * K2)))) hmT
      (ae_restrict_of_forall_mem measurableSet_Icc (fun r hr => ?_))
    rw [Real.norm_of_nonneg (hTriNn r)]
    have h3 : M1 * vortJet c 1 v r ≤ M1 * (‖APEllipticCaux.lam‖ ^ 2 * K2) :=
      mul_le_mul_of_nonneg_left (hV1 r hr) hM0
    linarith [hTriLe r hr]

end UnforcedLeray.Short.PartI
