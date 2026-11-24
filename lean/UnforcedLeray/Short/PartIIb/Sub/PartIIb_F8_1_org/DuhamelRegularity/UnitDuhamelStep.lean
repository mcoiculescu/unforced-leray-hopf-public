import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org.DuhamelRegularity.UnitDuhamelStep.BochnerWeak

/-!
# `PartII-b:F8/1/org/3/1` (`UnitDuhamelStep.lean`): Unit-window `(σ, σ + 1)` Bochner–Duhamel
weak solution, `H¹` trace/continuity, and `H¹ → H²` parabolic regularity

Source of record: `the November 2 reference manuscript` (SP), lines 2296–2305.

Proves `cylUnitDuhamelStep_proof : UnforcedLeray.Short.IIb.CylUnitDuhamelStep` by realizing the
unit-window Bochner–Duhamel path `WPath` and second-derivative paths `d2Path` as jointly strongly
measurable, `QPeriodic` `CProf` profiles via `JointMeasurableRep.exists_stronglyMeasurable_rep` +
`F8Duh.perJointProf`, lifting slice weak derivatives via `TailPeriodizeAux.sliceWeakToJoint`, and
lifting the slice Duhamel equation `duhamel_slice_weak_eq` via `qPeriodize` Fubini disintegration.

All helper declarations live inside `UnforcedLeray.Short.IIb.UnitDuhamelStepAux` (R6).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIb.UnitDuhamelStepAux

open UnforcedLeray.Short.IIb
open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-! ## 1. Joint `StronglyMeasurable` + `QPeriodic` window realization and slice-to-joint lifts -/

/-- Realizes a strongly measurable `L2Cell c` path `u` on `Ioo σ (σ + 1)` (`0 ≤ σ`) as a jointly
`StronglyMeasurable`, `QPeriodic c` profile vanishing outside `x.1 ∈ Ioo σ (σ + 1)`. -/
lemma exists_window_cprof {c σ : ℝ} (hc : 0 < c) (hσ : 0 ≤ σ)
    {u : ℝ → L2Cell c} (hu : StronglyMeasurable u) :
    ∃ prof : CProf,
      StronglyMeasurable prof ∧
      QPeriodic c prof ∧
      (∀ t ∈ Ioo σ (σ + 1), F8U.slice prof t =ᵐ[F8Sm.cellMeas c] u t) ∧
      (∀ x : Coord, x.1 ∉ Ioo σ (σ + 1) → prof x = 0) := by
  obtain ⟨F, hF_sm, hF_ae⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep hu
  let S_win : Set Coord := {x : Coord | x.1 ∈ Ioo σ (σ + 1)}
  have hS_meas : MeasurableSet S_win := measurableSet_Ioo.preimage measurable_fst
  let P0 : CProf := F8Duh.perJointProf c (Function.curry F)
  have hP0_sm : StronglyMeasurable P0 :=
    F8Duh.stronglyMeasurable_perJointProf (by simpa [Function.uncurry_curry] using hF_sm)
  let prof : CProf := S_win.indicator P0
  refine ⟨prof, hP0_sm.indicator hS_meas, ?_, ?_,
    fun x hx => indicator_of_notMem (show x ∉ S_win from hx) P0⟩
  · refine QPerHalf.of_ae_imp ?_
    filter_upwards [QPerHalf.ae_imp (F8Duh.qPeriodic_perJointProf hc (Function.curry F))]
      with x hx hp
    by_cases hm : x ∈ S_win
    · have hm' : qShift c x ∈ S_win := hm
      dsimp only [prof]
      rw [indicator_of_mem hm', indicator_of_mem hm]
      exact hx hp
    · have hm' : qShift c x ∉ S_win := hm
      dsimp only [prof]
      rw [indicator_of_notMem hm', indicator_of_notMem hm]
  · intro t ht
    have ht_pos : 0 < t := lt_of_le_of_lt hσ ht.1
    have hslice_eq : F8U.slice prof t = F8U.slice P0 t := by
      funext y
      exact indicator_of_mem (show (t, y) ∈ S_win from ht) P0
    rw [hslice_eq]
    exact F8Duh.slice_perJointProf_ae_cell hc (fun s _ => hF_ae s) ht_pos

private lemma eLpNorm_comp_le_merid (c : ℝ) (g : CProf) (s : ℝ) (i : Fin 2) :
    eLpNorm (fun z => g (s, z) i) 2 (volume.restrict (B0579.cell c)) ≤
      eLpNorm (fun z => g (s, z)) 2 (volume.restrict (B0579.cell c)) := by
  refine eLpNorm_mono_enorm fun z => ?_
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
  exact_mod_cast PiLp.norm_apply_le (g (s, z)) i

private lemma fubini_cell_slices {c a b : ℝ} {F : Coord → ℂ}
    (hF : IntegrableOn F (Icc a b ×ˢ B0579.cell c) volume) :
    IntegrableOn (fun s : ℝ => ∫ z in B0579.cell c, F (s, z)) (Icc a b) volume ∧
      ∀ᵐ s ∂(volume.restrict (Icc a b)),
        IntegrableOn (fun z : B0579.Plane => F (s, z)) (B0579.cell c) volume := by
  have hF' : Integrable F ((volume.restrict (Icc a b)).prod (volume.restrict (B0579.cell c))) := by
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact ⟨hF'.integral_prod_left, hF'.prod_right_ae⟩

/-- Joint strong measurability and `q`-periodicity of `flatBv p.train w wq wη` for profiles
supported on `Ioo σ (σ + 1)` (`0 ≤ σ`). -/
lemma flatBv_window_meas_and_per (p : Params) {σ : ℝ} (hσ : 0 ≤ σ)
    {w wq wη : CProf}
    (hw_sm : StronglyMeasurable w) (hwq_sm : StronglyMeasurable wq)
    (hwη_sm : StronglyMeasurable wη)
    (hw_per : QPeriodic p.c w) (hwq_per : QPeriodic p.c wq) (hwη_per : QPeriodic p.c wη)
    (hw_out : ∀ x : Coord, x.1 ∉ Ioo σ (σ + 1) → w x = 0)
    (hwq_out : ∀ x : Coord, x.1 ∉ Ioo σ (σ + 1) → wq x = 0)
    (hwη_out : ∀ x : Coord, x.1 ∉ Ioo σ (σ + 1) → wη x = 0) :
    StronglyMeasurable (flatBv p.train w wq wη) ∧
      QPeriodic p.c (flatBv p.train w wq wη) ∧
      (∀ x : Coord, x.1 ∉ Ioo σ (σ + 1) → flatBv p.train w wq wη x = 0) := by
  let Upos : Set Coord := Ioi (0 : ℝ) ×ˢ (univ : Set B0579.Plane)
  have hUpos_open : IsOpen Upos := isOpen_Ioi.prod isOpen_univ
  have hUpos_meas : MeasurableSet Upos := measurableSet_Ioi.prod MeasurableSet.univ
  let vi (i : Fin 2) : Coord → ℝ := fun x => p.train.v x.1 x.2 i
  have hvi_sm : ∀ i : Fin 2, ContDiffOn ℝ ∞ (vi i) Upos := fun i =>
    (EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn
      (p.train.isTrain.smooth_v.mono (prod_mono_left Ioi_subset_Ici_self))
  have hvi_ind_sm : ∀ k : Fin 2, StronglyMeasurable (Upos.indicator (vi k)) := fun k =>
    UnforcedLeray.Infra.JointMeasurableRep.stronglyMeasurable_indicator_of_continuousOn
      (hvi_sm k).continuousOn hUpos_meas
  have hdv_cont : ∀ (j i : Fin 2),
      ContinuousOn (fun x : Coord => fderiv ℝ (fun z => p.train.v x.1 z i) x.2 (B0579.dir j))
        Upos := by
    intro j i
    have hdvi_cont : ContinuousOn (fun x : Coord => fderiv ℝ (vi i) x (0, B0579.dir j)) Upos := by
      intro x hx
      exact ((((hvi_sm i).contDiffAt (hUpos_open.mem_nhds hx)).fderiv_right
        (m := ∞) (by simp)).clm_apply contDiffAt_const).continuousAt.continuousWithinAt
    refine hdvi_cont.congr fun x hx => ?_
    have hfa : DifferentiableAt ℝ (vi i) (x.1, x.2) :=
      ((hvi_sm i).contDiffAt (hUpos_open.mem_nhds hx)).differentiableAt (by simp)
    have hin : HasFDerivAt (fun z : B0579.Plane => (x.1, z))
        ((0 : B0579.Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ B0579.Plane)) x.2 :=
      (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) x.2)
    change fderiv ℝ (vi i ∘ Prod.mk x.1) x.2 (B0579.dir j) = _
    rw [(hfa.hasFDerivAt.comp x.2 hin).fderiv]
    rfl
  have hdv_ind_sm : ∀ (j i : Fin 2), StronglyMeasurable
      (Upos.indicator fun x : Coord =>
        fderiv ℝ (fun z => p.train.v x.1 z i) x.2 (B0579.dir j)) :=
    fun j i => UnforcedLeray.Infra.JointMeasurableRep.stronglyMeasurable_indicator_of_continuousOn
      (hdv_cont j i) hUpos_meas
  refine ⟨?_, ?_, fun x hx => by ext i; simp [flatBv, hw_out x hx, hwq_out x hx, hwη_out x hx]⟩
  · have hm_coord : ∀ i : Fin 2,
        StronglyMeasurable (fun x : Coord => flatBv p.train w wq wη x i) := by
      intro i
      have hw0 : StronglyMeasurable (fun x : Coord => w x 0) :=
        (EuclideanSpace.proj 0 : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable hw_sm
      have hw1 : StronglyMeasurable (fun x : Coord => w x 1) :=
        (EuclideanSpace.proj 1 : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable hw_sm
      have hwqi : StronglyMeasurable (fun x : Coord => wq x i) :=
        (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable hwq_sm
      have hwηi : StronglyMeasurable (fun x : Coord => wη x i) :=
        (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable hwη_sm
      have hv0_c : StronglyMeasurable
          (fun x : Coord => ((Upos.indicator (vi 0) x : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp_stronglyMeasurable (hvi_ind_sm 0)
      have hv1_c : StronglyMeasurable
          (fun x : Coord => ((Upos.indicator (vi 1) x : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp_stronglyMeasurable (hvi_ind_sm 1)
      have hdv0_c : StronglyMeasurable (fun x : Coord =>
          ((Upos.indicator (fun y : Coord =>
            fderiv ℝ (fun z => p.train.v y.1 z i) y.2 (B0579.dir 0)) x : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp_stronglyMeasurable (hdv_ind_sm 0 i)
      have hdv1_c : StronglyMeasurable (fun x : Coord =>
          ((Upos.indicator (fun y : Coord =>
            fderiv ℝ (fun z => p.train.v y.1 z i) y.2 (B0579.dir 1)) x : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp_stronglyMeasurable (hdv_ind_sm 1 i)
      have heq : (fun x : Coord => flatBv p.train w wq wη x i) = fun x =>
          ((Upos.indicator (vi 0) x : ℝ) : ℂ) * wq x i +
          ((Upos.indicator (vi 1) x : ℝ) : ℂ) * wη x i +
          w x 0 * ((Upos.indicator (fun y : Coord =>
            fderiv ℝ (fun z => p.train.v y.1 z i) y.2 (B0579.dir 0)) x : ℝ) : ℂ) +
          w x 1 * ((Upos.indicator (fun y : Coord =>
            fderiv ℝ (fun z => p.train.v y.1 z i) y.2 (B0579.dir 1)) x : ℝ) : ℂ) := by
        funext x
        by_cases hx : x.1 ∈ Ioo σ (σ + 1)
        · have hxU : x ∈ Upos := ⟨lt_of_le_of_lt hσ hx.1, trivial⟩
          simp [flatBv, vi, B0579.dir, indicator_of_mem hxU]
        · simp [flatBv, hw_out x hx, hwq_out x hx, hwη_out x hx]
      rw [heq]
      exact (((hv0_c.mul hwqi).add (hv1_c.mul hwηi)).add (hw0.mul hdv0_c)).add (hw1.mul hdv1_c)
    have hm : Measurable (flatBv p.train w wq wη) := by
      have heq : flatBv p.train w wq wη =
          fun x => WithLp.toLp 2 (fun i : Fin 2 => flatBv p.train w wq wη x i) :=
        funext fun _ => rfl
      rw [heq]
      exact (PiLp.continuous_toLp 2 _).measurable.comp
        (measurable_pi_lambda _ fun i => (hm_coord i).measurable)
    exact hm.stronglyMeasurable
  · refine QPerHalf.of_ae_imp ?_
    filter_upwards [QPerHalf.ae_imp hw_per, QPerHalf.ae_imp hwq_per, QPerHalf.ae_imp hwη_per]
      with x hwx hwqx hwηx hpos
    have hs_nn : 0 ≤ x.1 := hpos.le
    have hVs : ContDiff ℝ ∞ (p.train.v x.1) := by
      have hc := p.train.isTrain.smooth_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (s := univ) (fun y _ => ⟨mem_Ici.2 hs_nn, mem_univ y⟩)
      exact contDiffOn_univ.1 hc
    have hd_per : ∀ (i : Fin 2) (dir_p : B0579.Plane),
        fderiv ℝ (fun z => p.train.v x.1 z i) (x.2.1 + p.c, x.2.2) dir_p =
          fderiv ℝ (fun z => p.train.v x.1 z i) x.2 dir_p := by
      intro i dir_p
      let fi : B0579.Plane → ℝ := fun z => p.train.v x.1 z i
      have hfi_sm : ContDiff ℝ ∞ fi :=
        (EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).contDiff.comp hVs
      have hshift : HasFDerivAt (fun z : B0579.Plane => z + (p.c, (0 : ℝ)))
          (ContinuousLinearMap.id ℝ B0579.Plane) x.2 :=
        (hasFDerivAt_id (𝕜 := ℝ) x.2).add_const (p.c, (0 : ℝ))
      have hdiff : DifferentiableAt ℝ fi (x.2 + (p.c, (0 : ℝ))) :=
        hfi_sm.contDiffAt.differentiableAt (by simp)
      have hcomp := hdiff.hasFDerivAt.comp x.2 hshift
      have hfun : (fi ∘ fun z : B0579.Plane => z + (p.c, (0 : ℝ))) = fi := by
        funext z
        change p.train.v x.1 (z.1 + p.c, z.2 + 0) i = p.train.v x.1 z i
        rw [add_zero, p.train.isTrain.periodic_v x.1 hs_nn z]
      rw [hfun, ContinuousLinearMap.comp_id] at hcomp
      have hz : (x.2.1 + p.c, x.2.2) = x.2 + (p.c, (0 : ℝ)) := by ext <;> simp
      rw [hz, ← hcomp.fderiv]
    ext i
    simp only [flatBv, qShift]
    change ((p.train.v x.1 (x.2.1 + p.c, x.2.2) 0 : ℝ) : ℂ) * wq (qShift p.c x) i +
        ((p.train.v x.1 (x.2.1 + p.c, x.2.2) 1 : ℝ) : ℂ) * wη (qShift p.c x) i +
        w (qShift p.c x) 0 *
          ((fderiv ℝ (fun z => p.train.v x.1 z i) (x.2.1 + p.c, x.2.2) ((1 : ℝ), (0 : ℝ)) : ℝ) : ℂ) +
        w (qShift p.c x) 1 *
          ((fderiv ℝ (fun z => p.train.v x.1 z i) (x.2.1 + p.c, x.2.2) ((0 : ℝ), (1 : ℝ)) : ℝ) : ℂ) = _
    rw [p.train.isTrain.periodic_v x.1 hs_nn x.2,
      hd_per i ((1 : ℝ), (0 : ℝ)), hd_per i ((0 : ℝ), (1 : ℝ)),
      hwx hpos, hwqx hpos, hwηx hpos]

/-- Lifts a.e. cell weak derivatives on `Ioo σ (σ + 1)` to `F8Duh.HasWeakVecOnIoo σ (σ + 1)`
for window-supported periodic profiles `g, G`. -/
lemma weakVecOnIoo_of_window_cprof {c σ : ℝ} (hc : 0 < c) (j : Fin 2)
    {g G : CProf} {ug uG : ℝ → L2Cell c}
    (hg_sm : StronglyMeasurable g) (hG_sm : StronglyMeasurable G)
    (hg_per : QPeriodic c g) (hG_per : QPeriodic c G)
    (hg_sl : ∀ t ∈ Ioo σ (σ + 1), F8U.slice g t =ᵐ[F8Sm.cellMeas c] ug t)
    (hG_sl : ∀ t ∈ Ioo σ (σ + 1), F8U.slice G t =ᵐ[F8Sm.cellMeas c] uG t)
    (hg_out : ∀ x : Coord, x.1 ∉ Ioo σ (σ + 1) → g x = 0)
    (hG_out : ∀ x : Coord, x.1 ∉ Ioo σ (σ + 1) → G x = 0)
    (hug_sm : StronglyMeasurable ug)
    (hug_l1 : (∫⁻ t in Ioo σ (σ + 1), ENNReal.ofReal ‖ug t‖) < ⊤)
    (huG_l1 : (∫⁻ t in Ioo σ (σ + 1), ENNReal.ofReal ‖uG t‖) < ⊤)
    (hwk : ∀ᵐ t ∂volume, t ∈ Ioo σ (σ + 1) → ∀ k : Fin 2,
      IIIa.HasWeakCellDerivC c j (fun y => ug t y k) (fun y => uG t y k)) :
    F8Duh.HasWeakVecOnIoo σ (σ + 1) (![vQ0, vEta] j) dZero g G := by
  refine F8Duh.hasWeakVecOnIoo_of_global σ (σ + 1)
    (TailPeriodizeAux.sliceWeakToJoint hc j g G hg_sm hG_sm hg_per hG_per ?_ ?_)
  · intro a b _ha
    have hind_eq : (fun s : ℝ =>
          eLpNorm (fun z => g (s, z)) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun z => G (s, z)) 2 (volume.restrict (B0579.cell c))) =
        (Ioo σ (σ + 1)).indicator
          (fun t => ENNReal.ofReal ‖ug t‖ + ENNReal.ofReal ‖uG t‖) := by
      funext s
      by_cases hs : s ∈ Ioo σ (σ + 1)
      · rw [indicator_of_mem hs]
        have e1 : eLpNorm (fun z => g (s, z)) 2 (volume.restrict (B0579.cell c)) =
            ENNReal.ofReal ‖ug s‖ :=
          (eLpNorm_congr_ae (hg_sl s hs)).trans (cellL2_coe_eq_ofReal_norm (ug s))
        have e2 : eLpNorm (fun z => G (s, z)) 2 (volume.restrict (B0579.cell c)) =
            ENNReal.ofReal ‖uG s‖ :=
          (eLpNorm_congr_ae (hG_sl s hs)).trans (cellL2_coe_eq_ofReal_norm (uG s))
        rw [e1, e2]
      · rw [indicator_of_notMem hs]
        have hg0 : (fun z => g (s, z)) = 0 := funext fun z => hg_out (s, z) hs
        have hG0 : (fun z => G (s, z)) = 0 := funext fun z => hG_out (s, z) hs
        simp [hg0, hG0]
    have hm1 : Measurable (fun t : ℝ => ENNReal.ofReal ‖ug t‖) :=
      ENNReal.measurable_ofReal.comp hug_sm.norm.measurable
    calc (∫⁻ s in Icc a b,
            (eLpNorm (fun z => g (s, z)) 2 (volume.restrict (B0579.cell c)) +
              eLpNorm (fun z => G (s, z)) 2 (volume.restrict (B0579.cell c))))
        ≤ ∫⁻ s, (Ioo σ (σ + 1)).indicator
            (fun t => ENNReal.ofReal ‖ug t‖ + ENNReal.ofReal ‖uG t‖) s := by
          rw [hind_eq]
          exact setLIntegral_le_lintegral _ _
      _ = (∫⁻ t in Ioo σ (σ + 1), ENNReal.ofReal ‖ug t‖) +
            (∫⁻ t in Ioo σ (σ + 1), ENNReal.ofReal ‖uG t‖) := by
          rw [lintegral_indicator measurableSet_Ioo, lintegral_add_left hm1]
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hug_l1, huG_l1⟩
  · filter_upwards [hwk] with s hs_wk _hs_pos k
    by_cases hs : s ∈ Ioo σ (σ + 1)
    · exact hasWeakCellDerivC_congr
        ((hg_sl s hs).symm.mono fun _ h => congrArg (· k) h)
        ((hG_sl s hs).symm.mono fun _ h => congrArg (· k) h)
        (hs_wk hs k)
    · have hg0 : (fun z => g (s, z) k) = fun _ => 0 :=
        funext fun z => by simp [hg_out (s, z) hs]
      have hG0 : (fun z => G (s, z) k) = fun _ => 0 :=
        funext fun z => by simp [hG_out (s, z) hs]
      rw [hg0, hG0]
      exact ⟨fun _ _ => ⟨by simp, by simp⟩, fun _ _ => by simp⟩

end UnforcedLeray.Short.IIb.UnitDuhamelStepAux

/-! ## 2. Proof of `CylUnitDuhamelStep` -/

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Short.IIb.UnitDuhamelStepAux
open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem cylUnitDuhamelStep_proof : UnforcedLeray.Short.IIb.CylUnitDuhamelStep := by
  intro A hA dm dp p d hreg _hν_le hflow σ hσ
    u₀ uq₀ uη₀ g₁ gq₁ gη₁ hu₀ hg₁_sm hgq₁_sm hgη₁_sm hg₁_per hgq₁_per hgη₁_per hg_ae hint_g
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨fp, hfp_sm, hfp_mem, hfp_supp, hfp_le, hfp_ae⟩ :=
    exists_clean_forcingPath hg₁_sm hgq₁_sm hgη₁_sm hg_ae
  have hfp_int := (integrable_h1RealNorm_of_forcingPath hfp_sm hfp_supp hfp_le hint_g).1
  let x0 : X3 p.c := datumToX3 hu₀
  have hx0 : x0 ∈ H1Set p.c := datumToX3_mem_H1Set hu₀
  let WP : ℝ → X3 p.c := WPath hflow σ x0 fp
  have hWP_sm : StronglyMeasurable WP :=
    stronglyMeasurable_WPath hA hreg hflow hσ hx0 hfp_sm hfp_mem
  have hWP1_sm : StronglyMeasurable (fun t => (WP t).1) :=
    (ContinuousLinearMap.fst ℝ (L2Cell p.c) (L2Cell p.c × L2Cell p.c)).continuous.comp_stronglyMeasurable hWP_sm
  have hWP21_sm : StronglyMeasurable (fun t => (WP t).2.1) :=
    ((ContinuousLinearMap.fst ℝ (L2Cell p.c) (L2Cell p.c)).comp
      (ContinuousLinearMap.snd ℝ (L2Cell p.c) (L2Cell p.c × L2Cell p.c))).continuous.comp_stronglyMeasurable hWP_sm
  have hWP22_sm : StronglyMeasurable (fun t => (WP t).2.2) :=
    ((ContinuousLinearMap.snd ℝ (L2Cell p.c) (L2Cell p.c)).comp
      (ContinuousLinearMap.snd ℝ (L2Cell p.c) (L2Cell p.c × L2Cell p.c))).continuous.comp_stronglyMeasurable hWP_sm
  obtain ⟨hWP_l1, hd2_all⟩ :=
    stronglyMeasurable_and_locL1_d2Path hA hreg hflow hσ hx0 hfp_sm hfp_mem hfp_int
  have hWP1_l1 : (∫⁻ t in Ioo σ (σ + 1), ENNReal.ofReal ‖(WP t).1‖) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun t => ?_) hWP_l1
    rw [← cellL2_coe_eq_ofReal_norm]
    exact le_self_add.trans le_self_add
  have hWP21_l1 : (∫⁻ t in Ioo σ (σ + 1), ENNReal.ofReal ‖(WP t).2.1‖) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun t => ?_) hWP_l1
    rw [← cellL2_coe_eq_ofReal_norm]
    exact le_add_self.trans le_self_add
  have hWP22_l1 : (∫⁻ t in Ioo σ (σ + 1), ENNReal.ofReal ‖(WP t).2.2‖) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun t => ?_) hWP_l1
    rw [← cellL2_coe_eq_ofReal_norm]
    exact le_add_self
  obtain ⟨w, hw_sm, hw_per, hw_sl, hw_out⟩ := exists_window_cprof p.c_pos hσ hWP1_sm
  obtain ⟨wq, hwq_sm, hwq_per, hwq_sl, hwq_out⟩ := exists_window_cprof p.c_pos hσ hWP21_sm
  obtain ⟨wη, hwη_sm, hwη_per, hwη_sl, hwη_out⟩ := exists_window_cprof p.c_pos hσ hWP22_sm
  have hex_D2 : ∀ i j : Fin 2, ∃ Dij : CProf,
      StronglyMeasurable Dij ∧ QPeriodic p.c Dij ∧
      (∀ t ∈ Ioo σ (σ + 1), F8U.slice Dij t =ᵐ[F8Sm.cellMeas p.c] d2Path hflow σ x0 fp i j t) ∧
      (∀ x : Coord, x.1 ∉ Ioo σ (σ + 1) → Dij x = 0) :=
    fun i j => exists_window_cprof p.c_pos hσ (hd2_all i j).1
  choose D2 hD2_spec using fun i => fun j => hex_D2 i j
  have hD2_sm : ∀ i j, StronglyMeasurable (D2 i j) := fun i j => (hD2_spec i j).1
  have hD2_per : ∀ i j, QPeriodic p.c (D2 i j) := fun i j => (hD2_spec i j).2.1
  have hD2_sl : ∀ i j, ∀ t ∈ Ioo σ (σ + 1),
      F8U.slice (D2 i j) t =ᵐ[F8Sm.cellMeas p.c] d2Path hflow σ x0 fp i j t :=
    fun i j => (hD2_spec i j).2.2.1
  have hD2_out : ∀ i j, ∀ x : Coord, x.1 ∉ Ioo σ (σ + 1) → D2 i j x = 0 :=
    fun i j => (hD2_spec i j).2.2.2
  have hWP_H1 : ∀ t ∈ Ioo σ (σ + 1),
      WP t ∈ H1Set p.c ∧
        h1ENN (WP t) ≤
          ENNReal.ofReal A *
            (F8U.cylH1 p.c u₀ uq₀ uη₀ + ∫⁻ τ in Ioc σ t, sliceH1Norm p.c g₁ gq₁ gη₁ τ) :=
    fun t ht => WPath_mem_H1Set_and_bound hA hreg hflow hσ hu₀ hfp_sm hfp_mem hfp_le hfp_int ht
  have hw_dat : ∀ t ∈ Ioo σ (σ + 1),
      F8U.IsCylH1Datum p.c (F8U.slice w t) (F8U.slice wq t) (F8U.slice wη t) ∧
        F8U.cylH1 p.c (F8U.slice w t) (F8U.slice wq t) (F8U.slice wη t) ≤
          ENNReal.ofReal A *
            (F8U.cylH1 p.c u₀ uq₀ uη₀ + ∫⁻ τ in Ioc σ t, sliceH1Norm p.c g₁ gq₁ gη₁ τ) := by
    intro t ht
    obtain ⟨hmem, hbd⟩ := hWP_H1 t ht
    refine ⟨isCylH1Datum_congr (hw_sl t ht).symm (hwq_sl t ht).symm (hwη_sl t ht).symm hmem, ?_⟩
    have heq_h1 : F8U.cylH1 p.c (F8U.slice w t) (F8U.slice wq t) (F8U.slice wη t) = h1ENN (WP t) := by
      unfold h1ENN F8U.cylH1 F8U.cellL2
      rw [eLpNorm_congr_ae (hw_sl t ht), eLpNorm_congr_ae (hwq_sl t ht),
        eLpNorm_congr_ae (hwη_sl t ht)]
    exact heq_h1.trans_le hbd
  have hae_d2 := ae_weakD2_and_bound_d2Path hA hreg hflow hσ hu₀ hfp_sm hfp_mem hfp_le hfp_int
  refine ⟨w, wq, wη, D2, hw_sm, hwq_sm, hwη_sm, hD2_sm, hw_per, hwq_per, hwη_per, hD2_per,
    hw_dat, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Interior `H¹` continuity on `Ioo σ (σ + 1)`
    intro t ht
    have hlim_real := tendsto_WPath_interior hA hreg hflow hσ hx0 hfp_sm hfp_mem hfp_int ht
    have hlim_enn : Tendsto (fun t' => ENNReal.ofReal (h1RealNorm (WP t' - WP t))) (𝓝 t) (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim_real
    refine hlim_enn.congr' ?_
    filter_upwards [isOpen_Ioo.mem_nhds ht] with t' ht'
    rw [← h1ENN_eq_ofReal]
    unfold h1ENN F8U.cylH1 F8U.cellL2
    have e1 : ((WP t' - WP t).1 : B0579.Plane → CMerid) =ᵐ[F8Sm.cellMeas p.c]
        fun y => w (t', y) - w (t, y) := by
      filter_upwards [Lp.coeFn_sub (WP t').1 (WP t).1, hw_sl t' ht', hw_sl t ht]
        with y hsub h1 h2
      simp only [Pi.sub_apply] at hsub
      change ((WP t').1 - (WP t).1) y = F8U.slice w t' y - F8U.slice w t y
      rw [hsub, h1, h2]
    have e2 : ((WP t' - WP t).2.1 : B0579.Plane → CMerid) =ᵐ[F8Sm.cellMeas p.c]
        fun y => wq (t', y) - wq (t, y) := by
      filter_upwards [Lp.coeFn_sub (WP t').2.1 (WP t).2.1, hwq_sl t' ht', hwq_sl t ht]
        with y hsub h1 h2
      simp only [Pi.sub_apply] at hsub
      change ((WP t').2.1 - (WP t).2.1) y = F8U.slice wq t' y - F8U.slice wq t y
      rw [hsub, h1, h2]
    have e3 : ((WP t' - WP t).2.2 : B0579.Plane → CMerid) =ᵐ[F8Sm.cellMeas p.c]
        fun y => wη (t', y) - wη (t, y) := by
      filter_upwards [Lp.coeFn_sub (WP t').2.2 (WP t).2.2, hwη_sl t' ht', hwη_sl t ht]
        with y hsub h1 h2
      simp only [Pi.sub_apply] at hsub
      change ((WP t').2.2 - (WP t).2.2) y = F8U.slice wη t' y - F8U.slice wη t y
      rw [hsub, h1, h2]
    rw [eLpNorm_congr_ae e1, eLpNorm_congr_ae e2, eLpNorm_congr_ae e3]
  · -- Initial `H¹` right-continuity at `σ⁺`
    have hlim_real := tendsto_WPath_initial hA hreg hflow hσ hx0 hfp_sm hfp_mem hfp_int
    have hlim_enn : Tendsto (fun t => ENNReal.ofReal (h1RealNorm (WP t - x0))) (𝓝[>] σ) (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim_real
    refine hlim_enn.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (by linarith : σ < σ + 1)] with t ht
    rw [← h1ENN_eq_ofReal]
    unfold h1ENN F8U.cylH1 F8U.cellL2
    have e1 : ((WP t - x0).1 : B0579.Plane → CMerid) =ᵐ[F8Sm.cellMeas p.c]
        fun y => w (t, y) - u₀ y := by
      filter_upwards [Lp.coeFn_sub (WP t).1 x0.1, hw_sl t ht, hu₀.memL2.1.coeFn_toLp]
        with y hsub h1 h2
      simp only [Pi.sub_apply] at hsub
      change ((WP t).1 - x0.1) y = F8U.slice w t y - u₀ y
      rw [hsub, h1]; dsimp only [x0, datumToX3]; rw [h2]
    have e2 : ((WP t - x0).2.1 : B0579.Plane → CMerid) =ᵐ[F8Sm.cellMeas p.c]
        fun y => wq (t, y) - uq₀ y := by
      filter_upwards [Lp.coeFn_sub (WP t).2.1 x0.2.1, hwq_sl t ht, hu₀.memL2.2.1.coeFn_toLp]
        with y hsub h1 h2
      simp only [Pi.sub_apply] at hsub
      change ((WP t).2.1 - x0.2.1) y = F8U.slice wq t y - uq₀ y
      rw [hsub, h1]; dsimp only [x0, datumToX3]; rw [h2]
    have e3 : ((WP t - x0).2.2 : B0579.Plane → CMerid) =ᵐ[F8Sm.cellMeas p.c]
        fun y => wη (t, y) - uη₀ y := by
      filter_upwards [Lp.coeFn_sub (WP t).2.2 x0.2.2, hwη_sl t ht, hu₀.memL2.2.2.coeFn_toLp]
        with y hsub h1 h2
      simp only [Pi.sub_apply] at hsub
      change ((WP t).2.2 - x0.2.2) y = F8U.slice wη t y - uη₀ y
      rw [hsub, h1]; dsimp only [x0, datumToX3]; rw [h2]
    rw [eLpNorm_congr_ae e1, eLpNorm_congr_ae e2, eLpNorm_congr_ae e3]
  · -- `HasWeakVecOnIoo σ (σ + 1) vQ0 dZero w wq`
    exact weakVecOnIoo_of_window_cprof p.c_pos 0 hw_sm hwq_sm hw_per hwq_per
      hw_sl hwq_sl hw_out hwq_out hWP1_sm hWP1_l1 hWP21_l1
      (Eventually.of_forall fun t ht k => (hWP_H1 t ht).1.weak_q k)
  · -- `HasWeakVecOnIoo σ (σ + 1) vEta dZero w wη`
    exact weakVecOnIoo_of_window_cprof p.c_pos 1 hw_sm hwη_sm hw_per hwη_per
      hw_sl hwη_sl hw_out hwη_out hWP1_sm hWP1_l1 hWP22_l1
      (Eventually.of_forall fun t ht k => (hWP_H1 t ht).1.weak_eta k)
  · -- `HasWeakVecOnIoo σ (σ + 1) vQ0 dZero wq (D2 0 0)`
    exact weakVecOnIoo_of_window_cprof p.c_pos 0 hwq_sm (hD2_sm 0 0) hwq_per (hD2_per 0 0)
      hwq_sl (hD2_sl 0 0) hwq_out (hD2_out 0 0) hWP21_sm hWP21_l1 (hd2_all 0 0).2
      (hae_d2.mono fun t ht hmem k => (ht hmem).1 0 k)
  · -- `HasWeakVecOnIoo σ (σ + 1) vEta dZero wq (D2 0 1)`
    exact weakVecOnIoo_of_window_cprof p.c_pos 1 hwq_sm (hD2_sm 0 1) hwq_per (hD2_per 0 1)
      hwq_sl (hD2_sl 0 1) hwq_out (hD2_out 0 1) hWP21_sm hWP21_l1 (hd2_all 0 1).2
      (hae_d2.mono fun t ht hmem k => (ht hmem).1 1 k)
  · -- `HasWeakVecOnIoo σ (σ + 1) vQ0 dZero wη (D2 1 0)`
    exact weakVecOnIoo_of_window_cprof p.c_pos 0 hwη_sm (hD2_sm 1 0) hwη_per (hD2_per 1 0)
      hwη_sl (hD2_sl 1 0) hwη_out (hD2_out 1 0) hWP22_sm hWP22_l1 (hd2_all 1 0).2
      (hae_d2.mono fun t ht hmem k => (ht hmem).2.1 0 k)
  · -- `HasWeakVecOnIoo σ (σ + 1) vEta dZero wη (D2 1 1)`
    exact weakVecOnIoo_of_window_cprof p.c_pos 1 hwη_sm (hD2_sm 1 1) hwη_per (hD2_per 1 1)
      hwη_sl (hD2_sl 1 1) hwη_out (hD2_out 1 1) hWP22_sm hWP22_l1 (hd2_all 1 1).2
      (hae_d2.mono fun t ht hmem k => (ht hmem).2.1 1 k)
  · -- Weak solenoidality on `(σ, σ + 1) × ℝ²`
    intro φ hφ
    obtain ⟨a, b, R, ha, hab, hR, hbox⟩ := TailPeriodizeAux.coordTest_box hφ.1
    have hwi_meas : ∀ i : Fin 2, AEStronglyMeasurable (fun x : Coord => w x i) volume := fun i =>
      ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
        hw_sm).aestronglyMeasurable
    have hwi_per : ∀ i : Fin 2, ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
        w (qShift p.c x) i = w x i :=
      fun i => hw_per.mono fun _ hx => congrArg (fun v : CMerid => v i) hx
    have hw_loc : ∀ i : Fin 2, (∫⁻ s in Icc a b,
        eLpNorm (fun z => w (s, z) i) 2 (volume.restrict (B0579.cell p.c))) < ⊤ := by
      intro i
      have hind : (fun s : ℝ => eLpNorm (fun z => w (s, z)) 2 (volume.restrict (B0579.cell p.c))) =
          (Ioo σ (σ + 1)).indicator (fun t => ENNReal.ofReal ‖(WP t).1‖) := by
        funext s
        by_cases hs : s ∈ Ioo σ (σ + 1)
        · rw [indicator_of_mem hs]
          exact (eLpNorm_congr_ae (hw_sl s hs)).trans (cellL2_coe_eq_ofReal_norm (WP s).1)
        · rw [indicator_of_notMem hs]
          have hw0 : (fun z => w (s, z)) = 0 := funext fun z => hw_out (s, z) hs
          simp [hw0]
      calc (∫⁻ s in Icc a b, eLpNorm (fun z => w (s, z) i) 2 (volume.restrict (B0579.cell p.c)))
          ≤ ∫⁻ s in Icc a b, eLpNorm (fun z => w (s, z)) 2 (volume.restrict (B0579.cell p.c)) :=
            lintegral_mono fun s => eLpNorm_comp_le_merid p.c w s i
        _ ≤ ∫⁻ s, (Ioo σ (σ + 1)).indicator (fun t => ENNReal.ofReal ‖(WP t).1‖) s := by
            rw [hind]; exact setLIntegral_le_lintegral _ _
        _ = ∫⁻ t in Ioo σ (σ + 1), ENNReal.ofReal ‖(WP t).1‖ :=
            lintegral_indicator measurableSet_Ioo _
        _ < ⊤ := hWP1_l1
    have hcpd1_cont : Continuous (cpd 1 φ) :=
      (((contDiff_infty_iff_fderiv.1 hφ.1.smooth).2).clm_apply contDiff_const).continuous
    have hcpd2_cont : Continuous (cpd 2 φ) :=
      (((contDiff_infty_iff_fderiv.1 hφ.1.smooth).2).clm_apply contDiff_const).continuous
    obtain ⟨hint0, hcell0, heq0⟩ :=
      TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize p.c_pos ha hab hR
        (hwi_meas 0) (hwi_per 0) (hw_loc 0) hcpd1_cont (fun x hx => (hbox x hx).2 1)
    obtain ⟨hint1, hcell1, heq1⟩ :=
      TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize p.c_pos ha hab hR
        (hwi_meas 1) (hwi_per 1) (hw_loc 1) hcpd2_cont (fun x hx => (hbox x hx).2 2)
    obtain ⟨hs_int0, hz_int0⟩ := fubini_cell_slices hcell0
    obtain ⟨hs_int1, hz_int1⟩ := fubini_cell_slices hcell1
    dsimp only at hs_int0 hs_int1 hz_int0 hz_int1
    refine ⟨hint0.add hint1, ?_⟩
    rw [integral_add hint0 hint1, heq0, heq1, ← integral_add hs_int0 hs_int1]
    refine (integral_congr_ae (g := fun _ => (0 : ℂ)) ?_).trans (by simp)
    filter_upwards [hz_int0, hz_int1] with s hi0 hi1
    rw [← integral_add hi0 hi1]
    have hpd0 : (fun z => TailPeriodizeAux.qPeriodize p.c (cpd 1 φ) s z) =
        B0579.pd 0 (TailPeriodizeAux.qPeriodize p.c φ s) :=
      funext fun z => (TailPeriodizeAux.pd_qPeriodize p.c_pos hφ.1 s 0 z).symm
    have hpd1 : (fun z => TailPeriodizeAux.qPeriodize p.c (cpd 2 φ) s z) =
        B0579.pd 1 (TailPeriodizeAux.qPeriodize p.c φ s) :=
      funext fun z => (TailPeriodizeAux.pd_qPeriodize p.c_pos hφ.1 s 1 z).symm
    simp_rw [hpd0, hpd1]
    by_cases hs : s ∈ Ioo σ (σ + 1)
    · exact ((hw_dat s hs).1.solenoidal
        (TailPeriodizeAux.qPeriodize p.c φ s)
        (TailPeriodizeAux.isCylTest_qPeriodize p.c_pos hφ.1 s)).2
    · have hz : (fun z : B0579.Plane =>
          w (s, z) 0 * (B0579.pd 0 (TailPeriodizeAux.qPeriodize p.c φ s) z : ℂ) +
          w (s, z) 1 * (B0579.pd 1 (TailPeriodizeAux.qPeriodize p.c φ s) z : ℂ)) =
          fun _ => 0 :=
        funext fun z => by simp [hw_out (s, z) hs]
      rw [hz, integral_zero]
  · -- Forced weak equation against planar solenoidal tests supported in `Ioo σ (σ + 1) × ℝ²`
    intro Ψ hΨ hΨ_supp
    obtain ⟨a'', a', b', b'', R, ha'', ha', hab', hb', hb'', hR, hΨ_tsupp⟩ :=
      planarSolTest_Ioo_box hΨ hΨ_supp
    have ha''_pos : 0 < a'' := lt_of_le_of_lt hσ ha''
    have hab'' : a'' ≤ b'' := (ha'.le.trans hab').trans hb'.le
    have hsub_ioo : Icc a'' b'' ⊆ Ioo σ (σ + 1) :=
      fun s hs => ⟨lt_of_lt_of_le ha'' hs.1, lt_of_le_of_lt hs.2 hb''⟩
    have hsub_ioc : Icc a'' b'' ⊆ Ioc σ (σ + 1) :=
      fun s hs => ⟨(hsub_ioo hs).1, (hsub_ioo hs).2.le⟩
    have hnot_tsupp : ∀ (i : Fin 2) (x : Coord),
        (x.1 ∉ Icc a'' b'' ∨ R < |x.2.1| ∨ R < |x.2.2|) →
          x ∉ tsupport (fun y => Ψ y i) := by
      intro i x hx
      refine hΨ_tsupp i x ?_
      rcases hx with h1 | h2 | h3
      · exact Or.inl fun hm => h1 ⟨ha'.le.trans hm.1, hm.2.trans hb'.le⟩
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h3)
    have hΨ_box : ∀ (i : Fin 2) (x : Coord),
        (x.1 ∉ Icc a'' b'' ∨ R < |x.2.1| ∨ R < |x.2.2|) → Ψ x i = 0 :=
      fun i x hx => (vanish_derivs_of_notMem_tsupport (hnot_tsupp i x hx)).1
    have hMT_box : ∀ (i : Fin 2) (x : Coord),
        (x.1 ∉ Icc a'' b'' ∨ R < |x.2.1| ∨ R < |x.2.2|) → mtReal p.ν Ψ x i = 0 := by
      intro i x hx
      obtain ⟨_, h1, h2⟩ := vanish_derivs_of_notMem_tsupport (hnot_tsupp i x hx)
      simp [mtReal, h1 0, h2 1 1, h2 2 2]
    let U : CProf := flatBv p.train w wq wη
    obtain ⟨hU_sm, hU_per, _⟩ :=
      flatBv_window_meas_and_per p hσ hw_sm hwq_sm hwη_sm hw_per hwq_per hwη_per
        hw_out hwq_out hwη_out
    have hwi_meas : ∀ i : Fin 2, AEStronglyMeasurable (fun x : Coord => w x i) volume := fun i =>
      ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
        hw_sm).aestronglyMeasurable
    have hUi_meas : ∀ i : Fin 2, AEStronglyMeasurable (fun x : Coord => U x i) volume := fun i =>
      ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
        hU_sm).aestronglyMeasurable
    have hgi_meas : ∀ i : Fin 2, AEStronglyMeasurable (fun x : Coord => g₁ x i) volume := fun i =>
      ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
        hg₁_sm).aestronglyMeasurable
    have hwi_per : ∀ i : Fin 2, ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
        w (qShift p.c x) i = w x i :=
      fun i => hw_per.mono fun _ hx => congrArg (fun v : CMerid => v i) hx
    have hUi_per : ∀ i : Fin 2, ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
        U (qShift p.c x) i = U x i :=
      fun i => hU_per.mono fun _ hx => congrArg (fun v : CMerid => v i) hx
    have hgi_per : ∀ i : Fin 2, ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
        g₁ (qShift p.c x) i = g₁ x i :=
      fun i => hg₁_per.mono fun _ hx => congrArg (fun v : CMerid => v i) hx
    -- Local `L¹_s([a'', b'']; L²(cell))` bounds for `w`, `U`, and `g₁`
    have hw_loc : ∀ i : Fin 2, (∫⁻ s in Icc a'' b'',
        eLpNorm (fun z => w (s, z) i) 2 (volume.restrict (B0579.cell p.c))) < ⊤ := by
      intro i
      have hle : ∀ s ∈ Icc a'' b'',
          eLpNorm (fun z => w (s, z) i) 2 (volume.restrict (B0579.cell p.c)) ≤ h1ENN (WP s) := by
        intro s hs
        calc eLpNorm (fun z => w (s, z) i) 2 (volume.restrict (B0579.cell p.c))
            ≤ eLpNorm (fun z => w (s, z)) 2 (volume.restrict (B0579.cell p.c)) :=
              eLpNorm_comp_le_merid p.c w s i
          _ = F8U.cellL2 p.c (WP s).1 := eLpNorm_congr_ae (hw_sl s (hsub_ioo hs))
          _ ≤ h1ENN (WP s) := le_self_add.trans le_self_add
      exact lt_of_le_of_lt
        ((setLIntegral_mono' measurableSet_Icc hle).trans
          (lintegral_mono_set (μ := volume) hsub_ioo))
        hWP_l1
    obtain ⟨M_tr, hM_tr, hV_s, _, hb0_tr, hb1_tr⟩ :=
      uniform_train_C1 hreg (T := b'' + 1) (by linarith)
    have hU_slice_ae : ∀ s ∈ Icc a'' b'',
        (fun z => U (s, z)) =ᵐ[F8Sm.cellMeas p.c]
          bvTripleSlice (p.train.v s) (WP s).1 (WP s).2.1 (WP s).2.2 := by
      intro s hs
      have hs_ioo := hsub_ioo hs
      filter_upwards [hw_sl s hs_ioo, hwq_sl s hs_ioo, hwη_sl s hs_ioo] with z hz hqz hηz
      change bvTripleSlice (p.train.v s) (F8U.slice w s) (F8U.slice wq s) (F8U.slice wη s) z = _
      dsimp only [bvTripleSlice]
      rw [hz, hqz, hηz]
    have hU_loc : ∀ i : Fin 2, (∫⁻ s in Icc a'' b'',
        eLpNorm (fun z => U (s, z) i) 2 (volume.restrict (B0579.cell p.c))) < ⊤ := by
      intro i
      have hle : ∀ s ∈ Icc a'' b'',
          eLpNorm (fun z => U (s, z) i) 2 (volume.restrict (B0579.cell p.c)) ≤
            ENNReal.ofReal (4 * M_tr) * h1ENN (WP s) := by
        intro s hs
        have hs_icc : s ∈ Icc (0 : ℝ) (b'' + 1) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
        obtain ⟨hm_bv, hbv_le⟩ := memLp_and_cellL2_bvTripleSlice hM_tr (hV_s s hs_icc)
          (hb0_tr s hs_icc) (hb1_tr s hs_icc)
          (Lp.memLp (WP s).1) (Lp.memLp (WP s).2.1) (Lp.memLp (WP s).2.2)
        have htr : ∀ u : L2Cell p.c, (F8U.cellL2 p.c u).toReal = ‖u‖ := fun u => by
          rw [cellL2_coe_eq_ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg u)]
        rw [htr (WP s).1, htr (WP s).2.1, htr (WP s).2.2] at hbv_le
        have hreal_bd :
            (F8U.cellL2 p.c (bvTripleSlice (p.train.v s) (WP s).1 (WP s).2.1 (WP s).2.2)).toReal ≤
              (4 * M_tr) * h1RealNorm (WP s) := by
          refine hbv_le.trans ?_
          unfold h1RealNorm
          nlinarith [norm_nonneg (WP s).1, norm_nonneg (WP s).2.1, norm_nonneg (WP s).2.2]
        calc eLpNorm (fun z => U (s, z) i) 2 (volume.restrict (B0579.cell p.c))
            ≤ eLpNorm (fun z => U (s, z)) 2 (volume.restrict (B0579.cell p.c)) :=
              eLpNorm_comp_le_merid p.c U s i
          _ = F8U.cellL2 p.c (bvTripleSlice (p.train.v s) (WP s).1 (WP s).2.1 (WP s).2.2) :=
              eLpNorm_congr_ae (hU_slice_ae s hs)
          _ = ENNReal.ofReal
                (F8U.cellL2 p.c (bvTripleSlice (p.train.v s) (WP s).1 (WP s).2.1 (WP s).2.2)).toReal :=
              (ENNReal.ofReal_toReal hm_bv.eLpNorm_ne_top).symm
          _ ≤ ENNReal.ofReal ((4 * M_tr) * h1RealNorm (WP s)) :=
              ENNReal.ofReal_le_ofReal hreal_bd
          _ = ENNReal.ofReal (4 * M_tr) * h1ENN (WP s) := by
              rw [ENNReal.ofReal_mul (by positivity), h1ENN_eq_ofReal]
      calc (∫⁻ s in Icc a'' b'',
              eLpNorm (fun z => U (s, z) i) 2 (volume.restrict (B0579.cell p.c)))
          ≤ ∫⁻ s in Icc a'' b'', ENNReal.ofReal (4 * M_tr) * h1ENN (WP s) :=
            setLIntegral_mono' measurableSet_Icc hle
        _ = ENNReal.ofReal (4 * M_tr) * ∫⁻ s in Icc a'' b'', h1ENN (WP s) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (4 * M_tr) * ∫⁻ s in Ioo σ (σ + 1), h1ENN (WP s) :=
            mul_le_mul_right (lintegral_mono_set (μ := volume) hsub_ioo) _
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hWP_l1
    have hg_loc : ∀ i : Fin 2, (∫⁻ s in Icc a'' b'',
        eLpNorm (fun z => g₁ (s, z) i) 2 (volume.restrict (B0579.cell p.c))) < ⊤ := by
      intro i
      have hle : ∀ s, eLpNorm (fun z => g₁ (s, z) i) 2 (volume.restrict (B0579.cell p.c)) ≤
          sliceH1Norm p.c g₁ gq₁ gη₁ s :=
        fun s => (eLpNorm_comp_le_merid p.c g₁ s i).trans (le_self_add.trans le_self_add)
      exact lt_of_le_of_lt
        ((lintegral_mono hle).trans (lintegral_mono_set (μ := volume) hsub_ioc))
        hint_g
    -- Disintegrate `w · mtReal`, `U · Ψ`, and `g₁ · Ψ` via `qPeriodize`
    have hMT_cont : ∀ i : Fin 2, Continuous (fun x : Coord => mtReal p.ν Ψ x i) :=
      fun i => (isCoordTest_mtReal p.ν hΨ i).smooth.continuous
    have hΨ_cont : ∀ i : Fin 2, Continuous (fun x : Coord => Ψ x i) :=
      fun i => (hΨ.smooth i).smooth.continuous
    obtain ⟨hw0_int, hw0_cell, hw0_eq⟩ :=
      TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize p.c_pos ha''_pos hab'' hR
        (hwi_meas 0) (hwi_per 0) (hw_loc 0) (hMT_cont 0) (hMT_box 0)
    obtain ⟨hw1_int, hw1_cell, hw1_eq⟩ :=
      TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize p.c_pos ha''_pos hab'' hR
        (hwi_meas 1) (hwi_per 1) (hw_loc 1) (hMT_cont 1) (hMT_box 1)
    obtain ⟨hU0_int, hU0_cell, hU0_eq⟩ :=
      TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize p.c_pos ha''_pos hab'' hR
        (hUi_meas 0) (hUi_per 0) (hU_loc 0) (hΨ_cont 0) (hΨ_box 0)
    obtain ⟨hU1_int, hU1_cell, hU1_eq⟩ :=
      TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize p.c_pos ha''_pos hab'' hR
        (hUi_meas 1) (hUi_per 1) (hU_loc 1) (hΨ_cont 1) (hΨ_box 1)
    obtain ⟨hg0_int, hg0_cell, hg0_eq⟩ :=
      TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize p.c_pos ha''_pos hab'' hR
        (hgi_meas 0) (hgi_per 0) (hg_loc 0) (hΨ_cont 0) (hΨ_box 0)
    obtain ⟨hg1_int, hg1_cell, hg1_eq⟩ :=
      TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize p.c_pos ha''_pos hab'' hR
        (hgi_meas 1) (hgi_per 1) (hg_loc 1) (hΨ_cont 1) (hΨ_box 1)
    have hmt_sum_fn : (fun x : Coord => ∑ i : Fin 2, w x i * meridTranspose p.ν Ψ x i) =
        fun x => w x 0 * (mtReal p.ν Ψ x 0 : ℂ) + w x 1 * (mtReal p.ν Ψ x 1 : ℂ) := by
      funext x
      rw [Fin.sum_univ_two, meridTranspose_eq_ofReal_mtReal, meridTranspose_eq_ofReal_mtReal]
    have hcdot_U : cdot U Ψ = fun x => U x 0 * (Ψ x 0 : ℂ) + U x 1 * (Ψ x 1 : ℂ) := by
      funext x; unfold cdot; rw [Fin.sum_univ_two]
    have hcdot_g : cdot g₁ Ψ = fun x => g₁ x 0 * (Ψ x 0 : ℂ) + g₁ x 1 * (Ψ x 1 : ℂ) := by
      funext x; unfold cdot; rw [Fin.sum_univ_two]
    have hint_w_mt : Integrable (fun x => ∑ i : Fin 2, w x i * meridTranspose p.ν Ψ x i) volume :=
      hmt_sum_fn ▸ (hw0_int.add hw1_int)
    have hint_U_Ψ : Integrable (cdot U Ψ) volume := hcdot_U ▸ (hU0_int.add hU1_int)
    have hint_g_Ψ : Integrable (cdot g₁ Ψ) volume := hcdot_g ▸ (hg0_int.add hg1_int)
    refine ⟨hint_w_mt, hint_U_Ψ, hint_g_Ψ, ?_⟩
    have hws0 := (fubini_cell_slices hw0_cell).1
    have hws1 := (fubini_cell_slices hw1_cell).1
    have hUs0 := (fubini_cell_slices hU0_cell).1
    have hUs1 := (fubini_cell_slices hU1_cell).1
    have hgs0 := (fubini_cell_slices hg0_cell).1
    have hgs1 := (fubini_cell_slices hg1_cell).1
    dsimp only at hws0 hws1 hUs0 hUs1 hgs0 hgs1
    have hws_sum : IntegrableOn (fun s =>
        (∫ z in B0579.cell p.c,
          w (s, z) 0 * (TailPeriodizeAux.qPeriodize p.c (fun x => mtReal p.ν Ψ x 0) s z : ℂ)) +
        (∫ z in B0579.cell p.c,
          w (s, z) 1 * (TailPeriodizeAux.qPeriodize p.c (fun x => mtReal p.ν Ψ x 1) s z : ℂ)))
        (Icc a'' b'') volume := hws0.add hws1
    have hUs_sum : IntegrableOn (fun s =>
        (∫ z in B0579.cell p.c,
          U (s, z) 0 * (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x 0) s z : ℂ)) +
        (∫ z in B0579.cell p.c,
          U (s, z) 1 * (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x 1) s z : ℂ)))
        (Icc a'' b'') volume := hUs0.add hUs1
    have hlhs_coord :
        (∫ x, (∑ i : Fin 2, w x i * meridTranspose p.ν Ψ x i + cdot U Ψ x)) =
          ∫ s in Icc a'' b'', sliceLHSVal p Ψ s (WP s) := by
      rw [integral_add hint_w_mt hint_U_Ψ, hmt_sum_fn, hcdot_U,
        integral_add hw0_int hw1_int, integral_add hU0_int hU1_int,
        hw0_eq, hw1_eq, hU0_eq, hU1_eq,
        ← integral_add hws0 hws1, ← integral_add hUs0 hUs1,
        ← integral_add hws_sum hUs_sum]
      refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      have hs_ioo := hsub_ioo hs
      have ew : ∀ i : Fin 2,
          (∫ z in B0579.cell p.c,
            w (s, z) i * (TailPeriodizeAux.qPeriodize p.c (fun x => mtReal p.ν Ψ x i) s z : ℂ)) =
          ∫ z in B0579.cell p.c,
            (WP s).1 z i * (TailPeriodizeAux.qPeriodize p.c (fun x => mtReal p.ν Ψ x i) s z : ℂ) := by
        intro i
        refine integral_congr_ae ?_
        filter_upwards [hw_sl s hs_ioo] with z hz
        change F8U.slice w s z i * _ = _
        rw [hz]
      have eU : ∀ i : Fin 2,
          (∫ z in B0579.cell p.c,
            U (s, z) i * (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s z : ℂ)) =
          ∫ z in B0579.cell p.c,
            bvTripleSlice (p.train.v s) (WP s).1 (WP s).2.1 (WP s).2.2 z i *
              (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s z : ℂ) := by
        intro i
        refine integral_congr_ae ?_
        filter_upwards [hU_slice_ae s hs] with z hz
        rw [hz]
      unfold sliceLHSVal
      simp only [Fin.sum_univ_two, ew 0, ew 1, eU 0, eU 1]
    have hrhs_coord :
        (∫ x, cdot g₁ Ψ x) =
          ∫ τ in Icc a'' b'', ∑ i : Fin 2, ∫ y in B0579.cell p.c,
            (fp τ).1 y i * (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) τ y : ℂ) := by
      rw [hcdot_g, integral_add hg0_int hg1_int, hg0_eq, hg1_eq, ← integral_add hgs0 hgs1]
      refine setIntegral_congr_ae measurableSet_Icc ?_
      filter_upwards [hfp_ae] with τ hτ hτ_icc
      obtain ⟨hτ1, _, _, _⟩ := hτ (hsub_ioc hτ_icc)
      have eg : ∀ i : Fin 2,
          (∫ y in B0579.cell p.c,
            g₁ (τ, y) i * (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) τ y : ℂ)) =
          ∫ y in B0579.cell p.c,
            (fp τ).1 y i * (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) τ y : ℂ) := by
        intro i
        refine integral_congr_ae ?_
        filter_upwards [hτ1] with y hy
        change F8U.slice g₁ τ y i * _ = _
        rw [hy]
      simp only [Fin.sum_univ_two, eg 0, eg 1]
    rw [hlhs_coord, hrhs_coord]
    exact duhamel_slice_weak_eq hA hreg hflow hσ hx0 hfp_sm hfp_mem hfp_int
      hΨ ha'' ha' hab' hb' hb'' hR hΨ_tsupp
  · -- Almost-everywhere `D²` Duhamel estimate on `Ioo σ (σ + 1)`
    filter_upwards [hae_d2] with t ht hmem
    have heq_ij : ∀ i j : Fin 2,
        F8U.cellL2 p.c (F8U.slice (D2 i j) t) =
          ENNReal.ofReal ‖d2Path hflow σ x0 fp i j t‖ :=
      fun i j => (eLpNorm_congr_ae (hD2_sl i j t hmem)).trans
        (cellL2_coe_eq_ofReal_norm (d2Path hflow σ x0 fp i j t))
    simp only [Fin.sum_univ_two]
    rw [heq_ij 0 0, heq_ij 0 1, heq_ij 1 0, heq_ij 1 1]
    have hbd := (ht hmem).2.2
    simpa only [Fin.sum_univ_two] using hbd

end UnforcedLeray.Short.IIb

end
