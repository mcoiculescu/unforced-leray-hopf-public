import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.Continuation.LinearGlue
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.TailSourceSlice.SliceP0Lift
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.Mollifier
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollIdentity.Bridge
import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2_2.LerayRepH1
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.TailContinuation.AdvectionEnergy
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import UnforcedLeray.Lib.BochnerTime.Energy

/-!
# `TailH1Gronwall`: Differentiated `H¹(C_c)` tail energy Gronwall bound (`PartII-b:F7/2/3`)

Source of record: `the November 2 reference manuscript`
(SP), lines 2054–2057 (`short-bg:train-late`), lines 2213–2217 (`short-bg:body-eq`), and lines
2289–2295 (`short-bg:global-energy`).

Proves `meridionalTailH1Gronwall_proof : UnforcedLeray.Short.IIb.MeridionalTailH1Gronwall`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff RealInnerProductSpace Convolution

namespace UnforcedLeray.Short.IIb

namespace TailH1GronwallAux

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.BochnerTime
open UnforcedLeray.Short.IIIa

/-! ## Section 1: Regime `1 ≤ p.c`, continuous `LMH` slice paths, strain & slice regularity -/

private lemma one_le_c_of_bgRegime {p : Params} {d dm dp : ℝ}
    (hreg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1) : 1 ≤ p.c := by
  have hν_pos : 0 < p.ν := p.ν_pos
  have hsq_pos : 0 < p.ν ^ 2 := sq_pos_of_pos hν_pos
  have hsq_le : p.ν ^ 2 ≤ 1 := by nlinarith
  rw [hreg.c_eq]
  exact one_le_inv₀ hsq_pos |>.2 hsq_le

private lemma sliceMeas {w : CProf} (hw : StronglyMeasurable w) (s : ℝ) :
    StronglyMeasurable (fun y : B0579.Plane => w (s, y)) :=
  hw.comp_measurable measurable_prodMk_left

private lemma cylSliceL2_sub_symm (c : ℝ) (u v : B0579.Plane → CMerid) :
    cylSliceL2 c (fun y => u y - v y) = cylSliceL2 c (fun y => v y - u y) := by
  unfold cylSliceL2
  have heq : (fun y => u y - v y) = -(fun y => v y - u y) := by
    funext y; simp
  rw [heq, eLpNorm_neg]

private lemma cylSliceH1_sub_symm (c : ℝ) (u uq uη v vq vη : B0579.Plane → CMerid) :
    cylSliceH1 c (fun y => u y - v y) (fun y => uq y - vq y) (fun y => uη y - vη y) =
      cylSliceH1 c (fun y => v y - u y) (fun y => vq y - uq y) (fun y => vη y - uη y) := by
  simp only [cylSliceH1, cylSliceL2_sub_symm]

private lemma cylSliceL2_triangle (c : ℝ) {u v : B0579.Plane → CMerid}
    (hu : StronglyMeasurable u) (hv : StronglyMeasurable v) :
    cylSliceL2 c u ≤ cylSliceL2 c v + cylSliceL2 c (fun y => u y - v y) := by
  have heq : u = v + (fun y => u y - v y) := by funext y; simp
  unfold cylSliceL2
  nth_rw 1 [heq]
  exact eLpNorm_add_le hv.aestronglyMeasurable (hu.sub hv).aestronglyMeasurable (by norm_num)

private lemma sliceH1Norm_triangle (c : ℝ) {z zq zη : CProf}
    (hz : StronglyMeasurable z) (hzq : StronglyMeasurable zq) (hzη : StronglyMeasurable zη)
    (s s' : ℝ) :
    sliceH1Norm c z zq zη s' ≤
      sliceH1Norm c z zq zη s +
        cylSliceH1 c (fun y => z (s', y) - z (s, y))
          (fun y => zq (s', y) - zq (s, y)) (fun y => zη (s', y) - zη (s, y)) := by
  have h1 := cylSliceL2_triangle c (sliceMeas hz s') (sliceMeas hz s)
  have h2 := cylSliceL2_triangle c (sliceMeas hzq s') (sliceMeas hzq s)
  have h3 := cylSliceL2_triangle c (sliceMeas hzη s') (sliceMeas hzη s)
  refine (add_le_add (add_le_add h1 h2) h3).trans (le_of_eq ?_)
  simp only [sliceH1Norm, cylSliceH1, cylSliceL2, add_assoc, add_left_comm]

/-- Clopen propagation along `Ici T`: `sliceH1Norm` is finite at every `t ≥ T`. -/
private lemma sliceH1Norm_lt_top_of_ge {c T : ℝ} {z zq zη : CProf}
    (hz : StronglyMeasurable z) (hzq : StronglyMeasurable zq) (hzη : StronglyMeasurable zη)
    (hT : sliceH1Norm c z zq zη T < ⊤)
    (hcont : ∀ s : ℝ, T ≤ s →
      Tendsto (fun s' => cylSliceH1 c
        (fun y => z (s', y) - z (s, y))
        (fun y => zq (s', y) - zq (s, y))
        (fun y => zη (s', y) - zη (s, y))) (𝓝[Ici T] s) (𝓝 0)) :
    ∀ t : ℝ, T ≤ t → sliceH1Norm c z zq zη t < ⊤ := by
  let S : Set (Ici T) := {x | sliceH1Norm c z zq zη x.1 < ⊤}
  have h_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hlim := hcont x.1 x.2
    have hev : ∀ᶠ s' in 𝓝[Ici T] x.1,
        cylSliceH1 c (fun y => z (s', y) - z (x.1, y))
          (fun y => zq (s', y) - zq (x.1, y)) (fun y => zη (s', y) - zη (x.1, y)) < 1 :=
      hlim.eventually (gt_mem_nhds zero_lt_one)
    rw [nhdsWithin_eq_map_subtype_coe x.2] at hev
    filter_upwards [hev] with y hy
    exact (sliceH1Norm_triangle c hz hzq hzη x.1 y.1).trans_lt
      (ENNReal.add_lt_top.2 ⟨hx, hy.trans (by norm_num)⟩)
  have h_closed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    have hlim := hcont x.1 x.2
    have hev : ∀ᶠ s' in 𝓝[Ici T] x.1,
        cylSliceH1 c (fun y => z (s', y) - z (x.1, y))
          (fun y => zq (s', y) - zq (x.1, y)) (fun y => zη (s', y) - zη (x.1, y)) < 1 :=
      hlim.eventually (gt_mem_nhds zero_lt_one)
    rw [nhdsWithin_eq_map_subtype_coe x.2] at hev
    filter_upwards [hev] with y hy hyS
    apply hx
    have hsymm := cylSliceH1_sub_symm c (fun w => z (y.1, w)) (fun w => zq (y.1, w))
      (fun w => zη (y.1, w)) (fun w => z (x.1, w)) (fun w => zq (x.1, w)) (fun w => zη (x.1, w))
    exact (sliceH1Norm_triangle c hz hzq hzη y.1 x.1).trans_lt
      (ENNReal.add_lt_top.2 ⟨hyS, by rw [← hsymm]; exact hy.trans (by norm_num)⟩)
  have : PreconnectedSpace (Ici T) := Subtype.preconnectedSpace isPreconnected_Ici
  have h_memT : (⟨T, mem_Ici.2 le_rfl⟩ : Ici T) ∈ S := hT
  have h_univ : S = univ :=
    IsClopen.eq_univ ⟨h_closed, h_open⟩ ⟨⟨T, mem_Ici.2 le_rfl⟩, h_memT⟩
  intro t ht
  have : (⟨t, ht⟩ : Ici T) ∈ S := by rw [h_univ]; trivial
  exact this

private lemma memLp_slice_of_sliceH1Norm_lt_top {c s : ℝ} {z zq zη : CProf}
    (hz : StronglyMeasurable z) (hzq : StronglyMeasurable zq) (hzη : StronglyMeasurable zη)
    (h : sliceH1Norm c z zq zη s < ⊤) :
    MemLp (fun y => z (s, y)) 2 (volume.restrict (B0579.cell c)) ∧
      MemLp (fun y => zq (s, y)) 2 (volume.restrict (B0579.cell c)) ∧
      MemLp (fun y => zη (s, y)) 2 (volume.restrict (B0579.cell c)) := by
  unfold sliceH1Norm at h
  have h12 : eLpNorm (fun y => z (s, y)) 2 (volume.restrict (B0579.cell c)) +
      eLpNorm (fun y => zq (s, y)) 2 (volume.restrict (B0579.cell c)) < ⊤ :=
    (le_self_add).trans_lt h
  exact ⟨⟨(sliceMeas hz s).aestronglyMeasurable, (le_self_add).trans_lt h12⟩,
    ⟨(sliceMeas hzq s).aestronglyMeasurable, (le_add_self).trans_lt h12⟩,
    ⟨(sliceMeas hzη s).aestronglyMeasurable, (le_add_self).trans_lt h⟩⟩

/-- Pointwise norm equality between `CMerid` and `IIIa.lmReal`. -/
private lemma norm_lmReal_cmerid (v : CMerid) :
    ‖IIIa.lmReal (fun i => v i)‖ = ‖v‖ := by
  have hsq : ‖IIIa.lmReal (fun i => v i)‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp [IIIa.lmReal, Fin.sum_univ_four, Fin.sum_univ_two, Complex.sq_norm,
      Complex.normSq_apply, Real.norm_eq_abs, sq_abs]
    ring
  nlinarith [norm_nonneg (IIIa.lmReal (fun i => v i)), norm_nonneg v]

private def profPath (c : ℝ) (w : CProf) : ℝ → IIIa.LMH c :=
  IIIa.lmPath c (fun s y i => w (s, y) i)

private lemma memLp_lmReal_of_memLp_cmerid {c : ℝ} {u : B0579.Plane → CMerid}
    (hu : MemLp u 2 (volume.restrict (B0579.cell c))) :
    MemLp (fun y => IIIa.lmReal (fun i => u y i)) 2 (volume.restrict (B0579.cell c)) := by
  have hcont : Continuous (fun v : CMerid => IIIa.lmReal (fun i => v i)) :=
    IIIa.lmReal_continuous.comp (continuous_pi fun i =>
      (EuclideanSpace.proj (𝕜 := ℂ) i).continuous)
  refine ⟨hcont.comp_aestronglyMeasurable hu.aestronglyMeasurable, ?_⟩
  have heq : eLpNorm (fun y => IIIa.lmReal (fun i => u y i)) 2 (volume.restrict (B0579.cell c)) =
      eLpNorm u 2 (volume.restrict (B0579.cell c)) := by
    refine eLpNorm_congr_norm_ae (Eventually.of_forall fun y => norm_lmReal_cmerid (u y))
  rw [heq]
  exact hu.eLpNorm_lt_top

private lemma eLpNorm_lmReal_eq_cylSliceL2 (c : ℝ) (u : B0579.Plane → CMerid) :
    eLpNorm (fun y => IIIa.lmReal (fun i => u y i)) 2 (volume.restrict (B0579.cell c)) =
      cylSliceL2 c u :=
  eLpNorm_congr_norm_ae (Eventually.of_forall fun y => norm_lmReal_cmerid (u y))

private lemma norm_profPath_eq {c s : ℝ} {w : CProf}
    (hm : MemLp (fun y => w (s, y)) 2 (volume.restrict (B0579.cell c))) :
    ‖profPath c w s‖ = (cylSliceL2 c (fun y => w (s, y))).toReal := by
  have hm' : MemLp (fun x => IIIa.lmF (fun s y i => w (s, y) i) (s, x))
      2 (volume.restrict (B0579.cell c)) := memLp_lmReal_of_memLp_cmerid hm
  unfold profPath IIIa.lmPath
  rw [toPathLq_of_memLp hm', Lp.norm_toLp]
  exact congrArg ENNReal.toReal (eLpNorm_lmReal_eq_cylSliceL2 c (fun y => w (s, y)))

private lemma norm_profPath_sub_le_cylSliceL2 {c s s' : ℝ} {w : CProf}
    (hms : MemLp (fun y => w (s, y)) 2 (volume.restrict (B0579.cell c)))
    (hms' : MemLp (fun y => w (s', y)) 2 (volume.restrict (B0579.cell c))) :
    ‖profPath c w s' - profPath c w s‖ =
      (cylSliceL2 c (fun y => w (s', y) - w (s, y))).toReal := by
  have hm_s : MemLp (fun x => IIIa.lmF (fun s y i => w (s, y) i) (s, x))
      2 (volume.restrict (B0579.cell c)) := memLp_lmReal_of_memLp_cmerid hms
  have hm_s' : MemLp (fun x => IIIa.lmF (fun s y i => w (s, y) i) (s', x))
      2 (volume.restrict (B0579.cell c)) := memLp_lmReal_of_memLp_cmerid hms'
  unfold profPath IIIa.lmPath
  rw [toPathLq_of_memLp hm_s', toPathLq_of_memLp hm_s, ← MemLp.toLp_sub, Lp.norm_toLp]
  have hlin : (fun x => IIIa.lmF (fun s y i => w (s, y) i) (s', x)) -
      (fun x => IIIa.lmF (fun s y i => w (s, y) i) (s, x)) =
      (fun y => IIIa.lmReal (fun i => (w (s', y) - w (s, y)) i)) := by
    funext y
    ext j
    fin_cases j <;> simp [IIIa.lmF, IIIa.lmReal]
  exact congrArg ENNReal.toReal
    ((congrArg (fun f => eLpNorm f 2 (volume.restrict (B0579.cell c))) hlin).trans
      (eLpNorm_lmReal_eq_cylSliceL2 c (fun y => w (s', y) - w (s, y))))

private lemma continuousOn_profPaths {c T : ℝ} {z zq zη : CProf}
    (hz : StronglyMeasurable z) (hzq : StronglyMeasurable zq) (hzη : StronglyMeasurable zη)
    (hT : sliceH1Norm c z zq zη T < ⊤)
    (hcont : ∀ s : ℝ, T ≤ s →
      Tendsto (fun s' => cylSliceH1 c
        (fun y => z (s', y) - z (s, y))
        (fun y => zq (s', y) - zq (s, y))
        (fun y => zη (s', y) - zη (s, y))) (𝓝[Ici T] s) (𝓝 0)) :
    ContinuousOn (profPath c z) (Ici T) ∧
      ContinuousOn (profPath c zq) (Ici T) ∧
      ContinuousOn (profPath c zη) (Ici T) := by
  have hfin := sliceH1Norm_lt_top_of_ge hz hzq hzη hT hcont
  have hmem : ∀ t ≥ T,
      MemLp (fun y => z (t, y)) 2 (volume.restrict (B0579.cell c)) ∧
      MemLp (fun y => zq (t, y)) 2 (volume.restrict (B0579.cell c)) ∧
      MemLp (fun y => zη (t, y)) 2 (volume.restrict (B0579.cell c)) :=
    fun t ht => memLp_slice_of_sliceH1Norm_lt_top hz hzq hzη (hfin t ht)
  have mk_cont : ∀ (w : CProf),
      (∀ t ≥ T, MemLp (fun y => w (t, y)) 2 (volume.restrict (B0579.cell c))) →
      (∀ s ≥ T, ∀ s', cylSliceL2 c (fun y => w (s', y) - w (s, y)) ≤
        cylSliceH1 c (fun y => z (s', y) - z (s, y))
          (fun y => zq (s', y) - zq (s, y)) (fun y => zη (s', y) - zη (s, y))) →
      ContinuousOn (profPath c w) (Ici T) := by
    intro w hw hle s hs
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    have hlim_enn := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hcont s hs)
      (fun _ => zero_le) (hle s hs)
    have hlim_real : Tendsto (fun s' =>
        (cylSliceL2 c (fun y => w (s', y) - w (s, y))).toReal) (𝓝[Ici T] s) (𝓝 0) := by
      have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim_enn
      rwa [ENNReal.toReal_zero] at h0
    refine hlim_real.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s' hs'
    exact (norm_profPath_sub_le_cylSliceL2 (hw s hs) (hw s' hs')).symm
  refine ⟨mk_cont z (fun t ht => (hmem t ht).1) (fun _ _ _ => ?_),
    mk_cont zq (fun t ht => (hmem t ht).2.1) (fun _ _ _ => ?_),
    mk_cont zη (fun t ht => (hmem t ht).2.2) (fun _ _ _ => ?_)⟩
  · unfold cylSliceH1; exact le_self_add.trans le_self_add
  · unfold cylSliceH1; exact le_add_self.trans le_self_add
  · unfold cylSliceH1; exact le_add_self

/-- Second-derivative measurability and local integrability for a BUC train. -/
private lemma continuousOn_iteratedFDeriv_two_slice {ν c : ℝ}
    (tr : B0140.TrainSol ν c) (z : B0579.Plane) :
    ContinuousOn (fun s : ℝ => ‖iteratedFDeriv ℝ 2 (tr.v s) z‖ₑ) (Ioi 0) := by
  let V : ℝ × B0579.Plane → UnforcedLeray.Train.Vec := fun p => tr.v p.1 p.2
  let U : Set (ℝ × B0579.Plane) := Ioi (0 : ℝ) ×ˢ (univ : Set B0579.Plane)
  have hU_open : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hV_sm : ContDiffOn ℝ ∞ V U :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have h_it_cont : ContinuousOn (iteratedFDeriv ℝ 2 V) U :=
    (hV_sm.continuousOn_iteratedFDerivWithin (m := 2) (by simp : (2 : ℕ∞ω) ≤ (⊤ : ℕ∞))
      hU_open.uniqueDiffOn).congr fun p hp =>
      (iteratedFDerivWithin_of_isOpen 2 hU_open hp).symm
  let ι : B0579.Plane →L[ℝ] ℝ × B0579.Plane := ContinuousLinearMap.inr ℝ ℝ B0579.Plane
  have h_pre : Continuous
      (fun M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℝ × B0579.Plane)
          UnforcedLeray.Train.Vec =>
        M.compContinuousLinearMap fun _ : Fin 2 => ι) :=
    ContinuousMultilinearMap.continuous_precomp (fun _ : Fin 2 => ι)
  have h_emb : Continuous (fun s : ℝ => (s, z)) := continuous_id.prodMk continuous_const
  have h_comp : ContinuousOn
      (fun s : ℝ => ‖(iteratedFDeriv ℝ 2 V (s, z)).compContinuousLinearMap
        (fun _ : Fin 2 => ι)‖ₑ) (Ioi 0) :=
    continuous_enorm.comp_continuousOn
      (h_pre.comp_continuousOn (h_it_cont.comp h_emb.continuousOn fun s hs => ⟨hs, trivial⟩))
  refine h_comp.congr fun s hs => ?_
  have hs_pos : 0 < s := hs
  let a : ℝ × B0579.Plane := (s, 0)
  let Vs : ℝ × B0579.Plane → UnforcedLeray.Train.Vec := fun p => V (a + p)
  let W : Set (ℝ × B0579.Plane) := Ioi (-s) ×ˢ (univ : Set B0579.Plane)
  have hW_open : IsOpen W := isOpen_Ioi.prod isOpen_univ
  have hVs_sm : ContDiffOn ℝ ∞ Vs W := by
    refine hV_sm.comp ((contDiff_const (c := a)).add contDiff_id).contDiffOn ?_
    intro p hp
    have hp1 : -s < p.1 := hp.1
    exact ⟨show 0 < s + p.1 by linarith, trivial⟩
  have hpre_W : ι ⁻¹' W = univ := by
    ext w
    simp [ι, W, neg_lt_zero.2 hs_pos]
  have hzW : ι z ∈ W := ⟨show -s < 0 from neg_lt_zero.2 hs_pos, trivial⟩
  have h_eq1 := ι.iteratedFDerivWithin_comp_right (f := Vs) (s := W) hVs_sm
    hW_open.uniqueDiffOn (by rw [hpre_W]; exact uniqueDiffOn_univ) hzW (i := 2)
    (by simp : (2 : ℕ∞ω) ≤ (⊤ : ℕ∞))
  rw [hpre_W, iteratedFDerivWithin_univ] at h_eq1
  have hVs_comp : Vs ∘ ι = tr.v s := by
    funext w
    simp [Vs, a, ι, V]
  rw [hVs_comp, iteratedFDerivWithin_of_isOpen 2 hW_open hzW] at h_eq1
  have h_shift : iteratedFDeriv ℝ 2 Vs (ι z) = iteratedFDeriv ℝ 2 V (s, z) := by
    have h1 := iteratedFDeriv_comp_add_left (𝕜 := ℝ) 2 a (ι z) (f := V)
    have h2 : a + ι z = (s, z) := by ext <;> simp [a, ι]
    simpa [Vs, h2] using h1
  dsimp only
  rw [h_eq1, h_shift]

private lemma measurable_supNormD_two_ite {ν c : ℝ} (tr : B0140.TrainSol ν c) :
    Measurable (fun s : ℝ => if 0 < s then B0277.supNormD 2 (tr.v s) else 0) := by
  let g : B0579.Plane → ℝ → ℝ≥0∞ := fun z s =>
    if 0 < s then ‖iteratedFDeriv ℝ 2 (tr.v s) z‖ₑ else 0
  have hg_lsc : ∀ z : B0579.Plane, LowerSemicontinuous (g z) := by
    intro z
    rw [lowerSemicontinuous_iff_isOpen_preimage]
    intro y
    have hpre : g z ⁻¹' Ioi y =
        Ioi (0 : ℝ) ∩ (fun s : ℝ => ‖iteratedFDeriv ℝ 2 (tr.v s) z‖ₑ) ⁻¹' Ioi y := by
      ext s
      simp only [mem_preimage, mem_Ioi, mem_inter_iff, g]
      split_ifs with hs <;> simp [hs]
    rw [hpre]
    exact (continuousOn_iteratedFDeriv_two_slice tr z).isOpen_inter_preimage isOpen_Ioi isOpen_Ioi
  have h_sup : (fun s : ℝ => if 0 < s then B0277.supNormD 2 (tr.v s) else 0) =
      fun s : ℝ => ⨆ z : B0579.Plane, g z s := by
    ext s
    dsimp [g, B0277.supNormD]
    split_ifs <;> simp
  rw [h_sup]
  exact (lowerSemicontinuous_iSup hg_lsc).measurable

private lemma supNormD_two_bound_on {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr) {S : ℝ} (hS : 0 ≤ S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Icc 0 S,
      B0277.supNormD 2 (tr.v s) ≤ ENNReal.ofReal M ∧
      (B0277.supNormD 2 (tr.v s)).toReal ≤ M ∧
      ∀ z : B0579.Plane, ‖iteratedFDeriv ℝ 2 (tr.v s) z‖ ≤ (B0277.supNormD 2 (tr.v s)).toReal := by
  obtain ⟨M₀, hM₀⟩ := htr.deriv_bound hS 2
  refine ⟨max M₀ 0, le_max_right _ _, fun s hs => ?_⟩
  have hle : B0277.supNormD 2 (tr.v s) ≤ ENNReal.ofReal (max M₀ 0) :=
    B0277.supNormD_le_ofReal fun z => (hM₀ s hs z).trans (le_max_left _ _)
  have hlt : B0277.supNormD 2 (tr.v s) < ⊤ := lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  have htoReal : (B0277.supNormD 2 (tr.v s)).toReal ≤ max M₀ 0 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rwa [ENNReal.toReal_ofReal (le_max_right _ _)] at this
  refine ⟨hle, htoReal, fun z => ?_⟩
  apply B0277.norm_le_of_supNormD_le ENNReal.toReal_nonneg _ z
  rw [ENNReal.ofReal_toReal hlt.ne]

private def strainRate {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) : ℝ :=
  (B0277.supNormD 1 (tr.v s)).toReal + (B0277.supNormD 2 (tr.v s)).toReal

private lemma strainRate_nonneg {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) :
    0 ≤ strainRate tr s :=
  add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

private lemma integrableOn_strainRate_Icc {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr) {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₁₂ : s₁ ≤ s₂) :
    IntegrableOn (strainRate tr) (Icc s₁ s₂) := by
  have h1 := IIIa.AdvectionEnergyAux.integrableOn_supNormD_one_Icc tr htr hs₁ hs₁₂
  have hs₂ : 0 ≤ s₂ := hs₁.le.trans hs₁₂
  obtain ⟨M, _, hM⟩ := supNormD_two_bound_on tr htr hs₂
  have hm : Measurable (fun s : ℝ =>
      if 0 < s then (B0277.supNormD 2 (tr.v s)).toReal else 0) := by
    convert ENNReal.measurable_toReal.comp (measurable_supNormD_two_ite tr) using 1
    ext s; by_cases hs0 : 0 < s <;> simp [hs0]
  have hI2 : IntegrableOn (fun s : ℝ =>
      if 0 < s then (B0277.supNormD 2 (tr.v s)).toReal else 0) (Icc s₁ s₂) := by
    refine IntegrableOn.of_bound measure_Icc_lt_top hm.aestronglyMeasurable M ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hs0 : 0 < s := lt_of_lt_of_le hs₁ hs.1
    simp only [hs0, ↓reduceIte, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact (hM s ⟨hs0.le, hs.2⟩).2.1
  have h2 : IntegrableOn (fun s : ℝ => (B0277.supNormD 2 (tr.v s)).toReal) (Icc s₁ s₂) := by
    refine hI2.congr_fun (fun s hs => ?_) measurableSet_Icc
    have hs0 : 0 < s := lt_of_lt_of_le hs₁ hs.1
    simp [hs0]
  exact h1.add h2

private lemma integral_strainRate_le {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr) {T s B_strain : ℝ}
    (hT : 0 < T) (hs : T ≤ s) (hB0 : 0 ≤ B_strain)
    (hStrain : ∫⁻ r in Ioi T, (B0277.supNormD 1 (tr.v r) + B0277.supNormD 2 (tr.v r)) ≤
      ENNReal.ofReal B_strain) :
    ∫ r in Icc T s, strainRate tr r ≤ B_strain := by
  have hint := integrableOn_strainRate_Icc tr htr hT hs
  rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
  have hsub : Ioc T s ⊆ Ioi T := fun r hr => hr.1
  have hl_le : ∫⁻ r in Ioc T s, ENNReal.ofReal (strainRate tr r) ≤ ENNReal.ofReal B_strain := by
    refine (setLIntegral_mono' measurableSet_Ioc fun r hr => ?_).trans
      ((lintegral_mono_set hsub).trans hStrain)
    have hr0 : 0 ≤ r := (hT.trans hr.1).le
    have hs0 : 0 ≤ s := (hT.trans_le hs).le
    obtain ⟨_, _, h1⟩ := IIIa.AdvectionEnergyAux.supNormD_one_bound_on tr htr hs0
    obtain ⟨_, _, h2⟩ := supNormD_two_bound_on tr htr hs0
    have hf1 : B0277.supNormD 1 (tr.v r) ≠ ⊤ :=
      ((h1 r ⟨hr0, hr.2⟩).1.trans_lt ENNReal.ofReal_lt_top).ne
    have hf2 : B0277.supNormD 2 (tr.v r) ≠ ⊤ :=
      ((h2 r ⟨hr0, hr.2⟩).1.trans_lt ENNReal.ofReal_lt_top).ne
    unfold strainRate
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hf1, ENNReal.ofReal_toReal hf2]
  have h_eq : ∫ r in Ioc T s, strainRate tr r =
      (∫⁻ r in Ioc T s, ENNReal.ofReal (strainRate tr r)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun r => strainRate_nonneg tr r)
      (hint.mono_set Ioc_subset_Icc_self).aestronglyMeasurable
  rw [h_eq]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hl_le
  rwa [ENNReal.toReal_ofReal hB0] at this

/-! ### 1B. `c`-periodic partition of unity, cylinder test lift, and slice regularity -/

private def qBump (c : ℝ) (hc : 0 < c) : ContDiffBump (0 : ℝ) where
  rIn := c / 2
  rOut := c
  rIn_pos := half_pos hc
  rIn_lt_rOut := half_lt_self hc

private def qBumpSum (c : ℝ) (hc : 0 < c) (q : ℝ) : ℝ :=
  ∑' k : ℤ, qBump c hc (q + (k : ℝ) * c)

private lemma qBump_eq_zero_of_abs_ge {c : ℝ} (hc : 0 < c) {q : ℝ} (hq : c ≤ |q|) :
    qBump c hc q = 0 := by
  apply (qBump c hc).zero_of_le_dist
  dsimp [qBump]
  simpa [Real.dist_eq, sub_zero] using hq

private lemma qBump_eq_one_of_abs_le {c : ℝ} (hc : 0 < c) {q : ℝ} (hq : |q| ≤ c / 2) :
    qBump c hc q = 1 := by
  apply (qBump c hc).one_of_mem_closedBall
  dsimp [qBump]
  simpa [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hq

private lemma qBump_shift_eq_zero_of_large {c : ℝ} (hc : 0 < c) {a b : ℝ} :
    ∃ N : ℕ, ∀ q ∈ Ioo a b, ∀ k : ℤ, k ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) →
      qBump c hc (q + (k : ℝ) * c) = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((max |a| |b|) / c + 1)
  refine ⟨N, fun q hq k hk => ?_⟩
  have hq_abs : |q| ≤ max |a| |b| := by
    rw [abs_le]
    have ha : -max |a| |b| ≤ a := neg_le_of_abs_le (le_max_left _ _)
    have hb : b ≤ max |a| |b| := le_trans (le_abs_self _) (le_max_right _ _)
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  apply qBump_eq_zero_of_abs_ge hc
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
  have hk_abs : (N : ℝ) + 1 ≤ |(k : ℝ)| := by
    have hk_int : (N : ℤ) + 1 ≤ |k| := by
      rcases hk with hk | hk
      · rw [abs_of_neg (by omega)]; omega
      · rw [abs_of_nonneg (by omega)]; omega
    have hk_r : ((N : ℤ) + 1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast hk_int
    simpa [Int.cast_abs] using hk_r
  have h1 : c < |(k : ℝ)| * c - |q| := by
    have hNc : max |a| |b| + c < (N : ℝ) * c := by
      have := mul_lt_mul_of_pos_right hN hc
      field_simp [hc.ne'] at this ⊢
      linarith
    have hkc : ((N : ℝ) + 1) * c ≤ |(k : ℝ)| * c := mul_le_mul_of_nonneg_right hk_abs hc.le
    linarith
  have h2 : |(k : ℝ)| * c - |q| ≤ |q + (k : ℝ) * c| := by
    have := abs_sub_abs_le_abs_add ((k : ℝ) * c) q
    rw [add_comm, abs_mul, abs_of_pos hc] at this
    linarith
  linarith

private lemma qBumpSum_summable {c : ℝ} (hc : 0 < c) (q : ℝ) :
    Summable (fun k : ℤ => qBump c hc (q + (k : ℝ) * c)) := by
  obtain ⟨N, hN⟩ := qBump_shift_eq_zero_of_large hc (a := q - 1) (b := q + 1)
  exact summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ)) (N : ℤ))
    (fun k hk => hN q ⟨by linarith, by linarith⟩ k hk)

private lemma qBumpSum_contDiff {c : ℝ} (hc : 0 < c) : ContDiff ℝ ∞ (qBumpSum c hc) := by
  rw [contDiff_iff_contDiffAt]
  intro q₀
  obtain ⟨N, hN⟩ := qBump_shift_eq_zero_of_large hc (a := q₀ - 1) (b := q₀ + 1)
  have h_eq : qBumpSum c hc =ᶠ[𝓝 q₀]
      fun q => ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), qBump c hc (q + (k : ℝ) * c) :=
    Filter.eventually_of_mem (Ioo_mem_nhds (by linarith) (by linarith)) fun q hq =>
      tsum_eq_sum (hN q hq)
  refine ContDiffAt.congr_of_eventuallyEq ?_ h_eq
  exact (ContDiff.sum fun k _ => (qBump c hc).contDiff.comp (contDiff_id.add contDiff_const)).contDiffAt

private lemma one_le_qBumpSum {c : ℝ} (hc : 0 < c) (q : ℝ) : 1 ≤ qBumpSum c hc q := by
  let k : ℤ := -⌊q / c + 1 / 2⌋
  have h1 : (⌊q / c + 1 / 2⌋ : ℝ) ≤ q / c + 1 / 2 := Int.floor_le _
  have h2 : q / c + 1 / 2 < (⌊q / c + 1 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hk_mem : |q + (k : ℝ) * c| ≤ c / 2 := by
    have hk_eq : q + (k : ℝ) * c = c * (q / c - (⌊q / c + 1 / 2⌋ : ℝ)) := by
      simp only [k, Int.cast_neg]
      field_simp [hc.ne']
      ring
    rw [hk_eq, abs_mul, abs_of_pos hc, show c / 2 = c * (1 / 2) by ring,
      mul_le_mul_iff_right₀ hc, abs_le]
    constructor <;> nlinarith
  have h_one : qBump c hc (q + (k : ℝ) * c) = 1 := qBump_eq_one_of_abs_le hc hk_mem
  rw [← h_one]
  exact (qBumpSum_summable hc q).le_tsum k (fun _ _ => (qBump c hc).nonneg)

private lemma qBumpSum_periodic_int {c : ℝ} (hc : 0 < c) (q : ℝ) (k : ℤ) :
    qBumpSum c hc (q + (k : ℝ) * c) = qBumpSum c hc q := by
  simp only [qBumpSum]
  have e : (fun m : ℤ => qBump c hc (q + (k : ℝ) * c + (m : ℝ) * c)) =
      (fun m : ℤ => qBump c hc (q + ((m + k : ℤ) : ℝ) * c)) := by
    funext m; push_cast; ring_nf
  rw [e]
  exact (Equiv.addRight k).tsum_eq (fun m : ℤ => qBump c hc (q + (m : ℝ) * c))

private def qPart (c : ℝ) (hc : 0 < c) (q : ℝ) : ℝ :=
  qBump c hc q / qBumpSum c hc q

private lemma qPart_contDiff {c : ℝ} (hc : 0 < c) : ContDiff ℝ ∞ (qPart c hc) :=
  (qBump c hc).contDiff.div (qBumpSum_contDiff hc) fun q => by linarith [one_le_qBumpSum hc q]

private lemma qPart_eq_zero_of_abs_ge {c : ℝ} (hc : 0 < c) {q : ℝ} (hq : c ≤ |q|) :
    qPart c hc q = 0 := by
  simp [qPart, qBump_eq_zero_of_abs_ge hc hq]

private lemma tsum_qPart_shift {c : ℝ} (hc : 0 < c) (q : ℝ) :
    ∑' k : ℤ, qPart c hc (q + (k : ℝ) * c) = 1 := by
  have heq : (fun k : ℤ => qPart c hc (q + (k : ℝ) * c)) =
      fun k : ℤ => qBump c hc (q + (k : ℝ) * c) / qBumpSum c hc q := by
    funext k
    rw [qPart, qBumpSum_periodic_int hc q k]
  have hpos : qBumpSum c hc q ≠ 0 := by linarith [one_le_qBumpSum hc q]
  rw [heq, tsum_div_const]
  exact div_self hpos

private lemma periodic_int_plane {c : ℝ} {ψ : B0579.Plane → ℝ}
    (hper : ∀ z : B0579.Plane, ψ (z.1 + c, z.2) = ψ z) (z : B0579.Plane) (k : ℤ) :
    ψ (z.1 + (k : ℝ) * c, z.2) = ψ z := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    push_cast
    have h1 : (z.1 + ((n : ℝ) + 1) * c, z.2) = ((z.1 + (n : ℝ) * c) + c, z.2) := by
      congr 1; ring
    rw [h1]
    exact (hper (z.1 + (n : ℝ) * c, z.2)).trans ih
  | pred n ih =>
    push_cast
    have h1 := hper (z.1 + (-(n : ℝ) - 1) * c, z.2)
    dsimp only at h1
    have h2 : (z.1 + (-(n : ℝ) - 1) * c + c, z.2) = (z.1 + (-(n : ℝ)) * c, z.2) := by
      congr 1; ring
    rw [h2] at h1
    have ih' : ψ (z.1 + (-(n : ℝ)) * c, z.2) = ψ z := by simpa using ih
    exact h1.symm.trans ih'

private def liftCylTest (c : ℝ) (hc : 0 < c) (θ : ℝ → ℝ) (ψ : B0579.Plane → ℝ) (x : Coord) : ℝ :=
  θ x.1 * qPart c hc x.2.1 * ψ x.2

private lemma qPeriodize_liftCylTest {c : ℝ} (hc : 0 < c) (θ : ℝ → ℝ) {ψ : B0579.Plane → ℝ}
    (hper : ∀ z : B0579.Plane, ψ (z.1 + c, z.2) = ψ z) (s : ℝ) (z : B0579.Plane) :
    TailPeriodizeAux.qPeriodize c (liftCylTest c hc θ ψ) s z = θ s * ψ z := by
  unfold TailPeriodizeAux.qPeriodize liftCylTest
  have heq : (fun k : ℤ => θ s * qPart c hc (z.1 + (k : ℝ) * c) * ψ (z.1 + (k : ℝ) * c, z.2)) =
      fun k : ℤ => (θ s * ψ z) * qPart c hc (z.1 + (k : ℝ) * c) := by
    funext k
    rw [periodic_int_plane hper z k]
    ring
  rw [heq, tsum_mul_left, tsum_qPart_shift hc z.1, mul_one]

private lemma isCoordTest_liftCylTest {c T a b : ℝ} (hc : 0 < c) (hT : 0 < T) (ha : T < a)
    {θ : ℝ → ℝ} (hθ_sm : ContDiff ℝ ∞ θ) (hθ_supp : tsupport θ ⊆ Ioo a b)
    {ψ : B0579.Plane → ℝ} (hψ : B0579.IsCylTest c ψ) :
    IsCoordTest (liftCylTest c hc θ ψ) ∧
      tsupport (liftCylTest c hc θ ψ) ⊆ Ioo a b ×ˢ univ ∧
      ∃ R : ℝ, 0 < R ∧ ∀ x : Coord,
        (x.1 ∉ Icc a b ∨ R < |x.2.1| ∨ R < |x.2.2|) → liftCylTest c hc θ ψ x = 0 := by
  obtain ⟨R0, hR0⟩ := hψ.band
  let R : ℝ := max c (max 1 R0)
  have hR_pos : 0 < R := lt_of_lt_of_le hc (le_max_left _ _)
  have hvan : ∀ x : Coord,
      (x.1 ∉ Icc a b ∨ R < |x.2.1| ∨ R < |x.2.2|) → liftCylTest c hc θ ψ x = 0 := by
    intro x hx
    unfold liftCylTest
    rcases hx with h1 | h2 | h3
    · have hθ0 : θ x.1 = 0 := image_eq_zero_of_notMem_tsupport fun hxt =>
        h1 (Ioo_subset_Icc_self (hθ_supp hxt))
      simp [hθ0]
    · have hq0 : qPart c hc x.2.1 = 0 :=
        qPart_eq_zero_of_abs_ge hc ((le_max_left c _).trans h2.le)
      simp [hq0]
    · have hψ0 : ψ x.2 = 0 :=
        hR0 x.2 (((le_max_right 1 R0).trans (le_max_right c _)).trans_lt h3)
      simp [hψ0]
  have hts_sub : tsupport (liftCylTest c hc θ ψ) ⊆
      tsupport θ ×ˢ (Icc (-R) R ×ˢ Icc (-R) R) := by
    have hclosed : IsClosed (tsupport θ ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)) :=
      (isClosed_tsupport θ).prod (isClosed_Icc.prod isClosed_Icc)
    refine closure_minimal ?_ hclosed
    intro x hx
    rw [Function.mem_support] at hx
    refine ⟨?_, ?_, ?_⟩
    · by_contra hnot
      exact hx (by simp [liftCylTest, image_eq_zero_of_notMem_tsupport hnot])
    · rw [mem_Icc, ← abs_le]
      by_contra hnot
      exact hx (hvan x (Or.inr (Or.inl (not_le.1 hnot))))
    · rw [mem_Icc, ← abs_le]
      by_contra hnot
      exact hx (hvan x (Or.inr (Or.inr (not_le.1 hnot))))
  have hts_Ioo : tsupport (liftCylTest c hc θ ψ) ⊆ Ioo a b ×ˢ univ :=
    hts_sub.trans (prod_mono hθ_supp (subset_univ _))
  have hcomp_box : IsCompact (Icc a b ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hcompact : HasCompactSupport (liftCylTest c hc θ ψ) :=
    HasCompactSupport.of_support_subset_isCompact hcomp_box
      ((subset_tsupport _).trans (hts_sub.trans
        (prod_mono (hθ_supp.trans Ioo_subset_Icc_self) Subset.rfl)))
  have hsm : ContDiff ℝ ∞ (liftCylTest c hc θ ψ) :=
    ((hθ_sm.comp contDiff_fst).mul ((qPart_contDiff hc).comp (contDiff_fst.comp contDiff_snd))).mul
      (hψ.smooth.comp contDiff_snd)
  refine ⟨⟨hsm, hcompact, hts_Ioo.trans (prod_mono ?_ Subset.rfl)⟩, hts_Ioo, R, hR_pos, hvan⟩
  intro s hs
  exact lt_trans hT (lt_trans ha hs.1)

private lemma tsupport_cpd_subset (j : Fin 3) (φ : Coord → ℝ) :
    tsupport (cpd j φ) ⊆ tsupport φ := by
  refine closure_minimal ?_ (isClosed_tsupport φ)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hnot
  exact hx (by simp [cpd, fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot])

private lemma isCoordTest_cpd (j : Fin 3) {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    IsCoordTest (cpd j φ) := by
  have hsm : ContDiff ℝ ∞ (cpd j φ) :=
    ((contDiff_infty_iff_fderiv.1 hφ.smooth).2).clm_apply contDiff_const
  have hts := tsupport_cpd_subset j φ
  exact ⟨hsm, HasCompactSupport.of_support_subset_isCompact hφ.compact
    ((subset_tsupport _).trans hts), hts.trans hφ.supp⟩

private def tailInd (T : ℝ) (w : CProf) : CProf :=
  fun x => if T < x.1 then w x else 0

private lemma stronglyMeasurable_tailInd (T : ℝ) {w : CProf} (hw : StronglyMeasurable w) :
    StronglyMeasurable (tailInd T w) :=
  StronglyMeasurable.ite (measurableSet_lt measurable_const measurable_fst) hw stronglyMeasurable_const

private lemma qPeriodic_tailInd {c T : ℝ} {w : CProf}
    (hper : ∀ᵐ x : Coord, T < x.1 → w (qShift c x) = w x) :
    QPeriodic c (tailInd T w) := by
  refine ae_restrict_of_ae ?_
  filter_upwards [hper] with x hx
  unfold tailInd
  have hfst : (qShift c x).1 = x.1 := rfl
  rw [hfst]
  split_ifs with hT
  · exact hx hT
  · rfl

private lemma memLp_of_isCylTest {c : ℝ} (_hc : 0 < c) {ψ : B0579.Plane → ℝ}
    (hψ : B0579.IsCylTest c ψ) :
    MemLp ψ 2 (volume.restrict (B0579.cell c)) ∧
      MemLp (fun z => (ψ z : ℂ)) 2 (volume.restrict (B0579.cell c)) := by
  obtain ⟨R0, hR0⟩ := hψ.band
  let R : ℝ := max 1 R0
  let B : Set B0579.Plane := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R
  have hB_comp : IsCompact B := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M0, hM0⟩ := hB_comp.exists_bound_of_continuousOn hψ.continuous.continuousOn
  let M : ℝ := max 0 M0
  have hB_meas : MeasurableSet B := measurableSet_Icc.prod measurableSet_Icc
  have hB_fin : volume B < ⊤ := by
    dsimp [B]
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hind : ψ =ᵐ[volume.restrict (B0579.cell c)] B.indicator ψ := by
    filter_upwards [ae_restrict_mem (B0579.measurableSet_cell c)] with z hz
    by_cases hzB : z ∈ B
    · exact (Set.indicator_of_mem hzB ψ).symm
    · rw [Set.indicator_of_notMem hzB]
      apply hR0 z
      by_contra hle
      push Not at hle
      apply hzB
      exact ⟨⟨hz.1.1, hz.1.2.le⟩, abs_le.1 (hle.trans (le_max_right 1 R0))⟩
  have hmem_ind : MemLp (B.indicator ψ) 2 (volume.restrict (B0579.cell c)) := by
    rw [memLp_indicator_iff_restrict hB_meas, Measure.restrict_restrict hB_meas]
    have hfin_inter : (volume : Measure B0579.Plane) (B ∩ B0579.cell c) < ⊤ :=
      (measure_mono inter_subset_left).trans_lt hB_fin
    have : IsFiniteMeasure (volume.restrict (B ∩ B0579.cell c)) :=
      ⟨by rwa [Measure.restrict_apply_univ]⟩
    refine MemLp.of_bound hψ.continuous.aestronglyMeasurable M ?_
    filter_upwards [ae_restrict_mem (hB_meas.inter (B0579.measurableSet_cell c))] with z hz
    exact (hM0 z hz.1).trans (le_max_right 0 M0)
  have hmem_real : MemLp ψ 2 (volume.restrict (B0579.cell c)) := hmem_ind.ae_eq hind.symm
  refine ⟨hmem_real, ?_⟩
  refine ⟨(Complex.continuous_ofReal.comp hψ.continuous).aestronglyMeasurable, ?_⟩
  have heq : eLpNorm (fun z => (ψ z : ℂ)) 2 (volume.restrict (B0579.cell c)) =
      eLpNorm ψ 2 (volume.restrict (B0579.cell c)) :=
    eLpNorm_congr_norm_ae (Eventually.of_forall fun z => Complex.norm_real (ψ z))
  rw [heq]
  exact hmem_real.eLpNorm_lt_top

/-- Elementary bump contradiction: a continuous function on `Ioi T` orthogonal to all smooth
bumps on `Ioo a b` (`T < a < b`) vanishes identically on `Ioi T`. -/
private lemma eq_zero_on_Ioi_of_test_integral_eq_zero {T : ℝ} {F : ℝ → ℂ}
    (hF_cont : ContinuousOn F (Ioi T))
    (h_orth : ∀ (a b : ℝ), T < a → a < b → ∀ θ : ℝ → ℝ,
      ContDiff ℝ ∞ θ → tsupport θ ⊆ Ioo a b →
      ∫ s in Icc a b, (θ s : ℂ) * F s = 0) :
    ∀ r : ℝ, T < r → F r = 0 := by
  have real_orth : ∀ g : ℝ → ℝ, ContinuousOn g (Ioi T) →
      (∀ (a b : ℝ), T < a → a < b → ∀ θ : ℝ → ℝ,
        ContDiff ℝ ∞ θ → tsupport θ ⊆ Ioo a b → ∫ s in Icc a b, θ s * g s = 0) →
      ∀ r : ℝ, T < r → 0 ≤ g r := by
    intro g hg_cont hg_orth r hr
    by_contra hneg
    push Not at hneg
    let η : ℝ := -g r / 2
    have hη : 0 < η := by dsimp [η]; linarith
    have hev : ∀ᶠ s in 𝓝 r, g s < -η := by
      have hcont_at : ContinuousAt g r := hg_cont.continuousAt (isOpen_Ioi.mem_nhds hr)
      exact hcont_at.eventually (gt_mem_nhds (by dsimp [η]; linarith))
    obtain ⟨δ0, hδ0_pos, hball⟩ := Metric.eventually_nhds_iff.1 hev
    let δ : ℝ := min (δ0 / 2) ((r - T) / 4)
    have hδ_pos : 0 < δ := lt_min (half_pos hδ0_pos) (by linarith)
    let b0 : ContDiffBump r :=
      { rIn := δ / 2
        rOut := δ
        rIn_pos := half_pos hδ_pos
        rIn_lt_rOut := half_lt_self hδ_pos }
    let a : ℝ := r - 2 * δ
    let b : ℝ := r + 2 * δ
    have haT : T < a := by
      have : δ ≤ (r - T) / 4 := min_le_right _ _
      dsimp [a]; linarith
    have hab : a < b := by dsimp [a, b]; linarith
    have hts : tsupport b0 ⊆ Ioo a b := by
      rw [b0.tsupport_eq]
      intro s hs
      rw [Metric.mem_closedBall, Real.dist_eq] at hs
      rw [abs_le] at hs
      exact ⟨by dsimp [a]; linarith, by dsimp [b]; linarith⟩
    have hint_zero := hg_orth a b haT hab b0 b0.contDiff hts
    have hsub_ab : Icc a b ⊆ Ioi T := fun s hs => lt_of_lt_of_le haT hs.1
    have hint_ab : IntegrableOn (fun s => b0 s * g s) (Icc a b) :=
      ((b0.contDiff (n := (⊤ : ℕ∞))).continuous.continuousOn.mul
        (hg_cont.mono hsub_ab)).integrableOn_Icc
    have hsub_in : Icc (r - δ / 2) (r + δ / 2) ⊆ Icc a b := by
      intro s hs; exact ⟨by dsimp [a]; linarith [hs.1], by dsimp [b]; linarith [hs.2]⟩
    have hnonpos : ∀ s ∈ Icc a b, b0 s * g s ≤ 0 := by
      intro s _
      by_cases hs_out : dist s r < δ
      · have hs_δ0 : dist s r < δ0 :=
          hs_out.trans_le ((min_le_left _ _).trans (half_le_self hδ0_pos.le))
        have hgs : g s < -η := hball hs_δ0
        exact mul_nonpos_of_nonneg_of_nonpos b0.nonneg (by linarith)
      · have hb0 : b0 s = 0 := b0.zero_of_le_dist (not_lt.1 hs_out)
        simp [hb0]
    have hle_in : ∫ s in Icc a b, b0 s * g s ≤
        ∫ s in Icc (r - δ / 2) (r + δ / 2), b0 s * g s := by
      have hneg_ge : ∫ s in Icc (r - δ / 2) (r + δ / 2), -(b0 s * g s) ≤
          ∫ s in Icc a b, -(b0 s * g s) :=
        setIntegral_mono_set (f := fun s => -(b0 s * g s)) hint_ab.fun_neg
          (ae_of_all _ fun s => neg_nonneg.2 (by
            by_cases h : s ∈ Icc a b
            · exact hnonpos s h
            · have : s ∉ tsupport b0 := fun ht => h (Ioo_subset_Icc_self (hts ht))
              simp [image_eq_zero_of_notMem_tsupport this]))
          (Eventually.of_forall hsub_in)
      rw [integral_neg, integral_neg] at hneg_ge
      linarith
    have h_in_bound : ∀ s ∈ Icc (r - δ / 2) (r + δ / 2), b0 s * g s ≤ -η := by
      intro s hs
      have hdist_in : dist s r ≤ δ / 2 := by
        rw [Real.dist_eq, abs_le]
        exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hb1 : b0 s = 1 := b0.one_of_mem_closedBall hdist_in
      have hs_δ0 : dist s r < δ0 :=
        (lt_of_le_of_lt hdist_in (half_lt_self hδ_pos)).trans_le
          ((min_le_left _ _).trans (half_le_self hδ0_pos.le))
      rw [hb1, one_mul]
      exact (hball hs_δ0).le
    have h_in_int : ∫ s in Icc (r - δ / 2) (r + δ / 2), b0 s * g s ≤
        ∫ _ in Icc (r - δ / 2) (r + δ / 2), (-η) :=
      setIntegral_mono_on (hint_ab.mono_set hsub_in) (integrableOn_const (hs := measure_Icc_lt_top.ne))
        measurableSet_Icc h_in_bound
    have h_const : ∫ _ in Icc (r - δ / 2) (r + δ / 2), (-η) = -η * δ := by
      rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith)]
      simp only [smul_eq_mul]
      ring
    linarith [mul_pos hη hδ_pos]
  intro r hr
  have hre_cont : ContinuousOn (fun s => (F s).re) (Ioi T) := Complex.continuous_re.comp_continuousOn hF_cont
  have him_cont : ContinuousOn (fun s => (F s).im) (Ioi T) := Complex.continuous_im.comp_continuousOn hF_cont
  have hre_orth : ∀ (a b : ℝ), T < a → a < b → ∀ θ : ℝ → ℝ,
      ContDiff ℝ ∞ θ → tsupport θ ⊆ Ioo a b → ∫ s in Icc a b, θ s * (F s).re = 0 := by
    intro a b haT hab θ hθ hts
    have hsub : Icc a b ⊆ Ioi T := fun s hs => lt_of_lt_of_le haT hs.1
    have hint : IntegrableOn (fun s => (θ s : ℂ) * F s) (Icc a b) :=
      ((Complex.continuous_ofReal.comp hθ.continuous).continuousOn.mul (hF_cont.mono hsub)).integrableOn_Icc
    have hre := congrArg Complex.re (h_orth a b haT hab θ hθ hts)
    have hcomm := Complex.reCLM.integral_comp_comm hint
    simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at hcomm
    exact hcomm.trans (hre.trans Complex.zero_re)
  have him_orth : ∀ (a b : ℝ), T < a → a < b → ∀ θ : ℝ → ℝ,
      ContDiff ℝ ∞ θ → tsupport θ ⊆ Ioo a b → ∫ s in Icc a b, θ s * (F s).im = 0 := by
    intro a b haT hab θ hθ hts
    have hsub : Icc a b ⊆ Ioi T := fun s hs => lt_of_lt_of_le haT hs.1
    have hint : IntegrableOn (fun s => (θ s : ℂ) * F s) (Icc a b) :=
      ((Complex.continuous_ofReal.comp hθ.continuous).continuousOn.mul (hF_cont.mono hsub)).integrableOn_Icc
    have him := congrArg Complex.im (h_orth a b haT hab θ hθ hts)
    have hcomm := Complex.imCLM.integral_comp_comm hint
    simp only [Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] at hcomm
    exact hcomm.trans (him.trans Complex.zero_im)
  have hre0 : (F r).re = 0 := le_antisymm
    (by
      have := real_orth (fun s => -(F s).re) hre_cont.neg (fun a b haT hab θ hθ hts => by
        simp_rw [mul_neg]; rw [integral_neg, hre_orth a b haT hab θ hθ hts, neg_zero]) r hr
      linarith)
    (real_orth _ hre_cont hre_orth r hr)
  have him0 : (F r).im = 0 := le_antisymm
    (by
      have := real_orth (fun s => -(F s).im) him_cont.neg (fun a b haT hab θ hθ hts => by
        simp_rw [mul_neg]; rw [integral_neg, him_orth a b haT hab θ hθ hts, neg_zero]) r hr
      linarith)
    (real_orth _ him_cont him_orth r hr)
  exact Complex.ext hre0 him0

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

private lemma norm_integral_mul_le_l2 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ x, f x * g x ∂μ‖ ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have hfn : MemLp (fun x => ‖f x‖) 2 μ := hf.norm
  have hgn : MemLp (fun x => ‖g x‖) 2 μ := hg.norm
  have h_ae : (fun x => ‖f x‖ * ‖g x‖) =ᵐ[μ]
      fun x => (hfn.toLp (fun x => ‖f x‖)) x * (hgn.toLp (fun x => ‖g x‖)) x := by
    filter_upwards [hfn.coeFn_toLp, hgn.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2]
  have h_inn : ∫ x, ‖f x‖ * ‖g x‖ ∂μ =
      ⟪hfn.toLp (fun x => ‖f x‖), hgn.toLp (fun x => ‖g x‖)⟫ := by
    rw [L2.inner_def]
    refine integral_congr_ae (h_ae.mono fun x hx => ?_)
    simpa [inner, mul_comm] using hx
  calc ‖∫ x, f x * g x ∂μ‖
      ≤ ∫ x, ‖f x * g x‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by simp_rw [norm_mul]
    _ = ⟪hfn.toLp (fun x => ‖f x‖), hgn.toLp (fun x => ‖g x‖)⟫ := h_inn
    _ ≤ ‖hfn.toLp (fun x => ‖f x‖)‖ * ‖hgn.toLp (fun x => ‖g x‖)‖ := real_inner_le_norm _ _
    _ = (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
        rw [Lp.norm_toLp, Lp.norm_toLp, eLpNorm_norm, eLpNorm_norm]

private lemma continuousOn_slice_test_pairing {c T : ℝ} (hc : 0 < c) {w : CProf}
    (hw_sm : StronglyMeasurable w)
    (hw_mem : ∀ t ≥ T, MemLp (fun y => w (t, y)) 2 (volume.restrict (B0579.cell c)))
    (hw_cont : ContinuousOn (profPath c w) (Ici T))
    {ψ : B0579.Plane → ℝ} (hψ : B0579.IsCylTest c ψ) (i : Fin 2) :
    ContinuousOn (fun r : ℝ => ∫ y in B0579.cell c, w (r, y) i * (ψ y : ℂ)) (Ici T) := by
  obtain ⟨_, hψ_memC⟩ := memLp_of_isCylTest hc hψ
  intro r hr
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  let M : ℝ := (eLpNorm (fun z => (ψ z : ℂ)) 2 (volume.restrict (B0579.cell c))).toReal + 1
  have hM_pos : 0 < M := add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg one_pos
  have hlim : Tendsto (fun r' => ‖profPath c w r' - profPath c w r‖) (𝓝[Ici T] r) (𝓝 0) := by
    have := hw_cont r hr
    rwa [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero] at this
  filter_upwards [hlim.eventually (gt_mem_nhds (div_pos hε hM_pos)), self_mem_nhdsWithin]
    with r' hr'_lt hr'
  rw [Complex.dist_eq]
  have hi_r' : IntegrableOn (fun y => w (r', y) i * (ψ y : ℂ)) (B0579.cell c) := by
    have hm_i : MemLp (fun y => w (r', y) i) 2 (volume.restrict (B0579.cell c)) :=
      ⟨((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
          (sliceMeas hw_sm r')).aestronglyMeasurable,
        (eLpNorm_comp_le_merid c w r' i).trans_lt (hw_mem r' hr').eLpNorm_lt_top⟩
    exact hm_i.integrable_mul hψ_memC
  have hi_r : IntegrableOn (fun y => w (r, y) i * (ψ y : ℂ)) (B0579.cell c) := by
    have hm_i : MemLp (fun y => w (r, y) i) 2 (volume.restrict (B0579.cell c)) :=
      ⟨((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
          (sliceMeas hw_sm r)).aestronglyMeasurable,
        (eLpNorm_comp_le_merid c w r i).trans_lt (hw_mem r hr).eLpNorm_lt_top⟩
    exact hm_i.integrable_mul hψ_memC
  rw [← integral_sub hi_r' hi_r]
  have hdiff_eq : (fun y => w (r', y) i * (ψ y : ℂ) - w (r, y) i * (ψ y : ℂ)) =
      fun y => (w (r', y) - w (r, y)) i * (ψ y : ℂ) := by
    funext y; simp [sub_mul]
  rw [hdiff_eq]
  have hm_diff : MemLp (fun y => (w (r', y) - w (r, y)) i) 2 (volume.restrict (B0579.cell c)) := by
    have hsub_mem := (hw_mem r' hr').sub (hw_mem r hr)
    refine ⟨((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
        ((sliceMeas hw_sm r').sub (sliceMeas hw_sm r))).aestronglyMeasurable, ?_⟩
    refine (eLpNorm_mono_enorm fun y => ?_).trans_lt hsub_mem.eLpNorm_lt_top
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
    exact_mod_cast PiLp.norm_apply_le (w (r', y) - w (r, y)) i
  have hcs := norm_integral_mul_le_l2 hm_diff hψ_memC
  have hL2_le : ‖profPath c w r' - profPath c w r‖ ≥
      (eLpNorm (fun y => (w (r', y) - w (r, y)) i) 2 (volume.restrict (B0579.cell c))).toReal := by
    rw [norm_profPath_sub_le_cylSliceL2 (hw_mem r hr) (hw_mem r' hr')]
    unfold cylSliceL2
    refine ENNReal.toReal_mono ((hw_mem r' hr').sub (hw_mem r hr)).eLpNorm_ne_top ?_
    refine eLpNorm_mono_enorm fun y => ?_
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
    exact_mod_cast PiLp.norm_apply_le (w (r', y) - w (r, y)) i
  have hM_le : (eLpNorm (fun y => (ψ y : ℂ)) 2 (volume.restrict (B0579.cell c))).toReal ≤ M := by
    dsimp [M]; linarith
  calc ‖∫ y in B0579.cell c, (w (r', y) - w (r, y)) i * (ψ y : ℂ)‖
      ≤ (eLpNorm (fun y => (w (r', y) - w (r, y)) i) 2 (volume.restrict (B0579.cell c))).toReal *
          (eLpNorm (fun y => (ψ y : ℂ)) 2 (volume.restrict (B0579.cell c))).toReal := hcs
    _ ≤ ‖profPath c w r' - profPath c w r‖ * M :=
        mul_le_mul hL2_le hM_le ENNReal.toReal_nonneg (norm_nonneg _)
    _ < (ε / M) * M := mul_lt_mul_of_pos_right hr'_lt hM_pos
    _ = ε := div_mul_cancel₀ ε hM_pos.ne'

private lemma loc_eLpNorm_lt_top_of_continuousOn_profPath {c T : ℝ} {w : CProf}
    (hw_mem : ∀ t ≥ T, MemLp (fun y => w (t, y)) 2 (volume.restrict (B0579.cell c)))
    (hw_cont : ContinuousOn (profPath c w) (Ici T))
    {a b : ℝ} (ha : T ≤ a) :
    (∫⁻ s in Icc a b, eLpNorm (fun y => w (s, y)) 2 (volume.restrict (B0579.cell c))) < ⊤ := by
  have hsub : Icc a b ⊆ Ici T := fun s hs => ha.trans hs.1
  obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn (hw_cont.mono hsub)
  let M : ℝ := max 0 M0
  have hle : ∫⁻ s in Icc a b, eLpNorm (fun y => w (s, y)) 2 (volume.restrict (B0579.cell c)) ≤
      ∫⁻ _ in Icc a b, ENNReal.ofReal M := by
    refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
    have hm := hw_mem s (hsub hs)
    have hn : (eLpNorm (fun y => w (s, y)) 2 (volume.restrict (B0579.cell c))).toReal =
        ‖profPath c w s‖ := (norm_profPath_eq hm).symm
    rw [← ENNReal.ofReal_toReal hm.eLpNorm_ne_top, hn]
    exact ENNReal.ofReal_le_ofReal ((hM0 s hs).trans (le_max_right 0 M0))
  refine hle.trans_lt ?_
  rw [setLIntegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Icc_lt_top

/-- Every slice `r ≥ T` of a continuous `H¹(C_c)` tail solution has cylinder weak derivatives
`zq₂, zη₂` and is weakly divergence-free (together with `zq₂, zη₂`). -/
private lemma tail_slice_regularity {p : Params} {T : ℝ} (hT : 0 < T)
    {g z₂ zq₂ zη₂ : CProf}
    (hz : StronglyMeasurable z₂) (hzq : StronglyMeasurable zq₂) (hzη : StronglyMeasurable zη₂)
    (hzT : IsCylH1Slice p.c (fun y => z₂ (T, y)) (fun y => zq₂ (T, y)) (fun y => zη₂ (T, y)))
    (hz_sol : IsTailMeridionalSolution p T g z₂ zq₂ zη₂)
    (hcont : ∀ s : ℝ, T ≤ s →
      Tendsto (fun s' => cylSliceH1 p.c
        (fun y => z₂ (s', y) - z₂ (s, y))
        (fun y => zq₂ (s', y) - zq₂ (s, y))
        (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici T] s) (𝓝 0)) :
    ∀ r : ℝ, T ≤ r →
      (∀ i : Fin 2,
        IIIa.HasWeakCellDerivC p.c 0 (fun y => z₂ (r, y) i) (fun y => zq₂ (r, y) i) ∧
        IIIa.HasWeakCellDerivC p.c 1 (fun y => z₂ (r, y) i) (fun y => zη₂ (r, y) i)) ∧
      IIIa.LMWeakDivFree p.c (fun y i => z₂ (r, y) i) ∧
      IIIa.LMWeakDivFree p.c (fun y i => zq₂ (r, y) i) ∧
      IIIa.LMWeakDivFree p.c (fun y i => zη₂ (r, y) i) := by
  have hc : 0 < p.c := p.c_pos
  have hT_fin : sliceH1Norm p.c z₂ zq₂ zη₂ T < ⊤ := by
    unfold sliceH1Norm
    exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2
      ⟨hzT.memL2_u.eLpNorm_lt_top, hzT.memL2_uq.eLpNorm_lt_top⟩, hzT.memL2_uη.eLpNorm_lt_top⟩
  have hfin := sliceH1Norm_lt_top_of_ge hz hzq hzη hT_fin hcont
  have hmem := fun t ht => memLp_slice_of_sliceH1Norm_lt_top hz hzq hzη (hfin t ht)
  obtain ⟨hcz, hczq, hczη⟩ := continuousOn_profPaths hz hzq hzη hT_fin hcont
  have hper_z := qPeriodic_tailInd (hz_sol.periodic.mono fun x hx hTx => (hx hTx).1)
  have hper_zq := qPeriodic_tailInd (hz_sol.periodic.mono fun x hx hTx => (hx hTx).2.1)
  have hper_zη := qPeriodic_tailInd (hz_sol.periodic.mono fun x hx hTx => (hx hTx).2.2)
  -- Helper for weak derivative in direction j ∈ {0, 1} for r > T
  have weak_gt : ∀ (j : Fin 2) (zj : CProf),
      StronglyMeasurable zj →
      (∀ t ≥ T, MemLp (fun y => zj (t, y)) 2 (volume.restrict (B0579.cell p.c))) →
      ContinuousOn (profPath p.c zj) (Ici T) →
      QPeriodic p.c (tailInd T zj) →
      (∀ i : Fin 2, ∀ φ, IsCoordTest φ → tsupport φ ⊆ Ioi T ×ˢ univ →
        Integrable (fun x => z₂ x i * (coordTranspose (![vQ0, vEta] j) dZero φ x : ℂ)) ∧
        Integrable (fun x => zj x i * (φ x : ℂ)) ∧
        ∫ x, zj x i * (φ x : ℂ) =
          ∫ x, z₂ x i * (coordTranspose (![vQ0, vEta] j) dZero φ x : ℂ)) →
      ∀ r > T, ∀ i : Fin 2,
        IIIa.HasWeakCellDerivC p.c j (fun y => z₂ (r, y) i) (fun y => zj (r, y) i) := by
    intro j zj hzj hmem_zj hczj hper_zj hw_joint r hr i
    refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
    · obtain ⟨_, hψC⟩ := memLp_of_isCylTest hc hψ
      obtain ⟨_, hpdC⟩ := memLp_of_isCylTest hc (hψ.pd j)
      have hm_z : MemLp (fun y => z₂ (r, y) i) 2 (volume.restrict (B0579.cell p.c)) :=
        ⟨((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
            (sliceMeas hz r)).aestronglyMeasurable,
          (eLpNorm_comp_le_merid p.c z₂ r i).trans_lt (hmem r hr.le).1.eLpNorm_lt_top⟩
      have hm_zj : MemLp (fun y => zj (r, y) i) 2 (volume.restrict (B0579.cell p.c)) :=
        ⟨((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
            (sliceMeas hzj r)).aestronglyMeasurable,
          (eLpNorm_comp_le_merid p.c zj r i).trans_lt (hmem_zj r hr.le).eLpNorm_lt_top⟩
      exact ⟨hm_z.integrable_mul hpdC, hm_zj.integrable_mul hψC⟩
    · let F : ℝ → ℂ := fun s =>
        (∫ y in B0579.cell p.c, zj (s, y) i * (ψ y : ℂ)) +
          (∫ y in B0579.cell p.c, z₂ (s, y) i * (B0579.pd j ψ y : ℂ))
      have hF_cont : ContinuousOn F (Ioi T) :=
        ((continuousOn_slice_test_pairing hc hzj hmem_zj hczj hψ i).add
          (continuousOn_slice_test_pairing hc hz (fun t ht => (hmem t ht).1) hcz
            (hψ.pd j) i)).mono Ioi_subset_Ici_self
      have hF_zero := eq_zero_on_Ioi_of_test_integral_eq_zero hF_cont ?_ r hr
      · exact eq_neg_of_add_eq_zero_right hF_zero
      · intro a b haT hab θ hθ hts
        obtain ⟨hφ, hts_ab, R, hR_pos, hvan⟩ := isCoordTest_liftCylTest hc hT haT hθ hts hψ
        have hts_T : tsupport (liftCylTest p.c hc θ ψ) ⊆ Ioi T ×ˢ univ :=
          hts_ab.trans (prod_mono (fun s hs => haT.trans hs.1) Subset.rfl)
        have hjoint := (hw_joint i (liftCylTest p.c hc θ ψ) hφ hts_T).2.2
        have hloc_z : (∫⁻ s in Icc a b,
            eLpNorm (fun z => tailInd T z₂ (s, z) i) 2 (volume.restrict (B0579.cell p.c))) < ⊤ := by
          have heq : ∫⁻ s in Icc a b,
              eLpNorm (fun z => tailInd T z₂ (s, z) i) 2 (volume.restrict (B0579.cell p.c)) =
              ∫⁻ s in Icc a b,
              eLpNorm (fun z => z₂ (s, z) i) 2 (volume.restrict (B0579.cell p.c)) := by
            refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
            have hsT : T < s := lt_of_lt_of_le haT hs.1
            simp [tailInd, hsT]
          rw [heq]
          exact (lintegral_mono fun s => eLpNorm_comp_le_merid p.c z₂ s i).trans_lt
            (loc_eLpNorm_lt_top_of_continuousOn_profPath (fun t ht => (hmem t ht).1) hcz haT.le)
        have hloc_zj : (∫⁻ s in Icc a b,
            eLpNorm (fun z => tailInd T zj (s, z) i) 2 (volume.restrict (B0579.cell p.c))) < ⊤ := by
          have heq : ∫⁻ s in Icc a b,
              eLpNorm (fun z => tailInd T zj (s, z) i) 2 (volume.restrict (B0579.cell p.c)) =
              ∫⁻ s in Icc a b,
              eLpNorm (fun z => zj (s, z) i) 2 (volume.restrict (B0579.cell p.c)) := by
            refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
            have hsT : T < s := lt_of_lt_of_le haT hs.1
            simp [tailInd, hsT]
          rw [heq]
          exact (lintegral_mono fun s => eLpNorm_comp_le_merid p.c zj s i).trans_lt
            (loc_eLpNorm_lt_top_of_continuousOn_profPath hmem_zj hczj haT.le)
        have hbox_ex : ∃ R1 : ℝ, 0 < R1 ∧
            ∀ x : Coord, (x.1 ∉ Icc a b ∨ R1 < |x.2.1| ∨ R1 < |x.2.2|) →
              liftCylTest p.c hc θ ψ x = 0 ∧
                ∀ k : Fin 3, cpd k (liftCylTest p.c hc θ ψ) x = 0 := by
          obtain ⟨_, _, R1, _, _, _, hb1⟩ := TailPeriodizeAux.coordTest_box hφ
          refine ⟨max R R1, lt_of_lt_of_le hR_pos (le_max_left _ _),
            fun x (hx : x.1 ∉ Icc a b ∨ max R R1 < |x.2.1| ∨ max R R1 < |x.2.2|) => ?_⟩
          rcases hx with h1 | h2 | h3
          · have hnot_ts : x ∉ tsupport (liftCylTest p.c hc θ ψ) := fun hxt =>
              h1 (Ioo_subset_Icc_self (hts_ab hxt).1)
            exact ⟨image_eq_zero_of_notMem_tsupport hnot_ts,
              fun k => by simp [cpd, fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot_ts]⟩
          · exact hb1 x (Or.inr (Or.inl ((le_max_right R R1).trans_lt h2)))
          · exact hb1 x (Or.inr (Or.inr ((le_max_right R R1).trans_lt h3)))
        obtain ⟨R1, hR1_pos, hbox_φ⟩ := hbox_ex
        have hm_zi : AEStronglyMeasurable (fun x : Coord => tailInd T z₂ x i) volume :=
          ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
            (stronglyMeasurable_tailInd T hz)).aestronglyMeasurable
        have hm_zji : AEStronglyMeasurable (fun x : Coord => tailInd T zj x i) volume :=
          ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
            (stronglyMeasurable_tailInd T hzj)).aestronglyMeasurable
        obtain ⟨hint_zj, hcell_zj, heq_zj⟩ :=
          TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize hc (hT.trans haT)
            hab.le hR1_pos hm_zji (hper_zj.mono fun _ hx => congrArg (fun v : CMerid => v i) hx)
            hloc_zj hφ.smooth.continuous (fun x hx => (hbox_φ x hx).1)
        obtain ⟨hint_cpd, hcell_cpd, heq_cpd⟩ :=
          TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize hc (hT.trans haT)
            hab.le hR1_pos hm_zi (hper_z.mono fun _ hx => congrArg (fun v : CMerid => v i) hx)
            hloc_z (isCoordTest_cpd j.succ hφ).smooth.continuous (fun x hx => (hbox_φ x hx).2 j.succ)
        have h_lhs_eq : (∫ x, zj x i * (liftCylTest p.c hc θ ψ x : ℂ)) =
            ∫ x, tailInd T zj x i * (liftCylTest p.c hc θ ψ x : ℂ) := by
          congr 1; funext x
          by_cases hxT : T < x.1
          · simp [tailInd, hxT]
          · have h0 : liftCylTest p.c hc θ ψ x = 0 :=
              (hbox_φ x (Or.inl fun hab_x => hxT (lt_of_lt_of_le haT hab_x.1))).1
            simp [h0]
        have h_rhs_eq : (∫ x, z₂ x i *
              (coordTranspose (![vQ0, vEta] j) dZero (liftCylTest p.c hc θ ψ) x : ℂ)) =
            -∫ x, tailInd T z₂ x i * (cpd j.succ (liftCylTest p.c hc θ ψ) x : ℂ) := by
          rw [← integral_neg]
          congr 1; funext x
          rw [TailPeriodizeAux.coordTranspose_vQ0_vEta]
          by_cases hxT : T < x.1
          · simp [tailInd, hxT]
          · have h0 : cpd j.succ (liftCylTest p.c hc θ ψ) x = 0 :=
              (hbox_φ x (Or.inl fun hab_x => hxT (lt_of_lt_of_le haT hab_x.1))).2 j.succ
            simp [h0]
        rw [h_lhs_eq, h_rhs_eq, heq_zj, heq_cpd] at hjoint
        have hs1 := (fubini_cell_slices hcell_zj).1
        have hs2 := (fubini_cell_slices hcell_cpd).1
        have hsum_zero : (∫ s in Icc a b, ∫ y in B0579.cell p.c,
              tailInd T zj (s, y) i *
                (TailPeriodizeAux.qPeriodize p.c (liftCylTest p.c hc θ ψ) s y : ℂ)) +
            (∫ s in Icc a b, ∫ y in B0579.cell p.c,
              tailInd T z₂ (s, y) i *
                (TailPeriodizeAux.qPeriodize p.c
                  (cpd j.succ (liftCylTest p.c hc θ ψ)) s y : ℂ)) = 0 := by
          rw [hjoint, neg_add_cancel]
        rw [← integral_add hs1 hs2] at hsum_zero
        refine (setIntegral_congr_fun measurableSet_Icc fun s hs => ?_).trans hsum_zero
        have hsT : T < s := lt_of_lt_of_le haT hs.1
        have h1 : ∫ y in B0579.cell p.c,
              tailInd T zj (s, y) i *
                (TailPeriodizeAux.qPeriodize p.c (liftCylTest p.c hc θ ψ) s y : ℂ) =
            (θ s : ℂ) * ∫ y in B0579.cell p.c, zj (s, y) i * (ψ y : ℂ) := by
          rw [← integral_const_mul]
          refine setIntegral_congr_fun (B0579.measurableSet_cell p.c) fun y _ => ?_
          rw [qPeriodize_liftCylTest hc θ hψ.periodic s y]
          simp [tailInd, hsT, mul_left_comm]
        have h2 : ∫ y in B0579.cell p.c,
              tailInd T z₂ (s, y) i *
                (TailPeriodizeAux.qPeriodize p.c
                  (cpd j.succ (liftCylTest p.c hc θ ψ)) s y : ℂ) =
            (θ s : ℂ) * ∫ y in B0579.cell p.c, z₂ (s, y) i * (B0579.pd j ψ y : ℂ) := by
          rw [← integral_const_mul]
          refine setIntegral_congr_fun (B0579.measurableSet_cell p.c) fun y _ => ?_
          rw [← TailPeriodizeAux.pd_qPeriodize hc hφ s j y]
          have hpd : B0579.pd j (TailPeriodizeAux.qPeriodize p.c (liftCylTest p.c hc θ ψ) s) y =
              θ s * B0579.pd j ψ y := by
            have heq_fn : TailPeriodizeAux.qPeriodize p.c (liftCylTest p.c hc θ ψ) s =
                fun w => θ s * ψ w := funext fun w => qPeriodize_liftCylTest hc θ hψ.periodic s w
            rw [heq_fn]
            unfold B0579.pd
            rw [fderiv_const_mul hψ.differentiable.differentiableAt, smul_apply,
              smul_eq_mul]
          rw [hpd]
          simp [tailInd, hsT, mul_left_comm]
        dsimp only [F]
        rw [mul_add, ← h1, ← h2]
  -- Solenoidality of z₂ for r > T
  have sol_gt : ∀ r > T, IIIa.LMWeakDivFree p.c (fun y i => z₂ (r, y) i) := by
    intro r hr ψ hψ
    let F : ℝ → ℂ := fun s =>
      (∫ y in B0579.cell p.c, z₂ (s, y) 0 * (B0579.pd 0 ψ y : ℂ)) +
        (∫ y in B0579.cell p.c, z₂ (s, y) 1 * (B0579.pd 1 ψ y : ℂ))
    obtain ⟨_, hpd0C⟩ := memLp_of_isCylTest hc (hψ.pd 0)
    obtain ⟨_, hpd1C⟩ := memLp_of_isCylTest hc (hψ.pd 1)
    have hm0 : MemLp (fun y => z₂ (r, y) 0) 2 (volume.restrict (B0579.cell p.c)) :=
      ⟨((EuclideanSpace.proj 0 : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
          (sliceMeas hz r)).aestronglyMeasurable,
        (eLpNorm_comp_le_merid p.c z₂ r 0).trans_lt (hmem r hr.le).1.eLpNorm_lt_top⟩
    have hm1 : MemLp (fun y => z₂ (r, y) 1) 2 (volume.restrict (B0579.cell p.c)) :=
      ⟨((EuclideanSpace.proj 1 : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
          (sliceMeas hz r)).aestronglyMeasurable,
        (eLpNorm_comp_le_merid p.c z₂ r 1).trans_lt (hmem r hr.le).1.eLpNorm_lt_top⟩
    change (∫ x in B0579.cell p.c,
        z₂ (r, x) 0 * (B0579.pd 0 ψ x : ℂ) + z₂ (r, x) 1 * (B0579.pd 1 ψ x : ℂ)) = 0
    have hi0_mul : IntegrableOn (fun x => z₂ (r, x) 0 * (B0579.pd 0 ψ x : ℂ)) (B0579.cell p.c) :=
      hm0.integrable_mul hpd0C
    have hi1_mul : IntegrableOn (fun x => z₂ (r, x) 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell p.c) :=
      hm1.integrable_mul hpd1C
    rw [integral_add hi0_mul hi1_mul]
    have hF_cont : ContinuousOn F (Ioi T) :=
      ((continuousOn_slice_test_pairing hc hz (fun t ht => (hmem t ht).1) hcz
          (hψ.pd 0) 0).add
        (continuousOn_slice_test_pairing hc hz (fun t ht => (hmem t ht).1) hcz
          (hψ.pd 1) 1)).mono Ioi_subset_Ici_self
    refine eq_zero_on_Ioi_of_test_integral_eq_zero hF_cont ?_ r hr
    intro a b haT hab θ hθ hts
    obtain ⟨hφ, hts_ab, R, hR_pos, _⟩ := isCoordTest_liftCylTest hc hT haT hθ hts hψ
    have hts_T : tsupport (liftCylTest p.c hc θ ψ) ⊆ Ioi T ×ˢ univ :=
      hts_ab.trans (prod_mono (fun s hs => haT.trans hs.1) Subset.rfl)
    obtain ⟨hint_sol, hsol⟩ := hz_sol.solenoidal (liftCylTest p.c hc θ ψ) hφ hts_T
    have hbox_ex : ∃ R1 : ℝ, 0 < R1 ∧
        ∀ x : Coord, (x.1 ∉ Icc a b ∨ R1 < |x.2.1| ∨ R1 < |x.2.2|) →
          liftCylTest p.c hc θ ψ x = 0 ∧
            ∀ k : Fin 3, cpd k (liftCylTest p.c hc θ ψ) x = 0 := by
      obtain ⟨_, _, R1, _, _, _, hb1⟩ := TailPeriodizeAux.coordTest_box hφ
      refine ⟨max R R1, lt_of_lt_of_le hR_pos (le_max_left _ _),
        fun x (hx : x.1 ∉ Icc a b ∨ max R R1 < |x.2.1| ∨ max R R1 < |x.2.2|) => ?_⟩
      rcases hx with h1 | h2 | h3
      · have hnot_ts : x ∉ tsupport (liftCylTest p.c hc θ ψ) := fun hxt =>
          h1 (Ioo_subset_Icc_self (hts_ab hxt).1)
        exact ⟨image_eq_zero_of_notMem_tsupport hnot_ts,
          fun k => by simp [cpd, fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot_ts]⟩
      · exact hb1 x (Or.inr (Or.inl ((le_max_right R R1).trans_lt h2)))
      · exact hb1 x (Or.inr (Or.inr ((le_max_right R R1).trans_lt h3)))
    obtain ⟨R1, hR1_pos, hbox_φ⟩ := hbox_ex
    have hloc_z : ∀ i : Fin 2, (∫⁻ s in Icc a b,
        eLpNorm (fun z => tailInd T z₂ (s, z) i) 2 (volume.restrict (B0579.cell p.c))) < ⊤ := by
      intro i
      have heq : ∫⁻ s in Icc a b,
          eLpNorm (fun z => tailInd T z₂ (s, z) i) 2 (volume.restrict (B0579.cell p.c)) =
          ∫⁻ s in Icc a b,
          eLpNorm (fun z => z₂ (s, z) i) 2 (volume.restrict (B0579.cell p.c)) := by
        refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
        simp [tailInd, lt_of_lt_of_le haT hs.1]
      rw [heq]
      exact (lintegral_mono fun s => eLpNorm_comp_le_merid p.c z₂ s i).trans_lt
        (loc_eLpNorm_lt_top_of_continuousOn_profPath (fun t ht => (hmem t ht).1) hcz haT.le)
    have hm_z : ∀ i : Fin 2, AEStronglyMeasurable (fun x : Coord => tailInd T z₂ x i) volume :=
      fun i => ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
        (stronglyMeasurable_tailInd T hz)).aestronglyMeasurable
    obtain ⟨hint0, hcell0, heq0⟩ :=
      TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize hc (hT.trans haT)
        hab.le hR1_pos (hm_z 0) (hper_z.mono fun _ hx => congrArg (fun v : CMerid => v 0) hx)
        (hloc_z 0) (isCoordTest_cpd 1 hφ).smooth.continuous (fun x hx => (hbox_φ x hx).2 1)
    obtain ⟨hint1, hcell1, heq1⟩ :=
      TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize hc (hT.trans haT)
        hab.le hR1_pos (hm_z 1) (hper_z.mono fun _ hx => congrArg (fun v : CMerid => v 1) hx)
        (hloc_z 1) (isCoordTest_cpd 2 hφ).smooth.continuous (fun x hx => (hbox_φ x hx).2 2)
    have hsol' : (∫ x, tailInd T z₂ x 0 * (cpd 1 (liftCylTest p.c hc θ ψ) x : ℂ)) +
        (∫ x, tailInd T z₂ x 1 * (cpd 2 (liftCylTest p.c hc θ ψ) x : ℂ)) = 0 := by
      rw [← integral_add hint0 hint1, ← hsol]
      congr 1; funext x
      by_cases hxT : T < x.1
      · simp [tailInd, hxT]
      · have h01 : cpd 1 (liftCylTest p.c hc θ ψ) x = 0 :=
          (hbox_φ x (Or.inl fun hab_x => hxT (lt_of_lt_of_le haT hab_x.1))).2 1
        have h02 : cpd 2 (liftCylTest p.c hc θ ψ) x = 0 :=
          (hbox_φ x (Or.inl fun hab_x => hxT (lt_of_lt_of_le haT hab_x.1))).2 2
        simp [h01, h02]
    rw [heq0, heq1, ← integral_add (fubini_cell_slices hcell0).1
      (fubini_cell_slices hcell1).1] at hsol'
    refine (setIntegral_congr_fun measurableSet_Icc fun s hs => ?_).trans hsol'
    have hsT : T < s := lt_of_lt_of_le haT hs.1
    have h_part : ∀ (j : Fin 2) (i : Fin 2),
        ∫ y in B0579.cell p.c,
          tailInd T z₂ (s, y) i *
            (TailPeriodizeAux.qPeriodize p.c
              (cpd j.succ (liftCylTest p.c hc θ ψ)) s y : ℂ) =
        (θ s : ℂ) * ∫ y in B0579.cell p.c, z₂ (s, y) i * (B0579.pd j ψ y : ℂ) := by
      intro j i
      rw [← integral_const_mul]
      refine setIntegral_congr_fun (B0579.measurableSet_cell p.c) fun y _ => ?_
      rw [← TailPeriodizeAux.pd_qPeriodize hc hφ s j y]
      have heq_fn : TailPeriodizeAux.qPeriodize p.c (liftCylTest p.c hc θ ψ) s =
          fun w => θ s * ψ w := funext fun w => qPeriodize_liftCylTest hc θ hψ.periodic s w
      have hpd : B0579.pd j (TailPeriodizeAux.qPeriodize p.c (liftCylTest p.c hc θ ψ) s) y =
          θ s * B0579.pd j ψ y := by
        rw [heq_fn]
        unfold B0579.pd
        rw [fderiv_const_mul hψ.differentiable.differentiableAt, smul_apply,
          smul_eq_mul]
      rw [hpd]
      simp [tailInd, hsT, mul_left_comm]
    dsimp only [F]
    rw [mul_add, ← h_part 0 0, ← h_part 1 1]
    rfl
  -- Derive solenoidality of a weak derivative u_j from solenoidality of u
  have sol_of_weak : ∀ {u uj : B0579.Plane → CMerid} (j : Fin 2),
      (∀ i : Fin 2, IIIa.HasWeakCellDerivC p.c j (fun y => u y i) (fun y => uj y i)) →
      IIIa.LMWeakDivFree p.c (fun y i => u y i) →
      IIIa.LMWeakDivFree p.c (fun y i => uj y i) := by
    intro u uj j hw hsol_u ψ hψ
    have hψ0 : B0579.IsCylTest p.c (B0579.pd 0 ψ) := hψ.pd 0
    have hψ1 : B0579.IsCylTest p.c (B0579.pd 1 ψ) := hψ.pd 1
    have hψj : B0579.IsCylTest p.c (B0579.pd j ψ) := hψ.pd j
    have hi0 : IntegrableOn (fun x => uj x 0 * (B0579.pd 0 ψ x : ℂ)) (B0579.cell p.c) :=
      ((hw 0).1 (B0579.pd 0 ψ) hψ0).2
    have hi1 : IntegrableOn (fun x => uj x 1 * (B0579.pd 1 ψ x : ℂ)) (B0579.cell p.c) :=
      ((hw 1).1 (B0579.pd 1 ψ) hψ1).2
    have hd0 : ∫ x in B0579.cell p.c, uj x 0 * (B0579.pd 0 ψ x : ℂ) =
        -∫ x in B0579.cell p.c, u x 0 * (B0579.pd j (B0579.pd 0 ψ) x : ℂ) :=
      neg_eq_iff_eq_neg.1 ((hw 0).2 (B0579.pd 0 ψ) hψ0).symm
    have hd1 : ∫ x in B0579.cell p.c, uj x 1 * (B0579.pd 1 ψ x : ℂ) =
        -∫ x in B0579.cell p.c, u x 1 * (B0579.pd j (B0579.pd 1 ψ) x : ℂ) :=
      neg_eq_iff_eq_neg.1 ((hw 1).2 (B0579.pd 1 ψ) hψ1).symm
    have hi0' : IntegrableOn (fun x => u x 0 * (B0579.pd j (B0579.pd 0 ψ) x : ℂ)) (B0579.cell p.c) :=
      ((hw 0).1 (B0579.pd 0 ψ) hψ0).1
    have hi1' : IntegrableOn (fun x => u x 1 * (B0579.pd j (B0579.pd 1 ψ) x : ℂ)) (B0579.cell p.c) :=
      ((hw 1).1 (B0579.pd 1 ψ) hψ1).1
    change (∫ x in B0579.cell p.c,
        uj x 0 * (B0579.pd 0 ψ x : ℂ) + uj x 1 * (B0579.pd 1 ψ x : ℂ)) = 0
    rw [integral_add hi0 hi1, hd0, hd1, ← neg_add, ← integral_add hi0' hi1']
    have hcomm : ∀ (l : Fin 2) (y : B0579.Plane),
        B0579.pd j (B0579.pd l ψ) y = B0579.pd l (B0579.pd j ψ) y := by
      intro l y
      unfold B0579.pd
      have hsymm := (hψ.smooth.contDiffAt (x := y)).isSymmSndFDerivAt (by simp)
      have hf2 : ∀ v w : B0579.Plane,
          fderiv ℝ (fun z => fderiv ℝ ψ z v) y w = fderiv ℝ (fderiv ℝ ψ) y w v := by
        intro v w
        have hd_fd : DifferentiableAt ℝ (fderiv ℝ ψ) y :=
          ((contDiff_infty_iff_fderiv.1 hψ.smooth).2.differentiable (by simp)).differentiableAt
        have hcomp := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp y hd_fd.hasFDerivAt
        exact congrArg (fun L => L w) hcomp.fderiv
      rw [hf2, hf2]
      exact hsymm.eq (B0579.dir j) (B0579.dir l)
    have hcongr : (fun y => u y 0 * (B0579.pd j (B0579.pd 0 ψ) y : ℂ) +
          u y 1 * (B0579.pd j (B0579.pd 1 ψ) y : ℂ)) =
        fun y => u y 0 * (B0579.pd 0 (B0579.pd j ψ) y : ℂ) +
          u y 1 * (B0579.pd 1 (B0579.pd j ψ) y : ℂ) := by
      funext y; rw [hcomm 0 y, hcomm 1 y]
    rw [hcongr, hsol_u (B0579.pd j ψ) hψj, neg_zero]
  intro r hr
  rcases eq_or_lt_of_le hr with rfl | hgt
  · have hw0 : ∀ i : Fin 2, IIIa.HasWeakCellDerivC p.c 0 (fun y => z₂ (T, y) i) (fun y => zq₂ (T, y) i) :=
      hzT.weak_q
    have hw1 : ∀ i : Fin 2, IIIa.HasWeakCellDerivC p.c 1 (fun y => z₂ (T, y) i) (fun y => zη₂ (T, y) i) :=
      hzT.weak_eta
    have hsolT : IIIa.LMWeakDivFree p.c (fun y i => z₂ (T, y) i) :=
      fun ψ hψ => (hzT.solenoidal ψ hψ).2
    exact ⟨fun i => ⟨hw0 i, hw1 i⟩, hsolT, sol_of_weak 0 hw0 hsolT, sol_of_weak 1 hw1 hsolT⟩
  · have hw0 : ∀ i : Fin 2, IIIa.HasWeakCellDerivC p.c 0 (fun y => z₂ (r, y) i) (fun y => zq₂ (r, y) i) :=
      weak_gt 0 zq₂ hzq (fun t ht => (hmem t ht).2.1) hczq hper_zq hz_sol.weak_q r hgt
    have hw1 : ∀ i : Fin 2, IIIa.HasWeakCellDerivC p.c 1 (fun y => z₂ (r, y) i) (fun y => zη₂ (r, y) i) :=
      weak_gt 1 zη₂ hzη (fun t ht => (hmem t ht).2.2) hczη hper_zη hz_sol.weak_eta r hgt
    have hsolr : IIIa.LMWeakDivFree p.c (fun y i => z₂ (r, y) i) := sol_gt r hgt
    exact ⟨fun i => ⟨hw0 i, hw1 i⟩, hsolr, sol_of_weak 0 hw0 hsolr, sol_of_weak 1 hw1 hsolr⟩

/-- Slice regularity and Bochner `L¹` integrability on `[T, t]` for the source `(g, gq, gη)`. -/
private lemma source_slice_regularity {c T : ℝ} (hc : 0 < c) (hT : 0 < T)
    {g gq gη : CProf} (hg_src : IsCylSourceH1 c g gq gη)
    (hg_int : (∫⁻ s in Ioi T, sliceH1Norm c g gq gη s) < ⊤) :
    (∀ a b : ℝ, T ≤ a → (∫⁻ s in Icc a b, sliceH1Norm c g gq gη s) < ⊤) ∧
    (∀ t : ℝ, T ≤ t →
      IntegrableOn (fun s => (sliceH1Norm c g gq gη s).toReal) (Icc T t) ∧
      IntegrableOn (profPath c g) (Icc T t) ∧
      IntegrableOn (profPath c gq) (Icc T t) ∧
      IntegrableOn (profPath c gη) (Icc T t)) ∧
    (∀ᵐ r ∂volume, T < r →
      sliceH1Norm c g gq gη r < ⊤ ∧
      (∀ i : Fin 2,
        IIIa.HasWeakCellDerivC c 0 (fun y => g (r, y) i) (fun y => gq (r, y) i) ∧
        IIIa.HasWeakCellDerivC c 1 (fun y => g (r, y) i) (fun y => gη (r, y) i))) := by
  have hm_H1 : Measurable (sliceH1Norm c g gq gη) :=
    CylProjectionSub.measurable_sliceH1Norm_cp c hg_src.sm_g hg_src.sm_gq hg_src.sm_gη
  have hloc : ∀ a b : ℝ, T ≤ a → (∫⁻ s in Icc a b, sliceH1Norm c g gq gη s) < ⊤ := by
    intro a b ha
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    have hsub : Ioc a b ⊆ Ioi T := fun s hs => lt_of_le_of_lt ha hs.1
    exact (lintegral_mono_set hsub).trans_lt hg_int
  have hae_fin_Ioi : ∀ᵐ r ∂(volume.restrict (Ioi T)), sliceH1Norm c g gq gη r < ⊤ :=
    ae_lt_top hm_H1 hg_int.ne
  have hae_fin : ∀ᵐ r ∂volume, T < r → sliceH1Norm c g gq gη r < ⊤ :=
    (ae_restrict_iff' measurableSet_Ioi).1 hae_fin_Ioi
  have hae_jq := FlatBvSliceGoodAeNeeded.jointWeakToSlice_proof c hc 0 g gq
    hg_src.sm_g hg_src.sm_gq hg_src.periodic_g hg_src.periodic_gq hg_src.weak_q
  have hae_jη := FlatBvSliceGoodAeNeeded.jointWeakToSlice_proof c hc 1 g gη
    hg_src.sm_g hg_src.sm_gη hg_src.periodic_g hg_src.periodic_gη hg_src.weak_eta
  refine ⟨hloc, ?_, ?_⟩
  · intro t ht
    have hlt := hloc T t le_rfl
    have hint_H1 : IntegrableOn (fun s => (sliceH1Norm c g gq gη s).toReal) (Icc T t) :=
      integrable_toReal_of_lintegral_ne_top hm_H1.aemeasurable hlt.ne
    have mk_boch : ∀ (w : CProf), StronglyMeasurable w →
        (∀ s, cylSliceL2 c (fun y => w (s, y)) ≤ sliceH1Norm c g gq gη s) →
        IntegrableOn (profPath c w) (Icc T t) := by
      intro w hw hle
      have hmeas_path : AEStronglyMeasurable (profPath c w) (volume.restrict (Icc T t)) := by
        have hm_lm : Measurable (fun p : Coord => IIIa.lmReal (fun i => w p i)) :=
          (IIIa.lmReal_continuous.comp (continuous_pi fun i =>
            (EuclideanSpace.proj (𝕜 := ℂ) i).continuous)).measurable.comp hw.measurable
        exact (stronglyMeasurable_toPathLq (μ := volume.restrict (B0579.cell c))
          hm_lm.stronglyMeasurable).aestronglyMeasurable
      refine Integrable.mono' hint_H1 hmeas_path ?_
      have hae_Icc : ∀ᵐ s ∂(volume.restrict (Icc T t)), sliceH1Norm c g gq gη s < ⊤ :=
        ae_lt_top hm_H1 hlt.ne
      filter_upwards [hae_Icc] with s hs_fin
      have hw_fin : eLpNorm (fun y => w (s, y)) 2 (volume.restrict (B0579.cell c)) < ⊤ :=
        (hle s).trans_lt hs_fin
      have hw_mem : MemLp (fun y => w (s, y)) 2 (volume.restrict (B0579.cell c)) :=
        ⟨(sliceMeas hw s).aestronglyMeasurable, hw_fin⟩
      rw [norm_profPath_eq hw_mem]
      exact ENNReal.toReal_mono hs_fin.ne (hle s)
    refine ⟨hint_H1,
      mk_boch g hg_src.sm_g (fun _ => le_self_add.trans le_self_add),
      mk_boch gq hg_src.sm_gq (fun _ => le_add_self.trans le_self_add),
      mk_boch gη hg_src.sm_gη (fun _ => le_add_self)⟩
  · filter_upwards [hae_fin, hae_jq, hae_jη] with r hfin hjq hjη hrT
    have hr0 : 0 < r := hT.trans hrT
    have hfin_r := hfin hrT
    obtain ⟨hmg, hmgq, hmgη⟩ :=
      memLp_slice_of_sliceH1Norm_lt_top hg_src.sm_g hg_src.sm_gq hg_src.sm_gη hfin_r
    exact ⟨hfin_r, fun i => ⟨hjq hr0 hmg hmgq i, hjη hr0 hmg hmgη i⟩⟩

/-! ## Section 2: Extended `IsH1DivFreeTest` slice weak equation on `(T, ∞)` -/

private lemma measurable_tailInd_real {T : ℝ} {f : Coord → ℝ}
    (hf : ContinuousOn f {x : Coord | T < x.1}) :
    Measurable (fun x : Coord => if T < x.1 then f x else 0) := by
  classical
  have hopen : IsOpen {x : Coord | T < x.1} := isOpen_lt continuous_const continuous_fst
  have heq : (fun x : Coord => if T < x.1 then f x else 0) =
      ({x : Coord | T < x.1}).piecewise f 0 := by
    funext x; by_cases hx : T < x.1 <;> simp [Set.piecewise, hx]
  rw [heq]
  exact hf.measurable_piecewise continuousOn_const hopen.measurableSet

private lemma stronglyMeasurable_tailInd_flatBv {ν c T : ℝ} (hT : 0 < T)
    (tr : B0140.TrainSol ν c) {z zq zη : CProf}
    (hz : StronglyMeasurable z) (hzq : StronglyMeasurable zq) (hzη : StronglyMeasurable zη) :
    StronglyMeasurable (tailInd T (flatBv tr z zq zη)) := by
  have hsub : {x : Coord | T < x.1} ⊆ FlatBvWL.U0 := fun x hx => ⟨hT.trans hx, trivial⟩
  have hcv : ∀ k : Fin 2, ContinuousOn (fun x : Coord => tr.v x.1 x.2 k) {x : Coord | T < x.1} :=
    fun k => (FlatBvWL.gC_contDiffOn tr k).continuousOn.mono hsub
  have hcd : ∀ (d : ℝ × ℝ) (k : Fin 2),
      ContinuousOn (fun x : Coord => trD1 tr d x.1 x.2 k) {x : Coord | T < x.1} := fun d k =>
    ((FlatBvWL.gD_contDiffOn tr k d).continuousOn.mono hsub).congr fun x hx =>
      (FlatBvWL.gD_eq tr k d (hT.trans hx)).symm
  have hm_prod : ∀ {A : Coord → ℝ} {w : CProf},
      ContinuousOn A {x : Coord | T < x.1} → StronglyMeasurable w → ∀ i : Fin 2,
      Measurable (fun x : Coord => if T < x.1 then (A x : ℂ) * w x i else 0) := by
    intro A w hA hw i
    have heq : (fun x : Coord => if T < x.1 then (A x : ℂ) * w x i else 0) =
        fun x => (((if T < x.1 then A x else 0 : ℝ) : ℂ) *
          ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ) (tailInd T w x))) := by
      funext x; by_cases hx : T < x.1 <;> simp [tailInd, hx]
    rw [heq]
    exact (Complex.measurable_ofReal.comp (measurable_tailInd_real hA)).mul
      (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
        (stronglyMeasurable_tailInd T hw)).measurable)
  have hm_coords : ∀ i : Fin 2, Measurable (fun x : Coord => tailInd T (flatBv tr z zq zη) x i) := by
    intro i
    have heq : (fun x : Coord => tailInd T (flatBv tr z zq zη) x i) = fun x =>
        (if T < x.1 then ((tr.v x.1 x.2 0 : ℝ) : ℂ) * zq x i else 0) +
        (if T < x.1 then ((tr.v x.1 x.2 1 : ℝ) : ℂ) * zη x i else 0) +
        (if T < x.1 then ((trD1 tr (1, 0) x.1 x.2 i : ℝ) : ℂ) * z x 0 else 0) +
        (if T < x.1 then ((trD1 tr (0, 1) x.1 x.2 i : ℝ) : ℂ) * z x 1 else 0) := by
      funext x
      by_cases hx : T < x.1
      · simp only [tailInd, hx, ↓reduceIte, FlatBvWL.flatBv_apply]
        ring
      · simp [tailInd, hx]
    rw [heq]
    exact (((hm_prod (hcv 0) hzq i).add (hm_prod (hcv 1) hzη i)).add
      (hm_prod (hcd (1, 0) i) hz 0)).add (hm_prod (hcd (0, 1) i) hz 1)
  have heq_toLp : tailInd T (flatBv tr z zq zη) =
      fun x => WithLp.toLp 2 (fun i : Fin 2 => tailInd T (flatBv tr z zq zη) x i) :=
    funext fun _ => rfl
  rw [heq_toLp]
  exact ((PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ hm_coords)).stronglyMeasurable

private lemma fderiv_periodic_plane_aux {c : ℝ} {f : B0579.Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hper : ∀ z : B0579.Plane, f (z.1 + c, z.2) = f z)
    (d : ℝ × ℝ) (z : B0579.Plane) :
    fderiv ℝ f (z.1 + c, z.2) d = fderiv ℝ f z d := by
  have hshift : HasFDerivAt (fun w : B0579.Plane => w + (c, (0 : ℝ)))
      (ContinuousLinearMap.id ℝ B0579.Plane) z := by
    simpa using (hasFDerivAt_id z).add_const (c, (0 : ℝ))
  have hdiff : DifferentiableAt ℝ f (z + (c, (0 : ℝ))) :=
    (hf.differentiable (by simp)).differentiableAt
  have hcomp := hdiff.hasFDerivAt.comp z hshift
  have hfun : (f ∘ fun w : B0579.Plane => w + (c, (0 : ℝ))) = f := by
    funext w
    change f (w.1 + c, w.2 + 0) = f w
    rw [add_zero, hper w]
  rw [hfun] at hcomp
  have heq : fderiv ℝ f z = fderiv ℝ f (z + (c, (0 : ℝ))) := by
    simpa using hcomp.fderiv
  have hz : (z.1 + c, z.2) = z + (c, (0 : ℝ)) := by ext <;> simp
  rw [hz, ← heq]

private lemma qPeriodic_tailInd_flatBv {ν c T : ℝ} (hT : 0 < T) (tr : B0140.TrainSol ν c)
    {z zq zη : CProf}
    (hpz : QPeriodic c (tailInd T z)) (hpzq : QPeriodic c (tailInd T zq))
    (hpzη : QPeriodic c (tailInd T zη)) :
    QPeriodic c (tailInd T (flatBv tr z zq zη)) := by
  filter_upwards [hpz, hpzq, hpzη] with x hxz hxzq hxzη
  have hfst : (qShift c x).1 = x.1 := rfl
  by_cases hxT : T < x.1
  · have hs : 0 ≤ x.1 := (hT.trans hxT).le
    have hxz' : z (qShift c x) = z x := by simpa [tailInd, hfst, hxT] using hxz
    have hxzq' : zq (qShift c x) = zq x := by simpa [tailInd, hfst, hxT] using hxzq
    have hxzη' : zη (qShift c x) = zη x := by simpa [tailInd, hfst, hxT] using hxzη
    simp only [tailInd, hfst, hxT, ↓reduceIte]
    ext i
    simp only [FlatBvWL.flatBv_apply, qShift]
    have hd1 : ∀ d : ℝ × ℝ, trD1 tr d x.1 (x.2.1 + c, x.2.2) i = trD1 tr d x.1 x.2 i :=
      fun d => fderiv_periodic_plane_aux (IIIa.AdvectionEnergyAux.contDiff_train_comp tr hs i)
        (fun w => congrArg (fun v => v i) (tr.isTrain.periodic_v x.1 hs w)) d x.2
    change ((tr.v x.1 (x.2.1 + c, x.2.2) 0 : ℝ) : ℂ) * zq (qShift c x) i +
        ((tr.v x.1 (x.2.1 + c, x.2.2) 1 : ℝ) : ℂ) * zη (qShift c x) i +
        z (qShift c x) 0 * ((trD1 tr (1, 0) x.1 (x.2.1 + c, x.2.2) i : ℝ) : ℂ) +
        z (qShift c x) 1 * ((trD1 tr (0, 1) x.1 (x.2.1 + c, x.2.2) i : ℝ) : ℂ) = _
    rw [tr.isTrain.periodic_v x.1 hs x.2, hd1 (1, 0), hd1 (0, 1), hxz', hxzq', hxzη']
  · simp [tailInd, hxT]

private lemma trD1_bound_of_supNormD_one {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr) {s S : ℝ} (hs0 : 0 ≤ s) (hsS : s ≤ S)
    (y : B0579.Plane) (i : Fin 2) :
    |trD1 tr (1, 0) s y i| ≤ (B0277.supNormD 1 (tr.v s)).toReal ∧
      |trD1 tr (0, 1) s y i| ≤ (B0277.supNormD 1 (tr.v s)).toReal := by
  obtain ⟨_, _, h1⟩ := IIIa.AdvectionEnergyAux.supNormD_one_bound_on tr htr (hs0.trans hsS)
  have hpt := (h1 s ⟨hs0, hsS⟩).2.2 y
  have hv_diff : DifferentiableAt ℝ (tr.v s) y :=
    ((IIIa.AdvectionEnergyAux.contDiff_train_slice tr hs0).differentiable (by simp)).differentiableAt
  have hcomp : fderiv ℝ (fun z => tr.v s z i) y =
      (EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).comp (fderiv ℝ (tr.v s) y) :=
    ((EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).hasFDerivAt.comp y
      hv_diff.hasFDerivAt).fderiv
  have mk_le : ∀ d : B0579.Plane, ‖d‖ = 1 →
      |trD1 tr d s y i| ≤ (B0277.supNormD 1 (tr.v s)).toReal := by
    intro d hd
    unfold trD1
    rw [hcomp]
    change |(fderiv ℝ (tr.v s) y d) i| ≤ (B0277.supNormD 1 (tr.v s)).toReal
    calc |(fderiv ℝ (tr.v s) y d) i|
        ≤ ‖fderiv ℝ (tr.v s) y d‖ := Real.norm_eq_abs _ ▸ PiLp.norm_apply_le (fderiv ℝ (tr.v s) y d) i
      _ ≤ ‖fderiv ℝ (tr.v s) y‖ * ‖d‖ := ContinuousLinearMap.le_opNorm _ d
      _ = ‖fderiv ℝ (tr.v s) y‖ := by rw [hd, mul_one]
      _ ≤ (B0277.supNormD 1 (tr.v s)).toReal := hpt
  exact ⟨mk_le (1, 0) (by simp [Prod.norm_def]), mk_le (0, 1) (by simp [Prod.norm_def])⟩

private lemma memLp_slice_flatBv_on {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr) {z zq zη : CProf}
    (hz : StronglyMeasurable z) (hzq : StronglyMeasurable zq) (hzη : StronglyMeasurable zη)
    {a b : ℝ} (ha0 : 0 < a) (hab : a ≤ b)
    (hmem : ∀ s ∈ Icc a b,
      MemLp (fun y => z (s, y)) 2 (volume.restrict (B0579.cell c)) ∧
      MemLp (fun y => zq (s, y)) 2 (volume.restrict (B0579.cell c)) ∧
      MemLp (fun y => zη (s, y)) 2 (volume.restrict (B0579.cell c)))
    (hcz : ContinuousOn (profPath c z) (Icc a b))
    (hczq : ContinuousOn (profPath c zq) (Icc a b))
    (hczη : ContinuousOn (profPath c zη) (Icc a b)) :
    ∃ C_bv : ℝ, 0 ≤ C_bv ∧ ∀ s ∈ Icc a b, ∀ i : Fin 2,
      MemLp (fun y => flatBv tr z zq zη (s, y) i) 2 (volume.restrict (B0579.cell c)) ∧
      (eLpNorm (fun y => flatBv tr z zq zη (s, y) i) 2
        (volume.restrict (B0579.cell c))).toReal ≤ C_bv ∧
      eLpNorm (fun y => flatBv tr z zq zη (s, y) i) 2
        (volume.restrict (B0579.cell c)) ≤ ENNReal.ofReal C_bv := by
  have hb0 : 0 ≤ b := ha0.le.trans hab
  obtain ⟨Mv, hMv_pos, hMv⟩ := IIIa.AdvectionEnergyAux.trainVel_bound_le tr htr hb0
  obtain ⟨Md, hMd0, hMd⟩ := IIIa.AdvectionEnergyAux.supNormD_one_bound_on tr htr hb0
  obtain ⟨Mz0, hMz0⟩ := isCompact_Icc.exists_bound_of_continuousOn hcz
  obtain ⟨Mzq0, hMzq0⟩ := isCompact_Icc.exists_bound_of_continuousOn hczq
  obtain ⟨Mzη0, hMzη0⟩ := isCompact_Icc.exists_bound_of_continuousOn hczη
  let Mz : ℝ := max 0 Mz0
  let Mzq : ℝ := max 0 Mzq0
  let Mzη : ℝ := max 0 Mzη0
  let C_bv : ℝ := Mv * (Mzq + Mzη) + 2 * Md * Mz
  have hC0 : 0 ≤ C_bv := by
    dsimp [C_bv, Mz, Mzq, Mzη]
    positivity
  refine ⟨C_bv, hC0, fun s hs i => ?_⟩
  have hs0 : 0 < s := lt_of_lt_of_le ha0 hs.1
  have hms := hmem s hs
  have hm_comp : ∀ (w : CProf), StronglyMeasurable w →
      MemLp (fun y => w (s, y)) 2 (volume.restrict (B0579.cell c)) → ∀ k : Fin 2,
      MemLp (fun y => w (s, y) k) 2 (volume.restrict (B0579.cell c)) ∧
      eLpNorm (fun y => w (s, y) k) 2 (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal ‖profPath c w s‖ := by
    intro w hw hmw k
    refine ⟨⟨((EuclideanSpace.proj k : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
        (sliceMeas hw s)).aestronglyMeasurable,
      (eLpNorm_comp_le_merid c w s k).trans_lt hmw.eLpNorm_lt_top⟩, ?_⟩
    rw [norm_profPath_eq hmw]
    unfold cylSliceL2
    rw [ENNReal.ofReal_toReal hmw.eLpNorm_ne_top]
    exact eLpNorm_comp_le_merid c w s k
  obtain ⟨hm_zq, hle_zq⟩ := hm_comp zq hzq hms.2.1 i
  obtain ⟨hm_zη, hle_zη⟩ := hm_comp zη hzη hms.2.2 i
  obtain ⟨hm_z0, hle_z0⟩ := hm_comp z hz hms.1 0
  obtain ⟨hm_z1, hle_z1⟩ := hm_comp z hz hms.1 1
  have hv_cont : ∀ k : Fin 2, Continuous (fun y : B0579.Plane => ((tr.v s y k : ℝ) : ℂ)) :=
    fun k => Complex.continuous_ofReal.comp (IIIa.AdvectionEnergyAux.contDiff_train_comp tr hs0.le k).continuous
  have hd_cont : ∀ d : B0579.Plane,
      Continuous (fun y : B0579.Plane => ((trD1 tr d s y i : ℝ) : ℂ)) := fun d =>
    Complex.continuous_ofReal.comp
      ((((contDiff_infty_iff_fderiv.1 (IIIa.AdvectionEnergyAux.contDiff_train_comp tr hs0.le i)).2).clm_apply
        contDiff_const).continuous)
  have hv_bdd : ∀ (k : Fin 2) (y : B0579.Plane), ‖((tr.v s y k : ℝ) : ℂ)‖ ≤ Mv := by
    intro k y
    have := hMv s hs.2 y k
    simpa [IIIa.trainVel, hs0.le] using this
  have hd_bdd1 : ∀ y : B0579.Plane, ‖((trD1 tr (1, 0) s y i : ℝ) : ℂ)‖ ≤ Md := fun y => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (trD1_bound_of_supNormD_one tr htr hs0.le hs.2 y i).1.trans (hMd s ⟨hs0.le, hs.2⟩).2.1
  have hd_bdd2 : ∀ y : B0579.Plane, ‖((trD1 tr (0, 1) s y i : ℝ) : ℂ)‖ ≤ Md := fun y => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (trD1_bound_of_supNormD_one tr htr hs0.le hs.2 y i).2.trans (hMd s ⟨hs0.le, hs.2⟩).2.1
  have mul_mem : ∀ {A : B0579.Plane → ℂ} {f : B0579.Plane → ℂ} {K B : ℝ},
      Continuous A → 0 ≤ K → 0 ≤ B → (∀ y, ‖A y‖ ≤ K) →
      MemLp f 2 (volume.restrict (B0579.cell c)) →
      eLpNorm f 2 (volume.restrict (B0579.cell c)) ≤ ENNReal.ofReal B →
      MemLp (fun y => A y * f y) 2 (volume.restrict (B0579.cell c)) ∧
      eLpNorm (fun y => A y * f y) 2 (volume.restrict (B0579.cell c)) ≤ ENNReal.ofReal (K * B) := by
    intro A f K B hA hK _hB hAb hf hfB
    have hmA : AEStronglyMeasurable A (volume.restrict (B0579.cell c)) := hA.aestronglyMeasurable
    have hel : eLpNorm (fun y => A y * f y) 2 (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal (K * B) := by
      calc eLpNorm (fun y => A y * f y) 2 (volume.restrict (B0579.cell c))
          ≤ eLpNorm ((K : ℂ) • f) 2 (volume.restrict (B0579.cell c)) := by
            refine eLpNorm_mono_enorm fun y => ?_
            change ‖A y * f y‖ₑ ≤ ‖(K : ℂ) * f y‖ₑ
            rw [enorm_mul, enorm_mul]
            have hA_le_K : ‖A y‖ₑ ≤ ‖(K : ℂ)‖ₑ := by
              rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg hK]
              exact ENNReal.ofReal_le_ofReal (hAb y)
            exact mul_le_mul_of_nonneg_right hA_le_K zero_le
        _ = ‖(K : ℂ)‖ₑ * eLpNorm f 2 (volume.restrict (B0579.cell c)) :=
            eLpNorm_const_smul (K : ℂ) f 2 _
        _ = ENNReal.ofReal K * eLpNorm f 2 (volume.restrict (B0579.cell c)) := by
            rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK]
        _ ≤ ENNReal.ofReal K * ENNReal.ofReal B := mul_le_mul_right hfB _
        _ = ENNReal.ofReal (K * B) := (ENNReal.ofReal_mul hK).symm
    exact ⟨⟨hmA.mul hf.aestronglyMeasurable, hel.trans_lt ENNReal.ofReal_lt_top⟩, hel⟩
  have hBz : ‖profPath c z s‖ ≤ Mz := (hMz0 s hs).trans (le_max_right 0 Mz0)
  have hBzq : ‖profPath c zq s‖ ≤ Mzq := (hMzq0 s hs).trans (le_max_right 0 Mzq0)
  have hBzη : ‖profPath c zη s‖ ≤ Mzη := (hMzη0 s hs).trans (le_max_right 0 Mzη0)
  obtain ⟨hm1, he1⟩ := mul_mem (hv_cont 0) hMv_pos.le (le_max_left 0 Mzq0) (hv_bdd 0)
    hm_zq (hle_zq.trans (ENNReal.ofReal_le_ofReal hBzq))
  obtain ⟨hm2, he2⟩ := mul_mem (hv_cont 1) hMv_pos.le (le_max_left 0 Mzη0) (hv_bdd 1)
    hm_zη (hle_zη.trans (ENNReal.ofReal_le_ofReal hBzη))
  obtain ⟨hm3, he3⟩ := mul_mem (hd_cont (1, 0)) hMd0 (le_max_left 0 Mz0) hd_bdd1
    hm_z0 (hle_z0.trans (ENNReal.ofReal_le_ofReal hBz))
  obtain ⟨hm4, he4⟩ := mul_mem (hd_cont (0, 1)) hMd0 (le_max_left 0 Mz0) hd_bdd2
    hm_z1 (hle_z1.trans (ENNReal.ofReal_le_ofReal hBz))
  have hsum_eq : (fun y => flatBv tr z zq zη (s, y) i) = fun y =>
      (((tr.v s y 0 : ℝ) : ℂ) * zq (s, y) i + ((tr.v s y 1 : ℝ) : ℂ) * zη (s, y) i) +
      (((trD1 tr (1, 0) s y i : ℝ) : ℂ) * z (s, y) 0 +
        ((trD1 tr (0, 1) s y i : ℝ) : ℂ) * z (s, y) 1) := by
    funext y
    simp only [FlatBvWL.flatBv_apply]
    ring
  have hm_all : MemLp (fun y => flatBv tr z zq zη (s, y) i) 2 (volume.restrict (B0579.cell c)) := by
    rw [hsum_eq]
    exact (hm1.add hm2).add (hm3.add hm4)
  have he_all : eLpNorm (fun y => flatBv tr z zq zη (s, y) i) 2
      (volume.restrict (B0579.cell c)) ≤ ENNReal.ofReal C_bv := by
    rw [hsum_eq]
    have htri1 := (eLpNorm_add_le (hm1.add hm2).aestronglyMeasurable
      (hm3.add hm4).aestronglyMeasurable one_le_two).trans
      (add_le_add
        (eLpNorm_add_le hm1.aestronglyMeasurable hm2.aestronglyMeasurable one_le_two)
        (eLpNorm_add_le hm3.aestronglyMeasurable hm4.aestronglyMeasurable one_le_two))
    refine htri1.trans ((add_le_add (add_le_add he1 he2) (add_le_add he3 he4)).trans ?_)
    have hnn1 : 0 ≤ Mv * Mzq := mul_nonneg hMv_pos.le (le_max_left 0 Mzq0)
    have hnn2 : 0 ≤ Mv * Mzη := mul_nonneg hMv_pos.le (le_max_left 0 Mzη0)
    have hnn3 : 0 ≤ Md * Mz := mul_nonneg hMd0 (le_max_left 0 Mz0)
    rw [← ENNReal.ofReal_add hnn1 hnn2, ← ENNReal.ofReal_add hnn3 hnn3,
      ← ENNReal.ofReal_add (add_nonneg hnn1 hnn2) (add_nonneg hnn3 hnn3)]
    exact ENNReal.ofReal_le_ofReal (by dsimp [C_bv]; linarith)
  have htoReal : (eLpNorm (fun y => flatBv tr z zq zη (s, y) i) 2
      (volume.restrict (B0579.cell c))).toReal ≤ C_bv := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top he_all
    rwa [ENNReal.toReal_ofReal hC0] at this
  exact ⟨hm_all, htoReal, he_all⟩

private def sliceWeakTerm (p : Params) (g z₂ zq₂ zη₂ : CProf)
    (θ : ℝ → ℝ) (φ : B0579.Plane → Fin 2 → ℝ) (s : ℝ) : ℂ :=
  -((deriv θ s : ℝ) : ℂ) * (∫ y in B0579.cell p.c, ∑ i : Fin 2, z₂ (s, y) i * (φ y i : ℂ)) +
    (θ s : ℂ) * ((p.ν : ℂ) * (∫ y in B0579.cell p.c, ∑ i : Fin 2,
        (zq₂ (s, y) i * (B0579.pd 0 (fun w => φ w i) y : ℂ) +
          zη₂ (s, y) i * (B0579.pd 1 (fun w => φ w i) y : ℂ))) +
      (∫ y in B0579.cell p.c, ∑ i : Fin 2,
        flatBv p.train z₂ zq₂ zη₂ (s, y) i * (φ y i : ℂ)) -
      (∫ y in B0579.cell p.c, ∑ i : Fin 2, g (s, y) i * (φ y i : ℂ)))

private lemma integrableOn_weighted_cell_pairing {c T a b : ℝ} (hT : 0 < T) (haT : T < a)
    {w : CProf} (hw_sm : StronglyMeasurable w)
    {α : ℝ → ℝ} (hα : Continuous α)
    {ψ : B0579.Plane → ℝ} (hψ_meas : Measurable ψ)
    (hψ_mem : MemLp (fun y => (ψ y : ℂ)) 2 (volume.restrict (B0579.cell c)))
    {W : ℝ → ℝ} (hW_int : IntegrableOn W (Icc a b))
    (hW_bound : ∀ᵐ s ∂(volume.restrict (Icc a b)), ∀ i : Fin 2,
      MemLp (fun y => w (s, y) i) 2 (volume.restrict (B0579.cell c)) ∧
      (eLpNorm (fun y => w (s, y) i) 2 (volume.restrict (B0579.cell c))).toReal ≤ W s)
    (i : Fin 2) :
    IntegrableOn (fun s => (α s : ℂ) * ∫ y in B0579.cell c, w (s, y) i * (ψ y : ℂ)) (Icc a b) := by
  let _ := hT; let _ := haT
  obtain ⟨Mα0, hMα0⟩ := isCompact_Icc.exists_bound_of_continuousOn hα.continuousOn
  let Mα : ℝ := max 0 Mα0
  let Mψ : ℝ := (eLpNorm (fun y => (ψ y : ℂ)) 2 (volume.restrict (B0579.cell c))).toReal
  have hf_meas : Measurable (fun p : Coord => w p i * (ψ p.2 : ℂ)) :=
    (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable hw_sm).measurable).mul
      (Complex.measurable_ofReal.comp (hψ_meas.comp measurable_snd))
  have hmeas_s : StronglyMeasurable (fun s : ℝ => ∫ y in B0579.cell c, w (s, y) i * (ψ y : ℂ)) :=
    hf_meas.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (B0579.cell c))
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ => (α s : ℂ) * ∫ y in B0579.cell c, w (s, y) i * (ψ y : ℂ))
      (volume.restrict (Icc a b)) :=
    ((Complex.continuous_ofReal.comp hα).stronglyMeasurable.mul hmeas_s).aestronglyMeasurable
  refine Integrable.mono' (hW_int.const_mul (Mα * Mψ)) hmeas ?_
  filter_upwards [hW_bound, ae_restrict_mem measurableSet_Icc] with s hs_b hs_ab
  obtain ⟨hm_w, hle_w⟩ := hs_b i
  have hcs := norm_integral_mul_le_l2 hm_w hψ_mem
  have hα_le : ‖(α s : ℂ)‖ ≤ Mα := by
    rw [Complex.norm_real]
    exact (hMα0 s hs_ab).trans (le_max_right 0 Mα0)
  have hW0 : 0 ≤ W s := ENNReal.toReal_nonneg.trans hle_w
  calc ‖(α s : ℂ) * ∫ y in B0579.cell c, w (s, y) i * (ψ y : ℂ)‖
      = ‖(α s : ℂ)‖ * ‖∫ y in B0579.cell c, w (s, y) i * (ψ y : ℂ)‖ := norm_mul _ _
    _ ≤ Mα * ((eLpNorm (fun y => w (s, y) i) 2 (volume.restrict (B0579.cell c))).toReal * Mψ) :=
        mul_le_mul hα_le hcs (norm_nonneg _) (le_max_left 0 Mα0)
    _ ≤ Mα * (W s * Mψ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle_w ENNReal.toReal_nonneg)
          (le_max_left 0 Mα0)
    _ = Mα * Mψ * W s := by ring

/-- `H¹(cell)` stability: if `sliceWeakTerm` integrates to `0` on `Icc a b` along a sequence `Φk`
of `IsH1DivFreeTest` fields converging to `φ` in `H¹(cell)`, then it integrates to `0` for `φ`. -/
private lemma sliceWeakEq_of_h1_tendsto {p : Params} {T a b : ℝ}
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train)
    (hT : 0 < T) (haT : T < a) (hab : a < b)
    {g gq gη z₂ zq₂ zη₂ : CProf}
    (hg_src : IsCylSourceH1 p.c g gq gη)
    (hg_int : (∫⁻ s in Ioi T, sliceH1Norm p.c g gq gη s) < ⊤)
    (hz : StronglyMeasurable z₂) (hzq : StronglyMeasurable zq₂) (hzη : StronglyMeasurable zη₂)
    (hzT : IsCylH1Slice p.c (fun y => z₂ (T, y)) (fun y => zq₂ (T, y)) (fun y => zη₂ (T, y)))
    (hcont : ∀ s : ℝ, T ≤ s →
      Tendsto (fun s' => cylSliceH1 p.c
        (fun y => z₂ (s', y) - z₂ (s, y))
        (fun y => zq₂ (s', y) - zq₂ (s, y))
        (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici T] s) (𝓝 0))
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    {φ : B0579.Plane → Fin 2 → ℝ} (hφ : IIIa.IsH1DivFreeTest p.c φ)
    {Φk : ℕ → B0579.Plane → Fin 2 → ℝ} (hΦk : ∀ k, IIIa.IsH1DivFreeTest p.c (Φk k))
    (heq_k : ∀ k, ∫ s in Icc a b, sliceWeakTerm p g z₂ zq₂ zη₂ θ (Φk k) s = 0)
    (hlim : ∀ i : Fin 2,
      Tendsto (fun k => (eLpNorm (fun y => Φk k y i - φ y i) 2
        (volume.restrict (B0579.cell p.c))).toReal) atTop (𝓝 0) ∧
      ∀ j : Fin 2,
        Tendsto (fun k => (eLpNorm (fun y =>
          B0579.pd j (fun w => Φk k w i) y - B0579.pd j (fun w => φ w i) y) 2
          (volume.restrict (B0579.cell p.c))).toReal) atTop (𝓝 0)) :
    IntegrableOn (sliceWeakTerm p g z₂ zq₂ zη₂ θ φ) (Icc a b) ∧
      ∫ s in Icc a b, sliceWeakTerm p g z₂ zq₂ zη₂ θ φ s = 0 := by
  have hc : 0 < p.c := p.c_pos
  have hT_fin : sliceH1Norm p.c z₂ zq₂ zη₂ T < ⊤ := by
    unfold sliceH1Norm
    exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2
      ⟨hzT.memL2_u.eLpNorm_lt_top, hzT.memL2_uq.eLpNorm_lt_top⟩, hzT.memL2_uη.eLpNorm_lt_top⟩
  have hfin := sliceH1Norm_lt_top_of_ge hz hzq hzη hT_fin hcont
  have hmem := fun t ht => memLp_slice_of_sliceH1Norm_lt_top hz hzq hzη (hfin t ht)
  obtain ⟨hcz, hczq, hczη⟩ := continuousOn_profPaths hz hzq hzη hT_fin hcont
  have hsub_T : Icc a b ⊆ Ici T := fun s hs => haT.le.trans hs.1
  obtain ⟨C_bv, hCbv0, hbv⟩ := memLp_slice_flatBv_on p.train htr hz hzq hzη
    (hT.trans haT) hab.le (fun s hs => hmem s (hsub_T hs))
    (hcz.mono hsub_T) (hczq.mono hsub_T) (hczη.mono hsub_T)
  obtain ⟨hloc_g, hboch_g, hae_g⟩ := source_slice_regularity hc hT hg_src hg_int
  have hint_gH1 : IntegrableOn (fun s => (sliceH1Norm p.c g gq gη s).toReal) (Icc a b) :=
    (hboch_g b (haT.trans hab).le).1.mono_set (Icc_subset_Icc haT.le le_rfl)
  have hdθ_cont : Continuous (deriv θ) := hθ.continuous_deriv (by simp)
  -- Helper proving `IntegrableOn` of `sliceWeakTerm ... ψ` for any `IsH1DivFreeTest` `ψ`
  have int_term : ∀ ψ : B0579.Plane → Fin 2 → ℝ, IIIa.IsH1DivFreeTest p.c ψ →
      IntegrableOn (sliceWeakTerm p g z₂ zq₂ zη₂ θ ψ) (Icc a b) := by
    intro ψ hψ
    have hψC : ∀ i, MemLp (fun y => (ψ y i : ℂ)) 2 (volume.restrict (B0579.cell p.c)) := fun i =>
      Complex.ofRealCLM.comp_memLp' (hψ.l2 i)
    have hpdC : ∀ i j, MemLp (fun y => (B0579.pd j (fun w => ψ w i) y : ℂ)) 2
        (volume.restrict (B0579.cell p.c)) := fun i j =>
      Complex.ofRealCLM.comp_memLp' (hψ.l2grad i j)
    have hpd_meas : ∀ i j, Measurable (fun y => B0579.pd j (fun w => ψ w i) y) := fun i j =>
      ((((contDiff_infty_iff_fderiv.1 (hψ.smooth i)).2).clm_apply contDiff_const).continuous).measurable
    have mk_w : ∀ (w : CProf), StronglyMeasurable w →
        (∀ t ≥ T, MemLp (fun y => w (t, y)) 2 (volume.restrict (B0579.cell p.c))) →
        ContinuousOn (profPath p.c w) (Ici T) →
        ∀ (α : ℝ → ℝ), Continuous α →
        ∀ (f : Fin 2 → B0579.Plane → ℝ), (∀ i, Measurable (f i)) →
        (∀ i, MemLp (fun y => (f i y : ℂ)) 2 (volume.restrict (B0579.cell p.c))) →
        IntegrableOn (fun s => (α s : ℂ) *
          ∫ y in B0579.cell p.c, ∑ i : Fin 2, w (s, y) i * (f i y : ℂ)) (Icc a b) := by
      intro w hw hmw hcw α hα f hf_m hf_l2
      have hW : IntegrableOn (fun s => ‖profPath p.c w s‖) (Icc a b) :=
        (continuous_norm.comp_continuousOn (hcw.mono hsub_T)).integrableOn_Icc
      have hWb : ∀ᵐ s ∂(volume.restrict (Icc a b)), ∀ i : Fin 2,
          MemLp (fun y => w (s, y) i) 2 (volume.restrict (B0579.cell p.c)) ∧
          (eLpNorm (fun y => w (s, y) i) 2 (volume.restrict (B0579.cell p.c))).toReal ≤
            ‖profPath p.c w s‖ := by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs i
        have hm := hmw s (hsub_T hs)
        refine ⟨⟨((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
            (sliceMeas hw s)).aestronglyMeasurable,
          (eLpNorm_comp_le_merid p.c w s i).trans_lt hm.eLpNorm_lt_top⟩, ?_⟩
        rw [norm_profPath_eq hm]
        exact ENNReal.toReal_mono hm.eLpNorm_ne_top (eLpNorm_comp_le_merid p.c w s i)
      have hi : ∀ i : Fin 2, IntegrableOn
          (fun s => (α s : ℂ) * ∫ y in B0579.cell p.c, w (s, y) i * (f i y : ℂ)) (Icc a b) :=
        fun i => integrableOn_weighted_cell_pairing hT haT hw hα (hf_m i) (hf_l2 i) hW hWb i
      refine IntegrableOn.congr_fun (integrable_finsetSum Finset.univ fun i _ => hi i)
        (fun s hs => ?_) measurableSet_Icc
      rw [← Finset.mul_sum, integral_finsetSum]
      intro i _
      have hm := hmw s (hsub_T hs)
      have hmi : MemLp (fun y => w (s, y) i) 2 (volume.restrict (B0579.cell p.c)) :=
        ⟨((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
            (sliceMeas hw s)).aestronglyMeasurable,
          (eLpNorm_comp_le_merid p.c w s i).trans_lt hm.eLpNorm_lt_top⟩
      exact hmi.integrable_mul (hf_l2 i)
    have hI_time := mk_w z₂ hz (fun t ht => (hmem t ht).1) hcz (-deriv θ) hdθ_cont.neg
      (fun i y => ψ y i) (fun i => (hψ.smooth i).continuous.measurable) hψC
    have hI_vq := mk_w zq₂ hzq (fun t ht => (hmem t ht).2.1) hczq (fun s => p.ν * θ s)
      (continuous_const.mul hθ.continuous)
      (fun i y => B0579.pd 0 (fun w => ψ w i) y) (fun i => hpd_meas i 0) (fun i => hpdC i 0)
    have hI_vη := mk_w zη₂ hzη (fun t ht => (hmem t ht).2.2) hczη (fun s => p.ν * θ s)
      (continuous_const.mul hθ.continuous)
      (fun i y => B0579.pd 1 (fun w => ψ w i) y) (fun i => hpd_meas i 1) (fun i => hpdC i 1)
    have hI_bv : IntegrableOn (fun s => (θ s : ℂ) *
        ∫ y in B0579.cell p.c, ∑ i : Fin 2,
          flatBv p.train z₂ zq₂ zη₂ (s, y) i * (ψ y i : ℂ)) (Icc a b) := by
      have hi : ∀ i : Fin 2, IntegrableOn (fun s => (θ s : ℂ) *
          ∫ y in B0579.cell p.c,
            tailInd T (flatBv p.train z₂ zq₂ zη₂) (s, y) i * (ψ y i : ℂ)) (Icc a b) := by
        intro i
        refine integrableOn_weighted_cell_pairing hT haT
          (stronglyMeasurable_tailInd_flatBv hT p.train hz hzq hzη) hθ.continuous
          (hψ.smooth i).continuous.measurable (hψC i)
          (integrableOn_const (C := C_bv) measure_Icc_lt_top.ne) ?_ i
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs k
        have hsT : T < s := lt_of_lt_of_le haT hs.1
        have heq_fn : (fun y => tailInd T (flatBv p.train z₂ zq₂ zη₂) (s, y) k) =
            fun y => flatBv p.train z₂ zq₂ zη₂ (s, y) k := by
          funext y; simp [tailInd, hsT]
        rw [heq_fn]
        exact ⟨(hbv s hs k).1, (hbv s hs k).2.1⟩
      refine IntegrableOn.congr_fun (integrable_finsetSum Finset.univ fun i _ => hi i)
        (fun s hs => ?_) measurableSet_Icc
      have hsT : T < s := lt_of_lt_of_le haT hs.1
      rw [← Finset.mul_sum]
      congr 1
      have h_ind : ∀ i : Fin 2,
          (∫ y in B0579.cell p.c,
            tailInd T (flatBv p.train z₂ zq₂ zη₂) (s, y) i * (ψ y i : ℂ)) =
          ∫ y in B0579.cell p.c, flatBv p.train z₂ zq₂ zη₂ (s, y) i * (ψ y i : ℂ) := by
        intro i; congr 1; funext y; simp [tailInd, hsT]
      simp_rw [h_ind]
      exact (integral_finsetSum Finset.univ fun i _ => (hbv s hs i).1.integrable_mul (hψC i)).symm
    have hI_g : IntegrableOn (fun s => (θ s : ℂ) *
        ∫ y in B0579.cell p.c, ∑ i : Fin 2, g (s, y) i * (ψ y i : ℂ)) (Icc a b) := by
      have hi : ∀ i : Fin 2, IntegrableOn (fun s => (θ s : ℂ) *
          ∫ y in B0579.cell p.c, g (s, y) i * (ψ y i : ℂ)) (Icc a b) := by
        intro i
        refine integrableOn_weighted_cell_pairing hT haT hg_src.sm_g hθ.continuous
          (hψ.smooth i).continuous.measurable (hψC i) hint_gH1 ?_ i
        filter_upwards [ae_restrict_of_ae hae_g, ae_restrict_mem measurableSet_Icc] with s hsg hs
        intro k
        have hfin_s := (hsg (lt_of_lt_of_le haT hs.1)).1
        obtain ⟨hmg, _, _⟩ :=
          memLp_slice_of_sliceH1Norm_lt_top hg_src.sm_g hg_src.sm_gq hg_src.sm_gη hfin_s
        have hle_H1 : eLpNorm (fun y => g (s, y) k) 2 (volume.restrict (B0579.cell p.c)) ≤
            sliceH1Norm p.c g gq gη s :=
          (eLpNorm_comp_le_merid p.c g s k).trans (le_self_add.trans le_self_add)
        exact ⟨⟨((EuclideanSpace.proj k : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
            (sliceMeas hg_src.sm_g s)).aestronglyMeasurable, hle_H1.trans_lt hfin_s⟩,
          ENNReal.toReal_mono hfin_s.ne hle_H1⟩
      refine (integrable_finsetSum Finset.univ fun i _ => hi i).congr ?_
      filter_upwards [ae_restrict_of_ae hae_g, ae_restrict_mem measurableSet_Icc] with s hsg hs
      have hfin_s := (hsg (lt_of_lt_of_le haT hs.1)).1
      obtain ⟨hmg, _, _⟩ :=
        memLp_slice_of_sliceH1Norm_lt_top hg_src.sm_g hg_src.sm_gq hg_src.sm_gη hfin_s
      rw [← Finset.mul_sum]
      congr 1
      exact (integral_finsetSum Finset.univ fun i _ =>
        (MemLp.integrable_mul
          ⟨((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
            (sliceMeas hg_src.sm_g s)).aestronglyMeasurable,
            (eLpNorm_comp_le_merid p.c g s i).trans_lt hmg.eLpNorm_lt_top⟩ (hψC i))).symm
    refine (hI_time.add ((hI_vq.add hI_vη).add (hI_bv.sub hI_g))).congr_fun
      (fun s hs => ?_) measurableSet_Icc
    have hm_s := hmem s (hsub_T hs)
    have hint_zq : ∀ i : Fin 2, IntegrableOn
        (fun y => zq₂ (s, y) i * (B0579.pd 0 (fun w => ψ w i) y : ℂ)) (B0579.cell p.c) := fun i =>
      (MemLp.integrable_mul
        ⟨((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
          (sliceMeas hzq s)).aestronglyMeasurable,
          (eLpNorm_comp_le_merid p.c zq₂ s i).trans_lt hm_s.2.1.eLpNorm_lt_top⟩ (hpdC i 0))
    have hint_zη : ∀ i : Fin 2, IntegrableOn
        (fun y => zη₂ (s, y) i * (B0579.pd 1 (fun w => ψ w i) y : ℂ)) (B0579.cell p.c) := fun i =>
      (MemLp.integrable_mul
        ⟨((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
          (sliceMeas hzη s)).aestronglyMeasurable,
          (eLpNorm_comp_le_merid p.c zη₂ s i).trans_lt hm_s.2.2.eLpNorm_lt_top⟩ (hpdC i 1))
    have hsum_v : (∫ y in B0579.cell p.c, ∑ i : Fin 2,
          (zq₂ (s, y) i * (B0579.pd 0 (fun w => ψ w i) y : ℂ) +
            zη₂ (s, y) i * (B0579.pd 1 (fun w => ψ w i) y : ℂ))) =
        (∫ y in B0579.cell p.c, ∑ i : Fin 2,
          zq₂ (s, y) i * (B0579.pd 0 (fun w => ψ w i) y : ℂ)) +
        (∫ y in B0579.cell p.c, ∑ i : Fin 2,
          zη₂ (s, y) i * (B0579.pd 1 (fun w => ψ w i) y : ℂ)) := by
      simp_rw [Finset.sum_add_distrib]
      exact integral_add (integrable_finsetSum Finset.univ fun i _ => hint_zq i)
        (integrable_finsetSum Finset.univ fun i _ => hint_zη i)
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, sliceWeakTerm]
    rw [hsum_v]
    push_cast
    ring
  have hint_φ := int_term φ hφ
  refine ⟨hint_φ, ?_⟩
  obtain ⟨Mθ0, hMθ0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc a b) hθ.continuous.continuousOn
  obtain ⟨Mdθ0, hMdθ0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc a b) hdθ_cont.continuousOn
  let Mθ : ℝ := max 0 Mθ0
  let Mdθ : ℝ := max 0 Mdθ0
  let C_θ : ℝ := Mdθ + Mθ * (p.ν + 2)
  have hCθ0 : 0 ≤ C_θ := by
    have hν0 : 0 ≤ p.ν := p.ν_pos.le
    dsimp [C_θ, Mdθ, Mθ]
    positivity
  let W_dom : ℝ → ℝ := fun s =>
    ‖profPath p.c z₂ s‖ + ‖profPath p.c zq₂ s‖ + ‖profPath p.c zη₂ s‖ + C_bv +
      (sliceH1Norm p.c g gq gη s).toReal
  have hW_int : IntegrableOn W_dom (Icc a b) :=
    (((((continuous_norm.comp_continuousOn (hcz.mono hsub_T)).integrableOn_Icc).add
      ((continuous_norm.comp_continuousOn (hczq.mono hsub_T)).integrableOn_Icc)).add
      ((continuous_norm.comp_continuousOn (hczη.mono hsub_T)).integrableOn_Icc)).add
      (integrableOn_const (C := C_bv) measure_Icc_lt_top.ne)).add hint_gH1
  let μc : Measure B0579.Plane := volume.restrict (B0579.cell p.c)
  let err : ℕ → ℝ := fun k => ∑ i : Fin 2,
    ((eLpNorm (fun y => Φk k y i - φ y i) 2 μc).toReal +
      ∑ j : Fin 2, (eLpNorm (fun y =>
        B0579.pd j (fun w => Φk k w i) y - B0579.pd j (fun w => φ w i) y) 2 μc).toReal)
  have herr_nn : ∀ k, 0 ≤ err k := fun k =>
    Finset.sum_nonneg fun _ _ => add_nonneg ENNReal.toReal_nonneg
      (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
  have herr_lim : Tendsto err atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∑ _i : Fin 2, ((0 : ℝ) + ∑ _j : Fin 2, (0 : ℝ)) := by simp
    rw [h0]
    exact tendsto_finsetSum Finset.univ fun i _ =>
      (hlim i).1.add (tendsto_finsetSum Finset.univ fun j _ => (hlim i).2 j)
  have h_ofReal_eLp : ∀ f : B0579.Plane → ℝ,
      eLpNorm (fun y => (f y : ℂ)) 2 μc = eLpNorm f 2 μc := fun f =>
    eLpNorm_congr_norm_ae (Eventually.of_forall fun y => Complex.norm_real (f y))
  have h_bound_k : ∀ k : ℕ, ‖∫ s in Icc a b, sliceWeakTerm p g z₂ zq₂ zη₂ θ φ s‖ ≤
      (C_θ * ∫ s in Icc a b, W_dom s) * err k := by
    intro k
    have hint_k := int_term (Φk k) (hΦk k)
    have h_eq_sub : ∫ s in Icc a b, sliceWeakTerm p g z₂ zq₂ zη₂ θ φ s =
        -(∫ s in Icc a b, (sliceWeakTerm p g z₂ zq₂ zη₂ θ (Φk k) s -
          sliceWeakTerm p g z₂ zq₂ zη₂ θ φ s)) := by
      rw [integral_sub hint_k hint_φ, heq_k k, zero_sub, neg_neg]
    rw [h_eq_sub, norm_neg]
    have h_dom_ae : ∀ᵐ s ∂(volume.restrict (Icc a b)),
        ‖sliceWeakTerm p g z₂ zq₂ zη₂ θ (Φk k) s - sliceWeakTerm p g z₂ zq₂ zη₂ θ φ s‖ ≤
          C_θ * W_dom s * err k := by
      filter_upwards [ae_restrict_of_ae hae_g, ae_restrict_mem measurableSet_Icc] with s hsg hs
      have hfin_g := (hsg (lt_of_lt_of_le haT hs.1)).1
      obtain ⟨hmg, _, _⟩ :=
        memLp_slice_of_sliceH1Norm_lt_top hg_src.sm_g hg_src.sm_gq hg_src.sm_gη hfin_g
      have hm_s := hmem s (hsub_T hs)
      have hd0_mem : ∀ i, MemLp (fun y => ((Φk k y i - φ y i : ℝ) : ℂ)) 2 μc := fun i =>
        Complex.ofRealCLM.comp_memLp' (((hΦk k).l2 i).sub (hφ.l2 i))
      have hd1_mem : ∀ i j, MemLp (fun y =>
          ((B0579.pd j (fun w => Φk k w i) y - B0579.pd j (fun w => φ w i) y : ℝ) : ℂ)) 2 μc :=
        fun i j => Complex.ofRealCLM.comp_memLp' (((hΦk k).l2grad i j).sub (hφ.l2grad i j))
      have he0_le : ∀ i : Fin 2, (eLpNorm (fun y => Φk k y i - φ y i) 2 μc).toReal ≤ err k := by
        intro i
        have h_term : (eLpNorm (fun y => Φk k y i - φ y i) 2 μc).toReal ≤
            (eLpNorm (fun y => Φk k y i - φ y i) 2 μc).toReal +
              ∑ j : Fin 2, (eLpNorm (fun y =>
                B0579.pd j (fun w => Φk k w i) y - B0579.pd j (fun w => φ w i) y) 2 μc).toReal :=
          le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
        exact h_term.trans (Finset.single_le_sum
          (f := fun m : Fin 2 => (eLpNorm (fun y => Φk k y m - φ y m) 2 μc).toReal +
            ∑ j : Fin 2, (eLpNorm (fun y =>
              B0579.pd j (fun w => Φk k w m) y - B0579.pd j (fun w => φ w m) y) 2 μc).toReal)
          (fun _ _ => add_nonneg ENNReal.toReal_nonneg
            (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)) (Finset.mem_univ i))
      have he0_sum_le : ∑ i : Fin 2, (eLpNorm (fun y => Φk k y i - φ y i) 2 μc).toReal ≤ err k := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
      have he1_sum_le : ∀ j : Fin 2, ∑ i : Fin 2,
          (eLpNorm (fun y =>
            B0579.pd j (fun w => Φk k w i) y - B0579.pd j (fun w => φ w i) y) 2 μc).toReal ≤ err k := by
        intro j
        refine Finset.sum_le_sum fun i _ => ?_
        exact (Finset.single_le_sum
          (f := fun l : Fin 2 => (eLpNorm (fun y =>
            B0579.pd l (fun w => Φk k w i) y - B0579.pd l (fun w => φ w i) y) 2 μc).toReal)
          (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ j)).trans
          (le_add_of_nonneg_left ENNReal.toReal_nonneg)
      -- Generic pairing-difference bound `‖∫ ∑ w * Φk - ∫ ∑ w * φ‖ ≤ B * ∑ e0_i`
      have pair_diff : ∀ (w : B0579.Plane → CMerid) (B : ℝ), 0 ≤ B →
          (∀ i : Fin 2, MemLp (fun y => w y i) 2 μc ∧ (eLpNorm (fun y => w y i) 2 μc).toReal ≤ B) →
          ∀ (f1 f2 : Fin 2 → B0579.Plane → ℝ),
          (∀ i, MemLp (fun y => (f1 i y : ℂ)) 2 μc) →
          (∀ i, MemLp (fun y => (f2 i y : ℂ)) 2 μc) →
          ‖(∫ y in B0579.cell p.c, ∑ i : Fin 2, w y i * (f1 i y : ℂ)) -
            (∫ y in B0579.cell p.c, ∑ i : Fin 2, w y i * (f2 i y : ℂ))‖ ≤
            B * ∑ i : Fin 2, (eLpNorm (fun y => f1 i y - f2 i y) 2 μc).toReal := by
        intro w B hB0 hwB f1 f2 hf1 hf2
        have hi1 : ∀ i, Integrable (fun y => w y i * (f1 i y : ℂ)) μc :=
          fun i => (hwB i).1.integrable_mul (hf1 i)
        have hi2 : ∀ i, Integrable (fun y => w y i * (f2 i y : ℂ)) μc :=
          fun i => (hwB i).1.integrable_mul (hf2 i)
        rw [integral_finsetSum Finset.univ fun i _ => hi1 i,
          integral_finsetSum Finset.univ fun i _ => hi2 i, ← Finset.sum_sub_distrib]
        refine (norm_sum_le Finset.univ _).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← integral_sub (hi1 i) (hi2 i)]
        have hsub_eq : (fun y => w y i * (f1 i y : ℂ) - w y i * (f2 i y : ℂ)) =
            fun y => w y i * ((f1 i y - f2 i y : ℝ) : ℂ) := by
          funext y; push_cast; ring
        rw [hsub_eq]
        have hf_diff : MemLp (fun y => ((f1 i y - f2 i y : ℝ) : ℂ)) 2 μc := by
          have hfn : (fun y => ((f1 i y - f2 i y : ℝ) : ℂ)) =
              (fun y => (f1 i y : ℂ)) - (fun y => (f2 i y : ℂ)) := by
            funext y; simp
          rw [hfn]
          exact (hf1 i).sub (hf2 i)
        have hcs := norm_integral_mul_le_l2 (hwB i).1 hf_diff
        rw [h_ofReal_eLp] at hcs
        exact hcs.trans (mul_le_mul_of_nonneg_right (hwB i).2 ENNReal.toReal_nonneg)
      have hz_B : ∀ i, MemLp (fun y => z₂ (s, y) i) 2 μc ∧
          (eLpNorm (fun y => z₂ (s, y) i) 2 μc).toReal ≤ ‖profPath p.c z₂ s‖ := by
        intro i
        refine ⟨⟨((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
            (sliceMeas hz s)).aestronglyMeasurable,
          (eLpNorm_comp_le_merid p.c z₂ s i).trans_lt hm_s.1.eLpNorm_lt_top⟩, ?_⟩
        rw [norm_profPath_eq hm_s.1]
        exact ENNReal.toReal_mono hm_s.1.eLpNorm_ne_top (eLpNorm_comp_le_merid p.c z₂ s i)
      have hzq_B : ∀ i, MemLp (fun y => zq₂ (s, y) i) 2 μc ∧
          (eLpNorm (fun y => zq₂ (s, y) i) 2 μc).toReal ≤ ‖profPath p.c zq₂ s‖ := by
        intro i
        refine ⟨⟨((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
            (sliceMeas hzq s)).aestronglyMeasurable,
          (eLpNorm_comp_le_merid p.c zq₂ s i).trans_lt hm_s.2.1.eLpNorm_lt_top⟩, ?_⟩
        rw [norm_profPath_eq hm_s.2.1]
        exact ENNReal.toReal_mono hm_s.2.1.eLpNorm_ne_top (eLpNorm_comp_le_merid p.c zq₂ s i)
      have hzη_B : ∀ i, MemLp (fun y => zη₂ (s, y) i) 2 μc ∧
          (eLpNorm (fun y => zη₂ (s, y) i) 2 μc).toReal ≤ ‖profPath p.c zη₂ s‖ := by
        intro i
        refine ⟨⟨((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
            (sliceMeas hzη s)).aestronglyMeasurable,
          (eLpNorm_comp_le_merid p.c zη₂ s i).trans_lt hm_s.2.2.eLpNorm_lt_top⟩, ?_⟩
        rw [norm_profPath_eq hm_s.2.2]
        exact ENNReal.toReal_mono hm_s.2.2.eLpNorm_ne_top (eLpNorm_comp_le_merid p.c zη₂ s i)
      have hbv_B : ∀ i, MemLp (fun y => flatBv p.train z₂ zq₂ zη₂ (s, y) i) 2 μc ∧
          (eLpNorm (fun y => flatBv p.train z₂ zq₂ zη₂ (s, y) i) 2 μc).toReal ≤ C_bv :=
        fun i => ⟨(hbv s hs i).1, (hbv s hs i).2.1⟩
      have hg_B : ∀ i, MemLp (fun y => g (s, y) i) 2 μc ∧
          (eLpNorm (fun y => g (s, y) i) 2 μc).toReal ≤ (sliceH1Norm p.c g gq gη s).toReal := by
        intro i
        have hle_H1 : eLpNorm (fun y => g (s, y) i) 2 μc ≤ sliceH1Norm p.c g gq gη s :=
          (eLpNorm_comp_le_merid p.c g s i).trans (le_self_add.trans le_self_add)
        exact ⟨⟨((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
            (sliceMeas hg_src.sm_g s)).aestronglyMeasurable, hle_H1.trans_lt hfin_g⟩,
          ENNReal.toReal_mono hfin_g.ne hle_H1⟩
      have hb_z := (pair_diff (fun y => z₂ (s, y)) ‖profPath p.c z₂ s‖ (norm_nonneg _) hz_B
        (fun i y => Φk k y i) (fun i y => φ y i)
        (fun i => Complex.ofRealCLM.comp_memLp' ((hΦk k).l2 i))
        (fun i => Complex.ofRealCLM.comp_memLp' (hφ.l2 i))).trans
        (mul_le_mul_of_nonneg_left he0_sum_le (norm_nonneg _))
      have hb_zq := (pair_diff (fun y => zq₂ (s, y)) ‖profPath p.c zq₂ s‖ (norm_nonneg _) hzq_B
        (fun i y => B0579.pd 0 (fun w => Φk k w i) y) (fun i y => B0579.pd 0 (fun w => φ w i) y)
        (fun i => Complex.ofRealCLM.comp_memLp' ((hΦk k).l2grad i 0))
        (fun i => Complex.ofRealCLM.comp_memLp' (hφ.l2grad i 0))).trans
        (mul_le_mul_of_nonneg_left (he1_sum_le 0) (norm_nonneg _))
      have hb_zη := (pair_diff (fun y => zη₂ (s, y)) ‖profPath p.c zη₂ s‖ (norm_nonneg _) hzη_B
        (fun i y => B0579.pd 1 (fun w => Φk k w i) y) (fun i y => B0579.pd 1 (fun w => φ w i) y)
        (fun i => Complex.ofRealCLM.comp_memLp' ((hΦk k).l2grad i 1))
        (fun i => Complex.ofRealCLM.comp_memLp' (hφ.l2grad i 1))).trans
        (mul_le_mul_of_nonneg_left (he1_sum_le 1) (norm_nonneg _))
      have hb_bv := (pair_diff (fun y => flatBv p.train z₂ zq₂ zη₂ (s, y)) C_bv hCbv0 hbv_B
        (fun i y => Φk k y i) (fun i y => φ y i)
        (fun i => Complex.ofRealCLM.comp_memLp' ((hΦk k).l2 i))
        (fun i => Complex.ofRealCLM.comp_memLp' (hφ.l2 i))).trans
        (mul_le_mul_of_nonneg_left he0_sum_le hCbv0)
      have hb_g := (pair_diff (fun y => g (s, y)) (sliceH1Norm p.c g gq gη s).toReal
        ENNReal.toReal_nonneg hg_B
        (fun i y => Φk k y i) (fun i y => φ y i)
        (fun i => Complex.ofRealCLM.comp_memLp' ((hΦk k).l2 i))
        (fun i => Complex.ofRealCLM.comp_memLp' (hφ.l2 i))).trans
        (mul_le_mul_of_nonneg_left he0_sum_le ENNReal.toReal_nonneg)
      have hv_split : ∀ ψ : B0579.Plane → Fin 2 → ℝ, IIIa.IsH1DivFreeTest p.c ψ →
          (∫ y in B0579.cell p.c, ∑ i : Fin 2,
            (zq₂ (s, y) i * (B0579.pd 0 (fun w => ψ w i) y : ℂ) +
              zη₂ (s, y) i * (B0579.pd 1 (fun w => ψ w i) y : ℂ))) =
          (∫ y in B0579.cell p.c, ∑ i : Fin 2,
            zq₂ (s, y) i * (B0579.pd 0 (fun w => ψ w i) y : ℂ)) +
          (∫ y in B0579.cell p.c, ∑ i : Fin 2,
            zη₂ (s, y) i * (B0579.pd 1 (fun w => ψ w i) y : ℂ)) := by
        intro ψ hψ_t
        simp_rw [Finset.sum_add_distrib]
        exact integral_add
          (integrable_finsetSum Finset.univ fun i _ =>
            (hzq_B i).1.integrable_mul (Complex.ofRealCLM.comp_memLp' (hψ_t.l2grad i 0)))
          (integrable_finsetSum Finset.univ fun i _ =>
            (hzη_B i).1.integrable_mul (Complex.ofRealCLM.comp_memLp' (hψ_t.l2grad i 1)))
      have hθ_le : ‖(θ s : ℂ)‖ ≤ Mθ := by
        rw [Complex.norm_real]; exact (hMθ0 s hs).trans (le_max_right 0 Mθ0)
      have hdθ_le : ‖((deriv θ s : ℝ) : ℂ)‖ ≤ Mdθ := by
        rw [Complex.norm_real]; exact (hMdθ0 s hs).trans (le_max_right 0 Mdθ0)
      have hν_le : ‖(p.ν : ℂ)‖ = p.ν := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos p.ν_pos]
      set Iz := (∫ y in B0579.cell p.c, ∑ i, z₂ (s, y) i * (Φk k y i : ℂ)) -
        (∫ y in B0579.cell p.c, ∑ i, z₂ (s, y) i * (φ y i : ℂ))
      set Izq := (∫ y in B0579.cell p.c, ∑ i, zq₂ (s, y) i *
          (B0579.pd 0 (fun w => Φk k w i) y : ℂ)) -
        (∫ y in B0579.cell p.c, ∑ i, zq₂ (s, y) i * (B0579.pd 0 (fun w => φ w i) y : ℂ))
      set Izη := (∫ y in B0579.cell p.c, ∑ i, zη₂ (s, y) i *
          (B0579.pd 1 (fun w => Φk k w i) y : ℂ)) -
        (∫ y in B0579.cell p.c, ∑ i, zη₂ (s, y) i * (B0579.pd 1 (fun w => φ w i) y : ℂ))
      set Ibv := (∫ y in B0579.cell p.c, ∑ i,
          flatBv p.train z₂ zq₂ zη₂ (s, y) i * (Φk k y i : ℂ)) -
        (∫ y in B0579.cell p.c, ∑ i, flatBv p.train z₂ zq₂ zη₂ (s, y) i * (φ y i : ℂ))
      set Ig := (∫ y in B0579.cell p.c, ∑ i, g (s, y) i * (Φk k y i : ℂ)) -
        (∫ y in B0579.cell p.c, ∑ i, g (s, y) i * (φ y i : ℂ))
      have hdiff_alg : sliceWeakTerm p g z₂ zq₂ zη₂ θ (Φk k) s -
          sliceWeakTerm p g z₂ zq₂ zη₂ θ φ s =
          -((deriv θ s : ℝ) : ℂ) * Iz +
            (θ s : ℂ) * ((p.ν : ℂ) * (Izq + Izη) + Ibv - Ig) := by
        dsimp only [sliceWeakTerm]
        rw [hv_split (Φk k) (hΦk k), hv_split φ hφ]
        dsimp only [Iz, Izq, Izη, Ibv, Ig]
        ring
      rw [hdiff_alg]
      have h1 : ‖-((deriv θ s : ℝ) : ℂ) * Iz‖ ≤ Mdθ * (‖profPath p.c z₂ s‖ * err k) := by
        rw [norm_mul, norm_neg]
        exact mul_le_mul hdθ_le hb_z (norm_nonneg _) (le_max_left 0 Mdθ0)
      have h2 : ‖(θ s : ℂ) * ((p.ν : ℂ) * (Izq + Izη) + Ibv - Ig)‖ ≤
          Mθ * (p.ν * (‖profPath p.c zq₂ s‖ * err k + ‖profPath p.c zη₂ s‖ * err k) +
            C_bv * err k + (sliceH1Norm p.c g gq gη s).toReal * err k) := by
        rw [norm_mul]
        refine mul_le_mul hθ_le ?_ (norm_nonneg _) (le_max_left 0 Mθ0)
        have ha1 := norm_add_le ((p.ν : ℂ) * (Izq + Izη) + Ibv) (-Ig)
        rw [ ← sub_eq_add_neg, norm_neg] at ha1
        have ha2 := norm_add_le ((p.ν : ℂ) * (Izq + Izη)) Ibv
        have ha3 : ‖(p.ν : ℂ) * (Izq + Izη)‖ ≤
            p.ν * (‖profPath p.c zq₂ s‖ * err k + ‖profPath p.c zη₂ s‖ * err k) := by
          rw [norm_mul, hν_le]
          exact mul_le_mul_of_nonneg_left
            ((norm_add_le Izq Izη).trans (add_le_add hb_zq hb_zη)) p.ν_pos.le
        linarith
      have hW_nn : 0 ≤ ‖profPath p.c z₂ s‖ ∧ 0 ≤ ‖profPath p.c zq₂ s‖ ∧
          0 ≤ ‖profPath p.c zη₂ s‖ ∧ 0 ≤ (sliceH1Norm p.c g gq gη s).toReal :=
        ⟨norm_nonneg _, norm_nonneg _, norm_nonneg _, ENNReal.toReal_nonneg⟩
      have hMθ_nn : 0 ≤ Mθ := le_max_left 0 Mθ0
      have hMdθ_nn : 0 ≤ Mdθ := le_max_left 0 Mdθ0
      have hν_pos : 0 < p.ν := p.ν_pos
      have herr_k := herr_nn k
      have h_tot := (norm_add_le (-((deriv θ s : ℝ) : ℂ) * Iz)
        ((θ s : ℂ) * ((p.ν : ℂ) * (Izq + Izη) + Ibv - Ig))).trans (add_le_add h1 h2)
      have h_fac : Mdθ * (‖profPath p.c z₂ s‖ * err k) +
          Mθ * (p.ν * (‖profPath p.c zq₂ s‖ * err k + ‖profPath p.c zη₂ s‖ * err k) +
            C_bv * err k + (sliceH1Norm p.c g gq gη s).toReal * err k) =
          (Mdθ * ‖profPath p.c z₂ s‖ +
            Mθ * (p.ν * (‖profPath p.c zq₂ s‖ + ‖profPath p.c zη₂ s‖) +
              C_bv + (sliceH1Norm p.c g gq gη s).toReal)) * err k := by ring
      have h_brack : Mdθ * ‖profPath p.c z₂ s‖ +
          Mθ * (p.ν * (‖profPath p.c zq₂ s‖ + ‖profPath p.c zη₂ s‖) +
            C_bv + (sliceH1Norm p.c g gq gη s).toReal) ≤ C_θ * W_dom s := by
        dsimp only [C_θ, W_dom]
        nlinarith [mul_nonneg hMθ_nn hν_pos.le, hCbv0]
      exact h_tot.trans ((le_of_eq h_fac).trans (mul_le_mul_of_nonneg_right h_brack herr_k))
    calc ‖∫ s in Icc a b, (sliceWeakTerm p g z₂ zq₂ zη₂ θ (Φk k) s -
            sliceWeakTerm p g z₂ zq₂ zη₂ θ φ s)‖
        ≤ ∫ s in Icc a b, ‖sliceWeakTerm p g z₂ zq₂ zη₂ θ (Φk k) s -
            sliceWeakTerm p g z₂ zq₂ zη₂ θ φ s‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ s in Icc a b, C_θ * W_dom s * err k :=
          integral_mono_ae (hint_k.sub hint_φ).norm
            ((hW_int.const_mul C_θ).mul_const (err k)) h_dom_ae
      _ = (C_θ * ∫ s in Icc a b, W_dom s) * err k := by
          rw [integral_mul_const, integral_const_mul]
  have h_zero_lim : Tendsto (fun k => (C_θ * ∫ s in Icc a b, W_dom s) * err k) atTop (𝓝 0) := by
    simpa using herr_lim.const_mul (C_θ * ∫ s in Icc a b, W_dom s)
  have h_norm_le : ‖∫ s in Icc a b, sliceWeakTerm p g z₂ zq₂ zη₂ θ φ s‖ ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds h_zero_lim (Eventually.of_forall h_bound_k)
  exact norm_le_zero_iff.1 h_norm_le

private lemma pd_comm_of_smooth {f : B0579.Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (j l : Fin 2) (y : B0579.Plane) :
    B0579.pd j (B0579.pd l f) y = B0579.pd l (B0579.pd j f) y := by
  unfold B0579.pd
  have hsymm := (hf.contDiffAt (x := y)).isSymmSndFDerivAt (by simp)
  have hf2 : ∀ v w : B0579.Plane,
      fderiv ℝ (fun z => fderiv ℝ f z v) y w = fderiv ℝ (fderiv ℝ f) y w v := by
    intro v w
    have hd_fd : DifferentiableAt ℝ (fderiv ℝ f) y :=
      ((contDiff_infty_iff_fderiv.1 hf).2.differentiable (by simp)).differentiableAt
    have hcomp := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp y hd_fd.hasFDerivAt
    exact congrArg (fun L => L w) hcomp.fderiv
  rw [hf2, hf2]
  exact hsymm.eq (B0579.dir j) (B0579.dir l)

private lemma cpd_comm_of_smooth {f : Coord → ℝ} (hf : ContDiff ℝ ∞ f)
    (j l : Fin 3) (x : Coord) :
    cpd j (cpd l f) x = cpd l (cpd j f) x := by
  unfold cpd
  have hsymm := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  have hf2 : ∀ v w : Coord,
      fderiv ℝ (fun z => fderiv ℝ f z v) x w = fderiv ℝ (fderiv ℝ f) x w v := by
    intro v w
    have hd_fd : DifferentiableAt ℝ (fderiv ℝ f) x :=
      ((contDiff_infty_iff_fderiv.1 hf).2.differentiable (by simp)).differentiableAt
    have hcomp := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x hd_fd.hasFDerivAt
    exact congrArg (fun L => L w) hcomp.fderiv
  rw [hf2, hf2]
  exact hsymm.eq (cdir j) (cdir l)

private lemma cpd_zero_liftCylTest {c : ℝ} (hc : 0 < c) {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    {ψ : B0579.Plane → ℝ} (hψ : ContDiff ℝ ∞ ψ) (x : Coord) :
    cpd 0 (liftCylTest c hc θ ψ) x = liftCylTest c hc (deriv θ) ψ x := by
  let g1 : Coord → ℝ := fun y => θ y.1
  let g2 : Coord → ℝ := fun y => qPart c hc y.2.1 * ψ y.2
  have hg1 : HasFDerivAt g1
      ((deriv θ x.1) • ContinuousLinearMap.fst ℝ ℝ B0579.Plane) x :=
    ((hθ.differentiable (by simp)).differentiableAt.hasDerivAt).comp_hasFDerivAt x
      (ContinuousLinearMap.fst ℝ ℝ B0579.Plane).hasFDerivAt
  have hg2_plane : Differentiable ℝ (fun z : B0579.Plane => qPart c hc z.1 * ψ z) :=
    (((qPart_contDiff hc).comp contDiff_fst).mul hψ).differentiable (by simp)
  have hg2 : HasFDerivAt g2
      ((fderiv ℝ (fun z : B0579.Plane => qPart c hc z.1 * ψ z) x.2).comp
        (ContinuousLinearMap.snd ℝ ℝ B0579.Plane)) x :=
    hg2_plane.differentiableAt.hasFDerivAt.comp x
      (ContinuousLinearMap.snd ℝ ℝ B0579.Plane).hasFDerivAt
  have heq : liftCylTest c hc θ ψ = g1 * g2 := by
    funext y; dsimp [liftCylTest, g1, g2]; ring
  unfold cpd
  rw [heq, (hg1.mul hg2).fderiv]
  change θ x.1 *
      (fderiv ℝ (fun z : B0579.Plane => qPart c hc z.1 * ψ z) x.2) (0 : B0579.Plane) +
    qPart c hc x.2.1 * ψ x.2 * (deriv θ x.1 * 1) =
    deriv θ x.1 * qPart c hc x.2.1 * ψ x.2
  rw [map_zero]
  ring

private lemma isCylTest_neg {c : ℝ} {ψ : B0579.Plane → ℝ} (hψ : B0579.IsCylTest c ψ) :
    B0579.IsCylTest c (fun y => -ψ y) := by
  obtain ⟨R, hR⟩ := hψ.band
  exact ⟨hψ.smooth.neg, fun z => by simp [hψ.periodic z], R, fun z hz => by simp [hR z hz]⟩

private lemma isCoordTest_neg {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    IsCoordTest (fun x => -φ x) :=
  ⟨hφ.smooth.neg, hφ.compact.neg, by simpa [tsupport_neg] using hφ.supp⟩

private lemma isH1DivFreeTest_skewGrad {c : ℝ} (hc : 0 < c) {H : B0579.Plane → ℝ}
    (hH : B0579.IsCylTest c H) :
    IIIa.IsH1DivFreeTest c (fun y => ![B0579.pd 1 H y, -B0579.pd 0 H y]) := by
  have h0 : B0579.IsCylTest c (B0579.pd 1 H) := hH.pd 1
  have h1 : B0579.IsCylTest c (fun y => -B0579.pd 0 H y) := isCylTest_neg (hH.pd 0)
  have hc_test : ∀ i : Fin 2, B0579.IsCylTest c (fun y => ![B0579.pd 1 H y, -B0579.pd 0 H y] i) := by
    intro i; fin_cases i
    · exact h0
    · exact h1
  refine ⟨fun i => (hc_test i).smooth, fun x i => (hc_test i).periodic x, fun x => ?_,
    fun i => (memLp_of_isCylTest hc (hc_test i)).1,
    fun i j => (memLp_of_isCylTest hc ((hc_test i).pd j)).1⟩
  change B0579.pd 0 (B0579.pd 1 H) x + B0579.pd 1 (fun y => -B0579.pd 0 H y) x = 0
  have hneg : B0579.pd 1 (fun y => -B0579.pd 0 H y) x = -B0579.pd 1 (B0579.pd 0 H) x := by
    unfold B0579.pd
    rw [show (fun y => -(fderiv ℝ H y) (B0579.dir 0)) = -B0579.pd 0 H from rfl,
      fderiv_neg, neg_apply]
    rfl
  rw [hneg, pd_comm_of_smooth hH.smooth 0 1 x, add_neg_cancel]

private lemma periodize_coordTest_integral {c T a b : ℝ}
    (hc : 0 < c) (hT : 0 < T) (haT : T < a) (hab : a < b)
    {u : CProf} (hu_sm : StronglyMeasurable (tailInd T u))
    (hu_per : QPeriodic c (tailInd T u))
    (hu_loc : ∀ i : Fin 2, (∫⁻ s in Icc a b,
      eLpNorm (fun z => tailInd T u (s, z) i) 2 (volume.restrict (B0579.cell c))) < ⊤)
    {α : Coord → ℝ} (hα : IsCoordTest α) (hα_ts : tsupport α ⊆ Ioo a b ×ˢ univ)
    (i : Fin 2) :
    Integrable (fun x : Coord => u x i * (α x : ℂ)) volume ∧
      IntegrableOn (fun s : ℝ =>
        ∫ z in B0579.cell c, u (s, z) i * (TailPeriodizeAux.qPeriodize c α s z : ℂ))
        (Icc a b) volume ∧
      ∫ x : Coord, u x i * (α x : ℂ) =
        ∫ s in Icc a b,
          ∫ z in B0579.cell c, u (s, z) i * (TailPeriodizeAux.qPeriodize c α s z : ℂ) := by
  obtain ⟨_, _, R1, _, _, hR1_pos, hb1⟩ := TailPeriodizeAux.coordTest_box hα
  have hbox : ∀ x : Coord, (x.1 ∉ Icc a b ∨ R1 < |x.2.1| ∨ R1 < |x.2.2|) → α x = 0 := by
    intro x hx
    rcases hx with h1 | h2 | h3
    · exact image_eq_zero_of_notMem_tsupport fun hxt => h1 (Ioo_subset_Icc_self (hα_ts hxt).1)
    · exact (hb1 x (Or.inr (Or.inl h2))).1
    · exact (hb1 x (Or.inr (Or.inr h3))).1
  have hm_ui : AEStronglyMeasurable (fun x : Coord => tailInd T u x i) volume :=
    ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
      hu_sm).aestronglyMeasurable
  obtain ⟨hint_c, hcell_c, heq_c⟩ :=
    TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize hc (hT.trans haT) hab.le
      hR1_pos hm_ui (hu_per.mono fun _ hx => congrArg (fun v : CMerid => v i) hx)
      (hu_loc i) hα.smooth.continuous hbox
  have h_pt : (fun x : Coord => u x i * (α x : ℂ)) =
      fun x : Coord => tailInd T u x i * (α x : ℂ) := by
    funext x
    by_cases hxT : T < x.1
    · simp [tailInd, hxT]
    · have h0 : α x = 0 := hbox x (Or.inl fun hx_ab => hxT (lt_of_lt_of_le haT hx_ab.1))
      simp [h0]
  have hs_fub := (fubini_cell_slices hcell_c).1
  have h_slice_eq : ∀ s ∈ Icc a b,
      (∫ z in B0579.cell c, tailInd T u (s, z) i * (TailPeriodizeAux.qPeriodize c α s z : ℂ)) =
      (∫ z in B0579.cell c, u (s, z) i * (TailPeriodizeAux.qPeriodize c α s z : ℂ)) := by
    intro s hs
    have hsT : T < s := lt_of_lt_of_le haT hs.1
    refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun z _ => ?_
    simp [tailInd, hsT]
  refine ⟨h_pt ▸ hint_c, hs_fub.congr_fun h_slice_eq measurableSet_Icc, ?_⟩
  rw [h_pt, heq_c]
  exact setIntegral_congr_fun measurableSet_Icc h_slice_eq

/-- For any stream potential `H` with `B0579.IsCylTest p.c H` and smooth cutoff `θ` supported in
`Ioo a b` (`T < a < b`), `sliceWeakTerm` integrates to `0` on `Icc a b` for `∇^⊥ H`. -/
private lemma sliceWeakEq_of_isCylTest {p : Params} {T a b : ℝ}
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train)
    (hT : 0 < T) (haT : T < a) (hab : a < b)
    {g gq gη z₂ zq₂ zη₂ : CProf}
    (hg_src : IsCylSourceH1 p.c g gq gη)
    (hg_int : (∫⁻ s in Ioi T, sliceH1Norm p.c g gq gη s) < ⊤)
    (hz : StronglyMeasurable z₂) (hzq : StronglyMeasurable zq₂) (hzη : StronglyMeasurable zη₂)
    (hzT : IsCylH1Slice p.c (fun y => z₂ (T, y)) (fun y => zq₂ (T, y)) (fun y => zη₂ (T, y)))
    (hz_sol : IsTailMeridionalSolution p T g z₂ zq₂ zη₂)
    (hcont : ∀ s : ℝ, T ≤ s →
      Tendsto (fun s' => cylSliceH1 p.c
        (fun y => z₂ (s', y) - z₂ (s, y))
        (fun y => zq₂ (s', y) - zq₂ (s, y))
        (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici T] s) (𝓝 0))
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hts : tsupport θ ⊆ Ioo a b)
    {H : B0579.Plane → ℝ} (hH : B0579.IsCylTest p.c H) :
    ∫ s in Icc a b, sliceWeakTerm p g z₂ zq₂ zη₂ θ
      (fun y => ![B0579.pd 1 H y, -B0579.pd 0 H y]) s = 0 := by
  have hc : 0 < p.c := p.c_pos
  let Φ : B0579.Plane → Fin 2 → ℝ := fun y => ![B0579.pd 1 H y, -B0579.pd 0 H y]
  have hΦ_cyl : ∀ i : Fin 2, B0579.IsCylTest p.c (fun y => Φ y i) := by
    intro i; fin_cases i
    · exact hH.pd 1
    · exact isCylTest_neg (hH.pd 0)
  let h : Coord → ℝ := liftCylTest p.c hc θ H
  have hdθ_sm : ContDiff ℝ ∞ (deriv θ) := (contDiff_infty_iff_deriv.1 hθ).2
  have hdθ_ts : tsupport (deriv θ) ⊆ Ioo a b :=
    tsupport_deriv_subset.trans hts
  let h' : Coord → ℝ := liftCylTest p.c hc (deriv θ) H
  obtain ⟨hh_test, hh_ts, _⟩ := isCoordTest_liftCylTest hc hT haT hθ hts hH
  obtain ⟨hh'_test, hh'_ts, _⟩ := isCoordTest_liftCylTest hc hT haT hdθ_sm hdθ_ts hH
  let Ψ : Coord → Fin 2 → ℝ := fun x => ![cpd 2 h x, -cpd 1 h x]
  have hΨ_coord : ∀ i : Fin 2, IsCoordTest (fun x => Ψ x i) := by
    intro i; fin_cases i
    · exact isCoordTest_cpd 2 hh_test
    · exact isCoordTest_neg (isCoordTest_cpd 1 hh_test)
  have hΨ_ts_ab : ∀ i : Fin 2, tsupport (fun x => Ψ x i) ⊆ Ioo a b ×ˢ univ := by
    intro i; fin_cases i
    · exact (tsupport_cpd_subset 2 h).trans hh_ts
    · change tsupport (fun x => -cpd 1 h x) ⊆ Ioo a b ×ˢ univ
      rw [show (fun x => -cpd 1 h x) = -cpd 1 h from rfl, tsupport_neg]
      exact (tsupport_cpd_subset 1 h).trans hh_ts
  have hΨ_sol : IsPlanarSolTest Ψ := by
    refine ⟨hΨ_coord, fun x => ?_⟩
    change cpd 1 (cpd 2 h) x + cpd 2 (fun y => -cpd 1 h y) x = 0
    have hneg : cpd 2 (fun y => -cpd 1 h y) x = -cpd 2 (cpd 1 h) x := by
      unfold cpd
      rw [show (fun y => -(fderiv ℝ h y) (cdir 1)) = -cpd 1 h from rfl,
        fderiv_neg, neg_apply]
      rfl
    rw [hneg, cpd_comm_of_smooth hh_test.smooth 1 2 x, add_neg_cancel]
  have hΨ_ts_T : ∀ i : Fin 2, tsupport (fun x => Ψ x i) ⊆ Ioi T ×ˢ univ := fun i =>
    (hΨ_ts_ab i).trans (prod_mono (fun s hs => haT.trans hs.1) Subset.rfl)
  obtain ⟨hint_mt, hint_bv, hint_g, heq_sol⟩ := hz_sol.equation Ψ hΨ_sol hΨ_ts_T
  -- Local L1-in-s L2(cell) bounds for `z₂`, `flatBv`, and `g` on `Icc a b`
  have hT_fin : sliceH1Norm p.c z₂ zq₂ zη₂ T < ⊤ := by
    unfold sliceH1Norm
    exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2
      ⟨hzT.memL2_u.eLpNorm_lt_top, hzT.memL2_uq.eLpNorm_lt_top⟩, hzT.memL2_uη.eLpNorm_lt_top⟩
  have hfin := sliceH1Norm_lt_top_of_ge hz hzq hzη hT_fin hcont
  have hmem := fun t ht => memLp_slice_of_sliceH1Norm_lt_top hz hzq hzη (hfin t ht)
  obtain ⟨hcz, hczq, hczη⟩ := continuousOn_profPaths hz hzq hzη hT_fin hcont
  have hsub_T : Icc a b ⊆ Ici T := fun s hs => haT.le.trans hs.1
  have hper_z := qPeriodic_tailInd (hz_sol.periodic.mono fun _ hx hTx => (hx hTx).1)
  have hper_zq := qPeriodic_tailInd (hz_sol.periodic.mono fun _ hx hTx => (hx hTx).2.1)
  have hper_zη := qPeriodic_tailInd (hz_sol.periodic.mono fun _ hx hTx => (hx hTx).2.2)
  have hper_bv := qPeriodic_tailInd_flatBv hT p.train hper_z hper_zq hper_zη
  have hper_g : QPeriodic p.c (tailInd T g) :=
    qPeriodic_tailInd (((ae_restrict_iff' QPerHalf.measurableSet_pos).1 hg_src.periodic_g).mono
      fun _ hx hTx => hx (hT.trans hTx))
  have hloc_z : ∀ i : Fin 2, (∫⁻ s in Icc a b,
      eLpNorm (fun z => tailInd T z₂ (s, z) i) 2 (volume.restrict (B0579.cell p.c))) < ⊤ := by
    intro i
    have heq : ∫⁻ s in Icc a b,
        eLpNorm (fun z => tailInd T z₂ (s, z) i) 2 (volume.restrict (B0579.cell p.c)) =
        ∫⁻ s in Icc a b,
        eLpNorm (fun z => z₂ (s, z) i) 2 (volume.restrict (B0579.cell p.c)) :=
      setLIntegral_congr_fun measurableSet_Icc fun s hs => by
        simp [tailInd, lt_of_lt_of_le haT hs.1]
    rw [heq]
    exact (lintegral_mono fun s => eLpNorm_comp_le_merid p.c z₂ s i).trans_lt
      (loc_eLpNorm_lt_top_of_continuousOn_profPath (fun t ht => (hmem t ht).1) hcz haT.le)
  obtain ⟨C_bv, _, hbv⟩ := memLp_slice_flatBv_on p.train htr hz hzq hzη
    (hT.trans haT) hab.le (fun s hs => hmem s (hsub_T hs))
    (hcz.mono hsub_T) (hczq.mono hsub_T) (hczη.mono hsub_T)
  have hloc_bv : ∀ i : Fin 2, (∫⁻ s in Icc a b,
      eLpNorm (fun z => tailInd T (flatBv p.train z₂ zq₂ zη₂) (s, z) i) 2
        (volume.restrict (B0579.cell p.c))) < ⊤ := by
    intro i
    have hle : ∫⁻ s in Icc a b,
        eLpNorm (fun z => tailInd T (flatBv p.train z₂ zq₂ zη₂) (s, z) i) 2
          (volume.restrict (B0579.cell p.c)) ≤
        ∫⁻ _ in Icc a b, ENNReal.ofReal C_bv := by
      refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
      have hsT : T < s := lt_of_lt_of_le haT hs.1
      have heq_fn : (fun z => tailInd T (flatBv p.train z₂ zq₂ zη₂) (s, z) i) =
          fun z => flatBv p.train z₂ zq₂ zη₂ (s, z) i := by
        funext z; simp [tailInd, hsT]
      rw [heq_fn]
      exact (hbv s hs i).2.2
    rw [setLIntegral_const] at hle
    exact hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Icc_lt_top)
  obtain ⟨hloc_gH1, _, hae_g⟩ := source_slice_regularity hc hT hg_src hg_int
  have hloc_g : ∀ i : Fin 2, (∫⁻ s in Icc a b,
      eLpNorm (fun z => tailInd T g (s, z) i) 2 (volume.restrict (B0579.cell p.c))) < ⊤ := by
    intro i
    have hle : ∫⁻ s in Icc a b,
        eLpNorm (fun z => tailInd T g (s, z) i) 2 (volume.restrict (B0579.cell p.c)) ≤
        ∫⁻ s in Icc a b, sliceH1Norm p.c g gq gη s := by
      refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
      have hsT : T < s := lt_of_lt_of_le haT hs.1
      have heq_fn : (fun z => tailInd T g (s, z) i) = fun z => g (s, z) i := by
        funext z; simp [tailInd, hsT]
      rw [heq_fn]
      exact (eLpNorm_comp_le_merid p.c g s i).trans (le_self_add.trans le_self_add)
    exact hle.trans_lt (hloc_gH1 a b haT.le)
  -- `qPeriodize` formulas for `Ψ`, `cpd 0 Ψ`, and `cpd j.succ (cpd j.succ Ψ)`
  have hqP_Ψ : ∀ (i : Fin 2) (s : ℝ) (y : B0579.Plane),
      TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y = θ s * Φ y i := by
    intro i s y
    fin_cases i
    · change TailPeriodizeAux.qPeriodize p.c (cpd (Fin.succ 1) h) s y = θ s * B0579.pd 1 H y
      rw [← TailPeriodizeAux.pd_qPeriodize hc (φ := h) hh_test s 1 y]
      have heq_fn : TailPeriodizeAux.qPeriodize p.c h s = fun w => θ s * H w :=
        funext fun w => qPeriodize_liftCylTest hc θ hH.periodic s w
      rw [heq_fn]; unfold B0579.pd
      rw [fderiv_const_mul hH.differentiable.differentiableAt, smul_apply,
        smul_eq_mul]
    · change TailPeriodizeAux.qPeriodize p.c (fun x => -cpd 1 h x) s y = θ s * (-B0579.pd 0 H y)
      have hneg_tsum : TailPeriodizeAux.qPeriodize p.c (fun x => -cpd 1 h x) s y =
          -TailPeriodizeAux.qPeriodize p.c (cpd (Fin.succ 0) h) s y := by
        unfold TailPeriodizeAux.qPeriodize; exact tsum_neg
      rw [hneg_tsum, ← TailPeriodizeAux.pd_qPeriodize hc (φ := h) hh_test s 0 y]
      have heq_fn : TailPeriodizeAux.qPeriodize p.c h s = fun w => θ s * H w :=
        funext fun w => qPeriodize_liftCylTest hc θ hH.periodic s w
      rw [heq_fn]; unfold B0579.pd
      rw [fderiv_const_mul hH.differentiable.differentiableAt, smul_apply,
        smul_eq_mul, mul_neg]
  have hcpd0_Ψ : ∀ (i : Fin 2) (x : Coord),
      cpd 0 (fun y => Ψ y i) x = ![cpd 2 h' x, -cpd 1 h' x] i := by
    have hh0 : cpd 0 h = h' := funext fun y => cpd_zero_liftCylTest hc hθ hH.smooth y
    intro i x
    fin_cases i
    · change cpd 0 (cpd 2 h) x = cpd 2 h' x
      rw [cpd_comm_of_smooth hh_test.smooth 0 2 x, hh0]
    · change cpd 0 (fun y => -cpd 1 h y) x = -cpd 1 h' x
      have hneg : cpd 0 (fun y => -cpd 1 h y) x = -cpd 0 (cpd 1 h) x := by
        unfold cpd
        rw [show (fun y => -(fderiv ℝ h y) (cdir 1)) = -cpd 1 h from rfl,
          fderiv_neg, neg_apply]
        rfl
      rw [hneg, cpd_comm_of_smooth hh_test.smooth 0 1 x, hh0]
  have hqP_cpd0 : ∀ (i : Fin 2) (s : ℝ) (y : B0579.Plane),
      TailPeriodizeAux.qPeriodize p.c (cpd 0 (fun x => Ψ x i)) s y = deriv θ s * Φ y i := by
    intro i s y
    have heq_fn0 : cpd 0 (fun x => Ψ x i) = fun x => ![cpd 2 h' x, -cpd 1 h' x] i :=
      funext fun x => hcpd0_Ψ i x
    rw [heq_fn0]
    fin_cases i
    · change TailPeriodizeAux.qPeriodize p.c (cpd (Fin.succ 1) h') s y = deriv θ s * B0579.pd 1 H y
      rw [← TailPeriodizeAux.pd_qPeriodize hc (φ := h') hh'_test s 1 y]
      have heq_fn : TailPeriodizeAux.qPeriodize p.c h' s = fun w => deriv θ s * H w :=
        funext fun w => qPeriodize_liftCylTest hc (deriv θ) hH.periodic s w
      rw [heq_fn]; unfold B0579.pd
      rw [fderiv_const_mul hH.differentiable.differentiableAt, smul_apply,
        smul_eq_mul]
    · change TailPeriodizeAux.qPeriodize p.c (fun x => -cpd 1 h' x) s y =
          deriv θ s * (-B0579.pd 0 H y)
      have hneg_tsum : TailPeriodizeAux.qPeriodize p.c (fun x => -cpd 1 h' x) s y =
          -TailPeriodizeAux.qPeriodize p.c (cpd (Fin.succ 0) h') s y := by
        unfold TailPeriodizeAux.qPeriodize; exact tsum_neg
      rw [hneg_tsum, ← TailPeriodizeAux.pd_qPeriodize hc (φ := h') hh'_test s 0 y]
      have heq_fn : TailPeriodizeAux.qPeriodize p.c h' s = fun w => deriv θ s * H w :=
        funext fun w => qPeriodize_liftCylTest hc (deriv θ) hH.periodic s w
      rw [heq_fn]; unfold B0579.pd
      rw [fderiv_const_mul hH.differentiable.differentiableAt, smul_apply,
        smul_eq_mul, mul_neg]
  have hqP_cpd2 : ∀ (i : Fin 2) (j : Fin 2) (s : ℝ) (y : B0579.Plane),
      TailPeriodizeAux.qPeriodize p.c
        (cpd j.succ (cpd j.succ (fun x => Ψ x i))) s y =
      θ s * B0579.pd j (B0579.pd j (fun w => Φ w i)) y := by
    intro i j s y
    rw [← TailPeriodizeAux.pd_qPeriodize hc (isCoordTest_cpd j.succ (hΨ_coord i)) s j y]
    have heq1 : TailPeriodizeAux.qPeriodize p.c (cpd j.succ (fun x => Ψ x i)) s =
        B0579.pd j (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s) :=
      funext fun w => (TailPeriodizeAux.pd_qPeriodize hc (hΨ_coord i) s j w).symm
    have heq2 : TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s = fun w => θ s * Φ w i :=
      funext fun w => hqP_Ψ i s w
    rw [heq1, heq2]
    have heq3 : B0579.pd j (fun w => θ s * Φ w i) = fun w => θ s * B0579.pd j (fun u => Φ u i) w := by
      funext w; unfold B0579.pd
      rw [fderiv_const_mul (hΦ_cyl i).differentiable.differentiableAt,
        smul_apply, smul_eq_mul]
    rw [heq3]
    change (fderiv ℝ (fun w => θ s * B0579.pd j (fun u => Φ u i) w) y) (B0579.dir j) =
      θ s * B0579.pd j (B0579.pd j (fun w => Φ w i)) y
    rw [fderiv_const_mul ((hΦ_cyl i).pd j).differentiable.differentiableAt,
      smul_apply, smul_eq_mul]
    rfl
  -- Periodize each component term
  have hp_time := fun i : Fin 2 =>
    periodize_coordTest_integral hc hT haT hab (stronglyMeasurable_tailInd T hz) hper_z hloc_z
      (isCoordTest_cpd 0 (hΨ_coord i)) ((tsupport_cpd_subset 0 _).trans (hΨ_ts_ab i)) i
  have hp_lap := fun (i j : Fin 2) =>
    periodize_coordTest_integral hc hT haT hab (stronglyMeasurable_tailInd T hz) hper_z hloc_z
      (isCoordTest_cpd j.succ (isCoordTest_cpd j.succ (hΨ_coord i)))
      ((tsupport_cpd_subset j.succ _).trans ((tsupport_cpd_subset j.succ _).trans (hΨ_ts_ab i))) i
  have hp_lap1 : ∀ i : Fin 2,
      Integrable (fun x => z₂ x i * (cpd 1 (cpd 1 (fun x => Ψ x i)) x : ℂ)) ∧
      IntegrableOn (fun s => ∫ z in B0579.cell p.c,
        z₂ (s, z) i * (TailPeriodizeAux.qPeriodize p.c
          (cpd 1 (cpd 1 (fun x => Ψ x i))) s z : ℂ)) (Icc a b) ∧
      ∫ x : Coord, z₂ x i * (cpd 1 (cpd 1 (fun x => Ψ x i)) x : ℂ) =
        ∫ s in Icc a b, ∫ z in B0579.cell p.c,
          z₂ (s, z) i * (TailPeriodizeAux.qPeriodize p.c
            (cpd 1 (cpd 1 (fun x => Ψ x i))) s z : ℂ) := fun i => hp_lap i 0
  have hp_lap2 : ∀ i : Fin 2,
      Integrable (fun x => z₂ x i * (cpd 2 (cpd 2 (fun x => Ψ x i)) x : ℂ)) ∧
      IntegrableOn (fun s => ∫ z in B0579.cell p.c,
        z₂ (s, z) i * (TailPeriodizeAux.qPeriodize p.c
          (cpd 2 (cpd 2 (fun x => Ψ x i))) s z : ℂ)) (Icc a b) ∧
      ∫ x : Coord, z₂ x i * (cpd 2 (cpd 2 (fun x => Ψ x i)) x : ℂ) =
        ∫ s in Icc a b, ∫ z in B0579.cell p.c,
          z₂ (s, z) i * (TailPeriodizeAux.qPeriodize p.c
            (cpd 2 (cpd 2 (fun x => Ψ x i))) s z : ℂ) := fun i => hp_lap i 1
  have hp_bv := fun i : Fin 2 =>
    periodize_coordTest_integral hc hT haT hab
      (stronglyMeasurable_tailInd_flatBv hT p.train hz hzq hzη) hper_bv hloc_bv
      (hΨ_coord i) (hΨ_ts_ab i) i
  have hp_g := fun i : Fin 2 =>
    periodize_coordTest_integral hc hT haT hab (stronglyMeasurable_tailInd T hg_src.sm_g)
      hper_g hloc_g (hΨ_coord i) (hΨ_ts_ab i) i
  -- Rewrite the Coord equation into sum of slice integrals = 0
  have h_mt_eq : ∫ x : Coord, ∑ i : Fin 2, z₂ x i * meridTranspose p.ν Ψ x i =
      ∑ i : Fin 2, (-(∫ s in Icc a b, ∫ y in B0579.cell p.c,
          z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c (cpd 0 (fun x => Ψ x i)) s y : ℂ)) -
        (p.ν : ℂ) * ((∫ s in Icc a b, ∫ y in B0579.cell p.c,
            z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c
              (cpd 1 (cpd 1 (fun x => Ψ x i))) s y : ℂ)) +
          (∫ s in Icc a b, ∫ y in B0579.cell p.c,
            z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c
              (cpd 2 (cpd 2 (fun x => Ψ x i))) s y : ℂ)))) := by
    have hi_lap_sum : ∀ i : Fin 2, Integrable (fun x : Coord =>
        (p.ν : ℂ) * (z₂ x i * (cpd 1 (cpd 1 (fun y => Ψ y i)) x : ℂ) +
          z₂ x i * (cpd 2 (cpd 2 (fun y => Ψ y i)) x : ℂ))) := fun i =>
      (((hp_lap1 i).1.add (hp_lap2 i).1).const_mul (p.ν : ℂ))
    have hi_mt : ∀ i : Fin 2, Integrable (fun x : Coord => z₂ x i * meridTranspose p.ν Ψ x i) := by
      intro i
      refine (((hp_time i).1.fun_neg).sub (hi_lap_sum i)).congr
        (Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply, meridTranspose]
      push_cast; ring
    rw [integral_finsetSum Finset.univ fun i _ => hi_mt i]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h_expand : (fun x : Coord => z₂ x i * meridTranspose p.ν Ψ x i) =
        fun x : Coord => -(z₂ x i * (cpd 0 (fun y => Ψ y i) x : ℂ)) -
          (p.ν : ℂ) * (z₂ x i * (cpd 1 (cpd 1 (fun y => Ψ y i)) x : ℂ) +
            z₂ x i * (cpd 2 (cpd 2 (fun y => Ψ y i)) x : ℂ)) := by
      funext x; dsimp only [meridTranspose]; push_cast; ring
    rw [h_expand, integral_sub (hp_time i).1.fun_neg (hi_lap_sum i),
      integral_neg, integral_const_mul, integral_add (hp_lap1 i).1 (hp_lap2 i).1,
      (hp_time i).2.2, (hp_lap1 i).2.2, (hp_lap2 i).2.2]
  have h_bv_eq : ∫ x : Coord, cdot (flatBv p.train z₂ zq₂ zη₂) Ψ x =
      ∑ i : Fin 2, ∫ s in Icc a b, ∫ y in B0579.cell p.c,
        flatBv p.train z₂ zq₂ zη₂ (s, y) i *
          (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ) := by
    unfold cdot
    rw [integral_finsetSum Finset.univ fun i _ => (hp_bv i).1]
    exact Finset.sum_congr rfl fun i _ => (hp_bv i).2.2
  have h_g_eq : ∫ x : Coord, cdot g Ψ x =
      ∑ i : Fin 2, ∫ s in Icc a b, ∫ y in B0579.cell p.c,
        g (s, y) i * (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ) := by
    unfold cdot
    rw [integral_finsetSum Finset.univ fun i _ => (hp_g i).1]
    exact Finset.sum_congr rfl fun i _ => (hp_g i).2.2
  have h_comb_zero :
      (∫ x : Coord, ∑ i : Fin 2, z₂ x i * meridTranspose p.ν Ψ x i) +
        (∫ x : Coord, cdot (flatBv p.train z₂ zq₂ zη₂) Ψ x) -
        (∫ x : Coord, cdot g Ψ x) = 0 := by
    rw [← integral_add hint_mt hint_bv, heq_sol, sub_self]
  rw [h_mt_eq, h_bv_eq, h_g_eq] at h_comb_zero
  -- Combine all `Icc a b` integrals under a single `∫ s in Icc a b, ...`
  have hreg := tail_slice_regularity hT hz hzq hzη hzT hz_sol hcont
  have hI_lap_s : ∀ i : Fin 2, IntegrableOn (fun s : ℝ =>
      (p.ν : ℂ) * ((∫ y in B0579.cell p.c,
          z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c
            (cpd 1 (cpd 1 (fun x => Ψ x i))) s y : ℂ)) +
        (∫ y in B0579.cell p.c,
          z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c
            (cpd 2 (cpd 2 (fun x => Ψ x i))) s y : ℂ)))) (Icc a b) := fun i =>
    (((hp_lap1 i).2.1.add (hp_lap2 i).2.1).const_mul (p.ν : ℂ))
  have hI_mt_s : ∀ i : Fin 2, IntegrableOn (fun s : ℝ =>
      -(∫ y in B0579.cell p.c,
          z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c (cpd 0 (fun x => Ψ x i)) s y : ℂ)) -
        (p.ν : ℂ) * ((∫ y in B0579.cell p.c,
            z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c
              (cpd 1 (cpd 1 (fun x => Ψ x i))) s y : ℂ)) +
          (∫ y in B0579.cell p.c,
            z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c
              (cpd 2 (cpd 2 (fun x => Ψ x i))) s y : ℂ)))) (Icc a b) := fun i =>
    (hp_time i).2.1.fun_neg.sub (hI_lap_s i)
  have h_mt_sum_s : (∑ i : Fin 2, (-(∫ s in Icc a b, ∫ y in B0579.cell p.c,
          z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c (cpd 0 (fun x => Ψ x i)) s y : ℂ)) -
        (p.ν : ℂ) * ((∫ s in Icc a b, ∫ y in B0579.cell p.c,
            z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c
              (cpd 1 (cpd 1 (fun x => Ψ x i))) s y : ℂ)) +
          (∫ s in Icc a b, ∫ y in B0579.cell p.c,
            z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c
              (cpd 2 (cpd 2 (fun x => Ψ x i))) s y : ℂ))))) =
      ∫ s in Icc a b, ∑ i : Fin 2,
        (-(∫ y in B0579.cell p.c,
            z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c (cpd 0 (fun x => Ψ x i)) s y : ℂ)) -
          (p.ν : ℂ) * ((∫ y in B0579.cell p.c,
              z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c
                (cpd 1 (cpd 1 (fun x => Ψ x i))) s y : ℂ)) +
            (∫ y in B0579.cell p.c,
              z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c
                (cpd 2 (cpd 2 (fun x => Ψ x i))) s y : ℂ)))) := by
    rw [integral_finsetSum Finset.univ fun i _ => hI_mt_s i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_sub (hp_time i).2.1.fun_neg (hI_lap_s i),
      integral_neg, integral_const_mul, integral_add (hp_lap1 i).2.1 (hp_lap2 i).2.1]
  have h_bv_sum_s : (∑ i : Fin 2, ∫ s in Icc a b, ∫ y in B0579.cell p.c,
        flatBv p.train z₂ zq₂ zη₂ (s, y) i *
          (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ)) =
      ∫ s in Icc a b, ∑ i : Fin 2, ∫ y in B0579.cell p.c,
        flatBv p.train z₂ zq₂ zη₂ (s, y) i *
          (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ) :=
    (integral_finsetSum Finset.univ fun i _ => (hp_bv i).2.1).symm
  have h_g_sum_s : (∑ i : Fin 2, ∫ s in Icc a b, ∫ y in B0579.cell p.c,
        g (s, y) i * (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ)) =
      ∫ s in Icc a b, ∑ i : Fin 2, ∫ y in B0579.cell p.c,
        g (s, y) i * (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ) :=
    (integral_finsetSum Finset.univ fun i _ => (hp_g i).2.1).symm
  have hI_sum_mt : IntegrableOn (fun s : ℝ => ∑ i : Fin 2,
      (-(∫ y in B0579.cell p.c,
          z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c (cpd 0 (fun x => Ψ x i)) s y : ℂ)) -
        (p.ν : ℂ) * ((∫ y in B0579.cell p.c,
            z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c
              (cpd 1 (cpd 1 (fun x => Ψ x i))) s y : ℂ)) +
          (∫ y in B0579.cell p.c,
            z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c
              (cpd 2 (cpd 2 (fun x => Ψ x i))) s y : ℂ))))) (Icc a b) :=
    integrable_finsetSum Finset.univ fun i _ => hI_mt_s i
  have hI_sum_bv : IntegrableOn (fun s : ℝ => ∑ i : Fin 2, ∫ y in B0579.cell p.c,
      flatBv p.train z₂ zq₂ zη₂ (s, y) i *
        (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ)) (Icc a b) :=
    integrable_finsetSum Finset.univ fun i _ => (hp_bv i).2.1
  have hI_sum_g : IntegrableOn (fun s : ℝ => ∑ i : Fin 2, ∫ y in B0579.cell p.c,
      g (s, y) i * (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ)) (Icc a b) :=
    integrable_finsetSum Finset.univ fun i _ => (hp_g i).2.1
  have hI_sum_mt_bv : IntegrableOn (fun s : ℝ =>
      (∑ i : Fin 2, (-(∫ y in B0579.cell p.c,
          z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c (cpd 0 (fun x => Ψ x i)) s y : ℂ)) -
        (p.ν : ℂ) * ((∫ y in B0579.cell p.c,
            z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c
              (cpd 1 (cpd 1 (fun x => Ψ x i))) s y : ℂ)) +
          (∫ y in B0579.cell p.c,
            z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c
              (cpd 2 (cpd 2 (fun x => Ψ x i))) s y : ℂ))))) +
      (∑ i : Fin 2, ∫ y in B0579.cell p.c,
        flatBv p.train z₂ zq₂ zη₂ (s, y) i *
          (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ))) (Icc a b) :=
    hI_sum_mt.add hI_sum_bv
  rw [h_mt_sum_s, h_bv_sum_s, h_g_sum_s,
    ← integral_add hI_sum_mt hI_sum_bv,
    ← integral_sub hI_sum_mt_bv hI_sum_g] at h_comb_zero
  -- Identify the integrand on `Icc a b` a.e. with `sliceWeakTerm`
  refine (integral_congr_ae ?_).trans h_comb_zero
  filter_upwards [ae_restrict_of_ae hae_g, ae_restrict_mem measurableSet_Icc] with s hsg hs
  have hsT : T < s := lt_of_lt_of_le haT hs.1
  have hfin_g := (hsg hsT).1
  obtain ⟨hmg, _, _⟩ :=
    memLp_slice_of_sliceH1Norm_lt_top hg_src.sm_g hg_src.sm_gq hg_src.sm_gη hfin_g
  have hm_s := hmem s hsT.le
  obtain ⟨hw_z, _, _, _⟩ := hreg s hsT.le
  obtain ⟨_, hΦ_memC0⟩ := memLp_of_isCylTest hc (hΦ_cyl 0)
  obtain ⟨_, hΦ_memC1⟩ := memLp_of_isCylTest hc (hΦ_cyl 1)
  have hΦ_memC : ∀ i : Fin 2, MemLp (fun y => (Φ y i : ℂ)) 2 (volume.restrict (B0579.cell p.c)) := by
    intro i; fin_cases i
    · exact hΦ_memC0
    · exact hΦ_memC1
  have hpd_memC : ∀ i j : Fin 2,
      MemLp (fun y => (B0579.pd j (fun w => Φ w i) y : ℂ)) 2 (volume.restrict (B0579.cell p.c)) :=
    fun i j => (memLp_of_isCylTest hc ((hΦ_cyl i).pd j)).2
  have hz_memC : ∀ i : Fin 2, MemLp (fun y => z₂ (s, y) i) 2 (volume.restrict (B0579.cell p.c)) :=
    fun i => ⟨((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
        (sliceMeas hz s)).aestronglyMeasurable,
      (eLpNorm_comp_le_merid p.c z₂ s i).trans_lt hm_s.1.eLpNorm_lt_top⟩
  have hzq_memC : ∀ i : Fin 2, MemLp (fun y => zq₂ (s, y) i) 2 (volume.restrict (B0579.cell p.c)) :=
    fun i => ⟨((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
        (sliceMeas hzq s)).aestronglyMeasurable,
      (eLpNorm_comp_le_merid p.c zq₂ s i).trans_lt hm_s.2.1.eLpNorm_lt_top⟩
  have hzη_memC : ∀ i : Fin 2, MemLp (fun y => zη₂ (s, y) i) 2 (volume.restrict (B0579.cell p.c)) :=
    fun i => ⟨((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
        (sliceMeas hzη s)).aestronglyMeasurable,
      (eLpNorm_comp_le_merid p.c zη₂ s i).trans_lt hm_s.2.2.eLpNorm_lt_top⟩
  have hg_memC : ∀ i : Fin 2, MemLp (fun y => g (s, y) i) 2 (volume.restrict (B0579.cell p.c)) :=
    fun i => ⟨((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
        (sliceMeas hg_src.sm_g s)).aestronglyMeasurable,
      (eLpNorm_comp_le_merid p.c g s i).trans_lt hmg.eLpNorm_lt_top⟩
  have ht_i : ∀ i : Fin 2,
      (∫ y in B0579.cell p.c,
        z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c (cpd 0 (fun x => Ψ x i)) s y : ℂ)) =
      ((deriv θ s : ℝ) : ℂ) * ∫ y in B0579.cell p.c, z₂ (s, y) i * (Φ y i : ℂ) := by
    intro i
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (B0579.measurableSet_cell p.c) fun y _ => ?_
    rw [hqP_cpd0 i s y]; push_cast; ring
  have hlap_0 : ∀ i : Fin 2,
      (∫ y in B0579.cell p.c,
        z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c
          (cpd 1 (cpd 1 (fun x => Ψ x i))) s y : ℂ)) =
      -(θ s : ℂ) * ∫ y in B0579.cell p.c,
        zq₂ (s, y) i * (B0579.pd 0 (fun w => Φ w i) y : ℂ) := by
    intro i
    have hibp := (hw_z i).1.2 (B0579.pd 0 (fun w => Φ w i)) ((hΦ_cyl i).pd 0)
    have hmul : (∫ y in B0579.cell p.c,
        z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c
          (cpd 1 (cpd 1 (fun x => Ψ x i))) s y : ℂ)) =
        (θ s : ℂ) * ∫ y in B0579.cell p.c,
          z₂ (s, y) i * (B0579.pd 0 (B0579.pd 0 (fun w => Φ w i)) y : ℂ) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun (B0579.measurableSet_cell p.c) fun y _ => ?_
      have h1 : TailPeriodizeAux.qPeriodize p.c (cpd 1 (cpd 1 fun x => Ψ x i)) s y =
          θ s * B0579.pd 0 (B0579.pd 0 (fun w => Φ w i)) y := hqP_cpd2 i 0 s y
      rw [h1]; push_cast; ring
    rw [hmul, hibp]; ring
  have hlap_1 : ∀ i : Fin 2,
      (∫ y in B0579.cell p.c,
        z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c
          (cpd 2 (cpd 2 (fun x => Ψ x i))) s y : ℂ)) =
      -(θ s : ℂ) * ∫ y in B0579.cell p.c,
        zη₂ (s, y) i * (B0579.pd 1 (fun w => Φ w i) y : ℂ) := by
    intro i
    have hibp := (hw_z i).2.2 (B0579.pd 1 (fun w => Φ w i)) ((hΦ_cyl i).pd 1)
    have hmul : (∫ y in B0579.cell p.c,
        z₂ (s, y) i * (TailPeriodizeAux.qPeriodize p.c
          (cpd 2 (cpd 2 (fun x => Ψ x i))) s y : ℂ)) =
        (θ s : ℂ) * ∫ y in B0579.cell p.c,
          z₂ (s, y) i * (B0579.pd 1 (B0579.pd 1 (fun w => Φ w i)) y : ℂ) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun (B0579.measurableSet_cell p.c) fun y _ => ?_
      have h1 : TailPeriodizeAux.qPeriodize p.c (cpd 2 (cpd 2 fun x => Ψ x i)) s y =
          θ s * B0579.pd 1 (B0579.pd 1 (fun w => Φ w i)) y := hqP_cpd2 i 1 s y
      rw [h1]; push_cast; ring
    rw [hmul, hibp]; ring
  have hbv_i : ∀ i : Fin 2,
      (∫ y in B0579.cell p.c,
        flatBv p.train z₂ zq₂ zη₂ (s, y) i *
          (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ)) =
      (θ s : ℂ) * ∫ y in B0579.cell p.c,
        flatBv p.train z₂ zq₂ zη₂ (s, y) i * (Φ y i : ℂ) := by
    intro i
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (B0579.measurableSet_cell p.c) fun y _ => ?_
    rw [hqP_Ψ i s y]; push_cast; ring
  have hg_i : ∀ i : Fin 2,
      (∫ y in B0579.cell p.c,
        g (s, y) i * (TailPeriodizeAux.qPeriodize p.c (fun x => Ψ x i) s y : ℂ)) =
      (θ s : ℂ) * ∫ y in B0579.cell p.c, g (s, y) i * (Φ y i : ℂ) := by
    intro i
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (B0579.measurableSet_cell p.c) fun y _ => ?_
    rw [hqP_Ψ i s y]; push_cast; ring
  change sliceWeakTerm p g z₂ zq₂ zη₂ θ Φ s = _
  dsimp only [sliceWeakTerm]
  have hi_z : ∀ i : Fin 2, IntegrableOn (fun y => z₂ (s, y) i * (Φ y i : ℂ)) (B0579.cell p.c) :=
    fun i => ((hz_memC i).integrable_mul (hΦ_memC i)).congr (Eventually.of_forall fun _ => rfl)
  have hi_zq : ∀ i : Fin 2,
      IntegrableOn (fun y => zq₂ (s, y) i * (B0579.pd 0 (fun w => Φ w i) y : ℂ)) (B0579.cell p.c) :=
    fun i => ((hzq_memC i).integrable_mul (hpd_memC i 0)).congr (Eventually.of_forall fun _ => rfl)
  have hi_zη : ∀ i : Fin 2,
      IntegrableOn (fun y => zη₂ (s, y) i * (B0579.pd 1 (fun w => Φ w i) y : ℂ)) (B0579.cell p.c) :=
    fun i => ((hzη_memC i).integrable_mul (hpd_memC i 1)).congr (Eventually.of_forall fun _ => rfl)
  have hi_bv : ∀ i : Fin 2,
      IntegrableOn (fun y => flatBv p.train z₂ zq₂ zη₂ (s, y) i * (Φ y i : ℂ)) (B0579.cell p.c) :=
    fun i => ((hbv s hs i).1.integrable_mul (hΦ_memC i)).congr (Eventually.of_forall fun _ => rfl)
  have hi_g : ∀ i : Fin 2, IntegrableOn (fun y => g (s, y) i * (Φ y i : ℂ)) (B0579.cell p.c) :=
    fun i => ((hg_memC i).integrable_mul (hΦ_memC i)).congr (Eventually.of_forall fun _ => rfl)
  have hi_zqzη : ∀ i : Fin 2, IntegrableOn (fun y =>
      zq₂ (s, y) i * (B0579.pd 0 (fun w => Φ w i) y : ℂ) +
        zη₂ (s, y) i * (B0579.pd 1 (fun w => Φ w i) y : ℂ)) (B0579.cell p.c) :=
    fun i => (hi_zq i).add (hi_zη i)
  rw [integral_finsetSum Finset.univ fun i _ => hi_z i,
    integral_finsetSum Finset.univ fun i _ => hi_zqzη i,
    integral_finsetSum Finset.univ fun i _ => hi_bv i,
    integral_finsetSum Finset.univ fun i _ => hi_g i]
  have hv_i : ∀ i : Fin 2,
      (∫ y in B0579.cell p.c,
        (zq₂ (s, y) i * (B0579.pd 0 (fun w => Φ w i) y : ℂ) +
          zη₂ (s, y) i * (B0579.pd 1 (fun w => Φ w i) y : ℂ))) =
      (∫ y in B0579.cell p.c, zq₂ (s, y) i * (B0579.pd 0 (fun w => Φ w i) y : ℂ)) +
        (∫ y in B0579.cell p.c, zη₂ (s, y) i * (B0579.pd 1 (fun w => Φ w i) y : ℂ)) :=
    fun i => integral_add (hi_zq i) (hi_zη i)
  simp_rw [hv_i, ht_i, hlap_0, hlap_1, hbv_i, hg_i, Fin.sum_univ_two]
  ring

private lemma isH1DivFreeTest_of_isFlatSpatialTest {c : ℝ} (hc : 0 < c)
    {Φ : B0579.Plane → Fin 2 → ℝ} (hΦ : IIIa.IsFlatSpatialTest c Φ) :
    IIIa.IsH1DivFreeTest c Φ := by
  obtain ⟨R0, hR0⟩ := hΦ.bounded
  have hcyl : ∀ i : Fin 2, B0579.IsCylTest c (fun x => Φ x i) := fun i =>
    ⟨hΦ.smooth i, fun x => hΦ.periodic x i, max 1 R0,
      fun x hx => hR0 x i ((le_max_right 1 R0).trans_lt hx)⟩
  exact ⟨hΦ.smooth, hΦ.periodic, hΦ.divFree,
    fun i => (memLp_of_isCylTest hc (hcyl i)).1,
    fun i j => (memLp_of_isCylTest hc ((hcyl i).pd j)).1⟩

private lemma pd_comp_snd {g : ℝ → ℝ} (hg : Differentiable ℝ g) (z : B0579.Plane) :
    B0579.pd 0 (fun w : B0579.Plane => g w.2) z = 0 ∧
      B0579.pd 1 (fun w : B0579.Plane => g w.2) z = deriv g z.2 := by
  have hfd : HasFDerivAt (fun w : B0579.Plane => g w.2)
      ((deriv g z.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) z :=
    hg.differentiableAt.hasDerivAt.comp_hasFDerivAt z
      (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  unfold B0579.pd
  rw [hfd.fderiv]
  simp [B0579.dir]

/-- Extension of `sliceWeakEq_of_isCylTest` from `∇^⊥ H` (`H` compactly `η`-supported) to all
`IIIa.IsFlatSpatialTest p.c Φ` (removing the zero-flux constraint on `Φ · 0` via a large-scale
`η`-cutoff of the bounded primitive of `c⁻¹ ∫ Φ₀ dq`). -/
private lemma sliceWeakEq_of_isFlatSpatialTest {p : Params} {T a b : ℝ}
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train)
    (hT : 0 < T) (haT : T < a) (hab : a < b)
    {g gq gη z₂ zq₂ zη₂ : CProf}
    (hg_src : IsCylSourceH1 p.c g gq gη)
    (hg_int : (∫⁻ s in Ioi T, sliceH1Norm p.c g gq gη s) < ⊤)
    (hz : StronglyMeasurable z₂) (hzq : StronglyMeasurable zq₂) (hzη : StronglyMeasurable zη₂)
    (hzT : IsCylH1Slice p.c (fun y => z₂ (T, y)) (fun y => zq₂ (T, y)) (fun y => zη₂ (T, y)))
    (hz_sol : IsTailMeridionalSolution p T g z₂ zq₂ zη₂)
    (hcont : ∀ s : ℝ, T ≤ s →
      Tendsto (fun s' => cylSliceH1 p.c
        (fun y => z₂ (s', y) - z₂ (s, y))
        (fun y => zq₂ (s', y) - zq₂ (s, y))
        (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici T] s) (𝓝 0))
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hts : tsupport θ ⊆ Ioo a b)
    {Φ : B0579.Plane → Fin 2 → ℝ} (hΦ : IIIa.IsFlatSpatialTest p.c Φ) :
    ∫ s in Icc a b, sliceWeakTerm p g z₂ zq₂ zη₂ θ Φ s = 0 := by
  have hc : 0 < p.c := p.c_pos
  have hΦ_h1 : IIIa.IsH1DivFreeTest p.c Φ := isH1DivFreeTest_of_isFlatSpatialTest hc hΦ
  obtain ⟨R0, hR0⟩ := hΦ.bounded
  let R : ℝ := max 1 R0
  have hR_pos : 0 < R := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hΦ_van : ∀ (x : B0579.Plane) (i : Fin 2), R < |x.2| → Φ x i = 0 :=
    fun x i hx => hR0 x i ((le_max_right 1 R0).trans_lt hx)
  have hq1_zero := IIIa.dfcQMeanZero p.c hc Φ hΦ_h1
  obtain ⟨hθ0_sm, hθ0_per, hθ0_pd0, hθ0_pd1⟩ :=
    IIIa.dfcPotentialFormulas p.c hc Φ hΦ_h1 hq1_zero
  let θ0 : B0579.Plane → ℝ := IIIa.dfcPotential p.c Φ
  have hθ0_van : ∀ x : B0579.Plane, R < |x.2| → θ0 x = 0 := by
    intro x hx
    have hprim0 : ∀ q : ℝ, IIIa.dfcQPrim p.c (fun y => Φ y 1) (q, x.2) = 0 := by
      intro q
      have h0 : ∀ t : ℝ, Φ (t, x.2) 1 = 0 := fun t => hΦ_van (t, x.2) 1 hx
      simp [IIIa.dfcQPrim, h0]
    dsimp only [θ0]
    unfold IIIa.dfcPotential IIIa.dfcQInt
    have hprim_x : IIIa.dfcQPrim p.c (fun y => Φ y 1) x = 0 := hprim0 x.1
    simp [hprim_x, hprim0]
  -- Flux profile `m(η) = c⁻¹ ∫_{-c/2}^{c/2} Φ(q, η)_0 dq` and its smooth bounded primitive `M`
  let m : ℝ → ℝ := fun η => p.c⁻¹ * IIIa.dfcQInt p.c (fun y => Φ y 0) η
  have hm_sm : ContDiff ℝ ∞ m :=
    contDiff_const.mul (IIIa.dfcQPrimSmooth p.c hc (fun y => Φ y 0) (hΦ.smooth 0)).2
  have hm_van : ∀ η : ℝ, R < |η| → m η = 0 := by
    intro η hη
    dsimp only [m]
    have h0 : ∀ t : ℝ, Φ (t, η) 0 = 0 := fun t => hΦ_van (t, η) 0 hη
    simp [IIIa.dfcQInt, h0]
  let M : ℝ → ℝ := fun η => ∫ t in (-(R + 1))..η, m t
  have hM_hasDeriv : ∀ η : ℝ, HasDerivAt M (m η) η := fun η =>
    (intervalIntegral.integral_hasStrictDerivAt_right
      (hm_sm.continuous.intervalIntegrable _ _)
      (hm_sm.continuous.stronglyMeasurableAtFilter _ _)
      hm_sm.continuous.continuousAt).hasDerivAt
  have hM_deriv : deriv M = m := funext fun η => (hM_hasDeriv η).deriv
  have hM_diff : Differentiable ℝ M := fun η => (hM_hasDeriv η).differentiableAt
  have hM_sm : ContDiff ℝ ∞ M := contDiff_infty_iff_deriv.2 ⟨hM_diff, hM_deriv.symm ▸ hm_sm⟩
  obtain ⟨CM0, hCM0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-(R + 1)) (R + 1)) hM_sm.continuous.continuousOn
  let CM : ℝ := max (max 0 CM0) |M (R + 1)|
  have hCM_nn : 0 ≤ CM := (le_max_left 0 CM0).trans (le_max_left _ _)
  have hM_bdd : ∀ η : ℝ, |M η| ≤ CM := by
    intro η
    by_cases hlo : η < -(R + 1)
    · have h0 : M η = 0 := by
        dsimp only [M]
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_]
        · simp
        · rw [Set.uIcc_of_ge hlo.le] at ht
          exact hm_van t (by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2])
      rw [h0, abs_zero]; exact hCM_nn
    · by_cases hhi : R + 1 < η
      · have heq : M η = M (R + 1) := by
          dsimp only [M]
          rw [← intervalIntegral.integral_add_adjacent_intervals
            (hm_sm.continuous.intervalIntegrable (-(R + 1)) (R + 1))
            (hm_sm.continuous.intervalIntegrable (R + 1) η)]
          have h0 : ∫ t in (R + 1)..η, m t = 0 := by
            rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_]
            · simp
            · rw [Set.uIcc_of_le hhi.le] at ht
              exact hm_van t (by rw [abs_of_pos (by linarith [ht.1])]; linarith [ht.1])
          rw [h0, add_zero]
        rw [heq]; exact le_max_right _ _
      · have hmem_Icc : η ∈ Icc (-(R + 1)) (R + 1) := ⟨not_lt.1 hlo, not_lt.1 hhi⟩
        exact (Real.norm_eq_abs (M η) ▸ hCM0 η hmem_Icc).trans
          ((le_max_right 0 CM0).trans (le_max_left _ _))
  -- Large-scale bump `χ_k(η) = b1(η / L_k)` with `L_k = k + R + 2`
  let b1 : ContDiffBump (0 : ℝ) :=
    { rIn := 1, rOut := 2, rIn_pos := one_pos, rIn_lt_rOut := one_lt_two }
  have hb1_sm : ContDiff ℝ ∞ b1 := b1.contDiff
  have hdb1_sm : ContDiff ℝ ∞ (deriv b1) := (contDiff_infty_iff_deriv.1 hb1_sm).2
  have hddb1_sm : ContDiff ℝ ∞ (deriv (deriv b1)) := (contDiff_infty_iff_deriv.1 hdb1_sm).2
  have hb1_ts : tsupport b1 ⊆ Icc (-2) 2 := by
    rw [b1.tsupport_eq]
    intro u hu
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at hu
    exact hu
  obtain ⟨Cb1_0, hCb1_0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-2) 2) hdb1_sm.continuous.continuousOn
  obtain ⟨Cb2_0, hCb2_0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-2) 2) hddb1_sm.continuous.continuousOn
  let Cb1 : ℝ := max 0 Cb1_0
  let Cb2 : ℝ := max 0 Cb2_0
  have hdb1_bdd : ∀ u : ℝ, |deriv b1 u| ≤ Cb1 := by
    intro u
    by_cases hu : u ∈ Icc (-2) 2
    · exact (Real.norm_eq_abs (deriv b1 u) ▸ hCb1_0 u hu).trans (le_max_right 0 Cb1_0)
    · have hnot : u ∉ tsupport (deriv b1) := fun h =>
        hu (hb1_ts (tsupport_deriv_subset h))
      rw [image_eq_zero_of_notMem_tsupport hnot, abs_zero]
      exact le_max_left 0 Cb1_0
  have hddb1_bdd : ∀ u : ℝ, |deriv (deriv b1) u| ≤ Cb2 := by
    intro u
    by_cases hu : u ∈ Icc (-2) 2
    · exact (Real.norm_eq_abs (deriv (deriv b1) u) ▸ hCb2_0 u hu).trans (le_max_right 0 Cb2_0)
    · have hnot : u ∉ tsupport (deriv (deriv b1)) := fun h =>
        hu (hb1_ts (tsupport_deriv_subset (tsupport_deriv_subset h)))
      rw [image_eq_zero_of_notMem_tsupport hnot, abs_zero]
      exact le_max_left 0 Cb2_0
  let Lk : ℕ → ℝ := fun k => (k : ℝ) + R + 2
  have hLk_pos : ∀ k : ℕ, 0 < Lk k := fun k => by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    dsimp [Lk]; linarith
  let χ : ℕ → ℝ → ℝ := fun k η => b1 (η / Lk k)
  have hχ_sm : ∀ k, ContDiff ℝ ∞ (χ k) := fun k =>
    hb1_sm.comp (contDiff_id.div_const (Lk k))
  have hχ_d1 : ∀ (k : ℕ) (η : ℝ), deriv (χ k) η = (Lk k)⁻¹ * deriv b1 (η / Lk k) := by
    intro k η
    have hd_in : HasDerivAt (fun t : ℝ => t / Lk k) (1 / Lk k) η :=
      (hasDerivAt_id η).div_const (Lk k)
    have hd_out : HasDerivAt b1 (deriv b1 (η / Lk k)) (η / Lk k) :=
      (hb1_sm.differentiable (by simp)).differentiableAt.hasDerivAt
    have hcomp := (hd_out.comp η hd_in).deriv
    dsimp only [Function.comp_def] at hcomp
    rw [show χ k = fun t => b1 (t / Lk k) from rfl, hcomp, one_div, mul_comm]
  have hχ_d2 : ∀ (k : ℕ) (η : ℝ),
      deriv (deriv (χ k)) η = ((Lk k)⁻¹) ^ 2 * deriv (deriv b1) (η / Lk k) := by
    intro k η
    have heq_d1 : deriv (χ k) = fun t => (Lk k)⁻¹ * deriv b1 (t / Lk k) :=
      funext (hχ_d1 k)
    have hd_in : HasDerivAt (fun t : ℝ => t / Lk k) (1 / Lk k) η :=
      (hasDerivAt_id η).div_const (Lk k)
    have hd_out : HasDerivAt (deriv b1) (deriv (deriv b1) (η / Lk k)) (η / Lk k) :=
      (hdb1_sm.differentiable (by simp)).differentiableAt.hasDerivAt
    have hhd : HasDerivAt (deriv (χ k))
        ((Lk k)⁻¹ * (deriv (deriv b1) (η / Lk k) * (1 / Lk k))) η := by
      rw [heq_d1]
      exact (hd_out.comp η hd_in).const_mul (Lk k)⁻¹
    rw [hhd.deriv]
    ring
  let Hk : ℕ → B0579.Plane → ℝ := fun k z => θ0 z + χ k z.2 * M z.2
  have hHk_cyl : ∀ k : ℕ, B0579.IsCylTest p.c (Hk k) := by
    intro k
    have hsm : ContDiff ℝ ∞ (Hk k) :=
      hθ0_sm.add (((hχ_sm k).comp contDiff_snd).mul (hM_sm.comp contDiff_snd))
    have hper : ∀ z : B0579.Plane, Hk k (z.1 + p.c, z.2) = Hk k z := fun z => by
      dsimp only [Hk, θ0]; rw [hθ0_per z]
    refine ⟨hsm, hper, 2 * Lk k, fun z hz => ?_⟩
    have hR_lt : R < |z.2| := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      dsimp [Lk] at hz; linarith
    have hdist : 2 ≤ dist (z.2 / Lk k) 0 := by
      rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (hLk_pos k)]
      exact (le_div_iff₀ (hLk_pos k)).2 hz.le
    have hb0 : b1 (z.2 / Lk k) = 0 := b1.zero_of_le_dist hdist
    dsimp only [Hk, χ]
    rw [hθ0_van z hR_lt, hb0, zero_mul, add_zero]
  let Φk : ℕ → B0579.Plane → Fin 2 → ℝ := fun k y =>
    ![B0579.pd 1 (Hk k) y, -B0579.pd 0 (Hk k) y]
  have hΦk_h1 : ∀ k : ℕ, IIIa.IsH1DivFreeTest p.c (Φk k) :=
    fun k => isH1DivFreeTest_skewGrad hc (hHk_cyl k)
  have heq_k : ∀ k : ℕ, ∫ s in Icc a b, sliceWeakTerm p g z₂ zq₂ zη₂ θ (Φk k) s = 0 :=
    fun k => sliceWeakEq_of_isCylTest htr hT haT hab hg_src hg_int
      hz hzq hzη hzT hz_sol hcont hθ hts (hHk_cyl k)
  -- Exact formulas for `Φk k - Φ` and its partial derivatives
  have h_diff_0 : ∀ (k : ℕ) (z : B0579.Plane), Φk k z 0 - Φ z 0 = deriv (χ k) z.2 * M z.2 := by
    intro k z
    let g_k : ℝ → ℝ := fun η => χ k η * M η
    have hgk_hd : ∀ η : ℝ, HasDerivAt g_k (deriv (χ k) η * M η + χ k η * m η) η := fun η =>
      (((hχ_sm k).differentiable (by simp)).differentiableAt.hasDerivAt).mul (hM_hasDeriv η)
    have hgk_diff : Differentiable ℝ g_k := fun η => (hgk_hd η).differentiableAt
    have hpd_gk := pd_comp_snd hgk_diff z
    have hpd1_Hk : B0579.pd 1 (Hk k) z = B0579.pd 1 θ0 z + deriv g_k z.2 := by
      have hfd_sum : HasFDerivAt (fun w : B0579.Plane => θ0 w + g_k w.2)
          (fderiv ℝ θ0 z + fderiv ℝ (fun w : B0579.Plane => g_k w.2) z) z :=
        (hθ0_sm.differentiable (by simp)).differentiableAt.hasFDerivAt.add
          (hgk_diff.comp differentiable_snd).differentiableAt.hasFDerivAt
      change B0579.pd 1 (fun w => θ0 w + g_k w.2) z = B0579.pd 1 θ0 z + deriv g_k z.2
      unfold B0579.pd
      rw [hfd_sum.fderiv, add_apply]
      exact congrArg (B0579.pd 1 θ0 z + ·) hpd_gk.2
    have hχm : χ k z.2 * m z.2 = m z.2 := by
      by_cases hzR : |z.2| ≤ R
      · have hdist : dist (z.2 / Lk k) 0 ≤ 1 := by
          rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (hLk_pos k)]
          refine (div_le_one (hLk_pos k)).2 ?_
          have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          dsimp [Lk]; linarith
        have hb1_eq : b1 (z.2 / Lk k) = 1 := b1.one_of_mem_closedBall hdist
        dsimp only [χ]
        rw [hb1_eq, one_mul]
      · rw [hm_van z.2 (not_le.1 hzR), mul_zero]
    change B0579.pd 1 (Hk k) z - Φ z 0 = deriv (χ k) z.2 * M z.2
    rw [hpd1_Hk, hθ0_pd1 z, (hgk_hd z.2).deriv, hχm]
    dsimp only [m]
    ring
  have h_eq_1 : ∀ k : ℕ, (fun z => Φk k z 1) = fun z => Φ z 1 := by
    intro k; funext z
    let g_k : ℝ → ℝ := fun η => χ k η * M η
    have hgk_diff : Differentiable ℝ g_k :=
      (((hχ_sm k).differentiable (by simp)).mul hM_diff)
    have hpd_gk := pd_comp_snd hgk_diff z
    change -B0579.pd 0 (fun w => θ0 w + g_k w.2) z = Φ z 1
    have hpd0 : B0579.pd 0 (fun w => θ0 w + g_k w.2) z = B0579.pd 0 θ0 z + 0 := by
      have hfd_sum : HasFDerivAt (fun w : B0579.Plane => θ0 w + g_k w.2)
          (fderiv ℝ θ0 z + fderiv ℝ (fun w : B0579.Plane => g_k w.2) z) z :=
        (hθ0_sm.differentiable (by simp)).differentiableAt.hasFDerivAt.add
          (hgk_diff.comp differentiable_snd).differentiableAt.hasFDerivAt
      unfold B0579.pd
      rw [hfd_sum.fderiv, add_apply]
      exact congrArg (B0579.pd 0 θ0 z + ·) hpd_gk.1
    rw [hpd0, add_zero, hθ0_pd0 z, neg_neg]
  have h_pd_diff_0 : ∀ (k : ℕ) (z : B0579.Plane),
      B0579.pd 0 (fun w => Φk k w 0) z - B0579.pd 0 (fun w => Φ w 0) z = 0 ∧
      B0579.pd 1 (fun w => Φk k w 0) z - B0579.pd 1 (fun w => Φ w 0) z =
        deriv (deriv (χ k)) z.2 * M z.2 := by
    intro k z
    let r_k : ℝ → ℝ := fun η => deriv (χ k) η * M η
    have hdχ_sm : ContDiff ℝ ∞ (deriv (χ k)) := (contDiff_infty_iff_deriv.1 (hχ_sm k)).2
    have hrk_hd : ∀ η : ℝ, HasDerivAt r_k
        (deriv (deriv (χ k)) η * M η + deriv (χ k) η * m η) η := fun η =>
      ((hdχ_sm.differentiable (by simp)).differentiableAt.hasDerivAt).mul (hM_hasDeriv η)
    have hrk_diff : Differentiable ℝ r_k := fun η => (hrk_hd η).differentiableAt
    have hsub_fn : (fun w : B0579.Plane => Φk k w 0 - Φ w 0) = fun w => r_k w.2 :=
      funext (h_diff_0 k)
    have hpd_sub : ∀ j : Fin 2,
        B0579.pd j (fun w => Φk k w 0) z - B0579.pd j (fun w => Φ w 0) z =
          B0579.pd j (fun w => r_k w.2) z := by
      intro j
      have hfd_sub : HasFDerivAt (fun w : B0579.Plane => Φk k w 0 - Φ w 0)
          (fderiv ℝ (fun w => Φk k w 0) z - fderiv ℝ (fun w => Φ w 0) z) z :=
        (((hΦk_h1 k).smooth 0).differentiable (by simp)).differentiableAt.hasFDerivAt.sub
          ((hΦ.smooth 0).differentiable (by simp)).differentiableAt.hasFDerivAt
      rw [← hsub_fn]
      symm
      unfold B0579.pd
      rw [hfd_sub.fderiv, sub_apply]
    obtain ⟨hp0, hp1⟩ := pd_comp_snd hrk_diff z
    refine ⟨(hpd_sub 0).trans hp0, ?_⟩
    rw [hpd_sub 1, hp1, (hrk_hd z.2).deriv]
    have hdχm : deriv (χ k) z.2 * m z.2 = 0 := by
      by_cases hzR : |z.2| ≤ R
      · have hlt1 : |z.2| / Lk k < 1 := by
          refine (div_lt_one (hLk_pos k)).2 ?_
          have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          dsimp [Lk]; linarith
        have hopen : IsOpen {t : ℝ | |t| / Lk k < 1} :=
          isOpen_lt (continuous_abs.div_const (Lk k)) continuous_const
        have hev : χ k =ᶠ[𝓝 z.2] fun _ : ℝ => (1 : ℝ) := by
          refine Filter.eventually_of_mem (hopen.mem_nhds hlt1) fun t ht => ?_
          have hdist : dist (t / Lk k) 0 ≤ 1 := by
            rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (hLk_pos k)]
            exact le_of_lt ht
          exact b1.one_of_mem_closedBall hdist
        rw [hev.deriv_eq, deriv_const, zero_mul]
      · rw [hm_van z.2 (not_le.1 hzR), mul_zero]
    rw [hdχm, add_zero]
  -- Bound `(eLpNorm (fun y => α k y.2) 2 (volume.restrict (B0579.cell p.c))).toReal → 0`
  let μc : Measure B0579.Plane := volume.restrict (B0579.cell p.c)
  have band_to_zero : ∀ (α : ℕ → ℝ → ℝ) (C : ℝ), 0 ≤ C →
      (∀ k, Continuous (α k)) →
      (∀ k η, 2 * Lk k < |η| → α k η = 0) →
      (∀ k η, |α k η| ≤ (Lk k)⁻¹ * C) →
      Tendsto (fun k => (eLpNorm (fun y : B0579.Plane => α k y.2) 2 μc).toReal)
        atTop (𝓝 0) := by
    intro α C hC0 hα_cont hα_van hα_bdd
    have h_le : ∀ k : ℕ, 0 ≤ (eLpNorm (fun y : B0579.Plane => α k y.2) 2 μc).toReal ∧
        (eLpNorm (fun y : B0579.Plane => α k y.2) 2 μc).toReal ≤
          (2 * Real.sqrt p.c * C) * (Real.sqrt (Lk k))⁻¹ := by
      intro k
      refine ⟨ENNReal.toReal_nonneg, ?_⟩
      let Bk : Set B0579.Plane := Ico (-(p.c / 2)) (p.c / 2) ×ˢ Icc (-(2 * Lk k)) (2 * Lk k)
      have hBk_meas : MeasurableSet Bk := measurableSet_Ico.prod measurableSet_Icc
      have hBk_sub : Bk ⊆ B0579.cell p.c := prod_mono Subset.rfl (subset_univ _)
      have hind : (fun y : B0579.Plane => α k y.2) =ᵐ[μc]
          Bk.indicator (fun y : B0579.Plane => α k y.2) := by
        filter_upwards [ae_restrict_mem (B0579.measurableSet_cell p.c)] with y hy
        by_cases hyB : y ∈ Bk
        · exact (Set.indicator_of_mem hyB (fun y : B0579.Plane => α k y.2)).symm
        · rw [Set.indicator_of_notMem hyB]
          apply hα_van k y.2
          by_contra hle
          exact hyB ⟨hy.1, abs_le.1 (not_lt.1 hle)⟩
      have hvol_Bk : (μc.restrict Bk) Set.univ = ENNReal.ofReal (4 * p.c * Lk k) := by
        dsimp only [μc]
        rw [Measure.restrict_restrict hBk_meas, Set.inter_eq_self_of_subset_left hBk_sub,
          Measure.restrict_apply_univ]
        dsimp only [Bk]
        rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc]
        have hq : p.c / 2 - -(p.c / 2) = p.c := by ring
        have hη : 2 * Lk k - -(2 * Lk k) = 4 * Lk k := by ring
        rw [hq, hη, ← ENNReal.ofReal_mul hc.le]
        congr 1; ring
      have he_eq : eLpNorm (fun y : B0579.Plane => α k y.2) 2 μc =
          eLpNorm (fun y : B0579.Plane => α k y.2) 2 (μc.restrict Bk) := by
        rw [eLpNorm_congr_ae hind, eLpNorm_indicator_eq_eLpNorm_restrict hBk_meas]
      have he_bdd : eLpNorm (fun y : B0579.Plane => α k y.2) 2 (μc.restrict Bk) ≤
          ((μc.restrict Bk) Set.univ) ^ ((2 : ℝ≥0∞).toReal)⁻¹ *
            ENNReal.ofReal ((Lk k)⁻¹ * C) := by
        refine eLpNorm_le_of_ae_bound (Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs]
        exact hα_bdd k y.2
      have h4pos : 0 ≤ 4 * p.c * Lk k := by positivity [hc.le, (hLk_pos k).le]
      have hA_nn : 0 ≤ (Lk k)⁻¹ * C := mul_nonneg (inv_nonneg.2 (hLk_pos k).le) hC0
      rw [hvol_Bk] at he_bdd
      have hpow_eq : (ENNReal.ofReal (4 * p.c * Lk k)) ^ ((2 : ℝ≥0∞).toReal)⁻¹ =
          ENNReal.ofReal (Real.sqrt (4 * p.c * Lk k)) := by
        have hinv : ((2 : ℝ≥0∞).toReal)⁻¹ = (1 / 2 : ℝ) := by norm_num
        rw [hinv, ENNReal.ofReal_rpow_of_nonneg (x := 4 * p.c * Lk k) (p := 1 / 2) h4pos (by norm_num),
          Real.sqrt_eq_rpow]
      rw [hpow_eq, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at he_bdd
      rw [he_eq]
      have htr_le := ENNReal.toReal_mono ENNReal.ofReal_ne_top he_bdd
      rw [ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) hA_nn)] at htr_le
      refine htr_le.trans (le_of_eq ?_)
      have hsq_4c : Real.sqrt (4 * p.c * Lk k) = 2 * Real.sqrt p.c * Real.sqrt (Lk k) := by
        have h1 : 4 * p.c * Lk k = 4 * (p.c * Lk k) := by ring
        rw [h1, Real.sqrt_mul (by norm_num), Real.sqrt_mul hc.le]
        norm_num
        ring
      have hsq_Lk : Real.sqrt (Lk k) * (Lk k)⁻¹ = (Real.sqrt (Lk k))⁻¹ := by
        have hpos_sq : Real.sqrt (Lk k) ≠ 0 := (Real.sqrt_pos.2 (hLk_pos k)).ne'
        have hsq : Lk k = Real.sqrt (Lk k) * Real.sqrt (Lk k) :=
          (Real.mul_self_sqrt (hLk_pos k).le).symm
        nth_rw 2 [hsq]
        rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hpos_sq, one_mul]
      calc Real.sqrt (4 * p.c * Lk k) * ((Lk k)⁻¹ * C)
          = (2 * Real.sqrt p.c * C) * (Real.sqrt (Lk k) * (Lk k)⁻¹) := by rw [hsq_4c]; ring
        _ = (2 * Real.sqrt p.c * C) * (Real.sqrt (Lk k))⁻¹ := by rw [hsq_Lk]
    have hLk_top : Tendsto Lk atTop atTop := by
      have : Lk = fun k : ℕ => (k : ℝ) + (R + 2) := by funext k; dsimp [Lk]; ring
      rw [this]
      exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have h_rhs_zero : Tendsto (fun k => (2 * Real.sqrt p.c * C) * (Real.sqrt (Lk k))⁻¹)
        atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hLk_top)).const_mul
        (2 * Real.sqrt p.c * C)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_rhs_zero
      (fun k => (h_le k).1) (fun k => (h_le k).2)
  have hlim_d0 : Tendsto (fun k =>
      (eLpNorm (fun y : B0579.Plane => deriv (χ k) y.2 * M y.2) 2 μc).toReal) atTop (𝓝 0) := by
    refine band_to_zero (fun k η => deriv (χ k) η * M η) (Cb1 * CM)
      (mul_nonneg (le_max_left 0 Cb1_0) hCM_nn)
      (fun k => (((contDiff_infty_iff_deriv.1 (hχ_sm k)).2).continuous).mul hM_sm.continuous)
      (fun k η hη => ?_) (fun k η => ?_)
    · rw [hχ_d1 k η]
      have hnot : η / Lk k ∉ tsupport (deriv b1) := by
        intro hmem
        have hI := hb1_ts (tsupport_deriv_subset hmem)
        have habs : |η / Lk k| ≤ 2 := abs_le.2 hI
        rw [abs_div, abs_of_pos (hLk_pos k), div_le_iff₀ (hLk_pos k)] at habs
        linarith
      rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero, zero_mul]
    · rw [hχ_d1 k η, abs_mul, abs_mul, abs_of_pos (inv_pos.2 (hLk_pos k)), mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (hdb1_bdd _) (hM_bdd η) (abs_nonneg _) (le_max_left 0 Cb1_0))
        (inv_nonneg.2 (hLk_pos k).le)
  have hlim_d1 : Tendsto (fun k =>
      (eLpNorm (fun y : B0579.Plane => deriv (deriv (χ k)) y.2 * M y.2) 2 μc).toReal)
      atTop (𝓝 0) := by
    refine band_to_zero (fun k η => deriv (deriv (χ k)) η * M η) (Cb2 * CM)
      (mul_nonneg (le_max_left 0 Cb2_0) hCM_nn)
      (fun k => (((contDiff_infty_iff_deriv.1
        (contDiff_infty_iff_deriv.1 (hχ_sm k)).2).2).continuous).mul hM_sm.continuous)
      (fun k η hη => ?_) (fun k η => ?_)
    · rw [hχ_d2 k η]
      have hnot : η / Lk k ∉ tsupport (deriv (deriv b1)) := by
        intro hmem
        have hI := hb1_ts (tsupport_deriv_subset (tsupport_deriv_subset hmem))
        have habs : |η / Lk k| ≤ 2 := abs_le.2 hI
        rw [abs_div, abs_of_pos (hLk_pos k), div_le_iff₀ (hLk_pos k)] at habs
        linarith
      rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero, zero_mul]
    · rw [hχ_d2 k η, abs_mul, abs_mul, abs_pow, abs_of_pos (inv_pos.2 (hLk_pos k))]
      have h1_le_Lk : 1 ≤ Lk k := by
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        dsimp [Lk]; linarith
      have hinv_le : (Lk k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1_le_Lk
      have hsq_le : ((Lk k)⁻¹) ^ 2 ≤ (Lk k)⁻¹ := by
        have hnn : 0 ≤ (Lk k)⁻¹ := inv_nonneg.2 (hLk_pos k).le
        nlinarith
      calc ((Lk k)⁻¹) ^ 2 * |deriv (deriv b1) (η / Lk k)| * |M η|
          ≤ (Lk k)⁻¹ * |deriv (deriv b1) (η / Lk k)| * |M η| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsq_le (abs_nonneg _)) (abs_nonneg _)
        _ ≤ (Lk k)⁻¹ * (Cb2 * CM) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul (hddb1_bdd _) (hM_bdd η) (abs_nonneg _) (le_max_left 0 Cb2_0))
              (inv_nonneg.2 (hLk_pos k).le)
  refine (sliceWeakEq_of_h1_tendsto htr hT haT hab hg_src hg_int hz hzq hzη hzT hcont
    hθ hΦ_h1 hΦk_h1 heq_k ?_).2
  intro i
  fin_cases i
  · refine ⟨?_, fun j => ?_⟩
    · change Tendsto (fun k => (eLpNorm (fun y => Φk k y 0 - Φ y 0) 2 μc).toReal) atTop (𝓝 0)
      have heq : (fun k => (eLpNorm (fun y => Φk k y 0 - Φ y 0) 2 μc).toReal) =
          fun k => (eLpNorm (fun y : B0579.Plane => deriv (χ k) y.2 * M y.2) 2 μc).toReal := by
        funext k; congr 1; congr 1; exact funext (h_diff_0 k)
      rwa [heq]
    · fin_cases j
      · change Tendsto (fun k => (eLpNorm (fun y =>
            B0579.pd 0 (fun w => Φk k w 0) y - B0579.pd 0 (fun w => Φ w 0) y) 2 μc).toReal)
            atTop (𝓝 0)
        have heq : (fun k => (eLpNorm (fun y =>
            B0579.pd 0 (fun w => Φk k w 0) y - B0579.pd 0 (fun w => Φ w 0) y) 2 μc).toReal) =
            fun _ => 0 := by
          funext k
          have h0 : (fun y => B0579.pd 0 (fun w => Φk k w 0) y -
              B0579.pd 0 (fun w => Φ w 0) y) = fun _ => 0 :=
            funext fun y => (h_pd_diff_0 k y).1
          simp [h0]
        rw [heq]; exact tendsto_const_nhds
      · change Tendsto (fun k => (eLpNorm (fun y =>
            B0579.pd 1 (fun w => Φk k w 0) y - B0579.pd 1 (fun w => Φ w 0) y) 2 μc).toReal)
            atTop (𝓝 0)
        have heq : (fun k => (eLpNorm (fun y =>
            B0579.pd 1 (fun w => Φk k w 0) y - B0579.pd 1 (fun w => Φ w 0) y) 2 μc).toReal) =
            fun k => (eLpNorm (fun y : B0579.Plane =>
              deriv (deriv (χ k)) y.2 * M y.2) 2 μc).toReal := by
          funext k; congr 1; congr 1; exact funext fun y => (h_pd_diff_0 k y).2
        rwa [heq]
  · refine ⟨?_, fun j => ?_⟩
    · change Tendsto (fun k => (eLpNorm (fun y => Φk k y 1 - Φ y 1) 2 μc).toReal) atTop (𝓝 0)
      have heq : (fun k => (eLpNorm (fun y => Φk k y 1 - Φ y 1) 2 μc).toReal) = fun _ => 0 := by
        funext k
        have h0 : (fun y => Φk k y 1 - Φ y 1) = fun _ => 0 := by
          funext y; rw [congrFun (h_eq_1 k) y, sub_self]
        simp [h0]
      rw [heq]; exact tendsto_const_nhds
    · change Tendsto (fun k => (eLpNorm (fun y =>
          B0579.pd j (fun w => Φk k w 1) y - B0579.pd j (fun w => Φ w 1) y) 2 μc).toReal)
          atTop (𝓝 0)
      have heq : (fun k => (eLpNorm (fun y =>
          B0579.pd j (fun w => Φk k w 1) y - B0579.pd j (fun w => Φ w 1) y) 2 μc).toReal) =
          fun _ => 0 := by
        funext k
        have h0 : (fun y => B0579.pd j (fun w => Φk k w 1) y -
            B0579.pd j (fun w => Φ w 1) y) = fun _ => 0 := by
          funext y; rw [h_eq_1 k, sub_self]
        simp [h0]
      rw [heq]; exact tendsto_const_nhds

/-- Full `IsH1DivFreeTest` slice weak equation on `Icc a b ⊂ (T, ∞)`: obtained by combining
`sliceWeakEq_of_isFlatSpatialTest` with `IIIa.divFreeCutoffDensity` and `sliceWeakEq_of_h1_tendsto`. -/
private lemma sliceWeakEq_of_isH1DivFreeTest {p : Params} {T a b : ℝ}
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train)
    (hT : 0 < T) (haT : T < a) (hab : a < b)
    {g gq gη z₂ zq₂ zη₂ : CProf}
    (hg_src : IsCylSourceH1 p.c g gq gη)
    (hg_int : (∫⁻ s in Ioi T, sliceH1Norm p.c g gq gη s) < ⊤)
    (hz : StronglyMeasurable z₂) (hzq : StronglyMeasurable zq₂) (hzη : StronglyMeasurable zη₂)
    (hzT : IsCylH1Slice p.c (fun y => z₂ (T, y)) (fun y => zq₂ (T, y)) (fun y => zη₂ (T, y)))
    (hz_sol : IsTailMeridionalSolution p T g z₂ zq₂ zη₂)
    (hcont : ∀ s : ℝ, T ≤ s →
      Tendsto (fun s' => cylSliceH1 p.c
        (fun y => z₂ (s', y) - z₂ (s, y))
        (fun y => zq₂ (s', y) - zq₂ (s, y))
        (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici T] s) (𝓝 0))
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hts : tsupport θ ⊆ Ioo a b)
    {φ : B0579.Plane → Fin 2 → ℝ} (hφ : IIIa.IsH1DivFreeTest p.c φ) :
    IntegrableOn (sliceWeakTerm p g z₂ zq₂ zη₂ θ φ) (Icc a b) ∧
      ∫ s in Icc a b, sliceWeakTerm p g z₂ zq₂ zη₂ θ φ s = 0 := by
  have hc : 0 < p.c := p.c_pos
  obtain ⟨φk, hφk_flat, hφk_lim⟩ := IIIa.divFreeCutoffDensity p.c hc φ hφ
  have hφk_h1 : ∀ k, IIIa.IsH1DivFreeTest p.c (φk k) :=
    fun k => isH1DivFreeTest_of_isFlatSpatialTest hc (hφk_flat k)
  have heq_k : ∀ k, ∫ s in Icc a b, sliceWeakTerm p g z₂ zq₂ zη₂ θ (φk k) s = 0 :=
    fun k => sliceWeakEq_of_isFlatSpatialTest htr hT haT hab hg_src hg_int
      hz hzq hzη hzT hz_sol hcont hθ hts (hφk_flat k)
  let μc : Measure B0579.Plane := volume.restrict (B0579.cell p.c)
  let S : ℕ → B0579.Plane → ℝ := fun k x => ∑ i : Fin 2,
    ((φk k x i - φ x i) ^ 2 +
      ∑ j : Fin 2, (B0579.pd j (fun y => φk k y i) x - B0579.pd j (fun y => φ y i) x) ^ 2)
  have sq_to_eLp : ∀ (d : ℕ → B0579.Plane → ℝ), (∀ k x, d k x ^ 2 ≤ S k x) →
      Tendsto (fun k => (eLpNorm (d k) 2 μc).toReal) atTop (𝓝 0) := by
    intro d hd_le
    have h_enorm : ∀ k : ℕ, eLpNorm (d k) 2 μc ≤
        (∫⁻ x in B0579.cell p.c, ENNReal.ofReal (S k x)) ^ (1 / 2 : ℝ) := by
      intro k
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      have hto : (2 : ℝ≥0∞).toReal = 2 := by norm_num
      rw [hto]
      refine ENNReal.rpow_le_rpow (lintegral_mono fun x => ?_) (by norm_num)
      have h1 : ‖d k x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (d k x ^ 2) := by
        rw [Real.enorm_eq_ofReal_abs,
          ENNReal.ofReal_rpow_of_nonneg (x := |d k x|) (p := 2) (abs_nonneg _) (by norm_num)]
        congr 1
        rw [Real.rpow_two, sq_abs]
      rw [h1]
      exact ENNReal.ofReal_le_ofReal (hd_le k x)
    have h_rpow_lim : Tendsto
        (fun k => (∫⁻ x in B0579.cell p.c, ENNReal.ofReal (S k x)) ^ (1 / 2 : ℝ))
        atTop (𝓝 0) := by
      have hcont_rpow : Continuous (fun u : ℝ≥0∞ => u ^ (1 / 2 : ℝ)) :=
        ENNReal.continuous_rpow_const
      have h0 : (0 : ℝ≥0∞) ^ (1 / 2 : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
      have hc_lim := (hcont_rpow.tendsto 0).comp hφk_lim
      rw [h0] at hc_lim
      exact hc_lim
    have h_eLp_lim : Tendsto (fun k => eLpNorm (d k) 2 μc) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_rpow_lim
        (fun _ => zero_le) h_enorm
    have hc_to := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h_eLp_lim
    rw [ENNReal.toReal_zero] at hc_to
    exact hc_to
  refine sliceWeakEq_of_h1_tendsto htr hT haT hab hg_src hg_int hz hzq hzη hzT hcont
    hθ hφ hφk_h1 heq_k fun i => ⟨sq_to_eLp _ fun k x => ?_, fun j => sq_to_eLp _ fun k x => ?_⟩
  · have h_term : (φk k x i - φ x i) ^ 2 ≤
        (φk k x i - φ x i) ^ 2 +
          ∑ j : Fin 2, (B0579.pd j (fun y => φk k y i) x - B0579.pd j (fun y => φ y i) x) ^ 2 :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact h_term.trans (Finset.single_le_sum
      (f := fun m : Fin 2 => (φk k x m - φ x m) ^ 2 +
        ∑ j : Fin 2, (B0579.pd j (fun y => φk k y m) x - B0579.pd j (fun y => φ y m) x) ^ 2)
      (fun _ _ => add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      (Finset.mem_univ i))
  · have h_term : (B0579.pd j (fun y => φk k y i) x - B0579.pd j (fun y => φ y i) x) ^ 2 ≤
        (φk k x i - φ x i) ^ 2 +
          ∑ l : Fin 2, (B0579.pd l (fun y => φk k y i) x - B0579.pd l (fun y => φ y i) x) ^ 2 :=
      (Finset.single_le_sum
        (f := fun l : Fin 2 => (B0579.pd l (fun y => φk k y i) x - B0579.pd l (fun y => φ y i) x) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ j)).trans
        (le_add_of_nonneg_left (sq_nonneg _))
    exact h_term.trans (Finset.single_le_sum
      (f := fun m : Fin 2 => (φk k x m - φ x m) ^ 2 +
        ∑ l : Fin 2, (B0579.pd l (fun y => φk k y m) x - B0579.pd l (fun y => φ y m) x) ^ 2)
      (fun _ _ => add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      (Finset.mem_univ i))


/-! ## Section 3: Homothetic Friedrichs mollifier, commutator bounds, and Gronwall closure -/

/-! ### 3A. Parametric periodized kernels `perOp` and homothetic mollifier `fhJs` -/

private def IsCellKernel (c : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ ρ ∧ tsupport ρ ⊆ Metric.closedBall (0 : ℝ × ℝ) (c / 8)

private lemma IsCellKernel.hasCompactSupport {c : ℝ} {ρ : ℝ × ℝ → ℝ} (h : IsCellKernel c ρ) :
    HasCompactSupport ρ :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ × ℝ) (c / 8))
    ((subset_tsupport ρ).trans h.2)

private lemma IsCellKernel.eq_zero_of_norm {c : ℝ} {ρ : ℝ × ℝ → ℝ} (h : IsCellKernel c ρ)
    {z : ℝ × ℝ} (hz : c / 8 < ‖z‖) : ρ z = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hle : ‖z‖ ≤ c / 8 := by simpa [Metric.mem_closedBall] using h.2 hmem
  linarith

private lemma IsCellKernel.eq_zero_of_fst {c : ℝ} {ρ : ℝ × ℝ → ℝ} (h : IsCellKernel c ρ)
    {z : ℝ × ℝ} (hz : c / 8 < |z.1|) : ρ z = 0 :=
  h.eq_zero_of_norm (hz.trans_le (by simp [Prod.norm_def]))

private lemma IsCellKernel.eq_zero_of_snd {c : ℝ} {ρ : ℝ × ℝ → ℝ} (h : IsCellKernel c ρ)
    {z : ℝ × ℝ} (hz : c / 8 < |z.2|) : ρ z = 0 :=
  h.eq_zero_of_norm (hz.trans_le (by simp [Prod.norm_def]))

private lemma IsCellKernel.bdd {c : ℝ} {ρ : ℝ × ℝ → ℝ} (h : IsCellKernel c ρ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℝ × ℝ, |ρ z| ≤ M := by
  obtain ⟨M0, hM0⟩ := h.hasCompactSupport.exists_bound_of_continuous h.1.continuous
  refine ⟨max 0 M0, le_max_left _ _, fun z => ?_⟩
  simpa [Real.norm_eq_abs] using (hM0 z).trans (le_max_right 0 M0)

private lemma IsCellKernel.pd {c : ℝ} {ρ : ℝ × ℝ → ℝ} (h : IsCellKernel c ρ) (j : Fin 2) :
    IsCellKernel c (B0579.pd j ρ) := by
  refine ⟨((contDiff_infty_iff_fderiv.1 h.1).2).clm_apply contDiff_const, ?_⟩
  refine (closure_minimal ?_ (isClosed_tsupport ρ)).trans h.2
  intro z hz
  rw [Function.mem_support] at hz
  by_contra hnot
  exact hz (by simp [B0579.pd, fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot])

private lemma IsCellKernel.comp_neg {c : ℝ} {ρ : ℝ × ℝ → ℝ} (h : IsCellKernel c ρ) :
    IsCellKernel c (fun z => ρ (-z)) := by
  refine ⟨h.1.comp contDiff_neg, ?_⟩
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro z hz
  rw [Function.mem_support] at hz
  have hmem : -z ∈ tsupport ρ := subset_tsupport ρ (Function.mem_support.2 hz)
  have hle : ‖-z‖ ≤ c / 8 := by simpa [Metric.mem_closedBall] using h.2 hmem
  simpa [Metric.mem_closedBall, norm_neg] using hle

private lemma IsCellKernel.neg {c : ℝ} {ρ : ℝ × ℝ → ℝ} (h : IsCellKernel c ρ) :
    IsCellKernel c (fun z => -ρ z) := by
  refine ⟨h.1.neg, ?_⟩
  have heq : Function.support (fun z => -ρ z) = Function.support ρ := by
    ext z; simp [Function.mem_support]
  simpa [tsupport, heq] using h.2

private def perK (c : ℝ) (ρ : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ := ρ (IIIa.lmPer c z)

private def perOp (c : ℝ) (ρ : ℝ × ℝ → ℝ) (g : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  ∫ y in B0579.cell c, (perK c ρ (x - y) : ℂ) * g y

private lemma perK_eventuallyEq {c : ℝ} (hc : 0 < c) {ρ : ℝ × ℝ → ℝ} (hρ : IsCellKernel c ρ)
    (z : ℝ × ℝ) :
    ∃ n : ℤ, IIIa.lmPer c z = (z.1 - n * c, z.2) ∧
      ∀ᶠ w in 𝓝 z, perK c ρ w = ρ (w.1 - n * c, w.2) := by
  obtain ⟨n, hn⟩ := IIIa.lmPer1_sub_self hc.ne' z.1
  have hmem := IIIa.lmPer1_mem hc z.1
  rw [hn] at hmem
  refine ⟨n, by simp [IIIa.lmPer, hn], ?_⟩
  have hnear : ∀ᶠ w : ℝ × ℝ in 𝓝 z, w.1 ∈ Ioo (z.1 - c / 8) (z.1 + c / 8) :=
    continuous_fst.tendsto z |>.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [hnear] with w hw
  by_cases h1 : w.1 - n * c < -(c / 2)
  · have hlow : -(c / 2) ≤ w.1 - ((n - 1 : ℤ) : ℝ) * c ∧ w.1 - ((n - 1 : ℤ) : ℝ) * c < c / 2 := by
      push_cast; constructor <;> nlinarith [hw.1, hw.2, hmem.1, hmem.2]
    have hper := IIIa.lmPer1_eq_sub_int hc (t := w.1) (n - 1) hlow
    have hL : perK c ρ w = 0 := by
      refine hρ.eq_zero_of_fst ?_
      show c / 8 < |IIIa.lmPer1 c w.1|
      rw [hper]; push_cast
      rw [abs_of_nonneg (by nlinarith [hw.1, hmem.1])]
      nlinarith [hw.1, hmem.1]
    have hR : ρ (w.1 - n * c, w.2) = 0 := by
      refine hρ.eq_zero_of_fst ?_
      show c / 8 < |w.1 - n * c|
      rw [abs_of_neg (by linarith)]; linarith
    rw [hL, hR]
  · push Not at h1
    by_cases h2 : w.1 - n * c < c / 2
    · have hper := IIIa.lmPer1_eq_sub_int hc (t := w.1) n ⟨h1, h2⟩
      show ρ (IIIa.lmPer1 c w.1, w.2) = _
      rw [hper]
    · push Not at h2
      have hhigh : -(c / 2) ≤ w.1 - ((n + 1 : ℤ) : ℝ) * c ∧ w.1 - ((n + 1 : ℤ) : ℝ) * c < c / 2 := by
        push_cast; constructor <;> nlinarith [hw.1, hw.2, hmem.1, hmem.2]
      have hper := IIIa.lmPer1_eq_sub_int hc (t := w.1) (n + 1) hhigh
      have hL : perK c ρ w = 0 := by
        refine hρ.eq_zero_of_fst ?_
        show c / 8 < |IIIa.lmPer1 c w.1|
        rw [hper]; push_cast
        rw [abs_of_nonpos (by nlinarith [hw.2, hmem.2])]
        nlinarith [hw.2, hmem.2]
      have hR : ρ (w.1 - n * c, w.2) = 0 := by
        refine hρ.eq_zero_of_fst ?_
        show c / 8 < |w.1 - n * c|
        rw [abs_of_nonneg (by linarith)]; linarith
      rw [hL, hR]

private lemma perK_contDiff {c : ℝ} (hc : 0 < c) {ρ : ℝ × ℝ → ℝ} (hρ : IsCellKernel c ρ) :
    ContDiff ℝ ∞ (perK c ρ) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  obtain ⟨n, -, hn⟩ := perK_eventuallyEq hc hρ z
  have hs : ContDiff ℝ ∞ (fun w : ℝ × ℝ => ρ (w.1 - n * c, w.2)) :=
    hρ.1.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
  exact hs.contDiffAt.congr_of_eventuallyEq hn

private lemma perK_pd {c : ℝ} (hc : 0 < c) {ρ : ℝ × ℝ → ℝ} (hρ : IsCellKernel c ρ)
    (j : Fin 2) (z : ℝ × ℝ) :
    B0579.pd j (perK c ρ) z = perK c (B0579.pd j ρ) z := by
  obtain ⟨n, hz, hn⟩ := perK_eventuallyEq hc hρ z
  have hn_eq : perK c ρ =ᶠ[𝓝 z] fun w : ℝ × ℝ => ρ (w.1 - n * c, w.2) := hn
  have heq : (fun w : ℝ × ℝ => ρ (w.1 - n * c, w.2)) =
      fun w => ρ (w + ((-(n * c), 0) : ℝ × ℝ)) := by
    funext w; congr 1; ext <;> simp [sub_eq_add_neg]
  have hz' : z + ((-(n * c), 0) : ℝ × ℝ) = IIIa.lmPer c z := by
    rw [hz]; ext <;> simp [sub_eq_add_neg]
  unfold B0579.pd
  rw [hn_eq.fderiv_eq, heq, fderiv_comp_add_right, hz']
  rfl

private lemma perK_periodic {c : ℝ} (hc : 0 < c) (ρ : ℝ × ℝ → ℝ) (z : ℝ × ℝ) :
    perK c ρ (z.1 + c, z.2) = perK c ρ z := by
  simp [perK, IIIa.lmPer_add c hc.ne' z]

private lemma perK_eq_zero_of_snd {c : ℝ} (hc : 0 < c) {ρ : ℝ × ℝ → ℝ} (hρ : IsCellKernel c ρ)
    {z : ℝ × ℝ} (hz : c / 3 ≤ |z.2|) : perK c ρ z = 0 :=
  hρ.eq_zero_of_snd (show c / 8 < |(IIIa.lmPer c z).2| by
    change c / 8 < |z.2|; linarith)

private lemma perK_neg_eq {c : ℝ} (hc : 0 < c) {ρ : ℝ × ℝ → ℝ}
    (h0 : ∀ u : ℝ × ℝ, c / 8 < |u.1| → ρ u = 0) (z : ℝ × ℝ) :
    perK c (fun w => ρ (-w)) (-z) = perK c ρ z := by
  obtain ⟨n, hn⟩ := IIIa.lmPer1_sub_self hc.ne' z.1
  have hmem := IIIa.lmPer1_mem hc z.1
  by_cases hend : IIIa.lmPer1 c z.1 = -(c / 2)
  · have hR : perK c ρ z = 0 := by
      apply h0
      show c / 8 < |IIIa.lmPer1 c z.1|
      rw [hend, abs_neg, abs_of_pos (by positivity)]; linarith
    have hL : perK c (fun w => ρ (-w)) (-z) = 0 := by
      apply h0
      show c / 8 < |-(IIIa.lmPer1 c (-z).1)|
      have hval : z.1 - n * c = -(c / 2) := by rw [← hn, hend]
      have hper := IIIa.lmPer1_eq_sub_int hc (t := (-z).1) (1 - n) (by
        rw [Prod.fst_neg]; push_cast; constructor <;> nlinarith)
      rw [abs_neg, hper, Prod.fst_neg]; push_cast
      have h_eq : -z.1 - (1 - (n : ℝ)) * c = -(c / 2) := by nlinarith
      rw [h_eq, abs_neg, abs_of_pos (by positivity)]; linarith
    rw [hL, hR]
  · have hgt : -(c / 2) < IIIa.lmPer1 c z.1 := lt_of_le_of_ne hmem.1 (Ne.symm hend)
    have hper := IIIa.lmPer1_eq_sub_int hc (t := (-z).1) (-n) (by
      rw [Prod.fst_neg, hn] at *; push_cast; constructor <;> nlinarith [hmem.1, hmem.2])
    have hP : IIIa.lmPer c (-z) = -IIIa.lmPer c z := by
      ext
      · show IIIa.lmPer1 c (-z).1 = -IIIa.lmPer1 c z.1
        rw [hper, hn, Prod.fst_neg]; push_cast; ring
      · rfl
    show ρ (-(IIIa.lmPer c (-z))) = ρ (IIIa.lmPer c z)
    rw [hP, neg_neg]

private lemma perK_test {c : ℝ} (hc : 0 < c) {ρ : ℝ × ℝ → ℝ} (hρ : IsCellKernel c ρ)
    (x : ℝ × ℝ) :
    B0579.IsCylTest c (fun y => perK c ρ (x - y)) ∧
      ∀ (j : Fin 2) (y : ℝ × ℝ),
        B0579.pd j (fun y => perK c ρ (x - y)) y = -perK c (B0579.pd j ρ) (x - y) := by
  refine ⟨⟨(perK_contDiff hc hρ).comp (contDiff_const.sub contDiff_id), fun y => ?_,
      ⟨|x.2| + c / 3, fun y hy => ?_⟩⟩, fun j y => ?_⟩
  · have h2 : x - (y.1 + c, y.2) = ((x - y).1 - c, (x - y).2) := by
      ext
      · simp; ring
      · simp
    simp only [perK, h2, IIIa.lmPer, IIIa.lmPer1_sub hc.ne']
  · refine perK_eq_zero_of_snd hc hρ ?_
    rw [Prod.snd_sub]
    have h1 := abs_sub_abs_le_abs_sub y.2 x.2
    rw [abs_sub_comm y.2 x.2] at h1
    linarith
  · have hd : DifferentiableAt ℝ (perK c ρ) (x - y) :=
      ((perK_contDiff hc hρ).differentiable (by simp)) _
    have h := (hd.hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)).fderiv
    have h' : fderiv ℝ (fun y => perK c ρ (x - y)) y = (fderiv ℝ (perK c ρ) (x - y)).comp
        (-ContinuousLinearMap.id ℝ (ℝ × ℝ)) := h
    unfold B0579.pd
    rw [h']
    simp only [ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.id_apply, map_neg]
    exact neg_inj.2 (perK_pd hc hρ j (x - y))

private lemma perOp_integrable {c : ℝ} (hc : 0 < c) {ρ : ℝ × ℝ → ℝ} (hρ : IsCellKernel c ρ)
    {g : ℝ × ℝ → ℂ} (hg : MemLp g 2 (volume.restrict (B0579.cell c))) (x : ℝ × ℝ) :
    Integrable (fun y => (perK c ρ (x - y) : ℂ) * g y) (volume.restrict (B0579.cell c)) := by
  obtain ⟨M, _, hM⟩ := hρ.bdd
  have h1 := IIIa.lm_memLp_band (c := c) (perK_contDiff hc hρ).continuous.measurable
    (fun z => hM _) (fun z hz => perK_eq_zero_of_snd hc hρ hz) x 2
  exact (Complex.ofRealCLM.comp_memLp' h1).integrable_mul hg

private lemma perOp_add {c : ℝ} (hc : 0 < c) {ρ : ℝ × ℝ → ℝ} (hρ : IsCellKernel c ρ)
    {f g : ℝ × ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (B0579.cell c)))
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) (x : ℝ × ℝ) :
    perOp c ρ (fun y => f y + g y) x = perOp c ρ f x + perOp c ρ g x := by
  unfold perOp
  simp_rw [mul_add]
  exact integral_add (perOp_integrable hc hρ hf x) (perOp_integrable hc hρ hg x)

private lemma perOp_sub {c : ℝ} (hc : 0 < c) {ρ : ℝ × ℝ → ℝ} (hρ : IsCellKernel c ρ)
    {f g : ℝ × ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (B0579.cell c)))
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) (x : ℝ × ℝ) :
    perOp c ρ (fun y => f y - g y) x = perOp c ρ f x - perOp c ρ g x := by
  unfold perOp
  simp_rw [mul_sub]
  exact integral_sub (perOp_integrable hc hρ hf x) (perOp_integrable hc hρ hg x)

private lemma perOp_smul (c : ℝ) (ρ : ℝ × ℝ → ℝ) (a : ℂ) (g : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    perOp c ρ (fun y => a * g y) x = a * perOp c ρ g x := by
  unfold perOp
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun y => by ring)

private lemma perOp_neg_kernel (c : ℝ) (ρ : ℝ × ℝ → ℝ) (g : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    perOp c (fun z => -ρ z) g x = -perOp c ρ g x := by
  unfold perOp perK
  rw [← integral_neg]
  exact integral_congr_ae (ae_of_all _ fun y => by push_cast; ring)

private lemma perOp_eq_convolution {c : ℝ} (hc : 0 < c) {ρ : ℝ × ℝ → ℝ} (hρ : IsCellKernel c ρ)
    (g : ℝ × ℝ → ℂ) :
    perOp c ρ g =
      MeasureTheory.convolution ρ (IIIa.lmExt c g) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext x
  rw [convolution_eq_swap]
  have hh : ∀ z : ℝ × ℝ, c / 3 ≤ |z.1| → ρ z = 0 :=
    fun _ hz => hρ.eq_zero_of_fst (by linarith)
  have h := IIIa.lm_cell_unfold hc hh (IIIa.lmExt_periodic hc g) x
  simp only [ContinuousLinearMap.lsmul_apply, Complex.real_smul]
  rw [← h]
  refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun y hy => ?_
  simp only [perK, IIIa.lmExt_of_mem hc g hy]

private lemma perOp_contDiff {c : ℝ} (hc : 0 < c) {ρ : ℝ × ℝ → ℝ} (hρ : IsCellKernel c ρ)
    {g : ℝ × ℝ → ℂ} (hg : MemLp g 2 (volume.restrict (B0579.cell c))) :
    ContDiff ℝ ∞ (perOp c ρ g) := by
  rw [perOp_eq_convolution hc hρ g]
  exact hρ.hasCompactSupport.contDiff_convolution_left _ hρ.1 (IIIa.lmExt_locallyIntegrable hc hg)

private lemma perOp_periodic {c : ℝ} (hc : 0 < c) (ρ : ℝ × ℝ → ℝ) (g : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    perOp c ρ g (x.1 + c, x.2) = perOp c ρ g x := by
  unfold perOp
  refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun y _ => ?_
  have h2 : (x.1 + c, x.2) - y = ((x - y).1 + c, (x - y).2) := by ext <;> simp; ring
  rw [h2, perK_periodic hc]

private lemma perOp_pd {c : ℝ} (hc : 0 < c) {ρ : ℝ × ℝ → ℝ} (hρ : IsCellKernel c ρ)
    {g : ℝ × ℝ → ℂ} (hg : MemLp g 2 (volume.restrict (B0579.cell c)))
    (j : Fin 2) (x : ℝ × ℝ) :
    IIIa.LMPd j (perOp c ρ g) x = perOp c (B0579.pd j ρ) g x := by
  have hd := perOp_contDiff hc hρ hg
  rw [IIIa.lmPd_eq_fderiv ((hd.differentiable (by simp)) x), perOp_eq_convolution hc hρ g]
  have hloc := IIIa.lmExt_locallyIntegrable hc hg
  have hcs := hρ.hasCompactSupport
  have hC1 : ContDiff ℝ 1 ρ := hρ.1.of_le (by simp)
  have hder := hcs.hasFDerivAt_convolution_left (𝕜 := ℝ) (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := volume) hC1 hloc x
  rw [hder.fderiv, convolution_eq_swap]
  have hexists := (hcs.fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).precompL (ℝ × ℝ))
    (hC1.continuous_fderiv (by simp)) hloc x
  rw [ContinuousLinearMap.integral_apply hexists.integrable_swap]
  trans ∫ y, (B0579.pd j ρ (x - y) : ℂ) * IIIa.lmExt c g y
  · refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp [B0579.pd, ContinuousLinearMap.precompL]
  · have hh : ∀ z : ℝ × ℝ, c / 3 ≤ |z.1| → B0579.pd j ρ z = 0 :=
      fun _ hz => (hρ.pd j).eq_zero_of_fst (by linarith)
    rw [← IIIa.lm_cell_unfold hc hh (IIIa.lmExt_periodic hc g) x]
    refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun y hy => ?_
    simp only [perK, IIIa.lmExt_of_mem hc g hy]

private lemma perOp_commute {c : ℝ} (hc : 0 < c) {ρ : ℝ × ℝ → ℝ} (hρ : IsCellKernel c ρ)
    {j : Fin 2} {g dg : ℝ × ℝ → ℂ} (hw : IIIa.HasWeakCellDerivC c j g dg) (x : ℝ × ℝ) :
    perOp c (B0579.pd j ρ) g x = perOp c ρ dg x := by
  obtain ⟨htest, hpd⟩ := perK_test hc hρ x
  have hid := hw.2 (fun y => perK c ρ (x - y)) htest
  have hL : (∫ y in B0579.cell c, g y * (B0579.pd j (fun y => perK c ρ (x - y)) y : ℂ)) =
      -perOp c (B0579.pd j ρ) g x := by
    unfold perOp
    rw [← integral_neg]
    refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun y _ => ?_
    rw [hpd j y]; push_cast; ring
  have hR : (∫ y in B0579.cell c, dg y * (perK c ρ (x - y) : ℂ)) = perOp c ρ dg x := by
    unfold perOp
    exact setIntegral_congr_fun (B0579.measurableSet_cell c) fun y _ => mul_comm _ _
  rw [hL, hR] at hid
  linear_combination -hid

private lemma perOp_memLp {c : ℝ} (hc : 0 < c) {ρ : ℝ × ℝ → ℝ} (hρ : IsCellKernel c ρ)
    {g : ℝ × ℝ → ℂ} (hg : MemLp g 2 (volume.restrict (B0579.cell c))) :
    MemLp (perOp c ρ g) 2 (volume.restrict (B0579.cell c)) := by
  obtain ⟨M, _, hM⟩ := hρ.bdd
  exact (IIIa.lm_schur_L2 hc (perK_contDiff hc hρ).continuous.measurable
    (fun z => hM _) (fun z hz => perK_eq_zero_of_snd hc hρ hz) hg
    (perOp_contDiff hc hρ hg).continuous).1

private lemma perOp_adj {c : ℝ} (hc : 0 < c) {ρ : ℝ × ℝ → ℝ} (hρ : IsCellKernel c ρ)
    {f g : ℝ × ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (B0579.cell c)))
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) :
    ∫ x in B0579.cell c, starRingEnd ℂ (perOp c ρ f x) * g x =
      ∫ y in B0579.cell c, starRingEnd ℂ (f y) * perOp c (fun w => ρ (-w)) g y := by
  set μ : Measure (ℝ × ℝ) := volume.restrict (B0579.cell c)
  obtain ⟨M, _, hM⟩ := hρ.bdd
  have hmK : Measurable (perK c ρ) := (perK_contDiff hc hρ).continuous.measurable
  have hmK' : Measurable (perK c (fun w => ρ (-w))) :=
    (perK_contDiff hc hρ.comp_neg).continuous.measurable
  have hP1 := IIIa.lm_schur_prod hc hmK (fun z => hM _)
    (fun z hz => perK_eq_zero_of_snd hc hρ hz) hf
  have hP2 := (IIIa.lm_schur_prod hc hmK' (fun z => hM _)
    (fun z hz => perK_eq_zero_of_snd hc hρ.comp_neg hz) hg).swap
  have hmeasK : AEStronglyMeasurable
      (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (perK c ρ (p.1 - p.2) : ℂ)) (μ.prod μ) :=
    (Complex.measurable_ofReal.comp
      (hmK.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable
  have hmeasF : AEStronglyMeasurable
      (fun p : (ℝ × ℝ) × (ℝ × ℝ) => starRingEnd ℂ (f p.2)) (μ.prod μ) :=
    Complex.continuous_conj.comp_aestronglyMeasurable hf.1.comp_snd
  have hmeasG : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => g p.1) (μ.prod μ) :=
    hg.1.comp_fst
  have hpair : Integrable
      (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
        (perK c ρ (p.1 - p.2) : ℂ) * (starRingEnd ℂ (f p.2) * g p.1)) (μ.prod μ) := by
    refine (hP1.add hP2).mono' (hmeasK.mul (hmeasF.mul hmeasG)) (ae_of_all _ fun p => ?_)
    have hsw : perK c (fun w => ρ (-w)) (p.2 - p.1) = perK c ρ (p.1 - p.2) := by
      have := perK_neg_eq hc (fun u hu => hρ.eq_zero_of_fst hu) (p.1 - p.2)
      simpa [neg_sub] using this
    simp only [Pi.add_apply, Function.comp_apply, Prod.fst_swap, Prod.snd_swap, hsw, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj]
    have hab : ‖f p.2‖ * ‖g p.1‖ ≤ ‖f p.2‖ ^ 2 + ‖g p.1‖ ^ 2 := by
      nlinarith [sq_nonneg (‖f p.2‖ - ‖g p.1‖)]
    calc |perK c ρ (p.1 - p.2)| * (‖f p.2‖ * ‖g p.1‖)
        ≤ |perK c ρ (p.1 - p.2)| * (‖f p.2‖ ^ 2 + ‖g p.1‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hab (abs_nonneg _)
      _ = _ := by ring
  have hL : ∀ x : ℝ × ℝ, starRingEnd ℂ (perOp c ρ f x) * g x =
      ∫ y in B0579.cell c, (perK c ρ (x - y) : ℂ) * (starRingEnd ℂ (f y) * g x) := fun x => by
    unfold perOp
    rw [← integral_conj, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [map_mul, Complex.conj_ofReal]; ring
  have hR : ∀ y : ℝ × ℝ, starRingEnd ℂ (f y) * perOp c (fun w => ρ (-w)) g y =
      ∫ x in B0579.cell c, (perK c ρ (x - y) : ℂ) * (starRingEnd ℂ (f y) * g x) := fun y => by
    unfold perOp
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    have hsw : perK c (fun w => ρ (-w)) (y - x) = perK c ρ (x - y) := by
      have := perK_neg_eq hc (fun u hu => hρ.eq_zero_of_fst hu) (x - y)
      simpa [neg_sub] using this
    rw [hsw]; ring
  simp only [hL, hR]
  exact integral_integral_swap
    (f := fun x y => (perK c ρ (x - y) : ℂ) * (starRingEnd ℂ (f y) * g x)) hpair

private lemma perOp_measurable {c : ℝ} (hc : 0 < c) {ρ : ℝ × ℝ → ℝ} (hρ : IsCellKernel c ρ)
    {f : ℝ × (ℝ × ℝ) → ℂ} (hf : Measurable f) :
    Measurable fun p : ℝ × (ℝ × ℝ) => perOp c ρ (fun y => f (p.1, y)) p.2 := by
  have hmK : Measurable (perK c ρ) := (perK_contDiff hc hρ).continuous.measurable
  have h : StronglyMeasurable (Function.uncurry fun (p : ℝ × (ℝ × ℝ)) (y : ℝ × ℝ) =>
      (perK c ρ (p.2 - y) : ℂ) * f (p.1, y)) := by
    apply Measurable.stronglyMeasurable
    refine (Complex.measurable_ofReal.comp (hmK.comp ?_)).mul (hf.comp ?_)
    · exact (measurable_snd.comp measurable_fst).sub measurable_snd
    · exact (measurable_fst.comp measurable_fst).prodMk measurable_snd
  exact (h.integral_prod_right (ν := volume.restrict (B0579.cell c))).measurable

/-- General Schur `L²(cell)` bound for any nonnegative, even, bounded kernel `w` supported in
`closedBall 0 (c / 8)` with `∫ w ≤ A`. -/
private lemma cell_even_kernel_l2_le {c A L M : ℝ} (hc : 0 < c) (hA : 0 < A) (_hL : 0 ≤ L)
    {w : ℝ × ℝ → ℝ} (hw_meas : Measurable w) (hw_nn : ∀ z, 0 ≤ w z)
    (hw_even : ∀ z, w (-z) = w z) (hw_bdd : ∀ z, w z ≤ M)
    (hw_supp : ∀ z : ℝ × ℝ, c / 8 < ‖z‖ → w z = 0)
    (hw_int : ∫ z : ℝ × ℝ, w z ≤ A)
    {F f : ℝ × ℝ → ℂ} (hF_meas : AEStronglyMeasurable F (volume.restrict (B0579.cell c)))
    (hf : MemLp f 2 (volume.restrict (B0579.cell c)))
    (hpt : ∀ x ∈ B0579.cell c,
      ‖F x‖ ≤ L * ∫ y in B0579.cell c, perK c w (x - y) * ‖f y‖) :
    MemLp F 2 (volume.restrict (B0579.cell c)) ∧
      ∫ x in B0579.cell c, ‖F x‖ ^ 2 ≤ (A * L) ^ 2 * ∫ y in B0579.cell c, ‖f y‖ ^ 2 := by
  set μ : Measure (ℝ × ℝ) := volume.restrict (B0579.cell c)
  let W : ℝ × ℝ → ℝ := perK c w
  have hM0 : 0 ≤ M := (hw_nn 0).trans (hw_bdd 0)
  have hW_meas : Measurable W := hw_meas.comp (IIIa.measurable_lmPer c)
  have hW_nn : ∀ z, 0 ≤ W z := fun _ => hw_nn _
  have hW_abs : ∀ z, |W z| ≤ M := fun z => by rw [abs_of_nonneg (hW_nn z)]; exact hw_bdd _
  have hW_band : ∀ z : ℝ × ℝ, c / 3 ≤ |z.2| → W z = 0 := fun z hz => by
    apply hw_supp
    have h1 : |z.2| ≤ ‖IIIa.lmPer c z‖ := by simp [IIIa.lmPer, Prod.norm_def]
    linarith
  have hW_swap : ∀ x y : ℝ × ℝ, W (x - y) = W (y - x) := by
    intro x y
    have h0 : ∀ u : ℝ × ℝ, c / 8 < |u.1| → w u = 0 :=
      fun u hu => hw_supp u (hu.trans_le (by simp [Prod.norm_def]))
    have hneg := perK_neg_eq hc h0 (x - y)
    simpa [W, perK, hw_even, neg_sub] using hneg.symm
  have hW_int_cell : ∀ x : ℝ × ℝ, ∫ y in B0579.cell c, W (x - y) ≤ A := by
    intro x
    have hh : ∀ z : ℝ × ℝ, c / 3 ≤ |z.1| → w z = 0 := fun z hz =>
      hw_supp z ((show c / 8 < |z.1| by linarith).trans_le (by simp [Prod.norm_def]))
    have hunf := IIIa.lm_cell_unfold hc hh (g := fun _ => (1 : ℂ)) (fun _ => rfl) x
    simp only [mul_one, integral_complex_ofReal] at hunf
    have heq_r : ∫ y in B0579.cell c, W (x - y) = ∫ y : ℝ × ℝ, w (x - y) :=
      Complex.ofReal_inj.mp hunf
    rw [heq_r, integral_sub_left_eq_self w volume x]
    exact hw_int
  have hW_int_left : ∀ y : ℝ × ℝ, ∫ x in B0579.cell c, W (x - y) ≤ A := by
    intro y
    simp_rw [hW_swap _ y]
    exact hW_int_cell y
  have hf2 : Integrable (fun y => ‖f y‖ ^ 2) μ := IIIa.lm_integrable_sq hf
  have hprod : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => W (p.1 - p.2) * ‖f p.2‖ ^ 2)
      (μ.prod μ) := by
    have hm : AEStronglyMeasurable
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) => W (p.1 - p.2) * ‖f p.2‖ ^ 2) (μ.prod μ) :=
      (hW_meas.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable.mul hf2.1.comp_snd
    rw [integrable_prod_iff' hm]
    refine ⟨ae_of_all _ fun y => ?_, ?_⟩
    · have hm1 : MemLp (fun x => W (x - y)) 1 μ := by
        simp_rw [hW_swap _ y]
        exact IIIa.lm_memLp_band hW_meas hW_abs hW_band y 1
      exact (memLp_one_iff_integrable.1 hm1).mul_const (‖f y‖ ^ 2)
    · refine (hf2.const_mul A).mono' hm.norm.prod_swap.integral_prod_right' (ae_of_all _ fun y => ?_)
      have h1 : ∀ x : ℝ × ℝ, ‖W (x - y) * ‖f y‖ ^ 2‖ = W (x - y) * ‖f y‖ ^ 2 := fun x =>
        Real.norm_of_nonneg (mul_nonneg (hW_nn _) (sq_nonneg _))
      simp only [h1]
      rw [integral_mul_const, Real.norm_of_nonneg
        (mul_nonneg (integral_nonneg fun x => hW_nn _) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (hW_int_left y) (sq_nonneg _)
  have hsq_pt : ∀ x ∈ B0579.cell c,
      ‖F x‖ ^ 2 ≤ L ^ 2 * A * ∫ y in B0579.cell c, W (x - y) * ‖f y‖ ^ 2 := by
    intro x hx
    have hKint : Integrable (fun y => W (x - y)) μ :=
      memLp_one_iff_integrable.1 (IIIa.lm_memLp_band hW_meas hW_abs hW_band x 1)
    have hKu : Integrable (fun y => W (x - y) * ‖f y‖) μ :=
      (IIIa.lm_memLp_band hW_meas hW_abs hW_band x 2).integrable_mul hf.norm
    have hKu2 : Integrable (fun y => W (x - y) * ‖f y‖ ^ 2) μ := by
      refine (hf2.const_mul M).mono' (hKint.1.mul hf2.1) (ae_of_all _ fun y => ?_)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hW_nn _),
        abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right (hw_bdd _) (sq_nonneg _)
    set I : ℝ := ∫ y, W (x - y) ∂μ
    set B : ℝ := ∫ y, W (x - y) * ‖f y‖ ∂μ
    set C : ℝ := ∫ y, W (x - y) * ‖f y‖ ^ 2 ∂μ
    have hIle : I ≤ A := hW_int_cell x
    set t : ℝ := B / A
    have hBt : B = t * A := by dsimp [t]; field_simp [hA.ne']
    have hnn : 0 ≤ ∫ y, W (x - y) * (‖f y‖ - t) ^ 2 ∂μ :=
      integral_nonneg fun y => mul_nonneg (hW_nn _) (sq_nonneg _)
    have hexp : ∫ y, W (x - y) * (‖f y‖ - t) ^ 2 ∂μ = C - 2 * t * B + t ^ 2 * I := by
      have heq : ∀ y, W (x - y) * (‖f y‖ - t) ^ 2 =
          W (x - y) * ‖f y‖ ^ 2 - 2 * t * (W (x - y) * ‖f y‖) + t ^ 2 * W (x - y) :=
        fun _ => by ring
      have hiC : Integrable (fun y => 2 * t * (W (x - y) * ‖f y‖)) μ := hKu.const_mul (2 * t)
      have hiA : Integrable (fun y => W (x - y) * ‖f y‖ ^ 2 - 2 * t * (W (x - y) * ‖f y‖)) μ :=
        hKu2.sub hiC
      have hiB : Integrable (fun y => t ^ 2 * W (x - y)) μ := hKint.const_mul (t ^ 2)
      simp only [heq]
      rw [integral_add hiA hiB, integral_sub hKu2 hiC, integral_const_mul, integral_const_mul]
    have hI_le : t ^ 2 * I ≤ t ^ 2 * A := mul_le_mul_of_nonneg_left hIle (sq_nonneg t)
    have hkey : t ^ 2 * A ≤ C := by
      rw [hexp] at hnn
      have : 2 * t * B = 2 * (t ^ 2 * A) := by rw [hBt]; ring
      linarith
    have hB2 : B ^ 2 ≤ A * C := by
      calc B ^ 2 = A * (t ^ 2 * A) := by rw [hBt]; ring
        _ ≤ A * C := mul_le_mul_of_nonneg_left hkey hA.le
    have hFx : ‖F x‖ ^ 2 ≤ (L * B) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hpt x hx) 2
    calc ‖F x‖ ^ 2 ≤ L ^ 2 * B ^ 2 := by linarith [show (L * B) ^ 2 = L ^ 2 * B ^ 2 by ring]
      _ ≤ L ^ 2 * (A * C) := mul_le_mul_of_nonneg_left hB2 (sq_nonneg L)
      _ = L ^ 2 * A * C := by ring
  have hL_prod := hprod.integral_prod_left
  have hF_sq_int : Integrable (fun x => ‖F x‖ ^ 2) μ := by
    refine (hL_prod.const_mul (L ^ 2 * A)).mono' (hF_meas.norm.pow 2) ?_
    filter_upwards [ae_restrict_mem (B0579.measurableSet_cell c)] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hsq_pt x hx
  refine ⟨(memLp_two_iff_integrable_sq_norm hF_meas).2 hF_sq_int, ?_⟩
  have h1 : ∫ x, ‖F x‖ ^ 2 ∂μ ≤
      ∫ x, (L ^ 2 * A * ∫ y, W (x - y) * ‖f y‖ ^ 2 ∂μ) ∂μ :=
    integral_mono_ae hF_sq_int (hL_prod.const_mul (L ^ 2 * A))
      ((ae_restrict_mem (B0579.measurableSet_cell c)).mono hsq_pt)
  have h2 : ∫ x, (∫ y, W (x - y) * ‖f y‖ ^ 2 ∂μ) ∂μ ≤ A * ∫ y, ‖f y‖ ^ 2 ∂μ := by
    rw [integral_integral_swap (f := fun x y => W (x - y) * ‖f y‖ ^ 2) hprod, ← integral_const_mul]
    refine integral_mono hprod.swap.integral_prod_left (hf2.const_mul A) (fun y => ?_)
    change ∫ x, W (x - y) * ‖f y‖ ^ 2 ∂μ ≤ A * ‖f y‖ ^ 2
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right (hW_int_left y) (sq_nonneg _)
  calc ∫ x, ‖F x‖ ^ 2 ∂μ
      ≤ L ^ 2 * A * ∫ x, (∫ y, W (x - y) * ‖f y‖ ^ 2 ∂μ) ∂μ := by
        rwa [integral_const_mul] at h1
    _ ≤ L ^ 2 * A * (A * ∫ y, ‖f y‖ ^ 2 ∂μ) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg (sq_nonneg L) hA.le)
    _ = (A * L) ^ 2 * ∫ y, ‖f y‖ ^ 2 ∂μ := by ring

private def fhBump0 : ContDiffBump (0 : ℝ × ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

private def fhRho0 : ℝ × ℝ → ℝ := fhBump0.normed volume

private def fhR (c : ℝ) (k : ℕ) : ℝ := min 1 (IIIa.lmDelta c) / ((k : ℝ) + 2)

private lemma fhR_pos (c : ℝ) (k : ℕ) : 0 < fhR c k := by
  unfold fhR
  exact div_pos (lt_min zero_lt_one (IIIa.lmDelta_pos c)) (by positivity)

private lemma fhR_le_half (c : ℝ) (k : ℕ) : fhR c k ≤ 1 / 2 := by
  unfold fhR
  have h1 : min 1 (IIIa.lmDelta c) ≤ 1 := min_le_left _ _
  have h2 : (2 : ℝ) ≤ (k : ℝ) + 2 := by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  calc min 1 (IIIa.lmDelta c) / ((k : ℝ) + 2) ≤ 1 / ((k : ℝ) + 2) :=
        div_le_div_of_nonneg_right h1 (by positivity)
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2

private lemma fhR_le_c_div_eight {c : ℝ} (hc : 0 < c) (k : ℕ) : fhR c k ≤ c / 8 := by
  unfold fhR
  have h1 : min 1 (IIIa.lmDelta c) ≤ c / 4 :=
    (min_le_right _ _).trans (le_of_eq (IIIa.lmDelta_eq hc))
  have h2 : (2 : ℝ) ≤ (k : ℝ) + 2 := by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  calc min 1 (IIIa.lmDelta c) / ((k : ℝ) + 2)
      ≤ (c / 4) / ((k : ℝ) + 2) := div_le_div_of_nonneg_right h1 (by positivity)
    _ ≤ (c / 4) / 2 := div_le_div_of_nonneg_left (by positivity) (by norm_num) h2
    _ = c / 8 := by ring

private lemma fhR_tendsto_zero (c : ℝ) : Tendsto (fhR c) atTop (𝓝 0) := by
  unfold fhR
  exact (tendsto_const_div_atTop_nhds_zero_nat (min 1 (IIIa.lmDelta c))).comp
    (tendsto_add_atTop_nat 2) |>.congr fun k => by simp

private def fhBump (c : ℝ) (k : ℕ) : ContDiffBump (0 : ℝ × ℝ) where
  rIn := fhR c k / 2
  rOut := fhR c k
  rIn_pos := half_pos (fhR_pos c k)
  rIn_lt_rOut := half_lt_self (fhR_pos c k)

private def fhRho (c : ℝ) (k : ℕ) : ℝ × ℝ → ℝ := (fhBump c k).normed volume

private lemma fhRho_isCellKernel {c : ℝ} (hc : 0 < c) (k : ℕ) :
    IsCellKernel c (fhRho c k) := by
  refine ⟨(fhBump c k).contDiff_normed, ?_⟩
  rw [fhRho, (fhBump c k).tsupport_normed_eq]
  exact Metric.closedBall_subset_closedBall (fhR_le_c_div_eight hc k)

private lemma pd_odd_of_even {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (heven : ∀ z, h (-z) = h z) (j : Fin 2) (z : ℝ × ℝ) :
    B0579.pd j h (-z) = -B0579.pd j h z := by
  have hd : DifferentiableAt ℝ h (-z) := (hh.differentiable (by simp)) (-z)
  have hcomp := (hd.hasFDerivAt.comp z (hasFDerivAt_id z).neg).fderiv
  have hfun : h ∘ Neg.neg = h := funext heven
  rw [hfun] at hcomp
  unfold B0579.pd
  rw [hcomp]
  simp

private lemma pd_even_of_odd {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hodd : ∀ z, h (-z) = -h z) (j : Fin 2) (z : ℝ × ℝ) :
    B0579.pd j h (-z) = B0579.pd j h z := by
  have hd : DifferentiableAt ℝ h (-z) := (hh.differentiable (by simp)) (-z)
  have hcomp := (hd.hasFDerivAt.comp z (hasFDerivAt_id z).neg).fderiv
  have hfun : h ∘ Neg.neg = -h := funext hodd
  rw [hfun, fderiv_neg] at hcomp
  have heq : fderiv ℝ h z = -(fderiv ℝ h (-z)).comp (-ContinuousLinearMap.id ℝ (ℝ × ℝ)) :=
    neg_eq_iff_eq_neg.1 hcomp
  unfold B0579.pd
  rw [heq]
  simp

private lemma fhRho_neg (c : ℝ) (k : ℕ) (z : ℝ × ℝ) : fhRho c k (-z) = fhRho c k z :=
  (fhBump c k).normed_neg z

private lemma pd_fhRho_neg (c : ℝ) (k : ℕ) (j : Fin 2) (z : ℝ × ℝ) :
    B0579.pd j (fhRho c k) (-z) = -B0579.pd j (fhRho c k) z :=
  pd_odd_of_even (fhBump c k).contDiff_normed (fhRho_neg c k) j z

private lemma pd2_fhRho_neg (c : ℝ) (k : ℕ) (l j : Fin 2) (z : ℝ × ℝ) :
    B0579.pd l (B0579.pd j (fhRho c k)) (-z) = B0579.pd l (B0579.pd j (fhRho c k)) z := by
  have hsm : ContDiff ℝ ∞ (B0579.pd j (fhRho c k)) :=
    ((contDiff_infty_iff_fderiv.1 (fhBump c k).contDiff_normed).2).clm_apply contDiff_const
  exact pd_even_of_odd hsm (pd_fhRho_neg c k j) l z

private lemma fhBump_eq_smul (c : ℝ) (k : ℕ) (z : ℝ × ℝ) :
    fhBump c k z = fhBump0 ((fhR c k)⁻¹ • z) := by
  have hR : fhR c k ≠ 0 := (fhR_pos c k).ne'
  rw [ContDiffBump.apply, ContDiffBump.apply]
  have h1 : (fhBump c k).rOut / (fhBump c k).rIn = fhBump0.rOut / fhBump0.rIn := by
    change fhR c k / (fhR c k / 2) = 1 / (1 / 2)
    field_simp [hR]
  have h2 : ((fhBump c k).rIn)⁻¹ • (z - 0) = (fhBump0.rIn)⁻¹ • ((fhR c k)⁻¹ • z - 0) := by
    change (fhR c k / 2)⁻¹ • (z - 0) = (1 / 2 : ℝ)⁻¹ • ((fhR c k)⁻¹ • z - 0)
    rw [sub_zero, sub_zero, smul_smul]
    congr 1
    field_simp [hR]
  rw [h1, h2]

private lemma fhRho_eq_smul (c : ℝ) (k : ℕ) (z : ℝ × ℝ) :
    fhRho c k z = (fhR c k)⁻¹ ^ 2 * fhRho0 ((fhR c k)⁻¹ • z) := by
  have hR : 0 < fhR c k := fhR_pos c k
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  have hint : ∫ w : ℝ × ℝ, fhBump c k w =
      (fhR c k) ^ 2 * ∫ u : ℝ × ℝ, fhBump0 u := by
    simp_rw [fhBump_eq_smul]
    rw [Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (ℝ × ℝ)) fhBump0 hR.le,
      hfin, smul_eq_mul]
  unfold fhRho fhRho0
  rw [ContDiffBump.normed_def, ContDiffBump.normed_def, fhBump_eq_smul, hint]
  have hpos0 : ∫ u : ℝ × ℝ, fhBump0 u ≠ 0 := fhBump0.integral_pos.ne'
  field_simp [hR.ne', hpos0]

private lemma pd_fhRho_eq_smul (c : ℝ) (k : ℕ) (j : Fin 2) (z : ℝ × ℝ) :
    B0579.pd j (fhRho c k) z = (fhR c k)⁻¹ ^ 3 * B0579.pd j fhRho0 ((fhR c k)⁻¹ • z) := by
  let R : ℝ := fhR c k
  have heq : fhRho c k = fun w => R⁻¹ ^ 2 * (fhRho0 ∘ HSMul.hSMul R⁻¹) w :=
    funext (fhRho_eq_smul c k)
  have hd0 : DifferentiableAt ℝ fhRho0 (R⁻¹ • z) :=
    ((fhBump0.contDiff_normed (n := (⊤ : ℕ∞))).differentiable (by simp)) (R⁻¹ • z)
  have hlin : HasFDerivAt (fun w : ℝ × ℝ => R⁻¹ • w)
      (R⁻¹ • ContinuousLinearMap.id ℝ (ℝ × ℝ)) z :=
    (R⁻¹ • ContinuousLinearMap.id ℝ (ℝ × ℝ)).hasFDerivAt
  have hder := ((hd0.hasFDerivAt.comp z hlin).const_mul (R⁻¹ ^ 2)).fderiv
  unfold B0579.pd
  rw [heq, hder]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  ring

private def fhCommConst : ℝ :=
  1 + ∑ j : Fin 2, ∫ u : ℝ × ℝ, |B0579.pd j fhRho0 u| * ‖u‖

private lemma one_le_fhCommConst : 1 ≤ fhCommConst := by
  unfold fhCommConst
  have hnn : 0 ≤ ∑ j : Fin 2, ∫ u : ℝ × ℝ, |B0579.pd j fhRho0 u| * ‖u‖ :=
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
  linarith

private lemma integral_pd_fhRho_mul_norm_le (c : ℝ) (k : ℕ) (j : Fin 2) :
    ∫ z : ℝ × ℝ, |B0579.pd j (fhRho c k) z| * ‖z‖ ≤ fhCommConst := by
  let R : ℝ := fhR c k
  have hR : 0 < R := fhR_pos c k
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  have hpt : (fun z : ℝ × ℝ => |B0579.pd j (fhRho c k) z| * ‖z‖) =
      fun z : ℝ × ℝ => R⁻¹ ^ 2 * (|B0579.pd j fhRho0 (R⁻¹ • z)| * ‖R⁻¹ • z‖) := by
    funext z
    rw [pd_fhRho_eq_smul c k j z]
    change |R⁻¹ ^ 3 * B0579.pd j fhRho0 (R⁻¹ • z)| * ‖z‖ = _
    have hz : ‖z‖ = R * ‖R⁻¹ • z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
      field_simp [hR.ne']
    rw [abs_mul, abs_of_pos (pow_pos (inv_pos.2 hR) 3), hz]
    field_simp [hR.ne']
  rw [hpt, integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (ℝ × ℝ))
      (fun u : ℝ × ℝ => |B0579.pd j fhRho0 u| * ‖u‖) hR.le,
    hfin, smul_eq_mul]
  have hcancel : R⁻¹ ^ 2 * (R ^ 2 * ∫ u : ℝ × ℝ, |B0579.pd j fhRho0 u| * ‖u‖) =
      ∫ u : ℝ × ℝ, |B0579.pd j fhRho0 u| * ‖u‖ := by
    field_simp [hR.ne']
  rw [hcancel]
  have hsingle : ∫ u : ℝ × ℝ, |B0579.pd j fhRho0 u| * ‖u‖ ≤
      ∑ l : Fin 2, ∫ u : ℝ × ℝ, |B0579.pd l fhRho0 u| * ‖u‖ :=
    Finset.single_le_sum
      (f := fun l : Fin 2 => ∫ u : ℝ × ℝ, |B0579.pd l fhRho0 u| * ‖u‖)
      (fun _ _ => integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (norm_nonneg _))
      (Finset.mem_univ j)
  unfold fhCommConst
  linarith

private def fhJs (c : ℝ) (k : ℕ) : (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ) := perOp c (fhRho c k)

private def fhJ (c : ℝ) (k : ℕ) (f : IIIa.LMSpField) : IIIa.LMSpField :=
  fun x i => fhJs c k (fun y => f y i) x

private lemma fhJs_contr {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) :
    MemLp (fhJs c k g) 2 (volume.restrict (B0579.cell c)) ∧
      ∫ x in B0579.cell c, ‖fhJs c k g x‖ ^ 2 ≤ ∫ y in B0579.cell c, ‖g y‖ ^ 2 := by
  have hK := fhRho_isCellKernel hc k
  obtain ⟨M, _, hM⟩ := hK.bdd
  have hres := cell_even_kernel_l2_le hc zero_lt_one zero_le_one
    hK.1.continuous.measurable (fun z => (fhBump c k).nonneg_normed z)
    (fhRho_neg c k) (fun z => (le_abs_self _).trans (hM z))
    (fun z hz => hK.eq_zero_of_norm hz)
    (le_of_eq (fhBump c k).integral_normed)
    (perOp_contDiff hc hK hg).continuous.aestronglyMeasurable hg ?_
  · unfold fhJs; simpa using hres
  · intro x _
    rw [one_mul]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun y _ => ?_
    have hnn : 0 ≤ perK c (fhRho c k) (x - y) := (fhBump c k).nonneg_normed _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]

private lemma fhJs_tendsto {c : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) :
    Tendsto (fun k : ℕ => ∫ x in B0579.cell c, ‖fhJs c k g x - g x‖ ^ 2) atTop (𝓝 0) := by
  have hloc := IIIa.lmExt_locallyIntegrable hc hg
  have hrOut : Tendsto (fun k : ℕ => (fhBump c k).rOut) atTop (𝓝 0) := fhR_tendsto_zero c
  have hratio : ∀ᶠ k : ℕ in atTop, (fhBump c k).rOut ≤ 2 * (fhBump c k).rIn := by
    refine Eventually.of_forall fun k => ?_
    change fhR c k ≤ 2 * (fhR c k / 2)
    linarith
  have hae0 := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := volume) hrOut hratio hloc
  have hae : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      Tendsto (fun k : ℕ => fhJs c k g x) atTop (𝓝 (g x)) := by
    filter_upwards [ae_restrict_of_ae hae0, ae_restrict_mem (B0579.measurableSet_cell c)]
      with x hx hmem
    rw [IIIa.lmExt_of_mem hc g hmem] at hx
    refine hx.congr fun k => ?_
    rw [fhJs, perOp_eq_convolution hc (fhRho_isCellKernel hc k) g]
    rfl
  exact IIIa.lm_l2_of_ae hg (fun k => (fhJs_contr hc k hg).1)
    (fun k => (fhJs_contr hc k hg).2) hae

private lemma fhJ_divFree_pt {c : ℝ} (hc : 0 < c) (k : ℕ) {f : IIIa.LMSpField}
    (hf : IIIa.LMCellL2 c f) (hdiv : IIIa.LMWeakDivFree c f) (x : ℝ × ℝ) :
    IIIa.LMPd 0 (fun y => fhJ c k f y 0) x + IIIa.LMPd 1 (fun y => fhJ c k f y 1) x = 0 := by
  have hK := fhRho_isCellKernel hc k
  obtain ⟨htest, hpd⟩ := perK_test hc hK x
  have hid := hdiv (fun y => perK c (fhRho c k) (x - y)) htest
  dsimp only [fhJ, fhJs]
  rw [perOp_pd hc hK (hf 0) 0 x, perOp_pd hc hK (hf 1) 1 x]
  unfold perOp
  have hi0 := perOp_integrable hc (hK.pd 0) (hf 0) x
  have hi1 := perOp_integrable hc (hK.pd 1) (hf 1) x
  rw [← integral_add hi0 hi1]
  have heq : (fun y : ℝ × ℝ =>
      (perK c (B0579.pd 0 (fhRho c k)) (x - y) : ℂ) * f y 0 +
      (perK c (B0579.pd 1 (fhRho c k)) (x - y) : ℂ) * f y 1) =
      fun y : ℝ × ℝ => -(f y 0 * (B0579.pd 0 (fun w => perK c (fhRho c k) (x - w)) y : ℂ) +
        f y 1 * (B0579.pd 1 (fun w => perK c (fhRho c k) (x - w)) y : ℂ)) := by
    funext y
    rw [hpd 0 y, hpd 1 y]; push_cast; ring
  rw [heq, integral_neg, hid, neg_zero]

private lemma fhJ_weakDivFree {c : ℝ} (hc : 0 < c) (k : ℕ) {f : IIIa.LMSpField}
    (hf : IIIa.LMCellL2 c f) (hdiv : IIIa.LMWeakDivFree c f) :
    IIIa.LMWeakDivFree c (fhJ c k f) := by
  intro ψ hψ
  have hK := fhRho_isCellKernel hc k
  have hd := fhJ_divFree_pt hc k hf hdiv
  have hw : ∀ j : Fin 2,
      IIIa.LMWeakPd c j (fun x => fhJ c k f x j) (IIIa.LMPd j (fun x => fhJ c k f x j)) :=
    fun j => IIIa.lmSmoothWeakPd c hc j _
      (perOp_contDiff hc hK (hf j))
      (fun x => perOp_periodic hc _ _ x)
      (perOp_memLp hc hK (hf j))
      (by
        have e : IIIa.LMPd j (fun x => fhJ c k f x j) = perOp c (B0579.pd j (fhRho c k)) (fun y => f y j) :=
          funext (perOp_pd hc hK (hf j) j)
        rw [e]; exact perOp_memLp hc (hK.pd j) (hf j))
  obtain ⟨R, hR⟩ := hψ.band
  have hi0 : ∀ j : Fin 2, Integrable (fun x => fhJ c k f x j * (B0579.pd j ψ x : ℂ))
      (volume.restrict (B0579.cell c)) := fun j => by
    obtain ⟨R', hR'⟩ := (hψ.pd j).band
    exact IIIa.lmSW_integrableOn (R := R') (perOp_memLp hc hK (hf j))
      (Complex.continuous_ofReal.comp (hψ.pd j).continuous) (fun x hx => by simp [hR' x hx])
  have hi1 : ∀ j : Fin 2,
      Integrable (fun x => IIIa.LMPd j (fun y => fhJ c k f y j) x * (ψ x : ℂ))
        (volume.restrict (B0579.cell c)) := fun j => by
    have hm : MemLp (IIIa.LMPd j (fun y => fhJ c k f y j)) 2 (volume.restrict (B0579.cell c)) := by
      have e : IIIa.LMPd j (fun x => fhJ c k f x j) = perOp c (B0579.pd j (fhRho c k)) (fun y => f y j) :=
        funext (perOp_pd hc hK (hf j) j)
      rw [e]; exact perOp_memLp hc (hK.pd j) (hf j)
    exact IIIa.lmSW_integrableOn (R := R) hm (Complex.continuous_ofReal.comp hψ.continuous)
      (fun x hx => by simp [hR x hx])
  rw [integral_add (hi0 0) (hi0 1), (hw 0).2.2 ψ hψ.smooth hψ.periodic hψ.band,
    (hw 1).2.2 ψ hψ.smooth hψ.periodic hψ.band, ← neg_add, ← integral_add (hi1 0) (hi1 1)]
  have hz : ∀ x : ℝ × ℝ, IIIa.LMPd 0 (fun y => fhJ c k f y 0) x * (ψ x : ℂ) +
      IIIa.LMPd 1 (fun y => fhJ c k f y 1) x * (ψ x : ℂ) = 0 :=
    fun x => by rw [← add_mul, hd x, zero_mul]
  simp [hz]

/-- Any componentwise `perOp c ρ f` with `IsCellKernel c ρ` whose classical divergence vanishes
has `Re` and `Im` satisfying `IIIa.IsH1DivFreeTest c`. -/
private lemma perOp_vec_isH1DivFreeTest {c : ℝ} (hc : 0 < c) {ρ : ℝ × ℝ → ℝ}
    (hρ : IsCellKernel c ρ) {f : IIIa.LMSpField} (hf : IIIa.LMCellL2 c f)
    (hdiv : ∀ x : ℝ × ℝ,
      IIIa.LMPd 0 (perOp c ρ (fun y => f y 0)) x +
      IIIa.LMPd 1 (perOp c ρ (fun y => f y 1)) x = 0) :
    let w : IIIa.LMSpField := fun x i => perOp c ρ (fun y => f y i) x
    IIIa.IsH1DivFreeTest c (fun x i => (w x i).re) ∧
      IIIa.IsH1DivFreeTest c (fun x i => (w x i).im) := by
  intro w
  have hsm : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x => w x i) := fun i => perOp_contDiff hc hρ (hf i)
  have hper : ∀ (x : ℝ × ℝ) (i : Fin 2), w (x.1 + c, x.2) i = w x i :=
    fun x i => perOp_periodic hc ρ _ x
  have hm0 : ∀ i : Fin 2, MemLp (fun x => w x i) 2 (volume.restrict (B0579.cell c)) :=
    fun i => perOp_memLp hc hρ (hf i)
  have hm1 : ∀ (i j : Fin 2),
      MemLp (IIIa.LMPd j (fun y => w y i)) 2 (volume.restrict (B0579.cell c)) := by
    intro i j
    have heq : IIIa.LMPd j (fun y => w y i) = perOp c (B0579.pd j ρ) (fun y => f y i) :=
      funext (perOp_pd hc hρ (hf i) j)
    rw [heq]
    exact perOp_memLp hc (hρ.pd j) (hf i)
  refine ⟨⟨fun i => Complex.reCLM.contDiff.comp (hsm i),
      fun x i => congrArg Complex.re (hper x i), fun x => ?_,
      fun i => (hm0 i).re, fun i j => ?_⟩,
    ⟨fun i => Complex.imCLM.contDiff.comp (hsm i),
      fun x i => congrArg Complex.im (hper x i), fun x => ?_,
      fun i => (hm0 i).im, fun i j => ?_⟩⟩
  · rw [IIIa.lmPd_re, IIIa.lmPd_re, ← Complex.add_re, hdiv x, Complex.zero_re]
  · have e : (fun x => B0579.pd j (fun y => (w y i).re) x) =
        fun x => (IIIa.LMPd j (fun y => w y i) x).re := funext (IIIa.lmPd_re j _)
    rw [e]; exact (hm1 i j).re
  · rw [IIIa.lmPd_im, IIIa.lmPd_im, ← Complex.add_im, hdiv x, Complex.zero_im]
  · have e : (fun x => B0579.pd j (fun y => (w y i).im) x) =
        fun x => (IIIa.LMPd j (fun y => w y i) x).im := funext (IIIa.lmPd_im j _)
    rw [e]; exact (hm1 i j).im

private lemma lmPd_comm_of_smooth {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (l j : Fin 2) (x : ℝ × ℝ) :
    IIIa.LMPd l (IIIa.LMPd j F) x = IIIa.LMPd j (IIIa.LMPd l F) x := by
  have hre : ContDiff ℝ ∞ (fun y => (F y).re) := Complex.reCLM.contDiff.comp hF
  have him : ContDiff ℝ ∞ (fun y => (F y).im) := Complex.imCLM.contDiff.comp hF
  unfold IIIa.LMPd
  have h1 : (fun y => (((B0579.pd j (fun w => (F w).re) y : ℝ) : ℂ) +
      Complex.I * ((B0579.pd j (fun w => (F w).im) y : ℝ) : ℂ)).re) =
      B0579.pd j (fun w => (F w).re) := by ext y; simp
  have h2 : (fun y => (((B0579.pd j (fun w => (F w).re) y : ℝ) : ℂ) +
      Complex.I * ((B0579.pd j (fun w => (F w).im) y : ℝ) : ℂ)).im) =
      B0579.pd j (fun w => (F w).im) := by ext y; simp
  have h3 : (fun y => (((B0579.pd l (fun w => (F w).re) y : ℝ) : ℂ) +
      Complex.I * ((B0579.pd l (fun w => (F w).im) y : ℝ) : ℂ)).re) =
      B0579.pd l (fun w => (F w).re) := by ext y; simp
  have h4 : (fun y => (((B0579.pd l (fun w => (F w).re) y : ℝ) : ℂ) +
      Complex.I * ((B0579.pd l (fun w => (F w).im) y : ℝ) : ℂ)).im) =
      B0579.pd l (fun w => (F w).im) := by ext y; simp
  rw [h1, h2, h3, h4, pd_comm_of_smooth hre l j x, pd_comm_of_smooth him l j x]

private lemma fhJ_isH1DivFreeTest {c : ℝ} (hc : 0 < c) (k : ℕ) {f : IIIa.LMSpField}
    (hf : IIIa.LMCellL2 c f) (hdiv : IIIa.LMWeakDivFree c f) :
    IIIa.IsH1DivFreeTest c (fun x i => (fhJ c k f x i).re) ∧
      IIIa.IsH1DivFreeTest c (fun x i => (fhJ c k f x i).im) :=
  perOp_vec_isH1DivFreeTest hc (fhRho_isCellKernel hc k) hf (fhJ_divFree_pt hc k hf hdiv)

private lemma neg_pd_fhJ_isH1DivFreeTest {c : ℝ} (hc : 0 < c) (k : ℕ) (j : Fin 2)
    {f : IIIa.LMSpField} (hf : IIIa.LMCellL2 c f) (hdiv : IIIa.LMWeakDivFree c f) :
    let w : IIIa.LMSpField :=
      fun x i => perOp c (fun z => -B0579.pd j (fhRho c k) z) (fun y => f y i) x
    IIIa.IsH1DivFreeTest c (fun x i => (w x i).re) ∧
      IIIa.IsH1DivFreeTest c (fun x i => (w x i).im) := by
  have hK := fhRho_isCellKernel hc k
  refine perOp_vec_isH1DivFreeTest hc (hK.pd j).neg hf fun x => ?_
  have hd_pt := fhJ_divFree_pt hc k hf hdiv
  have heq : ∀ i : Fin 2, perOp c (fun z => -B0579.pd j (fhRho c k) z) (fun y => f y i) =
      fun y => -IIIa.LMPd j (fun w => fhJ c k f w i) y := by
    intro i; funext y
    rw [perOp_neg_kernel, ← perOp_pd hc hK (hf i) j y]
    rfl
  have hneg_pd : ∀ (l : Fin 2) (F : ℝ × ℝ → ℂ),
      IIIa.LMPd l (fun y => -F y) x = -IIIa.LMPd l F x := by
    intro l F
    unfold IIIa.LMPd B0579.pd
    have hr : (fun y => (-F y).re) = -(fun y => (F y).re) := rfl
    have hi : (fun y => (-F y).im) = -(fun y => (F y).im) := rfl
    rw [hr, hi, fderiv_neg, fderiv_neg]
    simp; ring
  have hsm0 : ContDiff ℝ ∞ (fun w => fhJ c k f w 0) := perOp_contDiff hc hK (hf 0)
  have hsm1 : ContDiff ℝ ∞ (fun w => fhJ c k f w 1) := perOp_contDiff hc hK (hf 1)
  rw [heq 0, heq 1, hneg_pd 0, hneg_pd 1,
    lmPd_comm_of_smooth hsm0 0 j x,
    lmPd_comm_of_smooth hsm1 1 j x]
  have hsum0 : (fun y => IIIa.LMPd 0 (fun w => fhJ c k f w 0) y +
      IIIa.LMPd 1 (fun w => fhJ c k f w 1) y) = fun _ => 0 := funext hd_pt
  have hadd_pd : IIIa.LMPd j (fun y => IIIa.LMPd 0 (fun w => fhJ c k f w 0) y) x +
      IIIa.LMPd j (fun y => IIIa.LMPd 1 (fun w => fhJ c k f w 1) y) x =
      IIIa.LMPd j (fun y => IIIa.LMPd 0 (fun w => fhJ c k f w 0) y +
        IIIa.LMPd 1 (fun w => fhJ c k f w 1) y) x := by
    have hd0 : DifferentiableAt ℝ (IIIa.LMPd 0 (fun w => fhJ c k f w 0)) x := by
      have e : IIIa.LMPd 0 (fun w => fhJ c k f w 0) =
          perOp c (B0579.pd 0 (fhRho c k)) (fun y => f y 0) :=
        funext (perOp_pd hc hK (hf 0) 0)
      rw [e]; exact ((perOp_contDiff hc (hK.pd 0) (hf 0)).differentiable (by simp)) x
    have hd1 : DifferentiableAt ℝ (IIIa.LMPd 1 (fun w => fhJ c k f w 1)) x := by
      have e : IIIa.LMPd 1 (fun w => fhJ c k f w 1) =
          perOp c (B0579.pd 1 (fhRho c k)) (fun y => f y 1) :=
        funext (perOp_pd hc hK (hf 1) 1)
      rw [e]; exact ((perOp_contDiff hc (hK.pd 1) (hf 1)).differentiable (by simp)) x
    change IIIa.LMPd j (fun y => IIIa.LMPd 0 (fun w => fhJ c k f w 0) y) x +
        IIIa.LMPd j (fun y => IIIa.LMPd 1 (fun w => fhJ c k f w 1) y) x =
        IIIa.LMPd j (IIIa.LMPd 0 (fun w => fhJ c k f w 0) +
          IIIa.LMPd 1 (fun w => fhJ c k f w 1)) x
    rw [IIIa.lmPd_eq_fderiv hd0 j, IIIa.lmPd_eq_fderiv hd1 j,
      IIIa.lmPd_eq_fderiv (hd0.add hd1) j, (hd0.hasFDerivAt.add hd1.hasFDerivAt).fderiv]
    simp
  have hz_pd : IIIa.LMPd j (fun _ : ℝ × ℝ => (0 : ℂ)) x = 0 := by
    simp [IIIa.LMPd, B0579.pd]
  linear_combination -(hadd_pd.trans (by rw [hsum0, hz_pd]))

/-! ### 3B. Commutator bounds, weak Leibniz rule, and slice advection/viscous bounds -/

private lemma periodic_plane_sub_le {c L : ℝ} (hc : 0 < c) {a : ℝ × ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hper : ∀ z : ℝ × ℝ, a (z.1 + c, z.2) = a z)
    (hL : ∀ z : ℝ × ℝ, ‖fderiv ℝ a z‖ ≤ L) (x y : ℝ × ℝ) :
    |a y - a x| ≤ L * ‖IIIa.lmPer c (x - y)‖ := by
  obtain ⟨n, hn⟩ := IIIa.lmPer1_sub_self hc.ne' (x - y).1
  let y' : ℝ × ℝ := (y.1 + (n : ℝ) * c, y.2)
  have hay : a y' = a y := periodic_int_plane hper y n
  have hdiff : y' - x = -IIIa.lmPer c (x - y) := by
    ext
    · show y.1 + (n : ℝ) * c - x.1 = -IIIa.lmPer1 c (x - y).1
      rw [hn, Prod.fst_sub]; ring
    · show y.2 - x.2 = -(x - y).2
      rw [Prod.snd_sub]; ring
  have hmvt := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (ha.differentiable (by simp)) z) (fun z _ => hL z) (mem_univ x) (mem_univ y')
  rw [hay, Real.norm_eq_abs, hdiff, norm_neg] at hmvt
  exact hmvt

private lemma memLp_bdd_real_mul {c M : ℝ} (hM0 : 0 ≤ M) {a : ℝ × ℝ → ℝ}
    (ha : Continuous a) (ha_bdd : ∀ z : ℝ × ℝ, |a z| ≤ M)
    {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (B0579.cell c))) :
    MemLp (fun y => (a y : ℂ) * f y) 2 (volume.restrict (B0579.cell c)) ∧
      ∫ y in B0579.cell c, ‖(a y : ℂ) * f y‖ ^ 2 ≤
        M ^ 2 * ∫ y in B0579.cell c, ‖f y‖ ^ 2 := by
  let _ := hM0
  set μ : Measure (ℝ × ℝ) := volume.restrict (B0579.cell c)
  have hf2 : Integrable (fun y => ‖f y‖ ^ 2) μ := IIIa.lm_integrable_sq hf
  have hmeas : AEStronglyMeasurable (fun y => (a y : ℂ) * f y) μ :=
    (Complex.continuous_ofReal.comp ha).aestronglyMeasurable.mul hf.1
  have hpt : ∀ y : ℝ × ℝ, ‖(a y : ℂ) * f y‖ ^ 2 ≤ M ^ 2 * ‖f y‖ ^ 2 := by
    intro y
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (ha_bdd y) 2) (sq_nonneg _)
  have haf2 : Integrable (fun y => ‖(a y : ℂ) * f y‖ ^ 2) μ := by
    refine (hf2.const_mul (M ^ 2)).mono' (hmeas.norm.pow 2) (ae_of_all _ fun y => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpt y
  refine ⟨(memLp_two_iff_integrable_sq_norm hmeas).2 haf2, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono haf2 (hf2.const_mul (M ^ 2)) hpt

/-- Zero-order commutator bound: `‖[fhJs c k, a] f‖_{L²(cell)} ≤ fhR c k * L * ‖f‖_{L²(cell)}`. -/
private lemma fhJs_comm_zero_bound {c L Ma : ℝ} (hc : 0 < c) (hL0 : 0 ≤ L) (hMa0 : 0 ≤ Ma)
    (k : ℕ) {a : ℝ × ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hper : ∀ z : ℝ × ℝ, a (z.1 + c, z.2) = a z)
    (ha_bdd : ∀ z : ℝ × ℝ, |a z| ≤ Ma) (hL : ∀ z : ℝ × ℝ, ‖fderiv ℝ a z‖ ≤ L)
    {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (B0579.cell c))) :
    let R0 : ℝ × ℝ → ℂ := fun x =>
      fhJs c k (fun y => (a y : ℂ) * f y) x - (a x : ℂ) * fhJs c k f x
    MemLp R0 2 (volume.restrict (B0579.cell c)) ∧
      ∫ x in B0579.cell c, ‖R0 x‖ ^ 2 ≤
        (fhR c k * L) ^ 2 * ∫ y in B0579.cell c, ‖f y‖ ^ 2 := by
  intro R0
  have hK := fhRho_isCellKernel hc k
  obtain ⟨M, _, hM⟩ := hK.bdd
  have haf : MemLp (fun y => (a y : ℂ) * f y) 2 (volume.restrict (B0579.cell c)) :=
    (memLp_bdd_real_mul hMa0 ha.continuous ha_bdd hf).1
  have hR0_cont : Continuous R0 :=
    (perOp_contDiff hc hK haf).continuous.sub
      ((Complex.continuous_ofReal.comp ha.continuous).mul (perOp_contDiff hc hK hf).continuous)
  have hR_pos : 0 < fhR c k := fhR_pos c k
  have hres := cell_even_kernel_l2_le hc zero_lt_one (mul_nonneg hR_pos.le hL0)
    hK.1.continuous.measurable (fun z => (fhBump c k).nonneg_normed z)
    (fhRho_neg c k) (fun z => (le_abs_self _).trans (hM z))
    (fun z hz => hK.eq_zero_of_norm hz)
    (le_of_eq (fhBump c k).integral_normed)
    hR0_cont.aestronglyMeasurable hf ?_
  · simpa [one_mul] using hres
  · intro x _
    have heq_x : R0 x = ∫ y in B0579.cell c,
        (perK c (fhRho c k) (x - y) : ℂ) * (((a y : ℂ) - (a x : ℂ)) * f y) := by
      dsimp [R0, fhJs]
      unfold perOp
      have hi1 := perOp_integrable hc hK haf x
      have hi2 := (perOp_integrable hc hK hf x).const_mul (a x : ℂ)
      rw [← integral_const_mul, ← integral_sub hi1 hi2]
      exact setIntegral_congr_fun (B0579.measurableSet_cell c) fun y _ => by ring
    rw [heq_x]
    have hK_norm : ∀ z : ℝ × ℝ, fhRho c k z * ‖z‖ ≤ fhR c k * fhRho c k z := by
      intro z
      by_cases hz : ‖z‖ ≤ fhR c k
      · calc fhRho c k z * ‖z‖
            ≤ fhRho c k z * fhR c k :=
              mul_le_mul_of_nonneg_left hz ((fhBump c k).nonneg_normed z)
          _ = fhR c k * fhRho c k z := mul_comm _ _
      · push Not at hz
        have hz0 : fhRho c k z = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          rw [fhRho, (fhBump c k).tsupport_normed_eq]
          intro hmem
          have hle : ‖z‖ ≤ fhR c k := by simpa [fhBump, Metric.mem_closedBall] using hmem
          linarith
        simp [hz0]
    have h1 := norm_integral_le_integral_norm
      (μ := volume.restrict (B0579.cell c))
      (fun y => (perK c (fhRho c k) (x - y) : ℂ) * (((a y : ℂ) - (a x : ℂ)) * f y))
    have hKu : Integrable (fun y => perK c (fhRho c k) (x - y) * ‖f y‖)
        (volume.restrict (B0579.cell c)) :=
      (IIIa.lm_memLp_band (perK_contDiff hc hK).continuous.measurable (fun z => hM _)
        (fun z hz => perK_eq_zero_of_snd hc hK hz) x 2).integrable_mul hf.norm
    have h2 : ∫ y in B0579.cell c,
        ‖(perK c (fhRho c k) (x - y) : ℂ) * (((a y : ℂ) - (a x : ℂ)) * f y)‖ ≤
        (fhR c k * L) * ∫ y in B0579.cell c, perK c (fhRho c k) (x - y) * ‖f y‖ := by
      rw [← integral_const_mul]
      refine integral_mono
        (by
          have hsub := (perOp_integrable hc hK haf x).sub
            ((perOp_integrable hc hK hf x).const_mul (a x : ℂ))
          refine hsub.norm.congr (ae_of_all _ fun y => ?_)
          simp only [Pi.sub_apply]; congr 1; ring)
        (hKu.const_mul (fhR c k * L)) fun y => ?_
      change ‖(perK c (fhRho c k) (x - y) : ℂ) * (((a y : ℂ) - (a x : ℂ)) * f y)‖ ≤
        (fhR c k * L) * (perK c (fhRho c k) (x - y) * ‖f y‖)
      have hnn : 0 ≤ perK c (fhRho c k) (x - y) := (fhBump c k).nonneg_normed _
      have hsub_a : ‖(a y : ℂ) - (a x : ℂ)‖ = |a y - a x| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn, hsub_a]
      have hlip := periodic_plane_sub_le hc ha hper hL x y
      have hkn := hK_norm (IIIa.lmPer c (x - y))
      calc perK c (fhRho c k) (x - y) * (|a y - a x| * ‖f y‖)
          ≤ perK c (fhRho c k) (x - y) * ((L * ‖IIIa.lmPer c (x - y)‖) * ‖f y‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hlip (norm_nonneg _)) hnn
        _ = L * (fhRho c k (IIIa.lmPer c (x - y)) * ‖IIIa.lmPer c (x - y)‖) * ‖f y‖ := by
            dsimp [perK]; ring
        _ ≤ L * (fhR c k * fhRho c k (IIIa.lmPer c (x - y))) * ‖f y‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkn hL0) (norm_nonneg _)
        _ = (fhR c k * L) * (perK c (fhRho c k) (x - y) * ‖f y‖) := by
            dsimp [perK]; ring
    exact h1.trans h2

/-- Universal first-order Friedrichs commutator bound:
`‖∂_j(fhJs c k (a * f)) - a * ∂_j(fhJs c k f)‖_{L²(cell)} ≤ fhCommConst * L * ‖f‖_{L²(cell)}`. -/
private lemma fhJs_comm_pd_bound {c L Ma : ℝ} (hc : 0 < c) (hL0 : 0 ≤ L) (hMa0 : 0 ≤ Ma)
    (k : ℕ) (j : Fin 2)
    {a : ℝ × ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hper : ∀ z : ℝ × ℝ, a (z.1 + c, z.2) = a z)
    (ha_bdd : ∀ z : ℝ × ℝ, |a z| ≤ Ma) (hL : ∀ z : ℝ × ℝ, ‖fderiv ℝ a z‖ ≤ L)
    {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (B0579.cell c))) :
    let R1 : ℝ × ℝ → ℂ := fun x =>
      IIIa.LMPd j (fhJs c k (fun y => (a y : ℂ) * f y)) x -
        (a x : ℂ) * IIIa.LMPd j (fhJs c k f) x
    MemLp R1 2 (volume.restrict (B0579.cell c)) ∧
      ∫ x in B0579.cell c, ‖R1 x‖ ^ 2 ≤
        (fhCommConst * L) ^ 2 * ∫ y in B0579.cell c, ‖f y‖ ^ 2 := by
  intro R1
  have hK := fhRho_isCellKernel hc k
  have hK1 := hK.pd j
  obtain ⟨M1, hM1_nn, hM1⟩ := hK1.bdd
  have haf : MemLp (fun y => (a y : ℂ) * f y) 2 (volume.restrict (B0579.cell c)) :=
    (memLp_bdd_real_mul hMa0 ha.continuous ha_bdd hf).1
  have hR1_eq : R1 = fun x =>
      perOp c (B0579.pd j (fhRho c k)) (fun y => (a y : ℂ) * f y) x -
        (a x : ℂ) * perOp c (B0579.pd j (fhRho c k)) f x := by
    funext x
    dsimp [R1, fhJs]
    rw [perOp_pd hc hK haf j x, perOp_pd hc hK hf j x]
  have hR1_cont : Continuous R1 := by
    rw [hR1_eq]
    exact (perOp_contDiff hc hK1 haf).continuous.sub
      ((Complex.continuous_ofReal.comp ha.continuous).mul (perOp_contDiff hc hK1 hf).continuous)
  let w : ℝ × ℝ → ℝ := fun z => |B0579.pd j (fhRho c k) z| * ‖z‖
  have hw_meas : Measurable w := (hK1.1.continuous.abs.mul continuous_norm).measurable
  have hw_nn : ∀ z, 0 ≤ w z := fun _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hw_even : ∀ z, w (-z) = w z := by
    intro z; dsimp [w]; rw [pd_fhRho_neg c k j z, abs_neg, norm_neg]
  have hw_supp : ∀ z : ℝ × ℝ, c / 8 < ‖z‖ → w z = 0 := by
    intro z hz; dsimp [w]; rw [hK1.eq_zero_of_norm hz, abs_zero, zero_mul]
  have hw_bdd : ∀ z, w z ≤ M1 * (c / 8) := by
    intro z
    by_cases hz : ‖z‖ ≤ c / 8
    · exact mul_le_mul (hM1 z) hz (norm_nonneg _) hM1_nn
    · push Not at hz
      rw [hw_supp z hz]
      exact mul_nonneg hM1_nn (by positivity)
  have hCF_pos : 0 < fhCommConst := lt_of_lt_of_le zero_lt_one one_le_fhCommConst
  refine cell_even_kernel_l2_le hc hCF_pos hL0 hw_meas hw_nn hw_even hw_bdd hw_supp
    (integral_pd_fhRho_mul_norm_le c k j) hR1_cont.aestronglyMeasurable hf ?_
  intro x _
  have heq_x : R1 x = ∫ y in B0579.cell c,
      (perK c (B0579.pd j (fhRho c k)) (x - y) : ℂ) * (((a y : ℂ) - (a x : ℂ)) * f y) := by
    rw [hR1_eq]
    dsimp only [perOp]
    have hi1 := perOp_integrable hc hK1 haf x
    have hi2 := (perOp_integrable hc hK1 hf x).const_mul (a x : ℂ)
    rw [← integral_const_mul, ← integral_sub hi1 hi2]
    exact setIntegral_congr_fun (B0579.measurableSet_cell c) fun y _ => by ring
  rw [heq_x]
  have h1 := norm_integral_le_integral_norm
    (μ := volume.restrict (B0579.cell c))
    (fun y => (perK c (B0579.pd j (fhRho c k)) (x - y) : ℂ) * (((a y : ℂ) - (a x : ℂ)) * f y))
  have hW_meas : Measurable (perK c w) := hw_meas.comp (IIIa.measurable_lmPer c)
  have hW_abs : ∀ z, |perK c w z| ≤ M1 * (c / 8) := by
    intro z; dsimp only [perK]; rw [abs_of_nonneg (hw_nn _)]; exact hw_bdd _
  have hW_band : ∀ z : ℝ × ℝ, c / 3 ≤ |z.2| → perK c w z = 0 := fun z hz => by
    apply hw_supp
    have : |z.2| ≤ ‖IIIa.lmPer c z‖ := by simp [IIIa.lmPer, Prod.norm_def]
    linarith
  have hKu : Integrable (fun y => perK c w (x - y) * ‖f y‖) (volume.restrict (B0579.cell c)) :=
    (IIIa.lm_memLp_band hW_meas hW_abs hW_band x 2).integrable_mul hf.norm
  have h2 : ∫ y in B0579.cell c,
      ‖(perK c (B0579.pd j (fhRho c k)) (x - y) : ℂ) * (((a y : ℂ) - (a x : ℂ)) * f y)‖ ≤
      L * ∫ y in B0579.cell c, perK c w (x - y) * ‖f y‖ := by
    rw [← integral_const_mul]
    refine integral_mono
      (by
        have hsub := (perOp_integrable hc hK1 haf x).sub
          ((perOp_integrable hc hK1 hf x).const_mul (a x : ℂ))
        refine hsub.norm.congr (ae_of_all _ fun y => ?_)
        simp only [Pi.sub_apply]; congr 1; ring)
      (hKu.const_mul L) fun y => ?_
    change ‖(perK c (B0579.pd j (fhRho c k)) (x - y) : ℂ) * (((a y : ℂ) - (a x : ℂ)) * f y)‖ ≤
      L * (perK c w (x - y) * ‖f y‖)
    have hsub_a : ‖(a y : ℂ) - (a x : ℂ)‖ = |a y - a x| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hsub_a]
    have hlip := periodic_plane_sub_le hc ha hper hL x y
    calc |perK c (B0579.pd j (fhRho c k)) (x - y)| * (|a y - a x| * ‖f y‖)
        ≤ |perK c (B0579.pd j (fhRho c k)) (x - y)| * ((L * ‖IIIa.lmPer c (x - y)‖) * ‖f y‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hlip (norm_nonneg _)) (abs_nonneg _)
      _ = L * (perK c w (x - y) * ‖f y‖) := by
          dsimp [perK, w]; ring
  exact h1.trans h2

/-- Weak Leibniz rule on `B0579.cell c` for a smooth `c`-periodic real multiplier `b` and a
complex `L²(cell)` function `u` with weak cylinder derivative `du`. -/
private lemma hasWeakCellDerivC_smooth_mul {c : ℝ} {j : Fin 2}
    {b : ℝ × ℝ → ℝ} (hb : ContDiff ℝ ∞ b) (hb_per : ∀ z : ℝ × ℝ, b (z.1 + c, z.2) = b z)
    {u du : ℝ × ℝ → ℂ} (hu : MemLp u 2 (volume.restrict (B0579.cell c)))
    (hdu : MemLp du 2 (volume.restrict (B0579.cell c)))
    (hw : IIIa.HasWeakCellDerivC c j u du) :
    IIIa.HasWeakCellDerivC c j (fun y => (b y : ℂ) * u y)
      (fun y => (B0579.pd j b y : ℂ) * u y + (b y : ℂ) * du y) := by
  have hb_diff : Differentiable ℝ b := hb.differentiable (by simp)
  have hdb_cont : Continuous (B0579.pd j b) :=
    (((contDiff_infty_iff_fderiv.1 hb).2).clm_apply contDiff_const).continuous
  have mul_test : ∀ {ψ : ℝ × ℝ → ℝ}, B0579.IsCylTest c ψ →
      B0579.IsCylTest c (fun y => b y * ψ y) ∧
      ∀ y : ℝ × ℝ, B0579.pd j (fun w => b w * ψ w) y =
        B0579.pd j b y * ψ y + b y * B0579.pd j ψ y := by
    intro ψ hψ
    obtain ⟨R, hR⟩ := hψ.band
    refine ⟨⟨hb.mul hψ.smooth, fun y => by rw [hb_per y, hψ.periodic y],
        ⟨R, fun y hy => by simp [hR y hy]⟩⟩, fun y => ?_⟩
    have hder := ((hb_diff y).hasFDerivAt.mul
      ((hψ.smooth.differentiable (by simp)) y).hasFDerivAt).fderiv
    unfold B0579.pd
    change (fderiv ℝ (b * ψ) y) (B0579.dir j) =
      (fderiv ℝ b y) (B0579.dir j) * ψ y + b y * (fderiv ℝ ψ y) (B0579.dir j)
    rw [hder]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · obtain ⟨R, hR⟩ := hψ.band
    obtain ⟨R', hR'⟩ := (hψ.pd j).band
    have hi1 : IntegrableOn (fun x => ((b x : ℂ) * u x) * (B0579.pd j ψ x : ℂ))
        (B0579.cell c) := by
      have h := IIIa.lmSW_integrableOn (R := R') hu
        (Complex.continuous_ofReal.comp (hb.continuous.mul (hψ.pd j).continuous))
        (fun x hx => by simp [hR' x hx])
      exact h.congr_fun
        (fun x _ => by simp only [Function.comp_apply, Pi.mul_apply]; push_cast; ring)
        (B0579.measurableSet_cell c)
    have hi2a : IntegrableOn (fun x => u x * ((B0579.pd j b x * ψ x : ℝ) : ℂ)) (B0579.cell c) :=
      IIIa.lmSW_integrableOn (R := R) hu
        (Complex.continuous_ofReal.comp (hdb_cont.mul hψ.continuous))
        (fun x hx => by simp [hR x hx])
    have hi2b : IntegrableOn (fun x => du x * ((b x * ψ x : ℝ) : ℂ)) (B0579.cell c) :=
      IIIa.lmSW_integrableOn (R := R) hdu
        (Complex.continuous_ofReal.comp (hb.continuous.mul hψ.continuous))
        (fun x hx => by simp [hR x hx])
    refine ⟨hi1, (hi2a.add hi2b).congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)⟩
    simp only [Pi.add_apply]; push_cast; ring
  · obtain ⟨R, hR⟩ := hψ.band
    obtain ⟨R', hR'⟩ := (hψ.pd j).band
    obtain ⟨hbψ, hpd_bψ⟩ := mul_test hψ
    have hid := hw.2 (fun y => b y * ψ y) hbψ
    have hi_u_db : IntegrableOn (fun x => u x * ((B0579.pd j b x * ψ x : ℝ) : ℂ))
        (B0579.cell c) :=
      IIIa.lmSW_integrableOn (R := R) hu
        (Complex.continuous_ofReal.comp (hdb_cont.mul hψ.continuous))
        (fun x hx => by simp [hR x hx])
    have hi_u_dψ : IntegrableOn (fun x => u x * ((b x * B0579.pd j ψ x : ℝ) : ℂ))
        (B0579.cell c) :=
      IIIa.lmSW_integrableOn (R := R') hu
        (Complex.continuous_ofReal.comp (hb.continuous.mul (hψ.pd j).continuous))
        (fun x hx => by simp [hR' x hx])
    have hi_du_b : IntegrableOn (fun x => du x * ((b x * ψ x : ℝ) : ℂ)) (B0579.cell c) :=
      IIIa.lmSW_integrableOn (R := R) hdu
        (Complex.continuous_ofReal.comp (hb.continuous.mul hψ.continuous))
        (fun x hx => by simp [hR x hx])
    have hsplit_L : (∫ x in B0579.cell c, u x * (B0579.pd j (fun y => b y * ψ y) x : ℂ)) =
        (∫ x in B0579.cell c, u x * ((B0579.pd j b x * ψ x : ℝ) : ℂ)) +
          ∫ x in B0579.cell c, ((b x : ℂ) * u x) * (B0579.pd j ψ x : ℂ) := by
      have heq1 : (fun x => u x * (B0579.pd j (fun y => b y * ψ y) x : ℂ)) =
          fun x => u x * ((B0579.pd j b x * ψ x : ℝ) : ℂ) +
            u x * ((b x * B0579.pd j ψ x : ℝ) : ℂ) := by
        funext x; rw [hpd_bψ x]; push_cast; ring
      rw [heq1, integral_add hi_u_db hi_u_dψ]
      congr 1
      exact setIntegral_congr_fun (B0579.measurableSet_cell c) fun x _ => by push_cast; ring
    rw [hsplit_L] at hid
    have hsplit_R : (∫ x in B0579.cell c,
        ((B0579.pd j b x : ℂ) * u x + (b x : ℂ) * du x) * (ψ x : ℂ)) =
        (∫ x in B0579.cell c, u x * ((B0579.pd j b x * ψ x : ℝ) : ℂ)) +
          ∫ x in B0579.cell c, du x * ((b x * ψ x : ℝ) : ℂ) := by
      rw [← integral_add hi_u_db hi_du_b]
      exact setIntegral_congr_fun (B0579.measurableSet_cell c) fun x _ => by push_cast; ring
    rw [hsplit_R]
    linear_combination hid

private lemma trD1_smooth_per_pd_bound {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr) {s S : ℝ} (hs0 : 0 ≤ s) (hsS : s ≤ S)
    {d : B0579.Plane} (hd : ‖d‖ = 1) (j i : Fin 2) :
    ContDiff ℝ ∞ (fun y => trD1 tr d s y i) ∧
      (∀ y : B0579.Plane, trD1 tr d s (y.1 + c, y.2) i = trD1 tr d s y i) ∧
      ∀ z : B0579.Plane,
        |B0579.pd j (fun y => trD1 tr d s y i) z| ≤ (B0277.supNormD 2 (tr.v s)).toReal := by
  have hv_sm : ContDiff ℝ ∞ (tr.v s) := IIIa.AdvectionEnergyAux.contDiff_train_slice tr hs0
  have hvi_sm : ContDiff ℝ ∞ (fun y => tr.v s y i) :=
    IIIa.AdvectionEnergyAux.contDiff_train_comp tr hs0 i
  have hsm_d1 : ContDiff ℝ ∞ (fun y => trD1 tr d s y i) :=
    ((contDiff_infty_iff_fderiv.1 hvi_sm).2).clm_apply contDiff_const
  have hper_d1 : ∀ y : B0579.Plane, trD1 tr d s (y.1 + c, y.2) i = trD1 tr d s y i :=
    fun y => fderiv_periodic_plane_aux hvi_sm
      (fun w => congrArg (fun v => v i) (tr.isTrain.periodic_v s hs0 w)) d y
  refine ⟨hsm_d1, hper_d1, fun z => ?_⟩
  obtain ⟨_, _, h2⟩ := supNormD_two_bound_on tr htr (hs0.trans hsS)
  have hpt2 := (h2 s ⟨hs0, hsS⟩).2.2 z
  let L : (B0579.Plane →L[ℝ] UnforcedLeray.Train.Vec) →L[ℝ] ℝ :=
    (EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ UnforcedLeray.Train.Vec d)
  have heq_fn : (fun y => trD1 tr d s y i) = L ∘ fderiv ℝ (tr.v s) := by
    funext y
    have hv_diff : DifferentiableAt ℝ (tr.v s) y := (hv_sm.differentiable (by simp)) y
    have hcomp : fderiv ℝ (fun w => tr.v s w i) y =
        (EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).comp (fderiv ℝ (tr.v s) y) :=
      ((EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).hasFDerivAt.comp y
        hv_diff.hasFDerivAt).fderiv
    unfold trD1
    rw [hcomp]
    rfl
  have hfd_diff : DifferentiableAt ℝ (fderiv ℝ (tr.v s)) z :=
    (((contDiff_infty_iff_fderiv.1 hv_sm).2).differentiable (by simp)) z
  have hder := (L.hasFDerivAt.comp z hfd_diff.hasFDerivAt).fderiv
  have hpd_eq : B0579.pd j (fun y => trD1 tr d s y i) z =
      (iteratedFDeriv ℝ 2 (tr.v s) z ![B0579.dir j, d]) i := by
    rw [heq_fn, B0579.pd, hder, ContinuousLinearMap.comp_apply,
      iteratedFDeriv_two_apply (tr.v s) z ![B0579.dir j, d]]
    rfl
  rw [hpd_eq]
  have hdir_norm : ‖B0579.dir j‖ = 1 := by
    fin_cases j <;> simp [B0579.dir, Prod.norm_def]
  have hprod_one : ∏ k : Fin 2, ‖(![B0579.dir j, d] : Fin 2 → B0579.Plane) k‖ = 1 := by
    rw [Fin.prod_univ_two]
    simp [hdir_norm, hd]
  calc |(iteratedFDeriv ℝ 2 (tr.v s) z ![B0579.dir j, d]) i|
      ≤ ‖iteratedFDeriv ℝ 2 (tr.v s) z ![B0579.dir j, d]‖ :=
        Real.norm_eq_abs _ ▸ PiLp.norm_apply_le _ i
    _ ≤ ‖iteratedFDeriv ℝ 2 (tr.v s) z‖ *
          ∏ k : Fin 2, ‖(![B0579.dir j, d] : Fin 2 → B0579.Plane) k‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ 2 (tr.v s) z‖ := by rw [hprod_one, mul_one]
    _ ≤ (B0277.supNormD 2 (tr.v s)).toReal := hpt2

/-- Pure transport by the divergence-free train slice `tr.v s` has zero real pairing on `L²(cell)`
for any smooth `c`-periodic scalar `w ∈ H¹(cell)`. -/
private lemma transport_re_eq_zero {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr) {s : ℝ} (hs0 : 0 ≤ s)
    {w : B0579.Plane → ℂ} (hw_sm : ContDiff ℝ ∞ w)
    (hw_per : ∀ x : B0579.Plane, w (x.1 + c, x.2) = w x)
    (hw_L2 : MemLp w 2 (volume.restrict (B0579.cell c)))
    (hw_pd0 : MemLp (IIIa.LMPd 0 w) 2 (volume.restrict (B0579.cell c)))
    (hw_pd1 : MemLp (IIIa.LMPd 1 w) 2 (volume.restrict (B0579.cell c))) :
    (∫ x in B0579.cell c,
      (((tr.v s x 0 : ℝ) : ℂ) * IIIa.LMPd 0 w x +
        ((tr.v s x 1 : ℝ) : ℂ) * IIIa.LMPd 1 w x) * starRingEnd ℂ (w x)).re = 0 ∧
    (∫ x in B0579.cell c,
      starRingEnd ℂ (((tr.v s x 0 : ℝ) : ℂ) * IIIa.LMPd 0 w x +
        ((tr.v s x 1 : ℝ) : ℂ) * IIIa.LMPd 1 w x) * w x).re = 0 := by
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c :=
    IIIa.AdvectionEnergyAux.cell_eq_cylCell c
  obtain ⟨Mv, _, hMv⟩ := IIIa.AdvectionEnergyAux.trainVel_bound_le tr htr hs0
  obtain ⟨Md, _, hMd⟩ := IIIa.AdvectionEnergyAux.supNormD_one_bound_on tr htr hs0
  have hv_bdd : ∀ (l : Fin 2) (x : B0579.Plane), |tr.v s x l| ≤ Mv := by
    intro l x
    have h := hMv s le_rfl x l
    simpa [IIIa.trainVel, hs0, Real.norm_eq_abs] using h
  have hvi_diff : ∀ l : Fin 2, Differentiable ℝ (fun x => tr.v s x l) :=
    fun l => IIIa.AdvectionEnergyAux.diff_train_comp tr hs0 l
  have hvi_cont : ∀ l : Fin 2, Continuous (fun x => tr.v s x l) :=
    fun l => (hvi_diff l).continuous
  have hv_per : UnforcedLeray.Cyl.IsPeriodic c (tr.v s) := tr.isTrain.periodic_v s hs0
  have hv_div : ∀ x, UnforcedLeray.Cyl.divergence (tr.v s) x = 0 := tr.isTrain.solenoidal s hs0
  let dv00 : B0579.Plane → ℝ := UnforcedLeray.Cyl.partialQ (fun y => tr.v s y 0)
  let dv11 : B0579.Plane → ℝ := UnforcedLeray.Cyl.partialEta (fun y => tr.v s y 1)
  have h0_c1 : ContDiff ℝ (0 + 1) (fun y => tr.v s y 0) :=
    (IIIa.AdvectionEnergyAux.contDiff_train_comp tr hs0 0).of_le (by simp)
  have h1_c1 : ContDiff ℝ (0 + 1) (fun y => tr.v s y 1) :=
    (IIIa.AdvectionEnergyAux.contDiff_train_comp tr hs0 1).of_le (by simp)
  have hdv00_cont : Continuous dv00 := (UnforcedLeray.Cyl.contDiff_partialQ h0_c1).continuous
  have hdv11_cont : Continuous dv11 := (UnforcedLeray.Cyl.contDiff_partialEta h1_c1).continuous
  have hdv_bdd : ∀ x, |dv00 x| ≤ Md ∧ |dv11 x| ≤ Md := by
    intro x
    have hv_diff_all := (IIIa.AdvectionEnergyAux.contDiff_train_slice tr hs0).differentiable (by simp)
    have hL_pt : ‖fderiv ℝ (tr.v s) x‖ ≤ Md :=
      ((hMd s ⟨hs0, le_rfl⟩).2.2 x).trans (hMd s ⟨hs0, le_rfl⟩).2.1
    have hMd0 : 0 ≤ Md := (norm_nonneg _).trans hL_pt
    have hq := (IIIa.AdvectionEnergyAux.partialQ_sq_sum_le hv_diff_all x).trans
      (pow_le_pow_left₀ (norm_nonneg _) hL_pt 2)
    have hη := (IIIa.AdvectionEnergyAux.partialEta_sq_sum_le hv_diff_all x).trans
      (pow_le_pow_left₀ (norm_nonneg _) hL_pt 2)
    rw [← abs_of_nonneg hMd0]
    exact ⟨sq_le_sq.1 (by linarith [sq_nonneg (UnforcedLeray.Cyl.partialQ (fun y => tr.v s y 1) x)]),
      sq_le_sq.1 (by linarith [sq_nonneg (UnforcedLeray.Cyl.partialEta (fun y => tr.v s y 0) x)])⟩
  let wr : B0579.Plane → ℝ := fun x => (w x).re
  let wi : B0579.Plane → ℝ := fun x => (w x).im
  have hw_diff : Differentiable ℝ w := hw_sm.differentiable (by simp)
  have hwr_diff : Differentiable ℝ wr := IIIa.lmSW_re_diff hw_diff
  have hwi_diff : Differentiable ℝ wi := IIIa.lmSW_im_diff hw_diff
  have hwr_L2 : MemLp wr 2 (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    rw [← hcell]; exact hw_L2.re
  have hwi_L2 : MemLp wi 2 (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    rw [← hcell]; exact hw_L2.im
  have hwr_q : MemLp (UnforcedLeray.Cyl.partialQ wr) 2 (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    rw [← hcell]
    have e : UnforcedLeray.Cyl.partialQ wr = fun x => (IIIa.LMPd 0 w x).re := by
      funext x; rw [← IIIa.lmSW_pd0_eq hwr_diff x, IIIa.lmPd_re]
    rw [e]; exact hw_pd0.re
  have hwi_q : MemLp (UnforcedLeray.Cyl.partialQ wi) 2 (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    rw [← hcell]
    have e : UnforcedLeray.Cyl.partialQ wi = fun x => (IIIa.LMPd 0 w x).im := by
      funext x; rw [← IIIa.lmSW_pd0_eq hwi_diff x, IIIa.lmPd_im]
    rw [e]; exact hw_pd0.im
  have hwr_η : MemLp (UnforcedLeray.Cyl.partialEta wr) 2 (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    rw [← hcell]
    have e : UnforcedLeray.Cyl.partialEta wr = fun x => (IIIa.LMPd 1 w x).re := by
      funext x; rw [← IIIa.lmSW_pd1_eq hwr_diff x, IIIa.lmPd_re]
    rw [e]; exact hw_pd1.re
  have hwi_η : MemLp (UnforcedLeray.Cyl.partialEta wi) 2 (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    rw [← hcell]
    have e : UnforcedLeray.Cyl.partialEta wi = fun x => (IIIa.LMPd 1 w x).im := by
      funext x; rw [← IIIa.lmSW_pd1_eq hwi_diff x, IIIa.lmPd_im]
    rw [e]; exact hw_pd1.im
  let W₀ : B0579.Plane → ℝ := fun x => (1 / 2) * tr.v s x 0 * (wr x * wr x + wi x * wi x)
  let W₁ : B0579.Plane → ℝ := fun x => (1 / 2) * tr.v s x 1 * (wr x * wr x + wi x * wi x)
  let W₀' : B0579.Plane → ℝ := fun x =>
    (1 / 2) * dv00 x * (wr x * wr x + wi x * wi x) +
      (1 / 2) * tr.v s x 0 *
        ((UnforcedLeray.Cyl.partialQ wr x * wr x + wr x * UnforcedLeray.Cyl.partialQ wr x) +
         (UnforcedLeray.Cyl.partialQ wi x * wi x + wi x * UnforcedLeray.Cyl.partialQ wi x))
  let W₁' : B0579.Plane → ℝ := fun x =>
    (1 / 2) * dv11 x * (wr x * wr x + wi x * wi x) +
      (1 / 2) * tr.v s x 1 *
        ((UnforcedLeray.Cyl.partialEta wr x * wr x + wr x * UnforcedLeray.Cyl.partialEta wr x) +
         (UnforcedLeray.Cyl.partialEta wi x * wi x + wi x * UnforcedLeray.Cyl.partialEta wi x))
  have hdW₀ : ∀ q η, HasDerivAt (fun q' => W₀ (q', η)) (W₀' (q, η)) q := by
    intro q η
    have hv0 := UnforcedLeray.Cyl.hasDerivAt_sliceQ (hvi_diff 0) q η
    have hfr := UnforcedLeray.Cyl.hasDerivAt_sliceQ hwr_diff q η
    have hfi := UnforcedLeray.Cyl.hasDerivAt_sliceQ hwi_diff q η
    exact (hv0.const_mul (1 / 2)).mul ((hfr.mul hfr).add (hfi.mul hfi))
  have hdW₁ : ∀ q η, HasDerivAt (fun η' => W₁ (q, η')) (W₁' (q, η)) η := by
    intro q η
    have hv1 := UnforcedLeray.Cyl.hasDerivAt_sliceEta (hvi_diff 1) q η
    have hfr := UnforcedLeray.Cyl.hasDerivAt_sliceEta hwr_diff q η
    have hfi := UnforcedLeray.Cyl.hasDerivAt_sliceEta hwi_diff q η
    exact (hv1.const_mul (1 / 2)).mul ((hfr.mul hfr).add (hfi.mul hfi))
  have hW₀_per : UnforcedLeray.Cyl.IsPeriodic c W₀ := by
    intro z; dsimp [W₀, wr, wi]
    rw [hv_per z, hw_per z]
  have hcell_meas : MeasurableSet (UnforcedLeray.Cyl.cell c) :=
    measurableSet_Ico.prod MeasurableSet.univ
  have hW₁_int : IntegrableOn W₁ (UnforcedLeray.Cyl.cell c) := by
    have h1 := IIIa.AdvectionEnergyAux.integrableOn_bdd_mul_l2 (hvi_cont 1) (hv_bdd 1) hwr_L2 hwr_L2
    have h2 := IIIa.AdvectionEnergyAux.integrableOn_bdd_mul_l2 (hvi_cont 1) (hv_bdd 1) hwi_L2 hwi_L2
    exact IntegrableOn.congr_fun ((h1.add h2).const_mul (1 / 2))
      (fun x _ => by dsimp [W₁]; ring) hcell_meas
  have hW₀'_int : IntegrableOn W₀' (UnforcedLeray.Cyl.cell c) := by
    have h1 := (IIIa.AdvectionEnergyAux.integrableOn_bdd_mul_l2 hdv00_cont (fun x => (hdv_bdd x).1)
      hwr_L2 hwr_L2).add
      (IIIa.AdvectionEnergyAux.integrableOn_bdd_mul_l2 hdv00_cont (fun x => (hdv_bdd x).1)
        hwi_L2 hwi_L2)
    have h2 := (IIIa.AdvectionEnergyAux.integrableOn_bdd_mul_l2 (hvi_cont 0) (hv_bdd 0) hwr_L2 hwr_q).add
      (IIIa.AdvectionEnergyAux.integrableOn_bdd_mul_l2 (hvi_cont 0) (hv_bdd 0) hwi_L2 hwi_q)
    exact IntegrableOn.congr_fun ((h1.const_mul (1 / 2)).add h2)
      (fun x _ => by dsimp [W₀']; ring) hcell_meas
  have hW₁'_int : IntegrableOn W₁' (UnforcedLeray.Cyl.cell c) := by
    have h1 := (IIIa.AdvectionEnergyAux.integrableOn_bdd_mul_l2 hdv11_cont (fun x => (hdv_bdd x).2)
      hwr_L2 hwr_L2).add
      (IIIa.AdvectionEnergyAux.integrableOn_bdd_mul_l2 hdv11_cont (fun x => (hdv_bdd x).2)
        hwi_L2 hwi_L2)
    have h2 := (IIIa.AdvectionEnergyAux.integrableOn_bdd_mul_l2 (hvi_cont 1) (hv_bdd 1) hwr_L2 hwr_η).add
      (IIIa.AdvectionEnergyAux.integrableOn_bdd_mul_l2 (hvi_cont 1) (hv_bdd 1) hwi_L2 hwi_η)
    exact IntegrableOn.congr_fun ((h1.const_mul (1 / 2)).add h2)
      (fun x _ => by dsimp [W₁']; ring) hcell_meas
  have hI₀ : ∫ x in UnforcedLeray.Cyl.cell c, W₀' x = 0 :=
    UnforcedLeray.Cyl.integral_cell_deriv_q_of_periodic hc hW₀_per hdW₀ hW₀'_int
  have hI₁ : ∫ x in UnforcedLeray.Cyl.cell c, W₁' x = 0 :=
    UnforcedLeray.Cyl.integral_cell_deriv_eta hdW₁ hW₁_int hW₁'_int
  have hsum_zero : ∫ x in UnforcedLeray.Cyl.cell c, (W₀' x + W₁' x) = 0 := by
    rw [integral_add hW₀'_int hW₁'_int, hI₀, hI₁, add_zero]
  have hMv0 : 0 ≤ Mv := (abs_nonneg _).trans (hv_bdd 0 0)
  have hm_tr0 := (memLp_bdd_real_mul hMv0 (hvi_cont 0) (hv_bdd 0) hw_pd0).1
  have hm_tr1 := (memLp_bdd_real_mul hMv0 (hvi_cont 1) (hv_bdd 1) hw_pd1).1
  have hm_tr : MemLp (fun x => ((tr.v s x 0 : ℝ) : ℂ) * IIIa.LMPd 0 w x +
      ((tr.v s x 1 : ℝ) : ℂ) * IIIa.LMPd 1 w x) 2 (volume.restrict (B0579.cell c)) :=
    hm_tr0.add hm_tr1
  have hintA : Integrable (fun x =>
      (((tr.v s x 0 : ℝ) : ℂ) * IIIa.LMPd 0 w x +
        ((tr.v s x 1 : ℝ) : ℂ) * IIIa.LMPd 1 w x) * starRingEnd ℂ (w x))
      (volume.restrict (B0579.cell c)) :=
    hm_tr.integrable_mul hw_L2.star
  have hintB : Integrable (fun x =>
      starRingEnd ℂ (((tr.v s x 0 : ℝ) : ℂ) * IIIa.LMPd 0 w x +
        ((tr.v s x 1 : ℝ) : ℂ) * IIIa.LMPd 1 w x) * w x)
      (volume.restrict (B0579.cell c)) :=
    hm_tr.star.integrable_mul hw_L2
  have hpt_re : ∀ x : B0579.Plane,
      ((((tr.v s x 0 : ℝ) : ℂ) * IIIa.LMPd 0 w x +
        ((tr.v s x 1 : ℝ) : ℂ) * IIIa.LMPd 1 w x) * starRingEnd ℂ (w x)).re =
      W₀' x + W₁' x ∧
      (starRingEnd ℂ (((tr.v s x 0 : ℝ) : ℂ) * IIIa.LMPd 0 w x +
        ((tr.v s x 1 : ℝ) : ℂ) * IIIa.LMPd 1 w x) * w x).re =
      W₀' x + W₁' x := by
    intro x
    have hdvx : dv00 x + dv11 x = 0 := hv_div x
    have hq_re : (IIIa.LMPd 0 w x).re = UnforcedLeray.Cyl.partialQ wr x := by
      rw [← IIIa.lmPd_re, IIIa.lmSW_pd0_eq hwr_diff x]
    have hq_im : (IIIa.LMPd 0 w x).im = UnforcedLeray.Cyl.partialQ wi x := by
      rw [← IIIa.lmPd_im, IIIa.lmSW_pd0_eq hwi_diff x]
    have hη_re : (IIIa.LMPd 1 w x).re = UnforcedLeray.Cyl.partialEta wr x := by
      rw [← IIIa.lmPd_re, IIIa.lmSW_pd1_eq hwr_diff x]
    have hη_im : (IIIa.LMPd 1 w x).im = UnforcedLeray.Cyl.partialEta wi x := by
      rw [← IIIa.lmPd_im, IIIa.lmSW_pd1_eq hwi_diff x]
    constructor
    · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im,
        Complex.conj_re, Complex.conj_im, hq_re, hq_im, hη_re, hη_im]
      dsimp [W₀', W₁', wr, wi]
      linear_combination -((1 / 2) * ((w x).re * (w x).re + (w x).im * (w x).im)) * hdvx
    · simp only [map_add, map_mul, Complex.conj_ofReal, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
        hq_re, hq_im, hη_re, hη_im]
      dsimp [W₀', W₁', wr, wi]
      linear_combination -((1 / 2) * ((w x).re * (w x).re + (w x).im * (w x).im)) * hdvx
  refine ⟨?_, ?_⟩
  · have hreA : ∫ x in B0579.cell c,
        ((((tr.v s x 0 : ℝ) : ℂ) * IIIa.LMPd 0 w x +
          ((tr.v s x 1 : ℝ) : ℂ) * IIIa.LMPd 1 w x) * starRingEnd ℂ (w x)).re =
        (∫ x in B0579.cell c,
          (((tr.v s x 0 : ℝ) : ℂ) * IIIa.LMPd 0 w x +
            ((tr.v s x 1 : ℝ) : ℂ) * IIIa.LMPd 1 w x) * starRingEnd ℂ (w x)).re := by
      simpa using integral_re hintA
    rw [← hreA]
    simp_rw [(hpt_re _).1, hcell]
    exact hsum_zero
  · have hreB : ∫ x in B0579.cell c,
        (starRingEnd ℂ (((tr.v s x 0 : ℝ) : ℂ) * IIIa.LMPd 0 w x +
          ((tr.v s x 1 : ℝ) : ℂ) * IIIa.LMPd 1 w x) * w x).re =
        (∫ x in B0579.cell c,
          starRingEnd ℂ (((tr.v s x 0 : ℝ) : ℂ) * IIIa.LMPd 0 w x +
            ((tr.v s x 1 : ℝ) : ℂ) * IIIa.LMPd 1 w x) * w x).re := by
      simpa using integral_re hintB
    rw [← hreB]
    simp_rw [(hpt_re _).2, hcell]
    exact hsum_zero

private lemma viscous_re_nonpos {c : ℝ} (hc : 0 < c) (l : Fin 2)
    {w : B0579.Plane → ℂ} (hw_sm : ContDiff ℝ ∞ w)
    (hw_per : ∀ x : B0579.Plane, w (x.1 + c, x.2) = w x)
    (hw_L2 : MemLp w 2 (volume.restrict (B0579.cell c)))
    (hw_pd : MemLp (IIIa.LMPd l w) 2 (volume.restrict (B0579.cell c)))
    (hw_pd2 : MemLp (IIIa.LMPd l (IIIa.LMPd l w)) 2 (volume.restrict (B0579.cell c))) :
    (∫ x in B0579.cell c,
      starRingEnd ℂ (IIIa.LMPd l (IIIa.LMPd l w) x) * w x).re ≤ 0 := by
  have hpd_sm : ContDiff ℝ ∞ (IIIa.LMPd l w) := by
    unfold IIIa.LMPd
    have hre : ContDiff ℝ ∞ (B0579.pd l (fun y => (w y).re)) :=
      ((contDiff_infty_iff_fderiv.1 (Complex.reCLM.contDiff.comp hw_sm)).2).clm_apply contDiff_const
    have him : ContDiff ℝ ∞ (B0579.pd l (fun y => (w y).im)) :=
      ((contDiff_infty_iff_fderiv.1 (Complex.imCLM.contDiff.comp hw_sm)).2).clm_apply contDiff_const
    exact (Complex.ofRealCLM.contDiff.comp hre).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp him))
  have hpd_per : ∀ x : B0579.Plane, IIIa.LMPd l w (x.1 + c, x.2) = IIIa.LMPd l w x := by
    intro x
    have h1 : B0579.pd l (fun y => (w y).re) (x.1 + c, x.2) = B0579.pd l (fun y => (w y).re) x :=
      fderiv_periodic_plane_aux (Complex.reCLM.contDiff.comp hw_sm)
        (fun y => congrArg Complex.re (hw_per y)) (B0579.dir l) x
    have h2 : B0579.pd l (fun y => (w y).im) (x.1 + c, x.2) = B0579.pd l (fun y => (w y).im) x :=
      fderiv_periodic_plane_aux (Complex.imCLM.contDiff.comp hw_sm)
        (fun y => congrArg Complex.im (hw_per y)) (B0579.dir l) x
    unfold IIIa.LMPd
    rw [h1, h2]
  have hibp := IIIa.lmSmoothIBP c hc l (IIIa.LMPd l w) w hpd_sm hw_sm hpd_per hw_per
    hw_pd hw_L2 hw_pd2 hw_pd
  have heq : ∫ x in B0579.cell c, starRingEnd ℂ (IIIa.LMPd l (IIIa.LMPd l w) x) * w x =
      -∫ x in B0579.cell c, starRingEnd ℂ (IIIa.LMPd l w x) * IIIa.LMPd l w x := by
    linear_combination hibp
  have hint_sq : Integrable (fun x => starRingEnd ℂ (IIIa.LMPd l w x) * IIIa.LMPd l w x)
      (volume.restrict (B0579.cell c)) := hw_pd.star.integrable_mul hw_pd
  have hre : ∫ x in B0579.cell c, (starRingEnd ℂ (IIIa.LMPd l w x) * IIIa.LMPd l w x).re =
      (∫ x in B0579.cell c, starRingEnd ℂ (IIIa.LMPd l w x) * IIIa.LMPd l w x).re := by
    simpa using integral_re hint_sq
  rw [heq, Complex.neg_re, ← hre]
  have hnn : 0 ≤ ∫ x in B0579.cell c,
      (starRingEnd ℂ (IIIa.LMPd l w x) * IIIa.LMPd l w x).re := by
    refine integral_nonneg fun x => ?_
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  linarith

/-! ### 3C. Bochner `HasWeakDerivTime` for `(fhPath z₂, fhPath zq₂, fhPath zη₂)` -/

private lemma memLp_lmReal_of_cellL2 {c : ℝ} {f : IIIa.LMSpField} (hf : IIIa.LMCellL2 c f) :
    MemLp (fun x => IIIa.lmReal (f x)) 2 (volume.restrict (B0579.cell c)) := by
  set μc : Measure (ℝ × ℝ) := volume.restrict (B0579.cell c)
  let pack : ℝ × ℝ × ℝ × ℝ → EuclideanSpace ℝ (Fin 4) :=
    fun q => WithLp.toLp 2 ![q.1, q.2.1, q.2.2.1, q.2.2.2]
  have hpack_cont : Continuous pack :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => by
      fin_cases j <;> fun_prop)
  have hquad_meas : AEStronglyMeasurable
      (fun x : ℝ × ℝ => ((f x 0).re, (f x 0).im, (f x 1).re, (f x 1).im)) μc :=
    (hf 0).1.re.prodMk ((hf 0).1.im.prodMk ((hf 1).1.re.prodMk (hf 1).1.im))
  have hmeas : AEStronglyMeasurable (fun x => IIIa.lmReal (f x)) μc := by
    have heq : (fun x => IIIa.lmReal (f x)) =
        fun x => pack ((f x 0).re, (f x 0).im, (f x 1).re, (f x 1).im) := by
      funext x; ext j; fin_cases j <;> rfl
    rw [heq]
    exact hpack_cont.comp_aestronglyMeasurable hquad_meas
  refine IIIa.memLp_two_of_lintegral_lt hmeas ?_
  simp_rw [IIIa.enorm_lmReal_sq]
  have hv_int := (IIIa.integrable_vnorm2_sq hf).2
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hv_int
  rw [Real.enorm_of_nonneg (sq_nonneg _)]

private lemma memLp_lmF_of_cellL2 {c r : ℝ} {u : ℝ → IIIa.LMSpField}
    (hu : IIIa.LMCellL2 c (u r)) :
    MemLp (fun x => IIIa.lmF u (r, x)) 2 (volume.restrict (B0579.cell c)) :=
  memLp_lmReal_of_cellL2 hu

private lemma norm_lmPath_sq_eq {c r : ℝ} {u : ℝ → IIIa.LMSpField}
    (hu : IIIa.LMCellL2 c (u r)) :
    ‖IIIa.lmPath c u r‖ ^ 2 = ∑ i : Fin 2, ∫ x in B0579.cell c, ‖u r x i‖ ^ 2 := by
  have hm := memLp_lmF_of_cellL2 hu
  unfold IIIa.lmPath
  rw [toPathLq_of_memLp hm, ← real_inner_self_eq_norm_sq, L2.inner_def]
  trans ∫ x in B0579.cell c, IIIa.vnorm2 (u r x) ^ 2
  · refine integral_congr_ae (hm.coeFn_toLp.mono fun x hx => ?_)
    dsimp only
    rw [hx, real_inner_self_eq_norm_sq]
    exact IIIa.norm_lmReal_sq (u r x)
  · simp_rw [IIIa.vnorm2_sq_eq]
    exact integral_finsetSum _ fun i _ => IIIa.lm_integrable_sq (hu i)

private lemma inner_lmPath_eq {c r : ℝ} {u v : ℝ → IIIa.LMSpField}
    (hu : IIIa.LMCellL2 c (u r)) (hv : IIIa.LMCellL2 c (v r)) :
    ⟪IIIa.lmPath c u r, IIIa.lmPath c v r⟫ = (IIIa.LMIp c (u r) (v r)).re := by
  have hmu := memLp_lmF_of_cellL2 hu
  have hmv := memLp_lmF_of_cellL2 hv
  unfold IIIa.lmPath
  rw [toPathLq_of_memLp hmu, toPathLq_of_memLp hmv, L2.inner_def]
  have hre : (IIIa.LMIp c (u r) (v r)).re =
      ∫ x in B0579.cell c, (∑ i : Fin 2, starRingEnd ℂ (u r x i) * v r x i).re := by
    unfold IIIa.LMIp
    simpa using (integral_re (IIIa.integrable_LMIp_integrand hu hv)).symm
  rw [hre]
  refine integral_congr_ae ?_
  filter_upwards [hmu.coeFn_toLp, hmv.coeFn_toLp] with x hxu hxv
  rw [hxu, hxv]
  exact IIIa.lmReal_inner (u r x) (v r x)

private lemma inner_lmLift_lmPath_eq {c r : ℝ} (χ : IIIa.LMH c) {u : ℝ → IIIa.LMSpField}
    (hu : IIIa.LMCellL2 c (u r)) :
    ⟪χ, IIIa.lmPath c u r⟫ = (IIIa.LMIp c (IIIa.lmLift χ) (u r)).re := by
  have hmu := memLp_lmF_of_cellL2 hu
  unfold IIIa.lmPath
  rw [toPathLq_of_memLp hmu, L2.inner_def]
  have hre : (IIIa.LMIp c (IIIa.lmLift χ) (u r)).re =
      ∫ x in B0579.cell c, (∑ i : Fin 2, starRingEnd ℂ (IIIa.lmLift χ x i) * u r x i).re := by
    unfold IIIa.LMIp
    simpa using (integral_re (IIIa.integrable_LMIp_integrand (IIIa.lmLift_cellL2 χ) hu)).symm
  rw [hre]
  refine integral_congr_ae (hmu.coeFn_toLp.mono fun x hxu => ?_)
  dsimp only
  rw [hxu, ← IIIa.lmLift_real χ x]
  exact IIIa.lmReal_inner (IIIa.lmLift χ x) (u r x)

private lemma integrableOn_lmPath_Icc_of_bound {c a b : ℝ} {u : ℝ → IIIa.LMSpField}
    (hu_meas : ∀ i : Fin 2, Measurable fun p : ℝ × (ℝ × ℝ) => u p.1 p.2 i)
    {W : ℝ → ℝ} (hW : IntegrableOn W (Icc a b))
    (hbound : ∀ᵐ r ∂(volume.restrict (Icc a b)), ‖IIIa.lmPath c u r‖ ≤ W r) :
    IntegrableOn (IIIa.lmPath c u) (Icc a b) := by
  have hm : StronglyMeasurable (IIIa.lmPath c u) :=
    stronglyMeasurable_toPathLq (IIIa.lmF_measurable u hu_meas).stronglyMeasurable
  exact Integrable.mono' hW hm.aestronglyMeasurable hbound

private lemma perOp_l2_bound {c : ℝ} (hc : 0 < c) {ρ : ℝ × ℝ → ℝ} (hρ : IsCellKernel c ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : ℝ × ℝ → ℂ},
      MemLp g 2 (volume.restrict (B0579.cell c)) →
      MemLp (perOp c ρ g) 2 (volume.restrict (B0579.cell c)) ∧
      ∫ x in B0579.cell c, ‖perOp c ρ g x‖ ^ 2 ≤ C ^ 2 * ∫ x in B0579.cell c, ‖g x‖ ^ 2 := by
  obtain ⟨M, _, hM⟩ := hρ.bdd
  have hmK : Measurable (perK c ρ) := (perK_contDiff hc hρ).continuous.measurable
  have hband : ∀ z : ℝ × ℝ, c / 3 ≤ |z.2| → perK c ρ z = 0 :=
    fun z hz => perK_eq_zero_of_snd hc hρ hz
  refine ⟨IIIa.lmSchurA c M, (IIIa.lmSchurA_pos hc hmK (fun z => hM _) hband).le, fun {g} hg => ?_⟩
  exact IIIa.lm_schur_L2 hc hmK (fun z => hM _) hband hg (perOp_contDiff hc hρ hg).continuous

private def fhField (c : ℝ) (k : ℕ) (w : CProf) : ℝ → IIIa.LMSpField :=
  fun r x i => fhJs c k (fun y => w (r, y) i) x

private def fhPath (c : ℝ) (k : ℕ) (w : CProf) : ℝ → IIIa.LMH c :=
  IIIa.lmPath c (fhField c k w)

private def fhPd (c : ℝ) (k : ℕ) (j : Fin 2) (w : CProf) : ℝ → IIIa.LMSpField :=
  fun r x i => perOp c (B0579.pd j (fhRho c k)) (fun y => w (r, y) i) x

private def fhLap (c : ℝ) (k : ℕ) (w : CProf) : ℝ → IIIa.LMSpField :=
  fun r x i =>
    perOp c (B0579.pd 0 (B0579.pd 0 (fhRho c k))) (fun y => w (r, y) i) x +
    perOp c (B0579.pd 1 (B0579.pd 1 (fhRho c k))) (fun y => w (r, y) i) x

private lemma cprof_slice_cellL2 {c r : ℝ} {w : CProf} (hw : StronglyMeasurable w)
    (hm : MemLp (fun y => w (r, y)) 2 (volume.restrict (B0579.cell c))) :
    IIIa.LMCellL2 c (fun y i => w (r, y) i) := fun i =>
  ⟨((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
      (sliceMeas hw r)).aestronglyMeasurable,
    (eLpNorm_comp_le_merid c w r i).trans_lt hm.eLpNorm_lt_top⟩

private lemma fhField_measurable {c : ℝ} (hc : 0 < c) (k : ℕ) {w : CProf}
    (hw : StronglyMeasurable w) (i : Fin 2) :
    Measurable fun p : ℝ × (ℝ × ℝ) => fhField c k w p.1 p.2 i :=
  perOp_measurable hc (fhRho_isCellKernel hc k)
    (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable hw).measurable)

private lemma fhPd_measurable {c : ℝ} (hc : 0 < c) (k : ℕ) (j : Fin 2) {w : CProf}
    (hw : StronglyMeasurable w) (i : Fin 2) :
    Measurable fun p : ℝ × (ℝ × ℝ) => fhPd c k j w p.1 p.2 i :=
  perOp_measurable hc ((fhRho_isCellKernel hc k).pd j)
    (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable hw).measurable)

private lemma fhLap_measurable {c : ℝ} (hc : 0 < c) (k : ℕ) {w : CProf}
    (hw : StronglyMeasurable w) (i : Fin 2) :
    Measurable fun p : ℝ × (ℝ × ℝ) => fhLap c k w p.1 p.2 i :=
  (perOp_measurable hc (((fhRho_isCellKernel hc k).pd 0).pd 0)
      (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable hw).measurable)).add
    (perOp_measurable hc (((fhRho_isCellKernel hc k).pd 1).pd 1)
      (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable hw).measurable))

private lemma fhPath_norm_le {c r : ℝ} (hc : 0 < c) (k : ℕ) {w : CProf}
    (hw : StronglyMeasurable w)
    (hm : MemLp (fun y => w (r, y)) 2 (volume.restrict (B0579.cell c))) :
    IIIa.LMCellL2 c (fhField c k w r) ∧ ‖fhPath c k w r‖ ≤ ‖profPath c w r‖ := by
  have hcw := cprof_slice_cellL2 hw hm
  have hcf : IIIa.LMCellL2 c (fhField c k w r) := fun i => (fhJs_contr hc k (hcw i)).1
  refine ⟨hcf, ?_⟩
  have hsq : ‖fhPath c k w r‖ ^ 2 ≤ ‖profPath c w r‖ ^ 2 := by
    unfold fhPath profPath
    rw [norm_lmPath_sq_eq hcf, norm_lmPath_sq_eq hcw]
    exact Finset.sum_le_sum fun i _ => (fhJs_contr hc k (hcw i)).2
  nlinarith [norm_nonneg (fhPath c k w r), norm_nonneg (profPath c w r)]

private lemma fhPath_sub_norm_le {c r r' : ℝ} (hc : 0 < c) (k : ℕ) {w : CProf}
    (hw : StronglyMeasurable w)
    (hm : MemLp (fun y => w (r, y)) 2 (volume.restrict (B0579.cell c)))
    (hm' : MemLp (fun y => w (r', y)) 2 (volume.restrict (B0579.cell c))) :
    ‖fhPath c k w r' - fhPath c k w r‖ ≤ ‖profPath c w r' - profPath c w r‖ := by
  let d : CProf := fun p => w (r', p.2) - w (r, p.2)
  have hd_sm : StronglyMeasurable d :=
    (hw.comp_measurable (measurable_const.prodMk measurable_snd)).sub
      (hw.comp_measurable (measurable_const.prodMk measurable_snd))
  have hd_mem : MemLp (fun y => d (0, y)) 2 (volume.restrict (B0579.cell c)) := hm'.sub hm
  have hK := fhRho_isCellKernel hc k
  have hcw := cprof_slice_cellL2 hw hm
  have hcw' := cprof_slice_cellL2 hw hm'
  have hcf : IIIa.LMCellL2 c (fhField c k w r) := fun i => (fhJs_contr hc k (hcw i)).1
  have hcf' : IIIa.LMCellL2 c (fhField c k w r') := fun i => (fhJs_contr hc k (hcw' i)).1
  have hm_f := memLp_lmF_of_cellL2 (u := fhField c k w) hcf
  have hm_f' := memLp_lmF_of_cellL2 (u := fhField c k w) hcf'
  have hm_d := memLp_lmF_of_cellL2 (u := fhField c k d) (fhPath_norm_le hc k hd_sm hd_mem).1
  have hpath_sub : fhPath c k w r' - fhPath c k w r = fhPath c k d 0 := by
    unfold fhPath IIIa.lmPath
    rw [toPathLq_of_memLp hm_f', toPathLq_of_memLp hm_f, toPathLq_of_memLp hm_d, ← MemLp.toLp_sub]
    refine MemLp.toLp_congr (hm_f'.sub hm_f) hm_d (ae_of_all _ fun x => ?_)
    have hdiff_i : ∀ i : Fin 2,
        fhField c k w r' x i - fhField c k w r x i = fhField c k d 0 x i := fun i =>
      (perOp_sub hc hK (hcw' i) (hcw i) x).symm
    ext j
    fin_cases j <;> simp [IIIa.lmF, IIIa.lmReal, Pi.sub_apply, ← hdiff_i 0, ← hdiff_i 1]
  have hprof_eq : ‖profPath c d 0‖ = ‖profPath c w r' - profPath c w r‖ := by
    rw [norm_profPath_eq hd_mem, norm_profPath_sub_le_cylSliceL2 hm hm']
  rw [hpath_sub, ← hprof_eq]
  exact (fhPath_norm_le hc k hd_sm hd_mem).2

private lemma continuousOn_fhPath {c : ℝ} (hc : 0 < c) (k : ℕ) {w : CProf}
    (hw : StronglyMeasurable w) {S : Set ℝ}
    (hmem : ∀ r ∈ S, MemLp (fun y => w (r, y)) 2 (volume.restrict (B0579.cell c)))
    (hcont : ContinuousOn (profPath c w) S) :
    ContinuousOn (fhPath c k w) S := by
  intro r hr
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun r' => ‖profPath c w r' - profPath c w r‖) (𝓝[S] r) (𝓝 0) := by
    have := hcont r hr
    rwa [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [self_mem_nhdsWithin] with r' hr'
  exact fhPath_sub_norm_le hc k hw (hmem r hr) (hmem r' hr')

private lemma tendsto_norm_fhPath_sq {c r : ℝ} (hc : 0 < c) {w : CProf}
    (hw : StronglyMeasurable w)
    (hm : MemLp (fun y => w (r, y)) 2 (volume.restrict (B0579.cell c))) :
    Tendsto (fun k : ℕ => ‖fhPath c k w r‖ ^ 2) atTop (𝓝 (‖profPath c w r‖ ^ 2)) := by
  have hcw := cprof_slice_cellL2 hw hm
  have hdiff_sq : ∀ k : ℕ, ‖fhPath c k w r - profPath c w r‖ ^ 2 =
      ∑ i : Fin 2, ∫ x in B0579.cell c, ‖fhJs c k (fun y => w (r, y) i) x - w (r, x) i‖ ^ 2 := by
    intro k
    have hcf : IIIa.LMCellL2 c (fhField c k w r) := fun i => (fhJs_contr hc k (hcw i)).1
    let diffF : ℝ → IIIa.LMSpField := fun _ x i => fhJs c k (fun y => w (r, y) i) x - w (r, x) i
    have hcd : IIIa.LMCellL2 c (diffF 0) := fun i => (hcf i).sub (hcw i)
    have hm_f := memLp_lmF_of_cellL2 (u := fhField c k w) hcf
    have hm_w := memLp_lmF_of_cellL2 (u := fun s y i => w (s, y) i) hcw
    have hm_d := memLp_lmF_of_cellL2 (r := 0) (u := diffF) hcd
    have heq : fhPath c k w r - profPath c w r = IIIa.lmPath c diffF 0 := by
      unfold fhPath profPath IIIa.lmPath
      rw [toPathLq_of_memLp hm_f, toPathLq_of_memLp hm_w, toPathLq_of_memLp hm_d, ← MemLp.toLp_sub]
      refine MemLp.toLp_congr (hm_f.sub hm_w) hm_d (ae_of_all _ fun x => ?_)
      ext j
      fin_cases j <;> simp [IIIa.lmF, IIIa.lmReal, fhField, diffF]
    rw [heq, norm_lmPath_sq_eq hcd]
  have hlim_sq : Tendsto (fun k : ℕ => ‖fhPath c k w r - profPath c w r‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [hdiff_sq]
    simpa using tendsto_finsetSum Finset.univ fun i _ => fhJs_tendsto hc (hcw i)
  have hlim_norm : Tendsto (fun k : ℕ => ‖fhPath c k w r - profPath c w r‖) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hlim_sq
    rw [Real.sqrt_zero] at h
    exact h.congr fun k => Real.sqrt_sq (norm_nonneg _)
  have hlim_vec : Tendsto (fun k : ℕ => fhPath c k w r) atTop (𝓝 (profPath c w r)) :=
    tendsto_iff_norm_sub_tendsto_zero.2 hlim_norm
  exact ((continuous_norm.pow 2).tendsto _).comp hlim_vec

/-- Complex sesquilinear `LMIp` slice weak equation on `Icc a b ⊂ (T, ∞)`. -/
private lemma sliceWeakEq_sesq {p : Params} {T a b : ℝ}
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train)
    (hT : 0 < T) (haT : T < a) (hab : a < b)
    {g gq gη z₂ zq₂ zη₂ : CProf}
    (hg_src : IsCylSourceH1 p.c g gq gη)
    (hg_int : (∫⁻ s in Ioi T, sliceH1Norm p.c g gq gη s) < ⊤)
    (hz : StronglyMeasurable z₂) (hzq : StronglyMeasurable zq₂) (hzη : StronglyMeasurable zη₂)
    (hzT : IsCylH1Slice p.c (fun y => z₂ (T, y)) (fun y => zq₂ (T, y)) (fun y => zη₂ (T, y)))
    (hz_sol : IsTailMeridionalSolution p T g z₂ zq₂ zη₂)
    (hcont : ∀ s : ℝ, T ≤ s →
      Tendsto (fun s' => cylSliceH1 p.c
        (fun y => z₂ (s', y) - z₂ (s, y))
        (fun y => zq₂ (s', y) - zq₂ (s, y))
        (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici T] s) (𝓝 0))
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hts : tsupport θ ⊆ Ioo a b)
    {Φ : IIIa.LMSpField}
    (hΦ_re : IIIa.IsH1DivFreeTest p.c (fun x i => (Φ x i).re))
    (hΦ_im : IIIa.IsH1DivFreeTest p.c (fun x i => (Φ x i).im)) :
    let term : ℝ → ℂ := fun r =>
      -((deriv θ r : ℝ) : ℂ) * IIIa.LMIp p.c Φ (fun y i => z₂ (r, y) i) +
        (θ r : ℂ) * ((p.ν : ℂ) *
            (IIIa.LMIp p.c (fun y i => IIIa.LMPd 0 (fun w => Φ w i) y)
                (fun y i => zq₂ (r, y) i) +
              IIIa.LMIp p.c (fun y i => IIIa.LMPd 1 (fun w => Φ w i) y)
                (fun y i => zη₂ (r, y) i)) +
          IIIa.LMIp p.c Φ (fun y i => flatBv p.train z₂ zq₂ zη₂ (r, y) i) -
          IIIa.LMIp p.c Φ (fun y i => g (r, y) i))
    IntegrableOn term (Icc a b) ∧ ∫ r in Icc a b, term r = 0 := by
  intro term
  obtain ⟨hint_re, heq_re⟩ := sliceWeakEq_of_isH1DivFreeTest htr hT haT hab hg_src hg_int
    hz hzq hzη hzT hz_sol hcont hθ hts hΦ_re
  obtain ⟨hint_im, heq_im⟩ := sliceWeakEq_of_isH1DivFreeTest htr hT haT hab hg_src hg_int
    hz hzq hzη hzT hz_sol hcont hθ hts hΦ_im
  have hT_fin : sliceH1Norm p.c z₂ zq₂ zη₂ T < ⊤ := by
    unfold sliceH1Norm
    exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2
      ⟨hzT.memL2_u.eLpNorm_lt_top, hzT.memL2_uq.eLpNorm_lt_top⟩, hzT.memL2_uη.eLpNorm_lt_top⟩
  have hfin_z := sliceH1Norm_lt_top_of_ge hz hzq hzη hT_fin hcont
  obtain ⟨hcz, hczq, hczη⟩ := continuousOn_profPaths hz hzq hzη hT_fin hcont
  have hsub_T : Icc a b ⊆ Ici T := fun r hr => haT.le.trans hr.1
  have hmem_z := fun r (hr : r ∈ Icc a b) =>
    memLp_slice_of_sliceH1Norm_lt_top hz hzq hzη (hfin_z r (hsub_T hr))
  obtain ⟨_, _, hbv_s⟩ := memLp_slice_flatBv_on p.train htr hz hzq hzη (hT.trans haT) hab.le
    hmem_z (hcz.mono hsub_T) (hczq.mono hsub_T) (hczη.mono hsub_T)
  obtain ⟨_, _, hae_g⟩ := source_slice_regularity p.c_pos hT hg_src hg_int
  have pair_sesq : ∀ (Ψre Ψim : B0579.Plane → Fin 2 → ℝ) (Ψ : IIIa.LMSpField)
      (w : IIIa.LMSpField),
      (∀ i, MemLp (fun y => (Ψre y i : ℂ)) 2 (volume.restrict (B0579.cell p.c))) →
      (∀ i, MemLp (fun y => (Ψim y i : ℂ)) 2 (volume.restrict (B0579.cell p.c))) →
      (∀ y i, ((Ψre y i : ℂ) - Complex.I * (Ψim y i : ℂ)) = starRingEnd ℂ (Ψ y i)) →
      IIIa.LMCellL2 p.c w →
      (∫ y in B0579.cell p.c, ∑ i : Fin 2, w y i * (Ψre y i : ℂ)) -
        Complex.I * (∫ y in B0579.cell p.c, ∑ i : Fin 2, w y i * (Ψim y i : ℂ)) =
        IIIa.LMIp p.c Ψ w := by
    intro Ψre Ψim Ψ w hm_re hm_im hconj hw
    have hi_re : Integrable (fun y => ∑ i : Fin 2, w y i * (Ψre y i : ℂ))
        (volume.restrict (B0579.cell p.c)) :=
      integrable_finsetSum _ fun i _ => (hw i).integrable_mul (hm_re i)
    have hi_im : Integrable (fun y => ∑ i : Fin 2, w y i * (Ψim y i : ℂ))
        (volume.restrict (B0579.cell p.c)) :=
      integrable_finsetSum _ fun i _ => (hw i).integrable_mul (hm_im i)
    rw [← integral_const_mul, ← integral_sub hi_re (hi_im.const_mul Complex.I)]
    unfold IIIa.LMIp
    refine setIntegral_congr_fun (B0579.measurableSet_cell p.c) fun y _ => ?_
    simp only [Fin.sum_univ_two, ← hconj]
    ring
  have hm_Φre : ∀ i, MemLp (fun y => ((Φ y i).re : ℂ)) 2 (volume.restrict (B0579.cell p.c)) :=
    fun i => Complex.ofRealCLM.comp_memLp' (hΦ_re.l2 i)
  have hm_Φim : ∀ i, MemLp (fun y => ((Φ y i).im : ℂ)) 2 (volume.restrict (B0579.cell p.c)) :=
    fun i => Complex.ofRealCLM.comp_memLp' (hΦ_im.l2 i)
  have hm_pdΦre : ∀ j i, MemLp (fun y => (B0579.pd j (fun w => (Φ w i).re) y : ℂ))
      2 (volume.restrict (B0579.cell p.c)) :=
    fun j i => Complex.ofRealCLM.comp_memLp' (hΦ_re.l2grad i j)
  have hm_pdΦim : ∀ j i, MemLp (fun y => (B0579.pd j (fun w => (Φ w i).im) y : ℂ))
      2 (volume.restrict (B0579.cell p.c)) :=
    fun j i => Complex.ofRealCLM.comp_memLp' (hΦ_im.l2grad i j)
  have hconj_Φ : ∀ y i, ((Φ y i).re : ℂ) - Complex.I * ((Φ y i).im : ℂ) =
      starRingEnd ℂ (Φ y i) := by
    intro y i
    apply Complex.ext <;> simp
  have hconj_pdΦ : ∀ j y i,
      (B0579.pd j (fun w => (Φ w i).re) y : ℂ) -
        Complex.I * (B0579.pd j (fun w => (Φ w i).im) y : ℂ) =
      starRingEnd ℂ (IIIa.LMPd j (fun w => Φ w i) y) := by
    intro j y i
    unfold IIIa.LMPd
    apply Complex.ext <;> simp
  have hae_eq : term =ᵐ[volume.restrict (Icc a b)]
      fun r => sliceWeakTerm p g z₂ zq₂ zη₂ θ (fun x i => (Φ x i).re) r -
        Complex.I * sliceWeakTerm p g z₂ zq₂ zη₂ θ (fun x i => (Φ x i).im) r := by
    filter_upwards [ae_restrict_of_ae hae_g, ae_restrict_mem measurableSet_Icc] with r hgr hr
    have hrT : T < r := lt_of_lt_of_le haT hr.1
    obtain ⟨hfin_gr, _⟩ := hgr hrT
    obtain ⟨hmg, _, _⟩ :=
      memLp_slice_of_sliceH1Norm_lt_top hg_src.sm_g hg_src.sm_gq hg_src.sm_gη hfin_gr
    have hcz_r := cprof_slice_cellL2 hz (hmem_z r hr).1
    have hczq_r := cprof_slice_cellL2 hzq (hmem_z r hr).2.1
    have hczη_r := cprof_slice_cellL2 hzη (hmem_z r hr).2.2
    have hcbv_r : IIIa.LMCellL2 p.c (fun y i => flatBv p.train z₂ zq₂ zη₂ (r, y) i) :=
      fun i => (hbv_s r hr i).1
    have hcg_r := cprof_slice_cellL2 hg_src.sm_g hmg
    have e1 := pair_sesq (fun x i => (Φ x i).re) (fun x i => (Φ x i).im) Φ _
      hm_Φre hm_Φim hconj_Φ hcz_r
    have e2 := pair_sesq (fun y i => B0579.pd 0 (fun w => (Φ w i).re) y)
      (fun y i => B0579.pd 0 (fun w => (Φ w i).im) y)
      (fun y i => IIIa.LMPd 0 (fun w => Φ w i) y) _
      (hm_pdΦre 0) (hm_pdΦim 0) (hconj_pdΦ 0) hczq_r
    have e3 := pair_sesq (fun y i => B0579.pd 1 (fun w => (Φ w i).re) y)
      (fun y i => B0579.pd 1 (fun w => (Φ w i).im) y)
      (fun y i => IIIa.LMPd 1 (fun w => Φ w i) y) _
      (hm_pdΦre 1) (hm_pdΦim 1) (hconj_pdΦ 1) hczη_r
    have eq_visc :
        (∫ y in B0579.cell p.c, ∑ i : Fin 2,
          (zq₂ (r, y) i * (B0579.pd 0 (fun w => (Φ w i).re) y : ℂ) +
            zη₂ (r, y) i * (B0579.pd 1 (fun w => (Φ w i).re) y : ℂ))) -
        Complex.I * (∫ y in B0579.cell p.c, ∑ i : Fin 2,
          (zq₂ (r, y) i * (B0579.pd 0 (fun w => (Φ w i).im) y : ℂ) +
            zη₂ (r, y) i * (B0579.pd 1 (fun w => (Φ w i).im) y : ℂ))) =
        IIIa.LMIp p.c (fun y i => IIIa.LMPd 0 (fun w => Φ w i) y) (fun y i => zq₂ (r, y) i) +
          IIIa.LMIp p.c (fun y i => IIIa.LMPd 1 (fun w => Φ w i) y) (fun y i => zη₂ (r, y) i) := by
      have split_v : ∀ (ψ0 ψ1 : B0579.Plane → Fin 2 → ℝ),
          (∀ i, MemLp (fun y => (ψ0 y i : ℂ)) 2 (volume.restrict (B0579.cell p.c))) →
          (∀ i, MemLp (fun y => (ψ1 y i : ℂ)) 2 (volume.restrict (B0579.cell p.c))) →
          (∫ y in B0579.cell p.c, ∑ i : Fin 2,
            (zq₂ (r, y) i * (ψ0 y i : ℂ) + zη₂ (r, y) i * (ψ1 y i : ℂ))) =
          (∫ y in B0579.cell p.c, ∑ i : Fin 2, zq₂ (r, y) i * (ψ0 y i : ℂ)) +
            (∫ y in B0579.cell p.c, ∑ i : Fin 2, zη₂ (r, y) i * (ψ1 y i : ℂ)) := by
        intro ψ0 ψ1 hm0 hm1
        have hi0 : Integrable (fun y => ∑ i : Fin 2, zq₂ (r, y) i * (ψ0 y i : ℂ))
            (volume.restrict (B0579.cell p.c)) :=
          integrable_finsetSum _ fun i _ => (hczq_r i).integrable_mul (hm0 i)
        have hi1 : Integrable (fun y => ∑ i : Fin 2, zη₂ (r, y) i * (ψ1 y i : ℂ))
            (volume.restrict (B0579.cell p.c)) :=
          integrable_finsetSum _ fun i _ => (hczη_r i).integrable_mul (hm1 i)
        rw [← integral_add hi0 hi1]
        exact setIntegral_congr_fun (B0579.measurableSet_cell p.c) fun y _ => by
          simp [Fin.sum_univ_two]; ring
      rw [split_v _ _ (hm_pdΦre 0) (hm_pdΦre 1), split_v _ _ (hm_pdΦim 0) (hm_pdΦim 1)]
      linear_combination e2 + e3
    have e4 := pair_sesq (fun x i => (Φ x i).re) (fun x i => (Φ x i).im) Φ _
      hm_Φre hm_Φim hconj_Φ hcbv_r
    have e5 := pair_sesq (fun x i => (Φ x i).re) (fun x i => (Φ x i).im) Φ _
      hm_Φre hm_Φim hconj_Φ hcg_r
    dsimp [term, sliceWeakTerm]
    linear_combination ((deriv θ r : ℝ) : ℂ) * e1 -
      (θ r : ℂ) * ((p.ν : ℂ) * eq_visc + e4 - e5)
  have hsub_int : IntegrableOn
      (fun r => sliceWeakTerm p g z₂ zq₂ zη₂ θ (fun x i => (Φ x i).re) r -
        Complex.I * sliceWeakTerm p g z₂ zq₂ zη₂ θ (fun x i => (Φ x i).im) r) (Icc a b) :=
    hint_re.sub (hint_im.const_mul Complex.I)
  refine ⟨hsub_int.congr hae_eq.symm, ?_⟩
  rw [integral_congr_ae hae_eq, integral_sub hint_re (hint_im.const_mul Complex.I),
    integral_const_mul, heq_re, heq_im]
  simp

private def rawZ0 (p : Params) (T : ℝ) (g z₂ zq₂ zη₂ : CProf) (k : ℕ) : ℝ → IIIa.LMSpField :=
  fun r x i =>
    (p.ν : ℂ) * fhLap p.c k z₂ r x i -
      fhField p.c k (tailInd T (flatBv p.train z₂ zq₂ zη₂)) r x i +
      fhField p.c k g r x i

private def rawZj (p : Params) (T : ℝ) (gq gη z₂ zq₂ zη₂ : CProf) (k : ℕ) (j : Fin 2) :
    ℝ → IIIa.LMSpField :=
  fun r x i =>
    (p.ν : ℂ) * fhLap p.c k (![zq₂, zη₂] j) r x i -
      fhPd p.c k j (tailInd T (flatBv p.train z₂ zq₂ zη₂)) r x i +
      fhField p.c k (![gq, gη] j) r x i

private lemma integral_norm_sq_eq_eLpNorm_sq {c : ℝ} {g : B0579.Plane → ℂ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) :
    ∫ x in B0579.cell c, ‖g x‖ ^ 2 =
      ((eLpNorm g 2 (volume.restrict (B0579.cell c))).toReal) ^ 2 := by
  have hgn : MemLp (fun x => ‖g x‖) 2 (volume.restrict (B0579.cell c)) := hg.norm
  have hen : eLpNorm (fun x => ‖g x‖) 2 (volume.restrict (B0579.cell c)) =
      eLpNorm g 2 (volume.restrict (B0579.cell c)) :=
    eLpNorm_congr_norm_ae (Eventually.of_forall fun x => norm_norm (g x))
  have hnorm : ‖hgn.toLp (fun x => ‖g x‖)‖ =
      (eLpNorm g 2 (volume.restrict (B0579.cell c))).toReal :=
    (Lp.norm_toLp (fun x => ‖g x‖) hgn).trans (congrArg ENNReal.toReal hen)
  symm
  rw [← hnorm, ← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (hgn.coeFn_toLp.mono fun x hx => ?_)
  dsimp only
  rw [hx, real_inner_self_eq_norm_sq, norm_norm]

private lemma three_sum_cell_bound {c X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    {A B D : IIIa.LMSpField}
    (hA : IIIa.LMCellL2 c A) (hB : IIIa.LMCellL2 c B) (hD : IIIa.LMCellL2 c D)
    (hbA : ∑ i : Fin 2, ∫ x in B0579.cell c, ‖A x i‖ ^ 2 ≤ 2 * X ^ 2)
    (hbB : ∑ i : Fin 2, ∫ x in B0579.cell c, ‖B x i‖ ^ 2 ≤ X ^ 2)
    (hbD : ∑ i : Fin 2, ∫ x in B0579.cell c, ‖D x i‖ ^ 2 ≤ Y ^ 2) :
    IIIa.LMCellL2 c (fun x i => A x i - B x i + D x i) ∧
    ∑ i : Fin 2, ∫ x in B0579.cell c, ‖A x i - B x i + D x i‖ ^ 2 ≤
      (3 * (X + Y)) ^ 2 := by
  have hcell : IIIa.LMCellL2 c (fun x i => A x i - B x i + D x i) :=
    fun i => ((hA i).sub (hB i)).add (hD i)
  refine ⟨hcell, ?_⟩
  have hpt : ∀ i : Fin 2, ∫ x in B0579.cell c, ‖A x i - B x i + D x i‖ ^ 2 ≤
      3 * ((∫ x in B0579.cell c, ‖A x i‖ ^ 2) +
        (∫ x in B0579.cell c, ‖B x i‖ ^ 2) +
        (∫ x in B0579.cell c, ‖D x i‖ ^ 2)) := by
    intro i
    have hiA := IIIa.lm_integrable_sq (hA i)
    have hiB := IIIa.lm_integrable_sq (hB i)
    have hiD := IIIa.lm_integrable_sq (hD i)
    have hiAB : Integrable (fun x => ‖A x i‖ ^ 2 + ‖B x i‖ ^ 2) (volume.restrict (B0579.cell c)) :=
      hiA.add hiB
    have hiABD : Integrable (fun x => (‖A x i‖ ^ 2 + ‖B x i‖ ^ 2) + ‖D x i‖ ^ 2)
        (volume.restrict (B0579.cell c)) :=
      hiAB.add hiD
    rw [← integral_add hiA hiB, ← integral_add hiAB hiD, ← integral_const_mul]
    refine integral_mono (IIIa.lm_integrable_sq (hcell i)) (hiABD.const_mul 3) fun x => ?_
    dsimp only
    have htri : ‖A x i - B x i + D x i‖ ≤ ‖A x i‖ + ‖B x i‖ + ‖D x i‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    have h1 := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg (‖A x i‖ - ‖B x i‖), sq_nonneg (‖A x i‖ - ‖D x i‖),
      sq_nonneg (‖B x i‖ - ‖D x i‖)]
  have hsum : ∑ i : Fin 2, ∫ x in B0579.cell c, ‖A x i - B x i + D x i‖ ^ 2 ≤
      3 * ((∑ i : Fin 2, ∫ x in B0579.cell c, ‖A x i‖ ^ 2) +
        (∑ i : Fin 2, ∫ x in B0579.cell c, ‖B x i‖ ^ 2) +
        (∑ i : Fin 2, ∫ x in B0579.cell c, ‖D x i‖ ^ 2)) := by
    refine (Finset.sum_le_sum fun i _ => hpt i).trans (le_of_eq ?_)
    simp only [Fin.sum_univ_two]
    ring
  calc ∑ i : Fin 2, ∫ x in B0579.cell c, ‖A x i - B x i + D x i‖ ^ 2
      ≤ 3 * (2 * X ^ 2 + X ^ 2 + Y ^ 2) := hsum.trans (by linarith)
    _ ≤ (3 * (X + Y)) ^ 2 := by nlinarith [mul_nonneg hX hY, sq_nonneg Y]

private lemma p0_path_bound_aux {c a b C_op M_all : ℝ} (hc : 0 < c)
    (hCop_pos : 0 ≤ C_op) (hMall_pos : 0 ≤ M_all)
    {G : ℝ → ℝ} (hG_nn : ∀ r, 0 ≤ G r) (hG_int : IntegrableOn G (Icc a b))
    (Z : ℝ → IIIa.LMSpField) (Yt : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (hYt_m : ∀ i, Measurable fun q => Yt q i)
    (hYt_ae : ∀ r : ℝ, ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
      Yt (r, x) i = IIIa.P0C c (Z r) x i)
    (hZ_b : ∀ᵐ r ∂(volume.restrict (Icc a b)),
      IIIa.LMCellL2 c (Z r) ∧
      ∑ i : Fin 2, ∫ x in B0579.cell c, ‖Z r x i‖ ^ 2 ≤
        (3 * (C_op * M_all + G r)) ^ 2) :
    IntegrableOn (IIIa.lmPath c (fun r x => Yt (r, x))) (Icc a b) ∧
    ∀ᵐ r ∂(volume.restrict (Icc a b)),
      IIIa.LMCellL2 c (Z r) ∧
      IIIa.LMCellL2 c (fun x i => Yt (r, x) i) ∧
      IIIa.lmPath c (fun r x => Yt (r, x)) r =
        IIIa.lmPath c (fun r => IIIa.P0C c (Z r)) r := by
  have hae_info : ∀ᵐ r ∂(volume.restrict (Icc a b)),
      IIIa.LMCellL2 c (Z r) ∧
      IIIa.LMCellL2 c (fun x i => Yt (r, x) i) ∧
      IIIa.lmPath c (fun r x => Yt (r, x)) r =
        IIIa.lmPath c (fun r => IIIa.P0C c (Z r)) r ∧
      ‖IIIa.lmPath c (fun r x => Yt (r, x)) r‖ ≤
        3 * (C_op * M_all + G r) := by
    filter_upwards [hZ_b] with r ⟨hZr, hsq_Z⟩
    have hP0_c : IIIa.LMCellL2 c (IIIa.P0C c (Z r)) := IIIa.lmP0C_cellL2 c (Z r)
    have hYt_c : IIIa.LMCellL2 c (fun x i => Yt (r, x) i) := fun i =>
      (hP0_c i).ae_eq ((hYt_ae r).mono fun x hx => (hx i).symm)
    have hm1 := memLp_lmF_of_cellL2 (u := fun s x => Yt (s, x)) hYt_c
    have hm2 := memLp_lmF_of_cellL2 (u := fun s => IIIa.P0C c (Z s)) hP0_c
    have heq_p : IIIa.lmPath c (fun r x => Yt (r, x)) r =
        IIIa.lmPath c (fun r => IIIa.P0C c (Z r)) r := by
      unfold IIIa.lmPath
      rw [toPathLq_of_memLp hm1, toPathLq_of_memLp hm2]
      refine MemLp.toLp_congr hm1 hm2 ((hYt_ae r).mono fun x hx => ?_)
      change IIIa.lmReal (fun i => Yt (r, x) i) = IIIa.lmReal (IIIa.P0C c (Z r) x)
      ext l; fin_cases l <;> simp [IIIa.lmReal, hx 0, hx 1]
    have hcontr := IIIa.lmP0CContr c hc (Z r) hZr
    have hsum_P0 : ∫ x in B0579.cell c, ∑ i : Fin 2, ‖IIIa.P0C c (Z r) x i‖ ^ 2 =
        ∑ i : Fin 2, ∫ x in B0579.cell c, ‖IIIa.P0C c (Z r) x i‖ ^ 2 :=
      integral_finsetSum _ fun i _ => IIIa.lm_integrable_sq (hP0_c i)
    have hsum_Z : ∫ x in B0579.cell c, ∑ i : Fin 2, ‖Z r x i‖ ^ 2 =
        ∑ i : Fin 2, ∫ x in B0579.cell c, ‖Z r x i‖ ^ 2 :=
      integral_finsetSum _ fun i _ => IIIa.lm_integrable_sq (hZr i)
    have hnorm_sq : ‖IIIa.lmPath c (fun r x => Yt (r, x)) r‖ ^ 2 ≤
        (3 * (C_op * M_all + G r)) ^ 2 := by
      have h_np : ‖IIIa.lmPath c (fun r => IIIa.P0C c (Z r)) r‖ ^ 2 =
          ∑ i : Fin 2, ∫ x in B0579.cell c, ‖IIIa.P0C c (Z r) x i‖ ^ 2 :=
        norm_lmPath_sq_eq (u := fun s => IIIa.P0C c (Z s)) hP0_c
      rw [heq_p, h_np, ← hsum_P0]
      exact (hcontr.trans (le_of_eq hsum_Z)).trans hsq_Z
    have hR_nn : 0 ≤ 3 * (C_op * M_all + G r) := by
      have := hG_nn r
      positivity
    exact ⟨hZr, hYt_c, heq_p,
      by nlinarith [norm_nonneg (IIIa.lmPath c (fun r x => Yt (r, x)) r)]⟩
  have hW_int : IntegrableOn (fun r => 3 * (C_op * M_all + G r)) (Icc a b) :=
    ((integrableOn_const (hs := measure_Icc_lt_top.ne)).add hG_int).const_mul 3
  exact ⟨integrableOn_lmPath_Icc_of_bound hYt_m hW_int (hae_info.mono fun _ h => h.2.2.2),
    hae_info.mono fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩⟩

private lemma fhLap_cell_bound {p : Params} (k : ℕ) {C00 C11 C_op M_all r : ℝ}
    (hC00_nn : 0 ≤ C00) (hC11_nn : 0 ≤ C11) (hMall_pos : 0 ≤ M_all)
    (hCop_le : p.ν * (C00 + C11) ≤ C_op)
    (hC00 : ∀ {g : ℝ × ℝ → ℂ}, MemLp g 2 (volume.restrict (B0579.cell p.c)) →
      MemLp (perOp p.c (B0579.pd 0 (B0579.pd 0 (fhRho p.c k))) g)
        2 (volume.restrict (B0579.cell p.c)) ∧
      ∫ x in B0579.cell p.c,
        ‖perOp p.c (B0579.pd 0 (B0579.pd 0 (fhRho p.c k))) g x‖ ^ 2 ≤
        C00 ^ 2 * ∫ x in B0579.cell p.c, ‖g x‖ ^ 2)
    (hC11 : ∀ {g : ℝ × ℝ → ℂ}, MemLp g 2 (volume.restrict (B0579.cell p.c)) →
      MemLp (perOp p.c (B0579.pd 1 (B0579.pd 1 (fhRho p.c k))) g)
        2 (volume.restrict (B0579.cell p.c)) ∧
      ∫ x in B0579.cell p.c,
        ‖perOp p.c (B0579.pd 1 (B0579.pd 1 (fhRho p.c k))) g x‖ ^ 2 ≤
        C11 ^ 2 * ∫ x in B0579.cell p.c, ‖g x‖ ^ 2)
    (w : CProf) (hw : StronglyMeasurable w)
    (hmw : MemLp (fun y => w (r, y)) 2 (volume.restrict (B0579.cell p.c)))
    (hbw : ‖profPath p.c w r‖ ≤ M_all) :
    IIIa.LMCellL2 p.c (fun x i => (p.ν : ℂ) * fhLap p.c k w r x i) ∧
    ∑ i : Fin 2, ∫ x in B0579.cell p.c, ‖(p.ν : ℂ) * fhLap p.c k w r x i‖ ^ 2 ≤
      2 * (C_op * M_all) ^ 2 := by
  have hcw := cprof_slice_cellL2 hw hmw
  have hcell : IIIa.LMCellL2 p.c (fun x i => (p.ν : ℂ) * fhLap p.c k w r x i) := fun i =>
    ((hC00 (hcw i)).1.add (hC11 (hcw i)).1).const_mul (p.ν : ℂ)
  refine ⟨hcell, ?_⟩
  have hsum_w : ∑ i : Fin 2, ∫ y in B0579.cell p.c, ‖w (r, y) i‖ ^ 2 ≤ M_all ^ 2 := by
    have hnp : ‖profPath p.c w r‖ ^ 2 = ∑ i : Fin 2, ∫ y in B0579.cell p.c, ‖w (r, y) i‖ ^ 2 :=
      norm_lmPath_sq_eq (u := fun s y i => w (s, y) i) hcw
    rw [← hnp]
    exact pow_le_pow_left₀ (norm_nonneg _) hbw 2
  have hpt_i : ∀ i : Fin 2, ∫ x in B0579.cell p.c, ‖(p.ν : ℂ) * fhLap p.c k w r x i‖ ^ 2 ≤
      2 * (p.ν * (C00 + C11)) ^ 2 * ∫ y in B0579.cell p.c, ‖w (r, y) i‖ ^ 2 := by
    intro i
    have h00 := (hC00 (hcw i)).2
    have h11 := (hC11 (hcw i)).2
    have hi0 := IIIa.lm_integrable_sq (hC00 (hcw i)).1
    have hi1 := IIIa.lm_integrable_sq (hC11 (hcw i)).1
    have hle1 : ∫ x in B0579.cell p.c, ‖(p.ν : ℂ) * fhLap p.c k w r x i‖ ^ 2 ≤
        2 * p.ν ^ 2 * ((∫ x in B0579.cell p.c,
            ‖perOp p.c (B0579.pd 0 (B0579.pd 0 (fhRho p.c k))) (fun y => w (r, y) i) x‖ ^ 2) +
          (∫ x in B0579.cell p.c,
            ‖perOp p.c (B0579.pd 1 (B0579.pd 1 (fhRho p.c k))) (fun y => w (r, y) i) x‖ ^ 2)) := by
      rw [← integral_add hi0 hi1, ← integral_const_mul]
      refine integral_mono (IIIa.lm_integrable_sq (hcell i))
        ((hi0.add hi1).const_mul (2 * p.ν ^ 2)) fun x => ?_
      dsimp only [fhLap, Pi.add_apply]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos p.ν_pos, mul_pow]
      set a0 := ‖perOp p.c (B0579.pd 0 (B0579.pd 0 (fhRho p.c k))) (fun y => w (r, y) i) x‖
      set a1 := ‖perOp p.c (B0579.pd 1 (B0579.pd 1 (fhRho p.c k))) (fun y => w (r, y) i) x‖
      have htri : ‖perOp p.c (B0579.pd 0 (B0579.pd 0 (fhRho p.c k))) (fun y => w (r, y) i) x +
          perOp p.c (B0579.pd 1 (B0579.pd 1 (fhRho p.c k))) (fun y => w (r, y) i) x‖ ≤ a0 + a1 :=
        norm_add_le _ _
      have hsq : ‖perOp p.c (B0579.pd 0 (B0579.pd 0 (fhRho p.c k))) (fun y => w (r, y) i) x +
          perOp p.c (B0579.pd 1 (B0579.pd 1 (fhRho p.c k))) (fun y => w (r, y) i) x‖ ^ 2 ≤
          2 * (a0 ^ 2 + a1 ^ 2) :=
        (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans (by nlinarith [sq_nonneg (a0 - a1)])
      calc p.ν ^ 2 * ‖perOp p.c (B0579.pd 0 (B0579.pd 0 (fhRho p.c k))) (fun y => w (r, y) i) x +
            perOp p.c (B0579.pd 1 (B0579.pd 1 (fhRho p.c k))) (fun y => w (r, y) i) x‖ ^ 2
          ≤ p.ν ^ 2 * (2 * (a0 ^ 2 + a1 ^ 2)) :=
            mul_le_mul_of_nonneg_left hsq (sq_nonneg p.ν)
        _ = 2 * p.ν ^ 2 * (a0 ^ 2 + a1 ^ 2) := by ring
    have hC_le : C00 ^ 2 + C11 ^ 2 ≤ (C00 + C11) ^ 2 := by nlinarith
    have hIw_nn : 0 ≤ ∫ y in B0579.cell p.c, ‖w (r, y) i‖ ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    have h01 : (∫ x in B0579.cell p.c,
          ‖perOp p.c (B0579.pd 0 (B0579.pd 0 (fhRho p.c k))) (fun y => w (r, y) i) x‖ ^ 2) +
        (∫ x in B0579.cell p.c,
          ‖perOp p.c (B0579.pd 1 (B0579.pd 1 (fhRho p.c k))) (fun y => w (r, y) i) x‖ ^ 2) ≤
        (C00 ^ 2 * ∫ y in B0579.cell p.c, ‖w (r, y) i‖ ^ 2) +
          (C11 ^ 2 * ∫ y in B0579.cell p.c, ‖w (r, y) i‖ ^ 2) :=
      add_le_add h00 h11
    calc ∫ x in B0579.cell p.c, ‖(p.ν : ℂ) * fhLap p.c k w r x i‖ ^ 2
        ≤ 2 * p.ν ^ 2 * ((C00 ^ 2 * ∫ y in B0579.cell p.c, ‖w (r, y) i‖ ^ 2) +
            (C11 ^ 2 * ∫ y in B0579.cell p.c, ‖w (r, y) i‖ ^ 2)) :=
          hle1.trans (mul_le_mul_of_nonneg_left h01 (by positivity))
      _ = 2 * p.ν ^ 2 * ((C00 ^ 2 + C11 ^ 2) * ∫ y in B0579.cell p.c, ‖w (r, y) i‖ ^ 2) := by ring
      _ ≤ 2 * p.ν ^ 2 * ((C00 + C11) ^ 2 * ∫ y in B0579.cell p.c, ‖w (r, y) i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC_le hIw_nn) (by positivity)
      _ = 2 * (p.ν * (C00 + C11)) ^ 2 * ∫ y in B0579.cell p.c, ‖w (r, y) i‖ ^ 2 := by ring
  calc ∑ i : Fin 2, ∫ x in B0579.cell p.c, ‖(p.ν : ℂ) * fhLap p.c k w r x i‖ ^ 2
      ≤ 2 * (p.ν * (C00 + C11)) ^ 2 * ∑ i : Fin 2, ∫ y in B0579.cell p.c, ‖w (r, y) i‖ ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => hpt_i i
    _ ≤ 2 * (p.ν * (C00 + C11)) ^ 2 * M_all ^ 2 :=
        mul_le_mul_of_nonneg_left hsum_w (by positivity)
    _ = 2 * ((p.ν * (C00 + C11)) * M_all) ^ 2 := by ring
    _ ≤ 2 * (C_op * M_all) ^ 2 := by
        have hprod_le : (p.ν * (C00 + C11)) * M_all ≤ C_op * M_all :=
          mul_le_mul_of_nonneg_right hCop_le hMall_pos
        have hprod_nn : 0 ≤ (p.ν * (C00 + C11)) * M_all := by
          have := p.ν_pos.le; positivity
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hprod_nn hprod_le 2) (by norm_num)

private lemma hasWeakDerivTime_of_scalar_inner {c a b : ℝ} (U U' : ℝ → IIIa.LMH c)
    (hU : IntegrableOn U (Ioo a b)) (hU' : IntegrableOn U' (Ioo a b))
    (hid : ∀ (θ : ℝ → ℝ), ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ Ioo a b →
      ∀ χ : IIIa.LMH c,
        ∫ r in Icc a b, (-(deriv θ r * ⟪χ, U r⟫) - θ r * ⟪χ, U' r⟫) = 0) :
    HasWeakDerivTime a b U U' := by
  refine ⟨hU, hU', fun θ hθ hcs hts => ?_⟩
  have hL := integrable_deriv_smul hθ hcs hts hU
  have hR := integrable_smul hθ hcs hts hU'
  apply ext_inner_left ℝ
  intro χ
  rw [inner_neg_right, ← integral_inner hL, ← integral_inner hR]
  simp_rw [real_inner_smul_right]
  have hL_re : Integrable (fun t => deriv θ t * ⟪χ, U t⟫) := by
    simpa [real_inner_smul_right] using (innerSL ℝ χ).integrable_comp hL
  have hL_neg : Integrable (fun t => -(deriv θ t * ⟪χ, U t⟫)) := hL_re.neg
  have hR_re : Integrable (fun t => θ t * ⟪χ, U' t⟫) := by
    simpa [real_inner_smul_right] using (innerSL ℝ χ).integrable_comp hR
  have h0 := hid θ hθ hcs hts χ
  have hcompl : ∀ t, t ∉ Icc a b → -(deriv θ t * ⟪χ, U t⟫) - θ t * ⟪χ, U' t⟫ = 0 := by
    intro t ht
    have hθ0 : θ t = 0 := image_eq_zero_of_notMem_tsupport
      fun hmem => ht (Ioo_subset_Icc_self (hts hmem))
    have hdθ0 : deriv θ t = 0 := image_eq_zero_of_notMem_tsupport
      fun hmem => ht (Ioo_subset_Icc_self ((tsupport_deriv_subset (𝕜 := ℝ) hmem) |> hts))
    simp [hθ0, hdθ0]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hcompl,
    integral_sub hL_neg hR_re, integral_neg] at h0
  linarith

private lemma re_test_pair_eq (d t : ℝ) (z1 z2 : ℂ) :
    (-(d : ℂ) * z1 + (t : ℂ) * (-z2)).re = -(d * z1.re) - t * z2.re := by
  simp
  ring

private lemma rawZ_bochner_lift {p : Params} {T a b : ℝ}
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train)
    (hT : 0 < T) (haT : T < a) (hab : a < b)
    {g gq gη z₂ zq₂ zη₂ : CProf}
    (hg_src : IsCylSourceH1 p.c g gq gη)
    (hg_int : (∫⁻ s in Ioi T, sliceH1Norm p.c g gq gη s) < ⊤)
    (hz : StronglyMeasurable z₂) (hzq : StronglyMeasurable zq₂) (hzη : StronglyMeasurable zη₂)
    (hzT : IsCylH1Slice p.c (fun y => z₂ (T, y)) (fun y => zq₂ (T, y)) (fun y => zη₂ (T, y)))
    (hcont : ∀ s : ℝ, T ≤ s →
      Tendsto (fun s' => cylSliceH1 p.c
        (fun y => z₂ (s', y) - z₂ (s, y))
        (fun y => zq₂ (s', y) - zq₂ (s, y))
        (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici T] s) (𝓝 0))
    (k : ℕ) :
    ∃ (U0' : ℝ → IIIa.LMH p.c) (Uj' : Fin 2 → ℝ → IIIa.LMH p.c),
      IntegrableOn U0' (Icc a b) ∧
      (∀ j : Fin 2, IntegrableOn (Uj' j) (Icc a b)) ∧
      (∀ᵐ r ∂(volume.restrict (Icc a b)),
        IIIa.LMCellL2 p.c (rawZ0 p T g z₂ zq₂ zη₂ k r) ∧
        U0' r = IIIa.lmPath p.c (fun s => IIIa.P0C p.c (rawZ0 p T g z₂ zq₂ zη₂ k s)) r) ∧
      (∀ j : Fin 2, ∀ᵐ r ∂(volume.restrict (Icc a b)),
        IIIa.LMCellL2 p.c (rawZj p T gq gη z₂ zq₂ zη₂ k j r) ∧
        Uj' j r = IIIa.lmPath p.c (fun s => IIIa.P0C p.c (rawZj p T gq gη z₂ zq₂ zη₂ k j s)) r) := by
  have hc : 0 < p.c := p.c_pos
  have hK := fhRho_isCellKernel hc k
  let bvT : CProf := tailInd T (flatBv p.train z₂ zq₂ zη₂)
  have hbvT_sm : StronglyMeasurable bvT :=
    stronglyMeasurable_tailInd_flatBv hT p.train hz hzq hzη
  have hZ0_meas : ∀ i : Fin 2,
      Measurable fun q : ℝ × (ℝ × ℝ) => rawZ0 p T g z₂ zq₂ zη₂ k q.1 q.2 i := fun i =>
    ((measurable_const.mul (fhLap_measurable hc k hz i)).sub
      (fhField_measurable hc k hbvT_sm i)).add (fhField_measurable hc k hg_src.sm_g i)
  have hZj_meas : ∀ (j : Fin 2) (i : Fin 2),
      Measurable fun q : ℝ × (ℝ × ℝ) => rawZj p T gq gη z₂ zq₂ zη₂ k j q.1 q.2 i := by
    intro j i
    have hwj_sm : StronglyMeasurable (![zq₂, zη₂] j) := by fin_cases j <;> assumption
    have hgj_sm : StronglyMeasurable (![gq, gη] j) := by
      fin_cases j
      · exact hg_src.sm_gq
      · exact hg_src.sm_gη
    exact ((measurable_const.mul (fhLap_measurable hc k hwj_sm i)).sub
      (fhPd_measurable hc k j hbvT_sm i)).add (fhField_measurable hc k hgj_sm i)
  obtain ⟨Yt0, hYt0_m, hYt0_ae⟩ :=
    IIIa.lmP0Rep p.c hc (fun q => rawZ0 p T g z₂ zq₂ zη₂ k q.1 q.2) hZ0_meas
  have hYtj_ex : ∀ j : Fin 2, ∃ Ytj : ℝ × (ℝ × ℝ) → Fin 2 → ℂ,
      (∀ i, Measurable fun q => Ytj q i) ∧
      ∀ s : ℝ, ∀ᵐ x ∂(volume.restrict (B0579.cell p.c)), ∀ i : Fin 2,
        Ytj (s, x) i = IIIa.P0C p.c (rawZj p T gq gη z₂ zq₂ zη₂ k j s) x i :=
    fun j => IIIa.lmP0Rep p.c hc (fun q => rawZj p T gq gη z₂ zq₂ zη₂ k j q.1 q.2) (hZj_meas j)
  let Ytj : Fin 2 → ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun j => Classical.choose (hYtj_ex j)
  have hYtj_m : ∀ j i, Measurable fun q => Ytj j q i :=
    fun j => (Classical.choose_spec (hYtj_ex j)).1
  have hYtj_ae : ∀ j (s : ℝ), ∀ᵐ x ∂(volume.restrict (B0579.cell p.c)), ∀ i : Fin 2,
      Ytj j (s, x) i = IIIa.P0C p.c (rawZj p T gq gη z₂ zq₂ zη₂ k j s) x i :=
    fun j => (Classical.choose_spec (hYtj_ex j)).2
  let U0' : ℝ → IIIa.LMH p.c := IIIa.lmPath p.c (fun r x => Yt0 (r, x))
  let Uj' : Fin 2 → ℝ → IIIa.LMH p.c := fun j => IIIa.lmPath p.c (fun r x => Ytj j (r, x))
  have hT_fin : sliceH1Norm p.c z₂ zq₂ zη₂ T < ⊤ := by
    unfold sliceH1Norm
    exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2
      ⟨hzT.memL2_u.eLpNorm_lt_top, hzT.memL2_uq.eLpNorm_lt_top⟩, hzT.memL2_uη.eLpNorm_lt_top⟩
  have hfin_z := sliceH1Norm_lt_top_of_ge hz hzq hzη hT_fin hcont
  obtain ⟨hcz, hczq, hczη⟩ := continuousOn_profPaths hz hzq hzη hT_fin hcont
  have hsub_T : Icc a b ⊆ Ici T := fun r hr => haT.le.trans hr.1
  have hmem_z := fun r (hr : r ∈ Icc a b) =>
    memLp_slice_of_sliceH1Norm_lt_top hz hzq hzη (hfin_z r (hsub_T hr))
  obtain ⟨C_bv, hCbv_nn, hbv_s⟩ := memLp_slice_flatBv_on p.train htr hz hzq hzη (hT.trans haT)
    hab.le hmem_z (hcz.mono hsub_T) (hczq.mono hsub_T) (hczη.mono hsub_T)
  obtain ⟨_, hsrc_boch, hae_g⟩ := source_slice_regularity hc hT hg_src hg_int
  have hG_int_ab : IntegrableOn (fun r => (sliceH1Norm p.c g gq gη r).toReal) (Icc a b) :=
    (hsrc_boch b (haT.le.trans hab.le)).1.mono_set (Icc_subset_Icc_left haT.le)
  obtain ⟨C00, hC00_nn, hC00⟩ := perOp_l2_bound hc ((hK.pd 0).pd 0)
  obtain ⟨C11, hC11_nn, hC11⟩ := perOp_l2_bound hc ((hK.pd 1).pd 1)
  obtain ⟨Cp0, hCp0_nn, hCp0⟩ := perOp_l2_bound hc (hK.pd 0)
  obtain ⟨Cp1, hCp1_nn, hCp1⟩ := perOp_l2_bound hc (hK.pd 1)
  obtain ⟨Mz0, hMz0⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcz.mono hsub_T)
  obtain ⟨Mzq0, hMzq0⟩ := isCompact_Icc.exists_bound_of_continuousOn (hczq.mono hsub_T)
  obtain ⟨Mzη0, hMzη0⟩ := isCompact_Icc.exists_bound_of_continuousOn (hczη.mono hsub_T)
  let M_all : ℝ := max 0 Mz0 + max 0 Mzq0 + max 0 Mzη0 + 2 * C_bv + 1
  have hMall_pos : 0 ≤ M_all := by dsimp [M_all]; positivity
  have h2Cbv : 2 * C_bv ^ 2 ≤ M_all ^ 2 := by
    have h2Cbv_le : 2 * C_bv ≤ M_all := by
      dsimp [M_all]
      linarith [le_max_left 0 Mz0, le_max_left 0 Mzq0, le_max_left 0 Mzη0]
    calc 2 * C_bv ^ 2 ≤ (2 * C_bv) ^ 2 := by nlinarith [sq_nonneg C_bv]
      _ ≤ M_all ^ 2 := pow_le_pow_left₀ (by positivity) h2Cbv_le 2
  let C_op : ℝ := p.ν * (C00 + C11) + Cp0 + Cp1 + 1
  have hCop_pos : 0 ≤ C_op := by have := p.ν_pos.le; dsimp [C_op]; positivity
  have hCop_le : p.ν * (C00 + C11) ≤ C_op := by dsimp [C_op]; linarith
  have h1_le_Cop : 1 ≤ C_op := by
    have := mul_nonneg p.ν_pos.le (add_nonneg hC00_nn hC11_nn)
    dsimp [C_op]; linarith
  have hZ0_ae_b : ∀ᵐ r ∂(volume.restrict (Icc a b)),
      IIIa.LMCellL2 p.c (rawZ0 p T g z₂ zq₂ zη₂ k r) ∧
      ∑ i : Fin 2, ∫ x in B0579.cell p.c, ‖rawZ0 p T g z₂ zq₂ zη₂ k r x i‖ ^ 2 ≤
        (3 * (C_op * M_all + (sliceH1Norm p.c g gq gη r).toReal)) ^ 2 := by
    filter_upwards [ae_restrict_of_ae hae_g, ae_restrict_mem measurableSet_Icc] with r hgr hr
    have hrT : T < r := lt_of_lt_of_le haT hr.1
    obtain ⟨hfin_gr, _⟩ := hgr hrT
    obtain ⟨hmg, _, _⟩ :=
      memLp_slice_of_sliceH1Norm_lt_top hg_src.sm_g hg_src.sm_gq hg_src.sm_gη hfin_gr
    have hbz : ‖profPath p.c z₂ r‖ ≤ M_all := by
      have := (hMz0 r hr).trans (le_max_right 0 Mz0)
      dsimp [M_all]; linarith [le_max_left 0 Mzq0, le_max_left 0 Mzη0]
    obtain ⟨hcA, hbA⟩ := fhLap_cell_bound k hC00_nn hC11_nn hMall_pos hCop_le
      (fun hg => hC00 hg) (fun hg => hC11 hg) z₂ hz (hmem_z r hr).1 hbz
    have hbv_eq : ∀ i y, bvT (r, y) i = flatBv p.train z₂ zq₂ zη₂ (r, y) i := by
      intro i y; simp [bvT, tailInd, hrT]
    have hcbv_i : ∀ i : Fin 2,
        MemLp (fun y => bvT (r, y) i) 2 (volume.restrict (B0579.cell p.c)) := by
      intro i; simp_rw [hbv_eq i]; exact (hbv_s r hr i).1
    have hcB : IIIa.LMCellL2 p.c (fhField p.c k bvT r) :=
      fun i => (fhJs_contr hc k (hcbv_i i)).1
    have hbB : ∑ i : Fin 2, ∫ x in B0579.cell p.c, ‖fhField p.c k bvT r x i‖ ^ 2 ≤
        (C_op * M_all) ^ 2 := by
      have hi_le : ∀ i : Fin 2, ∫ x in B0579.cell p.c, ‖fhField p.c k bvT r x i‖ ^ 2 ≤ C_bv ^ 2 := by
        intro i
        refine ((fhJs_contr hc k (hcbv_i i)).2).trans ?_
        simp_rw [hbv_eq i]
        rw [integral_norm_sq_eq_eLpNorm_sq (hbv_s r hr i).1]
        exact pow_le_pow_left₀ ENNReal.toReal_nonneg (hbv_s r hr i).2.1 2
      have hsum2 : ∑ i : Fin 2, ∫ x in B0579.cell p.c, ‖fhField p.c k bvT r x i‖ ^ 2 ≤
          2 * C_bv ^ 2 := by
        have h0 := hi_le 0; have h1 := hi_le 1
        simp [Fin.sum_univ_two]; linarith
      have hM_le : M_all ≤ C_op * M_all := le_mul_of_one_le_left hMall_pos h1_le_Cop
      exact hsum2.trans (h2Cbv.trans (pow_le_pow_left₀ hMall_pos hM_le 2))
    obtain ⟨hcD, hnormD⟩ := fhPath_norm_le hc k hg_src.sm_g hmg
    have hbD : ∑ i : Fin 2, ∫ x in B0579.cell p.c, ‖fhField p.c k g r x i‖ ^ 2 ≤
        ((sliceH1Norm p.c g gq gη r).toReal) ^ 2 := by
      have hnp : ‖fhPath p.c k g r‖ ^ 2 =
          ∑ i : Fin 2, ∫ x in B0579.cell p.c, ‖fhField p.c k g r x i‖ ^ 2 :=
        norm_lmPath_sq_eq hcD
      rw [← hnp]
      have hg_le : ‖profPath p.c g r‖ ≤ (sliceH1Norm p.c g gq gη r).toReal := by
        rw [norm_profPath_eq hmg]
        unfold sliceH1Norm cylSliceL2
        exact ENNReal.toReal_mono hfin_gr.ne (le_self_add.trans le_self_add)
      exact pow_le_pow_left₀ (norm_nonneg _) (hnormD.trans hg_le) 2
    exact three_sum_cell_bound (mul_nonneg hCop_pos hMall_pos) ENNReal.toReal_nonneg
      hcA hcB hcD hbA hbB hbD
  have hZj_ae_b : ∀ j : Fin 2, ∀ᵐ r ∂(volume.restrict (Icc a b)),
      IIIa.LMCellL2 p.c (rawZj p T gq gη z₂ zq₂ zη₂ k j r) ∧
      ∑ i : Fin 2, ∫ x in B0579.cell p.c, ‖rawZj p T gq gη z₂ zq₂ zη₂ k j r x i‖ ^ 2 ≤
        (3 * (C_op * M_all + (sliceH1Norm p.c g gq gη r).toReal)) ^ 2 := by
    intro j
    filter_upwards [ae_restrict_of_ae hae_g, ae_restrict_mem measurableSet_Icc] with r hgr hr
    have hrT : T < r := lt_of_lt_of_le haT hr.1
    obtain ⟨hfin_gr, _⟩ := hgr hrT
    obtain ⟨_, hmgq, hmgη⟩ :=
      memLp_slice_of_sliceH1Norm_lt_top hg_src.sm_g hg_src.sm_gq hg_src.sm_gη hfin_gr
    have hwj_sm : StronglyMeasurable (![zq₂, zη₂] j) := by fin_cases j <;> assumption
    have hmwj : MemLp (fun y => (![zq₂, zη₂] j) (r, y)) 2 (volume.restrict (B0579.cell p.c)) := by
      fin_cases j
      · exact (hmem_z r hr).2.1
      · exact (hmem_z r hr).2.2
    have hbwj : ‖profPath p.c (![zq₂, zη₂] j) r‖ ≤ M_all := by
      fin_cases j
      · have := (hMzq0 r hr).trans (le_max_right 0 Mzq0)
        dsimp [M_all]; linarith [le_max_left 0 Mz0, le_max_left 0 Mzη0]
      · have := (hMzη0 r hr).trans (le_max_right 0 Mzη0)
        dsimp [M_all]; linarith [le_max_left 0 Mz0, le_max_left 0 Mzq0]
    obtain ⟨hcA, hbA⟩ := fhLap_cell_bound k hC00_nn hC11_nn hMall_pos hCop_le
      (fun hg => hC00 hg) (fun hg => hC11 hg) (![zq₂, zη₂] j) hwj_sm hmwj hbwj
    have hbv_eq : ∀ i y, bvT (r, y) i = flatBv p.train z₂ zq₂ zη₂ (r, y) i := by
      intro i y; simp [bvT, tailInd, hrT]
    have hcbv_i : ∀ i : Fin 2,
        MemLp (fun y => bvT (r, y) i) 2 (volume.restrict (B0579.cell p.c)) := by
      intro i; simp_rw [hbv_eq i]; exact (hbv_s r hr i).1
    have hCpj : ∃ Cp : ℝ, Cp ≤ Cp0 + Cp1 ∧ 0 ≤ Cp ∧
        ∀ {f : ℝ × ℝ → ℂ}, MemLp f 2 (volume.restrict (B0579.cell p.c)) →
          MemLp (perOp p.c (B0579.pd j (fhRho p.c k)) f) 2 (volume.restrict (B0579.cell p.c)) ∧
          ∫ x in B0579.cell p.c, ‖perOp p.c (B0579.pd j (fhRho p.c k)) f x‖ ^ 2 ≤
            Cp ^ 2 * ∫ x in B0579.cell p.c, ‖f x‖ ^ 2 := by
      fin_cases j
      · exact ⟨Cp0, by linarith, hCp0_nn, fun hf => hCp0 hf⟩
      · exact ⟨Cp1, by linarith, hCp1_nn, fun hf => hCp1 hf⟩
    obtain ⟨Cp, hCp_le, hCp_nn, hCp_b⟩ := hCpj
    have hcB : IIIa.LMCellL2 p.c (fhPd p.c k j bvT r) := fun i => (hCp_b (hcbv_i i)).1
    have hbB : ∑ i : Fin 2, ∫ x in B0579.cell p.c, ‖fhPd p.c k j bvT r x i‖ ^ 2 ≤
        (C_op * M_all) ^ 2 := by
      have hi_le : ∀ i : Fin 2,
          ∫ x in B0579.cell p.c, ‖fhPd p.c k j bvT r x i‖ ^ 2 ≤ (Cp * C_bv) ^ 2 := by
        intro i
        refine ((hCp_b (hcbv_i i)).2).trans ?_
        simp_rw [hbv_eq i]
        rw [integral_norm_sq_eq_eLpNorm_sq (hbv_s r hr i).1, mul_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ ENNReal.toReal_nonneg (hbv_s r hr i).2.1 2) (sq_nonneg Cp)
      have hsum2 : ∑ i : Fin 2, ∫ x in B0579.cell p.c, ‖fhPd p.c k j bvT r x i‖ ^ 2 ≤
          2 * (Cp * C_bv) ^ 2 := by
        have h0 := hi_le 0; have h1 := hi_le 1
        simp [Fin.sum_univ_two]; linarith
      have hCp_Cop : Cp ≤ C_op := by
        have := mul_nonneg p.ν_pos.le (add_nonneg hC00_nn hC11_nn)
        dsimp [C_op]; linarith
      have h1 : 2 * (Cp * C_bv) ^ 2 ≤ (Cp * M_all) ^ 2 := by
        calc 2 * (Cp * C_bv) ^ 2 = Cp ^ 2 * (2 * C_bv ^ 2) := by ring
          _ ≤ Cp ^ 2 * M_all ^ 2 := mul_le_mul_of_nonneg_left h2Cbv (sq_nonneg Cp)
          _ = (Cp * M_all) ^ 2 := by ring
      exact hsum2.trans (h1.trans (pow_le_pow_left₀ (mul_nonneg hCp_nn hMall_pos)
        (mul_le_mul_of_nonneg_right hCp_Cop hMall_pos) 2))
    have hgj_sm : StronglyMeasurable (![gq, gη] j) := by
      fin_cases j
      · exact hg_src.sm_gq
      · exact hg_src.sm_gη
    have hmgj : MemLp (fun y => (![gq, gη] j) (r, y)) 2 (volume.restrict (B0579.cell p.c)) := by
      fin_cases j <;> assumption
    obtain ⟨hcD, hnormD⟩ := fhPath_norm_le hc k hgj_sm hmgj
    have hbD : ∑ i : Fin 2, ∫ x in B0579.cell p.c, ‖fhField p.c k (![gq, gη] j) r x i‖ ^ 2 ≤
        ((sliceH1Norm p.c g gq gη r).toReal) ^ 2 := by
      have hnp : ‖fhPath p.c k (![gq, gη] j) r‖ ^ 2 =
          ∑ i : Fin 2, ∫ x in B0579.cell p.c, ‖fhField p.c k (![gq, gη] j) r x i‖ ^ 2 :=
        norm_lmPath_sq_eq hcD
      rw [← hnp]
      have hgj_le : ‖profPath p.c (![gq, gη] j) r‖ ≤ (sliceH1Norm p.c g gq gη r).toReal := by
        rw [norm_profPath_eq hmgj]
        fin_cases j
        · dsimp only [Matrix.cons_val_zero]
          unfold sliceH1Norm cylSliceL2
          exact ENNReal.toReal_mono hfin_gr.ne (le_add_self.trans le_self_add)
        · dsimp only [Matrix.cons_val_one, Matrix.cons_val_zero]
          unfold sliceH1Norm cylSliceL2
          exact ENNReal.toReal_mono hfin_gr.ne le_add_self
      exact pow_le_pow_left₀ (norm_nonneg _) (hnormD.trans hgj_le) 2
    exact three_sum_cell_bound (mul_nonneg hCop_pos hMall_pos) ENNReal.toReal_nonneg
      hcA hcB hcD hbA hbB hbD
  obtain ⟨hU0'_int_Icc, hae_Z0⟩ := p0_path_bound_aux hc hCop_pos hMall_pos
    (fun _ => ENNReal.toReal_nonneg) hG_int_ab _ Yt0 hYt0_m hYt0_ae hZ0_ae_b
  have hUj'_res := fun j => p0_path_bound_aux hc hCop_pos hMall_pos
    (fun _ => ENNReal.toReal_nonneg) hG_int_ab _ (Ytj j) (hYtj_m j) (hYtj_ae j) (hZj_ae_b j)
  exact ⟨U0', Uj', hU0'_int_Icc, fun j => (hUj'_res j).1,
    hae_Z0.mono fun _ h => ⟨h.1, h.2.2⟩,
    fun j => ((hUj'_res j).2).mono fun _ h => ⟨h.1, h.2.2⟩⟩

private lemma hasWeakDerivTime_fhPath_zero {p : Params} {T a b : ℝ}
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train)
    (hT : 0 < T) (haT : T < a) (hab : a < b)
    {g gq gη z₂ zq₂ zη₂ : CProf}
    (hg_src : IsCylSourceH1 p.c g gq gη)
    (hg_int : (∫⁻ s in Ioi T, sliceH1Norm p.c g gq gη s) < ⊤)
    (hz : StronglyMeasurable z₂) (hzq : StronglyMeasurable zq₂) (hzη : StronglyMeasurable zη₂)
    (hzT : IsCylH1Slice p.c (fun y => z₂ (T, y)) (fun y => zq₂ (T, y)) (fun y => zη₂ (T, y)))
    (hz_sol : IsTailMeridionalSolution p T g z₂ zq₂ zη₂)
    (hcont : ∀ s : ℝ, T ≤ s →
      Tendsto (fun s' => cylSliceH1 p.c
        (fun y => z₂ (s', y) - z₂ (s, y))
        (fun y => zq₂ (s', y) - zq₂ (s, y))
        (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici T] s) (𝓝 0))
    (k : ℕ) {U0' : ℝ → IIIa.LMH p.c}
    (hU0'_int : IntegrableOn U0' (Icc a b))
    (hae_Z0 : ∀ᵐ r ∂(volume.restrict (Icc a b)),
      IIIa.LMCellL2 p.c (rawZ0 p T g z₂ zq₂ zη₂ k r) ∧
      U0' r = IIIa.lmPath p.c (fun s => IIIa.P0C p.c (rawZ0 p T g z₂ zq₂ zη₂ k s)) r) :
    HasWeakDerivTime a b (fhPath p.c k z₂) U0' := by
  have hc : 0 < p.c := p.c_pos
  have hK := fhRho_isCellKernel hc k
  let bvT : CProf := tailInd T (flatBv p.train z₂ zq₂ zη₂)
  have hT_fin : sliceH1Norm p.c z₂ zq₂ zη₂ T < ⊤ := by
    unfold sliceH1Norm
    exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2
      ⟨hzT.memL2_u.eLpNorm_lt_top, hzT.memL2_uq.eLpNorm_lt_top⟩, hzT.memL2_uη.eLpNorm_lt_top⟩
  have hfin_z := sliceH1Norm_lt_top_of_ge hz hzq hzη hT_fin hcont
  obtain ⟨hcz, hczq, hczη⟩ := continuousOn_profPaths hz hzq hzη hT_fin hcont
  have hsub_T : Icc a b ⊆ Ici T := fun r hr => haT.le.trans hr.1
  have hmem_z := fun r (hr : r ∈ Icc a b) =>
    memLp_slice_of_sliceH1Norm_lt_top hz hzq hzη (hfin_z r (hsub_T hr))
  obtain ⟨_, _, hbv_s⟩ := memLp_slice_flatBv_on p.train htr hz hzq hzη (hT.trans haT)
    hab.le hmem_z (hcz.mono hsub_T) (hczq.mono hsub_T) (hczη.mono hsub_T)
  have hreg_z := tail_slice_regularity hT hz hzq hzη hzT hz_sol hcont
  obtain ⟨_, _, hae_g⟩ := source_slice_regularity hc hT hg_src hg_int
  have hU0_cont : ContinuousOn (fhPath p.c k z₂) (Icc a b) :=
    continuousOn_fhPath hc k hz (fun r hr => (hmem_z r hr).1) (hcz.mono hsub_T)
  have hU0_int : IntegrableOn (fhPath p.c k z₂) (Ioo a b) :=
    hU0_cont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  refine hasWeakDerivTime_of_scalar_inner _ _ hU0_int (hU0'_int.mono_set Ioo_subset_Icc_self) ?_
  intro θ hθ _hcs hts χ
  let ψ : IIIa.LMSpField := IIIa.P0C p.c (IIIa.lmLift χ)
  have hχ : IIIa.LMCellL2 p.c (IIIa.lmLift χ) := IIIa.lmLift_cellL2 χ
  have hψ : IIIa.LMCellL2 p.c ψ := IIIa.lmP0C_cellL2 p.c _
  have hψ_div : IIIa.LMWeakDivFree p.c ψ := fun f hf => IIIa.p0DivFreeC p.c hc _ f hf
  obtain ⟨hΦ_re, hΦ_im⟩ := fhJ_isH1DivFreeTest hc k hψ hψ_div
  obtain ⟨hint_sesq, heq_sesq⟩ := sliceWeakEq_sesq htr hT haT hab hg_src hg_int
    hz hzq hzη hzT hz_sol hcont hθ hts hΦ_re hΦ_im
  have hre0 : ∫ r in Icc a b,
      (-((deriv θ r : ℝ) : ℂ) * IIIa.LMIp p.c (fhJ p.c k ψ) (fun y i => z₂ (r, y) i) +
        (θ r : ℂ) * ((p.ν : ℂ) *
            (IIIa.LMIp p.c (fun y i => IIIa.LMPd 0 (fun w => fhJ p.c k ψ w i) y)
                (fun y i => zq₂ (r, y) i) +
              IIIa.LMIp p.c (fun y i => IIIa.LMPd 1 (fun w => fhJ p.c k ψ w i) y)
                (fun y i => zη₂ (r, y) i)) +
          IIIa.LMIp p.c (fhJ p.c k ψ) (fun y i => flatBv p.train z₂ zq₂ zη₂ (r, y) i) -
          IIIa.LMIp p.c (fhJ p.c k ψ) (fun y i => g (r, y) i))).re = 0 := by
    rw [show (0 : ℝ) = (0 : ℂ).re from Complex.zero_re.symm, ← heq_sesq]
    simpa using integral_re hint_sesq
  rw [← hre0]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hae_g, hae_Z0, ae_restrict_mem measurableSet_Icc]
    with r hgr ⟨hZr, heq_U0'_r⟩ hr
  have hrT : T < r := lt_of_lt_of_le haT hr.1
  obtain ⟨hfin_gr, _⟩ := hgr hrT
  obtain ⟨hmg, _, _⟩ :=
    memLp_slice_of_sliceH1Norm_lt_top hg_src.sm_g hg_src.sm_gq hg_src.sm_gη hfin_gr
  obtain ⟨hw_z, hsol_z, _, _⟩ := hreg_z r hrT.le
  have hcz_r := cprof_slice_cellL2 hz (hmem_z r hr).1
  have hczq_r := cprof_slice_cellL2 hzq (hmem_z r hr).2.1
  have hczη_r := cprof_slice_cellL2 hzη (hmem_z r hr).2.2
  have hcbv_r : IIIa.LMCellL2 p.c (fun y i => flatBv p.train z₂ zq₂ zη₂ (r, y) i) :=
    fun i => (hbv_s r hr i).1
  have hcg_r := cprof_slice_cellL2 hg_src.sm_g hmg
  have adj_fhJ : ∀ (f : IIIa.LMSpField), IIIa.LMCellL2 p.c f →
      IIIa.LMIp p.c (fhJ p.c k ψ) f = IIIa.LMIp p.c ψ (fhJ p.c k f) := by
    intro f hf
    unfold IIIa.LMIp
    dsimp only [fhJ, fhJs]
    rw [integral_finsetSum _ fun i _ => IIIa.integrable_conj_mul_of_memLp
        (perOp_memLp hc hK (hψ i)) (hf i),
      integral_finsetSum _ fun i _ => IIIa.integrable_conj_mul_of_memLp
        (hψ i) (perOp_memLp hc hK (hf i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [perOp_adj hc hK (hψ i) (hf i)]
    simp_rw [fhRho_neg p.c k]
  have h_t1 : IIIa.LMIp p.c (fhJ p.c k ψ) (fun y i => z₂ (r, y) i) =
      IIIa.LMIp p.c (IIIa.lmLift χ) (fhField p.c k z₂ r) := by
    rw [adj_fhJ _ hcz_r]
    have hdiv_u := fhJ_weakDivFree hc k hcz_r hsol_z
    have hcf_u : IIIa.LMCellL2 p.c (fhJ p.c k (fun y i => z₂ (r, y) i)) :=
      fun i => (fhJs_contr hc k (hcz_r i)).1
    have hadj_u : IIIa.LMIp p.c ψ (fhJ p.c k (fun y i => z₂ (r, y) i)) =
        IIIa.LMIp p.c (IIIa.lmLift χ)
          (IIIa.P0C p.c (fhJ p.c k (fun y i => z₂ (r, y) i))) :=
      IIIa.lmP0CAdj p.c hc (IIIa.lmLift χ) _ hχ hcf_u
    rw [hadj_u]
    exact IIIa.lmIp_congr_right (IIIa.lmP0CFix p.c hc _ hcf_u hdiv_u)
  have h_visc_l : ∀ (l : Fin 2) (wl : CProf),
      IIIa.LMCellL2 p.c (fun y i => wl (r, y) i) →
      (∀ i, IIIa.HasWeakCellDerivC p.c l (fun y => z₂ (r, y) i) (fun y => wl (r, y) i)) →
      IIIa.LMIp p.c (fun y i => IIIa.LMPd l (fun w => fhJ p.c k ψ w i) y)
        (fun y i => wl (r, y) i) =
      -IIIa.LMIp p.c ψ (fun x i =>
        perOp p.c (B0579.pd l (B0579.pd l (fhRho p.c k))) (fun y => z₂ (r, y) i) x) := by
    intro l wl hcwl hwl
    have hpd_eq : ∀ y i, IIIa.LMPd l (fun w => fhJ p.c k ψ w i) y =
        perOp p.c (B0579.pd l (fhRho p.c k)) (fun w => ψ w i) y :=
      fun y i => perOp_pd hc hK (hψ i) l y
    unfold IIIa.LMIp
    simp_rw [hpd_eq]
    rw [integral_finsetSum _ fun i _ => IIIa.integrable_conj_mul_of_memLp
        (perOp_memLp hc (hK.pd l) (hψ i)) (hcwl i),
      integral_finsetSum _ fun i _ => IIIa.integrable_conj_mul_of_memLp
        (hψ i) (perOp_memLp hc ((hK.pd l).pd l) (hcz_r i)),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [perOp_adj hc (hK.pd l) (hψ i) (hcwl i)]
    have hneg_kern : (fun w => B0579.pd l (fhRho p.c k) (-w)) =
        fun w => -B0579.pd l (fhRho p.c k) w :=
      funext (pd_fhRho_neg p.c k l)
    rw [hneg_kern, ← integral_neg]
    refine setIntegral_congr_fun (B0579.measurableSet_cell p.c) fun x _ => ?_
    rw [perOp_neg_kernel, ← perOp_commute hc (hK.pd l) (hwl i) x]
    ring
  have hv0 := h_visc_l 0 zq₂ hczq_r (fun i => (hw_z i).1)
  have hv1 := h_visc_l 1 zη₂ hczη_r (fun i => (hw_z i).2)
  have hbv_eq : fhJ p.c k (fun y i => flatBv p.train z₂ zq₂ zη₂ (r, y) i) =
      fhField p.c k bvT r := by
    funext x i; dsimp [fhJ, fhField]
    congr 1; funext y; simp [bvT, tailInd, hrT]
  have h_bv := adj_fhJ _ hcbv_r
  rw [hbv_eq] at h_bv
  have h_g := adj_fhJ _ hcg_r
  have hg_eq : fhJ p.c k (fun y i => g (r, y) i) = fhField p.c k g r := rfl
  rw [hg_eq] at h_g
  have hZ_split : ((p.ν : ℂ) *
        (IIIa.LMIp p.c (fun y i => IIIa.LMPd 0 (fun w => fhJ p.c k ψ w i) y)
            (fun y i => zq₂ (r, y) i) +
          IIIa.LMIp p.c (fun y i => IIIa.LMPd 1 (fun w => fhJ p.c k ψ w i) y)
            (fun y i => zη₂ (r, y) i)) +
      IIIa.LMIp p.c (fhJ p.c k ψ) (fun y i => flatBv p.train z₂ zq₂ zη₂ (r, y) i) -
      IIIa.LMIp p.c (fhJ p.c k ψ) (fun y i => g (r, y) i)) =
      -IIIa.LMIp p.c (IIIa.lmLift χ) (IIIa.P0C p.c (rawZ0 p T g z₂ zq₂ zη₂ k r)) := by
    have hadjZ : IIIa.LMIp p.c ψ (rawZ0 p T g z₂ zq₂ zη₂ k r) =
        IIIa.LMIp p.c (IIIa.lmLift χ) (IIIa.P0C p.c (rawZ0 p T g z₂ zq₂ zη₂ k r)) :=
      IIIa.lmP0CAdj p.c hc (IIIa.lmLift χ) _ hχ hZr
    rw [hv0, hv1, h_bv, h_g, ← hadjZ]
    have h00_c : IIIa.LMCellL2 p.c (fun x i =>
        perOp p.c (B0579.pd 0 (B0579.pd 0 (fhRho p.c k))) (fun y => z₂ (r, y) i) x) :=
      fun i => perOp_memLp hc ((hK.pd 0).pd 0) (hcz_r i)
    have h11_c : IIIa.LMCellL2 p.c (fun x i =>
        perOp p.c (B0579.pd 1 (B0579.pd 1 (fhRho p.c k))) (fun y => z₂ (r, y) i) x) :=
      fun i => perOp_memLp hc ((hK.pd 1).pd 1) (hcz_r i)
    have hlap_c : IIIa.LMCellL2 p.c (fhLap p.c k z₂ r) := fun i => (h00_c i).add (h11_c i)
    have hνlap_c : IIIa.LMCellL2 p.c (fun x i => (p.ν : ℂ) * fhLap p.c k z₂ r x i) :=
      fun i => (hlap_c i).const_mul _
    have hbv_c : IIIa.LMCellL2 p.c (fhField p.c k bvT r) :=
      fun i => by rw [← hbv_eq]; exact perOp_memLp hc hK (hcbv_r i)
    have hnbv_c : IIIa.LMCellL2 p.c (fun x i => -fhField p.c k bvT r x i) :=
      fun i => (hbv_c i).neg
    have hνnbv_c : IIIa.LMCellL2 p.c (fun x i =>
        (p.ν : ℂ) * fhLap p.c k z₂ r x i + -fhField p.c k bvT r x i) :=
      fun i => (hνlap_c i).add (hnbv_c i)
    have hg_c : IIIa.LMCellL2 p.c (fhField p.c k g r) :=
      fun i => perOp_memLp hc hK (hcg_r i)
    have heq_raw : rawZ0 p T g z₂ zq₂ zη₂ k r = fun x i =>
        ((p.ν : ℂ) * fhLap p.c k z₂ r x i + -fhField p.c k bvT r x i) +
          fhField p.c k g r x i := by
      funext x i; dsimp [rawZ0]; ring
    rw [heq_raw, IIIa.lmIp_add_right hψ hνnbv_c hg_c,
      IIIa.lmIp_add_right hψ hνlap_c hnbv_c, IIIa.lmIp_smul_right]
    have hlap_ip : IIIa.LMIp p.c ψ (fhLap p.c k z₂ r) =
        IIIa.LMIp p.c ψ (fun x i =>
          perOp p.c (B0579.pd 0 (B0579.pd 0 (fhRho p.c k))) (fun y => z₂ (r, y) i) x) +
        IIIa.LMIp p.c ψ (fun x i =>
          perOp p.c (B0579.pd 1 (B0579.pd 1 (fhRho p.c k))) (fun y => z₂ (r, y) i) x) :=
      IIIa.lmIp_add_right hψ h00_c h11_c
    have hneg_ip : IIIa.LMIp p.c ψ (fun x i => -fhField p.c k bvT r x i) =
        -IIIa.LMIp p.c ψ (fhField p.c k bvT r) := by
      have : (fun x i => -fhField p.c k bvT r x i) =
          fun x i => (-1 : ℂ) * fhField p.c k bvT r x i := by
        funext x i; ring
      rw [this, IIIa.lmIp_smul_right]; ring
    rw [hlap_ip, hneg_ip]
    ring
  rw [h_t1, hZ_split]
  have h_in1 : ⟪χ, fhPath p.c k z₂ r⟫ =
      (IIIa.LMIp p.c (IIIa.lmLift χ) (fhField p.c k z₂ r)).re :=
    inner_lmLift_lmPath_eq χ (fhPath_norm_le hc k hz (hmem_z r hr).1).1
  have h_in2 : ⟪χ, U0' r⟫ =
      (IIIa.LMIp p.c (IIIa.lmLift χ)
        (IIIa.P0C p.c (rawZ0 p T g z₂ zq₂ zη₂ k r))).re := by
    rw [heq_U0'_r]
    exact inner_lmLift_lmPath_eq (u := fun s => IIIa.P0C p.c (rawZ0 p T g z₂ zq₂ zη₂ k s)) χ
      (IIIa.lmP0C_cellL2 p.c (rawZ0 p T g z₂ zq₂ zη₂ k r))
  rw [re_test_pair_eq, ← h_in1, ← h_in2]

private lemma hasWeakDerivTime_fhPath_pd {p : Params} {T a b : ℝ}
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train)
    (hT : 0 < T) (haT : T < a) (hab : a < b)
    {g gq gη z₂ zq₂ zη₂ : CProf}
    (hg_src : IsCylSourceH1 p.c g gq gη)
    (hg_int : (∫⁻ s in Ioi T, sliceH1Norm p.c g gq gη s) < ⊤)
    (hz : StronglyMeasurable z₂) (hzq : StronglyMeasurable zq₂) (hzη : StronglyMeasurable zη₂)
    (hzT : IsCylH1Slice p.c (fun y => z₂ (T, y)) (fun y => zq₂ (T, y)) (fun y => zη₂ (T, y)))
    (hz_sol : IsTailMeridionalSolution p T g z₂ zq₂ zη₂)
    (hcont : ∀ s : ℝ, T ≤ s →
      Tendsto (fun s' => cylSliceH1 p.c
        (fun y => z₂ (s', y) - z₂ (s, y))
        (fun y => zq₂ (s', y) - zq₂ (s, y))
        (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici T] s) (𝓝 0))
    (k : ℕ) (j : Fin 2) {Uj' : ℝ → IIIa.LMH p.c}
    (hUj'_int : IntegrableOn Uj' (Icc a b))
    (hae_Zj : ∀ᵐ r ∂(volume.restrict (Icc a b)),
      IIIa.LMCellL2 p.c (rawZj p T gq gη z₂ zq₂ zη₂ k j r) ∧
      Uj' r = IIIa.lmPath p.c (fun s => IIIa.P0C p.c (rawZj p T gq gη z₂ zq₂ zη₂ k j s)) r) :
    HasWeakDerivTime a b (fhPath p.c k (![zq₂, zη₂] j)) Uj' := by
  have hc : 0 < p.c := p.c_pos
  have hK := fhRho_isCellKernel hc k
  let bvT : CProf := tailInd T (flatBv p.train z₂ zq₂ zη₂)
  have hT_fin : sliceH1Norm p.c z₂ zq₂ zη₂ T < ⊤ := by
    unfold sliceH1Norm
    exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2
      ⟨hzT.memL2_u.eLpNorm_lt_top, hzT.memL2_uq.eLpNorm_lt_top⟩, hzT.memL2_uη.eLpNorm_lt_top⟩
  have hfin_z := sliceH1Norm_lt_top_of_ge hz hzq hzη hT_fin hcont
  obtain ⟨hcz, hczq, hczη⟩ := continuousOn_profPaths hz hzq hzη hT_fin hcont
  have hsub_T : Icc a b ⊆ Ici T := fun r hr => haT.le.trans hr.1
  have hmem_z := fun r (hr : r ∈ Icc a b) =>
    memLp_slice_of_sliceH1Norm_lt_top hz hzq hzη (hfin_z r (hsub_T hr))
  obtain ⟨_, _, hbv_s⟩ := memLp_slice_flatBv_on p.train htr hz hzq hzη (hT.trans haT)
    hab.le hmem_z (hcz.mono hsub_T) (hczq.mono hsub_T) (hczη.mono hsub_T)
  have hreg_z := tail_slice_regularity hT hz hzq hzη hzT hz_sol hcont
  obtain ⟨_, _, hae_g⟩ := source_slice_regularity hc hT hg_src hg_int
  have hUj_cont : ContinuousOn (fhPath p.c k (![zq₂, zη₂] j)) (Icc a b) := by
    fin_cases j
    · exact continuousOn_fhPath hc k hzq (fun r hr => (hmem_z r hr).2.1) (hczq.mono hsub_T)
    · exact continuousOn_fhPath hc k hzη (fun r hr => (hmem_z r hr).2.2) (hczη.mono hsub_T)
  have hUj_int : IntegrableOn (fhPath p.c k (![zq₂, zη₂] j)) (Ioo a b) :=
    hUj_cont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  refine hasWeakDerivTime_of_scalar_inner _ _ hUj_int (hUj'_int.mono_set Ioo_subset_Icc_self) ?_
  intro θ hθ _hcs hts χ
  let ψ : IIIa.LMSpField := IIIa.P0C p.c (IIIa.lmLift χ)
  have hχ : IIIa.LMCellL2 p.c (IIIa.lmLift χ) := IIIa.lmLift_cellL2 χ
  have hψ : IIIa.LMCellL2 p.c ψ := IIIa.lmP0C_cellL2 p.c _
  have hψ_div : IIIa.LMWeakDivFree p.c ψ := fun f hf => IIIa.p0DivFreeC p.c hc _ f hf
  let Φj : IIIa.LMSpField :=
    fun x i => perOp p.c (fun z => -B0579.pd j (fhRho p.c k) z) (fun y => ψ y i) x
  obtain ⟨hΦ_re, hΦ_im⟩ := neg_pd_fhJ_isH1DivFreeTest hc k j hψ hψ_div
  obtain ⟨hint_sesq, heq_sesq⟩ := sliceWeakEq_sesq htr hT haT hab hg_src hg_int
    hz hzq hzη hzT hz_sol hcont hθ hts hΦ_re hΦ_im
  have hre0 : ∫ r in Icc a b,
      (-((deriv θ r : ℝ) : ℂ) * IIIa.LMIp p.c Φj (fun y i => z₂ (r, y) i) +
        (θ r : ℂ) * ((p.ν : ℂ) *
            (IIIa.LMIp p.c (fun y i => IIIa.LMPd 0 (fun w => Φj w i) y)
                (fun y i => zq₂ (r, y) i) +
              IIIa.LMIp p.c (fun y i => IIIa.LMPd 1 (fun w => Φj w i) y)
                (fun y i => zη₂ (r, y) i)) +
          IIIa.LMIp p.c Φj (fun y i => flatBv p.train z₂ zq₂ zη₂ (r, y) i) -
          IIIa.LMIp p.c Φj (fun y i => g (r, y) i))).re = 0 := by
    rw [show (0 : ℝ) = (0 : ℂ).re from Complex.zero_re.symm, ← heq_sesq]
    simpa using integral_re hint_sesq
  rw [← hre0]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hae_g, hae_Zj, ae_restrict_mem measurableSet_Icc]
    with r hgr ⟨hZr, heq_Uj'_r⟩ hr
  have hrT : T < r := lt_of_lt_of_le haT hr.1
  obtain ⟨hfin_gr, hw_g⟩ := hgr hrT
  obtain ⟨hmg, hmgq, hmgη⟩ :=
    memLp_slice_of_sliceH1Norm_lt_top hg_src.sm_g hg_src.sm_gq hg_src.sm_gη hfin_gr
  obtain ⟨hw_z, _, hsol_zq, hsol_zη⟩ := hreg_z r hrT.le
  have hcz_r := cprof_slice_cellL2 hz (hmem_z r hr).1
  have hczq_r := cprof_slice_cellL2 hzq (hmem_z r hr).2.1
  have hczη_r := cprof_slice_cellL2 hzη (hmem_z r hr).2.2
  have hcbv_r : IIIa.LMCellL2 p.c (fun y i => flatBv p.train z₂ zq₂ zη₂ (r, y) i) :=
    fun i => (hbv_s r hr i).1
  have hcg_r := cprof_slice_cellL2 hg_src.sm_g hmg
  let wj : CProf := ![zq₂, zη₂] j
  let gj : CProf := ![gq, gη] j
  have hwj_sm : StronglyMeasurable wj := by dsimp [wj]; fin_cases j <;> assumption
  have hmwj : MemLp (fun y => wj (r, y)) 2 (volume.restrict (B0579.cell p.c)) := by
    dsimp [wj]; fin_cases j
    · exact (hmem_z r hr).2.1
    · exact (hmem_z r hr).2.2
  have hcwj_r := cprof_slice_cellL2 hwj_sm hmwj
  have hsol_wj : IIIa.LMWeakDivFree p.c (fun y i => wj (r, y) i) := by
    dsimp [wj]; fin_cases j <;> assumption
  have hw_z_j : ∀ i, IIIa.HasWeakCellDerivC p.c j
      (fun y => z₂ (r, y) i) (fun y => wj (r, y) i) := by
    intro i; dsimp [wj]; fin_cases j
    · exact (hw_z i).1
    · exact (hw_z i).2
  have hw_g_j : ∀ i, IIIa.HasWeakCellDerivC p.c j
      (fun y => g (r, y) i) (fun y => gj (r, y) i) := by
    intro i; dsimp [gj]; fin_cases j
    · exact (hw_g i).1
    · exact (hw_g i).2
  have hgj_sm : StronglyMeasurable gj := by
    dsimp [gj]; fin_cases j
    · exact hg_src.sm_gq
    · exact hg_src.sm_gη
  have hmgj : MemLp (fun y => gj (r, y)) 2 (volume.restrict (B0579.cell p.c)) := by
    dsimp [gj]; fin_cases j <;> assumption
  have hcgj_r := cprof_slice_cellL2 hgj_sm hmgj
  have adj_Φj : ∀ (f : IIIa.LMSpField), IIIa.LMCellL2 p.c f →
      IIIa.LMIp p.c Φj f =
        IIIa.LMIp p.c ψ (fun x i => perOp p.c (B0579.pd j (fhRho p.c k)) (fun y => f y i) x) := by
    intro f hf
    unfold IIIa.LMIp
    rw [integral_finsetSum _ fun i _ => IIIa.integrable_conj_mul_of_memLp
        (perOp_memLp hc (hK.pd j).neg (hψ i)) (hf i),
      integral_finsetSum _ fun i _ => IIIa.integrable_conj_mul_of_memLp
        (hψ i) (perOp_memLp hc (hK.pd j) (hf i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [perOp_adj hc (hK.pd j).neg (hψ i) (hf i)]
    have hneg_neg : (fun w => -(B0579.pd j (fhRho p.c k) (-w))) = B0579.pd j (fhRho p.c k) := by
      funext w; rw [pd_fhRho_neg p.c k j w, neg_neg]
    rw [hneg_neg]
  have h_t1 : IIIa.LMIp p.c Φj (fun y i => z₂ (r, y) i) =
      IIIa.LMIp p.c (IIIa.lmLift χ) (fhField p.c k wj r) := by
    rw [adj_Φj _ hcz_r]
    have hcomm_z : (fun x i => perOp p.c (B0579.pd j (fhRho p.c k)) (fun y => z₂ (r, y) i) x) =
        fhJ p.c k (fun y i => wj (r, y) i) := by
      funext x i; exact perOp_commute hc hK (hw_z_j i) x
    rw [hcomm_z]
    have hdiv_u := fhJ_weakDivFree hc k hcwj_r hsol_wj
    have hcf_u : IIIa.LMCellL2 p.c (fhJ p.c k (fun y i => wj (r, y) i)) :=
      fun i => (fhJs_contr hc k (hcwj_r i)).1
    have hadj_u : IIIa.LMIp p.c ψ (fhJ p.c k (fun y i => wj (r, y) i)) =
        IIIa.LMIp p.c (IIIa.lmLift χ)
          (IIIa.P0C p.c (fhJ p.c k (fun y i => wj (r, y) i))) :=
      IIIa.lmP0CAdj p.c hc (IIIa.lmLift χ) _ hχ hcf_u
    rw [hadj_u]
    exact IIIa.lmIp_congr_right (IIIa.lmP0CFix p.c hc _ hcf_u hdiv_u)
  have h_visc_l : ∀ (l : Fin 2) (wl : CProf),
      IIIa.LMCellL2 p.c (fun y i => wl (r, y) i) →
      (∀ i, IIIa.HasWeakCellDerivC p.c l (fun y => z₂ (r, y) i) (fun y => wl (r, y) i)) →
      IIIa.LMIp p.c (fun y i => IIIa.LMPd l (fun w => Φj w i) y)
        (fun y i => wl (r, y) i) =
      -IIIa.LMIp p.c ψ (fun x i =>
        perOp p.c (B0579.pd l (B0579.pd l (fhRho p.c k))) (fun y => wj (r, y) i) x) := by
    intro l wl hcwl hwl
    have hK_neg_pd : B0579.pd l (fun z => -B0579.pd j (fhRho p.c k) z) =
        fun z => -B0579.pd l (B0579.pd j (fhRho p.c k)) z := by
      funext z
      unfold B0579.pd
      change (fderiv ℝ (-(B0579.pd j (fhRho p.c k))) z) (B0579.dir l) =
        -(fderiv ℝ (B0579.pd j (fhRho p.c k)) z) (B0579.dir l)
      rw [fderiv_neg]
      simp
    have hpd_eq : ∀ y i, IIIa.LMPd l (fun w => Φj w i) y =
        perOp p.c (fun z => -B0579.pd l (B0579.pd j (fhRho p.c k)) z) (fun w => ψ w i) y := by
      intro y i
      dsimp only [Φj]
      rw [perOp_pd hc (hK.pd j).neg (hψ i) l y, hK_neg_pd]
    unfold IIIa.LMIp
    simp_rw [hpd_eq]
    rw [integral_finsetSum _ fun i _ => IIIa.integrable_conj_mul_of_memLp
        (perOp_memLp hc ((hK.pd j).pd l).neg (hψ i)) (hcwl i),
      integral_finsetSum _ fun i _ => IIIa.integrable_conj_mul_of_memLp
        (hψ i) (perOp_memLp hc ((hK.pd l).pd l) (hcwj_r i)),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [perOp_adj hc ((hK.pd j).pd l).neg (hψ i) (hcwl i)]
    have heven_neg : (fun w => -B0579.pd l (B0579.pd j (fhRho p.c k)) (-w)) =
        fun w => -B0579.pd l (B0579.pd j (fhRho p.c k)) w := by
      funext w; rw [pd2_fhRho_neg p.c k l j w]
    have h3_eq : ∀ x,
        perOp p.c (B0579.pd l (B0579.pd j (fhRho p.c k))) (fun y => wl (r, y) i) x =
        perOp p.c (B0579.pd l (B0579.pd l (fhRho p.c k))) (fun y => wj (r, y) i) x := by
      intro x
      rw [← perOp_commute hc ((hK.pd j).pd l) (hwl i) x]
      have h12 : B0579.pd l (B0579.pd j (fhRho p.c k)) =
          B0579.pd j (B0579.pd l (fhRho p.c k)) :=
        funext (pd_comm_of_smooth hK.1 l j)
      have hkern_eq : B0579.pd l (B0579.pd l (B0579.pd j (fhRho p.c k))) =
          B0579.pd j (B0579.pd l (B0579.pd l (fhRho p.c k))) := by
        rw [h12]
        exact funext (pd_comm_of_smooth (hK.pd l).1 l j)
      rw [hkern_eq, perOp_commute hc ((hK.pd l).pd l) (hw_z_j i) x]
    rw [heven_neg, ← integral_neg]
    refine setIntegral_congr_fun (B0579.measurableSet_cell p.c) fun x _ => ?_
    rw [perOp_neg_kernel, h3_eq x]
    ring
  have hv0 := h_visc_l 0 zq₂ hczq_r (fun i => (hw_z i).1)
  have hv1 := h_visc_l 1 zη₂ hczη_r (fun i => (hw_z i).2)
  have h_bv := adj_Φj _ hcbv_r
  have hbv_eq : (fun x i => perOp p.c (B0579.pd j (fhRho p.c k))
        (fun y => flatBv p.train z₂ zq₂ zη₂ (r, y) i) x) =
      fhPd p.c k j bvT r := by
    funext x i; dsimp [fhPd]; congr 1; funext y; simp [bvT, tailInd, hrT]
  rw [hbv_eq] at h_bv
  have h_g := adj_Φj _ hcg_r
  have hg_eq : (fun x i => perOp p.c (B0579.pd j (fhRho p.c k)) (fun y => g (r, y) i) x) =
      fhField p.c k gj r := by
    funext x i; exact perOp_commute hc hK (hw_g_j i) x
  rw [hg_eq] at h_g
  have hZ_split : ((p.ν : ℂ) *
        (IIIa.LMIp p.c (fun y i => IIIa.LMPd 0 (fun w => Φj w i) y)
            (fun y i => zq₂ (r, y) i) +
          IIIa.LMIp p.c (fun y i => IIIa.LMPd 1 (fun w => Φj w i) y)
            (fun y i => zη₂ (r, y) i)) +
      IIIa.LMIp p.c Φj (fun y i => flatBv p.train z₂ zq₂ zη₂ (r, y) i) -
      IIIa.LMIp p.c Φj (fun y i => g (r, y) i)) =
      -IIIa.LMIp p.c (IIIa.lmLift χ) (IIIa.P0C p.c (rawZj p T gq gη z₂ zq₂ zη₂ k j r)) := by
    have hadjZ : IIIa.LMIp p.c ψ (rawZj p T gq gη z₂ zq₂ zη₂ k j r) =
        IIIa.LMIp p.c (IIIa.lmLift χ) (IIIa.P0C p.c (rawZj p T gq gη z₂ zq₂ zη₂ k j r)) :=
      IIIa.lmP0CAdj p.c hc (IIIa.lmLift χ) _ hχ hZr
    rw [hv0, hv1, h_bv, h_g, ← hadjZ]
    have h00_c : IIIa.LMCellL2 p.c (fun x i =>
        perOp p.c (B0579.pd 0 (B0579.pd 0 (fhRho p.c k))) (fun y => wj (r, y) i) x) :=
      fun i => perOp_memLp hc ((hK.pd 0).pd 0) (hcwj_r i)
    have h11_c : IIIa.LMCellL2 p.c (fun x i =>
        perOp p.c (B0579.pd 1 (B0579.pd 1 (fhRho p.c k))) (fun y => wj (r, y) i) x) :=
      fun i => perOp_memLp hc ((hK.pd 1).pd 1) (hcwj_r i)
    have hlap_c : IIIa.LMCellL2 p.c (fhLap p.c k wj r) := fun i => (h00_c i).add (h11_c i)
    have hνlap_c : IIIa.LMCellL2 p.c (fun x i => (p.ν : ℂ) * fhLap p.c k wj r x i) :=
      fun i => (hlap_c i).const_mul _
    have hbv_c : IIIa.LMCellL2 p.c (fhPd p.c k j bvT r) :=
      fun i => by rw [← hbv_eq]; exact perOp_memLp hc (hK.pd j) (hcbv_r i)
    have hnbv_c : IIIa.LMCellL2 p.c (fun x i => -fhPd p.c k j bvT r x i) :=
      fun i => (hbv_c i).neg
    have hνnbv_c : IIIa.LMCellL2 p.c (fun x i =>
        (p.ν : ℂ) * fhLap p.c k wj r x i + -fhPd p.c k j bvT r x i) :=
      fun i => (hνlap_c i).add (hnbv_c i)
    have hgj_c : IIIa.LMCellL2 p.c (fhField p.c k gj r) :=
      fun i => perOp_memLp hc hK (hcgj_r i)
    have heq_raw : rawZj p T gq gη z₂ zq₂ zη₂ k j r = fun x i =>
        ((p.ν : ℂ) * fhLap p.c k wj r x i + -fhPd p.c k j bvT r x i) +
          fhField p.c k gj r x i := by
      funext x i; dsimp [rawZj, wj, gj]; ring
    rw [heq_raw, IIIa.lmIp_add_right hψ hνnbv_c hgj_c,
      IIIa.lmIp_add_right hψ hνlap_c hnbv_c, IIIa.lmIp_smul_right]
    have hlap_ip : IIIa.LMIp p.c ψ (fhLap p.c k wj r) =
        IIIa.LMIp p.c ψ (fun x i =>
          perOp p.c (B0579.pd 0 (B0579.pd 0 (fhRho p.c k))) (fun y => wj (r, y) i) x) +
        IIIa.LMIp p.c ψ (fun x i =>
          perOp p.c (B0579.pd 1 (B0579.pd 1 (fhRho p.c k))) (fun y => wj (r, y) i) x) :=
      IIIa.lmIp_add_right hψ h00_c h11_c
    have hneg_ip : IIIa.LMIp p.c ψ (fun x i => -fhPd p.c k j bvT r x i) =
        -IIIa.LMIp p.c ψ (fhPd p.c k j bvT r) := by
      have : (fun x i => -fhPd p.c k j bvT r x i) =
          fun x i => (-1 : ℂ) * fhPd p.c k j bvT r x i := by
        funext x i; ring
      rw [this, IIIa.lmIp_smul_right]; ring
    rw [hlap_ip, hneg_ip]
    ring
  rw [h_t1, hZ_split]
  have h_in1 : ⟪χ, fhPath p.c k (![zq₂, zη₂] j) r⟫ =
      (IIIa.LMIp p.c (IIIa.lmLift χ) (fhField p.c k wj r)).re :=
    inner_lmLift_lmPath_eq χ (fhPath_norm_le hc k hwj_sm hmwj).1
  have h_in2 : ⟪χ, Uj' r⟫ =
      (IIIa.LMIp p.c (IIIa.lmLift χ)
        (IIIa.P0C p.c (rawZj p T gq gη z₂ zq₂ zη₂ k j r))).re := by
    rw [heq_Uj'_r]
    exact inner_lmLift_lmPath_eq (u := fun s => IIIa.P0C p.c (rawZj p T gq gη z₂ zq₂ zη₂ k j s)) χ
      (IIIa.lmP0C_cellL2 p.c (rawZj p T gq gη z₂ zq₂ zη₂ k j r))
  rw [re_test_pair_eq, ← h_in1, ← h_in2]

/-- Joint `HasWeakDerivTime` on `Ioo a b ⊂ (T, ∞)` for `fhPath p.c k z₂` and
`fhPath p.c k (![zq₂, zη₂] j)`, together with the slice pairing identities against `rawZ0`/`rawZj`. -/
private lemma hasWeakDerivTime_fhPaths {p : Params} {T a b : ℝ}
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train)
    (hT : 0 < T) (haT : T < a) (hab : a < b)
    {g gq gη z₂ zq₂ zη₂ : CProf}
    (hg_src : IsCylSourceH1 p.c g gq gη)
    (hg_int : (∫⁻ s in Ioi T, sliceH1Norm p.c g gq gη s) < ⊤)
    (hz : StronglyMeasurable z₂) (hzq : StronglyMeasurable zq₂) (hzη : StronglyMeasurable zη₂)
    (hzT : IsCylH1Slice p.c (fun y => z₂ (T, y)) (fun y => zq₂ (T, y)) (fun y => zη₂ (T, y)))
    (hz_sol : IsTailMeridionalSolution p T g z₂ zq₂ zη₂)
    (hcont : ∀ s : ℝ, T ≤ s →
      Tendsto (fun s' => cylSliceH1 p.c
        (fun y => z₂ (s', y) - z₂ (s, y))
        (fun y => zq₂ (s', y) - zq₂ (s, y))
        (fun y => zη₂ (s', y) - zη₂ (s, y))) (𝓝[Ici T] s) (𝓝 0))
    (k : ℕ) :
    ∃ (U0' : ℝ → IIIa.LMH p.c) (Uj' : Fin 2 → ℝ → IIIa.LMH p.c),
      HasWeakDerivTime a b (fhPath p.c k z₂) U0' ∧
      (∀ j : Fin 2, HasWeakDerivTime a b (fhPath p.c k (![zq₂, zη₂] j)) (Uj' j)) ∧
      (∀ᵐ r ∂(volume.restrict (Icc a b)),
        ⟪U0' r, fhPath p.c k z₂ r⟫ =
          (IIIa.LMIp p.c (rawZ0 p T g z₂ zq₂ zη₂ k r) (fhField p.c k z₂ r)).re ∧
        ∀ j : Fin 2,
          ⟪Uj' j r, fhPath p.c k (![zq₂, zη₂] j) r⟫ =
            (IIIa.LMIp p.c (rawZj p T gq gη z₂ zq₂ zη₂ k j r)
              (fhField p.c k (![zq₂, zη₂] j) r)).re) := by
  have hc : 0 < p.c := p.c_pos
  obtain ⟨U0', Uj', hU0'_int, hUj'_int, hae_Z0, hae_Zj⟩ :=
    rawZ_bochner_lift htr hT haT hab hg_src hg_int hz hzq hzη hzT hcont k
  have hw0 : HasWeakDerivTime a b (fhPath p.c k z₂) U0' :=
    hasWeakDerivTime_fhPath_zero htr hT haT hab hg_src hg_int hz hzq hzη hzT hz_sol hcont k
      hU0'_int hae_Z0
  have hwj : ∀ j : Fin 2, HasWeakDerivTime a b (fhPath p.c k (![zq₂, zη₂] j)) (Uj' j) :=
    fun j => hasWeakDerivTime_fhPath_pd htr hT haT hab hg_src hg_int hz hzq hzη hzT hz_sol hcont
      k j (hUj'_int j) (hae_Zj j)
  have hT_fin : sliceH1Norm p.c z₂ zq₂ zη₂ T < ⊤ := by
    unfold sliceH1Norm
    exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2
      ⟨hzT.memL2_u.eLpNorm_lt_top, hzT.memL2_uq.eLpNorm_lt_top⟩, hzT.memL2_uη.eLpNorm_lt_top⟩
  have hfin_z := sliceH1Norm_lt_top_of_ge hz hzq hzη hT_fin hcont
  have hmem_z := fun r (hr : r ∈ Icc a b) =>
    memLp_slice_of_sliceH1Norm_lt_top hz hzq hzη (hfin_z r (haT.le.trans hr.1))
  have hreg_z := tail_slice_regularity hT hz hzq hzη hzT hz_sol hcont
  refine ⟨U0', Uj', hw0, hwj, ?_⟩
  filter_upwards [hae_Z0, hae_Zj 0, hae_Zj 1, ae_restrict_mem measurableSet_Icc]
    with r ⟨hZ0r, heq0⟩ ⟨hZq_r, heqq⟩ ⟨hZη_r, heqη⟩ hr
  have hrT : T ≤ r := (haT.trans_le hr.1).le
  obtain ⟨_, hsol_z, hsol_zq, hsol_zη⟩ := hreg_z r hrT
  have hcz_r := cprof_slice_cellL2 hz (hmem_z r hr).1
  have hcu0 := (fhPath_norm_le hc k hz (hmem_z r hr).1).1
  have hdiv_u0 := fhJ_weakDivFree hc k hcz_r hsol_z
  have hp0 : ⟪U0' r, fhPath p.c k z₂ r⟫ =
      (IIIa.LMIp p.c (rawZ0 p T g z₂ zq₂ zη₂ k r) (fhField p.c k z₂ r)).re := by
    rw [heq0]
    dsimp only [fhPath]
    rw [inner_lmPath_eq (u := fun s => IIIa.P0C p.c (rawZ0 p T g z₂ zq₂ zη₂ k s))
        (IIIa.lmP0C_cellL2 p.c _) hcu0,
      IIIa.lmP0CAdj p.c hc _ _ hZ0r hcu0,
      IIIa.lmIp_congr_right (IIIa.lmP0CFix p.c hc _ hcu0 hdiv_u0)]
  refine ⟨hp0, fun j => ?_⟩
  fin_cases j
  · have hczq_r := cprof_slice_cellL2 hzq (hmem_z r hr).2.1
    have hcuq := (fhPath_norm_le hc k hzq (hmem_z r hr).2.1).1
    have hdiv_uq := fhJ_weakDivFree hc k hczq_r hsol_zq
    change ⟪Uj' 0 r, fhPath p.c k zq₂ r⟫ =
      (IIIa.LMIp p.c (rawZj p T gq gη z₂ zq₂ zη₂ k 0 r) (fhField p.c k zq₂ r)).re
    rw [heqq]
    dsimp only [fhPath]
    rw [inner_lmPath_eq (u := fun s => IIIa.P0C p.c (rawZj p T gq gη z₂ zq₂ zη₂ k 0 s))
        (IIIa.lmP0C_cellL2 p.c _) hcuq,
      IIIa.lmP0CAdj p.c hc _ _ hZq_r hcuq,
      IIIa.lmIp_congr_right (IIIa.lmP0CFix p.c hc _ hcuq hdiv_uq)]
  · have hczη_r := cprof_slice_cellL2 hzη (hmem_z r hr).2.2
    have hcuη := (fhPath_norm_le hc k hzη (hmem_z r hr).2.2).1
    have hdiv_uη := fhJ_weakDivFree hc k hczη_r hsol_zη
    change ⟪Uj' 1 r, fhPath p.c k zη₂ r⟫ =
      (IIIa.LMIp p.c (rawZj p T gq gη z₂ zq₂ zη₂ k 1 r) (fhField p.c k zη₂ r)).re
    rw [heqη]
    dsimp only [fhPath]
    rw [inner_lmPath_eq (u := fun s => IIIa.P0C p.c (rawZj p T gq gη z₂ zq₂ zη₂ k 1 s))
        (IIIa.lmP0C_cellL2 p.c _) hcuη,
      IIIa.lmP0CAdj p.c hc _ _ hZη_r hcuη,
      IIIa.lmIp_congr_right (IIIa.lmP0CFix p.c hc _ hcuη hdiv_uη)]

/-! ### 3D. Quantitative slice pairing bounds, regularized `√` FTC, and integral Gronwall -/

private lemma re_conj_mul_integral_le {c A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {f u : B0579.Plane → ℂ}
    (hf : MemLp f 2 (volume.restrict (B0579.cell c)))
    (hu : MemLp u 2 (volume.restrict (B0579.cell c)))
    (hf_sq : ∫ x in B0579.cell c, ‖f x‖ ^ 2 ≤ A ^ 2)
    (hu_sq : ∫ x in B0579.cell c, ‖u x‖ ^ 2 ≤ B ^ 2) :
    |(∫ x in B0579.cell c, starRingEnd ℂ (f x) * u x).re| ≤ A * B := by
  set μc : Measure B0579.Plane := volume.restrict (B0579.cell c)
  have norm_le : ∀ {g : B0579.Plane → ℂ} {M : ℝ}, 0 ≤ M → MemLp g 2 μc →
      ∫ x in B0579.cell c, ‖g x‖ ^ 2 ≤ M ^ 2 → (eLpNorm g 2 μc).toReal ≤ M := by
    intro g M hM hg hsq
    have heq : ∫ x in B0579.cell c, ‖g x‖ ^ 2 = ((eLpNorm g 2 μc).toReal) ^ 2 :=
      integral_norm_sq_eq_eLpNorm_sq hg
    rw [heq] at hsq
    nlinarith [ENNReal.toReal_nonneg (a := eLpNorm g 2 μc)]
  have he_star : eLpNorm (fun x => starRingEnd ℂ (f x)) 2 μc = eLpNorm f 2 μc :=
    eLpNorm_congr_norm_ae (Eventually.of_forall fun x => RCLike.norm_conj (f x))
  have hf_le : (eLpNorm (fun x => starRingEnd ℂ (f x)) 2 μc).toReal ≤ A := by
    rw [he_star]; exact norm_le hA hf hf_sq
  have hu_le : (eLpNorm u 2 μc).toReal ≤ B := norm_le hB hu hu_sq
  calc |(∫ x, starRingEnd ℂ (f x) * u x ∂μc).re|
      ≤ ‖∫ x, starRingEnd ℂ (f x) * u x ∂μc‖ := Complex.abs_re_le_norm _
    _ ≤ (eLpNorm (fun x => starRingEnd ℂ (f x)) 2 μc).toReal * (eLpNorm u 2 μc).toReal :=
        norm_integral_mul_le_l2 hf.star hu
    _ ≤ A * B := mul_le_mul hf_le hu_le ENNReal.toReal_nonneg hA

private lemma fderiv_train_comp_norm_le {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr) {r : ℝ} (hr0 : 0 ≤ r)
    (l : Fin 2) (z : B0579.Plane) :
    ‖fderiv ℝ (fun y => tr.v r y l) z‖ ≤ (B0277.supNormD 1 (tr.v r)).toReal := by
  obtain ⟨_, _, h1⟩ := IIIa.AdvectionEnergyAux.supNormD_one_bound_on tr htr hr0
  have hpt := (h1 r ⟨hr0, le_rfl⟩).2.2 z
  have hv_diff : DifferentiableAt ℝ (tr.v r) z :=
    ((IIIa.AdvectionEnergyAux.contDiff_train_slice tr hr0).differentiable (by simp)).differentiableAt
  have hcomp : fderiv ℝ (fun y => tr.v r y l) z =
      (EuclideanSpace.proj l : UnforcedLeray.Train.Vec →L[ℝ] ℝ).comp (fderiv ℝ (tr.v r) z) :=
    ((EuclideanSpace.proj l : UnforcedLeray.Train.Vec →L[ℝ] ℝ).hasFDerivAt.comp z
      hv_diff.hasFDerivAt).fderiv
  rw [hcomp]
  refine ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg fun v => ?_
  change |(fderiv ℝ (tr.v r) z v) l| ≤ (B0277.supNormD 1 (tr.v r)).toReal * ‖v‖
  calc |(fderiv ℝ (tr.v r) z v) l|
      ≤ ‖fderiv ℝ (tr.v r) z v‖ := Real.norm_eq_abs _ ▸ PiLp.norm_apply_le _ l
    _ ≤ ‖fderiv ℝ (tr.v r) z‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ v
    _ ≤ (B0277.supNormD 1 (tr.v r)).toReal * ‖v‖ :=
        mul_le_mul_of_nonneg_right hpt (norm_nonneg v)

private lemma raw_pairings_bound {p : Params} {T r B : ℝ}
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train)
    (hT : 0 < T) (hrT : T < r) (hB0 : 0 ≤ B)
    {g gq gη z₂ zq₂ zη₂ : CProf}
    (hg_src : IsCylSourceH1 p.c g gq gη)
    (hz : StronglyMeasurable z₂) (hzq : StronglyMeasurable zq₂) (hzη : StronglyMeasurable zη₂)
    (hfin_z : sliceH1Norm p.c z₂ zq₂ zη₂ r < ⊤)
    (hfin_g : sliceH1Norm p.c g gq gη r < ⊤)
    (hw_z : ∀ i : Fin 2,
      IIIa.HasWeakCellDerivC p.c 0 (fun y => z₂ (r, y) i) (fun y => zq₂ (r, y) i) ∧
      IIIa.HasWeakCellDerivC p.c 1 (fun y => z₂ (r, y) i) (fun y => zη₂ (r, y) i))
    (k : ℕ)
    (hB_z : ‖fhPath p.c k z₂ r‖ ^ 2 ≤ B ^ 2)
    (hB_zq : ‖fhPath p.c k zq₂ r‖ ^ 2 ≤ B ^ 2)
    (hB_zη : ‖fhPath p.c k zη₂ r‖ ^ 2 ≤ B ^ 2) :
    (IIIa.LMIp p.c (rawZ0 p T g z₂ zq₂ zη₂ k r) (fhField p.c k z₂ r)).re +
      (IIIa.LMIp p.c (rawZj p T gq gη z₂ zq₂ zη₂ k 0 r) (fhField p.c k zq₂ r)).re +
      (IIIa.LMIp p.c (rawZj p T gq gη z₂ zq₂ zη₂ k 1 r) (fhField p.c k zη₂ r)).re ≤
      (32 * fhCommConst * strainRate p.train r * (sliceH1Norm p.c z₂ zq₂ zη₂ r).toReal +
        2 * (sliceH1Norm p.c g gq gη r).toReal) * B := by
  have hc : 0 < p.c := p.c_pos
  have hr0 : 0 ≤ r := (hT.trans hrT).le
  have hK := fhRho_isCellKernel hc k
  have hCF1 : 1 ≤ fhCommConst := one_le_fhCommConst
  have hCF_pos : 0 ≤ fhCommConst := zero_le_one.trans hCF1
  set μc : Measure B0579.Plane := volume.restrict (B0579.cell p.c)
  set W : ℝ := (sliceH1Norm p.c z₂ zq₂ zη₂ r).toReal
  set S : ℝ := strainRate p.train r
  have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
  have hS0 : 0 ≤ S := strainRate_nonneg p.train r
  obtain ⟨hmz, hmzq, hmzη⟩ := memLp_slice_of_sliceH1Norm_lt_top hz hzq hzη hfin_z
  obtain ⟨hmg, hmgq, hmgη⟩ :=
    memLp_slice_of_sliceH1Norm_lt_top hg_src.sm_g hg_src.sm_gq hg_src.sm_gη hfin_g
  have hcz := cprof_slice_cellL2 hz hmz
  have hczq := cprof_slice_cellL2 hzq hmzq
  have hczη := cprof_slice_cellL2 hzη hmzη
  have hcg := cprof_slice_cellL2 hg_src.sm_g hmg
  have hcgq := cprof_slice_cellL2 hg_src.sm_gq hmgq
  have hcgη := cprof_slice_cellL2 hg_src.sm_gη hmgη
  -- Component L² norms bounded by W^2
  have comp_sq_W : ∀ (w : CProf), StronglyMeasurable w → MemLp (fun y => w (r, y)) 2 μc →
      cylSliceL2 p.c (fun y => w (r, y)) ≤ sliceH1Norm p.c z₂ zq₂ zη₂ r →
      ∀ i : Fin 2, ∫ y in B0579.cell p.c, ‖w (r, y) i‖ ^ 2 ≤ W ^ 2 := by
    intro w hw hmw hle i
    have hcw := cprof_slice_cellL2 hw hmw
    have h1 : ∫ y in B0579.cell p.c, ‖w (r, y) i‖ ^ 2 ≤ ‖profPath p.c w r‖ ^ 2 := by
      unfold profPath
      rw [norm_lmPath_sq_eq hcw]
      exact Finset.single_le_sum (f := fun m : Fin 2 => ∫ y in B0579.cell p.c, ‖w (r, y) m‖ ^ 2)
        (fun _ _ => integral_nonneg fun _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : ‖profPath p.c w r‖ ≤ W := by
      rw [norm_profPath_eq hmw]
      exact ENNReal.toReal_mono hfin_z.ne hle
    exact h1.trans (pow_le_pow_left₀ (norm_nonneg _) h2 2)
  have hW_z := comp_sq_W z₂ hz hmz (le_self_add.trans le_self_add)
  have hW_zq := comp_sq_W zq₂ hzq hmzq (le_add_self.trans le_self_add)
  have hW_zη := comp_sq_W zη₂ hzη hmzη le_add_self
  -- Component L² norms of fhField bounded by B^2
  have comp_sq_B : ∀ (w : CProf), StronglyMeasurable w → MemLp (fun y => w (r, y)) 2 μc →
      ‖fhPath p.c k w r‖ ^ 2 ≤ B ^ 2 →
      ∀ i : Fin 2, MemLp (fun x => fhField p.c k w r x i) 2 μc ∧
        ∫ x in B0579.cell p.c, ‖fhField p.c k w r x i‖ ^ 2 ≤ B ^ 2 := by
    intro w hw hmw hBw i
    have hcf := (fhPath_norm_le hc k hw hmw).1
    refine ⟨hcf i, ?_⟩
    have h1 : ∫ x in B0579.cell p.c, ‖fhField p.c k w r x i‖ ^ 2 ≤ ‖fhPath p.c k w r‖ ^ 2 := by
      unfold fhPath
      rw [norm_lmPath_sq_eq hcf]
      exact Finset.single_le_sum
        (f := fun m : Fin 2 => ∫ x in B0579.cell p.c, ‖fhField p.c k w r x m‖ ^ 2)
        (fun _ _ => integral_nonneg fun _ => sq_nonneg _) (Finset.mem_univ i)
    exact h1.trans hBw
  -- Viscous pairing ≤ 0 for any w ∈ {z₂, zq₂, zη₂}
  have visc_le_zero : ∀ (w : CProf), StronglyMeasurable w → MemLp (fun y => w (r, y)) 2 μc →
      ∀ i : Fin 2,
        (∫ x in B0579.cell p.c,
          starRingEnd ℂ ((p.ν : ℂ) * fhLap p.c k w r x i) * fhField p.c k w r x i).re ≤ 0 := by
    intro w hw hmw i
    have hcw := cprof_slice_cellL2 hw hmw
    let u_i : B0579.Plane → ℂ := fun x => fhField p.c k w r x i
    have hu_sm : ContDiff ℝ ∞ u_i := perOp_contDiff hc hK (hcw i)
    have hu_per : ∀ x, u_i (x.1 + p.c, x.2) = u_i x := fun x => perOp_periodic hc _ _ x
    have hu_L2 : MemLp u_i 2 μc := perOp_memLp hc hK (hcw i)
    have hpd_eq : ∀ (l : Fin 2), IIIa.LMPd l u_i =
        perOp p.c (B0579.pd l (fhRho p.c k)) (fun y => w (r, y) i) :=
      fun l => funext (perOp_pd hc hK (hcw i) l)
    have hpd2_eq : ∀ (l : Fin 2), IIIa.LMPd l (IIIa.LMPd l u_i) =
        perOp p.c (B0579.pd l (B0579.pd l (fhRho p.c k))) (fun y => w (r, y) i) := by
      intro l; rw [hpd_eq l]; exact funext (perOp_pd hc (hK.pd l) (hcw i) l)
    have hu_pd : ∀ l, MemLp (IIIa.LMPd l u_i) 2 μc := by
      intro l; rw [hpd_eq l]; exact perOp_memLp hc (hK.pd l) (hcw i)
    have hu_pd2 : ∀ l, MemLp (IIIa.LMPd l (IIIa.LMPd l u_i)) 2 μc := by
      intro l; rw [hpd2_eq l]; exact perOp_memLp hc ((hK.pd l).pd l) (hcw i)
    have hv0 := viscous_re_nonpos hc 0 hu_sm hu_per hu_L2 (hu_pd 0) (hu_pd2 0)
    have hv1 := viscous_re_nonpos hc 1 hu_sm hu_per hu_L2 (hu_pd 1) (hu_pd2 1)
    have hlap_eq : (fun x => fhLap p.c k w r x i) =
        fun x => IIIa.LMPd 0 (IIIa.LMPd 0 u_i) x + IIIa.LMPd 1 (IIIa.LMPd 1 u_i) x := by
      funext x; dsimp [fhLap]; rw [hpd2_eq 0, hpd2_eq 1]
    have hi0 := IIIa.integrable_conj_mul_of_memLp (hu_pd2 0) hu_L2
    have hi1 := IIIa.integrable_conj_mul_of_memLp (hu_pd2 1) hu_L2
    have hsplit : ∫ x in B0579.cell p.c,
        starRingEnd ℂ ((p.ν : ℂ) * fhLap p.c k w r x i) * u_i x =
        (p.ν : ℂ) * ((∫ x in B0579.cell p.c, starRingEnd ℂ (IIIa.LMPd 0 (IIIa.LMPd 0 u_i) x) * u_i x) +
          (∫ x in B0579.cell p.c, starRingEnd ℂ (IIIa.LMPd 1 (IIIa.LMPd 1 u_i) x) * u_i x)) := by
      rw [← integral_add hi0 hi1, ← integral_const_mul]
      refine setIntegral_congr_fun (B0579.measurableSet_cell p.c) fun x _ => ?_
      rw [congrFun hlap_eq x]
      simp only [map_mul, map_add, Complex.conj_ofReal]; ring
    rw [hsplit]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.add_re]
    nlinarith [p.ν_pos]
  -- Source pairing bound for any src ∈ {g, gq, gη}
  have src_pair_le : ∀ (src w : CProf), StronglyMeasurable src →
      MemLp (fun y => src (r, y)) 2 μc → StronglyMeasurable w →
      MemLp (fun y => w (r, y)) 2 μc → ‖fhPath p.c k w r‖ ^ 2 ≤ B ^ 2 →
      ∀ i : Fin 2,
        (∫ x in B0579.cell p.c,
          starRingEnd ℂ (fhField p.c k src r x i) * fhField p.c k w r x i).re ≤
        ‖profPath p.c src r‖ * B := by
    intro src w hsrc hmsrc hw hmw hBw i
    have hcsrc := cprof_slice_cellL2 hsrc hmsrc
    obtain ⟨hm_u, hsq_u⟩ := comp_sq_B w hw hmw hBw i
    have hm_s := (fhJs_contr hc k (hcsrc i)).1
    have hsq_s : ∫ x in B0579.cell p.c, ‖fhField p.c k src r x i‖ ^ 2 ≤ ‖profPath p.c src r‖ ^ 2 := by
      refine ((fhJs_contr hc k (hcsrc i)).2).trans ?_
      unfold profPath; rw [norm_lmPath_sq_eq hcsrc]
      exact Finset.single_le_sum (f := fun m : Fin 2 => ∫ y in B0579.cell p.c, ‖src (r, y) m‖ ^ 2)
        (fun _ _ => integral_nonneg fun _ => sq_nonneg _) (Finset.mem_univ i)
    exact (le_abs_self _).trans
      (re_conj_mul_integral_le (norm_nonneg _) hB0 hm_s hm_u hsq_s hsq_u)
  -- Train slice bounds at r
  obtain ⟨Mv, hMv_pos, hMv⟩ := IIIa.AdvectionEnergyAux.trainVel_bound_le p.train htr hr0
  have hv_sm : ∀ l : Fin 2, ContDiff ℝ ∞ (fun y => p.train.v r y l) :=
    fun l => IIIa.AdvectionEnergyAux.contDiff_train_comp p.train hr0 l
  have hv_per : ∀ (l : Fin 2) (y : B0579.Plane),
      p.train.v r (y.1 + p.c, y.2) l = p.train.v r y l :=
    fun l y => congrArg (fun v => v l) (p.train.isTrain.periodic_v r hr0 y)
  have hv_bdd : ∀ (l : Fin 2) (y : B0579.Plane), |p.train.v r y l| ≤ Mv := by
    intro l y
    have := hMv r le_rfl y l
    simpa [IIIa.trainVel, hr0, Real.norm_eq_abs] using this
  have hv_lip : ∀ (l : Fin 2) (y : B0579.Plane),
      ‖fderiv ℝ (fun w => p.train.v r w l) y‖ ≤ S := fun l y =>
    (fderiv_train_comp_norm_le p.train htr hr0 l y).trans
      (le_add_of_nonneg_right ENNReal.toReal_nonneg)
  have hd1_bdd : ∀ (m i : Fin 2) (y : B0579.Plane),
      |trD1 p.train (![(1, 0), (0, 1)] m) r y i| ≤ S := by
    intro m i y
    fin_cases m
    · exact (trD1_bound_of_supNormD_one p.train htr hr0 le_rfl y i).1.trans
        (le_add_of_nonneg_right ENNReal.toReal_nonneg)
    · exact (trD1_bound_of_supNormD_one p.train htr hr0 le_rfl y i).2.trans
        (le_add_of_nonneg_right ENNReal.toReal_nonneg)
  have hd1_sm_per : ∀ (m j i : Fin 2),
      ContDiff ℝ ∞ (fun y => trD1 p.train (![(1, 0), (0, 1)] m) r y i) ∧
      (∀ y, trD1 p.train (![(1, 0), (0, 1)] m) r (y.1 + p.c, y.2) i =
        trD1 p.train (![(1, 0), (0, 1)] m) r y i) ∧
      ∀ z, |B0579.pd j (fun y => trD1 p.train (![(1, 0), (0, 1)] m) r y i) z| ≤ S := by
    intro m j i
    have hd_norm : ‖(![(1, (0 : ℝ)), ((0 : ℝ), 1)] m : B0579.Plane)‖ = 1 := by
      fin_cases m <;> simp [Prod.norm_def]
    obtain ⟨h1, h2, h3⟩ := trD1_smooth_per_pd_bound p.train htr hr0 le_rfl hd_norm j i
    exact ⟨h1, h2, fun z => (h3 z).trans (le_add_of_nonneg_left ENNReal.toReal_nonneg)⟩
  -- Term m = 0 bound (per component i : Fin 2)
  have hZ0_comp : ∀ i : Fin 2,
      (∫ x in B0579.cell p.c,
        starRingEnd ℂ (rawZ0 p T g z₂ zq₂ zη₂ k r x i) * fhField p.c k z₂ r x i).re ≤
      (4 * fhCommConst * S * W + ‖profPath p.c g r‖) * B := by
    intro i
    let u0_i : B0579.Plane → ℂ := fun x => fhField p.c k z₂ r x i
    obtain ⟨hm_u0, hsq_u0⟩ := comp_sq_B z₂ hz hmz hB_z i
    have hu0_sm : ContDiff ℝ ∞ u0_i := perOp_contDiff hc hK (hcz i)
    have hu0_per : ∀ x, u0_i (x.1 + p.c, x.2) = u0_i x := fun x => perOp_periodic hc _ _ x
    have hpd_u0 : ∀ l : Fin 2, IIIa.LMPd l u0_i =
        fun x => fhJs p.c k (fun y => (![zq₂, zη₂] l) (r, y) i) x := by
      intro l; funext x
      dsimp only [u0_i, fhField, fhJs]
      rw [perOp_pd hc hK (hcz i) l x]
      fin_cases l
      · exact perOp_commute hc hK (hw_z i).1 x
      · exact perOp_commute hc hK (hw_z i).2 x
    have hm_pd0 : MemLp (IIIa.LMPd 0 u0_i) 2 μc := by
      rw [hpd_u0 0]; exact (fhJs_contr hc k (hczq i)).1
    have hm_pd1 : MemLp (IIIa.LMPd 1 u0_i) 2 μc := by
      rw [hpd_u0 1]; exact (fhJs_contr hc k (hczη i)).1
    have htr_zero := (transport_re_eq_zero hc p.train htr hr0 hu0_sm hu0_per hm_u0 hm_pd0 hm_pd1).2
    -- Commutator pieces R0_0, R0_1
    obtain ⟨hm_R00, hsq_R00⟩ := fhJs_comm_zero_bound hc hS0 hMv_pos.le k (hv_sm 0) (hv_per 0)
      (hv_bdd 0) (hv_lip 0) (hczq i)
    obtain ⟨hm_R01, hsq_R01⟩ := fhJs_comm_zero_bound hc hS0 hMv_pos.le k (hv_sm 1) (hv_per 1)
      (hv_bdd 1) (hv_lip 1) (hczη i)
    have hR_CF : fhR p.c k ≤ fhCommConst := (fhR_le_half p.c k).trans (by linarith)
    have hsq_R00' : ∫ x in B0579.cell p.c,
        ‖fhJs p.c k (fun y => ((p.train.v r y 0 : ℝ) : ℂ) * zq₂ (r, y) i) x -
          ((p.train.v r x 0 : ℝ) : ℂ) * fhJs p.c k (fun y => zq₂ (r, y) i) x‖ ^ 2 ≤
        (fhCommConst * S * W) ^ 2 := by
      have h1 : (fhR p.c k * S) ^ 2 ≤ (fhCommConst * S) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (fhR_pos p.c k).le hS0)
          (mul_le_mul_of_nonneg_right hR_CF hS0) 2
      have h2 := hW_zq i
      have h3 : (fhCommConst * S) ^ 2 * W ^ 2 = (fhCommConst * S * W) ^ 2 := by ring
      exact hsq_R00.trans ((mul_le_mul h1 h2 (integral_nonneg fun _ => sq_nonneg _)
        (sq_nonneg _)).trans (le_of_eq h3))
    have hsq_R01' : ∫ x in B0579.cell p.c,
        ‖fhJs p.c k (fun y => ((p.train.v r y 1 : ℝ) : ℂ) * zη₂ (r, y) i) x -
          ((p.train.v r x 1 : ℝ) : ℂ) * fhJs p.c k (fun y => zη₂ (r, y) i) x‖ ^ 2 ≤
        (fhCommConst * S * W) ^ 2 := by
      have h1 : (fhR p.c k * S) ^ 2 ≤ (fhCommConst * S) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (fhR_pos p.c k).le hS0)
          (mul_le_mul_of_nonneg_right hR_CF hS0) 2
      have h2 := hW_zη i
      have h3 : (fhCommConst * S) ^ 2 * W ^ 2 = (fhCommConst * S * W) ^ 2 := by ring
      exact hsq_R01.trans ((mul_le_mul h1 h2 (integral_nonneg fun _ => sq_nonneg _)
        (sq_nonneg _)).trans (le_of_eq h3))
    -- Stretching pieces S0, S1
    have stretch_b : ∀ m : Fin 2,
        let f_m : B0579.Plane → ℂ := fun x =>
          fhJs p.c k (fun y => ((trD1 p.train (![(1, 0), (0, 1)] m) r y i : ℝ) : ℂ) * z₂ (r, y) m) x
        MemLp f_m 2 μc ∧ ∫ x in B0579.cell p.c, ‖f_m x‖ ^ 2 ≤ (fhCommConst * S * W) ^ 2 := by
      intro m
      obtain ⟨hm_mul, hsq_mul⟩ := memLp_bdd_real_mul hS0 (hd1_sm_per m 0 i).1.continuous
        (hd1_bdd m i) (hcz m)
      obtain ⟨hm_j, hsq_j⟩ := fhJs_contr hc k hm_mul
      refine ⟨hm_j, hsq_j.trans (hsq_mul.trans ?_)⟩
      have h1 : S ≤ fhCommConst * S := le_mul_of_one_le_left hS0 hCF1
      have h2 : S ^ 2 ≤ (fhCommConst * S) ^ 2 := pow_le_pow_left₀ hS0 h1 2
      have h3 : (fhCommConst * S) ^ 2 * W ^ 2 = (fhCommConst * S * W) ^ 2 := by ring
      exact (mul_le_mul h2 (hW_z m) (integral_nonneg fun _ => sq_nonneg _) (sq_nonneg _)).trans
        (le_of_eq h3)
    obtain ⟨hm_S0, hsq_S0⟩ := stretch_b 0
    obtain ⟨hm_S1, hsq_S1⟩ := stretch_b 1
    -- Algebraic decomposition of fhField bvT
    let tr_term : B0579.Plane → ℂ := fun x =>
      ((p.train.v r x 0 : ℝ) : ℂ) * IIIa.LMPd 0 u0_i x +
      ((p.train.v r x 1 : ℝ) : ℂ) * IIIa.LMPd 1 u0_i x
    let R00 : B0579.Plane → ℂ := fun x =>
      fhJs p.c k (fun y => ((p.train.v r y 0 : ℝ) : ℂ) * zq₂ (r, y) i) x -
        ((p.train.v r x 0 : ℝ) : ℂ) * fhJs p.c k (fun y => zq₂ (r, y) i) x
    let R01 : B0579.Plane → ℂ := fun x =>
      fhJs p.c k (fun y => ((p.train.v r y 1 : ℝ) : ℂ) * zη₂ (r, y) i) x -
        ((p.train.v r x 1 : ℝ) : ℂ) * fhJs p.c k (fun y => zη₂ (r, y) i) x
    let St0 : B0579.Plane → ℂ := fun x =>
      fhJs p.c k (fun y => ((trD1 p.train (1, 0) r y i : ℝ) : ℂ) * z₂ (r, y) 0) x
    let St1 : B0579.Plane → ℂ := fun x =>
      fhJs p.c k (fun y => ((trD1 p.train (0, 1) r y i : ℝ) : ℂ) * z₂ (r, y) 1) x
    have hbv_decomp : ∀ x, fhField p.c k (tailInd T (flatBv p.train z₂ zq₂ zη₂)) r x i =
        tr_term x + R00 x + R01 x + St0 x + St1 x := by
      intro x
      have hbv_pt : (fun y => tailInd T (flatBv p.train z₂ zq₂ zη₂) (r, y) i) = fun y =>
          (((p.train.v r y 0 : ℝ) : ℂ) * zq₂ (r, y) i +
            ((p.train.v r y 1 : ℝ) : ℂ) * zη₂ (r, y) i) +
          (((trD1 p.train (1, 0) r y i : ℝ) : ℂ) * z₂ (r, y) 0 +
            ((trD1 p.train (0, 1) r y i : ℝ) : ℂ) * z₂ (r, y) 1) := by
        funext y; simp only [tailInd, hrT, ↓reduceIte, FlatBvWL.flatBv_apply]; ring
      have hm1 : MemLp (fun y => ((p.train.v r y 0 : ℝ) : ℂ) * zq₂ (r, y) i) 2 μc :=
        (memLp_bdd_real_mul hMv_pos.le (hv_sm 0).continuous (hv_bdd 0) (hczq i)).1
      have hm2 : MemLp (fun y => ((p.train.v r y 1 : ℝ) : ℂ) * zη₂ (r, y) i) 2 μc :=
        (memLp_bdd_real_mul hMv_pos.le (hv_sm 1).continuous (hv_bdd 1) (hczη i)).1
      have hm3 : MemLp (fun y => ((trD1 p.train (1, 0) r y i : ℝ) : ℂ) * z₂ (r, y) 0) 2 μc :=
        (memLp_bdd_real_mul hS0 (hd1_sm_per 0 0 i).1.continuous (hd1_bdd 0 i) (hcz 0)).1
      have hm4 : MemLp (fun y => ((trD1 p.train (0, 1) r y i : ℝ) : ℂ) * z₂ (r, y) 1) 2 μc :=
        (memLp_bdd_real_mul hS0 (hd1_sm_per 1 0 i).1.continuous (hd1_bdd 1 i) (hcz 1)).1
      have hm12 : MemLp (fun y => ((p.train.v r y 0 : ℝ) : ℂ) * zq₂ (r, y) i +
          ((p.train.v r y 1 : ℝ) : ℂ) * zη₂ (r, y) i) 2 μc := hm1.add hm2
      have hm34 : MemLp (fun y => ((trD1 p.train (1, 0) r y i : ℝ) : ℂ) * z₂ (r, y) 0 +
          ((trD1 p.train (0, 1) r y i : ℝ) : ℂ) * z₂ (r, y) 1) 2 μc := hm3.add hm4
      dsimp only [fhField, fhJs]
      rw [hbv_pt, perOp_add hc hK hm12 hm34 x,
        perOp_add hc hK hm1 hm2 x, perOp_add hc hK hm3 hm4 x]
      dsimp only [tr_term, R00, R01, St0, St1, fhJs]
      rw [hpd_u0 0, hpd_u0 1]
      dsimp only [fhJs, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    have hm_tr : MemLp tr_term 2 μc :=
      ((memLp_bdd_real_mul hMv_pos.le (hv_sm 0).continuous (hv_bdd 0) hm_pd0).1).add
        ((memLp_bdd_real_mul hMv_pos.le (hv_sm 1).continuous (hv_bdd 1) hm_pd1).1)
    have hm_lap : MemLp (fun x => (p.ν : ℂ) * fhLap p.c k z₂ r x i) 2 μc :=
      ((perOp_memLp hc ((hK.pd 0).pd 0) (hcz i)).add
        (perOp_memLp hc ((hK.pd 1).pd 1) (hcz i))).const_mul _
    have hm_g_i : MemLp (fun x => fhField p.c k g r x i) 2 μc := (fhJs_contr hc k (hcg i)).1
    have pair_re_lin : ∀ {f1 f2 : B0579.Plane → ℂ}, MemLp f1 2 μc → MemLp f2 2 μc →
        (∫ x in B0579.cell p.c, starRingEnd ℂ (f1 x + f2 x) * u0_i x).re =
        (∫ x in B0579.cell p.c, starRingEnd ℂ (f1 x) * u0_i x).re +
          (∫ x in B0579.cell p.c, starRingEnd ℂ (f2 x) * u0_i x).re := by
      intro f1 f2 hf1 hf2
      have hi1 := IIIa.integrable_conj_mul_of_memLp hf1 hm_u0
      have hi2 := IIIa.integrable_conj_mul_of_memLp hf2 hm_u0
      have heq : (fun x => starRingEnd ℂ (f1 x + f2 x) * u0_i x) =
          fun x => starRingEnd ℂ (f1 x) * u0_i x + starRingEnd ℂ (f2 x) * u0_i x := by
        funext x; rw [map_add, add_mul]
      rw [heq, integral_add hi1 hi2, Complex.add_re]
    have pair_re_sub : ∀ {f1 f2 : B0579.Plane → ℂ}, MemLp f1 2 μc → MemLp f2 2 μc →
        (∫ x in B0579.cell p.c, starRingEnd ℂ (f1 x - f2 x) * u0_i x).re =
        (∫ x in B0579.cell p.c, starRingEnd ℂ (f1 x) * u0_i x).re -
          (∫ x in B0579.cell p.c, starRingEnd ℂ (f2 x) * u0_i x).re := by
      intro f1 f2 hf1 hf2
      have hi1 := IIIa.integrable_conj_mul_of_memLp hf1 hm_u0
      have hi2 := IIIa.integrable_conj_mul_of_memLp hf2 hm_u0
      have heq : (fun x => starRingEnd ℂ (f1 x - f2 x) * u0_i x) =
          fun x => starRingEnd ℂ (f1 x) * u0_i x - starRingEnd ℂ (f2 x) * u0_i x := by
        funext x; rw [map_sub, sub_mul]
      rw [heq, integral_sub hi1 hi2, Complex.sub_re]
    have hm_R00' : MemLp R00 2 μc := hm_R00
    have hm_R01' : MemLp R01 2 μc := hm_R01
    have hm_St0 : MemLp St0 2 μc := hm_S0
    have hm_St1 : MemLp St1 2 μc := hm_S1
    have hsq_R00_b : ∫ x in B0579.cell p.c, ‖R00 x‖ ^ 2 ≤ (fhCommConst * S * W) ^ 2 := hsq_R00'
    have hsq_R01_b : ∫ x in B0579.cell p.c, ‖R01 x‖ ^ 2 ≤ (fhCommConst * S * W) ^ 2 := hsq_R01'
    have hsq_St0 : ∫ x in B0579.cell p.c, ‖St0 x‖ ^ 2 ≤ (fhCommConst * S * W) ^ 2 := hsq_S0
    have hsq_St1 : ∫ x in B0579.cell p.c, ‖St1 x‖ ^ 2 ≤ (fhCommConst * S * W) ^ 2 := hsq_S1
    have hm_bv : MemLp (fun x => tr_term x + R00 x + R01 x + St0 x + St1 x) 2 μc :=
      (((hm_tr.add hm_R00').add hm_R01').add hm_St0).add hm_St1
    have hraw_eq : ∀ x, rawZ0 p T g z₂ zq₂ zη₂ k r x i =
        ((p.ν : ℂ) * fhLap p.c k z₂ r x i -
          (tr_term x + R00 x + R01 x + St0 x + St1 x)) + fhField p.c k g r x i := by
      intro x; dsimp only [rawZ0]; rw [hbv_decomp x]
    have hsplit : (∫ x in B0579.cell p.c,
          starRingEnd ℂ (rawZ0 p T g z₂ zq₂ zη₂ k r x i) * u0_i x).re =
        (∫ x in B0579.cell p.c, starRingEnd ℂ ((p.ν : ℂ) * fhLap p.c k z₂ r x i) * u0_i x).re -
        ((∫ x in B0579.cell p.c, starRingEnd ℂ (tr_term x) * u0_i x).re +
          (∫ x in B0579.cell p.c, starRingEnd ℂ (R00 x) * u0_i x).re +
          (∫ x in B0579.cell p.c, starRingEnd ℂ (R01 x) * u0_i x).re +
          (∫ x in B0579.cell p.c, starRingEnd ℂ (St0 x) * u0_i x).re +
          (∫ x in B0579.cell p.c, starRingEnd ℂ (St1 x) * u0_i x).re) +
        (∫ x in B0579.cell p.c, starRingEnd ℂ (fhField p.c k g r x i) * u0_i x).re := by
      simp_rw [hraw_eq]
      have h1 := pair_re_lin (f1 := fun x => (p.ν : ℂ) * fhLap p.c k z₂ r x i -
        (tr_term x + R00 x + R01 x + St0 x + St1 x)) (hm_lap.sub hm_bv) hm_g_i
      have h2 := pair_re_sub hm_lap hm_bv
      have h3 := pair_re_lin (f1 := fun x => tr_term x + R00 x + R01 x + St0 x)
        (((hm_tr.add hm_R00').add hm_R01').add hm_St0) hm_St1
      have h4 := pair_re_lin (f1 := fun x => tr_term x + R00 x + R01 x)
        ((hm_tr.add hm_R00').add hm_R01') hm_St0
      have h5 := pair_re_lin (f1 := fun x => tr_term x + R00 x) (hm_tr.add hm_R00') hm_R01'
      have h6 := pair_re_lin hm_tr hm_R00'
      linarith
    have hvisc0 : (∫ x in B0579.cell p.c,
        starRingEnd ℂ ((p.ν : ℂ) * fhLap p.c k z₂ r x i) * u0_i x).re ≤ 0 :=
      visc_le_zero z₂ hz hmz i
    have hsrc0 : (∫ x in B0579.cell p.c,
        starRingEnd ℂ (fhField p.c k g r x i) * u0_i x).re ≤ ‖profPath p.c g r‖ * B :=
      src_pair_le g z₂ hg_src.sm_g hmg hz hmz hB_z i
    have htr0 : (∫ x in B0579.cell p.c, starRingEnd ℂ (tr_term x) * u0_i x).re = 0 := htr_zero
    have hCS_nn : 0 ≤ fhCommConst * S * W := mul_nonneg (mul_nonneg hCF_pos hS0) hW0
    have hb1 := (neg_le_abs _).trans
      (re_conj_mul_integral_le hCS_nn hB0 hm_R00' hm_u0 hsq_R00_b hsq_u0)
    have hb2 := (neg_le_abs _).trans
      (re_conj_mul_integral_le hCS_nn hB0 hm_R01' hm_u0 hsq_R01_b hsq_u0)
    have hb3 := (neg_le_abs _).trans
      (re_conj_mul_integral_le hCS_nn hB0 hm_St0 hm_u0 hsq_St0 hsq_u0)
    have hb4 := (neg_le_abs _).trans
      (re_conj_mul_integral_le hCS_nn hB0 hm_St1 hm_u0 hsq_St1 hsq_u0)
    have hrhs : 4 * ((fhCommConst * S * W) * B) + ‖profPath p.c g r‖ * B =
        (4 * fhCommConst * S * W + ‖profPath p.c g r‖) * B := by ring
    change (∫ x in B0579.cell p.c,
        starRingEnd ℂ (rawZ0 p T g z₂ zq₂ zη₂ k r x i) * u0_i x).re ≤
      (4 * fhCommConst * S * W + ‖profPath p.c g r‖) * B
    linarith
  -- Term m = j + 1 bound (per j : Fin 2 and i : Fin 2)
  have hZj_comp : ∀ (j i : Fin 2),
      (∫ x in B0579.cell p.c,
        starRingEnd ℂ (rawZj p T gq gη z₂ zq₂ zη₂ k j r x i) *
          fhField p.c k (![zq₂, zη₂] j) r x i).re ≤
      (6 * fhCommConst * S * W + ‖profPath p.c (![gq, gη] j) r‖) * B := by
    intro j i
    let wj : CProf := ![zq₂, zη₂] j
    let gj : CProf := ![gq, gη] j
    have hwj_sm : StronglyMeasurable wj := by dsimp [wj]; fin_cases j <;> assumption
    have hmwj : MemLp (fun y => wj (r, y)) 2 μc := by dsimp [wj]; fin_cases j <;> assumption
    have hBwj : ‖fhPath p.c k wj r‖ ^ 2 ≤ B ^ 2 := by dsimp [wj]; fin_cases j <;> assumption
    have hgj_sm : StronglyMeasurable gj := by
      dsimp [gj]; fin_cases j
      · exact hg_src.sm_gq
      · exact hg_src.sm_gη
    have hmgj : MemLp (fun y => gj (r, y)) 2 μc := by dsimp [gj]; fin_cases j <;> assumption
    have hcwj := cprof_slice_cellL2 hwj_sm hmwj
    have hcgj := cprof_slice_cellL2 hgj_sm hmgj
    have hW_wj : ∀ m : Fin 2, ∫ y in B0579.cell p.c, ‖wj (r, y) m‖ ^ 2 ≤ W ^ 2 := by
      intro m; dsimp [wj]; fin_cases j
      · exact hW_zq m
      · exact hW_zη m
    have hw_z_j : ∀ m : Fin 2,
        IIIa.HasWeakCellDerivC p.c j (fun y => z₂ (r, y) m) (fun y => wj (r, y) m) := by
      intro m; dsimp [wj]; fin_cases j
      · exact (hw_z m).1
      · exact (hw_z m).2
    let uj_i : B0579.Plane → ℂ := fun x => fhField p.c k wj r x i
    obtain ⟨hm_uj, hsq_uj⟩ := comp_sq_B wj hwj_sm hmwj hBwj i
    have huj_sm : ContDiff ℝ ∞ uj_i := perOp_contDiff hc hK (hcwj i)
    have huj_per : ∀ x, uj_i (x.1 + p.c, x.2) = uj_i x := fun x => perOp_periodic hc _ _ x
    have hcomm_jl : ∀ l : Fin 2,
        IIIa.LMPd j (fhJs p.c k (fun y => (![zq₂, zη₂] l) (r, y) i)) = IIIa.LMPd l uj_i := by
      intro l; funext x
      have hcwl : MemLp (fun y => (![zq₂, zη₂] l) (r, y) i) 2 μc := by
        fin_cases l
        · exact hczq i
        · exact hczη i
      have hwl : IIIa.HasWeakCellDerivC p.c l
          (fun y => z₂ (r, y) i) (fun y => (![zq₂, zη₂] l) (r, y) i) := by
        fin_cases l
        · exact (hw_z i).1
        · exact (hw_z i).2
      have hkern_comm : B0579.pd l (B0579.pd j (fhRho p.c k)) =
          B0579.pd j (B0579.pd l (fhRho p.c k)) := funext (pd_comm_of_smooth hK.1 l j)
      dsimp only [uj_i, fhField, fhJs]
      rw [perOp_pd hc hK hcwl j x, ← perOp_commute hc (hK.pd j) hwl x, hkern_comm,
        perOp_commute hc (hK.pd l) (hw_z_j i) x, perOp_pd hc hK (hcwj i) l x]
    have hm_pd0 : MemLp (IIIa.LMPd 0 uj_i) 2 μc := by
      dsimp only [uj_i, fhField]
      have e : IIIa.LMPd 0 (fhJs p.c k (fun y => wj (r, y) i)) =
          perOp p.c (B0579.pd 0 (fhRho p.c k)) (fun y => wj (r, y) i) :=
        funext (perOp_pd hc hK (hcwj i) 0)
      rw [e]; exact perOp_memLp hc (hK.pd 0) (hcwj i)
    have hm_pd1 : MemLp (IIIa.LMPd 1 uj_i) 2 μc := by
      dsimp only [uj_i, fhField]
      have e : IIIa.LMPd 1 (fhJs p.c k (fun y => wj (r, y) i)) =
          perOp p.c (B0579.pd 1 (fhRho p.c k)) (fun y => wj (r, y) i) :=
        funext (perOp_pd hc hK (hcwj i) 1)
      rw [e]; exact perOp_memLp hc (hK.pd 1) (hcwj i)
    have htr_zero := (transport_re_eq_zero hc p.train htr hr0 huj_sm huj_per hm_uj hm_pd0 hm_pd1).2
    -- First-order commutators R1_0, R1_1
    obtain ⟨hm_R10, hsq_R10⟩ := fhJs_comm_pd_bound hc hS0 hMv_pos.le k j (hv_sm 0) (hv_per 0)
      (hv_bdd 0) (hv_lip 0) (hczq i)
    obtain ⟨hm_R11, hsq_R11⟩ := fhJs_comm_pd_bound hc hS0 hMv_pos.le k j (hv_sm 1) (hv_per 1)
      (hv_bdd 1) (hv_lip 1) (hczη i)
    have hCS_nn : 0 ≤ fhCommConst * S * W := mul_nonneg (mul_nonneg hCF_pos hS0) hW0
    have hsq_R10' : ∫ x in B0579.cell p.c,
        ‖IIIa.LMPd j (fhJs p.c k (fun y => ((p.train.v r y 0 : ℝ) : ℂ) * zq₂ (r, y) i)) x -
          ((p.train.v r x 0 : ℝ) : ℂ) *
            IIIa.LMPd j (fhJs p.c k (fun y => zq₂ (r, y) i)) x‖ ^ 2 ≤
        (fhCommConst * S * W) ^ 2 := by
      have h3 : (fhCommConst * S) ^ 2 * W ^ 2 = (fhCommConst * S * W) ^ 2 := by ring
      exact hsq_R10.trans ((mul_le_mul_of_nonneg_left (hW_zq i) (sq_nonneg _)).trans (le_of_eq h3))
    have hsq_R11' : ∫ x in B0579.cell p.c,
        ‖IIIa.LMPd j (fhJs p.c k (fun y => ((p.train.v r y 1 : ℝ) : ℂ) * zη₂ (r, y) i)) x -
          ((p.train.v r x 1 : ℝ) : ℂ) *
            IIIa.LMPd j (fhJs p.c k (fun y => zη₂ (r, y) i)) x‖ ^ 2 ≤
        (fhCommConst * S * W) ^ 2 := by
      have h3 : (fhCommConst * S) ^ 2 * W ^ 2 = (fhCommConst * S * W) ^ 2 := by ring
      exact hsq_R11.trans ((mul_le_mul_of_nonneg_left (hW_zη i) (sq_nonneg _)).trans (le_of_eq h3))
    -- Differentiated stretching terms: Leibniz split into D²v * z₂ + Dv * wj
    have stretch_pd : ∀ m : Fin 2,
        let b_m : B0579.Plane → ℝ := fun y => trD1 p.train (![(1, 0), (0, 1)] m) r y i
        let A_m : B0579.Plane → ℂ :=
          fhJs p.c k (fun y => ((B0579.pd j b_m y : ℝ) : ℂ) * z₂ (r, y) m)
        let B_m : B0579.Plane → ℂ :=
          fhJs p.c k (fun y => ((b_m y : ℝ) : ℂ) * wj (r, y) m)
        (∀ x, perOp p.c (B0579.pd j (fhRho p.c k))
          (fun y => ((b_m y : ℝ) : ℂ) * z₂ (r, y) m) x = A_m x + B_m x) ∧
        MemLp A_m 2 μc ∧ MemLp B_m 2 μc ∧
        ∫ x in B0579.cell p.c, ‖A_m x‖ ^ 2 ≤ (fhCommConst * S * W) ^ 2 ∧
        ∫ x in B0579.cell p.c, ‖B_m x‖ ^ 2 ≤ (fhCommConst * S * W) ^ 2 := by
      intro m
      obtain ⟨hb_sm, hb_per, hdb_bdd⟩ := hd1_sm_per m j i
      have hdb_cont : Continuous (B0579.pd j (fun y => trD1 p.train (![(1, 0), (0, 1)] m) r y i)) :=
        (((contDiff_infty_iff_fderiv.1 hb_sm).2).clm_apply contDiff_const).continuous
      have hw_leib := hasWeakCellDerivC_smooth_mul hb_sm hb_per (hcz m) (hcwj m) (hw_z_j m)
      obtain ⟨hm_db_z, hsq_db_z⟩ := memLp_bdd_real_mul hS0 hdb_cont hdb_bdd (hcz m)
      obtain ⟨hm_b_wj, hsq_b_wj⟩ := memLp_bdd_real_mul hS0 hb_sm.continuous (hd1_bdd m i) (hcwj m)
      obtain ⟨hm_Am, hsq_Am⟩ := fhJs_contr hc k hm_db_z
      obtain ⟨hm_Bm, hsq_Bm⟩ := fhJs_contr hc k hm_b_wj
      have hS_CF : S ^ 2 ≤ (fhCommConst * S) ^ 2 :=
        pow_le_pow_left₀ hS0 (le_mul_of_one_le_left hS0 hCF1) 2
      have h3 : (fhCommConst * S) ^ 2 * W ^ 2 = (fhCommConst * S * W) ^ 2 := by ring
      refine ⟨fun x => ?_, hm_Am, hm_Bm,
        hsq_Am.trans (hsq_db_z.trans ((mul_le_mul hS_CF (hW_z m)
          (integral_nonneg fun _ => sq_nonneg _) (sq_nonneg _)).trans (le_of_eq h3))),
        hsq_Bm.trans (hsq_b_wj.trans ((mul_le_mul hS_CF (hW_wj m)
          (integral_nonneg fun _ => sq_nonneg _) (sq_nonneg _)).trans (le_of_eq h3)))⟩
      rw [perOp_commute hc hK hw_leib x, perOp_add hc hK hm_db_z hm_b_wj x]
      rfl
    obtain ⟨heq_st0, hm_A0, hm_B0, hsq_A0, hsq_B0⟩ := stretch_pd 0
    obtain ⟨heq_st1, hm_A1, hm_B1, hsq_A1, hsq_B1⟩ := stretch_pd 1
    let tr_term : B0579.Plane → ℂ := fun x =>
      ((p.train.v r x 0 : ℝ) : ℂ) * IIIa.LMPd 0 uj_i x +
      ((p.train.v r x 1 : ℝ) : ℂ) * IIIa.LMPd 1 uj_i x
    let R10 : B0579.Plane → ℂ := fun x =>
      IIIa.LMPd j (fhJs p.c k (fun y => ((p.train.v r y 0 : ℝ) : ℂ) * zq₂ (r, y) i)) x -
        ((p.train.v r x 0 : ℝ) : ℂ) * IIIa.LMPd j (fhJs p.c k (fun y => zq₂ (r, y) i)) x
    let R11 : B0579.Plane → ℂ := fun x =>
      IIIa.LMPd j (fhJs p.c k (fun y => ((p.train.v r y 1 : ℝ) : ℂ) * zη₂ (r, y) i)) x -
        ((p.train.v r x 1 : ℝ) : ℂ) * IIIa.LMPd j (fhJs p.c k (fun y => zη₂ (r, y) i)) x
    let A0 : B0579.Plane → ℂ :=
      fhJs p.c k (fun y => ((B0579.pd j (fun w => trD1 p.train (1, 0) r w i) y : ℝ) : ℂ) * z₂ (r, y) 0)
    let B0 : B0579.Plane → ℂ :=
      fhJs p.c k (fun y => ((trD1 p.train (1, 0) r y i : ℝ) : ℂ) * wj (r, y) 0)
    let A1 : B0579.Plane → ℂ :=
      fhJs p.c k (fun y => ((B0579.pd j (fun w => trD1 p.train (0, 1) r w i) y : ℝ) : ℂ) * z₂ (r, y) 1)
    let B1 : B0579.Plane → ℂ :=
      fhJs p.c k (fun y => ((trD1 p.train (0, 1) r y i : ℝ) : ℂ) * wj (r, y) 1)
    have hbv_decomp : ∀ x, fhPd p.c k j (tailInd T (flatBv p.train z₂ zq₂ zη₂)) r x i =
        tr_term x + R10 x + R11 x + A0 x + B0 x + A1 x + B1 x := by
      intro x
      have hbv_pt : (fun y => tailInd T (flatBv p.train z₂ zq₂ zη₂) (r, y) i) = fun y =>
          (((p.train.v r y 0 : ℝ) : ℂ) * zq₂ (r, y) i +
            ((p.train.v r y 1 : ℝ) : ℂ) * zη₂ (r, y) i) +
          (((trD1 p.train (1, 0) r y i : ℝ) : ℂ) * z₂ (r, y) 0 +
            ((trD1 p.train (0, 1) r y i : ℝ) : ℂ) * z₂ (r, y) 1) := by
        funext y; simp only [tailInd, hrT, ↓reduceIte, FlatBvWL.flatBv_apply]; ring
      have hm1 : MemLp (fun y => ((p.train.v r y 0 : ℝ) : ℂ) * zq₂ (r, y) i) 2 μc :=
        (memLp_bdd_real_mul hMv_pos.le (hv_sm 0).continuous (hv_bdd 0) (hczq i)).1
      have hm2 : MemLp (fun y => ((p.train.v r y 1 : ℝ) : ℂ) * zη₂ (r, y) i) 2 μc :=
        (memLp_bdd_real_mul hMv_pos.le (hv_sm 1).continuous (hv_bdd 1) (hczη i)).1
      have hm3 : MemLp (fun y => ((trD1 p.train (1, 0) r y i : ℝ) : ℂ) * z₂ (r, y) 0) 2 μc :=
        (memLp_bdd_real_mul hS0 (hd1_sm_per 0 0 i).1.continuous (hd1_bdd 0 i) (hcz 0)).1
      have hm4 : MemLp (fun y => ((trD1 p.train (0, 1) r y i : ℝ) : ℂ) * z₂ (r, y) 1) 2 μc :=
        (memLp_bdd_real_mul hS0 (hd1_sm_per 1 0 i).1.continuous (hd1_bdd 1 i) (hcz 1)).1
      have hm12 : MemLp (fun y => ((p.train.v r y 0 : ℝ) : ℂ) * zq₂ (r, y) i +
          ((p.train.v r y 1 : ℝ) : ℂ) * zη₂ (r, y) i) 2 μc := hm1.add hm2
      have hm34 : MemLp (fun y => ((trD1 p.train (1, 0) r y i : ℝ) : ℂ) * z₂ (r, y) 0 +
          ((trD1 p.train (0, 1) r y i : ℝ) : ℂ) * z₂ (r, y) 1) 2 μc := hm3.add hm4
      have hst0 : perOp p.c (B0579.pd j (fhRho p.c k))
          (fun y => ((trD1 p.train (1, 0) r y i : ℝ) : ℂ) * z₂ (r, y) 0) x = A0 x + B0 x :=
        heq_st0 x
      have hst1 : perOp p.c (B0579.pd j (fhRho p.c k))
          (fun y => ((trD1 p.train (0, 1) r y i : ℝ) : ℂ) * z₂ (r, y) 1) x = A1 x + B1 x :=
        heq_st1 x
      dsimp only [fhPd]
      rw [hbv_pt, perOp_add hc (hK.pd j) hm12 hm34 x,
        perOp_add hc (hK.pd j) hm1 hm2 x, perOp_add hc (hK.pd j) hm3 hm4 x,
        ← perOp_pd hc hK hm1 j x, ← perOp_pd hc hK hm2 j x,
        hst0, hst1]
      dsimp only [tr_term, R10, R11, fhJs]
      rw [← hcomm_jl 0, ← hcomm_jl 1]
      dsimp only [fhJs, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    have hm_tr : MemLp tr_term 2 μc :=
      ((memLp_bdd_real_mul hMv_pos.le (hv_sm 0).continuous (hv_bdd 0) hm_pd0).1).add
        ((memLp_bdd_real_mul hMv_pos.le (hv_sm 1).continuous (hv_bdd 1) hm_pd1).1)
    have hm_lap : MemLp (fun x => (p.ν : ℂ) * fhLap p.c k wj r x i) 2 μc :=
      ((perOp_memLp hc ((hK.pd 0).pd 0) (hcwj i)).add
        (perOp_memLp hc ((hK.pd 1).pd 1) (hcwj i))).const_mul _
    have hm_gj_i : MemLp (fun x => fhField p.c k gj r x i) 2 μc := (fhJs_contr hc k (hcgj i)).1
    have pair_re_lin : ∀ {f1 f2 : B0579.Plane → ℂ}, MemLp f1 2 μc → MemLp f2 2 μc →
        (∫ x in B0579.cell p.c, starRingEnd ℂ (f1 x + f2 x) * uj_i x).re =
        (∫ x in B0579.cell p.c, starRingEnd ℂ (f1 x) * uj_i x).re +
          (∫ x in B0579.cell p.c, starRingEnd ℂ (f2 x) * uj_i x).re := by
      intro f1 f2 hf1 hf2
      have hi1 := IIIa.integrable_conj_mul_of_memLp hf1 hm_uj
      have hi2 := IIIa.integrable_conj_mul_of_memLp hf2 hm_uj
      have heq : (fun x => starRingEnd ℂ (f1 x + f2 x) * uj_i x) =
          fun x => starRingEnd ℂ (f1 x) * uj_i x + starRingEnd ℂ (f2 x) * uj_i x := by
        funext x; rw [map_add, add_mul]
      rw [heq, integral_add hi1 hi2, Complex.add_re]
    have pair_re_sub : ∀ {f1 f2 : B0579.Plane → ℂ}, MemLp f1 2 μc → MemLp f2 2 μc →
        (∫ x in B0579.cell p.c, starRingEnd ℂ (f1 x - f2 x) * uj_i x).re =
        (∫ x in B0579.cell p.c, starRingEnd ℂ (f1 x) * uj_i x).re -
          (∫ x in B0579.cell p.c, starRingEnd ℂ (f2 x) * uj_i x).re := by
      intro f1 f2 hf1 hf2
      have hi1 := IIIa.integrable_conj_mul_of_memLp hf1 hm_uj
      have hi2 := IIIa.integrable_conj_mul_of_memLp hf2 hm_uj
      have heq : (fun x => starRingEnd ℂ (f1 x - f2 x) * uj_i x) =
          fun x => starRingEnd ℂ (f1 x) * uj_i x - starRingEnd ℂ (f2 x) * uj_i x := by
        funext x; rw [map_sub, sub_mul]
      rw [heq, integral_sub hi1 hi2, Complex.sub_re]
    have hm_R10' : MemLp R10 2 μc := hm_R10
    have hm_R11' : MemLp R11 2 μc := hm_R11
    have hm_A0' : MemLp A0 2 μc := hm_A0
    have hm_B0' : MemLp B0 2 μc := hm_B0
    have hm_A1' : MemLp A1 2 μc := hm_A1
    have hm_B1' : MemLp B1 2 μc := hm_B1
    have hsq_R10_b : ∫ x in B0579.cell p.c, ‖R10 x‖ ^ 2 ≤ (fhCommConst * S * W) ^ 2 := hsq_R10'
    have hsq_R11_b : ∫ x in B0579.cell p.c, ‖R11 x‖ ^ 2 ≤ (fhCommConst * S * W) ^ 2 := hsq_R11'
    have hsq_A0' : ∫ x in B0579.cell p.c, ‖A0 x‖ ^ 2 ≤ (fhCommConst * S * W) ^ 2 := hsq_A0
    have hsq_B0' : ∫ x in B0579.cell p.c, ‖B0 x‖ ^ 2 ≤ (fhCommConst * S * W) ^ 2 := hsq_B0
    have hsq_A1' : ∫ x in B0579.cell p.c, ‖A1 x‖ ^ 2 ≤ (fhCommConst * S * W) ^ 2 := hsq_A1
    have hsq_B1' : ∫ x in B0579.cell p.c, ‖B1 x‖ ^ 2 ≤ (fhCommConst * S * W) ^ 2 := hsq_B1
    have hm_bv : MemLp (fun x => tr_term x + R10 x + R11 x + A0 x + B0 x + A1 x + B1 x) 2 μc :=
      (((((hm_tr.add hm_R10').add hm_R11').add hm_A0').add hm_B0').add hm_A1').add hm_B1'
    have hraw_eq : ∀ x, rawZj p T gq gη z₂ zq₂ zη₂ k j r x i =
        ((p.ν : ℂ) * fhLap p.c k wj r x i -
          (tr_term x + R10 x + R11 x + A0 x + B0 x + A1 x + B1 x)) + fhField p.c k gj r x i := by
      intro x; dsimp only [rawZj, wj, gj]; rw [hbv_decomp x]
    have hsplit : (∫ x in B0579.cell p.c,
          starRingEnd ℂ (rawZj p T gq gη z₂ zq₂ zη₂ k j r x i) * uj_i x).re =
        (∫ x in B0579.cell p.c, starRingEnd ℂ ((p.ν : ℂ) * fhLap p.c k wj r x i) * uj_i x).re -
        ((∫ x in B0579.cell p.c, starRingEnd ℂ (tr_term x) * uj_i x).re +
          (∫ x in B0579.cell p.c, starRingEnd ℂ (R10 x) * uj_i x).re +
          (∫ x in B0579.cell p.c, starRingEnd ℂ (R11 x) * uj_i x).re +
          (∫ x in B0579.cell p.c, starRingEnd ℂ (A0 x) * uj_i x).re +
          (∫ x in B0579.cell p.c, starRingEnd ℂ (B0 x) * uj_i x).re +
          (∫ x in B0579.cell p.c, starRingEnd ℂ (A1 x) * uj_i x).re +
          (∫ x in B0579.cell p.c, starRingEnd ℂ (B1 x) * uj_i x).re) +
        (∫ x in B0579.cell p.c, starRingEnd ℂ (fhField p.c k gj r x i) * uj_i x).re := by
      simp_rw [hraw_eq]
      have h1 := pair_re_lin (f1 := fun x => (p.ν : ℂ) * fhLap p.c k wj r x i -
        (tr_term x + R10 x + R11 x + A0 x + B0 x + A1 x + B1 x)) (hm_lap.sub hm_bv) hm_gj_i
      have h2 := pair_re_sub hm_lap hm_bv
      have h3 := pair_re_lin (f1 := fun x => tr_term x + R10 x + R11 x + A0 x + B0 x + A1 x)
        (((((hm_tr.add hm_R10').add hm_R11').add hm_A0').add hm_B0').add hm_A1') hm_B1'
      have h4 := pair_re_lin (f1 := fun x => tr_term x + R10 x + R11 x + A0 x + B0 x)
        ((((hm_tr.add hm_R10').add hm_R11').add hm_A0').add hm_B0') hm_A1'
      have h5 := pair_re_lin (f1 := fun x => tr_term x + R10 x + R11 x + A0 x)
        (((hm_tr.add hm_R10').add hm_R11').add hm_A0') hm_B0'
      have h6 := pair_re_lin (f1 := fun x => tr_term x + R10 x + R11 x)
        ((hm_tr.add hm_R10').add hm_R11') hm_A0'
      have h7 := pair_re_lin (f1 := fun x => tr_term x + R10 x) (hm_tr.add hm_R10') hm_R11'
      have h8 := pair_re_lin hm_tr hm_R10'
      linarith
    have hvisc0 : (∫ x in B0579.cell p.c,
        starRingEnd ℂ ((p.ν : ℂ) * fhLap p.c k wj r x i) * uj_i x).re ≤ 0 :=
      visc_le_zero wj hwj_sm hmwj i
    have hsrc0 : (∫ x in B0579.cell p.c,
        starRingEnd ℂ (fhField p.c k gj r x i) * uj_i x).re ≤
        ‖profPath p.c (![gq, gη] j) r‖ * B :=
      src_pair_le gj wj hgj_sm hmgj hwj_sm hmwj hBwj i
    have htr0 : (∫ x in B0579.cell p.c, starRingEnd ℂ (tr_term x) * uj_i x).re = 0 := htr_zero
    have hb1 := (neg_le_abs _).trans
      (re_conj_mul_integral_le hCS_nn hB0 hm_R10' hm_uj hsq_R10_b hsq_uj)
    have hb2 := (neg_le_abs _).trans
      (re_conj_mul_integral_le hCS_nn hB0 hm_R11' hm_uj hsq_R11_b hsq_uj)
    have hb3 := (neg_le_abs _).trans
      (re_conj_mul_integral_le hCS_nn hB0 hm_A0' hm_uj hsq_A0' hsq_uj)
    have hb4 := (neg_le_abs _).trans
      (re_conj_mul_integral_le hCS_nn hB0 hm_B0' hm_uj hsq_B0' hsq_uj)
    have hb5 := (neg_le_abs _).trans
      (re_conj_mul_integral_le hCS_nn hB0 hm_A1' hm_uj hsq_A1' hsq_uj)
    have hb6 := (neg_le_abs _).trans
      (re_conj_mul_integral_le hCS_nn hB0 hm_B1' hm_uj hsq_B1' hsq_uj)
    have hrhs : 6 * ((fhCommConst * S * W) * B) + ‖profPath p.c (![gq, gη] j) r‖ * B =
        (6 * fhCommConst * S * W + ‖profPath p.c (![gq, gη] j) r‖) * B := by ring
    change (∫ x in B0579.cell p.c,
        starRingEnd ℂ (rawZj p T gq gη z₂ zq₂ zη₂ k j r x i) * uj_i x).re ≤
      (6 * fhCommConst * S * W + ‖profPath p.c (![gq, gη] j) r‖) * B
    linarith
  -- Sum over i : Fin 2 for each of the three LMIp pairings
  have lmip_re_sum : ∀ (Z u : IIIa.LMSpField), IIIa.LMCellL2 p.c Z → IIIa.LMCellL2 p.c u →
      (IIIa.LMIp p.c Z u).re =
        (∫ x in B0579.cell p.c, starRingEnd ℂ (Z x 0) * u x 0).re +
          (∫ x in B0579.cell p.c, starRingEnd ℂ (Z x 1) * u x 1).re := by
    intro Z u hZ hu
    unfold IIIa.LMIp
    simp only [Fin.sum_univ_two]
    rw [integral_add (IIIa.integrable_conj_mul_of_memLp (hZ 0) (hu 0))
      (IIIa.integrable_conj_mul_of_memLp (hZ 1) (hu 1)), Complex.add_re]
  have hcbv_r : ∀ i : Fin 2, MemLp (fun y => tailInd T (flatBv p.train z₂ zq₂ zη₂) (r, y) i) 2 μc := by
    intro i
    have hpt : (fun y => tailInd T (flatBv p.train z₂ zq₂ zη₂) (r, y) i) = fun y =>
        (((p.train.v r y 0 : ℝ) : ℂ) * zq₂ (r, y) i +
          ((p.train.v r y 1 : ℝ) : ℂ) * zη₂ (r, y) i) +
        (((trD1 p.train (1, 0) r y i : ℝ) : ℂ) * z₂ (r, y) 0 +
          ((trD1 p.train (0, 1) r y i : ℝ) : ℂ) * z₂ (r, y) 1) := by
      funext y; simp only [tailInd, hrT, ↓reduceIte, FlatBvWL.flatBv_apply]; ring
    rw [hpt]
    exact (((memLp_bdd_real_mul hMv_pos.le (hv_sm 0).continuous (hv_bdd 0) (hczq i)).1.add
      (memLp_bdd_real_mul hMv_pos.le (hv_sm 1).continuous (hv_bdd 1) (hczη i)).1).add
      ((memLp_bdd_real_mul hS0 (hd1_sm_per 0 0 i).1.continuous (hd1_bdd 0 i) (hcz 0)).1.add
        (memLp_bdd_real_mul hS0 (hd1_sm_per 1 0 i).1.continuous (hd1_bdd 1 i) (hcz 1)).1))
  have hcZ0 : IIIa.LMCellL2 p.c (rawZ0 p T g z₂ zq₂ zη₂ k r) := fun i =>
    ((((perOp_memLp hc ((hK.pd 0).pd 0) (hcz i)).add
      (perOp_memLp hc ((hK.pd 1).pd 1) (hcz i))).const_mul _).sub
      (perOp_memLp hc hK (hcbv_r i))).add (perOp_memLp hc hK (hcg i))
  have hcZq : IIIa.LMCellL2 p.c (rawZj p T gq gη z₂ zq₂ zη₂ k 0 r) := fun i =>
    ((((perOp_memLp hc ((hK.pd 0).pd 0) (hczq i)).add
      (perOp_memLp hc ((hK.pd 1).pd 1) (hczq i))).const_mul _).sub
      (perOp_memLp hc (hK.pd 0) (hcbv_r i))).add (perOp_memLp hc hK (hcgq i))
  have hcZη : IIIa.LMCellL2 p.c (rawZj p T gq gη z₂ zq₂ zη₂ k 1 r) := fun i =>
    ((((perOp_memLp hc ((hK.pd 0).pd 0) (hczη i)).add
      (perOp_memLp hc ((hK.pd 1).pd 1) (hczη i))).const_mul _).sub
      (perOp_memLp hc (hK.pd 1) (hcbv_r i))).add (perOp_memLp hc hK (hcgη i))
  rw [lmip_re_sum _ _ hcZ0 (fun i => (comp_sq_B z₂ hz hmz hB_z i).1),
    lmip_re_sum _ _ hcZq (fun i => (comp_sq_B zq₂ hzq hmzq hB_zq i).1),
    lmip_re_sum _ _ hcZη (fun i => (comp_sq_B zη₂ hzη hmzη hB_zη i).1)]
  have h00 := hZ0_comp 0; have h01 := hZ0_comp 1
  have h10 := hZj_comp 0 0; have h11 := hZj_comp 0 1
  have h20 := hZj_comp 1 0; have h21 := hZj_comp 1 1
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h10 h11 h20 h21
  have hg_sum : ‖profPath p.c g r‖ + ‖profPath p.c gq r‖ + ‖profPath p.c gη r‖ =
      (sliceH1Norm p.c g gq gη r).toReal := by
    rw [norm_profPath_eq hmg, norm_profPath_eq hmgq, norm_profPath_eq hmgη]
    unfold sliceH1Norm cylSliceL2
    rw [ENNReal.toReal_add
      (ENNReal.add_lt_top.2 ⟨hmg.eLpNorm_lt_top, hmgq.eLpNorm_lt_top⟩).ne hmgη.eLpNorm_lt_top.ne,
      ENNReal.toReal_add hmg.eLpNorm_ne_top hmgq.eLpNorm_ne_top]
  nlinarith

/-- Continuous integral Gronwall inequality on `Icc T s` (`T ≤ s`). -/
private lemma integral_gronwall_continuous {T s C₀ : ℝ} (hTs : T ≤ s) (hC₀ : 0 ≤ C₀)
    {f β : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc T s))
    (hβ_nn : ∀ r ∈ Icc T s, 0 ≤ β r) (hβ_int : IntegrableOn β (Icc T s))
    (h_ineq : ∀ t ∈ Icc T s, f t ≤ C₀ + ∫ r in Icc T t, β r * f r) :
    f s ≤ Real.exp (∫ r in Icc T s, β r) * C₀ := by
  obtain ⟨Mf0, hMf0⟩ := isCompact_Icc.exists_bound_of_continuousOn hf_cont
  let Mf : ℝ := max 0 Mf0
  have hβf_int : IntegrableOn (fun r => β r * f r) (Icc T s) := by
    refine Integrable.mono' (hβ_int.const_mul Mf)
      (hβ_int.aestronglyMeasurable.mul (hf_cont.aestronglyMeasurable measurableSet_Icc)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hβ_nn r hr), mul_comm]
    exact mul_le_mul_of_nonneg_right ((hMf0 r hr).trans (le_max_right 0 Mf0)) (hβ_nn r hr)
  have hβ_ii : IntervalIntegrable β volume T s := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hTs]; exact hβ_int
  have hβf_ii : IntervalIntegrable (fun r => β r * f r) volume T s := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hTs]; exact hβf_int
  let B : ℝ → ℝ := fun t => ∫ r in T..t, β r
  let I : ℝ → ℝ := fun t => C₀ + ∫ r in T..t, β r * f r
  have hB_ac : AbsolutelyContinuousOnInterval B T s :=
    absolutelyContinuousOnInterval_primitive hβ_ii (left_mem_uIcc (a := T) (b := s))
  have hI_ac : AbsolutelyContinuousOnInterval I T s :=
    (contDiff_const.contDiffOn.absolutelyContinuousOnInterval).add
      (absolutelyContinuousOnInterval_primitive hβf_ii (left_mem_uIcc (a := T) (b := s)))
  have hB_nonneg : ∀ t ∈ uIcc T s, 0 ≤ B t := by
    intro t ht
    rw [uIcc_of_le hTs] at ht
    dsimp [B]
    rw [intervalIntegral.integral_of_le ht.1, Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact setIntegral_nonneg measurableSet_Icc fun r hr =>
      hβ_nn r ⟨hr.1, hr.2.trans ht.2⟩
  have hexp_ac : AbsolutelyContinuousOnInterval (fun t => Real.exp (-B t)) T s := by
    refine hB_ac.neg.of_dist_le (K := 1) fun x hx y hy => ?_
    rw [one_mul, Real.dist_eq, Real.dist_eq]
    have hx0 : -B x ≤ 0 := neg_nonpos.2 (hB_nonneg x hx)
    have hy0 : -B y ≤ 0 := neg_nonpos.2 (hB_nonneg y hy)
    have hmvt := (convex_Iic (0 : ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun z _ => Real.differentiable_exp z)
      (fun z (hz : z ≤ 0) => by
        rw [Real.deriv_exp, Real.norm_of_nonneg (Real.exp_pos z).le]
        exact Real.exp_le_one_iff.2 hz)
      hy0 hx0
    rwa [one_mul, Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  let H : ℝ → ℝ := fun t => Real.exp (-B t) * I t
  have hH_ac : AbsolutelyContinuousOnInterval H T s := hexp_ac.fun_mul hI_ac
  let H' : ℝ → ℝ := fun r => Real.exp (-B r) * (-β r * I r + β r * f r)
  have hdH : ∀ᵐ r, r ∈ uIcc T s → HasDerivAt H (H' r) r := by
    filter_upwards [hβ_ii.ae_hasDerivAt_integral, hβf_ii.ae_hasDerivAt_integral]
      with r hdB hdI hr
    have hb : HasDerivAt B (β r) r := hdB hr T left_mem_uIcc
    have hi : HasDerivAt I (β r * f r) r := (hdI hr T left_mem_uIcc).const_add C₀
    exact ((hb.neg.exp).mul hi).congr_deriv (by dsimp [H']; ring)
  have hH'_ii : IntervalIntegrable H' volume T s := by
    have hcont_exp : ContinuousOn (fun r => Real.exp (-B r)) (uIcc T s) :=
      hexp_ac.continuousOn
    have hcont_I : ContinuousOn I (uIcc T s) := hI_ac.continuousOn
    have h1 := (hβ_ii.neg.mul_continuousOn hcont_I).continuousOn_mul hcont_exp
    have h2 := hβf_ii.continuousOn_mul hcont_exp
    refine (h1.add h2).congr fun r _ => ?_
    dsimp [H']; ring
  have hftc := integral_eq_sub_of_ae_hasDerivAt hH_ac hdH hH'_ii
  have hf_le_I : ∀ r ∈ Icc T s, f r ≤ I r := by
    intro r hr
    dsimp [I]
    rw [intervalIntegral.integral_of_le hr.1, Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact h_ineq r hr
  have hH'_nonpos : ∀ r ∈ Icc T s, H' r ≤ 0 := by
    intro r hr
    dsimp [H']
    have h1 : -β r * I r + β r * f r ≤ 0 := by
      nlinarith [hβ_nn r hr, hf_le_I r hr]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le h1
  have hint_nonpos : ∫ r in T..s, H' r ≤ 0 := by
    rw [intervalIntegral.integral_of_le hTs]
    have h_ioc : IntegrableOn H' (Ioc T s) := by
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hTs] at hH'_ii
    exact (setIntegral_mono_on h_ioc (integrableOn_const (hs := measure_Ioc_lt_top.ne))
      measurableSet_Ioc fun r hr => hH'_nonpos r ⟨hr.1.le, hr.2⟩).trans (by simp)
  have hHT : H T = C₀ := by
    dsimp [H, B, I]
    simp
  have hHs_le : Real.exp (-B s) * I s ≤ C₀ := by
    rw [hHT] at hftc
    dsimp [H] at hftc
    linarith
  have hIs_le : I s ≤ Real.exp (B s) * C₀ := by
    have := mul_le_mul_of_nonneg_left hHs_le (Real.exp_pos (B s)).le
    rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at this
  have hBs_eq : B s = ∫ r in Icc T s, β r := by
    dsimp [B]
    rw [intervalIntegral.integral_of_le hTs, Measure.restrict_congr_set Ioc_ae_eq_Icc]
  let _ := hC₀
  rw [← hBs_eq]
  exact (hf_le_I s ⟨hTs, le_rfl⟩).trans hIs_le

end TailH1GronwallAux

/-- **Differentiated `H¹(C_c)` tail energy Gronwall bound (`PartII-b:F7/2/3`)**. -/
theorem meridionalTailH1Gronwall_proof : MeridionalTailH1Gronwall := by
  let K0 : ℝ := 32 * TailH1GronwallAux.fhCommConst
  let K_H1 : ℝ := 2 * K0
  have hCF1 : 1 ≤ TailH1GronwallAux.fhCommConst := TailH1GronwallAux.one_le_fhCommConst
  have hKH1_pos : 0 < K_H1 := by dsimp [K_H1, K0]; linarith
  refine ⟨2, K_H1, by norm_num, hKH1_pos, ?_⟩
  intro p d dm dp T B_strain hreg hν1 hT1 hB0 hStrain g gq gη z₂ zq₂ zη₂
    hg_src hg_int hz hzq hzη hzT hz_sol hcont s hsT
  let _ := TailH1GronwallAux.one_le_c_of_bgRegime hreg hν1
  have hc : 0 < p.c := p.c_pos
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have htr := hreg.train_buc
  have hT_fin : sliceH1Norm p.c z₂ zq₂ zη₂ T < ⊤ := by
    unfold sliceH1Norm
    exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2
      ⟨hzT.memL2_u.eLpNorm_lt_top, hzT.memL2_uq.eLpNorm_lt_top⟩, hzT.memL2_uη.eLpNorm_lt_top⟩
  have hfin_z := TailH1GronwallAux.sliceH1Norm_lt_top_of_ge hz hzq hzη hT_fin hcont
  have hmem_z := fun t ht =>
    TailH1GronwallAux.memLp_slice_of_sliceH1Norm_lt_top hz hzq hzη (hfin_z t ht)
  obtain ⟨hcz, hczq, hczη⟩ :=
    TailH1GronwallAux.continuousOn_profPaths hz hzq hzη hT_fin hcont
  have hreg_z := TailH1GronwallAux.tail_slice_regularity hT0 hz hzq hzη hzT hz_sol hcont
  obtain ⟨_, hsrc_boch, hae_g⟩ :=
    TailH1GronwallAux.source_slice_regularity hc hT0 hg_src hg_int
  let E : ℝ → ℝ := fun t =>
    ‖TailH1GronwallAux.profPath p.c z₂ t‖ ^ 2 +
      ‖TailH1GronwallAux.profPath p.c zq₂ t‖ ^ 2 +
      ‖TailH1GronwallAux.profPath p.c zη₂ t‖ ^ 2
  let f : ℝ → ℝ := fun t => Real.sqrt (E t)
  let W : ℝ → ℝ := fun t => (sliceH1Norm p.c z₂ zq₂ zη₂ t).toReal
  let G : ℝ → ℝ := fun t => (sliceH1Norm p.c g gq gη t).toReal
  let S : ℝ → ℝ := TailH1GronwallAux.strainRate p.train
  have hf_cont_Ici : ContinuousOn f (Ici T) :=
    Real.continuous_sqrt.comp_continuousOn
      (((hcz.norm.pow 2).add (hczq.norm.pow 2)).add (hczη.norm.pow 2))
  have hW_eq_sum : ∀ t ≥ T, W t =
      ‖TailH1GronwallAux.profPath p.c z₂ t‖ +
        ‖TailH1GronwallAux.profPath p.c zq₂ t‖ +
        ‖TailH1GronwallAux.profPath p.c zη₂ t‖ := by
    intro t ht
    obtain ⟨hm1, hm2, hm3⟩ := hmem_z t ht
    rw [TailH1GronwallAux.norm_profPath_eq hm1, TailH1GronwallAux.norm_profPath_eq hm2,
      TailH1GronwallAux.norm_profPath_eq hm3]
    dsimp [W]
    unfold sliceH1Norm cylSliceL2
    rw [ENNReal.toReal_add (ENNReal.add_lt_top.2 ⟨hm1.eLpNorm_lt_top, hm2.eLpNorm_lt_top⟩).ne
        hm3.eLpNorm_lt_top.ne,
      ENNReal.toReal_add hm1.eLpNorm_ne_top hm2.eLpNorm_ne_top]
  have hW_le_2f : ∀ t ≥ T, W t ≤ 2 * f t := by
    intro t ht
    rw [hW_eq_sum t ht]
    dsimp [f, E]
    set x := ‖TailH1GronwallAux.profPath p.c z₂ t‖
    set y := ‖TailH1GronwallAux.profPath p.c zq₂ t‖
    set w := ‖TailH1GronwallAux.profPath p.c zη₂ t‖
    have hE_nn : 0 ≤ x ^ 2 + y ^ 2 + w ^ 2 := by positivity
    have hsq : (x + y + w) ^ 2 ≤ (2 * Real.sqrt (x ^ 2 + y ^ 2 + w ^ 2)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hE_nn]
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - w), sq_nonneg (y - w),
        sq_nonneg x, sq_nonneg y, sq_nonneg w]
    nlinarith [Real.sqrt_nonneg (x ^ 2 + y ^ 2 + w ^ 2)]
  have hf_le_W : ∀ t ≥ T, f t ≤ W t := by
    intro t ht
    rw [hW_eq_sum t ht]
    dsimp [f, E]
    set x := ‖TailH1GronwallAux.profPath p.c z₂ t‖
    set y := ‖TailH1GronwallAux.profPath p.c zq₂ t‖
    set w := ‖TailH1GronwallAux.profPath p.c zη₂ t‖
    have hx : 0 ≤ x := norm_nonneg _
    have hy : 0 ≤ y := norm_nonneg _
    have hw : 0 ≤ w := norm_nonneg _
    exact Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  have hW_cont_Ici : ContinuousOn W (Ici T) :=
    ((hcz.norm.add hczq.norm).add hczη.norm).congr fun t ht => hW_eq_sum t ht
  have hG_int : IntegrableOn G (Icc T s) := (hsrc_boch s hsT.le).1
  have hS_int : IntegrableOn S (Icc T s) :=
    TailH1GronwallAux.integrableOn_strainRate_Icc p.train htr hT0 hsT.le
  obtain ⟨MW0, hMW0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hW_cont_Ici.mono fun r (hr : r ∈ Icc T s) => hr.1)
  let MW : ℝ := max 0 MW0
  have hSW_int : IntegrableOn (fun r => K0 * S r * W r + 2 * G r) (Icc T s) := by
    refine (Integrable.mono' (hS_int.const_mul (K0 * MW))
      (((continuous_const.mul continuous_id).comp_aestronglyMeasurable
          hS_int.aestronglyMeasurable).mul
        ((hW_cont_Ici.mono fun r (hr : r ∈ Icc T s) => hr.1).aestronglyMeasurable
          measurableSet_Icc)) ?_).add (hG_int.const_mul 2)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have hK0_nn : 0 ≤ K0 := by dsimp [K0]; linarith
    have hSr := TailH1GronwallAux.strainRate_nonneg p.train r
    have hWr : 0 ≤ W r := ENNReal.toReal_nonneg
    change ‖K0 * TailH1GronwallAux.strainRate p.train r * W r‖ ≤ K0 * MW * S r
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hK0_nn hSr) hWr)]
    have hWb : W r ≤ MW := (le_abs_self _).trans ((hMW0 r hr).trans (le_max_right 0 MW0))
    calc K0 * S r * W r ≤ K0 * S r * MW :=
          mul_le_mul_of_nonneg_left hWb (mul_nonneg hK0_nn hSr)
      _ = K0 * MW * S r := by ring
  -- Step 1: For any T < a ≤ t ≤ s and k : ℕ, √(E_k t) ≤ √(E_k a) + ∫_{Icc a t} (K0 S W + 2 G)
  have step_moll : ∀ (a t : ℝ), T < a → a ≤ t → t ≤ s → ∀ k : ℕ,
      let Ek : ℝ → ℝ := fun r =>
        ‖TailH1GronwallAux.fhPath p.c k z₂ r‖ ^ 2 +
          ‖TailH1GronwallAux.fhPath p.c k zq₂ r‖ ^ 2 +
          ‖TailH1GronwallAux.fhPath p.c k zη₂ r‖ ^ 2
      Real.sqrt (Ek t) ≤ Real.sqrt (Ek a) + ∫ r in Icc a t, (K0 * S r * W r + 2 * G r) := by
    intro a t haT hat hts k Ek
    rcases eq_or_lt_of_le hat with rfl | hat_lt
    · have hnn : 0 ≤ ∫ r in Icc a a, (K0 * S r * W r + 2 * G r) :=
        setIntegral_nonneg measurableSet_Icc fun r _ => by
          have hK0_nn : 0 ≤ K0 := by dsimp [K0]; linarith
          exact add_nonneg
            (mul_nonneg (mul_nonneg hK0_nn (TailH1GronwallAux.strainRate_nonneg p.train r))
              ENNReal.toReal_nonneg)
            (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
      linarith
    have hab_s : a < s := hat_lt.trans_le hts
    obtain ⟨U0', Uj', hw0, hwj, hae_pair⟩ :=
      TailH1GronwallAux.hasWeakDerivTime_fhPaths htr hT0 haT hab_s hg_src hg_int
        hz hzq hzη hzT hz_sol hcont k
    have hsub_as : Icc a s ⊆ Ici T := fun r hr => haT.le.trans hr.1
    have heq0 := hw0.eqOn_rep hab_s
      (TailH1GronwallAux.continuousOn_fhPath hc k hz
        (fun r hr => (hmem_z r (hsub_as hr)).1) (hcz.mono hsub_as))
      (Eventually.of_forall fun _ => rfl)
    have heqq := (hwj 0).eqOn_rep hab_s
      (TailH1GronwallAux.continuousOn_fhPath hc k hzq
        (fun r hr => (hmem_z r (hsub_as hr)).2.1) (hczq.mono hsub_as))
      (Eventually.of_forall fun _ => rfl)
    have heqη := (hwj 1).eqOn_rep hab_s
      (TailH1GronwallAux.continuousOn_fhPath hc k hzη
        (fun r hr => (hmem_z r (hsub_as hr)).2.2) (hczη.mono hsub_as))
      (Eventually.of_forall fun _ => rfl)
    by_contra hlt_goal
    push Not at hlt_goal
    let ε : ℝ := (Real.sqrt (Ek t) -
        (Real.sqrt (Ek a) + ∫ r in Icc a t, (K0 * S r * W r + 2 * G r))) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    let Erep : ℝ → ℝ := fun r =>
      ‖hw0.rep r‖ ^ 2 + ‖(hwj 0).rep r‖ ^ 2 + ‖(hwj 1).rep r‖ ^ 2
    let Φ : ℝ → ℝ := fun r => Real.sqrt (Erep r + ε ^ 2)
    have hsub_at_as : Icc a t ⊆ Icc a s := Icc_subset_Icc_right hts
    have hsub_u : uIcc a t ⊆ uIcc a s := by
      rw [uIcc_of_le hat_lt.le, uIcc_of_le hab_s.le]; exact hsub_at_as
    have sq_ac : ∀ {u u' : ℝ → UnforcedLeray.Short.IIIa.LMH p.c}
        (hw : UnforcedLeray.BochnerTime.HasWeakDerivTime a s u u'),
        AbsolutelyContinuousOnInterval (fun r => ‖hw.rep r‖ ^ 2) a t := by
      intro u u' hw
      obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hw.continuousOn_rep
      refine ((hw.absolutelyContinuousOnInterval_rep hab_s.le).mono hsub_u).of_dist_le
        (K := 2 * max 0 M) fun x hx y hy => ?_
      rw [uIcc_of_le hat_lt.le] at hx hy
      have hxM := (hM x (hsub_at_as hx)).trans (le_max_right 0 M)
      have hyM := (hM y (hsub_at_as hy)).trans (le_max_right 0 M)
      rw [Real.dist_eq, dist_eq_norm, sq, sq, mul_self_sub_mul_self, abs_mul]
      have h1 : |‖hw.rep x‖ + ‖hw.rep y‖| ≤ 2 * max 0 M := by
        rw [abs_of_nonneg (by positivity)]; linarith
      have h2 : |‖hw.rep x‖ - ‖hw.rep y‖| ≤ ‖hw.rep x - hw.rep y‖ := abs_norm_sub_norm_le _ _
      exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    have hE_ac : AbsolutelyContinuousOnInterval (fun r => Erep r + ε ^ 2) a t :=
      (((sq_ac hw0).add (sq_ac (hwj 0))).add (sq_ac (hwj 1))).add
        contDiff_const.contDiffOn.absolutelyContinuousOnInterval
    have hΦ_ge : ∀ r : ℝ, ε ≤ Φ r := by
      intro r
      dsimp [Φ, Erep]
      have h1 : ε ^ 2 ≤ ‖hw0.rep r‖ ^ 2 + ‖(hwj 0).rep r‖ ^ 2 + ‖(hwj 1).rep r‖ ^ 2 + ε ^ 2 :=
        le_add_of_nonneg_left (by positivity)
      exact (Real.sqrt_sq hε.le).symm.trans_le (Real.sqrt_le_sqrt h1)
    have hΦ_ac : AbsolutelyContinuousOnInterval Φ a t := by
      refine hE_ac.of_dist_le (K := (2 * ε)⁻¹) fun x _ y _ => ?_
      rw [Real.dist_eq, Real.dist_eq]
      dsimp only [Φ]
      set Ax := Erep x + ε ^ 2
      set Ay := Erep y + ε ^ 2
      have hAx : 0 ≤ Ax := by dsimp [Ax, Erep]; positivity
      have hAy : 0 ≤ Ay := by dsimp [Ay, Erep]; positivity
      have hsum_ge : 2 * ε ≤ Real.sqrt Ax + Real.sqrt Ay := by
        linarith [hΦ_ge x, hΦ_ge y]
      have hprod : |Real.sqrt Ax - Real.sqrt Ay| * (Real.sqrt Ax + Real.sqrt Ay) = |Ax - Ay| := by
        have h1 : (Real.sqrt Ax - Real.sqrt Ay) * (Real.sqrt Ax + Real.sqrt Ay) = Ax - Ay := by
          nlinarith [Real.sq_sqrt hAx, Real.sq_sqrt hAy]
        rw [← abs_of_pos (by linarith : 0 < Real.sqrt Ax + Real.sqrt Ay), ← abs_mul, h1]
      rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
      calc |Real.sqrt Ax - Real.sqrt Ay| * (2 * ε)
          ≤ |Real.sqrt Ax - Real.sqrt Ay| * (Real.sqrt Ax + Real.sqrt Ay) :=
            mul_le_mul_of_nonneg_left hsum_ge (abs_nonneg _)
        _ = |Ax - Ay| := hprod
    let P : ℝ → ℝ := fun r =>
      ⟪U0' r, hw0.rep r⟫ + ⟪Uj' 0 r, (hwj 0).rep r⟫ + ⟪Uj' 1 r, (hwj 1).rep r⟫
    have hdΦ : ∀ᵐ r, r ∈ uIcc a t → HasDerivAt Φ (P r / Φ r) r := by
      have ha_ne : ∀ᵐ r : ℝ ∂volume, r ≠ a := by simp [ae_iff, measure_singleton]
      have hs_ne : ∀ᵐ r : ℝ ∂volume, r ≠ s := by simp [ae_iff, measure_singleton]
      filter_upwards [hw0.ae_hasDerivAt_rep, (hwj 0).ae_hasDerivAt_rep,
        (hwj 1).ae_hasDerivAt_rep, ha_ne, hs_ne] with r hd0 hdq hdη hra hrs hr_mem
      rw [uIcc_of_le hat_lt.le] at hr_mem
      have hr_ioo : r ∈ Ioo a s :=
        ⟨lt_of_le_of_ne hr_mem.1 (Ne.symm hra), lt_of_le_of_ne (hr_mem.2.trans hts) hrs⟩
      have h0 := (hd0 hr_ioo).norm_sq
      have hq := (hdq hr_ioo).norm_sq
      have hη := (hdη hr_ioo).norm_sq
      rw [real_inner_comm] at h0 hq hη
      have hdE : HasDerivAt (fun r => Erep r + ε ^ 2) (2 * P r) r :=
        (((h0.add hq).add hη).add_const (ε ^ 2)).congr_deriv (by dsimp [P]; ring)
      have hpos : Erep r + ε ^ 2 ≠ 0 := by dsimp [Erep]; positivity
      refine (hdE.sqrt hpos).congr_deriv ?_
      dsimp only [Φ]
      have hΦ_ne : Real.sqrt (Erep r + ε ^ 2) ≠ 0 := (lt_of_lt_of_le hε (hΦ_ge r)).ne'
      field_simp [hΦ_ne]
    have hP_ii : IntervalIntegrable P volume a t :=
      ((hw0.intervalIntegrable_inner_rep ⟨le_rfl, hab_s.le⟩ ⟨hat_lt.le, hts⟩).add
        ((hwj 0).intervalIntegrable_inner_rep ⟨le_rfl, hab_s.le⟩ ⟨hat_lt.le, hts⟩)).add
        ((hwj 1).intervalIntegrable_inner_rep ⟨le_rfl, hab_s.le⟩ ⟨hat_lt.le, hts⟩)
    have hΦ_inv_cont : ContinuousOn (fun r => (Φ r)⁻¹) (uIcc a t) :=
      hΦ_ac.continuousOn.inv₀ fun r _ => (lt_of_lt_of_le hε (hΦ_ge r)).ne'
    have hΦ'_ii : IntervalIntegrable (fun r => P r / Φ r) volume a t := by
      refine (hP_ii.mul_continuousOn hΦ_inv_cont).congr fun r _ => ?_
      simp [div_eq_mul_inv]
    have hftc := UnforcedLeray.BochnerTime.integral_eq_sub_of_ae_hasDerivAt hΦ_ac hdΦ hΦ'_ii
    -- Pointwise a.e. bound P r / Φ r ≤ K0 * S r * W r + 2 * G r on Ioc a t
    have hae_ioc : ∀ᵐ r ∂(volume.restrict (Ioc a t)),
        P r / Φ r ≤ K0 * S r * W r + 2 * G r := by
      have hae_pair' : ∀ᵐ r ∂(volume.restrict (Ioc a t)),
          ⟪U0' r, TailH1GronwallAux.fhPath p.c k z₂ r⟫ =
            (UnforcedLeray.Short.IIIa.LMIp p.c
              (TailH1GronwallAux.rawZ0 p T g z₂ zq₂ zη₂ k r)
              (TailH1GronwallAux.fhField p.c k z₂ r)).re ∧
          ∀ j : Fin 2,
            ⟪Uj' j r, TailH1GronwallAux.fhPath p.c k (![zq₂, zη₂] j) r⟫ =
              (UnforcedLeray.Short.IIIa.LMIp p.c
                (TailH1GronwallAux.rawZj p T gq gη z₂ zq₂ zη₂ k j r)
                (TailH1GronwallAux.fhField p.c k (![zq₂, zη₂] j) r)).re :=
        ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Icc_self.trans hsub_at_as) hae_pair
      filter_upwards [hae_pair', ae_restrict_of_ae hae_g, ae_restrict_mem measurableSet_Ioc]
        with r ⟨hp0, hpj⟩ hgr hr
      have hr_as : r ∈ Icc a s := ⟨hr.1.le, hr.2.trans hts⟩
      have hrT : T < r := haT.trans hr.1
      obtain ⟨hfin_gr, _⟩ := hgr hrT
      obtain ⟨hw_z_r, _, _, _⟩ := hreg_z r hrT.le
      have hEq_rep : Erep r = Ek r := by
        dsimp only [Erep, Ek]
        rw [← heq0 hr_as, ← heqq hr_as, ← heqη hr_as]
      have hPr_eq : P r =
          (UnforcedLeray.Short.IIIa.LMIp p.c
              (TailH1GronwallAux.rawZ0 p T g z₂ zq₂ zη₂ k r)
              (TailH1GronwallAux.fhField p.c k z₂ r)).re +
            (UnforcedLeray.Short.IIIa.LMIp p.c
              (TailH1GronwallAux.rawZj p T gq gη z₂ zq₂ zη₂ k 0 r)
              (TailH1GronwallAux.fhField p.c k zq₂ r)).re +
            (UnforcedLeray.Short.IIIa.LMIp p.c
              (TailH1GronwallAux.rawZj p T gq gη z₂ zq₂ zη₂ k 1 r)
              (TailH1GronwallAux.fhField p.c k zη₂ r)).re := by
        have hpq : ⟪Uj' 0 r, TailH1GronwallAux.fhPath p.c k zq₂ r⟫ =
            (UnforcedLeray.Short.IIIa.LMIp p.c
              (TailH1GronwallAux.rawZj p T gq gη z₂ zq₂ zη₂ k 0 r)
              (TailH1GronwallAux.fhField p.c k zq₂ r)).re := hpj 0
        have hpη : ⟪Uj' 1 r, TailH1GronwallAux.fhPath p.c k zη₂ r⟫ =
            (UnforcedLeray.Short.IIIa.LMIp p.c
              (TailH1GronwallAux.rawZj p T gq gη z₂ zq₂ zη₂ k 1 r)
              (TailH1GronwallAux.fhField p.c k zη₂ r)).re := hpj 1
        dsimp only [P]
        rw [← heq0 hr_as, ← heqq hr_as, ← heqη hr_as, hp0, hpq, hpη]
      let Bk : ℝ := Real.sqrt (Ek r)
      have hEk_nn : 0 ≤ Ek r := by dsimp [Ek]; positivity
      have hBk_sq : Bk ^ 2 = Ek r := Real.sq_sqrt hEk_nn
      have hBz : ‖TailH1GronwallAux.fhPath p.c k z₂ r‖ ^ 2 ≤ Bk ^ 2 := by
        rw [hBk_sq]; dsimp [Ek]; linarith [sq_nonneg ‖TailH1GronwallAux.fhPath p.c k zq₂ r‖,
          sq_nonneg ‖TailH1GronwallAux.fhPath p.c k zη₂ r‖]
      have hBzq : ‖TailH1GronwallAux.fhPath p.c k zq₂ r‖ ^ 2 ≤ Bk ^ 2 := by
        rw [hBk_sq]; dsimp [Ek]; linarith [sq_nonneg ‖TailH1GronwallAux.fhPath p.c k z₂ r‖,
          sq_nonneg ‖TailH1GronwallAux.fhPath p.c k zη₂ r‖]
      have hBzη : ‖TailH1GronwallAux.fhPath p.c k zη₂ r‖ ^ 2 ≤ Bk ^ 2 := by
        rw [hBk_sq]; dsimp [Ek]; linarith [sq_nonneg ‖TailH1GronwallAux.fhPath p.c k z₂ r‖,
          sq_nonneg ‖TailH1GronwallAux.fhPath p.c k zq₂ r‖]
      have hraw_b := TailH1GronwallAux.raw_pairings_bound htr hT0 hrT (Real.sqrt_nonneg _)
        hg_src hz hzq hzη (hfin_z r hrT.le) hfin_gr hw_z_r k hBz hBzq hBzη
      rw [← hPr_eq] at hraw_b
      have hΦ_pos : 0 < Φ r := lt_of_lt_of_le hε (hΦ_ge r)
      have hBk_le_Φ : Bk ≤ Φ r := by
        dsimp [Bk, Φ]; rw [hEq_rep]
        exact Real.sqrt_le_sqrt (by linarith [sq_nonneg ε])
      have hRHS_nn : 0 ≤ K0 * S r * W r + 2 * G r := by
        have hK0_nn : 0 ≤ K0 := by dsimp [K0]; linarith
        exact add_nonneg
          (mul_nonneg (mul_nonneg hK0_nn (TailH1GronwallAux.strainRate_nonneg p.train r))
            ENNReal.toReal_nonneg)
          (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
      rw [div_le_iff₀ hΦ_pos]
      exact hraw_b.trans (mul_le_mul_of_nonneg_left hBk_le_Φ hRHS_nn)
    have hint_le : ∫ r in a..t, P r / Φ r ≤ ∫ r in Icc a t, (K0 * S r * W r + 2 * G r) := by
      rw [intervalIntegral.integral_of_le hat_lt.le,
        ← Measure.restrict_congr_set (Ioc_ae_eq_Icc (a := a) (b := t))]
      have h1 : IntegrableOn (fun r => P r / Φ r) (Ioc a t) := by
        rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hat_lt.le] at hΦ'_ii
      have h2 : IntegrableOn (fun r => K0 * S r * W r + 2 * G r) (Ioc a t) :=
        hSW_int.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc haT.le hts))
      exact integral_mono_ae h1 h2 hae_ioc
    have hΦt_ge : Real.sqrt (Ek t) ≤ Φ t := by
      dsimp only [Φ, Erep, Ek]
      rw [← heq0 ⟨hat_lt.le, hts⟩, ← heqq ⟨hat_lt.le, hts⟩, ← heqη ⟨hat_lt.le, hts⟩]
      exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε))
    have hΦa_le : Φ a ≤ Real.sqrt (Ek a) + ε := by
      dsimp only [Φ, Erep]
      have hEq_a : ‖hw0.rep a‖ ^ 2 + ‖(hwj 0).rep a‖ ^ 2 + ‖(hwj 1).rep a‖ ^ 2 = Ek a := by
        dsimp only [Ek]
        rw [← heq0 ⟨le_rfl, hab_s.le⟩, ← heqq ⟨le_rfl, hab_s.le⟩, ← heqη ⟨le_rfl, hab_s.le⟩]
      rw [hEq_a]
      have hEka_nn : 0 ≤ Ek a := by dsimp [Ek]; positivity
      exact Real.sqrt_le_iff.2 ⟨by positivity, by
        nlinarith [Real.sq_sqrt hEka_nn, Real.sqrt_nonneg (Ek a)]⟩
    dsimp only [ε] at hε hΦa_le
    linarith [hftc, hint_le, hΦt_ge, hΦa_le, hε]
  -- Step 2: Pass k → ∞ at fixed T < a ≤ t ≤ s
  have step_lim_k : ∀ (a t : ℝ), T < a → a ≤ t → t ≤ s →
      f t ≤ f a + ∫ r in Icc a t, (K0 * S r * W r + 2 * G r) := by
    intro a t haT hat hts
    have htT : T ≤ t := haT.le.trans hat
    have hlim_Ek : ∀ r ≥ T, Tendsto (fun k : ℕ =>
        Real.sqrt (‖TailH1GronwallAux.fhPath p.c k z₂ r‖ ^ 2 +
          ‖TailH1GronwallAux.fhPath p.c k zq₂ r‖ ^ 2 +
          ‖TailH1GronwallAux.fhPath p.c k zη₂ r‖ ^ 2)) atTop (𝓝 (f r)) := by
      intro r hr
      obtain ⟨hm1, hm2, hm3⟩ := hmem_z r hr
      have l1 := TailH1GronwallAux.tendsto_norm_fhPath_sq hc hz hm1
      have l2 := TailH1GronwallAux.tendsto_norm_fhPath_sq hc hzq hm2
      have l3 := TailH1GronwallAux.tendsto_norm_fhPath_sq hc hzη hm3
      exact (Real.continuous_sqrt.tendsto (E r)).comp ((l1.add l2).add l3)
    exact le_of_tendsto_of_tendsto (hlim_Ek t htT)
      ((hlim_Ek a haT.le).add_const _) (Eventually.of_forall (step_moll a t haT hat hts))
  -- Step 3: Pass a → T⁺ to get the integral Gronwall inequality on Icc T s
  let C₀ : ℝ := f T + 2 * ∫ r in Icc T s, G r
  have hG_int_nn : 0 ≤ ∫ r in Icc T s, G r :=
    setIntegral_nonneg measurableSet_Icc fun _ _ => ENNReal.toReal_nonneg
  have hC₀_nn : 0 ≤ C₀ := add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) hG_int_nn)
  let β : ℝ → ℝ := fun r => K_H1 * S r
  have hβ_nn : ∀ r ∈ Icc T s, 0 ≤ β r :=
    fun r _ => mul_nonneg hKH1_pos.le (TailH1GronwallAux.strainRate_nonneg p.train r)
  have hβ_int : IntegrableOn β (Icc T s) := hS_int.const_mul K_H1
  obtain ⟨Mf0, hMf0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf_cont_Ici.mono fun r (hr : r ∈ Icc T s) => hr.1)
  have hβf_int_all : IntegrableOn (fun r => β r * f r) (Icc T s) := by
    refine Integrable.mono' (hβ_int.const_mul (max 0 Mf0))
      (hβ_int.aestronglyMeasurable.mul
        ((hf_cont_Ici.mono fun r (hr : r ∈ Icc T s) => hr.1).aestronglyMeasurable
          measurableSet_Icc)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hβ_nn r hr), mul_comm]
    exact mul_le_mul_of_nonneg_right ((hMf0 r hr).trans (le_max_right 0 Mf0)) (hβ_nn r hr)
  have step_int_gronwall : ∀ t ∈ Icc T s, f t ≤ C₀ + ∫ r in Icc T t, β r * f r := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | ht_gt
    · have h1 : 0 ≤ ∫ r in Icc T T, β r * f r :=
        setIntegral_nonneg measurableSet_Icc fun r hr =>
          mul_nonneg (hβ_nn r ⟨hr.1, hr.2.trans hsT.le⟩) (Real.sqrt_nonneg _)
      dsimp [C₀]; linarith
    · -- Sequence a_n = T + (t - T) / (n + 2) → T in Ici T
      let an : ℕ → ℝ := fun n => T + (t - T) / ((n : ℝ) + 2)
      have han_T : ∀ n, T < an n := fun n => by
        dsimp [an]; linarith [div_pos (sub_pos.2 ht_gt) (show (0 : ℝ) < (n : ℝ) + 2 by positivity)]
      have han_t : ∀ n, an n ≤ t := fun n => by
        dsimp [an]
        have h2 : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
        have hdiv : (t - T) / ((n : ℝ) + 2) ≤ t - T :=
          div_le_self (sub_pos.2 ht_gt).le h2
        linarith
      have h_rhs_bound : ∀ n : ℕ,
          ∫ r in Icc (an n) t, (K0 * S r * W r + 2 * G r) ≤
            2 * (∫ r in Icc T s, G r) + ∫ r in Icc T t, β r * f r := by
        intro n
        have hsub_at : Icc (an n) t ⊆ Icc T t := Icc_subset_Icc_left (han_T n).le
        have hsub_ts : Icc T t ⊆ Icc T s := Icc_subset_Icc_right ht.2
        have hi_βf : IntegrableOn (fun r => β r * f r) (Icc (an n) t) :=
          hβf_int_all.mono_set (hsub_at.trans hsub_ts)
        have hi_2G : IntegrableOn (fun r => 2 * G r) (Icc (an n) t) :=
          (hG_int.mono_set (hsub_at.trans hsub_ts)).const_mul 2
        have hi_sum : IntegrableOn (fun r => β r * f r + 2 * G r) (Icc (an n) t) :=
          hi_βf.add hi_2G
        have h1 := setIntegral_mono_on (hSW_int.mono_set (hsub_at.trans hsub_ts))
          hi_sum measurableSet_Icc fun r hr => by
            have hrT : T ≤ r := (han_T n).le.trans hr.1
            have hK0_nn : 0 ≤ K0 := by dsimp [K0]; linarith
            have hSr := TailH1GronwallAux.strainRate_nonneg p.train r
            have := mul_le_mul_of_nonneg_left (hW_le_2f r hrT) (mul_nonneg hK0_nn hSr)
            dsimp [β, K_H1, S] at this ⊢
            linarith
        rw [integral_add hi_βf hi_2G] at h1
        have h2 : ∫ r in Icc (an n) t, β r * f r ≤ ∫ r in Icc T t, β r * f r :=
          setIntegral_mono_set (hβf_int_all.mono_set hsub_ts)
            (ae_of_all _ fun r => mul_nonneg
              (mul_nonneg hKH1_pos.le (TailH1GronwallAux.strainRate_nonneg p.train r))
              (Real.sqrt_nonneg _))
            (Eventually.of_forall hsub_at)
        have h3 : ∫ r in Icc (an n) t, 2 * G r ≤ 2 * ∫ r in Icc T s, G r := by
          rw [← integral_const_mul]
          exact setIntegral_mono_set (hG_int.const_mul 2)
            (ae_of_all _ fun _ => mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
            (Eventually.of_forall (hsub_at.trans hsub_ts))
        linarith
      have h_seq : ∀ n : ℕ, f t ≤ f (an n) +
          (2 * (∫ r in Icc T s, G r) + ∫ r in Icc T t, β r * f r) :=
        fun n => (step_lim_k (an n) t (han_T n) (han_t n) ht.2).trans
          (add_le_add le_rfl (h_rhs_bound n))
      have han_lim : Tendsto an atTop (𝓝[Ici T] T) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, Eventually.of_forall fun n => (han_T n).le⟩
        have h0 := (tendsto_const_div_atTop_nhds_zero_nat (t - T)).comp (tendsto_add_atTop_nat 2)
        simpa [an] using h0.const_add T
      have hf_lim : Tendsto (fun n => f (an n)) atTop (𝓝 (f T)) :=
        (hf_cont_Ici T (mem_Ici.2 le_rfl)).tendsto.comp han_lim
      have hfinal := le_of_tendsto_of_tendsto tendsto_const_nhds
        (hf_lim.add_const _) (Eventually.of_forall h_seq)
      dsimp [C₀]
      linarith
  -- Step 4: Apply continuous integral Gronwall on Icc T s and convert back to ℝ≥0∞
  have hfs := TailH1GronwallAux.integral_gronwall_continuous hsT.le hC₀_nn
    (hf_cont_Ici.mono fun r (hr : r ∈ Icc T s) => hr.1) hβ_nn hβ_int step_int_gronwall
  have hβ_int_le : ∫ r in Icc T s, β r ≤ K_H1 * B_strain := by
    dsimp [β]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (TailH1GronwallAux.integral_strainRate_le p.train htr hT0 hsT.le hB0 hStrain) hKH1_pos.le
  have h2_le_KH1 : 2 ≤ K_H1 := by dsimp [K_H1, K0]; linarith
  have hC₀_le : C₀ ≤ W T + K_H1 * (∫⁻ t in Ioi T, sliceH1Norm p.c g gq gη t).toReal := by
    have hG_le_Ioi : ∫ r in Icc T s, G r ≤ (∫⁻ t in Ioi T, sliceH1Norm p.c g gq gη t).toReal := by
      rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
      have hm_H1 : Measurable (sliceH1Norm p.c g gq gη) :=
        CylProjectionSub.measurable_sliceH1Norm_cp p.c hg_src.sm_g hg_src.sm_gq hg_src.sm_gη
      have hlt_ioc : (∫⁻ t in Ioc T s, sliceH1Norm p.c g gq gη t) < ⊤ :=
        (lintegral_mono_set (fun r (hr : r ∈ Ioc T s) => hr.1)).trans_lt hg_int
      have h_eq : ∫ r in Ioc T s, G r = (∫⁻ r in Ioc T s, sliceH1Norm p.c g gq gη r).toReal := by
        dsimp [G]
        rw [integral_toReal hm_H1.aemeasurable (ae_lt_top hm_H1 hlt_ioc.ne)]
      rw [h_eq]
      exact ENNReal.toReal_mono hg_int.ne (lintegral_mono_set fun r (hr : r ∈ Ioc T s) => hr.1)
    have h1 := hf_le_W T le_rfl
    have h2 : 2 * ∫ r in Icc T s, G r ≤ K_H1 * (∫⁻ t in Ioi T, sliceH1Norm p.c g gq gη t).toReal :=
      mul_le_mul h2_le_KH1 hG_le_Ioi hG_int_nn hKH1_pos.le
    dsimp [C₀]; linarith
  have hWs_real : W s ≤
      (2 * Real.exp (K_H1 * B_strain)) *
        (W T + K_H1 * (∫⁻ t in Ioi T, sliceH1Norm p.c g gq gη t).toReal) := by
    have hexp_le : Real.exp (∫ r in Icc T s, β r) ≤ Real.exp (K_H1 * B_strain) :=
      Real.exp_le_exp.2 hβ_int_le
    calc W s ≤ 2 * f s := hW_le_2f s hsT.le
      _ ≤ 2 * (Real.exp (∫ r in Icc T s, β r) * C₀) :=
          mul_le_mul_of_nonneg_left hfs (by norm_num)
      _ ≤ 2 * (Real.exp (K_H1 * B_strain) *
            (W T + K_H1 * (∫⁻ t in Ioi T, sliceH1Norm p.c g gq gη t).toReal)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hexp_le hC₀_le hC₀_nn (Real.exp_pos _).le) (by norm_num)
      _ = _ := by ring
  rw [← ENNReal.ofReal_toReal (hfin_z s hsT.le).ne]
  refine (ENNReal.ofReal_le_ofReal hWs_real).trans (le_of_eq ?_)
  have hA_nn : 0 ≤ 2 * Real.exp (K_H1 * B_strain) := by positivity
  have hWT_nn : 0 ≤ W T := ENNReal.toReal_nonneg
  have hKG_nn : 0 ≤ K_H1 * (∫⁻ t in Ioi T, sliceH1Norm p.c g gq gη t).toReal :=
    mul_nonneg hKH1_pos.le ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_mul hA_nn, ENNReal.ofReal_add hWT_nn hKG_nn,
    ENNReal.ofReal_mul hKH1_pos.le,
    ENNReal.ofReal_toReal hT_fin.ne, ENNReal.ofReal_toReal hg_int.ne]

end UnforcedLeray.Short.IIb

end
