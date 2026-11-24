import UnforcedLeray.Short.PartI.Sub.PartI_T04_9_1
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.CurlRegularity

/-!
# Part I, `PartI:T04/9/1/1`: time continuity of the cutoff jets (`APLevel2CutCont`)

Source of record: `the November 2 reference manuscript`, lines 285-288 (qualitative).

Route:
* `apcc_slice`: for `s ∈ [0,T]`, the spatial jet of the slice `w ↦ G (s,w)` is the composition of
  the within-jet of `G` on the closed strip with the inclusion `w ↦ (0,w)`;
* `apcc_jet_joint`: hence `(s,z) ↦ iteratedFDeriv j (G (s,·)) z` is continuous on the strip;
* `apcc_curl_smooth`: the curl of a classical solution is `C^∞` on the closed strip;
* `apcc_param`: continuity of the cutoff parameter integral by dominated convergence.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Pointwise

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

theorem apcc_eta_nonneg (R η : ℝ) : 0 ≤ etaCutoff R η := by
  show 0 ≤ Real.smoothTransition (2 - |η| / R) ^ 2
  positivity

theorem apcc_eta_le_one (R η : ℝ) : etaCutoff R η ≤ 1 := by
  show Real.smoothTransition (2 - |η| / R) ^ 2 ≤ 1
  exact pow_le_one₀ (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)

theorem apcc_eta_eq_zero {R : ℝ} (hR : 0 < R) {η : ℝ} (hη : 2 * R ≤ |η|) :
    etaCutoff R η = 0 := by
  have h2 : 2 ≤ |η| / R := (le_div_iff₀ hR).2 (by linarith)
  have hle : 2 - |η| / R ≤ 0 := by linarith
  show Real.smoothTransition (2 - |η| / R) ^ 2 = 0
  simp [Real.smoothTransition.zero_of_nonpos hle]

theorem apcc_eta_continuous (R : ℝ) : Continuous (etaCutoff R) := by
  show Continuous fun η : ℝ => Real.smoothTransition (2 - |η| / R) ^ 2
  exact (Real.smoothTransition.continuous.comp
    (continuous_const.sub (continuous_abs.div_const R))).pow 2

/-- The slice jet at time `s ∈ [0,T]` is the within-jet of `G` on the closed strip, composed with
the inclusion `w ↦ (0,w)`. -/
theorem apcc_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : ℝ × Plane → F} {T : ℝ} (hT : 0 < T)
    (hG : ContDiffOn ℝ ∞ G (Icc (0 : ℝ) T ×ˢ (univ : Set Plane))) (j : ℕ)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (z : Plane) :
    iteratedFDeriv ℝ j (fun w : Plane => G (s, w)) z =
      (iteratedFDerivWithin ℝ j G (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) (s, z)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ Plane) := by
  have hS' : UniqueDiffOn ℝ (Icc (-s) (T - s) ×ˢ (univ : Set Plane)) :=
    UniqueDiffOn.prod (uniqueDiffOn_Icc (by linarith)) uniqueDiffOn_univ
  have hvS : (((s, (0 : Plane)) : ℝ × Plane) +ᵥ (Icc (-s) (T - s) ×ˢ (univ : Set Plane))) =
      Icc (0 : ℝ) T ×ˢ (univ : Set Plane) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨?_, ?_⟩, mem_univ _⟩
      · show 0 ≤ s + x.1
        linarith [hx.1.1]
      · show s + x.1 ≤ T
        linarith [hx.1.2]
    · intro hy
      refine ⟨y - ((s, (0 : Plane)) : ℝ × Plane), ⟨⟨?_, ?_⟩, mem_univ _⟩, ?_⟩
      · show -s ≤ y.1 - s
        linarith [hy.1.1]
      · show y.1 - s ≤ T - s
        linarith [hy.1.2]
      · simp
  have hf' : ContDiffOn ℝ ∞ (fun y : ℝ × Plane => G (((s, (0 : Plane)) : ℝ × Plane) + y))
      (Icc (-s) (T - s) ×ˢ (univ : Set Plane)) := by
    refine hG.comp (contDiff_const.add contDiff_id).contDiffOn ?_
    intro y hy
    rw [← hvS]
    exact ⟨y, hy, rfl⟩
  have hpre : (ContinuousLinearMap.inr ℝ ℝ Plane) ⁻¹' (Icc (-s) (T - s) ×ˢ (univ : Set Plane)) =
      univ := by
    ext w
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Icc, Set.mem_univ, and_true,
      ContinuousLinearMap.inr_apply, iff_true]
    constructor <;> linarith [hs.1, hs.2]
  have hz' : (ContinuousLinearMap.inr ℝ ℝ Plane) z ∈ (Icc (-s) (T - s) ×ˢ (univ : Set Plane)) := by
    rw [← Set.mem_preimage, hpre]
    exact mem_univ z
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right
    (ContinuousLinearMap.inr ℝ ℝ Plane) hf' hS' (by rw [hpre]; exact uniqueDiffOn_univ) hz'
    (i := j) (by exact_mod_cast le_top)
  rw [hpre] at hcomp
  have htr := iteratedFDerivWithin_comp_add_left (𝕜 := ℝ) (f := G)
    (s := Icc (-s) (T - s) ×ˢ (univ : Set Plane)) j ((s, (0 : Plane)) : ℝ × Plane)
    (ContinuousLinearMap.inr ℝ ℝ Plane z)
  rw [hvS] at htr
  have hpt : ((s, (0 : Plane)) : ℝ × Plane) + ContinuousLinearMap.inr ℝ ℝ Plane z = (s, z) := by
    simp
  rw [hpt] at htr
  rw [htr] at hcomp
  have hfun : (fun w : Plane => G (s, w)) =
      (fun y : ℝ × Plane => G (((s, (0 : Plane)) : ℝ × Plane) + y)) ∘
        (ContinuousLinearMap.inr ℝ ℝ Plane) := by
    funext w
    simp
  rw [← iteratedFDerivWithin_univ, hfun, hcomp]

/-- Joint continuity of the spatial jets of a function which is `C^∞` on the closed strip. -/
theorem apcc_jet_joint {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : ℝ × Plane → F} {T : ℝ} (hT : 0 < T)
    (hG : ContDiffOn ℝ ∞ G (Icc (0 : ℝ) T ×ˢ (univ : Set Plane))) (j : ℕ) :
    ContinuousOn (fun x : ℝ × Plane => iteratedFDeriv ℝ j (fun w : Plane => G (x.1, w)) x.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) := by
  have hS : UniqueDiffOn ℝ (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    UniqueDiffOn.prod (uniqueDiffOn_Icc hT) uniqueDiffOn_univ
  have hc : ContinuousOn (iteratedFDerivWithin ℝ j G (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)))
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    hG.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hS
  have hΦ : Continuous (fun M : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℝ × Plane) F =>
      M.compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ ℝ Plane)) :=
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin j => ContinuousLinearMap.inr ℝ ℝ Plane)).continuous
  refine (hΦ.comp_continuousOn hc).congr ?_
  intro x hx
  exact apcc_slice hT hG j hx.1 x.2

/-- The curl of a field which is `C^∞` on the closed strip is `C^∞` on the closed strip. -/
theorem apcc_curl_smooth {v : ℝ → Plane → Vec} {T : ℝ} (hT : 0 < T)
    (hv : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Icc 0 T ×ˢ (univ : Set Plane))) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => Cyl.curl (v x.1) x.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) := by
  have hS : UniqueDiffOn ℝ (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    UniqueDiffOn.prod (uniqueDiffOn_Icc hT) uniqueDiffOn_univ
  have h1 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane =>
      fderivWithin ℝ (crFc v 1) (Icc 0 T ×ˢ (univ : Set Plane)) x crEQ)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    ((crFc_contDiffOn hv 1).fderivWithin hS (by simp)).clm_apply contDiffOn_const
  have h0 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane =>
      fderivWithin ℝ (crFc v 0) (Icc 0 T ×ˢ (univ : Set Plane)) x crEE)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    ((crFc_contDiffOn hv 0).fderivWithin hS (by simp)).clm_apply contDiffOn_const
  exact (h1.sub h0).congr (fun x hx => crCurl_within hv hx.1)

/-- Dominated continuity of the cutoff parameter integral `s ↦ ∫_cell χ_R H(s,·)`. -/
theorem apcc_param (c T R : ℝ) (hR : 1 ≤ R) (H : ℝ → Plane → ℝ)
    (hH : ContinuousOn (fun x : ℝ × Plane => H x.1 x.2) (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)))
    (hnn : ∀ s ∈ Icc (0 : ℝ) T, ∀ z, 0 ≤ H s z) :
    ContinuousOn (fun s : ℝ => ∫ z in Cyl.cell c, etaCutoff R z.2 * H s z) (Icc (0 : ℝ) T) := by
  have hR0 : 0 < R := by linarith
  have hK : IsCompact (Icc (0 : ℝ) T ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R))) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hK_sub : Icc (0 : ℝ) T ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)) ⊆
      Icc (0 : ℝ) T ×ˢ (univ : Set Plane) := by
    intro x hx
    exact Set.mem_prod.2 ⟨(Set.mem_prod.1 hx).1, mem_univ _⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hH.mono hK_sub)
  have hbox_meas : MeasurableSet (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hbox_fin : volume (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)) < ⊤ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have hcell_meas : MeasurableSet (Cyl.cell c) := by
    unfold Cyl.cell
    exact measurableSet_Ico.prod MeasurableSet.univ
  have hfin : (volume.restrict (Cyl.cell c)) (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)) ≠ ⊤ :=
    ne_top_of_le_ne_top hbox_fin.ne (Measure.restrict_apply_le _ _)
  have hbound_int : Integrable
      ((Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)).indicator (fun _ : Plane => max C 0))
      (volume.restrict (Cyl.cell c)) :=
    (integrable_indicator_iff hbox_meas).2 (integrableOn_const hfin)
  have hz : ∀ s : ℝ, s ∈ Icc (0 : ℝ) T →
      Continuous (fun z : Plane => etaCutoff R z.2 * H s z) := by
    intro s hs
    have hmap : ∀ z : Plane, (s, z) ∈ Icc (0 : ℝ) T ×ˢ (univ : Set Plane) :=
      fun z => Set.mk_mem_prod hs (mem_univ z)
    have hcs : Continuous (fun z : Plane => ((s, z) : ℝ × Plane)) :=
      continuous_const.prodMk continuous_id
    have h1 : Continuous (fun z : Plane => H s z) := hH.comp_continuous hcs hmap
    exact ((apcc_eta_continuous R).comp continuous_snd).mul h1
  have hs_cont : ∀ a : Plane, ContinuousOn
      (fun s : ℝ => etaCutoff R a.2 * H s a) (Icc (0 : ℝ) T) := by
    intro a
    have hmap : MapsTo (fun s : ℝ => ((s, a) : ℝ × Plane)) (Icc (0 : ℝ) T)
        (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
      fun s hs => Set.mk_mem_prod hs (mem_univ a)
    have hcs : ContinuousOn (fun s : ℝ => ((s, a) : ℝ × Plane)) (Icc (0 : ℝ) T) :=
      (continuous_id.prodMk continuous_const).continuousOn
    have hc1 : ContinuousOn (fun s : ℝ => H s a) (Icc (0 : ℝ) T) := hH.comp hcs hmap
    exact continuousOn_const.mul hc1
  have hbound : ∀ s ∈ Icc (0 : ℝ) T, ∀ᵐ a ∂(volume.restrict (Cyl.cell c)),
      ‖etaCutoff R a.2 * H s a‖ ≤
        (Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)).indicator (fun _ : Plane => max C 0) a := by
    intro s hs
    filter_upwards [ae_restrict_mem hcell_meas] with a ha
    have hq0 : 0 ≤ H s a := hnn s hs a
    by_cases hb : a ∈ Icc (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)
    · have hbC : ‖H s a‖ ≤ C := hC (s, a) (Set.mk_mem_prod hs hb)
      rw [Real.norm_of_nonneg hq0] at hbC
      rw [Set.indicator_of_mem hb, Real.norm_of_nonneg (mul_nonneg (apcc_eta_nonneg R a.2) hq0)]
      exact (mul_le_of_le_one_left hq0 (apcc_eta_le_one R a.2)).trans
        (hbC.trans (le_max_left _ _))
    · have ha1 : a.1 ∈ Icc (-c / 2) (c / 2) := Ico_subset_Icc_self (Set.mem_prod.1 ha).1
      have hR2 : 2 * R ≤ |a.2| := by
        by_contra hlt
        rw [not_le] at hlt
        apply hb
        exact Set.mem_prod.2 ⟨ha1, Set.mem_Icc.2
          ⟨by linarith [neg_abs_le a.2], by linarith [le_abs_self a.2]⟩⟩
      rw [Set.indicator_of_notMem hb]
      simp [apcc_eta_eq_zero hR0 hR2]
  have hmain : ContinuousOn
      (fun s : ℝ => ∫ z, etaCutoff R z.2 * H s z ∂(volume.restrict (Cyl.cell c)))
      (Icc (0 : ℝ) T) :=
    MeasureTheory.continuousOn_of_dominated
      (F := fun s z => etaCutoff R z.2 * H s z)
      (fun s hs => (hz s hs).aestronglyMeasurable) hbound hbound_int
      (ae_of_all _ (fun a => hs_cont a))
  exact hmain

/-- Joint continuity of the jet applied to a fixed vector. -/
theorem apcc_jet_apply {G : ℝ → Plane → ℝ} {S : Set (ℝ × Plane)} {j : ℕ}
    (hJ : ContinuousOn (fun x : ℝ × Plane => iteratedFDeriv ℝ j (G x.1) x.2) S)
    (m : Fin j → Plane) :
    ContinuousOn (fun x : ℝ × Plane => iteratedFDeriv ℝ j (G x.1) x.2 m) S :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Plane) ℝ m).continuous.comp_continuousOn hJ

/-- Operator-norm cutoff jets (second vorticity jet and trilinear majorant) are continuous on
`[0,T]`; used for the measurability in `APLevel2Integ`. -/
theorem apcc_op_cont {ν c T : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}
    (hcls : IsAPrioriClass ν c T v p) (R : ℝ) (hR : 1 ≤ R) :
    ContinuousOn (fun s => ∫ z in Cyl.cell c, etaCutoff R z.2 *
      ‖iteratedFDeriv ℝ 2 (Cyl.curl (v s)) z‖ ^ 2) (Icc (0 : ℝ) T) ∧
    ContinuousOn (fun s => 4 * ∫ z in Cyl.cell c, etaCutoff R z.2 *
      (‖iteratedFDeriv ℝ 1 (Cyl.curl (v s)) z‖ ^ 2 * ‖iteratedFDeriv ℝ 1 (v s) z‖))
      (Icc (0 : ℝ) T) := by
  have hT : 0 < T := hcls.pos
  have hv := hcls.classical.smooth_v
  have hcurl := apcc_curl_smooth hT hv
  have hJv : ∀ j : ℕ, ContinuousOn (fun x : ℝ × Plane => iteratedFDeriv ℝ j (v x.1) x.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) := fun j => apcc_jet_joint hT hv j
  have hJc : ∀ j : ℕ, ContinuousOn
      (fun x : ℝ × Plane => iteratedFDeriv ℝ j (Cyl.curl (v x.1)) x.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) := fun j => apcc_jet_joint hT hcurl j
  have hH2 : ContinuousOn
      (fun x : ℝ × Plane => ‖iteratedFDeriv ℝ 2 (Cyl.curl (v x.1)) x.2‖ ^ 2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    ((hJc 2).norm).pow 2
  have hH3 : ContinuousOn
      (fun x : ℝ × Plane => ‖iteratedFDeriv ℝ 1 (Cyl.curl (v x.1)) x.2‖ ^ 2 *
        ‖iteratedFDeriv ℝ 1 (v x.1) x.2‖)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    (((hJc 1).norm).pow 2).mul (hJv 1).norm
  refine ⟨?_, ?_⟩
  · exact apcc_param c T R hR (fun s z => ‖iteratedFDeriv ℝ 2 (Cyl.curl (v s)) z‖ ^ 2) hH2
      (fun s _ z => sq_nonneg _)
  · exact continuousOn_const.mul (apcc_param c T R hR
      (fun s z => ‖iteratedFDeriv ℝ 1 (Cyl.curl (v s)) z‖ ^ 2 * ‖iteratedFDeriv ℝ 1 (v s) z‖)
      hH3 (fun s _ z => mul_nonneg (sq_nonneg _) (norm_nonneg _)))

/-- `PartI:T04/9/1/1`: the (Euclidean) cutoff jets are continuous on `[0,T]` for `R ≥ 1`. -/
theorem apLevel2CutCont : APLevel2CutCont := by
  intro ν c T v p hν hc hcls R hR
  have hT : 0 < T := hcls.pos
  have hv := hcls.classical.smooth_v
  have hcurl := apcc_curl_smooth hT hv
  have hS : ∀ s ∈ Icc (0 : ℝ) T, ContDiff ℝ ∞ (Cyl.curl (v s)) := fun s hs =>
    APEllipticCaux.curl_contDiff (by
      have h := hv.comp_contDiff
        ((contDiff_const : ContDiff ℝ ∞ (fun _ : Plane => s)).prodMk contDiff_id :
          ContDiff ℝ ∞ (fun z : Plane => ((s, z) : ℝ × Plane)))
        (fun z => (⟨hs, mem_univ z⟩ : ((s, z) : ℝ × Plane) ∈ Icc (0 : ℝ) T ×ˢ univ))
      exact h)
  have hJv : ∀ j : ℕ, ContinuousOn (fun x : ℝ × Plane => iteratedFDeriv ℝ j (v x.1) x.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) := fun j => apcc_jet_joint hT hv j
  have hJc : ∀ j : ℕ, ContinuousOn
      (fun x : ℝ × Plane => iteratedFDeriv ℝ j (Cyl.curl (v x.1)) x.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) := fun j => apcc_jet_joint hT hcurl j
  have hE1 : ContinuousOn (fun x : ℝ × Plane => eucJet1 (Cyl.curl (v x.1)) x.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) := by
    have : ContinuousOn (fun x : ℝ × Plane =>
        (iteratedFDeriv ℝ 1 (Cyl.curl (v x.1)) x.2 ![eQ]) ^ 2 +
          (iteratedFDeriv ℝ 1 (Cyl.curl (v x.1)) x.2 ![eE]) ^ 2)
        (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
      ((apcc_jet_apply (G := fun s => Cyl.curl (v s)) (hJc 1) ![eQ])).pow 2 |>.add (((apcc_jet_apply (G := fun s => Cyl.curl (v s)) (hJc 1) ![eE])).pow 2)
    exact this.congr (fun x hx => eucJet1_eq (hS x.1 hx.1) x.2)
  have hE2 : ContinuousOn (fun x : ℝ × Plane => eucJet2 (Cyl.curl (v x.1)) x.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) := by
    have : ContinuousOn (fun x : ℝ × Plane =>
        (iteratedFDeriv ℝ 2 (Cyl.curl (v x.1)) x.2 ![eQ, eQ]) ^ 2 +
          (iteratedFDeriv ℝ 2 (Cyl.curl (v x.1)) x.2 ![eQ, eE]) ^ 2 +
          (iteratedFDeriv ℝ 2 (Cyl.curl (v x.1)) x.2 ![eE, eQ]) ^ 2 +
          (iteratedFDeriv ℝ 2 (Cyl.curl (v x.1)) x.2 ![eE, eE]) ^ 2)
        (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
      (((((apcc_jet_apply (G := fun s => Cyl.curl (v s)) (hJc 2) ![eQ, eQ])).pow 2).add (((apcc_jet_apply (G := fun s => Cyl.curl (v s)) (hJc 2) ![eQ, eE])).pow 2)).add
        (((apcc_jet_apply (G := fun s => Cyl.curl (v s)) (hJc 2) ![eE, eQ])).pow 2)).add (((apcc_jet_apply (G := fun s => Cyl.curl (v s)) (hJc 2) ![eE, eE])).pow 2)
    exact this.congr (fun x hx => eucJet2_eq (hS x.1 hx.1) x.2)
  have hH2 : ContinuousOn (fun x : ℝ × Plane => eucJetN 2 (Cyl.curl (v x.1)) x.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    hE2.congr (fun x _ => eucJetN_two _ _)
  have hH3 : ContinuousOn
      (fun x : ℝ × Plane => eucJet1 (Cyl.curl (v x.1)) x.2 * ‖iteratedFDeriv ℝ 1 (v x.1) x.2‖)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    hE1.mul (hJv 1).norm
  refine ⟨?_, ?_⟩
  · exact apcc_param c T R hR (fun s z => eucJetN 2 (Cyl.curl (v s)) z) hH2
      (fun s _ z => eucJetN_nonneg _ _ _)
  · exact continuousOn_const.mul (apcc_param c T R hR
      (fun s z => eucJet1 (Cyl.curl (v s)) z * ‖iteratedFDeriv ℝ 1 (v s) z‖)
      hH3 (fun s _ z => mul_nonneg (eucJet1_nonneg _ _) (norm_nonneg _)))

end UnforcedLeray.Short.PartI
