import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2.JointSmoothUpgrade.TrainJets
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2.JointSmoothUpgrade.CylP0Smooth
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2.JointSmoothUpgrade.TimeTower
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_1_7.Mixed

/-!
# Part II-b, Task `PartII-b:F8/1/org/2/3`: Joint Space-Time Smooth Upgrade (`RealCylOseenJointSmoothUpgrade`)

Source of record: `the November 2 reference manuscript`,
lines 270–288, 2213–2217, 2296–2301.

Upgrades spatially smooth `C((0, 2); H^∞(C_c))` slices `w` of a weak `C([0, 2]; H¹_σ(C_c))` Oseen
solution driven by the shifted BUC train `F8Ex.shiftedDriftTrain tr σ` (`0 < c`, `0 < ν`, `0 ≤ σ`)
to a jointly `C^∞((0, 2) × ℝ²)` interior classical orbit `W_reg (s, y) := w s y` satisfying
`F8Ex.IsRealInteriorSmoothOrbit`.

## Proof Architecture
1. `JointSmoothUpgrade/TrainJets.lean`: all-order mixed age-and-spatial derivative bounds on compact
   subintervals `[T₁, T₂] ⊂ (0, 2)` for `F8Ex.shiftedDriftTrain tr σ` at arbitrary `0 < c`, `0 < ν`.
2. `JointSmoothUpgrade/CylP0Smooth.lean`: `0 < c` cylinder Sobolev sup estimates, `Cyl.divFree c`
   Liouville uniqueness against solenoidal cylinder tests, and `P0Smooth c` on `IsCylSmoothHInf c`.
3. `JointSmoothUpgrade/TimeTower.lean`: `H^∞(C_c)` time-derivative tower `wSeq` on `(0, 2)` and
   `BwdRoute.Joint.Tower` verification on every compact subinterval `[T₁, T₂] ⊂ (0, 2)`.
4. `JointSmoothUpgrade.lean` (this file): applies `BwdRoute.Joint.mixedSmooth` on exhausting compact
   subintervals `[T₁, T₂] ⊂ (0, 2)` to obtain joint `C^∞` regularity on `(0, 2) × ℝ²`, identifies
   `∂_s ∂^α W_reg` with `∂^α (wSeq 1)` via chain rule, and proves `(1, ≤ 2)` `L²(cell)` continuity
   and `L²_σ(C_c)` orthogonality of `F8Ex.realHomResidual`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIb.F8JointUpgrade

open UnforcedLeray
open UnforcedLeray.Short.IIb

/-- Joint `C^∞` regularity of `(s, y) ↦ w s y` on `(0, 2) × ℝ²` by applying
`BwdRoute.Joint.mixedSmooth` to `tower_wSeq_on_subinterval` on exhausting compact subintervals. -/
lemma w_jointSmooth {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (tr : B0140.TrainSol ν c) (hbuc : PartI.IsBUCTrain tr) {σ : ℝ} (hσ : 0 ≤ σ)
    {u uq uη : B0579.Plane → F8Ex.RMerid}
    {W Wq Wη w : ℝ → B0579.Plane → F8Ex.RMerid}
    (hdat : F8Ex.IsRealCylH1Datum c u uq uη)
    (hwk : F8Ex.IsRealWeakH1OseenSol c ν (F8Ex.shiftedDriftTrain tr σ) W Wq Wη u uq uη)
    (hsp : F8Ex.IsRealSpatialSmoothOseenSlices c w W Wq Wη) :
    ContDiffOn ℝ ∞ (fun x : Coord => w x.1 x.2) (Ioo (0 : ℝ) 2 ×ˢ univ) := by
  rintro ⟨s₀, y₀⟩ ⟨hs₀, -⟩
  let T₁ : ℝ := s₀ / 2
  let T₂ : ℝ := (s₀ + 2) / 2
  have hT₁ : 0 < T₁ := by dsimp [T₁]; linarith [hs₀.1]
  have hT₁₂ : T₁ < T₂ := by dsimp [T₁, T₂]; linarith [hs₀.2]
  have hT₂ : T₂ < 2 := by dsimp [T₂]; linarith [hs₀.2]
  have hcomp_k : ∀ k : Fin 2,
      ContDiffOn ℝ ∞ (fun x : Coord => w x.1 x.2 k) (Icc T₁ T₂ ×ˢ univ) := by
    intro k
    have htow := tower_wSeq_on_subinterval hc hν tr hbuc hσ hdat hwk hsp hT₁ hT₁₂ hT₂ k
    have hms : ContDiffOn ℝ ∞ (fun z : ℝ × B0579.Plane => w (T₁ + z.1) z.2 k)
        (Icc 0 (T₂ - T₁) ×ˢ univ) :=
      BwdRoute.Joint.mixedSmooth (T₂ - T₁) _ (sub_pos.mpr hT₁₂) htow
    let sh : Coord → ℝ × B0579.Plane := fun x => (x.1 - T₁, x.2)
    have hsh : ContDiff ℝ ∞ sh := (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
    have hmap : MapsTo sh (Icc T₁ T₂ ×ˢ univ) (Icc 0 (T₂ - T₁) ×ˢ univ) := by
      rintro ⟨s, y⟩ ⟨hs, -⟩
      exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, trivial⟩
    refine (hms.comp hsh.contDiffOn hmap).congr fun ⟨s, y⟩ _ => ?_
    dsimp [sh]
    rw [add_sub_cancel]
  let L0 : ℝ →L[ℝ] F8Ex.RMerid := (ContinuousLinearMap.id ℝ ℝ).smulRight F8Ex.eR0
  let L1 : ℝ →L[ℝ] F8Ex.RMerid := (ContinuousLinearMap.id ℝ ℝ).smulRight F8Ex.eR1
  have hcd_box : ContDiffOn ℝ ∞ (fun x : Coord => w x.1 x.2) (Icc T₁ T₂ ×ˢ univ) := by
    have hsum : ContDiffOn ℝ ∞ (fun x : Coord => L0 (w x.1 x.2 0) + L1 (w x.1 x.2 1))
        (Icc T₁ T₂ ×ˢ univ) :=
      (L0.contDiff.comp_contDiffOn (hcomp_k 0)).add (L1.contDiff.comp_contDiffOn (hcomp_k 1))
    refine hsum.congr fun x _ => ?_
    ext i
    fin_cases i <;> simp [L0, L1, F8Ex.eR0, F8Ex.eR1]
  have hnhds : Icc T₁ T₂ ×ˢ (univ : Set B0579.Plane) ∈ 𝓝 (s₀, y₀) := by
    have hmem_open : (s₀, y₀) ∈ Ioo T₁ T₂ ×ˢ (univ : Set B0579.Plane) :=
      ⟨⟨by dsimp [T₁]; linarith [hs₀.1], by dsimp [T₂]; linarith [hs₀.2]⟩, trivial⟩
    exact Filter.mem_of_superset ((isOpen_Ioo.prod isOpen_univ).mem_nhds hmem_open)
      (prod_mono Ioo_subset_Icc_self Subset.rfl)
  exact (hcd_box.contDiffAt hnhds).contDiffWithinAt

/-- Chain-rule identification of the space-time age derivative `∂_s ∂^α W_reg` on `(0, 2) × ℝ²`
with the slice derivative `∂^α (wSeq 1)` of the first tower level. -/
lemma psR_pdIterR_eq_wSeq_one {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (tr : B0140.TrainSol ν c) (hbuc : PartI.IsBUCTrain tr) {σ : ℝ} (hσ : 0 ≤ σ)
    {u uq uη : B0579.Plane → F8Ex.RMerid}
    {W Wq Wη w : ℝ → B0579.Plane → F8Ex.RMerid}
    (hdat : F8Ex.IsRealCylH1Datum c u uq uη)
    (hwk : F8Ex.IsRealWeakH1OseenSol c ν (F8Ex.shiftedDriftTrain tr σ) W Wq Wη u uq uη)
    (hsp : F8Ex.IsRealSpatialSmoothOseenSlices c w W Wq Wη)
    (hsmooth : ContDiffOn ℝ ∞ (fun x : Coord => w x.1 x.2) F8Ex.strip0)
    {n : ℕ} (α : Fin n → Fin 2) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) (y : B0579.Plane) :
    F8Ex.psR (F8Ex.pdIterR α (fun x : Coord => w x.1 x.2)) (s, y) =
      F8Ex.slicePdIterR α (wSeq c ν (F8Ex.shiftedDriftTrain tr σ) w 1 s) y := by
  let W_reg : F8Ex.RProf := fun x => w x.1 x.2
  have hx : (s, y) ∈ F8Ex.strip0 := ⟨hs, trivial⟩
  have hd_jt : DifferentiableAt ℝ (F8Ex.pdIterR α W_reg) (s, y) :=
    ((F8Ex.contDiffOn_pdR hsmooth α).contDiffAt
      (F8Ex.isOpen_strip0.mem_nhds hx)).differentiableAt (by simp)
  have hemb : HasDerivAt (fun r : ℝ => ((r, y) : Coord)) (1, (0, 0)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
  have hd1 : HasDerivAt (fun r => F8Ex.pdIterR α W_reg (r, y))
      (F8Ex.psR (F8Ex.pdIterR α W_reg) (s, y)) s :=
    hd_jt.hasFDerivAt.comp_hasDerivAt s hemb
  have hev : (fun r => F8Ex.pdIterR α W_reg (r, y)) =ᶠ[𝓝 s]
      fun r => F8Ex.slicePdIterR α (w r) y := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
    exact F8Ex.pdIterR_uncurry_eq_slicePdIterR hsmooth α hr y
  have hd2 := (hasHInfDerivOn_wSeq hc hν tr hbuc hσ hdat hwk hsp 0).hasDerivAt_slicePdIterR
    hc α hs y
  exact hd1.unique (hd2.congr_of_eventuallyEq hev)

/-- Pointwise formula for the unprojected Oseen residual `F8Ex.realHomResidual` on `(0, 2) × ℝ²`:
it equals `(I - P0Smooth c) (bvOp (V s) (w s))`. -/
lemma realHomResidual_eq_sub_P0Smooth {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (tr : B0140.TrainSol ν c) (hbuc : PartI.IsBUCTrain tr) {σ : ℝ} (hσ : 0 ≤ σ)
    {u uq uη : B0579.Plane → F8Ex.RMerid}
    {W Wq Wη w : ℝ → B0579.Plane → F8Ex.RMerid}
    (hdat : F8Ex.IsRealCylH1Datum c u uq uη)
    (hwk : F8Ex.IsRealWeakH1OseenSol c ν (F8Ex.shiftedDriftTrain tr σ) W Wq Wη u uq uη)
    (hsp : F8Ex.IsRealSpatialSmoothOseenSlices c w W Wq Wη)
    (hsmooth : ContDiffOn ℝ ∞ (fun x : Coord => w x.1 x.2) F8Ex.strip0)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) (y : B0579.Plane) :
    F8Ex.realHomResidual ν (F8Ex.shiftedDriftTrain tr σ) (fun x : Coord => w x.1 x.2) (s, y) =
      bvOp (F8Ex.shiftedDriftTrain tr σ s) (w s) y -
        P0Smooth c (bvOp (F8Ex.shiftedDriftTrain tr σ s) (w s)) y := by
  let V := F8Ex.shiftedDriftTrain tr σ
  let W_reg : F8Ex.RProf := fun x => w x.1 x.2
  have hps : F8Ex.psR W_reg (s, y) =
      ν • sliceLapR (w s) y - P0Smooth c (bvOp (V s) (w s)) y := by
    have h0 := psR_pdIterR_eq_wSeq_one hc hν tr hbuc hσ hdat hwk hsp hsmooth Fin.elim0 hs y
    change F8Ex.psR W_reg (s, y) = wSeq c ν V w 1 s y at h0
    rw [h0, wSeq_one_eq]
    rfl
  have hp00 : F8Ex.pdR 0 (F8Ex.pdR 0 W_reg) (s, y) =
      F8Ex.slicePdR 0 (F8Ex.slicePdR 0 (w s)) y :=
    F8Ex.pdIterR_uncurry_eq_slicePdIterR hsmooth ![0, 0] hs y
  have hp11 : F8Ex.pdR 1 (F8Ex.pdR 1 W_reg) (s, y) =
      F8Ex.slicePdR 1 (F8Ex.slicePdR 1 (w s)) y :=
    F8Ex.pdIterR_uncurry_eq_slicePdIterR hsmooth ![1, 1] hs y
  have hq : F8Ex.sliceR (F8Ex.pdR 0 W_reg) s = F8Ex.slicePdR 0 (w s) := by
    funext z
    exact F8Ex.pdR_uncurry_eq_slicePdR hsmooth hs 0 z
  have he : F8Ex.sliceR (F8Ex.pdR 1 W_reg) s = F8Ex.slicePdR 1 (w s) := by
    funext z
    exact F8Ex.pdR_uncurry_eq_slicePdR hsmooth hs 1 z
  unfold F8Ex.realHomResidual
  change F8Ex.psR W_reg (s, y) -
      ν • (F8Ex.pdR 0 (F8Ex.pdR 0 W_reg) (s, y) + F8Ex.pdR 1 (F8Ex.pdR 1 W_reg) (s, y)) +
      F8Ex.realBvSlice (V s) (w s) (F8Ex.sliceR (F8Ex.pdR 0 W_reg) s)
        (F8Ex.sliceR (F8Ex.pdR 1 W_reg) s) y = _
  rw [hps, hp00, hp11, hq, he]
  change (ν • sliceLapR (w s) y - P0Smooth c (bvOp (V s) (w s)) y) -
      ν • sliceLapR (w s) y + bvOp (V s) (w s) y = _
  abel

end UnforcedLeray.Short.IIb.F8JointUpgrade

namespace UnforcedLeray.Short.IIb

open F8JointUpgrade

/-- **Target theorem** (`PartII-b:F8/1/org/2/3`, SP 270–288, 2213–2217, 2296–2301):
joint space-time `C^∞` upgrade, `(1, ≤ 2)` `L²(cell)` slice continuity, and `L²_σ(C_c)` residual
orthogonality for spatially smooth Oseen slices driven by the shifted BUC train. -/
theorem realCylOseenJointSmoothUpgrade_proof :
    UnforcedLeray.Short.IIb.RealCylOseenJointSmoothUpgrade := by
  intro c ν hc hν tr hbuc σ hσ u uq uη W Wq Wη w hdat hwk hsp
  let V := F8Ex.shiftedDriftTrain tr σ
  let W_reg : F8Ex.RProf := fun x => w x.1 x.2
  have hsmooth : ContDiffOn ℝ ∞ W_reg (Ioo (0 : ℝ) 2 ×ˢ univ) :=
    w_jointSmooth hc hν tr hbuc hσ hdat hwk hsp
  have hw1 : IsHInfContOn c (wSeq c ν V w 1) :=
    (hasHInfDerivOn_wSeq hc hν tr hbuc hσ hdat hwk hsp 0).u'_cont
  have hbv_cont : IsHInfContOn c (fun s => bvOp (V s) (w s)) := by
    simpa only [dtIterV_zero] using
      (isHInfContOn_of_spatialSmoothSlices hsp).bvOp_dtIterV hc hν tr hbuc hσ 0
  refine ⟨W_reg, F8Ex.isRealInteriorSmoothOrbit_of_joint hsp hsmooth ?_ ?_ ?_⟩
  · -- `hmem_s`: `MemLp (sliceR (psR (pdIterR α W_reg)) s) 2 (cellMeas c)`
    intro s hs n _ α
    have heq : F8Ex.sliceR (F8Ex.psR (F8Ex.pdIterR α W_reg)) s =
        F8Ex.slicePdIterR α (wSeq c ν V w 1 s) := by
      funext y
      exact psR_pdIterR_eq_wSeq_one hc hν tr hbuc hσ hdat hwk hsp hsmooth α hs y
    rw [heq]
    exact (hw1.hinf hs).memL2 n α
  · -- `hcont_s`: `L²(cell)` slice continuity of `∂_s ∂^α W_reg` on `(0, 2)`
    intro s hs n _ α
    have htend_norm : Tendsto
        (fun t => ‖uL2 c α (wSeq c ν V w 1) t - uL2 c α (wSeq c ν V w 1) s‖) (𝓝 s) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp (hw1.continuousAt α hs)
    have htend_enn : Tendsto
        (fun t => ENNReal.ofReal ‖uL2 c α (wSeq c ν V w 1) t - uL2 c α (wSeq c ν V w 1) s‖)
        (𝓝 s) (𝓝 0) := by
      have hcomp := (ENNReal.continuous_ofReal.tendsto 0).comp htend_norm
      rw [ENNReal.ofReal_zero] at hcomp
      exact hcomp
    refine htend_enn.congr' ?_
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    have hlp : uL2 c α (wSeq c ν V w 1) t - uL2 c α (wSeq c ν V w 1) s =
        toLpCell (((hw1.hinf ht).memL2 n α).sub ((hw1.hinf hs).memL2 n α)) := by
      rw [hw1.uL2_eq α ht, hw1.uL2_eq α hs, ← toLpCell_sub]
    rw [hlp, ofReal_norm_toLpCell]
    have hfun : (fun y => F8Ex.slicePdIterR α (wSeq c ν V w 1 t) y -
          F8Ex.slicePdIterR α (wSeq c ν V w 1 s) y) =
        fun y => F8Ex.psR (F8Ex.pdIterR α W_reg) (t, y) -
          F8Ex.psR (F8Ex.pdIterR α W_reg) (s, y) := by
      funext y
      rw [psR_pdIterR_eq_wSeq_one hc hν tr hbuc hσ hdat hwk hsp hsmooth α ht y,
        psR_pdIterR_eq_wSeq_one hc hν tr hbuc hσ hdat hwk hsp hsmooth α hs y]
    change F8Ex.cellL2R c (fun y => F8Ex.slicePdIterR α (wSeq c ν V w 1 t) y -
      F8Ex.slicePdIterR α (wSeq c ν V w 1 s) y) = _
    rw [hfun]
  · -- `hproj`: `L²_σ(C_c)` orthogonality of `realHomResidual`
    intro s hs φ hmφ hsolφ
    have hbv_s : IsCylSmoothHInf c (bvOp (V s) (w s)) := hbv_cont.hinf hs
    let hm_bv := hbv_s.memL2 0 Fin.elim0
    let hm_p0 := (P0Smooth_isCylSmoothHInf hc hbv_s).memL2 0 Fin.elim0
    have hres_pt : ∀ y : B0579.Plane,
        F8Ex.realHomResidual ν (F8Ex.shiftedDriftTrain tr σ) (fun x : Coord => w x.1 x.2) (s, y) =
          (bvOp (V s) (w s) - P0Smooth c (bvOp (V s) (w s))) y :=
      fun y => realHomResidual_eq_sub_P0Smooth hc hν tr hbuc hσ hdat hwk hsp hsmooth hs y
    have hφ_div : toLpCell hmφ ∈ Cyl.divFree c := (toLpCell_mem_divFree_iff hmφ).mpr hsolφ
    simp_rw [hres_pt]
    change ∫ y in B0579.cell c,
      ⟪φ y, (F8Ex.slicePdIterR Fin.elim0 (bvOp (V s) (w s)) -
        F8Ex.slicePdIterR Fin.elim0 (P0Smooth c (bvOp (V s) (w s)))) y⟫_ℝ = 0
    rw [← inner_toLpCell_eq hmφ (hm_bv.sub hm_p0), toLpCell_sub hm_bv hm_p0,
      toLpCell_P0Smooth hc hbv_s,
      inner_sub_right, ← Cyl.inner_P0_comm, Cyl.P0_eq_self hφ_div, sub_self]

end UnforcedLeray.Short.IIb
