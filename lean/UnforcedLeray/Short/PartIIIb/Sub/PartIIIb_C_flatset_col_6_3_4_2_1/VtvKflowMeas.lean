import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2_1
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.TrainSliceVel.Bridge

/-!
# `PartIII-b:C/flatset/col/6/3/4/2/1/3` (`vtvKflowMeas`): joint measurability of the flow kernel

Source of record: `the November 2 reference manuscript` (line 4610).
`vtvKflow` is `b₀ ∂₁Ψ - b₁ ∂₀Ψ - (b·∇E)φ` with `Ψ = νΔφ_s + v_r·∇φ_s`.  The factor `b` is
measurable; the other factors are `x`-partial derivatives of jointly smooth functions of
`((s,r),x)` on the open set `r > 0` (the train is smooth on `[0,∞) × ℝ²`, the test `∂_sη` is
smooth everywhere), so they are jointly continuous there.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The `j`-th partial derivative in the last slot, as a function of `(a, x)`. -/
def vtvFl_Dx {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α] (G : α × (ℝ × ℝ) → ℝ)
    (j : Fin 2) (p : α × (ℝ × ℝ)) : ℝ :=
  fderiv ℝ G p ((0 : α), B0579.dir j)

/-- The age derivative `∂_s` of the uncurried stream test. -/
def vtvFl_K (η : ℝ → ℝ × ℝ → ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ :=
  fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2) p ((1 : ℝ), (0 : ℝ × ℝ))

/-- The open set `{0 < r}` in the variables `((s,r),x)`. -/
abbrev vtvFl_U : Set ((ℝ × ℝ) × (ℝ × ℝ)) := (univ ×ˢ Ioi (0 : ℝ)) ×ˢ (univ : Set (ℝ × ℝ))

theorem vtvFl_U_open : IsOpen vtvFl_U :=
  (isOpen_univ.prod isOpen_Ioi).prod isOpen_univ

theorem vtvFl_mem {q : (ℝ × ℝ) × (ℝ × ℝ)} (hq : q ∈ vtvFl_U) : 0 < q.1.2 :=
  (Set.mem_prod.1 (Set.mem_prod.1 hq).1).2

theorem vtvFl_K_contDiff (η : ℝ → ℝ × ℝ → ℝ)
    (hsm : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2)) :
    ContDiff ℝ ∞ (vtvFl_K η) :=
  (contDiff_infty_iff_fderiv.1 hsm).2.clm_apply contDiff_const

theorem vtvFl_deriv_eq (η : ℝ → ℝ × ℝ → ℝ)
    (hsm : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2)) (s : ℝ) (x : ℝ × ℝ) :
    deriv (fun s' => η s' x) s = vtvFl_K η (s, x) := by
  have hGdiff : Differentiable ℝ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2) :=
    hsm.differentiable (by simp)
  have hG : HasFDerivAt (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2)
      (fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2) (s, x)) (s, x) :=
    (hGdiff (s, x)).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => ((t, x) : ℝ × (ℝ × ℝ))) ((1 : ℝ), (0 : ℝ × ℝ)) s :=
    (hasDerivAt_id' s).prodMk (hasDerivAt_const s x)
  have hcomp := hG.comp_hasDerivAt s hline
  exact hcomp.deriv

theorem vtvFl_dgen {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    (F : α × (ℝ × ℝ) → ℝ) (a : α) (x : ℝ × ℝ) (j : Fin 2)
    (hF : DifferentiableAt ℝ F (a, x)) :
    B0579.pd j (fun y => F (a, y)) x = vtvFl_Dx F j (a, x) := by
  have hd : HasFDerivAt (fun y : ℝ × ℝ => F (a, y))
      ((fderiv ℝ F (a, x)).comp (ContinuousLinearMap.inr ℝ α (ℝ × ℝ))) x :=
    hF.hasFDerivAt.comp x (hasFDerivAt_prodMk_right a x)
  unfold B0579.pd vtvFl_Dx
  rw [hd.fderiv]
  rfl

theorem vtvFl_dx_contDiff {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    (G : α × (ℝ × ℝ) → ℝ) (hG : ContDiff ℝ ∞ G) (j : Fin 2) :
    ContDiff ℝ ∞ (vtvFl_Dx G j) :=
  (contDiff_infty_iff_fderiv.1 hG).2.clm_apply contDiff_const

theorem vtvFl_dx_cont {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    (G : α × (ℝ × ℝ) → ℝ) {U : Set (α × (ℝ × ℝ))} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) (j : Fin 2) : ContinuousOn (vtvFl_Dx G j) U :=
  (hG.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const

theorem vtvFl_K_pd (η : ℝ → ℝ × ℝ → ℝ)
    (hsm : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2)) (s : ℝ) (y : ℝ × ℝ) (k : Fin 2) :
    B0579.pd k (fun x => deriv (fun s' => η s' x) s) y = vtvFl_Dx (vtvFl_K η) k (s, y) := by
  have hfun : (fun x : ℝ × ℝ => deriv (fun s' => η s' x) s) = fun x => vtvFl_K η (s, x) :=
    funext fun x => vtvFl_deriv_eq η hsm s x
  rw [hfun]
  exact vtvFl_dgen (vtvFl_K η) s y k ((vtvFl_K_contDiff η hsm).differentiable (by simp) _)

/-- The Laplacian of the test `∂_sη(s)` at `x`, as a function of `(s, x)`. -/
def vtvFl_Lap (η : ℝ → ℝ × ℝ → ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ :=
  vtvFl_Dx (vtvFl_Dx (vtvFl_K η) 0) 0 p + vtvFl_Dx (vtvFl_Dx (vtvFl_K η) 1) 1 p

theorem vtvFl_lap_contDiff (η : ℝ → ℝ × ℝ → ℝ)
    (hsm : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2)) :
    ContDiff ℝ ∞ (vtvFl_Lap η) :=
  have hK := vtvFl_K_contDiff η hsm
  (vtvFl_dx_contDiff _ (vtvFl_dx_contDiff _ hK 0) 0).add
    (vtvFl_dx_contDiff _ (vtvFl_dx_contDiff _ hK 1) 1)

theorem vtvFl_lapP (η : ℝ → ℝ × ℝ → ℝ)
    (hsm : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2)) (s : ℝ) (y : ℝ × ℝ) :
    UnforcedLeray.Short.IIIa.lapP (fun x => deriv (fun s' => η s' x) s) y = vtvFl_Lap η (s, y) := by
  have hK := vtvFl_K_contDiff η hsm
  have h0 : B0579.pd 0 (fun x => deriv (fun s' => η s' x) s) =
      fun z => vtvFl_Dx (vtvFl_K η) 0 (s, z) :=
    funext fun z => vtvFl_K_pd η hsm s z 0
  have h1 : B0579.pd 1 (fun x => deriv (fun s' => η s' x) s) =
      fun z => vtvFl_Dx (vtvFl_K η) 1 (s, z) :=
    funext fun z => vtvFl_K_pd η hsm s z 1
  have d0 : DifferentiableAt ℝ (vtvFl_Dx (vtvFl_K η) 0) (s, y) :=
    ((vtvFl_dx_contDiff _ hK 0).differentiable (by simp)) _
  have d1 : DifferentiableAt ℝ (vtvFl_Dx (vtvFl_K η) 1) (s, y) :=
    ((vtvFl_dx_contDiff _ hK 1).differentiable (by simp)) _
  unfold UnforcedLeray.Short.IIIa.lapP vtvFl_Lap
  rw [h0, h1, vtvFl_dgen (vtvFl_Dx (vtvFl_K η) 0) s y 0 d0,
    vtvFl_dgen (vtvFl_Dx (vtvFl_K η) 1) s y 1 d1]

/-- The velocity-weighted test `Ψ` written as a function of `((s,r),x)`. -/
def vtvFl_Wq {ν c : ℝ} (η : ℝ → ℝ × ℝ → ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  ν * vtvFl_Lap η (q.1.1, q.2) +
    (tr.v q.1.2 q.2 0 * vtvFl_Dx (vtvFl_K η) 0 (q.1.1, q.2) +
      tr.v q.1.2 q.2 1 * vtvFl_Dx (vtvFl_K η) 1 (q.1.1, q.2))

theorem vtvFl_Wq_eq {ν c : ℝ} (η : ℝ → ℝ × ℝ → ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hsm : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2)) (a y : ℝ × ℝ) :
    vtvFl_Wq η tr (a, y) = ν * UnforcedLeray.Short.IIIa.lapP
        (fun x => deriv (fun s' => η s' x) a.1) y +
      (tr.v a.2 y 0 * B0579.pd 0 (fun x => deriv (fun s' => η s' x) a.1) y +
        tr.v a.2 y 1 * B0579.pd 1 (fun x => deriv (fun s' => η s' x) a.1) y) := by
  unfold vtvFl_Wq
  dsimp only
  rw [vtvFl_lapP η hsm a.1 y, vtvFl_K_pd η hsm a.1 y 0, vtvFl_K_pd η hsm a.1 y 1]

theorem vtvFl_Wq_contDiffOn {ν c : ℝ} (η : ℝ → ℝ × ℝ → ℝ)
    (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hsm : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2)) :
    ContDiffOn ℝ ∞ (vtvFl_Wq η tr) vtvFl_U := by
  have hK := vtvFl_K_contDiff η hsm
  have hmap : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × (ℝ × ℝ) => ((q.1.2, q.2) : ℝ × (ℝ × ℝ))) :=
    (contDiff_snd.comp contDiff_fst).prodMk contDiff_snd
  have hmap2 : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × (ℝ × ℝ) => ((q.1.1, q.2) : ℝ × (ℝ × ℝ))) :=
    (contDiff_fst.comp contDiff_fst).prodMk contDiff_snd
  have hV : ∀ i : Fin 2, ContDiffOn ℝ ∞ (fun q : (ℝ × ℝ) × (ℝ × ℝ) => tr.v q.1.2 q.2 i) vtvFl_U :=
    fun i =>
      ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn
        tr.isTrain.smooth_v).comp hmap.contDiffOn
        (fun q hq => Set.mem_prod.2 ⟨mem_Ici.2 (le_of_lt (vtvFl_mem hq)), mem_univ _⟩)
  have hLap : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × (ℝ × ℝ) => vtvFl_Lap η (q.1.1, q.2)) :=
    (vtvFl_lap_contDiff η hsm).comp hmap2
  have hD0 : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × (ℝ × ℝ) => vtvFl_Dx (vtvFl_K η) 0 (q.1.1, q.2)) :=
    (vtvFl_dx_contDiff _ hK 0).comp hmap2
  have hD1 : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × (ℝ × ℝ) => vtvFl_Dx (vtvFl_K η) 1 (q.1.1, q.2)) :=
    (vtvFl_dx_contDiff _ hK 1).comp hmap2
  exact (contDiffOn_const.mul hLap.contDiffOn).add
    ((hV 0).mul hD0.contDiffOn |>.add ((hV 1).mul hD1.contDiffOn))

theorem vtvKflowMeas : VtvKflowMeas := by
  intro ν c μ tr om g b G f H η hη
  have hsm : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => η q.1 q.2) := hη.1
  have hE : IsEnergyField c b G := H.2.2.2.1
  have hK := vtvFl_K_contDiff η hsm
  have hW := vtvFl_Wq_contDiffOn η tr hsm
  have hEcU : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (UnforcedLeray.Short.IIIa.Ec_contDiffOn tr).mono
      (prod_mono Ioi_subset_Ici_self (subset_refl _))
  have hIopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  set T : Set ((ℝ × ℝ) × (ℝ × ℝ)) := (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) ×ˢ B0579.cell c with hTdef
  have hTU : T ⊆ vtvFl_U := fun q hq =>
    ⟨⟨mem_univ _, (Set.mem_prod.1 (Set.mem_prod.1 hq).1).2⟩, mem_univ _⟩
  have hμ : ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))).prod
      (volume.restrict (B0579.cell c)) = (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))).restrict T := by
    rw [Measure.prod_restrict, Measure.prod_restrict, ← Measure.volume_eq_prod,
      ← Measure.volume_eq_prod]
  rw [hμ]
  have hTm : MeasurableSet T :=
    (measurableSet_Ioi.prod measurableSet_Ioi).prod (B0579.measurableSet_cell c)
  have hmapU : ContinuousOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) => ((q.1.2, q.2) : ℝ × (ℝ × ℝ)))
      vtvFl_U :=
    (((continuous_snd.comp continuous_fst).prodMk continuous_snd)).continuousOn
  have hmap2c : Continuous (fun q : (ℝ × ℝ) × (ℝ × ℝ) => ((q.1.1, q.2) : ℝ × (ℝ × ℝ))) :=
    (continuous_fst.comp continuous_fst).prodMk continuous_snd
  have hbm : ∀ i : Fin 2, Measurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => b (q.1.2, q.2) i) :=
    fun i => (hE.measurable i).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hWc : ∀ j : Fin 2, ContinuousOn
      (fun q : (ℝ × ℝ) × (ℝ × ℝ) => ((vtvFl_Dx (vtvFl_Wq η tr) j (q.1, q.2) : ℝ) : ℂ)) vtvFl_U :=
    fun j => Complex.continuous_ofReal.comp_continuousOn
      (vtvFl_dx_cont (vtvFl_Wq η tr) vtvFl_U_open hW j)
  have hEc : ∀ j : Fin 2, ContinuousOn
      (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        ((vtvFl_Dx (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2) j (q.1.2, q.2) : ℝ) : ℂ))
      vtvFl_U := fun j =>
    Complex.continuous_ofReal.comp_continuousOn
      (ContinuousOn.comp (vtvFl_dx_cont _ hIopen hEcU j) hmapU
        (fun q hq => Set.mem_prod.2 ⟨mem_Ioi.2 (vtvFl_mem hq), mem_univ _⟩))
  have hP : ContinuousOn
      (fun q : (ℝ × ℝ) × (ℝ × ℝ) => ((vtvFl_K η (q.1.1, q.2) : ℝ) : ℂ)) vtvFl_U :=
    (Complex.continuous_ofReal.comp (hK.continuous.comp hmap2c)).continuousOn
  have hF : AEStronglyMeasurable
      (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        b (q.1.2, q.2) 0 * ((vtvFl_Dx (vtvFl_Wq η tr) 1 (q.1, q.2) : ℝ) : ℂ) -
          b (q.1.2, q.2) 1 * ((vtvFl_Dx (vtvFl_Wq η tr) 0 (q.1, q.2) : ℝ) : ℂ) -
          (b (q.1.2, q.2) 0 *
              ((vtvFl_Dx (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2) 0 (q.1.2, q.2) : ℝ) : ℂ) +
            b (q.1.2, q.2) 1 *
              ((vtvFl_Dx (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2) 1 (q.1.2, q.2) : ℝ) : ℂ)) *
            ((vtvFl_K η (q.1.1, q.2) : ℝ) : ℂ))
      (volume.restrict T) := by
    have hb0 : AEStronglyMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => b (q.1.2, q.2) 0)
        (volume.restrict T) := (hbm 0).aestronglyMeasurable
    have hb1 : AEStronglyMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => b (q.1.2, q.2) 1)
        (volume.restrict T) := (hbm 1).aestronglyMeasurable
    have hW1 := ((hWc 1).mono hTU).aestronglyMeasurable (μ := volume) hTm
    have hW0 := ((hWc 0).mono hTU).aestronglyMeasurable (μ := volume) hTm
    have hE0 := ((hEc 0).mono hTU).aestronglyMeasurable (μ := volume) hTm
    have hE1 := ((hEc 1).mono hTU).aestronglyMeasurable (μ := volume) hTm
    have hP' := (hP.mono hTU).aestronglyMeasurable (μ := volume) hTm
    exact (((hb0.mul hW1).sub (hb1.mul hW0)).sub (((hb0.mul hE0).add (hb1.mul hE1)).mul hP'))
  have key : ∀ q ∈ vtvFl_U,
      vtvKflow tr b (fun s x => deriv (fun s' => η s' x) s) q.1 q.2 =
        b (q.1.2, q.2) 0 * ((vtvFl_Dx (vtvFl_Wq η tr) 1 (q.1, q.2) : ℝ) : ℂ) -
          b (q.1.2, q.2) 1 * ((vtvFl_Dx (vtvFl_Wq η tr) 0 (q.1, q.2) : ℝ) : ℂ) -
          (b (q.1.2, q.2) 0 *
              ((vtvFl_Dx (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2) 0 (q.1.2, q.2) : ℝ) : ℂ) +
            b (q.1.2, q.2) 1 *
              ((vtvFl_Dx (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2) 1 (q.1.2, q.2) : ℝ) : ℂ)) *
            ((vtvFl_K η (q.1.1, q.2) : ℝ) : ℂ) := by
    intro q hq
    have hr : 0 < q.1.2 := vtvFl_mem hq
    have hdW : DifferentiableAt ℝ (vtvFl_Wq η tr) (q.1, q.2) :=
      (hW.contDiffAt (vtvFl_U_open.mem_nhds hq)).differentiableAt (by simp)
    have hdE : DifferentiableAt ℝ (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2)
        (q.1.2, q.2) :=
      (hEcU.contDiffAt (hIopen.mem_nhds (Set.mem_prod.2 ⟨mem_Ioi.2 hr, mem_univ _⟩))).differentiableAt
        (by simp)
    have hEcpd : ∀ j : Fin 2, B0579.pd j (UnforcedLeray.B0238.Ec tr q.1.2) q.2 =
        vtvFl_Dx (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2) j (q.1.2, q.2) :=
      fun j => vtvFl_dgen (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2)
        q.1.2 q.2 j hdE
    have hpsi : (fun y : ℝ × ℝ => ν * UnforcedLeray.Short.IIIa.lapP
          (fun x => deriv (fun s' => η s' x) q.1.1) y +
        (tr.v q.1.2 y 0 * B0579.pd 0 (fun x => deriv (fun s' => η s' x) q.1.1) y +
          tr.v q.1.2 y 1 * B0579.pd 1 (fun x => deriv (fun s' => η s' x) q.1.1) y)) =
        fun y => vtvFl_Wq η tr (q.1, y) :=
      funext fun y => (vtvFl_Wq_eq η tr hsm q.1 y).symm
    unfold vtvKflow vtvFlowRHS
    dsimp only
    rw [hpsi, vtvFl_dgen (vtvFl_Wq η tr) q.1 q.2 1 hdW, vtvFl_dgen (vtvFl_Wq η tr) q.1 q.2 0 hdW,
      hEcpd 0, hEcpd 1, vtvFl_deriv_eq η hsm q.1.1 q.2]
  refine AEStronglyMeasurable.congr hF ?_
  refine (ae_restrict_iff' hTm).2 (Eventually.of_forall fun q hq => ?_)
  exact (key q (hTU hq)).symm

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
