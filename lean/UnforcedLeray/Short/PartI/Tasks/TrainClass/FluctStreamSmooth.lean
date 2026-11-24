import UnforcedLeray.Short.PartI.Sub.T01Class
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.HmeanContDiff
import UnforcedLeray.Short.PartI.Tasks.TrainClass.FluctStreamSmooth.Prim

/-!
# Part I, task `PartI:TC/7`: the fluctuation of the stream is jointly smooth

Source of record: `the November 2 reference manuscript`, lines 397-404 (the
mean stream `S = \bar ψ`) and lines 261-288 (the train is the BUC solution).  The Prop is
`FluctStreamSmooth` (`Sub/T01Class.lean`): for every train, `(s,q,η) ↦ ψ(s,q,η) - S(s,η)` is
`C^∞` on `(0,∞) × ℝ²`.

Route.  Write `F(s,z) = ∫_0^{z₁} v₂(s,t,z₂) dt` (`fluctPrim`, `z = (q,η)`), i.e.
`F(s,(q,η)) = q ∫_0^1 v₂(s,qτ,η) dτ`.
* `F` is jointly smooth on `(0,∞) × ℝ²` (`fluctPrim_contDiffOn`): a parametric integral over
  `[0,1]` (`FluctPrim.contDiff_primitive01`) in the log-age variable.
* `ψ(s,q,η) - ψ(s,0,η) = F(s,(q,η))` (`fluctPrim_eq`): the fundamental theorem of calculus in `q`,
  since `∂_qψ = v₂` (`stream`, `perpendicularGradient`).
* Hence `S(s,η) = ψ(s,0,η) + \bar F(s,η)` (`meanStream_eq`), so
  `ψ - S = F - \bar F` (`fluct_identity`), which is `C^∞` by `hmeanContDiff`.

Helper module: `Short/PartI/Tasks/TrainClass/FluctStreamSmooth/Prim.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (toVec_one)

/-- The primitive `F(s,z) = z₁ ∫_0^1 v₂(s, z₁ τ, z₂) dτ = ∫_0^{z₁} v₂(s,t,z₂) dt`, written on
`x = (s, z) ∈ ℝ × Plane`; `x.2.1 = q`, `x.2.2 = η`, and `e^{log s} = s` for `s > 0`. -/
def fluctPrim {ν c : ℝ} (tr : B0140.TrainSol ν c) (x : ℝ × Plane) : ℝ :=
  x.2.1 * ∫ τ in (0 : ℝ)..1, tr.v (Real.exp (Real.log x.1)) (x.2.1 * τ, x.2.2) 1

/-- The second velocity component `v₂ = ∂_q ψ` is jointly `C^∞` on `(0,∞) × ℝ²`. -/
theorem fluct_G_contDiffOn {ν c : ℝ} (tr : B0140.TrainSol ν c) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2 1) (Ioi 0 ×ˢ univ) := by
  have h1 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self subset_rfl)
  exact (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn h1

/-- The parametric integrand `(τ, (t, (q, η))) ↦ v₂(e^t, q τ, η)` gives a `C^∞` integral in
`(t, (q, η))`. -/
theorem fluct_K_contDiff {ν c : ℝ} (tr : B0140.TrainSol ν c) :
    ContDiff ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => ∫ τ in (0 : ℝ)..1,
      tr.v (Real.exp y.1) (y.2.1 * τ, y.2.2) 1) := by
  have hΞ : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × (ℝ × ℝ)) =>
      ((Real.exp p.2.1, (p.2.2.1 * p.1, p.2.2.2)) : ℝ × Plane)) := by
    fun_prop
  have hΦ : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × (ℝ × ℝ)) =>
      tr.v (Real.exp p.2.1) (p.2.2.1 * p.1, p.2.2.2) 1) :=
    (fluct_G_contDiffOn tr).comp_contDiff hΞ
      (fun p => ⟨Set.mem_Ioi.2 (Real.exp_pos _), Set.mem_univ _⟩)
  exact FluctPrim.contDiff_primitive01 hΦ

/-- The primitive `F` is jointly `C^∞` on `(0,∞) × ℝ²`. -/
theorem fluctPrim_contDiffOn {ν c : ℝ} (tr : B0140.TrainSol ν c) :
    ContDiffOn ℝ ∞ (fluctPrim tr) (Ioi 0 ×ˢ univ) := by
  have hlog : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => ((Real.log x.1, x.2) : ℝ × Plane))
      (Ioi 0 ×ˢ univ) :=
    ContDiffOn.prodMk
      (Real.contDiffOn_log.comp contDiffOn_fst (fun x hx => (Set.mem_Ioi.1 hx.1).ne'))
      contDiffOn_snd
  have hK := (fluct_K_contDiff tr).comp_contDiffOn hlog
  have hfst : ContDiff ℝ ∞ (fun x : ℝ × Plane => x.2.1) := by fun_prop
  exact hfst.contDiffOn.mul hK

/-- Fundamental theorem of calculus in `q`: for `s > 0`, `F(s,(q,η)) = ψ(s,q,η) - ψ(s,0,η)`,
because `∂_qψ(s,·,η) = v₂(s,·,η)` (`stream`: `v = toVec (perpendicularGradient ψ)`). -/
theorem fluctPrim_eq {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 < s) (q η : ℝ) :
    fluctPrim tr (s, (q, η)) = tr.ψ s (q, η) - tr.ψ s (0, η) := by
  have hψd : Differentiable ℝ (tr.ψ s) := tr.isTrain.stream_differentiable s hs.le
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => tr.ψ s (t', η)) (tr.v s (t, η) 1) t := by
    intro t
    have hpath : HasDerivAt (fun t' : ℝ => ((t', η) : Plane)) ((1 : ℝ), (0 : ℝ)) t :=
      (hasDerivAt_id' t).prodMk (hasDerivAt_const t η)
    have hdiffAt : DifferentiableAt ℝ (fun t' : ℝ => tr.ψ s (t', η)) t :=
      (hψd (t, η)).comp t hpath.differentiableAt
    have hval : tr.v s (t, η) 1 = deriv (fun t' : ℝ => tr.ψ s (t', η)) t := by
      rw [tr.isTrain.stream s hs.le (t, η), toVec_one]
      rfl
    rw [hval]
    exact hdiffAt.hasDerivAt
  have hcontG : Continuous (fun t : ℝ => tr.v s (t, η) 1) := by
    have hmap : Continuous (fun t : ℝ => ((s, (t, η)) : ℝ × Plane)) :=
      continuous_const.prodMk (continuous_id.prodMk continuous_const)
    exact (fluct_G_contDiffOn tr).continuousOn.comp_continuous hmap
      (fun t => ⟨Set.mem_Ioi.2 hs, Set.mem_univ _⟩)
  have hFTC : ∫ t in (0 : ℝ)..q, tr.v s (t, η) 1 = tr.ψ s (q, η) - tr.ψ s (0, η) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t' : ℝ => tr.ψ s (t', η)) (f' := fun t : ℝ => tr.v s (t, η) 1)
      (fun t _ => hderiv t) (hcontG.intervalIntegrable _ _)
  rw [← hFTC]
  have key := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => tr.v s (t, η) 1) q
  simp only [smul_eq_mul, mul_zero, mul_one] at key
  show q * ∫ τ in (0 : ℝ)..1, tr.v (Real.exp (Real.log s)) (q * τ, η) 1 = _
  rw [Real.exp_log hs]
  exact key

/-- The mean stream at age `s > 0`: `S(s,η) = ψ(s,0,η) + \bar F(s,η)`, where `\bar F` is the
horizontal average (`hmean`) of `F(s,·)`. -/
theorem meanStream_eq {ν c : ℝ} (tr : B0140.TrainSol ν c) (hc : 0 < c) {s : ℝ} (hs : 0 < s)
    (η : ℝ) :
    meanStream tr s η = tr.ψ s (0, η) + hmean c (fun z => fluctPrim tr (s, z)) η := by
  have hψc : Continuous (fun q : ℝ => tr.ψ s (q, η)) :=
    (tr.isTrain.stream_differentiable s hs.le).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hFc : Continuous (fun q : ℝ => fluctPrim tr (s, (q, η))) := by
    have hfun : (fun q : ℝ => fluctPrim tr (s, (q, η))) =
        fun q : ℝ => tr.ψ s (q, η) - tr.ψ s (0, η) :=
      funext fun q => fluctPrim_eq tr hs q η
    rw [hfun]
    exact hψc.sub continuous_const
  have hint : EqOn (fun q : ℝ => tr.ψ s (q, η))
      (fun q : ℝ => tr.ψ s (0, η) + fluctPrim tr (s, (q, η))) (Ioc (-c / 2) (c / 2)) := by
    intro q _
    dsimp only
    rw [fluctPrim_eq tr hs q η]
    ring
  have hvol : volume.real (Ioc (-c / 2) (c / 2)) = c := by
    rw [Real.volume_real_Ioc_of_le (by linarith)]
    ring
  have hI1 : Integrable (fun _ : ℝ => tr.ψ s (0, η))
      (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    integrable_const _
  have hI2 : Integrable (fun q : ℝ => fluctPrim tr (s, (q, η)))
      (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    hFc.integrableOn_Ioc
  have hA : ∫ q in Ioc (-c / 2) (c / 2), tr.ψ s (q, η) =
      c • tr.ψ s (0, η) + ∫ q in Ioc (-c / 2) (c / 2), fluctPrim tr (s, (q, η)) := by
    rw [setIntegral_congr_fun measurableSet_Ioc hint, integral_add hI1 hI2, setIntegral_const,
      hvol]
  unfold meanStream hmean
  rw [hA, smul_add, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

/-- The fluctuation identity at age `s > 0`: `ψ - S = F - \bar F`. -/
theorem fluct_identity {ν c : ℝ} (tr : B0140.TrainSol ν c) (hc : 0 < c) {s : ℝ} (hs : 0 < s)
    (q η : ℝ) :
    tr.ψ s (q, η) - meanStream tr s η =
      fluctPrim tr (s, (q, η)) - hmean c (fun z => fluctPrim tr (s, z)) η := by
  rw [meanStream_eq tr hc hs η, fluctPrim_eq tr hs q η]
  ring

/-- **`PartI:TC/7`. The fluctuation of the stream is jointly smooth** (any train; lines 397-404):
`(s,q,η) ↦ ψ(s,q,η) - S(s,η)` is `C^∞` on `(0,∞) × ℝ²`. -/
theorem fluctStreamSmooth : FluctStreamSmooth := by
  intro ν c _ hc tr
  have hFp := fluctPrim_contDiffOn tr
  have hHm : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => hmean c (fun z => fluctPrim tr (x.1, z)) x.2)
      (Ioi 0 ×ˢ univ) :=
    hmeanContDiff c hc (fun s z => fluctPrim tr (s, z)) hFp
  have hproj : ContDiff ℝ ∞ (fun x : ℝ × Plane => ((x.1, x.2.2) : ℝ × ℝ)) := by fun_prop
  have hHm' : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => hmean c (fun z => fluctPrim tr (x.1, z)) x.2.2) (Ioi 0 ×ˢ univ) :=
    hHm.comp hproj.contDiffOn (fun x hx => ⟨hx.1, Set.mem_univ _⟩)
  refine (hFp.sub hHm').congr fun x hx => ?_
  exact fluct_identity tr hc hx.1 x.2.1 x.2.2

end UnforcedLeray.Short.PartI
