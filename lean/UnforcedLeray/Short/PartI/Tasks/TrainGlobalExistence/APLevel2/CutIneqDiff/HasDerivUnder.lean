import UnforcedLeray.Short.PartI.Sub.PartI_T04_9_1_2_2
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnstrophy.HasDeriv

/-!
# Part I, `PartI:T04/9/1/2/2/1`: differentiation under the integral (`APL2HasDerivUnder`)

Source lines 285-288.  For `s ∈ (0,T)` and `R ≥ 1`, `G¹_R(t) = ∫_cell χ_R (P_t² + Q_t²)` with
`P_t = ∂_q ω(t)`, `Q_t = ∂_η ω(t)`.  Both `W_e(t,z) = ∂_e ω(t)(z)` are `C²` on the open strip, so the
template `apHD_deriv_integral` applies to each of the two summands.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff Interval

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- The vorticity as a function on the space-time strip. -/
def tdOm (v : ℝ → Plane → Vec) : ℝ × Plane → ℝ :=
  fun y => Cyl.curl (v y.1) y.2

/-- Space-time derivative of the vorticity in the direction `(0,e)`. -/
def tdW (v : ℝ → Plane → Vec) (e : Plane) : ℝ × Plane → ℝ :=
  fun x => fderiv ℝ (tdOm v) x ((0 : ℝ), e)

theorem tdSlice_hasFDeriv {v : ℝ → Plane → Vec} {s : ℝ} {z : Plane}
    (hd : DifferentiableAt ℝ (tdOm v) (s, z)) :
    HasFDerivAt (Cyl.curl (v s))
      ((fderiv ℝ (tdOm v) (s, z)).comp (ContinuousLinearMap.inr ℝ ℝ Plane)) z := by
  have hg : HasFDerivAt (fun w : Plane => ((s, w) : ℝ × Plane))
      (ContinuousLinearMap.inr ℝ ℝ Plane) z := hasFDerivAt_prodMk_right s z
  exact hd.hasFDerivAt.comp z hg

theorem tdSlice_fderiv {v : ℝ → Plane → Vec} {s : ℝ} {z : Plane}
    (hd : DifferentiableAt ℝ (tdOm v) (s, z)) (e : Plane) :
    fderiv ℝ (Cyl.curl (v s)) z e = fderiv ℝ (tdOm v) (s, z) ((0 : ℝ), e) := by
  rw [(tdSlice_hasFDeriv hd).fderiv]
  simp

theorem tdPartialQ_eq {v : ℝ → Plane → Vec} {s : ℝ} {z : Plane}
    (hd : DifferentiableAt ℝ (tdOm v) (s, z)) :
    Cyl.partialQ (Cyl.curl (v s)) z = tdW v eQ (s, z) := by
  have hdz : DifferentiableAt ℝ (Cyl.curl (v s)) z := (tdSlice_hasFDeriv hd).differentiableAt
  rw [UnforcedLeray.Short.PartI.partialQ_eq_fderiv hdz, tdSlice_fderiv hd]
  rfl

theorem tdPartialEta_eq {v : ℝ → Plane → Vec} {s : ℝ} {z : Plane}
    (hd : DifferentiableAt ℝ (tdOm v) (s, z)) :
    Cyl.partialEta (Cyl.curl (v s)) z = tdW v eE (s, z) := by
  have hdz : DifferentiableAt ℝ (Cyl.curl (v s)) z := (tdSlice_hasFDeriv hd).differentiableAt
  rw [UnforcedLeray.Short.PartI.partialEta_eq_fderiv hdz, tdSlice_fderiv hd]
  rfl

theorem tdEucJet1_eq {v : ℝ → Plane → Vec} {s : ℝ} {z : Plane}
    (hd : DifferentiableAt ℝ (tdOm v) (s, z)) :
    eucJet1 (Cyl.curl (v s)) z = tdW v eQ (s, z) * tdW v eQ (s, z)
      + tdW v eE (s, z) * tdW v eE (s, z) := by
  unfold eucJet1
  rw [tdPartialQ_eq hd, tdPartialEta_eq hd]
  ring

/-- **`PartI:T04/9/1/2/2/1`**: the cutoff enstrophy `G¹_R` has derivative `apL2W` at `s ∈ (0,T)`. -/
theorem aPL2HasDerivUnder : APL2HasDerivUnder := by
  intro ν c T v p hν hc hcls R hR s hs
  have hT : (0 : ℝ) < T := hcls.pos
  have hc0 : (0 : ℝ) < c := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hv := hcls.classical.smooth_v
  have hΩS : ContDiffOn ℝ ∞ (tdOm v) (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    apcc_curl_smooth hT hv
  have hUS : Ioo (0 : ℝ) T ×ˢ (univ : Set Plane) ⊆ Icc (0 : ℝ) T ×ˢ (univ : Set Plane) :=
    Set.prod_mono Ioo_subset_Icc_self subset_rfl
  have hU_open : IsOpen (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) := isOpen_Ioo.prod isOpen_univ
  have hΩU : ContDiffOn ℝ ∞ (tdOm v) (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    hΩS.mono hUS
  have hdiffΩ : ∀ x ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set Plane), DifferentiableAt ℝ (tdOm v) x :=
    fun x hx => (hΩU.contDiffAt (hU_open.mem_nhds hx)).differentiableAt (by simp)
  have hWc : ∀ e : Plane, ContDiffOn ℝ 2 (tdW v e) (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) := by
    intro e
    exact (hΩU.fderiv_of_isOpen hU_open (m := 2) (by simp)).clm_apply contDiffOn_const
  have hslice : ∀ f : ℝ × Plane → ℝ, ContinuousOn f (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) →
      ∀ t ∈ Ioo (0 : ℝ) T, Continuous (fun z : Plane => f (t, z)) := by
    intro f hf t ht
    exact hf.comp_continuous (f := fun z : Plane => (t, z)) (by fun_prop)
      (fun z => Set.mk_mem_prod ht (mem_univ z))
  have hcontW : ∀ e : Plane, ∀ t ∈ Ioo (0 : ℝ) T, Continuous (fun z : Plane => tdW v e (t, z)) :=
    fun e t ht => hslice (tdW v e) (hWc e).continuousOn t ht
  have hFc : ∀ e : Plane, ContinuousOn
      (fun x : ℝ × Plane => fderiv ℝ (tdW v e) x ((1 : ℝ), (0 : Plane)))
      (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) := fun e =>
    ((hWc e).continuousOn_fderiv_of_isOpen hU_open (by norm_num)).clm_apply continuousOn_const
  have hcontF : ∀ e : Plane, ∀ t ∈ Ioo (0 : ℝ) T,
      Continuous (fun z : Plane => fderiv ℝ (tdW v e) (t, z) ((1 : ℝ), (0 : Plane))) :=
    fun e t ht => hslice (fun x : ℝ × Plane => fderiv ℝ (tdW v e) x ((1 : ℝ), (0 : Plane)))
      (hFc e) t ht
  have hIntSq : ∀ e : Plane, ∀ t ∈ Ioo (0 : ℝ) T,
      IntegrableOn (fun z : Plane => etaCutoff R z.2 * (tdW v e (t, z) * tdW v e (t, z)))
        (Cyl.cell c) := by
    intro e t ht
    have hc1 : Continuous (fun z : Plane => etaCutoff R z.2 * (tdW v e (t, z) * tdW v e (t, z))) :=
      ((apcc_eta_continuous R).comp continuous_snd).mul ((hcontW e t ht).mul (hcontW e t ht))
    exact apHD_integ (c := c) (R0 := 2 * R) hc1 (fun z hz => by
      simp [apcc_eta_eq_zero hR0 hz.le])
  have hIntA : ∀ e : Plane, IntegrableOn (fun z : Plane => etaCutoff R z.2 *
      (fderiv ℝ (tdW v e) (s, z) ((1 : ℝ), (0 : Plane)) * tdW v e (s, z)
        + tdW v e (s, z) * fderiv ℝ (tdW v e) (s, z) ((1 : ℝ), (0 : Plane))))
      (Cyl.cell c) := by
    intro e
    have hc1 : Continuous (fun z : Plane => etaCutoff R z.2 *
        (fderiv ℝ (tdW v e) (s, z) ((1 : ℝ), (0 : Plane)) * tdW v e (s, z)
          + tdW v e (s, z) * fderiv ℝ (tdW v e) (s, z) ((1 : ℝ), (0 : Plane)))) :=
      ((apcc_eta_continuous R).comp continuous_snd).mul
        (((hcontF e s hs).mul (hcontW e s hs)).add ((hcontW e s hs).mul (hcontF e s hs)))
    exact apHD_integ (c := c) (R0 := 2 * R) hc1 (fun z hz => by
      simp [apcc_eta_eq_zero hR0 hz.le])
  have hA : ∀ e : Plane, HasDerivAt
      (fun t => ∫ z in Cyl.cell c, etaCutoff R z.2 * (tdW v e (t, z) * tdW v e (t, z)))
      (∫ z in Cyl.cell c, etaCutoff R z.2 *
        (fderiv ℝ (tdW v e) (s, z) ((1 : ℝ), (0 : Plane)) * tdW v e (s, z)
          + tdW v e (s, z) * fderiv ℝ (tdW v e) (s, z) ((1 : ℝ), (0 : Plane)))) s :=
    fun e => apHD_deriv_integral (apcc_eta_continuous R)
      (fun x hx => apHD_eta_zero hR0 hx.le) (fun x => apHD_eta_abs R x) (hWc e) c hc0 hs.1 hs.2
  have hpoint : ∀ t ∈ Ioo (0 : ℝ) T, apCutG c 1 v R t =
      (∫ z in Cyl.cell c, etaCutoff R z.2 * (tdW v eQ (t, z) * tdW v eQ (t, z)))
        + ∫ z in Cyl.cell c, etaCutoff R z.2 * (tdW v eE (t, z) * tdW v eE (t, z)) := by
    intro t ht
    unfold apCutG
    rw [← integral_add (hIntSq eQ t ht) (hIntSq eE t ht)]
    congr 1
    funext z
    rw [eucJetN_one, tdEucJet1_eq (hdiffΩ (t, z) (Set.mk_mem_prod ht (mem_univ z)))]
    ring
  have hev : apCutG c 1 v R =ᶠ[𝓝 s] (fun t =>
      (∫ z in Cyl.cell c, etaCutoff R z.2 * (tdW v eQ (t, z) * tdW v eQ (t, z)))
        + ∫ z in Cyl.cell c, etaCutoff R z.2 * (tdW v eE (t, z) * tdW v eE (t, z))) :=
    Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) hpoint
  have hD := ((hA eQ).add (hA eE)).congr_of_eventuallyEq hev
  refine HasDerivAt.congr_deriv hD ?_
  -- the time derivative of the integrand at `s`
  have hdQ : ∀ z : Plane, deriv (fun t => Cyl.partialQ (Cyl.curl (v t)) z) s
      = fderiv ℝ (tdW v eQ) (s, z) ((1 : ℝ), (0 : Plane)) := by
    intro z
    have hev' : (fun t => Cyl.partialQ (Cyl.curl (v t)) z) =ᶠ[𝓝 s] (fun t => tdW v eQ (t, z)) :=
      Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) (fun t ht =>
        tdPartialQ_eq (hdiffΩ (t, z) (Set.mk_mem_prod ht (mem_univ z))))
    rw [hev'.deriv_eq]
    exact (apHD_deriv_at (hWc eQ) hs.1 hs.2 z).deriv
  have hdE : ∀ z : Plane, deriv (fun t => Cyl.partialEta (Cyl.curl (v t)) z) s
      = fderiv ℝ (tdW v eE) (s, z) ((1 : ℝ), (0 : Plane)) := by
    intro z
    have hev' : (fun t => Cyl.partialEta (Cyl.curl (v t)) z) =ᶠ[𝓝 s] (fun t => tdW v eE (t, z)) :=
      Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) (fun t ht =>
        tdPartialEta_eq (hdiffΩ (t, z) (Set.mk_mem_prod ht (mem_univ z))))
    rw [hev'.deriv_eq]
    exact (apHD_deriv_at (hWc eE) hs.1 hs.2 z).deriv
  rw [← integral_add (hIntA eQ) (hIntA eE)]
  unfold apL2W
  congr 1
  funext z
  have hPz : Cyl.partialQ (Cyl.curl (v s)) z = tdW v eQ (s, z) :=
    tdPartialQ_eq (hdiffΩ (s, z) (Set.mk_mem_prod hs (mem_univ z)))
  have hQz : Cyl.partialEta (Cyl.curl (v s)) z = tdW v eE (s, z) :=
    tdPartialEta_eq (hdiffΩ (s, z) (Set.mk_mem_prod hs (mem_univ z)))
  rw [hdQ z, hdE z, hPz, hQz]
  ring

end UnforcedLeray.Short.PartI
