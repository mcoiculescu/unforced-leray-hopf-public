import UnforcedLeray.Short.PartI.Sub.PartI_T04_9_1_2
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutCont
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnstrophy.HasDeriv

/-!
# Part I, `PartI:T04/9/1/2/1`: `apRReg` (regularity of the cutoff enstrophy `G¹_R`)

Source of record: `the November 2 reference manuscript`, lines 285-288.

For `R ≥ 1`, `G¹_R(s) = ∫_cell χ_R(η) |Dω(s)|²` (Euclidean, `eucJet1`).

* continuity on `[0,T]`: `apcc_param` with `H = eucJet1 (curl v)`, jointly continuous (as in
  `apLevel2CutCont`);
* differentiability on `(0,T)`: `|Dω|² = (∂_q ω)² + (∂_η ω)²` and the space-time derivatives
  `W_e(t,z) = ∂_e ω(t)(z)` are `C^∞` on the open strip (`apRW`); differentiate under the integral
  with `apHD_deriv_integral`;
* integrability of the derivative on `[0,T]`: the derivative is bounded on `(0,T)` by the second
  space-time derivatives of `curl v`, which are continuous on the closed strip, hence bounded on the
  compact box.
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
def apROm (v : ℝ → Plane → Vec) : ℝ × Plane → ℝ :=
  fun y => Cyl.curl (v y.1) y.2

/-- Space-time derivative of the vorticity in the direction `(0,e)`; for fixed `t` this is the
spatial derivative `∂_e ω(t)`. -/
def apRW (v : ℝ → Plane → Vec) (e : Plane) : ℝ × Plane → ℝ :=
  fun x => fderiv ℝ (apROm v) x ((0 : ℝ), e)

/-- The time-derivative of `apRW` in direction `(1,0)`, integrated over the cell. -/
def apRDint (v : ℝ → Plane → Vec) (e : Plane) (R c r : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, etaCutoff R z.2 *
    (fderiv ℝ (apRW v e) (r, z) ((1 : ℝ), (0 : Plane)) * apRW v e (r, z)
      + apRW v e (r, z) * fderiv ℝ (apRW v e) (r, z) ((1 : ℝ), (0 : Plane)))

theorem apR_slice_hasFDeriv {v : ℝ → Plane → Vec} {s : ℝ} {z : Plane}
    (hd : DifferentiableAt ℝ (apROm v) (s, z)) :
    HasFDerivAt (Cyl.curl (v s))
      ((fderiv ℝ (apROm v) (s, z)).comp (ContinuousLinearMap.inr ℝ ℝ Plane)) z := by
  have hg : HasFDerivAt (fun w : Plane => ((s, w) : ℝ × Plane))
      (ContinuousLinearMap.inr ℝ ℝ Plane) z := hasFDerivAt_prodMk_right s z
  exact hd.hasFDerivAt.comp z hg

theorem apR_slice_fderiv {v : ℝ → Plane → Vec} {s : ℝ} {z e : Plane}
    (hd : DifferentiableAt ℝ (apROm v) (s, z)) :
    fderiv ℝ (Cyl.curl (v s)) z e = fderiv ℝ (apROm v) (s, z) ((0 : ℝ), e) := by
  rw [(apR_slice_hasFDeriv hd).fderiv]
  simp

theorem apR_eucJet1 {v : ℝ → Plane → Vec} {s : ℝ} {z : Plane}
    (hd : DifferentiableAt ℝ (apROm v) (s, z)) :
    eucJet1 (Cyl.curl (v s)) z =
      apRW v eQ (s, z) * apRW v eQ (s, z) + apRW v eE (s, z) * apRW v eE (s, z) := by
  unfold eucJet1
  have hdz : DifferentiableAt ℝ (Cyl.curl (v s)) z := (apR_slice_hasFDeriv hd).differentiableAt
  rw [UnforcedLeray.Short.PartI.partialQ_eq_fderiv hdz,
    UnforcedLeray.Short.PartI.partialEta_eq_fderiv hdz, apR_slice_fderiv hd,
    apR_slice_fderiv hd]
  unfold apRW
  ring

theorem apR_fderiv_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (a m : E) :
    fderiv ℝ (fun y => fderiv ℝ f y m) x a = iteratedFDeriv ℝ 2 f x ![a, m] := by
  rw [iteratedFDeriv_two_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have := fderiv_clm_apply (c := fderiv ℝ f) (u := fun _ : E => m) hd (differentiableAt_const m)
  have h0 : fderiv ℝ (fun _ : E => m) x = 0 := by rw [fderiv_fun_const]; rfl
  rw [this, h0]
  simp

theorem apR_bound_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x y : E) : |fderiv ℝ f x y| ≤ ‖iteratedFDeriv ℝ 1 f x‖ * ‖y‖ := by
  have h := (iteratedFDeriv ℝ 1 f x).le_opNorm (fun _ : Fin 1 => y)
  rw [iteratedFDeriv_one_apply] at h
  simpa [Real.norm_eq_abs] using h

theorem apR_bound_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (a m : E) :
    |fderiv ℝ (fun y => fderiv ℝ f y m) x a| ≤ ‖iteratedFDeriv ℝ 2 f x‖ * ‖a‖ * ‖m‖ := by
  rw [apR_fderiv_fderiv hf a m]
  have h := (iteratedFDeriv ℝ 2 f x).le_opNorm ![a, m]
  simpa [Real.norm_eq_abs, Fin.prod_univ_two, mul_assoc] using h

theorem apR_cell_bound {c R M : ℝ} (hc : 0 < c) (hM : 0 ≤ M) (f : Plane → ℝ)
    (hf : ∀ z : Plane, 2 * R < |z.2| → f z = 0)
    (hb : ∀ z : Plane, |z.1| ≤ c → |z.2| ≤ 2 * R → |f z| ≤ M) :
    ‖∫ z in Cyl.cell c, f z‖ ≤
      ∫ z in Cyl.cell c, (Icc (-c) c ×ˢ Icc (-(2 * R)) (2 * R)).indicator (fun _ : Plane => M) z := by
  have hcellm : MeasurableSet (Cyl.cell c) := by
    unfold Cyl.cell
    exact measurableSet_Ico.prod MeasurableSet.univ
  have hbox : IsCompact (Icc (-c) c ×ˢ Icc (-(2 * R)) (2 * R)) :=
    isCompact_Icc.prod isCompact_Icc
  have hint : Integrable ((Icc (-c) c ×ˢ Icc (-(2 * R)) (2 * R)).indicator (fun _ : Plane => M))
      (volume.restrict (Cyl.cell c)) := by
    rw [integrable_indicator_iff hbox.isClosed.measurableSet]
    refine integrableOn_const ?_
    rw [Measure.restrict_apply hbox.isClosed.measurableSet]
    exact ne_top_of_le_ne_top hbox.measure_lt_top.ne (measure_mono inter_subset_left)
  apply norm_integral_le_of_norm_le hint
  filter_upwards [ae_restrict_mem hcellm] with z hz
  have hz1 : |z.1| ≤ c := by
    have h := hz
    simp only [Cyl.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true] at h
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  by_cases h2 : |z.2| ≤ 2 * R
  · have hm : z ∈ Icc (-c) c ×ˢ Icc (-(2 * R)) (2 * R) := ⟨abs_le.1 hz1, abs_le.1 h2⟩
    rw [Set.indicator_of_mem hm]
    exact hb z hz1 h2
  · rw [hf z (not_le.1 h2), norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hM) z

theorem apRReg : APL2Reg := by
  intro ν c T v p hν hc hcls R hR
  have hT : (0 : ℝ) < T := hcls.pos
  have hv := hcls.classical.smooth_v
  have hR0 : (0 : ℝ) < R := by linarith
  have hc0 : (0 : ℝ) < c := by linarith
  -- the closed strip, the open strip and the box
  have hΩS : ContDiffOn ℝ ∞ (apROm v) (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    apcc_curl_smooth hT hv
  have hUS : Ioo (0 : ℝ) T ×ˢ (univ : Set Plane) ⊆ Icc (0 : ℝ) T ×ˢ (univ : Set Plane) :=
    Set.prod_mono Ioo_subset_Icc_self subset_rfl
  have hU_open : IsOpen (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) := isOpen_Ioo.prod isOpen_univ
  have hSuniq : UniqueDiffOn ℝ (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    UniqueDiffOn.prod (uniqueDiffOn_Icc hT) uniqueDiffOn_univ
  have hΩU : ContDiffOn ℝ ∞ (apROm v) (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    hΩS.mono hUS
  have hΩdiff : ∀ x ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set Plane), ContDiffAt ℝ ∞ (apROm v) x :=
    fun x hx => hΩU.contDiffAt (hU_open.mem_nhds hx)
  have hWc : ∀ e : Plane,
      ContDiffOn ℝ 2 (apRW v e) (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) := by
    intro e
    exact (hΩU.fderiv_of_isOpen hU_open (m := 2) (by simp)).clm_apply contDiffOn_const
  -- continuity of the cutoff enstrophy on [0,T]
  have hcurl := apcc_curl_smooth hT hv
  have hS : ∀ s ∈ Icc (0 : ℝ) T, ContDiff ℝ ∞ (Cyl.curl (v s)) := fun s hs =>
    APEllipticCaux.curl_contDiff (by
      have h := hv.comp_contDiff
        ((contDiff_const : ContDiff ℝ ∞ (fun _ : Plane => s)).prodMk contDiff_id :
          ContDiff ℝ ∞ (fun z : Plane => ((s, z) : ℝ × Plane)))
        (fun z => (⟨hs, mem_univ z⟩ : ((s, z) : ℝ × Plane) ∈ Icc (0 : ℝ) T ×ˢ univ))
      exact h)
  have hJc1 : ContinuousOn (fun x : ℝ × Plane => iteratedFDeriv ℝ 1 (Cyl.curl (v x.1)) x.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) := apcc_jet_joint hT hcurl 1
  have hE1 : ContinuousOn (fun x : ℝ × Plane => eucJet1 (Cyl.curl (v x.1)) x.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) := by
    have : ContinuousOn (fun x : ℝ × Plane =>
        (iteratedFDeriv ℝ 1 (Cyl.curl (v x.1)) x.2 ![eQ]) ^ 2 +
          (iteratedFDeriv ℝ 1 (Cyl.curl (v x.1)) x.2 ![eE]) ^ 2)
        (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
      ((apcc_jet_apply (G := fun s => Cyl.curl (v s)) hJc1 ![eQ]).pow 2).add
        ((apcc_jet_apply (G := fun s => Cyl.curl (v s)) hJc1 ![eE]).pow 2)
    exact this.congr (fun x hx => eucJet1_eq (hS x.1 hx.1) x.2)
  have hfunc : apCutG c 1 v R =
      fun s => ∫ z in Cyl.cell c, etaCutoff R z.2 * eucJet1 (Cyl.curl (v s)) z := by
    funext s
    unfold apCutG
    congr 1
  have hcont : ContinuousOn (apCutG c 1 v R) (Icc (0 : ℝ) T) := by
    rw [hfunc]
    exact apcc_param c T R hR (fun s z => eucJet1 (Cyl.curl (v s)) z) hE1
      (fun s _ z => eucJet1_nonneg _ _)
  -- bounds on the box
  have hφc : Continuous (etaCutoff R) := apcc_eta_continuous R
  have hφv : ∀ x : ℝ, 2 * R < |x| → etaCutoff R x = 0 :=
    fun x hx => apHD_eta_zero hR0 hx.le
  have hKS : Icc (0 : ℝ) T ×ˢ (Icc (-c) c ×ˢ Icc (-(2 * R)) (2 * R)) ⊆
      Icc (0 : ℝ) T ×ˢ (univ : Set Plane) :=
    Set.prod_mono subset_rfl (subset_univ _)
  have hKc : IsCompact (Icc (0 : ℝ) T ×ˢ (Icc (-c) c ×ˢ Icc (-(2 * R)) (2 * R))) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hJ1 : ContinuousOn (iteratedFDerivWithin ℝ 1 (apROm v) (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)))
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    hΩS.continuousOn_iteratedFDerivWithin (m := 1) (by simp) hSuniq
  have hJ2 : ContinuousOn (iteratedFDerivWithin ℝ 2 (apROm v) (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)))
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    hΩS.continuousOn_iteratedFDerivWithin (m := 2) (by simp) hSuniq
  obtain ⟨C1, hC1⟩ := hKc.exists_bound_of_continuousOn (hJ1.mono hKS)
  obtain ⟨C2, hC2⟩ := hKc.exists_bound_of_continuousOn (hJ2.mono hKS)
  have hb1 : ∀ x : ℝ × Plane, x ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set Plane) →
      x.2 ∈ Icc (-c) c ×ˢ Icc (-(2 * R)) (2 * R) → ‖iteratedFDeriv ℝ 1 (apROm v) x‖ ≤ C1 := by
    intro x hx hb
    rw [← iteratedFDerivWithin_eq_iteratedFDeriv hSuniq
      (show ContDiffAt ℝ 1 (apROm v) x from (hΩdiff x hx).of_le (by simp)) (hUS hx)]
    exact hC1 x ⟨⟨hx.1.1.le, hx.1.2.le⟩, hb⟩
  have hb2 : ∀ x : ℝ × Plane, x ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set Plane) →
      x.2 ∈ Icc (-c) c ×ˢ Icc (-(2 * R)) (2 * R) → ‖iteratedFDeriv ℝ 2 (apROm v) x‖ ≤ C2 := by
    intro x hx hb
    rw [← iteratedFDerivWithin_eq_iteratedFDeriv hSuniq
      (show ContDiffAt ℝ 2 (apROm v) x from (hΩdiff x hx).of_le (by simp)) (hUS hx)]
    exact hC2 x ⟨⟨hx.1.1.le, hx.1.2.le⟩, hb⟩
  have hM1 : 0 ≤ max C1 0 := le_max_right _ _
  have hM2 : 0 ≤ max C2 0 := le_max_right _ _
  have hpairQ : ∀ e : Plane, ‖e‖ ≤ 1 → ‖((0 : ℝ), e)‖ ≤ 1 := fun e he => by
    rw [Prod.norm_def]
    exact max_le (by simp) he
  have hpair1 : ‖((1 : ℝ), (0 : Plane))‖ ≤ 1 := by
    rw [Prod.norm_def]
    exact max_le (by simp) (by simp)
  have hWbd : ∀ e : Plane, ‖e‖ ≤ 1 → ∀ x : ℝ × Plane,
      x ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set Plane) →
      x.2 ∈ Icc (-c) c ×ˢ Icc (-(2 * R)) (2 * R) → |apRW v e x| ≤ max C1 0 := by
    intro e he x hx hb
    have h := apR_bound_one (apROm v) x ((0 : ℝ), e)
    have hn : ‖iteratedFDeriv ℝ 1 (apROm v) x‖ * ‖((0 : ℝ), e)‖ ≤ max C1 0 := by
      have h1 := hb1 x hx hb
      have h2 := hpairQ e he
      calc ‖iteratedFDeriv ℝ 1 (apROm v) x‖ * ‖((0 : ℝ), e)‖
          ≤ ‖iteratedFDeriv ℝ 1 (apROm v) x‖ * 1 := by gcongr
        _ = ‖iteratedFDeriv ℝ 1 (apROm v) x‖ := by ring
        _ ≤ C1 := h1
        _ ≤ max C1 0 := le_max_left _ _
    exact h.trans hn
  have hDWbd : ∀ e : Plane, ‖e‖ ≤ 1 → ∀ x : ℝ × Plane,
      x ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set Plane) →
      x.2 ∈ Icc (-c) c ×ˢ Icc (-(2 * R)) (2 * R) →
      |fderiv ℝ (apRW v e) x ((1 : ℝ), (0 : Plane))| ≤ max C2 0 := by
    intro e he x hx hb
    unfold apRW
    have h := apR_bound_two (hΩdiff x hx) ((1 : ℝ), (0 : Plane)) ((0 : ℝ), e)
    have h2 := hb2 x hx hb
    have hpe := hpairQ e he
    have hn : ‖iteratedFDeriv ℝ 2 (apROm v) x‖ * ‖((1 : ℝ), (0 : Plane))‖ *
        ‖((0 : ℝ), e)‖ ≤ max C2 0 := by
      calc ‖iteratedFDeriv ℝ 2 (apROm v) x‖ * ‖((1 : ℝ), (0 : Plane))‖ * ‖((0 : ℝ), e)‖
          ≤ ‖iteratedFDeriv ℝ 2 (apROm v) x‖ * 1 * 1 := by gcongr
        _ = ‖iteratedFDeriv ℝ 2 (apROm v) x‖ := by ring
        _ ≤ C2 := h2
        _ ≤ max C2 0 := le_max_left _ _
    exact h.trans hn
  -- the derivative formula on (0,T)
  have hA : ∀ e : Plane, ∀ r ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun t => ∫ z in Cyl.cell c, etaCutoff R z.2 *
          (apRW v e (t, z) * apRW v e (t, z))) (apRDint v e R c r) r :=
    fun e r hr => apHD_deriv_integral hφc hφv (apHD_eta_abs R) (hWc e) c hc0 hr.1 hr.2
  have hIcont : ∀ e : Plane, ∀ t ∈ Ioo (0 : ℝ) T, IntegrableOn
      (fun z : Plane => etaCutoff R z.2 * (apRW v e (t, z) * apRW v e (t, z))) (Cyl.cell c) := by
    intro e t ht
    have hs : Continuous (fun z : Plane => apRW v e (t, z)) :=
      (hWc e).continuousOn.comp_continuous (f := fun z : Plane => (t, z)) (by fun_prop)
        (fun z => Set.mk_mem_prod ht (mem_univ z))
    exact apHD_integ (c := c) (R0 := 2 * R)
      ((hφc.comp continuous_snd).mul (hs.mul hs))
      (fun z hz => by simp [apHD_eta_zero hR0 hz.le])
  -- pointwise and integrated identities on (0,T)
  have hGeq : ∀ t ∈ Ioo (0 : ℝ) T, apCutG c 1 v R t =
      (∫ z in Cyl.cell c, etaCutoff R z.2 * (apRW v eQ (t, z) * apRW v eQ (t, z)))
        + ∫ z in Cyl.cell c, etaCutoff R z.2 * (apRW v eE (t, z) * apRW v eE (t, z)) := by
    intro t ht
    have key : ∫ z in Cyl.cell c, etaCutoff R z.2 * eucJetN 1 (Cyl.curl (v t)) z =
        ∫ z in Cyl.cell c, (etaCutoff R z.2 * (apRW v eQ (t, z) * apRW v eQ (t, z))
          + etaCutoff R z.2 * (apRW v eE (t, z) * apRW v eE (t, z))) := by
      congr 1
      funext z
      have hd : DifferentiableAt ℝ (apROm v) (t, z) :=
        (hΩdiff (t, z) ⟨ht, mem_univ z⟩).differentiableAt (by simp)
      rw [show eucJetN 1 (Cyl.curl (v t)) z = eucJet1 (Cyl.curl (v t)) z by simp [eucJetN],
        apR_eucJet1 hd, mul_add]
    unfold apCutG
    rw [key, integral_add (hIcont eQ t ht) (hIcont eE t ht)]
  have hGd : ∀ r ∈ Ioo (0 : ℝ) T, HasDerivAt (apCutG c 1 v R)
      (apRDint v eQ R c r + apRDint v eE R c r) r := by
    intro r hr
    have hsum := (hA eQ r hr).add (hA eE r hr)
    refine hsum.congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem (Ioo_mem_nhds hr.1 hr.2) (fun t ht => hGeq t ht)
  have hdiffOn : DifferentiableOn ℝ (apCutG c 1 v R) (Ioo (0 : ℝ) T) :=
    fun r hr => (hGd r hr).differentiableAt.differentiableWithinAt
  -- uniform bound on the derivative
  obtain ⟨Kc, hKc_def⟩ : ∃ K : ℝ, K = ∫ z in Cyl.cell c,
      (Icc (-c) c ×ˢ Icc (-(2 * R)) (2 * R)).indicator
        (fun _ : Plane => 2 * max C1 0 * max C2 0) z := ⟨_, rfl⟩
  have hbnd : ∀ e : Plane, ‖e‖ ≤ 1 → ∀ r ∈ Ioo (0 : ℝ) T, ‖apRDint v e R c r‖ ≤ Kc := by
    intro e he r hr
    rw [hKc_def]
    unfold apRDint
    have hM : (0 : ℝ) ≤ 2 * max C1 0 * max C2 0 :=
      mul_nonneg (mul_nonneg (by norm_num) hM1) hM2
    refine apR_cell_bound hc0 hM _ ?_ ?_
    · intro z hz
      simp [apHD_eta_zero hR0 hz.le]
    · intro z hz1 hz2
      have hx : ((r, z) : ℝ × Plane) ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set Plane) := ⟨hr, mem_univ z⟩
      have hbz : z ∈ Icc (-c) c ×ˢ Icc (-(2 * R)) (2 * R) := ⟨abs_le.1 hz1, abs_le.1 hz2⟩
      have hW := hWbd e he (r, z) hx hbz
      have hD := hDWbd e he (r, z) hx hbz
      set D := fderiv ℝ (apRW v e) (r, z) ((1 : ℝ), (0 : Plane)) with hDdef
      set W := apRW v e (r, z) with hWdef
      have h1 : |etaCutoff R z.2| ≤ 1 := apHD_eta_abs R z.2
      have h2 : |D * W + W * D| ≤ 2 * max C1 0 * max C2 0 := by
        refine (abs_add_le _ _).trans ?_
        calc |D * W| + |W * D| = |D| * |W| + |W| * |D| := by rw [abs_mul, abs_mul]
          _ ≤ max C2 0 * max C1 0 + max C1 0 * max C2 0 :=
            add_le_add (mul_le_mul hD hW (abs_nonneg _) hM2) (mul_le_mul hW hD (abs_nonneg _) hM1)
          _ = 2 * max C1 0 * max C2 0 := by ring
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) h1).trans h2
  have hdbd : ∀ r ∈ Ioo (0 : ℝ) T, ‖deriv (apCutG c 1 v R) r‖ ≤ 2 * Kc := by
    intro r hr
    rw [(hGd r hr).deriv]
    have h1 := hbnd eQ (le_of_eq norm_eQ) r hr
    have h2 := hbnd eE (le_of_eq norm_eE) r hr
    linarith [norm_add_le (apRDint v eQ R c r) (apRDint v eE R c r)]
  have hmeas : Measurable (deriv (apCutG c 1 v R)) := measurable_deriv _
  have hIoo : IntegrableOn (deriv (apCutG c 1 v R)) (Ioo (0 : ℝ) T) := by
    refine Measure.integrableOn_of_bounded (M := 2 * Kc) measure_Ioo_lt_top.ne
      hmeas.aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun r hr => hdbd r hr)
  have hint : IntervalIntegrable (deriv (apCutG c 1 v R)) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    exact (integrableOn_Ioc_iff_integrableOn_Ioo (by finiteness)).2 hIoo
  exact ⟨hcont, hdiffOn, hint⟩

end UnforcedLeray.Short.PartI
