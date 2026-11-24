import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Lemmas
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletContDiff
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_1_3

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1/2/1` (decomposition): `InletFieldRegular`

Source `the November 2 reference manuscript`
lines 1206-1222, 5283-5295, 5199-5201.

**Statement defect.** `InletFieldRegular` (in `PartIII-b_C_ward_12_3_1_2_5_1_2.lean`) writes
`ContDiff ℝ ⊤ ...`; in this Mathlib `⊤ : WithTop ℕ∞` is `ω` (real *analyticity*), which is false
for the cutoff field `E_i` (the age cutoff is a smooth transition, not analytic) and is not what
the source says (`C^∞`).  `InletFieldRegularInf` below is the intended statement (`C^∞`).

Proved here, unconditionally: `E_i` is jointly `C^∞` (uniformly in the age cutoff), `period`-periodic
in `τ`, pointwise divergence free; `raw` is divergence free given its joint smoothness.  The only
remaining input is `RawJointSmooth` (task `PartIII-b:C/ward/12/3/1/2/6/1/1`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff
open UnforcedLeray UnforcedLeray.PhaseSpace UnforcedLeray.Axi UnforcedLeray.Blueprint
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The intended `InletFieldRegular`, with `C^∞` (`∞`) in place of the analytic `⊤ = ω`. -/
def InletFieldRegularInf : Prop := GERegime fun p _ _ =>
  ContDiff ℝ ∞ (fun x : ℝ × Space => UnforcedLeray.B0412.realC (p.raw x.1 x.2)) ∧
  (∀ x, ∑ k : Fin 3, dy k (fun x : ℝ × Space =>
      UnforcedLeray.B0412.realC (p.raw x.1 x.2)) x k = 0) ∧
  ∀ i : Fin 2, ContDiff ℝ ∞ (p.Efun i) ∧
    (∀ x : ℝ × Space, p.Efun i (x.1 + p.period, x.2) = p.Efun i x) ∧
    (∀ x, ∑ k : Fin 3, dy k (p.Efun i) x k = 0)

/-- Real vectors of `ℝ³` seen in `ℂ³`, as a continuous real-linear map. -/
def realCLin : Space →L[ℝ] CVec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => UnforcedLeray.B0412.realC x
      map_add' := fun x y => by ext i; simp [UnforcedLeray.B0412.realC_apply]
      map_smul' := fun c x => by ext i; simp [UnforcedLeray.B0412.realC_apply, Complex.real_smul] }

theorem realCLin_apply (x : Space) : realCLin x = UnforcedLeray.B0412.realC x := rfl

theorem contDiff_realC_comp {F : ℝ × Space → Space} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun x => UnforcedLeray.B0412.realC (F x)) :=
  realCLin.contDiff.comp hF

/-- The `j`-th phase derivative of `realC ∘ F`, componentwise. -/
theorem dy_realC_apply {F : ℝ × Space → Space} (hF : Differentiable ℝ F) (j k : Fin 3)
    (x : ℝ × Space) :
    dy j (fun x => UnforcedLeray.B0412.realC (F x)) x k =
      ((fderiv ℝ F x (0, coordinateVector j) k : ℝ) : ℂ) := by
  have h : (fun x => UnforcedLeray.B0412.realC (F x)) = realCLin ∘ F := rfl
  unfold dy
  rw [h, fderiv_comp x realCLin.differentiableAt (hF x)]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv]
  exact UnforcedLeray.B0412.realC_apply _ k

/-- The partial derivative of a jointly differentiable field in the `y`-direction is the slice
derivative. -/
theorem fderiv_joint_eq_slice {F : ℝ × Space → Space} (hF : Differentiable ℝ F) (x : ℝ × Space)
    (v : Space) :
    fderiv ℝ F x (0, v) = fderiv ℝ (fun y => F (x.1, y)) x.2 v := by
  have hFd : HasFDerivAt F (fderiv ℝ F x) (x.1, x.2) := (hF x).hasFDerivAt
  have hg : HasFDerivAt (fun y : Space => ((x.1, y) : ℝ × Space))
      (ContinuousLinearMap.inr ℝ ℝ Space) x.2 := hasFDerivAt_prodMk_right x.1 x.2
  have hc := hFd.comp x.2 hg
  have := hc.fderiv
  change fderiv ℝ (fun y => F (x.1, y)) x.2 = _ at this
  rw [this]
  rfl

/-- Pointwise divergence of `realC ∘ F` is the real divergence of the slice. -/
theorem sum_dy_realC {F : ℝ × Space → Space} (hF : Differentiable ℝ F) (x : ℝ × Space) :
    ∑ k : Fin 3, dy k (fun x => UnforcedLeray.B0412.realC (F x)) x k =
      ((Axi.divergence (fun y => F (x.1, y)) x.2 : ℝ) : ℂ) := by
  simp only [dy_realC_apply hF, Axi.divergence, fderiv_joint_eq_slice hF]
  push_cast
  rfl

/-- A `C¹` field divergence free off the axis is divergence free (the axis complement is dense). -/
theorem divergence_zero_of_offAxis {G : Space → Space} (hG : ContDiff ℝ 1 G)
    (h : ∀ y, y ∉ Axi.axis → Axi.divergence G y = 0) (y : Space) : Axi.divergence G y = 0 := by
  have hcont : Continuous fun z : Space => Axi.divergence G z := by
    refine continuous_finsetSum _ fun k _ => ?_
    have h1 : Continuous fun z : Space => fderiv ℝ G z (coordinateVector k) :=
      (hG.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k).comp h1
  have hext := Continuous.ext_on UnforcedLeray.Cons.C03.dense_compl_axis hcont continuous_const
    (fun z hz => h z hz)
  simpa using congrFun hext y

/-- Smoothness of the frozen inlet, jointly in `(τ, y)`, uniformly in the age cutoff. -/
theorem inlet_contDiff {p : Params} {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) {d dm dp : ℝ}
    (hreg : UnforcedLeray.Short.IIb.BgRegime p d dm dp) (hν : p.ν ≤ 1) (hmode : p.mode = q)
    (i : Fin 2) : ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2) := by
  obtain ⟨C, κ, N, -, -, hper⟩ := UnforcedLeray.Short.IIb.frozenStreamBounds lam q hq 0
  have hνpos : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hP : ContDiff ℝ ∞ (periodicStream q p.c) := (hper p.c hc1).1
  have hfro : ∀ k : Fin 2, ContDiff ℝ ∞ (p.frozenStream k) :=
    fun k => UnforcedLeray.Short.IIb.inletCD_frozenStream hP hmode k
  have hH : 0 < p.H := div_pos p.ageCut_pos p.ν_pos
  have hcut : ContDiff ℝ ∞ (p.cutStream i) := by
    unfold Params.cutStream
    exact ((UnforcedLeray.Cons.C03.Concrete.contDiff_ageCutoff p.H).comp contDiff_fst).mul
      ((hfro i).comp contDiff_snd)
  have hB : ContDiff ℝ ∞ (p.inletProfile i) := by
    unfold Params.inletProfile
    exact UnforcedLeray.Short.IIb.inletCD_ringStreamProfile hcut
  have hvan : ∀ x : ℝ × (ℝ × ℝ), p.H / 2 < x.1 → p.inletProfile i x = 0 := by
    intro x hx
    have hcut0 : p.cutStream i x = 0 := by
      unfold Params.cutStream
      simp [UnforcedLeray.Cons.C03.Concrete.ageCutoff_eq_zero hH hx.le]
    have hev : ∀ᶠ y in 𝓝 x, p.H / 2 < y.1 :=
      (continuous_fst.tendsto x).eventually (lt_mem_nhds hx)
    have hfun : p.cutStream i =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hev] with y hy
      unfold Params.cutStream
      simp [UnforcedLeray.Cons.C03.Concrete.ageCutoff_eq_zero hH hy.le]
    have hfd : fderiv ℝ (p.cutStream i) x = 0 := by
      rw [hfun.fderiv_eq]
      simp
    have hdS : Axi.dS (p.cutStream i) x = 0 := by
      unfold Axi.dS
      rw [hfd]
      simp
    have hdQ : Axi.dQ (p.cutStream i) x = 0 := by
      unfold Axi.dQ
      rw [hfd]
      simp
    have hdE : Axi.dEta (p.cutStream i) x = 0 := by
      unfold Axi.dEta
      rw [hfd]
      simp
    simp [Params.inletProfile, Axi.ringStreamProfile, hdS, hdQ, hdE, hcut0]
  exact UnforcedLeray.Short.IIb.NicePT.contDiff_Nv p.R_pos hB (s1 := p.H / 2) hvan


/-- The cutoff stream of the inlet column is `C^∞`. -/
theorem cutStream_contDiff {p : Params} {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) {d dm dp : ℝ}
    (hreg : UnforcedLeray.Short.IIb.BgRegime p d dm dp) (hν : p.ν ≤ 1) (hmode : p.mode = q)
    (i : Fin 2) : ContDiff ℝ ∞ (p.cutStream i) := by
  obtain ⟨C, κ, N, -, -, hper⟩ := UnforcedLeray.Short.IIb.frozenStreamBounds lam q hq 0
  have hνpos : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hP : ContDiff ℝ ∞ (periodicStream q p.c) := (hper p.c hc1).1
  have hfro : ∀ k : Fin 2, ContDiff ℝ ∞ (p.frozenStream k) :=
    fun k => UnforcedLeray.Short.IIb.inletCD_frozenStream hP hmode k
  unfold Params.cutStream
  exact ((UnforcedLeray.Cons.C03.Concrete.contDiff_ageCutoff p.H).comp contDiff_fst).mul
    ((hfro i).comp contDiff_snd)

/-- The inlet is `period`-periodic in `τ` (the phase `ξ` advances by `c` over one period). -/
theorem inlet_periodic (p : Params) (i : Fin 2) (τ : ℝ) (y : Space) :
    p.inlet i (τ + p.period) y = p.inlet i τ y := by
  have hR : p.R ≠ 0 := p.R_pos.ne'
  have hch : Axi.chart p.R (τ + p.period) y =
      (Axi.age p.R y, (Axi.phase p.R τ y + p.c, Axi.trans p.R y)) := by
    simp only [Axi.chart, Axi.phase, p.period_eq]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    show p.R * (τ + 2 * p.c / p.R) / 2 - p.R / 2 * Real.log (Axi.age p.R y) =
      p.R * τ / 2 - p.R / 2 * Real.log (Axi.age p.R y) + p.c
    field_simp
    ring
  unfold Params.inlet Axi.Nv
  rw [hch, p.inletProfile_periodic i]
  rfl

theorem efun_periodic (p : Params) (i : Fin 2) (x : ℝ × Space) :
    p.Efun i (x.1 + p.period, x.2) = p.Efun i x := by
  unfold Params.Efun
  rw [inlet_periodic]

theorem merChart_contDiffOn {R : ℝ} (hR : R ≠ 0) (τ : ℝ) :
    ContDiffOn ℝ ∞ (merChart R τ) (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
  have hne : ∀ x ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), x.1 ≠ 0 := fun x hx => ne_of_gt hx.1
  have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => R ^ 2 / p.1 ^ 2) (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :=
    contDiffOn_const.div (contDiff_fst.pow 2).contDiffOn fun x hx => pow_ne_zero 2 (hne x hx)
  have h2 : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => R * τ / 2 - (R / 2) * Real.log (R ^ 2 / p.1 ^ 2))
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
    refine contDiffOn_const.sub (contDiffOn_const.mul (ContDiffOn.log h1 ?_))
    intro x hx
    exact div_ne_zero (pow_ne_zero 2 hR) (pow_ne_zero 2 (hne x hx))
  have h3 : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => R * p.2 / p.1) (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :=
    (contDiffOn_const.mul contDiff_snd.contDiffOn).div contDiff_fst.contDiffOn hne
  exact h1.prodMk (h2.prodMk h3)


theorem ringStream_contDiffOn {R : ℝ} (hR : R ≠ 0) (τ : ℝ) {φ : ℝ × (ℝ × ℝ) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) :
    ContDiffOn ℝ 2 (ringStream R τ φ) (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
  have h := (contDiffOn_fst (𝕜 := ℝ) (s := Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).mul
    (hφ.contDiffOn.comp (merChart_contDiffOn hR τ) (Set.mapsTo_univ _ _))
  exact (h.of_le (by simp))

/-- Off the axis the inlet slice is divergence free (it is the stream lift of `ϱ·χψ`). -/
theorem inlet_div_offAxis {p : Params} {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) {d dm dp : ℝ}
    (hreg : UnforcedLeray.Short.IIb.BgRegime p d dm dp) (hν : p.ν ≤ 1) (hmode : p.mode = q)
    (i : Fin 2) (τ : ℝ) {y : Space} (hy : y ∉ Axi.axis) :
    Axi.divergence (p.inlet i τ) y = 0 := by
  have hcut := cutStream_contDiff hq hreg hν hmode i
  have hev : p.inlet i τ =ᶠ[𝓝 y] Axi.streamLift (ringStream p.R τ (p.cutStream i)) := by
    filter_upwards [Axi.isOpen_compl_axis.mem_nhds (Set.mem_compl hy)] with z hz
    exact (Axi.ringStreamLift_components p.R_pos hz
      (hcut.differentiable (by simp) _)).symm
  unfold Axi.divergence
  rw [hev.fderiv_eq]
  exact Axi.div_streamLift_eq_zero (ringStream_contDiffOn p.R_pos.ne' τ hcut) hy

/-- Off the axis the raw slice is divergence free. -/
theorem raw_div_offAxis {p : Params} {d dm dp : ℝ}
    (hreg : UnforcedLeray.Short.IIb.BgRegime p d dm dp) (τ : ℝ) {y : Space}
    (hy : y ∉ Axi.axis) : Axi.divergence (p.raw τ) y = 0 := by
  have := UnforcedLeray.Short.IIb.offAxis_divFree hreg τ hy
  simpa [Axi.divergence, coordinateVector] using this

/-- **`InletFieldRegular`, with `C^∞`** (1206-1222, 5283-5295), from the joint smoothness of
`raw` (`RawJointSmooth`, task `PartIII-b:C/ward/12/3/1/2/6/1/1`). -/
theorem inletFieldRegularInf_of (h : RawJointSmooth) : InletFieldRegularInf := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₀, hν₀, H⟩ := h dm dp hdm
  refine ⟨min ν₀ 1, lt_min hν₀ one_pos, fun p d hreg hν hmode z g hg => ?_⟩
  have hν0 : p.ν ≤ ν₀ := hν.trans (min_le_left _ _)
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hraw := H p d hreg hν0
  refine ⟨contDiff_realC_comp hraw, ?_, fun i => ?_⟩
  · intro x
    have hd : Differentiable ℝ (fun x : ℝ × Space => p.raw x.1 x.2) :=
      hraw.differentiable (by simp)
    rw [sum_dy_realC hd x]
    have hC : ContDiff ℝ 1 (p.raw x.1) :=
      (hraw.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
    have := divergence_zero_of_offAxis hC (fun y hy => raw_div_offAxis hreg x.1 hy) x.2
    simp [this]
  · have hin := inlet_contDiff hq hreg hν1 hmode i
    refine ⟨contDiff_realC_comp hin, efun_periodic p i, fun x => ?_⟩
    have hd : Differentiable ℝ (fun x : ℝ × Space => p.inlet i x.1 x.2) :=
      hin.differentiable (by simp)
    show ∑ k : Fin 3, dy k (fun x : ℝ × Space => UnforcedLeray.B0412.realC (p.inlet i x.1 x.2)) x k
      = 0
    rw [sum_dy_realC hd x]
    have hC : ContDiff ℝ 1 (p.inlet i x.1) :=
      (hin.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
    have := divergence_zero_of_offAxis hC
      (fun y hy => inlet_div_offAxis hq hreg hν1 hmode i x.1 hy) x.2
    simp [this]

end UnforcedLeray.Short.PartIIIb.Concrete
