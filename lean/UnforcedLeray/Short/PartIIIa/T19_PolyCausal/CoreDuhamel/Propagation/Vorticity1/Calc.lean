import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_2_3_2
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.FlatWeakFromDensity.Basic

/-!
# `PartIII-a:T19/2/3/2/1` helpers: calculus on cylinder tests

Closure of cylinder tests, the partial-derivative algebra (`pd` of sums and products, symmetry of
second derivatives, `∂_j Δ = Δ ∂_j`), the train velocity slice (smoothness, periodicity,
divergence-free, curl `= Ec`), the perpendicular gradient test field `Ψ = (∂_η φ, -∂_q φ)`, and
smoothness of the complex weight `r ↦ r^μ θ(r)` (SP 3426-3440, 3462-3466).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.V1

open UnforcedLeray.Short.IIIa

/-! ## Cylinder tests -/

theorem cell_eq (c : ℝ) : B0579.cell c = UnforcedLeray.Cyl.cell c := by
  ext x; simp [B0579.cell, UnforcedLeray.Cyl.cell, neg_div]

theorem cylTest_add {c : ℝ} {f g : ℝ × ℝ → ℝ} (hf : B0579.IsCylTest c f)
    (hg : B0579.IsCylTest c g) : B0579.IsCylTest c (fun x => f x + g x) where
  smooth := hf.smooth.add hg.smooth
  periodic x := by simp only [hf.periodic x, hg.periodic x]
  band := by
    obtain ⟨R₁, h₁⟩ := hf.band
    obtain ⟨R₂, h₂⟩ := hg.band
    exact ⟨max R₁ R₂, fun x hx => by
      rw [h₁ x (lt_of_le_of_lt (le_max_left _ _) hx), h₂ x (lt_of_le_of_lt (le_max_right _ _) hx),
        add_zero]⟩

theorem cylTest_neg {c : ℝ} {f : ℝ × ℝ → ℝ} (hf : B0579.IsCylTest c f) :
    B0579.IsCylTest c (fun x => -f x) where
  smooth := hf.smooth.neg
  periodic x := by simp only [hf.periodic x]
  band := by
    obtain ⟨R, h⟩ := hf.band
    exact ⟨R, fun x hx => by rw [h x hx, neg_zero]⟩

theorem cylTest_sub {c : ℝ} {f g : ℝ × ℝ → ℝ} (hf : B0579.IsCylTest c f)
    (hg : B0579.IsCylTest c g) : B0579.IsCylTest c (fun x => f x - g x) := by
  have := cylTest_add hf (cylTest_neg hg)
  simpa [sub_eq_add_neg] using this

/-- A smooth `c`-periodic function times a cylinder test is a cylinder test. -/
theorem cylTest_mul_left {c : ℝ} {h f : ℝ × ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hper : ∀ x : ℝ × ℝ, h (x.1 + c, x.2) = h x) (hf : B0579.IsCylTest c f) :
    B0579.IsCylTest c (fun x => h x * f x) where
  smooth := hh.mul hf.smooth
  periodic x := by simp only [hper x, hf.periodic x]
  band := by
    obtain ⟨R, hR⟩ := hf.band
    exact ⟨R, fun x hx => by rw [hR x hx, mul_zero]⟩

theorem cylTest_const_mul {c : ℝ} (k : ℝ) {f : ℝ × ℝ → ℝ} (hf : B0579.IsCylTest c f) :
    B0579.IsCylTest c (fun x => k * f x) :=
  cylTest_mul_left contDiff_const (fun _ => rfl) hf

theorem cylTest_lapP {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    B0579.IsCylTest c (lapP φ) :=
  cylTest_add ((hφ.pd 0).pd 0) ((hφ.pd 1).pd 1)

/-- A cylinder test is bounded on the cell. -/
theorem cylTest_bound {c : ℝ} {f : ℝ × ℝ → ℝ} (hf : B0579.IsCylTest c f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ B0579.cell c, |f x| ≤ M := by
  obtain ⟨R, hR⟩ := hf.vanish
  obtain ⟨C, hC⟩ := (B0579.isCompact_box c R).exists_bound_of_continuousOn
    hf.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  by_cases hxK : x ∈ B0579.box c R
  · exact (Real.norm_eq_abs _ ▸ hC x hxK).trans (le_max_left _ _)
  · rw [hR x hx hxK, abs_zero]; exact le_max_right _ _

/-- The band of a cylinder test, with a nonnegative radius. -/
theorem cylTest_band {c : ℝ} {f : ℝ × ℝ → ℝ} (hf : B0579.IsCylTest c f) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : ℝ × ℝ, R < |x.2| → f x = 0 := by
  obtain ⟨R, hR⟩ := hf.band
  exact ⟨max R 0, le_max_right _ _, fun x hx => hR x (lt_of_le_of_lt (le_max_left _ _) hx)⟩

/-- A test is bounded by `M · 1_{|η| ≤ R}` on the cell. -/
theorem cylTest_bound_band {c : ℝ} {f : ℝ × ℝ → ℝ} (hf : B0579.IsCylTest c f) :
    ∃ M R : ℝ, 0 ≤ M ∧ 0 ≤ R ∧
      ∀ x ∈ B0579.cell c, |f x| ≤ M * (Icc (-R) R).indicator 1 x.2 := by
  obtain ⟨M, hM0, hM⟩ := cylTest_bound hf
  obtain ⟨R, hR0, hR⟩ := cylTest_band hf
  refine ⟨M, R, hM0, hR0, fun x hx => ?_⟩
  by_cases hxR : x.2 ∈ Icc (-R) R
  · rw [indicator_of_mem hxR, Pi.one_apply, mul_one]; exact hM x hx
  · have : R < |x.2| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hxR
      rcases hxR with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [hR x this, indicator_of_notMem hxR, mul_zero, abs_zero]

/-! ## Partial-derivative algebra -/

theorem pd_add {f g : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (j : Fin 2) :
    B0579.pd j (fun y => f y + g y) x = B0579.pd j f x + B0579.pd j g x := by
  simp only [B0579.pd]
  rw [fderiv_fun_add hf hg]
  rfl

theorem pd_sub {f g : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (j : Fin 2) :
    B0579.pd j (fun y => f y - g y) x = B0579.pd j f x - B0579.pd j g x := by
  simp only [B0579.pd]
  rw [fderiv_fun_sub hf hg]
  rfl

theorem pd_neg (f : ℝ × ℝ → ℝ) (x : ℝ × ℝ) (j : Fin 2) :
    B0579.pd j (fun y => -f y) x = -B0579.pd j f x := by
  simp only [B0579.pd]
  rw [fderiv_fun_neg]
  rfl

theorem pd_mul' {f g : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin 2)
    (x : ℝ × ℝ) : B0579.pd j (fun y => f y * g y) x = B0579.pd j f x * g x + f x * B0579.pd j g x :=
  B0579.pd_mul hf hg j x

theorem pd_const_mul {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (j : Fin 2) (k : ℝ)
    (x : ℝ × ℝ) : B0579.pd j (fun y => k * f y) x = k * B0579.pd j f x := by
  rw [pd_const_mul_fun hf j k]

theorem pd_pd_eq_fderiv_fderiv {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (i j : Fin 2)
    (x : ℝ × ℝ) :
    B0579.pd i (B0579.pd j f) x = fderiv ℝ (fderiv ℝ f) x (B0579.dir i) (B0579.dir j) := by
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  show fderiv ℝ (fun y => fderiv ℝ f y (B0579.dir j)) x (B0579.dir i) = _
  rw [fderiv_clm_apply (hdf x) (differentiableAt_const _)]
  simp

/-- `∂_i ∂_j f = ∂_j ∂_i f` for a `C²` function. -/
theorem pd_comm {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (i j : Fin 2) :
    B0579.pd i (B0579.pd j f) = B0579.pd j (B0579.pd i f) := by
  funext x
  rw [pd_pd_eq_fderiv_fderiv hf, pd_pd_eq_fderiv_fderiv hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

theorem cylTest_c2 {c : ℝ} {g : ℝ × ℝ → ℝ} (hg : B0579.IsCylTest c g) : ContDiff ℝ 2 g :=
  hg.smooth.of_le (by simp)

/-- `∂_i Δ φ = Δ ∂_i φ` for a cylinder test. -/
theorem pd_lapP {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) (i : Fin 2) :
    B0579.pd i (lapP φ) = lapP (B0579.pd i φ) := by
  funext x
  have hlap : lapP φ = fun y => B0579.pd 0 (B0579.pd 0 φ) y + B0579.pd 1 (B0579.pd 1 φ) y := rfl
  rw [hlap, pd_add ((hφ.pd 0).pd 0).differentiable.differentiableAt
    ((hφ.pd 1).pd 1).differentiable.differentiableAt]
  simp only [lapP]
  rw [pd_comm (cylTest_c2 (hφ.pd 0)) i 0, pd_comm (cylTest_c2 hφ) i 0,
    pd_comm (cylTest_c2 (hφ.pd 1)) i 1, pd_comm (cylTest_c2 hφ) i 1]

theorem lapP_neg {c : ℝ} {f : ℝ × ℝ → ℝ} (hf : B0579.IsCylTest c f) (x : ℝ × ℝ) :
    lapP (fun y => -f y) x = -lapP f x := by
  unfold lapP
  have h0 : B0579.pd 0 (fun y => -f y) = fun y => -B0579.pd 0 f y := funext fun y => pd_neg f y 0
  have h1 : B0579.pd 1 (fun y => -f y) = fun y => -B0579.pd 1 f y := funext fun y => pd_neg f y 1
  rw [h0, h1, pd_neg, pd_neg]
  ring

/-! ## The train slice -/

variable {ν c : ℝ}

theorem vS_contDiff (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) :
    ContDiff ℝ ∞ (tr.v r) := by
  have h := tr.isTrain.smooth_v
  have hg : ContDiff ℝ ∞ (fun x : ℝ × ℝ => ((r, x) : ℝ × (ℝ × ℝ))) :=
    contDiff_const.prodMk contDiff_id
  have := h.comp hg.contDiffOn (s := univ) (fun x _ => ⟨hr, trivial⟩)
  exact contDiffOn_univ.1 this

/-- The component `v_k = (tr.v r ·) k`. -/
def vC (tr : UnforcedLeray.B0140.TrainSol ν c) (r : ℝ) (k : Fin 2) : ℝ × ℝ → ℝ :=
  fun y => tr.v r y k

theorem vC_contDiff (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) (k : Fin 2) :
    ContDiff ℝ ∞ (vC tr r k) :=
  (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp (vS_contDiff tr hr)

theorem vC_diff (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) (k : Fin 2) :
    Differentiable ℝ (vC tr r k) :=
  (vC_contDiff tr hr k).differentiable (by simp)

theorem vC_periodic (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) (k : Fin 2)
    (x : ℝ × ℝ) : vC tr r k (x.1 + c, x.2) = vC tr r k x := by
  simp only [vC]
  rw [tr.isTrain.periodic_v r hr x]

theorem pd_eq_partialQ {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (x : ℝ × ℝ) :
    B0579.pd 0 f x = UnforcedLeray.Cyl.partialQ f x := by
  rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hf]; rfl

theorem pd_eq_partialEta {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (x : ℝ × ℝ) :
    B0579.pd 1 f x = UnforcedLeray.Cyl.partialEta f x := by
  rw [UnforcedLeray.Cyl.partialEta_eq_fderiv hf]; rfl

theorem vC_div (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) (x : ℝ × ℝ) :
    B0579.pd 0 (vC tr r 0) x + B0579.pd 1 (vC tr r 1) x = 0 := by
  have h := tr.isTrain.solenoidal r hr x
  rw [pd_eq_partialQ (vC_diff tr hr 0), pd_eq_partialEta (vC_diff tr hr 1)]
  exact h

theorem Ec_eq (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) :
    UnforcedLeray.B0238.Ec tr r = fun x => B0579.pd 0 (vC tr r 1) x - B0579.pd 1 (vC tr r 0) x := by
  funext x
  rw [pd_eq_partialQ (vC_diff tr hr 1), pd_eq_partialEta (vC_diff tr hr 0)]
  rfl

theorem pdv_contDiff (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) (k j : Fin 2) :
    ContDiff ℝ ∞ (B0579.pd j (vC tr r k)) :=
  ((contDiff_infty_iff_fderiv.1 (vC_contDiff tr hr k)).2).clm_apply contDiff_const

theorem pdv_periodic (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) (k j : Fin 2)
    (x : ℝ × ℝ) : B0579.pd j (vC tr r k) (x.1 + c, x.2) = B0579.pd j (vC tr r k) x := by
  have hT : vC tr r k ∘ (fun y : ℝ × ℝ => (y.1 + c, y.2)) = vC tr r k :=
    funext fun y => vC_periodic tr hr k y
  have hd := (vC_diff tr hr k) (x.1 + c, x.2)
  have hS : HasFDerivAt (fun y : ℝ × ℝ => (y.1 + c, y.2)) (ContinuousLinearMap.id ℝ (ℝ × ℝ)) x := by
    have : (fun y : ℝ × ℝ => (y.1 + c, y.2)) = fun y => y + ((c, 0) : ℝ × ℝ) := by
      funext y; ext <;> simp
    rw [this]
    exact (hasFDerivAt_id x).add_const _
  have hc := hd.hasFDerivAt.comp x hS
  rw [hT] at hc
  simp only [B0579.pd]
  rw [hc.fderiv]
  rfl

theorem Ec_contDiff (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) :
    ContDiff ℝ ∞ (UnforcedLeray.B0238.Ec tr r) := by
  rw [Ec_eq tr hr]
  exact (pdv_contDiff tr hr 1 0).sub (pdv_contDiff tr hr 0 1)

theorem Ec_periodic (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r)
    (x : ℝ × ℝ) : UnforcedLeray.B0238.Ec tr r (x.1 + c, x.2) = UnforcedLeray.B0238.Ec tr r x := by
  rw [Ec_eq tr hr]
  simp only [pdv_periodic tr hr]

theorem pdE_contDiff (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) (j : Fin 2) :
    ContDiff ℝ ∞ (B0579.pd j (UnforcedLeray.B0238.Ec tr r)) :=
  ((contDiff_infty_iff_fderiv.1 (Ec_contDiff tr hr)).2).clm_apply contDiff_const

/-! ## The perpendicular gradient field `Ψ = (∂_η φ, -∂_q φ)` -/

/-- `Ψ φ = (∂_η φ, -∂_q φ)`, so that `∫ curl u · φ = ∫ u · Ψ φ`. -/
def perpF (φ : ℝ × ℝ → ℝ) : ℝ × ℝ → Fin 2 → ℝ :=
  fun x => ![B0579.pd 1 φ x, -B0579.pd 0 φ x]

@[simp] theorem perpF_zero (φ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : perpF φ x 0 = B0579.pd 1 φ x := rfl

@[simp] theorem perpF_one (φ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : perpF φ x 1 = -B0579.pd 0 φ x := rfl

theorem perpF_cylTest {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) (i : Fin 2) :
    B0579.IsCylTest c (fun y => perpF φ y i) := by
  fin_cases i
  · exact hφ.pd 1
  · exact cylTest_neg (hφ.pd 0)

theorem perpF_isFlatSpatialTest {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    IsFlatSpatialTest c (perpF φ) where
  smooth i := (perpF_cylTest hφ i).smooth
  periodic x i := (perpF_cylTest hφ i).periodic x
  bounded := by
    obtain ⟨R₀, h₀⟩ := (perpF_cylTest hφ 0).band
    obtain ⟨R₁, h₁⟩ := (perpF_cylTest hφ 1).band
    refine ⟨max R₀ R₁, fun x i hx => ?_⟩
    fin_cases i
    · exact h₀ x (lt_of_le_of_lt (le_max_left _ _) hx)
    · exact h₁ x (lt_of_le_of_lt (le_max_right _ _) hx)
  divFree x := by
    show B0579.pd 0 (B0579.pd 1 φ) x + B0579.pd 1 (fun y => -B0579.pd 0 φ y) x = 0
    rw [pd_neg, pd_comm (cylTest_c2 hφ) 0 1]
    ring

/-! ## The complex weight `r ↦ r^μ θ(r)` -/

theorem cpow_eventuallyEq (μ : ℂ) {r : ℝ} (hr : 0 < r) :
    (fun t : ℝ => (t : ℂ) ^ μ) =ᶠ[𝓝 r] fun t => Complex.exp ((Real.log t : ℂ) * μ) := by
  filter_upwards [lt_mem_nhds hr] with t ht
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ht.ne'), ← Complex.ofReal_log ht.le]

theorem contDiffAt_cpow (μ : ℂ) {r : ℝ} (hr : 0 < r) :
    ContDiffAt ℝ ∞ (fun t : ℝ => (t : ℂ) ^ μ) r := by
  refine ContDiffAt.congr_of_eventuallyEq ?_ (cpow_eventuallyEq μ hr)
  refine ContDiffAt.cexp ?_
  refine ContDiffAt.mul ?_ contDiffAt_const
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp r (Real.contDiffAt_log.2 hr.ne')

theorem weight_contDiff {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hts : tsupport θ ⊆ Ioi 0) (μ : ℂ) :
    ContDiff ℝ ∞ (fun r : ℝ => (r : ℂ) ^ μ * (θ r : ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro r
  by_cases hr : 0 < r
  · exact (contDiffAt_cpow μ hr).mul (Complex.ofRealCLM.contDiff.comp hθ).contDiffAt
  · have hn : r ∉ tsupport θ := fun h => hr (hts h)
    have hev : (fun r : ℝ => (r : ℂ) ^ μ * (θ r : ℂ)) =ᶠ[𝓝 r] fun _ => (0 : ℂ) := by
      filter_upwards [(isClosed_tsupport θ).isOpen_compl.mem_nhds hn] with t ht
      rw [image_eq_zero_of_notMem_tsupport ht]
      simp
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem weight_support_subset (θ : ℝ → ℝ) (μ : ℂ) (F : ℂ →L[ℝ] ℝ) :
    Function.support (fun r : ℝ => F ((r : ℂ) ^ μ * (θ r : ℂ))) ⊆ Function.support θ := by
  intro r hr
  by_contra h
  rw [Function.notMem_support] at h
  apply hr
  simp [h]

theorem weight_tsupport_subset (θ : ℝ → ℝ) (μ : ℂ) (F : ℂ →L[ℝ] ℝ) :
    tsupport (fun r : ℝ => F ((r : ℂ) ^ μ * (θ r : ℂ))) ⊆ tsupport θ :=
  closure_mono (weight_support_subset θ μ F)

theorem weight_hasCompactSupport {θ : ℝ → ℝ} (hθc : HasCompactSupport θ) (μ : ℂ) (F : ℂ →L[ℝ] ℝ) :
    HasCompactSupport (fun r : ℝ => F ((r : ℂ) ^ μ * (θ r : ℂ))) :=
  hθc.mono (weight_support_subset θ μ F)

theorem weight_hasDerivAt {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) {μ : ℂ} (hμ : μ ≠ 0) {r : ℝ}
    (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ μ * (θ t : ℂ))
      (μ / (r : ℂ) * (r : ℂ) ^ μ * (θ r : ℂ) + (r : ℂ) ^ μ * ((deriv θ r : ℝ) : ℂ)) r := by
  have h1 := hasDerivAt_ofReal_cpow_const hr.ne' hμ
  have hθd : HasDerivAt (fun t : ℝ => (θ t : ℂ)) ((deriv θ r : ℝ) : ℂ) r :=
    ((hθ.differentiable (by simp)) r).hasDerivAt.ofReal_comp
  have h2 := h1.mul hθd
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hpow : (r : ℂ) ^ (μ - 1) = (r : ℂ) ^ μ / (r : ℂ) := by
    rw [Complex.cpow_sub _ _ hr', Complex.cpow_one]
  refine h2.congr_deriv ?_
  rw [hpow]
  ring

/-- The real-part / imaginary-part test weights: `deriv` of `F (r^μ θ)` is `F` of the complex
derivative, for `F = re, im`. -/
theorem weight_part_hasDerivAt {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) {μ : ℂ} (hμ : μ ≠ 0) {r : ℝ}
    (hr : 0 < r) (F : ℂ →L[ℝ] ℝ) :
    HasDerivAt (fun t : ℝ => F ((t : ℂ) ^ μ * (θ t : ℂ)))
      (F (μ / (r : ℂ) * (r : ℂ) ^ μ * (θ r : ℂ) + (r : ℂ) ^ μ * ((deriv θ r : ℝ) : ℂ))) r :=
  F.hasFDerivAt.comp_hasDerivAt r (weight_hasDerivAt hθ hμ hr)

end UnforcedLeray.Short.IIIa.V1

end
