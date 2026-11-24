import UnforcedLeray.Loc.Hyp.ModeIdentification.Phase
import UnforcedLeray.Lib.SobolevB.Mollify

/-!
# H-ModeId helpers: elliptic `H¹` regularity on `ℝ³` (`LaplacianH1Regularity`)

Support for `Loc/Hyp/ModeIdentification.lean` (target `ModeIdentificationHyp`,
`paper/main.tex` lines 308–312, "`H²` from `‖f‖₂ + ‖Δf‖₂`"; blueprint unit B1009; INF11).

**Theorem** (`laplacianH1Regularity`). If `f, g ∈ L²(ℝ³;ℝ³)` and `⟨f, Δφ⟩ = ⟨g, φ⟩` for every
vector test `φ`, then `f ∈ H¹` and `⟨g, G⟩ = -∑ᵢ⟨∂ᵢf, ∂ᵢG⟩` for every `G ∈ H¹`.

**Proof** (mollification, no Fourier transform). With a mollifier `κₙ` (the normalized bump
of `Lib/SobolevB/Mollify.lean`) put `uₙ = κₙ ⋆ f`, smooth with all derivatives
`∂^α uₙ = (∂^α κₙ) ⋆ f ∈ L²` (Young). Testing the hypothesis with the compactly supported
`φ(t) = κₙ(x - t)v` gives `Δuₙ = κₙ ⋆ g` pointwise. Hence
`‖∇(uₙ - uₘ)‖² = -⟨κₙ⋆g - κₘ⋆g, uₙ - uₘ⟩ → 0`, so `uₙ` is Cauchy in the compiled `H¹`; its
limit `F` has value `f`, and the identity `⟨κₙ⋆g, G⟩ = -∑ᵢ⟨∂ᵢuₙ, ∂ᵢG⟩` passes to the limit.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.ModeId

open SobolevGraph

/-! ## Kernels -/

/-- `∂ᵢκ` for a scalar kernel. -/
def kd (i : Fin 3) (κ : Space → ℝ) : Space → ℝ := fun y => fderiv ℝ κ y (coordinateVector i)

theorem contDiff_kd {κ : Space → ℝ} (hκ : ContDiff ℝ ∞ κ) (i : Fin 3) :
    ContDiff ℝ ∞ (kd i κ) :=
  (hκ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem hasCompactSupport_kd {κ : Space → ℝ} (hc : HasCompactSupport κ) (i : Fin 3) :
    HasCompactSupport (kd i κ) :=
  hc.fderiv_apply (𝕜 := ℝ) _

theorem kd_neg {κ : Space → ℝ} (_hκ : ContDiff ℝ ∞ κ) (i : Fin 3) :
    kd i (fun y => -kd i κ y) = fun y => -kd i (kd i κ) y := by
  funext y
  unfold kd
  rw [fderiv_fun_neg]
  rfl

/-- `∂ᵢ` of the reflected test `t ↦ κ(x - t) v`. -/
theorem testPartial_reflect {κ : Space → ℝ} (hκ : ContDiff ℝ ∞ κ) (x v : Space) (i : Fin 3) :
    testPartial (fun t => κ (x - t) • v) i = fun t => (-kd i κ (x - t)) • v := by
  funext t
  unfold testPartial
  have h1 : HasFDerivAt (fun t : Space => x - t) (-ContinuousLinearMap.id ℝ Space) t :=
    (hasFDerivAt_id t).const_sub x
  have h2 : HasFDerivAt (fun t => κ (x - t))
      ((fderiv ℝ κ (x - t)).comp (-ContinuousLinearMap.id ℝ Space)) t :=
    ((hκ.differentiable (by simp) (x - t)).hasFDerivAt).comp t h1
  have h3 := h2.smul_const v
  rw [h3.fderiv]
  simp [kd]

theorem testLap_reflect {κ : Space → ℝ} (hκ : ContDiff ℝ ∞ κ) (x v : Space) :
    testLap (fun t => κ (x - t) • v) =
      fun t => ∑ i : Fin 3, kd i (kd i κ) (x - t) • v := by
  funext t
  unfold testLap
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [testPartial_reflect hκ x v i]
  have hκ' : ContDiff ℝ ∞ (fun y => -kd i κ y) := (contDiff_kd hκ i).neg
  rw [testPartial_reflect hκ' x v i, kd_neg hκ i]
  simp

theorem isVectorTest_reflect {κ : Space → ℝ} (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ)
    (x v : Space) : IsVectorTest (fun t => κ (x - t) • v) := by
  refine ⟨(hκ.comp (contDiff_const.sub contDiff_id)).smul contDiff_const, ?_⟩
  have h : HasCompactSupport (fun t => κ (x - t)) :=
    hc.comp_homeomorph (Homeomorph.subLeft x)
  exact h.smul_right

/-! ## Convolutions with `L²` fields -/

theorem continuous_cv {κ : Space → ℝ} (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ)
    (u : L2Space) : Continuous (Sob.cv volume κ (u : SpatialField)) :=
  (Sob.contDiff_cv hκ hc ((Lp.memLp u).locallyIntegrable (by norm_num))).continuous

theorem memLp_cv {κ : Space → ℝ} (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ)
    (u : L2Space) : MemLp (Sob.cv volume κ (u : SpatialField)) 2 volume := by
  refine ⟨(continuous_cv hκ hc u).aestronglyMeasurable, ?_⟩
  refine (Sob.eLpNorm_cv_le hκ.continuous (Lp.aestronglyMeasurable u) one_le_two
    ENNReal.ofNat_ne_top).trans_lt (ENNReal.mul_lt_top ?_ (Lp.eLpNorm_lt_top u))
  exact (hκ.continuous.integrable_of_hasCompactSupport hc).2

/-- `⟨(κ ⋆ u)(x), v⟩ = ⟨u, κ(x - ·)v⟩`. -/
theorem inner_cv_apply {κ : Space → ℝ} (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ)
    (u : L2Space) (x v : Space) :
    inner ℝ v (Sob.cv volume κ (u : SpatialField) x) =
      inner ℝ u (toL2 (fun t => κ (x - t) • v)) := by
  have hψ := isVectorTest_reflect hκ hc x v
  have hgc : HasCompactSupport (fun t => κ (x - t)) :=
    hc.comp_homeomorph (Homeomorph.subLeft x)
  have hint : Integrable (fun t => κ (x - t) • (u : SpatialField) t) :=
    ((Lp.memLp u).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      (hκ.continuous.comp (continuous_const.sub continuous_id)) hgc
  rw [Sob.cv_apply]
  have h1 := (innerSL ℝ v).integral_comp_comm hint
  simp only [innerSL_apply_apply] at h1
  rw [← h1, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 (L13.isVectorTest_memLp hψ)] with t ht
  rw [ht, real_inner_smul_right, real_inner_smul_right, real_inner_comm]

/-! ## `Δ(κ ⋆ f) = κ ⋆ g` -/

theorem cv_lap {f g : L2Space}
    (hfg : ∀ φ : Space → Space, IsVectorTest φ →
      inner ℝ f (toL2 (testLap φ)) = inner ℝ g (toL2 φ))
    {κ : Space → ℝ} (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) (x : Space) :
    ∑ i : Fin 3, Sob.cv volume (kd i (kd i κ)) (f : SpatialField) x =
      Sob.cv volume κ (g : SpatialField) x := by
  have hkk : ∀ i, ContDiff ℝ ∞ (kd i (kd i κ)) := fun i => contDiff_kd (contDiff_kd hκ i) i
  have hkkc : ∀ i, HasCompactSupport (kd i (kd i κ)) := fun i =>
    hasCompactSupport_kd (hasCompactSupport_kd hc i) i
  apply ext_inner_left ℝ
  intro v
  rw [inner_sum, inner_cv_apply hκ hc g x v, ← hfg _ (isVectorTest_reflect hκ hc x v),
    testLap_reflect hκ x v]
  have hm : ∀ i, MemLp (fun t => kd i (kd i κ) (x - t) • v) 2 volume := fun i =>
    L13.isVectorTest_memLp (isVectorTest_reflect (hkk i) (hkkc i) x v)
  have hsum : toL2 (fun t => ∑ i : Fin 3, kd i (kd i κ) (x - t) • v) =
      ∑ i : Fin 3, toL2 (fun t => kd i (kd i κ) (x - t) • v) := by
    have e : (fun t => ∑ i : Fin 3, kd i (kd i κ) (x - t) • v) =
        (fun t => kd 0 (kd 0 κ) (x - t) • v) + (fun t => kd 1 (kd 1 κ) (x - t) • v) +
          (fun t => kd 2 (kd 2 κ) (x - t) • v) := by
      funext t
      simp [Fin.sum_univ_three]
    rw [e, L13.toL2_add' ((hm 0).add (hm 1)) (hm 2), L13.toL2_add' (hm 0) (hm 1),
      Fin.sum_univ_three]
  rw [hsum, inner_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact inner_cv_apply (hkk i) (hkkc i) f x v

/-! ## The mollified field in `H²` -/

/-- `∂ᵢ(κ ⋆ u) = (∂ᵢκ) ⋆ u`, as a weak derivative. -/
theorem hasWeak_cv {κ : Space → ℝ} (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ)
    (u : L2Space) (i : Fin 3) :
    HasWeakSpatialDerivative i (Sob.cv volume κ (u : SpatialField))
      (Sob.cv volume (kd i κ) (u : SpatialField)) := by
  have hloc : LocallyIntegrable (u : SpatialField) volume :=
    (Lp.memLp u).locallyIntegrable (by norm_num)
  have h := hasWeakSpatialDerivative_of_contDiff
    ((Sob.contDiff_cv hκ hc hloc).of_le (by simp)) i
  have e : (fun x => fderiv ℝ (Sob.cv volume κ (u : SpatialField)) x (coordinateVector i)) =
      Sob.cv volume (kd i κ) (u : SpatialField) := by
    funext x
    exact Sob.fderiv_cv_apply hκ hc hloc x _
  rwa [e] at h

/-- `κ ⋆ u` as an `H²` field, with first derivatives `(∂ᵢκ) ⋆ u` and second derivatives
`(∂ⱼ∂ᵢκ) ⋆ u`. -/
def mollH2 {κ : Space → ℝ} (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) (u : L2Space) :
    H2 :=
  H2.ofFields (Sob.cv volume κ (u : SpatialField))
    (fun i => Sob.cv volume (kd i κ) (u : SpatialField))
    (fun i j => Sob.cv volume (kd j (kd i κ)) (u : SpatialField))
    (memLp_cv hκ hc u) (fun i => memLp_cv (contDiff_kd hκ i) (hasCompactSupport_kd hc i) u)
    (fun i j => memLp_cv (contDiff_kd (contDiff_kd hκ i) j)
      (hasCompactSupport_kd (hasCompactSupport_kd hc i) j) u)
    (fun i => hasWeak_cv hκ hc u i)
    (fun i j => hasWeak_cv (contDiff_kd hκ i) (hasCompactSupport_kd hc i) u j)

/-- Under `⟨f, Δφ⟩ = ⟨g, φ⟩`, the Laplacian of `κ ⋆ f` is `κ ⋆ g`. -/
theorem laplace_mollH2 {f g : L2Space}
    (hfg : ∀ φ : Space → Space, IsVectorTest φ →
      inner ℝ f (toL2 (testLap φ)) = inner ℝ g (toL2 φ))
    {κ : Space → ℝ} (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) :
    H2.laplace (mollH2 hκ hc f) = toL2 (Sob.cv volume κ (g : SpatialField)) := by
  have hm : ∀ i, MemLp (Sob.cv volume (kd i (kd i κ)) (f : SpatialField)) 2 volume := fun i =>
    memLp_cv (contDiff_kd (contDiff_kd hκ i) i)
      (hasCompactSupport_kd (hasCompactSupport_kd hc i) i) f
  have e : Sob.cv volume κ (g : SpatialField) =
      Sob.cv volume (kd 0 (kd 0 κ)) (f : SpatialField) +
        Sob.cv volume (kd 1 (kd 1 κ)) (f : SpatialField) +
          Sob.cv volume (kd 2 (kd 2 κ)) (f : SpatialField) := by
    funext x
    rw [← cv_lap hfg hκ hc x, Fin.sum_univ_three]
    rfl
  rw [H2.laplace_eq, e, L13.toL2_add' ((hm 0).add (hm 1)) (hm 2),
    L13.toL2_add' (hm 0) (hm 1), Fin.sum_univ_three]
  rfl

/-! ## Closedness of the weak Laplacian -/

/-- **The weak Laplacian graph is closed under `L²` convergence of values and Laplacians.**
If `Fₙ ∈ H¹` has weak Laplacian `Lₙ`, `Fₙ → f` and `Lₙ → g` in `L²`, then
`‖∇(Fₙ - Fₘ)‖² = -⟨Lₙ - Lₘ, Fₙ - Fₘ⟩`, so `Fₙ` is Cauchy in `H¹`; its limit has value `f` and
weak Laplacian `g`. -/
theorem exists_hasWeakLaplacian_of_tendsto {F : ℕ → H1} {L : ℕ → L2Space} {f g : L2Space}
    (hL : ∀ n, HasWeakLaplacian (F n) (L n))
    (hf : Tendsto (fun n => (F n).value) atTop (𝓝 f)) (hg : Tendsto L atTop (𝓝 g)) :
    ∃ F' : H1, F'.value = f ∧ HasWeakLaplacian F' g := by
  have hbound : ∀ n m, ‖F n - F m‖ ≤ ‖(F n).value - (F m).value‖ + ‖L n - L m‖ := by
    intro n m
    have hval : (F n - F m).value = (F n).value - (F m).value := map_sub H1.valueCLM (F n) (F m)
    have hlap := (hL n).sub (hL m) (F n - F m)
    simp only [real_inner_self_eq_norm_sq] at hlap
    rw [hval] at hlap
    have hns := H1.norm_sq (F n - F m)
    rw [hval] at hns
    set a := ‖(F n).value - (F m).value‖ with ha
    set b := ‖L n - L m‖ with hb
    set N := ∑ i : Fin 3, ‖(F n - F m).derivative i‖ ^ 2 with hN
    have hci : -(b * a) ≤ inner ℝ (L n - L m) ((F n).value - (F m).value) := by
      have := abs_real_inner_le_norm (L n - L m) ((F n).value - (F m).value)
      rw [← ha, ← hb] at this
      linarith [neg_abs_le (inner ℝ (L n - L m) ((F n).value - (F m).value))]
    have ha0 : 0 ≤ a := norm_nonneg _
    have hb0 : 0 ≤ b := norm_nonneg _
    have hx0 : 0 ≤ ‖F n - F m‖ := norm_nonneg _
    have hsq : ‖F n - F m‖ ^ 2 ≤ (a + b) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (‖F n - F m‖ - (a + b))]
  have hpair : Tendsto (fun n => ((F n).value, L n)) atTop (𝓝 (f, g)) := hf.prodMk_nhds hg
  have hcF : CauchySeq F := by
    have hcp := hpair.cauchySeq
    rw [Metric.cauchySeq_iff] at hcp ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hcp (ε / 2) (by linarith)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm n hn
    rw [Prod.dist_eq, max_lt_iff] at h1
    simp only [dist_eq_norm] at h1 ⊢
    linarith [hbound m n, h1.1, h1.2]
  obtain ⟨F', hF'⟩ := cauchySeq_tendsto_of_complete hcF
  refine ⟨F', ?_, ?_⟩
  · have hv : Tendsto (fun n => (F n).value) atTop (𝓝 F'.value) :=
      (H1.valueCLM.continuous.tendsto F').comp hF'
    exact tendsto_nhds_unique hv hf
  · intro G
    have h1 : Tendsto (fun n => inner ℝ (L n) G.value) atTop (𝓝 (inner ℝ g G.value)) :=
      hg.inner tendsto_const_nhds
    have h2 : Tendsto (fun n => -∑ i : Fin 3, inner ℝ ((F n).derivative i) (G.derivative i))
        atTop (𝓝 (-∑ i : Fin 3, inner ℝ (F'.derivative i) (G.derivative i))) := by
      refine (tendsto_finsetSum _ (fun i _ => ?_)).neg
      have hd : Tendsto (fun n => (F n).derivative i) atTop (𝓝 (F'.derivative i)) :=
        ((H1.derivativeCLM i).continuous.tendsto F').comp hF'
      exact hd.inner tendsto_const_nhds
    have h3 : (fun n => inner ℝ (L n) G.value) =
        fun n => -∑ i : Fin 3, inner ℝ ((F n).derivative i) (G.derivative i) :=
      funext fun n => hL n G
    rw [h3] at h1
    exact tendsto_nhds_unique h1 h2

/-! ## The theorem -/

/-- The bumps `κₙ` with radii `1/(n+2) < 1/(n+1)`. -/
def bumpSeq (n : ℕ) : ContDiffBump (0 : Space) :=
  ⟨1 / ((n : ℝ) + 2), 1 / ((n : ℝ) + 1), by positivity,
    one_div_lt_one_div_of_lt (by positivity) (by linarith)⟩

theorem tendsto_bumpSeq_rOut : Tendsto (fun n => (bumpSeq n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- `κₙ ⋆ u → u` in `L²`. -/
theorem tendsto_toL2_cv_bumpSeq (u : L2Space) :
    Tendsto (fun n => toL2 (Sob.cv volume ((bumpSeq n).normed volume) (u : SpatialField)))
      atTop (𝓝 u) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have h := Sob.tendsto_eLpNorm_moll_sub (p := 2) (by norm_num) (Lp.memLp u)
    tendsto_bumpSeq_rOut
  refine Tendsto.congr (fun n => ?_) h
  rw [eLpNorm_sub_comm]
  refine eLpNorm_congr_ae ?_
  filter_upwards [coeFn_toL2 (memLp_cv ((bumpSeq n).contDiff_normed (μ := volume))
    ((bumpSeq n).hasCompactSupport_normed (μ := volume)) u)] with x hx
  rw [Pi.sub_apply, Pi.sub_apply, hx]
  rfl

/-- **Elliptic `H¹` regularity on `ℝ³`** (`LaplacianH1Regularity`; tex lines 308–312, B1009,
INF11): if `f, g ∈ L²(ℝ³;ℝ³)` and `⟨f, Δφ⟩ = ⟨g, φ⟩` for every vector test `φ`, then `f ∈ H¹`
with weak `H¹` Laplacian `g`. -/
theorem laplacianH1Regularity : LaplacianH1Regularity := by
  intro f g hfg
  have hκ : ∀ n, ContDiff ℝ ∞ ((bumpSeq n).normed volume) := fun n =>
    (bumpSeq n).contDiff_normed
  have hc : ∀ n, HasCompactSupport ((bumpSeq n).normed volume) := fun n =>
    (bumpSeq n).hasCompactSupport_normed
  refine exists_hasWeakLaplacian_of_tendsto
    (F := fun n => h2ToH1 (mollH2 (hκ n) (hc n) f))
    (L := fun n => H2.laplace (mollH2 (hκ n) (hc n) f))
    (fun n => hasWeakLaplacian_h2 _) (tendsto_toL2_cv_bumpSeq f) ?_
  exact Tendsto.congr (fun n => (laplace_mollH2 hfg (hκ n) (hc n)).symm)
    (tendsto_toL2_cv_bumpSeq g)

end UnforcedLeray.Blueprint.ModeId
