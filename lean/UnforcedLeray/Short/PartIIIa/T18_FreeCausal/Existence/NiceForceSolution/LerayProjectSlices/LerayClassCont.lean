import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.GaussianSliceMemLp

/-!
# Part III-a, task `PartIII-a:T18/2/4/2/2`: continuity of the projected slices

Target (`Sub/T18_2_4_2.lean`): `LerayClassCont`. For a nice family `u` the classes
`s ↦ 𝒫₀ Re u(s)`, `𝒫₀ Im u(s)`, `s ↦ 𝒫₀ Re ∂_j u(s)`, `𝒫₀ Im ∂_j u(s)` are continuous on `(0, ∞)`.

Proof. `𝒫₀` is a continuous linear map, so it suffices to show that `s ↦ toL2v c (reVec (Φ s))`
is continuous (and the same for `imVec`). This is dominated convergence on the cell: the
`L²`-distance squared is `∫ |w(s,·) - w(s₀,·)|²`, the integrand tends to `0` pointwise by joint
continuity, and it is dominated by `(4 C e^{-κ η²})²`, which is integrable on the cell.
The slice derivative `pdC j (u_i(s,·)) x` is jointly continuous in `(s, x)` by the chain rule
(`cc_pdC_slice_eq`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Continuity of a `Vec2`-valued map from its two real components. -/
theorem cc_cont_vec2 {α : Type*} [TopologicalSpace α] (a b : α → ℝ) (ha : Continuous a)
    (hb : Continuous b) : Continuous fun x => UnforcedLeray.Cyl.vec (a x) (b x) := by
  unfold UnforcedLeray.Cyl.vec
  fun_prop

/-- `(eLpNorm F 2 μ).toReal² = ∫ ‖F‖²` for a strongly measurable `F` with values in a normed group. -/
theorem cc_toReal_eLpNorm_two_sq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {F : α → E} (hF : AEStronglyMeasurable F μ) :
    (eLpNorm F 2 μ).toReal ^ 2 = ∫ x, ‖F x‖ ^ 2 ∂μ := by
  have hm2 : AEStronglyMeasurable (fun x => ‖F x‖ ^ 2) μ := hF.norm.pow 2
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => by positivity)
    hm2, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ← ENNReal.toReal_pow]
  congr 1
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp only [ENNReal.toReal_ofNat, Nat.cast_ofNat]
  norm_num

/-- The squared `L²` norm of a class is the integral of the squared norm of a representative. -/
theorem cc_sq_norm_toLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → UnforcedLeray.Cyl.Vec2} (hg : MemLp g 2 μ) :
    ‖hg.toLp g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂μ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp hg)]
  exact cc_toReal_eLpNorm_two_sq hg.aestronglyMeasurable

/-- Chain rule: the slice derivative of a joint function is a partial derivative of it. -/
theorem cc_pdC_slice_eq {G : ℝ × (ℝ × ℝ) → ℂ} (hG : Differentiable ℝ G) (s : ℝ)
    (x : ℝ × ℝ) (j : Fin 2) :
    pdC j (fun y => G (s, y)) x = fderiv ℝ G (s, x) (0, B0579.dir j) := by
  have hinner := (hasFDerivAt_const (𝕜 := ℝ) s x).prodMk (hasFDerivAt_id x)
  have hd : HasFDerivAt G (fderiv ℝ G (s, x)) (s, x) := (hG (s, x)).hasFDerivAt
  have hc : HasFDerivAt (fun y : ℝ × ℝ => G (s, y))
      ((fderiv ℝ G (s, x)).comp ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod
        (ContinuousLinearMap.id ℝ (ℝ × ℝ)))) x :=
    hd.comp x hinner
  unfold pdC
  rw [hc.fderiv]
  simp

/-- The slice derivative is continuous in the age, jointly with the space variable fixed. -/
theorem cc_pdC_slice_cont {G : ℝ × (ℝ × ℝ) → ℂ} (hG : ContDiff ℝ ∞ G) (j : Fin 2)
    (x : ℝ × ℝ) : Continuous fun s : ℝ => pdC j (fun y => G (s, y)) x := by
  have e : (fun s : ℝ => pdC j (fun y => G (s, y)) x) =
      fun s : ℝ => fderiv ℝ G (s, x) (0, B0579.dir j) :=
    funext fun s => cc_pdC_slice_eq (hG.differentiable (by simp)) s x j
  rw [e]
  have hf : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by simp)
  exact (hf.comp (continuous_id.prodMk continuous_const)).clm_apply continuous_const

/-- **Continuity of the `L²` class of a Gaussian-bounded family.** If `s ↦ w s x` is continuous,
`x ↦ w s x` is continuous and `‖w s x‖` is dominated by a Gaussian (locally uniformly in `s`),
then `s ↦ toL2v c (w s)` is continuous at every `s₀`. -/
theorem cc_toL2v_contAt (c : ℝ) (w : ℝ → ℝ × ℝ → UnforcedLeray.Cyl.Vec2)
    (hx : ∀ s, Continuous (w s)) (hs : ∀ x, Continuous fun s => w s x)
    (hb : ∀ s₂ : ℝ, ∃ C κ : ℝ, 0 < κ ∧ ∀ s, s ≤ s₂ → ∀ x : ℝ × ℝ,
      ‖w s x‖ ≤ 2 * (C * Real.exp (-κ * x.2 ^ 2)))
    (s₀ : ℝ) :
    ContinuousAt (fun s => toL2v c (w s)) s₀ := by
  obtain ⟨C, κ, hκ, hC⟩ := hb (s₀ + 1)
  have hmem : ∀ s, s ≤ s₀ + 1 → MemLp (w s) 2 (UnforcedLeray.Cyl.cellμ c) := fun s hs' =>
    memLp_of_gauss_bound_aux c C κ hκ (w s) (hx s) (fun x => hC s hs' x)
  have hdiff : ∀ s, s ≤ s₀ + 1 →
      ‖toL2v c (w s) - toL2v c (w s₀)‖ ^ 2 =
        ∫ x, ‖w s x - w s₀ x‖ ^ 2 ∂(UnforcedLeray.Cyl.cellμ c) := by
    intro s hs'
    have hm1 := hmem s hs'
    have hm0 := hmem s₀ (by linarith)
    unfold toL2v
    rw [dif_pos hm1, dif_pos hm0, ← MeasureTheory.MemLp.toLp_sub]
    exact cc_sq_norm_toLp (hm1.sub hm0)
  have hb1 : ∀ᶠ s in 𝓝 s₀, s ≤ s₀ + 1 :=
    Filter.eventually_of_mem (Iio_mem_nhds (lt_add_one s₀)) (fun s hs' => le_of_lt hs')
  have hint : Integrable (fun x : ℝ × ℝ => (4 * (C * Real.exp (-κ * x.2 ^ 2))) ^ 2)
      (UnforcedLeray.Cyl.cellμ c) :=
    ((gauss_dom_memLp_aux c κ hκ).integrable_sq.const_mul (16 * C ^ 2)).congr
      (Filter.Eventually.of_forall fun x => by beta_reduce; ring)
  have hcont_s : ∀ s, Continuous fun x => ‖w s x - w s₀ x‖ ^ 2 := fun s =>
    (((hx s).sub (hx s₀)).norm).pow 2
  have hbd : ∀ᶠ s in 𝓝 s₀, ∀ᵐ x ∂(UnforcedLeray.Cyl.cellμ c),
      ‖‖w s x - w s₀ x‖ ^ 2‖ ≤ (4 * (C * Real.exp (-κ * x.2 ^ 2))) ^ 2 := by
    filter_upwards [hb1] with s hs'
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h1 : ‖w s x - w s₀ x‖ ≤ 4 * (C * Real.exp (-κ * x.2 ^ 2)) := by
      have := norm_sub_le (w s x) (w s₀ x)
      linarith [hC s hs' x, hC s₀ (by linarith) x]
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    gcongr
  have hlimpt : ∀ᵐ x ∂(UnforcedLeray.Cyl.cellμ c),
      Tendsto (fun s => ‖w s x - w s₀ x‖ ^ 2) (𝓝 s₀) (𝓝 (0 : ℝ)) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have hcs : Continuous fun s => ‖w s x - w s₀ x‖ ^ 2 :=
      ((((hs x).sub continuous_const).norm).pow 2)
    have h : Tendsto (fun s => ‖w s x - w s₀ x‖ ^ 2) (𝓝 s₀)
        (𝓝 (‖w s₀ x - w s₀ x‖ ^ 2)) := hcs.tendsto s₀
    simpa using h
  have hlim : Tendsto (fun s => ∫ x, ‖w s x - w s₀ x‖ ^ 2 ∂(UnforcedLeray.Cyl.cellμ c))
      (𝓝 s₀) (𝓝 0) := by
    have hT := tendsto_integral_filter_of_dominated_convergence
      (μ := UnforcedLeray.Cyl.cellμ c) (l := 𝓝 s₀)
      (F := fun s x => ‖w s x - w s₀ x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (fun x => (4 * (C * Real.exp (-κ * x.2 ^ 2))) ^ 2)
      (Filter.Eventually.of_forall fun s => (hcont_s s).aestronglyMeasurable) hbd hint hlimpt
    convert hT using 2 <;> simp
  have hlim2 : Tendsto (fun s => ‖toL2v c (w s) - toL2v c (w s₀)‖ ^ 2) (𝓝 s₀) (𝓝 0) := by
    refine hlim.congr' ?_
    filter_upwards [hb1] with s hs'
    exact (hdiff s hs').symm
  have hnorm : Tendsto (fun s => ‖toL2v c (w s) - toL2v c (w s₀)‖) (𝓝 s₀) (𝓝 0) := by
    have h4 := (Real.continuous_sqrt.tendsto 0).comp hlim2
    rw [Real.sqrt_zero] at h4
    refine h4.congr (fun s => ?_)
    exact Real.sqrt_sq (norm_nonneg _)
  show Tendsto (fun s => toL2v c (w s)) (𝓝 s₀) (𝓝 (toL2v c (w s₀)))
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

/-- Continuity of the `L²` class of a jointly continuous, Gaussian-bounded family. -/
theorem cc_family_cont (c : ℝ) (w : ℝ → ℝ × ℝ → UnforcedLeray.Cyl.Vec2)
    (hjoint : Continuous fun p : ℝ × (ℝ × ℝ) => w p.1 p.2)
    (hb : ∀ s₂ : ℝ, ∃ C κ : ℝ, 0 < κ ∧ ∀ s, s ≤ s₂ → ∀ x : ℝ × ℝ,
      ‖w s x‖ ≤ 2 * (C * Real.exp (-κ * x.2 ^ 2))) :
    Continuous fun s => toL2v c (w s) := by
  rw [continuous_iff_continuousAt]
  intro s₀
  refine cc_toL2v_contAt c w (fun s => ?_) (fun x => ?_) hb s₀
  · exact hjoint.comp (f := fun x : ℝ × ℝ => ((s, x) : ℝ × (ℝ × ℝ))) (by fun_prop)
  · exact hjoint.comp (f := fun s : ℝ => ((s, x) : ℝ × (ℝ × ℝ))) (by fun_prop)

/-- The derivative `(s,x) ↦ ∂_j u_i(s,x)` is jointly continuous. -/
theorem cc_pdC_joint (u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (hu : ∀ i : Fin 2, ContDiff ℝ ∞ fun p : ℝ × (ℝ × ℝ) => u p i) (i j : Fin 2) :
    Continuous fun p : ℝ × (ℝ × ℝ) => pdC j (fun y => u (p.1, y) i) p.2 := by
  have hG : ContDiff ℝ ∞ fun q : ℝ × (ℝ × ℝ) => u q i := hu i
  have e : (fun p : ℝ × (ℝ × ℝ) => pdC j (fun y => u (p.1, y) i) p.2) =
      fun p => fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => u q i) p (0, B0579.dir j) := by
    funext p
    exact cc_pdC_slice_eq (hG.differentiable (by simp)) p.1 p.2 j
  rw [e]
  exact (hG.continuous_fderiv (by simp)).clm_apply continuous_const

/-- The slice derivative is bounded by the operator norm of the full derivative. -/
theorem cc_pdC_norm_le (g : ℝ × ℝ → ℂ) (j : Fin 2) (x : ℝ × ℝ) :
    ‖pdC j g x‖ ≤ ‖fderiv ℝ g x‖ := by
  have hdir : ‖B0579.dir j‖ ≤ 1 := by
    fin_cases j <;> simp [B0579.dir, Prod.norm_def]
  unfold pdC
  calc ‖fderiv ℝ g x (B0579.dir j)‖
      ≤ ‖fderiv ℝ g x‖ * ‖B0579.dir j‖ := (fderiv ℝ g x).le_opNorm _
    _ ≤ ‖fderiv ℝ g x‖ * 1 := mul_le_mul_of_nonneg_left hdir (norm_nonneg _)
    _ = _ := mul_one _

/-- Pointwise Gaussian bounds of the values and of the slice derivatives of `u`. -/
theorem cc_val_bound (u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (hdec : GaussianDecayLoc u) (s₂ : ℝ) :
    ∃ C κ : ℝ, 0 < κ ∧ ∀ (s : ℝ), s ≤ s₂ → ∀ (x : ℝ × ℝ) (i : Fin 2),
      ‖u (s, x) i‖ ≤ C * Real.exp (-κ * x.2 ^ 2) ∧
      ∀ j : Fin 2, ‖pdC j (fun y => u (s, y) i) x‖ ≤ C * Real.exp (-κ * x.2 ^ 2) := by
  obtain ⟨C, κ, hκ, hb⟩ := hdec s₂
  refine ⟨C, κ, hκ, fun s hs x i => ⟨?_, fun j => ?_⟩⟩
  · have h1 := hb s x i hs
    linarith [norm_nonneg (fderiv ℝ (fun y => u (s, y) i) x)]
  · have h1 := hb s x i hs
    have h2 := cc_pdC_norm_le (fun y => u (s, y) i) j x
    linarith [norm_nonneg (u (s, x) i)]

theorem cc_vec_re (z0 z1 : ℂ) (M : ℝ) (h0 : ‖z0‖ ≤ M) (h1 : ‖z1‖ ≤ M) :
    ‖UnforcedLeray.Cyl.vec z0.re z1.re‖ ≤ 2 * M :=
  vec_norm_le_two_aux _ _ _ ((Complex.abs_re_le_norm _).trans h0)
    ((Complex.abs_re_le_norm _).trans h1)

theorem cc_vec_im (z0 z1 : ℂ) (M : ℝ) (h0 : ‖z0‖ ≤ M) (h1 : ‖z1‖ ≤ M) :
    ‖UnforcedLeray.Cyl.vec z0.im z1.im‖ ≤ 2 * M :=
  vec_norm_le_two_aux _ _ _ ((Complex.abs_im_le_norm _).trans h0)
    ((Complex.abs_im_le_norm _).trans h1)

/-- **Continuity of the projected slices** (`PartIII-a:T18/2/4/2/2`). -/
theorem lerayClassCont : UnforcedLeray.Short.IIIa.LerayClassCont := by
  intro c _hc u hu
  have hU : ∀ i : Fin 2, Continuous fun p : ℝ × (ℝ × ℝ) => u p i :=
    fun i => (hu.smooth i).continuous
  have hD : ∀ i : Fin 2, ContDiff ℝ ∞ fun p : ℝ × (ℝ × ℝ) => u p i := fun i => hu.smooth i
  -- real and imaginary parts of the slices
  have hReU : Continuous fun s => toL2v c (reVec (uSl u s)) := by
    refine cc_family_cont c (fun s x => reVec (uSl u s) x) ?_ ?_
    · exact cc_cont_vec2 (fun p : ℝ × (ℝ × ℝ) => (u p 0).re) (fun p : ℝ × (ℝ × ℝ) => (u p 1).re)
        (Complex.continuous_re.comp (hU 0)) (Complex.continuous_re.comp (hU 1))
    · intro s₂
      obtain ⟨C, κ, hκ, h⟩ := cc_val_bound u hu.decay s₂
      exact ⟨C, κ, hκ, fun s hs x => cc_vec_re (u (s, x) 0) (u (s, x) 1)
        (C * Real.exp (-κ * x.2 ^ 2)) ((h s hs x 0).1) ((h s hs x 1).1)⟩
  have hImU : Continuous fun s => toL2v c (imVec (uSl u s)) := by
    refine cc_family_cont c (fun s x => imVec (uSl u s) x) ?_ ?_
    · exact cc_cont_vec2 (fun p : ℝ × (ℝ × ℝ) => (u p 0).im) (fun p : ℝ × (ℝ × ℝ) => (u p 1).im)
        (Complex.continuous_im.comp (hU 0)) (Complex.continuous_im.comp (hU 1))
    · intro s₂
      obtain ⟨C, κ, hκ, h⟩ := cc_val_bound u hu.decay s₂
      exact ⟨C, κ, hκ, fun s hs x => cc_vec_im (u (s, x) 0) (u (s, x) 1)
        (C * Real.exp (-κ * x.2 ^ 2)) ((h s hs x 0).1) ((h s hs x 1).1)⟩
  have hReD : ∀ j : Fin 2, Continuous fun s => toL2v c (reVec (duSl u s j)) := by
    intro j
    refine cc_family_cont c (fun s x => reVec (duSl u s j) x) ?_ ?_
    · exact cc_cont_vec2 (fun p : ℝ × (ℝ × ℝ) => (pdC j (fun y => u (p.1, y) 0) p.2).re)
        (fun p : ℝ × (ℝ × ℝ) => (pdC j (fun y => u (p.1, y) 1) p.2).re)
        (Complex.continuous_re.comp (cc_pdC_joint u hD 0 j))
        (Complex.continuous_re.comp (cc_pdC_joint u hD 1 j))
    · intro s₂
      obtain ⟨C, κ, hκ, h⟩ := cc_val_bound u hu.decay s₂
      exact ⟨C, κ, hκ, fun s hs x => cc_vec_re (pdC j (fun y => u (s, y) 0) x)
        (pdC j (fun y => u (s, y) 1) x) (C * Real.exp (-κ * x.2 ^ 2))
        ((h s hs x 0).2 j) ((h s hs x 1).2 j)⟩
  have hImD : ∀ j : Fin 2, Continuous fun s => toL2v c (imVec (duSl u s j)) := by
    intro j
    refine cc_family_cont c (fun s x => imVec (duSl u s j) x) ?_ ?_
    · exact cc_cont_vec2 (fun p : ℝ × (ℝ × ℝ) => (pdC j (fun y => u (p.1, y) 0) p.2).im)
        (fun p : ℝ × (ℝ × ℝ) => (pdC j (fun y => u (p.1, y) 1) p.2).im)
        (Complex.continuous_im.comp (cc_pdC_joint u hD 0 j))
        (Complex.continuous_im.comp (cc_pdC_joint u hD 1 j))
    · intro s₂
      obtain ⟨C, κ, hκ, h⟩ := cc_val_bound u hu.decay s₂
      exact ⟨C, κ, hκ, fun s hs x => cc_vec_im (pdC j (fun y => u (s, y) 0) x)
        (pdC j (fun y => u (s, y) 1) x) (C * Real.exp (-κ * x.2 ^ 2))
        ((h s hs x 0).2 j) ((h s hs x 1).2 j)⟩
  refine ⟨?_, ?_, fun j => ⟨?_, ?_⟩⟩
  · exact ((UnforcedLeray.Cyl.P0 c).continuous.comp hReU).continuousOn
  · exact ((UnforcedLeray.Cyl.P0 c).continuous.comp hImU).continuousOn
  · exact ((UnforcedLeray.Cyl.P0 c).continuous.comp (hReD j)).continuousOn
  · exact ((UnforcedLeray.Cyl.P0 c).continuous.comp (hImD j)).continuousOn

end UnforcedLeray.Short.IIIa
