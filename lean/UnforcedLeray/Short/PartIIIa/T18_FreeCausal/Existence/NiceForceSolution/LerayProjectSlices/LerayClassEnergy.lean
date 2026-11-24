import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.GaussianSliceMemLp

/-!
# Part III-a, task `PartIII-a:T18/2/4/2/3`: local energy bound of the projected slices

Target (`Sub/T18_2_4_2.lean`): `LerayClassEnergy`. For a nice family `u` and every `s₂` there is `M`
with `∫_cell (|𝒫₀ u(s)|² + |𝒫₀ ∇u(s)|²) ≤ M` for all `0 < s ≤ s₂`.

Proof. `‖𝒫₀‖ ≤ 1` gives the `L²` contraction `∫ |𝒫₀ g|² ≤ ∫ |g|²` for the real and imaginary parts
of `u(s)` and `∂_j u(s)` (six classes in all). Each `|g|²` is bounded by the fixed Gaussian
`(2 C e^{-κ η²})²`, which is integrable on the cell, uniformly for `s ≤ s₂`. The pointwise identity
`|𝒫₀ f|² = |Re 𝒫₀ f|² + |Im 𝒫₀ f|²` turns the integrand into the sum of the six squares.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The Gaussian majorant `(2 C e^{-κ η²})²` used for the squared components. -/
def ce_bnd (C κ : ℝ) (x : ℝ × ℝ) : ℝ := (2 * (C * Real.exp (-κ * x.2 ^ 2))) ^ 2

/-- Continuity of a `Vec2`-valued map from its two real components. -/
theorem ce_cont_vec2 {α : Type*} [TopologicalSpace α] (a b : α → ℝ) (ha : Continuous a)
    (hb : Continuous b) : Continuous fun x => UnforcedLeray.Cyl.vec (a x) (b x) := by
  unfold UnforcedLeray.Cyl.vec
  fun_prop

/-- `(eLpNorm F 2 μ).toReal² = ∫ ‖F‖²` for a strongly measurable `F` with values in a normed group. -/
theorem ce_toReal_eLpNorm_two_sq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
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

/-- The squared norm of an `L²` class is the lower integral of the squared norm, as an `ENNReal`. -/
theorem ce_lint_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : Lp UnforcedLeray.Cyl.Vec2 2 μ) :
    ∫⁻ x, ENNReal.ofReal (‖F x‖ ^ 2) ∂μ = ENNReal.ofReal (‖F‖ ^ 2) := by
  have hn : ‖F‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 ∂μ := by
    rw [Lp.norm_def]
    exact ce_toReal_eLpNorm_two_sq (Lp.aestronglyMeasurable F)
  have hint : Integrable (fun x => ‖F x‖ ^ 2) μ := by
    have h := (Lp.memLp F).integrable_norm_rpow (p := 2) two_ne_zero ENNReal.ofNat_ne_top
    simpa [Real.rpow_two] using h
  rw [hn, ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _)]

/-- Measurability of the squared-norm lower integrand of an `L²` class. -/
theorem ce_aemeas {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : Lp UnforcedLeray.Cyl.Vec2 2 μ) :
    AEMeasurable (fun x => ENNReal.ofReal (‖F x‖ ^ 2)) μ :=
  ENNReal.measurable_ofReal.comp_aemeasurable ((Lp.aestronglyMeasurable F).norm.pow 2).aemeasurable

/-- `𝒫₀` contracts the lower integral of the squared norm (`‖𝒫₀‖ ≤ 1`). -/
theorem ce_contract (c : ℝ) (F : UnforcedLeray.Cyl.L2v c) :
    ∫⁻ x, ENNReal.ofReal (‖(UnforcedLeray.Cyl.P0 c F) x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) ≤
      ∫⁻ x, ENNReal.ofReal (‖F x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) := by
  rw [ce_lint_norm_sq (UnforcedLeray.Cyl.P0 c F), ce_lint_norm_sq F]
  apply ENNReal.ofReal_le_ofReal
  have h : ‖UnforcedLeray.Cyl.P0 c F‖ ≤ ‖F‖ := by
    calc ‖UnforcedLeray.Cyl.P0 c F‖ ≤ ‖UnforcedLeray.Cyl.P0 c‖ * ‖F‖ :=
          (UnforcedLeray.Cyl.P0 c).le_opNorm F
      _ ≤ 1 * ‖F‖ := mul_le_mul_of_nonneg_right UnforcedLeray.Cyl.norm_P0_le (norm_nonneg F)
      _ = ‖F‖ := one_mul _
  gcongr

/-- A single component: the contraction of the `L²` class of a dominated field. -/
theorem ce_piece (c : ℝ) (g : ℝ × ℝ → UnforcedLeray.Cyl.Vec2)
    (hg : MemLp g 2 (UnforcedLeray.Cyl.cellμ c)) (bnd : ℝ × ℝ → ℝ)
    (hbnd : ∀ x, ‖g x‖ ^ 2 ≤ bnd x) :
    ∫⁻ x, ENNReal.ofReal (‖(UnforcedLeray.Cyl.P0 c (toL2v c g)) x‖ ^ 2)
        ∂(UnforcedLeray.Cyl.cellμ c) ≤
      ∫⁻ x, ENNReal.ofReal (bnd x) ∂(UnforcedLeray.Cyl.cellμ c) := by
  have e : toL2v c g = hg.toLp g := by
    unfold toL2v
    rw [dif_pos hg]
  rw [e]
  refine le_trans (ce_contract c (hg.toLp g)) ?_
  calc ∫⁻ x, ENNReal.ofReal (‖(hg.toLp g) x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c)
      = ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) :=
        lintegral_congr_ae (by
          filter_upwards [MemLp.coeFn_toLp hg] with x hx
          rw [hx])
    _ ≤ ∫⁻ x, ENNReal.ofReal (bnd x) ∂(UnforcedLeray.Cyl.cellμ c) :=
        lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hbnd x))

/-- The real and imaginary contraction bounds for one `ℂ²`-valued family with Gaussian bound. -/
theorem ce_piece_fam (c : ℝ) (C κ : ℝ) (hκ : 0 < κ) (Φ : ℝ × ℝ → Fin 2 → ℂ)
    (hΦ : ∀ i, Continuous fun x => Φ x i)
    (hb : ∀ x i, ‖Φ x i‖ ≤ C * Real.exp (-κ * x.2 ^ 2)) :
    ∫⁻ x, ENNReal.ofReal (‖P0re c Φ x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) ≤
        ∫⁻ x, ENNReal.ofReal (ce_bnd C κ x) ∂(UnforcedLeray.Cyl.cellμ c) ∧
      ∫⁻ x, ENNReal.ofReal (‖P0im c Φ x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) ≤
        ∫⁻ x, ENNReal.ofReal (ce_bnd C κ x) ∂(UnforcedLeray.Cyl.cellμ c) := by
  have hre : Continuous (reVec Φ) := by
    unfold reVec
    exact ce_cont_vec2 (fun x => (Φ x 0).re) (fun x => (Φ x 1).re)
      (Complex.continuous_re.comp (hΦ 0)) (Complex.continuous_re.comp (hΦ 1))
  have him : Continuous (imVec Φ) := by
    unfold imVec
    exact ce_cont_vec2 (fun x => (Φ x 0).im) (fun x => (Φ x 1).im)
      (Complex.continuous_im.comp (hΦ 0)) (Complex.continuous_im.comp (hΦ 1))
  have hbre : ∀ x, ‖reVec Φ x‖ ≤ 2 * (C * Real.exp (-κ * x.2 ^ 2)) := fun x =>
    vec_norm_le_two_aux (Φ x 0).re (Φ x 1).re (C * Real.exp (-κ * x.2 ^ 2))
      ((Complex.abs_re_le_norm _).trans (hb x 0)) ((Complex.abs_re_le_norm _).trans (hb x 1))
  have hbim : ∀ x, ‖imVec Φ x‖ ≤ 2 * (C * Real.exp (-κ * x.2 ^ 2)) := fun x =>
    vec_norm_le_two_aux (Φ x 0).im (Φ x 1).im (C * Real.exp (-κ * x.2 ^ 2))
      ((Complex.abs_im_le_norm _).trans (hb x 0)) ((Complex.abs_im_le_norm _).trans (hb x 1))
  have hmre : MemLp (reVec Φ) 2 (UnforcedLeray.Cyl.cellμ c) :=
    memLp_of_gauss_bound_aux c C κ hκ _ hre hbre
  have hmim : MemLp (imVec Φ) 2 (UnforcedLeray.Cyl.cellμ c) :=
    memLp_of_gauss_bound_aux c C κ hκ _ him hbim
  have hsre : ∀ x, ‖reVec Φ x‖ ^ 2 ≤ ce_bnd C κ x := fun x => by
    have h := hbre x
    unfold ce_bnd
    gcongr
  have hsim : ∀ x, ‖imVec Φ x‖ ^ 2 ≤ ce_bnd C κ x := fun x => by
    have h := hbim x
    unfold ce_bnd
    gcongr
  exact ⟨ce_piece c (reVec Φ) hmre (ce_bnd C κ) hsre, ce_piece c (imVec Φ) hmim (ce_bnd C κ) hsim⟩

/-- Six lower integrals split as a right-nested sum. -/
theorem ce_lint_six {α : Type*} [MeasurableSpace α] (μ : Measure α) (t1 t2 t3 t4 t5 t6 : α → ℝ≥0∞)
    (h1 : AEMeasurable t1 μ) (h2 : AEMeasurable t2 μ) (h3 : AEMeasurable t3 μ)
    (h4 : AEMeasurable t4 μ) (h5 : AEMeasurable t5 μ) :
    ∫⁻ x, (t1 x + (t2 x + (t3 x + (t4 x + (t5 x + t6 x))))) ∂μ =
      ∫⁻ x, t1 x ∂μ + (∫⁻ x, t2 x ∂μ + (∫⁻ x, t3 x ∂μ + (∫⁻ x, t4 x ∂μ +
        (∫⁻ x, t5 x ∂μ + ∫⁻ x, t6 x ∂μ)))) := by
  rw [lintegral_add_left' h1, lintegral_add_left' h2, lintegral_add_left' h3,
    lintegral_add_left' h4, lintegral_add_left' h5]

/-- Real-to-extended splitting of six nonnegative summands. -/
theorem ce_ofReal_chain (a1 a2 a3 a4 a5 a6 : ℝ) (h1 : 0 ≤ a1) (h2 : 0 ≤ a2) (h3 : 0 ≤ a3)
    (h4 : 0 ≤ a4) (h5 : 0 ≤ a5) (h6 : 0 ≤ a6) :
    ENNReal.ofReal (a1 + (a2 + (a3 + (a4 + (a5 + a6))))) =
      ENNReal.ofReal a1 + (ENNReal.ofReal a2 + (ENNReal.ofReal a3 +
        (ENNReal.ofReal a4 + (ENNReal.ofReal a5 + ENNReal.ofReal a6)))) := by
  rw [ENNReal.ofReal_add h1 (add_nonneg h2 (add_nonneg h3 (add_nonneg h4 (add_nonneg h5 h6))))]
  rw [ENNReal.ofReal_add h2 (add_nonneg h3 (add_nonneg h4 (add_nonneg h5 h6)))]
  rw [ENNReal.ofReal_add h3 (add_nonneg h4 (add_nonneg h5 h6))]
  rw [ENNReal.ofReal_add h4 (add_nonneg h5 h6)]
  rw [ENNReal.ofReal_add h5 h6]

/-- The Gaussian majorant is integrable on the cell. -/
theorem ce_bnd_integrable (c C κ : ℝ) (hκ : 0 < κ) :
    Integrable (ce_bnd C κ) (UnforcedLeray.Cyl.cellμ c) := by
  have h := ((gauss_dom_memLp_aux c κ hκ).integrable_sq).const_mul (4 * C ^ 2)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [ce_bnd]
  ring

/-- `|z|² = (Re z)² + (Im z)²` for a complex number written as `a + i b`. -/
theorem ce_norm_cplx_sq (x y : ℝ) :
    ‖((x : ℂ) + Complex.I * (y : ℂ))‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [Complex.sq_norm, mul_comm, Complex.normSq_add_mul_I]

/-- The Euclidean norm of `a + i b` built from two real vectors. -/
theorem ce_vnorm_cplx (a b : UnforcedLeray.Cyl.Vec2) :
    vnorm2 (fun i => ((a i : ℝ) : ℂ) + Complex.I * ((b i : ℝ) : ℂ)) ^ 2 =
      ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  unfold vnorm2
  rw [Real.sq_sqrt]
  · rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_two, ce_norm_cplx_sq, Real.norm_eq_abs, sq_abs]
    ring
  · positivity

theorem ce_vnorm2_sq' (a : Fin 2 → ℂ) : vnorm2 a ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
  unfold vnorm2
  rw [Real.sq_sqrt]
  positivity

theorem ce_tnorm2_sq' (T : Fin 2 → Fin 2 → ℂ) : tnorm2 T ^ 2 = ∑ i, ∑ j, ‖T i j‖ ^ 2 := by
  unfold tnorm2
  rw [Real.sq_sqrt]
  positivity

/-- The squared Hilbert–Schmidt-type norm of two columns splits over the columns. -/
theorem ce_tn_split (g : Fin 2 → ℝ × ℝ → Fin 2 → ℂ) (x : ℝ × ℝ) :
    tnorm2 (fun i j => g j x i) ^ 2 = vnorm2 (g 0 x) ^ 2 + vnorm2 (g 1 x) ^ 2 := by
  rw [ce_tnorm2_sq', ce_vnorm2_sq', ce_vnorm2_sq']
  simp only [Fin.sum_univ_two]
  ring

/-- The squared Euclidean norm of `𝒫₀ f(x)` is the sum of the squares of its real and imaginary
parts. -/
theorem ce_vnorm_P0C (c : ℝ) (f : ℝ × ℝ → Fin 2 → ℂ) (x : ℝ × ℝ) :
    vnorm2 (P0C c f x) ^ 2 = ‖P0re c f x‖ ^ 2 + ‖P0im c f x‖ ^ 2 :=
  ce_vnorm_cplx (P0re c f x) (P0im c f x)

theorem ce_uSl_cont {c : ℝ} {u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} (hu : NiceSlices c u) (s : ℝ)
    (i : Fin 2) : Continuous fun x => uSl u s x i := by
  show Continuous fun x => u (s, x) i
  exact (hu.smooth i).continuous.comp (continuous_const.prodMk continuous_id)

theorem ce_duSl_cont {c : ℝ} {u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} (hu : NiceSlices c u) (s : ℝ)
    (j i : Fin 2) : Continuous fun x => duSl u s j x i := by
  have hC : ContDiff ℝ ∞ fun y : ℝ × ℝ => u (s, y) i :=
    (hu.smooth i).comp (contDiff_const.prodMk contDiff_id)
  have hf := hC.continuous_fderiv (by simp)
  show Continuous fun x => pdC j (fun y => u (s, y) i) x
  unfold pdC
  exact hf.clm_apply continuous_const

/-- **Local energy bound** (`PartIII-a:T18/2/4/2/3`). -/
theorem lerayClassEnergy : UnforcedLeray.Short.IIIa.LerayClassEnergy := by
  unfold UnforcedLeray.Short.IIIa.LerayClassEnergy
  intro c hc u hu s₂
  obtain ⟨C, κ, hκ, hC⟩ := hu.decay s₂
  have hbint : Integrable (ce_bnd C κ) (UnforcedLeray.Cyl.cellμ c) :=
    ce_bnd_integrable c C κ hκ
  have hKeq : ∫⁻ x, ENNReal.ofReal (ce_bnd C κ x) ∂(UnforcedLeray.Cyl.cellμ c) =
      ENNReal.ofReal (∫ x, ce_bnd C κ x ∂(UnforcedLeray.Cyl.cellμ c)) :=
    (ofReal_integral_eq_lintegral_ofReal hbint
      (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm
  have hdir : ∀ j : Fin 2, ‖B0579.dir j‖ ≤ 1 := by
    intro j
    fin_cases j <;> simp [B0579.dir, Prod.norm_def]
  have hU : ∀ s, s ≤ s₂ → ∀ (x : ℝ × ℝ) (i : Fin 2),
      ‖uSl u s x i‖ ≤ C * Real.exp (-κ * x.2 ^ 2) := by
    intro s hs x i
    have h1 := hC s x i hs
    show ‖u (s, x) i‖ ≤ _
    linarith [norm_nonneg (fderiv ℝ (fun y => u (s, y) i) x)]
  have hD : ∀ j : Fin 2, ∀ s, s ≤ s₂ → ∀ (x : ℝ × ℝ) (i : Fin 2),
      ‖duSl u s j x i‖ ≤ C * Real.exp (-κ * x.2 ^ 2) := by
    intro j s hs x i
    have h1 := hC s x i hs
    have h2 : ‖pdC j (fun y => u (s, y) i) x‖ ≤ ‖fderiv ℝ (fun y => u (s, y) i) x‖ := by
      unfold pdC
      calc ‖fderiv ℝ (fun y => u (s, y) i) x (B0579.dir j)‖
          ≤ ‖fderiv ℝ (fun y => u (s, y) i) x‖ * ‖B0579.dir j‖ :=
            (fderiv ℝ (fun y => u (s, y) i) x).le_opNorm _
        _ ≤ ‖fderiv ℝ (fun y => u (s, y) i) x‖ * 1 :=
            mul_le_mul_of_nonneg_left (hdir j) (norm_nonneg _)
        _ = _ := mul_one _
    show ‖pdC j (fun y => u (s, y) i) x‖ ≤ _
    linarith [norm_nonneg (u (s, x) i)]
  refine ⟨6 * ∫ x, ce_bnd C κ x ∂(UnforcedLeray.Cyl.cellμ c), fun s _ hs2 => ?_⟩
  rw [← cellμ_eq c]
  have P1 := ce_piece_fam c C κ hκ (uSl u s) (fun i => ce_uSl_cont hu s i)
    (fun x i => hU s hs2 x i)
  have P3 := ce_piece_fam c C κ hκ (duSl u s 0) (fun i => ce_duSl_cont hu s 0 i)
    (fun x i => hD 0 s hs2 x i)
  have P5 := ce_piece_fam c C κ hκ (duSl u s 1) (fun i => ce_duSl_cont hu s 1 i)
    (fun x i => hD 1 s hs2 x i)
  have hpt : ∀ x : ℝ × ℝ,
      ENNReal.ofReal (vnorm2 (P0C c (uSl u s) x) ^ 2 +
        tnorm2 (fun i j => P0C c (duSl u s j) x i) ^ 2) =
      ENNReal.ofReal (‖P0re c (uSl u s) x‖ ^ 2) + (ENNReal.ofReal (‖P0im c (uSl u s) x‖ ^ 2) +
        (ENNReal.ofReal (‖P0re c (duSl u s 0) x‖ ^ 2) + (ENNReal.ofReal (‖P0im c (duSl u s 0) x‖ ^ 2) +
          (ENNReal.ofReal (‖P0re c (duSl u s 1) x‖ ^ 2) +
            ENNReal.ofReal (‖P0im c (duSl u s 1) x‖ ^ 2))))) := by
    intro x
    have e1 : tnorm2 (fun i j => P0C c (duSl u s j) x i) ^ 2 =
        vnorm2 (P0C c (duSl u s 0) x) ^ 2 + vnorm2 (P0C c (duSl u s 1) x) ^ 2 :=
      ce_tn_split (fun j => P0C c (duSl u s j)) x
    have e : vnorm2 (P0C c (uSl u s) x) ^ 2 +
        tnorm2 (fun i j => P0C c (duSl u s j) x i) ^ 2 =
        ‖P0re c (uSl u s) x‖ ^ 2 + (‖P0im c (uSl u s) x‖ ^ 2 +
          (‖P0re c (duSl u s 0) x‖ ^ 2 + (‖P0im c (duSl u s 0) x‖ ^ 2 +
            (‖P0re c (duSl u s 1) x‖ ^ 2 + ‖P0im c (duSl u s 1) x‖ ^ 2)))) := by
      rw [e1, ce_vnorm_P0C, ce_vnorm_P0C, ce_vnorm_P0C]
      ring
    rw [e]
    exact ce_ofReal_chain _ _ _ _ _ _ (sq_nonneg _) (sq_nonneg _) (sq_nonneg _)
      (sq_nonneg _) (sq_nonneg _) (sq_nonneg _)
  calc ∫⁻ x, ENNReal.ofReal (vnorm2 (P0C c (uSl u s) x) ^ 2 +
          tnorm2 (fun i j => P0C c (duSl u s j) x i) ^ 2) ∂(UnforcedLeray.Cyl.cellμ c)
      = ∫⁻ x, (ENNReal.ofReal (‖P0re c (uSl u s) x‖ ^ 2) + (ENNReal.ofReal (‖P0im c (uSl u s) x‖ ^ 2) +
          (ENNReal.ofReal (‖P0re c (duSl u s 0) x‖ ^ 2) + (ENNReal.ofReal (‖P0im c (duSl u s 0) x‖ ^ 2) +
            (ENNReal.ofReal (‖P0re c (duSl u s 1) x‖ ^ 2) +
              ENNReal.ofReal (‖P0im c (duSl u s 1) x‖ ^ 2)))))) ∂(UnforcedLeray.Cyl.cellμ c) :=
        lintegral_congr hpt
    _ = ∫⁻ x, ENNReal.ofReal (‖P0re c (uSl u s) x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) +
        (∫⁻ x, ENNReal.ofReal (‖P0im c (uSl u s) x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) +
          (∫⁻ x, ENNReal.ofReal (‖P0re c (duSl u s 0) x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) +
            (∫⁻ x, ENNReal.ofReal (‖P0im c (duSl u s 0) x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) +
              (∫⁻ x, ENNReal.ofReal (‖P0re c (duSl u s 1) x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c) +
                ∫⁻ x, ENNReal.ofReal (‖P0im c (duSl u s 1) x‖ ^ 2) ∂(UnforcedLeray.Cyl.cellμ c))))) :=
        ce_lint_six _ _ _ _ _ _ _ (ce_aemeas _) (ce_aemeas _) (ce_aemeas _) (ce_aemeas _)
          (ce_aemeas _)
    _ ≤ ∫⁻ x, ENNReal.ofReal (ce_bnd C κ x) ∂(UnforcedLeray.Cyl.cellμ c) +
        (∫⁻ x, ENNReal.ofReal (ce_bnd C κ x) ∂(UnforcedLeray.Cyl.cellμ c) +
          (∫⁻ x, ENNReal.ofReal (ce_bnd C κ x) ∂(UnforcedLeray.Cyl.cellμ c) +
            (∫⁻ x, ENNReal.ofReal (ce_bnd C κ x) ∂(UnforcedLeray.Cyl.cellμ c) +
              (∫⁻ x, ENNReal.ofReal (ce_bnd C κ x) ∂(UnforcedLeray.Cyl.cellμ c) +
                ∫⁻ x, ENNReal.ofReal (ce_bnd C κ x) ∂(UnforcedLeray.Cyl.cellμ c))))) :=
        add_le_add P1.1 (add_le_add P1.2 (add_le_add P3.1 (add_le_add P3.2
          (add_le_add P5.1 P5.2))))
    _ = 6 * ∫⁻ x, ENNReal.ofReal (ce_bnd C κ x) ∂(UnforcedLeray.Cyl.cellμ c) := by ring
    _ = ENNReal.ofReal (6 * ∫ x, ce_bnd C κ x ∂(UnforcedLeray.Cyl.cellμ c)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6), ENNReal.ofReal_ofNat, hKeq]

end UnforcedLeray.Short.IIIa
