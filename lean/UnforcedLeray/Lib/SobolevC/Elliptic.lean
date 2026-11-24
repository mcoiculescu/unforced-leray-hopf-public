import UnforcedLeray.Lib.SobolevC.OfMemSobolev

/-!
# Elliptic `H²` regularity on `ℝⁿ` (INF11 target S9a, `ellipticH2`)


target S9a (`ellipticH2`); decision D3 of `scoping/README.md` §3.  Manuscript uses: B0091
(tex 1463–1477: "`χ ∈ L²` … Thus `Δχ ∈ L²`, and the Fourier characterization first gives
`χ ∈ H²`"), B1009 (tex 308–312: "`H²` from `‖f‖₂ + ‖Δf‖₂` (Plancherel)"), B0122 (tex
1867–1871).

## Main declarations
* `lapl`, `IsWeakLaplacian f g`: `g = Δf` in `𝒟'(ℝⁿ)` (real `C_c^∞` tests);
* `IsWeakLaplacian.integral_eq`: the identity extends to smooth tests with integrable pairings
  (cutoffs `χ_R ψ` and dominated convergence);
* `IsWeakLaplacian.dD_sum`: for `f, g ∈ L²`, `∑ᵢ ∂ᵢ∂ᵢ f = g` in `𝓢'`;
* `IsWeakLaplacian.fourier_ae`: `-(2π)²|ξ|² 𝓕f = 𝓕g` a.e.;
* `IsWeakLaplacian.memSobolev_two`: `f ∈ H²` (Mathlib's `MemSobolev 2 2`);
* `W.second`, `ellipticH2`: `f, Δf ∈ L²(ℝⁿ)` give `x ∈ W^{2,2}(ℝⁿ)` with field `f` and
  `∑_{i,j} ‖∂ᵢ∂ⱼ x‖² = ‖Δf‖²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric SchwartzMap TemperedDistribution LineDeriv
open scoped ENNReal NNReal Topology ContDiff FourierTransform SchwartzMap Real

namespace UnforcedLeray.Sob

variable {n : ℕ}

/-! ### The weak Laplacian -/

section Lap

/-- The Laplacian of a real function, `Δφ = ∑ᵢ ∂ᵢ∂ᵢ φ`. -/
def lapl (φ : Eucl n → ℝ) (x : Eucl n) : ℝ := ∑ i, iterDirDeriv [e i, e i] φ x

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Weak Laplacian**: `g = Δf` in the sense of distributions on `ℝⁿ`, i.e.
`∫ Δφ • f = ∫ φ • g` for every real `φ ∈ C_c^∞(ℝⁿ)` (the hypothesis `Δχ ∈ L²` of tex 1463–1477,
B0091).  It is used below only for `f, g ∈ L²`, where both pairings are genuine integrals. -/
def IsWeakLaplacian (f g : Eucl n → G) : Prop :=
  ∀ φ : Eucl n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∫ x, lapl φ x • f x = ∫ x, φ x • g x

theorem fderiv_mul_apply' {a b : Eucl n → ℝ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (x v : Eucl n) :
    fderiv ℝ (fun y => a y * b y) x v = fderiv ℝ a x v * b x + a x * fderiv ℝ b x v := by
  show fderiv ℝ (a * b) x v = _
  rw [((ha x).hasFDerivAt.mul (hb x).hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul]
  ring

/-- Leibniz rule for `∂_v∂_v`. -/
theorem iterDirDeriv_two_mul {a b : Eucl n → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (v x : Eucl n) :
    iterDirDeriv [v, v] (fun y => a y * b y) x =
      iterDirDeriv [v, v] a x * b x + 2 * (fderiv ℝ a x v * fderiv ℝ b x v) +
        a x * iterDirDeriv [v, v] b x := by
  have hda : Differentiable ℝ a := ha.differentiable (by simp)
  have hdb : Differentiable ℝ b := hb.differentiable (by simp)
  have hda' : Differentiable ℝ (fun y => fderiv ℝ a y v) :=
    (contDiff_dirDeriv ha v).differentiable (by simp)
  have hdb' : Differentiable ℝ (fun y => fderiv ℝ b y v) :=
    (contDiff_dirDeriv hb v).differentiable (by simp)
  have h1 : (fun y => fderiv ℝ (fun z => a z * b z) y v) =
      (fun y => fderiv ℝ a y v * b y) + (fun y => a y * fderiv ℝ b y v) :=
    funext fun y => fderiv_mul_apply' hda hdb y v
  simp only [iterDirDeriv_cons, iterDirDeriv_nil]
  rw [h1, fderiv_add (show DifferentiableAt ℝ (fun y => fderiv ℝ a y v * b y) x from
      (hda' x).mul (hdb x)) (show DifferentiableAt ℝ (fun y => a y * fderiv ℝ b y v) x from
      (hda x).mul (hdb' x)), ContinuousLinearMap.add_apply,
    fderiv_mul_apply' hda' hdb, fderiv_mul_apply' hda hdb']
  ring

/-- Iterated derivatives of functions agreeing on an open set agree there. -/
theorem iterDirDeriv_eqOn {U : Set (Eucl n)} (hU : IsOpen U) {φ₁ φ₂ : Eucl n → ℝ}
    (h : EqOn φ₁ φ₂ U) (ws : List (Eucl n)) :
    EqOn (iterDirDeriv ws φ₁) (iterDirDeriv ws φ₂) U := by
  induction ws with
  | nil => exact h
  | cons v ws ih =>
    intro y hy
    simp only [iterDirDeriv_cons]
    have : iterDirDeriv ws φ₁ =ᶠ[𝓝 y] iterDirDeriv ws φ₂ :=
      Filter.eventually_of_mem (hU.mem_nhds hy) ih
    rw [this.fderiv_eq]

/-- Bound for `∂_v∂_v (χ_R ψ)`, `R ≥ 1`. -/
theorem abs_iterDirDeriv_cut_mul_le (v : Eucl n) :
    ∃ C, 0 ≤ C ∧ ∀ {R : ℝ}, 1 ≤ R → ∀ {ψ : Eucl n → ℝ}, ContDiff ℝ ∞ ψ → ∀ x,
      |iterDirDeriv [v, v] (fun y => GN.cut R y * ψ y) x| ≤
        C * |ψ x| + C * |fderiv ℝ ψ x v| + |iterDirDeriv [v, v] ψ x| := by
  obtain ⟨C₁, hC₁⟩ := GN.exists_bound_d1 (n := n) v
  obtain ⟨C₂, hC₂⟩ := GN.exists_bound_d2 (n := n) v
  refine ⟨max C₂ 0 + 2 * max C₁ 0, by positivity, fun {R} hR {ψ} hψ x => ?_⟩
  have hR0 : 0 < R := by linarith
  have hRi : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  have hRi0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR0.le
  rw [iterDirDeriv_two_mul (GN.contDiff_cut R) hψ]
  have h2 : |iterDirDeriv [v, v] (GN.cut (n := n) R) x| ≤ max C₂ 0 := by
    simp only [iterDirDeriv_cons, iterDirDeriv_nil]
    rw [GN.fderiv_fderiv_cut_apply, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hR0)]
    have h0' : |GN.d2 n v (R⁻¹ • x)| ≤ C₂ := by simpa [Real.norm_eq_abs] using hC₂ (R⁻¹ • x)
    have h0 : |GN.d2 n v (R⁻¹ • x)| ≤ max C₂ 0 := h0'.trans (le_max_left _ _)
    calc R⁻¹ * (R⁻¹ * |GN.d2 n v (R⁻¹ • x)|) ≤ 1 * (1 * max C₂ 0) := by
          gcongr
      _ = max C₂ 0 := by ring
  have h1 : |fderiv ℝ (GN.cut (n := n) R) x v| ≤ max C₁ 0 := by
    rw [GN.fderiv_cut_apply, abs_mul, abs_of_pos (inv_pos.mpr hR0)]
    have h0' : |GN.d1 n v (R⁻¹ • x)| ≤ C₁ := by simpa [Real.norm_eq_abs] using hC₁ (R⁻¹ • x)
    have h0 : |GN.d1 n v (R⁻¹ • x)| ≤ max C₁ 0 := h0'.trans (le_max_left _ _)
    calc R⁻¹ * |GN.d1 n v (R⁻¹ • x)| ≤ 1 * max C₁ 0 := by gcongr
      _ = max C₁ 0 := one_mul _
  have hc0 : 0 ≤ GN.cut (n := n) R x := GN.cut_nonneg _ _
  have hc1 : GN.cut (n := n) R x ≤ 1 := GN.cut_le_one _ _
  have hm1 : 0 ≤ max C₁ 0 := le_max_right _ _
  have hm2 : 0 ≤ max C₂ 0 := le_max_right _ _
  calc |iterDirDeriv [v, v] (GN.cut R) x * ψ x +
        2 * (fderiv ℝ (GN.cut R) x v * fderiv ℝ ψ x v) + GN.cut R x * iterDirDeriv [v, v] ψ x|
      ≤ |iterDirDeriv [v, v] (GN.cut R) x| * |ψ x| +
          2 * (|fderiv ℝ (GN.cut R) x v| * |fderiv ℝ ψ x v|) +
          |GN.cut R x| * |iterDirDeriv [v, v] ψ x| := by
        refine (abs_add_le _ _).trans ?_
        refine add_le_add ((abs_add_le _ _).trans ?_) (abs_mul _ _).le
        rw [abs_mul, abs_mul, abs_mul, abs_two]
    _ ≤ max C₂ 0 * |ψ x| + 2 * (max C₁ 0 * |fderiv ℝ ψ x v|) +
          1 * |iterDirDeriv [v, v] ψ x| := by
        rw [abs_of_nonneg hc0]
        gcongr
    _ ≤ (max C₂ 0 + 2 * max C₁ 0) * |ψ x| + (max C₂ 0 + 2 * max C₁ 0) * |fderiv ℝ ψ x v| +
          |iterDirDeriv [v, v] ψ x| := by
        have hp1 := abs_nonneg (ψ x)
        have hp2 := abs_nonneg (fderiv ℝ ψ x v)
        nlinarith [mul_nonneg hm1 hp1, mul_nonneg hm2 hp2]

/-- **The weak Laplacian identity for smooth tests with integrable pairings** (cutoffs
`χ_R ψ` and dominated convergence). -/
theorem IsWeakLaplacian.integral_eq {f g : Eucl n → G} (h : IsWeakLaplacian f g)
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    {ψ : Eucl n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (i0 : Integrable (fun x => ψ x • f x))
    (i1 : ∀ i, Integrable (fun x => fderiv ℝ ψ x (e i) • f x))
    (i2 : ∀ i, Integrable (fun x => iterDirDeriv [e i, e i] ψ x • f x))
    (i3 : Integrable (fun x => ψ x • g x)) :
    ∫ x, lapl ψ x • f x = ∫ x, ψ x • g x := by
  set R : ℕ → ℝ := fun k => (k : ℝ) + 1 with hR_def
  have hR1 : ∀ k, 1 ≤ R k := fun k => by
    simp only [hR_def]; have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith
  have hR : ∀ k, 0 < R k := fun k => by linarith [hR1 k]
  set ψk : ℕ → Eucl n → ℝ := fun k x => GN.cut (R k) x * ψ x with hψk_def
  have hψk_s : ∀ k, ContDiff ℝ ∞ (ψk k) := fun k => (GN.contDiff_cut _).mul hψ
  have hψk_c : ∀ k, HasCompactSupport (ψk k) := fun k =>
    (GN.hasCompactSupport_cut (hR k).ne').mul_right
  have hid : ∀ k, ∫ x, lapl (ψk k) x • f x = ∫ x, ψk k x • g x := fun k =>
    h _ (hψk_s k) (hψk_c k)
  have hev : ∀ x, ∀ᶠ k in atTop, ψk k x = ψ x ∧
      ∀ i, iterDirDeriv [e i, e i] (ψk k) x = iterDirDeriv [e i, e i] ψ x := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop N] with k hk
    have hlt : ‖x‖ < R k := by
      simp only [hR_def]
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hEq : EqOn (ψk k) ψ (ball 0 (R k)) := fun y hy => by
      simp only [hψk_def, GN.cut_eq_one (hR k) (le_of_lt (mem_ball_zero_iff.mp hy)), one_mul]
    exact ⟨hEq (mem_ball_zero_iff.mpr hlt), fun i =>
      iterDirDeriv_eqOn isOpen_ball hEq _ (mem_ball_zero_iff.mpr hlt)⟩
  -- each direction separately
  have hdir : ∀ i, (∀ k, Integrable (fun x => iterDirDeriv [e i, e i] (ψk k) x • f x)) ∧
      Tendsto (fun k => ∫ x, iterDirDeriv [e i, e i] (ψk k) x • f x) atTop
        (𝓝 (∫ x, iterDirDeriv [e i, e i] ψ x • f x)) := by
    intro i
    obtain ⟨C, hC0, hC⟩ := abs_iterDirDeriv_cut_mul_le (n := n) (e i)
    set bound : Eucl n → ℝ := fun x => C * ‖ψ x • f x‖ + C * ‖fderiv ℝ ψ x (e i) • f x‖ +
      ‖iterDirDeriv [e i, e i] ψ x • f x‖ with hbound
    have hbi : Integrable bound :=
      ((i0.norm.const_mul _).add ((i1 i).norm.const_mul _)).add (i2 i).norm
    have hle : ∀ k x, ‖iterDirDeriv [e i, e i] (ψk k) x • f x‖ ≤ bound x := by
      intro k x
      simp only [hbound, norm_smul, Real.norm_eq_abs]
      calc |iterDirDeriv [e i, e i] (ψk k) x| * ‖f x‖
          ≤ (C * |ψ x| + C * |fderiv ℝ ψ x (e i)| + |iterDirDeriv [e i, e i] ψ x|) * ‖f x‖ :=
            mul_le_mul_of_nonneg_right (hC (hR1 k) hψ x) (norm_nonneg _)
        _ = C * (|ψ x| * ‖f x‖) + C * (|fderiv ℝ ψ x (e i)| * ‖f x‖) +
              |iterDirDeriv [e i, e i] ψ x| * ‖f x‖ := by ring
    have hmeas : ∀ k, AEStronglyMeasurable (fun x => iterDirDeriv [e i, e i] (ψk k) x • f x)
        volume := fun k =>
      ((contDiff_iterDirDeriv (hψk_s k) _).continuous.aestronglyMeasurable).smul hf
    refine ⟨fun k => hbi.mono' (hmeas k) (Eventually.of_forall (hle k)), ?_⟩
    refine tendsto_integral_of_dominated_convergence bound hmeas hbi
      (fun k => Eventually.of_forall (hle k)) (Eventually.of_forall fun x => ?_)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev x] with k hk
    rw [hk.2 i]
  have hlap : ∀ φ : Eucl n → ℝ, (∀ i, Integrable (fun x => iterDirDeriv [e i, e i] φ x • f x)) →
      ∫ x, lapl φ x • f x = ∑ i, ∫ x, iterDirDeriv [e i, e i] φ x • f x := by
    intro φ hφ
    simp only [lapl, Finset.sum_smul]
    exact integral_finsetSum _ fun i _ => hφ i
  have hL : Tendsto (fun k => ∫ x, lapl (ψk k) x • f x) atTop (𝓝 (∫ x, lapl ψ x • f x)) := by
    rw [hlap ψ i2]
    refine (tendsto_finsetSum _ fun i _ => (hdir i).2).congr fun k => ?_
    rw [hlap _ fun i => (hdir i).1 k]
  have hRr : Tendsto (fun k => ∫ x, ψk k x • g x) atTop (𝓝 (∫ x, ψ x • g x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖ψ x • g x‖) (fun k => ?_)
      i3.norm (fun k => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · exact ((hψk_s k).continuous.aestronglyMeasurable).smul hg
    · simp only [hψk_def, norm_smul, Real.norm_eq_abs, abs_mul]
      have hc0 : 0 ≤ GN.cut (R k) x := GN.cut_nonneg _ _
      have hc1 : GN.cut (R k) x ≤ 1 := GN.cut_le_one _ _
      rw [abs_of_nonneg hc0]
      gcongr
      exact mul_le_of_le_one_left (abs_nonneg _) hc1
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with k hk
      rw [hk.1]
  exact tendsto_nhds_unique (hL.congr hid) hRr

end Lap

/-! ### The weak Laplacian on `𝓢'` and on the Fourier side -/

section Fourier

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem IsWeakLaplacian.const_smul {f g : Eucl n → F} (h : IsWeakLaplacian f g) (c : ℂ) :
    IsWeakLaplacian (fun x => c • f x) (fun x => c • g x) := by
  intro φ hφ hc
  simp_rw [smul_comm (_ : ℝ) c]
  rw [integral_smul, integral_smul, h φ hφ hc]

theorem memLp_two_iterDirDeriv_re (ws : List (Eucl n)) (ψ : 𝓢(Eucl n, ℂ)) :
    MemLp (iterDirDeriv ws (fun x => Complex.reCLM (ψ x))) 2 volume := by
  rw [iterDirDeriv_comp]
  exact ((dDs ws ψ).memLp 2 volume).of_le
    (Complex.reCLM.continuous.comp (dDs ws ψ).continuous).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      simp only [Complex.reCLM_apply, Real.norm_eq_abs]; exact Complex.abs_re_le_norm _)

theorem memLp_two_iterDirDeriv_im (ws : List (Eucl n)) (ψ : 𝓢(Eucl n, ℂ)) :
    MemLp (iterDirDeriv ws (fun x => Complex.imCLM (ψ x))) 2 volume := by
  rw [iterDirDeriv_comp]
  exact ((dDs ws ψ).memLp 2 volume).of_le
    (Complex.imCLM.continuous.comp (dDs ws ψ).continuous).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      simp only [Complex.imCLM_apply, Real.norm_eq_abs]; exact Complex.abs_im_le_norm _)

omit [CompleteSpace F] in
/-- The Laplacian identity against a real smooth test whose derivatives are Schwartz parts. -/
theorem IsWeakLaplacian.integral_eq_of_memLp {f g : Lp F 2 (volume : Measure (Eucl n))}
    (h : IsWeakLaplacian (f : Eucl n → F) (g : Eucl n → F)) {ψ : Eucl n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hm : ∀ ws : List (Eucl n), MemLp (iterDirDeriv ws ψ) 2 volume) :
    ∫ x, lapl ψ x • (f : Eucl n → F) x = ∫ x, ψ x • (g : Eucl n → F) x := by
  refine h.integral_eq (Lp.aestronglyMeasurable f) (Lp.aestronglyMeasurable g) hψ
    (integrable_smul_of_memLp_two (hm []) (Lp.memLp f))
    (fun i => integrable_smul_of_memLp_two (hm [e i]) (Lp.memLp f))
    (fun i => integrable_smul_of_memLp_two (hm [e i, e i]) (Lp.memLp f))
    (integrable_smul_of_memLp_two (hm []) (Lp.memLp g))

/-- **The weak Laplacian on `𝓢'`**: for `f, g ∈ L²` with `g = Δf` weakly,
`∑ᵢ ∂ᵢ∂ᵢ f = g` in `𝓢'(ℝⁿ, F)`. -/
theorem IsWeakLaplacian.dD_sum {f g : Lp F 2 (volume : Measure (Eucl n))}
    (h : IsWeakLaplacian (f : Eucl n → F) (g : Eucl n → F)) :
    ∑ i, dD [e i, e i] (f : 𝓢'(Eucl n, F)) = (g : 𝓢'(Eucl n, F)) := by
  ext ψ
  set gr : Eucl n → ℝ := fun x => Complex.reCLM (ψ x) with hgr
  set gi : Eucl n → ℝ := fun x => Complex.imCLM (ψ x) with hgi
  have hgr_s : ContDiff ℝ ∞ gr := Complex.reCLM.contDiff.comp (ψ.smooth ⊤)
  have hgi_s : ContDiff ℝ ∞ gi := Complex.imCLM.contDiff.comp (ψ.smooth ⊤)
  have hu2 : MemLp (f : Eucl n → F) 2 volume := Lp.memLp f
  have hg2 : MemLp (g : Eucl n → F) 2 volume := Lp.memLp g
  have hIf : MemLp (fun x => Complex.I • (f : Eucl n → F) x) 2 volume := hu2.const_smul _
  have hIg : MemLp (fun x => Complex.I • (g : Eucl n → F) x) 2 volume := hg2.const_smul _
  have hI := h.const_smul Complex.I
  have e1 : ∫ x, lapl gr x • (f : Eucl n → F) x = ∫ x, gr x • (g : Eucl n → F) x :=
    h.integral_eq_of_memLp hgr_s fun ws => memLp_two_iterDirDeriv_re ws ψ
  have e2 : ∫ x, lapl gi x • (Complex.I • (f : Eucl n → F) x) =
      ∫ x, gi x • (Complex.I • (g : Eucl n → F) x) :=
    hI.integral_eq hIf.1 hIg.1 hgi_s
      (integrable_smul_of_memLp_two (memLp_two_iterDirDeriv_im [] ψ) hIf)
      (fun i => integrable_smul_of_memLp_two (memLp_two_iterDirDeriv_im [e i] ψ) hIf)
      (fun i => integrable_smul_of_memLp_two (memLp_two_iterDirDeriv_im [e i, e i] ψ) hIf)
      (integrable_smul_of_memLp_two (memLp_two_iterDirDeriv_im [] ψ) hIg)
  -- left side
  have hdre : ∀ i x, (dDs [e i, e i] ψ x).re = iterDirDeriv [e i, e i] gr x := fun i x =>
    (congrFun (iterDirDeriv_comp Complex.reCLM [e i, e i] ψ) x).symm
  have hdim : ∀ i x, (dDs [e i, e i] ψ x).im = iterDirDeriv [e i, e i] gi x := fun i x =>
    (congrFun (iterDirDeriv_comp Complex.imCLM [e i, e i] ψ) x).symm
  have hsplitL : ∀ x, (∑ i, dDs [e i, e i] ψ x) • (f : Eucl n → F) x =
      lapl gr x • (f : Eucl n → F) x + lapl gi x • (Complex.I • (f : Eucl n → F) x) := by
    intro x
    rw [complex_smul_eq, Complex.re_sum, Complex.im_sum]
    simp only [hdre, hdim, lapl]
  have hsplitR : ∀ x, ψ x • (g : Eucl n → F) x =
      gr x • (g : Eucl n → F) x + gi x • (Complex.I • (g : Eucl n → F) x) := by
    intro x
    rw [complex_smul_eq]
    rfl
  have hiL : ∀ i, Integrable (fun x => dDs [e i, e i] ψ x • (f : Eucl n → F) x) volume := by
    intro i
    have := hu2.smul (r := 1) ((dDs [e i, e i] ψ).memLp 2 volume)
    exact memLp_one_iff_integrable.mp this
  calc (∑ i, dD [e i, e i] (f : 𝓢'(Eucl n, F))) ψ
      = ∑ i, ∫ x, dDs [e i, e i] ψ x • (f : Eucl n → F) x := by
        rw [show (∑ i, dD [e i, e i] (f : 𝓢'(Eucl n, F))) ψ =
          ∑ i, dD [e i, e i] (f : 𝓢'(Eucl n, F)) ψ by simp]
        simp only [dD_apply, Lp.toTemperedDistribution_apply, List.length_cons, List.length_nil]
        norm_num
    _ = ∫ x, (∑ i, dDs [e i, e i] ψ x) • (f : Eucl n → F) x := by
        rw [← integral_finsetSum _ fun i _ => hiL i]
        simp only [Finset.sum_smul]
    _ = (∫ x, lapl gr x • (f : Eucl n → F) x) +
          ∫ x, lapl gi x • (Complex.I • (f : Eucl n → F) x) := by
        simp_rw [hsplitL]
        have hlr : MemLp (lapl gr) 2 volume :=
          memLp_finsetSum Finset.univ fun i _ => memLp_two_iterDirDeriv_re [e i, e i] ψ
        have hli : MemLp (lapl gi) 2 volume :=
          memLp_finsetSum Finset.univ fun i _ => memLp_two_iterDirDeriv_im [e i, e i] ψ
        exact integral_add (integrable_smul_of_memLp_two hlr hu2)
          (integrable_smul_of_memLp_two hli hIf)
    _ = ∫ x, ψ x • (g : Eucl n → F) x := by
        have hmr : MemLp gr 2 volume := memLp_two_iterDirDeriv_re [] ψ
        have hmi : MemLp gi 2 volume := memLp_two_iterDirDeriv_im [] ψ
        rw [e1, e2, ← integral_add (integrable_smul_of_memLp_two hmr hg2)
          (integrable_smul_of_memLp_two hmi hIg)]
        simp_rw [hsplitR]
    _ = (g : 𝓢'(Eucl n, F)) ψ := by rw [Lp.toTemperedDistribution_apply]

theorem polyW_pair (i j : Fin n) (ξ : Eucl n) : polyW [e i, e j] ξ = ((ξ i * ξ j : ℝ) : ℂ) := by
  simp [polyW, e, EuclideanSpace.inner_single_right]

/-- The symbol of `Δ`: `-(2π)²|ξ|²`. -/
def lapSym (ξ : Eucl n) : ℂ := ((-(2 * π) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)

theorem lapSym_eq_sum :
    (lapSym : Eucl n → ℂ) = fun ξ => ∑ i, ((2 * π * Complex.I) ^ 2 • polyW [e i, e i]) ξ := by
  funext ξ
  have hI : (2 * (π : ℂ) * Complex.I) ^ 2 = ((-(2 * π) ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq]; push_cast; ring
  have hn : ‖ξ‖ ^ 2 = ∑ i, ξ i * ξ i := by
    rw [EuclideanSpace.norm_sq_eq]; simp [Real.norm_eq_abs, sq]
  simp only [Pi.smul_apply, smul_eq_mul, polyW_pair, lapSym]
  rw [← Finset.mul_sum, hI, hn, ← Complex.ofReal_sum, ← Complex.ofReal_mul]

/-- **The Fourier side of `Δf = g`**: `-(2π)²|ξ|² 𝓕f(ξ) = 𝓕g(ξ)` for a.e. `ξ`. -/
theorem IsWeakLaplacian.fourier_ae {f g : Lp F 2 (volume : Measure (Eucl n))}
    (h : IsWeakLaplacian (f : Eucl n → F) (g : Eucl n → F)) :
    (fun ξ => lapSym ξ • ((𝓕 f : Lp F 2 (volume : Measure (Eucl n))) : Eucl n → F) ξ)
      =ᵐ[volume] ((𝓕 g : Lp F 2 (volume : Measure (Eucl n))) : Eucl n → F) := by
  have hpt : ∀ i : Fin n, (polyW [e i, e i]).HasTemperateGrowth := fun i => polyW_temperate _
  have hs : (lapSym : Eucl n → ℂ).HasTemperateGrowth := by
    unfold lapSym; fun_prop
  apply ae_eq_of_smulLeftCLM_eq hs
  rw [← Lp.fourier_toTemperedDistribution_eq, ← Lp.fourier_toTemperedDistribution_eq, ← h.dD_sum,
    FourierTransform.fourier_sum]
  simp_rw [fourier_dD]
  have hti : ∀ i : Fin n, ((2 * π * Complex.I) ^ 2 • polyW [e i, e i]).HasTemperateGrowth := by
    intro i
    have : ((2 * π * Complex.I) ^ 2 • polyW [e i, e i]) =
        (fun _ => (2 * π * Complex.I) ^ 2) * polyW [e i, e i] := by
      funext ξ; simp [smul_eq_mul]
    rw [this]
    exact (Function.HasTemperateGrowth.const _).mul (hpt i)
  rw [lapSym_eq_sum, TemperedDistribution.smulLeftCLM_sum (fun i _ => hti i),
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TemperedDistribution.smulLeftCLM_smul (hpt i), ContinuousLinearMap.smul_apply]
  simp

/-- **`f, Δf ∈ L²` gives `f ∈ H²`** ("the Fourier characterization first gives `χ ∈ H²`",
tex 1463–1477, B0091): `(1 + |ξ|²) 𝓕f = 𝓕f - (2π)⁻² 𝓕g ∈ L²`. -/
theorem IsWeakLaplacian.memSobolev_two {f g : Lp F 2 (volume : Measure (Eucl n))}
    (h : IsWeakLaplacian (f : Eucl n → F) (g : Eucl n → F)) :
    MemSobolev ((2 : ℕ) : ℝ) 2 (f : 𝓢'(Eucl n, F)) := by
  rw [memSobolev_iff_exists_smulLeftCLM_fourier]
  set c : ℝ := ((2 * π) ^ 2)⁻¹ with hc
  refine ⟨𝓕 f - (c : ℂ) • 𝓕 g, ?_⟩
  have hgT : (fun ξ : Eucl n => (((1 + ‖ξ‖ ^ 2) ^ (((2 : ℕ) : ℝ) / 2) : ℝ) : ℂ)).HasTemperateGrowth := by
    fun_prop
  rw [Lp.fourier_toTemperedDistribution_eq]
  ext φ
  rw [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [h.fourier_ae, Lp.coeFn_sub (𝓕 f) ((c : ℂ) • 𝓕 g), Lp.coeFn_smul (c : ℂ) (𝓕 g)]
    with ξ h1 h2 h3
  rw [SchwartzMap.smulLeftCLM_apply_apply hgT, h2, Pi.sub_apply, h3, Pi.smul_apply, ← h1]
  have hm : (((1 + ‖ξ‖ ^ 2) ^ (((2 : ℕ) : ℝ) / 2) : ℝ) : ℂ) = 1 - (c : ℂ) * lapSym ξ := by
    have hr : ((1 + ‖ξ‖ ^ 2) ^ (((2 : ℕ) : ℝ) / 2) : ℝ) = 1 - c * (-(2 * π) ^ 2 * ‖ξ‖ ^ 2) := by
      rw [show (((2 : ℕ) : ℝ) / 2) = 1 by norm_num, Real.rpow_one, hc]
      have : (2 * π) ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    rw [hr, lapSym]
    push_cast
    ring
  rw [smul_eq_mul, hm, smul_smul (c : ℂ), mul_comm _ (φ ξ), mul_smul, sub_smul, one_smul]

/-! ### `ellipticH2` -/

/-- The index `(i, j)` of `∂ᵢ∂ⱼ` in `Idx n 2`. -/
def idx2 (i j : Fin n) : Idx n 2 := Idx.cons i (Idx.cons j Idx.zero)

theorem word_idx2 (i j : Fin n) : (wholeSpace n).word (idx2 i j) = [e i, e j] := by
  simp [idx2, TestDomain.word_cons, wholeSpace_dir]

@[simp] theorem idx2_fst (i j : Fin n) : (idx2 i j).1.val = 2 := rfl

end Fourier

section Second

variable {ρ : Weight (Eucl n)} {𝕜 : Type*} [RCLike 𝕜] {G : Type*} [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 G] [NormedSpace ℝ G] [IsScalarTower ℝ 𝕜 G] [FiniteDimensional 𝕜 G]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The second derivative `∂ᵢ∂ⱼ x ∈ L^p(ρ)` of `x ∈ W^{2,p}(ℝⁿ)`. -/
def W.second (x : W (wholeSpace n) ρ 𝕜 G 2 p) (i j : Fin n) :
    Lp G p (wμ (wholeSpace n).μ ρ) :=
  W.deriv (wholeSpace n) ρ 𝕜 G 2 p (idx2 i j) x

end Second

section Elliptic

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [FiniteDimensional ℂ F]

/-- **Elliptic `H²` regularity on `ℝⁿ`** (S9a `ellipticH2`; tex 1463–1477 B0091, tex 308–312
B1009 "`H²` from `‖f‖₂ + ‖Δf‖₂` (Plancherel)"): if `f, g ∈ L²(ℝⁿ; F)` and `g = Δf` in
`𝒟'(ℝⁿ)`, then `f` is the field of some `x ∈ W^{2,2}(ℝⁿ; F)`, and
`∑_{i,j} ‖∂ᵢ∂ⱼ x‖²_{L²} = ‖Δf‖²_{L²}`. -/
theorem ellipticH2 {f g : Lp F 2 (volume : Measure (Eucl n))}
    (h : IsWeakLaplacian (f : Eucl n → F) (g : Eucl n → F)) :
    ∃ x : W (wholeSpace n) 1 ℂ F 2 2, toVol (W.value (wholeSpace n) 1 ℂ F 2 2 x) = f ∧
      ∑ i, ∑ j, ‖W.second x i j‖ ^ 2 = ‖g‖ ^ 2 := by
  obtain ⟨x, hx⟩ := W.ofMemSobolev h.memSobolev_two
  refine ⟨x, hx, ?_⟩
  have hFv : W.fourierValue x = 𝓕 f := by rw [W.fourierValue, hx]
  have hI : (2 * (π : ℂ) * Complex.I) ^ 2 = ((-(2 * π) ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq]; push_cast; ring
  have hpt : ∀ i j, ∀ᵐ ξ ∂volume,
      (((-(2 * π) ^ 2 * (ξ i * ξ j)) : ℝ) : ℂ) • ((𝓕 f : Lp F 2 volume) : Eucl n → F) ξ =
        (W.fourierDeriv x (idx2 i j) : Eucl n → F) ξ := by
    intro i j
    have := W.fourierDeriv_ae x (idx2 i j)
    rw [word_idx2, idx2_fst, hFv] at this
    filter_upwards [this] with ξ hξ
    rw [← hξ, Pi.smul_apply, smul_eq_mul, polyW_pair, hI, ← Complex.ofReal_mul]
  have hnorm : ∀ i j, ‖W.second x i j‖ = ‖W.fourierDeriv x (idx2 i j)‖ := by
    intro i j
    rw [W.fourierDeriv, Lp.norm_fourier_eq, norm_toVol]
    rfl
  have hall : ∀ᵐ ξ ∂volume, (∀ i j,
      (((-(2 * π) ^ 2 * (ξ i * ξ j)) : ℝ) : ℂ) • ((𝓕 f : Lp F 2 volume) : Eucl n → F) ξ =
        (W.fourierDeriv x (idx2 i j) : Eucl n → F) ξ) ∧
      lapSym ξ • ((𝓕 f : Lp F 2 volume) : Eucl n → F) ξ = ((𝓕 g : Lp F 2 volume) : Eucl n → F) ξ := by
    have h1 : ∀ᵐ ξ ∂volume, ∀ i j,
        (((-(2 * π) ^ 2 * (ξ i * ξ j)) : ℝ) : ℂ) • ((𝓕 f : Lp F 2 volume) : Eucl n → F) ξ =
          (W.fourierDeriv x (idx2 i j) : Eucl n → F) ξ :=
      eventually_all.mpr fun i => eventually_all.mpr fun j => hpt i j
    filter_upwards [h1, h.fourier_ae] with ξ hξ1 hξ2 using ⟨hξ1, hξ2⟩
  have key : ∀ᵐ ξ ∂volume, ∑ i, ∑ j, ‖(W.fourierDeriv x (idx2 i j) : Eucl n → F) ξ‖ ^ 2 =
      ‖((𝓕 g : Lp F 2 volume) : Eucl n → F) ξ‖ ^ 2 := by
    filter_upwards [hall] with ξ ⟨h1, h2⟩
    set v := ((𝓕 f : Lp F 2 volume) : Eucl n → F) ξ
    have hn : ‖ξ‖ ^ 2 = ∑ i, ξ i ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]; simp [Real.norm_eq_abs]
    have e1 : ∀ i j, ‖(W.fourierDeriv x (idx2 i j) : Eucl n → F) ξ‖ ^ 2 =
        ((2 * π) ^ 4 * ‖v‖ ^ 2) * (ξ i ^ 2 * ξ j ^ 2) := by
      intro i j
      rw [← h1 i j, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    have e2 : ‖((𝓕 g : Lp F 2 volume) : Eucl n → F) ξ‖ ^ 2 =
        ((2 * π) ^ 4 * ‖v‖ ^ 2) * (‖ξ‖ ^ 2 * ‖ξ‖ ^ 2) := by
      rw [← h2, lapSym, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    simp_rw [e1, ← Finset.mul_sum]
    rw [e2, hn, Finset.sum_mul]
  have hofReal : ∀ w : F, ‖w‖ₑ ^ 2 = ENNReal.ofReal (‖w‖ ^ 2) := fun w => by
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hmeas : ∀ i j, AEMeasurable
      (fun ξ => ‖(W.fourierDeriv x (idx2 i j) : Eucl n → F) ξ‖ₑ ^ 2) volume := fun i j =>
    (Lp.aestronglyMeasurable _).enorm.pow_const 2
  have hL : ENNReal.ofReal (∑ i, ∑ j, ‖W.second x i j‖ ^ 2) = ENNReal.ofReal (‖g‖ ^ 2) := by
    calc ENNReal.ofReal (∑ i, ∑ j, ‖W.second x i j‖ ^ 2)
        = ∑ i, ∑ j, ∫⁻ ξ, ‖(W.fourierDeriv x (idx2 i j) : Eucl n → F) ξ‖ₑ ^ 2 := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [eLpNorm_two_sq_Lp, hnorm]
      _ = ∫⁻ ξ, ∑ i, ∑ j, ‖(W.fourierDeriv x (idx2 i j) : Eucl n → F) ξ‖ₑ ^ 2 := by
          rw [lintegral_finsetSum' (f := fun i ξ =>
            ∑ j, ‖(W.fourierDeriv x (idx2 i j) : Eucl n → F) ξ‖ₑ ^ 2) Finset.univ
            fun i _ => Finset.aemeasurable_fun_sum _ fun j _ => hmeas i j]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [lintegral_finsetSum' _ fun j _ => hmeas i j]
      _ = ∫⁻ ξ, ‖((𝓕 g : Lp F 2 volume) : Eucl n → F) ξ‖ₑ ^ 2 := by
          refine lintegral_congr_ae ?_
          filter_upwards [key] with ξ hξ
          simp_rw [hofReal]
          rw [← hξ, ENNReal.ofReal_sum_of_nonneg
            (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
      _ = ENNReal.ofReal (‖g‖ ^ 2) := by rw [eLpNorm_two_sq_Lp, Lp.norm_fourier_eq]
  exact (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).mp hL

end Elliptic

end UnforcedLeray.Sob
