import UnforcedLeray.Lib.SobolevC.GNDensity
import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.Analysis.Fourier.LpSpace

/-!
# The `p = 2` Fourier bridge (INF11 target S9a, first half)


target S9a; decision D3 of `scoping/README.md` §3 (Mathlib `MemSobolev` is used only as the
`p = 2` Fourier bridge).  Manuscript uses: B0091 (tex 1463–1477, "Fourier characterization",
`χ, Δχ ∈ L² ⇒ χ ∈ H²`), B1009 (tex 308–312, "`H²` from `‖f‖₂ + ‖Δf‖₂` (Plancherel)"), B0122
(tex 1867–1871), B0059 (tex 1206–1213), B0711 (tex 279–290).

## Main declarations
* `HasWeakDeriv.integral_fderiv_smul_eq`: the weak-derivative identity extends from `C_c^∞` to
  smooth tests `ψ` with integrable pairings (cutoff + dominated convergence);
* `lineDerivOp_toTemperedDistribution`: for `u, u' ∈ L²(ℝⁿ; F)` with `u' = ∂_v u` weakly,
  `∂_v u = u'` in `𝓢'(ℝⁿ, F)`;
* `W.toVol`, `W.dD_value`: every component `∂^α x` of `x ∈ W^{k,2}(ℝⁿ)` is the
  distributional derivative `∂^α` of `x`;
* `fourier_dD`: `𝓕 (∂^α T) = (2πi)^{|α|} ξ^α 𝓕 T` on `𝓢'`;
* `W.memSobolev`: `x ∈ W^{k,2}(ℝⁿ; F)` (complex `F`) is in Mathlib's `H^k`
  (`MemSobolev k 2`), with the quantitative bound
  `‖(1 + |ξ|²)^{k/2} 𝓕x‖₂ ≤ 2^{k/2} ‖x‖_{H^k}` (`W.bessel_bound`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric SchwartzMap TemperedDistribution LineDeriv
open scoped ENNReal NNReal Topology ContDiff FourierTransform SchwartzMap

namespace UnforcedLeray.Sob

variable {n : ℕ}

/-! ### Schwartz tests in the weak-derivative identity -/

section Extend

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- **The weak-derivative identity for smooth tests with integrable pairings**:
if `u' = ∂_v u` weakly (tests `C_c^∞`) and `ψ` is smooth with `ψ u`, `∂_v ψ u`, `ψ u'`
integrable, then `∫ ∂_v ψ • u = -∫ ψ • u'`.  Proof: `ψ_R = χ_R ψ` and dominated convergence. -/
theorem HasWeakDeriv.integral_fderiv_smul_eq {v : Eucl n} {u u' : Eucl n → G}
    (h : HasWeakDeriv (wholeSpace n) [v] u u') (hu : AEStronglyMeasurable u volume)
    (hu' : AEStronglyMeasurable u' volume) {ψ : Eucl n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (i1 : Integrable (fun x => ψ x • u x)) (i2 : Integrable (fun x => fderiv ℝ ψ x v • u x))
    (i3 : Integrable (fun x => ψ x • u' x)) :
    ∫ x, fderiv ℝ ψ x v • u x = -∫ x, ψ x • u' x := by
  obtain ⟨C₁, hC₁⟩ := GN.exists_bound_d1 v
  set R : ℕ → ℝ := fun k => (k : ℝ) + 1 with hR_def
  have hR : ∀ k, 0 < R k := fun k => by positivity
  have hR1 : ∀ k, (R k)⁻¹ ≤ 1 := fun k =>
    inv_le_one_of_one_le₀ (by simp only [hR_def]; have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
  set ψk : ℕ → Eucl n → ℝ := fun k x => GN.cut (R k) x * ψ x with hψk_def
  have hψk : ∀ k, (wholeSpace n).Adm (ψk k) := fun k =>
    ⟨(GN.contDiff_cut _).mul hψ, (GN.hasCompactSupport_cut (hR k).ne').mul_right⟩
  have hd : ∀ k x, fderiv ℝ (ψk k) x v =
      fderiv ℝ (GN.cut (R k)) x v * ψ x + GN.cut (R k) x * fderiv ℝ ψ x v := by
    intro k x
    have h1 : DifferentiableAt ℝ (GN.cut (n := n) (R k)) x :=
      ((GN.contDiff_cut _).differentiable (by simp)) x
    have h2 : DifferentiableAt ℝ ψ x := (hψ.differentiable (by simp)) x
    have hm : fderiv ℝ (fun y => GN.cut (R k) y * ψ y) x =
        GN.cut (R k) x • fderiv ℝ ψ x + ψ x • fderiv ℝ (GN.cut (R k)) x := fderiv_mul h1 h2
    rw [show ψk k = fun y => GN.cut (R k) y * ψ y from rfl, hm]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      smul_eq_mul]
    ring
  have hid : ∀ k, ∫ x, fderiv ℝ (ψk k) x v • u x = -∫ x, ψk k x • u' x := by
    intro k
    have := h.identity _ (hψk k)
    simpa only [iterDirDeriv_singleton, wholeSpace_μ, List.length_singleton, pow_one, neg_smul,
      one_smul] using this
  -- eventually `ψ_k = ψ` near each point
  have hev : ∀ x, ∀ᶠ k in atTop, ψk k x = ψ x ∧ fderiv ℝ (ψk k) x v = fderiv ℝ ψ x v := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop N] with k hk
    have hlt : ‖x‖ < R k := by
      simp only [hR_def]
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    refine ⟨?_, ?_⟩
    · simp only [hψk_def, GN.cut_eq_one (hR k) hlt.le, one_mul]
    · rw [hd, GN.fderiv_cut_eq_zero (hR k) hlt, GN.cut_eq_one (hR k) hlt.le]
      simp
  have hL : Tendsto (fun k => ∫ x, fderiv ℝ (ψk k) x v • u x) atTop
      (𝓝 (∫ x, fderiv ℝ ψ x v • u x)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => max C₁ 0 * ‖ψ x • u x‖ + ‖fderiv ℝ ψ x v • u x‖) (fun k => ?_)
      ((i1.norm.const_mul _).add i2.norm) (fun k => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · exact ((contDiff_dirDeriv (hψk k).1 v).continuous.aestronglyMeasurable).smul hu
    · rw [hd, norm_smul, Real.norm_eq_abs]
      have ha : |fderiv ℝ (GN.cut (R k)) x v| ≤ max C₁ 0 := by
        rw [GN.fderiv_cut_apply, abs_mul, abs_of_pos (inv_pos.mpr (hR k))]
        have h0 : |GN.d1 n v ((R k)⁻¹ • x)| ≤ C₁ := by
          simpa [Real.norm_eq_abs] using hC₁ ((R k)⁻¹ • x)
        have h1 : |GN.d1 n v ((R k)⁻¹ • x)| ≤ max C₁ 0 := h0.trans (le_max_left _ _)
        calc (R k)⁻¹ * |GN.d1 n v ((R k)⁻¹ • x)| ≤ 1 * max C₁ 0 :=
              mul_le_mul (hR1 k) h1 (abs_nonneg _) zero_le_one
          _ = max C₁ 0 := one_mul _
      have hc0 : 0 ≤ GN.cut (R k) x := GN.cut_nonneg _ _
      have hc1 : GN.cut (R k) x ≤ 1 := GN.cut_le_one _ _
      have hsum : |fderiv ℝ (GN.cut (R k)) x v * ψ x + GN.cut (R k) x * fderiv ℝ ψ x v| ≤
          max C₁ 0 * |ψ x| + |fderiv ℝ ψ x v| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hc0]
        gcongr
        exact mul_le_of_le_one_left (abs_nonneg _) hc1
      calc |fderiv ℝ (GN.cut (R k)) x v * ψ x + GN.cut (R k) x * fderiv ℝ ψ x v| * ‖u x‖
          ≤ (max C₁ 0 * |ψ x| + |fderiv ℝ ψ x v|) * ‖u x‖ :=
            mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
        _ = max C₁ 0 * ‖ψ x • u x‖ + ‖fderiv ℝ ψ x v • u x‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]; ring
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with k hk
      rw [hk.2]
  have hRr : Tendsto (fun k => ∫ x, ψk k x • u' x) atTop (𝓝 (∫ x, ψ x • u' x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖ψ x • u' x‖) (fun k => ?_)
      i3.norm (fun k => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · exact ((hψk k).1.continuous.aestronglyMeasurable).smul hu'
    · simp only [hψk_def, norm_smul, Real.norm_eq_abs, abs_mul]
      have hc0 : 0 ≤ GN.cut (R k) x := GN.cut_nonneg _ _
      have hc1 : GN.cut (R k) x ≤ 1 := GN.cut_le_one _ _
      rw [abs_of_nonneg hc0]
      gcongr
      exact mul_le_of_le_one_left (abs_nonneg _) hc1
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with k hk
      rw [hk.1]
  exact tendsto_nhds_unique (Tendsto.congr hid hL) hRr.neg

end Extend

/-! ### Weak derivatives of `L²` functions are distributional derivatives -/

section Distr

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem complex_smul_eq (z : ℂ) (w : F) : z • w = z.re • w + z.im • (Complex.I • w) := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

theorem integrable_smul_of_memLp_two {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {ψ : Eucl n → ℝ} {w : Eucl n → G} (hψ : MemLp ψ 2 volume) (hw : MemLp w 2 volume) :
    Integrable (fun x => ψ x • w x) volume := by
  have := hw.smul (r := 1) hψ
  exact memLp_one_iff_integrable.mp this

/-- **Distributional derivative of an `L²` function** (S9a): if `u' = ∂_v u` weakly with
`C_c^∞` tests, then `∂_v u = u'` in `𝓢'(ℝⁿ, F)`. -/
theorem lineDerivOp_toTemperedDistribution {v : Eucl n}
    {u u' : Lp F 2 (volume : Measure (Eucl n))}
    (h : HasWeakDeriv (wholeSpace n) [v] (u : Eucl n → F) (u' : Eucl n → F)) :
    ∂_{v} (u : 𝓢'(Eucl n, F)) = (u' : 𝓢'(Eucl n, F)) := by
  ext g
  rw [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  set gr : Eucl n → ℝ := fun x => (g x).re with hgr
  set gi : Eucl n → ℝ := fun x => (g x).im with hgi
  have hgs : ContDiff ℝ ∞ g := g.smooth ⊤
  have hgr_s : ContDiff ℝ ∞ gr := Complex.reCLM.contDiff.comp hgs
  have hgi_s : ContDiff ℝ ∞ gi := Complex.imCLM.contDiff.comp hgs
  have hdgr : ∀ x, fderiv ℝ gr x v = (fderiv ℝ g x v).re := by
    intro x
    have : HasFDerivAt gr (Complex.reCLM.comp (fderiv ℝ g x)) x :=
      Complex.reCLM.hasFDerivAt.comp x g.differentiableAt.hasFDerivAt
    rw [this.fderiv]; rfl
  have hdgi : ∀ x, fderiv ℝ gi x v = (fderiv ℝ g x v).im := by
    intro x
    have : HasFDerivAt gi (Complex.imCLM.comp (fderiv ℝ g x)) x :=
      Complex.imCLM.hasFDerivAt.comp x g.differentiableAt.hasFDerivAt
    rw [this.fderiv]; rfl
  -- `L²` memberships
  have hgL : MemLp (g : Eucl n → ℂ) 2 volume := g.memLp 2
  have hdgL : MemLp (fun x => fderiv ℝ g x v) 2 volume := by
    have h0 := (∂_{v} g : 𝓢(Eucl n, ℂ)).memLp 2 (volume : Measure (Eucl n))
    have : ((∂_{v} g : 𝓢(Eucl n, ℂ)) : Eucl n → ℂ) = fun x => fderiv ℝ g x v :=
      funext fun x => SchwartzMap.lineDerivOp_apply_eq_fderiv v g x
    rwa [this] at h0
  have mr : MemLp gr 2 volume := hgL.of_le hgr_s.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      simp only [hgr, Real.norm_eq_abs]; exact Complex.abs_re_le_norm _)
  have mi : MemLp gi 2 volume := hgL.of_le hgi_s.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      simp only [hgi, Real.norm_eq_abs]; exact Complex.abs_im_le_norm _)
  have mdr : MemLp (fun x => fderiv ℝ gr x v) 2 volume := hdgL.of_le
    ((hgr_s.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [hdgr, Real.norm_eq_abs]; exact Complex.abs_re_le_norm _)
  have mdi : MemLp (fun x => fderiv ℝ gi x v) 2 volume := hdgL.of_le
    ((hgi_s.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [hdgi, Real.norm_eq_abs]; exact Complex.abs_im_le_norm _)
  have hu2 : MemLp (u : Eucl n → F) 2 volume := Lp.memLp u
  have hu2' : MemLp (u' : Eucl n → F) 2 volume := Lp.memLp u'
  have hIu : MemLp (fun x => Complex.I • (u : Eucl n → F) x) 2 volume := hu2.const_smul _
  have hIu' : MemLp (fun x => Complex.I • (u' : Eucl n → F) x) 2 volume := hu2'.const_smul _
  have hI : HasWeakDeriv (wholeSpace n) [v] (Complex.I • (u : Eucl n → F))
      (Complex.I • (u' : Eucl n → F)) := h.smul Complex.I
  have e1 := h.integral_fderiv_smul_eq hu2.1 hu2'.1 hgr_s (integrable_smul_of_memLp_two mr hu2)
    (integrable_smul_of_memLp_two mdr hu2) (integrable_smul_of_memLp_two mr hu2')
  have e2 := hI.integral_fderiv_smul_eq hIu.1 hIu'.1 hgi_s (integrable_smul_of_memLp_two mi hIu)
    (integrable_smul_of_memLp_two mdi hIu) (integrable_smul_of_memLp_two mi hIu')
  simp only [Pi.smul_apply] at e2
  have hsplitL : ∀ x, (-∂_{v} g) x • (u : Eucl n → F) x =
      -(fderiv ℝ gr x v • (u : Eucl n → F) x +
        fderiv ℝ gi x v • (Complex.I • (u : Eucl n → F) x)) := by
    intro x
    rw [SchwartzMap.neg_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, neg_smul,
      complex_smul_eq, hdgr, hdgi]
  have hsplitR : ∀ x, g x • (u' : Eucl n → F) x =
      gr x • (u' : Eucl n → F) x + gi x • (Complex.I • (u' : Eucl n → F) x) := by
    intro x
    rw [complex_smul_eq]
  simp_rw [hsplitL, hsplitR]
  rw [integral_neg, integral_add (integrable_smul_of_memLp_two mdr hu2)
    (integrable_smul_of_memLp_two mdi hIu), integral_add (integrable_smul_of_memLp_two mr hu2')
    (integrable_smul_of_memLp_two mi hIu'), e1, e2]
  abel

end Distr

/-! ### Iterated distributional derivatives and the Fourier transform -/

section Words

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- `∂_{w₁} ⋯ ∂_{w_m} T` on `𝓢'` (same convention as `iterDirDeriv`). -/
def dD (ws : List (Eucl n)) (T : 𝓢'(Eucl n, F)) : 𝓢'(Eucl n, F) :=
  ws.foldr (fun m S => ∂_{m} S) T

@[simp] theorem dD_nil (T : 𝓢'(Eucl n, F)) : dD [] T = T := rfl

@[simp] theorem dD_cons (m : Eucl n) (ws : List (Eucl n)) (T : 𝓢'(Eucl n, F)) :
    dD (m :: ws) T = ∂_{m} (dD ws T) := rfl

/-- The symbol `ξ ↦ ∏_{m ∈ ws} ⟨ξ, m⟩`. -/
def polyW (ws : List (Eucl n)) (ξ : Eucl n) : ℂ :=
  (ws.map fun m => ((inner ℝ ξ m : ℝ) : ℂ)).prod

theorem polyW_cons (m : Eucl n) (ws : List (Eucl n)) :
    polyW (m :: ws) = fun ξ => ((inner ℝ ξ m : ℝ) : ℂ) * polyW ws ξ := by
  funext ξ; simp [polyW]

theorem polyW_temperate (ws : List (Eucl n)) : (polyW ws).HasTemperateGrowth := by
  induction ws with
  | nil =>
    have : polyW ([] : List (Eucl n)) = fun _ => (1 : ℂ) := by funext ξ; simp [polyW]
    rw [this]
    exact Function.HasTemperateGrowth.const 1
  | cons m ws ih =>
    rw [polyW_cons]
    have h1 : (fun ξ : Eucl n => ((inner ℝ ξ m : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
    exact h1.mul ih

/-- **Fourier transform of iterated derivatives** on `𝓢'`:
`𝓕 (∂_{ws} T) = (2πi)^{|ws|} ∏⟨ξ, m⟩ · 𝓕 T`. -/
theorem fourier_dD (ws : List (Eucl n)) (T : 𝓢'(Eucl n, F)) :
    𝓕 (dD ws T) = ((2 * Real.pi * Complex.I) ^ ws.length) •
      TemperedDistribution.smulLeftCLM F (polyW ws) (𝓕 T) := by
  induction ws with
  | nil =>
    have : polyW ([] : List (Eucl n)) = fun _ => (1 : ℂ) := by funext ξ; simp [polyW]
    simp [this]
  | cons m ws ih =>
    have h1 : (fun ξ : Eucl n => ((inner ℝ ξ m : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
    rw [dD_cons, TemperedDistribution.fourier_lineDerivOp_eq, ih, map_smul,
      TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (polyW_temperate ws) h1, smul_smul,
      List.length_cons, pow_succ, mul_comm (2 * Real.pi * Complex.I)]
    congr 2
    rw [polyW_cons]
    congr 1
    funext ξ
    simp only [Pi.mul_apply]
    ring

/-- A multiplier identity on `𝓢'` between `L²` functions is a pointwise a.e. identity. -/
theorem ae_eq_of_smulLeftCLM_eq {g : Eucl n → ℂ} (hg : g.HasTemperateGrowth)
    {H G : Lp F 2 (volume : Measure (Eucl n))}
    (h : TemperedDistribution.smulLeftCLM F g (H : 𝓢'(Eucl n, F)) = (G : 𝓢'(Eucl n, F))) :
    (fun ξ => g ξ • (H : Eucl n → F) ξ) =ᵐ[volume] G := by
  have hHl : LocallyIntegrable (H : Eucl n → F) volume := (Lp.memLp H).locallyIntegrable (by norm_num)
  have hGl : LocallyIntegrable (G : Eucl n → F) volume := (Lp.memLp G).locallyIntegrable (by norm_num)
  have hgc : Continuous g := hg.1.continuous
  have hgH : LocallyIntegrable (fun ξ => g ξ • (H : Eucl n → F) ξ) volume :=
    hHl.continuous_smul hgc
  have hD := ae_eq_zero_of_integral_contDiff_smul_eq_zero (hgH.sub hGl) (fun φ hφ hφc => by
    have hc1 : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hφc.comp_left rfl
    have hc2 : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
    set ψ : 𝓢(Eucl n, ℂ) := hc1.toSchwartzMap hc2
    have hψ : ∀ ξ, ψ ξ = (φ ξ : ℂ) := fun ξ => rfl
    have e := congrArg (fun T : 𝓢'(Eucl n, F) => T ψ) h
    simp only [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
      SchwartzMap.smulLeftCLM_apply_apply hg, hψ, smul_eq_mul] at e
    have i1 : Integrable (fun ξ => φ ξ • (g ξ • (H : Eucl n → F) ξ)) volume :=
      hgH.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    have i2 : Integrable (fun ξ => φ ξ • (G : Eucl n → F) ξ) volume :=
      hGl.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    have hl : ∀ ξ, (g ξ * (φ ξ : ℂ)) • (H : Eucl n → F) ξ = φ ξ • (g ξ • (H : Eucl n → F) ξ) := by
      intro ξ
      rw [mul_comm, mul_smul, Complex.coe_smul]
    have hr : ∀ ξ, (φ ξ : ℂ) • (G : Eucl n → F) ξ = φ ξ • (G : Eucl n → F) ξ := fun ξ =>
      Complex.coe_smul _ _
    simp_rw [hl, hr] at e
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub i1 i2, e, sub_self])
  filter_upwards [hD] with ξ hξ
  simpa [sub_eq_zero] using hξ

end Words

/-! ### Elements of `W^{k,2}(ℝⁿ)` as tempered distributions -/

section WDistr

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [FiniteDimensional ℂ F] {k : ℕ}

/-- The `L²(ℝⁿ)` element of an `L²(1 · dx)` element. -/
def toVol (f : Lp F 2 (wμ (wholeSpace n).μ (1 : Weight (Eucl n)))) :
    Lp F 2 (volume : Measure (Eucl n)) :=
  ((Lp.memLp f).of_measure_le_smul ENNReal.one_ne_top (by rw [one_smul, wμ_one]; rfl)).toLp f

theorem coeFn_toVol (f : Lp F 2 (wμ (wholeSpace n).μ (1 : Weight (Eucl n)))) :
    (toVol f : Eucl n → F) =ᵐ[volume] f :=
  MemLp.coeFn_toLp _

theorem norm_toVol (f : Lp F 2 (wμ (wholeSpace n).μ (1 : Weight (Eucl n)))) :
    ‖toVol f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_toVol f)]
  congr 1
  generalize (f : Eucl n → F) = g
  rw [wμ_one]
  rfl

theorem Idx.ofList_toList' {k : ℕ} (α : Idx n k) (h : (Idx.toList α).length ≤ k) :
    Idx.ofList (Idx.toList α) h = α := by
  rcases α with ⟨⟨j, hj⟩, f⟩
  have hl : (List.ofFn f).length = j := List.length_ofFn
  refine Sigma.ext (Fin.ext hl) ?_
  refine (Fin.heq_fun_iff hl).mpr fun i => ?_
  simp [Idx.ofList, Idx.toList]

theorem word_ofList {k : ℕ} (u : List (Fin n)) (h : u.length ≤ k) :
    (wholeSpace n).word (Idx.ofList u h : Idx n k) = u.map e := by
  rw [TestDomain.word_eq_map, Idx.toList_ofList, wholeSpace_dir]

/-- The components of `x ∈ W^{k,2}` along lists are iterated distributional derivatives. -/
theorem W.dD_ofList (x : W (wholeSpace n) 1 ℂ F k 2) (u : List (Fin n)) (h : u.length ≤ k) :
    dD (u.map e) (toVol (W.value (wholeSpace n) 1 ℂ F k 2 x) : 𝓢'(Eucl n, F)) =
      (toVol (W.deriv (wholeSpace n) 1 ℂ F k 2 (Idx.ofList u h) x) : 𝓢'(Eucl n, F)) := by
  induction u with
  | nil =>
    rw [List.map_nil, dD_nil, Idx.ofList_nil, W.deriv_zero]
  | cons i u ih =>
    have h' : u.length ≤ k := by simp at h; omega
    rw [List.map_cons, dD_cons, ih h']
    apply lineDerivOp_toTemperedDistribution
    have h1 := W.hasWeakDeriv x (Idx.ofList u h')
    have h2 := W.hasWeakDeriv x (Idx.ofList (i :: u) h)
    rw [word_ofList] at h1 h2
    rw [List.map_cons] at h2
    have h3 := h2.perm (List.perm_append_singleton _ _).symm
    have h4 := h1.of_append h3
    exact h4.congr_ae (coeFn_toVol _).symm (coeFn_toVol _).symm

/-- **Each component is a distributional derivative**: `∂^α x = ∂_{word α} x` in `𝓢'`. -/
theorem W.dD_value (x : W (wholeSpace n) 1 ℂ F k 2) (α : Idx n k) :
    dD ((wholeSpace n).word α) (toVol (W.value (wholeSpace n) 1 ℂ F k 2 x) : 𝓢'(Eucl n, F)) =
      (toVol (W.deriv (wholeSpace n) 1 ℂ F k 2 α x) : 𝓢'(Eucl n, F)) := by
  have hlen : (Idx.toList α).length ≤ k := by
    rw [Idx.length_toList]; exact Nat.lt_succ_iff.mp α.1.isLt
  have := W.dD_ofList x (Idx.toList α) hlen
  rw [Idx.ofList_toList'] at this
  rw [TestDomain.word_eq_map, wholeSpace_dir]
  exact this

end WDistr

/-! ### The Bessel bound and `MemSobolev` -/

section Bessel

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [FiniteDimensional ℂ F] {k : ℕ}

theorem polyW_word (α : Idx n k) (ξ : Eucl n) :
    polyW ((wholeSpace n).word α) ξ = ∏ j : Fin α.1, ((ξ (α.2 j) : ℝ) : ℂ) := by
  simp only [polyW, TestDomain.word, wholeSpace_dir, List.map_ofFn, List.prod_ofFn]
  congr 1
  funext j
  simp [e, EuclideanSpace.inner_single_right]

theorem norm_polyW_word (α : Idx n k) (ξ : Eucl n) :
    ‖polyW ((wholeSpace n).word α) ξ‖ = ∏ j : Fin α.1, |ξ (α.2 j)| := by
  rw [polyW_word, norm_prod]
  simp

/-- `(1 + |ξ|²)^k ≤ 2^k ∑_{|α| ≤ k} ∏ ξ_{α_j}²`. -/
theorem one_add_sq_pow_le (ξ : Eucl n) :
    (1 + ‖ξ‖ ^ 2) ^ k ≤ 2 ^ k * ∑ α : Idx n k, ∏ j : Fin α.1, ξ (α.2 j) ^ 2 := by
  have hs : ‖ξ‖ ^ 2 = ∑ i, ξ i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [Real.norm_eq_abs, sq_abs]
  rw [hs, add_comm, add_pow, Fintype.sum_sigma, Finset.mul_sum,
    ← Fin.sum_univ_eq_sum_range (fun m => (∑ i, ξ i ^ 2) ^ m * 1 ^ (k - m) * (k.choose m : ℝ))]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [one_pow, mul_one, Fintype.sum_pow, mul_comm]
  have hc : ((k.choose (j : ℕ) : ℕ) : ℝ) ≤ 2 ^ k := by exact_mod_cast Nat.choose_le_two_pow k j
  have hnn : 0 ≤ ∑ p : Fin (j : ℕ) → Fin n, ∏ i, ξ (p i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => sq_nonneg _
  exact mul_le_mul_of_nonneg_right hc hnn

/-- The `L²` Fourier transform of the field of `x`. -/
def W.fourierValue (x : W (wholeSpace n) 1 ℂ F k 2) : Lp F 2 (volume : Measure (Eucl n)) :=
  𝓕 (toVol (W.value (wholeSpace n) 1 ℂ F k 2 x))

/-- The `L²` Fourier transform of the component `∂^α x`. -/
def W.fourierDeriv (x : W (wholeSpace n) 1 ℂ F k 2) (α : Idx n k) :
    Lp F 2 (volume : Measure (Eucl n)) :=
  𝓕 (toVol (W.deriv (wholeSpace n) 1 ℂ F k 2 α x))

/-- **The symbol of `∂^α`** (Plancherel form): `(2πi)^{|α|} ξ^α 𝓕x = 𝓕(∂^α x)` a.e. -/
theorem W.fourierDeriv_ae (x : W (wholeSpace n) 1 ℂ F k 2) (α : Idx n k) :
    (fun ξ => ((2 * Real.pi * Complex.I) ^ α.1.val • polyW ((wholeSpace n).word α)) ξ •
      (W.fourierValue x : Eucl n → F) ξ) =ᵐ[volume] W.fourierDeriv x α := by
  have hpt : (polyW ((wholeSpace n).word α)).HasTemperateGrowth := polyW_temperate _
  have hg : ((2 * Real.pi * Complex.I) ^ α.1.val • polyW ((wholeSpace n).word α)).HasTemperateGrowth := by
    have : ((2 * Real.pi * Complex.I) ^ α.1.val • polyW ((wholeSpace n).word α)) =
        (fun _ => (2 * Real.pi * Complex.I) ^ α.1.val) * polyW ((wholeSpace n).word α) := by
      funext ξ; simp [smul_eq_mul]
    rw [this]
    exact (Function.HasTemperateGrowth.const _).mul hpt
  apply ae_eq_of_smulLeftCLM_eq hg
  rw [TemperedDistribution.smulLeftCLM_smul hpt, W.fourierValue, W.fourierDeriv,
    ← Lp.fourier_toTemperedDistribution_eq, ← Lp.fourier_toTemperedDistribution_eq,
    ← W.dD_value x α, fourier_dD, TestDomain.length_word]
  rfl

/-- **Pointwise Bessel bound**: `(1+|ξ|²)^k |𝓕x(ξ)|² ≤ 2^k ∑_α |𝓕(∂^α x)(ξ)|²` a.e. -/
theorem W.bessel_ae (x : W (wholeSpace n) 1 ℂ F k 2) :
    ∀ᵐ ξ ∂volume, (1 + ‖ξ‖ ^ 2) ^ k * ‖(W.fourierValue x : Eucl n → F) ξ‖ ^ 2 ≤
      2 ^ k * ∑ α : Idx n k, ‖(W.fourierDeriv x α : Eucl n → F) ξ‖ ^ 2 := by
  have hall : ∀ᵐ ξ ∂volume, ∀ α : Idx n k,
      ((2 * Real.pi * Complex.I) ^ α.1.val • polyW ((wholeSpace n).word α)) ξ •
        (W.fourierValue x : Eucl n → F) ξ = (W.fourierDeriv x α : Eucl n → F) ξ :=
    eventually_all.mpr fun α => W.fourierDeriv_ae x α
  filter_upwards [hall] with ξ hξ
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
  have hterm : ∀ α : Idx n k, (∏ j : Fin α.1, ξ (α.2 j) ^ 2) *
      ‖(W.fourierValue x : Eucl n → F) ξ‖ ^ 2 ≤ ‖(W.fourierDeriv x α : Eucl n → F) ξ‖ ^ 2 := by
    intro α
    rw [← hξ α, norm_smul, Pi.smul_apply, smul_eq_mul, norm_mul, norm_pow, norm_polyW_word]
    have h2 : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
      simp [Complex.norm_I, abs_of_pos Real.pi_pos]
    rw [h2]
    have hprod : (∏ j : Fin α.1, ξ (α.2 j) ^ 2) = (∏ j : Fin α.1, |ξ (α.2 j)|) ^ 2 := by
      rw [← Finset.prod_pow]; simp [sq_abs]
    rw [hprod]
    have h1 : 1 ≤ (2 * Real.pi) ^ α.1.val := one_le_pow₀ hpi
    have hP : 0 ≤ ∏ j : Fin α.1, |ξ (α.2 j)| := Finset.prod_nonneg fun _ _ => abs_nonneg _
    have hN := norm_nonneg ((W.fourierValue x : Eucl n → F) ξ)
    nlinarith [mul_nonneg hP hN, mul_nonneg (mul_nonneg hP hN) (mul_nonneg hP hN),
      mul_le_mul_of_nonneg_right h1 (mul_nonneg (mul_nonneg hP hN) (mul_nonneg hP hN))]
  calc (1 + ‖ξ‖ ^ 2) ^ k * ‖(W.fourierValue x : Eucl n → F) ξ‖ ^ 2
      ≤ (2 ^ k * ∑ α : Idx n k, ∏ j : Fin α.1, ξ (α.2 j) ^ 2) *
          ‖(W.fourierValue x : Eucl n → F) ξ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (one_add_sq_pow_le ξ) (sq_nonneg _)
    _ = 2 ^ k * ∑ α : Idx n k, (∏ j : Fin α.1, ξ (α.2 j) ^ 2) *
          ‖(W.fourierValue x : Eucl n → F) ξ‖ ^ 2 := by
        rw [mul_assoc, Finset.sum_mul]
    _ ≤ 2 ^ k * ∑ α : Idx n k, ‖(W.fourierDeriv x α : Eucl n → F) ξ‖ ^ 2 := by
        gcongr with α
        exact hterm α

theorem eLpNorm_two_sq {G : Type*} [NormedAddCommGroup G] (μ : Measure (Eucl n))
    (f : Eucl n → G) : eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [one_div, show (2⁻¹ : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num,
    ENNReal.rpow_inv_natCast_pow (by norm_num)]

theorem eLpNorm_two_sq_Lp (G : Lp F 2 (volume : Measure (Eucl n))) :
    ∫⁻ x, ‖(G : Eucl n → F) x‖ₑ ^ 2 ∂volume = ENNReal.ofReal (‖G‖ ^ 2) := by
  rw [← eLpNorm_two_sq, ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top G)]

/-- The function `(1 + |ξ|²)^{k/2} 𝓕x(ξ)`. -/
def W.besselFn (x : W (wholeSpace n) 1 ℂ F k 2) (ξ : Eucl n) : F :=
  (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) • (W.fourierValue x : Eucl n → F) ξ

theorem W.norm_besselFn_sq (x : W (wholeSpace n) 1 ℂ F k 2) (ξ : Eucl n) :
    ‖W.besselFn x ξ‖ ^ 2 = (1 + ‖ξ‖ ^ 2) ^ k * ‖(W.fourierValue x : Eucl n → F) ξ‖ ^ 2 := by
  have hb : (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ)) ^ 2 = (1 + ‖ξ‖ ^ 2) ^ k := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity),
      show (k : ℝ) / 2 * ((2 : ℕ) : ℝ) = ((k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [W.besselFn, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hb]

/-- **Quantitative Bessel bound** (S9a): `‖(1 + |ξ|²)^{k/2} 𝓕x‖²_{L²} ≤ 2^k ‖x‖²_{H^k}`. -/
theorem W.bessel_sq_le (x : W (wholeSpace n) 1 ℂ F k 2) :
    eLpNorm (W.besselFn x) 2 volume ^ 2 ≤ 2 ^ k * ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [eLpNorm_two_sq]
  have hpt : ∀ᵐ ξ ∂volume, ‖W.besselFn x ξ‖ₑ ^ 2 ≤
      2 ^ k * ∑ α : Idx n k, ‖(W.fourierDeriv x α : Eucl n → F) ξ‖ₑ ^ 2 := by
    filter_upwards [W.bessel_ae x] with ξ hξ
    calc ‖W.besselFn x ξ‖ₑ ^ 2 = ENNReal.ofReal (‖W.besselFn x ξ‖ ^ 2) := by
          rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
      _ ≤ ENNReal.ofReal (2 ^ k * ∑ α : Idx n k, ‖(W.fourierDeriv x α : Eucl n → F) ξ‖ ^ 2) := by
          rw [W.norm_besselFn_sq]; exact ENNReal.ofReal_le_ofReal hξ
      _ = 2 ^ k * ∑ α : Idx n k, ‖(W.fourierDeriv x α : Eucl n → F) ξ‖ₑ ^ 2 := by
          rw [ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
          congr 1
          · rw [ENNReal.ofReal_pow (by norm_num)]; simp
          · refine Finset.sum_congr rfl fun α _ => ?_
            rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  calc ∫⁻ ξ, ‖W.besselFn x ξ‖ₑ ^ 2 ∂volume
      ≤ ∫⁻ ξ, 2 ^ k * ∑ α : Idx n k, ‖(W.fourierDeriv x α : Eucl n → F) ξ‖ₑ ^ 2 ∂volume :=
        lintegral_mono_ae hpt
    _ = 2 ^ k * ∑ α : Idx n k, ∫⁻ ξ, ‖(W.fourierDeriv x α : Eucl n → F) ξ‖ₑ ^ 2 ∂volume := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_finsetSum' _ fun α _ =>
          ((Lp.aestronglyMeasurable _).enorm.pow_const 2)]
    _ = 2 ^ k * ENNReal.ofReal (‖x‖ ^ 2) := by
        congr 1
        simp_rw [eLpNorm_two_sq_Lp, W.fourierDeriv, Lp.norm_fourier_eq, norm_toVol]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _), W.norm_sq]

theorem W.memLp_besselFn (x : W (wholeSpace n) 1 ℂ F k 2) :
    MemLp (W.besselFn x) 2 volume := by
  refine ⟨?_, lt_of_le_of_ne le_top fun h => ?_⟩
  · have hc : Continuous fun ξ : Eucl n => (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_const.add (continuous_norm.pow 2)).rpow_const
        fun y => Or.inl (by positivity : (1 : ℝ) + ‖y‖ ^ 2 ≠ 0))
    exact hc.aestronglyMeasurable.smul (Lp.aestronglyMeasurable _)
  · have := W.bessel_sq_le x
    rw [h, ENNReal.top_pow (by norm_num)] at this
    exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top (top_le_iff.mp this)

/-- **`W^{k,2}(ℝⁿ) ⊂ H^k`** (S9a; D3: Mathlib `MemSobolev` as the `p = 2` bridge): the field of
`x ∈ W^{k,2}(ℝⁿ; F)` is a Sobolev distribution of order `k` (tex 1463–1477 B0091, tex 308–312
B1009). -/
theorem W.memSobolev (x : W (wholeSpace n) 1 ℂ F k 2) :
    MemSobolev (k : ℝ) 2 (toVol (W.value (wholeSpace n) 1 ℂ F k 2 x) : 𝓢'(Eucl n, F)) := by
  rw [memSobolev_iff_exists_smulLeftCLM_fourier]
  refine ⟨(W.memLp_besselFn x).toLp _, ?_⟩
  have hg : (fun ξ : Eucl n => (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ)).HasTemperateGrowth := by
    fun_prop
  rw [Lp.fourier_toTemperedDistribution_eq]
  ext φ
  rw [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [(W.memLp_besselFn x).coeFn_toLp] with ξ hξ
  rw [hξ, SchwartzMap.smulLeftCLM_apply_apply hg, W.besselFn, smul_eq_mul, mul_comm, mul_smul]
  rfl

end Bessel

end UnforcedLeray.Sob
