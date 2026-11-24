import UnforcedLeray.Units.B0418.Operator
import UnforcedLeray.Units.B0418.GeneratorLp

/-!
# B0418 — the explicit free similarity semigroup `S_ν(r)` (`eq:free-stress-7`)

Blueprint unit B0418 (construction), `paper/main.tex` lines 7411--7427, in the proof
"Semigroup construction and initial inverse bound" (§`sec:st18-8976`), under the section's
standing assumption `ν > 0` (tex line 7306):

> The spatial semigroup of `νΔ + ½ y·∇ + ½` is
> `S_ν(r)h(y) = e^{r/2} [e^{ν(e^r-1)Δ} h](e^{r/2} y)`, `r ≥ 0`.  (eq:free-stress-7)
> Differentiation verifies the generator, initially for smooth functions. [...]
> It is strongly continuous.

The `L^q` decay `‖S_ν(r)‖ ≤ e^{-γ_q r}` (`eq:free-stress-8`, tex lines 7420--7425) is unit B0419;
it is proved here only as the helper `eLpNorm_freeEvolution_le` because strong continuity uses it.

## Conventions

* Fields are real three-vector fields `SpatialField = Space → Space` on `Space = ℝ³`
  (complex fields are handled componentwise in the manuscript).
* `S_ν(r)` is the library operator `AncientLocalization.freeEvolution ν r`
  (`lean/UnforcedLeray/Analysis/AncientLocalization/FreeEvolution.lean`), reused, not
  redefined; `eq_free_stress_7` records that it is literally the displayed formula.
* `e^{tΔ}` is the library `Heat.flow`: the Gaussian Bochner integral
  `∫ k_t(y) h(x-y) dy` for `t > 0` (and the identity for `t ≤ 0`). For `h ∈ L^p`,
  `1 ≤ p < ∞`, this integral converges absolutely at every point
  (`heat_integrand_integrable`), so no Bochner junk value enters.
* The exponent range is `1 ≤ p < ∞` (blueprint statement); the surrounding theorem
  (tex line 7365) only uses `1 < q < 3`, so no hypothesis is stronger than the manuscript's.
* "The generator, verified on smooth functions" is formalized as: for `h ∈ C_c^∞(ℝ³;ℝ³)`,
  `r⁻¹(S_ν(r)h - h) → (νΔ + ½ y·∇ + ½)h` in `L^p` as `r → 0⁺`, i.e. `C_c^∞` lies in the
  domain of the `L^p` generator and the generator acts there as the stated operator. The
  manuscript does not claim (and this file does not formalize) that `C_c^∞` is a core.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff

namespace UnforcedLeray.B0418

open UnforcedLeray.AncientLocalization

/-- `eq:free-stress-7` (tex lines 7414--7417): the library operator `freeEvolution ν r` is
literally `S_ν(r)h(y) = e^{r/2} [e^{ν(e^r-1)Δ}h](e^{r/2} y)`. -/
theorem eq_free_stress_7 (ν r : ℝ) (h : SpatialField) (y : Space) :
    freeEvolution ν r h y =
      Real.exp (r / 2) • Heat.flow h (ν * (Real.exp r - 1)) (Real.exp (r / 2) • y) :=
  freeEvolution_apply ν r h y

/-- The heat factor is the literal Gaussian integral, absolutely convergent on `L^p`. -/
theorem heat_factor_literal {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ (∞ : ℝ≥0∞)) {h : SpatialField}
    (hh : MemLp h p volume) {t : ℝ} (ht : 0 < t) (x : Space) :
    Heat.flow h t x = ∫ y, Heat.kernel t y • h (x - y) ∧
      Integrable (fun y => Heat.kernel t y • h (x - y)) :=
  ⟨by rw [Heat.flow_pos h ht]; rfl, heat_integrand_integrable ht hp1 hp hh x⟩

/-- `C_c^∞` fields have their image under `νΔ + ½ y·∇ + ½` in every `L^p`. -/
theorem memLp_generator {p : ℝ≥0∞} (ν : ℝ) {h : SpatialField} (hs : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) : MemLp (generator ν h) p volume := by
  have hcf : Continuous (fderiv ℝ h) :=
    (contDiff_one_of_infty hs).continuous_fderiv one_ne_zero
  have hB : Continuous (fun y => fderiv ℝ h y y) := hcf.clm_apply continuous_id
  have hBc : HasCompactSupport (fun y => fderiv ℝ h y y) := by
    refine hc.mono' (fun y hy => support_fderiv_subset ℝ (Function.mem_support.mpr ?_))
    intro h0
    exact (Function.mem_support.mp hy) (by rw [h0]; rfl)
  have hL : MemLp (vecLaplacian h) p volume :=
    (continuous_vecLaplacian hs).memLp_of_hasCompactSupport (hasCompactSupport_vecLaplacian hc)
  have hD : MemLp (fun y => fderiv ℝ h y y) p volume := hB.memLp_of_hasCompactSupport hBc
  have hH : MemLp h p volume := hs.continuous.memLp_of_hasCompactSupport hc
  have he : generator ν h =
      ν • vecLaplacian h + (1 / 2 : ℝ) • (fun y => fderiv ℝ h y y) + (1 / 2 : ℝ) • h := by
    funext y
    rfl
  rw [he]
  exact ((hL.const_smul ν).add (hD.const_smul (1 / 2 : ℝ))).add (hH.const_smul (1 / 2 : ℝ))

/-- The generator statement at the level of `L^p` classes: for `h ∈ C_c^∞`,
`r⁻¹ (S_ν(r)h - h) → (νΔ + ½ y·∇ + ½)h` in `Lp`. -/
theorem tendsto_generator_Lp {ν : ℝ} (hν : 0 < ν) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ (∞ : ℝ≥0∞)) {h : SpatialField} (hs : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    Tendsto (fun r : ℝ => r⁻¹ • (freeSemigroupLp hp ν r
        ((hs.continuous.memLp_of_hasCompactSupport hc : MemLp h p volume).toLp h) -
        (hs.continuous.memLp_of_hasCompactSupport hc : MemLp h p volume).toLp h))
      (𝓝[>] 0) (𝓝 ((memLp_generator ν hs hc : MemLp (generator ν h) p volume).toLp
        (generator ν h))) := by
  have hH : MemLp h p volume := hs.continuous.memLp_of_hasCompactSupport hc
  rw [tendsto_iff_edist_tendsto_0]
  refine (tendsto_generator hν Fact.out hp hs hc).congr (fun r => ?_)
  rw [Lp.edist_def]
  apply eLpNorm_congr_ae
  have hH' : ((hs.continuous.memLp_of_hasCompactSupport hc : MemLp h p volume).toLp h :
      SpatialField) =ᵐ[volume] h := MemLp.coeFn_toLp _
  have h1 := Lp.coeFn_smul r⁻¹ (freeSemigroupLp hp ν r
      ((hs.continuous.memLp_of_hasCompactSupport hc : MemLp h p volume).toLp h) -
      (hs.continuous.memLp_of_hasCompactSupport hc : MemLp h p volume).toLp h)
  have h2 := Lp.coeFn_sub (freeSemigroupLp hp ν r
      ((hs.continuous.memLp_of_hasCompactSupport hc : MemLp h p volume).toLp h))
      ((hs.continuous.memLp_of_hasCompactSupport hc : MemLp h p volume).toLp h)
  have h3 := coeFn_freeSemigroupLp hp ν r
      ((hs.continuous.memLp_of_hasCompactSupport hc : MemLp h p volume).toLp h)
  have h4 := freeEvolution_congr_ae hH' ν r
  have h5 : ((memLp_generator ν hs hc : MemLp (generator ν h) p volume).toLp (generator ν h) :
      SpatialField) =ᵐ[volume] generator ν h := MemLp.coeFn_toLp _
  filter_upwards [h1, h2, h3, h4, h5, hH'] with y e1 e2 e3 e4 e5 e6
  simp only [Pi.sub_apply, Pi.smul_apply] at e1 e2 ⊢
  rw [e1, e2, e3, e4, e5, e6]

/-- **Unit B0418** (tex lines 7411--7427). For `ν > 0` and `1 ≤ p < ∞`, the operators
`S_ν(r)` of `eq:free-stress-7` form a strongly continuous semigroup on `L^p(ℝ³; ℝ³)`:
`S_ν(0) = I`, `S_ν(r₁ + r₂) = S_ν(r₁) S_ν(r₂)` for `r₁, r₂ ≥ 0`, every orbit is continuous on
`[0, ∞)`; each `S_ν(r)` is represented by the literal formula; and on `C_c^∞` fields the
generator is `νΔ + ½ y·∇ + ½`. -/
theorem free_similarity_semigroup {ν : ℝ} (hν : 0 < ν) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ (∞ : ℝ≥0∞)) :
    (∀ r : ℝ, ∀ u : Lp Space p (volume : Measure Space),
      (freeSemigroupLp hp ν r u : SpatialField) =ᵐ[volume] fun y =>
        Real.exp (r / 2) • Heat.flow (u : SpatialField) (ν * (Real.exp r - 1))
          (Real.exp (r / 2) • y)) ∧
    freeSemigroupLp hp ν 0 = ContinuousLinearMap.id ℝ _ ∧
    (∀ r₁ r₂ : ℝ, 0 ≤ r₁ → 0 ≤ r₂ →
      freeSemigroupLp hp ν (r₁ + r₂) =
        (freeSemigroupLp hp ν r₁).comp (freeSemigroupLp hp ν r₂)) ∧
    (∀ u : Lp Space p (volume : Measure Space),
      ContinuousOn (fun r => freeSemigroupLp hp ν r u) (Ici 0)) ∧
    (∀ h : SpatialField, ∀ (hs : ContDiff ℝ ∞ h) (hc : HasCompactSupport h),
      Tendsto (fun r : ℝ => r⁻¹ • (freeSemigroupLp hp ν r
          ((hs.continuous.memLp_of_hasCompactSupport hc : MemLp h p volume).toLp h) -
          (hs.continuous.memLp_of_hasCompactSupport hc : MemLp h p volume).toLp h))
        (𝓝[>] 0) (𝓝 ((memLp_generator ν hs hc : MemLp (generator ν h) p volume).toLp
          (generator ν h)))) :=
  ⟨fun r u => coeFn_freeSemigroupLp hp ν r u,
    freeSemigroupLp_zero hp ν,
    fun _ _ hr₁ hr₂ => freeSemigroupLp_add hp hν.le hr₁ hr₂,
    fun u => continuousOn_freeSemigroupLp hp hν.le u,
    fun _ hs hc => tendsto_generator_Lp hν hp hs hc⟩

/-- The same statement for the literal pointwise operators on `L^p` fields: semigroup law
at every point, `S_ν(0) = id`, strong continuity on `[0, ∞)` and the generator on `C_c^∞`. -/
theorem free_similarity_semigroup_fields {ν : ℝ} (hν : 0 < ν) {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ (∞ : ℝ≥0∞)) :
    (∀ h : SpatialField, freeEvolution ν 0 h = h) ∧
    (∀ h : SpatialField, MemLp h p volume → ∀ r : ℝ, MemLp (freeEvolution ν r h) p volume) ∧
    (∀ h : SpatialField, MemLp h p volume → ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → 0 ≤ r₂ →
      freeEvolution ν r₁ (freeEvolution ν r₂ h) = freeEvolution ν (r₁ + r₂) h) ∧
    (∀ h : SpatialField, MemLp h p volume → ∀ r₀ : ℝ, 0 ≤ r₀ →
      Tendsto (fun r => eLpNorm (freeEvolution ν r h - freeEvolution ν r₀ h) p volume)
        (𝓝[Ici 0] r₀) (𝓝 0)) ∧
    (∀ h : SpatialField, ContDiff ℝ ∞ h → HasCompactSupport h →
      Tendsto (fun r => eLpNorm (fun y => r⁻¹ • (freeEvolution ν r h y - h y) -
        generator ν h y) p volume) (𝓝[>] 0) (𝓝 0)) :=
  ⟨fun h => freeEvolution_zero ν h,
    fun _ hh r => freeEvolution_memLp hp1 hp hh ν r,
    fun _ hh _ _ hr₁ hr₂ => freeEvolution_add hν.le hr₁ hr₂ hp1 hp hh,
    fun _ hh _ hr₀ => tendsto_freeEvolution hν.le hp1 hp hh hr₀,
    fun _ hs hc => tendsto_generator hν hp1 hp hs hc⟩

end UnforcedLeray.B0418
