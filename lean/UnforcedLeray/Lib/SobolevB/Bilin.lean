import UnforcedLeray.Lib.SobolevB.Density

/-!
# The bilinear product rule for weak derivatives (INF11 target S5, `HasWeakDeriv.bilin`)

Scoping note `INF11-INF14-Sobolev.md` §5.1 (S5). Manuscript uses: the Leibniz rule for weak
derivatives of products (tex 5812–5829, B0694; tex 5955–5958, B0699, `L⁴ · L⁴ ⊂ L²`;
tex 7550–7576, B0433).

For a continuous bilinear `B : F × F' → G` (`F` finite dimensional), `f, f' ∈ L^p`,
`g, g' ∈ L^q`, `1/p + 1/q = 1/r`, `1 ≤ r`, `p < ∞`, with `f' = ∂_v f` and `g' = ∂_v g` weakly:
`∂_v B(f, g) = B(f', g) + B(f, g')` weakly (`HasWeakDeriv.bilin`).

Proof. For a smooth first factor `u` the rule follows from the scalar rule
`HasWeakDeriv.smul_left` in a basis of `F` (`HasWeakDeriv.bilin_smooth`). For general `f` the
mollifications `f_j = f ⋆ b̃_j` are smooth with `∂_v f_j = f' ⋆ b̃_j`, `f_j → f` and
`∂_v f_j → f'` in `L^p`; the pairings against a test function converge by Hölder
(`tendsto_integral_test_bilin`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology ContDiff

namespace UnforcedLeray.Sob

variable {n : ℕ} {F F' G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem nnnorm_bilin_le (B : F →L[ℝ] F' →L[ℝ] G) (a : F) (c : F') :
    ‖B a c‖₊ ≤ ‖B‖₊ * ‖a‖₊ * ‖c‖₊ := by
  rw [← NNReal.coe_le_coe]; push_cast; exact B.le_opNorm₂ a c

theorem locallyIntegrable_clm_comp {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup K] [NormedSpace ℝ K] (L : H →L[ℝ] K) {g : Eucl n → H}
    (hg : LocallyIntegrable g volume) : LocallyIntegrable (fun x => L (g x)) volume :=
  locallyIntegrableOn_univ.mp (L.locallyIntegrableOn_comp (locallyIntegrableOn_univ.mpr hg))

/-- **Leibniz rule with a smooth first factor**: `∂_v B(u, g) = B(∂_v u, g) + B(u, ∂_v g)`. -/
theorem HasWeakDeriv.bilin_smooth (B : F →L[ℝ] F' →L[ℝ] G) {u : Eucl n → F}
    (hu : ContDiff ℝ ∞ u) {v : Eucl n} {g g' : Eucl n → F'} (hg : LocallyIntegrable g volume)
    (hg' : LocallyIntegrable g' volume) (hw : HasWeakDeriv (wholeSpace n) [v] g g') :
    HasWeakDeriv (wholeSpace n) [v] (fun x => B (u x) (g x))
      (fun x => B (fderiv ℝ u x v) (g x) + B (u x) (g' x)) := by
  set b := Module.finBasis ℝ F
  set cl : Fin (Module.finrank ℝ F) → F →L[ℝ] ℝ := fun k =>
    LinearMap.toContinuousLinearMap (b.coord k)
  have hc : ∀ k, ContDiff ℝ ∞ (fun x => cl k (u x)) := fun k => (cl k).contDiff.comp hu
  have hterm : ∀ k ∈ Finset.univ, HasWeakDeriv (wholeSpace n) [v]
      (fun x => cl k (u x) • B (b k) (g x))
      (fun x => fderiv ℝ (fun y => cl k (u y)) x v • B (b k) (g x) +
        cl k (u x) • B (b k) (g' x)) := fun k _ =>
    (hw.map_clm (B (b k))).smul_left (hc k) (locallyIntegrable_clm_comp _ hg)
      (locallyIntegrable_clm_comp _ hg')
  have hsum := HasWeakDeriv.sum Finset.univ hterm
  have hrepr : ∀ w : F, w = ∑ k, cl k w • b k := fun w => by
    conv_lhs => rw [← b.sum_repr w]
    rfl
  refine hsum.congr_ae (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · simp only
    conv_rhs => rw [hrepr (u x)]
    simp [map_sum, map_smul]
  · simp only
    have hd : ∀ k, fderiv ℝ (fun y => cl k (u y)) x v = cl k (fderiv ℝ u x v) := by
      intro k
      have h1 : HasFDerivAt (fun y => cl k (u y)) ((cl k).comp (fderiv ℝ u x)) x :=
        (cl k).hasFDerivAt.comp x ((hu.differentiable (by simp)) x).hasFDerivAt
      rw [h1.fderiv]
      rfl
    simp only [hd, Finset.sum_add_distrib]
    conv_rhs => rw [hrepr (fderiv ℝ u x v), hrepr (u x)]
    simp [map_sum, map_smul]

section Limit

variable {p q r : ℝ≥0∞}

/-- Pairings `∫ ψ B(u_j, w)` with a test function converge when `u_j → u₀` in `L^p`,
`w ∈ L^q`, `1/p + 1/q = 1/r`, `1 ≤ r`. -/
theorem tendsto_integral_test_bilin (B : F →L[ℝ] F' →L[ℝ] G) [ENNReal.HolderTriple p q r]
    [Fact (1 ≤ r)] {ψ : Eucl n → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {u : ℕ → Eucl n → F} {u₀ : Eucl n → F} (hu : ∀ j, AEStronglyMeasurable (u j) volume)
    (hu₀ : AEStronglyMeasurable u₀ volume)
    (hconv : Tendsto (fun j => eLpNorm (u j - u₀) p volume) atTop (𝓝 0))
    {w : Eucl n → F'} (hw : MemLp w q volume)
    (hint : ∀ j, Integrable (fun x => ψ x • B (u j x) (w x)) volume) :
    Tendsto (fun j => ∫ x, ψ x • B (u j x) (w x)) atTop (𝓝 (∫ x, ψ x • B (u₀ x) (w x))) := by
  haveI := holderTriple_conjExp r
  have hBm : ∀ a : Eucl n → F, AEStronglyMeasurable a volume →
      AEStronglyMeasurable (fun x => B (a x) (w x)) volume := fun a ha =>
    (B.continuous₂.comp_aestronglyMeasurable₂ ha hw.1)
  refine tendsto_integral_of_L1 _ (hψ.aestronglyMeasurable.smul (hBm u₀ hu₀))
    (Eventually.of_forall hint) ?_
  have hψm : eLpNorm ψ (conjExp r) volume ≠ ⊤ :=
    (hψ.memLp_of_hasCompactSupport (μ := volume) hψc).2.ne
  have hb : ∀ j, ∫⁻ x, ‖ψ x • B (u j x) (w x) - ψ x • B (u₀ x) (w x)‖ₑ ≤
      eLpNorm ψ (conjExp r) volume * (‖B‖₊ * eLpNorm (u j - u₀) p volume * eLpNorm w q volume) := by
    intro j
    have e1 : (fun x => ψ x • B (u j x) (w x) - ψ x • B (u₀ x) (w x)) =
        ψ • fun x => B ((u j - u₀) x) (w x) := by
      funext x; simp [smul_sub, map_sub]
    rw [← eLpNorm_one_eq_lintegral_enorm, e1]
    refine (eLpNorm_smul_le_mul_eLpNorm (p := conjExp r) (q := r) (r := 1)
      (hBm _ ((hu j).sub hu₀)) hψ.aestronglyMeasurable).trans ?_
    gcongr
    exact eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm ((hu j).sub hu₀) hw.1 (fun a c => B a c) ‖B‖₊
      (Eventually.of_forall fun x => nnnorm_bilin_le B _ _)
  have hlim : Tendsto (fun j => eLpNorm ψ (conjExp r) volume *
      (‖B‖₊ * eLpNorm (u j - u₀) p volume * eLpNorm w q volume)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => (‖B‖₊ : ℝ≥0∞) * eLpNorm (u j - u₀) p volume) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hconv (Or.inr ENNReal.coe_ne_top)
    have h2 := ENNReal.Tendsto.mul_const h1 (Or.inr hw.2.ne)
    have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr hψm)
    simpa using h3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun j => zero_le) hb

end Limit

/-- **Bilinear product rule** (S5, `HasWeakDeriv.bilin`): for `f, f' ∈ L^p`, `g, g' ∈ L^q`,
`1/p + 1/q = 1/r` with `1 ≤ r`, `p < ∞`, if `f' = ∂_v f` and `g' = ∂_v g` weakly, then
`∂_v B(f, g) = B(f', g) + B(f, g')` weakly. -/
theorem HasWeakDeriv.bilin (B : F →L[ℝ] F' →L[ℝ] G) {p q r : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] [Fact (1 ≤ r)] [ENNReal.HolderTriple p q r] (hp : p ≠ ⊤) {v : Eucl n}
    {f f' : Eucl n → F} {g g' : Eucl n → F'} (hf : MemLp f p volume) (hf' : MemLp f' p volume)
    (hg : MemLp g q volume) (hg' : MemLp g' q volume)
    (hwf : HasWeakDeriv (wholeSpace n) [v] f f') (hwg : HasWeakDeriv (wholeSpace n) [v] g g') :
    HasWeakDeriv (wholeSpace n) [v] (fun x => B (f x) (g x))
      (fun x => B (f' x) (g x) + B (f x) (g' x)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hq1 : (1 : ℝ≥0∞) ≤ q := Fact.out
  have hr1 : (1 : ℝ≥0∞) ≤ r := Fact.out
  have hbil : ∀ {a : Eucl n → F} {c : Eucl n → F'}, MemLp a p volume → MemLp c q volume →
      MemLp (fun x => B (a x) (c x)) r volume := fun ha hc =>
    MemLp.of_bilin (fun a c => B a c) ‖B‖₊ ha hc
      (B.continuous₂.comp_aestronglyMeasurable₂ ha.1 hc.1)
      (Eventually.of_forall fun x => nnnorm_bilin_le B _ _)
  have hloc : ∀ {a : Eucl n → F} {c : Eucl n → F'}, MemLp a p volume → MemLp c q volume →
      LocallyIntegrable (fun x => B (a x) (c x)) volume := fun ha hc =>
    (hbil ha hc).locallyIntegrable hr1
  refine HasWeakDeriv.of_locallyIntegrable (hloc hf hg) ((hloc hf' hg).add (hloc hf hg'))
    fun φ hφs hφc => ?_
  simp only [iterDirDeriv_singleton, List.length_singleton, pow_one, neg_smul, one_smul]
  have hφ : (wholeSpace n).Adm φ := ⟨hφs, hφc⟩
  have hdφ : (wholeSpace n).Adm (fun x => fderiv ℝ φ x v) := (wholeSpace n).deriv_mem hφ v
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable hp1
  have hf'l : LocallyIntegrable f' volume := hf'.locallyIntegrable hp1
  have hgl : LocallyIntegrable g volume := hg.locallyIntegrable hq1
  have hg'l : LocallyIntegrable g' volume := hg'.locallyIntegrable hq1
  -- the mollified first factor
  set fj : ℕ → Eucl n → F := fun j => moll (shrinkBump n j) volume f
  set fj' : ℕ → Eucl n → F := fun j => moll (shrinkBump n j) volume f'
  have hfs : ∀ j, ContDiff ℝ ∞ (fj j) := fun j => contDiff_moll _ hfl
  have hder : ∀ j x, fderiv ℝ (fj j) x v = fj' j x := by
    intro j x
    have h := iterDD_cv_of_hasWeakDeriv (μ := volume) (dir := e) hwf
      ((shrinkBump n j).contDiff_normed (μ := volume))
      ((shrinkBump n j).hasCompactSupport_normed (μ := volume)) hfl
    exact congrFun h x
  have hfm : ∀ j, MemLp (fj j) p volume := fun j =>
    memLp_moll _ hp1 hp hf (hfs j).continuous.aestronglyMeasurable
  have hf'm : ∀ j, MemLp (fj' j) p volume := fun j =>
    memLp_moll _ hp1 hp hf' (contDiff_moll _ hf'l).continuous.aestronglyMeasurable
  have hc1 : Tendsto (fun j => eLpNorm (fj j - f) p volume) atTop (𝓝 0) := by
    refine (tendsto_eLpNorm_moll_sub hp hf (tendsto_shrinkBump_rOut n)).congr fun j => ?_
    rw [eLpNorm_sub_comm]
  have hc2 : Tendsto (fun j => eLpNorm (fj' j - f') p volume) atTop (𝓝 0) := by
    refine (tendsto_eLpNorm_moll_sub hp hf' (tendsto_shrinkBump_rOut n)).congr fun j => ?_
    rw [eLpNorm_sub_comm]
  -- the identity for the mollified factor
  have hid : ∀ j, ∫ x, fderiv ℝ φ x v • B (fj j x) (g x) =
      -((∫ x, φ x • B (fj' j x) (g x)) + ∫ x, φ x • B (fj j x) (g' x)) := by
    intro j
    have hw := HasWeakDeriv.bilin_smooth B (hfs j) hgl hg'l hwg
    have h := hw.identity φ hφ
    simp only [iterDirDeriv_singleton, wholeSpace_μ, List.length_singleton, pow_one, neg_smul,
      one_smul, hder] at h
    rw [h, ← integral_add (integrable_smul_of_adm hφ (hloc (hf'm j) hg))
      (integrable_smul_of_adm hφ (hloc (hfm j) hg'))]
    congr 2; funext x; rw [smul_add]
  have hL := tendsto_integral_test_bilin (p := p) (q := q) (r := r) B hdφ.1.continuous hdφ.2
    (fun j => (hfm j).1) hf.1 hc1 hg (fun j => integrable_smul_of_adm hdφ (hloc (hfm j) hg))
  have hR1 := tendsto_integral_test_bilin (p := p) (q := q) (r := r) B hφs.continuous hφc
    (fun j => (hf'm j).1) hf'.1 hc2 hg (fun j => integrable_smul_of_adm hφ (hloc (hf'm j) hg))
  have hR2 := tendsto_integral_test_bilin (p := p) (q := q) (r := r) B hφs.continuous hφc
    (fun j => (hfm j).1) hf.1 hc1 hg' (fun j => integrable_smul_of_adm hφ (hloc (hfm j) hg'))
  have hR := (hR1.add hR2).neg
  have hlim := tendsto_nhds_unique (hL.congr hid) hR
  rw [hlim, ← integral_add (integrable_smul_of_adm hφ (hloc hf' hg))
    (integrable_smul_of_adm hφ (hloc hf hg'))]
  congr 2; funext x; rw [smul_add]

end UnforcedLeray.Sob
