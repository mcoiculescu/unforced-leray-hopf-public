import UnforcedLeray.Lib.Sobolev.HigherChain

/-!
# Change of variables on `Sob.W` (INF11 target S6: `W.compDiffeo`)

Scoping note `INF11-INF14-Sobolev.md` §5.1 (S6): "Change of variables: translations, linear
isometries, dilations, C^∞ diffeomorphisms with bounded derivatives",
`W.compDiffeo : W (wholeSpace n) ρ 𝕜 F k p →L[𝕜] W (wholeSpace n) (ρ ∘ Φ.symm) 𝕜 F k p`.
Manuscript uses: B0062 (composition with the area-preserving flow, tex 1228–1237), B0102
(`J_a f = a⁻² f(·/√a)`, tex 1569–1580), B0156 (tex 2370–2377), B0712 (tex 292–298),
B0912 (tex 14162–14178), B1029 (tex 238–242).

`W.compDiffeo Φ … x = x ∘ Φ⁻¹`. Its derivatives are the combinations of
`HigherChain.lean`; the `L^p` bounds come from the change of variables
`map Φ⁻¹ (ρ ∘ Φ⁻¹ dx) ≤ C · ρ dy` (`map_symm_le`), where `C` bounds the Jacobian of `Φ`.

## Hypotheses (deviation from the note's signature)
The note asks for bounded derivatives of `Φ` of orders `≤ k` and `|det DΦ| ≥ c > 0`. What the
proof uses is: bounded derivatives of `Φ⁻¹` of orders `1, …, k` (`hbd`) and `|det DΦ| ≤ C`
(`hjac`). Under smoothness of `Φ` and `Φ⁻¹` the two sets of hypotheses are equivalent
(inverse function formula and `|det A| ≤ ‖A‖ⁿ`), so the statement is not stronger than the
manuscript's; for the manuscript's maps (dilations, translations, rotations, the
area-preserving flow) both are checked directly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff Topology

namespace UnforcedLeray.Sob

variable {n : ℕ}

/-- The weight `ρ ∘ Ψ` for a homeomorphism `Ψ`. -/
def Weight.compHomeo (ρ : Weight (Eucl n)) (Ψ : Eucl n ≃ₜ Eucl n) : Weight (Eucl n) where
  toFun x := ρ (Ψ x)
  measurable := ρ.measurable.comp Ψ.continuous.measurable
  pos x := ρ.pos _
  locBdd K hK := by
    obtain ⟨a, b, ha, hab⟩ := ρ.locBdd (Ψ '' K) (hK.image Ψ.continuous)
    exact ⟨a, b, ha, fun x hx => hab _ ⟨x, hx, rfl⟩⟩

@[simp] theorem Weight.compHomeo_apply (ρ : Weight (Eucl n)) (Ψ : Eucl n ≃ₜ Eucl n)
    (x : Eucl n) : ρ.compHomeo Ψ x = ρ (Ψ x) := rfl

section Lp

variable (Φ : Eucl n ≃ₜ Eucl n) (hΦ : ContDiff ℝ ∞ Φ) (hΨ : ContDiff ℝ ∞ Φ.symm)
  (ρ : Weight (Eucl n)) {C : ℝ} (hC : ∀ y, jac Φ y ≤ C)

include hΦ hC in
/-- `Φ⁻¹` pushes `(ρ ∘ Φ⁻¹) dx` to at most `C · ρ dy`. -/
theorem map_symm_le :
    Measure.map Φ.symm (wμ volume (ρ.compHomeo Φ.symm)) ≤
      ENNReal.ofReal C • wμ volume ρ := by
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [Measure.map_apply Φ.symm.continuous.measurable hs, Measure.smul_apply, smul_eq_mul, wμ,
    wμ, withDensity_apply _ (Φ.symm.continuous.measurable hs), withDensity_apply _ hs,
    ← lintegral_indicator (Φ.symm.continuous.measurable hs),
    ← lintegral_indicator hs, ← lintegral_const_mul _ ((measurable_ofReal_weight ρ).indicator hs)]
  have e1 : ∀ x, (Φ.symm ⁻¹' s).indicator (fun x => ENNReal.ofReal (ρ.compHomeo Φ.symm x)) x =
      s.indicator (fun y => ENNReal.ofReal (ρ y)) (Φ.symm x) := by
    intro x
    classical
    simp only [Set.indicator_apply, Set.mem_preimage, Weight.compHomeo_apply]
  simp_rw [e1]
  rw [lintegral_comp_diffeo Φ hΦ (fun x => s.indicator (fun y => ENNReal.ofReal (ρ y))
    (Φ.symm x))]
  refine lintegral_mono fun y => ?_
  simp only [Homeomorph.symm_apply_apply]
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hC y)) (by simp)

include hΦ hC in
theorem ac_map_symm :
    Measure.map Φ.symm (wμ volume (ρ.compHomeo Φ.symm)) ≪ wμ volume ρ :=
  Measure.absolutelyContinuous_of_le_smul (map_symm_le Φ hΦ ρ hC)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞}

/-- The constant `max C 1 ^ (1/p)` of the composition bound. -/
def compConst (C : ℝ) (p : ℝ≥0∞) : ℝ≥0∞ := ENNReal.ofReal (max C 1) ^ (1 / p).toReal

theorem compConst_ne_top (C : ℝ) (p : ℝ≥0∞) : compConst C p ≠ ⊤ :=
  ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top

include hΦ hC in
theorem eLpNorm_comp_symm_le {f : Eucl n → F} (hf : AEStronglyMeasurable f (wμ volume ρ)) :
    eLpNorm (fun x => f (Φ.symm x)) p (wμ volume (ρ.compHomeo Φ.symm)) ≤
      compConst C p * eLpNorm f p (wμ volume ρ) := by
  have hC' : ∀ y, jac Φ y ≤ max C 1 := fun y => (hC y).trans (le_max_left _ _)
  have hle := map_symm_le Φ hΦ ρ hC'
  have hfm : AEStronglyMeasurable f (Measure.map Φ.symm (wμ volume (ρ.compHomeo Φ.symm))) :=
    hf.mono_ac (Measure.absolutelyContinuous_of_le_smul hle)
  have hΨm : AEMeasurable Φ.symm (wμ volume (ρ.compHomeo Φ.symm)) :=
    Φ.symm.continuous.measurable.aemeasurable
  have hne : ENNReal.ofReal (max C 1) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact lt_of_lt_of_le one_pos (le_max_right _ _)
  calc eLpNorm (fun x => f (Φ.symm x)) p (wμ volume (ρ.compHomeo Φ.symm))
      = eLpNorm f p (Measure.map Φ.symm (wμ volume (ρ.compHomeo Φ.symm))) :=
        (eLpNorm_map_measure hfm hΨm).symm
    _ ≤ eLpNorm f p (ENNReal.ofReal (max C 1) • wμ volume ρ) := eLpNorm_mono_measure f hle
    _ = compConst C p * eLpNorm f p (wμ volume ρ) := by
        rw [eLpNorm_smul_measure_of_ne_zero hne, smul_eq_mul, compConst]

include hΦ hC in
theorem memLp_comp_symm {f : Eucl n → F} (hf : MemLp f p (wμ volume ρ)) :
    MemLp (fun x => f (Φ.symm x)) p (wμ volume (ρ.compHomeo Φ.symm)) := by
  have hC' : ∀ y, jac Φ y ≤ max C 1 := fun y => (hC y).trans (le_max_left _ _)
  have hle := map_symm_le Φ hΦ ρ hC'
  have hfm : AEStronglyMeasurable f (Measure.map Φ.symm (wμ volume (ρ.compHomeo Φ.symm))) :=
    hf.1.mono_ac (Measure.absolutelyContinuous_of_le_smul hle)
  refine ⟨hfm.comp_aemeasurable Φ.symm.continuous.measurable.aemeasurable, ?_⟩
  exact (eLpNorm_comp_symm_le Φ hΦ ρ hC hf.1).trans_lt
    (ENNReal.mul_lt_top (compConst_ne_top C p).lt_top hf.2)

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] [Fact (1 ≤ p)]

include hΦ in
theorem ae_comp_symm_of_ae {P : Eucl n → Prop} (h : ∀ᵐ y ∂(wμ volume ρ), P y) :
    ∀ᵐ x ∂(wμ volume (ρ.compHomeo Φ.symm)), P (Φ.symm x) := by
  rw [ae_wμ_iff] at h ⊢
  exact ae_comp_symm Φ hΦ h

/-- **Composition with `Φ⁻¹`** on weighted `L^p`. -/
def compSymmL : Lp F p (wμ volume ρ) →L[𝕜] Lp F p (wμ volume (ρ.compHomeo Φ.symm)) :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_comp_symm Φ hΦ ρ hC (Lp.memLp f)).toLp _
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [(memLp_comp_symm Φ hΦ ρ hC (Lp.memLp (f + g))).coeFn_toLp,
          (memLp_comp_symm Φ hΦ ρ hC (Lp.memLp f)).coeFn_toLp,
          (memLp_comp_symm Φ hΦ ρ hC (Lp.memLp g)).coeFn_toLp,
          Lp.coeFn_add ((memLp_comp_symm Φ hΦ ρ hC (Lp.memLp f)).toLp _)
            ((memLp_comp_symm Φ hΦ ρ hC (Lp.memLp g)).toLp _),
          ae_comp_symm_of_ae Φ hΦ ρ (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
        simp only [h1, h2, h3, h4, h5, Pi.add_apply]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [(memLp_comp_symm Φ hΦ ρ hC (Lp.memLp (c • f))).coeFn_toLp,
          (memLp_comp_symm Φ hΦ ρ hC (Lp.memLp f)).coeFn_toLp,
          Lp.coeFn_smul c ((memLp_comp_symm Φ hΦ ρ hC (Lp.memLp f)).toLp _),
          ae_comp_symm_of_ae Φ hΦ ρ (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
        simp only [RingHom.id_apply, h1, h2, h3, h4, Pi.smul_apply] }
    (compConst C p).toReal fun f => by
      change ‖(memLp_comp_symm Φ hΦ ρ hC (Lp.memLp f)).toLp _‖ ≤ _
      rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top (compConst_ne_top C p) (Lp.eLpNorm_ne_top f))
        (eLpNorm_comp_symm_le Φ hΦ ρ hC (Lp.aestronglyMeasurable f))

theorem coeFn_compSymmL (f : Lp F p (wμ volume ρ)) :
    ⇑(compSymmL (𝕜 := 𝕜) Φ hΦ ρ hC f) =ᵐ[wμ volume (ρ.compHomeo Φ.symm)]
      fun x => f (Φ.symm x) := by
  simp only [compSymmL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  exact (memLp_comp_symm Φ hΦ ρ hC (Lp.memLp f)).coeFn_toLp

end Lp

section Mul

variable {μ : Measure (Eucl n)} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F]
  (a : Eucl n → ℝ) (ha : Continuous a) {B : ℝ} (hB : ∀ x, |a x| ≤ B)

include ha hB in
theorem memLp_smul_bdd {f : Eucl n → F} (hf : MemLp f p μ) : MemLp (fun x => a x • f x) p μ :=
  hf.of_le_mul (ha.aestronglyMeasurable.smul hf.1) (Eventually.of_forall fun x => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _))

/-- Multiplication by a bounded continuous real coefficient on `L^p`. -/
def mulL : Lp F p μ →L[𝕜] Lp F p μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_smul_bdd a ha hB (Lp.memLp f)).toLp _
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [(memLp_smul_bdd a ha hB (Lp.memLp (f + g))).coeFn_toLp,
          (memLp_smul_bdd a ha hB (Lp.memLp f)).coeFn_toLp,
          (memLp_smul_bdd a ha hB (Lp.memLp g)).coeFn_toLp,
          Lp.coeFn_add ((memLp_smul_bdd a ha hB (Lp.memLp f)).toLp _)
            ((memLp_smul_bdd a ha hB (Lp.memLp g)).toLp _),
          Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
        simp only [h1, h2, h3, h4, h5, Pi.add_apply, smul_add]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [(memLp_smul_bdd a ha hB (Lp.memLp (c • f))).coeFn_toLp,
          (memLp_smul_bdd a ha hB (Lp.memLp f)).coeFn_toLp,
          Lp.coeFn_smul c ((memLp_smul_bdd a ha hB (Lp.memLp f)).toLp _),
          Lp.coeFn_smul c f] with x h1 h2 h3 h4
        simp only [RingHom.id_apply, h1, h2, h3, h4, Pi.smul_apply]
        rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), RCLike.real_smul_eq_coe_smul (K := 𝕜),
          smul_smul, smul_smul, mul_comm] }
    B fun f => by
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [(memLp_smul_bdd a ha hB (Lp.memLp f)).coeFn_toLp] with x hx
      simp only [LinearMap.coe_mk, AddHom.coe_mk, hx, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

theorem coeFn_mulL (f : Lp F p μ) :
    ⇑(mulL (𝕜 := 𝕜) a ha hB f) =ᵐ[μ] fun x => a x • f x := by
  simp only [mulL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  exact (memLp_smul_bdd a ha hB (Lp.memLp f)).coeFn_toLp

end Mul

/-! ### The change of variables on `W` -/

section CompDiffeo

variable {F : Type*} [NormedAddCommGroup F] {𝕜 : Type*} [RCLike 𝕜] [InnerProductSpace 𝕜 F]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [FiniteDimensional 𝕜 F] {k : ℕ} {p : ℝ≥0∞}
  [Fact (1 ≤ p)] (ρ : Weight (Eucl n))

/-- The hypotheses of the change of variables (S6), bundled. -/
structure DiffeoData (n k : ℕ) where
  /-- The diffeomorphism. -/
  Φ : Eucl n ≃ₜ Eucl n
  smooth : ContDiff ℝ ∞ Φ
  smooth_symm : ContDiff ℝ ∞ Φ.symm
  /-- Bounded derivatives of `Φ⁻¹` of orders `1, …, k`. -/
  bdd : ∀ j, 1 ≤ j → j ≤ k → ∃ C, ∀ x, ‖iteratedFDeriv ℝ j Φ.symm x‖ ≤ C
  /-- Bounded Jacobian of `Φ`. -/
  jac_le : ∃ C, ∀ y, |(fderiv ℝ Φ y).det| ≤ C

variable (Θ : DiffeoData n k)

theorem DiffeoData.coef_bounded (w u : List (Fin n)) (hw : w.length ≤ k) :
    ∃ B, ∀ x, |coef Θ.Φ w u x| ≤ B :=
  (bddDerivs_coef Θ.Φ Θ.smooth_symm Θ.bdd w hw u).bounded

/-- The `L^p` coefficient operator `f ↦ coef Φ w u · f` (zero if `|w| > k`). -/
def DiffeoData.coefL (w u : List (Fin n)) {μ : Measure (Eucl n)} :
    Lp F p μ →L[𝕜] Lp F p μ :=
  if hw : w.length ≤ k then
    mulL (coef Θ.Φ w u) (contDiff_coef Θ.Φ Θ.smooth_symm w u).continuous
      (Classical.choose_spec (Θ.coef_bounded w u hw))
  else 0

/-- The weak derivative `∂^u` as a map `W → L^p` (zero if `|u| > k`). -/
def derivL (u : List (Fin n)) :
    W (wholeSpace n) ρ 𝕜 F k p →L[𝕜] Lp F p (wμ volume ρ) :=
  if h : u.length ≤ k then W.deriv (wholeSpace n) ρ 𝕜 F k p (Idx.ofList u h) else 0

/-- The components `∑_u coef Φ α u · (∂^u x) ∘ Φ⁻¹`. -/
def DiffeoData.component (α : Idx n k) :
    W (wholeSpace n) ρ 𝕜 F k p →L[𝕜] Lp F p (wμ volume (ρ.compHomeo Θ.Φ.symm)) :=
  ∑ u ∈ wordSet k, (Θ.coefL (Idx.toList α) u).comp
    ((compSymmL Θ.Φ Θ.smooth ρ (C := Classical.choose Θ.jac_le)
      (Classical.choose_spec Θ.jac_le)).comp (derivL ρ u))

variable {ρ}

theorem coeFn_component (α : Idx n k) (x : W (wholeSpace n) ρ 𝕜 F k p) :
    ⇑(Θ.component ρ α x) =ᵐ[wμ volume (ρ.compHomeo Θ.Φ.symm)] fun y =>
      ∑ u ∈ wordSet k, coef Θ.Φ (Idx.toList α) u y • (derivL ρ u x) (Θ.Φ.symm y) := by
  have hα : (Idx.toList α).length ≤ k := by
    rw [Idx.length_toList]; exact Nat.lt_succ_iff.mp α.1.2
  rw [DiffeoData.component, ContinuousLinearMap.sum_apply]
  have hterm : ∀ u ∈ wordSet k, ⇑(((Θ.coefL (Idx.toList α) u).comp
      ((compSymmL Θ.Φ Θ.smooth ρ (C := Classical.choose Θ.jac_le)
        (Classical.choose_spec Θ.jac_le)).comp (derivL ρ u))) x) =ᵐ[wμ volume
          (ρ.compHomeo Θ.Φ.symm)]
        fun y => coef Θ.Φ (Idx.toList α) u y • (derivL ρ u x) (Θ.Φ.symm y) := by
    intro u _
    simp only [ContinuousLinearMap.comp_apply, DiffeoData.coefL, dif_pos hα]
    filter_upwards [coeFn_mulL (𝕜 := 𝕜) (coef Θ.Φ (Idx.toList α) u)
        (contDiff_coef Θ.Φ Θ.smooth_symm _ u).continuous
        (Classical.choose_spec (Θ.coef_bounded _ u hα)) ((compSymmL (𝕜 := 𝕜) Θ.Φ Θ.smooth ρ
          (Classical.choose_spec Θ.jac_le)) (derivL ρ u x)),
      coeFn_compSymmL (𝕜 := 𝕜) Θ.Φ Θ.smooth ρ (Classical.choose_spec Θ.jac_le)
        (derivL ρ u x)] with y h1 h2
    simp only [h1, h2]
  filter_upwards [Lp.coeFn_finsetSum (wordSet k) (fun u => ((Θ.coefL (Idx.toList α) u).comp
      ((compSymmL Θ.Φ Θ.smooth ρ (C := Classical.choose Θ.jac_le)
        (Classical.choose_spec Θ.jac_le)).comp (derivL ρ u))) x),
    (Filter.eventually_all_finset (wordSet k)).mpr hterm] with y h1 h2
  rw [h1, Finset.sum_apply]
  exact Finset.sum_congr rfl fun u hu => h2 u hu

theorem derivL_of_le (u : List (Fin n)) (h : u.length ≤ k) (x : W (wholeSpace n) ρ 𝕜 F k p) :
    derivL ρ u x = W.deriv (wholeSpace n) ρ 𝕜 F k p (Idx.ofList u h) x := by
  have hd : derivL (𝕜 := 𝕜) (F := F) (k := k) (p := p) ρ u =
      W.deriv (wholeSpace n) ρ 𝕜 F k p (Idx.ofList u h) := dif_pos h
  rw [hd] <;> rfl

theorem derivL_nil (x : W (wholeSpace n) ρ 𝕜 F k p) :
    derivL ρ [] x = W.value (wholeSpace n) ρ 𝕜 F k p x := by
  rw [derivL_of_le [] (Nat.zero_le _), Idx.ofList_nil]
  rfl

theorem hasWeakDeriv_derivL (x : W (wholeSpace n) ρ 𝕜 F k p) (u : List (Fin n))
    (h : u.length ≤ k) :
    HasWeakDeriv (wholeSpace n) (u.map e) ⇑(derivL ρ [] x) ⇑(derivL ρ u x) := by
  have hw := W.hasWeakDeriv x (Idx.ofList u h)
  rw [TestDomain.word_eq_map, Idx.toList_ofList, wholeSpace_dir] at hw
  rw [derivL_of_le u h, derivL_nil]
  exact hw

theorem sum_coef_component_nil (x : W (wholeSpace n) ρ 𝕜 F k p) :
    ⇑(Θ.component ρ Idx.zero x) =ᵐ[wμ volume (ρ.compHomeo Θ.Φ.symm)]
      fun y => (derivL ρ [] x) (Θ.Φ.symm y) := by
  filter_upwards [coeFn_component Θ Idx.zero x] with y hy
  rw [hy, Idx.toList_zero]
  exact sum_coef_nil_smul Θ.Φ k (fun u => ⇑(derivL ρ u x)) y

theorem mem_SobSub_compDiffeo (x : W (wholeSpace n) ρ 𝕜 F k p) :
    (WithLp.toLp p (fun α => Θ.component ρ α x) : SobTuple (wholeSpace n)
      (ρ.compHomeo Θ.Φ.symm) F k p) ∈ SobSub (wholeSpace n) (ρ.compHomeo Θ.Φ.symm) 𝕜 F k p := by
  rw [mem_SobSub_iff]
  intro α
  have hα : (Idx.toList α).length ≤ k := by
    rw [Idx.length_toList]; exact Nat.lt_succ_iff.mp α.1.2
  have hgl : ∀ u : List (Fin n), u.length ≤ k →
      LocallyIntegrable (⇑(derivL ρ u x) : Eucl n → F) volume :=
    fun u _ => locallyIntegrable_of_memLp (Lp.memLp _)
  have main := hasWeakDeriv_comp_symm_word Θ.Φ Θ.smooth Θ.smooth_symm
    (fun u => ⇑(derivL ρ u x)) hgl (fun u hu => hasWeakDeriv_derivL x u hu) (Idx.toList α) hα
  rw [TestDomain.word_eq_map, wholeSpace_dir]
  refine main.congr_ae ?_ ?_
  · exact ((ae_eq_wμ_iff volume (ρ.compHomeo Θ.Φ.symm)).mp
      (sum_coef_component_nil Θ x)).symm
  · exact ((ae_eq_wμ_iff volume (ρ.compHomeo Θ.Φ.symm)).mp (coeFn_component Θ α x)).symm

/-- The change of variables `x ↦ x ∘ Φ⁻¹` on `W` for bundled hypotheses. -/
def DiffeoData.compW : W (wholeSpace n) ρ 𝕜 F k p →L[𝕜]
    W (wholeSpace n) (ρ.compHomeo Θ.Φ.symm) 𝕜 F k p :=
  (((PiLp.continuousLinearEquiv p 𝕜 (fun _ : Idx n k =>
      Lp F p (wμ (wholeSpace n).μ (ρ.compHomeo Θ.Φ.symm)))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun α => Θ.component ρ α))).codRestrict _
    (mem_SobSub_compDiffeo Θ)

theorem DiffeoData.deriv_compW (x : W (wholeSpace n) ρ 𝕜 F k p) (α : Idx n k) :
    W.deriv (wholeSpace n) (ρ.compHomeo Θ.Φ.symm) 𝕜 F k p α (Θ.compW x) =
      Θ.component ρ α x := rfl

end CompDiffeo

section Main

variable {F : Type*} [NormedAddCommGroup F] {𝕜 : Type*} [RCLike 𝕜] [InnerProductSpace 𝕜 F]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [FiniteDimensional 𝕜 F] {k : ℕ} {p : ℝ≥0∞}
  [Fact (1 ≤ p)] {ρ : Weight (Eucl n)}

/-- **Change of variables on `W`** (S6): for a homeomorphism `Φ` of `ℝⁿ` with `Φ`, `Φ⁻¹`
smooth, the derivatives of `Φ⁻¹` of orders `1, …, k` bounded and the Jacobian of `Φ` bounded,
`x ↦ x ∘ Φ⁻¹` is a continuous linear map `W^{k,p}(ρ) → W^{k,p}(ρ ∘ Φ⁻¹)`. -/
def W.compDiffeo (Φ : Eucl n ≃ₜ Eucl n) (hΦ : ContDiff ℝ ∞ Φ) (hΨ : ContDiff ℝ ∞ Φ.symm)
    (hbd : ∀ j, 1 ≤ j → j ≤ k → ∃ C, ∀ x, ‖iteratedFDeriv ℝ j Φ.symm x‖ ≤ C)
    (hjac : ∃ C, ∀ y, |(fderiv ℝ Φ y).det| ≤ C) :
    W (wholeSpace n) ρ 𝕜 F k p →L[𝕜] W (wholeSpace n) (ρ.compHomeo Φ.symm) 𝕜 F k p :=
  DiffeoData.compW (⟨Φ, hΦ, hΨ, hbd, hjac⟩ : DiffeoData n k)

/-- The field of `W.compDiffeo … x` is `x ∘ Φ⁻¹`. -/
theorem W.value_compDiffeo (Φ : Eucl n ≃ₜ Eucl n) (hΦ : ContDiff ℝ ∞ Φ)
    (hΨ : ContDiff ℝ ∞ Φ.symm)
    (hbd : ∀ j, 1 ≤ j → j ≤ k → ∃ C, ∀ x, ‖iteratedFDeriv ℝ j Φ.symm x‖ ≤ C)
    (hjac : ∃ C, ∀ y, |(fderiv ℝ Φ y).det| ≤ C) (x : W (wholeSpace n) ρ 𝕜 F k p) :
    ⇑(W.value (wholeSpace n) (ρ.compHomeo Φ.symm) 𝕜 F k p (W.compDiffeo Φ hΦ hΨ hbd hjac x))
      =ᵐ[volume] fun y => W.value (wholeSpace n) ρ 𝕜 F k p x (Φ.symm y) := by
  have h := sum_coef_component_nil (⟨Φ, hΦ, hΨ, hbd, hjac⟩ : DiffeoData n k) x
  rw [derivL_nil] at h
  exact (ae_eq_wμ_iff volume (ρ.compHomeo Φ.symm)).mp h

/-- The derivatives of `W.compDiffeo … x`: `∂^α (x ∘ Φ⁻¹) = ∑_{|u| ≤ k} coef Φ α u · (∂^u x) ∘ Φ⁻¹`. -/
theorem W.deriv_compDiffeo (Φ : Eucl n ≃ₜ Eucl n) (hΦ : ContDiff ℝ ∞ Φ)
    (hΨ : ContDiff ℝ ∞ Φ.symm)
    (hbd : ∀ j, 1 ≤ j → j ≤ k → ∃ C, ∀ x, ‖iteratedFDeriv ℝ j Φ.symm x‖ ≤ C)
    (hjac : ∃ C, ∀ y, |(fderiv ℝ Φ y).det| ≤ C) (x : W (wholeSpace n) ρ 𝕜 F k p)
    (α : Idx n k) :
    ⇑(W.deriv (wholeSpace n) (ρ.compHomeo Φ.symm) 𝕜 F k p α (W.compDiffeo Φ hΦ hΨ hbd hjac x))
      =ᵐ[volume] fun y => ∑ u ∈ wordSet k, coef Φ (Idx.toList α) u y •
        (derivL ρ u x) (Φ.symm y) :=
  (ae_eq_wμ_iff volume (ρ.compHomeo Φ.symm)).mp
    (coeFn_component (⟨Φ, hΦ, hΨ, hbd, hjac⟩ : DiffeoData n k) α x)

end Main


end UnforcedLeray.Sob
