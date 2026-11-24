import UnforcedLeray.Units.B0062.ChainRule
import UnforcedLeray.Units.B0008

/-!
# B0062: the transport group and its polynomial bound on `H^j_M`

Blueprint unit **B0062**, label `eq:st18-t00051`, `paper/main.tex` lines 1228–1237
(proof of "Generator realization and resolvent estimates", §"The weighted generator").

**Statement** (`paper/main.tex:1228-1237`). Let `D_E = Ω∂_ϑ`. Its explicit group is
`T(t)f(r,ϑ) = f(r, ϑ - Ω(r)t)` (`eq:st18-t00050`). The flow preserves area and every radial
weight. Its Cartesian derivatives through order `j` grow at most polynomially in `|t|`, of
degree `j`. The chain rule gives `‖T(t)‖_{H^j_M → H^j_M} ≤ C_j (1+|t|)^j` (`eq:st18-t00051`).

**Formalization.**
* `Omega`, `flow` (helper `B0062/Flow.lean`): `Ω(r) = e^{-r²/4}` (B0006, bridged by
  `omegaR_eq_planarGaussian`), `flow t y = e^{-iΩ(|y|)t} y`; `flow_polar` is
  `(r, ϑ) ↦ (r, ϑ - Ω(r)t)`; `flow_flow`, `flow_zero` the group law.
* Area and radial weights: `measurePreserving_flow`, `norm_flow`,
  `measurePreserving_flow_withDensity`, `measurePreserving_flow_wMeasure`.
* Derivatives of the flow: `norm_iteratedFDeriv_flow_le` (`‖D^n Φ_t‖ ≤ C_n (1+|t|)^n`, `n ≥ 1`).
* `transport j M t : H^j_M →L[ℂ] H^j_M` (space of B0008, any real `M`; the manuscript's `M > 1`
  is not needed): `transport_value` (`T(t)f = f ∘ Φ_t` a.e.), `transport_add`, `transport_zero`
  (group law), and **`norm_transport_le`**: `∃ C_j, ‖T(t)‖ ≤ C_j (1+|t|)^j` for all `t ∈ ℝ`.
* The chain rule is distributional (helper `B0062/ChainRule.lean`). For `|α| ≤ j`,
  `∂^α (f ∘ Φ_t) = ∑ c_{p}(t) (∂^{γ_p} f) ∘ Φ_t` weakly (`hasWeakDeriv_terms`), with coefficient
  families `c_p` built recursively (`terms`) whose derivatives grow like `(1+|t|)^{|α|+n}`
  (`PolyBd`, helper `B0062/Bounds.lean`; Gaussian decay of `Ω` enters there).

Reference formalization consulted: `NonUniqueEuler/lean/NonUniqueEuler/H/Sec4/
SemigroupConstruct/TransportY.lean` (`measurePreserving_rot_radial`, adapted in `Flow.lean`).
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff ENNReal NNReal
open Set MeasureTheory NonUniqueEuler.Sob NonUniqueEuler.Sob.WeakDerivAux UnforcedLeray.B0008

namespace UnforcedLeray.B0062

/-! ### The flow as a smooth area-preserving diffeomorphism -/

theorem smoothMP_flow (t : ℝ) : SmoothMP (flow t) (flow (-t)) :=
  ⟨contDiff_flow t, contDiff_flow (-t), flow_neg_flow t, flow_flow_neg t,
    measurePreserving_flow t⟩

/-- The weight `⟨y⟩^{2M}` of B0008 as a function of `|y|`. -/
def radialDensity (M : ℝ) (r : ℝ) : ℝ≥0∞ := ((Real.toNNReal ((1 + r ^ 2) ^ M) : ℝ≥0) : ℝ≥0∞)

theorem wMeasure_eq_radial (M : ℝ) :
    wMeasure M = volume.withDensity fun y => radialDensity M ‖y‖ := rfl

/-- The flow preserves the weighted measure `⟨y⟩^{2M} dy` of `H^j_M` (radial weight). -/
theorem measurePreserving_flow_wMeasure (M t : ℝ) :
    MeasurePreserving (flow t) (wMeasure M) (wMeasure M) := by
  rw [wMeasure_eq_radial]
  refine measurePreserving_flow_withDensity t ?_
  exact ((measurable_const.add (measurable_id.pow_const 2)).pow_const M).real_toNNReal
    |>.coe_nnreal_ennreal

theorem ae_comp_flow (t : ℝ) {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) :
    (fun y => f (flow t y)) =ᵐ[volume] fun y => g (flow t y) :=
  (measurePreserving_flow t).quasiMeasurePreserving.ae_eq_comp h

/-! ### Coefficient families of the iterated chain rule -/

/-- A family of coefficients `c t : ℂ → ℂ`, `t ∈ ℝ`. -/
abbrev Coef : Type := ℝ → ℂ → ℂ

/-- `Re(DΦ_t(y) v)`. -/
def bRe (v : ℂ) : Coef := fun t y => ((fderiv ℝ (flow t) y v).re : ℂ)

/-- `Im(DΦ_t(y) v)`. -/
def bIm (v : ℂ) : Coef := fun t y => ((fderiv ℝ (flow t) y v).im : ℂ)

theorem polyBd_bRe (v : ℂ) : PolyBd 1 (bRe v) := by
  have := (polyBd_fderiv_flow v).clm_comp (Complex.ofRealCLM.comp Complex.reCLM)
  simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.ofRealCLM_apply] at this
  exact this

theorem polyBd_bIm (v : ℂ) : PolyBd 1 (bIm v) := by
  have := (polyBd_fderiv_flow v).clm_comp (Complex.ofRealCLM.comp Complex.imCLM)
  simp only [ContinuousLinearMap.comp_apply, Complex.imCLM_apply, Complex.ofRealCLM_apply] at this
  exact this

/-- One chain-rule step in direction `v` applied to the term `c · (∂^γ f) ∘ Φ_t`:
`(∂_v c) (∂^γ f)∘Φ + c Re(DΦ v) (∂₁∂^γ f)∘Φ + c Im(DΦ v) (∂₂∂^γ f)∘Φ`. -/
def step (v : ℂ) (p : Coef × (ℕ × ℕ)) : List (Coef × (ℕ × ℕ)) :=
  [(fun t y => dirDeriv v (p.1 t) y, p.2),
   (fun t y => p.1 t y * bRe v t y, (p.2.1 + 1, p.2.2)),
   (fun t y => p.1 t y * bIm v t y, (p.2.1, p.2.2 + 1))]

/-- The terms of `∂_{vs}(f ∘ Φ_t) = ∑ c (∂^γ f) ∘ Φ_t`. -/
def terms : List ℂ → List (Coef × (ℕ × ℕ))
  | [] => [(fun _ _ => 1, (0, 0))]
  | v :: vs => (terms vs).flatMap (step v)

/-- Each term of `terms vs` has `|γ| ≤ |vs|` and a coefficient of polynomial degree `|vs|`. -/
theorem terms_spec : ∀ (vs : List ℂ), ∀ p ∈ terms vs,
    p.2.1 + p.2.2 ≤ vs.length ∧ PolyBd vs.length p.1
  | [] => by
    intro p hp
    simp only [terms, List.mem_singleton] at hp
    subst hp
    exact ⟨le_refl _, PolyBd.of_cbInf (CbInf.const (E := ℂ) (1 : ℂ))⟩
  | v :: vs => by
    intro p hp
    simp only [terms, List.mem_flatMap] at hp
    obtain ⟨q, hq, hpq⟩ := hp
    obtain ⟨h1, h2⟩ := terms_spec vs q hq
    simp only [step, List.mem_cons, List.not_mem_nil, or_false] at hpq
    rcases hpq with rfl | rfl | rfl
    · exact ⟨by simp only [List.length_cons]; omega, h2.dirDeriv v⟩
    · exact ⟨by simp only [List.length_cons]; omega, h2.mul (polyBd_bRe v)⟩
    · exact ⟨by simp only [List.length_cons]; omega, h2.mul (polyBd_bIm v)⟩

theorem step_continuous (v : ℂ) (t : ℝ) (p : Coef × (ℕ × ℕ)) (hp : ContDiff ℝ ∞ (p.1 t)) :
    ∀ q ∈ step v p, Continuous (q.1 t) := by
  intro q hq
  simp only [step, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact (contDiff_dirDeriv hp v).continuous
  · exact hp.continuous.mul ((polyBd_bRe v).1 t).continuous
  · exact hp.continuous.mul ((polyBd_bIm v).1 t).continuous

/-- A uniform sup bound for a list of `PolyBd d` coefficients. -/
theorem exists_uniform_bound (d : ℕ) : ∀ L : List (Coef × (ℕ × ℕ)), (∀ p ∈ L, PolyBd d p.1) →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p ∈ L, ∀ t y, ‖p.1 t y‖ ≤ K * (1 + |t|) ^ d
  | [], _ => ⟨0, le_rfl, fun p hp => by simp at hp⟩
  | p :: L, hL => by
    obtain ⟨K₁, hK₁, h₁⟩ := (hL p List.mem_cons_self).norm_le
    obtain ⟨K₂, hK₂, h₂⟩ := exists_uniform_bound d L fun q hq => hL q (List.mem_cons_of_mem _ hq)
    refine ⟨K₁ + K₂, by positivity, fun q hq t y => ?_⟩
    have hT : 0 ≤ (1 + |t|) ^ d := by positivity
    rcases List.mem_cons.1 hq with rfl | hq
    · nlinarith [h₁ t y]
    · nlinarith [h₂ q hq t y]

/-- One constant for all multi-indices `|α| ≤ j`: number of terms and coefficient sup bounds
`‖c_p(t)‖ ≤ C (1+|t|)^j`. -/
theorem exists_terms_const (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ α ∈ multiIdx j,
    ((terms (pdList α)).length : ℝ) ≤ C ∧
      ∀ p ∈ terms (pdList α), ∀ t y, ‖p.1 t y‖ ≤ C * (1 + |t|) ^ j := by
  have hα : ∀ α : ℕ × ℕ, ∃ K : ℝ, 0 ≤ K ∧ (α.1 + α.2 ≤ j →
      ∀ p ∈ terms (pdList α), ∀ t y, ‖p.1 t y‖ ≤ K * (1 + |t|) ^ j) := by
    intro α
    obtain ⟨K, hK, hb⟩ := exists_uniform_bound (pdList α).length (terms (pdList α))
      fun p hp => (terms_spec _ p hp).2
    refine ⟨K, hK, fun hj p hp t y => (hb p hp t y).trans ?_⟩
    refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_one_add_abs t) ?_) hK
    simpa using hj
  choose K hK0 hK using hα
  refine ⟨∑ α ∈ multiIdx j, (K α + (terms (pdList α)).length), Finset.sum_nonneg fun α _ => by
    have := hK0 α; positivity, fun α hαj => ⟨?_, fun p hp t y => ?_⟩⟩
  · have := Finset.single_le_sum (f := fun α => K α + ((terms (pdList α)).length : ℝ))
      (fun β _ => by have := hK0 β; positivity) hαj
    have := hK0 α
    linarith
  · have h1 := hK α (mem_multiIdx.1 hαj) p hp t y
    have h2 := Finset.single_le_sum (f := fun α => K α + ((terms (pdList α)).length : ℝ))
      (fun β _ => by have := hK0 β; positivity) hαj
    have hT : 0 ≤ (1 + |t|) ^ j := by positivity
    have : K α ≤ ∑ α ∈ multiIdx j, (K α + ((terms (pdList α)).length : ℝ)) := by
      have : (0 : ℝ) ≤ (terms (pdList α)).length := Nat.cast_nonneg _
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_right this hT)

/-! ### The derivatives of an element of `H^j_M`, as a total family -/

variable {j : ℕ} {M : ℝ}

/-- `γ ↦ ∂^γ f` for `|γ| ≤ j` (and `0` otherwise). -/
def fam (F : HjM j M) (γ : ℕ × ℕ) : ℂ → ℂ :=
  if h : γ ∈ multiIdx j then (F.der ⟨γ, h⟩ : ℂ → ℂ) else 0

theorem fam_of_mem (F : HjM j M) {γ : ℕ × ℕ} (h : γ ∈ multiIdx j) :
    fam F γ = (F.der ⟨γ, h⟩ : ℂ → ℂ) := dif_pos h

theorem fam_zero_idx (F : HjM j M) : fam F (0, 0) = (F.value : ℂ → ℂ) :=
  fam_of_mem F (zero_mem_multiIdx j)

theorem locallyIntegrable_fam (F : HjM j M) (γ : ℕ × ℕ) : LocallyIntegrable (fam F γ) := by
  unfold fam
  split_ifs
  · exact locallyIntegrable_L2w M _
  · exact locallyIntegrable_zero

theorem memLp_fam (F : HjM j M) (γ : ℕ × ℕ) : MemLp (fam F γ) 2 (wMeasure M) := by
  unfold fam
  split_ifs
  · exact Lp.memLp _
  · exact MemLp.zero

theorem eLpNorm_fam_le (F : HjM j M) (γ : ℕ × ℕ) :
    eLpNorm (fam F γ) 2 (wMeasure M) ≤ ENNReal.ofReal ‖F‖ := by
  unfold fam
  split_ifs with h
  · rw [← Lp.enorm_def, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le (F : Tuple j M) ⟨γ, h⟩)
  · rw [eLpNorm_zero]
    exact zero_le

theorem memLp_fam_comp (F : HjM j M) (γ : ℕ × ℕ) (t : ℝ) :
    MemLp (fun y => fam F γ (flow t y)) 2 (wMeasure M) :=
  (memLp_fam F γ).comp_measurePreserving (measurePreserving_flow_wMeasure M t)

theorem eLpNorm_fam_comp_le (F : HjM j M) (γ : ℕ × ℕ) (t : ℝ) :
    eLpNorm (fun y => fam F γ (flow t y)) 2 (wMeasure M) ≤ ENNReal.ofReal ‖F‖ := by
  have := eLpNorm_comp_measurePreserving (p := 2) (memLp_fam F γ).1
    (measurePreserving_flow_wMeasure M t)
  exact (le_of_eq this).trans (eLpNorm_fam_le F γ)

/-- From `∂^α f = g` and `∂^β f = h` with `∂^β = ∂_w ∂^α`, get `∂_w g = h` weakly. -/
theorem hasWeakDeriv_of_perm {f g h : ℂ → ℂ} {α β : ℕ × ℕ} {w : ℂ}
    (hα : HasWeakDerivOn univ (pdList α) f g) (hβ : HasWeakDerivOn univ (pdList β) f h)
    (hp : (pdList α ++ [w]).Perm (pdList β)) : HasWeakDerivOn univ [w] g h := by
  intro φ hφ
  have e1 := hα _ (hφ.dirDeriv w)
  have e2 := hβ φ hφ
  rw [← iterDirDeriv_perm hp hφ.smooth, iterDirDeriv_append] at e2
  have hlen : (pdList β).length = (pdList α).length + 1 := by
    rw [← hp.length_eq, List.length_append, List.length_singleton]
  rw [hlen] at e2
  rw [iterDirDeriv_single]
  simp only [List.length_singleton, pow_one]
  have key := e1.symm.trans e2
  rw [pow_succ, mul_assoc] at key
  exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) key

theorem perm_one (γ : ℕ × ℕ) : (pdList γ ++ [1]).Perm (pdList (γ.1 + 1, γ.2)) := by
  have e : pdList (γ.1 + 1, γ.2) = 1 :: pdList γ := by
    simp [pdList, List.replicate_succ]
  rw [e]
  exact List.perm_append_singleton 1 (pdList γ)

theorem perm_I (γ : ℕ × ℕ) : (pdList γ ++ [Complex.I]).Perm (pdList (γ.1, γ.2 + 1)) := by
  have e : pdList (γ.1, γ.2 + 1) = pdList γ ++ [Complex.I] := by
    simp [pdList, List.replicate_succ', List.append_assoc]
  rw [e]

theorem fam_deriv_one (F : HjM j M) {γ : ℕ × ℕ} (hγ : γ.1 + γ.2 < j) :
    HasWeakDerivOn univ [1] (fam F γ) (fam F (γ.1 + 1, γ.2)) := by
  have h1 : γ ∈ multiIdx j := mem_multiIdx.2 (by omega)
  have h2 : (γ.1 + 1, γ.2) ∈ multiIdx j := mem_multiIdx.2 (by simp only; omega)
  rw [fam_of_mem F h1, fam_of_mem F h2]
  exact hasWeakDeriv_of_perm (F.hasWeakDeriv ⟨γ, h1⟩) (F.hasWeakDeriv ⟨_, h2⟩) (perm_one γ)

theorem fam_deriv_I (F : HjM j M) {γ : ℕ × ℕ} (hγ : γ.1 + γ.2 < j) :
    HasWeakDerivOn univ [Complex.I] (fam F γ) (fam F (γ.1, γ.2 + 1)) := by
  have h1 : γ ∈ multiIdx j := mem_multiIdx.2 (by omega)
  have h2 : (γ.1, γ.2 + 1) ∈ multiIdx j := mem_multiIdx.2 (by simp only; omega)
  rw [fam_of_mem F h1, fam_of_mem F h2]
  exact hasWeakDeriv_of_perm (F.hasWeakDeriv ⟨γ, h1⟩) (F.hasWeakDeriv ⟨_, h2⟩) (perm_I γ)

/-! ### The iterated distributional chain rule -/

/-- `∑_{p ∈ L} c_p(t, y) (∂^{γ_p} f)(Φ_t y)`. -/
def termSum (F : HjM j M) (t : ℝ) (L : List (Coef × (ℕ × ℕ))) (y : ℂ) : ℂ :=
  (L.map fun p => p.1 t y * fam F p.2 (flow t y)).sum

theorem termSum_nil (F : HjM j M) (t : ℝ) : termSum F t [] = 0 := by
  funext y
  simp [termSum]

theorem termSum_cons (F : HjM j M) (t : ℝ) (p : Coef × (ℕ × ℕ)) (L : List (Coef × (ℕ × ℕ))) :
    termSum F t (p :: L) = (fun y => p.1 t y * fam F p.2 (flow t y)) + termSum F t L := by
  funext y
  simp [termSum]

theorem termSum_append (F : HjM j M) (t : ℝ) (L L' : List (Coef × (ℕ × ℕ))) :
    termSum F t (L ++ L') = termSum F t L + termSum F t L' := by
  funext y
  simp [termSum]

theorem locallyIntegrable_termSum (F : HjM j M) (t : ℝ) :
    ∀ L : List (Coef × (ℕ × ℕ)), (∀ p ∈ L, Continuous (p.1 t)) →
      LocallyIntegrable (termSum F t L)
  | [], _ => by
    rw [termSum_nil]
    exact locallyIntegrable_zero
  | p :: L, hL => by
    rw [termSum_cons]
    exact (locallyIntegrable_cont_mul (hL p List.mem_cons_self)
      ((smoothMP_flow t).locallyIntegrable_comp (locallyIntegrable_fam F p.2))).add
      (locallyIntegrable_termSum F t L fun q hq => hL q (List.mem_cons_of_mem _ hq))

/-- The chain rule for one term (`hasWeakDeriv_comp` and `hasWeakDeriv_mul_smooth`). -/
theorem hasWeakDeriv_term (F : HjM j M) (t : ℝ) (v : ℂ) (p : Coef × (ℕ × ℕ))
    (hc : ContDiff ℝ ∞ (p.1 t)) (hγ : p.2.1 + p.2.2 < j) :
    HasWeakDerivOn univ [v] (fun y => p.1 t y * fam F p.2 (flow t y))
      (termSum F t (step v p)) := by
  have hS := smoothMP_flow t
  have hch := hS.hasWeakDeriv_comp (locallyIntegrable_fam F p.2) (locallyIntegrable_fam F _)
    (locallyIntegrable_fam F _) (fam_deriv_one F hγ) (fam_deriv_I F hγ) v
  have hloc_g : LocallyIntegrable (fun y => ((fderiv ℝ (flow t) y v).re : ℂ) *
      fam F (p.2.1 + 1, p.2.2) (flow t y) +
      ((fderiv ℝ (flow t) y v).im : ℂ) * fam F (p.2.1, p.2.2 + 1) (flow t y)) :=
    (locallyIntegrable_cont_mul ((polyBd_bRe v).1 t).continuous
      (hS.locallyIntegrable_comp (locallyIntegrable_fam F _))).add
      (locallyIntegrable_cont_mul ((polyBd_bIm v).1 t).continuous
        (hS.locallyIntegrable_comp (locallyIntegrable_fam F _)))
  have hl := hasWeakDeriv_mul_smooth (hS.locallyIntegrable_comp (locallyIntegrable_fam F p.2))
    hloc_g hc hch
  convert hl using 1
  funext y
  simp only [termSum, step, bRe, bIm, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

theorem hasWeakDeriv_termSum_step (F : HjM j M) (t : ℝ) (v : ℂ) :
    ∀ L : List (Coef × (ℕ × ℕ)), (∀ p ∈ L, ContDiff ℝ ∞ (p.1 t) ∧ p.2.1 + p.2.2 < j) →
      HasWeakDerivOn univ [v] (termSum F t L) (termSum F t (L.flatMap (step v)))
  | [], _ => by
    intro φ _
    simp [termSum]
  | p :: L, hL => by
    have hp := hL p List.mem_cons_self
    have hL' : ∀ q ∈ L, ContDiff ℝ ∞ (q.1 t) ∧ q.2.1 + q.2.2 < j :=
      fun q hq => hL q (List.mem_cons_of_mem _ hq)
    have ih := hasWeakDeriv_termSum_step F t v L hL'
    have h1 := hasWeakDeriv_term F t v p hp.1 hp.2
    have hc1 : ∀ q ∈ step v p, Continuous (q.1 t) := step_continuous v t p hp.1
    have hc2 : ∀ q ∈ L.flatMap (step v), Continuous (q.1 t) := by
      intro q hq
      obtain ⟨r, hr, hqr⟩ := List.mem_flatMap.1 hq
      exact step_continuous v t r (hL' r hr).1 q hqr
    have hcL : ∀ q ∈ L, Continuous (q.1 t) := fun q hq => (hL' q hq).1.continuous
    rw [termSum_cons, List.flatMap_cons, termSum_append]
    exact HasWeakDerivOn.add isOpen_univ
      ((locallyIntegrable_cont_mul hp.1.continuous
        ((smoothMP_flow t).locallyIntegrable_comp (locallyIntegrable_fam F p.2))).locallyIntegrableOn
          univ)
      ((locallyIntegrable_termSum F t L hcL).locallyIntegrableOn univ)
      ((locallyIntegrable_termSum F t _ hc1).locallyIntegrableOn univ)
      ((locallyIntegrable_termSum F t _ hc2).locallyIntegrableOn univ) h1 ih

/-- **Iterated distributional chain rule**: for `|vs| ≤ j`,
`∂_{vs}(f ∘ Φ_t) = ∑_{p ∈ terms vs} c_p(t) (∂^{γ_p} f) ∘ Φ_t` weakly. -/
theorem hasWeakDeriv_terms (F : HjM j M) (t : ℝ) :
    ∀ vs : List ℂ, vs.length ≤ j →
      HasWeakDerivOn univ vs (fun y => F.value (flow t y)) (termSum F t (terms vs))
  | [], _ => by
    intro φ _
    simp [termSum, terms, fam_zero_idx]
  | v :: vs, hlen => by
    have hlen' : vs.length < j := by simp only [List.length_cons] at hlen; omega
    have ih := hasWeakDeriv_terms F t vs hlen'.le
    have hstep := hasWeakDeriv_termSum_step F t v (terms vs) fun p hp =>
      ⟨(terms_spec vs p hp).2.1 t, lt_of_le_of_lt (terms_spec vs p hp).1 hlen'⟩
    exact ih.trans hstep

/-- `L²(⟨y⟩^{2M})` bound of a sum of terms with coefficients bounded by `B`. -/
theorem termSum_bound (F : HjM j M) (t : ℝ) (B : ℝ) (hB : 0 ≤ B) :
    ∀ L : List (Coef × (ℕ × ℕ)), (∀ p ∈ L, Continuous (p.1 t) ∧ ∀ y, ‖p.1 t y‖ ≤ B) →
      MemLp (termSum F t L) 2 (wMeasure M) ∧
        eLpNorm (termSum F t L) 2 (wMeasure M) ≤ ENNReal.ofReal (L.length * B * ‖F‖)
  | [], _ => by
    rw [termSum_nil, eLpNorm_zero]
    exact ⟨MemLp.zero, zero_le⟩
  | p :: L, hL => by
    obtain ⟨ihm, ihb⟩ := termSum_bound F t B hB L fun q hq => hL q (List.mem_cons_of_mem _ hq)
    obtain ⟨hc, hb⟩ := hL p List.mem_cons_self
    have hm := memLp_fam_comp F p.2 t
    have hle : ∀ᵐ y ∂(wMeasure M),
        ‖p.1 t y * fam F p.2 (flow t y)‖ ≤ B * ‖fam F p.2 (flow t y)‖ :=
      Filter.Eventually.of_forall fun y => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hb y) (norm_nonneg _)
    have hmeas : AEStronglyMeasurable (fun y => p.1 t y * fam F p.2 (flow t y)) (wMeasure M) :=
      hc.aestronglyMeasurable.mul hm.1
    have hm1 : MemLp (fun y => p.1 t y * fam F p.2 (flow t y)) 2 (wMeasure M) :=
      hm.of_le_mul hmeas hle
    have hb1 : eLpNorm (fun y => p.1 t y * fam F p.2 (flow t y)) 2 (wMeasure M) ≤
        ENNReal.ofReal B * ENNReal.ofReal ‖F‖ :=
      (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hle 2).trans
        (mul_le_mul_of_nonneg_left (eLpNorm_fam_comp_le F p.2 t) zero_le)
    rw [termSum_cons]
    refine ⟨hm1.add ihm, (eLpNorm_add_le hmeas ihm.1 (by norm_num)).trans ?_⟩
    calc _ ≤ ENNReal.ofReal B * ENNReal.ofReal ‖F‖ + ENNReal.ofReal (L.length * B * ‖F‖) :=
          add_le_add hb1 ihb
      _ = ENNReal.ofReal ((p :: L).length * B * ‖F‖) := by
        rw [← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

/-! ### The transport group on `H^j_M` -/

/-- The constant of `exists_terms_const`. -/
def termsConst (j : ℕ) : ℝ := Classical.choose (exists_terms_const j)

theorem termsConst_spec (j : ℕ) : 0 ≤ termsConst j ∧ ∀ α ∈ multiIdx j,
    ((terms (pdList α)).length : ℝ) ≤ termsConst j ∧
      ∀ p ∈ terms (pdList α), ∀ t y, ‖p.1 t y‖ ≤ termsConst j * (1 + |t|) ^ j :=
  Classical.choose_spec (exists_terms_const j)

theorem memHjM_comp (F : HjM j M) (t : ℝ) : MemHjM j M (fun y => F.value (flow t y)) := by
  have hC := termsConst_spec j
  refine ⟨(memLp_wMeasure_iff M).1
    ((Lp.memLp F.value).comp_measurePreserving (measurePreserving_flow_wMeasure M t)),
    fun α hα => ⟨termSum F t (terms (pdList α)), ?_, ?_⟩⟩
  · refine (memLp_wMeasure_iff M).1 (termSum_bound F t (termsConst j * (1 + |t|) ^ j)
      (by have := hC.1; positivity) _ fun p hp =>
        ⟨((terms_spec _ p hp).2.1 t).continuous, fun y => (hC.2 α hα).2 p hp t y⟩).1
  · exact hasWeakDeriv_terms F t (pdList α) (by simpa using mem_multiIdx.1 hα)

/-- `T(t)F`: the element of `H^j_M` with function `f ∘ Φ_t`. -/
def transportFun (t : ℝ) (F : HjM j M) : HjM j M := HjM.ofMemHjM (memHjM_comp F t)

theorem transportFun_value (t : ℝ) (F : HjM j M) :
    ((transportFun t F).value : ℂ → ℂ) =ᵐ[volume] fun y => F.value (flow t y) :=
  HjM.value_ofMemHjM _

theorem L2w_eq_of_ae {F G : L2w M} (h : (F : ℂ → ℂ) =ᵐ[volume] G) : F = G :=
  Lp.ext ((wMeasure_ac M).ae_le h)

theorem transportFun_add (t : ℝ) (F G : HjM j M) :
    transportFun t (F + G) = transportFun t F + transportFun t G := by
  apply HjM.ext
  apply L2w_eq_of_ae
  have h2 : ((F + G).value : ℂ → ℂ) =ᵐ[volume] fun y => F.value y + G.value y :=
    (volume_ac M).ae_le (Lp.coeFn_add F.value G.value)
  have h6 : ((transportFun t F + transportFun t G).value : ℂ → ℂ) =ᵐ[volume]
      fun y => (transportFun t F).value y + (transportFun t G).value y :=
    (volume_ac M).ae_le (Lp.coeFn_add _ _)
  filter_upwards [transportFun_value t (F + G), ae_comp_flow t h2, transportFun_value t F,
    transportFun_value t G, h6] with y e1 e3 e4 e5 e6
  rw [e1, e3, e6, e4, e5]

theorem transportFun_smul (t : ℝ) (c : ℂ) (F : HjM j M) :
    transportFun t (c • F) = c • transportFun t F := by
  apply HjM.ext
  apply L2w_eq_of_ae
  have h2 : ((c • F).value : ℂ → ℂ) =ᵐ[volume] fun y => c • F.value y :=
    (volume_ac M).ae_le (Lp.coeFn_smul c F.value)
  have h6 : ((c • transportFun t F).value : ℂ → ℂ) =ᵐ[volume]
      fun y => c • (transportFun t F).value y :=
    (volume_ac M).ae_le (Lp.coeFn_smul _ _)
  filter_upwards [transportFun_value t (c • F), ae_comp_flow t h2, transportFun_value t F, h6]
    with y e1 e3 e4 e6
  rw [e1, e3, e6, e4]

/-- The derivatives of `T(t)F` are the sums `termSum` (uniqueness of weak derivatives). -/
theorem der_transportFun_ae (t : ℝ) (F : HjM j M) (α : Idx j) :
    (((transportFun t F).der α : L2w M) : ℂ → ℂ) =ᵐ[wMeasure M]
      termSum F t (terms (pdList α.1)) := by
  have hw1 := (transportFun t F).hasWeakDeriv α
  have hw2 : HasWeakDerivOn univ (pdList α.1) ((transportFun t F).value : ℂ → ℂ)
      (termSum F t (terms (pdList α.1))) :=
    (hasWeakDeriv_terms F t (pdList α.1) (by simpa using mem_multiIdx.1 α.2)).congr_ae
      ((transportFun_value t F).mono fun y hy _ => hy.symm)
      (Filter.Eventually.of_forall fun _ _ => rfl)
  have hae := HasWeakDerivOn.ae_eq isOpen_univ
    ((locallyIntegrable_L2w M _).locallyIntegrableOn univ)
    ((locallyIntegrable_termSum F t _
      fun p hp => ((terms_spec _ p hp).2.1 t).continuous).locallyIntegrableOn univ) hw1 hw2
  exact (wMeasure_ac M).ae_le (hae.mono fun y hy => hy (mem_univ y))

theorem norm_der_transportFun_le (t : ℝ) (F : HjM j M) (α : Idx j) :
    ‖(transportFun t F).der α‖ ≤ termsConst j * termsConst j * (1 + |t|) ^ j * ‖F‖ := by
  have hC := termsConst_spec j
  have hC0 := hC.1
  have hlen := (hC.2 α.1 α.2).1
  have hb := termSum_bound F t (termsConst j * (1 + |t|) ^ j) (by positivity)
    (terms (pdList α.1)) fun p hp =>
      ⟨((terms_spec _ p hp).2.1 t).continuous, fun y => (hC.2 α.1 α.2).2 p hp t y⟩
  rw [Lp.norm_def, eLpNorm_congr_ae (der_transportFun_ae t F α)]
  have hT : 0 ≤ (1 + |t|) ^ j := by positivity
  calc (eLpNorm (termSum F t (terms (pdList α.1))) 2 (wMeasure M)).toReal
      ≤ (ENNReal.ofReal ((terms (pdList α.1)).length * (termsConst j * (1 + |t|) ^ j) *
          ‖F‖)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb.2
    _ = (terms (pdList α.1)).length * (termsConst j * (1 + |t|) ^ j) * ‖F‖ :=
        ENNReal.toReal_ofReal (by positivity)
    _ ≤ termsConst j * (termsConst j * (1 + |t|) ^ j) * ‖F‖ := by gcongr
    _ = termsConst j * termsConst j * (1 + |t|) ^ j * ‖F‖ := by ring

/-- The constant `C_j` of `eq:st18-t00051`. -/
def transportConst (j : ℕ) : ℝ := Fintype.card (Idx j) * (termsConst j * termsConst j)

theorem transportConst_nonneg (j : ℕ) : 0 ≤ transportConst j := by
  have := (termsConst_spec j).1
  unfold transportConst
  positivity

theorem norm_transportFun_le (t : ℝ) (F : HjM j M) :
    ‖transportFun t F‖ ≤ transportConst j * (1 + |t|) ^ j * ‖F‖ := by
  have hC0 := (termsConst_spec j).1
  set D : ℝ := termsConst j * termsConst j * (1 + |t|) ^ j * ‖F‖ with hD
  have hD0 : 0 ≤ D := by positivity
  have hcard : (1 : ℝ) ≤ Fintype.card (Idx j) :=
    Nat.one_le_cast.2 (Fintype.card_pos_iff.2 ⟨idx0 j⟩)
  have hsq : ‖transportFun t F‖ ^ 2 ≤ (Fintype.card (Idx j) * D) ^ 2 := by
    rw [HjM.norm_sq]
    calc ∑ α : Idx j, ‖(transportFun t F).der α‖ ^ 2 ≤ ∑ _α : Idx j, D ^ 2 :=
          Finset.sum_le_sum fun α _ =>
            pow_le_pow_left₀ (norm_nonneg _) (norm_der_transportFun_le t F α) 2
      _ = Fintype.card (Idx j) * D ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (Fintype.card (Idx j) * D) ^ 2 := by
          rw [mul_pow]
          have : (0 : ℝ) ≤ D ^ 2 := sq_nonneg D
          nlinarith
  have := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  calc ‖transportFun t F‖ ≤ Fintype.card (Idx j) * D := this
    _ = transportConst j * (1 + |t|) ^ j * ‖F‖ := by rw [hD, transportConst]; ring

variable (j M) in
/-- **The transport group `T(t)` on `H^j_M`** (`eq:st18-t00050`): `T(t)f = f ∘ Φ_t`,
`Φ_t(r, ϑ) = (r, ϑ - Ω(r)t)`, as a bounded operator. -/
def transport (t : ℝ) : HjM j M →L[ℂ] HjM j M :=
  LinearMap.mkContinuous
    { toFun := transportFun t
      map_add' := transportFun_add t
      map_smul' := transportFun_smul t }
    (transportConst j * (1 + |t|) ^ j) (norm_transportFun_le t)

theorem transport_apply (t : ℝ) (F : HjM j M) : transport j M t F = transportFun t F := rfl

/-- `T(t)f(r,ϑ) = f(r, ϑ - Ω(r)t)`: the function of `T(t)F` is `f ∘ Φ_t` (a.e.). -/
theorem transport_value (t : ℝ) (F : HjM j M) :
    ((transport j M t F).value : ℂ → ℂ) =ᵐ[volume] fun y => F.value (flow t y) :=
  transportFun_value t F

/-- Group law `T(s+t) = T(s) T(t)`. -/
theorem transport_add (s t : ℝ) :
    transport j M (s + t) = (transport j M s).comp (transport j M t) := by
  ext1 F
  apply HjM.ext
  apply L2w_eq_of_ae
  filter_upwards [transport_value (j := j) (M := M) (s + t) F, transport_value s (transport j M t F),
    ae_comp_flow s (transport_value t F)] with y e1 e2 e3
  rw [ContinuousLinearMap.comp_apply, e1, e2, e3, flow_flow, add_comm]

/-- `T(0) = 1`. -/
theorem transport_zero : transport j M 0 = ContinuousLinearMap.id ℂ (HjM j M) := by
  ext1 F
  apply HjM.ext
  apply L2w_eq_of_ae
  filter_upwards [transport_value (j := j) (M := M) 0 F] with y e1
  rw [e1, flow_zero]
  rfl

variable (j M) in
/-- **`eq:st18-t00051`**: `‖T(t)‖_{H^j_M → H^j_M} ≤ C_j (1+|t|)^j` for all `t ∈ ℝ`, with `C_j`
independent of `t`. -/
theorem norm_transport_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖transport j M t‖ ≤ C * (1 + |t|) ^ j :=
  ⟨transportConst j, transportConst_nonneg j, fun t =>
    LinearMap.mkContinuous_norm_le _ (by have := transportConst_nonneg j; positivity) _⟩

variable (j M) in
/-- **Unit B0062, all claims together** (`paper/main.tex:1228-1237`): the polar form of the
group, the group law, preservation of area, of `|y|` (hence of every radial weight), of the
weighted measure of `H^j_M`, polynomial growth of the Cartesian derivatives of the flow, and the
operator bound `‖T(t)‖_{H^j_M → H^j_M} ≤ C_j(1+|t|)^j`. -/
theorem transport_group_polynomial_bound :
    (∀ t r θ : ℝ, 0 ≤ r → flow t ((r : ℂ) * gexp θ) = (r : ℂ) * gexp (θ - Omega r * t)) ∧
    (∀ s t : ℝ, ∀ y, flow s (flow t y) = flow (s + t) y) ∧
    (∀ t : ℝ, MeasurePreserving (flow t) volume volume) ∧
    (∀ t : ℝ, ∀ y, ‖flow t y‖ = ‖y‖) ∧
    (∀ t : ℝ, MeasurePreserving (flow t) (wMeasure M) (wMeasure M)) ∧
    (∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 ≤ C ∧
      ∀ t y, ‖iteratedFDeriv ℝ n (flow t) y‖ ≤ C * (1 + |t|) ^ n) ∧
    (∀ t : ℝ, ∀ F : HjM j M,
      ((transport j M t F).value : ℂ → ℂ) =ᵐ[volume] fun y => F.value (flow t y)) ∧
    (∀ s t : ℝ, transport j M (s + t) = (transport j M s).comp (transport j M t)) ∧
    transport j M 0 = ContinuousLinearMap.id ℂ (HjM j M) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖transport j M t‖ ≤ C * (1 + |t|) ^ j) :=
  ⟨fun t _ θ hr => flow_polar t hr θ, flow_flow, measurePreserving_flow, norm_flow,
    measurePreserving_flow_wMeasure M, norm_iteratedFDeriv_flow_le, transport_value,
    transport_add, transport_zero, norm_transport_le j M⟩

end UnforcedLeray.B0062
