import UnforcedLeray.Units.B0121

/-!
# B0122 helper: the Leibniz rule with Gaussian Schwartz coefficients on `ℝ²`

Blueprint unit **B0122** (`paper/main.tex` lines 1867--1871) uses two Leibniz expansions:
"Multiplication by `Ω` is bounded by Leibniz" and "Every `G^{-1/2} ∂^α k` is bounded, so another
Leibniz expansion gives ...". Both coefficients `Ω(y) = e^{-|y|²/4}` and
`k(y) = (|y|²/4 - 2) e^{-|y|²/4}` (tex line 639, `eq:st18-t00001`) are of the form `√G ψ` with
`ψ` a Schwartz function (`B0121.gS ψ`). This file proves the weak Leibniz rule for such
coefficients in the vendored framework `UnforcedLeray.PlanarBS.Sob.HasWeakDerivOn` used by
B0121 (`Units/B0121.lean`), together with the `L²` bound of the expansion.

## The recursion

For a word `w = v :: ws` of directions, `∂_v (√G ψ · F) = √G (A_v ψ) · F + √G ψ · ∂_v F`
(`B0121.dop_gS`: `∂ᵢ (√G ζ) = √G Aᵢ ζ`, `Aᵢ = ∂ᵢ - yᵢ/4`). Iterating, the weak derivative of
`√G ψ · g []` along `w` is `√G · leibC w ψ g`, where `g u` is the weak derivative of `F` along
the word `u` (`IsLFam`). `leibC w ψ g` is a sum of `2^{|w|}` products of a Schwartz function
`A_{us} ψ` with some `g u`, `|u| ≤ |w|`; hence `‖leibC w ψ g‖_{L²} ≤ 2^{|w|} M N` when every
`A_{us} ψ`, `|us| ≤ |w|`, is bounded by `M` and every `g u` has `L²` norm `≤ N`
(`eLpNorm_leibC_le`). Dividing by `√G`, the Gaussian norm of the derivative of the product is
the plain `L²` norm of `leibC w ψ g`: this is how `G^{-1/2} ∂^α k` bounded enters.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped SchwartzMap ENNReal ContDiff

namespace UnforcedLeray.B0122

open UnforcedLeray.B0121 UnforcedLeray.PlanarBS.Sob

/-! ## Words -/

/-- The direction list `[e_{u 0}, e_{u 1}, …]` of a word `u` over `{1, 2}`. -/
def dl (u : List (Fin 2)) : List (ℝ × ℝ) := u.map ev

/-- The multi-index `(#1's, #2's)` of a word. -/
def cnt (u : List (Fin 2)) : ℕ × ℕ := (u.count 0, u.count 1)

/-- The sorted word `1^{α₁} 2^{α₂}` of a multi-index. -/
def wordOf (α : ℕ × ℕ) : List (Fin 2) := List.replicate α.1 0 ++ List.replicate α.2 1

theorem dl_wordOf (α : ℕ × ℕ) : dl (wordOf α) = pdListR α := by
  simp [dl, wordOf, pdListR, List.map_replicate]

theorem length_wordOf (α : ℕ × ℕ) : (wordOf α).length = α.1 + α.2 := by
  simp [wordOf]

theorem dl_perm (u : List (Fin 2)) : (dl u).Perm (pdListR (cnt u)) := by
  have h := (perm_replicate_count u).map ev
  simpa [dl, cnt, pdListR, List.map_replicate] using h

theorem cnt_cons (v : Fin 2) (u : List (Fin 2)) :
    (cnt (v :: u)).1 + (cnt (v :: u)).2 = (cnt u).1 + (cnt u).2 + 1 := by
  have h1 := count_add_count u
  have h2 := count_add_count (v :: u)
  simp only [cnt, List.length_cons] at h1 h2 ⊢
  omega

theorem cnt_le (u : List (Fin 2)) : (cnt u).1 + (cnt u).2 = u.length := count_add_count u

/-! ## Weak derivatives: composition, sums, the product rule -/

theorem hasWeakDerivOn_cons {v : ℝ × ℝ} {ws : List (ℝ × ℝ)} {P P' Q : ℝ × ℝ → ℂ}
    (h1 : HasWeakDerivOn univ [v] P P') (h2 : HasWeakDerivOn univ ws P' Q) :
    HasWeakDerivOn univ (v :: ws) P Q := by
  intro φ hφ
  have e1 := h1 _ (hφ.iterDirDeriv ws)
  have e2 := h2 φ hφ
  have e : iterDirDeriv (v :: ws) φ = iterDirDeriv [v] (iterDirDeriv ws φ) := rfl
  rw [e, e1, e2]
  simp only [List.length_cons, List.length_nil, zero_add, pow_succ]
  ring

theorem hasWeakDerivOn_add {vs : List (ℝ × ℝ)} {P₁ P₂ Q₁ Q₂ : ℝ × ℝ → ℂ}
    (hP₁ : LocallyIntegrable P₁) (hP₂ : LocallyIntegrable P₂)
    (hQ₁ : LocallyIntegrable Q₁) (hQ₂ : LocallyIntegrable Q₂)
    (h₁ : HasWeakDerivOn univ vs P₁ Q₁) (h₂ : HasWeakDerivOn univ vs P₂ Q₂) :
    HasWeakDerivOn univ vs (fun z => P₁ z + P₂ z) (fun z => Q₁ z + Q₂ z) := by
  intro φ hφ
  have hψ := hφ.iterDirDeriv vs
  have i1 := integrable_mul_testFn (hP₁.locallyIntegrableOn univ) hψ
  have i2 := integrable_mul_testFn (hP₂.locallyIntegrableOn univ) hψ
  have i3 := integrable_mul_testFn (hQ₁.locallyIntegrableOn univ) hφ
  have i4 := integrable_mul_testFn (hQ₂.locallyIntegrableOn univ) hφ
  have e1 : (∫ x, (P₁ x + P₂ x) * iterDirDeriv vs φ x) =
      (∫ x, P₁ x * iterDirDeriv vs φ x) + ∫ x, P₂ x * iterDirDeriv vs φ x := by
    rw [← integral_add i1 i2]
    congr 1
    funext x
    ring
  have e2 : (∫ x, (Q₁ x + Q₂ x) * φ x) = (∫ x, Q₁ x * φ x) + ∫ x, Q₂ x * φ x := by
    rw [← integral_add i3 i4]
    congr 1
    funext x
    ring
  rw [e1, e2, h₁ φ hφ, h₂ φ hφ]
  ring

theorem hasWeakDerivOn_congr {vs : List (ℝ × ℝ)} {P P' Q Q' : ℝ × ℝ → ℂ}
    (h : HasWeakDerivOn univ vs P Q) (hP : P =ᵐ[volume] P') (hQ : Q =ᵐ[volume] Q') :
    HasWeakDerivOn univ vs P' Q' := by
  intro φ hφ
  have e1 : (∫ x, P' x * iterDirDeriv vs φ x) = ∫ x, P x * iterDirDeriv vs φ x := by
    refine integral_congr_ae ?_
    filter_upwards [hP] with x hx
    rw [hx]
  have e2 : (∫ x, Q' x * φ x) = ∫ x, Q x * φ x := by
    refine integral_congr_ae ?_
    filter_upwards [hQ] with x hx
    rw [hx]
  rw [e1, e2]
  exact h φ hφ

theorem contDiff_gS (ψ : S2) : ContDiff ℝ ∞ ⇑(gS ψ) := (gS ψ).smooth ⊤

theorem dirDeriv_gS (i : Fin 2) (ψ : S2) : dirDeriv (ev i) ⇑(gS ψ) = ⇑(gS (Aop i ψ)) := by
  rw [← coe_dop_eq_dirDeriv, dop_gS]

theorem isTestFn_mul {a φ : ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a) (hφ : IsTestFn univ φ) :
    IsTestFn univ (fun z => a z * φ z) :=
  ⟨ha.mul hφ.smooth, hφ.compact.mul_left, subset_univ _⟩

/-- **The product rule** for one derivative: `∂ᵢ(√G ψ · g) = √G (Aᵢψ) · g + √G ψ · ∂ᵢ g`. -/
theorem hasWeakDerivOn_gS_mul (ψ : S2) (i : Fin 2) {g g' : ℝ × ℝ → ℂ}
    (hg : LocallyIntegrable g) (hg' : LocallyIntegrable g')
    (h : HasWeakDerivOn univ [ev i] g g') :
    HasWeakDerivOn univ [ev i] (fun z => gS ψ z * g z)
      (fun z => gS (Aop i ψ) z * g z + gS ψ z * g' z) := by
  intro φ hφ
  set a : ℝ × ℝ → ℂ := ⇑(gS ψ) with ha
  set a' : ℝ × ℝ → ℂ := ⇑(gS (Aop i ψ)) with ha'
  have hac : ContDiff ℝ ∞ a := contDiff_gS ψ
  have ha'c : ContDiff ℝ ∞ a' := contDiff_gS _
  have t1 : IsTestFn univ (fun z => a z * φ z) := isTestFn_mul hac hφ
  have t2 : IsTestFn univ (fun z => a' z * φ z) := isTestFn_mul ha'c hφ
  have t3 : IsTestFn univ (fun z => a z * dirDeriv (ev i) φ z) :=
    isTestFn_mul hac (hφ.dirDeriv _)
  have hgl := hg.locallyIntegrableOn univ
  have hgl' := hg'.locallyIntegrableOn univ
  have I1 := integrable_mul_testFn hgl t2
  have I2 := integrable_mul_testFn hgl t3
  have I3 := integrable_mul_testFn hgl' t1
  have hd : ∀ z, dirDeriv (ev i) (fun z => a z * φ z) z =
      a' z * φ z + a z * dirDeriv (ev i) φ z := by
    intro z
    have hda : DifferentiableAt ℝ a z := (hac.differentiable (by simp)) z
    have hdφ : DifferentiableAt ℝ φ z := (hφ.smooth.differentiable (by simp)) z
    have e : a' z = dirDeriv (ev i) a z := by rw [ha', ha, dirDeriv_gS]
    rw [e]
    simp only [dirDeriv]
    have hm : HasFDerivAt (fun y => a y * φ y)
        (a z • fderiv ℝ φ z + φ z • fderiv ℝ a z) z := hda.hasFDerivAt.mul hdφ.hasFDerivAt
    rw [hm.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hA := h _ t1
  simp only [iterDirDeriv_cons, iterDirDeriv_nil, List.length_singleton, pow_one] at hA
  have key : (∫ z, g z * dirDeriv (ev i) (fun z => a z * φ z) z) =
      (∫ z, g z * (a' z * φ z)) + ∫ z, g z * (a z * dirDeriv (ev i) φ z) := by
    rw [← integral_add I1 I2]
    congr 1
    funext z
    rw [hd]
    ring
  rw [key] at hA
  have eL : (∫ z, (a z * g z) * iterDirDeriv [ev i] φ z) =
      ∫ z, g z * (a z * dirDeriv (ev i) φ z) := by
    congr 1
    funext z
    simp only [iterDirDeriv_cons, iterDirDeriv_nil]
    ring
  have eR : (∫ z, (a' z * g z + a z * g' z) * φ z) =
      (∫ z, g z * (a' z * φ z)) + ∫ z, g' z * (a z * φ z) := by
    rw [← integral_add I1 I3]
    congr 1
    funext z
    ring
  show (∫ z, (a z * g z) * iterDirDeriv [ev i] φ z) =
    (-1 : ℂ) ^ [ev i].length * ∫ z, (a' z * g z + a z * g' z) * φ z
  rw [eL, eR, List.length_singleton, pow_one]
  linear_combination hA

/-! ## The Leibniz expansion -/

/-- `A_{us} ψ = A_{u_k} ⋯ A_{u_1} ψ` (the conjugated derivatives `Aᵢ = ∂ᵢ - yᵢ/4`), so that
`∂_{us} (√G ψ) = √G A_{us} ψ`. -/
def AopL (us : List (Fin 2)) (ψ : S2) : S2 := us.foldl (fun φ i => Aop i φ) ψ

@[simp] theorem AopL_nil (ψ : S2) : AopL [] ψ = ψ := rfl

theorem AopL_cons (v : Fin 2) (us : List (Fin 2)) (ψ : S2) :
    AopL (v :: us) ψ = AopL us (Aop v ψ) := rfl

/-- The (conjugated) Leibniz expansion: `√G · leibC w ψ g` is `∂_w (√G ψ · g [])` when `g u` is
the weak derivative of `g []` along `u` (`leibniz_hasWeakDerivOn`). -/
def leibC : List (Fin 2) → S2 → (List (Fin 2) → ℝ × ℝ → ℂ) → ℝ × ℝ → ℂ
  | [], ψ, g => fun z => ψ z * g [] z
  | v :: ws, ψ, g => fun z => leibC ws (Aop v ψ) g z + leibC ws ψ (fun u => g (u ++ [v])) z

/-- `g u = ∂_u (g [])` weakly, one letter at a time, for `|u| ≤ n`, with `g u ∈ L²(ℝ²)`. -/
structure IsLFam (n : ℕ) (g : List (Fin 2) → ℝ × ℝ → ℂ) : Prop where
  memLp : ∀ u : List (Fin 2), u.length ≤ n → MemLp (g u) 2 volume
  step : ∀ (u : List (Fin 2)) (v : Fin 2), u.length < n →
    HasWeakDerivOn univ [ev v] (g u) (g (v :: u))

theorem IsLFam.mono {n m : ℕ} {g : List (Fin 2) → ℝ × ℝ → ℂ} (h : IsLFam n g) (hm : m ≤ n) :
    IsLFam m g :=
  ⟨fun u hu => h.memLp u (hu.trans hm), fun u v hu => h.step u v (lt_of_lt_of_le hu hm)⟩

theorem IsLFam.shift {n : ℕ} {g : List (Fin 2) → ℝ × ℝ → ℂ} (h : IsLFam (n + 1) g)
    (v : Fin 2) : IsLFam n (fun u => g (u ++ [v])) := by
  refine ⟨fun u hu => h.memLp _ (by simp; omega), fun u v' hu => ?_⟩
  exact h.step (u ++ [v]) v' (by simp; omega)

theorem norm_gS_le (ψ : S2) (z : ℝ × ℝ) : ‖gS ψ z‖ ≤ SchwartzMap.seminorm ℂ 0 0 (gS ψ) :=
  SchwartzMap.norm_le_seminorm ℂ _ z

theorem memLp_schwartz_mul (ψ : S2) {h : ℝ × ℝ → ℂ} (hh : MemLp h 2 volume) :
    MemLp (fun z => ψ z * h z) 2 volume :=
  hh.of_le_mul (ψ.continuous.aestronglyMeasurable.mul hh.aestronglyMeasurable)
    (Eventually.of_forall fun z => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℂ ψ z) (norm_nonneg _))

theorem norm_sqGc_le (z : ℝ × ℝ) : ‖sqGc z‖ ≤ B0093.sqrtConst := by
  rw [sqGc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sqG_pos z)]
  exact sqG_le z

theorem continuous_sqGc : Continuous sqGc :=
  Complex.continuous_ofReal.comp contDiff_sqG.continuous

theorem memLp_sqGc_mul {h : ℝ × ℝ → ℂ} (hh : MemLp h 2 volume) :
    MemLp (fun z => sqGc z * h z) 2 volume :=
  hh.of_le_mul (continuous_sqGc.aestronglyMeasurable.mul hh.aestronglyMeasurable)
    (Eventually.of_forall fun z => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_sqGc_le z) (norm_nonneg _))

theorem memLp_leibC : ∀ (w : List (Fin 2)) (ψ : S2) (g : List (Fin 2) → ℝ × ℝ → ℂ),
    (∀ u : List (Fin 2), u.length ≤ w.length → MemLp (g u) 2 volume) →
    MemLp (leibC w ψ g) 2 volume
  | [], ψ, g, hg => memLp_schwartz_mul ψ (hg [] le_rfl)
  | v :: ws, ψ, g, hg => by
    have h1 := memLp_leibC ws (Aop v ψ) g fun u hu => hg u (by simp; omega)
    have h2 := memLp_leibC ws ψ (fun u => g (u ++ [v])) fun u hu => hg _ (by simp; omega)
    exact h1.add h2

/-- **The Leibniz rule**: `∂_w (√G ψ · g []) = √G · leibC w ψ g` weakly on `ℝ²`. -/
theorem leibniz_hasWeakDerivOn : ∀ (w : List (Fin 2)) (ψ : S2)
    (g : List (Fin 2) → ℝ × ℝ → ℂ), IsLFam w.length g →
    HasWeakDerivOn univ (dl w) (fun z => gS ψ z * g [] z) (fun z => sqGc z * leibC w ψ g z)
  | [], ψ, g, _ => by
    intro φ _
    simp only [dl, List.map_nil, iterDirDeriv_nil, List.length_nil, pow_zero, one_mul, leibC,
      gS_apply]
    congr 1
    funext z
    ring
  | v :: ws, ψ, g, hg => by
    have hg0 : MemLp (g []) 2 volume := hg.memLp [] (by simp)
    have hgv : MemLp (g [v]) 2 volume := hg.memLp [v] (by simp)
    have hs := hasWeakDerivOn_gS_mul ψ v (hg0.locallyIntegrable (by norm_num))
      (hgv.locallyIntegrable (by norm_num)) (hg.step [] v (by simp))
    have hg1 : IsLFam ws.length g := hg.mono (by simp)
    have hg2 : IsLFam ws.length (fun u => g (u ++ [v])) := hg.shift v
    have ih1 := leibniz_hasWeakDerivOn ws (Aop v ψ) g hg1
    have ih2 := leibniz_hasWeakDerivOn ws ψ (fun u => g (u ++ [v])) hg2
    have m1 := memLp_leibC ws (Aop v ψ) g hg1.memLp
    have m2 := memLp_leibC ws ψ (fun u => g (u ++ [v])) hg2.memLp
    have hadd := hasWeakDerivOn_add
      ((memLp_schwartz_mul (gS (Aop v ψ)) hg0).locallyIntegrable (by norm_num))
      ((memLp_schwartz_mul (gS ψ) hgv).locallyIntegrable (by norm_num))
      ((memLp_sqGc_mul m1).locallyIntegrable (by norm_num))
      ((memLp_sqGc_mul m2).locallyIntegrable (by norm_num)) ih1 ih2
    have hc := hasWeakDerivOn_cons hs hadd
    refine hasWeakDerivOn_congr hc (Eventually.of_forall fun z => rfl)
      (Eventually.of_forall fun z => ?_)
    simp only [leibC]
    ring

/-- **The `L²` bound of the Leibniz expansion**: `‖leibC w ψ g‖_{L²} ≤ 2^{|w|} M N`. -/
theorem eLpNorm_leibC_le : ∀ (w : List (Fin 2)) (ψ : S2) (g : List (Fin 2) → ℝ × ℝ → ℂ)
    (M : ℝ) (N : ℝ≥0∞),
    (∀ us : List (Fin 2), us.length ≤ w.length → ∀ z, ‖AopL us ψ z‖ ≤ M) →
    (∀ u : List (Fin 2), u.length ≤ w.length → MemLp (g u) 2 volume) →
    (∀ u : List (Fin 2), u.length ≤ w.length → eLpNorm (g u) 2 volume ≤ N) →
    eLpNorm (leibC w ψ g) 2 volume ≤ 2 ^ w.length * (ENNReal.ofReal M * N)
  | [], ψ, g, M, N, hM, _, hN => by
    simp only [leibC, List.length_nil, pow_zero, one_mul]
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := g []) (c := M)
      (Eventually.of_forall fun z => ?_) 2).trans ?_
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM [] le_rfl z) (norm_nonneg _)
    · gcongr
      exact hN [] le_rfl
  | v :: ws, ψ, g, M, N, hM, hm, hN => by
    have b1 := eLpNorm_leibC_le ws (Aop v ψ) g M N
      (fun us hus z => by
        have := hM (v :: us) (by simp; omega) z
        rwa [AopL_cons] at this)
      (fun u hu => hm u (by simp; omega)) (fun u hu => hN u (by simp; omega))
    have b2 := eLpNorm_leibC_le ws ψ (fun u => g (u ++ [v])) M N
      (fun us hus z => hM us (by simp; omega) z)
      (fun u hu => hm _ (by simp; omega)) (fun u hu => hN _ (by simp; omega))
    have m1 := memLp_leibC ws (Aop v ψ) g fun u hu => hm u (by simp; omega)
    have m2 := memLp_leibC ws ψ (fun u => g (u ++ [v])) fun u hu => hm _ (by simp; omega)
    calc eLpNorm (leibC (v :: ws) ψ g) 2 volume
        = eLpNorm (leibC ws (Aop v ψ) g + leibC ws ψ (fun u => g (u ++ [v]))) 2 volume := rfl
      _ ≤ eLpNorm (leibC ws (Aop v ψ) g) 2 volume +
          eLpNorm (leibC ws ψ (fun u => g (u ++ [v]))) 2 volume :=
          eLpNorm_add_le m1.aestronglyMeasurable m2.aestronglyMeasurable (by norm_num)
      _ ≤ 2 ^ ws.length * (ENNReal.ofReal M * N) + 2 ^ ws.length * (ENNReal.ofReal M * N) :=
          add_le_add b1 b2
      _ = 2 ^ (v :: ws).length * (ENNReal.ofReal M * N) := by
          rw [List.length_cons, pow_succ, ← two_mul]
          ring

/-- Every Schwartz function has uniformly bounded conjugated derivatives `A_{us} ψ`,
`|us| ≤ n`. -/
theorem exists_AopL_bound (n : ℕ) : ∀ ψ : S2, ∃ M : ℝ, 0 ≤ M ∧
    ∀ us : List (Fin 2), us.length ≤ n → ∀ z, ‖AopL us ψ z‖ ≤ M := by
  induction n with
  | zero =>
    intro ψ
    refine ⟨SchwartzMap.seminorm ℂ 0 0 ψ, apply_nonneg _ _, fun us hus z => ?_⟩
    have : us = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact SchwartzMap.norm_le_seminorm ℂ ψ z
  | succ n ih =>
    intro ψ
    choose M hM0 hM using fun v : Fin 2 => ih (Aop v ψ)
    refine ⟨SchwartzMap.seminorm ℂ 0 0 ψ + ∑ v : Fin 2, M v,
      add_nonneg (apply_nonneg _ _) (Finset.sum_nonneg fun v _ => hM0 v), ?_⟩
    rintro (_ | ⟨v, us⟩) hus z
    · have h1 := SchwartzMap.norm_le_seminorm ℂ ψ z
      have h2 : 0 ≤ ∑ v : Fin 2, M v := Finset.sum_nonneg fun v _ => hM0 v
      simp only [AopL_nil]
      linarith
    · rw [AopL_cons]
      have h1 := hM v us (by simp at hus; omega) z
      have h2 : M v ≤ ∑ v : Fin 2, M v :=
        Finset.single_le_sum (fun v _ => hM0 v) (Finset.mem_univ v)
      have h3 := apply_nonneg (SchwartzMap.seminorm ℂ 0 0) ψ
      linarith

end UnforcedLeray.B0122
