import UnforcedLeray.Units.B0121.Ops
import UnforcedLeray.Lib.Kernels.PlanarBS.Defs.Infra.Sobolev
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# B0121 helper: weak derivatives on `ℝ²`, words and multi-indices

Blueprint unit B0121 (`eq:st18-t00100`, `paper/main.tex` lines 1856--1865). The derivatives
`∂^α f` of `eq:st18-t00100` are distributional. We use the project's notion
`UnforcedLeray.PlanarBS.Sob.HasWeakDerivOn` (`Lib/Kernels/PlanarBS/Defs/Infra/Sobolev.lean`):
`g = ∂_{v₁} ⋯ ∂_{vₙ} f` weakly iff `∫ f ∂_{v₁} ⋯ ∂_{vₙ} φ = (-1)ⁿ ∫ g φ` for every smooth
compactly supported `φ`.

The first part is copied from the NonUniqueEuler reference formalization,
`NonUniqueEuler/lean/NonUniqueEuler/P/Infra/Sobolev/WeakDeriv.lean` (Mathlib pin 85e3a25e,
as here), adapted to the vendored definitions `UnforcedLeray.PlanarBS.Sob` and the namespace
`UnforcedLeray.B0121`: commuting directional derivatives of smooth functions, uniqueness of weak
derivatives (`hasWeakDerivOn_ae_eq`), classical derivatives are weak derivatives
(`hasWeakDerivOn_of_contDiffOn`), and invariance under permutations (`hasWeakDerivOn_perm`).

The second part relates words and multi-indices on `ℝ²`: `pdListR α` is the direction list of
`∂^α = ∂₁^{α₁} ∂₂^{α₂}`; a word `w : Fin k → Fin 2` (an ordered product `∂_{w 0} ⋯ ∂_{w (k-1)}`)
has direction list `dirs w`, a permutation of `pdListR (mi w)` where `mi w` counts the letters.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace UnforcedLeray.B0121

open UnforcedLeray.PlanarBS.Sob

/-! ## Copied from the reference: weak derivatives -/

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem testFn_eq_zero {V : Set E} {φ : E → ℂ} (hφ : IsTestFn V φ) {x : E} (hx : x ∉ V) :
    φ x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.subset h))

/-- A real test function, viewed as a complex one. -/
theorem isTestFn_ofReal {V : Set E} {ρ : E → ℝ} (h1 : ContDiff ℝ ∞ ρ) (h2 : HasCompactSupport ρ)
    (h3 : tsupport ρ ⊆ V) : IsTestFn V (fun x => (ρ x : ℂ)) := by
  refine ⟨Complex.ofRealCLM.contDiff.comp h1, h2.comp_left Complex.ofReal_zero, ?_⟩
  exact (tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero ρ).trans h3

theorem contDiff_dirDeriv {φ : E → ℂ} (h : ContDiff ℝ ∞ φ) (v : E) :
    ContDiff ℝ ∞ (dirDeriv v φ) :=
  (ContDiff.fderiv_right (m := ∞) h (by simp)).clm_apply contDiff_const

theorem contDiff_iterDirDeriv {φ : E → ℂ} (h : ContDiff ℝ ∞ φ) (vs : List E) :
    ContDiff ℝ ∞ (iterDirDeriv vs φ) := by
  induction vs with
  | nil => simpa using h
  | cons v vs ih => simpa using contDiff_dirDeriv ih v

theorem dirDeriv_dirDeriv_eq {φ : E → ℂ} (h : ContDiff ℝ ∞ φ) (v w x : E) :
    dirDeriv v (dirDeriv w φ) x = fderiv ℝ (fderiv ℝ φ) x v w := by
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (ContDiff.fderiv_right (m := ∞) h (by simp)).differentiable (by simp)
  have hx : HasFDerivAt (fun y => fderiv ℝ φ y w) ((fderiv ℝ (fderiv ℝ φ) x).flip w) x := by
    have := (hd x).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
    simpa using this
  show fderiv ℝ (fun y => fderiv ℝ φ y w) x v = _
  rw [hx.fderiv]
  rfl

theorem dirDeriv_comm {φ : E → ℂ} (h : ContDiff ℝ ∞ φ) (v w : E) :
    dirDeriv v (dirDeriv w φ) = dirDeriv w (dirDeriv v φ) := by
  funext x
  rw [dirDeriv_dirDeriv_eq h, dirDeriv_dirDeriv_eq h]
  exact (h.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w

/-- For smooth `φ`, `iterDirDeriv vs φ` only depends on `vs` up to permutation. -/
theorem iterDirDeriv_perm {vs ws : List E} (hp : vs.Perm ws) {φ : E → ℂ}
    (h : ContDiff ℝ ∞ φ) : iterDirDeriv vs φ = iterDirDeriv ws φ := by
  induction hp with
  | nil => rfl
  | cons x _ ih => simp only [iterDirDeriv_cons, ih]
  | swap x y l =>
    simp only [iterDirDeriv_cons]
    exact dirDeriv_comm (contDiff_iterDirDeriv h l) y x
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem contDiffOn_iterDirDeriv {V : Set E} (hV : IsOpen V) {f : E → ℂ} {n : ℕ}
    (hf : ContDiffOn ℝ n f V) (ws : List E) :
    ∀ m : ℕ, m + ws.length ≤ n → ContDiffOn ℝ m (iterDirDeriv ws f) V := by
  induction ws with
  | nil =>
    intro m hm
    exact hf.of_le (by exact_mod_cast (by simpa using hm))
  | cons w ws ih =>
    intro m hm
    have h1 := ih (m + 1) (by simp only [List.length_cons] at hm; omega)
    have h2 := h1.fderiv_of_isOpen hV (m := m) (by push_cast; exact le_rfl)
    exact h2.clm_apply contDiffOn_const

end Calculus

section Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]

/-- A locally integrable function on `V` times a test function supported in `V` is
integrable. -/
theorem integrable_mul_testFn [OpensMeasurableSpace E] {V : Set E} {g φ : E → ℂ}
    (hg : LocallyIntegrableOn g V) (hφ : IsTestFn V φ) : Integrable (fun x => g x * φ x) := by
  have hK : IsCompact (tsupport φ) := hφ.compact
  have h1 : IntegrableOn g (tsupport φ) := hg.integrableOn_compact_subset hφ.subset hK
  have h2 : IntegrableOn (fun x => g x * φ x) (tsupport φ) :=
    h1.mul_continuousOn hφ.continuous.continuousOn hK
  refine h2.integrable_of_forall_notMem_eq_zero (fun x hx => ?_)
  simp [image_eq_zero_of_notMem_tsupport hx]

/-- Invariance of the pairing under a.e. modification on `V`. -/
theorem integral_mul_testFn_congr {V : Set E} {f f' φ : E → ℂ} (hφ : IsTestFn V φ)
    (hf : ∀ᵐ x, x ∈ V → f x = f' x) : ∫ x, f' x * φ x = ∫ x, f x * φ x := by
  refine integral_congr_ae ?_
  filter_upwards [hf] with x hx
  by_cases hxV : x ∈ V
  · rw [hx hxV]
  · simp [testFn_eq_zero hφ hxV]

end Measure

section Haar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- A function continuous on the open set `V` times a test function supported in `V` is
integrable. -/
theorem integrable_continuousOn_mul_testFn {V : Set E} (hV : IsOpen V) {a φ : E → ℂ}
    (ha : ContinuousOn a V) (hφ : IsTestFn V φ) : Integrable (fun x => a x * φ x) :=
  integrable_mul_testFn (ha.locallyIntegrableOn hV.measurableSet) hφ

omit [(volume : Measure E).IsAddHaarMeasure] in
/-- Two locally integrable functions with the same pairings against all test functions
supported in the open set `V` agree a.e. on `V`. -/
theorem ae_eq_of_integral_testFn {V : Set E} (hV : IsOpen V) {g₁ g₂ : E → ℂ}
    (hg₁ : LocallyIntegrableOn g₁ V) (hg₂ : LocallyIntegrableOn g₂ V)
    (key : ∀ φ, IsTestFn V φ → ∫ x, g₁ x * φ x = ∫ x, g₂ x * φ x) :
    ∀ᵐ x, x ∈ V → g₁ x = g₂ x := by
  have h := hV.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hg₁.sub hg₂)
    (fun ρ hρ hρc hρV => by
      have hφ := isTestFn_ofReal hρ hρc hρV
      have i1 := integrable_mul_testFn hg₁ hφ
      have i2 := integrable_mul_testFn hg₂ hφ
      calc ∫ x, ρ x • (g₁ - g₂) x = ∫ x, (g₁ x * (ρ x : ℂ) - g₂ x * (ρ x : ℂ)) := by
            congr 1
            ext x
            simp only [Pi.sub_apply, Complex.real_smul]
            ring
        _ = 0 := by rw [integral_sub i1 i2, key _ hφ, sub_self])
  filter_upwards [h] with x hx hxV
  exact sub_eq_zero.1 (hx hxV)

/-- One integration by parts: for `F` of class `C¹` on the open set `V` and a test function
`ψ` supported in `V`, `∫ F ∂_v ψ = - ∫ (∂_v F) ψ`. -/
theorem integral_mul_dirDeriv {V : Set E} (hV : IsOpen V) {F ψ : E → ℂ}
    (hF : ContDiffOn ℝ 1 F V) (hψ : IsTestFn V ψ) (v : E) :
    ∫ x, F x * dirDeriv v ψ x = - ∫ x, dirDeriv v F x * ψ x := by
  have hFd : ∀ x ∈ V, DifferentiableAt ℝ F x := fun x hx =>
    (hF.differentiableOn one_ne_zero x hx).differentiableAt (hV.mem_nhds hx)
  have hFc : ContinuousOn F V := hF.continuousOn
  have hF'c : ContinuousOn (dirDeriv v F) V :=
    (hF.continuousOn_fderiv_of_isOpen hV le_rfl).clm_apply continuousOn_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_continuousOn_mul_testFn hV hF'c hψ)
    (integrable_continuousOn_mul_testFn hV hFc (hψ.dirDeriv v))
    (integrable_continuousOn_mul_testFn hV hFc hψ)
    (fun x hx => hFd x (hψ.subset hx))
    (fun x _ => (hψ.smooth.differentiable (by simp)).differentiableAt)

/-- Uniqueness: two locally integrable weak derivatives on an open set agree a.e. on it. -/
theorem hasWeakDerivOn_ae_eq {V : Set E} (hV : IsOpen V) {vs : List E} {f g₁ g₂ : E → ℂ}
    (hg₁ : LocallyIntegrableOn g₁ V) (hg₂ : LocallyIntegrableOn g₂ V)
    (h₁ : HasWeakDerivOn V vs f g₁) (h₂ : HasWeakDerivOn V vs f g₂) :
    ∀ᵐ x, x ∈ V → g₁ x = g₂ x := by
  refine ae_eq_of_integral_testFn hV hg₁ hg₂ (fun φ hφ => ?_)
  have e := (h₁ φ hφ).symm.trans (h₂ φ hφ)
  have hne : ((-1 : ℂ) ^ vs.length) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_left_cancel₀ hne e

/-- Classical derivatives are weak derivatives: if `f` is `C^n` on the open set `V`,
`n ≥ |vs|`, then `∂_{vs} f` (computed classically) is the weak derivative on `V`. -/
theorem hasWeakDerivOn_of_contDiffOn {V : Set E} (hV : IsOpen V) {vs : List E} {f : E → ℂ}
    {n : ℕ} (hn : vs.length ≤ n) (hf : ContDiffOn ℝ n f V) :
    HasWeakDerivOn V vs f (iterDirDeriv vs f) := by
  induction vs with
  | nil => intro φ _; simp
  | cons v ws ih =>
    intro φ hφ
    have hws : ws.length ≤ n := by simp only [List.length_cons] at hn; omega
    have hF : ContDiffOn ℝ 1 (iterDirDeriv ws f) V :=
      contDiffOn_iterDirDeriv hV hf ws 1 (by simp only [List.length_cons] at hn; omega)
    have e1 : iterDirDeriv (v :: ws) φ = iterDirDeriv ws (dirDeriv v φ) := by
      rw [iterDirDeriv_perm (List.perm_append_singleton v ws).symm hφ.smooth,
        iterDirDeriv_append]
      rfl
    rw [e1, ih hws _ (hφ.dirDeriv v), integral_mul_dirDeriv hV hF hφ v, iterDirDeriv_cons,
      List.length_cons, pow_succ]
    ring

end Haar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]

/-- The order of the directions does not matter. -/
theorem hasWeakDerivOn_perm {V : Set E} {vs ws : List E} (hp : vs.Perm ws) {f g : E → ℂ}
    (h : HasWeakDerivOn V vs f g) : HasWeakDerivOn V ws f g := by
  intro φ hφ
  rw [← iterDirDeriv_perm hp hφ.smooth, h φ hφ, hp.length_eq]

/-! ## Words and multi-indices on `ℝ²` -/

/-- The direction list of `∂^α = ∂₁^{α₁} ∂₂^{α₂}` on `ℝ²` (the analogue on `ℝ × ℝ` of the
library's `pdList` on `ℂ`). -/
def pdListR (α : ℕ × ℕ) : List (ℝ × ℝ) := List.replicate α.1 (ev 0) ++ List.replicate α.2 (ev 1)

@[simp] theorem pdListR_length (α : ℕ × ℕ) : (pdListR α).length = α.1 + α.2 := by
  simp [pdListR]

/-- The direction list `[e_{w 0}, …, e_{w (k-1)}]` of the word `w`. -/
def dirs {k : ℕ} (w : Fin k → Fin 2) : List (ℝ × ℝ) := List.ofFn fun m => ev (w m)

@[simp] theorem dirs_length {k : ℕ} (w : Fin k → Fin 2) : (dirs w).length = k := by
  simp [dirs]

theorem dirs_cons {k : ℕ} (i : Fin 2) (w : Fin k → Fin 2) :
    dirs (Fin.cons i w : Fin (k + 1) → Fin 2) = ev i :: dirs w := by
  simp [dirs, List.ofFn_succ]

/-- The multi-index of a word: the numbers of letters `0` and `1`. -/
def mi {k : ℕ} (w : Fin k → Fin 2) : ℕ × ℕ := ((List.ofFn w).count 0, (List.ofFn w).count 1)

theorem ev_injective : Function.Injective ev := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [ev, B0094.e1, B0094.e2]

theorem perm_replicate_count (l : List (Fin 2)) :
    l.Perm (List.replicate (l.count 0) 0 ++ List.replicate (l.count 1) 1) := by
  rw [List.perm_iff_count]
  intro a
  fin_cases a <;> simp [List.count_replicate]

theorem dirs_perm {k : ℕ} (w : Fin k → Fin 2) : (dirs w).Perm (pdListR (mi w)) := by
  have h1 : dirs w = (List.ofFn w).map ev := by
    simp [dirs, List.map_ofFn]
    rfl
  have h2 : pdListR (mi w) =
      (List.replicate ((List.ofFn w).count 0) (0 : Fin 2) ++
        List.replicate ((List.ofFn w).count 1) 1).map ev := by
    simp [pdListR, mi, List.map_replicate]
  rw [h1, h2]
  exact (perm_replicate_count _).map ev

theorem count_add_count (l : List (Fin 2)) : l.count 0 + l.count 1 = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    fin_cases a <;> simp [List.count_cons] <;> omega

theorem mi_mem_antidiagonal {k : ℕ} (w : Fin k → Fin 2) :
    mi w ∈ Finset.antidiagonal k := by
  rw [Finset.mem_antidiagonal, mi, count_add_count, List.length_ofFn]

theorem mi_cons {k : ℕ} (i : Fin 2) (w : Fin k → Fin 2) :
    mi (Fin.cons i w : Fin (k + 1) → Fin 2) =
      mi w + (if i = 0 then ((1 : ℕ), (0 : ℕ)) else ((0 : ℕ), (1 : ℕ))) := by
  have h : List.ofFn (Fin.cons i w : Fin (k + 1) → Fin 2) = i :: List.ofFn w := by
    simp [List.ofFn_succ]
  fin_cases i <;> simp [mi, h, List.count_cons] <;> omega

theorem exists_word {k : ℕ} {α : ℕ × ℕ} (hα : α ∈ Finset.antidiagonal k) :
    ∃ w : Fin k → Fin 2, mi w = α := by
  induction k generalizing α with
  | zero =>
    rw [Finset.mem_antidiagonal] at hα
    obtain ⟨a, b⟩ := α
    simp only at hα
    refine ⟨Fin.elim0, ?_⟩
    refine Prod.ext ?_ ?_ <;> simp [mi] <;> omega
  | succ k ih =>
    rw [Finset.mem_antidiagonal] at hα
    obtain ⟨a, b⟩ := α
    simp only at hα
    rcases Nat.eq_zero_or_pos a with ha | ha
    · obtain ⟨w, hw⟩ := ih (α := (0, b - 1)) (by rw [Finset.mem_antidiagonal]; simp; omega)
      refine ⟨Fin.cons 1 w, ?_⟩
      rw [mi_cons, hw]
      refine Prod.ext ?_ ?_ <;> simp <;> omega
    · obtain ⟨w, hw⟩ := ih (α := (a - 1, b)) (by rw [Finset.mem_antidiagonal]; simp; omega)
      refine ⟨Fin.cons 0 w, ?_⟩
      rw [mi_cons, hw]
      refine Prod.ext ?_ ?_ <;> simp <;> omega

/-- Multi-index sum `≤` word sum (every multi-index of order `k` is the multi-index of a
word). -/
theorem sum_antidiagonal_le_sum_words (k : ℕ) (h : ℕ × ℕ → ℝ) (hh : ∀ α, 0 ≤ h α) :
    ∑ α ∈ Finset.antidiagonal k, h α ≤ ∑ w : Fin k → Fin 2, h (mi w) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.antidiagonal k)
    (g := mi) (fun w _ => mi_mem_antidiagonal w)]
  refine Finset.sum_le_sum fun α hα => ?_
  obtain ⟨w, hw⟩ := exists_word hα
  have hmem : w ∈ Finset.univ.filter fun w : Fin k → Fin 2 => mi w = α := by simp [hw]
  calc h α = h (mi w) := by rw [hw]
    _ ≤ ∑ w ∈ Finset.univ.filter fun w : Fin k → Fin 2 => mi w = α, h (mi w) :=
        Finset.single_le_sum (f := fun w => h (mi w)) (fun w _ => hh _) hmem

/-- Word sum `≤ 2^k ×` multi-index sum. -/
theorem sum_words_le (k : ℕ) (h : ℕ × ℕ → ℝ) (hh : ∀ α, 0 ≤ h α) :
    ∑ w : Fin k → Fin 2, h (mi w) ≤ 2 ^ k * ∑ α ∈ Finset.antidiagonal k, h α := by
  have hS : ∀ w : Fin k → Fin 2, h (mi w) ≤ ∑ α ∈ Finset.antidiagonal k, h α :=
    fun w => Finset.single_le_sum (fun α _ => hh α) (mi_mem_antidiagonal w)
  calc ∑ w : Fin k → Fin 2, h (mi w)
      ≤ ∑ _w : Fin k → Fin 2, ∑ α ∈ Finset.antidiagonal k, h α := Finset.sum_le_sum fun w _ => hS w
    _ = 2 ^ k * ∑ α ∈ Finset.antidiagonal k, h α := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- The multi-indices `|α| ≤ j` sorted by order. -/
theorem sum_multiIdx (j : ℕ) {M : Type*} [AddCommMonoid M] (h : ℕ × ℕ → M) :
    ∑ α ∈ multiIdx j, h α = ∑ k ∈ Finset.range (j + 1), ∑ α ∈ Finset.antidiagonal k, h α := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := multiIdx j) (t := Finset.range (j + 1))
    (g := fun α => α.1 + α.2) (fun α hα => by
      rw [mem_multiIdx] at hα
      rw [Finset.mem_range]
      omega)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  congr 1
  ext α
  simp only [Finset.mem_filter, mem_multiIdx, Finset.mem_antidiagonal]
  omega

end UnforcedLeray.B0121
