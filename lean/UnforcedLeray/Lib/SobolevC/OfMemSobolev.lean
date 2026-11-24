import UnforcedLeray.Lib.SobolevC.FourierBridge

/-!
# The converse `p = 2` Fourier bridge `H^k ⊂ W^{k,2}(ℝⁿ)` (INF11 target S9a, `W.ofMemSobolev`)


target S9a (`W.ofMemSobolev`); decision D3 of `scoping/README.md` §3 (Mathlib `MemSobolev` only as
the `p = 2` Fourier bridge).  Manuscript uses: B0091 (tex 1463–1477, "the Fourier
characterization first gives `χ ∈ H²`"), B1009 (tex 308–312), B0122 (tex 1867–1871, global
elliptic regularity as a Fourier multiplier), B0059 (tex 1206–1213).

## Main declarations
* `dDs`, `dD_apply`: the pairing `⟨∂_{ws} T, ψ⟩ = (-1)^{|ws|} ⟨T, ∂_{ws} ψ⟩`;
* `iterDirDeriv_comp`, `dDs_ofRealTest`: real parts of iterated derivatives of Schwartz tests;
* `hasWeakDeriv_of_dD`: an identity `∂_{ws} u = g` in `𝓢'` between `L²` functions is a weak
  derivative identity for the tests `C_c^∞(ℝⁿ)` (the converse of
  `lineDerivOp_toTemperedDistribution`);
* `memSobolev_dD`: `∂_{ws}` maps `H^s` to `H^{s - |ws|}`;
* `W.ofMemSobolev`: every `f ∈ L²(ℝⁿ; F)` with `f ∈ H^k` (Mathlib's `MemSobolev k 2`) is the
  field of an element of `W^{k,2}(ℝⁿ; F)`;
* `memSobolev_iff_exists_W`: `MemSobolev k 2 f ↔ ∃ x ∈ W^{k,2}, x = f` (with `W.memSobolev`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric SchwartzMap TemperedDistribution LineDeriv
open scoped ENNReal NNReal Topology ContDiff FourierTransform SchwartzMap

namespace UnforcedLeray.Sob

variable {n : ℕ}

/-! ### Iterated derivatives of Schwartz tests -/

section Tests

/-- `∂_{w_m} ⋯ ∂_{w_1} ψ` for `ws = [w_1, …, w_m]` (the transpose order of `dD`). -/
def dDs (ws : List (Eucl n)) (ψ : 𝓢(Eucl n, ℂ)) : 𝓢(Eucl n, ℂ) :=
  ws.foldl (fun χ m => ∂_{m} χ) ψ

@[simp] theorem dDs_nil (ψ : 𝓢(Eucl n, ℂ)) : dDs [] ψ = ψ := rfl

@[simp] theorem dDs_cons (m : Eucl n) (ws : List (Eucl n)) (ψ : 𝓢(Eucl n, ℂ)) :
    dDs (m :: ws) ψ = dDs ws (∂_{m} ψ) := rfl

theorem dDs_neg (ws : List (Eucl n)) (ψ : 𝓢(Eucl n, ℂ)) : dDs ws (-ψ) = -dDs ws ψ := by
  induction ws generalizing ψ with
  | nil => rfl
  | cons m ws ih => rw [dDs_cons, dDs_cons, LineDeriv.lineDerivOp_neg, ih]

/-- Real-linear images of iterated derivatives of a Schwartz test (reversed word). -/
theorem iterDirDeriv_reverse_comp (L : ℂ →L[ℝ] ℝ) (ws : List (Eucl n)) (ψ : 𝓢(Eucl n, ℂ)) :
    iterDirDeriv ws.reverse (fun x => L (ψ x)) = fun x => L (dDs ws ψ x) := by
  induction ws generalizing ψ with
  | nil => rfl
  | cons m ws ih =>
    rw [List.reverse_cons, iterDirDeriv_append, dDs_cons, ← ih]
    congr 1
    funext x
    simp only [iterDirDeriv_singleton, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have h : HasFDerivAt (⇑L ∘ ⇑ψ) (L.comp (fderiv ℝ ψ x)) x :=
      L.hasFDerivAt.comp x ψ.differentiableAt.hasFDerivAt
    change fderiv ℝ (⇑L ∘ ⇑ψ) x m = L (fderiv ℝ ψ x m)
    rw [h.fderiv]
    rfl

/-- Real-linear images of iterated derivatives of a Schwartz test. -/
theorem iterDirDeriv_comp (L : ℂ →L[ℝ] ℝ) (ws : List (Eucl n)) (ψ : 𝓢(Eucl n, ℂ)) :
    iterDirDeriv ws (fun x => L (ψ x)) = fun x => L (dDs ws ψ x) := by
  have hs : ContDiff ℝ ∞ (fun x => L (ψ x)) := L.contDiff.comp (ψ.smooth ⊤)
  rw [iterDirDeriv_perm (List.reverse_perm ws).symm hs, iterDirDeriv_reverse_comp]

theorem iterDirDeriv_zero (ws : List (Eucl n)) : iterDirDeriv ws (fun _ : Eucl n => (0 : ℝ)) = 0 := by
  induction ws with
  | nil => rfl
  | cons m ws ih =>
    funext x
    simp only [iterDirDeriv_cons, ih, Pi.zero_apply]
    simp

/-- The complex Schwartz test of a real `C_c^∞` function. -/
def ofRealTest (φ : Eucl n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    𝓢(Eucl n, ℂ) :=
  (show HasCompactSupport (Complex.ofRealCLM ∘ φ) from hc.comp_left rfl).toSchwartzMap
    (by fun_prop)

@[simp] theorem ofRealTest_apply (φ : Eucl n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (x : Eucl n) : ofRealTest φ hφ hc x = (φ x : ℂ) := rfl

/-- `∂_{ws}` of the complex test of `φ` is the complex test of `∂_{ws} φ`. -/
theorem dDs_ofRealTest (ws : List (Eucl n)) (φ : Eucl n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (x : Eucl n) :
    dDs ws (ofRealTest φ hφ hc) x = (iterDirDeriv ws φ x : ℂ) := by
  have hre := congrFun (iterDirDeriv_comp Complex.reCLM ws (ofRealTest φ hφ hc)) x
  have him := congrFun (iterDirDeriv_comp Complex.imCLM ws (ofRealTest φ hφ hc)) x
  simp only [ofRealTest_apply, Complex.reCLM_apply, Complex.imCLM_apply, Complex.ofReal_re,
    Complex.ofReal_im] at hre him
  rw [iterDirDeriv_zero] at him
  apply Complex.ext
  · rw [Complex.ofReal_re, ← hre]
  · rw [Complex.ofReal_im, ← him]
    rfl

end Tests

/-! ### Distributional identities give weak derivatives -/

section Weak

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Pairing of iterated distributional derivatives**: `⟨∂_{ws} T, ψ⟩ = (-1)^{|ws|} ⟨T, ∂_{ws} ψ⟩`. -/
theorem dD_apply (ws : List (Eucl n)) (T : 𝓢'(Eucl n, F)) (ψ : 𝓢(Eucl n, ℂ)) :
    dD ws T ψ = (-1 : ℂ) ^ ws.length • T (dDs ws ψ) := by
  induction ws generalizing ψ with
  | nil => simp
  | cons m ws ih =>
    rw [dD_cons, TemperedDistribution.lineDerivOp_apply_apply, ih, dDs_neg, map_neg, dDs_cons,
      List.length_cons, pow_succ, mul_smul, neg_one_smul, smul_neg]

/-- **Converse of `lineDerivOp_toTemperedDistribution`** (S9a): an identity `∂_{ws} u = g` in
`𝓢'(ℝⁿ, F)` between `L²` functions is a weak derivative identity with `C_c^∞` tests. -/
theorem hasWeakDeriv_of_dD {ws : List (Eucl n)} {u g : Lp F 2 (volume : Measure (Eucl n))}
    (h : dD ws (u : 𝓢'(Eucl n, F)) = (g : 𝓢'(Eucl n, F))) :
    HasWeakDeriv (wholeSpace n) ws (u : Eucl n → F) (g : Eucl n → F) := by
  have hmemφ : ∀ φ : Eucl n → ℝ, (wholeSpace n).Adm φ → MemLp φ 2 volume := fun φ hφ =>
    hφ.1.continuous.memLp_of_hasCompactSupport hφ.2
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · exact integrable_smul_of_memLp_two (hmemφ _ ((wholeSpace n).adm_iterDirDeriv hφ ws))
      (Lp.memLp u)
  · exact integrable_smul_of_memLp_two (hmemφ _ hφ) (Lp.memLp g)
  · have e := congrArg (fun T : 𝓢'(Eucl n, F) => T (ofRealTest φ hφ.1 hφ.2)) h
    simp only [dD_apply, Lp.toTemperedDistribution_apply, dDs_ofRealTest, ofRealTest_apply,
      Complex.coe_smul] at e
    rw [wholeSpace_μ, ← e, ← Complex.coe_smul, smul_smul]
    push_cast
    rw [← mul_pow]
    norm_num

end Weak

/-! ### `H^k ⊂ W^{k,2}` -/

section Converse

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- `∂_{ws}` maps `H^s` into `H^{s - |ws|}` (iterate `MemSobolev.lineDerivOp`). -/
theorem memSobolev_dD {s : ℝ} {T : 𝓢'(Eucl n, F)} (hT : MemSobolev s 2 T) (ws : List (Eucl n)) :
    MemSobolev (s - ws.length) 2 (dD ws T) := by
  induction ws with
  | nil => simpa using hT
  | cons m ws ih =>
    rw [dD_cons, List.length_cons]
    have := ih.lineDerivOp (m := m)
    have e : s - ((ws.length + 1 : ℕ) : ℝ) = s - ws.length - 1 := by push_cast; ring
    rw [e]
    exact this

theorem toTemperedDistribution_injective :
    Function.Injective (fun f : Lp F 2 (volume : Measure (Eucl n)) => (f : 𝓢'(Eucl n, F))) := by
  have := LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := F) (μ := (volume : Measure (Eucl n))) (p := 2))
  intro f g hfg
  exact this hfg

variable [FiniteDimensional ℂ F] {k : ℕ}

/-- **The converse Fourier bridge** (S9a, `W.ofMemSobolev`): every `f ∈ L²(ℝⁿ; F)` which is a
Sobolev distribution of order `k` (Mathlib's `MemSobolev k 2`) is the field of an element of
`W^{k,2}(ℝⁿ; F)` ("Fourier characterization", tex 1463–1477 B0091; tex 308–312 B1009). -/
theorem W.ofMemSobolev {f : Lp F 2 (volume : Measure (Eucl n))}
    (hf : MemSobolev (k : ℝ) 2 (f : 𝓢'(Eucl n, F))) :
    ∃ x : W (wholeSpace n) 1 ℂ F k 2, toVol (W.value (wholeSpace n) 1 ℂ F k 2 x) = f := by
  have hg : ∀ α : Idx n k, ∃ g : Lp F 2 (volume : Measure (Eucl n)),
      dD ((wholeSpace n).word α) (f : 𝓢'(Eucl n, F)) = (g : 𝓢'(Eucl n, F)) := by
    intro α
    have h1 := memSobolev_dD hf ((wholeSpace n).word α)
    have hle : (((wholeSpace n).word α).length : ℝ) ≤ k := by
      rw [TestDomain.length_word]; exact_mod_cast Nat.lt_succ_iff.mp α.1.isLt
    have h2 : MemSobolev 0 2 (dD ((wholeSpace n).word α) (f : 𝓢'(Eucl n, F))) :=
      h1.mono (by linarith)
    exact memSobolev_zero_iff.mp h2
  choose g hg using hg
  have hfg : g Idx.zero = f := by
    apply toTemperedDistribution_injective
    simp only
    rw [← hg Idx.zero]
    rfl
  have hmem : ∀ α, MemLp (fun y => (g α : Eucl n → F) y) 2
      (wμ (wholeSpace n).μ (1 : Weight (Eucl n))) := fun α =>
    by rw [wμ_one]; exact Lp.memLp _
  have hw : ∀ α : Idx n k, HasWeakDeriv (wholeSpace n) ((wholeSpace n).word α)
      ((fun β y => (g β : Eucl n → F) y) Idx.zero) ((fun β y => (g β : Eucl n → F) y) α) := by
    intro α
    apply hasWeakDeriv_of_dD
    rw [hfg]
    exact hg α
  refine ⟨W.ofFields (fun α y => (g α : Eucl n → F) y) hmem hw, ?_⟩
  apply Lp.ext
  rw [← hfg]
  filter_upwards [coeFn_toVol (W.value (wholeSpace n) 1 ℂ F k 2 (W.ofFields _ hmem hw)),
    (ae_eq_wμ_iff volume (1 : Weight (Eucl n))).mp (hmem Idx.zero).coeFn_toLp] with y h1 h2
  rw [h1, W.value_ofFields, h2]

/-- **`W^{k,2}(ℝⁿ) = H^k`** (S9a): an `L²` function is a Sobolev distribution of order `k` iff it
is the field of an element of `W^{k,2}(ℝⁿ; F)`. -/
theorem memSobolev_iff_exists_W {f : Lp F 2 (volume : Measure (Eucl n))} :
    MemSobolev (k : ℝ) 2 (f : 𝓢'(Eucl n, F)) ↔
      ∃ x : W (wholeSpace n) 1 ℂ F k 2, toVol (W.value (wholeSpace n) 1 ℂ F k 2 x) = f := by
  refine ⟨W.ofMemSobolev, ?_⟩
  rintro ⟨x, rfl⟩
  exact W.memSobolev x

end Converse

end UnforcedLeray.Sob
