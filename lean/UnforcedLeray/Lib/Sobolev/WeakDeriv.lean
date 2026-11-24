import UnforcedLeray.Lib.Sobolev.TestDomain
import UnforcedLeray.Statement
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Weak derivatives over a test domain (INF11 target S1)

Scoping note `INF11-INF14-Sobolev.md` §5.1 (S1). The manuscript's derivatives are weak
derivatives with the unweighted pairing (tex 13876–13886), periodic on the cylinder
(tex 4573–4577, 13850–13852).

`HasWeakDeriv D vs f g` says `g = ∂_{vs} f` weakly for the test class of `D`:
`∫ (∂_{vs} φ) f dμ = (-1)^{|vs|} ∫ φ g dμ` for every admissible `φ`, *with both pairings
integrable* (the same design as `HasWeakSpatialDerivative` in `Statement.lean:65`, so no junk
value of the Bochner integral is used). The codomain `F` is any real normed space; in a
non-complete `F` every Bochner integral is `0`, so the predicate is only meaningful for
complete `F` (all consumers use finite-dimensional `F`; the uniqueness theorem assumes
`CompleteSpace F`).

## Main results
* `HasWeakDeriv.congr_ae`, `.add`, `.neg`, `.sub`, `.smul`, `.zero`, `.map_clm` (linear calculus);
* `HasWeakDeriv.append`: `∂_{vs}(∂_{ws} f) = ∂_{vs ++ ws} f`; `.perm`; `.cons` (the note's
  form); `.of_cons` (peeling one derivative off, used for `W.partial`);
* `HasWeakDeriv.ae_unique`: locally integrable weak derivatives agree `μ`-a.e.;
* `hasWeakSpatialDerivative_iff`: the bridge to the target statement's
  `HasWeakSpatialDerivative` (same sign convention, `(-1)^1`).

The calculus follows NonUniqueEuler `P/Infra/Sobolev/WeakDeriv.lean` (`HasWeakDerivOn.trans`,
`.perm`, `.congr_ae`), vendored at `lean/NonUniqueEuler/P/Infra/Sobolev/WeakDeriv.lean`;
here tests are real, values are in a real normed space, and integrability is part of the
predicate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Sob

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] {n : ℕ}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Weak derivative** (S1): `g = ∂_{vs} f` weakly for the admissible tests of `D`, with
integrable pairings: `∫ (∂_{vs} φ) • f dμ = (-1)^{|vs|} • ∫ φ • g dμ`. -/
structure HasWeakDeriv (D : TestDomain E n) (vs : List E) (f g : E → F) : Prop where
  int_left : ∀ φ, D.Adm φ → Integrable (fun x => iterDirDeriv vs φ x • f x) D.μ
  int_right : ∀ φ, D.Adm φ → Integrable (fun x => φ x • g x) D.μ
  identity : ∀ φ, D.Adm φ →
    ∫ x, iterDirDeriv vs φ x • f x ∂D.μ = (-1 : ℝ) ^ vs.length • ∫ x, φ x • g x ∂D.μ

namespace HasWeakDeriv

variable {D : TestDomain E n} {vs ws : List E} {f f' g g' h : E → F}

theorem congr_ae (hw : HasWeakDeriv D vs f g) (hf : f =ᵐ[D.μ] f') (hg : g =ᵐ[D.μ] g') :
    HasWeakDeriv D vs f' g' := by
  have ef : ∀ ψ : E → ℝ, (fun x => ψ x • f x) =ᵐ[D.μ] fun x => ψ x • f' x := fun ψ => by
    filter_upwards [hf] with x hx; rw [hx]
  have eg : ∀ ψ : E → ℝ, (fun x => ψ x • g x) =ᵐ[D.μ] fun x => ψ x • g' x := fun ψ => by
    filter_upwards [hg] with x hx; rw [hx]
  refine ⟨fun φ hφ => (hw.int_left φ hφ).congr (ef _), fun φ hφ => (hw.int_right φ hφ).congr
    (eg _), fun φ hφ => ?_⟩
  rw [← integral_congr_ae (ef _), ← integral_congr_ae (eg _)]
  exact hw.identity φ hφ

theorem zero : HasWeakDeriv D vs (0 : E → F) 0 :=
  ⟨fun _ _ => by simpa using (integrable_zero E F D.μ),
    fun _ _ => by simpa using (integrable_zero E F D.μ), fun _ _ => by simp⟩

theorem add {f₁ f₂ g₁ g₂ : E → F} (h₁ : HasWeakDeriv D vs f₁ g₁)
    (h₂ : HasWeakDeriv D vs f₂ g₂) : HasWeakDeriv D vs (f₁ + f₂) (g₁ + g₂) := by
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · simp only [Pi.add_apply, smul_add]; exact (h₁.int_left φ hφ).add (h₂.int_left φ hφ)
  · simp only [Pi.add_apply, smul_add]; exact (h₁.int_right φ hφ).add (h₂.int_right φ hφ)
  · simp only [Pi.add_apply, smul_add]
    rw [integral_add (h₁.int_left φ hφ) (h₂.int_left φ hφ),
      integral_add (h₁.int_right φ hφ) (h₂.int_right φ hφ), h₁.identity φ hφ,
      h₂.identity φ hφ, smul_add]

theorem smul {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
    (hw : HasWeakDeriv D vs f g) (c : 𝕜) : HasWeakDeriv D vs (c • f) (c • g) := by
  have e1 : ∀ (ψ : E → ℝ) (u : E → F),
      (fun x => ψ x • (c • u) x) = fun x => c • (ψ x • u x) := fun ψ u => by
    funext x; simp only [Pi.smul_apply]; exact smul_comm _ _ _
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · rw [e1]; exact (hw.int_left φ hφ).smul c
  · rw [e1]; exact (hw.int_right φ hφ).smul c
  · rw [e1, e1, integral_smul, integral_smul, hw.identity φ hφ]
    exact (smul_comm _ _ _).symm

theorem neg (hw : HasWeakDeriv D vs f g) : HasWeakDeriv D vs (-f) (-g) := by
  simpa using hw.smul (-1 : ℝ)

theorem sub {f₁ f₂ g₁ g₂ : E → F} (h₁ : HasWeakDeriv D vs f₁ g₁)
    (h₂ : HasWeakDeriv D vs f₂ g₂) : HasWeakDeriv D vs (f₁ - f₂) (g₁ - g₂) := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

/-- Weak derivatives commute with continuous linear maps. -/
theorem map_clm [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G]
    (L : F →L[ℝ] G) (hw : HasWeakDeriv D vs f g) :
    HasWeakDeriv D vs (fun x => L (f x)) (fun x => L (g x)) := by
  have e1 : ∀ (ψ : E → ℝ) (u : E → F), (fun x => ψ x • L (u x)) = fun x => L (ψ x • u x) :=
    fun ψ u => by funext x; rw [map_smul]
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · rw [e1]; exact L.integrable_comp (hw.int_left φ hφ)
  · rw [e1]; exact L.integrable_comp (hw.int_right φ hφ)
  · rw [e1, e1, L.integral_comp_comm (hw.int_left φ hφ), L.integral_comp_comm
      (hw.int_right φ hφ), hw.identity φ hφ, map_smul]

/-- `∂_{vs}(∂_{ws} f) = ∂_{vs ++ ws} f`: if `g = ∂_{vs} f` and `h = ∂_{ws} g` weakly, then
`h = ∂_{vs ++ ws} f` weakly. -/
theorem append (h₁ : HasWeakDeriv D vs f g) (h₂ : HasWeakDeriv D ws g h) :
    HasWeakDeriv D (vs ++ ws) f h := by
  refine ⟨fun φ hφ => ?_, fun φ hφ => h₂.int_right φ hφ, fun φ hφ => ?_⟩
  · rw [iterDirDeriv_append]
    exact h₁.int_left _ (D.adm_iterDirDeriv hφ ws)
  · rw [iterDirDeriv_append, h₁.identity _ (D.adm_iterDirDeriv hφ ws), h₂.identity φ hφ,
      smul_smul, List.length_append, pow_add]

/-- The order of the directions does not matter. -/
theorem perm (hp : vs.Perm ws) (hw : HasWeakDeriv D vs f g) : HasWeakDeriv D ws f g := by
  refine ⟨fun φ hφ => ?_, hw.int_right, fun φ hφ => ?_⟩
  · rw [← iterDirDeriv_perm hp (D.smooth hφ)]; exact hw.int_left φ hφ
  · rw [← iterDirDeriv_perm hp (D.smooth hφ), hw.identity φ hφ, hp.length_eq]

/-- The note's form of the chain: `g = ∂_{vs} f` and `g' = ∂_v g` give `g' = ∂_{v :: vs} f`. -/
theorem cons {v : E} (hw : HasWeakDeriv D vs f g) (h' : HasWeakDeriv D [v] g g') :
    HasWeakDeriv D (v :: vs) f g' :=
  (hw.append h').perm (List.perm_append_singleton v vs)

/-- Peeling one derivative off: if `g = ∂_v f` and `h = ∂_{v :: vs} f` weakly, then
`h = ∂_{vs} g` weakly. -/
theorem of_cons {v : E} (h₁ : HasWeakDeriv D [v] f g) (h₂ : HasWeakDeriv D (v :: vs) f h) :
    HasWeakDeriv D vs g h := by
  refine ⟨fun φ hφ => h₁.int_right _ (D.adm_iterDirDeriv hφ vs), h₂.int_right,
    fun φ hφ => ?_⟩
  have e1 := h₁.identity _ (D.adm_iterDirDeriv hφ vs)
  have e2 := h₂.identity φ hφ
  simp only [iterDirDeriv_cons, iterDirDeriv_nil] at e1 e2
  rw [e1] at e2
  simp only [List.length_cons, List.length_nil, zero_add] at e2
  calc ∫ x, iterDirDeriv vs φ x • g x ∂D.μ
      = (-1 : ℝ) • ((-1 : ℝ) ^ 1 • ∫ x, iterDirDeriv vs φ x • g x ∂D.μ) := by
        rw [smul_smul]; norm_num
    _ = (-1 : ℝ) • ((-1 : ℝ) ^ (vs.length + 1) • ∫ x, φ x • h x ∂D.μ) := by rw [e2]
    _ = (-1 : ℝ) ^ vs.length • ∫ x, φ x • h x ∂D.μ := by
        rw [smul_smul]; congr 1; ring

/-- The empty word: `f` is its own weak `0`-th derivative once the pairings converge. -/
theorem nil (hf : ∀ φ, D.Adm φ → Integrable (fun x => φ x • f x) D.μ) :
    HasWeakDeriv D [] f f :=
  ⟨fun φ hφ => by simpa using hf φ hφ, hf, fun φ _ => by simp⟩

/-- **Uniqueness** (S1): two locally integrable weak derivatives of the same function agree
`μ`-a.e. -/
theorem ae_unique [CompleteSpace F] [SecondCountableTopology F] {g₁ g₂ : E → F}
    (h₁ : HasWeakDeriv D vs f g₁) (h₂ : HasWeakDeriv D vs f g₂)
    (hg₁ : LocallyIntegrable g₁ D.μ) (hg₂ : LocallyIntegrable g₂ D.μ) : g₁ =ᵐ[D.μ] g₂ := by
  have hd : LocallyIntegrable (g₁ - g₂) D.μ := hg₁.sub hg₂
  have hpair : ∀ φ, D.Adm φ → ∫ x, φ x • (g₁ - g₂) x ∂D.μ = 0 := by
    intro φ hφ
    have e := (h₁.identity φ hφ).symm.trans (h₂.identity φ hφ)
    have hne : ((-1 : ℝ) ^ vs.length) ≠ 0 := pow_ne_zero _ (by norm_num)
    have e' : ∫ x, φ x • g₁ x ∂D.μ = ∫ x, φ x • g₂ x ∂D.μ := smul_right_injective F hne e
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub (h₁.int_right φ hφ) (h₂.int_right φ hφ), e', sub_self]
  have hz : g₁ - g₂ =ᵐ[D.μ] 0 := by
    apply ae_eq_zero_of_forall_dual (𝕜 := ℝ)
    intro c
    apply D.ae_zero
    · intro x
      obtain ⟨s, hs, hint⟩ := hd x
      exact ⟨s, hs, c.integrable_comp hint⟩
    · intro φ hφ
      have hint : Integrable (fun x => φ x • (g₁ - g₂) x) D.μ := by
        simp only [Pi.sub_apply, smul_sub]
        exact (h₁.int_right φ hφ).sub (h₂.int_right φ hφ)
      have e1 : (fun x => φ x * c ((g₁ - g₂) x)) = fun x => c (φ x • (g₁ - g₂) x) := by
        funext x; rw [map_smul, smul_eq_mul]
      rw [e1, c.integral_comp_comm hint, hpair φ hφ, map_zero]
  filter_upwards [hz] with x hx
  exact sub_eq_zero.mp hx

end HasWeakDeriv

/-! ### Bridge to the target statement -/

theorem iterDirDeriv_single_e (i : Fin 3) (φ : Space → ℝ) :
    iterDirDeriv [e i] φ = spatialTestDerivative i φ := rfl

/-- `HasWeakSpatialDerivative` of `Statement.lean:65` is `HasWeakDeriv (wholeSpace 3) [e i]`
(same sign: `-(∫ φ g) = (-1)^1 • ∫ φ g`). -/
theorem hasWeakSpatialDerivative_iff {i : Fin 3} {f g : Space → Space} :
    HasWeakSpatialDerivative i f g ↔ HasWeakDeriv (wholeSpace 3) [e i] f g := by
  have hadm : ∀ φ : Space → ℝ, IsSpatialTest φ ↔ (wholeSpace 3).Adm φ := fun φ =>
    ⟨fun h => ⟨h.smooth, h.compact⟩, fun h => ⟨h.1, h.2⟩⟩
  constructor
  · intro h
    refine ⟨fun φ hφ => h.left_integrable φ ((hadm φ).2 hφ),
      fun φ hφ => h.right_integrable φ ((hadm φ).2 hφ), fun φ hφ => ?_⟩
    simp only [wholeSpace_μ, List.length_singleton, pow_one, neg_smul, one_smul]
    exact h.identity φ ((hadm φ).2 hφ)
  · intro h
    refine ⟨fun φ hφ => h.int_left φ ((hadm φ).1 hφ),
      fun φ hφ => h.int_right φ ((hadm φ).1 hφ), fun φ hφ => ?_⟩
    have := h.identity φ ((hadm φ).1 hφ)
    simp only [wholeSpace_μ, List.length_singleton, pow_one, neg_smul, one_smul] at this
    exact this

end UnforcedLeray.Sob
