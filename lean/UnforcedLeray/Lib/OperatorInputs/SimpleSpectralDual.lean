import UnforcedLeray.Lib.Semigroups.Dunford.Deflation

/-!
# A rank-one spectral projection forces a nonzero dual pairing (ExternalInputs E4)


bypass BX12 (replaces `STD:closed-range-simplicity`); Wave 1 block 1G part 4. Blueprint unit
**B0230** (`paper/main.tex` 3923–3948): "Its pairing with the direct eigenvector is nonzero by
algebraic simplicity: otherwise that eigenvector would belong to the range of `L-λ` and admit a
generalized eigenvector" (lines 3940–3943).

The algebraic simplicity of the eigenvalue `z₀` of a bounded operator `L` on a complex Banach
space is encoded, as in the rest of the project, by the Laurent structure
`UnforcedLeray.Infra.Dunford.IsSimpleSpectralProj L P z₀` (vendored from NonUniqueEuler in
`UnforcedLeray/Lib/Semigroups/Dunford/Defs.lean`): `P² = P`, `LP = PL = z₀P`, a punctured
neighbourhood of `z₀` is resolvent, and `(z - L)⁻¹ - (z - z₀)⁻¹P` has a limit `R₀` at `z₀`.
The vendored `Deflation.laurent_limit_identities` gives `(z₀ - L) R₀ = 1 - P`.

* `sub_apply_mem_range`: `x - P x = (z₀ - L)(R₀ x)`, so `ker P ⊆ Ran(L - z₀)`;
* `range_sub_eq_ker`: `Ran(z₀ - L) = ker P`; in particular it is closed (`isClosed_range_sub`).
  This is the closed-range statement of `STD:closed-range-simplicity`.
* `apply_eq_apply_proj`: a functional `g` with `g ∘ L = z₀ g` satisfies `g = g ∘ P`;
* `apply_ne_zero_of_isSimpleSpectralProj` (**E4**): if moreover `P` has rank one with range
  spanned by `q` and `g ≠ 0`, then `g q ≠ 0`.

Compared with the signature proposed in the scoping note, the hypotheses `q ≠ 0` and `P q = q` are
dropped: they are not needed (if `q = 0` then `P = 0`, so `g = g ∘ P = 0`). The statement is
therefore slightly stronger than proposed.

No `sorry`, no axioms.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Infra.Dunford

namespace UnforcedLeray.ExternalInputs

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {L P : X →L[ℂ] X} {z₀ : ℂ}

/-- The deflation identity on vectors: `x - P x = z₀ (R₀ x) - L (R₀ x)` for the regular part
`R₀` of the Laurent expansion at `z₀`. Hence `ker P ⊆ Ran(z₀ - L)`. -/
theorem sub_apply_mem_range (hP : IsSimpleSpectralProj L P z₀) :
    ∃ R₀ : X →L[ℂ] X, ∀ x : X, x - P x = z₀ • R₀ x - L (R₀ x) := by
  obtain ⟨R₀, hR₀⟩ := hP.laurent
  have h := (Deflation.laurent_limit_identities hP hR₀).1
  refine ⟨R₀, fun x => ?_⟩
  have hx := congrArg (fun T : X →L[ℂ] X => T x) h
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.algebraMap_apply, ContinuousLinearMap.one_apply] at hx
  exact hx.symm

/-- `Ran(z₀ - L) ⊆ ker P`, from `P L = z₀ P`. -/
theorem proj_apply_sub_eq_zero (hP : IsSimpleSpectralProj L P z₀) (y : X) :
    P (z₀ • y - L y) = 0 := by
  have h := congrArg (fun T : X →L[ℂ] X => T y) hP.proj_mul
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply] at h
  rw [map_sub, map_smul, h, sub_self]

/-- **Closed range from simplicity** (BX12; `paper/main.tex` 3940–3943): for a simple isolated
eigenvalue `z₀` with spectral projection `P`, `Ran(z₀ - L) = ker P`. -/
theorem range_sub_eq_ker (hP : IsSimpleSpectralProj L P z₀) :
    LinearMap.range ((z₀ • (1 : X →L[ℂ] X) - L : X →L[ℂ] X) : X →ₗ[ℂ] X) =
      LinearMap.ker (P : X →ₗ[ℂ] X) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  constructor
  · rintro ⟨y, rfl⟩
    exact proj_apply_sub_eq_zero hP y
  · intro hx
    obtain ⟨R₀, hR₀⟩ := sub_apply_mem_range hP
    refine ⟨R₀ x, ?_⟩
    rw [← hR₀ x, hx, sub_zero]

/-- The range of `z₀ - L` is closed. -/
theorem isClosed_range_sub (hP : IsSimpleSpectralProj L P z₀) :
    IsClosed (LinearMap.range ((z₀ • (1 : X →L[ℂ] X) - L : X →L[ℂ] X) : X →ₗ[ℂ] X) :
      Set X) := by
  rw [range_sub_eq_ker hP]
  exact ContinuousLinearMap.isClosed_ker P

/-- A left eigenfunctional `g ∘ L = z₀ g` vanishes on `Ran(z₀ - L) = ker P`, hence
`g x = g (P x)` for every `x`. -/
theorem apply_eq_apply_proj (hP : IsSimpleSpectralProj L P z₀) {g : X →L[ℂ] ℂ}
    (hgL : ∀ x, g (L x) = z₀ * g x) (x : X) : g x = g (P x) := by
  obtain ⟨R₀, hR₀⟩ := sub_apply_mem_range hP
  have h : g (x - P x) = 0 := by
    rw [hR₀ x, map_sub, map_smul, hgL, smul_eq_mul, sub_self]
  rw [map_sub, sub_eq_zero] at h
  exact h

/-- **E4: a rank-one spectral projection forces a nonzero dual pairing** (scoping note §5.2 E4,
BX12; B0230, `paper/main.tex` 3940–3943). Let `P` be the spectral projection of the simple
isolated eigenvalue `z₀` of `L` (`IsSimpleSpectralProj`), with range spanned by `q`
(`P x = c • q`). A nonzero bounded functional `g` with `g ∘ L = z₀ g` pairs nontrivially with
`q`: `g q ≠ 0`. -/
theorem apply_ne_zero_of_isSimpleSpectralProj (hP : IsSimpleSpectralProj L P z₀) {q : X}
    (hrank : ∀ x, ∃ c : ℂ, P x = c • q) {g : X →L[ℂ] ℂ} (hg : g ≠ 0)
    (hgL : ∀ x, g (L x) = z₀ * g x) : g q ≠ 0 := by
  intro hq
  apply hg
  ext x
  obtain ⟨c, hc⟩ := hrank x
  rw [apply_eq_apply_proj hP hgL x, hc, map_smul, hq, smul_zero,
    ContinuousLinearMap.zero_apply]

/-- **E4** with the normalization of B0230: under the hypotheses of
`apply_ne_zero_of_isSimpleSpectralProj`, `g` can be rescaled so that its pairing with `q` is
`1`, and then `P x = ℓ x • q`. -/
theorem exists_normalized_dual (hP : IsSimpleSpectralProj L P z₀) {q : X}
    (hrank : ∀ x, ∃ c : ℂ, P x = c • q) {g : X →L[ℂ] ℂ} (hg : g ≠ 0)
    (hgL : ∀ x, g (L x) = z₀ * g x) :
    ∃ ℓ : X →L[ℂ] ℂ, ℓ q = 1 ∧ (∀ x, ℓ (L x) = z₀ * ℓ x) ∧ ∀ x, P x = ℓ x • q := by
  have hgq := apply_ne_zero_of_isSimpleSpectralProj hP hrank hg hgL
  refine ⟨(g q)⁻¹ • g, ?_, fun x => ?_, fun x => ?_⟩
  · simp [hgq]
  · simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hgL]
    ring
  · obtain ⟨c, hc⟩ := hrank x
    have h1 : g x = c * g q := by
      rw [apply_eq_apply_proj hP hgL x, hc, map_smul, smul_eq_mul]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, h1, hc]
    rw [mul_comm c, ← mul_assoc, inv_mul_cancel₀ hgq, one_mul]

end UnforcedLeray.ExternalInputs
