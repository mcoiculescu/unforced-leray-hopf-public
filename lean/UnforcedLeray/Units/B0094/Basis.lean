import UnforcedLeray.Units.B0094.Diagonal
import UnforcedLeray.Units.B0094.Density
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Algebra.Polynomial.Basis

/-!
# B0094 helper: the oscillator eigenbasis of `X_G` and the core operator

Blueprint unit B0094 (`eq:st18-t00068`, `paper/main.tex` lines 1503--1515).

* `oscBasis : HilbertBasis ℕ ℂ XG` is the Gram–Schmidt orthonormalization of the monomial
  profiles `r^{2+2k} e^{-r²/4}`; it is a Hilbert basis by `eq_zero_of_inner_prof_X_pow`
  (completeness). Its `ℓ`-th vector is, up to normalization, the Laguerre function
  `r² L_ℓ^{(2)}(r²/4) e^{-r²/4}` (the unit's notes); we never need the Laguerre formula.
* `oscBasis_eigen`: `oscBasis ℓ = prof q` for a polynomial `q` with `lag q = -ℓ q`: the
  angular-two oscillator level `N = 2 + 2ℓ` has eigenvalue `-ℓ` (tex lines 1506--1510).
  Proof: `lag` is triangular on the monomials with diagonal `-ℓ`
  (`lag Xᵏ = 4k(k+2) X^{k-1} - k Xᵏ`) and symmetric (`inner_lag_symm`).
* `Dcore`: the operator `D = Δ + ½ y·∇ + 2` on the core of Gaussian-polynomial profiles,
  `prof p ↦ prof (lag p)`; it is symmetric, and `Dcore_closure` shows that it is closable with
  closure `diagOp oscBasis`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Polynomial InnerProductSpace
open scoped ComplexConjugate InnerProductSpace

namespace UnforcedLeray.B0094

open UnforcedLeray.B0010

/-- The monomial profiles `v k = r^{2+2k} e^{-r²/4}` in `X_G`. -/
def vmono (k : ℕ) : XG := prof (X ^ k)

theorem linearIndependent_vmono : LinearIndependent ℂ vmono := by
  have h := (Polynomial.basisMonomials ℂ).linearIndependent.map' prof
    (LinearMap.ker_eq_bot.2 prof_injective)
  have e : vmono = ⇑prof ∘ ⇑(Polynomial.basisMonomials ℂ) := by
    funext k
    simp [vmono, Polynomial.coe_basisMonomials, X_pow_eq_monomial]
  rw [e]
  exact h

/-- The orthonormal oscillator eigenvectors: Gram–Schmidt applied to `v k`. -/
def osc (n : ℕ) : XG := gramSchmidtNormed ℂ vmono n

theorem orthonormal_osc : Orthonormal ℂ osc :=
  gramSchmidtNormed_orthonormal linearIndependent_vmono

theorem span_osc : Submodule.span ℂ (Set.range osc) = Submodule.span ℂ (Set.range vmono) := by
  change Submodule.span ℂ (Set.range (gramSchmidtNormed ℂ vmono)) = _
  rw [span_gramSchmidtNormed_range, span_gramSchmidt]

theorem orthogonal_span_vmono : (Submodule.span ℂ (Set.range vmono))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  apply eq_zero_of_inner_prof_X_pow x
  intro k
  exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self k)) hx

/-- The Hilbert basis of `X_G` formed by the angular-two oscillator eigenvectors. -/
def oscBasis : HilbertBasis ℕ ℂ XG :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_osc (by rw [span_osc]; exact orthogonal_span_vmono)

theorem coe_oscBasis : ⇑oscBasis = osc :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-! ## Triangularity of `lag` -/

/-- Polynomials of degree `< n`, as the span of the monomials. -/
def polyLT (n : ℕ) : Submodule ℂ ℂ[X] := Submodule.span ℂ ((fun k : ℕ => (X : ℂ[X]) ^ k) '' Iio n)

theorem X_pow_mem_polyLT {k n : ℕ} (h : k < n) : (X : ℂ[X]) ^ k ∈ polyLT n :=
  Submodule.subset_span (Set.mem_image_of_mem _ h)

theorem map_prof_polyLT (n : ℕ) :
    (polyLT n).map prof = Submodule.span ℂ (vmono '' Iio n) := by
  rw [polyLT, Submodule.map_span, Set.image_image]
  rfl

theorem lag_mem_polyLT {n : ℕ} {s : ℂ[X]} (hs : s ∈ polyLT n) : lag s ∈ polyLT n := by
  have : polyLT n ≤ (polyLT n).comap lag := by
    rw [polyLT, Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, lag_X_pow]
    refine Submodule.sub_mem _ (Submodule.smul_mem _ _ (X_pow_mem_polyLT ?_))
      (Submodule.smul_mem _ _ (X_pow_mem_polyLT hk))
    exact lt_of_le_of_lt (Nat.sub_le k 1) hk
  exact this hs

theorem lag_X_pow_add_mem (n : ℕ) : lag (X ^ n) + (n : ℂ) • X ^ n ∈ polyLT n := by
  rw [lag_X_pow, sub_add_cancel]
  rcases n with _ | n
  · simp
  · exact Submodule.smul_mem _ _ (X_pow_mem_polyLT (by omega))

/-! ## Gram–Schmidt vectors are eigenvectors -/

theorem gramSchmidt_sub_mem (n : ℕ) :
    gramSchmidt ℂ vmono n - vmono n ∈ Submodule.span ℂ (vmono '' Iio n) := by
  rw [← span_gramSchmidt_Iio]
  have h := gramSchmidt_def'' ℂ vmono n
  have : gramSchmidt ℂ vmono n - vmono n = -∑ i ∈ Finset.Iio n,
      (⟪gramSchmidt ℂ vmono i, vmono n⟫_ℂ / (‖gramSchmidt ℂ vmono i‖ : ℂ) ^ 2) •
        gramSchmidt ℂ vmono i := by
    conv_lhs => rw [h]
    abel
  rw [this]
  refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span ⟨i, Finset.mem_Iio.1 hi, rfl⟩

theorem inner_span_gramSchmidt (n : ℕ) {x : XG} (hx : x ∈ Submodule.span ℂ (vmono '' Iio n)) :
    ⟪x, gramSchmidt ℂ vmono n⟫_ℂ = 0 := by
  rw [← span_gramSchmidt_Iio] at hx
  have hle : Submodule.span ℂ (gramSchmidt ℂ vmono '' Iio n) ≤
      (ℂ ∙ gramSchmidt ℂ vmono n)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact gramSchmidt_orthogonal ℂ vmono (ne_of_lt hi)
  exact (Submodule.mem_orthogonal_singleton_iff_inner_left).1 (hle hx)

theorem gramSchmidt_eigen (n : ℕ) :
    ∃ q : ℂ[X], gramSchmidt ℂ vmono n = prof q ∧ prof (lag q) = -(n : ℂ) • prof q := by
  -- pull back the polynomial
  obtain ⟨s, hs, hsprof⟩ : ∃ s ∈ polyLT n, prof s = gramSchmidt ℂ vmono n - vmono n := by
    have := gramSchmidt_sub_mem n
    rw [← map_prof_polyLT, Submodule.mem_map] at this
    exact this
  set q := X ^ n + s with hq
  have hqprof : gramSchmidt ℂ vmono n = prof q := by
    rw [hq, map_add, hsprof]
    simp [vmono]
  refine ⟨q, hqprof, ?_⟩
  set t := lag q + (n : ℂ) • q with ht
  have htmem : t ∈ polyLT n := by
    have : t = (lag (X ^ n) + (n : ℂ) • X ^ n) + (lag s + (n : ℂ) • s) := by
      rw [ht, hq, map_add, smul_add]
      abel
    rw [this]
    exact Submodule.add_mem _ (lag_X_pow_add_mem n)
      (Submodule.add_mem _ (lag_mem_polyLT hs) (Submodule.smul_mem _ _ hs))
  have hperp : ∀ s' ∈ polyLT n, ⟪prof s', prof q⟫_ℂ = 0 := by
    intro s' hs'
    rw [← hqprof]
    apply inner_span_gramSchmidt
    rw [← map_prof_polyLT]
    exact Submodule.mem_map_of_mem hs'
  have horth : ∀ s' ∈ polyLT n, ⟪prof s', prof t⟫_ℂ = 0 := by
    intro s' hs'
    rw [ht, map_add, map_smul, inner_add_right, inner_smul_right, ← inner_lag_symm,
      hperp _ (lag_mem_polyLT hs'), hperp _ hs', mul_zero, add_zero]
  have h0 : prof t = 0 := inner_self_eq_zero.1 (horth t htmem)
  rw [ht, map_add, map_smul] at h0
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left h0

theorem osc_eigen (n : ℕ) :
    ∃ q : ℂ[X], osc n = prof q ∧ prof (lag q) = -(n : ℂ) • prof q := by
  obtain ⟨q, hq, hlag⟩ := gramSchmidt_eigen n
  set c : ℂ := (‖gramSchmidt ℂ vmono n‖ : ℂ)⁻¹ with hc
  have hosc : osc n = c • gramSchmidt ℂ vmono n := rfl
  refine ⟨c • q, ?_, ?_⟩
  · rw [hosc, hq, map_smul]
  · simp only [map_smul, hlag]
    rw [smul_comm]

/-! ## The core operator -/

/-- The parametrization of the core by polynomials. -/
def coreEquiv : ℂ[X] ≃ₗ[ℂ] LinearMap.range prof := LinearEquiv.ofInjective prof prof_injective

/-- The operator `D = Δ + ½ y·∇ + 2` on the core of Gaussian-polynomial profiles
`r² p(r²) e^{-r²/4}` (see `Planar.lean` for the identification with the planar operator). -/
def Dcore : XG →ₗ.[ℂ] XG where
  domain := LinearMap.range prof
  toFun := prof ∘ₗ lag ∘ₗ coreEquiv.symm.toLinearMap

theorem mem_Dcore_domain (p : ℂ[X]) : prof p ∈ Dcore.domain := ⟨p, rfl⟩

theorem Dcore_apply (p : ℂ[X]) (hp : prof p ∈ Dcore.domain) :
    Dcore ⟨prof p, hp⟩ = prof (lag p) := by
  have : coreEquiv.symm ⟨prof p, hp⟩ = p := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext (LinearEquiv.ofInjective_apply _ _).symm
  change prof (lag (coreEquiv.symm ⟨prof p, hp⟩)) = _
  rw [this]

theorem Dcore_apply' (x : Dcore.domain) (p : ℂ[X]) (hx : (x : XG) = prof p) :
    Dcore x = prof (lag p) := by
  have : x = ⟨prof p, mem_Dcore_domain p⟩ := Subtype.ext hx
  rw [this, Dcore_apply]

theorem Dcore_symm (x y : Dcore.domain) :
    ⟪Dcore x, (y : XG)⟫_ℂ = ⟪(x : XG), Dcore y⟫_ℂ := by
  obtain ⟨p, hp⟩ := x.2
  obtain ⟨q, hq⟩ := y.2
  rw [Dcore_apply' x p hp.symm, Dcore_apply' y q hq.symm, ← hp, ← hq]
  exact inner_lag_symm p q

theorem oscBasis_mem_Dcore (n : ℕ) : oscBasis n ∈ Dcore.domain := by
  obtain ⟨q, hq, -⟩ := osc_eigen n
  rw [coe_oscBasis, hq]
  exact mem_Dcore_domain q

theorem Dcore_oscBasis (n : ℕ) :
    Dcore ⟨oscBasis n, oscBasis_mem_Dcore n⟩ = -(n : ℂ) • oscBasis n := by
  obtain ⟨q, hq, hlag⟩ := osc_eigen n
  have he : oscBasis n = prof q := by rw [coe_oscBasis, hq]
  rw [Dcore_apply' _ q he, hlag, he]

/-- The core operator is closable and its closure is `diag(-ℓ)` in the oscillator basis. -/
theorem Dcore_closure : Dcore.IsClosable ∧ Dcore.closure = diagOp oscBasis :=
  closure_eq_diagOp oscBasis Dcore_symm oscBasis_mem_Dcore Dcore_oscBasis

end UnforcedLeray.B0094
