import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Tactic

/-!
# B0094 helper: the diagonal model `diag(-ℓ)` in a Hilbert basis

Blueprint unit B0094 (`eq:st18-t00068`, `paper/main.tex` lines 1503--1515). The unit's notes
(blueprint `units.json`) recommend the model used here: identify `X_G` with `ℓ²(ℕ)` through the
orthonormal eigenbasis of the angular-two oscillator levels and let `D = diag(-ℓ)`.

This file is abstract: `H` is any complex Hilbert space with a Hilbert basis `b : ℕ → H`.
* `diagOp b` is the unbounded operator `f ↦ ∑ (-ℓ) ⟪b ℓ, f⟫ b ℓ` with the coefficient domain
  `{f : ∑ ℓ² |⟪b ℓ, f⟫|² < ∞}` (equivalently `∑ (1 + ℓ²) |⟪b ℓ, f⟫|² < ∞`, tex line 1512);
* `isSelfAdjoint_diagOp`: it is selfadjoint (`D† = D` for the `LinearPMap` adjoint);
* `diagOp_nonpos`: `⟪f, D f⟫` is real and `≤ 0`;
* `opSpectrum`: the spectrum of an unbounded operator (complement of the set of `μ` for which
  `T - μ` is a bijection of the domain onto `H` with bounded inverse), and
  `opSpectrum_diagOp`: the spectrum of `diag(-ℓ)` is `{0, -1, -2, …}`;
* `closure_eq_diagOp`: a symmetric operator whose domain contains the basis and which has
  `T b ℓ = -ℓ b ℓ` has closure `diag(-ℓ)` (the basis is a core);
* `diagCLM`: bounded diagonal operators (e.g. the resolvent and `e^{aD}`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

open scoped InnerProductSpace ComplexConjugate ENNReal
open Filter Topology

namespace UnforcedLeray.B0094

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Small facts on `ℓ²(ℕ, ℂ)` -/

/-- Comparison test in `ℓ²`. -/
theorem memℓp_two_of_norm_le {f g : ℕ → ℂ} (C : ℝ) (hg : Memℓp g 2)
    (h : ∀ i, ‖f i‖ ≤ C * ‖g i‖) : Memℓp f 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  apply memℓp_gen
  have hs := hg.summable hp
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs ⊢
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (hs.mul_left (C ^ 2))
  calc ‖f i‖ ^ 2 ≤ (C * ‖g i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (h i) 2
    _ = C ^ 2 * ‖g i‖ ^ 2 := by ring

/-- Norm comparison in `ℓ²`. -/
theorem lp_norm_le_of_le {v w : lp (fun _ : ℕ => ℂ) 2} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖v i‖ ≤ C * ‖w i‖) : ‖v‖ ≤ C * ‖w‖ := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  apply lp.norm_le_of_tsum_le hp (by positivity)
  rw [Real.mul_rpow hC (norm_nonneg _), lp.norm_rpow_eq_tsum hp, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun i => ?_) ((lp.memℓp v).summable hp)
    (((lp.memℓp w).summable hp).mul_left _)
  rw [← Real.mul_rpow hC (norm_nonneg _)]
  exact Real.rpow_le_rpow (norm_nonneg _) (h i) (by norm_num)

variable (b : HilbertBasis ℕ ℂ H)

theorem inner_repr_symm (v : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    ⟪b n, b.repr.symm v⟫_ℂ = v n := by
  rw [← b.repr_apply_apply, LinearIsometryEquiv.apply_symm_apply]

/-- Two vectors with the same coefficients in a Hilbert basis are equal. -/
theorem ext_inner_basis {x y : H} (h : ∀ n, ⟪b n, x⟫_ℂ = ⟪b n, y⟫_ℂ) : x = y := by
  apply b.repr.injective
  ext n
  rw [b.repr_apply_apply, b.repr_apply_apply, h]

theorem inner_basis_basis (m n : ℕ) : ⟪b m, b n⟫_ℂ = if m = n then 1 else 0 := by
  exact (orthonormal_iff_ite.1 b.orthonormal) m n

/-! ## The diagonal operator `diag(-ℓ)` -/

/-- The domain of `diag(-ℓ)`: `∑ ℓ² |⟪b ℓ, f⟫|² < ∞`. -/
def diagDomain : Submodule ℂ H where
  carrier := {f | Memℓp (fun n : ℕ => (n : ℂ) * ⟪b n, f⟫_ℂ) 2}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, inner_zero_right, mul_zero]
    exact zero_mem_ℓp'
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq, inner_add_right, mul_add] at hf hg ⊢
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_setOf_eq, inner_smul_right] at hf ⊢
    have := hf.const_smul c
    convert this using 1
    funext n
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- The coefficient sequence `(-ℓ ⟪b ℓ, f⟫)_ℓ ∈ ℓ²`. -/
def diagSeq (f : diagDomain b) : lp (fun _ : ℕ => ℂ) 2 :=
  ⟨fun n => -((n : ℂ) * ⟪b n, (f : H)⟫_ℂ), f.2.neg⟩

/-- The linear map `f ↦ ∑ (-ℓ) ⟪b ℓ, f⟫ b ℓ` on the domain. -/
def diagLin : diagDomain b →ₗ[ℂ] H where
  toFun f := b.repr.symm (diagSeq b f)
  map_add' f g := by
    rw [← map_add]
    congr 1
    ext n
    simp only [diagSeq, Submodule.coe_add, inner_add_right, lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' c f := by
    rw [RingHom.id_apply, ← map_smul]
    congr 1
    ext n
    simp only [diagSeq, Submodule.coe_smul, inner_smul_right, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul]
    ring

/-- The diagonal operator `D = diag(-ℓ)` in the Hilbert basis `b`, with its maximal
coefficient domain (tex lines 1511--1514). -/
def diagOp : H →ₗ.[ℂ] H := ⟨diagDomain b, diagLin b⟩

theorem mem_diagOp_domain_iff (f : H) :
    f ∈ (diagOp b).domain ↔ Memℓp (fun n : ℕ => (n : ℂ) * ⟪b n, f⟫_ℂ) 2 := Iff.rfl

/-- The domain in the form of tex line 1512: `∑ (1 + ℓ²) ‖f_ℓ‖² < ∞`, where
`‖f_ℓ‖ = |⟪b ℓ, f⟫|` is the norm of the component of `f` in the `ℓ`-th eigenspace. -/
theorem mem_diagOp_domain_iff_summable (f : H) :
    f ∈ (diagOp b).domain ↔
      Summable fun n : ℕ => (1 + (n : ℝ) ^ 2) * ‖⟪b n, f⟫_ℂ‖ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hb : Summable fun n : ℕ => ‖⟪b n, f⟫_ℂ‖ ^ 2 := by
    have := (lp.memℓp (b.repr f)).summable hp
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr_apply_apply] at this
    exact this
  rw [mem_diagOp_domain_iff, memℓp_gen_iff hp]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, Complex.norm_natCast, mul_pow]
  constructor
  · intro h
    simpa only [add_mul, one_mul] using hb.add h
  · intro h
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h
    nlinarith [sq_nonneg ‖⟪b n, f⟫_ℂ‖]

theorem inner_diagOp (f : (diagOp b).domain) (n : ℕ) :
    ⟪b n, diagOp b f⟫_ℂ = -(n : ℂ) * ⟪b n, (f : H)⟫_ℂ := by
  change ⟪b n, b.repr.symm (diagSeq b f)⟫_ℂ = _
  rw [inner_repr_symm]
  change -((n : ℂ) * ⟪b n, (f : H)⟫_ℂ) = _
  ring

/-- A vector `x` lies in the domain with `D x = y` as soon as the coefficients match. -/
theorem exists_diagOp_eq (x y : H) (h : ∀ n, ⟪b n, y⟫_ℂ = -(n : ℂ) * ⟪b n, x⟫_ℂ) :
    ∃ hx : x ∈ (diagOp b).domain, diagOp b ⟨x, hx⟩ = y := by
  have hx : x ∈ (diagOp b).domain := by
    rw [mem_diagOp_domain_iff]
    have hfun : (fun n : ℕ => (n : ℂ) * ⟪b n, x⟫_ℂ) = -⇑(b.repr y) := by
      funext n
      rw [Pi.neg_apply, b.repr_apply_apply, h]
      ring
    rw [hfun]
    exact (lp.memℓp (b.repr y)).neg
  exact ⟨hx, ext_inner_basis b fun n => by rw [inner_diagOp, h]⟩

/-- Characterization of the graph of `D` by coefficients. -/
theorem diagOp_graph_iff (x y : H) :
    (∃ hx : x ∈ (diagOp b).domain, diagOp b ⟨x, hx⟩ = y) ↔
      ∀ n, ⟪b n, y⟫_ℂ = -(n : ℂ) * ⟪b n, x⟫_ℂ := by
  constructor
  · rintro ⟨hx, rfl⟩ n
    exact inner_diagOp b ⟨x, hx⟩ n
  · exact exists_diagOp_eq b x y

theorem basis_mem_domain (n : ℕ) : b n ∈ (diagOp b).domain := by
  rw [mem_diagOp_domain_iff]
  have hfun : (fun m : ℕ => (m : ℂ) * ⟪b m, b n⟫_ℂ) = (n : ℂ) • ⇑(b.repr (b n)) := by
    funext m
    rw [Pi.smul_apply, smul_eq_mul, b.repr_apply_apply, inner_basis_basis]
    split_ifs with h
    · rw [h]
    · simp
  rw [hfun]
  exact (lp.memℓp (b.repr (b n))).const_smul (n : ℂ)

/-- The basis vectors are eigenvectors: `D b ℓ = -ℓ b ℓ`. -/
theorem diagOp_basis (n : ℕ) :
    diagOp b ⟨b n, basis_mem_domain b n⟩ = -(n : ℂ) • b n := by
  apply ext_inner_basis b
  intro m
  rw [inner_diagOp, inner_smul_right, inner_basis_basis]
  split_ifs with h
  · rw [h]
  · simp

/-- `D` is symmetric. -/
theorem diagOp_symm (x y : (diagOp b).domain) :
    ⟪diagOp b x, (y : H)⟫_ℂ = ⟪(x : H), diagOp b y⟫_ℂ := by
  rw [← b.tsum_inner_mul_inner, ← b.tsum_inner_mul_inner]
  congr 1
  funext n
  rw [← inner_conj_symm (diagOp b x) (b n), inner_diagOp, inner_diagOp, map_mul, map_neg,
    Complex.conj_natCast, inner_conj_symm]
  ring

theorem dense_diagOp_domain : Dense ((diagOp b).domain : Set H) := by
  have hle : Submodule.span ℂ (Set.range b) ≤ (diagOp b).domain :=
    Submodule.span_le.2 (by rintro _ ⟨n, rfl⟩; exact basis_mem_domain b n)
  have hd : Dense (Submodule.span ℂ (Set.range b) : Set H) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2 b.dense_span
  exact hd.mono hle

/-- **Selfadjointness** of `diag(-ℓ)`. -/
theorem isSelfAdjoint_diagOp : IsSelfAdjoint (diagOp b) := by
  rw [LinearPMap.isSelfAdjoint_def]
  have hd := dense_diagOp_domain b
  have hadj : ∀ g : (diagOp b).adjoint.domain, ∀ n,
      ⟪b n, (diagOp b).adjoint g⟫_ℂ = -(n : ℂ) * ⟪b n, (g : H)⟫_ℂ := by
    intro g n
    have h1 := LinearPMap.adjoint_isFormalAdjoint hd g ⟨b n, basis_mem_domain b n⟩
    rw [diagOp_basis, inner_smul_right] at h1
    rw [← inner_conj_symm, h1, map_mul, map_neg, Complex.conj_natCast, inner_conj_symm]
  apply le_antisymm
  · refine ⟨fun g hg => (exists_diagOp_eq b g _ (hadj ⟨g, hg⟩)).1, fun x y hxy => ?_⟩
    obtain ⟨hx', hD⟩ := exists_diagOp_eq b x _ (hadj x)
    have : y = ⟨x, hx'⟩ := Subtype.ext hxy.symm
    rw [this, hD]
  · exact LinearPMap.IsFormalAdjoint.le_adjoint hd (fun x y => diagOp_symm b x y)

/-- The quadratic form: `⟪f, D f⟫ = -∑ ℓ |⟪b ℓ, f⟫|²`. -/
theorem hasSum_inner_diagOp_self (f : (diagOp b).domain) :
    HasSum (fun n : ℕ => -((n : ℂ) * ((‖⟪b n, (f : H)⟫_ℂ‖ ^ 2 : ℝ) : ℂ)))
      ⟪(f : H), diagOp b f⟫_ℂ := by
  have e : (fun n : ℕ => -((n : ℂ) * ((‖⟪b n, (f : H)⟫_ℂ‖ ^ 2 : ℝ) : ℂ))) =
      fun n => ⟪(f : H), b n⟫_ℂ * ⟪b n, diagOp b f⟫_ℂ := by
    funext n
    rw [inner_diagOp, ← inner_conj_symm (f : H) (b n)]
    push_cast
    rw [← Complex.conj_mul']
    ring
  rw [e]
  exact b.hasSum_inner_mul_inner (f : H) (diagOp b f)

/-- **Nonpositivity**: `⟪f, D f⟫` is real and nonpositive (`D ≤ 0`, tex line 1509). -/
theorem diagOp_nonpos (f : (diagOp b).domain) :
    (⟪(f : H), diagOp b f⟫_ℂ).re ≤ 0 ∧ (⟪(f : H), diagOp b f⟫_ℂ).im = 0 := by
  have h := hasSum_inner_diagOp_self b f
  constructor
  · have hre := Complex.hasSum_re h
    refine hasSum_le (fun n => ?_) hre hasSum_zero
    simp only [Complex.neg_re, Complex.mul_re, Complex.natCast_re, Complex.ofReal_re,
      Complex.natCast_im, Complex.ofReal_im, mul_zero, sub_zero]
    have : (0 : ℝ) ≤ (n : ℝ) * ‖⟪b n, (f : H)⟫_ℂ‖ ^ 2 := by positivity
    linarith
  · have him := Complex.hasSum_im h
    have h0 : (fun n : ℕ => (-((n : ℂ) * ((‖⟪b n, (f : H)⟫_ℂ‖ ^ 2 : ℝ) : ℂ))).im) = 0 := by
      funext n
      simp only [Complex.neg_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero, neg_zero,
        Pi.zero_apply]
    rw [h0] at him
    exact him.unique hasSum_zero

/-! ## Bounded diagonal operators -/

/-- The bounded diagonal operator with coefficients `c`, `|c ℓ| ≤ C`. -/
def diagCLM (c : ℕ → ℂ) (C : ℝ) (hc : ∀ n, ‖c n‖ ≤ C) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun x => b.repr.symm ⟨fun n => c n * ⟪b n, x⟫_ℂ,
        memℓp_two_of_norm_le C (lp.memℓp (b.repr x)) (fun n => by
          rw [norm_mul, b.repr_apply_apply]
          exact mul_le_mul_of_nonneg_right (hc n) (norm_nonneg _))⟩
      map_add' := fun x y => by
        rw [← map_add]
        congr 1
        ext n
        simp only [inner_add_right, lp.coeFn_add, Pi.add_apply]
        ring
      map_smul' := fun a x => by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        ext n
        simp only [inner_smul_right, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        ring }
    C (fun x => by
      have hC : 0 ≤ C := (norm_nonneg _).trans (hc 0)
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearIsometryEquiv.norm_map]
      rw [← b.repr.norm_map x]
      apply lp_norm_le_of_le hC
      intro n
      change ‖c n * ⟪b n, x⟫_ℂ‖ ≤ C * ‖b.repr x n‖
      rw [norm_mul, b.repr_apply_apply]
      exact mul_le_mul_of_nonneg_right (hc n) (norm_nonneg _))

theorem inner_diagCLM (c : ℕ → ℂ) (C : ℝ) (hc : ∀ n, ‖c n‖ ≤ C) (x : H) (n : ℕ) :
    ⟪b n, diagCLM b c C hc x⟫_ℂ = c n * ⟪b n, x⟫_ℂ := by
  simp only [diagCLM, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [inner_repr_symm]

/-! ## The spectrum -/

/-- The resolvent set of an unbounded operator `T`: the `μ` for which `T - μ` maps `T.domain`
bijectively onto `H` with a bounded inverse `R`. -/
def resolventSet (T : H →ₗ.[ℂ] H) : Set ℂ :=
  {μ | ∃ R : H →L[ℂ] H, ∃ hR : ∀ x, R x ∈ T.domain,
    (∀ x, T ⟨R x, hR x⟩ - μ • R x = x) ∧ ∀ x : T.domain, R (T x - μ • (x : H)) = x}

/-- The spectrum of an unbounded operator. -/
def opSpectrum (T : H →ₗ.[ℂ] H) : Set ℂ := (resolventSet T)ᶜ

theorem exists_dist_pos {μ : ℂ} (hμ : μ ∉ Set.range fun n : ℕ => -(n : ℂ)) :
    ∃ δ > 0, ∀ n : ℕ, δ ≤ ‖(n : ℂ) + μ‖ := by
  set N : ℕ := ⌈‖μ‖⌉₊ + 1
  have hne : (Finset.range N).Nonempty := ⟨0, Finset.mem_range.2 (by omega)⟩
  have hpos : ∀ n : ℕ, 0 < ‖(n : ℂ) + μ‖ := by
    intro n
    rw [norm_pos_iff]
    intro h
    exact hμ ⟨n, by linear_combination -h⟩
  refine ⟨min 1 ((Finset.range N).inf' hne fun n => ‖(n : ℂ) + μ‖), ?_, fun n => ?_⟩
  · refine lt_min one_pos ?_
    rw [Finset.lt_inf'_iff]
    exact fun n _ => hpos n
  · by_cases hn : n < N
    · exact (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_range.2 hn))
    · refine (min_le_left _ _).trans ?_
      have h1 : (N : ℝ) ≤ n := by exact_mod_cast not_lt.1 hn
      have h2 : ‖μ‖ ≤ ⌈‖μ‖⌉₊ := Nat.le_ceil _
      have h3 : ‖(n : ℂ)‖ ≤ ‖(n : ℂ) + μ‖ + ‖μ‖ := by
        calc ‖(n : ℂ)‖ = ‖((n : ℂ) + μ) + (-μ)‖ := by ring_nf
          _ ≤ ‖(n : ℂ) + μ‖ + ‖-μ‖ := norm_add_le _ _
          _ = _ := by rw [norm_neg]
      rw [Complex.norm_natCast] at h3
      have : (N : ℝ) = ⌈‖μ‖⌉₊ + 1 := by simp [N]
      linarith

/-- **Spectrum** of `diag(-ℓ)`: `{0, -1, -2, …}` (tex line 1510). -/
theorem opSpectrum_diagOp : opSpectrum (diagOp b) = Set.range fun n : ℕ => -(n : ℂ) := by
  ext μ
  constructor
  · intro hμ
    by_contra hμ'
    apply hμ
    obtain ⟨δ, hδ, hδn⟩ := exists_dist_pos hμ'
    have hne : ∀ n : ℕ, (n : ℂ) + μ ≠ 0 := fun n h => by
      have := hδn n
      rw [h, norm_zero] at this
      linarith
    have hc : ∀ n : ℕ, ‖-((n : ℂ) + μ)⁻¹‖ ≤ δ⁻¹ := fun n => by
      rw [norm_neg, norm_inv]
      exact inv_anti₀ hδ (hδn n)
    set R := diagCLM b (fun n => -((n : ℂ) + μ)⁻¹) δ⁻¹ hc
    have hRc : ∀ x n, ⟪b n, R x⟫_ℂ = -((n : ℂ) + μ)⁻¹ * ⟪b n, x⟫_ℂ :=
      fun x n => inner_diagCLM b _ _ hc x n
    have hdom : ∀ x, R x ∈ (diagOp b).domain := by
      intro x
      rw [mem_diagOp_domain_iff]
      refine memℓp_two_of_norm_le (1 + ‖μ‖ * δ⁻¹) (lp.memℓp (b.repr x)) (fun n => ?_)
      rw [hRc, b.repr_apply_apply, ← mul_assoc, norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have heq : (n : ℂ) * -((n : ℂ) + μ)⁻¹ = -1 + μ * ((n : ℂ) + μ)⁻¹ := by
        field_simp [hne n]
        ring
      rw [heq]
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg, norm_one, norm_mul, norm_inv]
      gcongr
      exact hδn n
    refine ⟨R, hdom, fun x => ?_, fun x => ?_⟩
    · apply ext_inner_basis b
      intro n
      rw [inner_sub_right, inner_diagOp, inner_smul_right, hRc]
      field_simp [hne n]
      ring
    · apply ext_inner_basis b
      intro n
      rw [hRc, inner_sub_right, inner_diagOp, inner_smul_right]
      field_simp [hne n]
      ring
  · rintro ⟨n, rfl⟩ ⟨R, hR, -, hleft⟩
    have h := hleft ⟨b n, basis_mem_domain b n⟩
    rw [diagOp_basis] at h
    simp only [sub_self, map_zero] at h
    exact b.orthonormal.ne_zero n h.symm

/-- The eigenspace of `D` for `-ℓ` is the line spanned by `b ℓ` (each level is simple). -/
theorem diagOp_eigen_iff (n : ℕ) (f : (diagOp b).domain) :
    diagOp b f = -(n : ℂ) • (f : H) ↔ (f : H) ∈ Submodule.span ℂ {b n} := by
  constructor
  · intro h
    have hcoef : ∀ m, m ≠ n → ⟪b m, (f : H)⟫_ℂ = 0 := by
      intro m hm
      have := inner_diagOp b f m
      rw [h, inner_smul_right] at this
      have hmn : (m : ℂ) ≠ n := by exact_mod_cast hm
      have : ((n : ℂ) - m) * ⟪b m, (f : H)⟫_ℂ = 0 := by linear_combination -this
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd (sub_eq_zero.1 h0).symm hmn
      · exact h0
    have : (f : H) = ⟪b n, (f : H)⟫_ℂ • b n := by
      apply ext_inner_basis b
      intro m
      rw [inner_smul_right, inner_basis_basis]
      split_ifs with hm
      · rw [hm, mul_one]
      · rw [mul_zero, hcoef m hm]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · intro h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h
    apply ext_inner_basis b
    intro m
    rw [inner_diagOp, inner_smul_right, ← ha, inner_smul_right, inner_basis_basis]
    split_ifs with hm
    · rw [hm]
    · simp

/-! ## Closure of a symmetric operator with the basis as eigenbasis -/

/-- If `T` is symmetric, its domain contains the Hilbert basis and `T b ℓ = -ℓ b ℓ`, then
`T` is closable and its closure is `diag(-ℓ)`; in particular the closure is selfadjoint. -/
theorem le_diagOp_of_symm {T : H →ₗ.[ℂ] H}
    (hsymm : ∀ x y : T.domain, ⟪T x, (y : H)⟫_ℂ = ⟪(x : H), T y⟫_ℂ)
    (hb : ∀ n, b n ∈ T.domain) (heig : ∀ n, T ⟨b n, hb n⟩ = -(n : ℂ) • b n) :
    T ≤ diagOp b := by
  have hcoef : ∀ x : T.domain, ∀ n, ⟪b n, T x⟫_ℂ = -(n : ℂ) * ⟪b n, (x : H)⟫_ℂ := by
    intro x n
    have h1 := hsymm x ⟨b n, hb n⟩
    rw [heig, inner_smul_right] at h1
    rw [← inner_conj_symm, h1, map_mul, map_neg, Complex.conj_natCast, inner_conj_symm]
  refine ⟨fun x hx => (exists_diagOp_eq b x _ (hcoef ⟨x, hx⟩)).1, fun x y hxy => ?_⟩
  obtain ⟨hx', hD⟩ := exists_diagOp_eq b x _ (hcoef x)
  have : y = ⟨x, hx'⟩ := Subtype.ext hxy.symm
  rw [this, hD]

theorem closure_eq_diagOp {T : H →ₗ.[ℂ] H}
    (hsymm : ∀ x y : T.domain, ⟪T x, (y : H)⟫_ℂ = ⟪(x : H), T y⟫_ℂ)
    (hb : ∀ n, b n ∈ T.domain) (heig : ∀ n, T ⟨b n, hb n⟩ = -(n : ℂ) • b n) :
    T.IsClosable ∧ T.closure = diagOp b := by
  have hle := le_diagOp_of_symm b hsymm hb heig
  have hclosed : (diagOp b).IsClosed := (isSelfAdjoint_diagOp b).isClosed
  have hT : T.IsClosable := hclosed.isClosable.leIsClosable hle
  refine ⟨hT, le_antisymm ?_ ?_⟩
  · apply LinearPMap.le_of_le_graph
    rw [← hT.graph_closure_eq_closure_graph]
    exact Submodule.topologicalClosure_minimal _ (LinearPMap.le_graph_of_le hle) hclosed
  · apply LinearPMap.le_of_le_graph
    rw [← hT.graph_closure_eq_closure_graph]
    intro p hp
    rw [LinearPMap.mem_graph_iff] at hp
    obtain ⟨f, hf1, hf2⟩ := hp
    -- truncations `f_N = ∑_{ℓ < N} ⟪b ℓ, f⟫ b ℓ`
    have hmemN : ∀ N, (∑ i ∈ Finset.range N, ⟪b i, (f : H)⟫_ℂ • b i) ∈ T.domain :=
      fun N => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hb i)
    have hTN : ∀ N, T ⟨_, hmemN N⟩ =
        ∑ i ∈ Finset.range N, ⟪b i, diagOp b f⟫_ℂ • b i := by
      intro N
      have : (⟨_, hmemN N⟩ : T.domain) =
          ∑ i ∈ Finset.range N, ⟪b i, (f : H)⟫_ℂ • (⟨b i, hb i⟩ : T.domain) := by
        apply Subtype.ext
        simp
      rw [this]
      change T.toFun _ = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, LinearPMap.toFun_eq_coe, heig, inner_diagOp, smul_smul]
      congr 1
      ring
    have h1 : Tendsto (fun N => ∑ i ∈ Finset.range N, ⟪b i, (f : H)⟫_ℂ • b i) atTop
        (𝓝 (f : H)) := by
      have := (b.hasSum_repr (f : H)).tendsto_sum_nat
      simpa only [b.repr_apply_apply] using this
    have h2 : Tendsto (fun N => ∑ i ∈ Finset.range N, ⟪b i, diagOp b f⟫_ℂ • b i) atTop
        (𝓝 (diagOp b f)) := by
      have := (b.hasSum_repr (diagOp b f)).tendsto_sum_nat
      simpa only [b.repr_apply_apply] using this
    have h12 := h1.prodMk_nhds h2
    have hp' : p = ((f : H), diagOp b f) := Prod.ext hf1.symm hf2.symm
    rw [hp', ← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    refine mem_closure_of_tendsto h12 (Eventually.of_forall fun N => ?_)
    rw [SetLike.mem_coe, LinearPMap.mem_graph_iff]
    exact ⟨⟨_, hmemN N⟩, rfl, hTN N⟩

end UnforcedLeray.B0094
