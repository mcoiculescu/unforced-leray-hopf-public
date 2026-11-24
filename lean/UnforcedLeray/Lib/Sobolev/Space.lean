import UnforcedLeray.Lib.Sobolev.Pairing
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# The Sobolev type `Sob.W D ρ 𝕜 F k p` (INF11 target S2; decision D3)

Scoping note `INF11-INF14-Sobolev.md` §5.0 (the representation, decided for the whole project)
and §5.1 (S2). Decision D3 of the scoping README §3: `Sob.W D ρ 𝕜 F k p` is the one Sobolev
representation, for `ℝⁿ` (n = 1, 2, 3) and the cylinder cell.

The manuscript: `X_m = L²(ρ_ℓ^m dq dη)`, `H^k_m = {f : D^α f ∈ X_m, |α| ≤ k}`, unweighted
distribution pairing (tex 13876–13886); periodic weak derivatives on the cylinder
(tex 4573–4577, 13850–13852); H^k norms are sums over derivatives of order `≤ k` (e.g.
tex 2672–2718, B0178).

## The representation
An element of `W D ρ 𝕜 F k p` is a tuple `(x_α)_{|α| ≤ k}` of classes in
`L^p(ρ dμ; F)`, indexed by the words `α : Idx n k` of length `≤ k` over the `n` coordinate
directions, such that `x_α = ∂^α x_∅` weakly for the tests of `D` (`mem_SobSub_iff`). Ordered
words are used (each mixed derivative appears once per ordering, as in the compiled
`SobolevGraph.H2`). The norm is the `PiLp p` norm, `(∑_α ‖x_α‖_p^p)^{1/p}`; at `p = 2` it is the
Hilbert norm `∑_α ‖x_α‖²` (`W.norm_sq`).

The defining constraints are kernels of the continuous test functionals of `Pairing.lean`
(`testPair`), so `W` is a closed subspace and complete (the kernel-intersection design of
NonUniqueEuler `Defs/Infra/SobolevSpace.lean`, as already used by the compiled
`SobolevGraph/Graph.lean`).

## Main declarations
* `Idx n k`, `Idx.zero`, `Idx.cons`, `Idx.castLE`, `TestDomain.word`;
* `SobTuple`, `SobSub`, `W`, `mem_SobSub_iff`, `isClosed_SobSub`, `CompleteSpace W`;
* `W.value`, `W.deriv α` (continuous linear), `W.hasWeakDeriv`, `W.value_injective`, `W.ext`;
* `W.ofFields`, `W.restrict`, `W.partialDeriv` (the note's `W.partial`; `partial` is a Lean
  keyword);
* `InnerProductSpace 𝕜 (W D ρ 𝕜 F k 2)`, `W.norm_sq`, `W.inner_eq`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.Sob

/-! ### Words -/

/-- Words of length `≤ k` over the letters `Fin n`: `⟨j, β⟩` is `∂_{β 0} ⋯ ∂_{β (j-1)}`. -/
abbrev Idx (n k : ℕ) := Σ j : Fin (k + 1), (Fin j → Fin n)

namespace Idx

variable {n k : ℕ}

/-- The empty word. -/
def zero : Idx n k := ⟨⟨0, Nat.succ_pos k⟩, Fin.elim0⟩

/-- Prepend the letter `i`. -/
def cons (i : Fin n) (α : Idx n k) : Idx n (k + 1) := ⟨α.1.succ, Fin.cons i α.2⟩

/-- A word of length `≤ k'` as a word of length `≤ k`. -/
def castLE {k' : ℕ} (h : k' ≤ k) (α : Idx n k') : Idx n k :=
  ⟨Fin.castLE (Nat.succ_le_succ h) α.1, α.2⟩

theorem castLE_zero {k' : ℕ} (h : k' ≤ k) : castLE h (zero : Idx n k') = zero := rfl

end Idx

section Word

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] {n : ℕ}
  (D : TestDomain E n)

/-- The list of directions of a word. -/
def TestDomain.word {k : ℕ} (α : Idx n k) : List E := List.ofFn fun i => D.dir (α.2 i)

@[simp] theorem TestDomain.word_zero {k : ℕ} : D.word (Idx.zero : Idx n k) = [] := rfl

theorem TestDomain.word_cons {k : ℕ} (i : Fin n) (α : Idx n k) :
    D.word (Idx.cons i α) = D.dir i :: D.word α := by
  simp [TestDomain.word, Idx.cons, List.ofFn_succ]

theorem TestDomain.word_castLE {k k' : ℕ} (h : k' ≤ k) (α : Idx n k') :
    D.word (Idx.castLE h α) = D.word α := rfl

@[simp] theorem TestDomain.length_word {k : ℕ} (α : Idx n k) : (D.word α).length = α.1 := by
  simp [TestDomain.word]

end Word

/-! ### The closed graph -/

theorem completeSpace_of_finiteDimensional (𝕜 F : Type*) [RCLike 𝕜] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F] : CompleteSpace F :=
  FiniteDimensional.complete 𝕜 F

section Space

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {n : ℕ}
  (D : TestDomain E n) (ρ : Weight E) (𝕜 : Type*) [RCLike 𝕜] (F : Type*)
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]
  [FiniteDimensional 𝕜 F] (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The ambient space of tuples `(x_α)_{|α| ≤ k}` in `L^p(ρ dμ; F)`. -/
abbrev SobTuple : Type _ := PiLp p (fun _ : Idx n k => Lp F p (wμ D.μ ρ))

/-- The constraint `∫ (∂^α φ) x_∅ dμ - (-1)^{|α|} ∫ φ x_α dμ` as a continuous functional. -/
def constraint (α : Idx n k) (φ : {φ : E → ℝ // D.Adm φ}) : SobTuple D ρ F k p →L[𝕜] F :=
  haveI := completeSpace_of_finiteDimensional 𝕜 F
  (testPair (𝕜 := 𝕜) D.μ ρ p (iterDirDeriv (D.word α) φ.1)
      (CompactlyBounded.of_adm (D.adm_iterDirDeriv φ.2 _))).comp
      (PiLp.proj p (fun _ : Idx n k => Lp F p (wμ D.μ ρ)) Idx.zero) -
    ((-1 : 𝕜) ^ (α.1 : ℕ)) • (testPair (𝕜 := 𝕜) D.μ ρ p φ.1 (CompactlyBounded.of_adm φ.2)).comp
      (PiLp.proj p (fun _ : Idx n k => Lp F p (wμ D.μ ρ)) α)

theorem constraint_apply (α : Idx n k) (φ : {φ : E → ℝ // D.Adm φ}) (x : SobTuple D ρ F k p) :
    constraint D ρ 𝕜 F k p α φ x =
      ∫ y, iterDirDeriv (D.word α) φ.1 y • (x.ofLp Idx.zero : E → F) y ∂D.μ -
        (-1 : ℝ) ^ (α.1 : ℕ) • ∫ y, φ.1 y • (x.ofLp α : E → F) y ∂D.μ := by
  haveI := completeSpace_of_finiteDimensional 𝕜 F
  simp only [constraint, ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply, testPair_apply]
  congr 1
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  push_cast
  rfl

/-- **The Sobolev graph** `{x | x_α = ∂^α x_∅ weakly for all |α| ≤ k}`. -/
def SobSub : Submodule 𝕜 (SobTuple D ρ F k p) :=
  ⨅ (α : Idx n k) (φ : {φ : E → ℝ // D.Adm φ}),
    LinearMap.ker (constraint D ρ 𝕜 F k p α φ : SobTuple D ρ F k p →ₗ[𝕜] F)

/-- **The Sobolev type** `W D ρ 𝕜 F k p` (D3): `W^{k,p}(ρ dμ; F)` for the test domain `D`,
with weak derivatives for the unweighted pairing. -/
abbrev W : Type _ := ↥(SobSub D ρ 𝕜 F k p)

variable {D ρ 𝕜 F k p}

/-- **Membership** is the family of genuine weak-derivative identities, with integrable
pairings, for every word of length `≤ k` (S2). -/
theorem mem_SobSub_iff (x : SobTuple D ρ F k p) :
    x ∈ SobSub D ρ 𝕜 F k p ↔ ∀ α : Idx n k,
      HasWeakDeriv D (D.word α) (x.ofLp Idx.zero : E → F) (x.ofLp α : E → F) := by
  simp only [SobSub, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    constraint_apply, sub_eq_zero]
  constructor
  · intro h α
    refine ⟨fun φ hφ => integrable_smul_of_memLp
        (CompactlyBounded.of_adm (D.adm_iterDirDeriv hφ _)) (Lp.memLp _),
      fun φ hφ => integrable_smul_of_memLp (CompactlyBounded.of_adm hφ) (Lp.memLp _),
      fun φ hφ => ?_⟩
    rw [TestDomain.length_word]
    exact h α ⟨φ, hφ⟩
  · intro h α φ
    have := (h α).identity φ.1 φ.2
    rwa [TestDomain.length_word] at this

variable (D ρ 𝕜 F k p)

theorem isClosed_SobSub : IsClosed (SobSub D ρ 𝕜 F k p : Set (SobTuple D ρ F k p)) := by
  rw [SobSub, Submodule.coe_iInf]
  refine isClosed_iInter fun α => ?_
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun φ => (constraint D ρ 𝕜 F k p α φ).isClosed_ker

instance W.completeSpace : CompleteSpace (W D ρ 𝕜 F k p) :=
  haveI := completeSpace_of_finiteDimensional 𝕜 F
  (isClosed_SobSub D ρ 𝕜 F k p).completeSpace_coe

namespace W

/-- The field `x_∅ ∈ L^p(ρ dμ; F)`. -/
def value : W D ρ 𝕜 F k p →L[𝕜] Lp F p (wμ D.μ ρ) :=
  (PiLp.proj p (fun _ : Idx n k => Lp F p (wμ D.μ ρ)) Idx.zero).comp
    (SobSub D ρ 𝕜 F k p).subtypeL

/-- The weak derivative `x_α = ∂^α x_∅ ∈ L^p(ρ dμ; F)`. -/
def deriv (α : Idx n k) : W D ρ 𝕜 F k p →L[𝕜] Lp F p (wμ D.μ ρ) :=
  (PiLp.proj p (fun _ : Idx n k => Lp F p (wμ D.μ ρ)) α).comp (SobSub D ρ 𝕜 F k p).subtypeL

variable {D ρ 𝕜 F k p}

@[simp] theorem value_apply (x : W D ρ 𝕜 F k p) :
    value D ρ 𝕜 F k p x = (x : SobTuple D ρ F k p).ofLp Idx.zero := rfl

@[simp] theorem deriv_apply (α : Idx n k) (x : W D ρ 𝕜 F k p) :
    deriv D ρ 𝕜 F k p α x = (x : SobTuple D ρ F k p).ofLp α := rfl

theorem deriv_zero (x : W D ρ 𝕜 F k p) :
    deriv D ρ 𝕜 F k p Idx.zero x = value D ρ 𝕜 F k p x := rfl

/-- Each component is the weak derivative of the field. -/
theorem hasWeakDeriv (x : W D ρ 𝕜 F k p) (α : Idx n k) :
    HasWeakDeriv D (D.word α) (value D ρ 𝕜 F k p x : E → F) (deriv D ρ 𝕜 F k p α x : E → F) :=
  (mem_SobSub_iff (x : SobTuple D ρ F k p)).mp x.2 α

/-- **The field determines the element**: weak derivatives are unique (S2). -/
theorem value_injective [FiniteDimensional ℝ E] [BorelSpace E] :
    Function.Injective (value D ρ 𝕜 F k p) := by
  haveI := completeSpace_of_finiteDimensional 𝕜 F
  haveI : ProperSpace F := FiniteDimensional.proper_rclike 𝕜 F
  intro x y hxy
  have hd : ∀ α, deriv D ρ 𝕜 F k p α x = deriv D ρ 𝕜 F k p α y := by
    intro α
    have h1 := W.hasWeakDeriv x α
    have h2 := W.hasWeakDeriv y α
    rw [hxy] at h1
    apply Lp.ext
    refine (ae_eq_wμ_iff D.μ ρ).mpr ?_
    exact h1.ae_unique h2 (locallyIntegrable_of_memLp (Lp.memLp _))
      (locallyIntegrable_of_memLp (Lp.memLp _))
  apply Subtype.ext
  apply (WithLp.ext_iff (p := p)).mpr
  funext α
  exact hd α

@[ext] theorem ext [FiniteDimensional ℝ E] [BorelSpace E] {x y : W D ρ 𝕜 F k p}
    (h : value D ρ 𝕜 F k p x = value D ρ 𝕜 F k p y) : x = y :=
  value_injective h

/-! ### Construction from fields -/

/-- The element with components `g α` (which must lie in `L^p(ρ dμ)` and be the weak
derivatives `∂^α (g ∅)`). -/
def ofFields (g : Idx n k → E → F) (hmem : ∀ α, MemLp (g α) p (wμ D.μ ρ))
    (hw : ∀ α, HasWeakDeriv D (D.word α) (g Idx.zero) (g α)) : W D ρ 𝕜 F k p :=
  ⟨WithLp.toLp p (fun α => (hmem α).toLp (g α)), by
    rw [mem_SobSub_iff]
    intro α
    refine (hw α).congr_ae ?_ ?_
    · exact (ae_eq_wμ_iff D.μ ρ).mp (hmem Idx.zero).coeFn_toLp.symm
    · exact (ae_eq_wμ_iff D.μ ρ).mp (hmem α).coeFn_toLp.symm⟩

theorem deriv_ofFields (g : Idx n k → E → F) (hmem : ∀ α, MemLp (g α) p (wμ D.μ ρ))
    (hw : ∀ α, HasWeakDeriv D (D.word α) (g Idx.zero) (g α)) (α : Idx n k) :
    deriv D ρ 𝕜 F k p α (ofFields g hmem hw) = (hmem α).toLp (g α) := rfl

theorem value_ofFields (g : Idx n k → E → F) (hmem : ∀ α, MemLp (g α) p (wμ D.μ ρ))
    (hw : ∀ α, HasWeakDeriv D (D.word α) (g Idx.zero) (g α)) :
    value D ρ 𝕜 F k p (ofFields g hmem hw) = (hmem Idx.zero).toLp (g Idx.zero) := rfl

/-! ### Reindexing: restriction of the order and partial derivatives -/

variable (D ρ 𝕜 F p) in
/-- The tuple map `x ↦ (x_{σ β})_β`. -/
def reindex {k' : ℕ} (σ : Idx n k' → Idx n k) : SobTuple D ρ F k p →L[𝕜] SobTuple D ρ F k' p :=
  (PiLp.continuousLinearEquiv p 𝕜 (fun _ : Idx n k' => Lp F p (wμ D.μ ρ))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun β => PiLp.proj p (fun _ : Idx n k => Lp F p (wμ D.μ ρ)) (σ β))

@[simp] theorem reindex_apply {k' : ℕ} (σ : Idx n k' → Idx n k) (x : SobTuple D ρ F k p)
    (β : Idx n k') : (reindex D ρ 𝕜 F p σ x).ofLp β = x.ofLp (σ β) := rfl

/-- `W^{k,p} → W^{k',p}` for `k' ≤ k` (forget the derivatives of order `> k'`). -/
def restrict {k' : ℕ} (h : k' ≤ k) : W D ρ 𝕜 F k p →L[𝕜] W D ρ 𝕜 F k' p :=
  ((reindex D ρ 𝕜 F p (Idx.castLE h)).comp (SobSub D ρ 𝕜 F k p).subtypeL).codRestrict _
    (fun x => by
      rw [mem_SobSub_iff]
      intro β
      exact W.hasWeakDeriv x (Idx.castLE h β))

@[simp] theorem value_restrict {k' : ℕ} (h : k' ≤ k) (x : W D ρ 𝕜 F k p) :
    value D ρ 𝕜 F k' p (restrict h x) = value D ρ 𝕜 F k p x := rfl

@[simp] theorem deriv_restrict {k' : ℕ} (h : k' ≤ k) (x : W D ρ 𝕜 F k p) (β : Idx n k') :
    deriv D ρ 𝕜 F k' p β (restrict h x) = deriv D ρ 𝕜 F k p (Idx.castLE h β) x := rfl

/-- The partial derivative `∂_i : W^{k+1,p} → W^{k,p}` (the note's `W.partial`). -/
def partialDeriv (i : Fin n) : W D ρ 𝕜 F (k + 1) p →L[𝕜] W D ρ 𝕜 F k p :=
  ((reindex D ρ 𝕜 F p (Idx.cons i)).comp (SobSub D ρ 𝕜 F (k + 1) p).subtypeL).codRestrict _
    (fun x => by
      rw [mem_SobSub_iff]
      intro β
      have h1 := W.hasWeakDeriv x (Idx.cons i (Idx.zero : Idx n k))
      have h2 := W.hasWeakDeriv x (Idx.cons i β)
      rw [D.word_cons, D.word_zero] at h1
      rw [D.word_cons] at h2
      exact h1.of_cons h2)

@[simp] theorem value_partialDeriv (i : Fin n) (x : W D ρ 𝕜 F (k + 1) p) :
    value D ρ 𝕜 F k p (partialDeriv i x) =
      deriv D ρ 𝕜 F (k + 1) p (Idx.cons i Idx.zero) x := rfl

@[simp] theorem deriv_partialDeriv (i : Fin n) (x : W D ρ 𝕜 F (k + 1) p) (β : Idx n k) :
    deriv D ρ 𝕜 F k p β (partialDeriv i x) = deriv D ρ 𝕜 F (k + 1) p (Idx.cons i β) x := rfl

end W

/-! ### The Hilbert case `p = 2` -/

instance W.innerProductSpace : InnerProductSpace 𝕜 (W D ρ 𝕜 F k 2) := inferInstance

variable {D ρ 𝕜 F k}

/-- The `H^k` norm: `‖x‖² = ∑_{|α| ≤ k} ‖∂^α x‖²_{L²(ρ dμ)}`. -/
theorem W.norm_sq (x : W D ρ 𝕜 F k 2) :
    ‖x‖ ^ 2 = ∑ α : Idx n k, ‖W.deriv D ρ 𝕜 F k 2 α x‖ ^ 2 := by
  change ‖(x : SobTuple D ρ F k 2)‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

theorem W.inner_eq (x y : W D ρ 𝕜 F k 2) :
    inner 𝕜 x y = ∑ α : Idx n k, inner 𝕜 (W.deriv D ρ 𝕜 F k 2 α x) (W.deriv D ρ 𝕜 F k 2 α y) := by
  rw [Submodule.coe_inner, PiLp.inner_apply]
  rfl

end Space

end UnforcedLeray.Sob
