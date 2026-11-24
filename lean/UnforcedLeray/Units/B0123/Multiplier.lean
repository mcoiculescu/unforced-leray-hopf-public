import UnforcedLeray.Units.B0094

/-!
# B0123 helper: multiplier operators in a Hilbert basis

Blueprint unit B0123 (`eq:st18-t00101`, `paper/main.tex` lines 1873--1878), infrastructure
INF31 ("spectral calculus of `D`, or the diagonal model").

For a Hilbert basis `b : HilbertBasis ℕ ℂ H` and a sequence `m : ℕ → ℂ`, `mulOp b m` is the
(possibly unbounded) operator `f ↦ ∑ₙ m n ⟪b n, f⟫ b n` with its maximal domain
`{f : ∑ₙ |m n|² |⟪b n, f⟫|² < ∞}`. This generalizes B0094's `diagOp` (the case `m n = -n`,
`Units/B0094/Diagonal.lean`); for an operator with orthonormal eigenbasis `b` and eigenvalues
`λₙ` it is the spectral calculus `φ(T)` with `m n = φ(λₙ)`.

API: `inner_mulOp` (coefficients), `mulOp_graph_iff` (graph by coefficients),
`mem_mulOp_domain_iff_summable`, `hasSum_norm_inner_sq` (Parseval), `hasSum_norm_mulOp_sq`,
`mem_mulOp_domain_of_bdd` and `mulOp_eq_diagCLM` (bounded multipliers give B0094's `diagCLM`),
`mulOp_mem_domain_iff` and `mulOp_comp_apply` (composition multiplies the multipliers).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped InnerProductSpace ComplexConjugate ENNReal

namespace UnforcedLeray.B0123

open UnforcedLeray.B0094

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (b : HilbertBasis ℕ ℂ H)

/-- **Parseval**: `‖f‖² = ∑ₙ |⟪b n, f⟫|²`. -/
theorem hasSum_norm_inner_sq (f : H) :
    HasSum (fun n : ℕ => ‖⟪b n, f⟫_ℂ‖ ^ 2) (‖f‖ ^ 2) := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h := lp.hasSum_norm hp (b.repr f)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr_apply_apply,
    LinearIsometryEquiv.norm_map] at h
  exact h

/-- The maximal domain of the multiplier `m`: `∑ₙ |m n|² |⟪b n, f⟫|² < ∞`. -/
def mulDomain (m : ℕ → ℂ) : Submodule ℂ H where
  carrier := {f | Memℓp (fun n : ℕ => m n * ⟪b n, f⟫_ℂ) 2}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, inner_zero_right, mul_zero]
    exact zero_mem_ℓp'
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_ofPred_eq, inner_add_right, mul_add] at hf hg ⊢
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_ofPred_eq, inner_smul_right] at hf ⊢
    have := hf.const_smul c
    convert this using 1
    funext n
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- The coefficient sequence `(m n ⟪b n, f⟫)ₙ ∈ ℓ²`. -/
def mulSeq (m : ℕ → ℂ) (f : mulDomain b m) : lp (fun _ : ℕ => ℂ) 2 :=
  ⟨fun n => m n * ⟪b n, (f : H)⟫_ℂ, f.2⟩

/-- The linear map `f ↦ ∑ₙ m n ⟪b n, f⟫ b n` on the domain. -/
def mulLin (m : ℕ → ℂ) : mulDomain b m →ₗ[ℂ] H where
  toFun f := b.repr.symm (mulSeq b m f)
  map_add' f g := by
    rw [← map_add]
    congr 1
    ext n
    simp only [mulSeq, Submodule.coe_add, inner_add_right, lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' c f := by
    rw [RingHom.id_apply, ← map_smul]
    congr 1
    ext n
    simp only [mulSeq, Submodule.coe_smul, inner_smul_right, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul]
    ring

/-- The multiplier operator `diag(m)` in the Hilbert basis `b`, with its maximal domain. -/
def mulOp (m : ℕ → ℂ) : H →ₗ.[ℂ] H := ⟨mulDomain b m, mulLin b m⟩

theorem mem_mulOp_domain_iff (m : ℕ → ℂ) (f : H) :
    f ∈ (mulOp b m).domain ↔ Memℓp (fun n : ℕ => m n * ⟪b n, f⟫_ℂ) 2 := Iff.rfl

theorem mem_mulOp_domain_iff_summable (m : ℕ → ℂ) (f : H) :
    f ∈ (mulOp b m).domain ↔ Summable fun n : ℕ => ‖m n‖ ^ 2 * ‖⟪b n, f⟫_ℂ‖ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  rw [mem_mulOp_domain_iff, memℓp_gen_iff hp]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, mul_pow]

/-- The coefficients of `diag(m) f` are `m n ⟪b n, f⟫`. -/
theorem inner_mulOp (m : ℕ → ℂ) (f : (mulOp b m).domain) (n : ℕ) :
    ⟪b n, mulOp b m f⟫_ℂ = m n * ⟪b n, (f : H)⟫_ℂ := by
  change ⟪b n, b.repr.symm (mulSeq b m f)⟫_ℂ = _
  rw [inner_repr_symm]
  rfl

/-- The graph of `diag(m)` by coefficients: `x ∈ 𝒟` and `diag(m) x = y` iff
`⟪b n, y⟫ = m n ⟪b n, x⟫` for every `n`. -/
theorem mulOp_graph_iff (m : ℕ → ℂ) (x y : H) :
    (∃ hx : x ∈ (mulOp b m).domain, mulOp b m ⟨x, hx⟩ = y) ↔
      ∀ n, ⟪b n, y⟫_ℂ = m n * ⟪b n, x⟫_ℂ := by
  constructor
  · rintro ⟨hx, rfl⟩ n
    exact inner_mulOp b m ⟨x, hx⟩ n
  · intro h
    have hx : x ∈ (mulOp b m).domain := by
      rw [mem_mulOp_domain_iff]
      have hfun : (fun n : ℕ => m n * ⟪b n, x⟫_ℂ) = ⇑(b.repr y) := by
        funext n
        rw [b.repr_apply_apply, h]
      rw [hfun]
      exact lp.memℓp (b.repr y)
    exact ⟨hx, ext_inner_basis b fun n => by rw [inner_mulOp, h]⟩

/-- `‖diag(m) f‖² = ∑ₙ |m n|² |⟪b n, f⟫|²`. -/
theorem hasSum_norm_mulOp_sq (m : ℕ → ℂ) (f : (mulOp b m).domain) :
    HasSum (fun n : ℕ => ‖m n‖ ^ 2 * ‖⟪b n, (f : H)⟫_ℂ‖ ^ 2) (‖mulOp b m f‖ ^ 2) := by
  have h := hasSum_norm_inner_sq b (mulOp b m f)
  simp only [inner_mulOp, norm_mul, mul_pow] at h
  exact h

/-- A bounded multiplier has full domain. -/
theorem mem_mulOp_domain_of_bdd (m : ℕ → ℂ) {C : ℝ} (hc : ∀ n, ‖m n‖ ≤ C) (f : H) :
    f ∈ (mulOp b m).domain :=
  memℓp_two_of_norm_le C (lp.memℓp (b.repr f)) fun n => by
    rw [norm_mul, b.repr_apply_apply]
    exact mul_le_mul_of_nonneg_right (hc n) (norm_nonneg _)

/-- A bounded multiplier operator is B0094's bounded diagonal operator `diagCLM`. -/
theorem mulOp_eq_diagCLM (m : ℕ → ℂ) {C : ℝ} (hc : ∀ n, ‖m n‖ ≤ C) (f : H) :
    mulOp b m ⟨f, mem_mulOp_domain_of_bdd b m hc f⟩ = diagCLM b m C hc f :=
  ext_inner_basis b fun n => by rw [inner_mulOp, inner_diagCLM]

/-- Composition of multipliers, domain: for `f ∈ 𝒟(diag m₂)`,
`diag(m₂) f ∈ 𝒟(diag m₁)` iff `f ∈ 𝒟(diag(m₁ m₂))`. -/
theorem mulOp_mem_domain_iff (m₁ m₂ : ℕ → ℂ) (f : (mulOp b m₂).domain) :
    mulOp b m₂ f ∈ (mulOp b m₁).domain ↔ (f : H) ∈ (mulOp b (m₁ * m₂)).domain := by
  rw [mem_mulOp_domain_iff, mem_mulOp_domain_iff]
  have : (fun n : ℕ => m₁ n * ⟪b n, mulOp b m₂ f⟫_ℂ) =
      fun n : ℕ => (m₁ * m₂) n * ⟪b n, (f : H)⟫_ℂ := by
    funext n
    rw [inner_mulOp, Pi.mul_apply, mul_assoc]
  rw [this]

/-- Composition of multipliers: `diag(m₁) diag(m₂) f = diag(m₁ m₂) f`. -/
theorem mulOp_comp_apply (m₁ m₂ : ℕ → ℂ) (f : (mulOp b m₂).domain)
    (h₁ : mulOp b m₂ f ∈ (mulOp b m₁).domain) (h : (f : H) ∈ (mulOp b (m₁ * m₂)).domain) :
    mulOp b m₁ ⟨mulOp b m₂ f, h₁⟩ = mulOp b (m₁ * m₂) ⟨f, h⟩ :=
  ext_inner_basis b fun n => by
    simp only [inner_mulOp, Pi.mul_apply, mul_assoc]

end UnforcedLeray.B0123
