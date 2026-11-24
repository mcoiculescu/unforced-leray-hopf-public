import UnforcedLeray.Units.B0121.Planar

/-!
# B0121 helper: the spaces `X_{G,j} = 𝒟((I - D)^{j/2})` and the Hermite levels

Blueprint unit B0121 (`eq:st18-t00100`, `paper/main.tex` lines 1856--1865), with
`X_{G,j} = 𝒟((I - D)^{j/2})` from `eq:st18-t00014` (tex line 748).

`D` is selfadjoint on `X_G` with the orthonormal eigenbasis `oscBasis` and `D e_ℓ = -ℓ e_ℓ`
(B0094, `eq:st18-t00068`). Its spectral calculus is therefore diagonal in this basis, and
`(I - D)^{j/2}` is the diagonal operator with entries `(1 + ℓ)^{j/2}` on its maximal domain
`X_{G,j} = {f : ∑ (1 + ℓ)^j |⟪e_ℓ, f⟫|² < ∞}` (`fracPow`, `XGj`, `mem_XGj_iff`). For `j = 2`
this is `I - D` itself (`fracPow_two`). The squared graph norm is
`‖f‖² + ‖(I - D)^{j/2} f‖² = ∑ (1 + (1 + ℓ)^j) |⟪e_ℓ, f⟫|²` (`graphNormSq_eq`).

On the Hermite levels (`φS ℓ = U_G e_ℓ`, the angular-two Hermite function of total degree
`N = 2 + 2ℓ`, B0094's `oscBasis_level`), `Q_k = ∏_{m<k}(T + m/2)` acts by
`qpoly k (2 + ℓ)`, and `sum_norm_sq_Aw_chi` computes the sum of the squared norms of all
`k`-th order conjugated derivatives of a finite combination of levels (tex line 1863).
`qsum_ge`, `qsum_le`: `∑_{k ≤ j} qpoly k (2 + ℓ)` is comparable to `1 + (1 + ℓ)^j`
(tex line 1863: "comparable to `(1 + N)^j`").
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology Polynomial
open scoped SchwartzMap InnerProductSpace ComplexConjugate Real ENNReal

namespace UnforcedLeray.B0121

open UnforcedLeray.B0094 UnforcedLeray.B0010

/-! ## `X_{G,j}` and `(I - D)^{j/2}` -/

/-- The weight `(1 + ℓ)^{j/2}`: the eigenvalue of `(I - D)^{j/2}` on `e_ℓ`. -/
def wt (j ℓ : ℕ) : ℝ := (1 + (ℓ : ℝ)) ^ ((j : ℝ) / 2)

theorem wt_sq (j ℓ : ℕ) : wt j ℓ ^ 2 = (1 + (ℓ : ℝ)) ^ j := by
  rw [wt, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
  congr 1
  push_cast
  ring

theorem wt_two (ℓ : ℕ) : wt 2 ℓ = 1 + (ℓ : ℝ) := by
  rw [wt]
  norm_num

/-- **`X_{G,j} = 𝒟((I - D)^{j/2})`** (`eq:st18-t00014`, tex line 748). -/
def XGj (j : ℕ) : Submodule ℂ XG where
  carrier := {f | Memℓp (fun ℓ : ℕ => (wt j ℓ : ℂ) * ⟪oscBasis ℓ, f⟫_ℂ) 2}
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

/-- `f ∈ X_{G,j}` iff `∑ (1 + ℓ)^j |⟪e_ℓ, f⟫|² < ∞`. -/
theorem mem_XGj_iff (j : ℕ) (f : XG) :
    f ∈ XGj j ↔ Summable fun ℓ : ℕ => (1 + (ℓ : ℝ)) ^ j * ‖⟪oscBasis ℓ, f⟫_ℂ‖ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  change Memℓp (fun ℓ : ℕ => (wt j ℓ : ℂ) * ⟪oscBasis ℓ, f⟫_ℂ) 2 ↔ _
  rw [memℓp_gen_iff hp]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs, wt_sq]

/-- The coefficient sequence `((1 + ℓ)^{j/2} ⟪e_ℓ, f⟫)_ℓ ∈ ℓ²`. -/
def fracSeq (j : ℕ) (f : XGj j) : lp (fun _ : ℕ => ℂ) 2 :=
  ⟨fun ℓ => (wt j ℓ : ℂ) * ⟪oscBasis ℓ, (f : XG)⟫_ℂ, f.2⟩

/-- `f ↦ ∑ (1 + ℓ)^{j/2} ⟪e_ℓ, f⟫ e_ℓ` on `X_{G,j}`. -/
def fracLin (j : ℕ) : XGj j →ₗ[ℂ] XG where
  toFun f := oscBasis.repr.symm (fracSeq j f)
  map_add' f g := by
    rw [← map_add]
    congr 1
    ext n
    simp only [fracSeq, Submodule.coe_add, inner_add_right, lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' c f := by
    rw [RingHom.id_apply, ← map_smul]
    congr 1
    ext n
    simp only [fracSeq, Submodule.coe_smul, inner_smul_right, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul]
    ring

/-- **`(I - D)^{j/2}`** on its domain `X_{G,j}`: the spectral calculus of the selfadjoint
`D = diag(-ℓ)` (B0094) for the function `λ ↦ (1 - λ)^{j/2}`. -/
def fracPow (j : ℕ) : XG →ₗ.[ℂ] XG := ⟨XGj j, fracLin j⟩

theorem fracPow_domain (j : ℕ) : (fracPow j).domain = XGj j := rfl

theorem inner_fracPow (j : ℕ) (f : (fracPow j).domain) (ℓ : ℕ) :
    ⟪oscBasis ℓ, fracPow j f⟫_ℂ = (wt j ℓ : ℂ) * ⟪oscBasis ℓ, (f : XG)⟫_ℂ := by
  change ⟪oscBasis ℓ, oscBasis.repr.symm (fracSeq j f)⟫_ℂ = _
  rw [inner_repr_symm]
  rfl

/-- For `j = 2`, `(I - D)^{j/2}` is `I - D`: `𝒟(D) ⊆ X_{G,2}` and `(I - D)^{1} f = f - D f`. -/
theorem fracPow_two (f : XG) (hf : f ∈ D.domain) :
    ∃ h : f ∈ (fracPow 2).domain, fracPow 2 ⟨f, h⟩ = f - D ⟨f, hf⟩ := by
  have hD : ∀ (n : ℕ) (g : D.domain),
      ⟪oscBasis n, D g⟫_ℂ = -(n : ℂ) * ⟪oscBasis n, (g : XG)⟫_ℂ := by
    intro n
    have h : ∀ T : XG →ₗ.[ℂ] XG, T = diagOp oscBasis → ∀ g : T.domain,
        ⟪oscBasis n, T g⟫_ℂ = -(n : ℂ) * ⟪oscBasis n, (g : XG)⟫_ℂ := by
      rintro T rfl g
      exact inner_diagOp oscBasis g n
    exact h D D_eq_diagOp
  have hmem : f ∈ (fracPow 2).domain := by
    rw [fracPow_domain, mem_XGj_iff]
    have hs := (mem_D_domain_iff f).1 hf
    have e : ∀ ℓ : ℕ, ‖⟪oscBasis ℓ, f⟫_ℂ • oscBasis ℓ‖ = ‖⟪oscBasis ℓ, f⟫_ℂ‖ := fun ℓ => by
      rw [norm_smul, oscBasis.orthonormal.1 ℓ, mul_one]
    simp only [e] at hs
    refine Summable.of_nonneg_of_le (fun ℓ => by positivity) (fun ℓ => ?_) (hs.mul_left 2)
    have hℓ : (1 + (ℓ : ℝ)) ^ 2 ≤ 2 * (1 + (ℓ : ℝ) ^ 2) := by nlinarith [sq_nonneg ((ℓ : ℝ) - 1)]
    calc (1 + (ℓ : ℝ)) ^ 2 * ‖⟪oscBasis ℓ, f⟫_ℂ‖ ^ 2
        ≤ 2 * (1 + (ℓ : ℝ) ^ 2) * ‖⟪oscBasis ℓ, f⟫_ℂ‖ ^ 2 := by gcongr
      _ = 2 * ((1 + (ℓ : ℝ) ^ 2) * ‖⟪oscBasis ℓ, f⟫_ℂ‖ ^ 2) := by ring
  refine ⟨hmem, ext_inner_basis oscBasis fun n => ?_⟩
  rw [inner_fracPow, inner_sub_right, hD, wt_two]
  push_cast
  ring

/-- The squared graph norm `‖f‖² + ‖(I - D)^{j/2} f‖²` of `X_{G,j}`. -/
def graphNormSq (j : ℕ) (f : (fracPow j).domain) : ℝ := ‖(f : XG)‖ ^ 2 + ‖fracPow j f‖ ^ 2

theorem norm_sq_eq_tsum (f : XG) : ‖f‖ ^ 2 = ∑' ℓ : ℕ, ‖⟪oscBasis ℓ, f⟫_ℂ‖ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h := lp.norm_rpow_eq_tsum hp (oscBasis.repr f)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map,
    oscBasis.repr_apply_apply] at h
  exact h

theorem summable_coef_sq (f : XG) : Summable fun ℓ : ℕ => ‖⟪oscBasis ℓ, f⟫_ℂ‖ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have := (lp.memℓp (oscBasis.repr f)).summable hp
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, oscBasis.repr_apply_apply] at this
  exact this

theorem norm_fracPow_sq (j : ℕ) (f : (fracPow j).domain) :
    ‖fracPow j f‖ ^ 2 = ∑' ℓ : ℕ, (1 + (ℓ : ℝ)) ^ j * ‖⟪oscBasis ℓ, (f : XG)⟫_ℂ‖ ^ 2 := by
  rw [norm_sq_eq_tsum]
  congr 1
  funext ℓ
  rw [inner_fracPow, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, wt_sq]

/-- **The squared graph norm in Hermite coefficients**:
`‖f‖² + ‖(I - D)^{j/2} f‖² = ∑ (1 + (1 + ℓ)^j) |⟪e_ℓ, f⟫|²`. -/
theorem graphNormSq_eq (j : ℕ) (f : (fracPow j).domain) :
    graphNormSq j f = ∑' ℓ : ℕ, (1 + (1 + (ℓ : ℝ)) ^ j) * ‖⟪oscBasis ℓ, (f : XG)⟫_ℂ‖ ^ 2 := by
  have h1 := summable_coef_sq (f : XG)
  have h2 := (mem_XGj_iff j f).1 f.2
  rw [graphNormSq, norm_fracPow_sq, norm_sq_eq_tsum, ← h1.tsum_add h2]
  congr 1
  funext ℓ
  ring

/-! ## The Hermite levels -/

/-- The polynomial of the `ℓ`-th level (B0094's `oscBasis_level`). -/
def lev (ℓ : ℕ) : ℂ[X] := (oscBasis_level ℓ).choose

/-- `U_G e_ℓ`: the angular-two Hermite function of total degree `2 + 2ℓ`. -/
def φS (ℓ : ℕ) : S2 := coreS (lev ℓ)

theorem isAngularTwo_φS (ℓ : ℕ) : IsAngularTwo (φS ℓ) := (oscBasis_level ℓ).choose_spec.2.1

theorem toXG_φS (ℓ : ℕ) : toXG (φS ℓ) = oscBasis ℓ :=
  (oscBasis_level ℓ).choose_spec.2.2.1.symm

theorem oscL_φS (ℓ : ℕ) : oscL (φS ℓ) = ((-(ℓ : ℝ) : ℝ) : ℂ) • φS ℓ := by
  have h : oscS (coreS (lev ℓ)) = (1 - ((2 + 2 * ℓ : ℕ) : ℂ) / 2) • coreS (lev ℓ) :=
    (oscBasis_level ℓ).choose_spec.2.2.2
  rw [oscL_eq, φS, h]
  congr 1
  push_cast
  ring

theorem isGP_φS (ℓ : ℕ) : IsGP (φS ℓ) := isGP_coreS _

theorem Qop_φS (k ℓ : ℕ) : Qop k (φS ℓ) = ((qpoly k (2 + ℓ) : ℝ) : ℂ) • φS ℓ := by
  rw [Qop_eigen k (oscL_φS ℓ)]
  congr 3
  ring

/-- A finite combination `∑_{ℓ ∈ s} aₗ φS ℓ` of Hermite levels. -/
def chi (s : Finset ℕ) (a : ℕ → ℂ) : S2 := ∑ ℓ ∈ s, a ℓ • φS ℓ

theorem isAngularTwo_zero : IsAngularTwo (⇑(0 : S2)) := fun θ z => by simp

theorem isAngularTwo_chi (s : Finset ℕ) (a : ℕ → ℂ) : IsAngularTwo (chi s a) := by
  classical
  unfold chi
  induction s using Finset.induction_on with
  | empty => simpa using isAngularTwo_zero
  | insert b s hb ih =>
    rw [Finset.sum_insert hb]
    exact ((isAngularTwo_φS b).smul (a b)).add ih

theorem isGP_chi (s : Finset ℕ) (a : ℕ → ℂ) : IsGP (chi s a) :=
  IsGP.sum s _ fun ℓ _ => (isGP_φS ℓ).smul (a ℓ)

theorem toXG_chi (s : Finset ℕ) (a : ℕ → ℂ) :
    toXG (chi s a) = ∑ ℓ ∈ s, a ℓ • oscBasis ℓ := by
  rw [chi, toXG_sum]
  simp only [toXG_smul, toXG_φS]

theorem Qop_chi (k : ℕ) (s : Finset ℕ) (a : ℕ → ℂ) :
    Qop k (chi s a) = chi s fun ℓ => a ℓ * ((qpoly k (2 + ℓ) : ℝ) : ℂ) := by
  rw [chi, chi, map_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [map_smul, Qop_φS, smul_smul]

/-- `⟪J χ, J (Q_k χ)⟫ = 2π ∑ qpoly k (2 + ℓ) |aₗ|²` on a finite combination of levels. -/
theorem inner_J_chi_Qop (k : ℕ) (s : Finset ℕ) (a : ℕ → ℂ) :
    ⟪J (chi s a), J (Qop k (chi s a))⟫_ℂ =
      ((2 * π * ∑ ℓ ∈ s, qpoly k (2 + ℓ) * ‖a ℓ‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_J_eq_toXG (isAngularTwo_chi s a) (by rw [Qop_chi]; exact isAngularTwo_chi s _),
    Qop_chi, toXG_chi, toXG_chi, oscBasis.orthonormal.inner_sum]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← mul_assoc, mul_comm (conj (a ℓ)) (a ℓ), Complex.mul_conj']
  ring

/-- **The squared norms of all `k`-th order conjugated derivatives of a finite combination of
Hermite levels** (tex line 1863):
`∑_{|w| = k} ‖A_w χ‖²_{L²} = 2π ∑ qpoly k (2 + ℓ) |aₗ|²`. -/
theorem sum_norm_sq_Aw_chi (k : ℕ) (s : Finset ℕ) (a : ℕ → ℂ) :
    ∑ w : Fin k → Fin 2, ‖J (Aw k w (chi s a))‖ ^ 2 =
      2 * π * ∑ ℓ ∈ s, qpoly k (2 + ℓ) * ‖a ℓ‖ ^ 2 := by
  rw [sum_norm_sq_Aw, inner_J_chi_Qop, Complex.ofReal_re]

/-! ## Comparison of `qpoly` with `(1 + ℓ)^j` -/

theorem qpoly_nonneg (k ℓ : ℕ) : 0 ≤ qpoly k (2 + ℓ) :=
  Finset.prod_nonneg fun m _ => by positivity

theorem qpoly_ge (k ℓ : ℕ) : (1 + (ℓ : ℝ)) ^ k ≤ qpoly k (2 + ℓ) := by
  have e : (1 + (ℓ : ℝ)) ^ k = ∏ _m ∈ Finset.range k, (1 + (ℓ : ℝ)) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [e, qpoly]
  refine Finset.prod_le_prod (fun _ _ => by positivity) fun m _ => ?_
  have : (0 : ℝ) ≤ (m : ℝ) / 2 := by positivity
  linarith

theorem qpoly_le {k j : ℕ} (hk : k ≤ j) (ℓ : ℕ) :
    qpoly k (2 + ℓ) ≤ (2 + (j : ℝ)) ^ j * (1 + (ℓ : ℝ)) ^ j := by
  have hb : (1 : ℝ) ≤ (2 + (j : ℝ)) * (1 + (ℓ : ℝ)) := by
    nlinarith [(j.cast_nonneg : (0 : ℝ) ≤ j), (ℓ.cast_nonneg : (0 : ℝ) ≤ ℓ)]
  calc qpoly k (2 + ℓ) ≤ ((2 + (j : ℝ)) * (1 + (ℓ : ℝ))) ^ k := by
        have e : ((2 + (j : ℝ)) * (1 + (ℓ : ℝ))) ^ k =
            ∏ _m ∈ Finset.range k, ((2 + (j : ℝ)) * (1 + (ℓ : ℝ))) := by
          rw [Finset.prod_const, Finset.card_range]
        rw [e, qpoly]
        refine Finset.prod_le_prod (fun _ _ => by positivity) fun m hm => ?_
        rw [Finset.mem_range] at hm
        have hm' : (m : ℝ) ≤ j := by exact_mod_cast (hm.le.trans hk)
        nlinarith [(j.cast_nonneg : (0 : ℝ) ≤ j), (ℓ.cast_nonneg : (0 : ℝ) ≤ ℓ),
          (m.cast_nonneg : (0 : ℝ) ≤ m)]
    _ ≤ ((2 + (j : ℝ)) * (1 + (ℓ : ℝ))) ^ j := pow_le_pow_right₀ hb hk
    _ = (2 + (j : ℝ)) ^ j * (1 + (ℓ : ℝ)) ^ j := mul_pow _ _ _

/-- `∑_{k ≤ j} qpoly k (2 + ℓ)`: the weight of level `ℓ` in the Sobolev sum of order `j`. -/
def qsum (j ℓ : ℕ) : ℝ := ∑ k ∈ Finset.range (j + 1), qpoly k (2 + ℓ)

theorem qsum_nonneg (j ℓ : ℕ) : 0 ≤ qsum j ℓ :=
  Finset.sum_nonneg fun k _ => qpoly_nonneg k ℓ

/-- Lower comparison: `(1 + (1 + ℓ)^j)/2 ≤ ∑_{k ≤ j} qpoly k (2 + ℓ)`. -/
theorem qsum_ge (j ℓ : ℕ) : (1 + (1 + (ℓ : ℝ)) ^ j) / 2 ≤ qsum j ℓ := by
  have h1 : qpoly j (2 + ℓ) ≤ qsum j ℓ :=
    Finset.single_le_sum (f := fun k => qpoly k (2 + ℓ)) (fun k _ => qpoly_nonneg k ℓ)
      (Finset.mem_range.2 (Nat.lt_succ_self j))
  have h2 := qpoly_ge j ℓ
  have h3 : (1 : ℝ) ≤ (1 + (ℓ : ℝ)) ^ j := one_le_pow₀ (by linarith [(ℓ.cast_nonneg : (0:ℝ) ≤ ℓ)])
  linarith

/-- Upper comparison: `∑_{k ≤ j} qpoly k (2 + ℓ) ≤ (j + 1)(j + 2)^j (1 + (1 + ℓ)^j)`. -/
theorem qsum_le (j ℓ : ℕ) :
    qsum j ℓ ≤ ((j : ℝ) + 1) * (2 + (j : ℝ)) ^ j * (1 + (1 + (ℓ : ℝ)) ^ j) := by
  have h : ∀ k ∈ Finset.range (j + 1), qpoly k (2 + ℓ) ≤ (2 + (j : ℝ)) ^ j * (1 + (ℓ : ℝ)) ^ j :=
    fun k hk => qpoly_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) ℓ
  have hs := Finset.sum_le_sum h
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have hpos : (0 : ℝ) ≤ (2 + (j : ℝ)) ^ j := by positivity
  calc qsum j ℓ ≤ ((j + 1 : ℕ) : ℝ) * ((2 + (j : ℝ)) ^ j * (1 + (ℓ : ℝ)) ^ j) := hs
    _ ≤ ((j : ℝ) + 1) * (2 + (j : ℝ)) ^ j * (1 + (1 + (ℓ : ℝ)) ^ j) := by
        push_cast
        nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1) hpos]

end UnforcedLeray.B0121
