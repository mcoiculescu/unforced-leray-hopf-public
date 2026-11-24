import UnforcedLeray.Units.B0094
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# B0121 helper: the conjugated derivatives `∂ᵢ - yᵢ/4` as oscillator ladder operators

Blueprint unit B0121 (`eq:st18-t00100`, `paper/main.tex` lines 1856--1865). Under the
conjugation `U_G f = f / √G` of B0093 (`eq:st18-t00067`, tex lines 1498--1502), the Cartesian
derivative `∂ᵢ` becomes `Aᵢ = ∂ᵢ - yᵢ/4` (tex line 1863: "an oscillator creation operator up to
a constant"); its formal `L²(ℝ²)` adjoint is `Bᵢ = -∂ᵢ - yᵢ/4`. On `𝓢(ℝ², ℂ)`:

* `sum_BA`: `B₁A₁ + B₂A₂ = T := 2 - osc`, where `osc = Δ - |y|²/16 + 3/2` is the oscillator of
  `eq:st18-t00067` (B0094's `oscS`, `oscL_eq`);
* `Top_Aop`: `T Aᵢ = Aᵢ (T + 1/2)`, the ladder relation (`Aᵢ` raises the Hermite level by one);
* `sum_Bw_Aw`: `∑_{|w| = k} B_w A_w = Q_k := ∏_{m<k} (T + m/2)` over the `2^k` words `w`
  (ordered products of derivatives); `inner_Aw`: `A_w` and `B_w` are formally adjoint;
* `sum_norm_sq_Aw`: `∑_{|w|=k} ‖A_w φ‖²_{L²} = Re ⟪φ, Q_k φ⟫_{L²}` (tex line 1863: the sum of
  squared norms of products of `k` creation operators), and `Qop_eigen`: on an eigenfunction of
  the oscillator, `Q_k` is the explicit product.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory
open LineDeriv
open scoped SchwartzMap InnerProductSpace ComplexConjugate ContDiff

namespace UnforcedLeray.B0121

open UnforcedLeray.B0094

/-- The Schwartz space `𝓢(ℝ², ℂ)`. -/
abbrev S2 : Type := 𝓢(ℝ × ℝ, ℂ)

/-- `L²(ℝ², dy)`. -/
abbrev L2v : Type := Lp ℂ 2 (volume : Measure (ℝ × ℝ))

/-- The embedding `𝓢(ℝ², ℂ) → L²(ℝ², dy)`. -/
abbrev J : S2 →L[ℂ] L2v := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (ℝ × ℝ))

/-- The unit vectors `e₁, e₂` (B0094's `e1`, `e2`). -/
def ev : Fin 2 → ℝ × ℝ := ![e1, e2]

/-- The coordinate functionals `y ↦ yᵢ`. -/
def crdL : Fin 2 → (ℝ × ℝ →L[ℝ] ℝ) :=
  ![ContinuousLinearMap.fst ℝ ℝ ℝ, ContinuousLinearMap.snd ℝ ℝ ℝ]

/-- The coordinate `yᵢ` as a complex function. -/
def crdC (i : Fin 2) (z : ℝ × ℝ) : ℂ := ((crdL i z : ℝ) : ℂ)

@[simp] theorem ev_zero : ev 0 = e1 := rfl
@[simp] theorem ev_one : ev 1 = e2 := rfl

@[simp] theorem crdL_zero_apply (z : ℝ × ℝ) : crdL 0 z = z.1 := rfl
@[simp] theorem crdL_one_apply (z : ℝ × ℝ) : crdL 1 z = z.2 := rfl

@[simp] theorem crdL_zero_ev_zero : crdL 0 (ev 0) = 1 := rfl
@[simp] theorem crdL_zero_ev_one : crdL 0 (ev 1) = 0 := rfl
@[simp] theorem crdL_one_ev_zero : crdL 1 (ev 0) = 0 := rfl
@[simp] theorem crdL_one_ev_one : crdL 1 (ev 1) = 1 := rfl

theorem crdL_ev_self (i : Fin 2) : crdL i (ev i) = 1 := by
  fin_cases i <;> rfl

theorem hasTemperateGrowth_crdC (i : Fin 2) : (crdC i).HasTemperateGrowth :=
  hasTemperateGrowth_ofReal_comp (crdL i).hasTemperateGrowth

theorem hasFDerivAt_crdC (i : Fin 2) (z : ℝ × ℝ) :
    HasFDerivAt (crdC i) (Complex.ofRealCLM.comp (crdL i)) z := by
  have h := (Complex.ofRealCLM.comp (crdL i)).hasFDerivAt (x := z)
  have e : (⇑(Complex.ofRealCLM.comp (crdL i)) : ℝ × ℝ → ℂ) = crdC i := by
    funext y
    simp [crdC]
  rwa [e] at h

/-! ## The basic operators on `𝓢(ℝ², ℂ)` -/

/-- Multiplication by `yᵢ`. -/
def X (i : Fin 2) : S2 →L[ℂ] S2 := SchwartzMap.smulLeftCLM ℂ (crdC i)

theorem X_apply (i : Fin 2) (φ : S2) (z : ℝ × ℝ) : X i φ z = crdC i z * φ z := by
  simp [X, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_crdC i)]

/-- The partial derivative `∂ᵢ`. -/
def dop (i : Fin 2) : S2 →L[ℂ] S2 := lineDerivOpCLM ℂ S2 (ev i)

theorem dop_apply (i : Fin 2) (φ : S2) (z : ℝ × ℝ) : dop i φ z = fderiv ℝ (⇑φ) z (ev i) := rfl

theorem coe_dop (i : Fin 2) (φ : S2) : ⇑(dop i φ) = fun z => fderiv ℝ (⇑φ) z (ev i) := rfl

/-- The product rule `∂ₖ (yᵢ φ) = δᵢₖ φ + yᵢ ∂ₖ φ`. -/
theorem dop_X (k i : Fin 2) (φ : S2) :
    dop k (X i φ) = ((crdL i (ev k) : ℝ) : ℂ) • φ + X i (dop k φ) := by
  ext z
  have hX : ⇑(X i φ) = crdC i * ⇑φ := by
    funext y
    rw [X_apply, Pi.mul_apply]
  have hm := (hasFDerivAt_crdC i z).mul (φ.hasFDerivAt z)
  rw [dop_apply, hX, hm.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul, add_apply,
    smul_apply, X_apply, dop_apply]
  ring

/-- Second derivatives of a smooth function as a bilinear form. -/
theorem fderiv_fderiv_apply {φ : ℝ × ℝ → ℂ} (h : ContDiff ℝ ∞ φ) (v w x : ℝ × ℝ) :
    fderiv ℝ (fun y => fderiv ℝ φ y w) x v = fderiv ℝ (fderiv ℝ φ) x v w := by
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (ContDiff.fderiv_right (m := ∞) h (by simp)).differentiable (by simp)
  have hx : HasFDerivAt (fun y => fderiv ℝ φ y w) ((fderiv ℝ (fderiv ℝ φ) x).flip w) x := by
    have := (hd x).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
    simpa using this
  rw [hx.fderiv]
  rfl

/-- Partial derivatives of Schwartz functions commute. -/
theorem dop_comm (i k : Fin 2) (φ : S2) : dop i (dop k φ) = dop k (dop i φ) := by
  ext z
  have hφ : ContDiff ℝ ∞ (⇑φ) := φ.smooth ⊤
  rw [dop_apply, dop_apply, coe_dop, coe_dop, fderiv_fderiv_apply hφ, fderiv_fderiv_apply hφ]
  have hs : IsSymmSndFDerivAt ℝ (⇑φ) z := ContDiffAt.isSymmSndFDerivAt hφ.contDiffAt (by simp)
  exact hs.eq (ev i) (ev k)

theorem dop_dop_dop (k i : Fin 2) (φ : S2) : dop k (dop k (dop i φ)) = dop i (dop k (dop k φ)) := by
  rw [dop_comm k i φ, dop_comm k i (dop k φ)]

/-- `Aᵢ = ∂ᵢ - yᵢ/4 = U_G ∂ᵢ U_G⁻¹`. -/
def Aop (i : Fin 2) : S2 →L[ℂ] S2 := dop i - (4⁻¹ : ℂ) • X i

/-- `Bᵢ = -∂ᵢ - yᵢ/4`, the formal adjoint of `Aᵢ`. -/
def Bop (i : Fin 2) : S2 →L[ℂ] S2 := -dop i - (4⁻¹ : ℂ) • X i

/-- The oscillator `Δ - |y|²/16 + 3/2` as a continuous linear map. -/
def oscL : S2 →L[ℂ] S2 :=
  (dop 0).comp (dop 0) + (dop 1).comp (dop 1) - (16⁻¹ : ℂ) • ((X 0).comp (X 0) + (X 1).comp (X 1))
    + (3 / 2 : ℂ) • ContinuousLinearMap.id ℂ S2

/-- `T = 2 - osc`. -/
def Top : S2 →L[ℂ] S2 := (2 : ℂ) • ContinuousLinearMap.id ℂ S2 - oscL

theorem Aop_apply (i : Fin 2) (φ : S2) : Aop i φ = dop i φ - (4⁻¹ : ℂ) • X i φ := rfl

theorem Bop_apply (i : Fin 2) (φ : S2) : Bop i φ = -dop i φ - (4⁻¹ : ℂ) • X i φ := rfl

theorem oscL_apply (φ : S2) : oscL φ = dop 0 (dop 0 φ) + dop 1 (dop 1 φ) -
    (16⁻¹ : ℂ) • (X 0 (X 0 φ) + X 1 (X 1 φ)) + (3 / 2 : ℂ) • φ := rfl

theorem Top_apply (φ : S2) : Top φ = (2 : ℂ) • φ - oscL φ := rfl

/-- `oscL` is B0094's oscillator `oscS` (the right side of `eq:st18-t00067`). -/
theorem oscL_eq (φ : S2) : oscL φ = oscS φ := by
  ext z
  rw [oscS_apply, oscL_apply]
  simp only [add_apply, sub_apply, smul_apply, X_apply,
    smul_eq_mul, lapS, dop, lineDerivOpCLM_apply, ev_zero, ev_one, crdC, crdL_zero_apply,
    crdL_one_apply, radS, sz]
  push_cast
  ring

/-- `Bᵢ Aᵢ = -∂ᵢ² + 1/4 + yᵢ²/16`. -/
theorem Bop_Aop (i : Fin 2) (φ : S2) :
    Bop i (Aop i φ) = -dop i (dop i φ) + (4⁻¹ : ℂ) • φ + (16⁻¹ : ℂ) • X i (X i φ) := by
  rw [Bop_apply, Aop_apply, map_sub, map_sub, map_smul, map_smul, dop_X, crdL_ev_self]
  ext z
  simp only [add_apply, sub_apply, neg_apply,
    smul_apply, X_apply, smul_eq_mul, Complex.ofReal_one]
  ring

/-- **`B₁A₁ + B₂A₂ = T = 2 - osc`**. -/
theorem sum_BA (φ : S2) : ∑ i : Fin 2, Bop i (Aop i φ) = Top φ := by
  rw [Fin.sum_univ_two, Bop_Aop, Bop_Aop, Top_apply, oscL_apply]
  ext z
  simp only [add_apply, sub_apply, neg_apply,
    smul_apply, X_apply, smul_eq_mul]
  ring

/-- **The ladder relation** `T Aᵢ = Aᵢ T + Aᵢ/2`. -/
theorem Top_Aop (i : Fin 2) (φ : S2) :
    Top (Aop i φ) = Aop i (Top φ) + (2⁻¹ : ℂ) • Aop i φ := by
  fin_cases i
  · simp only [Fin.zero_eta, Top_apply, oscL_apply, Aop_apply, map_add, map_sub, map_smul,
      dop_X, crdL_zero_ev_zero, crdL_zero_ev_one, crdL_one_ev_zero, crdL_one_ev_one,
      Complex.ofReal_one, Complex.ofReal_zero, one_smul, zero_smul, zero_add]
    rw [dop_dop_dop 1 0 φ]
    ext z
    simp only [add_apply, sub_apply, smul_apply, X_apply,
      smul_eq_mul]
    ring
  · simp only [Fin.mk_one, Top_apply, oscL_apply, Aop_apply, map_add, map_sub, map_smul,
      dop_X, crdL_zero_ev_zero, crdL_zero_ev_one, crdL_one_ev_zero, crdL_one_ev_one,
      Complex.ofReal_one, Complex.ofReal_zero, one_smul, zero_smul, zero_add]
    rw [dop_dop_dop 0 1 φ]
    ext z
    simp only [add_apply, sub_apply, smul_apply, X_apply,
      smul_eq_mul]
    ring

/-! ## Words of derivatives -/

/-- `A_w = A_{w 0} ∘ A_{w 1} ∘ ⋯ ∘ A_{w (k-1)}` for a word `w` of length `k`. -/
def Aw : (k : ℕ) → (Fin k → Fin 2) → (S2 →L[ℂ] S2)
  | 0, _ => ContinuousLinearMap.id ℂ S2
  | k + 1, w => (Aop (w 0)).comp (Aw k (Fin.tail w))

/-- `B_w = B_{w (k-1)} ∘ ⋯ ∘ B_{w 0}`, the formal adjoint of `A_w`. -/
def Bw : (k : ℕ) → (Fin k → Fin 2) → (S2 →L[ℂ] S2)
  | 0, _ => ContinuousLinearMap.id ℂ S2
  | k + 1, w => (Bw k (Fin.tail w)).comp (Bop (w 0))

theorem Aw_zero (w : Fin 0 → Fin 2) (φ : S2) : Aw 0 w φ = φ := rfl

theorem Aw_succ (k : ℕ) (w : Fin (k + 1) → Fin 2) (φ : S2) :
    Aw (k + 1) w φ = Aop (w 0) (Aw k (Fin.tail w) φ) := rfl

theorem Bw_succ (k : ℕ) (w : Fin (k + 1) → Fin 2) (φ : S2) :
    Bw (k + 1) w φ = Bw k (Fin.tail w) (Bop (w 0) φ) := rfl

/-- `Q₀ = 1`, `Q_{k+1} = Q_k (T + k/2)`, so `Q_k = ∏_{m<k} (T + m/2)`. -/
def Qop : ℕ → (S2 →L[ℂ] S2)
  | 0 => ContinuousLinearMap.id ℂ S2
  | k + 1 => (Qop k).comp (Top + ((k : ℂ) / 2) • ContinuousLinearMap.id ℂ S2)

theorem Qop_succ (k : ℕ) (φ : S2) : Qop (k + 1) φ = Qop k (Top φ + ((k : ℂ) / 2) • φ) := rfl

/-- The iterated ladder relation `T A_w = A_w (T + |w|/2)`. -/
theorem Top_Aw (k : ℕ) (w : Fin k → Fin 2) (φ : S2) :
    Top (Aw k w φ) = Aw k w (Top φ + ((k : ℂ) / 2) • φ) := by
  induction k generalizing φ with
  | zero => simp [Aw_zero]
  | succ k ih =>
    rw [Aw_succ, Top_Aop, ih, Aw_succ, ← map_smul, ← map_add, ← map_smul, ← map_add]
    congr 2
    rw [add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

/-- Reindexing a sum over words of length `k + 1` by the first letter and the tail. -/
theorem sum_words_succ {M : Type*} [AddCommMonoid M] (k : ℕ) (g : (Fin (k + 1) → Fin 2) → M) :
    ∑ w, g w = ∑ i : Fin 2, ∑ w : Fin k → Fin 2, g (Fin.cons i w) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 2) _ _ (fun p => rfl)).symm

/-- **`∑_{|w| = k} B_w A_w = Q_k`**. -/
theorem sum_Bw_Aw (k : ℕ) (φ : S2) : ∑ w : Fin k → Fin 2, Bw k w (Aw k w φ) = Qop k φ := by
  induction k generalizing φ with
  | zero => simp [Fintype.sum_unique, Bw, Aw, Qop]
  | succ k ih =>
    rw [sum_words_succ, Finset.sum_comm, Qop_succ, ← ih]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Bw_succ, Aw_succ, Fin.tail_cons, Fin.cons_zero]
    rw [← map_sum, sum_BA, Top_Aw]

/-! ## Adjointness in `L²(ℝ²)` -/

theorem inner_J (ψ φ : S2) : ⟪J ψ, J φ⟫_ℂ = pairS ψ φ := by
  rw [MeasureTheory.L2.inner_def, pairS]
  refine integral_congr_ae ?_
  filter_upwards [ψ.coeFn_toLp 2 volume, φ.coeFn_toLp 2 volume] with z h1 h2
  simp only [SchwartzMap.toLpCLM_apply, h1, h2, RCLike.inner_apply]
  ring

theorem pairS_dop (i : Fin 2) (ψ φ : S2) : pairS (dop i ψ) φ = -pairS ψ (dop i φ) := by
  have h := SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left (μ := volume)
    ψ φ Lc (ev i)
  simp only [Lc_apply] at h
  simp only [pairS, dop, lineDerivOpCLM_apply]
  rw [h, neg_neg]

theorem pairS_X (i : Fin 2) (ψ φ : S2) : pairS (X i ψ) φ = pairS ψ (X i φ) := by
  simp only [pairS, X_apply, map_mul, crdC, Complex.conj_ofReal]
  congr 1
  funext z
  ring

theorem pairS_sub_smul_left (a b φ : S2) (c : ℂ) :
    pairS (a - c • b) φ = pairS a φ - conj c * pairS b φ := by
  have i1 : Integrable (fun z => conj (a z) * φ z) := integrable_conj_mul a φ
  have i2 : Integrable (fun z => conj c * (conj (b z) * φ z)) :=
    (integrable_conj_mul b φ).const_mul (conj c)
  calc pairS (a - c • b) φ = ∫ z, (conj (a z) * φ z - conj c * (conj (b z) * φ z)) := by
        simp only [pairS, sub_apply, smul_apply, smul_eq_mul, map_sub, map_mul]
        congr 1
        funext z
        ring
    _ = _ := by rw [integral_sub i1 i2, integral_const_mul]; rfl

theorem pairS_neg_sub_smul_right (ψ a b : S2) (c : ℂ) :
    pairS ψ (-a - c • b) = -pairS ψ a - c * pairS ψ b := by
  have i1 : Integrable (fun z => -(conj (ψ z) * a z)) := (integrable_conj_mul ψ a).neg
  have i2 : Integrable (fun z => c * (conj (ψ z) * b z)) :=
    (integrable_conj_mul ψ b).const_mul c
  calc pairS ψ (-a - c • b) = ∫ z, (-(conj (ψ z) * a z) - c * (conj (ψ z) * b z)) := by
        simp only [pairS, sub_apply, neg_apply, smul_apply, smul_eq_mul]
        congr 1
        funext z
        ring
    _ = _ := by rw [integral_sub i1 i2, integral_neg, integral_const_mul]; rfl

/-- `Aᵢ` and `Bᵢ` are formally adjoint: `⟪Aᵢ ψ, φ⟫ = ⟪ψ, Bᵢ φ⟫`. -/
theorem pairS_Aop (i : Fin 2) (ψ φ : S2) : pairS (Aop i ψ) φ = pairS ψ (Bop i φ) := by
  rw [Aop_apply, Bop_apply, pairS_sub_smul_left, pairS_neg_sub_smul_right, pairS_dop, pairS_X]
  rw [show (starRingEnd ℂ) (4⁻¹ : ℂ) = 4⁻¹ by rw [map_inv₀, map_ofNat]]

theorem inner_Aop (i : Fin 2) (ψ φ : S2) : ⟪J (Aop i ψ), J φ⟫_ℂ = ⟪J ψ, J (Bop i φ)⟫_ℂ := by
  rw [inner_J, inner_J, pairS_Aop]

/-- `A_w` and `B_w` are formally adjoint. -/
theorem inner_Aw (k : ℕ) (w : Fin k → Fin 2) (ψ φ : S2) :
    ⟪J (Aw k w ψ), J φ⟫_ℂ = ⟪J ψ, J (Bw k w φ)⟫_ℂ := by
  induction k generalizing φ with
  | zero => rfl
  | succ k ih =>
    rw [Aw_succ, inner_Aop, ih, Bw_succ]

/-- **The squared norms of the `k`-th order conjugated derivatives**:
`∑_{|w| = k} ‖A_w φ‖²_{L²} = Re ⟪φ, Q_k φ⟫_{L²}`. -/
theorem sum_norm_sq_Aw (k : ℕ) (φ : S2) :
    ∑ w : Fin k → Fin 2, ‖J (Aw k w φ)‖ ^ 2 = (⟪J φ, J (Qop k φ)⟫_ℂ).re := by
  have h : ∀ w : Fin k → Fin 2, ‖J (Aw k w φ)‖ ^ 2 = (⟪J φ, J (Bw k w (Aw k w φ))⟫_ℂ).re := by
    intro w
    rw [← inner_Aw, @norm_sq_eq_re_inner ℂ]
    rfl
  simp_rw [h]
  rw [← Complex.re_sum, ← inner_sum, ← map_sum, sum_Bw_Aw]

/-- The product `∏_{m<k} (t + m/2)`. -/
def qpoly (k : ℕ) (t : ℝ) : ℝ := ∏ m ∈ Finset.range k, (t + (m : ℝ) / 2)

/-- On an eigenfunction `osc φ = μ φ`, `Q_k φ = ∏_{m<k} (2 - μ + m/2) φ`. -/
theorem Qop_eigen (k : ℕ) {φ : S2} {μ : ℝ} (h : oscL φ = (μ : ℂ) • φ) :
    Qop k φ = ((qpoly k (2 - μ) : ℝ) : ℂ) • φ := by
  induction k with
  | zero => simp [Qop, qpoly]
  | succ k ih =>
    rw [Qop_succ, Top_apply, h, ← sub_smul, ← add_smul, map_smul, ih, smul_smul]
    congr 1
    simp only [qpoly, Finset.prod_range_succ]
    push_cast
    ring

end UnforcedLeray.B0121
