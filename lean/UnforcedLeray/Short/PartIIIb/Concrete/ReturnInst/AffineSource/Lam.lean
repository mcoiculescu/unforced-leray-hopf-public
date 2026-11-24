import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Levels
import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope.Envelope

/-!
# The pinned real row `Λ_{μ,ν}` at the levels (source 4614-4618, 4757-4760, 4812-4815, 4863-4864)

Source of record: `the November 2 reference manuscript` (73 pages).

Part (b) of `ORG:return-concrete/instance-3/affine-source`.  The real row is
`Λ_{μ,ν}(A) = -(3π/16) ε³ ν^{5+2μ} Re[i N_ν J(μ) a₀(B_{μ,ν}[A])]` (source 4812-4815, `LamFun`),
with `B_{μ,ν}[A] = (A^y)' + μA^y/s` (4757-4758, `Bmat`) and the limiting amplitude
`a₀(B) = -½ℓ₊(H₀)∫₀^∞ t^μ e^{-λt}(d(t) - ie(t)) dt` (4614-4618, `aZero`).  "The row is bounded
because its Laplace integrand is bounded by `C t^{μ+3/2} e^{-(γ-a_s)t}`" (4863-4864): on `𝒜`,
`B` is supported in `(0, 1.1/ν)` with `|B(t)| ≤ (1+μ)t^{3/2}M(A)` there (`BmatBound`, accepted
`PartIII-b:C/inst/9/2`), so the integral converges absolutely, is linear in `A`, and
`|a₀(B_{μ,ν}[A])| ≤ C_ν M(A) ≤ C_ν' ‖A‖_𝒜` (generic envelope, source 5089-5091).

## Leaves (tasks)

* `AZeroBmatLinear as χf` : `A ↦ a₀(B_{μ,ν}[A])` is additive and real-homogeneous on `𝒜`;
* `AZeroBmatBound as χf` : `‖a₀(B_{μ,ν}[A])‖ ≤ C M(A)` at each fixed `ν > 0`, `μ ≥ 0`.

## Proved here

* `lamFun_add_of`, `lamFun_smul_of`, `abs_lamFun_le_of` : linearity and the bound of `Λ`;
* `exists_lamOp_of` : the pin `∃ l : 𝒜 →L ℝ, ∀ A, l A = Λ(ιA)` at one regime (the third clause of
  `IsSourceLPinned`, hypothesis `hLam` of `concreteBase_isSourceLPinned`);
* `SeqData.eventually_exists_LamOp` : the pin at all large levels of the sequence, `z ∈ [-1,1]`,
  with the envelope `affMEnvelope` (accepted `PartIII-b:C/env/3`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. The leaves -/

/-- **`A ↦ a₀(B_{μ,ν}[A])` is real-linear on `𝒜`** (source 4614-4618, 4757-4760, 4812-4815): for
`A, A' ∈ 𝒜` the Laplace integrands `t^μ e^{-λt}(d(t) - ie(t))` of `B = (A^y)' + μA^y/s` are
integrable on `(0,∞)` (`B = 0` for `t ≥ 1.1/ν`, `|B(t)| ≤ (1+μ)t^{3/2}M(A)` on `(0, 1.1/ν]`), and
`B_{μ,ν}[A + A'] = B_{μ,ν}[A] + B_{μ,ν}[A']`, `B_{μ,ν}[rA] = rB_{μ,ν}[A]` at every `t > 0`
(`BmatLinear` with `AyDiffAt`); `d, e` are linear in `B`. -/
def AZeroBmatLinear (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (lam ell : ℂ) (ν μ : ℝ), 0 < ν → 0 ≤ μ →
    ∀ (A A' : ℝ → Mat3) (r : ℝ), IsAffElem as A → IsAffElem as A' →
      aZero lam ell (μ : ℂ) (Bmat ν μ χf (A + A')) =
          aZero lam ell (μ : ℂ) (Bmat ν μ χf A) + aZero lam ell (μ : ℂ) (Bmat ν μ χf A') ∧
        aZero lam ell (μ : ℂ) (Bmat ν μ χf (r • A)) =
          (r : ℂ) * aZero lam ell (μ : ℂ) (Bmat ν μ χf A)

/-- **The Laplace row is bounded** (source 4863-4864: "its Laplace integrand is bounded by
`C t^{μ+3/2} e^{-(γ-a_s)t}`"): at each fixed `ν > 0`, `μ ≥ 0`, `|a₀(B_{μ,ν}[A])| ≤ C M(A)` on `𝒜`
(`B` vanishes for `t ≥ 1.1/ν` and `|B(t)| ≤ (1+μ)t^{3/2}M(A)` on `(0, 1.1/ν]`, `BmatBound`;
`|t^μ e^{-λt}| ≤ (1.1/ν)^μ e^{1.1|Re λ|/ν}` there). -/
def AZeroBmatBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (lam ell : ℂ) (ν μ : ℝ), 0 < ν → 0 ≤ μ →
    ∃ C : ℝ, ∀ A : ℝ → Mat3, IsAffElem as A →
      ‖aZero lam ell (μ : ℂ) (Bmat ν μ χf A)‖ ≤ C * affM ν χf A

/-! ## 2. Linearity and the bound of `Λ` -/

section Row

variable {as : ℝ} {χf : ℝ → ℝ} {lam κ ell : ℂ} {J : ℂ → ℂ} {ε ν μ : ℝ}

/-- `LamFun = K₀ Re[w a₀]` with `K₀ = -(3π/16)ε³ν^{5+2μ}`, `w = iN_νJ(μ)`. -/
theorem lamFun_eq (A : ℝ → Mat3) :
    LamFun lam κ ell J ε ν μ χf A = (-(3 * Real.pi / 16) * ε ^ 3 * ν ^ (5 + 2 * μ)) *
      (Complex.I * Nnu lam κ ν * J (μ : ℂ) * aZero lam ell (μ : ℂ) (Bmat ν μ χf A)).re := rfl

theorem lamFun_add_of (hl : AZeroBmatLinear as χf) (hχ : IsSourceCutoffC χf) (hν : 0 < ν)
    (hμ : 0 ≤ μ) {A A' : ℝ → Mat3} (hA : IsAffElem as A) (hA' : IsAffElem as A') :
    LamFun lam κ ell J ε ν μ χf (A + A') =
      LamFun lam κ ell J ε ν μ χf A + LamFun lam κ ell J ε ν μ χf A' := by
  rw [lamFun_eq, lamFun_eq, lamFun_eq, (hl hχ lam ell ν μ hν hμ A A' 1 hA hA').1, mul_add,
    Complex.add_re]
  ring

theorem lamFun_smul_of (hl : AZeroBmatLinear as χf) (hχ : IsSourceCutoffC χf) (hν : 0 < ν)
    (hμ : 0 ≤ μ) (r : ℝ) {A : ℝ → Mat3} (hA : IsAffElem as A) :
    LamFun lam κ ell J ε ν μ χf (r • A) = r * LamFun lam κ ell J ε ν μ χf A := by
  rw [lamFun_eq, lamFun_eq, (hl hχ lam ell ν μ hν hμ A A r hA hA).2]
  have e : Complex.I * Nnu lam κ ν * J (μ : ℂ) * ((r : ℂ) * aZero lam ell (μ : ℂ) (Bmat ν μ χf A))
      = (r : ℂ) * (Complex.I * Nnu lam κ ν * J (μ : ℂ) * aZero lam ell (μ : ℂ) (Bmat ν μ χf A)) := by
    ring
  rw [e, Complex.re_ofReal_mul]
  ring

/-- `|Λ(A)| ≤ |K₀| ‖w‖ C M(A)`. -/
theorem abs_lamFun_le_of {C : ℝ}
    (hC : ∀ A : ℝ → Mat3, IsAffElem as A → ‖aZero lam ell (μ : ℂ) (Bmat ν μ χf A)‖ ≤ C * affM ν χf A)
    {A : ℝ → Mat3} (hA : IsAffElem as A) :
    |LamFun lam κ ell J ε ν μ χf A| ≤
      |-(3 * Real.pi / 16) * ε ^ 3 * ν ^ (5 + 2 * μ)| * ‖Complex.I * Nnu lam κ ν * J (μ : ℂ)‖ *
        (C * affM ν χf A) := by
  set K0 : ℝ := -(3 * Real.pi / 16) * ε ^ 3 * ν ^ (5 + 2 * μ)
  set w : ℂ := Complex.I * Nnu lam κ ν * J (μ : ℂ)
  set a : ℂ := aZero lam ell (μ : ℂ) (Bmat ν μ χf A)
  have h1 : |(w * a).re| ≤ ‖w‖ * (C * affM ν χf A) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [Complex.norm_mul]
    exact mul_le_mul_of_nonneg_left (hC A hA) (norm_nonneg w)
  calc |LamFun lam κ ell J ε ν μ χf A| = |K0| * |(w * a).re| := by
        rw [lamFun_eq, abs_mul]
    _ ≤ |K0| * (‖w‖ * (C * affM ν χf A)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg K0)
    _ = |K0| * ‖w‖ * (C * affM ν χf A) := by ring

end Row

/-! ## 3. The pin at one regime -/

/-- **The pin of `Λ` at one regime** (source 4812-4815, 4863-4864): with the leaves and an envelope
`M(ιA) ≤ C_env ‖A‖` (source 5089-5091), `A ↦ Λ_{μ,ν}(ιA)` is a continuous linear functional on
`𝒜 = AffSp a_s`. -/
theorem exists_lamOp_of {as ν ε μ : ℝ} {χf : ℝ → ℝ} {lam κ ell : ℂ} {J : ℂ → ℂ}
    (hl : AZeroBmatLinear as χf) (hb : AZeroBmatBound as χf) (hχ : IsSourceCutoffC χf)
    (hν : 0 < ν) (hμ : 0 ≤ μ) (Cenv : ℝ)
    (henv : ∀ A : AffSp as, affM ν χf (affIota as A) ≤ Cenv * ‖A‖) :
    ∃ l : AffSp as →L[ℝ] ℝ, ∀ A, l A = LamFun lam κ ell J ε ν μ χf (affIota as A) := by
  obtain ⟨C, hC⟩ := hb hχ lam ell ν μ hν hμ
  set K := |-(3 * Real.pi / 16) * ε ^ 3 * ν ^ (5 + 2 * μ)| * ‖Complex.I * Nnu lam κ ν * J (μ : ℂ)‖
    with hK
  have hK0 : 0 ≤ K := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hC' : ∀ A : ℝ → Mat3, IsAffElem as A →
      ‖aZero lam ell (μ : ℂ) (Bmat ν μ χf A)‖ ≤ max C 0 * affM ν χf A := fun A hA =>
    (hC A hA).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (affM_nonneg _ _ _))
  let f : AffSp as →ₗ[ℝ] ℝ :=
    { toFun := fun A => LamFun lam κ ell J ε ν μ χf (affIota as A)
      map_add' := fun A A' => by
        simp only [map_add]
        exact lamFun_add_of hl hχ hν hμ (affIota_mem as A) (affIota_mem as A')
      map_smul' := fun r A => by
        simp only [map_smul, RingHom.id_apply, smul_eq_mul]
        exact lamFun_smul_of hl hχ hν hμ r (affIota_mem as A) }
  refine ⟨f.mkContinuous (K * max C 0 * Cenv) fun A => ?_, fun A => rfl⟩
  show ‖LamFun lam κ ell J ε ν μ χf (affIota as A)‖ ≤ K * max C 0 * Cenv * ‖A‖
  rw [Real.norm_eq_abs]
  have h1 := abs_lamFun_le_of (lam := lam) (κ := κ) (J := J) (ε := ε) hC' (affIota_mem as A)
  have h2 : K * (max C 0 * affM ν χf (affIota as A)) ≤ K * (max C 0 * (Cenv * ‖A‖)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (henv A) (le_max_right _ _)) hK0
  calc |LamFun lam κ ell J ε ν μ χf (affIota as A)|
      ≤ K * (max C 0 * affM ν χf (affIota as A)) := h1
    _ ≤ K * (max C 0 * (Cenv * ‖A‖)) := h2
    _ = K * max C 0 * Cenv * ‖A‖ := by ring

/-! ## 4. The pin along the sequence -/

/-- **The `Λ` pin at the levels** (source 4812-4815 at 5926-5950): for large `n` and
`z ∈ [-1,1]`, `∃ l : 𝒜 →L ℝ, ∀ A, l A = LamFun λ κ ℓ₊(H₀) 𝒥 ε_n ν_n μ_n(z) χ_f (ιA)`, the
hypothesis `hLam` of `concreteBase_isSourceLPinned` at `L = D.level n`, `μ = D.mu n z`. -/
theorem SeqData.eventually_exists_LamOp (D : SeqData) (hω : D.Pl.eigenvalue.im ≠ 0)
    (hσ0 : 0 < D.σ₀) (hσ1 : D.σ₀ < 1 / 4) (hχf : IsSourceCutoffC D.K.χf) (has : 0 ≤ D.K.as)
    (hl : AZeroBmatLinear D.K.as D.K.χf) (hb : AZeroBmatBound D.K.as D.K.χf) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ l : AffSp D.K.as →L[ℝ] ℝ, ∀ A, l A =
        LamFun D.Pl.eigenvalue D.Pl.kappa D.Pl.strainCoupling (planarJ D.Pl) (D.level n).ε
          (D.level n).ν (D.mu n z) D.K.χf (affIota D.K.as A) := by
  obtain ⟨C, -, hC⟩ := affM_le_norm_of (affMEnvelope D.K.χf hχf)
  filter_upwards [D.eventually_mu_mem_Ioo hω hσ0 hσ1] with n hn z hz
  have hν : 0 < (D.level n).ν := retNu_pos _ _ _
  exact exists_lamOp_of hl hb hχf hν (hn z hz).1.le
    (C * Real.exp (1.1 * D.K.as / (D.level n).ν)) fun A =>
      hC D.K.as (D.level n).ν (fun A => affIota D.K.as A) has hν (affIota_mem D.K.as)
        (fun A => (affNorm_affIota D.K.as A).le) A

end UnforcedLeray.Short.PartIIIb.Concrete
