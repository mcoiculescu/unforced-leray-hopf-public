import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8

/-!
# `PartIII-b:C/asrc/ra/8/2/org` : the distinct-center products of `r_per` (objects and leaves)

Source of record `the November 2 reference manuscript`
(73 pages): 5026-5031 ("`r_per` consists of distinct-center convection products and `(v - Σ_jV_j)`
terms. Gaussian summation ... bound its cell norms ... by `C δ_base M(A) s^{5/2}`"), 4371
(`δ_base = P_ν e^{C_Σ/ν - b_Σ c²}`), 4955-4972 (`A^y = χ_f A`, `M(A)`, `a = 1 + νs`,
`x_j = (q - jc, η)`, `c = ν⁻²`, `V_j = a⁻² e^{-|x_j|²/(4a)} J x_j`, `h^p_A = Σ_j [V_j, A^y_mer x_j]`).

## Objects (the matrix `B` stands for `A^y(s)`)

* `rcBrk ν s B j` : the bracket `b_j = [V_j, B_mer x_j] = B_mer V_j - DV_j(B_mer x_j)` (4971-4972);
  `brk ν χ A s j = rcBrk ν s (Ay ν χ A s) j` by definition (`brk_eq_rcBrk`);
* `rcPair ν s B j k` : the pair term `P_{jk} = (V_k·∇)b_j + (b_j·∇)V_k` (5026-5027);
* `rcCross ν s B = Σ_j Σ_{k≠j} P_{jk}`; `rCross ν χ A s = rcCross ν s (Ay ν χ A s)`
  by definition (`rCross_eq_rcCross`);
* `rcW ν s j x = e^{-(q - jc)²/(8a)}` : the lattice weight, in the form of `FAcLatticeWeight`.

## Leaves (all for `0 < ν ≤ 1`, `0 < s ≤ 1.1/ν`, hence `1 ≤ a ≤ 2.1`, `c = ν⁻² ≥ 1`)

* `RcBrkPointwise`, `RcHessDir`, `RcBrkDerivPointwise` : `b_j`, `D²V_j`, `Db_j` are
  `|B|·poly(|x_j|)·e^{-|x_j|²/(4a)}` (4963-4972: `V_j` is a Gaussian times `Jx_j`);
* `RcPairPointwise` (spec item (a)) : `|P_{jk}| ≤ C|B| poly(|x_j|,|x_k|) e^{-(|x_j|²+|x_k|²)/(4a)}`;
* `RcPairSeparated` : for `k ≠ j`, `|x_j|² + |x_k|² ≥ (q-jc)² + (q-kc)² ≥ (j-k)²c²/2 ≥ c²/2`
  (`x_j - x_k = ((k-j)c, 0)`, for every `q`, in particular on the centred cell `|q| ≤ c/2` of
  `Cyl.avgμ c`), so a quarter of the Gaussian pays `e^{-c²/(64a)} ≤ e^{-c²/135}` (the factor
  `e^{-c²/(16a)}` of 5029-5031 up to the fixed fraction of the exponent), another the `η`-decay
  `e^{-η²/(16a)} ≤ e^{-η²/34}`, half the lattice weights, and the rest absorbs the polynomial;
* `RcCrossPointwise` (spec item (b)) : `|rcCross| ≤ K|B| e^{-c²/135} e^{-η²/34}` (sum of the
  weights over `j` and `k`, `FAcLatticeWeight`);
* `RcCellGaussL2` (spec item (c)) : a field `≤ D e^{-η²/34}` has normalized cell norm `≤ K D`;
* `RcPairContinuous`, `RcCrossContinuous` (spec item (d)) : continuity in `x` (locally uniform
  Gaussian majorant, `continuousOn_tsum` twice), giving the `AEMeasurable` conjunct.

The assembly `rCrossBound_of` (with `|A^y(s)| ≤ s^{5/2}M(A)`, `fac_frob_Ay_le`,
`aySumBdd_inst11`, and `δ_base` at `C_Σ = 0`, `b_Σ = 1/135`) is in `Cross/Of.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The bracket `b_j = [V_j, B_mer x_j] = B_mer V_j - DV_j (B_mer x_j)` at the matrix `B`
(source 4971-4972; `B = A^y(s)`). -/
def rcBrk (ν s : ℝ) (B : Mat3) (j : ℤ) (x : ℝ × ℝ) : ℝ × ℝ :=
  merApply B (Vj ν s j x) - fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))

/-- The pair term `P_{jk} = (V_k·∇)b_j + (b_j·∇)V_k` (source 5026-5027). -/
def rcPair (ν s : ℝ) (B : Mat3) (j k : ℤ) (x : ℝ × ℝ) : ℝ × ℝ :=
  fderiv ℝ (rcBrk ν s B j) x (Vj ν s k x) + fderiv ℝ (Vj ν s k) x (rcBrk ν s B j x)

/-- The distinct-center sum `Σ_j Σ_{k≠j} P_{jk}` at the matrix `B` (source 5026-5027). -/
def rcCross (ν s : ℝ) (B : Mat3) (x : ℝ × ℝ) : ℝ × ℝ :=
  ∑' j : ℤ, ∑' k : ℤ, if k = j then 0 else rcPair ν s B j k x

/-- The lattice weight `e^{-(q - jc)²/(8a)}` (the summand of `FAcLatticeWeight`). -/
def rcW (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) : ℝ :=
  Real.exp (-((x.1 - j * cOf ν) ^ 2) / (8 * ageA ν s))

theorem brk_eq_rcBrk (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ) :
    brk ν χ A s j = rcBrk ν s (Ay ν χ A s) j := rfl

theorem rCross_eq_rcCross (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) :
    rCross ν χ A s = rcCross ν s (Ay ν χ A s) := rfl

/-- `merApply B` as a continuous linear map (helper for the derivative leaves). -/
def rcMerL (B : Mat3) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := merApply B
      map_add' := fun v w => by
        simp only [merApply, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
        congr 1 <;> ring
      map_smul' := fun r v => by
        simp only [merApply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply,
          Prod.smul_mk]
        congr 1 <;> ring }

theorem rcMerL_apply (B : Mat3) (v : ℝ × ℝ) : rcMerL B v = merApply B v := rfl

/-- `V_j` is smooth in `x`. -/
theorem rc_Vj_contDiff (ν s : ℝ) (j : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Vj ν s j) := by
  unfold Vj xj Jrot sq2
  fun_prop

/-- `x_j` is smooth in `x`. -/
theorem rc_xj_contDiff (ν : ℝ) (j : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xj ν j) := by
  unfold xj
  fun_prop

/-- `b_j` is smooth in `x`. -/
theorem rc_brk_contDiff (ν s : ℝ) (B : Mat3) (j : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (rcBrk ν s B j) := by
  have hV := rc_Vj_contDiff ν s j
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => rcMerL B (Vj ν s j x)) :=
    (rcMerL B).contDiff.comp hV
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ (Vj ν s j)) :=
    hV.fderiv_right (by simp)
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => fderiv ℝ (Vj ν s j) x (rcMerL B (xj ν j x))) :=
    hD.clm_apply ((rcMerL B).contDiff.comp (rc_xj_contDiff ν j))
  exact h1.sub h2

/-- Leaf (source 4963-4972): `|b_j| ≤ C |B| (1+|x_j|²)² e^{-|x_j|²/(4a)}` (`|V_j| ≤ a⁻²e|x_j|`,
`|DV_j w| ≤ a⁻²e(1+|x_j|²/a)|w|`, `|B_mer w| ≤ 4|B||w|`, `a ≥ 1`). -/
def RcBrkPointwise : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν s : ℝ) (B : Mat3) (j : ℤ) (x : ℝ × ℝ), 0 < ν → ν ≤ 1 → 0 < s →
    s ≤ (11 / 10) / ν →
    ‖rcBrk ν s B j x‖ ≤
      C * frob B * (1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))

/-- Leaf (source 4963-4966): second derivatives of `V_j` as a bilinear form,
`|D²V_j(x)[v][w]| ≤ K (1+|x_j|²)² e^{-|x_j|²/(4a)} |v||w|` (bilinear extension of the basis
bound `HessVjUnif`). -/
def RcHessDir : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν s : ℝ) (j : ℤ) (x v w : ℝ × ℝ), 0 < ν → ν ≤ 1 → 0 < s →
    s ≤ (11 / 10) / ν →
    ‖fderiv ℝ (fderiv ℝ (Vj ν s j)) x v w‖ ≤
      K * (1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * ‖v‖ * ‖w‖

/-- Leaf (source 4963-4972): `|Db_j(x) v| ≤ C |B| (1+|x_j|²)³ e^{-|x_j|²/(4a)} |v|`, from
`Db_j(x)v = B_mer(DV_j(x)v) - D²V_j(x)[v][B_mer x_j] - DV_j(x)(B_mer v)`. -/
def RcBrkDerivPointwise : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν s : ℝ) (B : Mat3) (j : ℤ) (x v : ℝ × ℝ), 0 < ν → ν ≤ 1 → 0 < s →
    s ≤ (11 / 10) / ν →
    ‖fderiv ℝ (rcBrk ν s B j) x v‖ ≤
      C * frob B * (1 + sq2 (xj ν j x)) ^ 3 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
        ‖v‖

/-- **Pair bound** (spec item (a); source 5026-5031): each pair term is a polynomial in
`x_j, x_k` times `e^{-(|x_j|²+|x_k|²)/(4a)}`, linear in `|B| = |A^y(s)|`. -/
def RcPairPointwise : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν s : ℝ) (B : Mat3) (j k : ℤ) (x : ℝ × ℝ), 0 < ν → ν ≤ 1 → 0 < s →
    s ≤ (11 / 10) / ν →
    ‖rcPair ν s B j k x‖ ≤
      C * frob B * ((1 + sq2 (xj ν j x)) ^ 3 * (1 + sq2 (xj ν k x)) ^ 3) *
        Real.exp (-(sq2 (xj ν j x) + sq2 (xj ν k x)) / (4 * ageA ν s))

/-- **Separated pair bound** (source 5029-5031, 4371): for `k ≠ j` the centers are `|k-j|c ≥ c`
apart, so `|x_j|² + |x_k|² ≥ c²/2` and, with `a ≤ 2.1`, the pair term carries
`e^{-c²/135}`, the `η`-decay `e^{-η²/34}` and the two lattice weights. -/
def RcPairSeparated : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν s : ℝ) (B : Mat3) (j k : ℤ) (x : ℝ × ℝ), 0 < ν → ν ≤ 1 → 0 < s →
    s ≤ (11 / 10) / ν → k ≠ j →
    ‖rcPair ν s B j k x‖ ≤
      K * frob B * Real.exp (-(cOf ν ^ 2) / 135) * Real.exp (-(x.2 ^ 2) / 34) *
        (rcW ν s j x * rcW ν s k x)

/-- **Double-sum bound** (spec item (b); source 5029-5031): uniformly in `x`,
`|Σ_j Σ_{k≠j} P_{jk}| ≤ K |B| e^{-c²/135} e^{-η²/34}`. -/
def RcCrossPointwise : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν s : ℝ) (B : Mat3) (x : ℝ × ℝ), 0 < ν → ν ≤ 1 → 0 < s →
    s ≤ (11 / 10) / ν →
    ‖rcCross ν s B x‖ ≤ K * frob B * Real.exp (-(cOf ν ^ 2) / 135) * Real.exp (-(x.2 ^ 2) / 34)

/-- **Normalized cell norm of a Gaussian-decaying field** (spec item (c); the cell norm of
5029-5031 is the normalized `Cyl.avgμ c = c⁻¹ dq dη` on `[-c/2, c/2) × ℝ`):
`∫ |f|² dq/c dη ≤ (K D)²` when `|f(q, η)| ≤ D e^{-η²/34}`. -/
def RcCellGaussL2 : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (c D : ℝ) (f : ℝ × ℝ → ℝ × ℝ), 0 < c → 0 ≤ D →
    (∀ x, ‖f x‖ ≤ D * Real.exp (-(x.2 ^ 2) / 34)) →
    ∫⁻ x, ENNReal.ofReal (‖toMer (f x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ c) ≤
      ENNReal.ofReal ((K * D) ^ 2)

/-- Each pair term is continuous in `x` (`V_j` is smooth, so `b_j` is smooth). -/
def RcPairContinuous : Prop :=
  ∀ (ν s : ℝ) (B : Mat3) (j k : ℤ), Continuous (rcPair ν s B j k)

/-- **Continuity of the cross sum** (spec item (d)): locally uniform Gaussian majorant of the
pair terms, hence `rcCross ν s B` is continuous (and `rCross` is measurable). -/
def RcCrossContinuous : Prop :=
  ∀ (ν s : ℝ) (B : Mat3), 0 < ν → ν ≤ 1 → 0 < s → s ≤ (11 / 10) / ν →
    Continuous (rcCross ν s B)

end UnforcedLeray.Short.PartIIIb.Concrete
