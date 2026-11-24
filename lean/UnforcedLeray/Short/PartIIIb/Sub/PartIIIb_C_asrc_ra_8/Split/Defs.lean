import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8

/-!
# `PartIII-b:C/asrc/ra/8/1/org` : the objects and leaves of the bracket split `RPerSplit`

Source of record: `the November 2 reference manuscript` (73 pages), 4963-4978
(`V_j, p_j, ψ_j`, `f_A, e_A, h^p_A`, "The sums and their required derivatives converge by Gaussian
decay"), 5022-5027 (the Cartesian bracket calculation and `r_per`), 2040-2051 (the train; the single
Gaussian is an exact solution).

## 1. Per-center summands

`fAj, eAj, PsiAj` are the `j`-th summands of `f_A, e_A, Ψ_A` (with the sign of `f_A` moved inside,
`f_A = Σ_j fAj`); `brk` (`b_j = [V_j, A^y_mer x_j]`) is already the summand of `h^p_A`.

## 2. Closed forms (`y = x_j`, `a = 1 + νs`, `M = A^y(s)` meridional block, `G = a⁻² e^{-|y|²/(4a)}`)

* `V_j = G Jy`, `DV_j[w] = G·bkV1`, `D²V_j[w,u] = G·bkV2`, `∇p_j = G²y`;
* `b_j = G·bkP` with `bkP = MJy - JMy + (y·My)/(2a) Jy`; `Db_j[w] = G·bkD1`, `∂_u(Db_j[w]) = G·bkD2`,
  `∂_s b_j = G·(bkP(M') + ν bkPa)` (`M' = (A^y)'`, `∂_s = ν∂_a` at fixed `x`);
* `∇Ψ_j = G²((M + Mᵀ)y - (y·My)/a · y)`, `Ψ_j = (My)·∇p_j`.

All closed forms and the single-center identity were checked symbolically (exact identities, `M(s)`
arbitrary: no trace or `MerJIdentity` condition is needed).

## 3. The single-center identity (`BrkIdentity`, source 5022-5025)

`(∂_s + μ/s - νΔ)b_j + (V_j·∇)b_j + (b_j·∇)V_j = f_{A,j} + e_{A,j} + ∇Ψ_j` (meridional parts),
from `∂_sV - νΔV + V·∇V + ∇p = 0` for the single Gaussian (source 2040-2051) and the bracket
calculation; in closed form it is the polynomial identity `bk_algebra` (in `Split/Of.lean`).

## 4. The tsum calculus (source 4978) and the double-sum split (source 5026-5027)

`HpASumS, HpASumX, HpASumLap, VsumSum, PsiAGradSum` (termwise derivatives of the lattice sums for
`s > 0`) and `TsumBilinSplit` (the split of `(v·∇)h + (h·∇)v`, `v = ΣV_k + (v - ΣV_k)`, into the
diagonal, `rCross` and `rTrain`).  `rPerSplit_of` (in `Split/Of.lean`) assembles `RPerSplit`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Per-center summands (source 4969-4977, 5024) -/

/-- The `j`-th summand of `f_A = -Σ_j[(B_mer x_j)·∇V_j + BV_j]` with the sign inside
(source 4969-4970), so `f_A = Σ_j fAj` (`fA_eq_tsum_fAj`). -/
def fAj (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ) (x : ℝ × ℝ) : Vec3 :=
  -(emb (fderiv ℝ (Vj ν s j) x (merApply (Bmat ν μ χ A s) (xj ν j x)))
      + mv (Bmat ν μ χ A s) (emb (Vj ν s j x)))

/-- The `j`-th summand of `e_A = Σ_j[2BV_j + 2νA^y:D²V_j - (A^y + (A^y)ᵀ)∇p_j]`
(source 4971-4972). -/
def eAj (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ) (x : ℝ × ℝ) : Vec3 :=
  (2 : ℝ) • mv (Bmat ν μ χ A s) (emb (Vj ν s j x))
    + (2 * ν) • hessContr (Ay ν χ A s) (Vj ν s j) x
    - mv (fun a b => Ay ν χ A s a b + Ay ν χ A s b a) (emb (mgrad (pj ν s j) x))

/-- The `j`-th summand `Ψ_j = (A^y_mer x_j)·∇p_j` of `Ψ_A` (source 5024). -/
def PsiAj (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ) (x : ℝ × ℝ) : ℝ :=
  (merApply (Ay ν χ A s) (xj ν j x)).1 * (mgrad (pj ν s j) x).1 +
    (merApply (Ay ν χ A s) (xj ν j x)).2 * (mgrad (pj ν s j) x).2

theorem fA_eq_tsum_fAj (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    fA ν μ χ A s x = ∑' j : ℤ, fAj ν μ χ A s j x := by
  unfold fA fAj
  rw [tsum_neg]

theorem fAj_eq_neg_fATerm (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    fAj ν μ χ A s j x = -fATerm ν μ χ A s x j := rfl

theorem eA_eq_tsum_eAj (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    eA ν μ χ A s x = ∑' j : ℤ, eAj ν μ χ A s j x := rfl

theorem eAj_eq_eATerm (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    eAj ν μ χ A s j x = eATerm ν μ χ A s x j := rfl

theorem PsiA_eq_tsum_PsiAj (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    PsiA ν χ A s x = ∑' j : ℤ, PsiAj ν χ A s j x := rfl

theorem hpA_eq_tsum_brk (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    hpA ν χ A s x = ∑' j : ℤ, brk ν χ A s j x := rfl

theorem vsum_eq_tsum (ν s : ℝ) (x : ℝ × ℝ) : vsum ν s x = ∑' k : ℤ, Vj ν s k x := rfl

/-! ## 2. Closed forms (source 4963-4973) -/

/-- `u·w` in the meridional plane. -/
def bkDot (u w : ℝ × ℝ) : ℝ := u.1 * w.1 + u.2 * w.2

/-- The Gaussian factor `G(a, y) = a⁻² e^{-|y|²/(4a)}` of `V_j = G(a, x_j) J x_j` (source 4963). -/
def bkG (a : ℝ) (y : ℝ × ℝ) : ℝ := (a ^ 2)⁻¹ * Real.exp (-(sq2 y) / (4 * a))

/-- The bracket profile: `b_j = G·bkP` with `bkP = MJy - JMy + (y·My)/(2a) Jy`. -/
def bkP (M : Mat3) (a : ℝ) (y : ℝ × ℝ) : ℝ × ℝ :=
  merApply M (Jrot y) - Jrot (merApply M y) + (bkDot y (merApply M y) / (2 * a)) • Jrot y

/-- `∂_w bkP` (the derivative of the polynomial `bkP` in `y`, direction `w`). -/
def bkPd (M : Mat3) (a : ℝ) (y w : ℝ × ℝ) : ℝ × ℝ :=
  merApply M (Jrot w) - Jrot (merApply M w)
    + ((bkDot w (merApply M y) + bkDot y (merApply M w)) / (2 * a)) • Jrot y
    + (bkDot y (merApply M y) / (2 * a)) • Jrot w

/-- `∂_u ∂_w bkP` (symmetric in `u, w`, independent of `y` up to the `Jy` factor). -/
def bkPdd (M : Mat3) (a : ℝ) (y u w : ℝ × ℝ) : ℝ × ℝ :=
  ((bkDot w (merApply M u) + bkDot u (merApply M w)) / (2 * a)) • Jrot y
    + ((bkDot w (merApply M y) + bkDot y (merApply M w)) / (2 * a)) • Jrot u
    + ((bkDot u (merApply M y) + bkDot y (merApply M u)) / (2 * a)) • Jrot w

/-- `Db_j[w] = G·bkD1` (first `x`-derivative of the bracket). -/
def bkD1 (M : Mat3) (a : ℝ) (y w : ℝ × ℝ) : ℝ × ℝ :=
  bkPd M a y w - (bkDot y w / (2 * a)) • bkP M a y

/-- `∂_u(Db_j[w]) = G·bkD2 M a y w u` (second `x`-derivative of the bracket). -/
def bkD2 (M : Mat3) (a : ℝ) (y w u : ℝ × ℝ) : ℝ × ℝ :=
  bkPdd M a y u w - (bkDot u w / (2 * a)) • bkP M a y - (bkDot y w / (2 * a)) • bkPd M a y u
    - (bkDot y u / (2 * a)) • bkD1 M a y w

/-- `∂_a(G·bkP)/G` at fixed `y, M`: `∂_s b_j = G·(bkP M' a y + ν·bkPa M a y)`. -/
def bkPa (M : Mat3) (a : ℝ) (y : ℝ × ℝ) : ℝ × ℝ :=
  (-2 / a + sq2 y / (4 * a ^ 2)) • bkP M a y - (bkDot y (merApply M y) / (2 * a ^ 2)) • Jrot y

/-- `DV_j[w] = G·bkV1` with `bkV1 = Jw - (y·w)/(2a) Jy`. -/
def bkV1 (a : ℝ) (y w : ℝ × ℝ) : ℝ × ℝ := Jrot w - (bkDot y w / (2 * a)) • Jrot y

/-- `∂_u(DV_j[w]) = G·bkV2 a y w u`. -/
def bkV2 (a : ℝ) (y w u : ℝ × ℝ) : ℝ × ℝ :=
  -(bkDot u w / (2 * a)) • Jrot y - (bkDot y w / (2 * a)) • Jrot u
    - (bkDot y u / (2 * a)) • bkV1 a y w

/-- The pressure-potential gradient profile: `∇Ψ_j = G²·bkPsi` with
`bkPsi = My + Mᵀy - (y·My)/a · y`. -/
def bkPsi (M : Mat3) (a : ℝ) (y : ℝ × ℝ) : ℝ × ℝ :=
  merApply M y + merApply (tr3 M) y - (bkDot y (merApply M y) / a) • y

/-- The Gaussian lattice majorant `(1 + |x_j|)⁶ e^{-|x_j|²/(4a)}` (source 4978). -/
def bkMaj (ν a : ℝ) (j : ℤ) (z : ℝ × ℝ) : ℝ :=
  (1 + ‖xj ν j z‖) ^ 6 * Real.exp (-(sq2 (xj ν j z)) / (4 * a))

theorem Vj_eq_bkG (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    Vj ν s j x = bkG (ageA ν s) (xj ν j x) • Jrot (xj ν j x) := rfl

/-! ## 3. Leaves: closed forms (source 4963-4973) -/

/-- **(L1)** `b_j = G·bkP` (source 4971-4973): `[V_j, W] = MV_j - DV_j[My]`, `DV_j[w] = G(Jw -
(y·w)/(2a)Jy)` (`gp_fderiv_Vj`). -/
def BrkClosed : Prop :=
  ∀ (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ) (x : ℝ × ℝ),
    brk ν χ A s j x = bkG (ageA ν s) (xj ν j x) • bkP (Ay ν χ A s) (ageA ν s) (xj ν j x)

/-- **(L2)** First `x`-derivative of the bracket (source 4973, 4978). -/
def BrkFDerivClosed : Prop :=
  ∀ (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ), 0 < ageA ν s →
    Differentiable ℝ (brk ν χ A s j) ∧
      ∀ x w : ℝ × ℝ, fderiv ℝ (brk ν χ A s j) x w =
        bkG (ageA ν s) (xj ν j x) • bkD1 (Ay ν χ A s) (ageA ν s) (xj ν j x) w

/-- **(L3)** Second `x`-derivative of the bracket (source 4973, 4978; needed for `Δb_j`). -/
def BrkSecondClosed : Prop :=
  ∀ (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ), 0 < ageA ν s → ∀ w : ℝ × ℝ,
    Differentiable ℝ (fun z => fderiv ℝ (brk ν χ A s j) z w) ∧
      ∀ x u : ℝ × ℝ, fderiv ℝ (fun z => fderiv ℝ (brk ν χ A s j) z w) x u =
        bkG (ageA ν s) (xj ν j x) • bkD2 (Ay ν χ A s) (ageA ν s) (xj ν j x) w u

/-- **(L4)** The `s`-derivative of the bracket at fixed `x` (source 4957-4958, 4963, 4973): with
`(A^y)'(s) = M'`, `∂_s b_j = G·(bkP M' + ν bkPa)` (`a = 1 + νs`, `∂_s = ν∂_a`). -/
def BrkDerivSClosed : Prop :=
  ∀ (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ) (x : ℝ × ℝ) (M' : Mat3),
    0 < ageA ν s → HasDerivAt (Ay ν χ A) M' s →
      HasDerivAt (fun s' => brk ν χ A s' j x)
        (bkG (ageA ν s) (xj ν j x) •
          (bkP M' (ageA ν s) (xj ν j x) + ν • bkPa (Ay ν χ A s) (ageA ν s) (xj ν j x))) s

/-- **(L5)** Second `x`-derivative of the Gaussian `V_j` (source 4963; enters `A^y:D²V_j` of
`e_A`, 4971). -/
def VjSecondClosed : Prop :=
  ∀ (ν s : ℝ) (j : ℤ), 0 < ageA ν s → ∀ w : ℝ × ℝ,
    Differentiable ℝ (fun z => fderiv ℝ (Vj ν s j) z w) ∧
      ∀ x u : ℝ × ℝ, fderiv ℝ (fun z => fderiv ℝ (Vj ν s j) z w) x u =
        bkG (ageA ν s) (xj ν j x) • bkV2 (ageA ν s) (xj ν j x) w u

/-- **(L6)** The gradient of `Ψ_j = (A^y_mer x_j)·∇p_j` (source 5024): with `∇p_j = G²x_j`,
`∇Ψ_j = G²((M + Mᵀ)x_j - (x_j·Mx_j)/a · x_j)`. -/
def MgradPsiAjClosed : Prop :=
  ∀ (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ), 0 < ageA ν s →
    Differentiable ℝ (PsiAj ν χ A s j) ∧
      ∀ x : ℝ × ℝ, mgrad (PsiAj ν χ A s j) x =
        bkG (ageA ν s) (xj ν j x) ^ 2 • bkPsi (Ay ν χ A s) (ageA ν s) (xj ν j x)

/-! ## 4. The single-center identity (source 5022-5025, 2040-2051) -/

/-- **Single-center bracket identity** (source 5022-5025, "the Cartesian bracket calculation, with
the full matrix retained").  With `V_j = J∇ψ_j`, `W_j = A^y_mer x_j` (`DW_j = A^y_mer`),
`b_j = [V_j, W_j]` and `B = (A^y)' + μA^y/s`:
`(∂_s + μ/s - νΔ)b_j + (V_j·∇)b_j + (b_j·∇)V_j = (f_A)_j + (e_A)_j + ∇Ψ_j` (meridional parts),
because the single Gaussian solves `∂_sV_j - νΔV_j + V_j·∇V_j + ∇p_j = 0` (source 2040-2051) and
`L[V,W] = BV - (Bx·∇)V + 2νA^y:D²V - (A^y + (A^y)ᵀ)∇p + ∇((A^y x)·∇p)`.  Only `A^y`
differentiable at `s` is used (no trace or symmetry condition). -/
def BrkIdentity : Prop :=
  ∀ (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ) (x : ℝ × ℝ), 0 < ν → 0 < s →
    DifferentiableAt ℝ (Ay ν χ A) s →
      deriv (fun s' => brk ν χ A s' j x) s + (μ / s) • brk ν χ A s j x
          - ν • lapPl (brk ν χ A s j) x
          + fderiv ℝ (brk ν χ A s j) x (Vj ν s j x) + fderiv ℝ (Vj ν s j) x (brk ν χ A s j x) =
        merPl (fAj ν μ χ A s j x) + merPl (eAj ν μ χ A s j x) + mgrad (PsiAj ν χ A s j) x

/-! ## 5. Leaves: Gaussian bounds and the tsum calculus (source 4978) -/

/-- **(G0)** The lattice majorant is summable in `j` (`c = ν⁻² > 0`, source 4963, 4978). -/
def BkMajSummable : Prop :=
  ∀ (ν a : ℝ) (x : ℝ × ℝ), 0 < ν → 0 < a → Summable (fun j : ℤ => bkMaj ν a j x)

/-- **(G1)** Termwise differentiation of a Gaussian lattice sum (source 4978): if every term and its
derivative are bounded by `K·bkMaj`, the sum is differentiable with the termwise derivative, and
both series converge absolutely. -/
def LatticeFDerivSum : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ν a K : ℝ) (f : ℤ → ℝ × ℝ → E), 0 < ν → 1 ≤ a → (∀ j, Differentiable ℝ (f j)) →
    (∀ (j : ℤ) (z : ℝ × ℝ), ‖f j z‖ ≤ K * bkMaj ν a j z) →
    (∀ (j : ℤ) (z : ℝ × ℝ), ‖fderiv ℝ (f j) z‖ ≤ K * bkMaj ν a j z) →
    ∀ x : ℝ × ℝ, HasFDerivAt (fun z => ∑' j : ℤ, f j z) (∑' j : ℤ, fderiv ℝ (f j) x) x ∧
      Summable (fun j : ℤ => ‖fderiv ℝ (f j) x‖) ∧ Summable (fun j : ℤ => ‖f j x‖)

/-- **(B1)** Gaussian bound of the bracket and its first derivative (source 4973, 4978). -/
def BrkGaussBound1 : Prop :=
  ∀ (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ), 0 < ν → 0 < s → ∃ K : ℝ,
    ∀ (j : ℤ) (z : ℝ × ℝ), ‖brk ν χ A s j z‖ ≤ K * bkMaj ν (ageA ν s) j z ∧
      ‖fderiv ℝ (brk ν χ A s j) z‖ ≤ K * bkMaj ν (ageA ν s) j z

/-- **(B2)** Gaussian bound of the second derivatives of the bracket (source 4973, 4978). -/
def BrkGaussBound2 : Prop :=
  ∀ (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ), 0 < ν → 0 < s → ∃ K : ℝ,
    ∀ (j : ℤ) (z : ℝ × ℝ) (b : Fin 2),
      ‖fderiv ℝ (fun z' => fderiv ℝ (brk ν χ A s j) z' (ei b)) z‖ ≤ K * bkMaj ν (ageA ν s) j z

/-- **(B3)** Gaussian bound of `V_j` and its first derivative (source 4963, 4978). -/
def VjGaussBound : Prop :=
  ∀ ν s : ℝ, 0 < ν → 0 < s → ∃ K : ℝ,
    ∀ (k : ℤ) (z : ℝ × ℝ), ‖Vj ν s k z‖ ≤ K * bkMaj ν (ageA ν s) k z ∧
      ‖fderiv ℝ (Vj ν s k) z‖ ≤ K * bkMaj ν (ageA ν s) k z

/-- **(B4)** Gaussian bound of `Ψ_j` and its first derivative (source 4964, 5024, 4978). -/
def PsiAjGaussBound : Prop :=
  ∀ (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ), 0 < ν → 0 < s → ∃ K : ℝ,
    ∀ (j : ℤ) (z : ℝ × ℝ), ‖PsiAj ν χ A s j z‖ ≤ K * bkMaj ν (ageA ν s) j z ∧
      ‖fderiv ℝ (PsiAj ν χ A s j) z‖ ≤ K * bkMaj ν (ageA ν s) j z

/-- **(T1)** `x`-derivative of `h^p_A` termwise (source 4978). -/
def HpASumX : Prop :=
  ∀ (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ), 0 < ν → 0 < s → ∀ x : ℝ × ℝ,
    HasFDerivAt (hpA ν χ A s) (∑' j : ℤ, fderiv ℝ (brk ν χ A s j) x) x ∧
      Summable (fun j : ℤ => ‖fderiv ℝ (brk ν χ A s j) x‖) ∧
      Summable (fun j : ℤ => ‖brk ν χ A s j x‖)

/-- **(T2)** `Δh^p_A = Σ_jΔb_j` (source 4978). -/
def HpASumLap : Prop :=
  ∀ (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ), 0 < ν → 0 < s → ∀ x : ℝ × ℝ,
    HasSum (fun j : ℤ => lapPl (brk ν χ A s j) x) (lapPl (hpA ν χ A s) x)

/-- **(T3)** `∂_sh^p_A = Σ_j∂_sb_j` at `s > 0` for `A ∈ 𝒜` (source 4978, 4741-4745: `A^y` is `C¹`
on `(0,∞)`, so `A^y, (A^y)'` are bounded near `s`). -/
def HpASumS (as : ℝ) (χ : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χ → ∀ ν : ℝ, 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A → ∀ s : ℝ, 0 < s →
    ∀ x : ℝ × ℝ,
      HasSum (fun j : ℤ => deriv (fun s' => brk ν χ A s' j x) s) (deriv (fun s' => hpA ν χ A s' x) s)

/-- **(T4)** The Gaussian train `Σ_kV_k` is differentiable termwise (source 4963, 4978). -/
def VsumSum : Prop :=
  ∀ ν s : ℝ, 0 < ν → 0 < s → ∀ x : ℝ × ℝ,
    HasFDerivAt (vsum ν s) (∑' k : ℤ, fderiv ℝ (Vj ν s k) x) x ∧
      Summable (fun k : ℤ => ‖fderiv ℝ (Vj ν s k) x‖) ∧ Summable (fun k : ℤ => ‖Vj ν s k x‖)

/-- **(T5)** `∇Ψ_A = Σ_j∇Ψ_j` (source 5024, 4978). -/
def PsiAGradSum : Prop :=
  ∀ (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ), 0 < ν → 0 < s → ∀ x : ℝ × ℝ,
    HasSum (fun j : ℤ => mgrad (PsiAj ν χ A s j) x) (mgrad (PsiA ν χ A s) x)

/-- **(D)** The split of the convection products into diagonal and distinct-center terms (source
5026-5027): for absolutely summable `b_j, V_k` and derivative families `Db_j, DV_k`,
`(ΣDb_j)(ΣV_k) + (ΣDV_k)(Σb_j) = Σ_j(Db_jV_j + DV_jb_j) + Σ_jΣ_{k≠j}(Db_jV_k + DV_kb_j)`. -/
def TsumBilinSplit : Prop :=
  ∀ (b V : ℤ → ℝ × ℝ) (Db DV : ℤ → (ℝ × ℝ →L[ℝ] ℝ × ℝ)),
    Summable (fun j => ‖b j‖) → Summable (fun k => ‖V k‖) →
    Summable (fun j => ‖Db j‖) → Summable (fun k => ‖DV k‖) →
      HasSum (fun j => Db j (V j) + DV j (b j))
        ((∑' j, Db j) (∑' k, V k) + (∑' k, DV k) (∑' j, b j) -
          ∑' j, ∑' k, if k = j then 0 else (Db j (V k) + DV k (b j)))

end UnforcedLeray.Short.PartIIIb.Concrete
