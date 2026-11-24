import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1.Decomp
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic

/-!
# `PartIII-b:C/grad/3/4/1/2/1`: termwise envelope of `ψ^p_A` under the seven operators

Source `the November 2 reference manuscript`
4963-4980 (`ψ_j`, `ψ^p_A`), 5036-5039 (`∂_q, ∂_η, 𝒦`), 5063-5079 (termwise Gaussian bounds).

Architecture.  The Gaussian kernels `a^{-m} u^p η^q e^{-(u²+η²)/(4a)}` (`a = 1+νs`,
`u = q - jc`) are encoded by lists of monomials (`GExpr`), evaluated by `gEval`.  A `GCombo` is a
function equal (for `s'` near `s`) to `Σ_{r,a,b} (s∂_s)^r A^y_{ab}(s') · gEval(e r a b)(s', y)`,
and `GLevel L` says only `r ≤ L` occur.  The leaves below (`GDomProp` ... `GKopProp`) are the
five facts about kernels; `gradPsiTermEnv_of` assembles them into `GradPsiTermEnv`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Finite kernel expressions: a list of monomials `(c, m, p, q)` standing for
`c · a^{-m} u^p η^q e^{-(u²+η²)/(4a)}`. -/
abbrev GExpr := List (ℝ × ℕ × ℕ × ℕ)

/-- One monomial at `(s, x)`, `a = 1+νs`, `u = x₁ - jc`, `η = x₂`. -/
def gMon (ν : ℝ) (j : ℤ) (t : ℝ × ℕ × ℕ × ℕ) (s : ℝ) (x : ℝ × ℝ) : ℝ :=
  t.1 * (ageA ν s)⁻¹ ^ t.2.1 * (x.1 - (j : ℝ) * cOf ν) ^ t.2.2.1 * x.2 ^ t.2.2.2 *
    Real.exp (-((x.1 - (j : ℝ) * cOf ν) ^ 2 + x.2 ^ 2) / (4 * ageA ν s))

/-- Evaluation of a kernel expression, as a function of `(s, x)`. -/
def gEval (e : GExpr) (ν : ℝ) (j : ℤ) : ℝ → ℝ × ℝ → ℝ :=
  fun s x => (e.map fun t => gMon ν j t s x).sum

/-- The coefficient matrices `A^y, s∂_sA^y, (s∂_s)²A^y`. -/
def gCoef (Ay : ℝ → Mat3) : Fin 3 → ℝ → Mat3 :=
  ![Ay, sDeriv Ay, sDeriv (sDeriv Ay)]

/-- `Σ_{r,a,b} (s∂_s)^r A_{mi a, mi b}(s) · gEval(e r a b)(s, x)`. -/
def GSum (e : Fin 3 → Fin 2 → Fin 2 → GExpr) (ν : ℝ) (j : ℤ) (Ay : ℝ → Mat3) (s : ℝ)
    (x : ℝ × ℝ) : ℝ :=
  ∑ r : Fin 3, ∑ a : Fin 2, ∑ b : Fin 2,
    gCoef Ay r s (mi a) (mi b) * gEval (e r a b) ν j s x

/-- Only the coefficient levels `r ≤ L` occur in `e`. -/
def GLevel (L : ℕ) (e : Fin 3 → Fin 2 → Fin 2 → GExpr) : Prop :=
  ∀ r : Fin 3, L < r.val → ∀ a b, e r a b = []

/-- `F` equals `GSum e` for `s'` near `s` (all `y`). -/
def GCombo (e : Fin 3 → Fin 2 → Fin 2 → GExpr) (ν : ℝ) (j : ℤ) (Ay : ℝ → Mat3) (s : ℝ)
    (F : ℝ → ℝ × ℝ → ℝ) : Prop :=
  ∀ᶠ s' in 𝓝 s, ∀ y, F s' y = GSum e ν j Ay s' y

/-- Leaf 1 (domination, source 5063-5079): every kernel expression is `≤ C · latticeW` uniformly
for `0 < ν ≤ 1`, `0 < s`, `νs ≤ 1.1` (so `a ≤ 2.1`, Gaussian rate `1/(4a) ≥ 1/8.4 > 1/9`). -/
def GDomProp : Prop :=
  ∀ e : GExpr, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ),
    0 < ν → ν ≤ 1 → 0 < s → ν * s ≤ 11 / 10 →
      |gEval e ν j s x| ≤ C * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2

/-- Leaf 2 (bound of a `GSum`): coefficient entries are `≤ gradF`. -/
def GBoundProp : Prop :=
  ∀ e : Fin 3 → Fin 2 → Fin 2 → GExpr, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ) (s : ℝ) (x : ℝ × ℝ),
      0 < ν → ν ≤ 1 → 0 < s → ν * s ≤ 11 / 10 →
        |GSum e ν j (Ay ν χf A) s x| ≤ C * gradF ν χf A s * gradW ν x j

/-- Leaf 3 (decomposition of `ψ^p_A` terms, source 4974-4975):
`ψ^p_A`-term `= Σ_{ab} A^y_{ab}(s) λ_{ab,j}`, `λ_{ab,j} = [a=b]ψ_j - (x_j)_b ∂_a ψ_j`. -/
def GPsiProp : Prop :=
  ∃ e : Fin 3 → Fin 2 → Fin 2 → GExpr, GLevel 0 e ∧
    ∀ (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ), 0 < ν → ∀ s : ℝ, 0 < s →
      GCombo e ν j (Ay ν χf A) s (gradPsiTm ν χf A j)

/-- Leaf 4 (`∂_q`, `∂_η` of a `GCombo`, at the point `s`). -/
def GDqProp : Prop :=
  ∀ (L : ℕ) (e : Fin 3 → Fin 2 → Fin 2 → GExpr), GLevel L e →
    ∃ e' : Fin 3 → Fin 2 → Fin 2 → GExpr, GLevel L e' ∧
      ∀ (ν : ℝ) (j : ℤ) (Ay : ℝ → Mat3) (s : ℝ) (F : ℝ → ℝ × ℝ → ℝ), 0 < ν → 0 < s →
        GCombo e ν j Ay s F → ∀ x, dQ F s x = GSum e' ν j Ay s x

def GDetaProp : Prop :=
  ∀ (L : ℕ) (e : Fin 3 → Fin 2 → Fin 2 → GExpr), GLevel L e →
    ∃ e' : Fin 3 → Fin 2 → Fin 2 → GExpr, GLevel L e' ∧
      ∀ (ν : ℝ) (j : ℤ) (Ay : ℝ → Mat3) (s : ℝ) (F : ℝ → ℝ × ℝ → ℝ), 0 < ν → 0 < s →
        GCombo e ν j Ay s F → ∀ x, dEta F s x = GSum e' ν j Ay s x

/-- Leaf 5 (`𝒦 = η∂_η + 2s∂_s` raises the level by one; `Ay` is `C²` at `s`; Leibniz in `s`). -/
def GKopProp : Prop :=
  ∀ (L : ℕ), L ≤ 1 → ∀ (e : Fin 3 → Fin 2 → Fin 2 → GExpr), GLevel L e →
    ∃ e' : Fin 3 → Fin 2 → Fin 2 → GExpr, GLevel (L + 1) e' ∧
      ∀ (ν : ℝ) (j : ℤ) (Ay : ℝ → Mat3) (s : ℝ) (F : ℝ → ℝ × ℝ → ℝ), 0 < ν → 0 < s →
        ContDiffAt ℝ 2 Ay s → GCombo e ν j Ay s F →
          GCombo e' ν j Ay s (fun s' y => Kop F s' y)

/-- Kernel leaf: `∂_q` of a kernel expression is a kernel expression (`ei 0` direction). -/
def GKerDqProp : Prop :=
  ∀ e : GExpr, ∃ e' : GExpr, ∀ (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ), 0 < ν → 0 < s →
    DifferentiableAt ℝ (gEval e ν j s) x ∧ fderiv ℝ (gEval e ν j s) x (ei 0) = gEval e' ν j s x

/-- Kernel leaf: `∂_η` of a kernel expression (`ei 1` direction). -/
def GKerDetaProp : Prop :=
  ∀ e : GExpr, ∃ e' : GExpr, ∀ (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ), 0 < ν → 0 < s →
    DifferentiableAt ℝ (gEval e ν j s) x ∧ fderiv ℝ (gEval e ν j s) x (ei 1) = gEval e' ν j s x

/-- Kernel leaf: `s∂_s` of a kernel expression (`s ∂_s a = a - 1`). -/
def GKerSProp : Prop :=
  ∀ e : GExpr, ∃ e' : GExpr, ∀ (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ), 0 < ν → 0 < s →
    HasDerivAt (fun t => gEval e ν j t x) (gEval e' ν j s x / s) s

/-- Kernel leaf: multiplication by `u = q - jc` and by `η` stays in the class. -/
def GKerMulProp : Prop :=
  ∀ e : GExpr,
    (∃ e' : GExpr, ∀ (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ),
      (x.1 - (j : ℝ) * cOf ν) * gEval e ν j s x = gEval e' ν j s x) ∧
    (∃ e' : GExpr, ∀ (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ),
      x.2 * gEval e ν j s x = gEval e' ν j s x)

/-- Kernel leaf: `𝒦 = η∂_η + 2s∂_s` of a kernel expression (from `GKerDeta`, `GKerS`,
`GKerMul`). -/
def GKerKopProp : Prop :=
  ∀ e : GExpr, ∃ e' : GExpr, ∀ (ν : ℝ) (j : ℤ) (s : ℝ) (x : ℝ × ℝ), 0 < ν → 0 < s →
    Kop (gEval e ν j) s x = gEval e' ν j s x

/-- Coefficient leaf: `s ∂_s` of the entries of `Ay` and of `sDeriv Ay` when `Ay` is `C²` at `s`. -/
def GCoefProp : Prop :=
  ∀ (Ay : ℝ → Mat3) (s : ℝ), 0 < s → ContDiffAt ℝ 2 Ay s → ∀ i j : Fin 3,
    HasDerivAt (fun t => Ay t i j) (sDeriv Ay s i j / s) s ∧
    HasDerivAt (fun t => sDeriv Ay t i j) (sDeriv (sDeriv Ay) s i j / s) s

theorem gCombo_self {e : Fin 3 → Fin 2 → Fin 2 → GExpr} {ν : ℝ} {j : ℤ} {Ay : ℝ → Mat3}
    {s : ℝ} {F : ℝ → ℝ × ℝ → ℝ} (h : GCombo e ν j Ay s F) (x : ℝ × ℝ) :
    F s x = GSum e ν j Ay s x :=
  (Filter.Eventually.self_of_nhds h) x

theorem gradW_nonneg (ν : ℝ) (x : ℝ × ℝ) (j : ℤ) : 0 ≤ gradW ν x j := by
  unfold gradW latticeW; positivity

theorem gradPsiTermEnv_of (hB : GBoundProp) (hP : GPsiProp) (hQ : GDqProp) (hE : GDetaProp)
    (hK : GKopProp) : GradPsiTermEnv := by
  obtain ⟨e0, hl0, hψ⟩ := hP
  obtain ⟨e0q, hl0q, hq0⟩ := hQ 0 e0 hl0
  obtain ⟨e0e, hl0e, he0⟩ := hE 0 e0 hl0
  obtain ⟨e1, hl1, hk1⟩ := hK 0 (by norm_num) e0 hl0
  obtain ⟨e1q, hl1q, hq1⟩ := hQ 1 e1 hl1
  obtain ⟨e1e, hl1e, he1⟩ := hE 1 e1 hl1
  obtain ⟨e2, hl2, hk2⟩ := hK 1 le_rfl e1 hl1
  obtain ⟨C0, h0, b0⟩ := hB e0
  obtain ⟨C1, h1, b1⟩ := hB e0q
  obtain ⟨C2, h2, b2⟩ := hB e0e
  obtain ⟨C3, h3, b3⟩ := hB e1
  obtain ⟨C4, h4, b4⟩ := hB e1q
  obtain ⟨C5, h5, b5⟩ := hB e1e
  obtain ⟨C6, h6, b6⟩ := hB e2
  refine ⟨C0 + C1 + C2 + C3 + C4 + C5 + C6, by positivity, ?_⟩
  intro ν s χf A hd x m j
  obtain ⟨hν, hν1, hs, hsb, hC2⟩ := hd
  have hνs : ν * s ≤ 11 / 10 := by
    rw [le_div_iff₀ hν] at hsb; linarith
  have hFW : 0 ≤ gradF ν χf A s * gradW ν x j :=
    mul_nonneg (gradF_nonneg _ _ _ _) (gradW_nonneg _ _ _)
  have hF0 := hψ ν χf A j hν s hs
  have up : ∀ {v C' : ℝ}, 0 ≤ C' → C' ≤ C0 + C1 + C2 + C3 + C4 + C5 + C6 →
      |v| ≤ C' * gradF ν χf A s * gradW ν x j →
      |v| ≤ (C0 + C1 + C2 + C3 + C4 + C5 + C6) * gradF ν χf A s * gradW ν x j := by
    intro v C' hC' hle hv
    refine hv.trans ?_
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hle hFW
  have hK1 := hk1 ν j _ s _ hν hs hC2 hF0
  have hK2 := hk2 ν j _ s _ hν hs hC2 hK1
  have hC0 : C0 ≤ C0 + C1 + C2 + C3 + C4 + C5 + C6 := by linarith
  fin_cases m
  · show |gradPsiTm ν χf A j s x| ≤ _
    rw [gCombo_self hF0 x]
    exact up h0 (by linarith) (b0 ν χf A j s x hν hν1 hs hνs)
  · show |dQ (gradPsiTm ν χf A j) s x| ≤ _
    rw [hq0 ν j _ s _ hν hs hF0 x]
    exact up h1 (by linarith) (b1 ν χf A j s x hν hν1 hs hνs)
  · show |dEta (gradPsiTm ν χf A j) s x| ≤ _
    rw [he0 ν j _ s _ hν hs hF0 x]
    exact up h2 (by linarith) (b2 ν χf A j s x hν hν1 hs hνs)
  · show |Kop (gradPsiTm ν χf A j) s x| ≤ _
    rw [show Kop (gradPsiTm ν χf A j) s x = GSum e1 ν j (Ay ν χf A) s x from
      gCombo_self hK1 x]
    exact up h3 (by linarith) (b3 ν χf A j s x hν hν1 hs hνs)
  · show |dQ (fun s' y => Kop (gradPsiTm ν χf A j) s' y) s x| ≤ _
    rw [hq1 ν j _ s _ hν hs hK1 x]
    exact up h4 (by linarith) (b4 ν χf A j s x hν hν1 hs hνs)
  · show |dEta (fun s' y => Kop (gradPsiTm ν χf A j) s' y) s x| ≤ _
    rw [he1 ν j _ s _ hν hs hK1 x]
    exact up h5 (by linarith) (b5 ν χf A j s x hν hν1 hs hνs)
  · show |Kop (fun s' y => Kop (gradPsiTm ν χf A j) s' y) s x| ≤ _
    rw [show Kop (fun s' y => Kop (gradPsiTm ν χf A j) s' y) s x
      = GSum e2 ν j (Ay ν χf A) s x from gCombo_self hK2 x]
    exact up h6 (by linarith) (b6 ν χf A j s x hν hν1 hs hνs)

end UnforcedLeray.Short.PartIIIb.Concrete
