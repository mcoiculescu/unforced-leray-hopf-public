import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4

/-!
# `PartIII-b:C/grad/3/4/1`: `GradEnvelope` from lattice-derivative envelopes

Source `the November 2 reference manuscript`
4963-4980, 5036-5039, 5063-5079.  `ĥ_A = √s [b_r e_r + b_z e_z]`,
`b_r = (h^p_A)_r`, `b_z = (h^p_A)_z + ε(ψ^p_A − 𝒦ψ^p_A)` (4980); the entries of `s⁻¹∇ĥ_A` are
`∂_q b, ∂_η b, −ε(𝒦+1)b` and `ε b_r` (5036-5039), so only `(h^p_A)_{r,z}`, `ψ^p_A` and their
derivatives `∂_q, ∂_η, 𝒦` (once for `h^p`, up to `𝒦²` and `∂𝒦` for `ψ^p`) enter.

Fixed lattice envelope: rate `gradAlpha = 1/9` (the terms are Gaussian of rate `≥ 1/(4a)`,
`a ≤ 2.1`, so `1/8.4 > 1/9`) and polynomial degree `gradK = 12` (actual degree `≤ 6`).

Proved: `gradEnvelope_of` (from the entrywise envelope `GradEntryEnvelope`).
Leaves: `GradLatticeHp`, `GradLatticePsi`, `GradLatticeSmooth`, and the chain-rule step
`gradEntryEnvelope_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Fixed Gaussian rate of the lattice envelope. -/
def gradAlpha : ℝ := 1 / 9

/-- Fixed polynomial degree of the lattice envelope. -/
def gradK : ℕ := 12

/-- The `A^y`-weight `|A^y| + |s∂_sA^y| + |(s∂_s)²A^y|` of the envelope. -/
def gradF (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) : ℝ :=
  frob (Ay ν χf A s) + frob (sDeriv (Ay ν χf A) s) + frob (sDeriv (sDeriv (Ay ν χf A)) s)

/-- `(h^p_A)_r` as a function of `(s, x)`. -/
def hpR (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) : ℝ := (hpA ν χ A s x).1

/-- `(h^p_A)_z` as a function of `(s, x)`. -/
def hpZ (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) : ℝ := (hpA ν χ A s x).2

/-- Common hypotheses of the lattice-derivative envelopes. -/
def GradData (ν s : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : Prop :=
  0 < ν ∧ ν ≤ 1 ∧ 0 < s ∧ s ≤ (11 / 10) / ν ∧ ContDiffAt ℝ 2 (Ay ν χf A) s

/-- Envelope for `(h^p_A)_r, (h^p_A)_z` and their `∂_q, ∂_η, 𝒦` derivatives (source 4973,
5063-5079: termwise, `V_j` Gaussian in `x − jc`, `[V_j, A x_j]` of polynomial degree `≤ 3`,
one `𝒦` adds degree `≤ 2`). -/
def GradLatticeHp : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν s : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3), GradData ν s χf A →
    ∀ x : ℝ × ℝ, ∀ u : ℝ → ℝ × ℝ → ℝ, (u = hpR ν χf A ∨ u = hpZ ν χf A) →
      |u s x| ≤ C * gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x ∧
      |dQ u s x| ≤ C * gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x ∧
      |dEta u s x| ≤ C * gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x ∧
      |Kop u s x| ≤ C * gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x

/-- Envelope for `ψ^p_A` and `∂_q, ∂_η, 𝒦, ∂_q𝒦, ∂_η𝒦, 𝒦²` of it (source 4974-4975, 5063-5079). -/
def GradLatticePsi : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν s : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3), GradData ν s χf A →
    ∀ x : ℝ × ℝ,
      |psipA ν χf A s x| ≤ C * gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x ∧
      |dQ (psipA ν χf A) s x| ≤ C * gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x ∧
      |dEta (psipA ν χf A) s x| ≤ C * gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x ∧
      |Kop (psipA ν χf A) s x| ≤ C * gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x ∧
      |dQ (fun s' y => Kop (psipA ν χf A) s' y) s x| ≤
        C * gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x ∧
      |dEta (fun s' y => Kop (psipA ν χf A) s' y) s x| ≤
        C * gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x ∧
      |Kop (fun s' y => Kop (psipA ν χf A) s' y) s x| ≤
        C * gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x

/-- Differentiability needed for the chain rule (sums and products of the above): `h^p_{r,z}`,
`ψ^p_A` and `𝒦ψ^p_A` are differentiable in `x` at fixed `s` and in `s` at fixed `x`
(termwise differentiation of the lattice sums, `s > 0`, `A^y` `C²` at `s`). -/
def GradLatticeSmooth : Prop :=
  ∀ (ν s : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3), GradData ν s χf A → ∀ x : ℝ × ℝ,
    ∀ u : ℝ → ℝ × ℝ → ℝ, (u = hpR ν χf A ∨ u = hpZ ν χf A ∨ u = psipA ν χf A ∨
        u = fun s' y => Kop (psipA ν χf A) s' y) →
      DifferentiableAt ℝ (u s) x ∧ DifferentiableAt ℝ (fun s' => u s' x) s

/-- Entrywise envelope of `s⁻¹∇ĥ_A` (source 5036-5039, 5063-5079). -/
def GradEntryEnvelope : Prop :=
  ∃ (C : ℝ), 0 ≤ C ∧
    ∀ (ν ε s : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3), GradData ν s χf A → 0 < ε → ε ≤ 1 →
      ∀ (x : ℝ × ℝ) (i j : Fin 3),
        |s⁻¹ * physGradA ν ε χf A s x i j| ≤
          C * gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x

/-- Chain rule: the entries of `s⁻¹∇ĥ_A` are `∂_q b, ∂_η b, −ε(𝒦+1)b, ε b_r` for
`b_r = h^p_r`, `b_z = h^p_z + ε(ψ^p − 𝒦ψ^p)`, `ĥ_A = √s b` (`𝒦(√s b) = √s(𝒦b + b)`). -/
def GradEntryChain : Prop :=
  GradLatticeHp → GradLatticePsi → GradLatticeSmooth → GradEntryEnvelope

theorem gradEnvelope_of (h : GradEntryEnvelope) : GradEnvelope := by
  obtain ⟨C, hC, hE⟩ := h
  refine ⟨9 * C, gradAlpha, gradK, by positivity, by norm_num [gradAlpha], ?_⟩
  intro ν ε s hν hν1 hε hε1 hs hsT χf A hA x
  have hd : GradData ν s χf A := ⟨hν, hν1, hs, hsT, hA⟩
  have hS : 0 ≤ C * gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x := by
    have h0 := hE ν ε s χf A hd hε hε1 x 0 0
    exact le_trans (abs_nonneg _) h0
  set B := C * gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x with hB
  have hent : ∀ i j : Fin 3, |(gradAcoef ν ε χf A (s, x)) (i, j)| ≤ B := by
    intro i j
    have := hE ν ε s χf A hd hε hε1 x i j
    simpa [gradAcoef, matTen] using this
  have hsq : ‖gradAcoef ν ε χf A (s, x)‖ ≤ 3 * B := by
    rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [Fintype.sum_prod_type]
    have : ∀ i j : Fin 3, ‖(gradAcoef ν ε χf A (s, x)) (i, j)‖ ^ 2 ≤ B ^ 2 := by
      intro i j
      rw [Real.norm_eq_abs, sq_abs]
      have h2 := abs_le.mp (hent i j)
      exact sq_le_sq' h2.1 h2.2
    calc ∑ i : Fin 3, ∑ j : Fin 3, ‖(gradAcoef ν ε χf A (s, x)) (i, j)‖ ^ 2
        ≤ ∑ i : Fin 3, ∑ j : Fin 3, B ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => this i j
      _ = (3 * B) ^ 2 := by simp; ring
  calc ‖gradAcoef ν ε χf A (s, x)‖ ≤ 3 * B := hsq
    _ ≤ 9 * C * (frob (Ay ν χf A s) + frob (sDeriv (Ay ν χf A) s) +
          frob (sDeriv (sDeriv (Ay ν χf A)) s)) * latticeS gradAlpha gradK (cOf ν) x := by
        have : B = C * gradF ν χf A s * latticeS gradAlpha gradK (cOf ν) x := rfl
        unfold gradF at this
        nlinarith [hS, this]

end UnforcedLeray.Short.PartIIIb.Concrete
