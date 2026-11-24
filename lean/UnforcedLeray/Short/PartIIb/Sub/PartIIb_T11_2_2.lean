import UnforcedLeray.Short.PartIIb.Sub.T11_2

/-!
# Part II-b, leaf `PartII-b:T11/2/2` (`DualFTestZero`): decomposition into five leaves

Source: `the November 2 reference manuscript` 1923-1927 (flat equation) and the
proof sketch in `Sub/T11.lean` / `Sub/T11_2.lean`.

Complex test `ψ_∞(σ,q,η) = σ^{μ-1} χ(σ) H(s-σ,q,η)`, `ψ_L = φ(η/L) ψ_∞`.  `FlatEqCellStream`
applied to `Re ψ_L`, `Im ψ_L` gives `∫ b · T(∇^⊥ψ_L) = 0`.  With
`Rem_L = T(∇^⊥ψ_L) - φ_L T(∇^⊥ψ_∞)` and `T(∇^⊥ψ_∞) = -σ^μ χ'(σ) ∇^⊥ g` (heat equation) the
pairing splits into a main term (limit `-∫χ' F`) and a remainder (limit `0`).

Leaves: `DualTestAdmissible` (`/1`), `DualTestEq` (`/2`), `DualHeatIdentity` (`/3`),
`DualRemainderLimit` (`/4`), `DualMainLimit` (`/5`).  Proved here: `dualFTestZero_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Partial derivative `∂_j ψ` (`j = 0,1,2` for `s,q,η`) of a complex-valued function. -/
def cpdC (j : Fin 3) (ψ : Coord → ℂ) (x : Coord) : ℂ := fderiv ℝ ψ x (cdir j)

/-- `∇^⊥ψ = (∂_ηψ, -∂_qψ)` for complex `ψ` on the chart. -/
def perpC (ψ : Coord → ℂ) (x : Coord) : Fin 2 → ℂ := ![cpdC 2 ψ x, -cpdC 1 ψ x]

/-- Complexification of `flatTranspose`: `(μ-1)Ψ - sΨ_s - νsΔ_{q,η}Ψ`. -/
def flatTransposeC (ν : ℝ) (μ : ℂ) (Ψ : Coord → Fin 2 → ℂ) (x : Coord) (i : Fin 2) : ℂ :=
  (μ - 1) * Ψ x i - (x.1 : ℂ) * cpdC 0 (fun y => Ψ y i) x -
    (ν : ℂ) * (x.1 : ℂ) * (cpdC 1 (fun y => cpdC 1 (fun z => Ψ z i) y) x +
      cpdC 2 (fun y => cpdC 2 (fun z => Ψ z i) y) x)

/-- The pairing `Σ_i b_i V_i`. -/
def pairC (b : CProf) (V : Coord → Fin 2 → ℂ) (x : Coord) : ℂ := ∑ i : Fin 2, b x i * V x i

/-- `ψ_∞(σ,q,η) = σ^{μ-1} χ(σ) H(s-σ,q,η)`. -/
def dualPsiInf (μ : ℂ) (χ : ℝ → ℝ) (H : Coord → ℝ) (s : ℝ) (x : Coord) : ℂ :=
  ((x.1 : ℂ) ^ (μ - 1)) * (χ x.1 : ℂ) * (H (s - x.1, x.2) : ℂ)

/-- `ψ_L = φ(η/L) ψ_∞`. -/
def dualPsi (μ : ℂ) (χ φ : ℝ → ℝ) (H : Coord → ℝ) (s : ℝ) (L : ℝ) (x : Coord) : ℂ :=
  (φ (x.2.2 / L) : ℂ) * dualPsiInf μ χ H s x

/-- `Rem_L = T(∇^⊥ψ_L) - φ_L · T(∇^⊥ψ_∞)`. -/
def dualRem (ν : ℝ) (μ : ℂ) (χ φ : ℝ → ℝ) (H : Coord → ℝ) (s L : ℝ) (x : Coord) :
    Fin 2 → ℂ := fun i =>
  flatTransposeC ν μ (perpC (dualPsi μ χ φ H s L)) x i -
    (φ (x.2.2 / L) : ℂ) * flatTransposeC ν μ (perpC (dualPsiInf μ χ H s)) x i

/-- The main-term field `φ_L · (-σ^μ χ'(σ) ∇^⊥g)`, `g(σ,·) = H(s-σ,·)`. -/
def dualMain (μ : ℂ) (χ φ : ℝ → ℝ) (H : Coord → ℝ) (s L : ℝ) (y : Coord) : Fin 2 → ℂ :=
  fun i => (φ (y.2.2 / L) : ℂ) *
    (-(((y.1 : ℂ) ^ μ) * ((deriv χ y.1 : ℝ) : ℂ) * perpC (fun z => (H (s - z.1, z.2) : ℂ)) y i))

/-- Admissible cutoffs `χ ∈ C_c^∞(0,s)`. -/
def DFChi (s : ℝ) (χ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ioo (0 : ℝ) s

/-- Admissible η-cutoffs: smooth, compact support, `φ 0 = 1`, `|φ| ≤ 1`. -/
def DFPhi (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ φ 0 = 1 ∧ ∀ t, |φ t| ≤ 1

/-- Leaf `T11/2/2/1`: `ψ_L` is a legitimate cell-stream test (smooth, `q`-periodic, vanishing for
`s < σ₀`, `s > σ₁`, `|η| > L'`).  `ψ_∞` is smooth since `tsupport χ ⊂ (0,s)` (outside it `ψ = 0`
near the point, inside `H` is smooth because `s-σ > 0`). -/
def DualTestAdmissible : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (H : Coord → ℝ) (s : ℝ) (r' : ℝ) (χ φ : ℝ → ℝ) (L : ℝ),
    0 < c → 0 < ν → 0 < s → HeatSol c ν r' H → DFChi s χ → DFPhi φ → 0 < L →
    ContDiff ℝ ∞ (dualPsi μ χ φ H s L) ∧
      (∀ x, dualPsi μ χ φ H s L (qShift c x) = dualPsi μ χ φ H s L x) ∧
      (∃ σ Hh Lm : ℝ, 0 < σ ∧ ∀ x : Coord, (x.1 < σ ∨ Hh < x.1 ∨ Lm < |x.2.2|) →
        dualPsi μ χ φ H s L x = 0)

/-- Leaf `T11/2/2/2` (complexification of `FlatEqCellStream`): for a complex smooth
`q`-periodic test `ψ` with the support condition, `∫ b·T(∇^⊥ψ) d(ageμ c 0) = 0`.  Proof:
apply `FlatEqCellStream` to `Re ψ` and `Im ψ` (real parts; `cpd` of `Re ψ` is `Re` of `cpdC`)
and recombine `flatTransposeC (perpC ψ) = flatTranspose(..Re ψ) + i flatTranspose(..Im ψ)`. -/
def DualTestEq : Prop :=
  FlatEqCellStream →
  ∀ (c r ν : ℝ) (μ : ℂ) (b : CProf), 0 < c → 0 < ν → 1 < r → InHr c r b →
    IsFlatResponse ν μ 0 b →
    ∀ ψ : Coord → ℂ, ContDiff ℝ ∞ ψ → (∀ x, ψ (qShift c x) = ψ x) →
      (∃ σ Hh Lm : ℝ, 0 < σ ∧ ∀ x : Coord, (x.1 < σ ∨ Hh < x.1 ∨ Lm < |x.2.2|) → ψ x = 0) →
      ∫ x, pairC b (fun y => flatTransposeC ν μ (perpC ψ) y) x ∂(Axi.ageμ c 0) = 0

/-- Leaf `T11/2/2/3` (heat identity, pointwise): with `g(σ,·) = H(s-σ,·)`, `g_σ = -νΔg`, so
`T(ag) = (μ-1)a g - σ a' g - σ a g_σ - νσ a Δg = -σ^μ χ' g` for `a = σ^{μ-1}χ`, hence
`T(∇^⊥ψ_∞) = ∇^⊥(Tψ_∞) = -σ^μ χ'(σ) ∇^⊥g` (`T` has `σ`-only coefficients, commutes with
`∂_q, ∂_η`).  For `x` outside `tsupport χ × ℝ²` both sides vanish (`ψ_∞` is `0` near `x`). -/
def DualHeatIdentity : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (H : Coord → ℝ) (s r' : ℝ) (χ : ℝ → ℝ),
    0 < c → 0 < ν → 0 < s → HeatSol c ν r' H → DFChi s χ →
    ∀ (x : Coord) (i : Fin 2),
      flatTransposeC ν μ (perpC (dualPsiInf μ χ H s)) x i =
        -(((x.1 : ℂ) ^ μ) * ((deriv χ x.1 : ℝ) : ℂ) * perpC (fun z => (H (s - z.1, z.2) : ℂ)) x i)

/-- Leaf `T11/2/2/4` (commutator estimate): for `L > 0` the remainder pairing is integrable for
`ageμ c 0` and tends to `0` as `L → ∞`.  `Rem_L` consists of terms with a factor `L^{-1}φ'(η/L)`
or `L^{-2}φ''(η/L)`, `L^{-3}φ'''`, times `σ^{μ-1}χ` and derivatives of `g` of order `≤ 3`;
Hölder over `supp χ × cell × ℝ` (`b ∈ L^r`, `HeatSol.deriv_memLp`, `n ≤ 3`) gives `O(1/L)`. -/
def DualRemainderLimit : Prop :=
  ∀ (c r ν : ℝ) (μ : ℂ) (b : CProf) (H : Coord → ℝ) (s : ℝ) (χ φ : ℝ → ℝ),
    0 < c → 0 < ν → 1 < r → 0 < s → InHr c r b → IsFlatResponse ν μ 0 b →
    HeatSol c ν (r / (r - 1)) H → DFChi s χ → DFPhi φ →
    (∀ L : ℝ, 0 < L →
      Integrable (fun x => pairC b (dualRem ν μ χ φ H s L) x) (Axi.ageμ c 0)) ∧
    Tendsto (fun L : ℝ => ∫ x, pairC b (dualRem ν μ χ φ H s L) x ∂(Axi.ageμ c 0)) atTop (𝓝 0)

/-- Leaf `T11/2/2/5` (main term, dominated convergence + Fubini): for `L > 0` the main pairing
is integrable for `ageμ c 0`, and as `L → ∞` it tends to `-∫_{(0,s)} χ'(σ) F(σ) dσ`
(`φ(η/L) → φ 0 = 1` pointwise, `|φ| ≤ 1`, dominating function `|b||σ^μ χ'||∇^⊥g|` integrable as in
`DualFLocInt`; `ageμ c 0 = dσ|_{σ>0} ⊗ avgμ c` and `perpC` of the real `H` is the cast of
`perpGrad`). -/
def DualMainLimit : Prop :=
  ∀ (c r ν : ℝ) (μ : ℂ) (b : CProf) (H : Coord → ℝ) (s : ℝ) (χ φ : ℝ → ℝ),
    0 < c → 0 < ν → 1 < r → 0 < s → InHr c r b → IsFlatResponse ν μ 0 b →
    HeatSol c ν (r / (r - 1)) H → DFChi s χ → DFPhi φ →
    (∀ L : ℝ, 0 < L →
      Integrable (fun x => pairC b (dualMain μ χ φ H s L) x) (Axi.ageμ c 0)) ∧
    Tendsto (fun L : ℝ => ∫ x, pairC b (dualMain μ χ φ H s L) x ∂(Axi.ageμ c 0)) atTop
      (𝓝 (-∫ σ in Ioo (0 : ℝ) s, ((deriv χ σ : ℝ) : ℂ) * dualF c μ b H s σ))

/-- A cutoff `φ` with `DFPhi φ` exists. -/
theorem exists_dfPhi : ∃ φ : ℝ → ℝ, DFPhi φ := by
  let B : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨B, B.contDiff, B.hasCompactSupport, ?_, fun t => ?_⟩
  · exact B.one_of_mem_closedBall (Metric.mem_closedBall_self B.rIn_pos.le)
  · rw [abs_of_nonneg B.nonneg]; exact B.le_one

/-- `DualFTestZero` from the five leaves. -/
theorem dualFTestZero_of (h1 : DualTestAdmissible) (h2 : DualTestEq) (h3 : DualHeatIdentity)
    (h4 : DualRemainderLimit) (h5 : DualMainLimit) : DualFTestZero := by
  intro hcs c r ν μ b H s hc hν hr hs hb hfl hH χ hχ hχc hχs
  have hχ' : DFChi s χ := ⟨hχ, hχc, hχs⟩
  obtain ⟨φ, hφ⟩ := exists_dfPhi
  obtain ⟨hRi, hRt⟩ := h4 c r ν μ b H s χ φ hc hν hr hs hb hfl hH hχ' hφ
  obtain ⟨hMi, hMt⟩ := h5 c r ν μ b H s χ φ hc hν hr hs hb hfl hH hχ' hφ
  set I : ℂ := ∫ σ in Ioo (0 : ℝ) s, ((deriv χ σ : ℝ) : ℂ) * dualF c μ b H s σ with hI
  have key : ∀ L : ℝ, 0 < L →
      ∫ x, pairC b (dualMain μ χ φ H s L) x ∂(Axi.ageμ c 0) =
        -∫ x, pairC b (dualRem ν μ χ φ H s L) x ∂(Axi.ageμ c 0) := by
    intro L hL
    obtain ⟨hs1, hs2, hs3⟩ := h1 c ν μ H s _ χ φ L hc hν hs hH hχ' hφ hL
    have h0 := h2 hcs c r ν μ b hc hν hr hb hfl _ hs1 hs2 hs3
    have hsplit : ∀ x, pairC b (fun y => flatTransposeC ν μ (perpC (dualPsi μ χ φ H s L)) y) x =
        pairC b (dualMain μ χ φ H s L) x + pairC b (dualRem ν μ χ φ H s L) x := by
      intro x
      unfold pairC
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := h3 c ν μ H s _ χ hc hν hs hH hχ' x i
      simp only [dualMain, dualRem]
      rw [← this]; ring
    have hint : Integrable (fun x => pairC b (fun y => flatTransposeC ν μ
        (perpC (dualPsi μ χ φ H s L)) y) x) (Axi.ageμ c 0) := by
      simp_rw [hsplit]; exact (hMi L hL).add (hRi L hL)
    simp_rw [hsplit] at h0
    rw [integral_add (hMi L hL) (hRi L hL)] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hlim : Tendsto (fun L : ℝ => ∫ x, pairC b (dualMain μ χ φ H s L) x ∂(Axi.ageμ c 0))
      atTop (𝓝 (-0)) := by
    refine hRt.neg.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL using (key L hL).symm
  have := tendsto_nhds_unique hMt hlim
  have h : I = 0 := by simpa using this
  exact h

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.dualFTestZero_of
