import UnforcedLeray.Short.PartIIb.Sub.T22_1.Stages

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace CylPDE

/-! # `PartII-b:T22/1/15` (`PicardLimit`): decomposition

Source: SP 2074-2093, 2103-2105 (cylinder equation and smoothing); the statements are standard
uniform-limit and Duhamel calculus.  The limit is `u = U 0 + Σ (U (n+1) - U n)`, with the
derivative series `picD1`, `picD2`; leaves: `PicLimDeriv`, `PicLimCont`, `PicLimSize`,
`ConvLinear`, `PicLimFix`. -/

/-- The hypotheses of `PicardLimit`. -/
structure PicHyp (c ν s T : ℝ) (v : ℝ → Pl → UnforcedLeray.Train.Vec) (f : Pl → ℝ)
    (U : ℕ → ℝ → Pl → ℝ) (B : ℝ) (ε : ℕ → ℝ) : Prop where
  hc : 0 < c
  hν : 0 < ν
  hs : 0 ≤ s
  hsT : s ≤ T
  hv : CylCoeff c T v
  hf : B0579.IsCylTest c f
  hU : ∀ n, PicClass c s T B (U n)
  hU0 : ∀ σ ∈ Icc s T, U 0 σ = heatSG (ν * (σ - s)) f
  hUs : ∀ n, ∀ σ ∈ Icc s T, ∀ x : Pl, U (n + 1) σ x = duhamelMap ν s v f (U n) σ x
  hε : Summable ε
  hdiff : ∀ n, ∀ σ ∈ Icc s T, ∀ x : Pl,
    W2 (fun y => U (n + 1) σ y - U n σ y) x * Real.cosh x.2 ≤ ε n

/-- The pointwise limit `U 0 + Σ_n (U (n+1) - U n)` of the Picard iterates. -/
def picLim (U : ℕ → ℝ → Pl → ℝ) (σ : ℝ) (x : Pl) : ℝ :=
  U 0 σ x + ∑' n, (U (n + 1) σ x - U n σ x)

/-- The series of first derivatives `∂_j U 0 + Σ (∂_j U (n+1) - ∂_j U n)`. -/
def picD1 (U : ℕ → ℝ → Pl → ℝ) (j : Fin 2) (σ : ℝ) (x : Pl) : ℝ :=
  B0579.pd j (U 0 σ) x + ∑' n, (B0579.pd j (U (n + 1) σ) x - B0579.pd j (U n σ) x)

/-- The series of second derivatives `∂_i ∂_j U 0 + Σ (∂_i ∂_j U (n+1) - ∂_i ∂_j U n)`. -/
def picD2 (U : ℕ → ℝ → Pl → ℝ) (i j : Fin 2) (σ : ℝ) (x : Pl) : ℝ :=
  B0579.pd i (B0579.pd j (U 0 σ)) x +
    ∑' n, (B0579.pd i (B0579.pd j (U (n + 1) σ)) x - B0579.pd i (B0579.pd j (U n σ)) x)

/-- The tail `Σ_{k ≥ n} ε k`. -/
def picTail (ε : ℕ → ℝ) (n : ℕ) : ℝ := ∑' k, ε (k + n)

/-- Conclusion of `PicLimDeriv`: `C²` slices and the derivatives are the derivative series. -/
def DerivConcl (s T : ℝ) (U : ℕ → ℝ → Pl → ℝ) : Prop :=
  ∀ σ ∈ Icc s T, ContDiff ℝ 2 (picLim U σ) ∧
    (∀ (j : Fin 2) (x : Pl), B0579.pd j (picLim U σ) x = picD1 U j σ x) ∧
    (∀ (i j : Fin 2) (x : Pl), B0579.pd i (B0579.pd j (picLim U σ)) x = picD2 U i j σ x)

/-- Conclusion of `PicLimCont`: periodicity and joint continuity of the limit and of its
derivative series. -/
def ContConcl (c s T : ℝ) (U : ℕ → ℝ → Pl → ℝ) : Prop :=
  (∀ σ ∈ Icc s T, ∀ x : Pl, picLim U σ (x.1 + c, x.2) = picLim U σ x) ∧
  ContinuousOn (fun z : ℝ × Pl => picLim U z.1 z.2) (Icc s T ×ˢ univ) ∧
  (∀ j : Fin 2, ContinuousOn (fun z : ℝ × Pl => picD1 U j z.1 z.2) (Icc s T ×ˢ univ)) ∧
  (∀ i j : Fin 2, ContinuousOn (fun z : ℝ × Pl => picD2 U i j z.1 z.2) (Icc s T ×ˢ univ))

/-- Conclusion of `PicLimSize`: the weighted `C²` bound of the limit and of its distance to `U n`. -/
def SizeConcl (s T B : ℝ) (U : ℕ → ℝ → Pl → ℝ) (ε : ℕ → ℝ) : Prop :=
  (∀ σ ∈ Icc s T, ∀ x : Pl, W2 (picLim U σ) x * Real.cosh x.2 ≤ B + ∑' k, ε k) ∧
  (∀ n, ∀ σ ∈ Icc s T, ∀ x : Pl,
    W2 (fun y => picLim U σ y - U n σ y) x * Real.cosh x.2 ≤ picTail ε n)

/-- **Leaf 1 (`/15/1`).** The uniform limit of the `C²` slices with summable `W2`-increments is
`C²` and its first and second derivatives are the limits of the derivatives (Weierstrass M-test
with `|∂ U| ≤ W2 ≤ W2 · cosh`; `hasFDerivAt_of_tendstoUniformly`; `contDiff_succ_iff_fderiv`). -/
def PicLimDeriv : Prop :=
  ∀ (c ν s T : ℝ) (v : ℝ → Pl → UnforcedLeray.Train.Vec) (f : Pl → ℝ) (U : ℕ → ℝ → Pl → ℝ)
    (B : ℝ) (ε : ℕ → ℝ), PicHyp c ν s T v f U B ε → DerivConcl s T U

/-- **Leaf 2 (`/15/2`).** Periodicity and joint continuity: limits of periodic functions are
periodic; uniform limits (in `(σ, x)` on `Icc s T ×ˢ univ`) of continuous functions are continuous
(`tendstoUniformlyOn_tsum`, `TendstoUniformlyOn.continuousOn`). -/
def PicLimCont : Prop :=
  ∀ (c ν s T : ℝ) (v : ℝ → Pl → UnforcedLeray.Train.Vec) (f : Pl → ℝ) (U : ℕ → ℝ → Pl → ℝ)
    (B : ℝ) (ε : ℕ → ℝ), PicHyp c ν s T v f U B ε → ContConcl c s T U

/-- **Leaf 3 (`/15/3`).** Size of the limit: `W2(u σ) cosh ≤ B + Σ ε` and
`W2(u σ - U n σ) cosh ≤ Σ_{k ≥ n} ε k`, via `DerivConcl` (the derivatives of `u σ - U n σ` are
the tails of the derivative series; `W2` of a tail is bounded by the sum of the `W2` of the
increments; `cosh` is a common factor). -/
def PicLimSize : Prop :=
  ∀ (c ν s T : ℝ) (v : ℝ → Pl → UnforcedLeray.Train.Vec) (f : Pl → ℝ) (U : ℕ → ℝ → Pl → ℝ)
    (B : ℝ) (ε : ℕ → ℝ), PicHyp c ν s T v f U B ε → DerivConcl s T U → SizeConcl s T B U ε

/-- **Leaf 4 (`/15/4`).** Linearity of the Duhamel convolution for regular integrands bounded in
the `cosh` weight: `G(F₁ - F₂) = G(F₁) - G(F₂)` (integrability of `r ↦ H_{ν(τ-r)} F(r) (x)` on
`[s, τ]`: continuity in `r < τ` and the bound `|H_a F(x)| ≤ sup |F|`; linearity of `heatSG`). -/
def ConvLinear : Prop :=
  ∀ (ν s T : ℝ), 0 < ν → s ≤ T → ∀ (F G : ℝ → Pl → ℝ), FReg s T F → FReg s T G →
    ∀ B : ℝ, (∀ r ∈ Icc s T, WB B (F r) ∧ WB B (G r)) →
      ∀ τ ∈ Icc s T, ∀ x : Pl,
        duhamelConv ν s (fun r y => F r y - G r y) τ x =
          duhamelConv ν s F τ x - duhamelConv ν s G τ x

/-- **Leaf 5 (`/15/5`).** The fixed point: `u = duhamelMap u`.  With `w_n = u - U n` one has
`duhamelMap u - duhamelMap (U n) = -G(transp v w_n)`; `TranspClass` (with the constant bound
`b = picTail ε n`, built from `DerivConcl`, `ContConcl`, `SizeConcl`) gives
`FReg` and `WB (K b)` for `transp v w_n`, and `ConvRegular` bounds `W2 (G ·) cosh ≤ K' ∫ (1 +
(τ-r)^{-1/2}) K b dr` which is `≤ C · picTail ε n → 0`; also `u - U (n+1) → 0` pointwise, and
`U (n+1) = duhamelMap (U n)`.  `ConvLinear` is used for the subtraction.  Note `w_n` has
derivatives `picD1 - pd U n` (from `DerivConcl`), so `pd (w_n)` is the difference of `pd` (use
`HasFDerivAt.sub` on `C²` slices). -/
def PicLimFix : Prop :=
  ConvRegular → TranspClass → ConvLinear →
  ∀ (c ν s T : ℝ) (v : ℝ → Pl → UnforcedLeray.Train.Vec) (f : Pl → ℝ) (U : ℕ → ℝ → Pl → ℝ)
    (B : ℝ) (ε : ℕ → ℝ), PicHyp c ν s T v f U B ε → DerivConcl s T U → ContConcl c s T U →
      SizeConcl s T B U ε →
      ∀ σ ∈ Icc s T, ∀ x : Pl, picLim U σ x = duhamelMap ν s v f (picLim U) σ x

/-- **`PicardLimit` from the leaves.** -/
theorem picardLimit_of (h1 : PicLimDeriv) (h2 : PicLimCont) (h3 : PicLimSize)
    (h4 : ConvRegular) (h5 : TranspClass) (h6 : ConvLinear) (h7 : PicLimFix) : PicardLimit := by
  intro c ν s T v f hc hν hs hsT hv hf U B ε hU hU0 hUs hε hdiff
  have H : PicHyp c ν s T v f U B ε := ⟨hc, hν, hs, hsT, hv, hf, hU, hU0, hUs, hε, hdiff⟩
  have hD := h1 c ν s T v f U B ε H
  obtain ⟨hper, hc0, hc1, hc2⟩ := h2 c ν s T v f U B ε H
  have hS := h3 c ν s T v f U B ε H hD
  have hF := h7 h4 h5 h6 c ν s T v f U B ε H hD ⟨hper, hc0, hc1, hc2⟩ hS
  refine ⟨picLim U, ⟨⟨B + ∑' k, ε k, ?_⟩, hF⟩⟩
  refine ⟨fun σ hσ => (hD σ hσ).1, hper, hc0, ?_, ?_, hS.1⟩
  · intro j
    refine (hc1 j).congr ?_
    intro z hz
    exact (hD z.1 hz.1).2.1 j z.2
  · intro i j
    refine (hc2 i j).congr ?_
    intro z hz
    exact (hD z.1 hz.1).2.2 i j z.2

end CylPDE

end UnforcedLeray.Short.IIb
