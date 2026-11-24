import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_15

/-!
# `PartII-b:T22/1/15/5`: the fixed point of the Picard limit

Source: `the November 2 reference manuscript` lines 2074-2093, 2103-2105.
The limit `u = picLim U` of the Picard iterates satisfies `u = duhamelMap u`.
Proof: `u - U (n+1)` is bounded by the tail `picTail ε (n+1)` (leaf `SizeConcl`), and
`duhamelMap u - duhamelMap (U n) = -G(transp v (u - U n))` (`ConvLinear`), which is bounded by
`C · picTail ε n` (`TranspClass` and `ConvRegular`).  Both bounds tend to zero.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace CylPDE

/-- `pd` of a difference of differentiable functions. -/
theorem plPdSubFun {f g : Pl → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (j : Fin 2) : B0579.pd j (fun x => f x - g x) = fun x => B0579.pd j f x - B0579.pd j g x := by
  funext x
  unfold B0579.pd
  rw [fderiv_fun_sub (hf x) (hg x)]
  rfl

/-- Pointwise form of `plPdSubFun`. -/
theorem plPdSubApp {f g : Pl → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (j : Fin 2) (x : Pl) :
    B0579.pd j (fun y => f y - g y) x = B0579.pd j f x - B0579.pd j g x :=
  congrFun (plPdSubFun hf hg j) x

/-- The first derivative of a `C²` function is differentiable. -/
theorem plPdDiff {G : Pl → ℝ} (hG : ContDiff ℝ 2 G) (j : Fin 2) :
    Differentiable ℝ (B0579.pd j G) := by
  have hfd : Differentiable ℝ (fderiv ℝ G) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  exact hfd.clm_apply (differentiable_const _)

/-- Second derivative of a difference of `C²` functions. -/
theorem plPd2SubApp {f g : Pl → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (i j : Fin 2) (x : Pl) :
    B0579.pd i (B0579.pd j (fun y => f y - g y)) x =
      B0579.pd i (B0579.pd j f) x - B0579.pd i (B0579.pd j g) x := by
  rw [plPdSubFun (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num)) j]
  exact plPdSubApp (plPdDiff hf j) (plPdDiff hg j) i x

/-- `|g x| ≤ W2 g x`. -/
theorem plAbsLeW2 (g : Pl → ℝ) (x : Pl) : |g x| ≤ W2 g x := by
  unfold W2
  linarith [abs_nonneg (B0579.pd 0 g x), abs_nonneg (B0579.pd 1 g x),
    abs_nonneg (B0579.pd 0 (B0579.pd 0 g) x), abs_nonneg (B0579.pd 0 (B0579.pd 1 g) x),
    abs_nonneg (B0579.pd 1 (B0579.pd 0 g) x), abs_nonneg (B0579.pd 1 (B0579.pd 1 g) x)]

theorem plW2Nonneg (g : Pl → ℝ) (x : Pl) : 0 ≤ W2 g x := by
  unfold W2
  positivity

/-- `|g x| ≤ W2 g x · cosh x₂`. -/
theorem plAbsLeW2Cosh (g : Pl → ℝ) (x : Pl) : |g x| ≤ W2 g x * Real.cosh x.2 := by
  have h1 := plAbsLeW2 g x
  have h2 := Real.one_le_cosh x.2
  have h3 := plW2Nonneg g x
  linarith [mul_le_mul h1 h2 zero_le_one h3]

/-- The Duhamel convolution depends only on the integrand on `[s, T]`. -/
theorem plDuhamelCongr {ν s T : ℝ} (hsT : s ≤ T) (F G : ℝ → Pl → ℝ)
    (h : ∀ r ∈ Icc s T, F r = G r) (τ : ℝ) (hτ : τ ∈ Icc s T) (x : Pl) :
    duhamelConv ν s F τ x = duhamelConv ν s G τ x := by
  unfold duhamelConv
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc s T := Set.uIcc_subset_Icc ⟨le_refl s, hsT⟩ hτ hr
  simp only [h r hr']

theorem picLimFix_proof : PicLimFix := by
  intro h4 h5 h6 c ν s T v f U B ε H hD hC hS σ hσ x
  have hν : 0 < ν := H.hν
  have hsT : s ≤ T := H.hsT
  -- nonnegativity of the summable sequence ε
  have hε0 : ∀ k, 0 ≤ ε k := fun k => by
    have h := H.hdiff k s ⟨le_refl s, hsT⟩ (0 : Pl)
    have h0 : 0 ≤ W2 (fun y => U (k + 1) s y - U k s y) (0 : Pl) * Real.cosh (0 : Pl).2 :=
      mul_nonneg (plW2Nonneg _ _) (Real.cosh_pos _).le
    linarith
  have hpt : ∀ k, 0 ≤ picTail ε k := fun k => by
    unfold picTail
    exact tsum_nonneg fun j => hε0 _
  have hTail : Tendsto (picTail ε) atTop (𝓝 0) := tendsto_sum_nat_add ε
  -- constants from the transport and the convolution hypotheses
  obtain ⟨K0, hK0, hTr⟩ := h5 c s T v H.hv H.hs hsT
  obtain ⟨Kc, hKc0, hReg⟩ := h4 ν s T hν hsT
  obtain ⟨M, hM1, hM2⟩ : ∃ M : ℝ, B + ∑' k, ε k ≤ M ∧ B ≤ M :=
    ⟨max (B + ∑' k, ε k) B, le_max_left _ _, le_max_right _ _⟩
  -- regularity of the limit
  have hc1 : ∀ j : Fin 2, ContinuousOn
      (fun z : ℝ × Pl => B0579.pd j (picLim U z.1) z.2) (Icc s T ×ˢ univ) :=
    fun j => (hC.2.2.1 j).congr (fun z hz => (hD z.1 hz.1).2.1 j z.2)
  have hc2 : ∀ i j : Fin 2, ContinuousOn
      (fun z : ℝ × Pl => B0579.pd i (B0579.pd j (picLim U z.1)) z.2) (Icc s T ×ˢ univ) :=
    fun i j => (hC.2.2.2 i j).congr (fun z hz => (hD z.1 hz.1).2.2 i j z.2)
  -- transport bounds for the limit and for the iterates
  have hFuLim := hTr (picLim U) (fun _ => M) (fun σ hσ => (hD σ hσ).1) hC.2.1 hc1 hc2
    (fun σ hσ x => le_trans (hS.1 σ hσ x) hM1)
  have hFUn : ∀ n : ℕ, FReg s T (transp v (U n)) ∧
      ∀ r ∈ Icc s T, WB (K0 * M) (transp v (U n) r) ∧
        ∀ j : Fin 2, WB (K0 * M) (B0579.pd j (transp v (U n) r)) := fun n =>
    hTr (U n) (fun _ => M) (fun σ hσ => (H.hU n).c2 σ hσ) (H.hU n).cont0 (H.hU n).cont1
      (H.hU n).cont2 (fun σ hσ x => le_trans ((H.hU n).bound σ hσ x) hM2)
  -- transport bounds for the differences `picLim U - U n`
  have hTw : ∀ n : ℕ, FReg s T (transp v (fun τ y => picLim U τ y - U n τ y)) ∧
      ∀ r ∈ Icc s T, WB (K0 * picTail ε n)
          (transp v (fun τ y => picLim U τ y - U n τ y) r) ∧
        ∀ j : Fin 2, WB (K0 * picTail ε n)
          (B0579.pd j (transp v (fun τ y => picLim U τ y - U n τ y) r)) := fun n =>
    hTr (fun τ y => picLim U τ y - U n τ y) (fun _ => picTail ε n)
      (fun σ hσ => (hD σ hσ).1.sub ((H.hU n).c2 σ hσ))
      (hC.2.1.sub (H.hU n).cont0)
      (fun j => ((hc1 j).sub ((H.hU n).cont1 j)).congr
        (fun z hz => plPdSubApp ((hD z.1 hz.1).1.differentiable (by norm_num))
          (((H.hU n).c2 z.1 hz.1).differentiable (by norm_num)) j z.2))
      (fun i j => ((hc2 i j).sub ((H.hU n).cont2 i j)).congr
        (fun z hz => plPd2SubApp (hD z.1 hz.1).1 ((H.hU n).c2 z.1 hz.1) i j z.2))
      (fun σ hσ x => hS.2 n σ hσ x)
  -- the tails of the Picard sequence tend to zero
  -- the bound on the integral for the fixed time σ
  set J : ℝ := ∫ r in s..σ, (1 + (σ - r) ^ (-(1 / 2 : ℝ))) with hJ
  have hbd : ∀ n : ℕ,
      |picLim U σ x - (heatSG (ν * (σ - s)) f x - duhamelConv ν s (transp v (picLim U)) σ x)|
        ≤ picTail ε (n + 1) + (Kc * (J * K0)) * picTail ε n := by
    intro n
    have hUs := H.hUs n σ hσ x
    unfold duhamelMap at hUs
    -- linearity of the convolution in the integrand
    have hcongr : ∀ r ∈ Icc s T,
        (fun y => transp v (picLim U) r y - transp v (U n) r y) =
          transp v (fun τ y => picLim U τ y - U n τ y) r := by
      intro r hr
      funext y
      have e0 := plPdSubApp ((hD r hr).1.differentiable (by norm_num))
        (((H.hU n).c2 r hr).differentiable (by norm_num)) 0 y
      have e1 := plPdSubApp ((hD r hr).1.differentiable (by norm_num))
        (((H.hU n).c2 r hr).differentiable (by norm_num)) 1 y
      simp only [transp]
      rw [e0, e1]
      ring
    have hdc := plDuhamelCongr (ν := ν) hsT (fun r y => transp v (picLim U) r y - transp v (U n) r y)
      (transp v (fun τ y => picLim U τ y - U n τ y)) hcongr σ hσ x
    have hlin := h6 ν s T hν hsT (transp v (picLim U)) (transp v (U n)) hFuLim.1 (hFUn n).1
      (K0 * M) (fun r hr => ⟨(hFuLim.2 r hr).1, (hFUn n).2 r hr |>.1⟩) σ hσ x
    -- the convolution estimate for `transp v (picLim U - U n)`
    have hW := (hReg (transp v (fun τ y => picLim U τ y - U n τ y)) (hTw n).1
      (fun _ => K0 * picTail ε n) continuousOn_const
      (fun r _ => mul_nonneg hK0 (hpt n)) (fun r hr => (hTw n).2 r hr)).2.2.2.2.2 σ hσ x
    try dsimp only at hW
    rw [intervalIntegral.integral_mul_const, ← hJ] at hW
    have hDabs : |duhamelConv ν s (transp v (fun τ y => picLim U τ y - U n τ y)) σ x|
        ≤ (Kc * (J * K0)) * picTail ε n := by
      have h1 := plAbsLeW2Cosh (duhamelConv ν s (transp v (fun τ y => picLim U τ y - U n τ y)) σ) x
      have h2 : Kc * (J * (K0 * picTail ε n)) = (Kc * (J * K0)) * picTail ε n := by ring
      linarith
    -- the tail of the Picard sequence
    have hPQ : |picLim U σ x - U (n + 1) σ x| ≤ picTail ε (n + 1) :=
      le_trans (plAbsLeW2Cosh (fun y => picLim U σ y - U (n + 1) σ y) x) (hS.2 (n + 1) σ hσ x)
    have hid : picLim U σ x - (heatSG (ν * (σ - s)) f x - duhamelConv ν s (transp v (picLim U)) σ x)
        = (picLim U σ x - U (n + 1) σ x) +
          duhamelConv ν s (transp v (fun τ y => picLim U τ y - U n τ y)) σ x := by
      linarith
    rw [hid]
    calc |(picLim U σ x - U (n + 1) σ x) +
          duhamelConv ν s (transp v (fun τ y => picLim U τ y - U n τ y)) σ x|
        ≤ |picLim U σ x - U (n + 1) σ x| +
          |duhamelConv ν s (transp v (fun τ y => picLim U τ y - U n τ y)) σ x| := abs_add_le _ _
      _ ≤ picTail ε (n + 1) + (Kc * (J * K0)) * picTail ε n := add_le_add hPQ hDabs
  -- the bound tends to zero
  have hlimit : Tendsto (fun n : ℕ => picTail ε (n + 1) + (Kc * (J * K0)) * picTail ε n)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => picTail ε (n + 1)) atTop (𝓝 0) :=
      hTail.comp (tendsto_add_atTop_nat 1)
    have h2 := hTail.const_mul (Kc * (J * K0))
    rw [mul_zero] at h2
    have h3 := h1.add h2
    rw [add_zero] at h3
    exact h3
  have hle : |picLim U σ x - (heatSG (ν * (σ - s)) f x - duhamelConv ν s (transp v (picLim U)) σ x)|
      ≤ 0 := ge_of_tendsto hlimit (Filter.Eventually.of_forall hbd)
  have h0 := abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  unfold duhamelMap
  linarith

end CylPDE

end UnforcedLeray.Short.IIb
