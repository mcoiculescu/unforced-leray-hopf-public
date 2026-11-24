import UnforcedLeray.Short.PartIIb.Sub.T22

/-!
# Plan for `PartII-b:T22/1` (`CylClassicalExists`): classical solutions of `ω_σ = νΔω - v·∇ω`

Source of record: `the November 2 reference manuscript`, lines 2074-2093 (the equation
`ω_s = (νΔ - v_c(s)·∇ + A_c(s)) ω` on the centered cell `C_c`), 2103-2105 ("one may smooth the weight
... to justify this calculation") and 2026-2663 (the short background construction). The source calls
this standard parabolic theory; this file fixes the statements in which it is proved, and proves
(`cylClassicalExists_of_parts`) that `CylClassicalExists` follows from four statements:

* `TrainCoeffBdd`: the train velocity is a bounded `C¹` coefficient (`CylCoeff`),
* `DuhamelExists`: the Duhamel integral equation has a `C²`, `cosh`-weighted solution,
* `DuhamelToPde`: a Duhamel solution is a classical solution (time derivative),
* `EtaPowLeCosh`: `(1 + η²)^N ≤ C_N cosh η`.

## Why this route (history, `ORG:cyl-weight`)

* The decay weight of `CylSmoothDecay` is `(1 + η²)^N`, not `(1 + q² + η²)^N` (a `c`-periodic function
  cannot decay in `q`: `Sub/T22_1.lean`).
* The slices are `C²`, not `C^∞`: `TrainClose` controls `D^j(v - V_c^p)` only for `j ≤ 4`, so `v` has
  bounded derivatives of order `≤ 4` and no more; a global `C^∞` solution would need bounds on all
  derivatives of `v`. The Picard iteration below needs `v` and `Dv` bounded (`CylCoeff`).
* The Gaussian weight `cosh η` (the decay class is closed under convolution with the heat kernel:
  `cosh(x₂) ≤ 2 cosh(x₂ - y₂) cosh(y₂)` and `∫ K_a(z) cosh z₂ dz = e^a`) gives the decay for every
  power `(1 + η²)^N` at once, so no uniqueness theorem is needed to pass between weights.

## The mathematics

With `H_a g = K_a * g` (`heatSG`, the Gaussian `K_a(z) = (4πa)⁻¹ e^{-|z|²/(4a)}`, `a = ν t`), the
Duhamel formula is
`u(σ) = H_{ν(σ-s)} f - ∫_s^σ H_{ν(σ-r)} [v(r)·∇u(r)] dr` (`duhamelMap`). It is solved by Picard
iteration in the norm `sup_σ sup_x cosh(η) (|u| + |∇u| + |∇²u|)` (`W2`): the map `F ↦ ∫ H F` gains one
derivative with the singular kernel `(σ - r)^{-1/2}` (`ConvRegular`), and `F = v·∇u` is `C¹` with the
bounds of `v`, `Dv` (`TranspClass`). The iterates are `C²` by construction (`PicardIterates`), their
differences are summable by the Volterra recursion and the Gamma bound
(`UnforcedLeray.Gronwall`, `Infra/VolterraEvolution/GammaBound.lean`), and the uniform limit is a
`C²` fixed point (`PicardLimit`). The time derivative of the Duhamel convolution
(`ConvTimeDeriv`) and the heat equation for the free part (`FreePart`) give the equation (`DuhamelToPde`).



`T22/1/1` `TrainCoeffBdd`; `/2` `EtaPowLeCosh`; the heat toolbox `/3` `HeatKernelMoments`, `/4`
`HeatWBounds`, `/5` `HeatPeriodic`, `/6` `HeatGradFormula`, `/7` `HeatCommute`, `/8` `HeatEqn`, `/9`
`HeatCont`; the Duhamel convolution `/10` `ConvRegular`, `/11` `ConvTimeDeriv`; the free part and the
transport term `/12` `FreePart`, `/13` `TranspClass`; Picard `/14` `PicardIterates`, `/15`
`PicardLimit`; the equation `/16` `DuhamelToPde`; the assembly `T22/1` is
`cylClassicalExists_of_parts` applied to `/1`, `/2`, `duhamelExists_of_parts /14 /15` and `/16`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace CylPDE

abbrev Pl : Type := B0579.Plane

/-! ## The heat kernel on the plane -/

/-- The Gaussian heat kernel `K_a(z) = (4πa)⁻¹ exp(-|z|²/(4a))` of `e^{aΔ}` on the plane (`a > 0`). -/
def heatK (a : ℝ) (z : Pl) : ℝ :=
  1 / (4 * Real.pi * a) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * a))

/-- `∂_{z_i} K_a(z) = -(z_i/(2a)) K_a(z)`. -/
def heatKd (i : Fin 2) (a : ℝ) (z : Pl) : ℝ :=
  -(![z.1, z.2] i) / (2 * a) * heatK a z

/-- The heat semigroup `e^{aΔ}` on functions on the plane: the Gaussian convolution `K_a * g` for
`a > 0` and the identity for `a ≤ 0`. -/
def heatSG (a : ℝ) (g : Pl → ℝ) (x : Pl) : ℝ :=
  if a ≤ 0 then g x else ∫ y : Pl, heatK a (x - y) * g y

/-- The derivative kernel operator `g ↦ (∂_i K_a) * g`. -/
def heatSGd (i : Fin 2) (a : ℝ) (g : Pl → ℝ) (x : Pl) : ℝ :=
  ∫ y : Pl, heatKd i a (x - y) * g y

/-- `g` is bounded in the weight `cosh η`: `|g(x)| cosh(x₂) ≤ B`. -/
def WB (B : ℝ) (g : Pl → ℝ) : Prop := ∀ x : Pl, |g x| * Real.cosh x.2 ≤ B

/-- The `C²` size of `g` at `x`: `|g| + |∇g| + |∇²g|` (all four second partials). -/
def W2 (g : Pl → ℝ) (x : Pl) : ℝ :=
  |g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |B0579.pd 0 (B0579.pd 0 g) x| +
    |B0579.pd 0 (B0579.pd 1 g) x| + |B0579.pd 1 (B0579.pd 0 g) x| +
    |B0579.pd 1 (B0579.pd 1 g) x|

/-! ## The coefficient and the Duhamel objects -/

/-- A bounded `C¹` periodic transport coefficient on `[0, T]`: what the Picard iteration needs of
the train velocity. -/
structure CylCoeff (c T : ℝ) (v : ℝ → Pl → UnforcedLeray.Train.Vec) : Prop where
  slice : ∀ σ ∈ Icc 0 T, ContDiff ℝ 1 (v σ)
  cont : ContinuousOn (fun z : ℝ × Pl => v z.1 z.2) (Icc 0 T ×ˢ univ)
  dcont : ContinuousOn (fun z : ℝ × Pl => fderiv ℝ (v z.1) z.2) (Icc 0 T ×ˢ univ)
  periodic : ∀ σ ∈ Icc 0 T, ∀ x : Pl, v σ (x.1 + c, x.2) = v σ x
  bdd : ∃ M : ℝ, ∀ σ ∈ Icc 0 T, ∀ x : Pl, ‖v σ x‖ ≤ M
  dbdd : ∃ M : ℝ, ∀ σ ∈ Icc 0 T, ∀ x : Pl, ‖fderiv ℝ (v σ) x‖ ≤ M

/-- The transport term `v·∇u` at age `r`. -/
def transp (v : ℝ → Pl → UnforcedLeray.Train.Vec) (u : ℝ → Pl → ℝ) (r : ℝ) (y : Pl) : ℝ :=
  v r y 0 * B0579.pd 0 (u r) y + v r y 1 * B0579.pd 1 (u r) y

/-- The Duhamel convolution `G(τ) = ∫_s^τ H_{ν(τ-r)} F(r) dr`. -/
def duhamelConv (ν s : ℝ) (F : ℝ → Pl → ℝ) (τ : ℝ) (x : Pl) : ℝ :=
  ∫ r in s..τ, heatSG (ν * (τ - r)) (F r) x

/-- The Duhamel map `u ↦ H_{ν(σ-s)} f - ∫_s^σ H_{ν(σ-r)} [v·∇u](r) dr`. -/
def duhamelMap (ν s : ℝ) (v : ℝ → Pl → UnforcedLeray.Train.Vec) (f : Pl → ℝ)
    (u : ℝ → Pl → ℝ) (σ : ℝ) (x : Pl) : ℝ :=
  heatSG (ν * (σ - s)) f x - duhamelConv ν s (transp v u) σ x

/-- The class of the Picard iteration: `C²` slices, `c`-periodic, jointly continuous with the first
and second derivatives, and `W2 · cosh ≤ B` uniformly on `[s, T]`. -/
structure PicClass (c s T B : ℝ) (u : ℝ → Pl → ℝ) : Prop where
  c2 : ∀ σ ∈ Icc s T, ContDiff ℝ 2 (u σ)
  periodic : ∀ σ ∈ Icc s T, ∀ x : Pl, u σ (x.1 + c, x.2) = u σ x
  cont0 : ContinuousOn (fun z : ℝ × Pl => u z.1 z.2) (Icc s T ×ˢ univ)
  cont1 : ∀ j : Fin 2,
    ContinuousOn (fun z : ℝ × Pl => B0579.pd j (u z.1) z.2) (Icc s T ×ˢ univ)
  cont2 : ∀ i j : Fin 2,
    ContinuousOn (fun z : ℝ × Pl => B0579.pd i (B0579.pd j (u z.1)) z.2) (Icc s T ×ˢ univ)
  bound : ∀ σ ∈ Icc s T, ∀ x : Pl, W2 (u σ) x * Real.cosh x.2 ≤ B

/-- A Duhamel (mild) solution in the class: `u = duhamelMap u` on `[s, T]`. -/
structure DuhamelSol (c ν : ℝ) (v : ℝ → Pl → UnforcedLeray.Train.Vec) (s T : ℝ) (f : Pl → ℝ)
    (u : ℝ → Pl → ℝ) : Prop where
  cls : ∃ B : ℝ, PicClass c s T B u
  duhamel : ∀ σ ∈ Icc s T, ∀ x : Pl, u σ x = duhamelMap ν s v f u σ x

/-- The regularity of an integrand `F` of the Duhamel convolution: jointly continuous, `C¹` in the
plane variable with jointly continuous first derivatives. -/
structure FReg (s T : ℝ) (F : ℝ → Pl → ℝ) : Prop where
  contF : ContinuousOn (fun z : ℝ × Pl => F z.1 z.2) (Icc s T ×ˢ univ)
  c1 : ∀ r ∈ Icc s T, ContDiff ℝ 1 (F r)
  contdF : ∀ j : Fin 2,
    ContinuousOn (fun z : ℝ × Pl => B0579.pd j (F z.1) z.2) (Icc s T ×ˢ univ)

/-! ## The four statements of the top-level reduction -/

/-- **`T22/1/1`.** For `Σ > 0`, `ν > 0`, `c ≥ 1`, `δ ≥ 0` and a train with `TrainClose tr Σ δ`, the
velocity is a bounded `C¹` periodic coefficient on `[0, Σ/ν]`: `CylCoeff c (Σ/ν) tr.v`.
Source: SP 2085-2093 (`TrainClose` at orders `0, 1`), `IsTrain.smooth_v`, `periodic_v`. -/
def TrainCoeffBdd : Prop :=
  ∀ Sg : ℝ, 0 < Sg → ∀ ν c δ : ℝ, 0 < ν → 1 ≤ c → 0 ≤ δ → ∀ tr : B0140.TrainSol ν c,
    TrainClose tr Sg δ → CylCoeff c (Sg / ν) tr.v

/-- **`T22/1/2`.** `(1 + η²)^N ≤ C cosh η` for every real `N`. -/
def EtaPowLeCosh : Prop :=
  ∀ N : ℝ, ∃ C : ℝ, ∀ η : ℝ, (1 + η ^ 2) ^ N ≤ C * Real.cosh η

/-- The existence of a Duhamel solution (`/14` and `/15`, see `duhamelExists_of_parts`). -/
def DuhamelExists : Prop :=
  ∀ (c ν s T : ℝ) (v : ℝ → Pl → UnforcedLeray.Train.Vec), 0 < c → 0 < ν → 0 ≤ s → s ≤ T →
    CylCoeff c T v → ∀ f : Pl → ℝ, B0579.IsCylTest c f →
      ∃ u : ℝ → Pl → ℝ, DuhamelSol c ν v s T f u

/-- **`T22/1/16`.** A Duhamel solution is a classical solution: `∂_σ u = νΔu - v·∇u` on `[s, T]`
(one-sided derivative in `σ` within `Icc s T`). -/
def DuhamelToPde : Prop :=
  ∀ (c ν s T : ℝ) (v : ℝ → Pl → UnforcedLeray.Train.Vec), 0 < c → 0 < ν → 0 ≤ s → s ≤ T →
    CylCoeff c T v → ∀ f : Pl → ℝ, B0579.IsCylTest c f → ∀ u : ℝ → Pl → ℝ,
      DuhamelSol c ν v s T f u → ∀ σ ∈ Icc s T, ∀ x : Pl,
        HasDerivWithinAt (fun r => u r x)
          (ν * lapP (u σ) x - (v σ x 0 * B0579.pd 0 (u σ) x + v σ x 1 * B0579.pd 1 (u σ) x))
          (Icc s T) σ

/-! ## The Picard iteration (`/14`, `/15`) -/

/-- **`T22/1/14`.** The Picard iterates `U₀ = H f`, `U_{n+1} = duhamelMap U_n` exist in a common class
`PicClass B` and their successive differences are bounded in `W2 · cosh` by a summable sequence. -/
def PicardIterates : Prop :=
  ∀ (c ν s T : ℝ) (v : ℝ → Pl → UnforcedLeray.Train.Vec) (f : Pl → ℝ), 0 < c → 0 < ν → 0 ≤ s →
    s ≤ T → CylCoeff c T v → B0579.IsCylTest c f →
      ∃ (U : ℕ → ℝ → Pl → ℝ) (B : ℝ) (ε : ℕ → ℝ),
        (∀ n, PicClass c s T B (U n)) ∧
        (∀ σ ∈ Icc s T, U 0 σ = heatSG (ν * (σ - s)) f) ∧
        (∀ n, ∀ σ ∈ Icc s T, ∀ x : Pl, U (n + 1) σ x = duhamelMap ν s v f (U n) σ x) ∧
        Summable ε ∧
        (∀ n, ∀ σ ∈ Icc s T, ∀ x : Pl,
          W2 (fun y => U (n + 1) σ y - U n σ y) x * Real.cosh x.2 ≤ ε n)

/-- **`T22/1/15`.** A summable Picard sequence has a limit that is a Duhamel solution: the uniform
limit of `C²` functions with summable `W2 · cosh` increments is `C²`, periodic, jointly continuous
with its derivatives, and is a fixed point of `duhamelMap` (continuity of `duhamelMap` for the `W2`
norm: `ConvRegular`, `TranspClass`). -/
def PicardLimit : Prop :=
  ∀ (c ν s T : ℝ) (v : ℝ → Pl → UnforcedLeray.Train.Vec) (f : Pl → ℝ), 0 < c → 0 < ν → 0 ≤ s →
    s ≤ T → CylCoeff c T v → B0579.IsCylTest c f →
      ∀ (U : ℕ → ℝ → Pl → ℝ) (B : ℝ) (ε : ℕ → ℝ),
        (∀ n, PicClass c s T B (U n)) →
        (∀ σ ∈ Icc s T, U 0 σ = heatSG (ν * (σ - s)) f) →
        (∀ n, ∀ σ ∈ Icc s T, ∀ x : Pl, U (n + 1) σ x = duhamelMap ν s v f (U n) σ x) →
        Summable ε →
        (∀ n, ∀ σ ∈ Icc s T, ∀ x : Pl,
          W2 (fun y => U (n + 1) σ y - U n σ y) x * Real.cosh x.2 ≤ ε n) →
        ∃ u : ℝ → Pl → ℝ, DuhamelSol c ν v s T f u

theorem duhamelExists_of_parts (h1 : PicardIterates) (h2 : PicardLimit) : DuhamelExists := by
  intro c ν s T v hc hν hs hsT hv f hf
  obtain ⟨U, B, ε, hU, hU0, hUs, hε, hdiff⟩ := h1 c ν s T v f hc hν hs hsT hv hf
  exact h2 c ν s T v f hc hν hs hsT hv hf U B ε hU hU0 hUs hε hdiff

/-! ## The top-level reduction -/

/-- **`CylClassicalExists` follows from the four statements** (the assembly of `PartII-b:T22/1`). -/
theorem cylClassicalExists_of_parts (h1 : TrainCoeffBdd) (h2 : EtaPowLeCosh)
    (hA : DuhamelExists) (hB : DuhamelToPde) : CylClassicalExists := by
  intro Sg hSg ν c δ hν hc hδ tr htr s hs hsT f hf
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  have hcoef := h1 Sg hSg ν c δ hν hc hδ tr htr
  obtain ⟨u, hu⟩ := hA c ν s (Sg / ν) tr.v hc0 hν hs hsT hcoef f hf
  obtain ⟨B, hB'⟩ := hu.cls
  have hSle : ∀ (g : Pl → ℝ) (x : Pl),
      |g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x| ≤ W2 g x := by
    intro g x
    unfold W2 lapP
    have h1 := abs_add_le (B0579.pd 0 (B0579.pd 0 g) x) (B0579.pd 1 (B0579.pd 1 g) x)
    have := abs_nonneg (B0579.pd 0 (B0579.pd 1 g) x)
    have := abs_nonneg (B0579.pd 1 (B0579.pd 0 g) x)
    linarith
  have hdec : ∀ N : ℝ, ∃ C : ℝ, ∀ σ ∈ Icc s (Sg / ν), ∀ x : Pl,
      (|u σ x| + |B0579.pd 0 (u σ) x| + |B0579.pd 1 (u σ) x| + |lapP (u σ) x|) *
        (1 + x.2 ^ 2) ^ N ≤ C := by
    intro N
    obtain ⟨C0, hC0⟩ := h2 N
    refine ⟨C0 * B, fun σ hσ x => ?_⟩
    have hpos : 0 < (1 + x.2 ^ 2) ^ N := Real.rpow_pos_of_pos (by positivity) N
    have hcosh : 1 ≤ Real.cosh x.2 := Real.one_le_cosh _
    have hC00 : 0 ≤ C0 := by
      have h0 := hC0 0
      simp only [Real.cosh_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        add_zero, Real.one_rpow] at h0
      exact le_trans zero_le_one h0
    have hS : 0 ≤ |u σ x| + |B0579.pd 0 (u σ) x| + |B0579.pd 1 (u σ) x| + |lapP (u σ) x| := by
      positivity
    have hb := hB'.bound σ hσ x
    calc (|u σ x| + |B0579.pd 0 (u σ) x| + |B0579.pd 1 (u σ) x| + |lapP (u σ) x|) *
          (1 + x.2 ^ 2) ^ N
        ≤ (|u σ x| + |B0579.pd 0 (u σ) x| + |B0579.pd 1 (u σ) x| + |lapP (u σ) x|) *
            (C0 * Real.cosh x.2) := mul_le_mul_of_nonneg_left (hC0 x.2) hS
      _ = C0 * ((|u σ x| + |B0579.pd 0 (u σ) x| + |B0579.pd 1 (u σ) x| + |lapP (u σ) x|) *
            Real.cosh x.2) := by ring
      _ ≤ C0 * (W2 (u σ) x * Real.cosh x.2) := by
          apply mul_le_mul_of_nonneg_left _ hC00
          exact mul_le_mul_of_nonneg_right (hSle _ _) (by positivity)
      _ ≤ C0 * B := mul_le_mul_of_nonneg_left hb hC00
  refine ⟨u, ⟨hB'.cont0, fun σ hσ => ⟨hB'.c2 σ hσ, hB'.periodic σ hσ, fun N => ?_⟩,
    hdec, ?_⟩, ?_⟩
  · obtain ⟨C, hC⟩ := hdec N
    exact ⟨C, fun x => hC σ hσ x⟩
  · exact fun σ hσ x => hB c ν s (Sg / ν) tr.v hc0 hν hs hsT hcoef f hf u hu σ hσ x
  · funext x
    have h := hu.duhamel s ⟨le_rfl, hsT⟩ x
    simp only [duhamelMap, duhamelConv, heatSG, sub_self, mul_zero, le_refl, ↓reduceIte,
      intervalIntegral.integral_same, sub_zero] at h
    exact h

end CylPDE

end UnforcedLeray.Short.IIb
