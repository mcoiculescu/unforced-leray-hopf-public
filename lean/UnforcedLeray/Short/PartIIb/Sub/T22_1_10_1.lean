import UnforcedLeray.Short.PartIIb.Sub.T22_1_10

/-!
# `PartII-b:T22/1/10/1` (`CRDeriv`) decomposed

Source: `the November 2 reference manuscript` lines 2074-2093 and 2103-2105.
`crDeriv_of` proves `CRDeriv` from three leaf statements about the Duhamel integral
(`DHyp`-integrands) and two elementary facts proved here (`heatSGd_eq_heatSG_pd`, the C² glue).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.CylPDE

/-- Hypotheses of a Duhamel integrand `g` with weight bound `b`: joint continuity, `b` continuous
and nonnegative, and `|g r| cosh η ≤ b r`. -/
def DHyp (s T : ℝ) (g : ℝ → Pl → ℝ) (b : ℝ → ℝ) : Prop :=
  ContinuousOn (fun z : ℝ × Pl => g z.1 z.2) (Icc s T ×ˢ univ) ∧ ContinuousOn b (Icc s T) ∧
    (∀ r ∈ Icc s T, 0 ≤ b r) ∧ ∀ r ∈ Icc s T, WB (b r) (g r)

/-- **Leaf `/1`.** Parametric continuity of the heat integrands: for `τ ∈ [s,T]`, the maps
`(r, x) ↦ e^{ν(τ-r)Δ} g(r)(x)` and `(r, x) ↦ (∂_i K_{ν(τ-r)}) * g(r) (x)` are jointly continuous on
`[s, τ) × Pl` (dominated convergence in `y`, uniform weight bound `sup b` on the compact interval,
`HeatCont`-type approximate identity is not needed since `a = ν(τ-r) > 0` there). -/
def DParamCont : Prop := ∀ (ν s T : ℝ), 0 < ν → s ≤ T → ∀ (g : ℝ → Pl → ℝ) (b : ℝ → ℝ),
  DHyp s T g b → ∀ τ ∈ Icc s T,
    ContinuousOn (fun z : ℝ × Pl => heatSG (ν * (τ - z.1)) (g z.1) z.2) (Ico s τ ×ˢ univ) ∧
    ∀ i : Fin 2,
      ContinuousOn (fun z : ℝ × Pl => heatSGd i (ν * (τ - z.1)) (g z.1) z.2) (Ico s τ ×ˢ univ)

/-- **Leaf `/2`.** Differentiation of the Duhamel integral in the plane variable: majorant
`2 e^{ν(T-s)} (1 + a^{-1/2}) (sup b)` (`heatWBounds`, `cosh ≥ 1`), integrable by
`intervalIntegrable_kernel_mul`; use `heatGradFormula` pointwise in `r`
(`hasFDerivAt_integral_of_dominated_of_fderiv_le`, interval version). -/
def DDiff : Prop := ∀ (ν s T : ℝ), 0 < ν → s ≤ T → ∀ (g : ℝ → Pl → ℝ) (b : ℝ → ℝ),
  DHyp s T g b → ∀ τ ∈ Icc s T,
    Differentiable ℝ (duhamelConv ν s g τ) ∧
    ∀ (i : Fin 2) (x : Pl), B0579.pd i (duhamelConv ν s g τ) x =
      ∫ r in s..τ, heatSGd i (ν * (τ - r)) (g r) x

/-- **Leaf `/3`.** Continuity in `x` of `∫_s^τ (∂_i K_{ν(τ-r)}) * g(r) (x) dr` (dominated
continuity with the same majorant, using `DParamCont`). -/
def DCont : Prop := ∀ (ν s T : ℝ), 0 < ν → s ≤ T → ∀ (g : ℝ → Pl → ℝ) (b : ℝ → ℝ),
  DHyp s T g b → ∀ τ ∈ Icc s T, ∀ i : Fin 2,
    Continuous (fun x : Pl => ∫ r in s..τ, heatSGd i (ν * (τ - r)) (g r) x)

/-- `∂_j K_a * g = e^{aΔ} ∂_j g` for `a > 0`. -/
theorem heatSGd_eq_heatSG_pd
    (hGrad : HeatGradFormula) (hComm : HeatCommute) (B : ℝ) (g : Pl → ℝ)
    (hg : ContDiff ℝ 1 g) (hB : WB B g) (hpB : ∀ j : Fin 2, WB B (B0579.pd j g))
    (a : ℝ) (ha : 0 < a) (j : Fin 2) (x : Pl) :
    heatSGd j a g x = heatSG a (B0579.pd j g) x := by
  rw [← (hGrad B g hg.continuous hB a ha).2.1 j x]
  exact hComm B g hg hB hpB a j x

/-- A differentiable function on the plane with continuous partials is `C¹`. -/
theorem contDiff_one_of_pd {h : Pl → ℝ} (hd : Differentiable ℝ h)
    (hc : ∀ i : Fin 2, Continuous (B0579.pd i h)) : ContDiff ℝ 1 h := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨hd, ?_⟩
  have key : fderiv ℝ h = fun x => (B0579.pd 0 h x) • (ContinuousLinearMap.fst ℝ ℝ ℝ) +
      (B0579.pd 1 h x) • (ContinuousLinearMap.snd ℝ ℝ ℝ) := by
    funext x
    ext v
    · simp [B0579.pd, B0579.dir]
    · simp [B0579.pd, B0579.dir]
  rw [key]
  exact ((hc 0).smul continuous_const).add ((hc 1).smul continuous_const)

/-- Glue: `f` differentiable, every `∂_j f` differentiable with continuous partials, and
(partials of `f`) continuous, give `f ∈ C²`. -/
theorem contDiff_two_of_pd {f : Pl → ℝ} (hd : Differentiable ℝ f)
    (hd1 : ∀ j : Fin 2, Differentiable ℝ (B0579.pd j f))
    (hc1 : ∀ j : Fin 2, Continuous (B0579.pd j f))
    (hc2 : ∀ i j : Fin 2, Continuous (B0579.pd i (B0579.pd j f))) : ContDiff ℝ 2 f := by
  have h2 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  rw [h2, contDiff_succ_iff_fderiv]
  refine ⟨hd, by simp, ?_⟩
  have key : fderiv ℝ f = fun x => (B0579.pd 0 f x) • (ContinuousLinearMap.fst ℝ ℝ ℝ) +
      (B0579.pd 1 f x) • (ContinuousLinearMap.snd ℝ ℝ ℝ) := by
    funext x
    ext v
    · simp [B0579.pd, B0579.dir]
    · simp [B0579.pd, B0579.dir]
  rw [key]
  exact ((contDiff_one_of_pd (hd1 0) (hc2 · 0)).smul contDiff_const).add
    ((contDiff_one_of_pd (hd1 1) (hc2 · 1)).smul contDiff_const)


/-- `CRDeriv` from `HeatGradFormula`, `HeatCommute` and the leaves `DDiff`, `DCont`. -/
theorem crDeriv_of (hGrad : HeatGradFormula) (hComm : HeatCommute) (hD : DDiff) (hC : DCont) :
    CRDeriv := by
  intro ν s T hν hsT F b hH τ hτ
  obtain ⟨hF, hb, hb0, hFb⟩ := hH
  have hDF : DHyp s T F b := ⟨hF.contF, hb, hb0, fun r hr => (hFb r hr).1⟩
  have hDj : ∀ j : Fin 2, DHyp s T (fun r => B0579.pd j (F r)) b :=
    fun j => ⟨hF.contdF j, hb, hb0, fun r hr => (hFb r hr).2 j⟩
  obtain ⟨hdG, hf1⟩ := hD ν s T hν hsT F b hDF τ hτ
  have hpd : ∀ j : Fin 2, B0579.pd j (duhamelConv ν s F τ) =
      duhamelConv ν s (fun r => B0579.pd j (F r)) τ := by
    intro j
    funext x
    rw [hf1 j x]
    unfold duhamelConv
    apply intervalIntegral.integral_congr_ae
    have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ τ := by simp [ae_iff]
    filter_upwards [hne] with r hr hmem
    rw [Set.uIoc_of_le hτ.1] at hmem
    have hrI : r ∈ Icc s T := ⟨hmem.1.le, hmem.2.trans hτ.2⟩
    have hlt : r < τ := lt_of_le_of_ne hmem.2 hr
    exact heatSGd_eq_heatSG_pd hGrad hComm (b r) (F r) (hF.c1 r hrI) (hFb r hrI).1
      (hFb r hrI).2 (ν * (τ - r)) (mul_pos hν (sub_pos.2 hlt)) j x
  have hsub : ∀ j : Fin 2, Differentiable ℝ (B0579.pd j (duhamelConv ν s F τ)) := fun j => by
    rw [hpd j]; exact (hD ν s T hν hsT _ b (hDj j) τ hτ).1
  have hc1 : ∀ j : Fin 2, Continuous (B0579.pd j (duhamelConv ν s F τ)) := fun j => by
    have : B0579.pd j (duhamelConv ν s F τ) =
        fun x => ∫ r in s..τ, heatSGd j (ν * (τ - r)) (F r) x := funext (hf1 j)
    rw [this]; exact hC ν s T hν hsT F b hDF τ hτ j
  have hf2 : ∀ i j : Fin 2, B0579.pd i (B0579.pd j (duhamelConv ν s F τ)) =
      fun x => ∫ r in s..τ, heatSGd i (ν * (τ - r)) (B0579.pd j (F r)) x := by
    intro i j
    rw [hpd j]
    exact funext ((hD ν s T hν hsT _ b (hDj j) τ hτ).2 i)
  have hc2 : ∀ i j : Fin 2, Continuous (B0579.pd i (B0579.pd j (duhamelConv ν s F τ))) := by
    intro i j
    rw [hf2 i j]
    exact hC ν s T hν hsT _ b (hDj j) τ hτ i
  refine ⟨contDiff_two_of_pd hdG hsub hc1 hc2, hf1, fun i j x => ?_⟩
  rw [hf2 i j]

end UnforcedLeray.Short.IIb.CylPDE
