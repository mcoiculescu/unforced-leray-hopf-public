import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub

/-!
# `PartIII-a:T21/2/3/1/4` (`ladVelLip`), decomposed

Source: `the November 2 reference manuscript` 3230-3240 (`‖K_d f‖₂ ≤ C_m‖f‖_{X_{m,d}}`,
zero mass), 2819-2830 (zero-circulation space, Biot-Savart velocity), 270-288.

`LadVelLip m` for `m > 8` follows from three leaves:
* `LadFlowZeroCirc`: `w ρ` has zero circulation (cut-off test `ladCut R` in the curl identity of
  `IsBiotSavart (u ρ)`, tail of `u ∈ L²`, dominated convergence);
* `LadBSSub`: `IsBiotSavart` is linear (differences);
* `LadBSBound m`: the Biot-Savart velocity of a zero-circulation `Ω ∈ X_{m,c}`, `c ≥ 1` obeys
  `‖U_j‖_2 ≤ C‖Ω‖_{X_m}` (`CTE.realBiotSavartUniform` on `Re Ω`, `Im Ω` and `CTE.isBiotSavart_unique`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-- **Leaf 1** (SP 270-288, 2819-2830): the weak linearised flow keeps zero circulation. -/
def LadFlowZeroCirc (m : ℝ) : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t : ℝ) (f : ℝ × ℝ → ℂ)
    (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ),
    1 ≤ c → HasZeroCirculation c f → IsLinearisedFlow ν c m tr t f w u →
      ∀ ρ : ℝ, t ≤ ρ → HasZeroCirculation c (w ρ)

/-- **Leaf 2**: linearity of `IsBiotSavart` (for `X_m` data, `m > 1`, so that the tested vorticity
integrands are integrable; `u ∈ L²` and the tests have bounded compactly supported derivatives). -/
def LadBSSub (m : ℝ) : Prop :=
  ∀ (c : ℝ) (ω₁ ω₂ : ℝ × ℝ → ℂ) (u₁ u₂ : ℝ × ℝ → Fin 2 → ℂ), 1 < m →
    MemLp ω₁ 2 (B0579.cellMeasure c m) → MemLp ω₂ 2 (B0579.cellMeasure c m) →
    IsBiotSavart c ω₁ u₁ → IsBiotSavart c ω₂ u₂ → IsBiotSavart c (ω₁ - ω₂) (u₁ - u₂)

/-- **Leaf 3** (SP 3230-3240 with uniqueness of the Biot-Savart velocity). -/
def LadBSBound (m : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (c : ℝ), 1 ≤ c → ∀ (Ω : ℝ × ℝ → ℂ), MemLp Ω 2 (B0579.cellMeasure c m) →
    HasZeroCirculation c Ω → ∀ U : ℝ × ℝ → Fin 2 → ℂ, IsBiotSavart c Ω U → ∀ j : Fin 2,
      eLpNorm (fun x => U x j) 2 (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal C * xNorm c m Ω

theorem ladVelLip_of (m : ℝ) (hm : 8 < m) (h1 : LadFlowZeroCirc m) (h2 : LadBSSub m)
    (h3 : LadBSBound m) : LadVelLip m := by
  intro ν c tr t f w u hc hf hflow
  obtain ⟨C, hC⟩ := h3
  refine ⟨C, fun ρ ρ' hρ hρ' j => ?_⟩
  have hm1 : 1 < m := by linarith
  have hz := h1 ν c tr t f w u hc hf hflow ρ hρ
  have hz' := h1 ν c tr t f w u hc hf hflow ρ' hρ'
  have hmem := hflow.memX ρ hρ
  have hmem' := hflow.memX ρ' hρ'
  have hbs := h2 c (w ρ) (w ρ') (u ρ) (u ρ') hm1 hmem hmem' (hflow.biotSavart ρ hρ)
    (hflow.biotSavart ρ' hρ')
  have hzd : HasZeroCirculation c (w ρ - w ρ') := by
    refine ⟨hz.1.sub hz'.1, ?_⟩
    have := integral_sub hz.1 hz'.1
    simp only [Pi.sub_apply]
    rw [this, hz.2, hz'.2, sub_zero]
  exact hC c hc (w ρ - w ρ') (hmem.sub hmem') hzd (u ρ - u ρ') hbs j

end UnforcedLeray.Short.IIIa
