import UnforcedLeray.Short.PartIIb.Sub.T15_2
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogTestBounds

/-!
# Part II-b, task `PartII-b:T15/2/16`: the weak identity at a translated test

Source of record: `the November 2 reference manuscript`, lines 1975-1979. The target
is the Prop `LogShiftTest` (`Sub/T15_2.lean`, leaf `PartII-b:T15/2/16`), proved unchanged.

Proof outline. Fix `σ` and a `LogTest Φ`, and put `Ψ(y) = Φ(y.1 - σ, y.2)`.
1. `Ψ` is a `LogTest` with `cpd 0 Ψ y = cpd 0 Φ (y.1 - σ, y.2)` (translation).
2. The translation `x ↦ (x.1 + σ, x.2)` preserves `logMeas c`, so the left side equals
   `∫ (g - u/4) Ψ dλ`.
3. `LogWeak` at `Ψ`, together with the integrability supplied by `logTestBounds`, gives
   `∫ (g - u/4) Ψ dλ = -∫ u (∂_tΨ) dλ`, which is the right side after step 1.
-/

set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem logShiftTest : UnforcedLeray.Short.IIb.LogShiftTest := by
  intro c u g hc hu hg hweak σ Φ hΦ
  -- the translated test `Ψ(y) = Φ(y.1 - σ, y.2)`
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Coord → ℝ, Ψ = fun y => Φ (y.1 - σ, y.2) := ⟨_, rfl⟩
  have hΨapp : ∀ y : Coord, Ψ y = Φ (y.1 - σ, y.2) := fun y => by rw [hΨ]
  have hshift : ∀ y : Coord, y + ((-σ : ℝ), ((0 : ℝ), (0 : ℝ))) = (y.1 - σ, y.2) := fun y => by
    show (y.1 + -σ, (y.2.1 + 0, y.2.2 + 0)) = (y.1 - σ, y.2)
    simp [sub_eq_add_neg]
  have hΨfun : Ψ = fun y => Φ (y + ((-σ : ℝ), ((0 : ℝ), (0 : ℝ)))) := by
    funext y
    rw [hΨapp, hshift]
  -- `Ψ` is a logarithmic test
  obtain ⟨T, L, hTL⟩ := hΦ.compact
  have hΨT : LogTest c Ψ := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hΨfun]
      exact hΦ.smooth.comp (contDiff_id.add contDiff_const)
    · intro y
      rw [hΨapp, hΨapp]
      exact hΦ.periodic (y.1 - σ, y.2)
    · refine ⟨T + |σ|, L, fun y hy => ?_⟩
      rw [hΨapp]
      apply hTL
      rcases hy with h | h
      · left
        have h1 := abs_sub_abs_le_abs_sub y.1 σ
        show T < |y.1 - σ|
        linarith
      · right
        exact h
  -- chain rule: `cpd 0 Ψ y = cpd 0 Φ (y.1 - σ, y.2)`
  have hcpd : ∀ y : Coord, cpd 0 Ψ y = cpd 0 Φ (y.1 - σ, y.2) := by
    intro y
    show fderiv ℝ Ψ y (cdir 0) = fderiv ℝ Φ (y.1 - σ, y.2) (cdir 0)
    rw [hΨfun, fderiv_comp_add_right, hshift]
  -- translation `x ↦ (x.1 + σ, x.2)` preserves `logMeas c`
  have hSF : SFinite (Cyl.avgμ c) := by
    unfold Cyl.avgμ Cyl.cellμ
    infer_instance
  have hmp : MeasurePreserving (fun x : Coord => (x.1 + σ, x.2)) (logMeas c) (logMeas c) :=
    (measurePreserving_add_right volume σ).prod (MeasurePreserving.id (Cyl.avgμ c))
  have hemb : MeasurableEmbedding (fun x : Coord => (x.1 + σ, x.2)) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.addRight σ)
      (MeasurableEquiv.refl (ℝ × ℝ))).measurableEmbedding
  -- integrability from the basic bounds
  obtain ⟨-, -, hint⟩ := logTestBounds c Ψ hc hΨT
  have hgΨ := (hint g hg).1
  have huΨ := (hint u hu).1
  have hucΨ := (hint u hu).2
  -- step 2: change of variables
  have key : ∫ x, (g (x.1 + σ, x.2) - u (x.1 + σ, x.2) / 4) * (Φ x : ℂ) ∂(logMeas c)
      = ∫ y, (g y - u y / 4) * (Ψ y : ℂ) ∂(logMeas c) := by
    refine Eq.trans ?_ (hmp.integral_comp hemb (fun y : Coord => (g y - u y / 4) * (Ψ y : ℂ)))
    congr 1
    funext x
    simp only [hΨapp, add_sub_cancel_right]
  -- step 3: split the left side of `LogWeak` at `Ψ`
  have hL : ∫ y, (g y - u y / 4) * (Ψ y : ℂ) ∂(logMeas c)
      = ∫ y, g y * (Ψ y : ℂ) ∂(logMeas c) - (1 / 4 : ℂ) * ∫ y, u y * (Ψ y : ℂ) ∂(logMeas c) := by
    have e1 : (fun y => (g y - u y / 4) * (Ψ y : ℂ))
        = fun y => g y * (Ψ y : ℂ) - (1 / 4 : ℂ) * (u y * (Ψ y : ℂ)) := by
      funext y
      ring
    rw [e1, integral_sub hgΨ (huΨ.const_mul _), integral_const_mul]
  -- step 4: split the right side of `LogWeak` at `Ψ`
  have hR2 : ∫ y, u y * ((Ψ y / 4 - cpd 0 Ψ y : ℝ) : ℂ) ∂(logMeas c)
      = (1 / 4 : ℂ) * ∫ y, u y * (Ψ y : ℂ) ∂(logMeas c)
        - ∫ y, u y * ((cpd 0 Ψ y : ℝ) : ℂ) ∂(logMeas c) := by
    have e2 : (fun y => u y * ((Ψ y / 4 - cpd 0 Ψ y : ℝ) : ℂ))
        = fun y => (1 / 4 : ℂ) * (u y * (Ψ y : ℂ)) - u y * ((cpd 0 Ψ y : ℝ) : ℂ) := by
      funext y
      push_cast
      ring
    rw [e2, integral_sub (huΨ.const_mul _) hucΨ, integral_const_mul]
  -- the right side is the chain-rule identity for `cpd`
  have hC : ∫ y, u y * ((cpd 0 Ψ y : ℝ) : ℂ) ∂(logMeas c)
      = ∫ x, u x * ((cpd 0 Φ (x.1 - σ, x.2) : ℝ) : ℂ) ∂(logMeas c) := by
    simp only [hcpd]
  -- `LogWeak` at `Ψ`
  have hW := hweak Ψ hΨT
  rw [key, hL, hW, hR2, hC]
  ring

end UnforcedLeray.Short.IIb
