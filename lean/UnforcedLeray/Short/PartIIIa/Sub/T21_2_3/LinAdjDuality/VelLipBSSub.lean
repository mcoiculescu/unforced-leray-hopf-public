import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_4
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutLimit

/-!
# `PartIII-a:T21/2/3/1/4`, leaf 2: linearity of `IsBiotSavart`

Source: `the November 2 reference manuscript` 2819-2830 (`IsBiotSavart`, `Defs.lean`
94-98). The three clauses of `IsBiotSavart` are linear: the `L²` clause is `MemLp.sub`, the
tested divergence and curl clauses are linear after splitting the integrals, all integrands being
integrable on the cell (`u ∈ L²(cell)` against the `L²` cylinder tests `∂_j ψ`; `ω ∈ X_m` against
the cylinder test `ψ ∈ X_{-m}`, `CutLimitAux.integrable_complex`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace BSSubAux

/-- `u ∈ L²(cell)` against the `L²` derivative of a cylinder test: integrable on the cell. -/
lemma integrable_u_pd {c : ℝ} {u : ℝ × ℝ → Fin 2 → ℂ} {ψ : ℝ × ℝ → ℝ}
    (hu : ∀ j, MemLp (fun x => u x j) 2 (volume.restrict (B0579.cell c)))
    (hψ : B0579.IsCylTest c ψ) (j j' : Fin 2) :
    Integrable (fun x => u x j * ((B0579.pd j' ψ x : ℝ) : ℂ)) (volume.restrict (B0579.cell c)) := by
  obtain ⟨R, hR⟩ := (hψ.pd j').vanish
  have hg : MemLp (fun x => B0579.pd j' ψ x) 2 (volume.restrict (B0579.cell c)) :=
    B0579.memLp_cell_of_continuous (hψ.pd j').continuous (B0579.isCompact_box c R)
      (fun x hx hK => hR x hx hK)
  exact (hu j).integrable_mul hg.ofReal

end BSSubAux

open BSSubAux in
/-- **Leaf 2** (linearity of the Biot-Savart relation). -/
theorem ladBSSub (m : ℝ) : LadBSSub m := by
  intro c ω₁ ω₂ u₁ u₂ hm h1 h2 b1 b2
  unfold IsBiotSavart at b1 b2 ⊢
  refine ⟨fun j => (b1.1 j).sub (b2.1 j), ?_, ?_⟩
  · intro ψ hψ
    have hi1 : Integrable (fun x => u₁ x 0 * ((B0579.pd 0 ψ x : ℝ) : ℂ) +
        u₁ x 1 * ((B0579.pd 1 ψ x : ℝ) : ℂ)) (volume.restrict (B0579.cell c)) :=
      (integrable_u_pd b1.1 hψ 0 0).add (integrable_u_pd b1.1 hψ 1 1)
    have hi2 : Integrable (fun x => u₂ x 0 * ((B0579.pd 0 ψ x : ℝ) : ℂ) +
        u₂ x 1 * ((B0579.pd 1 ψ x : ℝ) : ℂ)) (volume.restrict (B0579.cell c)) :=
      (integrable_u_pd b2.1 hψ 0 0).add (integrable_u_pd b2.1 hψ 1 1)
    have key : ∀ x, (u₁ - u₂) x 0 * ((B0579.pd 0 ψ x : ℝ) : ℂ) +
        (u₁ - u₂) x 1 * ((B0579.pd 1 ψ x : ℝ) : ℂ) =
        (u₁ x 0 * ((B0579.pd 0 ψ x : ℝ) : ℂ) + u₁ x 1 * ((B0579.pd 1 ψ x : ℝ) : ℂ)) -
        (u₂ x 0 * ((B0579.pd 0 ψ x : ℝ) : ℂ) + u₂ x 1 * ((B0579.pd 1 ψ x : ℝ) : ℂ)) := by
      intro x
      simp only [Pi.sub_apply]
      ring
    simp only [key]
    rw [integral_sub hi1 hi2, b1.2.1 ψ hψ, b2.2.1 ψ hψ, sub_zero]
  · intro ψ hψ
    have I1 : Integrable (fun x => ω₁ x * ((ψ x : ℝ) : ℂ)) (volume.restrict (B0579.cell c)) :=
      CutLimitAux.integrable_complex h1 (hψ.memLp (-m)).ofReal
    have I2 : Integrable (fun x => ω₂ x * ((ψ x : ℝ) : ℂ)) (volume.restrict (B0579.cell c)) :=
      CutLimitAux.integrable_complex h2 (hψ.memLp (-m)).ofReal
    have K1 := integrable_u_pd b1.1 hψ 0 1
    have K1' := integrable_u_pd b1.1 hψ 1 0
    have K2 := integrable_u_pd b2.1 hψ 0 1
    have K2' := integrable_u_pd b2.1 hψ 1 0
    have hA1 : Integrable (fun x => u₁ x 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) -
        u₁ x 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ)) (volume.restrict (B0579.cell c)) := K1.sub K1'
    have hA2 : Integrable (fun x => u₂ x 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) -
        u₂ x 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ)) (volume.restrict (B0579.cell c)) := K2.sub K2'
    have hL : ∀ x, (ω₁ - ω₂) x * ((ψ x : ℝ) : ℂ) = ω₁ x * ((ψ x : ℝ) : ℂ) - ω₂ x * ((ψ x : ℝ) : ℂ) := by
      intro x
      simp only [Pi.sub_apply]
      ring
    have hR : ∀ x, (u₁ - u₂) x 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) - (u₁ - u₂) x 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ) =
        (u₁ x 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) - u₁ x 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ)) -
        (u₂ x 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) - u₂ x 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ)) := by
      intro x
      simp only [Pi.sub_apply]
      ring
    simp only [hL, hR]
    rw [integral_sub I1 I2, b1.2.2 ψ hψ, b2.2.2 ψ hψ, integral_sub hA1 hA2]

end UnforcedLeray.Short.IIIa
