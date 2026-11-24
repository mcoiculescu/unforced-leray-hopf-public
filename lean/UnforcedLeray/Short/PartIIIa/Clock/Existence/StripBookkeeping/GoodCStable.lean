import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_9

/-!
# Part III-a, `PartIII-a:T21/3/9/3`: admissibility is stable

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
Statement `GoodCStable` is in `Sub/PartIIIa_T21_3_9.lean`. Elements of the physical state space
are admissible (`MemLp` from `X_{m,c}`, zero circulation from the submodule; integrability on the
cell from `B0610.oneX`, which needs `1/2 < m`), and admissible data are stable under
`f₁ + I f₂`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- Elements of `X_{m,c}` are integrable on the cell for `1/2 < m` (pair with `oneX`). -/
theorem gcs_integrableOn {c m : ℝ} (hm : 1 / 2 < m) (f : B0579.X c m) :
    IntegrableOn (fun x => f x) (B0579.cell c) := by
  have h := B0579.integrableOn_mul_neg c m f (B0610.oneX c m hm)
  refine h.congr_fun_ae ?_
  filter_upwards [B0610.coeFn_oneX (c := c) (m := m) hm] with x hx
  simp only [hx, mul_one]

theorem goodCStable : UnforcedLeray.Short.IIIa.Exist.GoodCStable := by
  unfold GoodCStable
  refine ⟨?_, ?_⟩
  · intro c m _ hm w
    have hm' : 1 / 2 < m := by linarith
    have hw : ∫ x in B0579.cell c, w.1 x = 0 :=
      (mem_zeroCirculationSubmodule_iff hm' w.1).1 w.2
    unfold GoodC HasZeroCirculation
    refine ⟨?_, ?_, ?_⟩
    · exact (Lp.memLp w.1).ofReal
    · exact Integrable.ofReal (gcs_integrableOn hm' w.1)
    · show ∫ x in B0579.cell c, ((vortFn hm w x : ℝ) : ℂ) = 0
      have h0 : ∫ x in B0579.cell c, vortFn hm w x = 0 := hw
      rw [integral_complex_ofReal, h0]
      simp
  · intro c m f₁ f₂ h₁ h₂
    obtain ⟨m1, i1, e1⟩ : MemLp f₁ 2 (B0579.cellMeasure c m) ∧
        IntegrableOn f₁ (B0579.cell c) ∧ ∫ x in B0579.cell c, f₁ x = 0 :=
      ⟨h₁.1, h₁.2.1, h₁.2.2⟩
    obtain ⟨m2, i2, e2⟩ : MemLp f₂ 2 (B0579.cellMeasure c m) ∧
        IntegrableOn f₂ (B0579.cell c) ∧ ∫ x in B0579.cell c, f₂ x = 0 :=
      ⟨h₂.1, h₂.2.1, h₂.2.2⟩
    unfold GoodC HasZeroCirculation
    refine ⟨m1.add (m2.const_mul Complex.I), Integrable.add i1 (Integrable.const_mul i2 Complex.I), ?_⟩
    rw [integral_add i1 (Integrable.const_mul i2 Complex.I), integral_const_mul, e1, e2,
      mul_zero, add_zero]
