import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas

/-!
# `PartIII-b:C/near/masked/9`: `StressMapUnique` (source 1678)

A stress map of `T_ε` is determined by its values on smooth tensor tests: for a test `M` the
classes `F = M` and `G = s div_ε M` satisfy the hypotheses of `PartIIa.IsStressMap`, so both stress
maps send `F` to `T G`.  Test classes are dense in `H_T` (`TensorTestDense`), and both maps are
continuous, so they agree everywhere (`Continuous.ext_on`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- **Uniqueness of the stress map** (source 1678). -/
theorem stressMapUnique_of (hD : TensorTestDense) (hM : TensorTestDivMem) : StressMapUnique := by
  intro c ε T S₁ S₂ hc h1 h2
  have key : ∀ M : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal,
      UnforcedLeray.Short.PartIIa.IsTensorTest c M → ∀ hMm : MemLp M 2
        (UnforcedLeray.Short.PartIIa.measureHT c),
      S₁ (hMm.toLp M) = S₂ (hMm.toLp M) := by
    intro M hMt hMm
    have hDv : MemLp (fun p => (p.1 : ℂ) • UnforcedLeray.Short.PartIIa.divEps ε M p) 2
        (UnforcedLeray.B0220.measureH c) := hM c ε hc M hMt
    have e1 := h1 M hMt (hMm.toLp M) (hDv.toLp _) (MemLp.coeFn_toLp hMm) (MemLp.coeFn_toLp hDv)
    have e2 := h2 M hMt (hMm.toLp M) (hDv.toLp _) (MemLp.coeFn_toLp hMm) (MemLp.coeFn_toLp hDv)
    rw [e1, e2]
  have hdense : Dense {x : UnforcedLeray.Short.PartIIa.HTSpace c |
      ∃ M : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal,
        UnforcedLeray.Short.PartIIa.IsTensorTest c M ∧
          ∃ hMm : MemLp M 2 (UnforcedLeray.Short.PartIIa.measureHT c), x = hMm.toLp M} := by
    rw [Metric.dense_iff]
    intro x r hr
    obtain ⟨M, hMt, hMm, hlt⟩ := hD c hc x r hr
    refine ⟨hMm.toLp M, ?_, M, hMt, hMm, rfl⟩
    rw [Metric.mem_ball, dist_comm, dist_eq_norm]
    exact hlt
  have hEq : ⇑S₁ = ⇑S₂ :=
    Continuous.ext_on hdense S₁.continuous S₂.continuous (fun x hx => by
      obtain ⟨M, hMt, hMm, rfl⟩ := hx
      exact key M hMt hMm)
  exact ContinuousLinearMap.ext fun F => congrFun hEq F

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
