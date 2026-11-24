import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_cont_S
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas
import UnforcedLeray.Units.B0223

/-!
# `PartIII-b:C/cont/S`: the resolvent identity for stress maps (source 1556-1583, 1675-1690,
3888-3890)

Source of record: `the November 2 reference manuscript` (73 pages).

The vector resolvent `R^{vec}(μ) = RepsVec μ` satisfies `R(μ) - R(μ') = (μ' - μ) R(μ) R(μ')` on
`H`, derived from the two-sided inverse properties on the generator graph (`RepsVec_left`,
`RepsVec_right`). Since `Teps μ = R^{vec}(μ) ∘ P_ε`, two stress maps of `T_ε(μ)` and `T_ε(μ')`
differ by `(μ' - μ) R^{vec}(μ) S'` on smooth tensor tests, and by density everywhere.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Vector resolvent identity** on `H`: `R(μ) x - R(μ') x = (μ' - μ) R(μ) (R(μ') x)` for real
`μ, μ' > -1/4` (inverse properties of `RepsVec` on the generator graph, source 1675-1690). -/
theorem repsVec_resolvent_apply {P ν ε c : ℝ} [Fact (0 < P)] (hν : 0 < ν) (hε : 0 < ε)
    (hc : 0 < c) (hP : P = 2 * ε * c) {μ μ' : ℝ} (hμ : -(1 / 4 : ℝ) < μ)
    (hμ' : -(1 / 4 : ℝ) < μ')
    (x : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC) :
    UnforcedLeray.B0223.RepsVec hν hε hc hP (μ : ℂ) x -
        UnforcedLeray.B0223.RepsVec hν hε hc hP (μ' : ℂ) x =
      (((μ' - μ : ℝ) : ℂ)) •
        UnforcedLeray.B0223.RepsVec hν hε hc hP (μ : ℂ)
          (UnforcedLeray.B0223.RepsVec hν hε hc hP (μ' : ℂ) x) := by
  have hγ : 0 < ((μ : ℂ)).re + 1 / 4 := by
    simp only [Complex.ofReal_re]; linarith
  have hγ' : 0 < ((μ' : ℂ)).re + 1 / 4 := by
    simp only [Complex.ofReal_re]; linarith
  have h1 := UnforcedLeray.B0223.RepsVec_right hν hε hc hP hγ' x
  have h2 := UnforcedLeray.B0223.RepsVec_left hν hε hc hP hγ h1
  have e : (μ : ℂ) • UnforcedLeray.B0223.RepsVec hν hε hc hP (μ' : ℂ) x -
        ((μ' : ℂ) • UnforcedLeray.B0223.RepsVec hν hε hc hP (μ' : ℂ) x - x) =
      x + (((μ : ℂ) - (μ' : ℂ)) • UnforcedLeray.B0223.RepsVec hν hε hc hP (μ' : ℂ) x) := by
    module
  rw [e, map_add, map_smul] at h2
  generalize UnforcedLeray.B0223.RepsVec hν hε hc hP (μ : ℂ)
    (UnforcedLeray.B0223.RepsVec hν hε hc hP (μ' : ℂ) x) = V at h2 ⊢
  generalize UnforcedLeray.B0223.RepsVec hν hε hc hP (μ' : ℂ) x = W at h2 ⊢
  generalize UnforcedLeray.B0223.RepsVec hν hε hc hP (μ : ℂ) x = A at h2 ⊢
  rw [← h2]
  push_cast
  module

/-- **Resolvent identity for stress maps** (source 1556-1583, 1675-1690, 3888-3890): if `S` and
`S'` are stress maps of `T_ε(μ)` and `T_ε(μ')` (real `μ, μ' > -1/4`), then
`S - S' = (μ' - μ) R^{vec}(μ) ∘ S'`. -/
theorem stressMapResolvent
    (hD : UnforcedLeray.Short.PartIIIb.NearInst.Masked.TensorTestDense)
    (hM : UnforcedLeray.Short.PartIIIb.NearInst.Masked.TensorTestDivMem) :
    StressMapResolvent := by
  unfold StressMapResolvent
  intro ν ε c P _ hν hε hc hP μ μ' hμ hμ' S S' h1 h2
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
  have key : ∀ M : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal,
      UnforcedLeray.Short.PartIIa.IsTensorTest c M →
      ∀ hMm : MemLp M 2 (UnforcedLeray.Short.PartIIa.measureHT c),
        (S - S') (hMm.toLp M) = (((μ' - μ : ℝ) : ℂ)) •
          ((UnforcedLeray.B0223.RepsVec hν hε hc hP (μ : ℂ)) ∘L S') (hMm.toLp M) := by
    intro M hMt hMm
    have hDv : MemLp (fun p => (p.1 : ℂ) • UnforcedLeray.Short.PartIIa.divEps ε M p) 2
        (UnforcedLeray.B0220.measureH c) := hM c ε hc M hMt
    have e1 := h1 M hMt (hMm.toLp M) (hDv.toLp _) (MemLp.coeFn_toLp hMm) (MemLp.coeFn_toLp hDv)
    have e2 := h2 M hMt (hMm.toLp M) (hDv.toLp _) (MemLp.coeFn_toLp hMm) (MemLp.coeFn_toLp hDv)
    simp only [sub_apply, ContinuousLinearMap.comp_apply]
    rw [e1, e2]
    simp only [UnforcedLeray.Short.PartIIa.Teps, ContinuousLinearMap.comp_apply]
    exact repsVec_resolvent_apply hν hε hc hP hμ hμ'
      (UnforcedLeray.Short.PartIIa.PepsC ε c (hDv.toLp _))
  have hEq : ⇑(S - S') = ⇑((((μ' - μ : ℝ) : ℂ)) •
      ((UnforcedLeray.B0223.RepsVec hν hε hc hP (μ : ℂ)) ∘L S')) :=
    Continuous.ext_on hdense (S - S').continuous
      ((((μ' - μ : ℝ) : ℂ)) • ((UnforcedLeray.B0223.RepsVec hν hε hc hP (μ : ℂ)) ∘L S')).continuous
      (fun x hx => by
        obtain ⟨M, hMt, hMm, rfl⟩ := hx
        exact key M hMt hMm)
  exact ContinuousLinearMap.ext fun F => congrFun hEq F

end UnforcedLeray.Short.PartIIIb.Concrete
