import UnforcedLeray.Short.PartIIb.Bridge.FieldModel

/-!
# Bridge: free responses in the field model are the projected inverse of Part II-a

Source of record: `the November 2 reference manuscript`, lines 1351-1364, 1409-1412,
1498-1500.

For `q = ofReal r`, `HasRepY Ff f`, `HasRepY Wq w`:
`IsFreeResponse ν μ r P f w ↔ w ∈ Y_r ∧ Wq ∈ D_r ∩ Y_σ ∧ bodyOp μ Wq = 𝐏 Ff`
(`isFreeResponse_iff`), the existence `field_response_exists` and the graph bound
`field_graph_bound`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.PartIIa

section Resp

variable {P ν : ℝ} [Fact (0 < P)] {r : ℝ} {μ : ℂ} (hr : 0 < r) [Fact (1 ≤ ENNReal.ofReal r)]
  {f w : ℝ × Space → CVec3}

include hr in
/-- **(c), forward**: a free response represents an element of `D_r ∩ Y_σ` solving the equation
against solenoidal tests. -/
theorem memD_of_isFreeResponse (h : IsFreeResponse ν μ r P f w)
    {Ff Wq : Yq P (ENNReal.ofReal r)} (hF : HasRepY Ff f) (hW : HasRepY Wq w) :
    ∃ hD : Wq ∈ D P ν (ENNReal.ofReal r), Wq ∈ Ysigma P (ENNReal.ofReal r) ∧
      ∀ Φ, IsSolTest P Φ →
        phasePair P (ENNReal.ofReal r) Φ (bodyOp P ν (ENNReal.ofReal r) μ ⟨Wq, hD⟩) =
          phasePair P (ENNReal.ofReal r) Φ Ff := by
  obtain ⟨a, ha, hpa⟩ := h.lapl
  obtain ⟨b, hb, hpb⟩ := h.drift
  obtain ⟨A, hA, -⟩ := exists_hasRepY P r hr a ha
  obtain ⟨B, hB, -⟩ := exists_hasRepY P r hr b hb
  have hD : Wq ∈ D P ν (ENNReal.ofReal r) :=
    mem_D.2 ⟨⟨A, (hasPtwOp_iff_hasPhaseOp (fun Φ hΦ => isPhaseTest_nuLapT hΦ ν) hW hA).1 hpa⟩,
      ⟨B, (hasPtwOp_iff_hasPhaseOp (fun Φ hΦ => hΦ.driftT) hW hB).1 hpb⟩⟩
  refine ⟨hD, ?_, ?_⟩
  · intro φ hφ
    rw [phasePair_eq_pairF_of_hasRepY Wq w hW hφ.gradT]
    exact h.solenoidal φ hφ
  · intro Φ hΦ
    have hT : IsPhaseTest P (fun x => L0T ν Φ x + μ • Φ x) :=
      (isPhaseTest_L0T hΦ.1 ν).add (hΦ.1.const_smul μ)
    rw [phasePair_bodyOp μ ⟨Wq, hD⟩ hΦ.1,
      phasePair_eq_pairF_of_hasRepY Wq w hW hT,
      phasePair_eq_pairF_of_hasRepY Ff f hF hΦ.1]
    exact h.equation Φ hΦ

include hr in
/-- **(c), backward**: an element of `D_r ∩ Y_σ` solving the equation against solenoidal tests,
represented by a field in `Y_r`, is a free response. -/
theorem isFreeResponse_of_memD {Ff Wq : Yq P (ENNReal.ofReal r)} (hF : HasRepY Ff f)
    (hw : IsInYr P r w) (hW : HasRepY Wq w) (hD : Wq ∈ D P ν (ENNReal.ofReal r))
    (hs : Wq ∈ Ysigma P (ENNReal.ofReal r))
    (heq : ∀ Φ, IsSolTest P Φ →
      phasePair P (ENNReal.ofReal r) Φ (bodyOp P ν (ENNReal.ofReal r) μ ⟨Wq, hD⟩) =
        phasePair P (ENNReal.ofReal r) Φ Ff) :
    IsFreeResponse ν μ r P f w := by
  obtain ⟨a, ha, hAa, -⟩ := exists_isInYr_hasRepY P r hr (nuLapD (⟨Wq, hD⟩ : D P ν _))
  obtain ⟨b, hb, hBb, -⟩ := exists_isInYr_hasRepY P r hr (T0D (⟨Wq, hD⟩ : D P ν _))
  refine ⟨hw, ⟨a, ha, ?_⟩, ⟨b, hb, ?_⟩, ?_, ?_⟩
  · exact (hasPtwOp_iff_hasPhaseOp (fun Φ hΦ => isPhaseTest_nuLapT hΦ ν) hW hAa).2
      (hasPhaseOp_nuLapD ⟨Wq, hD⟩)
  · exact (hasPtwOp_iff_hasPhaseOp (fun Φ hΦ => hΦ.driftT) hW hBb).2 (hasPhaseOp_T0D ⟨Wq, hD⟩)
  · intro φ hφ
    rw [← phasePair_eq_pairF_of_hasRepY Wq w hW hφ.gradT]
    exact hs φ hφ
  · intro Φ hΦ
    have hT : IsPhaseTest P (fun x => L0T ν Φ x + μ • Φ x) :=
      (isPhaseTest_L0T hΦ.1 ν).add (hΦ.1.const_smul μ)
    rw [← phasePair_eq_pairF_of_hasRepY Wq w hW hT,
      ← phasePair_bodyOp μ ⟨Wq, hD⟩ hΦ.1, heq Φ hΦ,
      phasePair_eq_pairF_of_hasRepY Ff f hF hΦ.1]

include hr in
/-- **(c)** `IsFreeResponse ν μ r P f w` is exactly "`W ∈ D_r ∩ Y_σ` and `(μ+L)W = 𝐏F`" for the
represented elements (`1 < r < ∞`; source 1358-1361). -/
theorem isFreeResponse_iff (hLP : LerayPairSol) (hSS : SolSeparation) (h1 : 1 < r)
    {Ff Wq : Yq P (ENNReal.ofReal r)} (hF : HasRepY Ff f) (hW : HasRepY Wq w) :
    IsFreeResponse ν μ r P f w ↔
      IsInYr P r w ∧ ∃ hD : Wq ∈ D P ν (ENNReal.ofReal r), Wq ∈ Ysigma P (ENNReal.ofReal r) ∧
        bodyOp P ν (ENNReal.ofReal r) μ ⟨Wq, hD⟩ =
          lerayY P (ENNReal.ofReal r) (ENNReal.one_lt_ofReal.2 h1) ENNReal.ofReal_ne_top Ff := by
  have h1' : 1 < ENNReal.ofReal r := ENNReal.one_lt_ofReal.2 h1
  constructor
  · intro h
    obtain ⟨hD, hs, heq⟩ := memD_of_isFreeResponse hr h hF hW
    exact ⟨h.mem_w, hD, hs, (bodyOp_eq_leray_iff hLP hSS h1' ENNReal.ofReal_ne_top μ ⟨Wq, hD⟩
      hs Ff).1 heq⟩
  · rintro ⟨hw, hD, hs, hb⟩
    exact isFreeResponse_of_memD hr hF hw hW hD hs
      ((bodyOp_eq_leray_iff hLP hSS h1' ENNReal.ofReal_ne_top μ ⟨Wq, hD⟩ hs Ff).2 hb)

end Resp

end UnforcedLeray.Short.IIb
