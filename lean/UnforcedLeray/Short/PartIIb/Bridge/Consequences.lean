import UnforcedLeray.Short.PartIIb.Bridge.Response

/-!
# Bridge: existence and graph bound for free responses in the field model

Source of record: `the November 2 reference manuscript`, lines 1351-1364
(Lemma `bg:common-body-graph`, projected inverse), 1409-1412 (maximal domain).

* `field_response_exists` : `IsInYr P r f → ∃ w, IsFreeResponse ν μ r P f w` (for `0 < P ≤ 1`,
  `ν > 0`, `a_r > 0`, `1 < r < 3`);
* `field_graph_bound` : the graph and gradient bound of `bg:body-graph` for every free response,
  with `C_r` independent of `P, ν, μ`.

Part II-a inputs (all proved): `commonBodyProjected_of lerayYResolventComm`, `commonBodyGraphBound`,
`norm_lerayY_le`.  Source facts carried as hypotheses: `LerayPairSol`, `SolSeparation`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.PartIIa

theorem gammaR_ofReal {r : ℝ} (hr : 0 ≤ r) : gammaR (ENNReal.ofReal r) = (3 / r - 1) / 2 := by
  simp [gammaR, ENNReal.toReal_ofReal hr]

theorem ofReal_lt_three {r : ℝ} (h3 : r < 3) : ENNReal.ofReal r < 3 := by
  rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 h3

/-- **(d1)** Existence of the free response in the field model (source 1358-1359). -/
theorem field_response_exists (hLP : LerayPairSol) {P ν r : ℝ} {μ : ℂ} {f : ℝ × Space → CVec3}
    (hf : IsInYr P r f) (hP : 0 < P) (hP1 : P ≤ 1) (hν : 0 < ν)
    (hμ : 0 < μ.re + (3 / r - 1) / 2) (h1 : 1 < r) (h3 : r < 3) :
    ∃ w, IsFreeResponse ν μ r P f w := by
  haveI : Fact (0 < P) := ⟨hP⟩
  have hr : 0 < r := by linarith
  have h1' : 1 < ENNReal.ofReal r := ENNReal.one_lt_ofReal.2 h1
  haveI : Fact (1 ≤ ENNReal.ofReal r) := ⟨h1'.le⟩
  have hμ' : 0 < μ.re + gammaR (ENNReal.ofReal r) := by rw [gammaR_ofReal hr.le]; exact hμ
  obtain ⟨Ff, hFrep, -⟩ := exists_hasRepY P r hr f hf
  obtain ⟨wD, hs, hb⟩ := commonBodyProjected_of lerayYResolventComm (ENNReal.ofReal r) h1'
    (ofReal_lt_three h3) P hP1 ν hν μ hμ' Ff
  obtain ⟨W, hWin, hWrep, -⟩ := exists_isInYr_hasRepY P r hr (wD : Yq P (ENNReal.ofReal r))
  refine ⟨W, isFreeResponse_of_memD hr hFrep hWin hWrep wD.2 hs ?_⟩
  intro Φ hΦ
  have : (⟨(wD : Yq P (ENNReal.ofReal r)), wD.2⟩ : D P ν (ENNReal.ofReal r)) = wD := rfl
  rw [this, hb, hLP _ h1' ENNReal.ofReal_ne_top P Ff Φ hΦ]

/-- **(d2)** The graph and gradient bound for every free response (source 1356-1357, 1409-1412). -/
theorem field_graph_bound (hLP : LerayPairSol) (hSS : SolSeparation) {r : ℝ} (h1 : 1 < r)
    (h3 : r < 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P ν : ℝ) (μ : ℂ) (f w : ℝ × Space → CVec3), 0 < P → P ≤ 1 → 0 < ν →
      0 < μ.re + (3 / r - 1) / 2 → IsInYr P r f → IsFreeResponse ν μ r P f w →
      ∃ g : Fin 3 → ℝ × Space → CVec3, (∀ j, IsInYr P r (g j)) ∧
        (∀ j, HasPtwOp P (fun Φ => -(dy j Φ)) w (g j)) ∧
        ∀ a b : ℝ × Space → CVec3, IsInYr P r a → HasPtwOp P (nuLapT ν) w a → IsInYr P r b →
          HasPtwOp P driftT w b →
          (phaseLpNorm P r w).toReal + (phaseLpNorm P r a).toReal + (phaseLpNorm P r b).toReal +
              Real.sqrt ν * ∑ j, (phaseLpNorm P r (g j)).toReal ≤
            C * (1 + (1 + ‖μ‖) / (μ.re + (3 / r - 1) / 2)) * (phaseLpNorm P r f).toReal := by
  have hr : 0 < r := by linarith
  have h1' : 1 < ENNReal.ofReal r := ENNReal.one_lt_ofReal.2 h1
  haveI : Fact (1 ≤ ENNReal.ofReal r) := ⟨h1'.le⟩
  have h3' := ofReal_lt_three h3
  obtain ⟨C₀, hC₀, hC⟩ := commonBodyGraphBound (ENNReal.ofReal r) h1' h3'
  refine ⟨C₀ * ‖lerayC (ENNReal.ofReal r) h1' ENNReal.ofReal_ne_top‖,
    mul_nonneg hC₀ (norm_nonneg _), ?_⟩
  intro P ν μ f w hP hP1 hν hμ hf hfr
  haveI : Fact (0 < P) := ⟨hP⟩
  have hμ' : 0 < μ.re + gammaR (ENNReal.ofReal r) := by rw [gammaR_ofReal hr.le]; exact hμ
  obtain ⟨Ff, hFrep, hFn⟩ := exists_hasRepY P r hr f hf
  obtain ⟨Wq, hWrep, hWn⟩ := exists_hasRepY P r hr w hfr.mem_w
  obtain ⟨hD, hs, heq⟩ := memD_of_isFreeResponse hr hfr hFrep hWrep
  have hbody := (bodyOp_eq_leray_iff hLP hSS h1' ENNReal.ofReal_ne_top μ ⟨Wq, hD⟩ hs Ff).1 heq
  obtain ⟨g, hgrad, hbound⟩ := hC P hP1 ν hν μ hμ' ⟨Wq, hD⟩
  have hg : ∀ j, ∃ G : ℝ × Space → CVec3, IsInYr P r G ∧ HasRepY (g j) G ∧
      (phaseLpNorm P r G).toReal = ‖g j‖ := fun j => exists_isInYr_hasRepY P r hr (g j)
  choose G hGin hGrep hGn using hg
  refine ⟨G, hGin, fun j => ?_, ?_⟩
  · exact (hasPtwOp_iff_hasPhaseOp (fun Φ hΦ => (hΦ.dy j).neg) hWrep (hGrep j)).2 (hgrad j)
  · intro a b ha hpa hb hpb
    obtain ⟨A, hArep, hAn⟩ := exists_hasRepY P r hr a ha
    obtain ⟨B, hBrep, hBn⟩ := exists_hasRepY P r hr b hb
    have hA : nuLapD (⟨Wq, hD⟩ : D P ν _) = A :=
      nuLapD_eq ((hasPtwOp_iff_hasPhaseOp (fun Φ hΦ => isPhaseTest_nuLapT hΦ ν) hWrep hArep).1 hpa)
    have hB : T0D (⟨Wq, hD⟩ : D P ν _) = B :=
      T0D_eq ((hasPtwOp_iff_hasPhaseOp (fun Φ hΦ => hΦ.driftT) hWrep hBrep).1 hpb)
    have hlp : ‖lerayY P (ENNReal.ofReal r) h1' ENNReal.ofReal_ne_top Ff‖ ≤
        ‖lerayC (ENNReal.ofReal r) h1' ENNReal.ofReal_ne_top‖ * ‖Ff‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (norm_lerayY_le h1' ENNReal.ofReal_ne_top) (norm_nonneg _))
    have hK : 0 ≤ 1 + (1 + ‖μ‖) / (μ.re + (3 / r - 1) / 2) := by positivity
    have hsum : ∑ j, (phaseLpNorm P r (G j)).toReal = ∑ j, ‖g j‖ :=
      Finset.sum_congr rfl fun j _ => hGn j
    have hb2 : graphNormD (⟨Wq, hD⟩ : D P ν _) + Real.sqrt ν * ∑ j, ‖g j‖ ≤
        C₀ * (1 + (1 + ‖μ‖) / (μ.re + (3 / r - 1) / 2)) *
          (‖lerayC (ENNReal.ofReal r) h1' ENNReal.ofReal_ne_top‖ * ‖Ff‖) := by
      refine hbound.trans ?_
      rw [gammaR_ofReal hr.le] at *
      rw [hbody]
      exact mul_le_mul_of_nonneg_left hlp (mul_nonneg hC₀ hK)
    unfold graphNormD at hb2
    simp only at hb2
    rw [hA, hB] at hb2
    rw [hsum, ← hWn, ← hAn, ← hBn, ← hFn]
    have hr' : C₀ * ‖lerayC (ENNReal.ofReal r) h1' ENNReal.ofReal_ne_top‖ *
        (1 + (1 + ‖μ‖) / (μ.re + (3 / r - 1) / 2)) * ‖Ff‖ =
        C₀ * (1 + (1 + ‖μ‖) / (μ.re + (3 / r - 1) / 2)) *
          (‖lerayC (ENNReal.ofReal r) h1' ENNReal.ofReal_ne_top‖ * ‖Ff‖) := by ring
    rw [hr']
    exact hb2

end UnforcedLeray.Short.IIb
