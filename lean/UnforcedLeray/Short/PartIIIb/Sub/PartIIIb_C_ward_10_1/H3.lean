import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_1.H2

/-!
# Helpers for `wardX0YoungL2_proved` (3): `sep:young` applied to the transfer field

Source of record: `the November 2 reference manuscript` (73 pages),
3631-3646 (`sep:young`, `p = q = 2`, `b = 1`), 2683-2689.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem w10Fn_enorm {R ν : ℝ} {N : ℝ → Space → ℝ} (hN : ∀ τ y, 0 ≤ N τ y) (τ : ℝ) {y : Space}
    (hy : R * Real.sqrt ν ≤ ϱ y) :
    ‖w10Fn R ν N τ y‖ₑ = ENNReal.ofReal (N τ (meridPt y)) := by
  unfold w10Fn
  rw [if_pos hy, ← ofReal_norm, norm_smul, Real.norm_of_nonneg (hN _ _)]
  simp [coordinateVector]

theorem w10_gtl (m : ℝ) (hm : -(1 / 4) < m) (j : ℕ) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (ν R c : ℝ), 0 < ν → 0 < R → 0 < c →
      ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
      IIIa.IsSepSource (2 * c / R) (R * Real.sqrt (5 * ν / 6)) T →
      ∀ (K : ℝ) (N : ℝ → Space → ℝ), 0 ≤ K → Measurable (fun x : ℝ × Space => N x.1 x.2) →
      (∀ τ y, N (τ + 2 * c / R) y = N τ y) → (∀ τ y, 0 ≤ N τ y) →
      (∀ τ y, R * Real.sqrt ν ≤ ϱ y →
        ENNReal.ofReal (N τ (meridPt y)) ≤ ENNReal.ofReal K * IIIa.wDerivNorm ν (m : ℂ) T j τ y) →
      ∫⁻ p in {p : Chart | ν * p.1 ≤ 1}, ‖coefOf R (w10Fn R ν N) p‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) ≤
        ENNReal.ofReal (1 / (Real.pi * R ^ 2)) *
          (ENNReal.ofReal K * (ENNReal.ofReal (C0 *
            (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-4 - (j : ℝ) + 3 / 1)) *
            IIIa.ltauLq (2 * c / R) 2 (IIIa.srcNorm T))) ^ (2 : ℝ) := by
  obtain ⟨C, hC, hY⟩ := IIIa.sepYoung {(m : ℂ)} isCompact_singleton
    (by intro μ hμ; rw [Set.mem_singleton_iff] at hμ; subst hμ; simpa using hm)
    j 2 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ⟨2 * m + 3 / 2, by linarith, by
      intro μ hμ; rw [Set.mem_singleton_iff] at hμ; subst hμ; simp⟩
  refine ⟨C, hC, ?_⟩
  intro ν R c hν hR hc T hT K N hK hNm hNp hN0 hDom
  have hP : 0 < 2 * c / R := by positivity
  have hper : ∀ τ y, w10Fn R ν N (τ + 2 * c / R) y = w10Fn R ν N τ y :=
    w10Fn_periodic R ν _ hNp
  have hTr := chartYoungTransport R c ν hR hc hν (w10Fn R ν N) (w10Fn_measurable R ν hNm)
    (w10Fn_axi R ν N) hper
  refine hTr.trans ?_
  gcongr
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hrO : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hY' := hY ν hν (m : ℂ) rfl (R * Real.sqrt (5 * ν / 6)) (R * Real.sqrt ν) (2 * c / R) hrO hrr
    hP T hT
  have hpt : ∀ τ y, (if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) then ‖w10Fn R ν N τ y‖ₑ
      else 0) ≤ ENNReal.ofReal K * IIIa.youngDerivNorm ν (m : ℂ) T j (R * Real.sqrt ν) τ y := by
    intro τ y
    by_cases h : R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
    · rw [if_pos h]
      have h' : R * Real.sqrt ν ≤ ϱ y := h
      rw [w10Fn_enorm hN0 τ h']
      simp only [IIIa.youngDerivNorm, if_pos h]
      exact hDom τ y h'
    · rw [if_neg h]
      exact zero_le
  calc IIIa.ltauLq (2 * c / R) 2 (fun τ y => if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
          then ‖w10Fn R ν N τ y‖ₑ else 0)
      ≤ IIIa.ltauLq (2 * c / R) 2 (fun τ y => ENNReal.ofReal K *
          IIIa.youngDerivNorm ν (m : ℂ) T j (R * Real.sqrt ν) τ y) :=
        IIIa.ltauLq_mono _ _ (by norm_num) hpt
    _ = ENNReal.ofReal K * IIIa.ltauLq (2 * c / R) 2
          (IIIa.youngDerivNorm ν (m : ℂ) T j (R * Real.sqrt ν)) :=
        IIIa.ltauLq_const_mul _ _ (by norm_num) _ ENNReal.ofReal_ne_top _
    _ ≤ _ := mul_le_mul_of_nonneg_left hY' zero_le

end UnforcedLeray.Short.PartIIIb.Concrete
end
