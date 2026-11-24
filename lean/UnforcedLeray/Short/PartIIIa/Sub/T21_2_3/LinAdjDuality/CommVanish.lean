import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutProps

/-!
# `PartIII-a:T21/2/3/1/12`: the cutoff commutator vanishes (SP 3074-3075)

`ladComm R ρ → 0` as `R → ∞`, for `ρ ∈ (t, s)`: the commutator is bounded by `(B/R)` times a fixed
integrable majorant `∫_cell |w|(|φ| + |∂_0φ| + |∂_1φ|)`, by `LadCutProps` (`|∂χ_R| ≤ K/R`,
`|Δχ_R| ≤ K/R²`) and the train velocity bound on the cell.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace CommVanishAux

/-- Integrability on the cell of `|F|·|G|` for `F ∈ X_{m,c}` and `G ∈ X_{-m,c}` (complex valued),
from the real Cauchy-Schwarz/Hölder pairing `B0579.integrableOn_mul_neg`. -/
lemma integrableOn_cell_norm_mul (c m : ℝ) {F G : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (B0579.cellMeasure c m)) (hG : MemLp G 2 (B0579.cellMeasure c (-m))) :
    IntegrableOn (fun x => ‖F x‖ * ‖G x‖) (B0579.cell c) := by
  have hF' : MemLp (fun x => ‖F x‖) 2 (B0579.cellMeasure c m) := hF.norm
  have hG' : MemLp (fun x => ‖G x‖) 2 (B0579.cellMeasure c (-m)) := hG.norm
  have h := B0579.integrableOn_mul_neg c m (hF'.toLp (fun x => ‖F x‖))
    (hG'.toLp (fun x => ‖G x‖))
  refine h.congr_fun_ae ?_
  have h1 : ∀ᵐ x ∂(B0579.cellMeasure c m), (hF'.toLp (fun x => ‖F x‖)) x = ‖F x‖ :=
    hF'.coeFn_toLp
  have h2 : ∀ᵐ x ∂(B0579.cellMeasure c (-m)), (hG'.toLp (fun x => ‖G x‖)) x = ‖G x‖ :=
    hG'.coeFn_toLp
  have h1' := (B0579.ac_cellMeasure c m).ae_le h1
  have h2' := ((B0579.ac_cellMeasure c m).trans (B0579.cellMeasure_ac_cellMeasure c m (-m)) |>.ae_le
    h2)
  filter_upwards [h1', h2'] with x hx1 hx2
  simp only [hx1, hx2]

/-- Pointwise bound for the commutator integrand, for `R > 0`. -/
lemma comm_pointwise (ν C K R p0 p1 L vv : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hq : 0 ≤ R⁻¹)
    (hp0 : |p0| ≤ K * R⁻¹) (hp1 : |p1| ≤ K * R⁻¹) (hL : |L| ≤ K * R⁻¹)
    (hvv : |vv| ≤ 2 * C * K * R⁻¹) (D0 D1 φ0 : ℂ) :
    ‖(ν : ℂ) * (2 * ((p0 : ℂ) * D0 + (p1 : ℂ) * D1) + (L : ℂ) * φ0) + (vv : ℂ) * φ0‖ ≤
      (3 * |ν| * K + 2 * C * K) * R⁻¹ * (‖φ0‖ + ‖D0‖ + ‖D1‖) := by
  have hA : 0 ≤ ‖D0‖ := norm_nonneg _
  have hB : 0 ≤ ‖D1‖ := norm_nonneg _
  have hP : 0 ≤ ‖φ0‖ := norm_nonneg _
  have hX : ‖(p0 : ℂ) * D0 + (p1 : ℂ) * D1‖ ≤ |p0| * ‖D0‖ + |p1| * ‖D1‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hY : ‖(2 : ℂ) * ((p0 : ℂ) * D0 + (p1 : ℂ) * D1) + (L : ℂ) * φ0‖ ≤
      2 * (|p0| * ‖D0‖ + |p1| * ‖D1‖) + |L| * ‖φ0‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, h2]
      exact mul_le_mul_of_nonneg_left hX (by norm_num)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hZ : ‖(ν : ℂ) * (2 * ((p0 : ℂ) * D0 + (p1 : ℂ) * D1) + (L : ℂ) * φ0) + (vv : ℂ) * φ0‖ ≤
      |ν| * (2 * (|p0| * ‖D0‖ + |p1| * ‖D1‖) + |L| * ‖φ0‖) + |vv| * ‖φ0‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hY (abs_nonneg _)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine hZ.trans ?_
  have e1 : |ν| * (2 * (|p0| * ‖D0‖ + |p1| * ‖D1‖) + |L| * ‖φ0‖) ≤
      |ν| * (2 * ((K * R⁻¹) * ‖D0‖ + (K * R⁻¹) * ‖D1‖) + (K * R⁻¹) * ‖φ0‖) := by
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have a0 : |p0| * ‖D0‖ ≤ (K * R⁻¹) * ‖D0‖ := mul_le_mul_of_nonneg_right hp0 hA
    have a1 : |p1| * ‖D1‖ ≤ (K * R⁻¹) * ‖D1‖ := mul_le_mul_of_nonneg_right hp1 hB
    have a2 : |L| * ‖φ0‖ ≤ (K * R⁻¹) * ‖φ0‖ := mul_le_mul_of_nonneg_right hL hP
    linarith
  have e2 : |vv| * ‖φ0‖ ≤ (2 * C * K * R⁻¹) * ‖φ0‖ := mul_le_mul_of_nonneg_right hvv hP
  have hq' : 0 ≤ R⁻¹ * (|ν| * K * (2 * ‖φ0‖ + ‖D0‖ + ‖D1‖) + 2 * C * K * (‖D0‖ + ‖D1‖)) := by
    apply mul_nonneg hq
    have := abs_nonneg ν
    have hKC : 0 ≤ C * K := mul_nonneg hC hK
    have hn : 0 ≤ |ν| * K := mul_nonneg this hK
    nlinarith
  nlinarith [hq', e1, e2]

end CommVanishAux

open CommVanishAux in
/-- **The commutator vanishes** (SP 3074-3075; `LadCommVanish m`). -/
theorem ladCommVanish (m : ℝ) : LadCommVanish m := by
  intro ν c tr t s g φ f w u hν hc ht hts hB hφ hw ρ hρ
  obtain ⟨K, hK0, hK⟩ := ladCutProps
  have hρS : ρ ∈ Icc (0 : ℝ) s := ⟨ht.trans hρ.1.le, hρ.2.le⟩
  obtain ⟨C, hCB⟩ := hB s (ht.trans hts.le)
  have hx0 : ((0 : ℝ), (0 : ℝ)) ∈ B0579.cell c :=
    ⟨⟨by linarith, by linarith⟩, Set.mem_univ _⟩
  have hC0 : 0 ≤ C := (abs_nonneg _).trans ((hCB ρ hρS _ hx0).1 0)
  have hI : IntegrableOn (fun x => ‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
      ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖) (B0579.cell c) := by
    have h1 := integrableOn_cell_norm_mul c m (hw.memX ρ hρ.1.le)
      (hφ.memX ρ ⟨hρ.1.le, hρ.2.le⟩)
    have h2 := integrableOn_cell_norm_mul c m (hw.memX ρ hρ.1.le)
      (hφ.memH1 ρ ⟨hρ.1.le, hρ.2⟩ 0)
    have h3 := integrableOn_cell_norm_mul c m (hw.memX ρ hρ.1.le)
      (hφ.memH1 ρ ⟨hρ.1.le, hρ.2⟩ 1)
    exact (h1.add h2).add h3
  set I := ∫ x in B0579.cell c, (‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
      ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖) with hIdef
  have hbound : ∀ R : ℝ, 1 ≤ R → ‖ladComm tr w φ R ρ‖ ≤
      (3 * |ν| * K + 2 * C * K) * R⁻¹ * I := by
    intro R hR1
    have hR0 : 0 < R := by linarith
    have hq : 0 ≤ R⁻¹ := inv_nonneg.2 hR0.le
    have hq1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1
    have hpt : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
        ‖w ρ x * ((ν : ℂ) * (2 * ((B0579.pd 0 (ladCut R) x : ℂ) * pdCx 0 (φ ρ) x +
          (B0579.pd 1 (ladCut R) x : ℂ) * pdCx 1 (φ ρ) x) + (lapP (ladCut R) x : ℂ) * φ ρ x) +
          ((tr.v ρ x 0 * B0579.pd 0 (ladCut R) x + tr.v ρ x 1 * B0579.pd 1 (ladCut R) x : ℝ) : ℂ) *
          φ ρ x)‖ ≤ (3 * |ν| * K + 2 * C * K) * R⁻¹ *
          (‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖ + ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖) := by
      rw [ae_restrict_iff' (B0579.measurableSet_cell c)]
      refine Eventually.of_forall fun x hx => ?_
      obtain ⟨hv, -⟩ := hCB ρ hρS x hx
      have hpd := hK R hR0
      have hp0 : |B0579.pd 0 (ladCut R) x| ≤ K * R⁻¹ := by
        have := hpd.2.2.2.2.1 x 0
        rwa [div_eq_mul_inv] at this
      have hp1 : |B0579.pd 1 (ladCut R) x| ≤ K * R⁻¹ := by
        have := hpd.2.2.2.2.1 x 1
        rwa [div_eq_mul_inv] at this
      have hL : |lapP (ladCut R) x| ≤ K * R⁻¹ := by
        have h := hpd.2.2.2.2.2 x
        have e : K / R ^ 2 = K * R⁻¹ * R⁻¹ := by ring
        rw [e] at h
        exact h.trans (mul_le_of_le_one_right (mul_nonneg hK0 hq) hq1)
      have hvv : |tr.v ρ x 0 * B0579.pd 0 (ladCut R) x + tr.v ρ x 1 * B0579.pd 1 (ladCut R) x| ≤
          2 * C * K * R⁻¹ := by
        calc |tr.v ρ x 0 * B0579.pd 0 (ladCut R) x + tr.v ρ x 1 * B0579.pd 1 (ladCut R) x|
            ≤ |tr.v ρ x 0 * B0579.pd 0 (ladCut R) x| + |tr.v ρ x 1 * B0579.pd 1 (ladCut R) x| :=
              abs_add_le _ _
          _ = |tr.v ρ x 0| * |B0579.pd 0 (ladCut R) x| + |tr.v ρ x 1| * |B0579.pd 1 (ladCut R) x| := by
              rw [abs_mul, abs_mul]
          _ ≤ C * (K * R⁻¹) + C * (K * R⁻¹) :=
              add_le_add (mul_le_mul (hv 0) hp0 (abs_nonneg _) hC0)
                (mul_le_mul (hv 1) hp1 (abs_nonneg _) hC0)
          _ = 2 * C * K * R⁻¹ := by ring
      have hZ := comm_pointwise ν C K R _ _ _ _ hK0 hC0 hq hp0 hp1 hL hvv
        (pdCx 0 (φ ρ) x) (pdCx 1 (φ ρ) x) (φ ρ x)
      rw [norm_mul]
      calc ‖w ρ x‖ * ‖(ν : ℂ) * (2 * ((B0579.pd 0 (ladCut R) x : ℂ) * pdCx 0 (φ ρ) x +
            (B0579.pd 1 (ladCut R) x : ℂ) * pdCx 1 (φ ρ) x) + (lapP (ladCut R) x : ℂ) * φ ρ x) +
            ((tr.v ρ x 0 * B0579.pd 0 (ladCut R) x + tr.v ρ x 1 * B0579.pd 1 (ladCut R) x : ℝ) : ℂ) *
            φ ρ x‖
          ≤ ‖w ρ x‖ * ((3 * |ν| * K + 2 * C * K) * R⁻¹ *
              (‖φ ρ x‖ + ‖pdCx 0 (φ ρ) x‖ + ‖pdCx 1 (φ ρ) x‖)) :=
            mul_le_mul_of_nonneg_left hZ (norm_nonneg _)
        _ = (3 * |ν| * K + 2 * C * K) * R⁻¹ *
            (‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖ + ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖) := by
            ring
    unfold ladComm
    calc ‖∫ x in B0579.cell c, w ρ x * ((ν : ℂ) * (2 * ((B0579.pd 0 (ladCut R) x : ℂ) *
            pdCx 0 (φ ρ) x + (B0579.pd 1 (ladCut R) x : ℂ) * pdCx 1 (φ ρ) x) +
            (lapP (ladCut R) x : ℂ) * φ ρ x) +
            ((tr.v ρ x 0 * B0579.pd 0 (ladCut R) x + tr.v ρ x 1 * B0579.pd 1 (ladCut R) x : ℝ) : ℂ) *
            φ ρ x)‖
        ≤ ∫ x in B0579.cell c, (3 * |ν| * K + 2 * C * K) * R⁻¹ *
            (‖w ρ x‖ * ‖φ ρ x‖ + ‖w ρ x‖ * ‖pdCx 0 (φ ρ) x‖ + ‖w ρ x‖ * ‖pdCx 1 (φ ρ) x‖) :=
          norm_integral_le_of_norm_le (hI.const_mul _) hpt
      _ = (3 * |ν| * K + 2 * C * K) * R⁻¹ * I := integral_const_mul _ _
  have hT : Tendsto (fun R : ℝ => (3 * |ν| * K + 2 * C * K) * R⁻¹ * I) atTop (𝓝 0) := by
    have h0 : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have := (h0.const_mul (3 * |ν| * K + 2 * C * K)).mul_const I
    simpa using this
  refine squeeze_zero_norm' ?_ hT
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR using hbound R hR

end UnforcedLeray.Short.IIIa
