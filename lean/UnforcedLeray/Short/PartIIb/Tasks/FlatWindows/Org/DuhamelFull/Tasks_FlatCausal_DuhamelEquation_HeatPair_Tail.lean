import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatPair.Tail
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_T12_7_4

/-!
# Part II-b, task `PartII-b:T12/7/4/3` (`dfe_deqhpTail`): Gaussian envelope of the smoothed test

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
Let `R₀` bound the support of `Ψ_i` (sup norm on `ℝ × ℝ`), `θ = ν(s-t) ∈ (0, ν]`, and
`E = max 0 (‖z‖ - R₀)`. Pointwise, `|Ψ(s, z-w)_i| ≤ M exp((|w|² - E²)/(8θ))` (the support of
`Ψ(s, z-w)` forces `‖w‖ ≥ E`), and `K_θ(w) exp(|w|²/(8θ)) = 2 · flatHeatKernel(2θ) w`, so
`|deqSmooth| ≤ 2M exp(-E²/(8θ)) ≤ 2M exp(-E²/(8ν))`. Take `C = 2M`, `R = R₀`, `a = 1/(8ν)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Exponent identity behind the Gaussian tail (`θ > 0`, `Q` the squared norm of `w`):
`(4πθ)⁻¹ e^{-Q/(4θ)} e^{(Q-d²)/(8θ)} = 2 · (4π·2θ)⁻¹ e^{-Q/(4·2θ)} · e^{-d²/(8θ)}`. -/
private theorem dfe_deqhpt_key (θ Q d : ℝ) (hθ : 0 < θ) :
    (4 * Real.pi * θ)⁻¹ * Real.exp (-Q / (4 * θ)) * Real.exp ((Q - d ^ 2) / (8 * θ)) =
      2 * ((4 * Real.pi * (2 * θ))⁻¹ * Real.exp (-Q / (4 * (2 * θ)))) *
        Real.exp (-d ^ 2 / (8 * θ)) := by
  have hne : θ ≠ 0 := hθ.ne'
  have h1 : Real.exp (-Q / (4 * θ)) * Real.exp ((Q - d ^ 2) / (8 * θ)) =
      Real.exp (-Q / (4 * (2 * θ))) * Real.exp (-d ^ 2 / (8 * θ)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have h2 : (4 * Real.pi * θ)⁻¹ = 2 * (4 * Real.pi * (2 * θ))⁻¹ := by
    first | (field_simp; done) | (field_simp; ring)
  calc (4 * Real.pi * θ)⁻¹ * Real.exp (-Q / (4 * θ)) * Real.exp ((Q - d ^ 2) / (8 * θ))
      = (4 * Real.pi * θ)⁻¹ * (Real.exp (-Q / (4 * θ)) * Real.exp ((Q - d ^ 2) / (8 * θ))) := by
        ring
    _ = 2 * (4 * Real.pi * (2 * θ))⁻¹ *
          (Real.exp (-Q / (4 * (2 * θ))) * Real.exp (-d ^ 2 / (8 * θ))) := by
        rw [h1, h2]
    _ = 2 * ((4 * Real.pi * (2 * θ))⁻¹ * Real.exp (-Q / (4 * (2 * θ)))) *
          Real.exp (-d ^ 2 / (8 * θ)) := by
        ring

/-- A vector of norm at least `d ≥ 0` has `d² ≤ w₁² + w₂²`. -/
private theorem dfe_deqhpt_sq_le (d : ℝ) (w : ℝ × ℝ) (hd : 0 ≤ d) (hdw : d ≤ ‖w‖) :
    d ^ 2 ≤ w.1 ^ 2 + w.2 ^ 2 := by
  rw [Prod.norm_def] at hdw
  rcases le_max_iff.mp hdw with h | h
  · rw [Real.norm_eq_abs] at h
    nlinarith [sq_abs w.1, sq_nonneg w.2, abs_nonneg w.1, mul_le_mul h h hd (abs_nonneg _)]
  · rw [Real.norm_eq_abs] at h
    nlinarith [sq_abs w.2, sq_nonneg w.1, abs_nonneg w.2, mul_le_mul h h hd (abs_nonneg _)]

theorem dfe_deqhpTail : dfe_DeqhpTail := by
  intro ν t hν ht Ψ hΨ i
  have hgc : Continuous (fun x : Coord => Ψ x i) := (hΨ.smooth i).smooth.continuous
  obtain ⟨M, hM⟩ := hgc.bounded_above_of_compact_support (hΨ.smooth i).compact
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hK : IsCompact (tsupport (fun x : Coord => Ψ x i)) := (hΨ.smooth i).compact
  obtain ⟨R0, hR0⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Coord)).mp hK.isBounded
  -- the test vanishes when the spatial part of its argument is beyond `R0`
  have hsupp : ∀ (s : ℝ) (y : ℝ × ℝ), R0 < ‖y‖ → Ψ (s, y) i = 0 := by
    intro s y hy
    by_contra hne
    have hmem : ((s, y) : Coord) ∈ tsupport (fun x : Coord => Ψ x i) :=
      subset_tsupport _ (Function.mem_support.mpr hne)
    have h1 := hR0 hmem
    rw [mem_closedBall_zero_iff] at h1
    have h2 : ‖y‖ ≤ ‖((s, y) : Coord)‖ := norm_snd_le (s, y)
    linarith
  refine ⟨2 * M, R0, 1 / (8 * ν), one_div_pos.mpr (by linarith), ?_⟩
  intro s hts hst1 z
  have hθ : 0 < ν * (s - t) := mul_pos hν (by linarith)
  have hθν : ν * (s - t) ≤ ν := mul_le_of_le_one_right hν.le (by linarith)
  have h2θ : 0 < 2 * (ν * (s - t)) := by linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = max 0 (‖z‖ - R0) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; exact le_max_left _ _
  -- pointwise majorant of the integrand
  have hpt : ∀ w : ℝ × ℝ,
      |flatHeatKernel (ν * (s - t)) w * Ψ (s, z - w) i| ≤
        2 * M * Real.exp (-E ^ 2 / (8 * (ν * (s - t)))) *
          flatHeatKernel (2 * (ν * (s - t))) w := by
    intro w
    have hKnn : 0 ≤ flatHeatKernel (ν * (s - t)) w := by
      rw [flatHeat_kernel_eq hθ]; exact UnforcedLeray.B0284.heatKernel2_nonneg hθ w
    have hKnn2 : 0 ≤ flatHeatKernel (2 * (ν * (s - t))) w := by
      rw [flatHeat_kernel_eq h2θ]; exact UnforcedLeray.B0284.heatKernel2_nonneg h2θ w
    rw [abs_mul, abs_of_nonneg hKnn]
    by_cases hz : R0 < ‖z - w‖
    · rw [hsupp s (z - w) hz, abs_zero, mul_zero]
      have : 0 ≤ 2 * M * Real.exp (-E ^ 2 / (8 * (ν * (s - t)))) := by
        have := Real.exp_pos (-E ^ 2 / (8 * (ν * (s - t))))
        positivity
      exact mul_nonneg this hKnn2
    · push_neg at hz
      have hEw : E ≤ ‖w‖ := by
        rw [hE]
        refine max_le (norm_nonneg w) ?_
        linarith [norm_sub_norm_le z w]
      have hQ := dfe_deqhpt_sq_le E w hE0 hEw
      have hΨ' : |Ψ (s, z - w) i| ≤ M := by
        simpa [Real.norm_eq_abs] using hM (s, z - w)
      have hexp : 1 ≤ Real.exp ((w.1 ^ 2 + w.2 ^ 2 - E ^ 2) / (8 * (ν * (s - t)))) :=
        Real.one_le_exp (div_nonneg (by linarith) (by linarith))
      have hMnn : 0 ≤ M := hM0
      calc flatHeatKernel (ν * (s - t)) w * |Ψ (s, z - w) i|
          ≤ flatHeatKernel (ν * (s - t)) w * M :=
            mul_le_mul_of_nonneg_left hΨ' hKnn
        _ ≤ flatHeatKernel (ν * (s - t)) w * M *
              Real.exp ((w.1 ^ 2 + w.2 ^ 2 - E ^ 2) / (8 * (ν * (s - t)))) := by
            refine le_mul_of_one_le_right (mul_nonneg hKnn hMnn) hexp
        _ = 2 * M * Real.exp (-E ^ 2 / (8 * (ν * (s - t)))) *
              flatHeatKernel (2 * (ν * (s - t))) w := by
            unfold flatHeatKernel
            have key := dfe_deqhpt_key (ν * (s - t)) (w.1 ^ 2 + w.2 ^ 2) E hθ
            calc (4 * Real.pi * (ν * (s - t)))⁻¹ * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * (ν * (s - t)))) *
                  M * Real.exp ((w.1 ^ 2 + w.2 ^ 2 - E ^ 2) / (8 * (ν * (s - t))))
                = M * ((4 * Real.pi * (ν * (s - t)))⁻¹ * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * (ν * (s - t)))) *
                  Real.exp ((w.1 ^ 2 + w.2 ^ 2 - E ^ 2) / (8 * (ν * (s - t))))) := by ring
              _ = M * (2 * ((4 * Real.pi * (2 * (ν * (s - t))))⁻¹ *
                    Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * (2 * (ν * (s - t))))))) *
                    Real.exp (-E ^ 2 / (8 * (ν * (s - t)))) := by
                rw [key]; ring
              _ = 2 * M * Real.exp (-E ^ 2 / (8 * (ν * (s - t)))) *
                    ((4 * Real.pi * (2 * (ν * (s - t))))⁻¹ *
                      Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * (2 * (ν * (s - t)))))) := by ring
  -- integrate the majorant
  have hfh : Integrable (fun w : ℝ × ℝ => flatHeatKernel (2 * (ν * (s - t))) w) :=
    (UnforcedLeray.B0284.integrable_heatKernel2 h2θ).congr
      (ae_of_all _ fun w => (flatHeat_kernel_eq h2θ w).symm)
  have hint : Integrable (fun w : ℝ × ℝ =>
      2 * M * Real.exp (-E ^ 2 / (8 * (ν * (s - t)))) *
        flatHeatKernel (2 * (ν * (s - t))) w) :=
    hfh.const_mul _
  have hI : ∫ w : ℝ × ℝ, flatHeatKernel (2 * (ν * (s - t))) w = 1 := by
    simp only [flatHeat_kernel_eq h2θ]
    exact UnforcedLeray.B0284.integral_heatKernel2 h2θ
  have hbound : ‖deqSmooth ν Ψ i t s z‖ ≤ 2 * M * Real.exp (-E ^ 2 / (8 * (ν * (s - t)))) := by
    unfold deqSmooth
    calc ‖∫ w : ℝ × ℝ, flatHeatKernel (ν * (s - t)) w * Ψ (s, z - w) i‖
        ≤ ∫ w : ℝ × ℝ, 2 * M * Real.exp (-E ^ 2 / (8 * (ν * (s - t)))) *
            flatHeatKernel (2 * (ν * (s - t))) w :=
          norm_integral_le_of_norm_le hint
            (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hpt w)
      _ = 2 * M * Real.exp (-E ^ 2 / (8 * (ν * (s - t)))) := by
          rw [integral_const_mul, hI, mul_one]
  -- compare the exponential with the one in the statement
  have hexp2 : Real.exp (-E ^ 2 / (8 * (ν * (s - t)))) ≤
      Real.exp (-(1 / (8 * ν)) * E ^ 2) := by
    apply Real.exp_le_exp.mpr
    have h8 : E ^ 2 / (8 * ν) ≤ E ^ 2 / (8 * (ν * (s - t))) :=
      div_le_div_of_nonneg_left (sq_nonneg E) (by linarith) (by linarith)
    have e1 : -E ^ 2 / (8 * (ν * (s - t))) = -(E ^ 2 / (8 * (ν * (s - t)))) := neg_div _ _
    have e2 : -(1 / (8 * ν)) * E ^ 2 = -(E ^ 2 / (8 * ν)) := by ring
    rw [e1, e2]
    linarith
  rw [← hE]
  calc |deqSmooth ν Ψ i t s z|
      = ‖deqSmooth ν Ψ i t s z‖ := (Real.norm_eq_abs _).symm
    _ ≤ 2 * M * Real.exp (-E ^ 2 / (8 * (ν * (s - t)))) := hbound
    _ ≤ 2 * M * Real.exp (-(1 / (8 * ν)) * E ^ 2) :=
        mul_le_mul_of_nonneg_left hexp2 (by linarith)

end UnforcedLeray.Short.IIb

end
