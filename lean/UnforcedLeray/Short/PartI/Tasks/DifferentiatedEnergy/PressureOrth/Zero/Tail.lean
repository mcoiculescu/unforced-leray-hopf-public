import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureOrth.Zero.IBP.Cut

/-!


Source: `the November 2 reference manuscript`, line 346.
Statement: `Sub/PartI_T08_6_2.lean`, `EtaCutTail`. Helpers: `IBP/Cut.lean`.

With `|deriv (etaCut R)| ≤ K / R`, the derivative vanishes for `|η| > 2R`, and `|P| ≤ M`,
Cauchy-Schwarz on the slab (`AM-GM` with weight `√R`) gives
`|∫_cell (etaCut R)' P f₁| ≤ K M (4c + ‖f₁‖²₂) / (2 √R)`, which tends to `0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- The quantitative tail bound on one cell. -/
theorem etaCut_tail_bound {c R K M : ℝ} (hc : 0 ≤ c) (hR : 0 < R)
    (hK : ∀ x : ℝ, ‖deriv (⇑etaBump) x‖ ≤ K) {P F : Plane → ℝ} (hPM : ∀ z, |P z| ≤ M)
    (hF : MemLp F 2 (Cyl.cellμ c)) :
    ‖∫ z in Cyl.cell c, deriv (etaCut R) z.2 * (P z * F z)‖
      ≤ K * M * (4 * c + ∫ z in Cyl.cell c, F z ^ 2) / (2 * Real.sqrt R) := by
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hPM 0)
  obtain ⟨s, hs_eq⟩ : ∃ s, Real.sqrt R = s := ⟨_, rfl⟩
  have hs : 0 < s := hs_eq ▸ Real.sqrt_pos.2 hR
  have hss : s * s = R := hs_eq ▸ Real.mul_self_sqrt hR.le
  rw [hs_eq]
  -- the slab measure
  have hμS : (volume.restrict (Cyl.cell c)).real (slab R) = c * (4 * R) := by
    rw [measureReal_def, Measure.restrict_apply (measurableSet_slab R), Set.inter_comm,
      volume_cell_inter_slab hc hR.le, ENNReal.toReal_ofReal (mul_nonneg hc (by linarith))]
  have hfin : Cyl.cellμ c (slab R) ≠ ⊤ := by
    rw [Cyl.cellμ, Measure.restrict_apply (measurableSet_slab R), Set.inter_comm,
      volume_cell_inter_slab hc hR.le]
    exact ENNReal.ofReal_ne_top
  have hB0 : 0 ≤ K * R⁻¹ * M * s / 2 := by
    have := mul_nonneg (mul_nonneg (mul_nonneg hK0 (inv_nonneg.2 hR.le)) hM0) hs.le
    linarith
  have hA0 : 0 ≤ K * R⁻¹ * M * (1 / s) / 2 := by
    have := mul_nonneg (mul_nonneg (mul_nonneg hK0 (inv_nonneg.2 hR.le)) hM0)
      (one_div_nonneg.2 hs.le)
    linarith
  -- integrable pieces
  have hIA : Integrable ((slab R).indicator (fun _ : Plane => K * R⁻¹ * M * (1 / s) / 2))
      (Cyl.cellμ c) :=
    (integrable_indicator_iff (measurableSet_slab R)).2 (integrableOn_const hfin)
  have hIB : Integrable ((slab R).indicator (fun z : Plane => K * R⁻¹ * M * s / 2 * F z ^ 2))
      (Cyl.cellμ c) :=
    ((hF.integrable_sq).const_mul (K * R⁻¹ * M * s / 2)).indicator (measurableSet_slab R)
  -- pointwise bound
  have hpt : ∀ z : Plane, ‖deriv (etaCut R) z.2 * (P z * F z)‖ ≤
      (slab R).indicator (fun _ : Plane => K * R⁻¹ * M * (1 / s) / 2) z
        + (slab R).indicator (fun z : Plane => K * R⁻¹ * M * s / 2 * F z ^ 2) z := by
    intro z
    by_cases hz : z ∈ slab R
    · simp only [indicator_of_mem hz]
      have hF1 : |F z| ≤ (1 / s + s * F z ^ 2) / 2 := by
        rw [← sq_abs (F z)]
        have key : 0 ≤ 1 + s ^ 2 * |F z| ^ 2 - 2 * |F z| * s := by
          nlinarith [sq_nonneg (s * |F z| - 1)]
        have e : (1 / s + s * |F z| ^ 2) / 2 - |F z|
            = (1 + s ^ 2 * |F z| ^ 2 - 2 * |F z| * s) / (2 * s) := by
          field_simp <;> ring
        have : 0 ≤ (1 + s ^ 2 * |F z| ^ 2 - 2 * |F z| * s) / (2 * s) :=
          div_nonneg key (by linarith)
        linarith
      have hd := etaCut_deriv_abs_le hR hK z.2
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |deriv (etaCut R) z.2| * (|P z| * |F z|)
          ≤ (K * R⁻¹) * (M * ((1 / s + s * F z ^ 2) / 2)) :=
            mul_le_mul hd (mul_le_mul (hPM z) hF1 (abs_nonneg _) hM0)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hK0 (inv_nonneg.2 hR.le))
        _ = K * R⁻¹ * M * (1 / s) / 2 + K * R⁻¹ * M * s / 2 * F z ^ 2 := by ring
    · simp only [indicator_of_notMem hz]
      have hz' : 2 * R < |z.2| := by
        simp only [slab, mem_setOf_eq, not_le] at hz
        exact hz
      rw [etaCut_deriv_eq_zero hR hz']
      simp
  -- the integral of the pointwise bound
  have hmono : ∫ z in Cyl.cell c, ‖deriv (etaCut R) z.2 * (P z * F z)‖ ≤
      ∫ z in Cyl.cell c, ((slab R).indicator (fun _ : Plane => K * R⁻¹ * M * (1 / s) / 2) z
        + (slab R).indicator (fun z : Plane => K * R⁻¹ * M * s / 2 * F z ^ 2) z) :=
    integral_mono_of_nonneg (Eventually.of_forall fun z => norm_nonneg _) (hIA.add hIB)
      (Eventually.of_forall hpt)
  have hI1 : ∫ z in Cyl.cell c, (slab R).indicator (fun _ : Plane => K * R⁻¹ * M * (1 / s) / 2) z
      = c * (4 * R) * (K * R⁻¹ * M * (1 / s) / 2) := by
    rw [integral_indicator (measurableSet_slab R), setIntegral_const, smul_eq_mul, hμS]
  have hI2 : ∫ z in Cyl.cell c, (slab R).indicator
      (fun z : Plane => K * R⁻¹ * M * s / 2 * F z ^ 2) z
      ≤ K * R⁻¹ * M * s / 2 * ∫ z in Cyl.cell c, F z ^ 2 := by
    calc ∫ z in Cyl.cell c, (slab R).indicator
          (fun z : Plane => K * R⁻¹ * M * s / 2 * F z ^ 2) z
        ≤ ∫ z in Cyl.cell c, K * R⁻¹ * M * s / 2 * F z ^ 2 :=
          integral_mono_of_nonneg
            (Eventually.of_forall fun z => indicator_nonneg (fun x _ =>
              mul_nonneg hB0 (sq_nonneg _)) z)
            ((hF.integrable_sq).const_mul _)
            (Eventually.of_forall fun z => indicator_le_self' (fun x _ =>
              mul_nonneg hB0 (sq_nonneg _)) z)
      _ = K * R⁻¹ * M * s / 2 * ∫ z in Cyl.cell c, F z ^ 2 := integral_const_mul _ _
  have hsplit : ∫ z in Cyl.cell c, ((slab R).indicator (fun _ : Plane => K * R⁻¹ * M * (1 / s) / 2) z
        + (slab R).indicator (fun z : Plane => K * R⁻¹ * M * s / 2 * F z ^ 2) z)
      = (∫ z in Cyl.cell c, (slab R).indicator (fun _ : Plane => K * R⁻¹ * M * (1 / s) / 2) z)
        + ∫ z in Cyl.cell c, (slab R).indicator
          (fun z : Plane => K * R⁻¹ * M * s / 2 * F z ^ 2) z :=
    integral_add hIA hIB
  have hs0 : s ≠ 0 := hs.ne'
  calc ‖∫ z in Cyl.cell c, deriv (etaCut R) z.2 * (P z * F z)‖
      ≤ ∫ z in Cyl.cell c, ‖deriv (etaCut R) z.2 * (P z * F z)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ _ := hmono
    _ = _ := hsplit
    _ ≤ c * (4 * R) * (K * R⁻¹ * M * (1 / s) / 2)
          + K * R⁻¹ * M * s / 2 * ∫ z in Cyl.cell c, F z ^ 2 := by
        rw [hI1]
        linarith [hI2]
    _ = K * M * (4 * c + ∫ z in Cyl.cell c, F z ^ 2) / (2 * s) := by
        rw [← hss]
        field_simp <;> ring

/-- **Leaf 3** (the cutoff-derivative term vanishes, source line 346). -/
theorem etaCutTail_proof : UnforcedLeray.Short.PartI.EtaCutTail := by
  intro c f P hyp
  obtain ⟨hc, ⟨hfc, hfper, hL2⟩, hdiv, hP, hper, ⟨M, hM⟩, hL2P⟩ := hyp
  obtain ⟨K, hK⟩ := etaBump_deriv_bound
  have hF : MemLp (fun z : Plane => f z 1) 2 (Cyl.cellμ c) := hL2 [] 1
  have hbound : ∀ R : ℝ, 0 < R →
      ‖∫ z in Cyl.cell c, deriv (etaCut R) z.2 * (P z * f z 1)‖
        ≤ (K * M * (4 * c + ∫ z in Cyl.cell c, f z 1 ^ 2) / 2) * (1 / Real.sqrt R) := by
    intro R hR
    have h := etaCut_tail_bound hc.le hR hK hM hF
    calc _ ≤ K * M * (4 * c + ∫ z in Cyl.cell c, f z 1 ^ 2) / (2 * Real.sqrt R) := h
      _ = _ := by ring
  have hlim : Tendsto (fun R : ℝ => (K * M * (4 * c + ∫ z in Cyl.cell c, f z 1 ^ 2) / 2)
      * (1 / Real.sqrt R)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => 1 / Real.sqrt R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
    simpa using h1.const_mul (K * M * (4 * c + ∫ z in Cyl.cell c, f z 1 ^ 2) / 2)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with R hR
  exact hbound R hR

end UnforcedLeray.Short.PartI
