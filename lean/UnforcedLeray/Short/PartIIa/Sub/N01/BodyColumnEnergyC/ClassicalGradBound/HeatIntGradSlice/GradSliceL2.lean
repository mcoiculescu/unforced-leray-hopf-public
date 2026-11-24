import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3_2_1_2
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.ClassicalGradBound.PlaneHeatGradSmoothing
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatSliceBounds

/-!
# `PartII-a:N01/9/1/3/3/2/1/2/2`: `GradSliceL2`

Source `the November 2 reference manuscript`
lines 1684-1689, 3373-3383.  Per-`σ` smoothing bound for the slice gradient: `planeHeatGradSmoothing`
applied to `f = heatSlice c F σ · i` (`C¹`, `c`-periodic in the first coordinate, bounded with
bounded derivative by `heatSliceBounds`), and `heatSlice c F σ w = σ⁻¹ • F (σ, w)` for the cell
`L²` norm.  The constant is `max C0 0`, which dominates `C0` and makes the statement independent
of the sign of `C0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem gradSliceL2 : UnforcedLeray.Short.PartIIa.N01.HIGS.GradSliceL2 := by
  obtain ⟨C0, hC0⟩ := UnforcedLeray.Short.PartIIa.N01.planeHeatGradSmoothing
  refine ⟨max C0 0, ?_⟩
  intro c ν hc hν F hF s hs i j σ hσ
  have hθ : 0 < ν * (s - σ) := mul_pos hν (sub_pos.2 hσ.2)
  obtain ⟨-, hcd, M, hM0, hM1⟩ := UnforcedLeray.Short.PartIIa.N01.heatSliceBounds c hc F hF
  obtain ⟨-, hFper, -⟩ := hF
  -- the periodized slice is `σ⁻¹ • F (σ, w)`
  have hsl : ∀ w : ℝ × ℝ, UnforcedLeray.Short.PartIIa.N01.heatSlice c F σ w = σ⁻¹ • F (σ, w) := by
    intro w
    unfold UnforcedLeray.Short.PartIIa.N01.heatSlice UnforcedLeray.B0220.periodize
    have hq : UnforcedLeray.B0220.QPeriodic c
        (fun q : UnforcedLeray.B0220.Profile => q.1⁻¹ • F q) := by
      intro p
      show p.1⁻¹ • F (p.1, p.2.1 + c, p.2.2) = p.1⁻¹ • F p
      rw [hFper p]
    exact UnforcedLeray.B0220.periodic_reduceIoc_eq _ hq σ w.1 w.2
  -- the slice is `c`-periodic in the first coordinate
  have hfC : ContDiff ℝ 1 (fun z : ℝ × ℝ => UnforcedLeray.Short.PartIIa.N01.heatSlice c F σ z i) := by
    have h := (hcd i).comp
      ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ × ℝ => σ)).prodMk
        (contDiff_id : ContDiff ℝ 1 (fun z : ℝ × ℝ => z)))
    exact h
  have hfper : ∀ x : ℝ × ℝ,
      UnforcedLeray.Short.PartIIa.N01.heatSlice c F σ (x.1 + c, x.2) i =
        UnforcedLeray.Short.PartIIa.N01.heatSlice c F σ x i := by
    intro x
    rw [hsl, hsl]
    have h1 : F (σ, (x.1 + c, x.2)) = F (σ, x) := hFper (σ, x)
    rw [h1]
  -- norm of the slice in terms of `F`
  have hpt : ∀ x : ℝ × ℝ,
      ‖UnforcedLeray.Short.PartIIa.N01.heatSlice c F σ x i‖ₑ =
        ENNReal.ofReal σ⁻¹ * ‖F (σ, x) i‖ₑ := by
    intro x
    rw [hsl x, PiLp.smul_apply, enorm_smul, Real.enorm_eq_ofReal_abs,
      abs_of_pos (inv_pos.2 hσ.1)]
  have hint : ∫⁻ x in UnforcedLeray.B0579.cell c,
      ‖UnforcedLeray.Short.PartIIa.N01.heatSlice c F σ x i‖ₑ ^ 2 =
        ENNReal.ofReal σ⁻¹ ^ 2 * ∫⁻ x in UnforcedLeray.B0579.cell c, ‖F (σ, x) i‖ₑ ^ 2 := by
    rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
    exact lintegral_congr fun x => by rw [hpt x, mul_pow]
  have t0 : 0 ≤ (ν * (s - σ)) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hθ.le _
  have hmono : ENNReal.ofReal (C0 * (ν * (s - σ)) ^ (-(1 / 2 : ℝ))) ≤
      ENNReal.ofReal (max C0 0 * (ν * (s - σ)) ^ (-(1 / 2 : ℝ))) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) t0)
  have hb : (∫⁻ x in UnforcedLeray.B0579.cell c,
        UnforcedLeray.Short.PartIIa.N01.HIGS.gradE c ν F s i j σ x ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (C0 * (ν * (s - σ)) ^ (-(1 / 2 : ℝ))) *
        (∫⁻ x in UnforcedLeray.B0579.cell c,
          ‖UnforcedLeray.Short.PartIIa.N01.heatSlice c F σ x i‖ₑ ^ 2) ^ (1 / 2 : ℝ) :=
    hC0 (ν * (s - σ)) c hθ hc (fun z : ℝ × ℝ => UnforcedLeray.Short.PartIIa.N01.heatSlice c F σ z i)
      hfC hfper ⟨M, fun x => hM0 i σ x⟩ ⟨M, fun x => hM1 i σ x⟩ j
  rw [hint, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    UnforcedLeray.Short.PartIIa.N01.HIGS.sq_half_eq] at hb
  exact hb.trans (mul_le_mul' hmono le_rfl)
