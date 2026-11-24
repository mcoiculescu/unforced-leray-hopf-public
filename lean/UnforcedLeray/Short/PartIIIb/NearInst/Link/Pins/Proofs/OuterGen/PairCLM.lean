import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2_3

/-!
# `OuterPairCLM` (task `PartIII-b:C/near/pins/3/4/2/3/1`)

Source `the November 2 reference manuscript` (lines 1339-1362, 3346-3352):
`F ↦ ⟪Ψ, F⟫` is a continuous `ℂ`-linear functional on `X = L²(dx dτ; ℂ³)`.
The bound `‖⟪Ψ,F⟫‖ ≤ ‖dotL‖ ‖Ψ‖ ‖F‖` is Cauchy-Schwarz in `L²`, linearity comes from
`outerPair_add`, `outerPair_smul` (`Sub/PartIII-b_C_near_pins_3_4_2.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.PhaseSpace

/-- The squared `L²`-norm as a real power integral (`p = 2` in the Hölder bound). -/
theorem lp_sq_norm_rpow {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure α} (F : Lp E 2 μ) :
    ∫ x, ‖F x‖ ^ (2 : ℝ) ∂μ = ‖F‖ ^ 2 := by
  symm
  rw [Lp.norm_def]
  simp only [Real.rpow_two]
  have hm2 : AEStronglyMeasurable (fun x => ‖F x‖ ^ 2) μ :=
    (Lp.aestronglyMeasurable F).norm.pow 2
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => by positivity) hm2,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ← ENNReal.toReal_pow]
  congr 1
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp only [ENNReal.toReal_ofNat, Nat.cast_ofNat]
  norm_num

theorem sqrt_sq_rpow_half (x : ℝ) (hx : 0 ≤ x) : (x ^ 2) ^ ((1 : ℝ) / 2) = x := by
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hx]

/-- `‖⟪Q, F⟫‖ ≤ ‖dotL‖ ‖Q‖ ‖F‖` in `X` (pointwise `dotL` bound, then Cauchy-Schwarz). -/
theorem outerPair_norm_le {P : ℝ} [Fact (0 < P)]
    (Q F : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P) :
    ‖outerPair Q F‖ ≤ ‖dotL‖ * (‖Q‖ * ‖F‖) := by
  have hQ := (Lp.memLp Q).norm
  have hF := (Lp.memLp F).norm
  have hint : Integrable (fun z => ‖dotL‖ * (‖Q z‖ * ‖F z‖)) volume :=
    (hQ.integrable_mul hF).const_mul ‖dotL‖
  have hHol := integral_mul_norm_le_Lp_mul_Lq (μ := volume) (f := ⇑Q) (g := ⇑F)
    Real.HolderConjugate.two_two (by simpa using Lp.memLp Q) (by simpa using Lp.memLp F)
  have key : ∫ z, ‖Q z‖ * ‖F z‖ ≤ ‖Q‖ * ‖F‖ := by
    refine hHol.trans (le_of_eq ?_)
    rw [lp_sq_norm_rpow Q, lp_sq_norm_rpow F, sqrt_sq_rpow_half _ (norm_nonneg _),
      sqrt_sq_rpow_half _ (norm_nonneg _)]
  calc ‖outerPair Q F‖ ≤ ∫ z, ‖dotL‖ * (‖Q z‖ * ‖F z‖) := by
        unfold outerPair
        refine norm_integral_le_of_norm_le hint ?_
        refine Filter.Eventually.of_forall fun z => ?_
        calc ‖dotL (Q z) (F z)‖ ≤ ‖dotL (Q z)‖ * ‖F z‖ := (dotL (Q z)).le_opNorm _
          _ ≤ (‖dotL‖ * ‖Q z‖) * ‖F z‖ :=
              mul_le_mul_of_nonneg_right (dotL.le_opNorm _) (norm_nonneg _)
          _ = ‖dotL‖ * (‖Q z‖ * ‖F z‖) := by ring
    _ = ‖dotL‖ * ∫ z, ‖Q z‖ * ‖F z‖ := by rw [integral_const_mul]
    _ ≤ ‖dotL‖ * (‖Q‖ * ‖F‖) := mul_le_mul_of_nonneg_left key (norm_nonneg dotL)

theorem outerPairCLM : OuterPairCLM := by
  intro P _ Ψ
  let L : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P →ₗ[ℂ] ℂ :=
    { toFun := fun F => outerPair Ψ F
      map_add' := fun a b => outerPair_add Ψ a b
      map_smul' := fun k a => by
        show outerPair Ψ (k • a) = (RingHom.id ℂ) k • outerPair Ψ a
        rw [outerPair_smul, RingHom.id_apply, smul_eq_mul] }
  refine ⟨LinearMap.mkContinuous L (‖dotL‖ * ‖Ψ‖) fun F => ?_, fun F => rfl⟩
  calc ‖L F‖ = ‖outerPair Ψ F‖ := rfl
    _ ≤ ‖dotL‖ * (‖Ψ‖ * ‖F‖) := outerPair_norm_le Ψ F
    _ = (‖dotL‖ * ‖Ψ‖) * ‖F‖ := by ring

end UnforcedLeray.Short.PartIIIb.NearInst
