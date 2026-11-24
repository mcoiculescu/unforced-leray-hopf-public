import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_7

/-!
# `BgRbL4` from `short-bg:strong` and the `L^{11/4}` bound of `Dw` (task `PartIII-b:C/ward/13/7/2`)

Source of record: `the November 2 reference manuscript` (73 pages).
`r_b = w = corr z` (2505-2524). `IIb.StrongRegularity` (2525-2562) gives the pointwise sup bounds on
`w` and `Dw` and `w ∈ L^{11/4}`. The `L^{11/4}` bound of `Dw` (2538-2562, 2608-2610) is not in Lean
and is isolated as `CorrDerivLbgp`. The interpolation `L^{11/4} ∩ L^∞ ⊂ L^4` is proved here
(`interpL4`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`D w ∈ C_per L^{11/4}` at the ball levels** (source 2538-2562 and 2608-2610: the `L^{11/4}`
bound of the derivative of the correction `w = r_b`: "`Dw ∈ Y_p` is already known", with
`Y_p`-norm of `w` in `W^{1,Y_p}` bounded by the right side of `short-bg:result`).
Analytic input not yet in Lean. -/
def CorrDerivLbgp : Prop :=
  AtBallLevels fun _ _ rb _ => ∃ C : ℝ, ∀ τ : ℝ,
    eLpNorm (fun y => fderiv ℝ (rb τ) y) (ENNReal.ofReal UnforcedLeray.Short.IIb.bgp) volume ≤
      ENNReal.ofReal C

/-- Interpolation `‖f‖_4^4 ≤ K^{5/4} ‖f‖_{11/4}^{11/4}` for pointwise bounded fields, with the
constant depending only on the sup bound and the `L^{11/4}` bound (source 2608-2610). -/
theorem interpL4 {E : Type*} [NormedAddCommGroup E] (K C0 : ℝ) :
    ∃ C : ℝ, ∀ f : Space → E, (∀ y, ‖f y‖ ≤ K) →
      eLpNorm f (ENNReal.ofReal UnforcedLeray.Short.IIb.bgp) volume ≤ ENNReal.ofReal C0 →
        eLpNorm f 4 volume ≤ ENNReal.ofReal C := by
  set B : ℝ≥0∞ := (ENNReal.ofReal K ^ ((5 : ℝ) / 4) * ENNReal.ofReal C0 ^ ((11 : ℝ) / 4)) ^
    ((1 : ℝ) / 4) with hB
  have hBt : B ≠ ⊤ := by
    rw [hB]
    refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top ?_ ?_)
    · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  refine ⟨B.toReal, fun f hK hL => ?_⟩
  rw [ENNReal.ofReal_toReal hBt]
  have hp : UnforcedLeray.Short.IIb.bgp = 11 / 4 := rfl
  have h4 : eLpNorm f 4 volume = (∫⁻ y, ‖f y‖ₑ ^ (4 : ℝ) ∂volume) ^ ((1 : ℝ) / 4) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
  have hq : (∫⁻ y, ‖f y‖ₑ ^ ((11 : ℝ) / 4) ∂volume) =
      eLpNorm f (ENNReal.ofReal (11 / 4)) volume ^ ((11 : ℝ) / 4) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) (by simp)]
    rw [ENNReal.toReal_ofReal (by norm_num), ← ENNReal.rpow_mul]
    norm_num
  rw [h4, hB]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  calc ∫⁻ y, ‖f y‖ₑ ^ (4 : ℝ) ∂volume
      ≤ ∫⁻ y, ENNReal.ofReal K ^ ((5 : ℝ) / 4) * ‖f y‖ₑ ^ ((11 : ℝ) / 4) ∂volume := by
        refine lintegral_mono fun y => ?_
        have h1 : ‖f y‖ₑ ≤ ENNReal.ofReal K := by
          rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hK y)
        calc ‖f y‖ₑ ^ (4 : ℝ) = ‖f y‖ₑ ^ ((5 : ℝ) / 4) * ‖f y‖ₑ ^ ((11 : ℝ) / 4) := by
              rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num
          _ ≤ _ := by gcongr
    _ = ENNReal.ofReal K ^ ((5 : ℝ) / 4) * ∫⁻ y, ‖f y‖ₑ ^ ((11 : ℝ) / 4) ∂volume := by
        refine lintegral_const_mul' _ _ ?_
        exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    _ ≤ _ := by
        rw [hq]
        gcongr
        rw [hp] at hL
        exact hL

/-- **`BgRbL4` from `short-bg:strong`, and the `L^{11/4}` bound of `Dw`.** -/
theorem bgRbL4_of (hSR : UnforcedLeray.Short.IIb.StrongRegularity) (hD : CorrDerivLbgp) :
    BgRbL4 := by
  have hS : AtBallLevels fun _ _ rb _ =>
      (∃ K : ℝ, ∀ τ y, ‖rb τ y‖ ≤ K ∧ ‖fderiv ℝ (rb τ) y‖ ≤ K) ∧
      (∃ C : ℝ, ∀ τ, eLpNorm (rb τ) (ENNReal.ofReal UnforcedLeray.Short.IIb.bgp) volume ≤
        ENNReal.ofReal C) := by
    intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
    obtain ⟨C₂, k₂, ν₀, hC₂, hν₀, h⟩ := hSR Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
    refine ⟨ν₀, hν₀, ?_⟩
    rintro p d hreg hν hSig' hq' V rb pres ⟨z, hz, hV, hrb, hball⟩ -
    obtain ⟨-, -, -, -, hcorr, hL, -⟩ := h p d hreg hν hSig' hq' z hz hball
    subst hrb
    exact ⟨⟨_, fun τ y => hcorr τ y⟩, ⟨_, hL⟩⟩
  refine AtBallLevels.mono' (AtBallLevels.and hS hD) ?_
  intro p V rb pres hU ⟨⟨⟨K, hK⟩, ⟨C0, hC0⟩⟩, ⟨C1, hC1⟩⟩
  obtain ⟨Ca, hCa⟩ := interpL4 (E := Space) K C0
  obtain ⟨Cb, hCb⟩ := interpL4 (E := Space →L[ℝ] Space) K C1
  refine ⟨|Ca| + |Cb|, fun τ => ⟨?_, ?_⟩⟩
  · exact (hCa (rb τ) (fun y => (hK τ y).1) (hC0 τ)).trans
      (ENNReal.ofReal_le_ofReal (by linarith [le_abs_self Ca, abs_nonneg Cb]))
  · exact (hCb (fun y => fderiv ℝ (rb τ) y) (fun y => (hK τ y).2) (hC1 τ)).trans
      (ENNReal.ofReal_le_ofReal (by linarith [le_abs_self Cb, abs_nonneg Ca]))

end UnforcedLeray.Short.PartIIIb.Concrete
