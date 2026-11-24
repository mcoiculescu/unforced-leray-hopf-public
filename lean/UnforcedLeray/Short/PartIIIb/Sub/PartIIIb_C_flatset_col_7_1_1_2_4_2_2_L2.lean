import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_2
import UnforcedLeray.Units.B0224.PlaneHeat
import UnforcedLeray.Lib.Cylinder.CellModes

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Gaussian (Euc gaussKernel)

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- `|a|² + |b|²` in `ℝ≥0∞`. -/
theorem ofReal_sq_add_sq_eq (a b : ℂ) :
    ENNReal.ofReal (‖a‖ ^ 2 + ‖b‖ ^ 2) = ‖a‖ₑ ^ 2 + ‖b‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_add (by positivity) (by positivity), UnforcedLeray.Cyl.ofReal_norm_sq,
    UnforcedLeray.Cyl.ofReal_norm_sq]

theorem sfcHeatJensen : SFCHeatJensen := by
  intro c θ hc hθ h₀ h₁ hh₀ hh₁ hper₀ hper₁
  rcases le_or_gt θ 0 with hθle | hθpos
  · simp only [UnforcedLeray.B0224.planeHeat_of_nonpos hθle, le_refl]
  -- the cell in the statement is the library cell
  have hcell : Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ) = UnforcedLeray.Cyl.cell c := by
    unfold UnforcedLeray.Cyl.cell
    rw [neg_div]
  rw [hcell]
  -- the periodic function `φ = |h₀|² + |h₁|²`
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ × ℝ → ℝ≥0∞, φ = fun z => ‖h₀ z‖ₑ ^ 2 + ‖h₁ z‖ₑ ^ 2 := ⟨_, rfl⟩
  have hφm : Measurable φ := by
    rw [hφ]
    exact ((hh₀.measurable.enorm).pow_const 2).add ((hh₁.measurable.enorm).pow_const 2)
  have hφper : UnforcedLeray.Cyl.IsPeriodic c φ := by
    rintro ⟨q, η⟩
    simp only [hφ, hper₀, hper₁]
  -- pointwise Gaussian Jensen for one continuous function
  have hJ : ∀ (h : ℝ × ℝ → ℂ), Continuous h → ∀ x : ℝ × ℝ,
      ‖UnforcedLeray.B0224.planeHeat θ h x‖ₑ ^ 2 ≤
        ∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) * ‖h (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2 := by
    intro h hh x
    rw [UnforcedLeray.B0224.planeHeat_of_pos hθpos]
    exact UnforcedLeray.B0224.enorm_integral_gauss_sq_le hθpos
      (g := fun y => h (x - UnforcedLeray.B0224.planeι y))
      ((hh.comp (continuous_const.sub UnforcedLeray.B0224.continuous_planeι)).aestronglyMeasurable)
  -- Jensen for the pair, integrated against the Gaussian
  have hpt : ∀ x : ℝ × ℝ,
      ‖UnforcedLeray.B0224.planeHeat θ h₀ x‖ₑ ^ 2 + ‖UnforcedLeray.B0224.planeHeat θ h₁ x‖ₑ ^ 2 ≤
        ∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) * φ (x - UnforcedLeray.B0224.planeι y) := by
    intro x
    have m0 : Measurable fun y : Euc 2 =>
        ENNReal.ofReal (gaussKernel 2 θ y) * ‖h₀ (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2 :=
      (UnforcedLeray.B0224.measurable_ofReal_gauss θ).mul
        ((((hh₀.comp (continuous_const.sub UnforcedLeray.B0224.continuous_planeι)).measurable).enorm).pow_const 2)
    have e : ∀ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) * φ (x - UnforcedLeray.B0224.planeι y) =
        ENNReal.ofReal (gaussKernel 2 θ y) * ‖h₀ (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2 +
          ENNReal.ofReal (gaussKernel 2 θ y) * ‖h₁ (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2 := by
      intro y
      simp only [hφ, mul_add]
    calc ‖UnforcedLeray.B0224.planeHeat θ h₀ x‖ₑ ^ 2 + ‖UnforcedLeray.B0224.planeHeat θ h₁ x‖ₑ ^ 2
        ≤ (∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) * ‖h₀ (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2) +
          ∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) * ‖h₁ (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2 :=
          add_le_add (hJ h₀ hh₀ x) (hJ h₁ hh₁ x)
      _ = ∫⁻ y : Euc 2, (ENNReal.ofReal (gaussKernel 2 θ y) * ‖h₀ (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2 +
          ENNReal.ofReal (gaussKernel 2 θ y) * ‖h₁ (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2) :=
          (lintegral_add_left m0 _).symm
      _ = ∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) * φ (x - UnforcedLeray.B0224.planeι y) :=
          lintegral_congr fun y => (e y).symm
  -- Tonelli and the periodic cell shift: the Gaussian average preserves the cell mass of `φ`
  have hmain : ∫⁻ x in UnforcedLeray.Cyl.cell c,
      ∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) * φ (x - UnforcedLeray.B0224.planeι y) =
        ∫⁻ x in UnforcedLeray.Cyl.cell c, φ x := by
    have hm : Measurable fun q : (ℝ × ℝ) × Euc 2 =>
        ENNReal.ofReal (gaussKernel 2 θ q.2) * φ (q.1 - UnforcedLeray.B0224.planeι q.2) :=
      ((UnforcedLeray.B0224.measurable_ofReal_gauss θ).comp measurable_snd).mul
        (hφm.comp (measurable_fst.sub (UnforcedLeray.B0224.measurable_planeι.comp measurable_snd)))
    rw [lintegral_lintegral_swap hm.aemeasurable]
    calc ∫⁻ y : Euc 2, ∫⁻ x in UnforcedLeray.Cyl.cell c,
          ENNReal.ofReal (gaussKernel 2 θ y) * φ (x - UnforcedLeray.B0224.planeι y)
        = ∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) * ∫⁻ x in UnforcedLeray.Cyl.cell c, φ x := by
          refine lintegral_congr fun y => ?_
          have hmy : Measurable fun x : ℝ × ℝ => φ (x - UnforcedLeray.B0224.planeι y) :=
            hφm.comp (measurable_id.sub_const _)
          rw [lintegral_const_mul _ hmy]
          congr 1
          simpa [sub_eq_add_neg] using
            UnforcedLeray.Cyl.lintegral_cell_comp_add hc hφper (-UnforcedLeray.B0224.planeι y)
      _ = (∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y)) * ∫⁻ x in UnforcedLeray.Cyl.cell c, φ x :=
          lintegral_mul_const _ (UnforcedLeray.B0224.measurable_ofReal_gauss θ)
      _ = ∫⁻ x in UnforcedLeray.Cyl.cell c, φ x := by
          rw [UnforcedLeray.B0224.lintegral_ofReal_gauss hθpos, one_mul]
  calc ∫⁻ x in UnforcedLeray.Cyl.cell c,
        ENNReal.ofReal (‖UnforcedLeray.B0224.planeHeat θ h₀ x‖ ^ 2 +
          ‖UnforcedLeray.B0224.planeHeat θ h₁ x‖ ^ 2)
      = ∫⁻ x in UnforcedLeray.Cyl.cell c,
          (‖UnforcedLeray.B0224.planeHeat θ h₀ x‖ₑ ^ 2 + ‖UnforcedLeray.B0224.planeHeat θ h₁ x‖ₑ ^ 2) :=
        lintegral_congr fun x => ofReal_sq_add_sq_eq _ _
    _ ≤ ∫⁻ x in UnforcedLeray.Cyl.cell c,
          ∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) * φ (x - UnforcedLeray.B0224.planeι y) :=
        lintegral_mono fun x => hpt x
    _ = ∫⁻ x in UnforcedLeray.Cyl.cell c, φ x := hmain
    _ = ∫⁻ x in UnforcedLeray.Cyl.cell c, ENNReal.ofReal (‖h₀ x‖ ^ 2 + ‖h₁ x‖ ^ 2) :=
        lintegral_congr fun x => by rw [ofReal_sq_add_sq_eq, hφ]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
