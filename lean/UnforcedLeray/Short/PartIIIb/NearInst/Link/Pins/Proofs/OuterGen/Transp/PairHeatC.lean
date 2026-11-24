import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2_3_2

/-!
# `OuterPairHeatC` (task `PartIII-b:C/near/pins/3/4/2/3/2/3`)

Source `the November 2 reference manuscript` lines 3350-3352.
Symmetry of the spatial heat semigroup for the bilinear pairing `outerPair`.  Proof at the level
of `L²`-valued Bochner integrals (no Fubini on the product): `e^{θΔ}u = ∫ G_θ(y) τ_y u dy`
(`Heat.heatLp_eq_integral`), the pairing is a continuous linear functional so it commutes with
the integral, `⟪τ_y w, Ψ⟫ = ⟪w, τ_{-y} Ψ⟫` (translation invariance of Lebesgue measure), and
`G_θ` is even.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Gaussian

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.B0223 UnforcedLeray.PhaseSpace

theorem outerPair_comm {P : ℝ} [Fact (0 < P)] (Ψ F : XC P) : outerPair Ψ F = outerPair F Ψ := by
  unfold outerPair
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [dotL_apply]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem outerPair_translate {P : ℝ} [Fact (0 < P)] (y : Euc 3) (w Ψ : XC P) :
    outerPair (Heat.translateLp (ιx P) continuous_ιx y w) Ψ =
      outerPair w (Heat.translateLp (ιx P) continuous_ιx (-y) Ψ) := by
  unfold outerPair
  have h1 : ∫ z, dotL ((Heat.translateLp (ιx P) continuous_ιx y w) z) (Ψ z) =
      ∫ z, dotL (w (z - ιx P y)) (Ψ z) := by
    refine integral_congr_ae ?_
    filter_upwards [Heat.coeFn_translateLp (ιx P) continuous_ιx y w] with z hz
    rw [hz]
  have h2 : ∫ z, dotL (w z) ((Heat.translateLp (ιx P) continuous_ιx (-y) Ψ) z) =
      ∫ z, dotL (w z) (Ψ (z - ιx P (-y))) := by
    refine integral_congr_ae ?_
    filter_upwards [Heat.coeFn_translateLp (ιx P) continuous_ιx (-y) Ψ] with z hz
    rw [hz]
  rw [h1, h2, ← integral_add_right_eq_self (fun z => dotL (w (z - ιx P y)) (Ψ z)) (ιx P y)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [add_sub_cancel_right, map_neg, sub_neg_eq_add]

theorem outerPairHeatC : OuterPairHeatC := by
  intro P _ θ Ψ w
  by_cases hθ : 0 < θ
  · have hI : ∀ u : XC P, Integrable (fun y : Euc 3 => gaussKernel 3 θ y •
        Heat.translateLp (ιx P) continuous_ιx y u) :=
      fun u => Heat.integrable_gauss_translateLp (ιx P) continuous_ιx ENNReal.ofNat_ne_top hθ u
    have hrep : ∀ u : XC P, heatC (E := SpaceC) θ u =
        ∫ y : Euc 3, gaussKernel 3 θ y • Heat.translateLp (ιx P) continuous_ιx y u :=
      fun u => Heat.heatLp_eq_integral (ιx P) continuous_ιx ENNReal.ofNat_ne_top hθ u
    have hL : outerPair Ψ (heatC (E := SpaceC) θ w) =
        ∫ y : Euc 3, gaussKernel 3 θ y • outerPair (Heat.translateLp (ιx P) continuous_ιx y w) Ψ := by
      rw [outerPair_comm, hrep w]
      have := ((outerPairL Ψ).restrictScalars ℝ).integral_comp_comm (hI w)
      calc outerPair (∫ y : Euc 3, gaussKernel 3 θ y • Heat.translateLp (ιx P) continuous_ιx y w) Ψ
          = ((outerPairL Ψ).restrictScalars ℝ)
              (∫ y : Euc 3, gaussKernel 3 θ y • Heat.translateLp (ιx P) continuous_ιx y w) := rfl
        _ = ∫ y : Euc 3, ((outerPairL Ψ).restrictScalars ℝ)
              (gaussKernel 3 θ y • Heat.translateLp (ιx P) continuous_ιx y w) := this.symm
        _ = _ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only [map_smul]
          rfl
    have hR : outerPair (heatC (E := SpaceC) θ Ψ) w =
        ∫ y : Euc 3, gaussKernel 3 θ y • outerPair (Heat.translateLp (ιx P) continuous_ιx y Ψ) w := by
      rw [hrep Ψ]
      have := ((outerPairL w).restrictScalars ℝ).integral_comp_comm (hI Ψ)
      calc outerPair (∫ y : Euc 3, gaussKernel 3 θ y • Heat.translateLp (ιx P) continuous_ιx y Ψ) w
          = ((outerPairL w).restrictScalars ℝ)
              (∫ y : Euc 3, gaussKernel 3 θ y • Heat.translateLp (ιx P) continuous_ιx y Ψ) := rfl
        _ = ∫ y : Euc 3, ((outerPairL w).restrictScalars ℝ)
              (gaussKernel 3 θ y • Heat.translateLp (ιx P) continuous_ιx y Ψ) := this.symm
        _ = _ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only [map_smul]
          rfl
    rw [hL, hR]
    set f : Euc 3 → ℂ := fun y => gaussKernel 3 θ y •
      outerPair (Heat.translateLp (ιx P) continuous_ιx y Ψ) w with hf
    have hfe : ∀ y : Euc 3, gaussKernel 3 θ y • outerPair (Heat.translateLp (ιx P) continuous_ιx y w) Ψ
        = f (-y) := by
      intro y
      simp only [hf]
      rw [outerPair_translate, outerPair_comm w]
      have : gaussKernel 3 θ (-y) = gaussKernel 3 θ y := by
        simp [gaussKernel]
      rw [this]
    simp_rw [hfe]
    exact integral_neg_eq_self f volume
  · rw [heatC_of_nonpos (not_lt.mp hθ), heatC_of_nonpos (not_lt.mp hθ)]

end UnforcedLeray.Short.PartIIIb.NearInst
