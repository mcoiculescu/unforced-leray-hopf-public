import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3.BandVanish

/-!
# Pairing bound for `R` on a box (source 3511-3514, 4464-4467)

`R(s,φ) = s^μ(⟨g,φ⟩ + ∫ω w - ∫(b·∇E)φ)`, `w = νΔφ+v·∇φ`: the curl clause gives
`⟨g,φ⟩ = ∫ f₀∂_ηφ - f₁∂_qφ`, `IsBiotSavart` gives `∫ω w = ∫ b₀∂_ηw - b₁∂_qw`, and the last term is
bounded by `K² dB_R`.  Everything lives on the box `cell ∩ {|η| ≤ R}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open UnforcedLeray.Short.IIIa (flowIntegrand)

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem vtvRPairBound : VtvRPairBound := by
  intro ν c μ tr ω g b G f H R s hs hfs φ hφ hw hz K hφK hφ1 hw1 hE
  have hBS := H.2.2.2.2.1 s hs
  have hcurl := H.2.2.2.2.2.2.1 s hs φ hφ
  have hω := H.2.2.2.2.2.2.2.2 s hs _ hw
  have hb : ∀ i : Fin 2, IntegrableOn (fun x => b (s, x) i) (vtvBox c R) := fun i =>
    integrableOn_vtvBox_of_memLp R (hBS.1 i)
  have hwz := vtvFlowTest_vanish tr s hz
  set E := UnforcedLeray.B0238.Ec tr s with hEdef
  set Q : ℝ × ℝ → ℂ := fun x =>
    (b (s, x) 0 * (B0579.pd 0 E x : ℂ) + b (s, x) 1 * (B0579.pd 1 E x : ℂ)) * (φ x : ℂ) with hQ
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hφK 0)
  -- the `Q` term
  have hQz : ∀ x ∈ B0579.cell c \ vtvBox c R, Q x = 0 := fun x hx => by
    have hx2 : R < |x.2| := by
      by_contra hcon
      exact hx.2 ⟨hx.1, not_lt.1 hcon⟩
    simp [hQ, hz x hx2]
  have hbm : ∀ i : Fin 2, Measurable fun x => b (s, x) i := fun i =>
    (H.2.2.2.1.measurable i).comp measurable_prodMk_left
  have hpdE : ∀ j, Measurable (B0579.pd j E) := fun j =>
    measurable_fderiv_apply_const ℝ E (B0579.dir j)
  have hQm : Measurable Q :=
    (((hbm 0).mul (Complex.measurable_ofReal.comp (hpdE 0))).add
      ((hbm 1).mul (Complex.measurable_ofReal.comp (hpdE 1)))).mul
      (Complex.measurable_ofReal.comp hφ.continuous.measurable)
  have hQbd : ∀ x, ‖Q x‖ ≤ K * K * (‖b (s, x) 0‖ + ‖b (s, x) 1‖) := fun x => by
    have e0 := hE x 0
    have e1 := hE x 1
    have p := hφK x
    calc ‖Q x‖ = ‖b (s, x) 0 * (B0579.pd 0 E x : ℂ) + b (s, x) 1 * (B0579.pd 1 E x : ℂ)‖ *
          |φ x| := by simp [hQ]
      _ ≤ (‖b (s, x) 0‖ * |B0579.pd 0 E x| + ‖b (s, x) 1‖ * |B0579.pd 1 E x|) * K := by
          gcongr
          refine (norm_add_le _ _).trans ?_
          simp
      _ ≤ (‖b (s, x) 0‖ * K + ‖b (s, x) 1‖ * K) * K := by gcongr
      _ = K * K * (‖b (s, x) 0‖ + ‖b (s, x) 1‖) := by ring
  have hBint : IntegrableOn (fun x => K * K * (‖b (s, x) 0‖ + ‖b (s, x) 1‖)) (vtvBox c R) :=
    (((hb 0).norm).add (hb 1).norm).const_mul (K * K)
  have hQint : IntegrableOn Q (vtvBox c R) :=
    Integrable.mono' hBint hQm.aestronglyMeasurable (Eventually.of_forall hQbd)
  have hQcell : IntegrableOn Q (B0579.cell c) :=
    hQint.of_forall_sdiff_eq_zero (B0579.measurableSet_cell c) hQz
  have hC : ‖∫ x in B0579.cell c, Q x‖ ≤ K * K * vtvDB c R b s := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (B0579.measurableSet_cell c)
      (vtvBox_subset_cell c R) hQz]
    unfold vtvDB
    rw [← integral_const_mul]
    exact norm_integral_le_of_norm_le hBint (Eventually.of_forall hQbd)
  have hA := pair_le c R (fun x => f (s, x) 0) (fun x => f (s, x) 1) (hfs 0) (hfs 1) φ hz K hφ1
  have hB := pair_le c R (fun x => b (s, x) 0) (fun x => b (s, x) 1) (hb 0) (hb 1)
    (vtvFlowTest tr s φ) hwz K hw1
  have hfl : ∫ x in B0579.cell c, flowIntegrand tr (ω s) (fun x => b (s, x)) s φ x =
      (∫ x in B0579.cell c, ω s x * (vtvFlowTest tr s φ x : ℂ)) - ∫ x in B0579.cell c, Q x := by
    rw [← integral_sub hω hQcell]
    rfl
  have hBdb : 0 ≤ vtvDB c R b s :=
    integral_nonneg fun x => add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hFdf : 0 ≤ vtvDF c R f s :=
    integral_nonneg fun x => add_nonneg (norm_nonneg _) (norm_nonneg _)
  unfold vtvR
  rw [norm_mul, hfl, hcurl, hBS.2.2 _ hw]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc _ ≤ _ + (_ + _) := (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
    _ ≤ K * vtvDF c R f s + (K * vtvDB c R b s + K * K * vtvDB c R b s) :=
        add_le_add hA (add_le_add hB hC)
    _ ≤ (K + K * K) * (vtvDB c R b s + vtvDF c R f s) := by
        nlinarith [mul_nonneg hK0 hBdb, mul_nonneg hK0 hFdf, mul_nonneg (mul_nonneg hK0 hK0) hBdb,
          mul_nonneg (mul_nonneg hK0 hK0) hFdf]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
