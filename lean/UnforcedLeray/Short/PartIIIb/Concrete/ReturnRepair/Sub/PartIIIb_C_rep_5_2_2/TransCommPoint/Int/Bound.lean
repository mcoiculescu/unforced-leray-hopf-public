import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Int.Phase

/-!
# Uniform pointwise bound of the dilation integral for a separated source

Source `the November 2 reference manuscript` 3604-3647 (`sep:kernel`,
`sep:young` at `p = b = 2`), 4181-4192.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `L²` norm of the unit gap kernel of order `j`. -/
def tcKc (j : ℕ) : ℝ≥0∞ := (∫⁻ x : Space, IIIa.sepKd j 1 x ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-- The phase constant (periodic dilation sum with `c = -1/2`). -/
def tcMph (P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / 2) * ((1 - ENNReal.ofReal (Real.exp (-((-(1 / 2 : ℝ) + 1) / 2) * P)))⁻¹ *
    (ENNReal.ofReal P * IIIa.ltauLq P 2 (IIIa.srcNorm T)))

theorem tcKc_ne_top (j : ℕ) : tcKc j ≠ ⊤ :=
  ENNReal.rpow_ne_top_of_nonneg (by norm_num) (tcd_kerL2_ne_top j)

theorem tcd_Kj {j : ℕ} {D : ℝ} (hD : 0 < D) :
    (ENNReal.ofReal (D ^ (3 - (4 + (j : ℝ)) * 2)) *
        ∫⁻ x : Space, IIIa.sepKd j 1 x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (D ^ (-(5 / 2 : ℝ) - j)) * tcKc j := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hD.le _) (by norm_num),
    ← Real.rpow_mul hD.le]
  unfold tcKc
  congr 3
  ring

theorem tcd_srcNorm_meas {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} {P rOut : ℝ}
    (hT : IIIa.IsSepSource P rOut T) : Measurable (Function.uncurry (IIIa.srcNorm T)) := by
  unfold IIIa.srcNorm IIIa.tensorNorm
  refine ENNReal.measurable_ofReal.comp ?_
  refine Real.continuous_sqrt.measurable.comp ?_
  refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
  exact (hT.measurable i j).pow_const 2

theorem tcMph_ne_top {P : ℝ} (hP : 0 < P) {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hM : SepMoment P T) : tcMph P T ≠ ⊤ := by
  unfold tcMph
  have hlt : ENNReal.ofReal (Real.exp (-((-(1 / 2 : ℝ) + 1) / 2) * P)) < 1 := by
    rw [← ENNReal.ofReal_one]
    refine (ENNReal.ofReal_lt_ofReal_iff one_pos).2 ?_
    have : Real.exp (-((-(1 / 2 : ℝ) + 1) / 2) * P) < Real.exp 0 :=
      Real.exp_lt_exp.2 (by nlinarith)
    simpa using this
  have h1 : (1 : ℝ≥0∞) - ENNReal.ofReal (Real.exp (-((-(1 / 2 : ℝ) + 1) / 2) * P)) ≠ 0 :=
    (tsub_pos_of_lt hlt).ne'
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 h1)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM.ne))

/-- **Uniform bound of the order-`j` dilation integral** (every phase, every receiver, gap `D`). -/
theorem tcd_sepDom_bound {P rOut a : ℝ} (hP : 0 < P) (ha : 1 ≤ a)
    {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (hT : IIIa.IsSepSource P rOut T) (j : ℕ)
    {D : ℝ} (hD : 0 < D) (τ : ℝ) (y : Space) :
    IIIa.sepDom a j D (IIIa.srcNorm T) τ y ≤
      ENNReal.ofReal (D ^ (-(5 / 2 : ℝ) - j)) * tcKc j * tcMph P T := by
  have hgm := tcd_srcNorm_meas hT
  have h1 := sepDom_anti_a' ha j D (IIIa.srcNorm T) τ y
  have h2 := tcd_sepDom_le 1 j D hD (IIIa.srcNorm T) hgm τ y
  rw [tcd_Kj hD] at h2
  set G : ℝ → ℝ≥0∞ := fun s => lqNorm 2 (IIIa.srcNorm T s) with hG
  have hGm : Measurable G := by
    simp only [hG]
    unfold lqNorm
    have : Measurable fun s => ∫⁻ y, IIIa.srcNorm T s y ^ (2 : ℝ) := by
      have h1 : Measurable (fun x : ℝ × Space => IIIa.srcNorm T x.1 x.2 ^ (2 : ℝ)) :=
        hgm.pow_const _
      exact h1.lintegral_prod_right'
    exact this.pow_const _
  have hGper : ∀ s, G (s + P) = G s := by
    intro s
    have : IIIa.srcNorm T (s + P) = IIIa.srcNorm T s := by
      funext z; simp only [IIIa.srcNorm, hT.periodic]
    simp only [hG, this]
  have h3 := tcd_dilSum (c := -(1 / 2 : ℝ)) (by norm_num) hP hGm hGper τ
  have h4 : IIIa.ltauAt P G = IIIa.ltauLq P 2 (IIIa.srcNorm T) :=
    ltauAt_lqNorm_eq P 2 (IIIa.srcNorm T)
  rw [h4] at h3
  have h5 : (1 : ℝ) - 3 / 2 = -(1 / 2 : ℝ) := by norm_num
  rw [h5] at h2
  calc IIIa.sepDom a j D (IIIa.srcNorm T) τ y ≤ IIIa.sepDom 1 j D (IIIa.srcNorm T) τ y := h1
    _ ≤ _ := h2
    _ ≤ (ENNReal.ofReal (D ^ (-(5 / 2 : ℝ) - j)) * tcKc j) * tcMph P T :=
        mul_le_mul' le_rfl h3

end UnforcedLeray.Short.PartIIIb.Concrete

end
