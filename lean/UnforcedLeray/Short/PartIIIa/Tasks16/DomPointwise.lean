import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16
import UnforcedLeray.Short.PartIIIa.Tasks16.DomPointwise.Kernel
import UnforcedLeray.Short.PartIIIa.Tasks16.DomPointwise.Norm
import UnforcedLeray.Short.PartIIIa.Tasks16.DomPointwise.Phase
import UnforcedLeray.Short.PartIIIa.Tasks16.DomPointwise.Minkowski

/-!
# Part III-a, `PartIII-a:T16/3`: `SepDomPointwise` (SP 3647)

For fixed `y`: Hölder in `z` (exponents `b`, `p`), dilation `l^{-3/b}` of the `L^b` norm of the
gap-truncated kernel, Minkowski in `l` over `(0,1)` in `L²_τ`, phase invariance, and
`∫_0^1 l^{a-3/b} dl = 1/(a-2+3/p) ≤ 1/δ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem sepDomPointwise : UnforcedLeray.Short.IIIa.SepDomPointwise := by
  intro j p b δ hp hb hpb hδ
  have hp1 : 1 < p := by
    rcases hp.lt_or_eq with h | h
    · exact h
    · subst h; have : 1 / b = 0 := by linarith
      have : 0 < 1 / b := by positivity
      linarith
  have hb1 : 1 < b := by
    rcases hb.lt_or_eq with h | h
    · exact h
    · subst h; have : 1 / p = 0 := by linarith
      have : 0 < 1 / p := by positivity
      linarith
  have hb0 : 0 < b := by linarith
  have hp0 : 0 < p := by linarith
  have hconj : b.HolderConjugate p := Real.holderConjugate_iff.mpr ⟨hb1, by simp only [one_div] at hpb; linarith⟩
  set I1 : ℝ≥0∞ := ∫⁻ x : Space, sepKd j 1 x ^ b with hI1
  have hI1top : I1 ≠ ⊤ := lintegral_sepKd_rpow_one_ne_top j b hb1
  refine ⟨(I1.toReal) ^ (1 / b) / δ, by positivity, ?_⟩
  intro a ha hδa D P hD hP g hgm hgper y
  have h3b : 3 / b = 3 - 3 / p := by
    have : 1 / b = 1 - 1 / p := by linarith
    calc 3 / b = 3 * (1 / b) := by ring
      _ = 3 - 3 / p := by rw [this]; ring
  have he1 : a - 3 / b + 1 = a - 2 + 3 / p := by rw [h3b]; ring
  have hδe : δ ≤ a - 3 / b + 1 := by rw [he1]; exact hδa
  have heg : -1 < a - 3 / b := by linarith
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ≥0∞, ∀ τ, G τ = (∫⁻ z, g τ z ^ p) ^ (1 / p) := ⟨_, fun _ => rfl⟩
  have hGm : Measurable G := by
    have h1 : Measurable fun q : ℝ × Space => g q.1 q.2 ^ p := hgm.pow_const p
    have h2 := h1.lintegral_prod_right' (ν := (volume : Measure Space))
    have : G = fun τ => (∫⁻ z, g τ z ^ p) ^ (1 / p) := funext hGdef
    rw [this]
    exact h2.pow_const _
  have hGper : ∀ τ, G (τ + P) = G τ := by intro τ; rw [hGdef, hGdef]; simp only [hgper]
  have hGL : ltauAt P G = ltauLq P p g := by
    unfold ltauAt ltauLq
    have : ∀ τ, G τ ^ (2:ℝ) = (∫⁻ z, g τ z ^ p) ^ (2 / p) := fun τ => by
      rw [hGdef, ← ENNReal.rpow_mul]; congr 1; ring
    simp_rw [this]
  set M : ℝ≥0∞ := ENNReal.ofReal (D ^ (-4 - (j : ℝ) + 3 / b)) * I1 ^ (1 / b) with hM
  have hMtop : M ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hI1top)
  have hpt : ∀ τ, sepDom a j D g τ y ≤
      ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (a - 3 / b)) * M * G (τ + 2 * Real.log l) := by
    intro τ
    unfold sepDom
    refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
    have hf : AEMeasurable (fun z : Space => sepKd j D (y - l • z)) volume :=
      ((sepKd_measurable j D).comp (measurable_const.sub (measurable_const_smul l))).aemeasurable
    have hg : AEMeasurable (g (τ + 2 * Real.log l)) volume :=
      (hgm.comp (measurable_prodMk_left (x := τ + 2 * Real.log l))).aemeasurable
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hconj hf hg
    have hH' : ∫⁻ z : Space, sepKd j D (y - l • z) * g (τ + 2 * Real.log l) z ≤
        (∫⁻ z : Space, sepKd j D (y - l • z) ^ b) ^ (1 / b) * G (τ + 2 * Real.log l) := by
      rw [hGdef]; exact hH
    calc ENNReal.ofReal (l ^ a) * ∫⁻ z : Space, sepKd j D (y - l • z) * g (τ + 2 * Real.log l) z
        ≤ ENNReal.ofReal (l ^ a) * ((∫⁻ z : Space, sepKd j D (y - l • z) ^ b) ^ (1 / b) *
            G (τ + 2 * Real.log l)) := by gcongr
      _ = ENNReal.ofReal (l ^ (a - 3 / b)) * M * G (τ + 2 * Real.log l) := by
        have hk : (∫⁻ z : Space, sepKd j D (y - l • z) ^ b) ^ (1 / b) =
            ENNReal.ofReal (l ^ (-(3 / b))) * M := kernelNorm j D b hD hb0 y l hl.1
        rw [hk, sub_eq_add_neg, Real.rpow_add hl.1, ENNReal.ofReal_mul (Real.rpow_nonneg hl.1.le _)]
        ring
  have hFm : Measurable (Function.uncurry fun (l τ : ℝ) =>
      ENNReal.ofReal (l ^ (a - 3 / b)) * M * G (τ + 2 * Real.log l)) := by
    refine Measurable.mul ?_ ?_
    · exact (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).mul_const M
    · exact hGm.comp (measurable_snd.add ((Real.measurable_log.comp measurable_fst).const_mul 2))
  have hI : I1 ^ (1 / b) = ENNReal.ofReal (I1.toReal ^ (1 / b)) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hI1top]
    rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity)]
  calc ltauAt P (fun τ => sepDom a j D g τ y)
      ≤ ltauAt P (fun τ => ∫⁻ l in Ioo (0 : ℝ) 1,
          ENNReal.ofReal (l ^ (a - 3 / b)) * M * G (τ + 2 * Real.log l)) := ltauAt_mono P hpt
    _ ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ltauAt P (fun τ =>
          ENNReal.ofReal (l ^ (a - 3 / b)) * M * G (τ + 2 * Real.log l)) :=
        ltauAt_lintegral_le P hP _ hFm
    _ = ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (a - 3 / b)) * (M * ltauAt P G) := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun l hl => ?_
        rw [ltauAt_const_mul P _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hMtop),
          ltauAt_shift P hP G hGper, mul_assoc]
    _ = ENNReal.ofReal (1 / (a - 3 / b + 1)) * (M * ltauAt P G) := by
        have hm : Measurable fun l : ℝ => ENNReal.ofReal (l ^ (a - 3 / b)) :=
          ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
        rw [lintegral_mul_const _ hm, sepDomPointwise_lintegral_Ioo_rpow _ heg]
    _ ≤ ENNReal.ofReal (I1.toReal ^ (1 / b) / δ * D ^ (-4 - (j : ℝ) + 3 / b)) * ltauLq P p g := by
        rw [← hGL, ← mul_assoc]
        gcongr
        have hpos : 0 < a - 3 / b + 1 := by linarith
        rw [hM, hI, ← ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _),
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : 1 / (a - 3 / b + 1) ≤ 1 / δ := one_div_le_one_div_of_le hδ hδe
        have h2 : 0 ≤ D ^ (-4 - (j : ℝ) + 3 / b) * I1.toReal ^ (1 / b) := by positivity
        calc 1 / (a - 3 / b + 1) * (D ^ (-4 - (j : ℝ) + 3 / b) * I1.toReal ^ (1 / b))
            ≤ 1 / δ * (D ^ (-4 - (j : ℝ) + 3 / b) * I1.toReal ^ (1 / b)) := by gcongr
          _ = _ := by ring

end UnforcedLeray.Short.IIIa

end
