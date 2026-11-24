import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2TransOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.VertYoungL2.Scaled
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.VertYoungL2.Phase
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_5.Of

/-!
# `PartIII-b:C/rep/5/2/2/8` : `VertYoungL2` (the `L²` vertical Young inequality)

Source `the November 2 reference manuscript` 3624-3647 (Young in the vertical
variable, dilation, Minkowski in `λ`, phase), 4181-4192 and 5590-5592 (the outward primitive in
`L²_τL²`). The `L²` analogue of `vertYoungPhase` (`Sub/PartIII-b_C_rep_2_4_5/Of.lean`):

* `vertKernYoungScaled2` (`VertYoungL2/Scaled.lean`): Young `1 + 1/2 = 19/22 + 7/11` with
  kernel in `L^{11/7}`, dilation `λ^{-3/22}`;
* Minkowski in `λ` for the `L²` vertical norm (`vertMinkowski`, `Of.lean`);
* the phase norm is the `L²(μP)` norm, `μP = (1/P)dτ` on `(0,P]`, and the dilation integral
  `∫_0^1 λ^{a-3/22} G(τ+2 log λ) dλ` is put in `L²_τ` by Minkowski, with the translation
  invariance of the normalized `L²` norm of a `P`-periodic function (`eLp2_shift`); no `P ≤ 1`
  is needed (this is why `PeriodicDilationSum` is not used).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`VertYoungL2`** (source 3624-3647, 4181-4192 in one dimension, `L²` case). -/
theorem vertYoungL2 : VertYoungL2 := by
  obtain ⟨CY, hCY, hS⟩ := vertKernYoungScaled2
  refine ⟨CY * (22 / 19), by positivity, ?_⟩
  intro a rIn D P ha hD0 hrIn hP h hhm hper
  have hGper : ∀ s, lqNorm1 (22 / 19) (h (s + P)) = lqNorm1 (22 / 19) (h s) := fun s => by
    rw [show h (s + P) = h s from funext (hper s)]
  have hGm : Measurable (fun σ => lqNorm1 (22 / 19) (h σ)) := by
    have h1 : Measurable (fun σ => ∫⁻ y, h σ y ^ (22 / 19 : ℝ)) := by
      have h2 : Measurable (fun x : ℝ × ℝ => h x.1 x.2 ^ (22 / 19 : ℝ)) := hhm.pow_const _
      exact h2.lintegral_prod_right'
    unfold lqNorm1
    exact h1.pow_const _
  have hhτ : ∀ (τ l : ℝ), Measurable (h (τ + 2 * Real.log l)) := fun τ l =>
    hhm.comp (measurable_const.prodMk measurable_id)
  -- pointwise: the `λ`-integral dominates the `L²_z` norm of the vertical dilation
  have hpt : ∀ τ, lqNorm1 2 (vertRedH a rIn D h τ) ≤ ∫⁻ l in Ioo (0 : ℝ) 1,
      (ENNReal.ofReal (CY * (rIn / D) * D ^ (-2 + 7 / 11 : ℝ)) *
        ENNReal.ofReal (l ^ (a + -(3 / 22)))) * lqNorm1 (22 / 19) (h (τ + 2 * Real.log l)) := by
    intro τ
    refine (vertMinkowski a rIn D 2 (by norm_num) h hhm τ).trans ?_
    refine setLIntegral_mono' measurableSet_Ioo (fun l hl => ?_)
    have hY := hS rIn D hrIn hD0 l hl.1 hl.2 (h (τ + 2 * Real.log l)) (hhτ τ l)
    calc ENNReal.ofReal (l ^ a) * lqNorm1 2
          (fun z => ∫⁻ s : ℝ, vertKern rIn D (z - l * s) * h (τ + 2 * Real.log l) s)
        ≤ ENNReal.ofReal (l ^ a) * (ENNReal.ofReal (CY * (rIn / D) * D ^ (-2 + 7 / 11 : ℝ)) *
            (ENNReal.ofReal (l ^ (-(3 / 22) : ℝ)) * lqNorm1 (22 / 19) (h (τ + 2 * Real.log l)))) :=
          mul_le_mul' le_rfl hY
      _ = (ENNReal.ofReal (CY * (rIn / D) * D ^ (-2 + 7 / 11 : ℝ)) *
            ENNReal.ofReal (l ^ (a + -(3 / 22)))) * lqNorm1 (22 / 19) (h (τ + 2 * Real.log l)) := by
          rw [Real.rpow_add hl.1, ENNReal.ofReal_mul (Real.rpow_nonneg hl.1.le _)]
          ring
  -- measurability of the dilation integrand in `(τ, l)`
  have hBm : Measurable (Function.uncurry (fun (τ l : ℝ) =>
      (ENNReal.ofReal (CY * (rIn / D) * D ^ (-2 + 7 / 11 : ℝ)) *
        ENNReal.ofReal (l ^ (a + -(3 / 22)))) * lqNorm1 (22 / 19) (h (τ + 2 * Real.log l)))) := by
    have m1 : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.2 ^ (a + -(3 / 22)))) :=
      ENNReal.measurable_ofReal.comp (measurable_snd.pow_const _)
    have m2 : Measurable (fun p : ℝ × ℝ => lqNorm1 (22 / 19) (h (p.1 + 2 * Real.log p.2))) :=
      hGm.comp (measurable_fst.add (measurable_const.mul (Real.measurable_log.comp measurable_snd)))
    exact (measurable_const.mul m1).mul m2
  haveI : IsFiniteMeasure (Rep522Phase.muP P) := muP_finite hP
  have hMink := UnforcedLeray.PlanarBS.Conv.eLpNorm_lintegral_le (μ := Rep522Phase.muP P)
    (ν := volume.restrict (Ioo (0 : ℝ) 1))
    (F := fun (τ l : ℝ) => (ENNReal.ofReal (CY * (rIn / D) * D ^ (-2 + 7 / 11 : ℝ)) *
        ENNReal.ofReal (l ^ (a + -(3 / 22)))) * lqNorm1 (22 / 19) (h (τ + 2 * Real.log l)))
    hBm.aemeasurable (p := 2) (by norm_num) (by norm_num)
  have hGl : ∀ l : ℝ, Measurable (fun τ => lqNorm1 (22 / 19) (h (τ + 2 * Real.log l))) :=
    fun l => hGm.comp (measurable_id.add_const _)
  calc ltauLq1 P 2 (vertRedH a rIn D h)
      = eLpNorm (fun τ => lqNorm1 2 (vertRedH a rIn D h τ)) 2 (Rep522Phase.muP P) :=
        ltau_eq_eLp2 (P := P) (q := 2) (vertRedH a rIn D h)
    _ ≤ eLpNorm (fun τ => ∫⁻ l in Ioo (0 : ℝ) 1,
          (ENNReal.ofReal (CY * (rIn / D) * D ^ (-2 + 7 / 11 : ℝ)) *
            ENNReal.ofReal (l ^ (a + -(3 / 22)))) * lqNorm1 (22 / 19) (h (τ + 2 * Real.log l)))
          2 (Rep522Phase.muP P) :=
        eLpNorm_mono_enorm (fun τ => by
          rw [enorm_eq_self, enorm_eq_self]
          exact hpt τ)
    _ ≤ ∫⁻ l in Ioo (0 : ℝ) 1, eLpNorm (fun τ =>
          (ENNReal.ofReal (CY * (rIn / D) * D ^ (-2 + 7 / 11 : ℝ)) *
            ENNReal.ofReal (l ^ (a + -(3 / 22)))) * lqNorm1 (22 / 19) (h (τ + 2 * Real.log l)))
          2 (Rep522Phase.muP P) := hMink
    _ = ∫⁻ l in Ioo (0 : ℝ) 1, (ENNReal.ofReal (CY * (rIn / D) * D ^ (-2 + 7 / 11 : ℝ)) *
            ENNReal.ofReal (l ^ (a + -(3 / 22)))) * eLpNorm (fun σ => lqNorm1 (22 / 19) (h σ))
              2 (Rep522Phase.muP P) := by
        refine lintegral_congr fun l => ?_
        rw [eLp2_const_mul P _ (fun τ => lqNorm1 (22 / 19) (h (τ + 2 * Real.log l))) (hGl l)]
        rw [eLp2_shift hP (G := fun σ => lqNorm1 (22 / 19) (h σ)) hGper (2 * Real.log l)]
    _ = (ENNReal.ofReal (CY * (rIn / D) * D ^ (-2 + 7 / 11 : ℝ)) *
            eLpNorm (fun σ => lqNorm1 (22 / 19) (h σ)) 2 (Rep522Phase.muP P)) *
          ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (a + -(3 / 22))) := by
        have hm : Measurable (fun l : ℝ => ENNReal.ofReal (l ^ (a + -(3 / 22)))) :=
          ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
        have e : ∀ l : ℝ, (ENNReal.ofReal (CY * (rIn / D) * D ^ (-2 + 7 / 11 : ℝ)) *
              ENNReal.ofReal (l ^ (a + -(3 / 22)))) *
              eLpNorm (fun σ => lqNorm1 (22 / 19) (h σ)) 2 (Rep522Phase.muP P) =
            (ENNReal.ofReal (CY * (rIn / D) * D ^ (-2 + 7 / 11 : ℝ)) *
              eLpNorm (fun σ => lqNorm1 (22 / 19) (h σ)) 2 (Rep522Phase.muP P)) *
              ENNReal.ofReal (l ^ (a + -(3 / 22))) := fun l => by ring
        simp_rw [e]
        exact lintegral_const_mul _ hm
    _ ≤ (ENNReal.ofReal (CY * (rIn / D) * D ^ (-2 + 7 / 11 : ℝ)) *
            eLpNorm (fun σ => lqNorm1 (22 / 19) (h σ)) 2 (Rep522Phase.muP P)) * ENNReal.ofReal (22 / 19) :=
        by
          gcongr
          exact phase_int_le (by linarith)
    _ = ENNReal.ofReal (CY * (22 / 19) * (rIn / D) * D ^ (-2 + 7 / 11 : ℝ)) *
          ltauLq1 P (22 / 19) h := by
        rw [ltau_eq_eLp2 (P := P) (q := 22 / 19) h]
        have hcon : ENNReal.ofReal (CY * (22 / 19) * (rIn / D) * D ^ (-2 + 7 / 11 : ℝ)) =
            ENNReal.ofReal (CY * (rIn / D) * D ^ (-2 + 7 / 11 : ℝ)) * ENNReal.ofReal (22 / 19) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
        rw [hcon]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
