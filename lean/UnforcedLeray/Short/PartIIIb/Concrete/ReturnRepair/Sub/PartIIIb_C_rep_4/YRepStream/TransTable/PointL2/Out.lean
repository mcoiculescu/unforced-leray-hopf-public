import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.PointL2.Core

/-!
# The outward-primitive part of `transMajPointL2` (source 4181-4192, 3647)
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace PL2

/-- On the half-line `ρ ≥ L`, the gap-`D` majorant of a source supported in `ϱ ≤ sL` is
dominated by the gap-`(1-s)ρ` majorant. -/
theorem sepDom_halfline_le {s L D ρ : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (hL : 0 < L)
    (hD : D = (1 - s) * L) (hρ : L ≤ ρ) (g : ℝ → Space → ℝ≥0∞)
    (hgs : ∀ τ (z : Space), s * L < ϱ z → g τ z = 0) (τ z : ℝ) :
    IIIa.sepDom 0 0 D g τ !₂[ρ, 0, z] ≤ IIIa.sepDom 0 0 ((1 - s) * ρ) g τ !₂[ρ, 0, z] := by
  unfold IIIa.sepDom
  refine setLIntegral_mono' measurableSet_Ioo (fun l hl => ?_)
  refine mul_le_mul' le_rfl (lintegral_mono fun z' => ?_)
  by_cases hg : g (τ + 2 * Real.log l) z' = 0
  · simp [hg]
  · have hw : ϱ z' ≤ s * L := by
      by_contra hcon
      exact hg (hgs _ z' (not_le.1 hcon))
    have hsL : 0 ≤ s * L := mul_nonneg hs0 hL.le
    have hρ' : s * L ≤ ρ := by nlinarith
    have hge := PmStep.geo_norm_ge ρ (s * L) l z z' hl.1.le hl.2.le hsL hρ' hw
    have h1 : (1 - s) * ρ ≤ ‖(!₂[ρ, 0, z] : Space) - l • z'‖ := by nlinarith
    have h2 : D ≤ ‖(!₂[ρ, 0, z] : Space) - l • z'‖ := by
      rw [hD]; nlinarith
    have e1 : IIIa.sepKd 0 D ((!₂[ρ, 0, z] : Space) - l • z') =
        IIIa.sepKd 0 ((1 - s) * ρ) ((!₂[ρ, 0, z] : Space) - l • z') := by
      unfold IIIa.sepKd
      rw [if_pos h2, if_pos h1]
    rw [e1]


/-- The outward primitive in the phase norm (Minkowski in `ρ`, gap `(1-s)ρ`, power integral). -/
theorem outMaj_ltauAt_le {s L D r C0 P : ℝ} {N : ℝ≥0∞} (hs0 : 0 ≤ s) (hs1 : s < 1) (hL : 0 < L)
    (hD : D = (1 - s) * L) (hr : L ≤ r) (hP : 0 < P) (hC0 : 0 ≤ C0)
    (g : ℝ → Space → ℝ≥0∞) (hgm : Measurable (Function.uncurry g))
    (hgs : ∀ τ (z : Space), s * L < ϱ z → g τ z = 0)
    (hpt : ∀ D' : ℝ, 0 < D' → ∀ y : Space,
      IIIa.ltauAt P (fun τ => IIIa.sepDom 0 0 D' g τ y) ≤
        ENNReal.ofReal (C0 * D' ^ (-(79 / 22) : ℝ)) * N) (z : ℝ) :
    IIIa.ltauAt P (fun τ => outMaj 0 D g τ r z) ≤
      ENNReal.ofReal (C0 * (1 - s) ^ (-(79 / 22) : ℝ) * (22 / 35 * r ^ (-(35 / 22) : ℝ))) * N := by
  have hr0 : 0 < r := hL.trans_le hr
  have hκ : 0 < 1 - s := by linarith
  have hFm : Measurable (Function.uncurry (fun ρ τ : ℝ =>
      ENNReal.ofReal ρ * IIIa.sepDom 0 0 D g τ !₂[ρ, 0, z])) := by
    have h1 : Measurable (Function.uncurry (IIIa.sepDom 0 0 D g)) :=
      sd_measurable_sepDom 0 0 D g hgm
    have h2 : Measurable (fun p : ℝ × ℝ => (p.2, (!₂[p.1, 0, z] : Space))) :=
      measurable_snd.prodMk ((measurable_halfline z).comp measurable_fst)
    have h3 : Measurable (fun p : ℝ × ℝ =>
        (Function.uncurry (IIIa.sepDom 0 0 D g)) (p.2, (!₂[p.1, 0, z] : Space))) := h1.comp h2
    exact (ENNReal.measurable_ofReal.comp measurable_fst).mul h3
  unfold outMaj
  calc IIIa.ltauAt P (fun τ => ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ * IIIa.sepDom 0 0 D g τ !₂[ρ, 0, z])
      ≤ ∫⁻ ρ in Ioi r, IIIa.ltauAt P (fun τ => ENNReal.ofReal ρ * IIIa.sepDom 0 0 D g τ !₂[ρ, 0, z]) := ltauAt_lintegral_set_le P hP (Ioi r) _ hFm
    _ ≤ ∫⁻ ρ in Ioi r, ENNReal.ofReal (C0 * (1 - s) ^ (-(79 / 22) : ℝ)) *
          (ENNReal.ofReal (ρ ^ (-(57 / 22) : ℝ)) * N) := by
        refine setLIntegral_mono' measurableSet_Ioi (fun ρ hρ => ?_)
        have hρL : L ≤ ρ := hr.trans (le_of_lt hρ)
        have hρ0 : 0 < ρ := hL.trans_le hρL
        have e1 : IIIa.ltauAt P (fun τ => ENNReal.ofReal ρ * IIIa.sepDom 0 0 D g τ !₂[ρ, 0, z]) =
            ENNReal.ofReal ρ * IIIa.ltauAt P (fun τ => IIIa.sepDom 0 0 D g τ !₂[ρ, 0, z]) :=
          IIIa.ltauAt_const_mul P _ ENNReal.ofReal_ne_top _
        rw [e1]
        have e2 : IIIa.ltauAt P (fun τ => IIIa.sepDom 0 0 D g τ !₂[ρ, 0, z]) ≤
            IIIa.ltauAt P (fun τ => IIIa.sepDom 0 0 ((1 - s) * ρ) g τ !₂[ρ, 0, z]) :=
          IIIa.ltauAt_mono P (fun τ => sepDom_halfline_le hs0 hs1 hL hD hρL g hgs τ z)
        refine (mul_le_mul' le_rfl (e2.trans (hpt _ (by positivity) _))).trans_eq ?_
        have hreal : ρ * (C0 * ((1 - s) * ρ) ^ (-(79 / 22) : ℝ)) =
            C0 * (1 - s) ^ (-(79 / 22) : ℝ) * ρ ^ (-(57 / 22) : ℝ) := by
          rw [Real.mul_rpow hκ.le hρ0.le]
          have : ρ ^ (-(57 / 22) : ℝ) = ρ * ρ ^ (-(79 / 22) : ℝ) := by
            rw [← Real.rpow_one_add' hρ0.le (by norm_num)]; norm_num
          rw [this]; ring
        calc ENNReal.ofReal ρ * (ENNReal.ofReal (C0 * ((1 - s) * ρ) ^ (-(79 / 22) : ℝ)) * N)
            = ENNReal.ofReal (ρ * (C0 * ((1 - s) * ρ) ^ (-(79 / 22) : ℝ))) * N := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul hρ0.le]
          _ = ENNReal.ofReal (C0 * (1 - s) ^ (-(79 / 22) : ℝ) * ρ ^ (-(57 / 22) : ℝ)) * N := by
              rw [hreal]
          _ = _ := by
              rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ = ENNReal.ofReal (C0 * (1 - s) ^ (-(79 / 22) : ℝ)) *
          ((∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ (-(57 / 22) : ℝ))) * N) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_mul_const'' N (f := fun a : ℝ => ENNReal.ofReal (a ^ (-(57 / 22) : ℝ)))
          (μ := volume.restrict (Ioi r))
          (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).aemeasurable
    _ = _ := by
        rw [lintegral_Ioi_rpow r hr0, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

end PL2

end UnforcedLeray.Short.PartIIIb.Concrete

end
