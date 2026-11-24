import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2_2.VtvRBoundAE

/-!
# `VtvPLsc`: lower semicontinuity of `p_s` under `C^∞` convergence (source 4610)

`p_s(φ) = ∫_{(0,s]} ‖R(r,φ)‖ dr`.  For a.e. `r ∈ (0,s]`, `R(r,·)` is linear (`vtvRLinAE`) and
bounded by finitely many `C^k` seminorms on the band (`vtvRBoundAE`), so `R(r,φ_n) → R(r,φ)`
for a.e. `r`.  Fatou's lemma then gives `p_s(φ) ≤ liminf p_s(φ_n) ≤ t`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem vtvPLsc : VtvPLsc := by
  intro ν c μ tr ω g b G f H s R hs φn φ hbt hφ hc t ht
  have hcyl : ∀ n, B0579.IsCylTest c (φn n) := fun n => (hbt n).1
  have hLin : ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) s)), ∀ φ ψ : ℝ × ℝ → ℝ,
      B0579.IsCylTest c φ → B0579.IsCylTest c ψ → ∀ a : ℝ,
        vtvR μ tr ω g b r (φ + ψ) = vtvR μ tr ω g b r φ + vtvR μ tr ω g b r ψ ∧
        vtvR μ tr ω g b r (a • φ) = (a : ℂ) * vtvR μ tr ω g b r φ :=
    ae_restrict_of_ae_restrict_of_subset (fun r hr => hr.1) (vtvRLinAE ν c μ tr ω g b G f H)
  have hBnd : ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) s)), ∃ (k : ℕ) (C : ℝ), ∀ φ, BandTest c R φ →
      ∀ M : ℝ, CkSmall k M φ → ‖vtvR μ tr ω g b r φ‖ ≤ C * M :=
    ae_restrict_of_ae_restrict_of_subset (fun r hr => hr.1) (vtvRBoundAE ν c μ tr ω g b G f H R)
  have hint : ∀ χ : ℝ × ℝ → ℝ, B0579.IsCylTest c χ →
      IntegrableOn (fun r => vtvR μ tr ω g b r χ) (Ioc 0 s) := by
    intro χ hχ
    obtain ⟨h1, h2, _⟩ := H.2.2.2.2.2.2.2.1 χ hχ s hs
    refine (h1.add h2).congr_fun (fun r _ => ?_) measurableSet_Ioc
    simp only [vtvR, mul_add, Pi.add_apply]
  -- a.e. pointwise convergence of R(r, φ_n) to R(r, φ)
  have hconv : ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) s)),
      Tendsto (fun n => vtvR μ tr ω g b r (φn n)) atTop (𝓝 (vtvR μ tr ω g b r φ)) := by
    filter_upwards [hLin, hBnd] with r hr hbr
    obtain ⟨k, C, hkC⟩ := hbr
    rw [Metric.tendsto_nhds]
    intro ε hε
    set δ : ℝ := ε / (|C| + 1) with hδ
    have hδpos : 0 < δ := div_pos hε (by positivity)
    have hδ' : |C| * δ < ε := by
      have h1 : δ * (|C| + 1) = ε := div_mul_cancel₀ ε (by positivity)
      nlinarith [abs_nonneg C]
    filter_upwards [(Filter.eventually_all_finite (Set.finite_Iic k)).2
      (fun j _ => hc j δ hδpos)] with n hn
    have hsmall : CkSmall k δ (φn n - φ) := fun j hj x => hn j hj x
    have hsub : φn n - φ = φn n + (-1 : ℝ) • φ := by
      funext x
      simp [sub_eq_add_neg]
    have hdiff : BandTest c R (φn n - φ) := by
      rw [hsub]
      exact ⟨cyl_add (hcyl n) (cyl_smul (-1) hφ.1),
        fun x hx => by simp [(hbt n).2 x hx, hφ.2 x hx]⟩
    have key : vtvR μ tr ω g b r (φn n) - vtvR μ tr ω g b r φ
        = vtvR μ tr ω g b r (φn n - φ) := by
      rw [hsub, (hr (φn n) ((-1 : ℝ) • φ) (hcyl n) (cyl_smul (-1) hφ.1) 1).1,
        (hr φ φ hφ.1 hφ.1 (-1)).2]
      push_cast
      ring
    have hb := hkC (φn n - φ) hdiff δ hsmall
    rw [dist_eq_norm, key]
    exact lt_of_le_of_lt (hb.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hδpos.le)) hδ'
  -- measurability for Fatou
  have hmeas : ∀ n, AEMeasurable (fun r => ENNReal.ofReal ‖vtvR μ tr ω g b r (φn n)‖)
      (volume.restrict (Ioc 0 s)) := fun n =>
    ((hint (φn n) (hcyl n)).aestronglyMeasurable.norm.aemeasurable).ennreal_ofReal
  have hfat := lintegral_liminf_le' (u := (atTop : Filter ℕ))
    (f := fun n r => ENNReal.ofReal ‖vtvR μ tr ω g b r (φn n)‖) hmeas
  have hae : ∫⁻ r in Ioc 0 s,
      liminf (fun n => ENNReal.ofReal ‖vtvR μ tr ω g b r (φn n)‖) atTop
        = ∫⁻ r in Ioc 0 s, ENNReal.ofReal ‖vtvR μ tr ω g b r φ‖ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hconv] with r hr
    exact (ENNReal.tendsto_ofReal hr.norm).liminf_eq
  have hle : liminf (fun n => ∫⁻ r in Ioc 0 s, ENNReal.ofReal ‖vtvR μ tr ω g b r (φn n)‖) atTop
      ≤ ENNReal.ofReal t := by
    refine Filter.liminf_le_of_frequently_le' (x := ENNReal.ofReal t) ?_
    refine (Filter.Eventually.frequently ?_)
    filter_upwards [ht] with n hn
    have hn' : ∫ r in Ioc 0 s, ‖vtvR μ tr ω g b r (φn n)‖ ≤ t := hn
    rw [← ofReal_integral_eq_lintegral_ofReal (hint (φn n) (hcyl n)).norm
      (ae_of_all _ fun r => norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hn'
  have hfin : ∫⁻ r in Ioc 0 s, ENNReal.ofReal ‖vtvR μ tr ω g b r φ‖ ≤ ENNReal.ofReal t := by
    calc ∫⁻ r in Ioc 0 s, ENNReal.ofReal ‖vtvR μ tr ω g b r φ‖
        = ∫⁻ r in Ioc 0 s,
            liminf (fun n => ENNReal.ofReal ‖vtvR μ tr ω g b r (φn n)‖) atTop := hae.symm
      _ ≤ liminf (fun n => ∫⁻ r in Ioc 0 s, ENNReal.ofReal ‖vtvR μ tr ω g b r (φn n)‖) atTop :=
          hfat
      _ ≤ ENNReal.ofReal t := hle
  have ht0 : 0 ≤ t := by
    obtain ⟨n, hn⟩ := ht.exists
    have hn' : ∫ r in Ioc 0 s, ‖vtvR μ tr ω g b r (φn n)‖ ≤ t := hn
    exact (integral_nonneg fun _ => norm_nonneg _).trans hn'
  show ∫ r in Ioc 0 s, ‖vtvR μ tr ω g b r φ‖ ≤ t
  by_cases hI : Integrable (fun r => ‖vtvR μ tr ω g b r φ‖) (volume.restrict (Ioc 0 s))
  · have heq := ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun r => norm_nonneg _)
    have hle2 : ENNReal.ofReal (∫ r in Ioc 0 s, ‖vtvR μ tr ω g b r φ‖) ≤ ENNReal.ofReal t := by
      rw [heq]
      exact hfin
    exact (ENNReal.ofReal_le_ofReal_iff ht0).1 hle2
  · rw [integral_undef hI]
    exact ht0

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
