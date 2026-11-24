import UnforcedLeray.Short.PartIIb.Sub.PartIIb_P1_1_1

/-!
# `PartII-b:P1/1/1`, step (4): finite `H_p` norm of the inverse-chart profile

Source `the November 2 reference manuscript` 1902-1906.  Proves `BLRNorm` from
`Axi.lintegral_Nv_rpow` and `Axi.perExt_ae_eq`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

theorem norm_realC_eq (x : Space) : ‖realC x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [realC_apply, Complex.norm_real]

theorem enorm_realC_eq (x : Space) : ‖realC x‖ₑ = ‖x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, norm_realC_eq]

theorem blrNorm_proof : BLRNorm := by
  intro R c P hR hc hP B hBm hfin
  have hq : (0 : ℝ) < bgp := by norm_num [bgp]
  have hPpos : 0 < P := hP ▸ div_pos (by positivity) hR
  have hlin := Axi.lintegral_Nv_rpow hR hc hP hq (b := Axi.perExt c B)
    (Axi.measurable_perExt c hBm) (Axi.perExt_periodic hc.ne' B)
  unfold phaseLpNorm at hfin
  have h0 : (0 : ℝ) ≤ 1 / bgp := by positivity
  have hne : ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
      ‖realC (Axi.Nv R (Axi.perExt c B) t y)‖ₑ ^ bgp < ⊤ := by
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon, ENNReal.top_rpow_of_pos (by positivity)] at hfin
    exact lt_irrefl _ hfin
  simp only [enorm_realC_eq] at hne
  have hne' : (ENNReal.ofReal P)⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
      ‖Axi.Nv R (Axi.perExt c B) t y‖ₑ ^ bgp < ⊤ := by
    rwa [← ENNReal.ofReal_inv_of_pos hPpos]
  rw [hlin] at hne'
  have hpi : ENNReal.ofReal (Real.pi * R ^ 2) ≠ 0 := by
    have : 0 < Real.pi * R ^ 2 := by positivity
    simpa using this
  have hint : ∫⁻ p, ‖Axi.perExt c B p‖ₑ ^ bgp ∂Axi.ageμ c (bgp / 2 - 5 / 2) < ⊤ := by
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon, ENNReal.mul_top hpi] at hne'
    exact lt_irrefl _ hne'
  have hae := Axi.perExt_ae_eq hc (bgp / 2 - 5 / 2) B
  have hint2 : ∫⁻ p, ‖B p‖ₑ ^ bgp ∂Axi.ageμ c (bgp / 2 - 5 / 2) < ⊤ := by
    have e : ∫⁻ p, ‖Axi.perExt c B p‖ₑ ^ bgp ∂Axi.ageμ c (bgp / 2 - 5 / 2) =
        ∫⁻ p, ‖B p‖ₑ ^ bgp ∂Axi.ageμ c (bgp / 2 - 5 / 2) :=
      lintegral_congr_ae (by filter_upwards [hae] with p hp; rw [hp])
    rw [← e]
    exact hint
  simp only [hMeas]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq)
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq.le]
  exact ENNReal.rpow_lt_top_of_nonneg h0 hint2.ne

end UnforcedLeray.Short.IIb
