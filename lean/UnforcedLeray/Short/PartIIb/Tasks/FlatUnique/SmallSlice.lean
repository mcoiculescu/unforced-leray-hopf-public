import UnforcedLeray.Short.PartIIb.Sub.T11

/-!
# Part II-b, leaf `PartII-b:T11/4` (`SmallSliceNorm`): zero entrance from `H_r`

Source of record: `the November 2 reference manuscript` (SP 1900-1938 for the
`H_r` norm and the flat-response bound). The statement is `SmallSliceNorm` of `Sub/T11.lean`.

Proof by contradiction. The `H_r` norm is `∫⁻ ‖b‖ₑ^r d(hMeas c r)`, and `hMeas c r` is the
product `(vol|_{(0,∞)} withDensity s^(r/2-5/2)) ⊗ Cyl.avgμ c`. Tonelli gives
`∫⁻ ‖b‖ₑ^r d(hMeas) = ∫⁻_{σ>0} σ^(r/2-5/2) J(σ) dσ` with `J(σ) = ∫⁻_p ‖b(σ,p)‖ₑ^r`.
If the slice quantity `I(σ) = σ^(r/2-3/2) J(σ)` exceeded `ε` a.e. on `(0,σ₀)`, then
`σ^(r/2-5/2) J(σ) = σ⁻¹ I(σ) ≥ ε σ⁻¹` there, and `∫⁻_{(0,σ₀)} ε σ⁻¹ = ∞`, a contradiction.
A measurable representative `b'` of `b` is used for Tonelli; the slices of `b` and `b'` agree
for a.e. `σ` (`Measure.ae_ae_of_ae_prod` and `ae_withDensity_iff`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- The normalized cell measure is `s`-finite (instance search does not unfold `Cyl.avgμ`). -/
instance smallSlice_sFinite_avgμ (c : ℝ) : SFinite (Cyl.avgμ c) := by
  unfold Cyl.avgμ
  infer_instance

/-- Tonelli slice decomposition of the `H_r` measure `hMeas c r` for a measurable `f`. -/
theorem smallSlice_lintegral_hMeas (c r : ℝ) (f : Coord → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂(hMeas c r) =
      ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (r / 2 - 5 / 2)) *
        ∫⁻ p, f (σ, p) ∂(Cyl.avgμ c) := by
  unfold hMeas Axi.ageμ
  rw [MeasureTheory.lintegral_prod _ hf.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ (Axi.measurable_ofReal_rpow _)
      hf.lintegral_prod_right']
  rfl

/-- `∫_{(0,σ₀)} σ⁻¹ dσ = ∞` (the integral of `1/σ` diverges at `0`). -/
theorem smallSlice_lintegral_inv_eq_top {σ₀ : ℝ} (hσ₀ : 0 < σ₀) :
    ∫⁻ σ in Ioo (0 : ℝ) σ₀, ENNReal.ofReal σ⁻¹ = ⊤ := by
  by_contra hne
  have hlt : ∫⁻ σ in Ioo (0 : ℝ) σ₀, ENNReal.ofReal σ⁻¹ < ⊤ := lt_top_iff_ne_top.2 hne
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) σ₀)] fun x : ℝ => x ^ (-1 : ℝ) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) σ₀))]
      with x hx
    exact (Real.rpow_pos_of_pos hx.1 _).le
  have hfi : HasFiniteIntegral (fun x : ℝ => x ^ (-1 : ℝ))
      (volume.restrict (Ioo (0 : ℝ) σ₀)) :=
    (hasFiniteIntegral_iff_ofReal hnn).2 (by simpa only [Real.rpow_neg_one] using hlt)
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ (-1 : ℝ))
      (volume.restrict (Ioo (0 : ℝ) σ₀)) :=
    (measurable_id.pow_const _).aestronglyMeasurable
  have h := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := -1) hσ₀).1 ⟨hmeas, hfi⟩
  exact lt_irrefl _ h

/-- **Leaf `PartII-b:T11/4`** (`SmallSliceNorm`, zero entrance from `H_r`). -/
theorem smallSliceNorm : UnforcedLeray.Short.IIb.SmallSliceNorm := by
  unfold SmallSliceNorm
  intro c r b _hc hr hb ε σ₀ hε hσ₀
  refine pos_iff_ne_zero.2 (fun h0 => ?_)
  -- `h0 : volume S = 0`, so a.e. `σ` lies outside the bad set `S`.
  have hae := measure_eq_zero_iff_ae_notMem.1 h0
  -- On `(0,σ₀)` a.e.: the slice quantity strictly exceeds `ε`.
  have hA : ∀ᵐ σ ∂(volume.restrict (Ioo (0 : ℝ) σ₀)),
      ENNReal.ofReal ε < ENNReal.ofReal (σ ^ (r / 2 - 3 / 2)) *
        ∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c) := by
    filter_upwards [ae_restrict_of_ae hae,
      ae_restrict_mem (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) σ₀))] with σ hσS hσI
    by_contra hcon
    exact hσS ⟨hσI, not_lt.1 hcon⟩
  -- A measurable representative `b'` of `b` (for Tonelli).
  obtain ⟨b', hb'm, hbb'⟩ := hb.meas
  have hb'meas : Measurable b' := hb'm.measurable
  have hf'm : Measurable fun z : Coord => ‖b' z‖ₑ ^ r := hb'meas.enorm.pow_const r
  -- Finiteness of the `H_r` norm.
  have hfin : ∫⁻ z, ‖b z‖ₑ ^ r ∂(hMeas c r) < ⊤ := by
    have h : eLpNorm b (ENNReal.ofReal r) (hMeas c r) < ⊤ := hb.finite
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (ENNReal.ofReal_pos.2 (show (0 : ℝ) < r by linarith)).ne' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (show (0 : ℝ) ≤ r by linarith)] at h
    exact h
  have hcongr : ∫⁻ z, ‖b z‖ₑ ^ r ∂(hMeas c r) = ∫⁻ z, ‖b' z‖ₑ ^ r ∂(hMeas c r) := by
    apply lintegral_congr_ae
    filter_upwards [hbb'] with z hz
    simp only [hz]
  have hL : ∫⁻ z, ‖b' z‖ₑ ^ r ∂(hMeas c r) =
      ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (r / 2 - 5 / 2)) *
        ∫⁻ p, ‖b' (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c) :=
    smallSlice_lintegral_hMeas c r _ hf'm
  have hLt : ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (r / 2 - 5 / 2)) *
      ∫⁻ p, ‖b' (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c) < ⊤ := by
    rw [← hL, ← hcongr]
    exact hfin
  -- Slices of `b` and `b'` agree for a.e. `σ` (Tonelli on the product, then withDensity).
  have hslice : ∀ᵐ σ ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
      fun s => ENNReal.ofReal (s ^ (r / 2 - 5 / 2))),
      ∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c) = ∫⁻ p, ‖b' (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c) := by
    have h2 : ∀ᵐ z ∂(((volume.restrict (Ioi (0 : ℝ))).withDensity
        fun s => ENNReal.ofReal (s ^ (r / 2 - 5 / 2))).prod (Cyl.avgμ c)), b z = b' z := hbb'
    filter_upwards [Measure.ae_ae_of_ae_prod h2] with σ hσ
    apply lintegral_congr_ae
    filter_upwards [hσ] with p hp
    have hp' : b (σ, p) = b' (σ, p) := hp
    simp only [hp']
  have hB0 := (ae_withDensity_iff (Axi.measurable_ofReal_rpow (r / 2 - 5 / 2))).1 hslice
  have hB : ∀ᵐ σ ∂(volume.restrict (Ioo (0 : ℝ) σ₀)),
      ∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c) = ∫⁻ p, ‖b' (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self hB0,
      ae_restrict_mem (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) σ₀))] with σ h1 h2
    exact h1 (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos h2.1 _)).ne'
  -- Pointwise lower bound: `σ⁻¹ ε ≤ σ^(r/2-5/2) J'(σ)` on `(0,σ₀)` a.e.
  have hpt : ∀ᵐ σ ∂(volume.restrict (Ioo (0 : ℝ) σ₀)),
      ENNReal.ofReal σ⁻¹ * ENNReal.ofReal ε ≤
        ENNReal.ofReal (σ ^ (r / 2 - 5 / 2)) * ∫⁻ p, ‖b' (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c) := by
    filter_upwards [hA, hB, ae_restrict_mem (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) σ₀))]
      with σ hσA hσB hσI
    have hσpos : 0 < σ := hσI.1
    have hkey : ENNReal.ofReal (σ ^ (r / 2 - 5 / 2)) =
        ENNReal.ofReal σ⁻¹ * ENNReal.ofReal (σ ^ (r / 2 - 3 / 2)) := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 hσpos.le)]
      congr 1
      have h1 : r / 2 - 5 / 2 = (r / 2 - 3 / 2) - 1 := by ring
      rw [h1, Real.rpow_sub_one hσpos.ne', div_eq_inv_mul]
    rw [hσB] at hσA
    calc ENNReal.ofReal σ⁻¹ * ENNReal.ofReal ε
        ≤ ENNReal.ofReal σ⁻¹ * (ENNReal.ofReal (σ ^ (r / 2 - 3 / 2)) *
            ∫⁻ p, ‖b' (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c)) :=
            mul_le_mul_of_nonneg_left hσA.le (by positivity)
      _ = ENNReal.ofReal (σ ^ (r / 2 - 5 / 2)) * ∫⁻ p, ‖b' (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c) := by
          rw [hkey]
          ring
  -- The contradiction: the left side is `∞`, the right side is at most `∫⁻ ‖b'‖ₑ^r < ∞`.
  have hconst : ∫⁻ σ in Ioo (0 : ℝ) σ₀, ENNReal.ofReal σ⁻¹ * ENNReal.ofReal ε = ⊤ := by
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, smallSlice_lintegral_inv_eq_top hσ₀,
      ENNReal.top_mul (ENNReal.ofReal_pos.2 hε).ne']
  have hlow : ∫⁻ σ in Ioo (0 : ℝ) σ₀, ENNReal.ofReal σ⁻¹ * ENNReal.ofReal ε ≤
      ∫⁻ σ in Ioo (0 : ℝ) σ₀, ENNReal.ofReal (σ ^ (r / 2 - 5 / 2)) *
        ∫⁻ p, ‖b' (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c) :=
    lintegral_mono_ae hpt
  have hup : ∫⁻ σ in Ioo (0 : ℝ) σ₀, ENNReal.ofReal (σ ^ (r / 2 - 5 / 2)) *
        ∫⁻ p, ‖b' (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c) ≤
      ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (r / 2 - 5 / 2)) *
        ∫⁻ p, ‖b' (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c) :=
    lintegral_mono_set Ioo_subset_Ioi_self
  rw [hconst] at hlow
  exact lt_irrefl (⊤ : ℝ≥0∞) ((hlow.trans hup).trans_lt hLt)

end UnforcedLeray.Short.IIb
