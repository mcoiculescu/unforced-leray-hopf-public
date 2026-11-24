import UnforcedLeray.Short.PartIIb.Sub.T11_6

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Integrability of the Fubini integrand `(x, z) ↦ χ(x) (ρ₁(x₁ - z₁) ρ₂(x₂ - z₂)) h(z)` on
`Coord × Coord`. Dominated by `1_{supp χ}(x) · 1_{L}(z) ‖h z‖`, where
`L = {x - y | x ∈ supp χ, y ∈ supp(ρ₁ ⊗ ρ₂)}` is compact. -/
theorem mtr_integrable (h : Coord → ℂ) (ρ₁ : ℝ → ℝ) (ρ₂ : ℝ × ℝ → ℝ) (χ : Coord → ℝ)
    (hh : LocallyIntegrable h volume) (hρ₁c : Continuous ρ₁) (hρ₁s : HasCompactSupport ρ₁)
    (hρ₂c : Continuous ρ₂) (hρ₂s : HasCompactSupport ρ₂) (hχc : Continuous χ)
    (hχs : HasCompactSupport χ) :
    Integrable (fun p : Coord × Coord =>
      (χ p.1 : ℂ) * (((ρ₁ (p.1.1 - p.2.1) * ρ₂ (p.1.2 - p.2.2) : ℝ) : ℂ) * h p.2))
      ((volume : Measure Coord).prod (volume : Measure Coord)) := by
  obtain ⟨Cχ, hCχ⟩ := hχc.bounded_above_of_compact_support hχs
  obtain ⟨C1, hC1⟩ := hρ₁c.bounded_above_of_compact_support hρ₁s
  obtain ⟨C2, hC2⟩ := hρ₂c.bounded_above_of_compact_support hρ₂s
  have hK : IsCompact (tsupport χ) := hχs
  have hA : IsCompact (tsupport ρ₁) := hρ₁s
  have hB : IsCompact (tsupport ρ₂) := hρ₂s
  have hT : IsCompact (tsupport ρ₁ ×ˢ tsupport ρ₂ : Set Coord) := hA.prod hB
  obtain ⟨Lc, hLc⟩ : ∃ L : Set Coord,
      L = (fun p : Coord × Coord => p.1 - p.2) ''
        (tsupport χ ×ˢ (tsupport ρ₁ ×ˢ tsupport ρ₂)) :=
    ⟨_, rfl⟩
  have hLcomp : IsCompact Lc := by
    rw [hLc]
    exact (hK.prod hT).image (continuous_fst.sub continuous_snd)
  have hmemL : ∀ x z : Coord, x ∈ tsupport χ → x.1 - z.1 ∈ tsupport ρ₁ →
      x.2 - z.2 ∈ tsupport ρ₂ → z ∈ Lc := by
    intro x z hx h1 h2
    rw [hLc]
    exact ⟨(x, x - z), ⟨hx, h1, h2⟩, sub_sub_cancel x z⟩
  have hf1 : Integrable ((tsupport χ).indicator (fun _ : Coord => Cχ * C1 * C2))
      (volume : Measure Coord) := by
    rw [integrable_indicator_iff hK.measurableSet]
    exact integrableOn_const hK.measure_lt_top.ne
  have hf2 : Integrable (Lc.indicator (fun z : Coord => ‖h z‖)) (volume : Measure Coord) := by
    rw [integrable_indicator_iff hLcomp.measurableSet]
    exact (hh.integrableOn_isCompact hLcomp).norm
  have hm := Integrable.mul_prod hf1 hf2
  have hFmeas : AEStronglyMeasurable (fun p : Coord × Coord =>
      (χ p.1 : ℂ) * (((ρ₁ (p.1.1 - p.2.1) * ρ₂ (p.1.2 - p.2.2) : ℝ) : ℂ) * h p.2))
      ((volume : Measure Coord).prod (volume : Measure Coord)) := by
    have hc1 : Continuous (fun p : Coord × Coord => (χ p.1 : ℂ)) := by fun_prop
    have hc2 : Continuous (fun p : Coord × Coord =>
        ((ρ₁ (p.1.1 - p.2.1) * ρ₂ (p.1.2 - p.2.2) : ℝ) : ℂ)) := by fun_prop
    have hh2 : AEStronglyMeasurable (fun p : Coord × Coord => h p.2)
        ((volume : Measure Coord).prod (volume : Measure Coord)) :=
      hh.aestronglyMeasurable.comp_snd
    exact hc1.aestronglyMeasurable.mul (hc2.aestronglyMeasurable.mul hh2)
  have hbound : ∀ p : Coord × Coord,
      ‖(χ p.1 : ℂ) * (((ρ₁ (p.1.1 - p.2.1) * ρ₂ (p.1.2 - p.2.2) : ℝ) : ℂ) * h p.2)‖ ≤
        ((tsupport χ).indicator (fun _ : Coord => Cχ * C1 * C2) p.1) *
          (Lc.indicator (fun z : Coord => ‖h z‖) p.2) := by
    rintro ⟨x, z⟩
    by_cases hx : x ∈ tsupport χ
    · by_cases hz : z ∈ Lc
      · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hz]
        have e : ‖(χ x : ℂ) * (((ρ₁ (x.1 - z.1) * ρ₂ (x.2 - z.2) : ℝ) : ℂ) * h z)‖ =
            ‖χ x‖ * (‖ρ₁ (x.1 - z.1)‖ * ‖ρ₂ (x.2 - z.2)‖) * ‖h z‖ := by
          simp only [norm_mul, Complex.norm_real]
          ring
        refine e.le.trans ?_
        have hnC1 : 0 ≤ C1 := le_trans (norm_nonneg _) (hC1 0)
        have hnCχ : 0 ≤ Cχ := le_trans (norm_nonneg _) (hCχ 0)
        have hmid : ‖χ x‖ * (‖ρ₁ (x.1 - z.1)‖ * ‖ρ₂ (x.2 - z.2)‖) ≤ Cχ * (C1 * C2) :=
          mul_le_mul (hCχ x) (mul_le_mul (hC1 _) (hC2 _) (norm_nonneg _) hnC1)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hnCχ
        calc ‖χ x‖ * (‖ρ₁ (x.1 - z.1)‖ * ‖ρ₂ (x.2 - z.2)‖) * ‖h z‖
            ≤ Cχ * (C1 * C2) * ‖h z‖ := mul_le_mul_of_nonneg_right hmid (norm_nonneg _)
          _ = Cχ * C1 * C2 * ‖h z‖ := by ring
      · have hzero : ρ₁ (x.1 - z.1) * ρ₂ (x.2 - z.2) = 0 := by
          by_cases h1 : x.1 - z.1 ∈ tsupport ρ₁
          · have h2 : x.2 - z.2 ∉ tsupport ρ₂ := fun h2 => hz (hmemL x z hx h1 h2)
            rw [image_eq_zero_of_notMem_tsupport h2, mul_zero]
          · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]
        simp only [Set.indicator_of_notMem hz, mul_zero]
        rw [hzero]
        simp
    · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp only [Set.indicator_of_notMem hx, zero_mul]
      rw [hχx]
      simp
  exact Integrable.mono' hm hFmeas (ae_of_all _ hbound)

/-- **Leaf `PartII-b:T11/6/16`** (transposition of a tensor mollification; Fubini). The Prop
`MollTranspose` is proved exactly as stated in `Sub/T11_6.lean`. -/
theorem mollTranspose : UnforcedLeray.Short.IIb.MollTranspose := by
  unfold UnforcedLeray.Short.IIb.MollTranspose
  intro h ρ₁ ρ₂ χ hh hρ₁c hρ₁s hρ₂c hρ₂s hχc hχs
  have hint := mtr_integrable h ρ₁ ρ₂ χ hh hρ₁c hρ₁s hρ₂c hρ₂s hχc hχs
  have hL : ∫ x : Coord, (χ x : ℂ) * mollG ρ₁ ρ₂ h x =
      ∫ x : Coord, ∫ z : Coord,
        (χ x : ℂ) * (((ρ₁ (x.1 - z.1) * ρ₂ (x.2 - z.2) : ℝ) : ℂ) * h z) := by
    congr 1
    funext x
    unfold mollG
    rw [integral_const_mul]
  have hswap : ∫ x : Coord, ∫ z : Coord,
        (χ x : ℂ) * (((ρ₁ (x.1 - z.1) * ρ₂ (x.2 - z.2) : ℝ) : ℂ) * h z) =
      ∫ z : Coord, ∫ x : Coord,
        (χ x : ℂ) * (((ρ₁ (x.1 - z.1) * ρ₂ (x.2 - z.2) : ℝ) : ℂ) * h z) :=
    integral_integral_swap hint
  rw [hL, hswap]
  congr 1
  funext z
  have e : ∀ x : Coord, (χ x : ℂ) * (((ρ₁ (x.1 - z.1) * ρ₂ (x.2 - z.2) : ℝ) : ℂ) * h z) =
      ((χ x * (ρ₁ (x.1 - z.1) * ρ₂ (x.2 - z.2)) : ℝ) : ℂ) * h z := by
    intro x
    push_cast
    ring
  simp_rw [e]
  rw [integral_mul_const]
  congr 1
  exact integral_ofReal

end UnforcedLeray.Short.IIb

end
