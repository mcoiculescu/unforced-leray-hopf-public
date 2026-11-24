import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_1

/-!
# Part II-b, task `PartII-b:G4/3/6/1/8`: the velocity jets `RawVelJets`

Source of record: `the November 2 reference manuscript` (SP) 2419-2423 (jets of
`b = (v₁, v₂ + εH)`) and 463-478 (tail and fixed-band regions of `sct:transverse`, `sct:fixed-band`).

The tail region `|η| ≥ Cp/ν + 2` is `RawVelTailJets` (with the constant `Cp`), and the band region
`|η| < Cp/ν + 2` is `RawVelBandJets` (for the same `Cp`).  The two bounds are merged by the case split
on `|x.2.2|`, with `C = C₁ + C₂`, `N = max N₁ N₂`, and `ν₀ = min (min ν₁ ν₂) 1`, so that
`(ν^N)⁻¹` dominates both `(ν^N₁)⁻¹` and `(ν^N₂)⁻¹` for `ν ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- Monotonicity of `k ↦ (ν^k)⁻¹` on `(0, 1]`: a higher power gives a larger reciprocal. -/
theorem velJets_inv_pow_mono {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) {k k' : ℕ} (hk : k ≤ k') :
    (ν ^ k)⁻¹ ≤ (ν ^ k')⁻¹ :=
  inv_anti₀ (pow_pos hν k') (pow_le_pow_of_le_one hν.le hν1 hk)

/-- **Velocity jets** (SP 2419-2423, 463-478): the tail region bound `RawVelTailJets` and the band
region bound `RawVelBandJets` (same `Cp`) combine to the velocity jets `RawVelJets` on `0 < s ≤ Σ/ν`
for all `η`. -/
theorem rawVelJets_of (ht : UnforcedLeray.Short.IIb.RawVelTailJets)
    (hb : UnforcedLeray.Short.IIb.RawVelBandJets) : UnforcedLeray.Short.IIb.RawVelJets := by
  obtain ⟨Cp, hCp, Ht⟩ := ht
  intro Sig hSig dm dp hdm
  obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, H₁⟩ := Ht Sig hSig dm dp hdm
  obtain ⟨C₂, N₂, ν₂, hC₂, hν₂, H₂⟩ := hb Cp hCp Sig hSig dm dp hdm
  refine ⟨C₁ + C₂, max N₁ N₂, min (min ν₁ ν₂) 1, by positivity,
    lt_min (lt_min hν₁ hν₂) one_pos, ?_⟩
  intro p d hBg hν hcut x hx0 hxH
  have hνpos : 0 < p.ν := p.ν_pos
  have hνa : p.ν ≤ ν₁ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνb : p.ν ≤ ν₂ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hinv0 : ∀ k : ℕ, 0 ≤ (p.ν ^ k)⁻¹ := fun k => inv_nonneg.2 (pow_nonneg hνpos.le k)
  by_cases h : Cp / p.ν + 2 ≤ |x.2.2|
  · have h1 := H₁ p d hBg hνa hcut x hx0 hxH h
    have hm : (p.ν ^ N₁)⁻¹ ≤ (p.ν ^ (max N₁ N₂))⁻¹ :=
      velJets_inv_pow_mono hνpos hν1 (le_max_left _ _)
    calc _ ≤ C₁ * (p.ν ^ N₁)⁻¹ := h1
      _ ≤ C₁ * (p.ν ^ (max N₁ N₂))⁻¹ := mul_le_mul_of_nonneg_left hm hC₁.le
      _ ≤ (C₁ + C₂) * (p.ν ^ (max N₁ N₂))⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) (hinv0 _)
  · have hlt : |x.2.2| < Cp / p.ν + 2 := not_le.mp h
    have h2 := H₂ p d hBg hνb hcut x hx0 hxH hlt
    have hm : (p.ν ^ N₂)⁻¹ ≤ (p.ν ^ (max N₁ N₂))⁻¹ :=
      velJets_inv_pow_mono hνpos hν1 (le_max_right _ _)
    calc _ ≤ C₂ * (p.ν ^ N₂)⁻¹ := h2
      _ ≤ C₂ * (p.ν ^ (max N₁ N₂))⁻¹ := mul_le_mul_of_nonneg_left hm hC₂.le
      _ ≤ (C₁ + C₂) * (p.ν ^ (max N₁ N₂))⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) (hinv0 _)

end UnforcedLeray.Short.IIb
