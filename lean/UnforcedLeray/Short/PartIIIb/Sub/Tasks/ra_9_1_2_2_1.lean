import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_2

/-!
# `PartIII-b:C/asrc/ra/9/1/2/2/1` : radial derivative of the weighted ring profile

Source: `the November 2 reference manuscript` lines 5034-5036 (`radial_chain`).
With `chartM R τ (ρ,z) = (R²/ρ², (Rτ/2 - (R/2) log(R²/ρ²), R z/ρ))` one has
`∂_ρ s = -2s/ρ`, `∂_ρ ξ = R/ρ`, `∂_ρ η = -η/ρ`, and `∂_ρ (R/ρ)^k = -k R⁻¹ (R/ρ)^(k+1)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Derivative of the scalar weight `ρ ↦ (R/ρ)^k`. -/
theorem ra2211_powDiv_hasDerivAt (R : ℝ) (hR : R ≠ 0) (k : ℕ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t' : ℝ => (R / t') ^ k) (-(k : ℝ) * R⁻¹ * (R / t) ^ (k + 1)) t := by
  have hq : HasDerivAt (fun t' : ℝ => R / t') (-(R / t ^ 2)) t := by
    have h := (hasDerivAt_inv ht).const_mul R
    have e : (fun t' : ℝ => R / t') = fun t' : ℝ => R * t'⁻¹ := by
      funext t'
      rw [div_eq_mul_inv]
    rw [e]
    exact h.congr_deriv (by rw [div_eq_mul_inv, mul_neg])
  have h := hq.pow k
  refine h.congr_deriv ?_
  cases k with
  | zero => simp
  | succ n =>
    have hRR : R⁻¹ * R = 1 := inv_mul_cancel₀ hR
    push_cast
    try simp only [Nat.add_sub_cancel]
    linear_combination ((n + 1 : ℝ) * R ^ (n + 1) * t⁻¹ ^ (n + 2)) * hRR

/-- The chart curve `ρ ↦ chartM R τ (ρ, z₀)` and its `ρ`-derivative in the coordinates
`(s, (ξ, η))`: `(-2s/ρ, (R/ρ, -η/ρ))` with `s = R²/ρ²`, `η = R z₀/ρ`. -/
theorem ra2211_chartCurve_rho (R τ z0 : ℝ) (hR : R ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t' : ℝ => chartM R τ (t', z0))
      (-2 * (R ^ 2 / t ^ 2) / t, (R / t, -(R * z0 / t) / t)) t := by
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
  have hs : HasDerivAt (fun t' : ℝ => R ^ 2 / t' ^ 2) (-2 * (R ^ 2 / t ^ 2) / t) t := by
    have h := (hasDerivAt_const t (R ^ 2)).div (hasDerivAt_pow 2 t) ht2
    refine h.congr_deriv ?_
    norm_num <;> field_simp <;> ring
  have hne : R ^ 2 / t ^ 2 ≠ 0 := div_ne_zero (pow_ne_zero 2 hR) ht2
  have hlog : HasDerivAt (fun t' : ℝ => R * τ / 2 - (R / 2) * Real.log (R ^ 2 / t' ^ 2))
      (R / t) t := by
    have hl := hs.log hne
    have h := (hasDerivAt_const t (R * τ / 2)).sub ((hasDerivAt_const t (R / 2)).mul hl)
    refine h.congr_deriv ?_
    field_simp <;> ring
  have hz : HasDerivAt (fun t' : ℝ => R * z0 / t') (-(R * z0 / t) / t) t := by
    have h := (hasDerivAt_const t (R * z0)).div (hasDerivAt_id' t) ht
    refine h.congr_deriv ?_
    field_simp <;> ring
  exact hs.prodMk (hlog.prodMk hz)

/-- Radial chain rule for the weighted ring profile (source 5034-5036). -/
theorem ringWeightedDRho {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {R : ℝ} (hR : 0 < R) (k : ℕ) {c : Chart → E} (hc : ContDiffOn ℝ 1 c (Set.Ioi 0 ×ˢ Set.univ)) (τ : ℝ) {m : ℝ × ℝ} (hm : 0 < m.1) : dρ (fun m' : ℝ × ℝ => (R / m'.1) ^ k • c (chartM R τ m')) m = (R / m.1) ^ (k + 1) • (UnforcedLeray.Axi.dQ c (chartM R τ m) - R⁻¹ • Kc c (chartM R τ m) - ((k : ℝ) * R⁻¹) • c (chartM R τ m)) := by
  have hRne : R ≠ 0 := hR.ne'
  have htne : m.1 ≠ 0 := hm.ne'
  have hmem : chartM R τ m ∈ (Ioi 0 ×ˢ univ : Set Chart) :=
    ⟨div_pos (pow_pos hR 2) (pow_pos hm 2), trivial⟩
  have hcd : DifferentiableAt ℝ c (chartM R τ m) :=
    (hc.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem)).differentiableAt (by norm_num)
  have h1 : ∀ m' ∈ (Ioi 0 ×ˢ univ : Set (ℝ × ℝ)), m'.1 ≠ 0 := fun m' hm' => ne_of_gt hm'.1
  have hs : ContDiffOn ℝ 1 (fun m' : ℝ × ℝ => R ^ 2 / m'.1 ^ 2) (Ioi 0 ×ˢ univ) :=
    contDiffOn_const.div (contDiff_fst.pow 2).contDiffOn fun m' hm' => pow_ne_zero 2 (h1 m' hm')
  have hspos : ∀ m' ∈ (Ioi 0 ×ˢ univ : Set (ℝ × ℝ)), R ^ 2 / m'.1 ^ 2 ≠ 0 := fun m' hm' =>
    div_ne_zero (pow_ne_zero 2 hRne) (pow_ne_zero 2 (h1 m' hm'))
  have hch : ContDiffOn ℝ 1 (chartM R τ) (Ioi 0 ×ˢ univ) := by
    unfold chartM
    refine hs.prodMk (ContDiffOn.prodMk ?_ ?_)
    · exact contDiffOn_const.sub (contDiffOn_const.mul (hs.log hspos))
    · exact (contDiffOn_const.mul contDiff_snd.contDiffOn).div contDiff_fst.contDiffOn h1
  have hmaps : MapsTo (chartM R τ) (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) := fun m' hm' =>
    ⟨div_pos (pow_pos hR 2) (pow_pos hm'.1 2), trivial⟩
  have hF : ContDiffOn ℝ 1 (fun m' : ℝ × ℝ => (R / m'.1) ^ k • c (chartM R τ m'))
      (Ioi 0 ×ˢ univ) :=
    ((contDiffOn_const.div contDiff_fst.contDiffOn h1).pow k).smul (hc.comp hch hmaps)
  have hmem' : m ∈ (Ioi 0 ×ˢ univ : Set (ℝ × ℝ)) := ⟨hm, trivial⟩
  have hFd : DifferentiableAt ℝ (fun m' : ℝ × ℝ => (R / m'.1) ^ k • c (chartM R τ m')) m :=
    (hF.differentiableOn (by norm_num)).differentiableAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem')
  have hγ : HasDerivAt (fun t : ℝ => ((t, m.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) m.1 :=
    (hasDerivAt_id' m.1).prodMk (hasDerivAt_const m.1 m.2)
  have hcomp := hFd.hasFDerivAt.comp_hasDerivAt m.1 hγ
  have hA : HasDerivAt (fun t : ℝ => (R / t) ^ k • c (chartM R τ (t, m.2)))
      ((-(k : ℝ) * R⁻¹ * (R / m.1) ^ (k + 1)) • c (chartM R τ m)
        + (R / m.1) ^ k • ((-2 * (R ^ 2 / m.1 ^ 2) / m.1) • UnforcedLeray.Axi.dS c (chartM R τ m)
          + (R / m.1) • UnforcedLeray.Axi.dQ c (chartM R τ m)
          + (-(R * m.2 / m.1) / m.1) • UnforcedLeray.Axi.dEta c (chartM R τ m))) m.1 := by
    have hw := ra2211_powDiv_hasDerivAt R hRne k htne
    have hcurve := ra2211_chartCurve_rho R τ m.2 hRne htne
    have hg : HasDerivAt (fun t : ℝ => c (chartM R τ (t, m.2)))
        (fderiv ℝ c (chartM R τ m) (-2 * (R ^ 2 / m.1 ^ 2) / m.1, (R / m.1, -(R * m.2 / m.1) / m.1)))
        m.1 := hcd.hasFDerivAt.comp_hasDerivAt m.1 hcurve
    have h := hw.smul hg
    refine h.congr_deriv ?_
    rw [clm_triple]
    unfold UnforcedLeray.Axi.dS UnforcedLeray.Axi.dQ UnforcedLeray.Axi.dEta
    rw [pow_succ (R / m.1) k]
    generalize (R / m.1) ^ k = u
    match_scalars <;> field_simp <;> ring
  have hkey := hcomp.unique hA
  show fderiv ℝ (fun m' : ℝ × ℝ => (R / m'.1) ^ k • c (chartM R τ m')) m (1, 0) = _
  rw [hkey]
  simp only [Kc, UnforcedLeray.Axi.dS, UnforcedLeray.Axi.dQ, UnforcedLeray.Axi.dEta, chartM]
  rw [pow_succ (R / m.1) k]
  generalize (R / m.1) ^ k = u
  match_scalars <;> field_simp <;> ring

end UnforcedLeray.Short.PartIIIb.Concrete
