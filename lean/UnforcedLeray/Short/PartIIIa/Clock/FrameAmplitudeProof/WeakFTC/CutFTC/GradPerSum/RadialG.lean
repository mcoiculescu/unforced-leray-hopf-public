import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_1_1_1
import UnforcedLeray.Cons.C01ReferenceChoice.Quadrupole

/-!
# Part III-a, leaf `SeedDualRadialGDerivBounds` (`PartIII-a:T21/c5/1/1/1/1`, SP 601-610, 890-912)

Source of record: `the November 2 reference manuscript` (SP), lines 601-610
(`eq:short-seed-functional`) and 890-912.

For the seed triple `(λ, h)` the radial quotient `G(r) = ψ(r) / (Ω(r) - iλ/2)`, `ψ = Δ₂⁻¹ h`
(`Planar.greenN 2 h`), satisfies `|G'(r)| = O(r)` at `0` and `|G'(r)| = O(r⁻²)` at `∞`.

Proof: `ψ' = -¼ Φ` with `Φ(t) = ∫ ∂ₜker₂(t, ρ) h(ρ) dρ` (`B0011.WProf.hasDerivAt_Psi`). The kernel
bounds `|∂ₜker₂(t, ρ)| |h(ρ)| ≤ t B₀(ρ)` (`t ≤ 1`, using `|h(ρ)| ≤ C ρ²` on `(0, 1]`) and
`≤ t⁻² B₁(ρ)` (`t ≥ 1`, using the finite moments `∫ (ρ + ρ³)|h|`) give `|Φ(t)| ≤ A₀ t` and
`|Φ(t)| ≤ A₁ t⁻²`. With `|Ω - iλ/2| ≥ Re λ / 2`, `|Ω'| ≤ 1`, and `|ψ(r)| ≤ C min(r, r⁻²)`
(`Planar.norm_greenN_two_le_XG`), the quotient rule gives both derivative bounds. The `0`-jet
bounds repeat `seedDualExplicit_cont_and_pairing`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff ComplexConjugate

namespace UnforcedLeray.Short.IIIa

namespace GradPerSumLeaves

theorem dL_two (ρ t : ℝ) : B0011.dL 2 ρ t = 2 * (t / ρ) := by
  simp [B0011.dL]

theorem dR_two (ρ t : ℝ) : B0011.dR 2 ρ t = -(2 * (ρ / t) ^ 3) := by
  simp [B0011.dR]

/-- Near-origin pointwise bound for the kernel `∂ₜker₂(t, ρ)`. -/
theorem abs_dker_two_mul_le_near {C₀ t ρ x : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hρ : 0 < ρ)
    (hx0 : 0 ≤ x) (hx : ρ ≤ 1 → x ≤ C₀ * ρ ^ 2) :
    |B0011.dker 2 t ρ| * x ≤
      t * ((Set.Iic (1 : ℝ)).indicator (fun ρ => 2 * C₀ * ρ) ρ + 2 * (ρ * x)) := by
  have hρx : 0 ≤ ρ * x := mul_nonneg hρ.le hx0
  have htρx : 0 ≤ t * (ρ * x) := mul_nonneg ht.le hρx
  by_cases htρ : t < ρ
  · rw [B0011.dker_of_lt htρ, dL_two, abs_of_nonneg (by positivity)]
    by_cases hρ1 : ρ ≤ 1
    · rw [Set.indicator_of_mem (show ρ ∈ Iic (1 : ℝ) from hρ1)]
      have hxb := hx hρ1
      calc 2 * (t / ρ) * x ≤ 2 * (t / ρ) * (C₀ * ρ ^ 2) := by gcongr
        _ = t * (2 * C₀ * ρ) := by field_simp
        _ ≤ t * (2 * C₀ * ρ + 2 * (ρ * x)) := by nlinarith
    · rw [Set.indicator_of_notMem (show ρ ∉ Iic (1 : ℝ) from hρ1), zero_add]
      have hρ1' : 1 < ρ := not_le.mp hρ1
      have h1 : t / ρ ≤ t * ρ := by
        rw [div_le_iff₀ hρ]
        have hρρ : 1 ≤ ρ * ρ := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hρρ ht.le]
      calc 2 * (t / ρ) * x ≤ 2 * (t * ρ) * x := by gcongr
        _ = t * (2 * (ρ * x)) := by ring
  · have htρ' : ρ ≤ t := not_lt.mp htρ
    have hρ1 : ρ ≤ 1 := htρ'.trans ht1
    rw [B0011.dker_of_ge htρ', dR_two, abs_neg, abs_of_nonneg (by positivity),
      Set.indicator_of_mem (show ρ ∈ Iic (1 : ℝ) from hρ1)]
    have hxb := hx hρ1
    have hC₀ : 0 ≤ C₀ := by
      by_contra hneg
      have : C₀ * ρ ^ 2 < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) (by positivity)
      linarith
    have h3 : (ρ / t) ^ 3 * ρ ^ 2 ≤ t * ρ := by
      rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have h4 := pow_le_pow_left₀ hρ.le htρ' 4
      nlinarith [mul_le_mul_of_nonneg_left h4 hρ.le]
    calc 2 * (ρ / t) ^ 3 * x ≤ 2 * (ρ / t) ^ 3 * (C₀ * ρ ^ 2) := by gcongr
      _ = 2 * C₀ * ((ρ / t) ^ 3 * ρ ^ 2) := by ring
      _ ≤ 2 * C₀ * (t * ρ) := by gcongr
      _ ≤ t * (2 * C₀ * ρ + 2 * (ρ * x)) := by nlinarith

/-- Far-field pointwise bound for the kernel `∂ₜker₂(t, ρ)`. -/
theorem abs_dker_two_mul_le_far {t ρ x : ℝ} (ht : 1 ≤ t) (hρ : 0 < ρ) (hx0 : 0 ≤ x) :
    |B0011.dker 2 t ρ| * x ≤ (t ^ 2)⁻¹ * (2 * ((ρ + ρ ^ 3) * x)) := by
  have ht0 : 0 < t := by linarith
  have hkey : ∀ u : ℝ, u * t ^ 2 ≤ ρ + ρ ^ 3 →
      2 * u * x ≤ (t ^ 2)⁻¹ * (2 * ((ρ + ρ ^ 3) * x)) := by
    intro u h
    have ht2 : 0 < t ^ 2 := by positivity
    rw [← div_eq_inv_mul, le_div_iff₀ ht2]
    nlinarith [mul_le_mul_of_nonneg_right h hx0]
  by_cases htρ : t < ρ
  · rw [B0011.dker_of_lt htρ, dL_two, abs_of_nonneg (by positivity)]
    refine hkey (t / ρ) ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hρ]
    have h3 := pow_le_pow_left₀ ht0.le htρ.le 3
    nlinarith [sq_nonneg (ρ ^ 2 - ρ / 2), sq_nonneg ρ]
  · have htρ' : ρ ≤ t := not_lt.mp htρ
    rw [B0011.dker_of_ge htρ', dR_two, abs_neg, abs_of_nonneg (by positivity)]
    refine hkey ((ρ / t) ^ 3) ?_
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have h1 : t ^ 2 ≤ t ^ 3 := pow_le_pow_right₀ ht (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left h1 (pow_pos hρ 3).le, mul_pos hρ (pow_pos ht0 3)]

/-- `|Φ₂ g (t)| ≤ A t` on `(0, 1]` when `|g(ρ)| ≤ C₀ ρ²` on `(0, 1]`. -/
theorem norm_Phi_two_le_near {g : ℝ → ℂ} (hg : B0011.WProf g) {C₀ : ℝ}
    (hC₀ : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ‖g ρ‖ ≤ C₀ * ρ ^ 2) :
    ∃ A : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → ‖B0011.Phi 2 g t‖ ≤ A * t := by
  let B : ℝ → ℝ := fun ρ =>
    (Set.Iic (1 : ℝ)).indicator (fun ρ => 2 * C₀ * ρ) ρ + 2 * (ρ * ‖g ρ‖)
  have hon : IntegrableOn (fun ρ : ℝ => 2 * C₀ * ρ) (Iic 1) (volume.restrict (Ioi 0)) := by
    rw [IntegrableOn, Measure.restrict_restrict measurableSet_Iic]
    exact ((continuous_const.mul continuous_id).integrableOn_Icc (a := (0 : ℝ)) (b := 1)).mono_set
      (fun x hx => ⟨le_of_lt hx.2, hx.1⟩)
  have hBi : Integrable B (volume.restrict (Ioi 0)) :=
    (hon.integrable_indicator measurableSet_Iic).add (hg.int.const_mul 2)
  refine ⟨∫ ρ in Ioi (0 : ℝ), B ρ, fun t ht ht1 => ?_⟩
  have hbound : ∀ᵐ ρ ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(B0011.dker 2 t ρ : ℂ) * g ρ‖ ≤ t * B ρ := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun ρ hρ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact abs_dker_two_mul_le_near ht ht1 hρ (norm_nonneg _) (hC₀ ρ hρ)
  calc ‖B0011.Phi 2 g t‖ ≤ ∫ ρ in Ioi (0 : ℝ), t * B ρ :=
        norm_integral_le_of_norm_le (hBi.const_mul t) hbound
    _ = (∫ ρ in Ioi (0 : ℝ), B ρ) * t := by rw [integral_const_mul, mul_comm]

/-- `|Φ₂ g (t)| ≤ A t⁻²` on `[1, ∞)` when `(ρ + ρ³) g ∈ L¹`. -/
theorem norm_Phi_two_le_far {g : ℝ → ℂ} (hg : B0011.WProf g)
    (hg3 : Integrable (fun ρ => ρ ^ 3 * ‖g ρ‖) (volume.restrict (Ioi 0))) :
    ∃ A : ℝ, ∀ t : ℝ, 1 ≤ t → ‖B0011.Phi 2 g t‖ ≤ A / t ^ 2 := by
  let B : ℝ → ℝ := fun ρ => 2 * ((ρ + ρ ^ 3) * ‖g ρ‖)
  have hBi : Integrable B (volume.restrict (Ioi 0)) := by
    refine ((hg.int.add hg3).const_mul 2).congr (Eventually.of_forall fun ρ => ?_)
    simp only [Pi.add_apply, B]
    ring
  refine ⟨∫ ρ in Ioi (0 : ℝ), B ρ, fun t ht => ?_⟩
  have hbound : ∀ᵐ ρ ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(B0011.dker 2 t ρ : ℂ) * g ρ‖ ≤ (t ^ 2)⁻¹ * B ρ := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun ρ hρ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact abs_dker_two_mul_le_far ht hρ (norm_nonneg _)
  calc ‖B0011.Phi 2 g t‖ ≤ ∫ ρ in Ioi (0 : ℝ), (t ^ 2)⁻¹ * B ρ :=
        norm_integral_le_of_norm_le (hBi.const_mul _) hbound
    _ = (∫ ρ in Ioi (0 : ℝ), B ρ) / t ^ 2 := by rw [integral_const_mul, div_eq_inv_mul]

/-- Quotient-rule bound `|(p'd - pd')/d²| ≤ |p'|/a + |p||d'|/a²` for `|d| ≥ a > 0`. -/
theorem norm_quot_deriv_le {p p' d d' : ℂ} {a : ℝ} (ha : 0 < a) (hd : a ≤ ‖d‖) :
    ‖(p' * d - p * d') / d ^ 2‖ ≤ ‖p'‖ / a + ‖p‖ * ‖d'‖ / a ^ 2 := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hd
    linarith
  have e : (p' * d - p * d') / d ^ 2 = p' / d - p * d' / d ^ 2 := by
    field_simp
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_div, norm_div, norm_mul, norm_pow]
  exact add_le_add (div_le_div_of_nonneg_left (norm_nonneg _) ha hd)
    (div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ ha.le hd 2))

/-- `|Ω'(r)| = (|r|/2) e^{-r²/4} ≤ 1`. -/
theorem norm_deriv_radialOmega_le (r : ℝ) :
    ‖(((-r / 2 * GaussianVortex.radialOmega r : ℝ)) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (GaussianVortex.radialOmega_pos r)]
  have h1 := Real.add_one_le_exp (r ^ 2 / 4)
  have h2 : GaussianVortex.radialOmega r * Real.exp (r ^ 2 / 4) = 1 := by
    unfold GaussianVortex.radialOmega
    rw [← Real.exp_add]
    simp
  have habs : |-r / 2| = |r| / 2 := by
    rw [neg_div, abs_neg, abs_div, abs_two]
  rw [habs]
  have h3 : |r| / 2 ≤ Real.exp (r ^ 2 / 4) := by
    nlinarith [sq_abs r, sq_nonneg (|r| / 2 - 1), abs_nonneg r]
  calc |r| / 2 * GaussianVortex.radialOmega r
      ≤ Real.exp (r ^ 2 / 4) * GaussianVortex.radialOmega r :=
        mul_le_mul_of_nonneg_right h3 (GaussianVortex.radialOmega_pos r).le
    _ = 1 := by rw [mul_comm, h2]

/-- **Leaf `SeedDualRadialGDerivBounds` (`PartIII-a:T21/c5/1/1/1/1`, SP 601-610, 890-912).** -/
theorem seedDualRadialGDerivBounds_proof : SeedDualRadialGDerivBounds := by
  intro lam h hh ℓ hS hsm hon _hder
  show ContDiffOn ℝ ∞ (CutFTCGradPerSum.seedDualRadialG lam h) (Ioi 0) ∧
    CutFTCGradPerSum.seedDualRadialG lam h 0 = 0 ∧
    (∃ C₀ : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ‖CutFTCGradPerSum.seedDualRadialG lam h r‖ ≤ C₀ * r ^ 2 ∧
      ‖deriv (CutFTCGradPerSum.seedDualRadialG lam h) r‖ ≤ C₀ * r) ∧
    (∃ C₁ : ℝ, ∀ r : ℝ, 1 ≤ r →
      ‖CutFTCGradPerSum.seedDualRadialG lam h r‖ ≤ C₁ / r ^ 2 ∧
      ‖deriv (CutFTCGradPerSum.seedDualRadialG lam h) r‖ ≤ C₁ / r ^ 2)
  set G : ℝ → ℂ := CutFTCGradPerSum.seedDualRadialG lam h with hGdef
  have hre := hS.re_pos
  set q : B0010.XG := hh.toLp h
  have hGs : ContDiffOn ℝ ∞ (fun r : ℝ => Planar.greenN 2 h r) (Ioi 0) :=
    PartI.greenTwoSmooth_proof h hh hon
  have hΩ : ContDiff ℝ ∞ (fun r : ℝ => (GaussianVortex.radialOmega r : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp GaussianVortex.radialOmega_smooth
  have hK : ContDiff ℝ ∞ (fun r : ℝ => (GaussianVortex.radialK r : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp GaussianVortex.radialK_smooth
  have hqh : (⇑q) =ᵐ[volume.restrict (Ioi (0 : ℝ))] h :=
    B0012.restrict_ac.ae_le hh.coeFn_toLp
  have hgreen : ∀ r, Planar.greenN 2 (⇑q) r = Planar.greenN 2 h r :=
    PartI.adjEig_greenN_congr hqh
  -- the denominator `D = Ω - iλ/2`
  set D : ℝ → ℂ := fun r => (GaussianVortex.radialOmega r : ℂ) - Complex.I * lam / 2
    with hDdef
  set a : ℝ := lam.re / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have hDne : ∀ r, D r ≠ 0 := fun r => PartI.adjEig_den_ne hre _
  have hDlow : ∀ r, a ≤ ‖D r‖ := by
    intro r
    have h1 := Complex.abs_im_le_norm ((GaussianVortex.radialOmega r : ℂ) - Complex.I * lam / 2)
    rw [PartI.adjEig_im_den, abs_neg, abs_of_pos (by linarith)] at h1
    exact h1
  have hgd : ContDiffOn ℝ ∞ (fun r => Planar.greenN 2 h r / D r) (Ioi 0) := by
    have hD' : ContDiffOn ℝ ∞ (fun r : ℝ => (D r)⁻¹) (Ioi 0) := by
      intro r _
      have hat : ContDiffAt ℝ ∞ (fun z : ℂ => z⁻¹) (D r) :=
        (contDiffAt_inv ℂ (hDne r)).restrict_scalars ℝ
      exact hat.comp_contDiffWithinAt r ((hΩ.sub contDiff_const).contDiffWithinAt)
    simpa only [div_eq_mul_inv] using hGs.mul hD'
  have hGr : ∀ r : ℝ, 0 < r → G r = Planar.greenN 2 h r / D r := by
    intro r hr
    rw [hGdef, hDdef]
    simp [CutFTCGradPerSum.seedDualRadialG, hr]
  have hGcd : ContDiffOn ℝ ∞ G (Ioi 0) := hgd.congr fun r hr => hGr r hr
  have hG0 : G 0 = 0 := by
    rw [hGdef]
    simp [CutFTCGradPerSum.seedDualRadialG]
  -- `G = h / k` where `k ≠ 0` (the `0`-jet at the origin)
  have hgk : ∀ r : ℝ, 0 < r → Blueprint.Planar.strainK r ≠ 0 →
      G r = h r / (Blueprint.Planar.strainK r : ℂ) := by
    intro r hr hk
    have hae : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
        ((GaussianVortex.radialOmega x : ℂ) - Complex.I * lam / 2) * h x =
          (GaussianVortex.radialK x : ℂ) * Planar.greenN 2 h x := by
      have h0 := B0012.restrict_ac.ae_le (PartI.adjEig_pointwise hS.eigen)
      filter_upwards [h0, hqh] with x hx hx'
      rw [← hx', ← hgreen x]
      exact hx
    have hcont : ContinuousOn
        (fun x : ℝ => ((GaussianVortex.radialOmega x : ℂ) - Complex.I * lam / 2) * h x)
        (Ioi 0) :=
      ((hΩ.continuous.sub continuous_const).continuousOn).mul hon.continuousOn
    have hcont2 : ContinuousOn
        (fun x : ℝ => (GaussianVortex.radialK x : ℂ) * Planar.greenN 2 h x) (Ioi 0) :=
      hK.continuous.continuousOn.mul hGs.continuousOn
    have heq := Measure.eqOn_open_of_ae_eq hae isOpen_Ioi hcont hcont2 hr
    simp only at heq
    have hk' : (Blueprint.Planar.strainK r : ℂ) ≠ 0 := by exact_mod_cast hk
    rw [Cons.C01.strainK_eq] at hk' ⊢
    have hD := PartI.adjEig_den_ne hre (GaussianVortex.radialOmega r)
    rw [hGr r hr, hDdef]
    dsimp only
    rw [div_eq_div_iff hD hk']
    linear_combination -heq
  obtain ⟨C0, hC0⟩ := seedProfileOrderTwo_proof h hsm
  have hGn : ∀ r : ℝ, 0 < r → r ≤ 1 → ‖G r‖ ≤ C0 * r ^ 2 := by
    intro r hr hr1
    have hk := strainK_abs_ge_one hr1 hr
    have hk0 : Blueprint.Planar.strainK r ≠ 0 := by
      intro h0
      rw [h0] at hk
      norm_num at hk
    rw [hgk r hr hk0, norm_div, Complex.norm_real, Real.norm_eq_abs]
    calc ‖h r‖ / |Blueprint.Planar.strainK r| ≤ ‖h r‖ := div_le_self (norm_nonneg _) hk
      _ ≤ _ := hC0 r hr hr1
  -- bounds on `ψ = Δ₂⁻¹ h`
  obtain ⟨C_G, hC_G0, hC_G⟩ := Planar.norm_greenN_two_le_XG
  have hψnear : ∀ r : ℝ, 0 < r → r ≤ 1 → ‖Planar.greenN 2 h r‖ ≤ C_G * ‖q‖ * r := by
    intro r hr _
    rw [← hgreen r]
    exact (hC_G q r hr).trans (by gcongr; exact min_le_left _ _)
  have hψfar : ∀ r : ℝ, 1 ≤ r → ‖Planar.greenN 2 h r‖ ≤ C_G * ‖q‖ / r ^ 2 := by
    intro r hr1
    have hr : 0 < r := by linarith
    rw [← hgreen r, div_eq_mul_inv]
    exact (hC_G q r hr).trans (by gcongr; exact min_le_right _ _)
  have hGfar : ∀ r : ℝ, 1 ≤ r → ‖G r‖ ≤ C_G * ‖q‖ / a / r ^ 2 := by
    intro r hr1
    have hr : 0 < r := by linarith
    rw [hGr r hr, norm_div]
    calc ‖Planar.greenN 2 h r‖ / ‖D r‖ ≤ (C_G * ‖q‖ / r ^ 2) / a :=
          div_le_div₀ (by positivity) (hψfar r hr1) ha (hDlow r)
      _ = C_G * ‖q‖ / a / r ^ 2 := by ring
  -- the derivative `ψ' = -¼ Φ₂ h`
  have hm : AEStronglyMeasurable h (volume.restrict (Ioi (0 : ℝ))) :=
    hon.continuousOn.aestronglyMeasurable measurableSet_Ioi
  have hX := Cons.G3b.memXG_of_memLp hm hh
  have hw : B0011.WProf h := Cons.C01.wprof_of_memXG hX
  have h3 : Integrable (fun ρ => ρ ^ 3 * ‖h ρ‖) (volume.restrict (Ioi 0)) := by
    refine (Cons.C01.integrableOn_moment hX).norm.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show (0 : ℝ) < ρ from hρ)]
  obtain ⟨A₀, hA₀⟩ := norm_Phi_two_le_near hw hC0
  obtain ⟨A₁, hA₁⟩ := norm_Phi_two_le_far hw h3
  have hψd : ∀ r : ℝ, 0 < r →
      HasDerivAt (fun s => Planar.greenN 2 h s) (-(1 / 4 : ℂ) * B0011.Phi 2 h r) r := by
    intro r hr
    have h1 := (hw.hasDerivAt_Psi 2 hr).const_mul (-(1 / 4 : ℂ))
    have he : (fun s => Planar.greenN 2 h s) = fun s => -(1 / 4 : ℂ) * B0011.Psi 2 h s := by
      funext s
      rw [Planar.greenN_eq_Psi]
      norm_num
    rw [he]
    exact h1
  have hDd : ∀ r : ℝ, HasDerivAt D (((-r / 2 * GaussianVortex.radialOmega r : ℝ)) : ℂ) r :=
    fun r => ((GaussianVortex.hasDerivAt_radialOmega r).ofReal_comp).sub_const _
  have hGder : ∀ r : ℝ, 0 < r → deriv G r =
      ((-(1 / 4 : ℂ) * B0011.Phi 2 h r) * D r -
        Planar.greenN 2 h r * (((-r / 2 * GaussianVortex.radialOmega r : ℝ)) : ℂ)) / D r ^ 2 := by
    intro r hr
    have hd := (hψd r hr).div (hDd r) (hDne r)
    have hev : G =ᶠ[𝓝 r] fun s => Planar.greenN 2 h s / D s := by
      filter_upwards [Ioi_mem_nhds hr] with s hs
      exact hGr s hs
    exact (hd.congr_of_eventuallyEq hev).deriv
  have hGd_le : ∀ r : ℝ, 0 < r → ‖deriv G r‖ ≤
      1 / 4 * ‖B0011.Phi 2 h r‖ / a + ‖Planar.greenN 2 h r‖ * 1 / a ^ 2 := by
    intro r hr
    rw [hGder r hr]
    refine (norm_quot_deriv_le ha (hDlow r)).trans ?_
    have e : ‖(-(1 / 4 : ℂ) * B0011.Phi 2 h r)‖ = 1 / 4 * ‖B0011.Phi 2 h r‖ := by
      rw [norm_mul, norm_neg]
      norm_num
    rw [e]
    gcongr
    exact norm_deriv_radialOmega_le r
  refine ⟨hGcd, hG0, ⟨max C0 (A₀ / (4 * a) + C_G * ‖q‖ / a ^ 2), fun r hr hr1 => ⟨?_, ?_⟩⟩,
    ⟨max (C_G * ‖q‖ / a) (A₁ / (4 * a) + C_G * ‖q‖ / a ^ 2), fun r hr1 => ⟨?_, ?_⟩⟩⟩
  · exact (hGn r hr hr1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have h1 := hGd_le r hr
    have h2 := hA₀ r hr hr1
    have h3 := hψnear r hr hr1
    calc ‖deriv G r‖ ≤ 1 / 4 * ‖B0011.Phi 2 h r‖ / a + ‖Planar.greenN 2 h r‖ * 1 / a ^ 2 := h1
      _ ≤ 1 / 4 * (A₀ * r) / a + (C_G * ‖q‖ * r) * 1 / a ^ 2 := by gcongr
      _ = (A₀ / (4 * a) + C_G * ‖q‖ / a ^ 2) * r := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hr.le
  · have hr : 0 < r := by linarith
    calc ‖G r‖ ≤ C_G * ‖q‖ / a / r ^ 2 := hGfar r hr1
      _ ≤ _ := (div_le_div_iff_of_pos_right (by positivity)).mpr (le_max_left _ _)
  · have hr : 0 < r := by linarith
    have h1 := hGd_le r hr
    have h2 := hA₁ r hr1
    have h3 := hψfar r hr1
    calc ‖deriv G r‖ ≤ 1 / 4 * ‖B0011.Phi 2 h r‖ / a + ‖Planar.greenN 2 h r‖ * 1 / a ^ 2 := h1
      _ ≤ 1 / 4 * (A₁ / r ^ 2) / a + (C_G * ‖q‖ / r ^ 2) * 1 / a ^ 2 := by gcongr
      _ = (A₁ / (4 * a) + C_G * ‖q‖ / a ^ 2) / r ^ 2 := by
          field_simp
      _ ≤ _ := (div_le_div_iff_of_pos_right (by positivity)).mpr (le_max_right _ _)

end GradPerSumLeaves

end UnforcedLeray.Short.IIIa
