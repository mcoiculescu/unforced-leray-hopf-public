import UnforcedLeray.Short.PartIIIa.SeparatedKernels
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# `sep:mean-comparison` (SP 3735-3790): reduction to four leaves

`F = F̄ + F_⊥` (phase mean plus oscillation).  The mean part is `τ`-independent and is handled by
the outer change of variables and a Taylor expansion in `(x', εY, t)` (SP 3753-3766); the
oscillatory part by `F_⊥(q_ε(r,τ+2log λ)) = ε λ ∂_λ[J F_⊥(...)]`, `J = ∂_q⁻¹` of norm
`≤ c/(2π)`, and an integration by parts in `λ` (SP 3768-3790).  The reduction below (Minkowski in
`L²_τ`, constants, moments) is proved here; leaves: `SepSplit`, `SepMeanPart`, `SepOscPart`,
`SepMomentSplit`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- The `q`-independent lift of `G(x',Y)`. -/
def meanLift (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) :
    ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun x' Y _ => G x' Y

/-- The oscillation `F_⊥ = F - F̄`. -/
def perpPart (c : ℝ) (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) :
    ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun x' Y q => F x' Y q - phaseMean c F x' Y

/-- **Leaf 1** (linearity of `∇W`, SP 3735-3745): for `thinMoment c F < ∞` and a.e. `τ`,
`∇W(F) = ∇W(F̄) + ∇W(F_⊥)` at the receiver `y = xo/ε` (all three kernel integrals converge
absolutely there since `|y' - λz'| ≥ (ρ_i - ρ_o)/ε`). -/
def SepSplit : Prop :=
  ∀ (ν c ε ρo ρi : ℝ) (μ : ℂ), 0 < ν → 0 < c → 0 < ε → 0 ≤ ρo → ρo < ρi → -(1 / 4) < μ.re →
    ∀ F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
      (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) →
      (∀ x' Y q, F x' Y (q + c) = F x' Y q) →
      (∀ x' Y q, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → F x' Y q = 0) →
      thinMoment c F ≠ ⊤ →
      ∀ xo : Space, ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) →
        ∀ᵐ τ ∂(volume.restrict (Ioc 0 (2 * ε * c))),
          fderiv ℝ (fun y => sepW ν μ (thinSource ε F) y τ) (ε⁻¹ • xo) =
            fderiv ℝ (fun y => sepW ν μ (thinSource ε (meanLift (phaseMean c F))) y τ) (ε⁻¹ • xo) +
            fderiv ℝ (fun y => sepW ν μ (thinSource ε (perpPart c F)) y τ) (ε⁻¹ • xo)

/-- **Leaf 2** (mean part, SP 3735-3766, steps M1-M2): for a `q`-independent source `G(x',Y)`
(so `W` is `τ`-independent), `‖∇_yW(ε⁻¹xo) - ε³∇_xV_{μ,0}(xo)‖ ≤ P_ν ε⁴ ∫(1+|Y|)|G|`.
Uses `SepKernelBounds` with `t = νε²(1-λ²) ≤ ε²` (`ν ≤ 1`, `ε ≤ 1`): Taylor in `(x', εY)` to first
order along the segment (distance `≥ ρ_i - ρ_o` from the singularity) and the bound
`|D(K_t - K_0)| ≤ Ct|x|⁻⁶`. -/
def SepMeanPart : Prop :=
  ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, -(1 / 4) < μ.re) → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ ν c ε ρo ρi : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 → 0 ≤ ρo → ρo < ρi → ∀ μ ∈ K,
      ∀ G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j) →
        (∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0) →
        ∀ xo : Space, ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) → ∀ τ : ℝ,
          ‖fderiv ℝ (fun y => sepW ν μ (thinSource ε (meanLift G)) y τ) (ε⁻¹ • xo) -
              (ε ^ 3 : ℝ) • fderiv ℝ (sepVmu0 μ G) xo‖ₑ ≤
            ENNReal.ofReal (C * (1 + ν⁻¹ + c + ρi + ρo + (ρi - ρo)⁻¹) ^ k * ε ^ 4) *
              thinMoment c (meanLift G)

/-- **Leaf 3** (oscillatory part, SP 3768-3790, steps M3): for a zero-mean `c`-periodic source,
`‖∇_yW(ε⁻¹xo)‖_{L²_τ} ≤ P_ν ε⁴ N₁`, stated with a measurable majorant `B` of the pointwise
(a.e. `τ`) norm.  Proof: `J = ∂_q⁻¹` on zero-mean periodic functions (`norm_Jq_le`, `≤ c/(2π)`),
`F(q_ε(r,τ+2log λ)) = ελ ∂_λ[JF(...)]`, integrate by parts in `λ` (boundary at `λ = 1` kept,
`λ = 0` vanishes since `2Re μ + 3 > 0`); derivative of the kernel is
`-(x',εY)·∇(∇K_t) - 2νε²λ Δ∇K_t`; all bounded by `SepKernelBounds` (`j ≤ 3`). -/
def SepOscPart : Prop :=
  ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, -(1 / 4) < μ.re) → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ ν c ε ρo ρi : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 → 0 ≤ ρo → ρo < ρi → ∀ μ ∈ K,
      ∀ F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) →
        (∀ x' Y q, F x' Y (q + c) = F x' Y q) →
        (∀ x' Y q, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → F x' Y q = 0) →
        (∀ x' Y i j, ∫ q in Ioc 0 c, F x' Y q i j = 0) →
        ∀ xo : Space, ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) →
          ∃ B : ℝ → ℝ≥0∞, Measurable B ∧
            (∀ᵐ τ ∂(volume.restrict (Ioc 0 (2 * ε * c))),
              ‖fderiv ℝ (fun y => sepW ν μ (thinSource ε F) y τ) (ε⁻¹ • xo)‖ₑ ≤ B τ) ∧
            ltauAt (2 * ε * c) B ≤
              ENNReal.ofReal (C * (1 + ν⁻¹ + c + ρi + ρo + (ρi - ρo)⁻¹) ^ k * ε ^ 4) *
                thinMoment c F

/-- **Leaf 4** (Jensen/Minkowski in `L²(dq/c)`): the mean lift and the oscillation have moments
`≤ N₁` and `≤ 2N₁`. -/
def SepMomentSplit : Prop :=
  ∀ c : ℝ, 0 < c → ∀ F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
    (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) →
    thinMoment c (meanLift (phaseMean c F)) ≤ thinMoment c F ∧
      thinMoment c (perpPart c F) ≤ 2 * thinMoment c F

/-! ## Proved reductions -/

theorem ltauAt_mono_ae (P : ℝ) {g h : ℝ → ℝ≥0∞}
    (hgh : ∀ᵐ τ ∂(volume.restrict (Ioc 0 P)), g τ ≤ h τ) : ltauAt P g ≤ ltauAt P h := by
  unfold ltauAt
  have : ∫⁻ τ in Ioc 0 P, g τ ^ (2 : ℝ) ≤ ∫⁻ τ in Ioc 0 P, h τ ^ (2 : ℝ) :=
    lintegral_mono_ae (by filter_upwards [hgh] with τ hτ using ENNReal.rpow_le_rpow hτ (by norm_num))
  gcongr

theorem ltauAt_eq_lintegral (P : ℝ) (g : ℝ → ℝ≥0∞) :
    ltauAt P g = (∫⁻ τ, g τ ^ (2 : ℝ) ∂((ENNReal.ofReal P)⁻¹ • (volume.restrict (Ioc 0 P))))
      ^ (1 / 2 : ℝ) := by
  unfold ltauAt
  rw [lintegral_smul_measure, smul_eq_mul]

theorem ltauAt_add_le (P : ℝ) {g h : ℝ → ℝ≥0∞} (hg : Measurable g) (hh : Measurable h) :
    ltauAt P (fun τ => g τ + h τ) ≤ ltauAt P g + ltauAt P h := by
  rw [ltauAt_eq_lintegral, ltauAt_eq_lintegral, ltauAt_eq_lintegral]
  have := ENNReal.lintegral_Lp_add_le (μ := (ENNReal.ofReal P)⁻¹ • (volume.restrict (Ioc 0 P)))
    hg.aemeasurable hh.aemeasurable (p := 2) (by norm_num)
  simpa using this

theorem ltauAt_const (P : ℝ) (hP : 0 < P) (a : ℝ≥0∞) : ltauAt P (fun _ => a) = a := by
  unfold ltauAt
  rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Ioc, sub_zero]
  have h1 : (ENNReal.ofReal P)⁻¹ * (a ^ (2 : ℝ) * ENNReal.ofReal P) = a ^ (2 : ℝ) := by
    rw [mul_comm (a ^ (2 : ℝ)), ← mul_assoc, ENNReal.inv_mul_cancel
      (by simpa using hP) ENNReal.ofReal_ne_top, one_mul]
  rw [h1, ← ENNReal.rpow_mul]
  norm_num


theorem phaseMean_measurable (c : ℝ) (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hF : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) (i j : Fin 3) :
    Measurable fun w : (ℝ × ℝ) × ℝ => phaseMean c F w.1 w.2 i j := by
  have h1 : Measurable fun p : ((ℝ × ℝ) × ℝ) × ℝ => F p.1.1 p.1.2 p.2 i j :=
    (hF i j).comp (f := fun p : ((ℝ × ℝ) × ℝ) × ℝ => (p.1.1, p.1.2, p.2)) (by fun_prop)
  have h2 : Measurable fun w : (ℝ × ℝ) × ℝ => ∫ q in Ioc 0 c, F w.1 w.2 q i j :=
    (StronglyMeasurable.integral_prod_right (f := fun (w : (ℝ × ℝ) × ℝ) (q : ℝ) => F w.1 w.2 q i j)
      (ν := volume.restrict (Ioc 0 c)) h1.stronglyMeasurable).measurable
  exact (h2.const_mul c⁻¹)

theorem perpPart_meanZero (c : ℝ) (hc : 0 < c) (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (x' : ℝ × ℝ) (Y : ℝ) (i j : Fin 3) : ∫ q in Ioc 0 c, perpPart c F x' Y q i j = 0 := by
  by_cases hint : IntegrableOn (fun q => F x' Y q i j) (Ioc 0 c)
  · have hc' : IntegrableOn (fun _ : ℝ => phaseMean c F x' Y i j) (Ioc 0 c) :=
      integrableOn_const (by simp)
    have : (fun q => perpPart c F x' Y q i j) =
        fun q => F x' Y q i j - phaseMean c F x' Y i j := by
      funext q; simp [perpPart]
    rw [this, integral_sub hint hc']
    simp only [setIntegral_const, Real.volume_real_Ioc_of_le hc.le, sub_zero, smul_eq_mul]
    simp only [phaseMean]
    field_simp
    simp
  · have : ¬ IntegrableOn (fun q => perpPart c F x' Y q i j) (Ioc 0 c) := by
      intro h
      apply hint
      have hc' : IntegrableOn (fun _ : ℝ => phaseMean c F x' Y i j) (Ioc 0 c) :=
        integrableOn_const (by simp)
      have := h.add hc'
      refine this.congr_fun (fun q _ => ?_) measurableSet_Ioc
      simp [perpPart]
    exact integral_undef this


theorem sepMeanComparison_of (hs : SepSplit) (hm : SepMeanPart) (ho : SepOscPart)
    (hmo : SepMomentSplit) : SepMeanComparison := by
  intro K hK hKre
  obtain ⟨C1, k1, hC1, h1⟩ := hm K hK hKre
  obtain ⟨C2, k2, hC2, h2⟩ := ho K hK hKre
  refine ⟨C1 + 2 * C2 + 1, max k1 k2, by positivity, ?_⟩
  intro ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ μ hμ F hmeas hper hsupp xo hxo
  have hD : 0 < (ρi - ρo)⁻¹ := inv_pos.2 (by linarith)
  have hb1 : 1 ≤ 1 + ν⁻¹ + c + ρi + ρo + (ρi - ρo)⁻¹ := by
    have : 0 < ν⁻¹ := inv_pos.2 hν
    linarith
  set b := 1 + ν⁻¹ + c + ρi + ρo + (ρi - ρo)⁻¹ with hb
  by_cases hN : thinMoment c F = ⊤
  · rw [hN, ENNReal.mul_top]
    · exact le_top
    · have : 0 < (C1 + 2 * C2 + 1) * b ^ (max k1 k2) * ε ^ 4 := by positivity
      simpa using this
  have hsplit := hs ν c ε ρo ρi μ hν hc hε hρo hρ (hKre μ hμ) F hmeas hper hsupp hN xo hxo
  have hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => phaseMean c F w.1 w.2 i j :=
    phaseMean_measurable c F hmeas
  have hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → phaseMean c F x' Y = 0 := by
    intro x' Y h
    funext i j
    simp [phaseMean, hsupp x' Y _ h]
  have hA := h1 ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ μ hμ (phaseMean c F) hGm hGs xo hxo
  have hPm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => perpPart c F w.1 w.2.1 w.2.2 i j := by
    intro i j
    have := phaseMean_measurable c F hmeas i j
    exact (hmeas i j).sub (this.comp (f := fun w : (ℝ × ℝ) × ℝ × ℝ => (w.1, w.2.1)) (by fun_prop))
  have hPp : ∀ x' Y q, perpPart c F x' Y (q + c) = perpPart c F x' Y q := by
    intro x' Y q; simp [perpPart, hper]
  have hPs : ∀ x' Y q, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → perpPart c F x' Y q = 0 := by
    intro x' Y q h
    simp [perpPart, hsupp x' Y q h, hGs x' Y h]
  obtain ⟨B, hBm, hBae, hBle⟩ := h2 ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ μ hμ (perpPart c F) hPm hPp
    hPs (perpPart_meanZero c hc F) xo hxo
  obtain ⟨hm1, hm2⟩ := hmo c hc F hmeas
  set a : ℝ≥0∞ := ENNReal.ofReal (C1 * b ^ k1 * ε ^ 4) * thinMoment c (meanLift (phaseMean c F))
    with ha
  have hP : 0 < 2 * ε * c := by positivity
  calc ltauAt (2 * ε * c) (fun τ => ‖fderiv ℝ (fun y => sepW ν μ (thinSource ε F) y τ) (ε⁻¹ • xo) -
              (ε ^ 3 : ℝ) • fderiv ℝ (sepVmu0 μ (phaseMean c F)) xo‖ₑ)
      ≤ ltauAt (2 * ε * c) (fun τ => a + B τ) := by
        apply ltauAt_mono_ae
        filter_upwards [hsplit, hBae] with τ hτ hBτ
        rw [hτ]
        have heq : fderiv ℝ (fun y => sepW ν μ (thinSource ε (meanLift (phaseMean c F))) y τ) (ε⁻¹ • xo) +
            fderiv ℝ (fun y => sepW ν μ (thinSource ε (perpPart c F)) y τ) (ε⁻¹ • xo) -
            (ε ^ 3 : ℝ) • fderiv ℝ (sepVmu0 μ (phaseMean c F)) xo =
            (fderiv ℝ (fun y => sepW ν μ (thinSource ε (meanLift (phaseMean c F))) y τ) (ε⁻¹ • xo) -
            (ε ^ 3 : ℝ) • fderiv ℝ (sepVmu0 μ (phaseMean c F)) xo) +
            fderiv ℝ (fun y => sepW ν μ (thinSource ε (perpPart c F)) y τ) (ε⁻¹ • xo) := by abel
        rw [heq]
        refine (enorm_add_le (E := Space →L[ℝ] (Fin 3 → ℂ)) _ _).trans ?_
        gcongr
        exact hA τ
    _ ≤ ltauAt (2 * ε * c) (fun _ => a) + ltauAt (2 * ε * c) B :=
        ltauAt_add_le _ measurable_const hBm
    _ = a + ltauAt (2 * ε * c) B := by rw [ltauAt_const _ hP]
    _ ≤ ENNReal.ofReal (C1 * b ^ k1 * ε ^ 4) * thinMoment c F +
          ENNReal.ofReal (C2 * b ^ k2 * ε ^ 4) * (2 * thinMoment c F) := by
        refine add_le_add ?_ ?_
        · rw [ha]; gcongr
        · exact hBle.trans (by gcongr)
    _ = ENNReal.ofReal (C1 * b ^ k1 * ε ^ 4 + 2 * (C2 * b ^ k2 * ε ^ 4)) * thinMoment c F := by
        have h1' : 0 ≤ C1 * b ^ k1 * ε ^ 4 := by positivity
        have h2' : 0 ≤ C2 * b ^ k2 * ε ^ 4 := by positivity
        have e : ENNReal.ofReal (2 * (C2 * b ^ k2 * ε ^ 4)) =
            2 * ENNReal.ofReal (C2 * b ^ k2 * ε ^ 4) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]; simp
        rw [ENNReal.ofReal_add h1' (by positivity), e]
        ring
    _ ≤ ENNReal.ofReal ((C1 + 2 * C2 + 1) * b ^ (max k1 k2) * ε ^ 4) * thinMoment c F := by
        gcongr
        have e1 : b ^ k1 ≤ b ^ (max k1 k2) := pow_le_pow_right₀ hb1 (le_max_left _ _)
        have e2 : b ^ k2 ≤ b ^ (max k1 k2) := pow_le_pow_right₀ hb1 (le_max_right _ _)
        have hε4 : 0 ≤ ε ^ 4 := by positivity
        have hbk : 0 ≤ b ^ (max k1 k2) := by positivity
        have : C1 * b ^ k1 ≤ C1 * b ^ (max k1 k2) := by gcongr
        have : C2 * b ^ k2 ≤ C2 * b ^ (max k1 k2) := by gcongr
        nlinarith [mul_nonneg hε4 hbk]

end UnforcedLeray.Short.IIIa
