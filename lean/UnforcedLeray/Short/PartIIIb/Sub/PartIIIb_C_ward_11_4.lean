import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.HBound.Young
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_11_4.H2

/-!
# `PartIII-b:C/ward/11/4`: `WardDXYoungSup` from the sup bounds of `X₀` and the stream correction

Source of record: `the November 2 reference manuscript` (73 pages), 5238-5244.

`X = χ_y X₀ + corr` (`wardX_eq_cut_add_corr`, 4180-4186).  The product rule for the cut part is
proved here (the scalar `χ_y(ν·age)` has a bounded gradient on `ϱ ≥ R√ν`); the two analytic
leaves are

* `WardX0DSup`: differentiability and `L^∞_τL^∞_y` bounds of `X₀` and `∂_jX₀` on `ϱ ≥ R√ν`
  (Cauchy-Schwarz in `sep:resolvent` 3621-3629, kernel `sep:kernel` 3603-3611);
* `WardCorrDSup`: the same for the stream correction (primitive `Ψ`, majorant 3687-3713).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **`X₀` and `∂_jX₀` are differentiable at, and uniformly bounded on, the young receivers**
(source 5238-5244): for old `L²` data, at every phase and every `y` with `ϱ y ≥ R√ν` (the gap
`D = R√ν(1 - √(5/6))` to the old disk), `X₀(τ,·)` is differentiable at `y` and
`|X₀(τ,y)|, |∂_jX₀(τ,y)| ≤ C‖g‖_{L²(s^{-1/2}dς)}`.  Differentiation under the integral of
`sepW` (`IIIa.sepWDiffUnder_proved`), then Cauchy-Schwarz in `sep:resolvent` 3621-3629 over
`(λ, z)` with the kernel bounds `|D^j∇K_t(x)| ≤ C|x|^{-4-j}` (`sep:kernel` 3603-3611), square
integrable across the gap, and the periodic geometric sum of one-period `L²_τL²` norms
(`T` is `P`-periodic, `∫_0^∞ e^{-at}‖T(τ-t)‖²dt`, `a > 0` for `μ > -1/4`). -/
def WardX0DSup : Prop :=
  ∀ (ν μ R c : ℝ), 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      ∀ (τ : ℝ) (y : Space), R * Real.sqrt ν ≤ ϱ y →
        DifferentiableAt ℝ (wardX0 ν μ R c g τ) y ∧
        ‖wardX0 ν μ R c g τ y‖ ≤ C * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal ∧
        ∀ j : Fin 3,
          ‖physPd (wardX0 ν μ R c g τ) j y‖ ≤ C * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal

/-- **The stream-cutoff correction `(χ_y'/r)Ψ_{X₀}e_z`** (source 4178-4186, 3687-3713): for old
`L²` data it is differentiable at every `y` with `ϱ y ≥ R√ν` and `|∂_j corr| ≤ C‖g‖`.  The
primitive `Ψ(r,z) = -∫_r^∞ ρ X₀_z(ρ,0,z)dρ` and its `z`-derivative are bounded by the
translation-invariant majorant `CD^{-2}(D² + |z - z_src|²)^{-1}1_{|y'-z'_src| ≤ CD}` of `L¹`
norm `CD^{-1}` (3687-3713), followed by the Cauchy-Schwarz/geometric-sum bound of
`WardX0DSup`; `χ_y'` is supported on `R√ν ≤ ϱ ≤ R√(5ν/4)` and bounded, `ϱ ≥ R√ν`. -/
def WardCorrDSup : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), IsYoungCutoff χy → 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ →
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g →
      ∀ (τ : ℝ) (y : Space), R * Real.sqrt ν ≤ ϱ y →
        DifferentiableAt ℝ (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) y ∧
        ∀ j : Fin 3, ‖physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y‖ ≤
          C * (eLpNorm g 2 (ageμ c (-1 / 2))).toReal

/-! ## The scalar cutoff `χ_y(ν·age)` -/

theorem w114_coord_abs_le (j i : Fin 3) : |(coordinateVector j : Space) i| ≤ 1 := by
  have h : ‖(coordinateVector j : Space)‖ = 1 := by
    simp [coordinateVector]
  calc |(coordinateVector j : Space) i| = ‖(coordinateVector j : Space) i‖ := rfl
    _ ≤ ‖(coordinateVector j : Space)‖ := PiLp.norm_apply_le _ _
    _ = 1 := h

theorem w114_deriv_bound {χ : ℝ → ℝ} (hχ : IsYoungCutoff χ) :
    ∃ M : ℝ, ∀ t, |deriv χ t| ≤ M := by
  have hc : Continuous (deriv χ) := hχ.smooth.continuous_deriv (by simp)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨M, fun t => ?_⟩
  by_cases h0 : t ∈ Icc (0 : ℝ) 1
  · simpa using hM t h0
  · have hzero : deriv χ t = 0 := by
      rcases not_and_or.1 h0 with h | h
      · have ht : t < 0 := not_le.1 h
        have : χ =ᶠ[𝓝 t] fun _ => 1 := by
          filter_upwards [Iio_mem_nhds (show t < 4 / 5 by linarith)] with s hs
          exact hχ.one s hs.le
        rw [this.deriv_eq]; simp
      · have ht : 1 < t := not_le.1 h
        have : χ =ᶠ[𝓝 t] fun _ => 0 := by
          filter_upwards [Ioi_mem_nhds ht] with s hs
          exact hχ.zero s hs.le
        rw [this.deriv_eq]; simp
    rw [hzero, abs_zero]
    have := hM 0 (by simp)
    exact (abs_nonneg _).trans (by simpa using this)

/-- The scalar `χ_y(ν·age R ·)` is differentiable on `ϱ ≥ R√ν` with a bounded derivative. -/
theorem w114_scalar {χ : ℝ → ℝ} (hχ : IsYoungCutoff χ) {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) :
    ∃ M : ℝ, ∀ y : Space, R * Real.sqrt ν ≤ ϱ y →
      DifferentiableAt ℝ (fun y' => χ (ν * age R y')) y ∧
        ∀ j : Fin 3, |fderiv ℝ (fun y' => χ (ν * age R y')) y (coordinateVector j)| ≤ M := by
  obtain ⟨M0, hM0⟩ := w114_deriv_bound hχ
  refine ⟨M0 * (4 * ν * R ^ 2 / (R * Real.sqrt ν) ^ 3), fun y hy => ?_⟩
  have hρ : 0 < R * Real.sqrt ν := mul_pos hR (Real.sqrt_pos.2 hν)
  have hρy : 0 < ϱ y := lt_of_lt_of_le hρ hy
  set q : Space → ℝ := fun y' => y' 0 * y' 0 + y' 1 * y' 1 with hqdef
  have hqy : q y = ϱ y ^ 2 := by
    unfold ϱ; rw [Real.sq_sqrt (by positivity)]; simp [hqdef]; ring
  have hq0 : q y ≠ 0 := by rw [hqy]; positivity
  have hage : ∀ y', age R y' = R ^ 2 * (q y')⁻¹ := by
    intro y'
    unfold age ϱ
    rw [Real.sq_sqrt (by positivity)]
    simp [hqdef, div_eq_mul_inv, sq]
  have hp0 : HasFDerivAt (fun y' : Space => y' 0) (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).hasFDerivAt
  have hp1 : HasFDerivAt (fun y' : Space => y' 1) (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).hasFDerivAt
  have hq : HasFDerivAt q ((2 * y 0) • (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ) +
      (2 * y 1) • (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ)) y := by
    refine ((hp0.mul hp0).add (hp1.mul hp1)).congr_fderiv ?_
    module
  have hinv := (hasDerivAt_inv hq0).comp_hasFDerivAt y hq
  have hin0 := (hinv.const_mul (R ^ 2)).const_mul ν
  have hin : HasFDerivAt (fun y' => ν * age R y')
      ((ν * R ^ 2) • (-(q y ^ 2)⁻¹ • ((2 * y 0) • (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ) +
        (2 * y 1) • (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ)))) y := by
    have hfun : (fun y' => ν * age R y') =
        fun y' => ν * (R ^ 2 * ((fun x : ℝ => x⁻¹) ∘ q) y') :=
      funext fun y' => by simp [hage]
    rw [hfun]
    refine hin0.congr_fderiv ?_
    module
  have hχd : HasDerivAt χ (deriv χ (ν * age R y)) (ν * age R y) :=
    (hχ.smooth.differentiable (by simp) _).hasDerivAt
  have hcomp := hχd.comp_hasFDerivAt y hin
  refine ⟨hcomp.differentiableAt, fun j => ?_⟩
  have hf : fderiv ℝ (fun y' => χ (ν * age R y')) y = _ := hcomp.fderiv
  have hy0 : |y 0| ≤ ϱ y := by
    unfold ϱ; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (y 1)])
  have hy1 : |y 1| ≤ ϱ y := by
    unfold ϱ; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (y 0)])
  have hc0 := w114_coord_abs_le j 0
  have hc1 := w114_coord_abs_le j 1
  have hm0 := mul_le_mul hy0 hc0 (abs_nonneg _) hρy.le
  have hm1 := mul_le_mul hy1 hc1 (abs_nonneg _) hρy.le
  have hs : |(2 * y 0) * (coordinateVector j : Space) 0 + (2 * y 1) * (coordinateVector j : Space) 1|
      ≤ 4 * ϱ y := by
    calc _ ≤ |(2 * y 0) * (coordinateVector j : Space) 0| +
            |(2 * y 1) * (coordinateVector j : Space) 1| := abs_add_le _ _
      _ ≤ 2 * ϱ y + 2 * ϱ y := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul]
          have : |(2 : ℝ)| = 2 := by norm_num
          rw [this]
          nlinarith
      _ = 4 * ϱ y := by ring
  have hden : |(q y ^ 2)⁻¹| = (ϱ y ^ 4)⁻¹ := by
    rw [hqy, abs_of_nonneg (by positivity)]; congr 1; ring
  have hM0nn : 0 ≤ M0 := (abs_nonneg _).trans (hM0 0)
  have hνR : 0 ≤ ν * R ^ 2 := by positivity
  have hev : fderiv ℝ (fun y' => χ (ν * age R y')) y (coordinateVector j) =
      deriv χ (ν * age R y) * ((ν * R ^ 2) * (-(q y ^ 2)⁻¹ *
        ((2 * y 0) * (coordinateVector j : Space) 0 + (2 * y 1) * (coordinateVector j : Space) 1))) := by
    rw [hf]
    simp [EuclideanSpace.proj]
    ring
  rw [hev]
  simp only [abs_mul, abs_neg, hden, abs_pow, abs_of_pos hν, abs_of_pos hR]
  have h3 : ϱ y ^ 3 ≤ ϱ y ^ 3 := le_rfl
  have hRr : (R * Real.sqrt ν) ^ 3 ≤ ϱ y ^ 3 := pow_le_pow_left₀ hρ.le hy 3
  have hkey : ν * R ^ 2 * ((ϱ y ^ 4)⁻¹ * (4 * ϱ y)) ≤ 4 * ν * R ^ 2 / (R * Real.sqrt ν) ^ 3 := by
    have e : ν * R ^ 2 * ((ϱ y ^ 4)⁻¹ * (4 * ϱ y)) = 4 * ν * R ^ 2 / ϱ y ^ 3 := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hRr
  calc _
      ≤ M0 * (ν * R ^ 2 * ((ϱ y ^ 4)⁻¹ * (4 * ϱ y))) := by
        gcongr
        · exact hM0 _
    _ ≤ M0 * (4 * ν * R ^ 2 / (R * Real.sqrt ν) ^ 3) := by gcongr

/-- **`WardDXYoungSup` from the two leaves** (product rule for `χ_y(ν·age)•X₀`, then the sum with
the stream correction; source 5238-5244). -/
theorem wardDXYoungSup_of (h0 : WardX0DSup) (hc : WardCorrDSup) : WardDXYoungSup := by
  intro ν μ R c χy hχ hν hR hc0 hμ
  obtain ⟨C1, h1⟩ := h0 ν μ R c hν hR hc0 hμ
  obtain ⟨C2, h2⟩ := hc ν μ R c χy hχ hν hR hc0 hμ
  obtain ⟨M, hM⟩ := w114_scalar hχ hν hR
  refine ⟨C1 + M * C1 + C2, fun g hg τ y hy j => ?_⟩
  set N := (eLpNorm g 2 (ageμ c (-1 / 2))).toReal with hN
  obtain ⟨hd1, hb0, hb1⟩ := h1 g hg τ y hy
  obtain ⟨hd2, hb2⟩ := h2 g hg τ y hy
  obtain ⟨hds, hMs⟩ := hM y hy
  have hfun : wardX ν μ R c χy g τ =
      (fun y' => χy (ν * age R y') • wardX0 ν μ R c g τ y') +
        wardStreamCorr ν R χy (wardX0 ν μ R c g) τ :=
    funext fun y' => wardX_eq_cut_add_corr ν μ R c χy g τ y'
  have hdc : DifferentiableAt ℝ (fun y' => χy (ν * age R y') • wardX0 ν μ R c g τ y') y :=
    hds.smul hd1
  have hE : physPd (wardX ν μ R c χy g τ) j y =
      χy (ν * age R y) • physPd (wardX0 ν μ R c g τ) j y +
        (fderiv ℝ (fun y' => χy (ν * age R y')) y (coordinateVector j)) •
          wardX0 ν μ R c g τ y +
        physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y := by
    unfold physPd
    have hsm : HasFDerivAt (fun y' => χy (ν * age R y') • wardX0 ν μ R c g τ y')
        (χy (ν * age R y) • fderiv ℝ (wardX0 ν μ R c g τ) y +
          (fderiv ℝ (fun y' => χy (ν * age R y')) y).smulRight (wardX0 ν μ R c g τ y)) y :=
      hds.hasFDerivAt.smul hd1.hasFDerivAt
    rw [hfun, fderiv_add hdc hd2, hsm.fderiv]
    simp [add_assoc]
  have hr := hχ.range (ν * age R y)
  rw [hE]
  have hMn : 0 ≤ M := (abs_nonneg _).trans (hMs j)
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  calc _ ≤ ‖χy (ν * age R y) • physPd (wardX0 ν μ R c g τ) j y +
          (fderiv ℝ (fun y' => χy (ν * age R y')) y (coordinateVector j)) •
            wardX0 ν μ R c g τ y‖ +
        ‖physPd (wardStreamCorr ν R χy (wardX0 ν μ R c g) τ) j y‖ := norm_add_le _ _
    _ ≤ (‖χy (ν * age R y) • physPd (wardX0 ν μ R c g τ) j y‖ +
          ‖(fderiv ℝ (fun y' => χy (ν * age R y')) y (coordinateVector j)) •
            wardX0 ν μ R c g τ y‖) + C2 * N := by
        gcongr
        · exact norm_add_le _ _
        · exact hb2 j
    _ ≤ (C1 * N + M * (C1 * N)) + C2 * N := by
        gcongr
        · rw [norm_smul, Real.norm_of_nonneg hr.1]
          calc _ ≤ 1 * ‖physPd (wardX0 ν μ R c g τ) j y‖ := by gcongr; exact hr.2
            _ ≤ C1 * N := by rw [one_mul]; exact hb1 j
        · rw [norm_smul, Real.norm_eq_abs]
          have := hMs j
          have hb := hb0
          have hnn : 0 ≤ ‖wardX0 ν μ R c g τ y‖ := norm_nonneg _
          exact mul_le_mul this hb hnn hMn
    _ = _ := by ring

theorem wardDXYoungSup_proved_of (h0 : WardX0DSup) (hc : WardCorrDSup) : WardDXYoungSup :=
  wardDXYoungSup_of h0 hc

theorem wardX0DSup_proved : WardX0DSup := w114_wardX0DSup_proved

theorem wardCorrDSup_proved : WardCorrDSup := w114_wardCorrDSup_proved

/-- **`DX ∈ L^∞_{τ,y}` on the young support** (`PartIII-b:C/ward/11/4`, source 5238-5244). -/
theorem wardDXYoungSup_proved : WardDXYoungSup :=
  wardDXYoungSup_of wardX0DSup_proved wardCorrDSup_proved

end UnforcedLeray.Short.PartIIIb.Concrete
