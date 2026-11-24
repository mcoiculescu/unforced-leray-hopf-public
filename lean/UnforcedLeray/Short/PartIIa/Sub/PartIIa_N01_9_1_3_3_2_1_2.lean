import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3_2_1
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.ClassicalGradBound.HeatIntGradSlice.HeatIntFderivComp
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.ClassicalGradBound.HeatIntGradSlice.MinkowskiSigma

/-!
# `PartII-a:N01/9/1/3/3/2/1/2` (decomposition): `HeatIntGradSlice`

Source `the November 2 reference manuscript`
lines 1684-1689, 3379-3383.  Minkowski in `L²(cell)` (σ-finite form, `minkowski_sq_sigmaFinite`) applied to
`∂_j u_i(s,x) = ∫₀^s (σ/s)^μ planeHeat(ν(s-σ))(∂_j f_σ,i)(x) dσ` (`heatIntFderivComp`), with the per-σ
smoothing bound `GradSliceL2` (from `PlaneHeatGradSmoothing`) and the joint measurability `GradSliceMeas`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01.HIGS

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.B0223 (MeridC)

/-- The `σ`-integrand modulus: `‖e^{ν(s-σ)Δ}(∂_j (f_σ)_i)(x)‖` with `f_σ = heatSlice c F σ`. -/
def gradE (c ν : ℝ) (F : Profile → MeridC) (s : ℝ) (i j : Fin 2) (σ : ℝ) (x : ℝ × ℝ) : ℝ≥0∞ :=
  ‖UnforcedLeray.B0224.planeHeat (ν * (s - σ))
    (fun z : ℝ × ℝ => fderiv ℝ (fun w : ℝ × ℝ => heatSlice c F σ w i) z
      (UnforcedLeray.B0579.dir j)) x‖ₑ

/-- **(M)** Joint measurability of `(σ,x) ↦ gradE σ x` on the strip `0 < σ < s` (zero elsewhere).
(For `0<σ<s` the function `(σ,x) ↦ planeHeat (ν(s-σ)) (∂_j f_σ,i) x` is continuous in `σ` for fixed `x`
(`HIFD.continuous_planeHeat_param`, `HeatSliceBounds`) and continuous in `x` for fixed `σ`; Carathéodory,
`measurable_uncurry_of_continuous_of_measurable`.) -/
def GradSliceMeas : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν → ∀ F : Profile → MeridC, IsSmoothForceFn c F →
    ∀ s : ℝ, 0 < s → ∀ i j : Fin 2,
      Measurable ((Ioo (0 : ℝ) s ×ˢ (univ : Set (ℝ × ℝ))).indicator
        (fun p : ℝ × (ℝ × ℝ) => gradE c ν F s i j p.1 p.2))

/-- **(L)** Per-`σ` bound (lines 3373-3383, 1684-1689): `planeHeatGradSmoothing` applied to
`f = (heatSlice c F σ) i` (`C¹`, `c`-periodic, bounded with bounded derivative by `heatSliceBounds`),
and `∫⁻_cell ‖f‖² = σ⁻² ∫⁻_cell ‖F(σ,·) i‖²` (`heatSlice c F σ w = σ⁻¹ • F (σ,w)` by periodicity). -/
def GradSliceL2 : Prop :=
  ∃ C0 : ℝ, ∀ (c ν : ℝ), 0 < c → 0 < ν → ∀ F : Profile → MeridC, IsSmoothForceFn c F →
    ∀ s : ℝ, 0 < s → ∀ i j : Fin 2, ∀ σ : ℝ, σ ∈ Ioo (0 : ℝ) s →
      (∫⁻ x in UnforcedLeray.B0579.cell c, gradE c ν F s i j σ x ^ 2) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C0 * (ν * (s - σ)) ^ (-(1 / 2 : ℝ))) *
          (ENNReal.ofReal σ⁻¹ * (∫⁻ x in UnforcedLeray.B0579.cell c, ‖F (σ, x) i‖ₑ ^ 2) ^ (1 / 2 : ℝ))

/-- Pointwise Minkowski step: `heatIntFderivComp` and `‖∫‖ ≤ ∫‖·‖`. -/
theorem gradSlice_pointwise (c ν : ℝ) (hc : 0 < c) (hν : 0 < ν) (μ : ℂ) (F : Profile → MeridC)
    (hF : IsSmoothForceFn c F) (s : ℝ) (hs : 0 < s) (i j : Fin 2) (y : ℝ × ℝ) :
    ‖fderiv ℝ (fun z : ℝ × ℝ => smoothHeatInt c ν μ F (s, z) i) y (UnforcedLeray.B0579.dir j)‖ₑ ≤
      ∫⁻ σ in Ioo (0 : ℝ) s, ENNReal.ofReal ((σ / s) ^ μ.re) * gradE c ν F s i j σ y := by
  obtain ⟨_, e⟩ := heatIntFderivComp c ν hc hν μ F hF s hs y i j
  rw [e, intervalIntegral.integral_of_le hs.le]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [setLIntegral_congr (Ioo_ae_eq_Ioc (μ := volume) (a := 0) (b := s)).symm]
  refine (setLIntegral_congr_fun measurableSet_Ioo (fun σ hσ => ?_)).le
  rw [enorm_smul]
  congr 1
  have h0 : 0 < σ / s := div_pos hσ.1 hs
  rw [← ofReal_norm, Complex.norm_cpow_eq_rpow_re_of_pos h0]


theorem sq_half_eq (a : ℝ≥0∞) : (a ^ 2) ^ (1 / 2 : ℝ) = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Assembly of `HeatIntGradSlice` from the measurability and per-slice smoothing bounds. -/
theorem heatIntGradSlice_of (hM : GradSliceMeas) (hL : GradSliceL2) : HeatIntGradSlice := by
  obtain ⟨C0, hC0⟩ := hL
  refine ⟨|C0|, ?_⟩
  intro c ν hc hν μ F hF s hs i j
  set Φ : ℝ → ℝ≥0∞ := fun σ => (∫⁻ x in UnforcedLeray.B0579.cell c, ‖F (σ, x) i‖ₑ ^ 2) ^ (1 / 2 : ℝ)
    with hΦ
  set a : ℝ → ℝ≥0∞ := fun σ => ENNReal.ofReal ((σ / s) ^ μ.re) with ha
  set H : ℝ → ℝ × ℝ → ℝ≥0∞ := fun σ x => a σ *
    (Ioo (0 : ℝ) s ×ˢ (univ : Set (ℝ × ℝ))).indicator
      (fun p : ℝ × (ℝ × ℝ) => gradE c ν F s i j p.1 p.2) (σ, x) with hH
  have ham : Measurable a :=
    ENNReal.measurable_ofReal.comp ((measurable_id.div_const s).pow_const _)
  have hHm : Measurable (fun p : ℝ × (ℝ × ℝ) => H p.1 p.2) :=
    (ham.comp measurable_fst).mul (hM c ν hc hν F hF s hs i j)
  have hHin : ∀ σ ∈ Ioo (0 : ℝ) s, ∀ x, H σ x = a σ * gradE c ν F s i j σ x := by
    intro σ hσ x
    simp [hH, Set.indicator_of_mem (show (σ, x) ∈ Ioo (0 : ℝ) s ×ˢ (univ : Set (ℝ × ℝ)) from
      ⟨hσ, mem_univ _⟩)]
  have h1 : ∀ x, ‖fderiv ℝ (fun y : ℝ × ℝ => smoothHeatInt c ν μ F (s, y) i) x
      (UnforcedLeray.B0579.dir j)‖ₑ ≤ ∫⁻ σ in Ioo (0 : ℝ) s, H σ x := by
    intro x
    refine (gradSlice_pointwise c ν hc hν μ F hF s hs i j x).trans (le_of_eq ?_)
    exact setLIntegral_congr_fun measurableSet_Ioo (fun σ hσ => by rw [hHin σ hσ x])
  have h2 : ∫⁻ x in UnforcedLeray.B0579.cell c,
      ‖fderiv ℝ (fun y : ℝ × ℝ => smoothHeatInt c ν μ F (s, y) i) x
        (UnforcedLeray.B0579.dir j)‖ₑ ^ 2 ≤
      ∫⁻ x in UnforcedLeray.B0579.cell c, (∫⁻ σ in Ioo (0 : ℝ) s, H σ x) ^ 2 :=
    lintegral_mono fun x => by gcongr; exact h1 x
  have h3 := UnforcedLeray.Short.PartIIa.N01.MinkowskiL2.minkowski_sq_sigmaFinite
    (μ := volume.restrict (Ioo (0 : ℝ) s))
    (ν := volume.restrict (UnforcedLeray.B0579.cell c)) H hHm
  have h4 : ∀ σ ∈ Ioo (0 : ℝ) s,
      (∫⁻ x in UnforcedLeray.B0579.cell c, H σ x ^ 2) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal |C0| * (ENNReal.ofReal (gradKernel μ.re ν s σ) * Φ σ) := by
    intro σ hσ
    have hσ0 : 0 < σ := hσ.1
    have hθ : 0 < ν * (s - σ) := mul_pos hν (sub_pos.2 hσ.2)
    have e1 : ∫⁻ x in UnforcedLeray.B0579.cell c, H σ x ^ 2 =
        a σ ^ 2 * ∫⁻ x in UnforcedLeray.B0579.cell c, gradE c ν F s i j σ x ^ 2 := by
      rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
      exact lintegral_congr fun x => by rw [hHin σ hσ x, mul_pow]
    rw [e1, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), sq_half_eq]
    have hb := hC0 c ν hc hν F hF s hs i j σ hσ
    have t0 : 0 ≤ (ν * (s - σ)) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hθ.le _
    have hle : ENNReal.ofReal (C0 * (ν * (s - σ)) ^ (-(1 / 2 : ℝ))) ≤
        ENNReal.ofReal |C0| * ENNReal.ofReal ((ν * (s - σ)) ^ (-(1 / 2 : ℝ))) := by
      rw [← ENNReal.ofReal_mul (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) t0)
    have hgk : ENNReal.ofReal (gradKernel μ.re ν s σ) = a σ *
        ENNReal.ofReal ((ν * (s - σ)) ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal σ⁻¹ := by
      have : 0 ≤ (σ / s) ^ μ.re := Real.rpow_nonneg (div_pos hσ0 hs).le _
      rw [gradKernel, div_eq_mul_inv, ENNReal.ofReal_mul (mul_nonneg this t0),
        ENNReal.ofReal_mul this]
    calc a σ * _ ≤ a σ * (ENNReal.ofReal |C0| * ENNReal.ofReal ((ν * (s - σ)) ^ (-(1 / 2 : ℝ))) *
          (ENNReal.ofReal σ⁻¹ * Φ σ)) :=
        by gcongr; exact hb.trans (by gcongr)
      _ = _ := by rw [hgk]; ring
  have h5 : ∫⁻ σ in Ioo (0 : ℝ) s, (∫⁻ x in UnforcedLeray.B0579.cell c, H σ x ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal |C0| * ∫⁻ σ in Ioo (0 : ℝ) s, ENNReal.ofReal (gradKernel μ.re ν s σ) * Φ σ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' measurableSet_Ioo h4
  calc _ ≤ _ := h2
    _ ≤ _ := h3
    _ ≤ (ENNReal.ofReal |C0| * ∫⁻ σ in Ioo (0 : ℝ) s, ENNReal.ofReal (gradKernel μ.re ν s σ) * Φ σ) ^ 2 := by
        gcongr
    _ = _ := by
        rw [mul_pow, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

end UnforcedLeray.Short.PartIIa.N01.HIGS
