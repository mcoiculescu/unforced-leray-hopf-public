import UnforcedLeray.Lib.CylinderB.Tests
import UnforcedLeray.Lib.Cylinder.CellModes

/-!
# Mode pairings on the cylinder (helpers of CY12 and CY13)


(CY12, CY13; bypass BP7 "per q-mode"). For a real `g ∈ L²(cell)` and a one-dimensional test
`ψ`, the pairings of `g` with the cylinder tests `cos(k_n q) ψ(η)` and `sin(k_n q) ψ(η)`
(`k_n = 2πn/c`) determine the pairing of the `n`-th `q`-mode `g^(n)` (CY04 `qMode`) with `ψ`:

  `∫_cell cos(k_n q) ψ(η) g − i ∫_cell sin(k_n q) ψ(η) g = c ∫ ψ(η) g^(n)(η) dη`
  (`pairC_eq`).

Together with `memLp_qMode` (`g^(n) ∈ L²(ℝ)`, Bessel) and `ae_eq_zero_of_qMode` (all modes
vanish ⇒ `g = 0`, Parseval `hasSum_cell_parseval` of CY04), this reduces cylinder Liouville
statements to the one-dimensional lemmas of `Liouville1D`. Manuscript: B0172
(`paper/main.tex` lines 2589–2598, "Parseval in q") and B0935 (line 14360).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Complex
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Cyl

variable {c : ℝ}

/-- The complex pairing `∫ cos(kq)ψ g − i ∫ sin(kq)ψ g` of a real cell function with the
`n`-th mode tests. -/
def pairC (c : ℝ) (n : ℤ) (g : Plane → ℝ) (ψ : ℝ → ℝ) : ℂ :=
  ((∫ z in cell c, cosTest (freq c n) ψ z * g z : ℝ) : ℂ) -
    ((∫ z in cell c, sinTest (freq c n) ψ z * g z : ℝ) : ℂ) * I

/-- The `L²(cell)` functions of the unweighted pairing. -/
theorem memLp_cell_of_wμ_one {g : Plane → ℝ} (hg : MemLp g 2 (cellμ c)) :
    MemLp g 2 (Sob.wμ (Sob.cylinder c).μ (1 : Sob.Weight Plane)) := by
  have : Sob.wμ (Sob.cylinder c).μ (1 : Sob.Weight Plane) = cellμ c := by
    rw [Sob.wμ, cylinder_μ_eq]
    have : (fun x => ENNReal.ofReal ((1 : Sob.Weight Plane) x)) = 1 := by funext x; simp
    rw [this, withDensity_one]
  rw [this]; exact hg

/-- A cylinder test times an `L²(cell)` function is integrable on the cell. -/
theorem integrableOn_test_mul {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ) {g : Plane → ℝ}
    (hg : MemLp g 2 (cellμ c)) : IntegrableOn (fun z => φ z * g z) (cell c) := by
  have h := Sob.integrable_smul_of_memLp (p := 2) (Sob.CompactlyBounded.of_adm
    (D := Sob.cylinder c) hφ) (memLp_cell_of_wμ_one hg)
  rw [cylinder_μ_eq] at h
  have h2 : Integrable (fun z => φ z * g z) (cellμ c) := by simpa only [smul_eq_mul] using h
  exact h2

theorem fourier_neg_eq (hc : 0 < c) (n : ℤ) (q : ℝ) :
    (fourier (-n) (q : AddCircle (c / 2 - -c / 2)) : ℂ) =
      (Real.cos (freq c n * q) : ℂ) - (Real.sin (freq c n * q) : ℂ) * I := by
  rw [fourier_coe_apply, half_sub_neg_half]
  have e : 2 * (Real.pi : ℂ) * I * ((-n : ℤ) : ℂ) * (q : ℂ) / (c : ℂ) =
      ((-(freq c n * q) : ℝ) : ℂ) * I := by
    simp only [freq]; push_cast
    field_simp
  rw [e, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg]
  push_cast; ring

/-- **The mode pairing** (BP7): `∫ cos(k_n q)ψ g − i ∫ sin(k_n q)ψ g = c ∫ ψ g^(n)`. -/
theorem pairC_eq (hc : 0 < c) (n : ℤ) {g : Plane → ℝ} (hg : MemLp g 2 (cellμ c)) {ψ : ℝ → ℝ}
    (hψ : OneD.Test ψ) :
    pairC c n g ψ = (c : ℂ) * ∫ η, ψ η • qMode c hc n (fun z => (g z : ℂ)) η := by
  have hcos := integrableOn_test_mul (isCylTest_cosTest hc n hψ) hg
  have hsin := integrableOn_test_mul (isCylTest_sinTest hc n hψ) hg
  set F : Plane → ℂ := fun z =>
    ((cosTest (freq c n) ψ z * g z : ℝ) : ℂ) - ((sinTest (freq c n) ψ z * g z : ℝ) : ℂ) * I
    with hF
  have hcosC : Integrable (fun z => ((cosTest (freq c n) ψ z * g z : ℝ) : ℂ))
      (volume.restrict (cell c)) := hcos.ofReal
  have hsinC : Integrable (fun z => ((sinTest (freq c n) ψ z * g z : ℝ) : ℂ) * I)
      (volume.restrict (cell c)) := (hsin.ofReal (𝕜 := ℂ)).mul_const I
  have hFi : IntegrableOn F (cell c) := hcosC.sub hsinC
  have hpair : pairC c n g ψ = ∫ z in cell c, F z := by
    simp only [pairC, hF]
    rw [integral_sub hcosC hsinC, integral_mul_const, integral_complex_ofReal,
      integral_complex_ofReal]
  have hFq : ∀ z : Plane, F z =
      (ψ z.2 : ℂ) * ((fourier (-n) (z.1 : AddCircle (c / 2 - -c / 2)) : ℂ) * (g z : ℂ)) := by
    intro z
    rw [fourier_neg_eq hc]
    simp only [hF, cosTest, sinTest]
    push_cast; ring
  rw [hpair, integral_cell_eq_integral_integral hFi, ← integral_const_mul]
  congr 1
  funext η
  rw [qMode_eq_setIntegral hc, Complex.real_smul]
  have : ∫ q in Ico (-c / 2) (c / 2), F (q, η) = (ψ η : ℂ) *
      ∫ q in Ico (-c / 2) (c / 2), (fourier (-n) (q : AddCircle (c / 2 - -c / 2)) : ℂ) *
        (g (q, η) : ℂ) := by
    rw [← integral_const_mul]
    congr 1; funext q; exact hFq (q, η)
  rw [this]
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  field_simp

/-! ### Bessel and Parseval in the form used -/

theorem lintegral_tsum_qMode (hc : 0 < c) {f : Plane → ℂ} (hf : MemLp f 2 (cellμ c)) :
    ∫⁻ η, ∑' m : ℤ, ‖qMode c hc m f η‖ₑ ^ 2 =
      ENNReal.ofReal c⁻¹ * ∫⁻ z in cell c, ‖f z‖ₑ ^ 2 := by
  have hm : AEStronglyMeasurable f (cellμ c) := hf.1
  have hae := ae_memLp_slice two_ne_zero ENNReal.ofNat_ne_top hf
  rw [lintegral_congr_ae (hae.mono fun η hη => tsum_enorm_sq_qMode hc η hη),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  have hm' := hm.enorm.pow_const 2
  rw [cellμ_eq_prod] at hm'
  rw [cellμ_eq_restrict, cellμ_eq_prod, lintegral_prod_symm _ hm']

/-- **Bessel**: every `q`-mode of `f ∈ L²(cell)` lies in `L²(ℝ)`. -/
theorem memLp_qMode (hc : 0 < c) (n : ℤ) {f : Plane → ℂ} (hf : MemLp f 2 (cellμ c)) :
    MemLp (qMode c hc n f) 2 volume := by
  refine ⟨aestronglyMeasurable_qMode hc n hf.1, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have hL : ∫⁻ z in cell c, ‖f z‖ₑ ^ 2 < ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero
      ENNReal.ofNat_ne_top).1 hf.2
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
    exact h
  calc ∫⁻ η, ‖qMode c hc n f η‖ₑ ^ 2 ≤ ∫⁻ η, ∑' m : ℤ, ‖qMode c hc m f η‖ₑ ^ 2 :=
        lintegral_mono fun η => ENNReal.le_tsum (f := fun m : ℤ => ‖qMode c hc m f η‖ₑ ^ 2) n
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ z in cell c, ‖f z‖ₑ ^ 2 := lintegral_tsum_qMode hc hf
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL

/-- **Parseval uniqueness**: if every `q`-mode of `f ∈ L²(cell)` vanishes, then `f = 0`. -/
theorem ae_eq_zero_of_qMode (hc : 0 < c) {f : Plane → ℂ} (hf : MemLp f 2 (cellμ c))
    (h : ∀ n : ℤ, qMode c hc n f =ᵐ[volume] 0) : f =ᵐ[cellμ c] 0 := by
  have hP := hasSum_cell_parseval hc hf
  have hz : ∀ n : ℤ, c * ∫ η, ‖qMode c hc n f η‖ ^ 2 = 0 := by
    intro n
    rw [integral_congr_ae (g := fun _ => (0 : ℝ)) ((h n).mono fun η hη => by simp [hη]),
      integral_zero, mul_zero]
  simp_rw [hz] at hP
  have h0 : ∫ z in cell c, ‖f z‖ ^ 2 = 0 := hP.unique hasSum_zero
  have hint : Integrable (fun z => ‖f z‖ ^ 2) (cellμ c) :=
    (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  have := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg ‖f z‖) hint).1 h0
  filter_upwards [this] with z hz
  simpa using hz

/-! ### Weak derivatives on modes -/

theorem integral_test_smul_qMode_integrable (hc : 0 < c) (n : ℤ) {f : Plane → ℂ}
    (hf : MemLp f 2 (cellμ c)) {ψ : ℝ → ℝ} (hψ : OneD.Test ψ) :
    Integrable (fun η => ψ η • qMode c hc n f η) volume :=
  OneD.integrable_smul_of_test hψ (memLp_qMode hc n hf)

end UnforcedLeray.Cyl
