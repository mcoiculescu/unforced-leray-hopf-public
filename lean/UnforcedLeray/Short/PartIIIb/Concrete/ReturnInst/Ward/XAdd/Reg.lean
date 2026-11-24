import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Defs
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L7
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.IntAll
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.IntCong

/-!
# Old `L²` data are separated sources, and `sepW` is additive on them
(source 4155-4171, 3611-3621)

Source of record: `the November 2 reference manuscript` (73 pages).

For old `L²` data `g` (`IsOldL2 c ν g`) the physical lift `oldPhys R c g` agrees a.e. in `(τ, z)`
with the cut source `oldCutSrc R c r₀ g`, `r₀ = R√(5ν/6)` (the lift vanishes where
`ϱ z > r₀`, as `ν s ≤ 6/5` there, 4163-4166), which is a `2c/R`-periodic separated source with
finite `Y₂` moment (2684-2687).  Hence the `sepW` integrand is integrable at every receiver `y`
with `r₀ < ϱ y` (`sepIntegrableOfSource_all`, `sepIntegrableCongrAE`), and `sepW` is additive.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem xa_nsSym_add (T T' : Ten3) :
    NearInst.nsSym (T + T') = NearInst.nsSym T + NearInst.nsSym T' := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [NearInst.nsSym, NearInst.symRZ] <;> ring

theorem xa_oldPhys_add (R c : ℝ) (g g' : Chart → Ten3) :
    oldPhys R c (g + g') = fun τ z => oldPhys R c g τ z + oldPhys R c g' τ z := by
  funext τ z
  simp only [oldPhys, NearInst.cartLift, Pi.add_apply, xa_nsSym_add, smul_add, Matrix.mul_add,
    Matrix.add_mul]

/-- `IsOldL2` data have finite `L²(s^{-1/2}dς)` moment as a lintegral. -/
theorem xa_lintegral_lt_top {c ν : ℝ} {g : Chart → Ten3} (hg : IsOldL2 c ν g) :
    ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) < ⊤ := by
  have h := hg.memLp.eLpNorm_lt_top
  have h2 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (by norm_num)
    (by norm_num) (f := g) (μ := ageμ c (-1 / 2))).1 h
  simpa using h2

/-- **Old `L²` data are a.e. a separated source with finite `Y₂` moment** (4155-4171). -/
theorem xa_oldReg {c ν R : ℝ} (hc : 0 < c) (hν : 0 < ν) (hR : 0 < R) {g : Chart → Ten3}
    (hg : IsOldL2 c ν g) :
    IIIa.IsSepSource (2 * c / R) (R * Real.sqrt (5 * ν / 6)) (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) ∧
      SepMoment (2 * c / R) (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) ∧
      ∀ᵐ x : ℝ × Space ∂volume,
        oldPhys R c g x.1 x.2 = oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g x.1 x.2 := by
  have hpull := chartOfNullPullback R c hR hc _ (ae_iff.1 hg.old)
  have hagree : ∀ᵐ x : ℝ × Space ∂volume,
      oldPhys R c g x.1 x.2 = oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g x.1 x.2 := by
    filter_upwards [hpull] with x hx
    simp only [not_not] at hx
    unfold oldCutSrc
    split_ifs with hz
    · rfl
    · have h0r : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
      have hlt := not_le.1 hz
      have hpos : 0 < NearInst.hRad x.2 := lt_of_le_of_lt h0r hlt
      have hsq : (R * Real.sqrt (5 * ν / 6)) ^ 2 = R ^ 2 * (5 * ν / 6) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      have hlt2 : (R * Real.sqrt (5 * ν / 6)) ^ 2 < NearInst.hRad x.2 ^ 2 := by
        nlinarith
      have hs : ν * (NearInst.chartOf R c x.2 x.1).1 ≤ 6 / 5 := by
        show ν * (R ^ 2 / NearInst.hRad x.2 ^ 2) ≤ 6 / 5
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      have hG0 := hx hs
      simp only [oldPhys, NearInst.cartLift, hG0, osr_nsSym_zero, smul_zero, Matrix.mul_zero,
        Matrix.zero_mul]
  have hper : ∀ τ z, oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g (τ + 2 * c / R) z =
      oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g τ z := by
    intro τ z
    unfold oldCutSrc
    rw [oldPhysPeriodic R c g τ z]
  have hsupp : ∀ τ z, R * Real.sqrt (5 * ν / 6) < Real.sqrt (z 0 ^ 2 + z 1 ^ 2) →
      oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g τ z = 0 := by
    intro τ z hz
    have hz' : ¬ NearInst.hRad z ≤ R * Real.sqrt (5 * ν / 6) := not_le.2 hz
    unfold oldCutSrc
    simp only [hz', ite_false]
  have hP : 2 * c / R = 2 * c / (R⁻¹)⁻¹ := by rw [inv_inv]
  refine ⟨⟨oldCutMeasurable R c _ g hg.measurable, hper, hsupp⟩, ?_, hagree⟩
  exact oldCutMoment R c _ g hR hc hg.measurable (xa_lintegral_lt_top hg)

/-- The `sepW` integrand of `oldPhys R c g` is integrable at every receiver `y` with
`R√(5ν/6) < ϱ y`, for `Re μ > -1/4`. -/
theorem xa_sepIntegrable {c ν R : ℝ} (hc : 0 < c) (hν : 0 < ν) (hR : 0 < R) {g : Chart → Ten3}
    (hg : IsOldL2 c ν g) (μ : ℂ) (hμ : -(1 / 4) < μ.re) (τ : ℝ) (y : Space)
    (hy : R * Real.sqrt (5 * ν / 6) < ϱ y) :
    SepIntegrableAt ν μ (oldPhys R c g) y τ := by
  obtain ⟨hS, hM, hae⟩ := xa_oldReg hc hν hR hg
  have h0r : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  exact sepIntegrableCongrAE ν μ _ _ hae y τ
    (sepIntegrableOfSource_all ν μ _ _ _ hν hμ h0r hP hS hM τ y hy)

theorem xa_sepPhi_add (ν : ℝ) (μ : ℂ) (T₁ T₂ : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    (i : Fin 3) (p : ℝ × Space) (y : Space) :
    sepPhi ν μ (fun t z => T₁ t z + T₂ t z) τ i p y =
      sepPhi ν μ T₁ τ i p y + sepPhi ν μ T₂ τ i p y := by
  unfold sepPhi
  simp only [Matrix.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib]

theorem xa_sepW_add (ν : ℝ) (μ : ℂ) (T₁ T₂ : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (y : Space)
    (τ : ℝ) (h₁ : SepIntegrableAt ν μ T₁ y τ) (h₂ : SepIntegrableAt ν μ T₂ y τ) :
    IIIa.sepW ν μ (fun t z => T₁ t z + T₂ t z) y τ = IIIa.sepW ν μ T₁ y τ + IIIa.sepW ν μ T₂ y τ := by
  funext i
  have h12 : Integrable (fun p => sepPhi ν μ (fun t z => T₁ t z + T₂ t z) τ i p y) sepRho := by
    simp only [xa_sepPhi_add]
    exact (h₁ i).add (h₂ i)
  rw [Pi.add_apply, sepW_eq_integral ν μ _ τ i y h12, sepW_eq_integral ν μ T₁ τ i y (h₁ i),
    sepW_eq_integral ν μ T₂ τ i y (h₂ i)]
  simp only [xa_sepPhi_add]
  exact integral_add (h₁ i) (h₂ i)

/-- `sepW` of the lift of `g + g'` is the sum, at receivers off the old disk. -/
theorem xa_sepW_oldPhys_add {c ν R : ℝ} (hc : 0 < c) (hν : 0 < ν) (hR : 0 < R)
    {g g' : Chart → Ten3} (hg : IsOldL2 c ν g) (hg' : IsOldL2 c ν g') (μ : ℂ)
    (hμ : -(1 / 4) < μ.re) (τ : ℝ) (y : Space) (hy : R * Real.sqrt (5 * ν / 6) < ϱ y) :
    IIIa.sepW ν μ (oldPhys R c (g + g')) y τ =
      IIIa.sepW ν μ (oldPhys R c g) y τ + IIIa.sepW ν μ (oldPhys R c g') y τ := by
  rw [xa_oldPhys_add]
  exact xa_sepW_add ν μ _ _ y τ (xa_sepIntegrable hc hν hR hg μ hμ τ y hy)
    (xa_sepIntegrable hc hν hR hg' μ hμ τ y hy)

/-- **Additivity of `X₀`** at every receiver with `R√(5ν/6) < ϱ y`. -/
theorem xa_wardX0_add {c ν μ R : ℝ} (hc : 0 < c) (hν : 0 < ν) (hR : 0 < R) (hμ : -(1 / 4) < μ)
    {g g' : Chart → Ten3} (hg : IsOldL2 c ν g) (hg' : IsOldL2 c ν g') (τ : ℝ) (y : Space)
    (hy : R * Real.sqrt (5 * ν / 6) < ϱ y) :
    wardX0 ν μ R c (g + g') τ y = wardX0 ν μ R c g τ y + wardX0 ν μ R c g' τ y := by
  have h1 : -(1 / 4) < ((μ : ℝ) : ℂ).re := by simpa using hμ
  have h2 : -(1 / 4) < (((μ : ℝ) : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]; linarith
  have e1 := xa_sepW_oldPhys_add hc hν hR hg hg' _ h1 τ y hy
  have e2 := xa_sepW_oldPhys_add hc hν hR hg hg' _ h2 τ y hy
  ext i
  simp only [wardX0, PiLp.toLp_apply, PiLp.add_apply, e1, e2, Pi.add_apply]
  simp only [Complex.add_re, Complex.sub_re]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
