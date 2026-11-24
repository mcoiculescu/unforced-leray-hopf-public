import UnforcedLeray.Short.PartIIb.Sub.G4_2_1_2_1

/-!
# Part II-b, task `PartII-b:G4/2/1/2/1/2` (`greenSqFormula`)

Source: `the November 2 reference manuscript`, lines 2347-2352.

For `G = greenInverse q`, `q(s) = a(s²) G(s)` (eigen equation), so `q(s) = s² h(s²)` with
`h = sqH lam q`.  The substitution `v = s²` (`integral_image_eq_integral_abs_deriv_smul`) gives
`∫₀^r s³q = ½∫₀^{r²} v²h` and `∫_r^∞ s⁻¹q = ½∫_{r²}^∞ h`; inserting these into
`G(r)/r² = -¼(r⁻⁴∫₀^r s³q + ∫_r^∞ s⁻¹q)` yields `sqF h (r²)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

/-- The eigen equation in the form `q(s) = a(s²) G(s)` for `s > 0`. -/
lemma greenSqF_eigen {lam : ℂ} {q : Planar.Profile} (hlam : 0 < lam.re)
    (heig : ∀ r : ℝ, 0 < r → Planar.generatorL0 q r = lam * q r) {s : ℝ} (hs : 0 < s) :
    q s = sqCoeff lam (s ^ 2) * Planar.greenInverse q s := by
  have hE := heig s hs
  unfold Planar.generatorL0 at hE
  simp only [Planar.vortexOmega, Planar.strainK] at hE
  have hden : lam + 2 * Complex.I * ((Real.exp (-(s ^ 2) / 4) : ℝ) : ℂ) ≠ 0 := by
    generalize Real.exp (-(s ^ 2) / 4) = E
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  unfold sqCoeff
  rw [div_mul_eq_mul_div, eq_div_iff hden]
  linear_combination (-1 : ℂ) * hE

/-- `s² · h(s²) = q(s)` for `s > 0`, where `h = sqH lam q`. -/
lemma greenSqF_h {lam : ℂ} {q : Planar.Profile} (hlam : 0 < lam.re)
    (heig : ∀ r : ℝ, 0 < r → Planar.generatorL0 q r = lam * q r) {s : ℝ} (hs : 0 < s) :
    (s : ℂ) ^ 2 * sqH lam q (s ^ 2) = q s := by
  unfold sqH
  rw [Real.sqrt_sq hs.le, greenSqF_eigen hlam heig hs]
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  push_cast
  field_simp <;> ring

/-- `x ↦ x²` maps `(0, r]` onto `(0, r²]`. -/
lemma greenSqF_image_Ioc {r : ℝ} (hr : 0 ≤ r) :
    (fun x : ℝ => x ^ 2) '' Ioc 0 r = Ioc 0 (r ^ 2) := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx0, hxr⟩, rfl⟩
    exact ⟨pow_pos hx0 2, pow_le_pow_left₀ hx0.le hxr 2⟩
  · rintro ⟨hy0, hyr⟩
    refine ⟨Real.sqrt y, ⟨Real.sqrt_pos.2 hy0, ?_⟩, Real.sq_sqrt hy0.le⟩
    nlinarith [Real.sq_sqrt hy0.le, Real.sqrt_nonneg y, hr]

/-- `x ↦ x²` maps `(r, ∞)` onto `(r², ∞)` for `r ≥ 0`. -/
lemma greenSqF_image_Ioi {r : ℝ} (hr : 0 ≤ r) :
    (fun x : ℝ => x ^ 2) '' Ioi r = Ioi (r ^ 2) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : r < x := hx
    show r ^ 2 < x ^ 2
    nlinarith
  · intro hy
    have hy' : r ^ 2 < y := hy
    refine ⟨Real.sqrt y, ?_, Real.sq_sqrt (by nlinarith)⟩
    show r < Real.sqrt y
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ y by nlinarith), Real.sqrt_nonneg y, hr]

lemma greenSqF_injOn {s : Set ℝ} (hs : ∀ x ∈ s, 0 < x) :
    InjOn (fun x : ℝ => x ^ 2) s := by
  intro x hx y hy hxy
  exact (pow_left_inj₀ (hs x hx).le (hs y hy).le two_ne_zero).1 hxy

lemma greenSqF_deriv (s : Set ℝ) (x : ℝ) :
    HasDerivWithinAt (fun x : ℝ => x ^ 2) (2 * x) s x := by
  have h := (hasDerivAt_pow 2 x).hasDerivWithinAt (s := s)
  simpa using h

/-- The `v²h` integral: `∫₀^{r²} v² h = 2 ∫₀^r s³ q`. -/
lemma greenSqF_claim1 {lam : ℂ} {q : Planar.Profile} (hlam : 0 < lam.re)
    (heig : ∀ r : ℝ, 0 < r → Planar.generatorL0 q r = lam * q r) {r : ℝ} (hr : 0 < r) :
    ∫ v in (0 : ℝ)..r ^ 2, (v : ℂ) ^ 2 * sqH lam q v
      = 2 * ∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * q s := by
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ r ^ 2 by positivity),
    intervalIntegral.integral_of_le hr.le, ← greenSqF_image_Ioc hr.le]
  rw [integral_image_eq_integral_abs_deriv_smul (f := fun x : ℝ => x ^ 2)
    (f' := fun x : ℝ => 2 * x) measurableSet_Ioc (fun x _ => greenSqF_deriv _ x)
    (greenSqF_injOn fun x hx => hx.1)]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have hx0 : (0 : ℝ) < x := hx.1
  have hqx := greenSqF_h hlam heig hx0
  show |2 * x| • (((x ^ 2 : ℝ) : ℂ) ^ 2 * sqH lam q (x ^ 2)) = 2 * ((x : ℂ) ^ 3 * q x)
  rw [Complex.real_smul, abs_of_pos (by linarith : (0 : ℝ) < 2 * x), ← hqx]
  push_cast
  ring

/-- The tail identity: `∫_{(r²,∞)} h = 2 ∫_{(r,∞)} s⁻¹ q`. -/
lemma greenSqF_claim2 {lam : ℂ} {q : Planar.Profile} (hlam : 0 < lam.re)
    (heig : ∀ r : ℝ, 0 < r → Planar.generatorL0 q r = lam * q r) {r : ℝ} (hr : 0 < r) :
    ∫ v in Ioi (r ^ 2), sqH lam q v = 2 * ∫ s in Ioi r, (s : ℂ)⁻¹ * q s := by
  rw [← greenSqF_image_Ioi hr.le]
  rw [integral_image_eq_integral_abs_deriv_smul (f := fun x : ℝ => x ^ 2)
    (f' := fun x : ℝ => 2 * x) measurableSet_Ioi (fun x _ => greenSqF_deriv _ x)
    (greenSqF_injOn fun x hx => lt_trans hr hx)]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : (0 : ℝ) < x := lt_trans hr hx
  have hqx := greenSqF_h hlam heig hx0
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx0.ne'
  show |2 * x| • sqH lam q (x ^ 2) = 2 * ((x : ℂ)⁻¹ * q x)
  rw [Complex.real_smul, abs_of_pos (by linarith : (0 : ℝ) < 2 * x), ← hqx]
  push_cast
  field_simp <;> ring

/-- Main identity with the radius and the squared variable tied by `r² = u`. -/
lemma greenSqF_main {lam : ℂ} {q : Planar.Profile} (hlam : 0 < lam.re)
    (heig : ∀ r : ℝ, 0 < r → Planar.generatorL0 q r = lam * q r) {r u : ℝ} (hr : 0 < r)
    (hru : r ^ 2 = u) :
    Planar.greenInverse q r / (u : ℂ) = sqF (sqH lam q) u := by
  subst hru
  have h1 := greenSqF_claim1 hlam heig hr
  have h2 := greenSqF_claim2 hlam heig hr
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  unfold sqF Planar.greenInverse
  rw [h1, h2]
  push_cast
  field_simp <;> ring

/-- **Leaf 2 (closed form)**: `G(√u)/u = sqF (sqH lam q) u` for `u > 0`. -/
theorem greenSqFormula : UnforcedLeray.Short.IIb.GreenSqFormula := by
  intro lam q hq _ u hu
  exact greenSqF_main hq.re_pos hq.eigen (Real.sqrt_pos.2 hu) (Real.sq_sqrt hu.le)

end UnforcedLeray.Short.IIb
