import UnforcedLeray.Units.B0011.Solve
import UnforcedLeray.Units.B0011.Unique
import UnforcedLeray.Analysis.GaussianVortex.RadialProfile
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Unit B0011 (`eq:st18-t00007`): the regular, decaying Green inverse of `Δ₂`

Blueprint unit `B0011`, label `eq:st18-t00007`, `paper/main.tex` lines 683–689 (in the
setting of lines 646–682: the Gaussian `G` of `eq:st18-t00002`, line 650, and the angular-two
Gaussian space `X_G` of `eq:st18-t00005`, lines 672–677).

**Statement.** For angular index two,
`Rf(r) = -(1/4) [ r⁻² ∫₀^r s³ f(s) ds + r² ∫_r^∞ s⁻¹ f(s) ds ]`
is the inverse of `Δ₂ = ∂_r² + r⁻¹ ∂_r - 4 r⁻²` that is regular at zero and decays at infinity.
Precisely, for every profile `f` of `X_G` (`∫₀^∞ |f(r)|² G(r)⁻¹ r dr < ∞`):
`Rf` solves `Δ₂(Rf) = f` on `(0,∞)` (in integrated form, and classically when `f` is
continuous); `Rf(r) → 0` as `r → 0⁺` and as `r → ∞`; and `Rf` is the only solution of
`Δ₂ψ = f` on `(0,∞)` with `ψ = o(r⁻²)` at `0⁺` and `ψ = o(r²)` at `∞`, in particular the only
one that is bounded near `0` and tends to `0` at `∞`.

**Formalization choices.**
* Profiles are functions `f : ℝ → ℂ` on `(0, ∞)` (`X_G` is a complex Hilbert space, line 676);
  `MemXG f` is the defining condition of `eq:st18-t00005`. Existence, the limits at `0` and
  `∞`, and uniqueness only use the weaker consequence `WProf f` (`f` measurable and
  `r f(r) ∈ L¹(0,∞)`, `MemXG.wprof`), and are also stated in that generality; the decay rate
  `O(r⁻²)` also uses `r³ f(r) ∈ L¹(0,∞)` (`MemXG.integrable_cube`).
* `R` is the manuscript formula `eq:st18-t00007` verbatim (`R`); for `r > 0` and `WProf f`
  both integrals converge absolutely (`WProf.integrable_R_parts`), so no junk value is
  involved. `R_eq_kernel` identifies it
  with the kernel form `-(1/4) ∫₀^∞ (min(r,s)/max(r,s))² s f(s) ds`.
* Since a general `f ∈ X_G` is only in `L²_loc`, `Δ₂ψ = f` is formalized in integrated form
  (`IsDelta2Sol`): `ψ` is differentiable on `(0,∞)` with continuous derivative `ψ'` and
  `ψ'(b) - ψ'(a) = ∫_a^b (f - ψ'/r + 4ψ/r²)` for all `a, b > 0`. `isDelta2Sol_of_classical`
  and `IsDelta2Sol.delta2_eq` show that this agrees with the pointwise operator `Delta2`
  for twice differentiable `ψ`, resp. continuous `f`.
* "Regular at zero" and "decaying at infinity" are the boundary conditions excluding the
  homogeneous solutions `r⁻²` and `r²` (the Wronskian pair of the proof outline).

The proofs adapt `green_spec` / `green_unique` of the reference formalization
`NonUniqueEuler/lean/NonUniqueEuler/P/Sec4/Sector.lean` (compactly supported `L²` profiles) to
the weighted class: see the helper files `Units/B0011/Kernel.lean`, `Units/B0011/Solve.lean`,
`Units/B0011/Unique.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Asymptotics

namespace UnforcedLeray.B0011

/-! ### Definitions -/

/-- The Gaussian `G(r) = (4π)⁻¹ e^{-r²/4}` of `eq:st18-t00002` (`paper/main.tex` line 650),
as a function of the radius; `GaussianVortex.radialOmega r = e^{-r²/4}`. -/
def gaussG (r : ℝ) : ℝ := (4 * Real.pi)⁻¹ * GaussianVortex.radialOmega r

/-- The radial profile `f₂` of an element `f₂(r) e^{2iϑ}` of the Gaussian space `X_G` of
`eq:st18-t00005` (`paper/main.tex` lines 672–677): `f₂` is measurable on `(0, ∞)` and
`∫₀^∞ |f₂(r)|² G(r)⁻¹ r dr < ∞`. -/
def MemXG (f : ℝ → ℂ) : Prop :=
  AEStronglyMeasurable f (volume.restrict (Ioi 0)) ∧
    Integrable (fun r => ‖f r‖ ^ 2 * (gaussG r)⁻¹ * r) (volume.restrict (Ioi 0))

/-- The Green operator `eq:st18-t00007` (`paper/main.tex` lines 685–688):
`Rf(r) = -(1/4) [ r⁻² ∫₀^r s³ f(s) ds + r² ∫_r^∞ s⁻¹ f(s) ds ]`. Only its values at `r > 0`
are meaningful. -/
def R (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  -(1 / 4 : ℂ) * (((r : ℂ) ^ 2)⁻¹ * (∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * f s) +
    (r : ℂ) ^ 2 * ∫ s in Ioi r, (s : ℂ)⁻¹ * f s)

/-- The angular-two radial Laplacian `Δ₂ψ = ψ'' + r⁻¹ψ' - 4r⁻²ψ`, pointwise, so that
`Δ(ψ(r)e^{2iϑ}) = (Δ₂ψ)(r)e^{2iϑ}`. The tex uses it in `R = Δ₂⁻¹` (`paper/main.tex` line 680,
`eq:st18-t00006`) without writing it out. It is meaningful at `r > 0` where `ψ` is twice
differentiable. -/
def Delta2 (ψ : ℝ → ℂ) (r : ℝ) : ℂ :=
  deriv (deriv ψ) r + deriv ψ r / (r : ℂ) - 4 * ψ r / (r : ℂ) ^ 2

/-- `ψ` solves `Δ₂ψ = f` on `(0, ∞)` in integrated form: `ψ` is differentiable on `(0,∞)`
with a continuous derivative `ψ'`, and `ψ'(b) - ψ'(a) = ∫_a^b (f - ψ'/r + 4ψ/r²) dr` for all
`a, b > 0` (`Δ₂` as in `R = Δ₂⁻¹`, `paper/main.tex` line 680). -/
def IsDelta2Sol (f ψ : ℝ → ℂ) : Prop :=
  ∃ ψ' : ℝ → ℂ, (∀ r : ℝ, 0 < r → HasDerivAt ψ (ψ' r) r) ∧ ContinuousOn ψ' (Ioi 0) ∧
    ∀ a b : ℝ, 0 < a → 0 < b →
      ψ' b - ψ' a = ∫ r in a..b, (f r - ψ' r / (r : ℂ) + 4 * ψ r / (r : ℂ) ^ 2)

/-! ### The Gaussian class gives the weighted integrability -/

theorem gaussG_pos (r : ℝ) : 0 < gaussG r :=
  mul_pos (inv_pos.2 (by positivity)) (GaussianVortex.radialOmega_pos r)

theorem integrableOn_rpow_mul_gaussG {s : ℝ} (hs : -1 < s) :
    IntegrableOn (fun ρ : ℝ => ρ ^ s * gaussG ρ) (Ioi 0) := by
  have h : IntegrableOn (fun x : ℝ => (4 * Real.pi)⁻¹ * (x ^ s * Real.exp (-(1 / 4) * x ^ 2)))
      (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num) hs).const_mul _
  refine IntegrableOn.congr_fun h (fun ρ _ => ?_) measurableSet_Ioi
  simp only [gaussG, GaussianVortex.radialOmega]
  ring_nf

theorem integrableOn_mul_gaussG : IntegrableOn (fun ρ : ℝ => ρ * gaussG ρ) (Ioi 0) := by
  have h := integrableOn_rpow_mul_gaussG (s := 1) (by norm_num)
  refine h.congr_fun (fun ρ _ => ?_) measurableSet_Ioi
  simp

theorem integrableOn_pow_five_mul_gaussG :
    IntegrableOn (fun ρ : ℝ => ρ ^ 5 * gaussG ρ) (Ioi 0) := by
  have h := integrableOn_rpow_mul_gaussG (s := 5) (by norm_num)
  refine h.congr_fun (fun ρ _ => ?_) measurableSet_Ioi
  simp only
  rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- `2 ρ^{k+1} x ≤ x² G⁻¹ ρ + ρ^{2k+1} G` (arithmetic–geometric mean). -/
theorem two_mul_pow_le {x G ρ : ℝ} (hG : 0 < G) (hρ : 0 ≤ ρ) (k : ℕ) :
    2 * (ρ ^ (k + 1) * x) ≤ x ^ 2 * G⁻¹ * ρ + ρ ^ (2 * k + 1) * G := by
  have key : x ^ 2 * G⁻¹ * ρ + ρ ^ (2 * k + 1) * G - 2 * (ρ ^ (k + 1) * x) =
      ρ * G⁻¹ * (x - ρ ^ k * G) ^ 2 := by
    field_simp
    ring
  have : 0 ≤ ρ * G⁻¹ * (x - ρ ^ k * G) ^ 2 := by
    have := inv_pos.2 hG
    positivity
  linarith

/-- The Gaussian class `X_G` gives the weighted hypothesis `WProf`: `r f(r) ∈ L¹(0, ∞)`. -/
theorem MemXG.wprof {f : ℝ → ℂ} (hf : MemXG f) : WProf f := by
  refine ⟨hf.1, ?_⟩
  have hb : Integrable (fun ρ => (1 / 2 : ℝ) *
      (‖f ρ‖ ^ 2 * (gaussG ρ)⁻¹ * ρ + ρ * gaussG ρ)) (volume.restrict (Ioi 0)) :=
    (hf.2.add integrableOn_mul_gaussG).const_mul _
  refine hb.mono' (aestronglyMeasurable_id.mul hf.1.norm) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun ρ hρ => ?_
  have hρ' : (0 : ℝ) < ρ := hρ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hρ'.le (norm_nonneg _))]
  have := two_mul_pow_le (x := ‖f ρ‖) (gaussG_pos ρ) hρ'.le 0
  simp only [zero_add, pow_one, mul_zero] at this
  linarith

/-- The Gaussian class `X_G` gives `r³ f(r) ∈ L¹(0, ∞)` (the quadrupole moment is finite). -/
theorem MemXG.integrable_cube {f : ℝ → ℂ} (hf : MemXG f) :
    Integrable (fun ρ => ρ ^ 3 * ‖f ρ‖) (volume.restrict (Ioi 0)) := by
  have hb : Integrable (fun ρ => (1 / 2 : ℝ) *
      (‖f ρ‖ ^ 2 * (gaussG ρ)⁻¹ * ρ + ρ ^ 5 * gaussG ρ)) (volume.restrict (Ioi 0)) :=
    (hf.2.add integrableOn_pow_five_mul_gaussG).const_mul _
  refine hb.mono' ((aestronglyMeasurable_id.pow 3).mul hf.1.norm) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun ρ hρ => ?_
  have hρ' : (0 : ℝ) < ρ := hρ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hρ'.le 3) (norm_nonneg _))]
  have := two_mul_pow_le (x := ‖f ρ‖) (gaussG_pos ρ) hρ'.le 2
  norm_num at this
  linarith

/-! ### The kernel form -/

/-- For `r > 0`, the manuscript formula is the kernel operator
`Rf(r) = -(1/4) ∫₀^∞ (min(r,s)/max(r,s))² s f(s) ds` (`paper/main.tex` lines 685–688). -/
theorem R_eq_kernel {f : ℝ → ℂ} (hf : WProf f) {r : ℝ} (hr : 0 < r) :
    R f r = -(1 / 4 : ℂ) *
      ∫ s in Ioi (0 : ℝ), (((min r s / max r s) ^ 2 * s : ℝ) : ℂ) * f s := by
  have hint : IntegrableOn (fun ρ => (ker 2 r ρ : ℂ) * f ρ) (Ioi 0) := hf.integrable_ker 2 hr.le
  have hsplit : (∫ s in Ioi (0 : ℝ), (ker 2 r s : ℂ) * f s) =
      (∫ ρ in Ioc 0 r, (ker 2 r ρ : ℂ) * f ρ) + ∫ ρ in Ioi r, (ker 2 r ρ : ℂ) * f ρ := by
    rw [← Ioc_union_Ioi_eq_Ioi hr.le]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hr.le))
  have h1 : ∫ ρ in Ioc 0 r, (ker 2 r ρ : ℂ) * f ρ =
      ((r : ℂ) ^ 2)⁻¹ * ∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * f s := by
    rw [intervalIntegral.integral_of_le hr.le, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun ρ hρ => ?_
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [ker_of_ge hρ.2, kR]
    push_cast
    field_simp
  have h2 : ∫ ρ in Ioi r, (ker 2 r ρ : ℂ) * f ρ =
      (r : ℂ) ^ 2 * ∫ s in Ioi r, (s : ℂ)⁻¹ * f s := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
    have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast (hr.trans hρ).ne'
    rw [ker_of_le (le_of_lt hρ), kL]
    push_cast
    field_simp
  have hk : (∫ s in Ioi (0 : ℝ), (((min r s / max r s) ^ 2 * s : ℝ) : ℂ) * f s) =
      ∫ s in Ioi (0 : ℝ), (ker 2 r s : ℂ) * f s := rfl
  rw [hk, hsplit, h1, h2, R]

/-- For `r > 0` and `r f(r) ∈ L¹(0,∞)`, both integrals of `eq:st18-t00007`
(`paper/main.tex` lines 685–688) converge absolutely, so `R f r` involves no junk value. -/
theorem WProf.integrable_R_parts {f : ℝ → ℂ} (hf : WProf f) {r : ℝ} (hr : 0 < r) :
    IntervalIntegrable (fun s : ℝ => (s : ℂ) ^ 3 * f s) volume 0 r ∧
      IntegrableOn (fun s : ℝ => (s : ℂ)⁻¹ * f s) (Ioi r) := by
  have hint : IntegrableOn (fun ρ => (ker 2 r ρ : ℂ) * f ρ) (Ioi 0) := hf.integrable_ker 2 hr.le
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le]
    refine IntegrableOn.congr_fun ((hint.mono_set Ioc_subset_Ioi_self).const_mul ((r : ℂ) ^ 2))
      (fun ρ hρ => ?_) measurableSet_Ioc
    rw [ker_of_ge hρ.2, kR]
    push_cast
    field_simp
  · refine IntegrableOn.congr_fun ((hint.mono_set (Ioi_subset_Ioi hr.le)).const_mul
      (((r : ℂ) ^ 2)⁻¹)) (fun ρ hρ => ?_) measurableSet_Ioi
    have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast (hr.trans hρ).ne'
    rw [ker_of_le (le_of_lt hρ), kL]
    push_cast
    field_simp

theorem R_eq_Psi {f : ℝ → ℂ} (hf : WProf f) {r : ℝ} (hr : 0 < r) :
    R f r = -(1 / 4 : ℂ) * Psi 2 f r :=
  R_eq_kernel hf hr

/-! ### Existence: `R f` solves `Δ₂ ψ = f` -/

/-- `R f` solves `Δ₂(Rf) = f` on `(0, ∞)` in integrated form, for `r f(r) ∈ L¹(0,∞)`
(`paper/main.tex` lines 683–689, `R = Δ₂⁻¹`). -/
theorem WProf.isDelta2Sol_R {f : ℝ → ℂ} (hf : WProf f) : IsDelta2Sol f (R f) := by
  obtain ⟨hd, hc, hi⟩ := hf.delta2_solution
  refine ⟨fun t => -(1 / 4 : ℂ) * Phi 2 f t, fun r hr => ?_, hc, fun a b ha hb => ?_⟩
  · refine (hd r hr).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact R_eq_Psi hf ht
  · rw [hi a b ha hb]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have : 0 < t := lt_of_lt_of_le (lt_min ha hb) ht.1
    simp only [R_eq_Psi hf this]

/-- **`eq:st18-t00007`, existence** (`paper/main.tex` lines 683–689): for `f ∈ X_G`,
`R f` solves `Δ₂(Rf) = f` on `(0, ∞)` (integrated form). -/
theorem isDelta2Sol_R {f : ℝ → ℂ} (hf : MemXG f) : IsDelta2Sol f (R f) :=
  hf.wprof.isDelta2Sol_R

/-! ### Integrated and classical solutions -/

/-- A twice differentiable `ψ` with `Δ₂ψ = f` pointwise on `(0, ∞)`, `f` locally integrable on
`(0, ∞)`, is an integrated solution. -/
theorem isDelta2Sol_of_classical {f ψ : ℝ → ℂ}
    (hf : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable f volume a b)
    (hd : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ ψ r)
    (hd2 : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ (deriv ψ) r)
    (heq : ∀ r : ℝ, 0 < r → Delta2 ψ r = f r) : IsDelta2Sol f ψ := by
  refine ⟨deriv ψ, fun r hr => (hd r hr).hasDerivAt,
    fun r hr => (hd2 r hr).continuousAt.continuousWithinAt, fun a b ha hb => ?_⟩
  have hsub : uIcc a b ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le (lt_min ha hb) hr.1
  have hr0 : ∀ r ∈ uIcc a b, (r : ℂ) ≠ 0 := fun r hr => by exact_mod_cast ne_of_gt (hsub hr)
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt (deriv ψ)
      (f x - deriv ψ x / (x : ℂ) + 4 * ψ x / (x : ℂ) ^ 2) x := by
    intro x hx
    have h1 := (hd2 x (hsub hx)).hasDerivAt
    have h2 := heq x (hsub hx)
    simp only [Delta2] at h2
    have h3 : deriv (deriv ψ) x = f x - deriv ψ x / (x : ℂ) + 4 * ψ x / (x : ℂ) ^ 2 := by
      linear_combination h2
    rwa [h3] at h1
  have hψ : ContinuousOn ψ (uIcc a b) := fun r hr =>
    (hd r (hsub hr)).continuousAt.continuousWithinAt
  have hψ' : ContinuousOn (deriv ψ) (uIcc a b) := fun r hr =>
    (hd2 r (hsub hr)).continuousAt.continuousWithinAt
  have h2 : ContinuousOn (fun r : ℝ => -(deriv ψ r / (r : ℂ)) + 4 * ψ r / (r : ℂ) ^ 2)
      (uIcc a b) :=
    (hψ'.div Complex.continuous_ofReal.continuousOn hr0).neg.add
      ((continuousOn_const.mul hψ).div (Complex.continuous_ofReal.continuousOn.pow 2)
        fun r hr => pow_ne_zero 2 (hr0 r hr))
  have hint : IntervalIntegrable (fun x : ℝ => f x - deriv ψ x / (x : ℂ) +
      4 * ψ x / (x : ℂ) ^ 2) volume a b :=
    ((hf a b ha hb).add h2.intervalIntegrable).congr fun r _ => by ring
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint).symm

/-- For continuous `f`, an integrated solution is a classical one: `ψ` is twice differentiable
on `(0, ∞)` and `Δ₂ψ = f` pointwise there. -/
theorem IsDelta2Sol.delta2_eq {f ψ : ℝ → ℂ} (h : IsDelta2Sol f ψ)
    (hf : ContinuousOn f (Ioi 0)) {r : ℝ} (hr : 0 < r) :
    DifferentiableAt ℝ ψ r ∧ DifferentiableAt ℝ (deriv ψ) r ∧ Delta2 ψ r = f r := by
  obtain ⟨ψ', hd, hc, hi⟩ := h
  set hh : ℝ → ℂ := fun r => f r - ψ' r / (r : ℂ) + 4 * ψ r / (r : ℂ) ^ 2 with hhh
  have hhc : ContinuousOn hh (Ioi 0) := by
    have hψcont : ContinuousOn ψ (Ioi 0) := fun r hr =>
      (hd r hr).continuousAt.continuousWithinAt
    have hr0 : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) ≠ 0 := fun r hr => by exact_mod_cast ne_of_gt hr
    exact (hf.sub (hc.div Complex.continuous_ofReal.continuousOn hr0)).add
      ((continuousOn_const.mul hψcont).div (Complex.continuous_ofReal.continuousOn.pow 2)
        fun r hr => pow_ne_zero 2 (hr0 r hr))
  have hψ'd : HasDerivAt ψ' (hh r) r := by
    have hF : HasDerivAt (fun s => ψ' r + ∫ u in r..s, hh u) (hh r) r :=
      (intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
        (hhc.stronglyMeasurableAtFilter isOpen_Ioi r hr)
        (hhc.continuousAt (Ioi_mem_nhds hr))).const_add _
    refine hF.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hr] with s hs
    linear_combination hi r s hr hs
  have hev : deriv ψ =ᶠ[𝓝 r] ψ' := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact (hd t ht).deriv
  have hdd : HasDerivAt (deriv ψ) (hh r) r := hψ'd.congr_of_eventuallyEq hev
  refine ⟨(hd r hr).differentiableAt, hdd.differentiableAt, ?_⟩
  simp only [Delta2, hdd.deriv, (hd r hr).deriv, hhh]
  ring

/-- **`eq:st18-t00007`, classical existence**: for `f ∈ X_G` continuous on `(0, ∞)`, `R f` is
twice differentiable on `(0, ∞)` and `Δ₂(Rf)(r) = f(r)` for every `r > 0`
(`paper/main.tex` lines 683–689). -/
theorem delta2_R {f : ℝ → ℂ} (hf : MemXG f) (hfc : ContinuousOn f (Ioi 0)) {r : ℝ}
    (hr : 0 < r) :
    DifferentiableAt ℝ (R f) r ∧ DifferentiableAt ℝ (deriv (R f)) r ∧ Delta2 (R f) r = f r :=
  (isDelta2Sol_R hf).delta2_eq hfc hr

/-! ### Regularity at zero and decay at infinity -/

/-- `R f(r) → 0` as `r → 0⁺` (regular at zero), for `r f(r) ∈ L¹(0,∞)`. -/
theorem WProf.tendsto_R_nhdsGT_zero {f : ℝ → ℂ} (hf : WProf f) :
    Tendsto (R f) (𝓝[>] 0) (𝓝 0) := by
  have h := (hf.tendsto_Psi_nhdsGT_zero two_ne_zero).const_mul (-(1 / 4 : ℂ))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (R_eq_Psi hf ht).symm

/-- `R f(r) → 0` as `r → ∞` (decay at infinity), for `r f(r) ∈ L¹(0,∞)`. -/
theorem WProf.tendsto_R_atTop {f : ℝ → ℂ} (hf : WProf f) : Tendsto (R f) atTop (𝓝 0) := by
  have h := (hf.tendsto_Psi_atTop two_ne_zero).const_mul (-(1 / 4 : ℂ))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [Ioi_mem_atTop 0] with t ht
  exact (R_eq_Psi hf ht).symm

/-- **`eq:st18-t00007`, regularity at zero** (`paper/main.tex` line 683): for `f ∈ X_G`,
`R f(r) → 0` as `r → 0⁺`. -/
theorem tendsto_R_nhdsGT_zero {f : ℝ → ℂ} (hf : MemXG f) : Tendsto (R f) (𝓝[>] 0) (𝓝 0) :=
  hf.wprof.tendsto_R_nhdsGT_zero

/-- **`eq:st18-t00007`, decay at infinity** (`paper/main.tex` line 683): for `f ∈ X_G`,
`R f(r) → 0` as `r → ∞`. -/
theorem tendsto_R_atTop {f : ℝ → ℂ} (hf : MemXG f) : Tendsto (R f) atTop (𝓝 0) :=
  hf.wprof.tendsto_R_atTop

theorem ker_two_le {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) : ker 2 r ρ ≤ (r ^ 2)⁻¹ * ρ ^ 3 := by
  by_cases h : r ≤ ρ
  · rw [ker_of_le h, kL]
    have key : (r ^ 2)⁻¹ * ρ ^ 3 - (r / ρ) ^ 2 * ρ = (ρ ^ 4 - r ^ 4) / (r ^ 2 * ρ) := by
      field_simp
    have : 0 ≤ (ρ ^ 4 - r ^ 4) / (r ^ 2 * ρ) :=
      div_nonneg (sub_nonneg.2 (pow_le_pow_left₀ hr.le h 4)) (by positivity)
    linarith
  · rw [ker_of_ge (le_of_lt (not_le.1 h)), kR]
    refine le_of_eq ?_
    field_simp

/-- The decay rate `|Rf(r)| ≤ (4r²)⁻¹ ∫₀^∞ s³ |f(s)| ds` for `r > 0`, when `s³ f ∈ L¹(0,∞)`
(e.g. for `f ∈ X_G`, `MemXG.integrable_cube`). -/
theorem norm_R_le {f : ℝ → ℂ} (hf : WProf f)
    (h3 : Integrable (fun ρ => ρ ^ 3 * ‖f ρ‖) (volume.restrict (Ioi 0))) {r : ℝ} (hr : 0 < r) :
    ‖R f r‖ ≤ (∫ ρ in Ioi (0 : ℝ), ρ ^ 3 * ‖f ρ‖) / (4 * r ^ 2) := by
  rw [R_eq_Psi hf hr, norm_mul, Psi]
  have hle : ‖∫ ρ in Ioi (0 : ℝ), (ker 2 r ρ : ℂ) * f ρ‖ ≤
      ∫ ρ in Ioi (0 : ℝ), (r ^ 2)⁻¹ * (ρ ^ 3 * ‖f ρ‖) := by
    refine norm_integral_le_of_norm_le (h3.const_mul _) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun ρ hρ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ker_nonneg hr.le hρ),
      ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (ker_two_le hr hρ) (norm_nonneg _)
  rw [integral_const_mul] at hle
  have hn : ‖-(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
  rw [hn]
  calc 1 / 4 * ‖∫ ρ in Ioi (0 : ℝ), (ker 2 r ρ : ℂ) * f ρ‖
      ≤ 1 / 4 * ((r ^ 2)⁻¹ * ∫ ρ in Ioi (0 : ℝ), ρ ^ 3 * ‖f ρ‖) := by gcongr
    _ = (∫ ρ in Ioi (0 : ℝ), ρ ^ 3 * ‖f ρ‖) / (4 * r ^ 2) := by
      field_simp

/-- **`eq:st18-t00007`, decay rate**: for `f ∈ X_G`, `Rf = O(r⁻²)` as `r → ∞`. -/
theorem R_isBigO_atTop {f : ℝ → ℂ} (hf : MemXG f) :
    R f =O[atTop] fun r : ℝ => (r ^ 2)⁻¹ := by
  refine IsBigO.of_bound ((∫ ρ in Ioi (0 : ℝ), ρ ^ 3 * ‖f ρ‖) / 4) ?_
  filter_upwards [Ioi_mem_atTop 0] with r hr
  have hr' : (0 : ℝ) < r := hr
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (pow_pos hr' 2))]
  calc ‖R f r‖ ≤ (∫ ρ in Ioi (0 : ℝ), ρ ^ 3 * ‖f ρ‖) / (4 * r ^ 2) :=
        norm_R_le hf.wprof hf.integrable_cube hr'
    _ = (∫ ρ in Ioi (0 : ℝ), ρ ^ 3 * ‖f ρ‖) / 4 * (r ^ 2)⁻¹ := by
        field_simp

/-! ### Uniqueness -/

theorem tendsto_mul_sq_of_isLittleO {φ : ℝ → ℂ}
    (h : φ =o[𝓝[>] 0] fun r : ℝ => (r ^ 2)⁻¹) :
    Tendsto (fun r : ℝ => φ r * (r : ℂ) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have h1 : (fun r : ℝ => φ r * (r : ℂ) ^ 2) =o[𝓝[>] 0] fun r : ℝ => (r ^ 2)⁻¹ * r ^ 2 :=
    h.mul_isBigO (isBigO_of_le _ fun r => by rw [norm_pow, norm_pow, Complex.norm_real])
  have h2 : (fun r : ℝ => (r ^ 2)⁻¹ * r ^ 2) =ᶠ[𝓝[>] 0] fun _ => (1 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hr))
  exact (isLittleO_one_iff ℝ).1 (h1.congr' EventuallyEq.rfl h2)

theorem tendsto_mul_inv_sq_of_isLittleO {φ : ℝ → ℂ} (h : φ =o[atTop] fun r : ℝ => r ^ 2) :
    Tendsto (fun r : ℝ => φ r * ((r : ℂ) ^ 2)⁻¹) atTop (𝓝 0) := by
  have h1 : (fun r : ℝ => φ r * ((r : ℂ) ^ 2)⁻¹) =o[atTop] fun r : ℝ => r ^ 2 * (r ^ 2)⁻¹ :=
    h.mul_isBigO (isBigO_of_le _ fun r => by
      rw [norm_inv, norm_inv, norm_pow, norm_pow, Complex.norm_real])
  have h2 : (fun r : ℝ => r ^ 2 * (r ^ 2)⁻¹) =ᶠ[atTop] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_atTop 0] with r hr
    exact mul_inv_cancel₀ (pow_ne_zero 2 (ne_of_gt hr))
  exact (isLittleO_one_iff ℝ).1 (h1.congr' EventuallyEq.rfl h2)

theorem tendsto_inv_sq_atTop : Tendsto (fun r : ℝ => ((r : ℂ) ^ 2)⁻¹) atTop (𝓝 0) := by
  have h : Tendsto (fun r : ℝ => (r ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)
  have := (Complex.continuous_ofReal.tendsto 0).comp h
  simpa [Function.comp_def] using this

theorem tendsto_sq_nhdsGT_zero : Tendsto (fun r : ℝ => (r : ℂ) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have : Tendsto (fun r : ℝ => (r : ℂ) ^ 2) (𝓝 0) (𝓝 (((0 : ℝ) : ℂ) ^ 2)) :=
    (Complex.continuous_ofReal.pow 2).tendsto 0
  rw [Complex.ofReal_zero, zero_pow two_ne_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- Uniqueness with the boundary conditions in limit form: an integrated solution `ψ` of
`Δ₂ψ = f` with `ψ(r) r² → 0` as `r → 0⁺` and `ψ(r) r⁻² → 0` as `r → ∞` equals `R f` on
`(0, ∞)`, for `r f(r) ∈ L¹(0,∞)`. -/
theorem WProf.eqOn_R_of_tendsto {f ψ : ℝ → ℂ} (hf : WProf f) (hψ : IsDelta2Sol f ψ)
    (h0 : Tendsto (fun r : ℝ => ψ r * (r : ℂ) ^ 2) (𝓝[>] 0) (𝓝 0))
    (hinf : Tendsto (fun r : ℝ => ψ r * ((r : ℂ) ^ 2)⁻¹) atTop (𝓝 0)) :
    EqOn ψ (R f) (Ioi 0) := by
  obtain ⟨ψ', hd, hc, hi⟩ := hψ
  obtain ⟨ψR', hdR, hcR, hiR⟩ := hf.isDelta2Sol_R
  refine eqOn_of_delta2 (fun a b ha hb => hf.intervalIntegrable ha hb) hd hc hi hdR hcR hiR
    ?_ ?_
  · have hR := hf.tendsto_R_nhdsGT_zero.mul tendsto_sq_nhdsGT_zero
    rw [mul_zero] at hR
    have := h0.sub hR
    rw [sub_zero] at this
    exact this.congr fun r => by ring
  · have hR := hf.tendsto_R_atTop.mul tendsto_inv_sq_atTop
    rw [mul_zero] at hR
    have := hinf.sub hR
    rw [sub_zero] at this
    exact this.congr fun r => by ring

/-- Uniqueness, little-o form, for `r f(r) ∈ L¹(0,∞)`. -/
theorem WProf.eqOn_R {f ψ : ℝ → ℂ} (hf : WProf f) (hψ : IsDelta2Sol f ψ)
    (h0 : ψ =o[𝓝[>] 0] fun r : ℝ => (r ^ 2)⁻¹) (hinf : ψ =o[atTop] fun r : ℝ => r ^ 2) :
    EqOn ψ (R f) (Ioi 0) :=
  hf.eqOn_R_of_tendsto hψ (tendsto_mul_sq_of_isLittleO h0) (tendsto_mul_inv_sq_of_isLittleO hinf)

/-- **`eq:st18-t00007`, uniqueness** (`paper/main.tex` lines 683–689): for `f ∈ X_G`, every
solution `ψ` of `Δ₂ψ = f` on `(0, ∞)` (integrated form) with `ψ = o(r⁻²)` as `r → 0⁺` and
`ψ = o(r²)` as `r → ∞` equals `R f` on `(0, ∞)`. These conditions exclude exactly the
homogeneous solutions `r⁻²` and `r²`. -/
theorem eqOn_R {f ψ : ℝ → ℂ} (hf : MemXG f) (hψ : IsDelta2Sol f ψ)
    (h0 : ψ =o[𝓝[>] 0] fun r : ℝ => (r ^ 2)⁻¹) (hinf : ψ =o[atTop] fun r : ℝ => r ^ 2) :
    EqOn ψ (R f) (Ioi 0) :=
  hf.wprof.eqOn_R hψ h0 hinf

/-- Uniqueness among the solutions that are bounded near `0` and tend to `0` at `∞`, for
`r f(r) ∈ L¹(0,∞)`. -/
theorem WProf.eqOn_R_of_bounded {f ψ : ℝ → ℂ} (hf : WProf f) (hψ : IsDelta2Sol f ψ)
    (h0 : ψ =O[𝓝[>] 0] fun _ : ℝ => (1 : ℝ)) (hinf : Tendsto ψ atTop (𝓝 0)) :
    EqOn ψ (R f) (Ioi 0) := by
  refine hf.eqOn_R_of_tendsto hψ ?_ ?_
  · have hsq : (fun r : ℝ => (r : ℂ) ^ 2) =O[𝓝[>] 0] fun r : ℝ => r ^ 2 :=
      isBigO_of_le _ fun r => by rw [norm_pow, norm_pow, Complex.norm_real]
    refine (h0.mul hsq).trans_tendsto ?_
    have : Tendsto (fun r : ℝ => (1 : ℝ) * r ^ 2) (𝓝 0) (𝓝 ((1 : ℝ) * (0 : ℝ) ^ 2)) :=
      (continuous_const.mul (continuous_pow 2)).tendsto (0 : ℝ)
    rw [zero_pow two_ne_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · have := hinf.mul tendsto_inv_sq_atTop
    rwa [mul_zero] at this

/-- **`eq:st18-t00007`, the Green inverse** (`paper/main.tex` lines 683–689, with
`R = Δ₂⁻¹` from line 680): for `f ∈ X_G`, `R f` solves `Δ₂(Rf) = f` on `(0, ∞)`, is regular at
zero (`Rf(r) → 0` as `r → 0⁺`) and decays at infinity (`Rf(r) → 0` as `r → ∞`), and it is the
unique solution of `Δ₂ψ = f` that is bounded near zero and tends to zero at infinity. -/
theorem R_isGreenInverse {f : ℝ → ℂ} (hf : MemXG f) :
    IsDelta2Sol f (R f) ∧ Tendsto (R f) (𝓝[>] 0) (𝓝 0) ∧ Tendsto (R f) atTop (𝓝 0) ∧
      ∀ ψ : ℝ → ℂ, IsDelta2Sol f ψ → ψ =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) →
        Tendsto ψ atTop (𝓝 0) → EqOn ψ (R f) (Ioi 0) :=
  ⟨isDelta2Sol_R hf, tendsto_R_nhdsGT_zero hf, tendsto_R_atTop hf,
    fun _ hψ h0 hinf => hf.wprof.eqOn_R_of_bounded hψ h0 hinf⟩

/-- **`eq:st18-t00007`, classical uniqueness** (`paper/main.tex` lines 683–689): for `f ∈ X_G`,
a twice differentiable `ψ` on `(0, ∞)` with `Δ₂ψ = f` pointwise there, `ψ = o(r⁻²)` as
`r → 0⁺` and `ψ = o(r²)` as `r → ∞`, equals `R f` on `(0, ∞)`. -/
theorem eqOn_R_of_classical {f ψ : ℝ → ℂ} (hf : MemXG f)
    (hd : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ ψ r)
    (hd2 : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ (deriv ψ) r)
    (heq : ∀ r : ℝ, 0 < r → Delta2 ψ r = f r)
    (h0 : ψ =o[𝓝[>] 0] fun r : ℝ => (r ^ 2)⁻¹) (hinf : ψ =o[atTop] fun r : ℝ => r ^ 2) :
    EqOn ψ (R f) (Ioi 0) :=
  eqOn_R hf (isDelta2Sol_of_classical (fun _ _ ha hb => hf.wprof.intervalIntegrable ha hb)
    hd hd2 heq) h0 hinf

end UnforcedLeray.B0011
