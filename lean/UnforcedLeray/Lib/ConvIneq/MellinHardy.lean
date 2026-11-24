import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The Mellin–Minkowski lemma and the Hardy family (INF22 A4, bypass BP2)

Blueprint infrastructure target **INF22 A4** of the scoping note

bypass BP2 of §4, = ExternalInputs BX22). One lemma covers every Hardy-type inequality of the
manuscript: for `k ≥ 0` on `(0,∞)`,
`‖s ↦ ∫_0^∞ k(u) |f(su)| du‖_{L^p(s^α ds)} ≤ (∫_0^∞ k(u) u^{-(α+1)/p} du) ‖f‖_{L^p(s^α ds)}`
(`eLpNorm_mellin_le`). Its proof is Minkowski's integral inequality (the vendored, compiled
`NonUniqueEuler.Conv.eLpNorm_lintegral_le`, `lean/NonUniqueEuler/P/Infra/ConvMinkowski/
Minkowski.lean`) and the dilation identity `‖f(·u)‖_{L^p(s^α)} = u^{-(α+1)/p} ‖f‖_{L^p(s^α)}`
(`eLpNorm_comp_mul_powWeight`, `paper/main.tex` 4697–4700).

Corollaries, with the manuscript's exact constants:
* `hardy_Ioi` and `hardy_age` — unit **B0275**, first line of `mixed-background:weighted-integrals`
  (`paper/main.tex` 4702–4718): `‖∫_0^s f‖_{L^p(s^{a_p}ds)} ≤ (2p/(3-p)) ‖f‖_{L^p(s^{b_p}ds)}`,
  `1 ≤ p < 3`, `a_p = p/2 - 5/2`, `b_p = a_p + p` (the constant is `22` at `p = 11/4`,
  `hardy_age_eleven_quarters`); `hardy_Ioi` is the general weighted Hardy inequality
  `‖∫_0^s f‖_{L^p(s^a)} ≤ (p/(-a-1)) ‖f‖_{L^p(s^{a+p})}`, `a < -1`;
* `volterra_age` — B0275, second line: `‖∫_0^s (s-t)^{-1/2} f(t) dt‖_{L^p((0,S),s^b ds)}
  ≤ √S · B(1-(b+1)/p, 1/2) ‖f‖_{L^p((0,S),s^b ds)}` whenever `(b+1)/p < 1`; at `p = 11/4`,
  `b = 13/8` the Beta value is `C_p = ∫_0^1 (1-u)^{-1/2} u^{-21/22} du`
  (`volterra_age_eleven_quarters`);
* `hardy_beta` — unit **B0611**, `eq:st18-t00558` (`paper/main.tex` 9913–9927):
  `‖∫_0^s c(t/s)(s-t)^{-1/2} f(t) dt‖_{L²(s^{-3/2}ds)} ≤ B(3/4,1/2) ‖f‖_{L²(s^{-1/2}ds)}`,
  for any multiplier with `|c| ≤ 1` on `(0,1]` (in particular `c(u) = u^μ`, `Re μ ≥ 0`);
* `hardy_tail` — unit **B0582** half-line piece (`paper/main.tex` 9412–9425):
  `‖∫_η^∞ f‖_{L²(0,∞)} ≤ 2 ‖ξ f‖_{L²(0,∞)}`.

**Conventions (junk values).**
* `powWeight α` is the measure `s^α ds` on `(0,∞)` (Lebesgue measure restricted to `Ioi 0`
  with density `ENNReal.ofReal (s ^ α)`); norms are `eLpNorm`, valued in `[0,∞]`, so no
  finiteness hypothesis is needed and none is assumed.
* Integrals on the left are Bochner (interval) integrals. Where the integrand is not
  integrable the Bochner junk value `0` only lowers the left side: every bound is proved
  through `‖∫ g‖ₑ ≤ ∫⁻ ‖g‖ₑ`, which holds unconditionally. The integrands `f` are assumed
  `AEStronglyMeasurable` on the domain where the manuscript's `L^p` hypothesis places them.
* `(s - t) ^ (-(1/2))` is `Real.rpow`; at `t = s` it is `0` (a null set), and for `t < s` it
  is the genuine power.
* Constants are stated through `Real.Gamma`, so no junk can enter: `B(a,c) = Γ(a)Γ(c)/Γ(a+c)`
  for `a, c > 0` (`lintegral_beta`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Conv

/-! ### The weighted measures `s^α ds` -/

/-- The power-weighted measure `s^α ds` on `(0,∞)` (scoping note INF22 A4). -/
def powWeight (α : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0:ℝ))).withDensity fun s => ENNReal.ofReal (s ^ α)

instance sigmaFinite_powWeight (α : ℝ) : SigmaFinite (powWeight α) := by
  unfold powWeight; infer_instance

/-- `s^0 ds` is Lebesgue measure on `(0,∞)`. -/
theorem powWeight_zero : powWeight 0 = volume.restrict (Ioi 0) := by
  simp only [powWeight, Real.rpow_zero, ENNReal.ofReal_one]
  exact withDensity_one

theorem powWeight_ac (α : ℝ) : powWeight α ≪ volume.restrict (Ioi 0) :=
  withDensity_absolutelyContinuous _ _

theorem ae_powWeight_pos (α : ℝ) : ∀ᵐ s ∂(powWeight α), 0 < s :=
  (powWeight_ac α).ae_le (ae_restrict_mem measurableSet_Ioi)

/-- Lower integrals against `powWeight α`; no measurability is needed. -/
theorem lintegral_powWeight (α : ℝ) (φ : ℝ → ℝ≥0∞) :
    ∫⁻ s, φ s ∂(powWeight α) = ∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ α) * φ s := by
  rw [powWeight, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (f := fun s => ENNReal.ofReal (s ^ α)) (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rfl

/-- The weighted `L^p` norm as a lower integral; no measurability is needed. -/
theorem eLpNorm_powWeight {ε : Type*} [ENorm ε] (α : ℝ) {p : ℝ} (hp : 0 < p) (g : ℝ → ε) :
    eLpNorm g (ENNReal.ofReal p) (powWeight α) =
      (∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ α) * ‖g s‖ₑ ^ p) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hp]) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le, lintegral_powWeight]

/-- The restriction of `powWeight α` to `(0,S)` is absolutely continuous with respect to
Lebesgue measure on `(0,S)`. -/
theorem powWeight_restrict_ac (α : ℝ) (A : Set ℝ) :
    (powWeight α).restrict A ≪ volume.restrict A :=
  ((powWeight_ac α).trans Measure.absolutelyContinuous_restrict).restrict A

/-! ### Elementary tools -/

/-- `eLpNorm (c * g) = c * eLpNorm g` for `[0,∞]`-valued `g` and any `c ∈ [0,∞]`. -/
theorem eLpNorm_const_mul_enn {β : Type*} [MeasurableSpace β] {μ : Measure β} {g : β → ℝ≥0∞}
    (hg : AEMeasurable g μ) (c : ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun x => c * g x) (ENNReal.ofReal p) μ = c * eLpNorm g (ENNReal.ofReal p) μ := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp [hp]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le]
  simp only [enorm_eq_self, ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  rw [lintegral_const_mul'' _ (hg.pow_const p), ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- The substitution `t = s u` on a measurable set, for any `[0,∞]`-valued integrand. -/
theorem lintegral_image_mul_left {s : ℝ} (hs : 0 < s) {A : Set ℝ} (hA : MeasurableSet A)
    (h : ℝ → ℝ≥0∞) :
    ∫⁻ t in (fun u => s * u) '' A, h t = ENNReal.ofReal s * ∫⁻ u in A, h (s * u) := by
  rw [lintegral_image_eq_lintegral_abs_deriv_mul hA (f' := fun _ => s)
    (fun x _ => (hasDerivAt_const_mul s).hasDerivWithinAt) ((mul_right_injective₀ hs.ne').injOn) h,
    abs_of_pos hs, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Lebesgue-almost-everywhere statements survive the dilation `u ↦ s u`, `s ≠ 0`. -/
theorem ae_comp_mul_left {P : ℝ → Prop} (h : ∀ᵐ t ∂(volume : Measure ℝ), P t) {s : ℝ}
    (hs : s ≠ 0) : ∀ᵐ u ∂(volume : Measure ℝ), P (s * u) :=
  (Measure.quasiMeasurePreserving_smul volume hs).ae h

/-- An indicator kernel on `(0,∞)`. -/
theorem setLIntegral_Ioi_indicator {A : Set ℝ} (hA : MeasurableSet A) (k₀ g : ℝ → ℝ≥0∞) :
    ∫⁻ u in Ioi 0, A.indicator k₀ u * g u = ∫⁻ u in A ∩ Ioi 0, k₀ u * g u := by
  have h : ∀ u, A.indicator k₀ u * g u = A.indicator (fun u => k₀ u * g u) u := fun u => by
    by_cases hu : u ∈ A <;> simp [hu]
  simp_rw [h]
  rw [lintegral_indicator hA, Measure.restrict_restrict hA]

/-! ### Dilation and weight shift -/

/-- **The dilation identity** (`paper/main.tex` 4697–4700, 9923–9925): for `u > 0`,
`‖φ(·u)‖_{L^p(s^α ds)} = u^{-(α+1)/p} ‖φ‖_{L^p(s^α ds)}`. No measurability is needed. -/
theorem eLpNorm_comp_mul_powWeight (α : ℝ) {p : ℝ} (hp : 0 < p) (φ : ℝ → ℝ≥0∞) {u : ℝ}
    (hu : 0 < u) :
    eLpNorm (fun s => φ (s * u)) (ENNReal.ofReal p) (powWeight α) =
      ENNReal.ofReal (u ^ (-(α + 1) / p)) * eLpNorm φ (ENNReal.ofReal p) (powWeight α) := by
  rw [eLpNorm_powWeight α hp, eLpNorm_powWeight α hp]
  simp only [enorm_eq_self]
  set I := ∫⁻ r in Ioi 0, ENNReal.ofReal (r ^ α) * φ r ^ p with hI
  set J := ∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ α) * φ (s * u) ^ p with hJ
  have hIJ : I = ENNReal.ofReal (u ^ (α + 1)) * J := by
    have h1 := lintegral_image_mul_left hu (A := Ioi 0) measurableSet_Ioi
      (fun r => ENNReal.ofReal (r ^ α) * φ r ^ p)
    rw [image_mul_left_Ioi hu, mul_zero] at h1
    rw [hI, h1, hJ, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    have hs' : (0:ℝ) < s := hs
    rw [show u * s = s * u from mul_comm u s, Real.mul_rpow hs'.le hu.le,
      Real.rpow_add hu, Real.rpow_one, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity)]
    ring
  have hJI : J = ENNReal.ofReal (u ^ (-(α + 1))) * I := by
    rw [hIJ, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hu,
      neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
  rw [hJI, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), ← Real.rpow_mul hu.le,
    show -(α + 1) * (1 / p) = -(α + 1) / p by ring]

/-- **Weight shift**: `‖s^β φ‖_{L^p(s^α ds)} = ‖φ‖_{L^p(s^{α+βp} ds)}`. -/
theorem eLpNorm_ofReal_rpow_mul_powWeight (α β : ℝ) {p : ℝ} (hp : 0 < p) (φ : ℝ → ℝ≥0∞) :
    eLpNorm (fun s => ENNReal.ofReal (s ^ β) * φ s) (ENNReal.ofReal p) (powWeight α) =
      eLpNorm φ (ENNReal.ofReal p) (powWeight (α + β * p)) := by
  rw [eLpNorm_powWeight α hp, eLpNorm_powWeight _ hp]
  simp only [enorm_eq_self]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have hs' : (0:ℝ) < s := hs
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le, ← Real.rpow_mul hs'.le, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hs']

/-! ### The Mellin–Minkowski lemma -/

/-- **Mellin–Minkowski**, `[0,∞]`-valued core (BP2): for measurable `k, φ ≥ 0` and `p ≥ 1`,
`‖s ↦ ∫_0^∞ k(u) φ(su) du‖_{L^p(s^α)} ≤ (∫_0^∞ k(u) u^{-(α+1)/p} du) ‖φ‖_{L^p(s^α)}`. -/
theorem eLpNorm_mellin_le_lintegral {p α : ℝ} (hp : 1 ≤ p) {k φ : ℝ → ℝ≥0∞}
    (hk : Measurable k) (hφ : Measurable φ) :
    eLpNorm (fun s => ∫⁻ u in Ioi 0, k u * φ (s * u)) (ENNReal.ofReal p) (powWeight α) ≤
      (∫⁻ u in Ioi 0, k u * ENNReal.ofReal (u ^ (-(α + 1) / p))) *
        eLpNorm φ (ENNReal.ofReal p) (powWeight α) := by
  have hp0 : 0 < p := by linarith
  have hkm : Measurable fun u => k u * ENNReal.ofReal (u ^ (-(α + 1) / p)) :=
    hk.mul (by fun_prop)
  have hF : AEMeasurable (Function.uncurry fun s u => k u * φ (s * u))
      ((powWeight α).prod (volume.restrict (Ioi 0))) := by
    refine Measurable.aemeasurable ?_
    show Measurable fun q : ℝ × ℝ => k q.2 * φ (q.1 * q.2)
    exact (hk.comp measurable_snd).mul (hφ.comp (measurable_fst.mul measurable_snd))
  calc eLpNorm (fun s => ∫⁻ u in Ioi 0, k u * φ (s * u)) (ENNReal.ofReal p) (powWeight α)
      ≤ ∫⁻ u in Ioi 0, eLpNorm (fun s => k u * φ (s * u)) (ENNReal.ofReal p) (powWeight α) :=
        NonUniqueEuler.Conv.eLpNorm_lintegral_le hF (ENNReal.one_le_ofReal.mpr hp)
          ENNReal.ofReal_ne_top
    _ = ∫⁻ u in Ioi 0, k u * ENNReal.ofReal (u ^ (-(α + 1) / p)) *
          eLpNorm φ (ENNReal.ofReal p) (powWeight α) := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
        have hm : Measurable fun s : ℝ => φ (s * u) := hφ.comp (measurable_id.mul_const u)
        rw [eLpNorm_const_mul_enn hm.aemeasurable (k u) hp0,
          eLpNorm_comp_mul_powWeight α hp0 φ hu, mul_assoc]
    _ = (∫⁻ u in Ioi 0, k u * ENNReal.ofReal (u ^ (-(α + 1) / p))) *
          eLpNorm φ (ENNReal.ofReal p) (powWeight α) := lintegral_mul_const _ hkm

/-- **Mellin–Minkowski** (INF22 A4, BP2), the form proposed in the scoping note: for `p ≥ 1`,
measurable `k ≥ 0` and `f` measurable on `(0,∞)`,
`‖s ↦ ∫_0^∞ k(u) ‖f(su)‖ du‖_{L^p(s^α ds)} ≤ (∫_0^∞ k(u) u^{-(α+1)/p} du) ‖f‖_{L^p(s^α ds)}`. -/
theorem eLpNorm_mellin_le {E : Type*} [NormedAddCommGroup E] {p α : ℝ} (hp : 1 ≤ p)
    {k : ℝ → ℝ≥0∞} (hk : Measurable k) {f : ℝ → E}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))) :
    eLpNorm (fun s => ∫⁻ u in Ioi 0, k u * ‖f (s * u)‖ₑ) (ENNReal.ofReal p) (powWeight α) ≤
      (∫⁻ u in Ioi 0, k u * ENNReal.ofReal (u ^ (-(α + 1) / p))) *
        eLpNorm f (ENNReal.ofReal p) (powWeight α) := by
  obtain ⟨f', hf'm, hfe⟩ : ∃ f' : ℝ → E, StronglyMeasurable f' ∧ f =ᵐ[_] f' :=
    ⟨hf.mk f, hf.stronglyMeasurable_mk, hf.ae_eq_mk⟩
  have hφ : Measurable fun t => ‖f' t‖ₑ := hf'm.enorm
  have hff' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioi 0 → f t = f' t :=
    (ae_restrict_iff' measurableSet_Ioi).1 hfe
  have heq : ∀ s, 0 < s → ∫⁻ u in Ioi 0, k u * ‖f (s * u)‖ₑ
      = ∫⁻ u in Ioi 0, k u * ‖f' (s * u)‖ₑ := by
    intro s hs
    refine lintegral_congr_ae ?_
    have h := ae_comp_mul_left hff' hs.ne'
    filter_upwards [ae_restrict_of_ae h, ae_restrict_mem measurableSet_Ioi] with u hu hu0
    rw [hu (mul_pos hs hu0)]
  calc eLpNorm (fun s => ∫⁻ u in Ioi 0, k u * ‖f (s * u)‖ₑ) (ENNReal.ofReal p) (powWeight α)
      = eLpNorm (fun s => ∫⁻ u in Ioi 0, k u * ‖f' (s * u)‖ₑ) (ENNReal.ofReal p)
          (powWeight α) :=
        eLpNorm_congr_ae ((ae_powWeight_pos α).mono fun s hs => heq s hs)
    _ ≤ (∫⁻ u in Ioi 0, k u * ENNReal.ofReal (u ^ (-(α + 1) / p))) *
          eLpNorm (fun t => ‖f' t‖ₑ) (ENNReal.ofReal p) (powWeight α) :=
        eLpNorm_mellin_le_lintegral (φ := fun t => ‖f' t‖ₑ) hp hk hφ
    _ = (∫⁻ u in Ioi 0, k u * ENNReal.ofReal (u ^ (-(α + 1) / p))) *
          eLpNorm f (ENNReal.ofReal p) (powWeight α) := by
        rw [eLpNorm_enorm]
        congr 1
        exact eLpNorm_congr_ae ((powWeight_ac α).ae_le hfe.symm)

/-- **Domination form** of Mellin–Minkowski: if `‖g(s)‖ ≤ c s^β ∫_0^∞ k(u) φ(su) du` for a.e.
`s > 0`, then `‖g‖_{L^p(s^α)} ≤ c (∫_0^∞ k(u) u^{-(α+βp+1)/p} du) ‖φ‖_{L^p(s^{α+βp})}`. -/
theorem eLpNorm_le_mellin {ε : Type*} [ENorm ε] {p α β : ℝ} (hp : 1 ≤ p) {k φ : ℝ → ℝ≥0∞}
    (hk : Measurable k) (hφ : Measurable φ) (c : ℝ≥0∞) {g : ℝ → ε}
    (hg : ∀ᵐ s ∂(volume.restrict (Ioi 0)),
      ‖g s‖ₑ ≤ c * (ENNReal.ofReal (s ^ β) * ∫⁻ u in Ioi 0, k u * φ (s * u))) :
    eLpNorm g (ENNReal.ofReal p) (powWeight α) ≤
      c * ((∫⁻ u in Ioi 0, k u * ENNReal.ofReal (u ^ (-(α + β * p + 1) / p))) *
        eLpNorm φ (ENNReal.ofReal p) (powWeight (α + β * p))) := by
  have hp0 : 0 < p := by linarith
  have hM : Measurable fun s => ∫⁻ u in Ioi 0, k u * φ (s * u) := by
    have : Measurable (Function.uncurry fun s u => k u * φ (s * u)) := by
      show Measurable fun q : ℝ × ℝ => k q.2 * φ (q.1 * q.2)
      exact (hk.comp measurable_snd).mul (hφ.comp (measurable_fst.mul measurable_snd))
    exact this.lintegral_prod_right'
  calc eLpNorm g (ENNReal.ofReal p) (powWeight α)
      ≤ eLpNorm (fun s => c * (ENNReal.ofReal (s ^ β) * ∫⁻ u in Ioi 0, k u * φ (s * u)))
          (ENNReal.ofReal p) (powWeight α) :=
        eLpNorm_mono_enorm_ae ((powWeight_ac α).ae_le (hg.mono fun s hs => by
          rw [enorm_eq_self]; exact hs))
    _ = c * eLpNorm (fun s => ENNReal.ofReal (s ^ β) * ∫⁻ u in Ioi 0, k u * φ (s * u))
          (ENNReal.ofReal p) (powWeight α) :=
        eLpNorm_const_mul_enn ((by fun_prop : Measurable fun s : ℝ => ENNReal.ofReal (s ^ β)).mul
          hM).aemeasurable c hp0
    _ = c * eLpNorm (fun s => ∫⁻ u in Ioi 0, k u * φ (s * u)) (ENNReal.ofReal p)
          (powWeight (α + β * p)) := by
        rw [eLpNorm_ofReal_rpow_mul_powWeight α β hp0]
    _ ≤ _ := mul_le_mul' le_rfl (eLpNorm_mellin_le_lintegral hp hk hφ)

/-! ### The Beta integral -/

/-- **Euler's Beta integral**, real form: for `a, c > 0`,
`∫_0^1 u^{a-1} (1-u)^{c-1} du = Γ(a) Γ(c) / Γ(a+c)` (as a lower integral). -/
theorem lintegral_beta {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∫⁻ u in Ioo 0 1, ENNReal.ofReal (u ^ (a - 1) * (1 - u) ^ (c - 1)) =
      ENNReal.ofReal (Real.Gamma a * Real.Gamma c / Real.Gamma (a + c)) := by
  set B : ℝ → ℝ := fun u => u ^ (a - 1) * (1 - u) ^ (c - 1) with hB
  have hcx : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      (x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((c : ℂ) - 1) = ((B x : ℝ) : ℂ) := by
    intro x hx0 hx1
    simp only [hB]
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx0, Complex.ofReal_cpow (by linarith),
      Complex.ofReal_sub, Complex.ofReal_one]
    push_cast
    ring
  have hconv := Complex.betaIntegral_convergent (u := (a : ℂ)) (v := (c : ℂ))
    (by simpa using ha) (by simpa using hc)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at hconv
  have hint : IntegrableOn B (Ioo 0 1) := by
    have h2 : IntegrableOn (fun x : ℝ => ((B x : ℝ) : ℂ)) (Ioo 0 1) :=
      hconv.congr_fun (fun x hx => hcx x hx.1.le hx.2.le) measurableSet_Ioo
    simpa using h2.re
  have hβ : Complex.betaIntegral a c = ((∫ u in (0:ℝ)..1, B u : ℝ) : ℂ) := by
    unfold Complex.betaIntegral
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    exact hcx x hx.1 hx.2
  have hG := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (a : ℂ)) (t := (c : ℂ))
    (by simpa using ha) (by simpa using hc)
  rw [hβ, ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_inj] at hG
  have hpos : 0 < Real.Gamma (a + c) := Real.Gamma_pos_of_pos (by linarith)
  have hval : ∫ u in (0:ℝ)..1, B u = Real.Gamma a * Real.Gamma c / Real.Gamma (a + c) := by
    rw [hG, mul_div_cancel_left₀ _ hpos.ne']
  rw [← hval, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ofReal_integral_eq_lintegral_ofReal hint]
  exact (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun u hu =>
    mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.rpow_nonneg (by linarith [hu.2]) _))

/-- `∫_0^1 u^{a-1} du = 1/a` for `a > 0`, as a lower integral over `(0,1]`. -/
theorem lintegral_Ioc_rpow {a : ℝ} (ha : 0 < a) :
    ∫⁻ u in Ioc 0 1, ENNReal.ofReal (u ^ (a - 1)) = ENNReal.ofReal (1 / a) := by
  have h := lintegral_beta ha one_pos
  have hG : Real.Gamma a * Real.Gamma 1 / Real.Gamma (a + 1) = 1 / a := by
    rw [Real.Gamma_one, Real.Gamma_add_one ha.ne', mul_one]
    field_simp [(Real.Gamma_pos_of_pos ha).ne']
  rw [hG] at h
  rw [← setLIntegral_congr Ioo_ae_eq_Ioc, ← h]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun u _ => ?_)
  rw [sub_self, Real.rpow_zero, mul_one]

/-! ### The Hardy family -/

/-- **Weighted Hardy inequality on `(0,∞)`** (BP2, `k = 1_{(0,1]}`): for `p ≥ 1`, `a < -1` and
`f` measurable on `(0,∞)`, `‖∫_0^s f‖_{L^p(s^a ds)} ≤ (p/(-a-1)) ‖f‖_{L^p(s^{a+p} ds)}`. -/
theorem hardy_Ioi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p a : ℝ} (hp : 1 ≤ p)
    (ha : a < -1) {f : ℝ → E} (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))) :
    eLpNorm (fun s => ∫ t in (0)..s, f t) (ENNReal.ofReal p) (powWeight a) ≤
      ENNReal.ofReal (p / (-a - 1)) * eLpNorm f (ENNReal.ofReal p) (powWeight (a + p)) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨f', hf'm, hfe⟩ : ∃ f' : ℝ → E, StronglyMeasurable f' ∧ f =ᵐ[_] f' :=
    ⟨hf.mk f, hf.stronglyMeasurable_mk, hf.ae_eq_mk⟩
  have hφ : Measurable fun t => ‖f' t‖ₑ := hf'm.enorm
  have hff' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioi 0 → f t = f' t :=
    (ae_restrict_iff' measurableSet_Ioi).1 hfe
  have hk : Measurable ((Iic (1:ℝ)).indicator (1 : ℝ → ℝ≥0∞)) :=
    measurable_one.indicator measurableSet_Iic
  have hdom : ∀ᵐ s ∂(volume.restrict (Ioi 0)), ‖∫ t in (0)..s, f t‖ₑ ≤
      1 * (ENNReal.ofReal (s ^ (1:ℝ)) * ∫⁻ u in Ioi 0,
        (Iic (1:ℝ)).indicator 1 u * ‖f' (s * u)‖ₑ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : (0:ℝ) < s := hs
    rw [one_mul, Real.rpow_one, setLIntegral_Ioi_indicator measurableSet_Iic,
      show Iic (1:ℝ) ∩ Ioi 0 = Ioc 0 1 by ext; simp [and_comm]]
    simp only [Pi.one_apply, one_mul]
    rw [intervalIntegral.integral_of_le hs'.le]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    have h1 := lintegral_image_mul_left hs' (A := Ioc 0 1) measurableSet_Ioc (fun t => ‖f t‖ₑ)
    rw [image_mul_left_Ioc hs', mul_zero, mul_one] at h1
    rw [h1]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (ae_comp_mul_left hff' hs'.ne'),
      ae_restrict_mem measurableSet_Ioc] with u hu hu0
    rw [hu (mul_pos hs' hu0.1)]
  have h := eLpNorm_le_mellin (α := a) (β := 1) hp hk hφ 1 hdom
  rw [one_mul] at h
  refine h.trans (le_of_eq ?_)
  have hA : 0 < -(a + 1) / p := div_pos (by linarith) hp0
  have hk' : ∫⁻ u in Ioi 0, (Iic (1:ℝ)).indicator 1 u *
      ENNReal.ofReal (u ^ (-(a + 1 * p + 1) / p)) = ENNReal.ofReal (p / (-a - 1)) := by
    rw [setLIntegral_Ioi_indicator measurableSet_Iic,
      show Iic (1:ℝ) ∩ Ioi 0 = Ioc 0 1 by ext; simp [and_comm]]
    simp only [Pi.one_apply, one_mul]
    have h2 := lintegral_Ioc_rpow hA
    have hpne : p ≠ 0 := hp0.ne'
    rw [show -(a + 1) / p - 1 = -(a + p + 1) / p by field_simp; ring, one_div_div,
      show -(a + 1) = -a - 1 by ring] at h2
    exact h2
  rw [hk', show a + 1 * p = a + p by ring, eLpNorm_enorm]
  congr 1
  exact eLpNorm_congr_ae ((powWeight_ac _).ae_le hfe.symm)

/-- `‖∫_0^s f‖_{L^p((0,S), s^a ds)}`-type statements restricted to `(0,S)` reduce to `(0,∞)` by
extending `f` by zero: the extension is measurable on `(0,∞)`. -/
theorem aestronglyMeasurable_indicator_Ioo {E : Type*} [NormedAddCommGroup E] {S : ℝ}
    {f : ℝ → E} (hf : AEStronglyMeasurable f (volume.restrict (Ioo 0 S))) :
    AEStronglyMeasurable ((Ioo 0 S).indicator f) (volume.restrict (Ioi 0)) := by
  refine (aestronglyMeasurable_indicator_iff measurableSet_Ioo).2 ?_
  rw [Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.2 Ioo_subset_Ioi_self]
  exact hf

/-- **B0275, first inequality** (`paper/main.tex` 4702–4718, label
`mixed-background:weighted-integrals`): for `1 ≤ p < 3`, `a_p = p/2 - 5/2`, `b_p = a_p + p`, and
`f` measurable on `(0,S)`,
`‖∫_0^s f‖_{L^p((0,S), s^{a_p} ds)} ≤ (2p/(3-p)) ‖f‖_{L^p((0,S), s^{b_p} ds)}`. -/
theorem hardy_age {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ} (hp1 : 1 ≤ p)
    (hp3 : p < 3) (S : ℝ) {f : ℝ → E} (hf : AEStronglyMeasurable f (volume.restrict (Ioo 0 S))) :
    eLpNorm (fun s => ∫ t in (0)..s, f t) (ENNReal.ofReal p)
        ((powWeight (p / 2 - 5 / 2)).restrict (Ioo 0 S)) ≤
      ENNReal.ofReal (2 * p / (3 - p)) *
        eLpNorm f (ENNReal.ofReal p) ((powWeight (3 * p / 2 - 5 / 2)).restrict (Ioo 0 S)) := by
  set f₀ : ℝ → E := (Ioo 0 S).indicator f with hf₀_def
  have h := hardy_Ioi (a := p / 2 - 5 / 2) hp1 (by linarith)
    (aestronglyMeasurable_indicator_Ioo hf)
  have hconst : p / (-(p / 2 - 5 / 2) - 1) = 2 * p / (3 - p) := by
    rw [show -(p / 2 - 5 / 2) - 1 = (3 - p) / 2 by ring, div_div_eq_mul_div, mul_comm]
  rw [hconst, show p / 2 - 5 / 2 + p = 3 * p / 2 - 5 / 2 by ring,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo] at h
  refine le_trans (le_of_eq ?_) ((eLpNorm_mono_measure _
    (Measure.restrict_le_self (s := Ioo 0 S))).trans h)
  refine eLpNorm_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  rw [intervalIntegral.integral_of_le hs.1.le, intervalIntegral.integral_of_le hs.1.le]
  refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  have hmem : t ∈ Ioo 0 S := ⟨ht.1, ht.2.trans_lt hs.2⟩
  rw [Set.indicator_of_mem hmem]

/-- `‖∫_0^s f‖_{L^p(s^{a_p})} ≤ 22 ‖f‖_{L^p(s^{b_p})}` at `p = 11/4` (`paper/main.tex` 4713:
"the first is `22`"); here `a_p = -9/8` and `b_p = 13/8`. -/
theorem hardy_age_eleven_quarters {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : ℝ)
    {f : ℝ → E} (hf : AEStronglyMeasurable f (volume.restrict (Ioo 0 S))) :
    eLpNorm (fun s => ∫ t in (0)..s, f t) (ENNReal.ofReal (11 / 4))
        ((powWeight (-(9 / 8))).restrict (Ioo 0 S)) ≤
      22 * eLpNorm f (ENNReal.ofReal (11 / 4)) ((powWeight (13 / 8)).restrict (Ioo 0 S)) := by
  have h := hardy_age (p := 11 / 4) (by norm_num) (by norm_num) S hf
  have e1 : (11 / 4 : ℝ) / 2 - 5 / 2 = -(9 / 8) := by norm_num
  have e2 : 3 * (11 / 4 : ℝ) / 2 - 5 / 2 = 13 / 8 := by norm_num
  have e3 : ENNReal.ofReal (2 * (11 / 4) / (3 - 11 / 4)) = 22 := by
    rw [show (2 * (11 / 4) / (3 - 11 / 4) : ℝ) = 22 by norm_num]; simp
  rwa [e1, e2, e3] at h

/-! ### Square-root (Volterra) kernels -/

/-- The substitution `t = s u` on `(0,s]`. -/
theorem lintegral_Ioc_scale {s : ℝ} (hs : 0 < s) (ψ : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioc 0 s, ψ t = ENNReal.ofReal s * ∫⁻ u in Ioc 0 1, ψ (s * u) := by
  have h1 := lintegral_image_mul_left hs (A := Ioc 0 1) measurableSet_Ioc ψ
  rwa [image_mul_left_Ioc hs, mul_zero, mul_one] at h1

/-- `t = s u` in the square-root kernel: `∫_0^s (s-t)^{-1/2} ψ(t) dt
= s^{1/2} ∫_0^1 (1-u)^{-1/2} ψ(su) du` (`paper/main.tex` 4701, 9923). -/
theorem lintegral_volterra_scale {s : ℝ} (hs : 0 < s) (ψ : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioc 0 s, ENNReal.ofReal ((s - t) ^ (-(1 / 2 : ℝ))) * ψ t =
      ENNReal.ofReal (s ^ (1 / 2 : ℝ)) *
        ∫⁻ u in Ioc 0 1, ENNReal.ofReal ((1 - u) ^ (-(1 / 2 : ℝ))) * ψ (s * u) := by
  rw [lintegral_Ioc_scale hs, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
  have h1u : 0 ≤ 1 - u := by linarith [hu.2]
  have hss : s * s ^ (-(1 / 2 : ℝ)) = s ^ (1 / 2 : ℝ) := by
    have h := Real.rpow_add hs 1 (-(1 / 2))
    rw [Real.rpow_one] at h
    rw [← h]
    norm_num
  have key : s * (s - s * u) ^ (-(1 / 2 : ℝ)) = s ^ (1 / 2 : ℝ) * (1 - u) ^ (-(1 / 2 : ℝ)) := by
    rw [show s - s * u = s * (1 - u) by ring, Real.mul_rpow hs.le h1u, ← mul_assoc, hss]
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hs.le, key,
    ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _)]

/-- The square-root kernel `k(u) = 1_{(0,1]}(u) (1-u)^{-1/2}`. -/
def sqrtKernel : ℝ → ℝ≥0∞ := (Iic (1:ℝ)).indicator fun u => ENNReal.ofReal ((1 - u) ^ (-(1 / 2 : ℝ)))

theorem measurable_sqrtKernel : Measurable sqrtKernel :=
  Measurable.indicator (by fun_prop) measurableSet_Iic

theorem setLIntegral_sqrtKernel (g : ℝ → ℝ≥0∞) :
    ∫⁻ u in Ioi 0, sqrtKernel u * g u =
      ∫⁻ u in Ioc 0 1, ENNReal.ofReal ((1 - u) ^ (-(1 / 2 : ℝ))) * g u := by
  rw [sqrtKernel, setLIntegral_Ioi_indicator measurableSet_Iic,
    show Iic (1:ℝ) ∩ Ioi 0 = Ioc 0 1 by ext; simp [and_comm]]

/-- The Mellin constant of the square-root kernel is a Beta value:
`∫_0^1 (1-u)^{-1/2} u^{A-1} du = Γ(A)Γ(1/2)/Γ(A+1/2)` for `A > 0`. -/
theorem lintegral_sqrtKernel_rpow {A e : ℝ} (hA : 0 < A) (he : e = A - 1) :
    ∫⁻ u in Ioi 0, sqrtKernel u * ENNReal.ofReal (u ^ e) =
      ENNReal.ofReal (Real.Gamma A * Real.Gamma (1 / 2) / Real.Gamma (A + 1 / 2)) := by
  subst he
  rw [setLIntegral_sqrtKernel, ← lintegral_beta hA one_half_pos, ← setLIntegral_congr Ioo_ae_eq_Ioc]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun u hu => ?_)
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith [hu.2]) _), mul_comm]
  norm_num

/-- **B0275, second inequality** (`paper/main.tex` 4702–4718): for `p ≥ 1`, `(b+1)/p < 1` and
`f` measurable on `(0,S)`,
`‖∫_0^s (s-t)^{-1/2} f(t) dt‖_{L^p((0,S),s^b ds)} ≤ √S · B(1-(b+1)/p, 1/2) ‖f‖_{L^p((0,S),s^b ds)}`
with `B(A,1/2) = Γ(A)Γ(1/2)/Γ(A+1/2)`. -/
theorem volterra_age {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p b : ℝ}
    (hp : 1 ≤ p) (hb : (b + 1) / p < 1) (S : ℝ) {f : ℝ → E}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioo 0 S))) :
    eLpNorm (fun s => ∫ t in (0)..s, (s - t) ^ (-(1 / 2 : ℝ)) • f t) (ENNReal.ofReal p)
        ((powWeight b).restrict (Ioo 0 S)) ≤
      ENNReal.ofReal (Real.sqrt S * (Real.Gamma (1 - (b + 1) / p) * Real.Gamma (1 / 2) /
          Real.Gamma (1 - (b + 1) / p + 1 / 2))) *
        eLpNorm f (ENNReal.ofReal p) ((powWeight b).restrict (Ioo 0 S)) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨f', hf'm, hfe⟩ : ∃ f' : ℝ → E, StronglyMeasurable f' ∧ f =ᵐ[_] f' :=
    ⟨hf.mk f, hf.stronglyMeasurable_mk, hf.ae_eq_mk⟩
  have hff' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo 0 S → f t = f' t :=
    (ae_restrict_iff' measurableSet_Ioo).1 hfe
  set φ : ℝ → ℝ≥0∞ := (Ioo 0 S).indicator fun t => ‖f' t‖ₑ with hφ_def
  have hφ : Measurable φ := hf'm.enorm.indicator measurableSet_Ioo
  set g : ℝ → E := fun s => ∫ t in (0)..s, (s - t) ^ (-(1 / 2 : ℝ)) • f t
  have hdom : ∀ᵐ s ∂(volume.restrict (Ioi 0)), ‖(Ioo 0 S).indicator g s‖ₑ ≤
      ENNReal.ofReal (Real.sqrt S) * (ENNReal.ofReal (s ^ (0:ℝ)) *
        ∫⁻ u in Ioi 0, sqrtKernel u * φ (s * u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : (0:ℝ) < s := hs
    by_cases hsS : s ∈ Ioo 0 S
    · rw [indicator_of_mem hsS, Real.rpow_zero, ENNReal.ofReal_one, one_mul,
        setLIntegral_sqrtKernel]
      calc ‖g s‖ₑ
          ≤ ∫⁻ t in Ioc 0 s, ‖(s - t) ^ (-(1 / 2 : ℝ)) • f t‖ₑ := by
            simp only [g]
            rw [intervalIntegral.integral_of_le hs'.le]
            exact enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ t in Ioc 0 s, ENNReal.ofReal ((s - t) ^ (-(1 / 2 : ℝ))) * ‖f t‖ₑ := by
            refine setLIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
            rw [enorm_smul, Real.enorm_eq_ofReal (Real.rpow_nonneg (by linarith [ht.2]) _)]
        _ = ENNReal.ofReal (s ^ (1 / 2 : ℝ)) *
              ∫⁻ u in Ioc 0 1, ENNReal.ofReal ((1 - u) ^ (-(1 / 2 : ℝ))) * ‖f (s * u)‖ₑ :=
            lintegral_volterra_scale hs' (fun t => ‖f t‖ₑ)
        _ = ENNReal.ofReal (s ^ (1 / 2 : ℝ)) *
              ∫⁻ u in Ioc 0 1, ENNReal.ofReal ((1 - u) ^ (-(1 / 2 : ℝ))) * φ (s * u) := by
            congr 1
            refine lintegral_congr_ae ?_
            filter_upwards [ae_restrict_of_ae (ae_comp_mul_left hff' hs'.ne'),
              ae_restrict_mem measurableSet_Ioc] with u hu hu0
            have hsu : s * u ∈ Ioo 0 S :=
              ⟨mul_pos hs' hu0.1, (mul_le_of_le_one_right hs'.le hu0.2).trans_lt hsS.2⟩
            rw [hφ_def, indicator_of_mem hsu, hu hsu]
        _ ≤ _ := by
            gcongr
            rw [Real.sqrt_eq_rpow]
            exact Real.rpow_le_rpow hs'.le hsS.2.le (by norm_num)
    · rw [indicator_of_notMem hsS, enorm_zero]
      exact zero_le
  have h := eLpNorm_le_mellin (α := b) (β := 0) hp measurable_sqrtKernel hφ _ hdom
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo]
  refine h.trans (le_of_eq ?_)
  have hA : 0 < 1 - (b + 1) / p := by linarith
  rw [lintegral_sqrtKernel_rpow hA (by field_simp; ring), zero_mul, add_zero, hφ_def,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo, eLpNorm_enorm,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_assoc]
  congr 2
  exact eLpNorm_congr_ae ((powWeight_restrict_ac b _).ae_le hfe.symm)

/-! ### Hardy–Beta (B0611) -/

/-- **B0611, domination form** (`paper/main.tex` 9913–9927): any `g` with
`‖g(s)‖ ≤ ∫_0^s (s-t)^{-1/2} ‖f(t)‖ dt` for a.e. `s > 0` satisfies
`‖g‖_{L²(s^{-3/2}ds)} ≤ B(3/4,1/2) ‖f‖_{L²(s^{-1/2}ds)}`, `B(3/4,1/2) = Γ(3/4)Γ(1/2)/Γ(5/4)`. -/
theorem hardy_beta_of_le {E ε : Type*} [NormedAddCommGroup E] [ENorm ε] {f : ℝ → E}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))) {g : ℝ → ε}
    (hg : ∀ᵐ s ∂(volume.restrict (Ioi (0:ℝ))),
      ‖g s‖ₑ ≤ ∫⁻ t in Ioc 0 s, ENNReal.ofReal ((s - t) ^ (-(1 / 2 : ℝ))) * ‖f t‖ₑ) :
    eLpNorm g 2 (powWeight (-(3 / 2))) ≤
      ENNReal.ofReal (Real.Gamma (3 / 4) * Real.Gamma (1 / 2) / Real.Gamma (5 / 4)) *
        eLpNorm f 2 (powWeight (-(1 / 2))) := by
  obtain ⟨f', hf'm, hfe⟩ : ∃ f' : ℝ → E, StronglyMeasurable f' ∧ f =ᵐ[_] f' :=
    ⟨hf.mk f, hf.stronglyMeasurable_mk, hf.ae_eq_mk⟩
  have hff' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioi 0 → f t = f' t :=
    (ae_restrict_iff' measurableSet_Ioi).1 hfe
  have hφ : Measurable fun t => ‖f' t‖ₑ := hf'm.enorm
  have hdom : ∀ᵐ s ∂(volume.restrict (Ioi 0)), ‖g s‖ₑ ≤
      1 * (ENNReal.ofReal (s ^ (1 / 2 : ℝ)) * ∫⁻ u in Ioi 0, sqrtKernel u * ‖f' (s * u)‖ₑ) := by
    filter_upwards [hg, ae_restrict_mem measurableSet_Ioi] with s hs hs0
    have hs' : (0:ℝ) < s := hs0
    have hv := lintegral_volterra_scale hs' (fun t => ‖f' t‖ₑ)
    rw [one_mul, setLIntegral_sqrtKernel, ← hv]
    refine hs.trans (le_of_eq (lintegral_congr_ae ?_))
    filter_upwards [ae_restrict_of_ae hff', ae_restrict_mem measurableSet_Ioc] with t ht ht0
    rw [ht ht0.1]
  have h := eLpNorm_le_mellin (α := -(3 / 2)) (β := 1 / 2) (p := 2) one_le_two
    measurable_sqrtKernel hφ 1 hdom
  rw [ENNReal.ofReal_ofNat, one_mul, lintegral_sqrtKernel_rpow (A := 3 / 4) (by norm_num)
    (by norm_num), show (-(3 / 2) + 1 / 2 * 2 : ℝ) = -(1 / 2) by norm_num, eLpNorm_enorm,
    show (3 / 4 + 1 / 2 : ℝ) = 5 / 4 by norm_num] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  exact eLpNorm_congr_ae ((powWeight_ac _).ae_le hfe.symm)

/-- **B0611, the Hardy–Beta inequality `eq:st18-t00558`** with the multiplier of
`paper/main.tex` 9927 (INF22 A4): for `f` measurable on `(0,∞)` and `c : ℝ → ℂ` with
`‖c(u)‖ ≤ 1` on `(0,1]` (for instance `c(u) = u^μ`, `Re μ ≥ 0`),
`‖s ↦ ∫_0^s c(t/s) (s-t)^{-1/2} f(t) dt‖_{L²(s^{-3/2}ds)}
≤ Γ(3/4)Γ(1/2)/Γ(5/4) · ‖f‖_{L²(s^{-1/2}ds)}`. -/
theorem hardy_beta {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℝ → E}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (c : ℝ → ℂ)
    (hc : ∀ u ∈ Ioc (0:ℝ) 1, ‖c u‖ ≤ 1) :
    eLpNorm (fun s => ∫ t in (0)..s, (c (t / s) * (((s - t) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • f t) 2
        (powWeight (-(3 / 2))) ≤
      ENNReal.ofReal (Real.Gamma (3 / 4) * Real.Gamma (1 / 2) / Real.Gamma (5 / 4)) *
        eLpNorm f 2 (powWeight (-(1 / 2))) := by
  refine hardy_beta_of_le hf ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs' : (0:ℝ) < s := hs
  rw [intervalIntegral.integral_of_le hs'.le]
  refine (enorm_integral_le_lintegral_enorm _).trans
    (setLIntegral_mono' measurableSet_Ioc fun t ht => ?_)
  have hst : 0 ≤ s - t := by linarith [ht.2]
  have hcu : ‖c (t / s)‖ ≤ 1 :=
    hc _ ⟨div_pos ht.1 hs', (div_le_one hs').2 ht.2⟩
  have hreal : ‖(((s - t) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ₑ =
      ENNReal.ofReal ((s - t) ^ (-(1 / 2 : ℝ))) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hst _)]
  rw [enorm_smul, enorm_mul, hreal]
  calc ‖c (t / s)‖ₑ * ENNReal.ofReal ((s - t) ^ (-(1 / 2 : ℝ))) * ‖f t‖ₑ
      ≤ 1 * ENNReal.ofReal ((s - t) ^ (-(1 / 2 : ℝ))) * ‖f t‖ₑ := by
        gcongr
        rw [← ofReal_norm, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hcu
    _ = _ := by rw [one_mul]

/-- B0611 without multiplier, for real scalars:
`‖∫_0^s (s-t)^{-1/2} f(t) dt‖_{L²(s^{-3/2}ds)} ≤ B(3/4,1/2) ‖f‖_{L²(s^{-1/2}ds)}`. -/
theorem hardy_beta_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))) :
    eLpNorm (fun s => ∫ t in (0)..s, (s - t) ^ (-(1 / 2 : ℝ)) • f t) 2
        (powWeight (-(3 / 2))) ≤
      ENNReal.ofReal (Real.Gamma (3 / 4) * Real.Gamma (1 / 2) / Real.Gamma (5 / 4)) *
        eLpNorm f 2 (powWeight (-(1 / 2))) := by
  refine hardy_beta_of_le hf ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs' : (0:ℝ) < s := hs
  rw [intervalIntegral.integral_of_le hs'.le]
  refine (enorm_integral_le_lintegral_enorm _).trans
    (le_of_eq (setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_))
  rw [enorm_smul, Real.enorm_eq_ofReal (Real.rpow_nonneg (by linarith [ht.2]) _)]

/-! ### The tail Hardy inequality (B0582) -/

/-- `∫_1^∞ u^{-3/2} du = 2`. -/
theorem lintegral_Ioi_one_rpow_neg_three_halves :
    ∫⁻ u in Ioi 1, ENNReal.ofReal (u ^ (-(3 / 2) : ℝ)) = 2 := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos)
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u hu =>
      Real.rpow_nonneg (le_of_lt (lt_trans one_pos hu)) _)),
    integral_Ioi_rpow_of_lt (by norm_num) one_pos, Real.one_rpow]
  norm_num

/-- **B0582, half-line Hardy inequality** (`paper/main.tex` 9412–9425; BP2 with
`k = 1_{(1,∞)}`): for `f` measurable on `(0,∞)`,
`‖η ↦ ∫_η^∞ f‖_{L²(0,∞)} ≤ 2 ‖ξ ↦ ξ f(ξ)‖_{L²(0,∞)}`. -/
theorem hardy_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))) :
    eLpNorm (fun η => ∫ ξ in Ioi η, f ξ) 2 (volume.restrict (Ioi 0)) ≤
      2 * eLpNorm (fun ξ => ξ • f ξ) 2 (volume.restrict (Ioi 0)) := by
  obtain ⟨f', hf'm, hfe⟩ : ∃ f' : ℝ → E, StronglyMeasurable f' ∧ f =ᵐ[_] f' :=
    ⟨hf.mk f, hf.stronglyMeasurable_mk, hf.ae_eq_mk⟩
  have hff' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioi 0 → f t = f' t :=
    (ae_restrict_iff' measurableSet_Ioi).1 hfe
  have hφ : Measurable fun t => ‖f' t‖ₑ := hf'm.enorm
  have hk : Measurable ((Ioi (1:ℝ)).indicator (1 : ℝ → ℝ≥0∞)) :=
    measurable_one.indicator measurableSet_Ioi
  have hset : Ioi (1:ℝ) ∩ Ioi 0 = Ioi 1 := inter_eq_left.2 (Ioi_subset_Ioi zero_le_one)
  have hdom : ∀ᵐ η ∂(volume.restrict (Ioi 0)), ‖∫ ξ in Ioi η, f ξ‖ₑ ≤
      1 * (ENNReal.ofReal (η ^ (1:ℝ)) * ∫⁻ u in Ioi 0,
        (Ioi (1:ℝ)).indicator 1 u * ‖f' (η * u)‖ₑ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with η hη
    have hη' : (0:ℝ) < η := hη
    rw [one_mul, Real.rpow_one, setLIntegral_Ioi_indicator measurableSet_Ioi, hset]
    simp only [Pi.one_apply, one_mul]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    have h1 := lintegral_image_mul_left hη' (A := Ioi 1) measurableSet_Ioi (fun t => ‖f t‖ₑ)
    rw [image_mul_left_Ioi hη', mul_one] at h1
    rw [h1]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (ae_comp_mul_left hff' hη'.ne'),
      ae_restrict_mem measurableSet_Ioi] with u hu hu1
    rw [hu (mul_pos hη' (lt_trans one_pos hu1))]
  have h := eLpNorm_le_mellin (α := 0) (β := 1) (p := 2) one_le_two hk hφ 1 hdom
  have hk2 : ∫⁻ u in Ioi 0, (Ioi (1:ℝ)).indicator 1 u *
      ENNReal.ofReal (u ^ (-(0 + 1 * 2 + 1) / 2 : ℝ)) = 2 := by
    rw [setLIntegral_Ioi_indicator measurableSet_Ioi, hset]
    simp only [Pi.one_apply, one_mul]
    rw [← lintegral_Ioi_one_rpow_neg_three_halves]
    norm_num
  rw [ENNReal.ofReal_ofNat, one_mul, hk2, powWeight_zero] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  have e := eLpNorm_ofReal_rpow_mul_powWeight 0 1 two_pos (fun t => ‖f' t‖ₑ)
  rw [ENNReal.ofReal_ofNat] at e
  rw [← e, powWeight_zero]
  refine eLpNorm_congr_enorm_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hfe] with ξ hξ hξf
  have hξ' : (0:ℝ) < ξ := hξ
  rw [enorm_eq_self, Real.rpow_one, enorm_smul, Real.enorm_eq_ofReal hξ'.le, hξf]

end UnforcedLeray.Conv
