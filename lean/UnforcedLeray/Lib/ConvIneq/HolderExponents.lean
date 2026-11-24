import UnforcedLeray.Lib.ConvIneq.MellinHardy
import UnforcedLeray.Units.B0276
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Data.ENNReal.Holder

/-!
# Hölder wrappers for the manuscript's exponents (INF22 A6)

Blueprint infrastructure target **INF22 A6** of the scoping note

uses in §2.5). Mathlib's Hölder inequality (`eLpNorm_smul_le_mul_eLpNorm`,
`Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean`) is driven by the class
`ENNReal.HolderTriple p q r` (`p⁻¹ + q⁻¹ = r⁻¹`). This file supplies:

* `holderTriple_ofReal`: real exponents with `1/p + 1/q = 1/r` give a triple of `ENNReal.ofReal`s,
  the form in which the Young inequalities of `YoungGroup.lean` take their exponents;
* instances for the manuscript's triples:
  `(11/4, 22/3, 2)`, i.e. `1/2 = 4/11 + 3/22` (`paper/main.tex` 9236–9245, 10518–10537;
  B0740, B0957, B0285, B0288);
  `(11/4, 2, 22/19)`, i.e. `19/22 = 4/11 + 1/2` (`paper/main.tex` 10518–10537, B0957);
  `(22/19, 22/3, 1)`, the pointwise kernel pairing (`paper/main.tex` 8960–8967, B0561);
  `(4, 4, 2)` (`paper/main.tex` 5955–5958, B0699);
  `(3, 2, 6/5)` and `(6/5, 6, 1)`, the three-factor case `1/3 + 1/2 + 1/6 = 1`
  (`paper/main.tex` 311–320, B1010);
* three-factor Hölder `eLpNorm_mul_mul_le` and its `L³·L²·L⁶ ⊂ L¹` form
  `lintegral_enorm_mul_mul_le_three_two_six` (B1010);
* age Hölder with power weights in the `powWeight` notation of `MellinHardy.lean`
  (B0276, `paper/main.tex` 4783–4794), as wrappers of the compiled draft


**Conventions.** Exponents that are not integers are written `ENNReal.ofReal (a/b)`; the
integer exponents `1, 2, 3, 4, 6` are `ℝ≥0∞` numerals, as in Mathlib's `L²` statements. Norms
are `eLpNorm`, valued in `[0,∞]`: nothing is assumed finite.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Conv

/-! ### Hölder triples of real exponents -/

/-- Real exponents `p, q, r > 0` with `1/p + 1/q = 1/r` form a Hölder triple of
`ENNReal.ofReal`s. -/
theorem holderTriple_ofReal {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (h : 1 / p + 1 / q = 1 / r) :
    ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) (ENNReal.ofReal r) := by
  constructor
  rw [← ENNReal.ofReal_inv_of_pos hp, ← ENNReal.ofReal_inv_of_pos hq,
    ← ENNReal.ofReal_inv_of_pos hr, ← ENNReal.ofReal_add (inv_nonneg.2 hp.le)
    (inv_nonneg.2 hq.le)]
  congr 1
  simpa only [one_div] using h

/-- `1/2 = 4/11 + 3/22`: `L^{11/4} · L^{22/3} ⊂ L²` (`paper/main.tex` 9236–9245 and
10518–10537; B0740, B0957; the pair `p = 11/4`, `r = 22/3` of B0285, B0288). -/
instance holderTriple_elevenFourths_twentytwoThirds :
    ENNReal.HolderTriple (ENNReal.ofReal (11 / 4)) (ENNReal.ofReal (22 / 3)) 2 := by
  have h := holderTriple_ofReal (p := 11 / 4) (q := 22 / 3) (r := 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rwa [ENNReal.ofReal_ofNat] at h

/-- `19/22 = 4/11 + 1/2`: `L^{11/4} · L² ⊂ L^{22/19}` (`paper/main.tex` 10518–10537, B0957). -/
instance holderTriple_elevenFourths_two :
    ENNReal.HolderTriple (ENNReal.ofReal (11 / 4)) 2 (ENNReal.ofReal (22 / 19)) := by
  have h := holderTriple_ofReal (p := 11 / 4) (q := 2) (r := 22 / 19) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rwa [ENNReal.ofReal_ofNat] at h

/-- `19/22 + 3/22 = 1`: the pointwise pairing of an `L^{22/19}` source with an `L^{22/3}`
kernel (`paper/main.tex` 8960–8967, B0561). -/
instance holderTriple_twentytwoNineteenths_twentytwoThirds :
    ENNReal.HolderTriple (ENNReal.ofReal (22 / 19)) (ENNReal.ofReal (22 / 3)) 1 := by
  have h := holderTriple_ofReal (p := 22 / 19) (q := 22 / 3) (r := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rwa [ENNReal.ofReal_one] at h

/-- `1/4 + 1/4 = 1/2`: `L⁴ · L⁴ ⊂ L²` (`paper/main.tex` 5955–5958, B0699). -/
instance holderTriple_four_four : ENNReal.HolderTriple 4 4 2 := by
  have h := holderTriple_ofReal (p := 4) (q := 4) (r := 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simpa only [ENNReal.ofReal_ofNat] using h

/-- `1/3 + 1/2 = 5/6`: first step of `L³ · L² · L⁶ ⊂ L¹` (`paper/main.tex` 311–320, B1010). -/
instance holderTriple_three_two : ENNReal.HolderTriple 3 2 (ENNReal.ofReal (6 / 5)) := by
  have h := holderTriple_ofReal (p := 3) (q := 2) (r := 6 / 5) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simpa only [ENNReal.ofReal_ofNat] using h

/-- `5/6 + 1/6 = 1`: second step of `L³ · L² · L⁶ ⊂ L¹` (`paper/main.tex` 311–320, B1010). -/
instance holderTriple_sixFifths_six : ENNReal.HolderTriple (ENNReal.ofReal (6 / 5)) 6 1 := by
  have h := holderTriple_ofReal (p := 6 / 5) (q := 6) (r := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using h

/-! ### Three-factor Hölder -/

section ThreeFactor

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Three-factor Hölder**: for `p⁻¹ + q⁻¹ = s⁻¹` and `s⁻¹ + t⁻¹ = r⁻¹`,
`‖f g h‖_{L^r} ≤ ‖f‖_{L^p} ‖g‖_{L^q} ‖h‖_{L^t}`, in `[0,∞]`. -/
theorem eLpNorm_mul_mul_le {𝕜 : Type*} [NormedRing 𝕜] {f g h : α → 𝕜}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hh : AEStronglyMeasurable h μ) {p q s t r : ℝ≥0∞} [ENNReal.HolderTriple p q s]
    [ENNReal.HolderTriple s t r] :
    eLpNorm (fun x => f x * g x * h x) r μ ≤ eLpNorm f p μ * eLpNorm g q μ * eLpNorm h t μ := by
  have h1 := eLpNorm_smul_le_mul_eLpNorm (p := p) (q := q) (r := s) (μ := μ) hg hf
  have h2 := eLpNorm_smul_le_mul_eLpNorm (p := s) (q := t) (r := r) (μ := μ) hh (hf.mul hg)
  have e1 : f • g = f * g := by
    funext x
    simp only [Pi.mul_apply, smul_eq_mul]
  have e2 : (f * g) • h = fun x => f x * g x * h x := by
    funext x
    simp only [Pi.mul_apply, smul_eq_mul]
  rw [e1] at h1
  rw [e2] at h2
  exact h2.trans (by gcongr)

/-- **`L³ · L² · L⁶ ⊂ L¹`** (`paper/main.tex` 311–320, B1010):
`∫ ‖f‖ ‖g‖ ‖h‖ ≤ ‖f‖_{L³} ‖g‖_{L²} ‖h‖_{L⁶}` for functions with values in any normed groups,
as lower integrals (no integrability assumed). -/
theorem lintegral_enorm_mul_mul_le_three_two_six {E F G : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedAddCommGroup G] {f : α → E} {g : α → F} {h : α → G}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hh : AEStronglyMeasurable h μ) :
    ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ * ‖h x‖ₑ ∂μ ≤ eLpNorm f 3 μ * eLpNorm g 2 μ * eLpNorm h 6 μ := by
  have key := eLpNorm_mul_mul_le (𝕜 := ℝ) (p := 3) (q := 2) (s := ENNReal.ofReal (6 / 5))
    (t := 6) (r := 1) hf.norm hg.norm hh.norm
  rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_norm, eLpNorm_norm, eLpNorm_norm] at key
  refine le_trans (le_of_eq ?_) key
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm, ofReal_norm]

end ThreeFactor

/-! ### Age Hölder with power weights (B0276) -/

/-- Lower integrals over a subset of `(0,∞)` against `s^α ds`. -/
theorem setLIntegral_powWeight (α : ℝ) {A : Set ℝ} (hA : MeasurableSet A) (hA0 : A ⊆ Ioi 0)
    (φ : ℝ → ℝ≥0∞) :
    ∫⁻ s in A, φ s ∂(powWeight α) = ∫⁻ s in A, ENNReal.ofReal (s ^ α) * φ s := by
  rw [powWeight, restrict_withDensity hA, Measure.restrict_restrict hA,
    inter_eq_left.2 hA0, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (f := fun s => ENNReal.ofReal (s ^ α)) (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rfl

/-- The weighted age norm `‖k‖_{p,b;Y}` of `paper/main.tex` 4753–4754 (draft
`UnforcedLeray.B0276.weightedAgeNorm`) is the `L^p` norm for `powWeight b` restricted to
`(0,S)`. -/
theorem eLpNorm_powWeight_restrict_Ioo {Y : Type*} [NormedAddCommGroup Y] {p : ℝ} (hp : 0 < p)
    (b S : ℝ) (k : ℝ → Y) :
    eLpNorm k (ENNReal.ofReal p) ((powWeight b).restrict (Ioo 0 S)) =
      B0276.weightedAgeNorm p b S k := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le, setLIntegral_powWeight b measurableSet_Ioo Ioo_subset_Ioi_self]
  rfl

/-- **Age Hölder with a power weight**, any `p > 1` and real `b` (`paper/main.tex` 4787–4793
before the exponents are fixed):
`∫_0^S ‖k‖ ≤ (∫_0^S s^{-b/(p-1)} ds)^{(p-1)/p} ‖k‖_{L^p((0,S), s^b ds)}`. -/
theorem lintegral_enorm_le_age_holder {Y : Type*} [NormedAddCommGroup Y] {p b S : ℝ}
    (hp : 1 < p) {k : ℝ → Y}
    (hk : AEMeasurable (fun s => ‖k s‖ₑ) (volume.restrict (Ioo 0 S))) :
    ∫⁻ s in Ioo 0 S, ‖k s‖ₑ ≤
      (∫⁻ s in Ioo 0 S, ENNReal.ofReal (s ^ (-(b / (p - 1))))) ^ ((p - 1) / p) *
        eLpNorm k (ENNReal.ofReal p) ((powWeight b).restrict (Ioo 0 S)) := by
  rw [eLpNorm_powWeight_restrict_Ioo (by linarith)]
  exact B0276.lintegral_enorm_le_holder hp hk

/-- **B0276** (`paper/main.tex` 4783–4794, `mixed-background:C.4`), in the `powWeight`
notation: for `p = 11/4`, `b = 13/8`,
`‖k‖_{L¹(0,S;Y)} ≤ 14^{7/11} S^{1/22} ‖k‖_{L^{11/4}((0,S), s^{13/8} ds)}`. -/
theorem eLpNorm_one_le_age_holder {Y : Type*} [NormedAddCommGroup Y] {S : ℝ} {k : ℝ → Y}
    (hk : AEStronglyMeasurable k (volume.restrict (Ioo 0 S))) :
    eLpNorm k 1 (volume.restrict (Ioo 0 S)) ≤
      ENNReal.ofReal ((14 : ℝ) ^ (7 / 11 : ℝ) * S ^ (1 / 22 : ℝ)) *
        eLpNorm k (ENNReal.ofReal (11 / 4)) ((powWeight (13 / 8)).restrict (Ioo 0 S)) := by
  rw [eLpNorm_powWeight_restrict_Ioo (by norm_num)]
  exact B0276.eLpNorm_one_le_weightedAgeNorm hk

end UnforcedLeray.Conv
