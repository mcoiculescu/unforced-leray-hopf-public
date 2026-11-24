import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.FlatGraphOrg
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_2
import UnforcedLeray.Short.PartIIb.Org.QPeriodicHalfSpace.Basic

/-!
# `PartII-b:T13/1/7` decomposition: the window estimates

Source: `the November 2 reference manuscript` lines 1928-1933. The window estimate
is first proved for one scalar component `b_i` (`WbdScalar`: this is where the cut-off heat
equation, the cylinder estimates and the weight comparison enter); `windowBound_of_scalar` is the
(proved) passage from the components to the meridional vector `(b_1, b_2)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

/-- The cutoff bounds of `WinCutProps` with the explicit constant `M`. -/
def WinCutBd (M : ℝ) : Prop :=
  ∀ a : ℝ, 0 < a →
    ContDiff ℝ ∞ (winCut a) ∧ (∀ s ∈ Icc a (2 * a), winCut a s = 1) ∧
      tsupport (winCut a) ⊆ Icc (a / 2) (4 * a) ∧ (∀ s, 0 ≤ winCut a s ∧ winCut a s ≤ 1) ∧
      ∀ s, |deriv (winCut a) s| ≤ M / a

/-- **Scalar window estimate** (SP 1928-1933), for one component `b_i`, on one window `(a, 2a)`:
local weak derivatives `T = S b_i`, `P = ∂_q b_i`, `Q = ∂_η b_i` (periodic, measurable), with
`‖T‖ ≤ K0 (‖G‖ + ‖b‖)` and `√ν ‖√s P‖, √ν ‖√s Q‖ ≤ K0 (‖G‖ + ‖b‖)`, windows as in
`WindowBound`, `K0` independent of `ν, c, a, G, b, i`. -/
def WbdScalar : Prop :=
  ∀ r : ℝ, 1 < r → r < 3 → ∀ μ : ℂ, ∃ K0 : ℝ, 0 < K0 ∧ ∀ ν c : ℝ, 0 < ν → 0 < c →
    ∀ G b : CProf, InHr c r G → InHr c r b → FullFlatEq ν μ G b → ∀ a : ℝ, 0 < a →
    ∀ i : Fin 2, ∃ T P Q : Coord → ℂ,
      HasWeakFOOn (winOpen a) vS dZero (fun x => b x i) T ∧
      HasWeakFOOn (winOpen a) vQ0 dZero (fun x => b x i) P ∧
      HasWeakFOOn (winOpen a) vEta dZero (fun x => b x i) Q ∧
      (QPeriodicS c T ∧ AEStronglyMeasurable T volume) ∧
      (QPeriodicS c P ∧ AEStronglyMeasurable P volume) ∧
      (QPeriodicS c Q ∧ AEStronglyMeasurable Q volume) ∧
      eLpNorm T (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a)) ≤
        ENNReal.ofReal K0 * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) ∧
      ENNReal.ofReal (Real.sqrt ν) *
          eLpNorm (fun x => (Real.sqrt x.1 : ℂ) * P x) (ENNReal.ofReal r)
            ((hMeas c r).restrict (winOpen a)) ≤
        ENNReal.ofReal K0 * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) ∧
      ENNReal.ofReal (Real.sqrt ν) *
          eLpNorm (fun x => (Real.sqrt x.1 : ℂ) * Q x) (ENNReal.ofReal r)
            ((hMeas c r).restrict (winOpen a)) ≤
        ENNReal.ofReal K0 * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b)

/-- Norm of a vector of `EuclideanSpace ℂ (Fin 2)` by its components. -/
theorem wbd_norm_le (v : EuclideanSpace ℂ (Fin 2)) : ‖v‖ ≤ ‖v 0‖ + ‖v 1‖ := by
  have h := EuclideanSpace.norm_eq v
  rw [h, Fin.sum_univ_two]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [norm_nonneg (v 0), norm_nonneg (v 1)]


/-- The meridional vector with components `F 0, F 1`. -/
def wbdVec (F : Fin 2 → Coord → ℂ) : CProf := fun x => WithLp.toLp 2 (fun i => F i x)

theorem wbdVec_apply (F : Fin 2 → Coord → ℂ) (x : Coord) (i : Fin 2) : wbdVec F x i = F i x := rfl

theorem wbdVec_per {c : ℝ} {F : Fin 2 → Coord → ℂ} (h : ∀ i, QPeriodicS c (F i)) :
    QPeriodic c (wbdVec F) := by
  have h0 := h 0
  have h1 := h 1
  unfold QPeriodicS at h0 h1
  refine QPerHalf.of_ae ?_
  filter_upwards [h0, h1] with x hx0 hx1
  ext i
  fin_cases i
  · exact hx0
  · exact hx1

theorem wbdVec_aesm {F : Fin 2 → Coord → ℂ} (h : ∀ i, AEStronglyMeasurable (F i) volume) :
    AEStronglyMeasurable (wbdVec F) volume := by
  have : wbdVec F = fun x => (EuclideanSpace.equiv (Fin 2) ℂ).symm (fun i => F i x) := rfl
  rw [this]
  exact ((EuclideanSpace.equiv (Fin 2) ℂ).symm.continuous.measurable.comp_aemeasurable
    (aemeasurable_pi_iff.mpr fun i => (h i).aemeasurable)).aestronglyMeasurable

theorem wbdVec_eLpNorm_le {μ : Measure Coord} {p : ℝ≥0∞} (hp : 1 ≤ p) {F : Fin 2 → Coord → ℂ}
    (h : ∀ i, AEStronglyMeasurable (F i) μ) :
    eLpNorm (wbdVec F) p μ ≤ eLpNorm (F 0) p μ + eLpNorm (F 1) p μ := by
  have h1 : eLpNorm (wbdVec F) p μ ≤ eLpNorm (fun x => ‖F 0 x‖ + ‖F 1 x‖) p μ := by
    apply eLpNorm_mono_ae_real
    filter_upwards with x
    have := wbd_norm_le (wbdVec F x)
    simpa [wbdVec_apply] using this
  refine h1.trans ?_
  calc eLpNorm (fun x => ‖F 0 x‖ + ‖F 1 x‖) p μ
      = eLpNorm ((fun x => ‖F 0 x‖) + fun x => ‖F 1 x‖) p μ := rfl
    _ ≤ eLpNorm (fun x => ‖F 0 x‖) p μ + eLpNorm (fun x => ‖F 1 x‖) p μ :=
        eLpNorm_add_le (h 0).norm (h 1).norm hp
    _ = _ := by rw [eLpNorm_norm, eLpNorm_norm]

theorem windowBound_of_scalar (hS : WbdScalar) : WindowBound := by
  classical
  intro r h1 h3 μ
  obtain ⟨K0, hK0, hK⟩ := hS r h1 h3 μ
  refine ⟨2 * K0, by positivity, ?_⟩
  intro ν c hν hc G b hG hb hF
  have H : ∀ (a : ℝ) (i : Fin 2), ∃ T P Q : Coord → ℂ, 0 < a →
      (HasWeakFOOn (winOpen a) vS dZero (fun x => b x i) T ∧
      HasWeakFOOn (winOpen a) vQ0 dZero (fun x => b x i) P ∧
      HasWeakFOOn (winOpen a) vEta dZero (fun x => b x i) Q ∧
      (QPeriodicS c T ∧ AEStronglyMeasurable T volume) ∧
      (QPeriodicS c P ∧ AEStronglyMeasurable P volume) ∧
      (QPeriodicS c Q ∧ AEStronglyMeasurable Q volume) ∧
      eLpNorm T (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a)) ≤
        ENNReal.ofReal K0 * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) ∧
      ENNReal.ofReal (Real.sqrt ν) *
          eLpNorm (fun x => (Real.sqrt x.1 : ℂ) * P x) (ENNReal.ofReal r)
            ((hMeas c r).restrict (winOpen a)) ≤
        ENNReal.ofReal K0 * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) ∧
      ENNReal.ofReal (Real.sqrt ν) *
          eLpNorm (fun x => (Real.sqrt x.1 : ℂ) * Q x) (ENNReal.ofReal r)
            ((hMeas c r).restrict (winOpen a)) ≤
        ENNReal.ofReal K0 * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b)) := by
    intro a i
    by_cases ha : 0 < a
    · obtain ⟨T, P, Q, hh⟩ := hK ν c hν hc G b hG hb hF a ha i
      exact ⟨T, P, Q, fun _ => hh⟩
    · exact ⟨0, 0, 0, fun h => absurd h ha⟩
  choose T P Q hTPQ using H
  refine ⟨fun a => wbdVec (fun i => T a i), fun a => wbdVec (fun i => P a i),
    fun a => wbdVec (fun i => Q a i), fun a ha => ?_⟩
  have hh : ∀ i, _ := fun i => hTPQ a i ha
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1.le
  set RHS := hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b with hRHS
  have hmeas : ∀ (F : Fin 2 → Coord → ℂ), (∀ i, AEStronglyMeasurable (F i) volume) →
      ∀ i, AEStronglyMeasurable (F i) ((hMeas c r).restrict (winOpen a)) := fun F hF i =>
    (hF i).mono_ac ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans
      (ageμ_ac_volume c (r / 2 - 5 / 2)))
  have two : ENNReal.ofReal (2 * K0) = ENNReal.ofReal K0 + ENNReal.ofReal K0 := by
    rw [two_mul, ENNReal.ofReal_add hK0.le hK0.le]
  have key : ∀ (F : Fin 2 → Coord → ℂ) (w : ℝ≥0∞), (∀ i, AEStronglyMeasurable (F i) volume) →
      (∀ i, w * eLpNorm (F i) (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a)) ≤
        ENNReal.ofReal K0 * RHS) →
      w * eLpNorm (wbdVec F) (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a)) ≤
        ENNReal.ofReal (2 * K0) * RHS := by
    intro F w hF hb
    calc w * eLpNorm (wbdVec F) (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a))
        ≤ w * (eLpNorm (F 0) (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a)) +
            eLpNorm (F 1) (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a))) :=
          by gcongr; exact wbdVec_eLpNorm_le hp1 (hmeas F hF)
      _ = w * eLpNorm (F 0) (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a)) +
            w * eLpNorm (F 1) (ENNReal.ofReal r) ((hMeas c r).restrict (winOpen a)) := mul_add _ _ _
      _ ≤ ENNReal.ofReal K0 * RHS + ENNReal.ofReal K0 * RHS := add_le_add (hb 0) (hb 1)
      _ = ENNReal.ofReal (2 * K0) * RHS := by rw [two, add_mul]
  have hsq : ∀ (F : Fin 2 → Coord → ℂ), sqrtS (wbdVec F) =
      wbdVec (fun i x => (Real.sqrt x.1 : ℂ) * F i x) := by
    intro F; funext x; ext j; simp [sqrtS, wbdVec]
  have hsqm : ∀ (F : Fin 2 → Coord → ℂ), (∀ i, AEStronglyMeasurable (F i) volume) →
      ∀ i, AEStronglyMeasurable (fun x : Coord => (Real.sqrt x.1 : ℂ) * F i x) volume := by
    intro F hF i
    exact (Complex.measurable_ofReal.comp ((Real.continuous_sqrt.measurable.comp measurable_fst))
      ).aestronglyMeasurable.mul (hF i)
  refine ⟨fun i => (hh i).1, fun i => (hh i).2.1, fun i => (hh i).2.2.1,
    ⟨wbdVec_per (fun i => (hh i).2.2.2.1.1), wbdVec_aesm (fun i => (hh i).2.2.2.1.2)⟩,
    ⟨wbdVec_per (fun i => (hh i).2.2.2.2.1.1), wbdVec_aesm (fun i => (hh i).2.2.2.2.1.2)⟩,
    ⟨wbdVec_per (fun i => (hh i).2.2.2.2.2.1.1), wbdVec_aesm (fun i => (hh i).2.2.2.2.2.1.2)⟩,
    ?_, ?_, ?_⟩
  · have := key (fun i => T a i) 1 (fun i => (hh i).2.2.2.1.2) (fun i => by
      simpa using (hh i).2.2.2.2.2.2.1)
    simpa [hNormOn] using this
  · have := key (fun i x => (Real.sqrt x.1 : ℂ) * P a i x) (ENNReal.ofReal (Real.sqrt ν))
      (hsqm _ (fun i => (hh i).2.2.2.2.1.2)) (fun i => (hh i).2.2.2.2.2.2.2.1)
    rw [hNormOn, hsq]; exact this
  · have := key (fun i x => (Real.sqrt x.1 : ℂ) * Q a i x) (ENNReal.ofReal (Real.sqrt ν))
      (hsqm _ (fun i => (hh i).2.2.2.2.2.1.2)) (fun i => (hh i).2.2.2.2.2.2.2.2)
    rw [hNormOn, hsq]; exact this


/-! ## The three ingredients of `WbdScalar` (SP 1928-1933) -/

/-- **Window data** (SP 1928-1931): `u = χ_a b_i` and `f = χ_a (G_i - μ b_i)/s + χ_a' b_i` are
`q`-periodic and measurable, and (weight comparison with `|χ| ≤ 1`, `|χ/s| ≤ 2/a` on `s ≥ a/2`,
`|χ'| ≤ M/a ≤ (2/a)(M/2)`, both vanishing outside `[a/2, 4a]`) have unweighted cylinder norms
bounded by the weighted window norms: with `e = (r/2-5/2)/r`,
`a^e ‖u‖_{cyl} ≤ 16 ‖b‖_{[a/2,4a]}`, `a^e ‖f‖_{cyl} ≤ (32/a)(‖G‖ + (|μ| + M/2)‖b‖)_{[a/2,4a]}`
(all finite). Representatives by `exists_periodic_rep`
(`Tasks/FlatCausal/DuhamelMeasurable/Periodic.lean`). -/
def WbdData : Prop :=
  ∀ M : ℝ, 0 ≤ M → WinCutBd M → WindowWeightCompare → ∀ (c r : ℝ), 0 < c → 1 < r → r < 3 →
    ∀ (μ : ℂ) (G b : CProf), InHr c r G → InHr c r b → ∀ a : ℝ, 0 < a → ∀ i : Fin 2,
      QPeriodicS c (fun x => windowProfile a b x i) ∧
      QPeriodicS c (fun x => windowSource a μ G b x i) ∧
      AEStronglyMeasurable (fun x => windowProfile a b x i) volume ∧
      AEStronglyMeasurable (fun x => windowSource a μ G b x i) volume ∧
      eLpNorm (fun x => windowProfile a b x i) (ENNReal.ofReal r) (cylMeas c) < ⊤ ∧
      eLpNorm (fun x => windowSource a μ G b x i) (ENNReal.ofReal r) (cylMeas c) < ⊤ ∧
      ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
          eLpNorm (fun x => windowProfile a b x i) (ENNReal.ofReal r) (cylMeas c) ≤
        16 * hNormOn c r (winSet2 a) b ∧
      ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
          eLpNorm (fun x => windowSource a μ G b x i) (ENNReal.ofReal r) (cylMeas c) ≤
        ENNReal.ofReal (32 / a) * (hNormOn c r (winSet2 a) G +
          ENNReal.ofReal (‖μ‖ + M / 2) * hNormOn c r (winSet2 a) b)

/-- **Local weak identities** (SP 1928-1933; the weak derivatives of `u = χ_a b_i` on the cylinder
are weak derivatives of `b_i` on the window): where `χ_a = 1` (`s ∈ [a, 2a]`), `u = b_i`; for a
test `φ` with `tsupport φ ⊆ winOpen a`, `y ↦ y.1 * φ y` is an `IsSTTestCoord`, `coordTranspose vS dZero φ
= -cpd 0 (y.1 * φ y)` (so `S b_i = s ∂_s u` is `x.1 * Dt`), `coordTranspose vQ0 dZero φ = -cpd 1 φ`,
`coordTranspose vEta dZero φ = -cpd 2 φ`. Integrability: `b_i` against compactly supported bounded
tests (from `b ∈ H_r`, weight bounded above and below on compacts of `s > 0`) and `Dt, D1`
against tests (`q`-periodic `L^r(cylMeas)` functions are locally integrable). -/
def WbdTransfer : Prop :=
  ∀ M : ℝ, WinCutBd M → ∀ (c r : ℝ), 0 < c → 1 < r → ∀ (μ : ℂ) (G b : CProf),
    InHr c r G → InHr c r b → ∀ a : ℝ, 0 < a → ∀ i : Fin 2,
    ∀ (Dt : Coord → ℂ) (D1 : Fin 2 → Coord → ℂ),
      (QPeriodicS c Dt ∧ AEStronglyMeasurable Dt volume ∧
        eLpNorm Dt (ENNReal.ofReal r) (cylMeas c) < ⊤) →
      (∀ j, QPeriodicS c (D1 j) ∧ AEStronglyMeasurable (D1 j) volume ∧
        eLpNorm (D1 j) (ENNReal.ofReal r) (cylMeas c) < ⊤) →
      (∀ φ, IsSTTestCoord φ → ∫ x, windowProfile a b x i * (cpd 0 φ x : ℂ) =
        -∫ x, Dt x * (φ x : ℂ)) →
      (∀ (j : Fin 2) (φ : Coord → ℝ), IsSTTestCoord φ →
        ∫ x, windowProfile a b x i * (cpd j.succ φ x : ℂ) = -∫ x, D1 j x * (φ x : ℂ)) →
      HasWeakFOOn (winOpen a) vS dZero (fun x => b x i) (fun x => (x.1 : ℂ) * Dt x) ∧
      HasWeakFOOn (winOpen a) vQ0 dZero (fun x => b x i) (D1 0) ∧
      HasWeakFOOn (winOpen a) vEta dZero (fun x => b x i) (D1 1)

/-- **Window norms** (SP 1930-1933, "multiplication by `s` cancels" `a^{-1}`; interpolation with
`λ = √(νa)`): the arithmetic of the bounds, for scalar functions on the window `(a, 2a)`, where
`s ≤ 2a`. Given `a^e‖u‖ ≤ 16 N_b`, `a^e‖f‖ ≤ (32/a)(N_G + (|μ| + M/2) N_b)` (cylinder norms),
`‖Dt‖ ≤ C‖f‖`, `‖ν D2‖ ≤ C‖f‖`, `‖D1 j‖ ≤ Ci (λ⁻¹‖u‖ + λ Σ‖D2‖)`, and the first weight comparison
(`WindowWeightCompare` on `A = winOpen a ⊆ winSet2 a`, applied to the scalar function viewed
as a profile with second component `0`), the weighted window norms of `s Dt` and
`√ν √s D1 j` are `≤ K0 (N_G + N_b)` with `K0` depending only on `M, |μ|, C, Ci`. -/
def WbdNorms : Prop :=
  ∀ (r M : ℝ), 1 < r → r < 3 → 0 ≤ M → ∀ (μ : ℂ) (C Ci : ℝ), 0 < C → 0 < Ci →
    ∃ K0 : ℝ, 0 < K0 ∧ ∀ (ν c a : ℝ), 0 < ν → 0 < c → 0 < a → ∀ (G b : CProf)
      (u f Dt : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ) (D1 : Fin 2 → Coord → ℂ),
      AEStronglyMeasurable Dt volume → (∀ j, AEStronglyMeasurable (D1 j) volume) →
      ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
          eLpNorm u (ENNReal.ofReal r) (cylMeas c) ≤ 16 * hNormOn c r (winSet2 a) b →
      ENNReal.ofReal (a ^ ((r / 2 - 5 / 2) / r)) *
          eLpNorm f (ENNReal.ofReal r) (cylMeas c) ≤
        ENNReal.ofReal (32 / a) * (hNormOn c r (winSet2 a) G +
          ENNReal.ofReal (‖μ‖ + M / 2) * hNormOn c r (winSet2 a) b) →
      eLpNorm Dt (ENNReal.ofReal r) (cylMeas c) ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal r) (cylMeas c) →
      (∀ i j, eLpNorm (fun x => (ν : ℂ) * D2 i j x) (ENNReal.ofReal r) (cylMeas c) ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal r) (cylMeas c)) →
      (∀ (j : Fin 2) (lam : ℝ), 0 < lam → eLpNorm (D1 j) (ENNReal.ofReal r) (cylMeas c) ≤
        ENNReal.ofReal Ci * (ENNReal.ofReal lam⁻¹ * eLpNorm u (ENNReal.ofReal r) (cylMeas c) +
          ENNReal.ofReal lam *
            ∑ k : Fin 2, ∑ l : Fin 2, eLpNorm (D2 k l) (ENNReal.ofReal r) (cylMeas c))) →
      WindowWeightCompare →
      eLpNorm (fun x => (x.1 : ℂ) * Dt x) (ENNReal.ofReal r)
          ((hMeas c r).restrict (winOpen a)) ≤
        ENNReal.ofReal K0 * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b) ∧
      ∀ j : Fin 2, ENNReal.ofReal (Real.sqrt ν) *
          eLpNorm (fun x => (Real.sqrt x.1 : ℂ) * D1 j x) (ENNReal.ofReal r)
            ((hMeas c r).restrict (winOpen a)) ≤
        ENNReal.ofReal K0 * (hNormOn c r (winSet2 a) G + hNormOn c r (winSet2 a) b)

end UnforcedLeray.Short.IIb
