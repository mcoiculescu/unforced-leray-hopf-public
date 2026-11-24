import UnforcedLeray.Short.PartI.Sub.T02_3

/-!
# Part I, task `PartI:ClassicalOdd/EtaCutoffFacts`: facts about the transverse cutoff

Source of record: `the November 2 reference manuscript`, lines 276-288 (the
transverse cutoffs in the velocity and vorticity energy identities).

The cutoff is `etaCutoff R η = ζ(2 - |η|/R)^2` with `ζ = Real.smoothTransition` (`Sub/T05.lean`).
`EtaCutoffFacts` (`Sub/T02_3.lean`) asks for one constant `C₀ ≥ 0`, independent of `R ≥ 1`, with
smoothness, values in `[0,1]`, the plateau `|η| ≤ R`, the support `|η| ≥ 2R ↦ 0`, and the bound
`|∂_η φ_R| ≤ (C₀/R) √φ_R`.

Strategy: `ψ_R(y) = ζ(2 - y/R)^2` is smooth on all of `ℝ`.  The cutoff `etaCutoff R` agrees with
`ψ_R` on `y > 0`, with `ψ_R ∘ neg` on `y < 0`, and is constant on the plateau, which covers `0`.
The derivative of `ζ` is bounded because it is continuous and vanishes outside `[0,1]`.

Helpers are prefixed `ec`.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

/-- `ψ_R(y) = ζ(2 - y/R)^2` is `C^∞` on `ℝ`. -/
theorem ecPsi_contDiff (R : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ => Real.smoothTransition (2 - y / R) ^ 2) := by
  have h1 : ContDiff ℝ ∞ (fun y : ℝ => 2 - y / R) := by fun_prop
  exact ((Real.smoothTransition.contDiff).comp h1).pow 2

/-- The derivative of `ψ_R` at every point `z`. -/
theorem ecPsi_hasDerivAt (R z : ℝ) :
    HasDerivAt (fun y : ℝ => Real.smoothTransition (2 - y / R) ^ 2)
      (((2 : ℕ) : ℝ) * Real.smoothTransition (2 - z / R) ^ (2 - 1) *
        (deriv Real.smoothTransition (2 - z / R) * -(1 / R))) z := by
  have hu : HasDerivAt (fun y : ℝ => 2 - y / R) (-(1 / R)) z :=
    ((hasDerivAt_id' z).div_const R).const_sub 2
  have hd : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
  have hz : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (2 - z / R))
      (2 - z / R) :=
    (hd _).hasDerivAt
  exact (hz.comp (x := z) hu).pow 2

/-- Algebraic bound: `|2 a (b (-t))| ≤ 2 L t a` when `a, t ≥ 0` and `|b| ≤ L`. -/
theorem ecAbsAux (a b t L : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) (hb : |b| ≤ L) :
    |2 * a * (b * -t)| ≤ 2 * L * t * a := by
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  have h1 : 0 ≤ a * t := mul_nonneg ha ht
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg h1 (show (0 : ℝ) ≤ L - b by linarith)]
  · nlinarith [mul_nonneg h1 (show (0 : ℝ) ≤ b + L by linarith)]

/-- The derivative of `ζ = Real.smoothTransition` is bounded: it is continuous, and it vanishes
outside `[0,1]`, where `ζ` is locally constant. -/
theorem ecDerivBdd : ∃ L : ℝ, 0 ≤ L ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ L := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv (by norm_num)
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · rw [← Real.norm_eq_abs]
    exact (hC x hx).trans (le_max_left _ _)
  · have hout : x < 0 ∨ 1 < x := by
      by_contra h
      simp only [not_or, not_lt] at h
      exact hx ⟨h.1, h.2⟩
    have hz : deriv Real.smoothTransition x = 0 := by
      rcases hout with h | h
      · have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
          filter_upwards [Iio_mem_nhds h] with y hy
          have hy' : y < 0 := hy
          exact Real.smoothTransition.zero_of_nonpos hy'.le
        rw [hev.deriv_eq, deriv_const]
      · have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
          filter_upwards [Ioi_mem_nhds h] with y hy
          have hy' : 1 < y := hy
          exact Real.smoothTransition.one_of_one_le hy'.le
        rw [hev.deriv_eq, deriv_const]
    rw [hz, abs_zero]
    exact le_max_right _ _

/-- The cutoff equals `1` on the plateau `|η| ≤ R`. -/
theorem ecOne (R : ℝ) (hR : 0 < R) (η : ℝ) (h : |η| ≤ R) : etaCutoff R η = 1 := by
  have h1 : |η| / R ≤ 1 := (div_le_one₀ hR).2 h
  have h2 : (1 : ℝ) ≤ 2 - |η| / R := by linarith
  unfold etaCutoff
  rw [Real.smoothTransition.one_of_one_le h2, one_pow]

/-- The cutoff is locally constant on the open plateau `|η| < R`, so its derivative vanishes there. -/
theorem ecFlat (R : ℝ) (hR : 0 < R) (η : ℝ) (h : |η| < R) :
    deriv (etaCutoff R) η = 0 := by
  have hopen : IsOpen {b : ℝ | |b| < R} := isOpen_lt continuous_abs continuous_const
  have hev : etaCutoff R =ᶠ[𝓝 η] fun _ => (1 : ℝ) := by
    filter_upwards [hopen.mem_nhds (show η ∈ {b : ℝ | |b| < R} from h)] with y hy
    exact ecOne R hR y (le_of_lt (show |y| < R from hy))
  rw [hev.deriv_eq, deriv_const]

/-- `etaCutoff R` is `C^∞` on `ℝ`. -/
theorem ecContDiff (R : ℝ) (hR : 0 < R) : ContDiff ℝ ∞ (etaCutoff R) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : |x| < R
  · have hopen : IsOpen {b : ℝ | |b| < R} := isOpen_lt continuous_abs continuous_const
    have hev : etaCutoff R =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [hopen.mem_nhds (show x ∈ {b : ℝ | |b| < R} from hx)] with y hy
      exact ecOne R hR y (le_of_lt (show |y| < R from hy))
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (by rw [abs_zero]; exact hR)
    rcases hx0.lt_or_gt with hneg | hpos
    · have hev : etaCutoff R =ᶠ[𝓝 x] fun y : ℝ => Real.smoothTransition (2 - -y / R) ^ 2 := by
        filter_upwards [Iio_mem_nhds hneg] with y hy
        have hy' : y < 0 := hy
        simp only [etaCutoff, abs_of_neg hy']
      exact ((ecPsi_contDiff R).comp contDiff_neg).contDiffAt.congr_of_eventuallyEq hev
    · have hev : etaCutoff R =ᶠ[𝓝 x] fun y : ℝ => Real.smoothTransition (2 - y / R) ^ 2 := by
        filter_upwards [Ioi_mem_nhds hpos] with y hy
        have hy' : 0 < y := hy
        simp only [etaCutoff, abs_of_pos hy']
      exact (ecPsi_contDiff R).contDiffAt.congr_of_eventuallyEq hev

/-- Uniform bound on the derivative of `ψ_R`: `|ψ_R'(z)| ≤ (2L/R) ζ(2 - z/R)`. -/
theorem ecDBound (R : ℝ) (hR : 0 < R) (L : ℝ)
    (hL : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ L) (z : ℝ) :
    |((2 : ℕ) : ℝ) * Real.smoothTransition (2 - z / R) ^ (2 - 1) *
        (deriv Real.smoothTransition (2 - z / R) * -(1 / R))| ≤
      2 * L * (1 / R) * Real.smoothTransition (2 - z / R) := by
  have e : ((2 : ℕ) : ℝ) * Real.smoothTransition (2 - z / R) ^ (2 - 1) *
        (deriv Real.smoothTransition (2 - z / R) * -(1 / R)) =
      2 * Real.smoothTransition (2 - z / R) *
        (deriv Real.smoothTransition (2 - z / R) * -(1 / R)) := by
    norm_num
  rw [e]
  exact ecAbsAux _ _ _ _ (Real.smoothTransition.nonneg _) (one_div_pos.2 hR).le (hL _)

/-- Pointwise derivative bound for the cutoff: `|φ_R'(η)| ≤ (2L/R) √φ_R(η)`. -/
theorem ecBound (R : ℝ) (hR : 0 < R) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ L) (η : ℝ) :
    |deriv (etaCutoff R) η| ≤ 2 * L / R * Real.sqrt (etaCutoff R η) := by
  by_cases hflat : |η| < R
  · rw [ecFlat R hR η hflat, abs_zero]
    exact mul_nonneg (div_nonneg (mul_nonneg two_pos.le hL0) hR.le) (Real.sqrt_nonneg _)
  · have hη0 : η ≠ 0 := by
      rintro rfl
      exact hflat (by rw [abs_zero]; exact hR)
    have hsqrt : Real.sqrt (etaCutoff R η) = Real.smoothTransition (2 - |η| / R) := by
      unfold etaCutoff
      exact Real.sqrt_sq (Real.smoothTransition.nonneg _)
    have hcoef : 2 * L / R * Real.smoothTransition (2 - |η| / R) =
        2 * L * (1 / R) * Real.smoothTransition (2 - |η| / R) := by
      ring
    rw [hsqrt, hcoef]
    rcases hη0.lt_or_gt with hneg | hpos
    · rw [abs_of_neg hneg]
      have hneg' : HasDerivAt (fun y : ℝ => -y) (-1) η := (hasDerivAt_id' η).neg
      have hc := (ecPsi_hasDerivAt R (-η)).comp (x := η) hneg'
      have hev : etaCutoff R =ᶠ[𝓝 η] fun y : ℝ => Real.smoothTransition (2 - -y / R) ^ 2 := by
        filter_upwards [Iio_mem_nhds hneg] with y hy
        have hy' : y < 0 := hy
        simp only [etaCutoff, abs_of_neg hy']
      rw [(hc.congr_of_eventuallyEq hev).deriv, abs_mul, abs_neg, abs_one, mul_one]
      exact ecDBound R hR L hL (-η)
    · rw [abs_of_pos hpos]
      have hev : etaCutoff R =ᶠ[𝓝 η] fun y : ℝ => Real.smoothTransition (2 - y / R) ^ 2 := by
        filter_upwards [Ioi_mem_nhds hpos] with y hy
        have hy' : 0 < y := hy
        simp only [etaCutoff, abs_of_pos hy']
      rw [((ecPsi_hasDerivAt R η).congr_of_eventuallyEq hev).deriv]
      exact ecDBound R hR L hL η

/-- **Facts about the transverse cutoff** (`EtaCutoffFacts`; source lines 276-288). -/
theorem etaCutoffFacts : EtaCutoffFacts := by
  obtain ⟨L, hL0, hL⟩ := ecDerivBdd
  unfold EtaCutoffFacts
  refine ⟨2 * L, by linarith, fun R hR1 => ?_⟩
  have hR : 0 < R := by linarith
  refine ⟨ecContDiff R hR, fun η => ⟨?_, ?_⟩, fun η hη => ecOne R hR η hη, fun η hη => ?_,
    fun η => ecBound R hR L hL0 hL η⟩
  · unfold etaCutoff
    exact sq_nonneg _
  · unfold etaCutoff
    have h0 := Real.smoothTransition.nonneg (2 - |η| / R)
    have h1 := Real.smoothTransition.le_one (2 - |η| / R)
    nlinarith
  · have h2 : 2 ≤ |η| / R := (le_div_iff₀ hR).2 (by linarith)
    have h3 : 2 - |η| / R ≤ 0 := by linarith
    unfold etaCutoff
    rw [Real.smoothTransition.zero_of_nonpos h3]
    norm_num

end UnforcedLeray.Short.PartI
