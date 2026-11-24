import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_2

/-!
# `InletFnNearOfJets`: decomposition (smoothness of `raw` + generic product-rule bound)

Source `the November 2 reference manuscript`
lines 2545-2551, 2563-2569, 1206-1222, 1217-1219.

The product rule for `inletFn = -∂_j(L₀E + (raw·∇)E + (E·∇)raw)` needs `E` and `raw` jointly
smooth (otherwise `fderiv` is junk), so `InletFnNearOfJets` rests on `RawJointSmooth` (the source
fact that `U_raw` is smooth through the axis for positive time, 1214, 1305-1325) and on the generic
pointwise product-rule bound `InletSrcDerivBound` below.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Generic product-rule bound** (2545-2551, 2563-2569): there is a universal constant `K` such
that for `ν ≤ 1` and jointly smooth `E_i`, `raw`, at every `(τ,y)`,
`‖inletFn p i j (τ,y)‖ ≤ K (1+‖y‖)(1+B) A`, where `A` is the sum of the slice jets of `E_i` of order
`≤ 3` and of `∂_τE_i` of order `≤ 1` at `y`, and `B` the sum of the jets of `raw τ` of order `≤ 2`.
(Terms: `∂_j∂_τE`, `∂_jE`, `y·∇∂_jE`, `ν∂_jΔE`, `∂_j raw·∇E`, `raw·∇∂_jE`, `∂_jE·∇raw`,
`E·∇∂_j raw`; the weight `y` comes from `radialT`.) -/
def InletSrcDerivBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (p : Params) (i : Fin 2) (j : Fin 3), p.ν ≤ 1 →
    ContDiff ℝ ∞ (p.Efun i) → ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2) →
    ∀ (τ : ℝ) (y : UnforcedLeray.Space),
      ‖inletFn p i j (τ, y)‖ ≤ K * (1 + ‖y‖) *
        (1 + ∑ k ∈ Finset.range 3, ‖iteratedFDeriv ℝ k (p.raw τ) y‖) *
        ((∑ k ∈ Finset.range 4,
            ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖) +
          ∑ k ∈ Finset.range 2,
            ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space =>
              UnforcedLeray.PhaseSpace.dτ (p.Efun i) (τ, x)) y‖)

theorem inletFnNearOfJets_of (hs : RawJointSmooth) (hK : InletSrcDerivBound) :
    InletFnNearOfJets := by
  intro hE hB lam q hq dm dp hdm
  obtain ⟨ν1, hν1, H1⟩ := hE lam q hq dm dp hdm
  obtain ⟨ν2, hν2, H2⟩ := hB dm dp hdm
  obtain ⟨ν3, hν3, H3⟩ := hs dm dp hdm
  obtain ⟨K, hK0, HK⟩ := hK
  refine ⟨min (min ν1 ν2) (min ν3 1), lt_min (lt_min hν1 hν2) (lt_min hν3 one_pos),
    fun p d hreg hν hm z g hg i j R0 hR0 => ?_⟩
  have h1 : p.ν ≤ ν1 := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : p.ν ≤ ν2 := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : p.ν ≤ ν3 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hR := H3 p d hreg h3
  have hI := inlet_contDiff_joint lam q hq hreg h4 hm i
  have hEs : ContDiff ℝ ∞ (p.Efun i) := contDiff_realC_meas.comp hI
  obtain ⟨CE, hCE⟩ := H1 p d hreg h1 hm z g hg i 3 R0 hR0
  obtain ⟨c0, hc0⟩ := H2 p d hreg h2 0
  obtain ⟨c1, hc1⟩ := H2 p d hreg h2 1
  obtain ⟨c2, hc2⟩ := H2 p d hreg h2 2
  refine ⟨K * (1 + R0) * (1 + (c0 + c1 + c2)) * (6 * CE), fun τ hτ y hy => ?_⟩
  obtain ⟨hA, hA'⟩ := hCE τ hτ y hy
  set t : ℝ := (1 + |y 2|) ^ (-((3 : ℕ) : ℝ)) with ht
  have hpos : 0 < 1 + |y 2| := by positivity
  have htpos : 0 < t := Real.rpow_pos_of_pos hpos _
  have hsumE : ∑ k ∈ Finset.range 4,
      ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖ ≤ 4 * (CE * t) := by
    calc _ ≤ ∑ k ∈ Finset.range 4, CE * t := by
          apply Finset.sum_le_sum
          intro k hk
          exact hA k (by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk)
      _ = 4 * (CE * t) := by simp
  have hsumD : ∑ k ∈ Finset.range 2,
      ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space =>
        UnforcedLeray.PhaseSpace.dτ (p.Efun i) (τ, x)) y‖ ≤ 2 * (CE * t) := by
    calc _ ≤ ∑ k ∈ Finset.range 2, CE * t := by
          apply Finset.sum_le_sum
          intro k hk
          exact hA' k (by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk)
      _ = 2 * (CE * t) := by simp
  have hsumB : ∑ k ∈ Finset.range 3, ‖iteratedFDeriv ℝ k (p.raw τ) y‖ ≤ c0 + c1 + c2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    exact add_le_add (add_le_add (hc0 τ y) (hc1 τ y)) (hc2 τ y)
  have hnorm : ‖y‖ ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + |y 2| := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs]
    have : Real.sqrt (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) ≤
        Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + Real.sqrt (y 2 ^ 2) := by
      rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
      apply Real.sqrt_le_sqrt
      nlinarith [Real.sq_sqrt (add_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1))),
        Real.sq_sqrt (sq_nonneg (y 2)), Real.sqrt_nonneg (y 0 ^ 2 + y 1 ^ 2),
        Real.sqrt_nonneg (y 2 ^ 2)]
    simpa [Real.sqrt_sq_eq_abs] using this
  have hy1 : 1 + ‖y‖ ≤ (1 + R0) * (1 + |y 2|) := by
    nlinarith [abs_nonneg (y 2)]
  have hbound := HK p i j h4 hEs hR τ y
  have hB0 : 0 ≤ 1 + ∑ k ∈ Finset.range 3, ‖iteratedFDeriv ℝ k (p.raw τ) y‖ := by positivity
  have hA0 : 0 ≤ (∑ k ∈ Finset.range 4,
            ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖) +
          ∑ k ∈ Finset.range 2,
            ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space =>
              UnforcedLeray.PhaseSpace.dτ (p.Efun i) (τ, x)) y‖ := by positivity
  have hAle := add_le_add hsumE hsumD
  have hCEt : 0 ≤ CE * t := by
    have : 0 ≤ (∑ k ∈ Finset.range 4,
            ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖) := by positivity
    nlinarith
  have hKy : K * (1 + ‖y‖) ≤ K * ((1 + R0) * (1 + |y 2|)) := mul_le_mul_of_nonneg_left hy1 hK0
  have hBle : 1 + ∑ k ∈ Finset.range 3, ‖iteratedFDeriv ℝ k (p.raw τ) y‖ ≤ 1 + (c0 + c1 + c2) := by
    linarith
  have hstep : K * (1 + ‖y‖) *
        (1 + ∑ k ∈ Finset.range 3, ‖iteratedFDeriv ℝ k (p.raw τ) y‖) *
        ((∑ k ∈ Finset.range 4,
            ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖) +
          ∑ k ∈ Finset.range 2,
            ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space =>
              UnforcedLeray.PhaseSpace.dτ (p.Efun i) (τ, x)) y‖) ≤
      K * ((1 + R0) * (1 + |y 2|)) * (1 + (c0 + c1 + c2)) * (6 * (CE * t)) := by
    have e1 : K * (1 + ‖y‖) * (1 + ∑ k ∈ Finset.range 3, ‖iteratedFDeriv ℝ k (p.raw τ) y‖) ≤
        K * ((1 + R0) * (1 + |y 2|)) * (1 + (c0 + c1 + c2)) :=
      mul_le_mul hKy hBle hB0 (by positivity)
    have hAle' : (∑ k ∈ Finset.range 4,
            ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖) +
          ∑ k ∈ Finset.range 2,
            ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space =>
              UnforcedLeray.PhaseSpace.dτ (p.Efun i) (τ, x)) y‖ ≤ 6 * (CE * t) := by linarith
    have hb0 : 0 ≤ K * ((1 + R0) * (1 + |y 2|)) * (1 + (c0 + c1 + c2)) :=
      mul_nonneg (mul_nonneg hK0 (by positivity)) (hB0.trans hBle)
    exact mul_le_mul e1 hAle' hA0 hb0
  refine hbound.trans (hstep.trans (le_of_eq ?_))
  have hmul : (1 + |y 2|) * t = (1 + |y 2|) ^ (-2 : ℝ) := by
    rw [ht, show (-((3 : ℕ) : ℝ)) = (-2 : ℝ) + (-1 : ℝ) by norm_num,
      Real.rpow_add hpos, Real.rpow_neg_one]
    field_simp
  calc K * ((1 + R0) * (1 + |y 2|)) * (1 + (c0 + c1 + c2)) * (6 * (CE * t))
      = K * (1 + R0) * (1 + (c0 + c1 + c2)) * (6 * CE) * ((1 + |y 2|) * t) := by ring
    _ = _ := by rw [hmul]

end UnforcedLeray.Short.PartIIIb.Concrete
