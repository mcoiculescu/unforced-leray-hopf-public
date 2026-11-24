import UnforcedLeray.Short.PartIIIa.Clock.Moving

/-!
# Part III-a full clock: the weak smoothing chain (C6), statements and clock identities
(SP 3030-3084, `prop:short-full-clock`, weak-source estimate).

* `periodicWeight`: the periodic weight `p_d = [1+y₂²+(d/π)² sin²(π y₁/d)]^m` (SP 3036-3037).
* `deltaZ`, `betaMin`: `Δz = z_s - z_t` and `β_min = ν a_t` (SP 3077-3079).
* `deltaZ_eq`, `betaMin_mul_deltaZ`: the clock identities `Δz = (s-t)/(a_s a_t)`,
  `β_min Δz = ν(s-t)/a_s` (SP 3077-3081), proved.
* `MovingWeakStrong`: the moving weak-to-strong bound `C (β_min Δz)^{-1/2}` (SP 3074-3076).
* `WeakSmoothingPhys`: the physical weak-to-strong cost `C_b ν^{-(m+2)/2} (s-t)^{-1/2}` (SP 3083-3084).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- The periodic weight `p_d(y) = [1 + y₂² + (d/π)² sin²(π y₁/d)]^m` (SP 3036-3037). -/
def periodicWeight (m d : ℝ) (y : ℝ × ℝ) : ℝ :=
  (1 + y.2 ^ 2 + (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2) ^ m

/-- `Δz = z_s - z_t`, `z = s/a(s)` (SP 3077). -/
def deltaZ (ν t s : ℝ) : ℝ := movingZ ν s - movingZ ν t

/-- `β_min = ν a_t`: the minimum of `β = θ⁻¹ = ν a` on `[t, s]` (SP 3079). -/
def betaMin (ν t : ℝ) : ℝ := ν * clockA ν t

/-- `Δz = (s-t)/(a_s a_t)` (SP 3077). -/
theorem deltaZ_eq (ν t s : ℝ) (ht : clockA ν t ≠ 0) (hs : clockA ν s ≠ 0) :
    deltaZ ν t s = (s - t) / (clockA ν s * clockA ν t) := by
  unfold deltaZ movingZ
  rw [div_sub_div _ _ hs ht]
  unfold clockA
  ring

/-- `β_min Δz = ν (s-t)/a_s` (SP 3080). -/
theorem betaMin_mul_deltaZ (ν t s : ℝ) (ht : clockA ν t ≠ 0) (hs : clockA ν s ≠ 0) :
    betaMin ν t * deltaZ ν t s = ν * (s - t) / clockA ν s := by
  rw [deltaZ_eq ν t s ht hs, betaMin]
  field_simp

/-- **Moving weak-to-strong bound** (SP 3074-3076): on `0 < s-t ≤ 1`, `θ(s) ≥ b`, the weak linearised
flow from a zero-circulation datum satisfies
`‖J_{a_s}⁻¹ w(s)‖_{X_{m,d_s}} ≤ C (β_min Δz)^{-1/2} ‖J_{a_t}⁻¹ f‖_{(H^1_{-m,d_t})^*}`,
`β_min Δz = ν (s-t)/a_s`.  For the trains of the BUC class `PartI.IsBUCTrain` (SP 270-288; the
rescaled-train bounds SP 3050-3051 hold for the source train only, `Short/PartI/TrainClass.lean`). -/
def MovingWeakStrong (m : ℝ) : Prop :=
  ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → ∃ (C ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t s : ℝ, 0 ≤ t → t < s → s - t ≤ 1 → b ≤ clockTheta ν s →
        ∀ f : ℝ × ℝ → ℂ, MemLp f 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) →
          HasZeroCirculation (ν ^ (-2 : ℝ)) f →
          ∀ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u →
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m (JscaleInv (clockA ν s) (w s)) ≤
              ENNReal.ofReal (C * (ν * (s - t) / clockA ν s) ^ (-1 / 2 : ℝ)) *
                negNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t)) m
                  (JscaleInv (clockA ν t) f)

/-- **Physical weak smoothing** (SP 3083-3084): `‖w(s)‖_{X_{m,c}} ≤ C_b ν^{-(m+2)/2}
(s-t)^{-1/2} ‖f‖_{Z^{-1}_{m,c}}` on `0 < s-t ≤ 1`, `θ(s) ≥ b`, for BUC trains
(`PartI.IsBUCTrain`, SP 270-288). -/
def WeakSmoothingPhys (m : ℝ) : Prop :=
  ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → ∃ (C ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t s : ℝ, 0 ≤ t → t < s → s - t ≤ 1 → b ≤ clockTheta ν s →
        ∀ f : ℝ × ℝ → ℂ, MemLp f 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) →
          HasZeroCirculation (ν ^ (-2 : ℝ)) f →
          ∀ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u →
            xNorm (ν ^ (-2 : ℝ)) m (w s) ≤
              ENNReal.ofReal (C * ν ^ (-((m + 2) / 2)) * (s - t) ^ (-1 / 2 : ℝ)) *
                negNorm (ν ^ (-2 : ℝ)) m f

end UnforcedLeray.Short.IIIa
