import UnforcedLeray.Short.PartI.Sub.T02_5

/-!
# Part I, task `PartI:T02/5/GammaTendsto`: `Γ → 0` at `±∞`

Source of record: `the November 2 reference manuscript`, the slice argument whose
statements are listed in `Short/PartI/Sub/T02_5.lean` (header lines 1-44; `GammaTendsto` at
lines 219-223 of that file, the source paragraph cited there is lines 261-288).

Proof. For a slice `w` and `η ∈ ℝ`, Cauchy-Schwarz on `(0, c)` gives `Γ(η)² ≤ c G(η)`, where
`Γ = sliceGamma c w` and `G = sliceEnergy c w`. By `sliceEnergy_tendsto`, `G → 0` at `±∞`, hence
`|Γ| ≤ √(c G) → 0` at `±∞` by squeezing.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- **`GammaTendsto` from the energy profile.** Given `TendstoZeroOfLipschitzIntegrable` and
`SliceEnergyProfile`, the circulation profile `Γ` of every slice tends to `0` at `±∞`. -/
theorem gammaTendsto (hB : TendstoZeroOfLipschitzIntegrable) (hC : SliceEnergyProfile) :
    GammaTendsto := by
  intro c w hs
  -- Cauchy-Schwarz on `(0, d)` for a continuous real function: `(∫ f)² ≤ d ∫ f²`.
  -- Proof: `0 ≤ ∫ (f - I/d)² = J - 2 (I/d) I + d (I/d)²` with `I = ∫ f`, `J = ∫ f²`.
  have cs : ∀ (f : ℝ → ℝ) (d : ℝ), Continuous f → 0 < d →
      (∫ q in (0 : ℝ)..d, f q) ^ 2 ≤ d * ∫ q in (0 : ℝ)..d, f q ^ 2 := by
    intro f d hf hd
    have hd0 : d ≠ 0 := hd.ne'
    have hf2 : IntervalIntegrable (fun q => f q ^ 2) MeasureTheory.volume 0 d :=
      Continuous.intervalIntegrable (by fun_prop) 0 d
    have hfa : ∀ a : ℝ, IntervalIntegrable (fun q => 2 * a * f q) MeasureTheory.volume 0 d :=
      fun a => Continuous.intervalIntegrable (by fun_prop) 0 d
    have hexp : ∀ a : ℝ, ∫ q in (0 : ℝ)..d, (f q - a) ^ 2
        = (∫ q in (0 : ℝ)..d, f q ^ 2) - 2 * a * (∫ q in (0 : ℝ)..d, f q) + d * a ^ 2 := by
      intro a
      have hA : IntervalIntegrable (fun q => f q ^ 2 - 2 * a * f q) MeasureTheory.volume 0 d :=
        Continuous.intervalIntegrable (by fun_prop) 0 d
      have e : (fun q => (f q - a) ^ 2) = fun q => (f q ^ 2 - 2 * a * f q) + a ^ 2 := by
        funext q
        ring
      rw [e, intervalIntegral.integral_add hA (intervalIntegrable_const (c := a ^ 2)),
        intervalIntegral.integral_sub hf2 (hfa a), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hnn : 0 ≤ ∫ q in (0 : ℝ)..d, (f q - (∫ r in (0 : ℝ)..d, f r) / d) ^ 2 :=
      intervalIntegral.integral_nonneg hd.le (fun q _ => sq_nonneg _)
    rw [hexp] at hnn
    have alg : ∀ I J t : ℝ, d * t = I → 0 ≤ J - 2 * t * I + d * t ^ 2 → I ^ 2 ≤ d * J := by
      intro I J t ht h
      have h2 : d * (J - 2 * t * I + d * t ^ 2) = d * J - I ^ 2 := by
        calc d * (J - 2 * t * I + d * t ^ 2) = d * J - 2 * (d * t) * I + (d * t) ^ 2 := by ring
          _ = d * J - I ^ 2 := by rw [ht]; ring
      have h3 : 0 ≤ d * (J - 2 * t * I + d * t ^ 2) := mul_nonneg hd.le h
      linarith
    exact alg _ _ ((∫ r in (0 : ℝ)..d, f r) / d) (by field_simp) hnn
  -- Pointwise bound `Γ(η)² ≤ c G(η)`.
  have hbound : ∀ η : ℝ, (sliceGamma c w η) ^ 2 ≤ c * sliceEnergy c w η := by
    intro η
    have hwc : Continuous w := hs.smooth.continuous
    have hq : Continuous (fun q : ℝ => w (q, η)) := by fun_prop
    have hcoord : Continuous (fun x : Vec => x 0) :=
      PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)
    have hf : Continuous (fun q : ℝ => w (q, η) 0) := hcoord.comp hq
    have hg : Continuous (fun q : ℝ => ‖w (q, η)‖ ^ 2) := hq.norm.pow 2
    have hle : ∀ q : ℝ, (w (q, η) 0) ^ 2 ≤ ‖w (q, η)‖ ^ 2 := by
      intro q
      have h1 : |w (q, η) 0| ≤ ‖w (q, η)‖ := by
        have h := PiLp.norm_apply_le (w (q, η)) 0
        rw [Real.norm_eq_abs] at h
        exact h
      nlinarith [abs_nonneg (w (q, η) 0), norm_nonneg (w (q, η)), sq_abs (w (q, η) 0)]
    have hmono : ∫ q in (0 : ℝ)..c, (w (q, η) 0) ^ 2 ≤ ∫ q in (0 : ℝ)..c, ‖w (q, η)‖ ^ 2 :=
      intervalIntegral.integral_mono_on hs.pos.le ((hf.pow 2).intervalIntegrable 0 c)
        (hg.intervalIntegrable 0 c) (fun q _ => hle q)
    have hcs := cs (fun q => w (q, η) 0) c hf hs.pos
    show (∫ q in (0 : ℝ)..c, w (q, η) 0) ^ 2 ≤ c * ∫ q in (0 : ℝ)..c, ‖w (q, η)‖ ^ 2
    exact hcs.trans (mul_le_mul_of_nonneg_left hmono hs.pos.le)
  -- Energy profile tends to `0` at both ends, so `√(c G)` does too.
  have hG := sliceEnergy_tendsto hB hC hs
  have hsqrt : ∀ l : Filter ℝ, Tendsto (sliceEnergy c w) l (𝓝 0) →
      Tendsto (fun η => Real.sqrt (c * sliceEnergy c w η)) l (𝓝 0) := by
    intro l hl
    have h := (hl.const_mul c).sqrt
    rw [mul_zero, Real.sqrt_zero] at h
    exact h
  have hnorm : ∀ η : ℝ, ‖sliceGamma c w η‖ ≤ Real.sqrt (c * sliceEnergy c w η) := by
    intro η
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (hbound η)
  exact ⟨squeeze_zero_norm hnorm (hsqrt atTop hG.1), squeeze_zero_norm hnorm (hsqrt atBot hG.2)⟩

end UnforcedLeray.Short.PartI
