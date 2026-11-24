import UnforcedLeray.Short.PartI.Sub.T02_5

/-!
# Part I, task `PartI:T02/5/PsiDecay`: `ψ → 0` as `|η| → ∞`, uniformly in `q`

Source of record: `the November 2 reference manuscript`, lines 261-288 (the decay of
the stream), packaged as the leaf `PsiDecay` in `Short/PartI/Sub/T02_5.lean` (lines 144-150).

Proof. Fix a slice `w`, write `G = sliceEnergy c w` and `V(q, η) = slicePrim w q η`, and let
`g → 0` at `±∞`.

1. `V(·, η)` is `c`-periodic: `V(q + c) - V(q) = ∫_q^{q+c} w₂(s, η) ds = ∫_0^c w₂(s, η) ds = 0`
   (periodicity of `w` and `SliceFluxZero`).
2. Every `q` is congruent modulo `c` to some `q' ∈ [0, c)`. Cauchy-Schwarz on `(0, q')`, together
   with `w₂² ≤ ‖w‖²` and `q' ≤ c`, gives `V(q', η)² ≤ c G(η)`. Hence `|V(q, η)| ≤ √(c G(η))` for
   every `q`.
3. The mean `V̄(η) = c⁻¹ ∫_0^c V(q, η) dq` obeys the same bound.

So `|ψ(q, η)| ≤ 2 √(c G(η)) + |g(η)|` uniformly in `q`. By `sliceEnergy_tendsto` and the
hypothesis on `g`, the right-hand side tends to `0` along `|η| → ∞` (through `comap_abs_atTop`),
and squeezing gives the claim.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- **`PsiDecay` from the energy profile and the vanishing flux.** For a slice `w` with zero flux
`∫₀^c w₂ = 0` and energy profile tending to `0`, the candidate stream `V - V̄ + g` tends to `0`
as `|η| → ∞`, uniformly in `q`, for every `g` tending to `0` at both ends. -/
theorem psiDecay (hB : TendstoZeroOfLipschitzIntegrable) (hC : SliceEnergyProfile)
    (hF : SliceFluxZero) : PsiDecay := by
  intro c w hs g hg1 hg2
  -- Cauchy-Schwarz on `(0, d)` for a continuous real function: `(∫ f)² ≤ d ∫ f²`.
  -- Proof: `0 ≤ ∫ (f - I/d)² = J - 2 (I/d) I + d (I/d)²` with `I = ∫ f`, `J = ∫ f²`.
  have cs : ∀ (f : ℝ → ℝ) (d : ℝ), Continuous f → 0 ≤ d →
      (∫ q in (0 : ℝ)..d, f q) ^ 2 ≤ d * ∫ q in (0 : ℝ)..d, f q ^ 2 := by
    intro f d hf hd
    rcases hd.eq_or_lt with h0 | hpos
    · subst h0
      simp
    have hd0 : d ≠ 0 := hpos.ne'
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
      intervalIntegral.integral_nonneg hpos.le (fun q _ => sq_nonneg _)
    rw [hexp] at hnn
    have alg : ∀ I J t : ℝ, d * t = I → 0 ≤ J - 2 * t * I + d * t ^ 2 → I ^ 2 ≤ d * J := by
      intro I J t ht h
      have h2 : d * (J - 2 * t * I + d * t ^ 2) = d * J - I ^ 2 := by
        calc d * (J - 2 * t * I + d * t ^ 2) = d * J - 2 * (d * t) * I + (d * t) ^ 2 := by ring
          _ = d * J - I ^ 2 := by rw [ht]; ring
      have h3 : 0 ≤ d * (J - 2 * t * I + d * t ^ 2) := mul_nonneg hpos.le h
      linarith
    exact alg _ _ ((∫ r in (0 : ℝ)..d, f r) / d) (by field_simp) hnn
  have hwc : Continuous w := hs.smooth.continuous
  have hcont : ∀ η : ℝ, Continuous (fun q : ℝ => w (q, η)) := fun η => by fun_prop
  have hcoord : Continuous (fun x : Vec => x 1) :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2)
  -- Pointwise `w₂² ≤ ‖w‖²`.
  have hle : ∀ z : Plane, (w z 1) ^ 2 ≤ ‖w z‖ ^ 2 := by
    intro z
    have h1 : |w z 1| ≤ ‖w z‖ := by
      have h := PiLp.norm_apply_le (w z) 1
      rw [Real.norm_eq_abs] at h
      exact h
    nlinarith [abs_nonneg (w z 1), norm_nonneg (w z), sq_abs (w z 1)]
  -- The primitive `V(·, η)` is `c`-periodic: its increment over one period is the flux `0`.
  have hper : ∀ η : ℝ, Function.Periodic (fun q => slicePrim w q η) c := by
    intro η q
    have hfp : Function.Periodic (fun s : ℝ => w (s, η) 1) c := by
      intro s
      show w (s + c, η) 1 = w (s, η) 1
      exact congrArg (fun v => v 1) (hs.periodic (s, η))
    have hint : ∫ s in q..q + c, w (s, η) 1 = 0 := by
      have h := hfp.intervalIntegral_add_eq q 0
      simp only [zero_add] at h
      rw [h]
      exact hF c w hs η
    have hc1 : Continuous (fun s : ℝ => w (s, η) 1) := hcoord.comp (hcont η)
    have hi : ∀ a b : ℝ,
        IntervalIntegrable (fun s : ℝ => w (s, η) 1) MeasureTheory.volume a b :=
      fun a b => hc1.intervalIntegrable a b
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hi 0 q) (hi q (q + c))
    show (∫ s in (0 : ℝ)..q + c, w (s, η) 1) = ∫ s in (0 : ℝ)..q, w (s, η) 1
    rw [← hsplit, hint, add_zero]
  -- `V(q, η)² ≤ c G(η)` for every `q`: reduce to `q' ∈ [0, c)` by periodicity, then Cauchy-Schwarz.
  have hVsq : ∀ η q : ℝ, (slicePrim w q η) ^ 2 ≤ c * sliceEnergy c w η := by
    intro η q
    obtain ⟨q', hq', hVq⟩ := (hper η).exists_mem_Ico₀ hs.pos q
    have hVq' : slicePrim w q η = slicePrim w q' η := hVq
    rw [hVq']
    obtain ⟨h0, hc'⟩ := hq'
    have hc1 : Continuous (fun s : ℝ => w (s, η) 1) := hcoord.comp (hcont η)
    have hgn : Continuous (fun s : ℝ => ‖w (s, η)‖ ^ 2) := ((hcont η).norm).pow 2
    have hgi : ∀ a b : ℝ,
        IntervalIntegrable (fun s : ℝ => ‖w (s, η)‖ ^ 2) MeasureTheory.volume a b :=
      fun a b => hgn.intervalIntegrable a b
    have hcs : (∫ s in (0 : ℝ)..q', w (s, η) 1) ^ 2
        ≤ q' * ∫ s in (0 : ℝ)..q', (w (s, η) 1) ^ 2 :=
      cs (fun s => w (s, η) 1) q' hc1 h0
    have hm : ∫ s in (0 : ℝ)..q', (w (s, η) 1) ^ 2 ≤ ∫ s in (0 : ℝ)..q', ‖w (s, η)‖ ^ 2 :=
      intervalIntegral.integral_mono_on h0 ((hc1.pow 2).intervalIntegrable 0 q') (hgi 0 q')
        (fun s _ => hle (s, η))
    have hsplitE := intervalIntegral.integral_add_adjacent_intervals (hgi 0 q') (hgi q' c)
    have hrest : 0 ≤ ∫ s in q'..c, ‖w (s, η)‖ ^ 2 :=
      intervalIntegral.integral_nonneg hc'.le (fun s _ => sq_nonneg _)
    have hJ0 : 0 ≤ ∫ s in (0 : ℝ)..q', (w (s, η) 1) ^ 2 :=
      intervalIntegral.integral_nonneg h0 (fun s _ => sq_nonneg _)
    have h1 : q' * ∫ s in (0 : ℝ)..q', (w (s, η) 1) ^ 2
        ≤ c * ∫ s in (0 : ℝ)..q', (w (s, η) 1) ^ 2 :=
      mul_le_mul_of_nonneg_right hc'.le hJ0
    have h2 : c * ∫ s in (0 : ℝ)..q', (w (s, η) 1) ^ 2
        ≤ c * ∫ s in (0 : ℝ)..c, ‖w (s, η)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (by linarith) hs.pos.le
    show (∫ s in (0 : ℝ)..q', w (s, η) 1) ^ 2 ≤ c * ∫ s in (0 : ℝ)..c, ‖w (s, η)‖ ^ 2
    linarith
  have hVabs : ∀ η q : ℝ, |slicePrim w q η| ≤ Real.sqrt (c * sliceEnergy c w η) :=
    fun η q => Real.abs_le_sqrt (hVsq η q)
  -- The mean `V̄(η) = c⁻¹ ∫₀^c V(q, η) dq` obeys the same bound.
  have hc0 : c ≠ 0 := hs.pos.ne'
  have hMabs : ∀ η : ℝ, |sliceMeanPrim c w η| ≤ Real.sqrt (c * sliceEnergy c w η) := by
    intro η
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := c) (f := fun q => slicePrim w q η)
      (C := Real.sqrt (c * sliceEnergy c w η))
      (fun q _ => by rw [Real.norm_eq_abs]; exact hVabs η q)
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos hs.pos] at hI
    unfold sliceMeanPrim
    rw [abs_mul, abs_of_pos (inv_pos.2 hs.pos)]
    calc c⁻¹ * |∫ q in (0 : ℝ)..c, slicePrim w q η|
        ≤ c⁻¹ * (Real.sqrt (c * sliceEnergy c w η) * c) :=
          mul_le_mul_of_nonneg_left hI (inv_nonneg.2 hs.pos.le)
      _ = Real.sqrt (c * sliceEnergy c w η) := by
          field_simp
  -- Uniform bound: `|ψ(q, η)| ≤ 2 √(c G(η)) + |g(η)|` for all `q`.
  have hpt : ∀ z : Plane, ‖slicePsi c w g z‖
      ≤ 2 * Real.sqrt (c * sliceEnergy c w z.2) + |g z.2| := by
    intro z
    rw [Real.norm_eq_abs]
    unfold slicePsi
    have h1 := hVabs z.2 z.1
    have h2 := hMabs z.2
    have h3 := abs_add_le (slicePrim w z.1 z.2 - sliceMeanPrim c w z.2) (g z.2)
    have h4 : |slicePrim w z.1 z.2 - sliceMeanPrim c w z.2|
        ≤ |slicePrim w z.1 z.2| + |sliceMeanPrim c w z.2| := by
      have h5 := abs_add_le (slicePrim w z.1 z.2) (-sliceMeanPrim c w z.2)
      rw [abs_neg, ← sub_eq_add_neg] at h5
      exact h5
    linarith
  -- The bound tends to `0` along any filter where `G` and `g` tend to `0`.
  have hG := sliceEnergy_tendsto hB hC hs
  have hsq : ∀ l : Filter ℝ, Tendsto (sliceEnergy c w) l (𝓝 0) →
      Tendsto (fun η => Real.sqrt (c * sliceEnergy c w η)) l (𝓝 0) := by
    intro l hl
    have h := (hl.const_mul c).sqrt
    rw [mul_zero, Real.sqrt_zero] at h
    exact h
  have hbound : ∀ l : Filter ℝ, Tendsto (sliceEnergy c w) l (𝓝 0) → Tendsto g l (𝓝 0) →
      Tendsto (fun η => 2 * Real.sqrt (c * sliceEnergy c w η) + |g η|) l (𝓝 0) := by
    intro l hl hgl
    have hab : Tendsto (fun η => |g η|) l (𝓝 0) := by
      have h := hgl.norm
      rw [norm_zero] at h
      simpa only [Real.norm_eq_abs] using h
    have ha := ((hsq l hl).const_mul 2).add hab
    rw [mul_zero, add_zero] at ha
    exact ha
  have hcomap : Tendsto (fun η : ℝ => 2 * Real.sqrt (c * sliceEnergy c w η) + |g η|)
      (comap (fun η : ℝ => |η|) atTop) (𝓝 0) := by
    rw [comap_abs_atTop, tendsto_sup]
    exact ⟨hbound atBot hG.2 hg2, hbound atTop hG.1 hg1⟩
  -- Pull back along `z ↦ z.2`, then squeeze.
  have hsnd : Tendsto (fun z : Plane => z.2) (comap (fun z : Plane => |z.2|) atTop)
      (comap (fun η : ℝ => |η|) atTop) :=
    tendsto_comap_iff.2 tendsto_comap
  exact squeeze_zero_norm hpt (hcomap.comp hsnd)

end UnforcedLeray.Short.PartI

end
