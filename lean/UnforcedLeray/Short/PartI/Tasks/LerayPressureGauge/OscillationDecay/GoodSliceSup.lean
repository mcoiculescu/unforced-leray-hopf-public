import UnforcedLeray.Short.PartI.Sub.T02_2_4
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.OscillationDecay.SliceEnergyIdentity
import UnforcedLeray.Lib.Cylinder.SupBound

/-!
# Part I, task `PartI:T02/2/4/4`: `GoodSliceSup` (good slices)

Source of record: `the November 2 reference manuscript`, line 447.
Statement: `GoodSliceSup` (`Short/PartI/Sub/T02_2_4.lean`, line 284). Dependency: `SliceEnergyIdentity`
(`PartI:T02/2/4/2`, `Short/PartI/Tasks/LerayPressureGauge/OscillationDecay/SliceEnergyIdentity.lean`).

Notation: `m(η) = ∫ w(q,η)² dq`, `P(η) = ∫ (∂_q w)² dq`, `F(η) = ∫ w Δw dq`, all over
`Ioc (-c/2) (c/2)`. The energy identity gives `m'' = m2 = 2Q + 2P + 2F` with `Q ≥ 0`, hence
`m2 ≥ 2P - 2|F|`.

## Route (convexity on a window, no bump function)

* `goodSlice_sup_sq_le` (Sobolev bound on a slice): `w(z)² ≤ 2c⁻¹ m(z₂) + c P(z₂)`, from
  `Cyl.sq_norm_le_cyl` applied to the `ℂ`-valued `w`.
* `goodSlice_convex_gap`: if `m'' ≥ κ` on `[s, s+2]`, then `m(s+1) + κ/2 ≤ (m s + m(s+2))/2`
  (convexity of `m + (κ/2)(η-s)(s+2-η)`, via `convexOn_of_deriv2_nonneg`).
* `goodSlice_exists_small_P` (window lemma): if `|F| ≤ κ/2` on `[s, s+2]`, `m(s), m(s+2) < ν`
  and `2ν ≤ κ`, then `P(a) ≤ κ` for some `a ∈ [s, s+2]`. If not, `m'' ≥ κ` on the window and the
  convexity gap gives `κ ≤ m(s) + m(s+2) < 2ν ≤ κ`.
* `goodSliceSup`: take `κ = 2ν`, `ν = min(εc/4, ε/(4c))`. For `|η|` large, `|F| ≤ ν` (since
  `|w| ≤ M` and `Δw → 0`) and `m < ν`. Apply the window lemma on `[η0-2, η0]` and `[η0, η0+2]`,
  then the Sobolev bound at the two slices.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Real

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- **Sobolev bound on a slice** (`Cyl.sq_norm_le_cyl`, applied to the `ℂ`-valued `w`): for a real
`C²`, `c`-periodic `w`, `w(z)² ≤ 2c⁻¹ ∫_{-c/2}^{c/2} w(q,z₂)² dq + c ∫_{-c/2}^{c/2} (∂_q w)(q,z₂)² dq`. -/
theorem goodSlice_sup_sq_le {c : ℝ} (hc : 0 < c) {w : Plane → ℝ} (hw : ContDiff ℝ 2 w)
    (hper : Cyl.IsPeriodic c w) (z : Plane) :
    w z ^ 2 ≤ 2 * c⁻¹ * (∫ q in Ioc (-c / 2) (c / 2), w (q, z.2) ^ 2) +
      c * ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ w (q, z.2) ^ 2 := by
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  have hwd : Differentiable ℝ w := hw.differentiable (by norm_num)
  have hf : ContDiff ℝ 1 (fun p : Plane => (w p : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hw1
  have hfper : Cyl.IsPeriodic c (fun p : Plane => (w p : ℂ)) := fun p => by
    show ((w (p.1 + c, p.2) : ℝ) : ℂ) = ((w p : ℝ) : ℂ)
    rw [hper p]
  have hQ : ∀ q η : ℝ, Cyl.partialQ (fun p : Plane => (w p : ℂ)) (q, η)
      = ((Cyl.partialQ w (q, η) : ℝ) : ℂ) := fun q η =>
    (Cyl.hasDerivAt_sliceQ hwd q η).ofReal_comp.deriv
  have hle : -c / 2 ≤ c / 2 := by linarith
  have key := Cyl.sq_norm_le_cyl hc hf hfper z
  simp only [hQ, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    intervalIntegral.integral_of_le hle] at key
  exact key

/-- **Convexity gap**: if `m' = m1`, `m1' = m2` and `m2 ≥ κ` on `[s, s+2]`, then
`m(s+1) + κ/2 ≤ (m(s) + m(s+2))/2`. (The function `m + (κ/2)(η-s)(s+2-η)` has second derivative
`m2 - κ ≥ 0`, so it is convex on the window, and it is `m(s)`, `m(s+2)` at the ends and
`m(s+1) + κ/2` at the midpoint.) -/
theorem goodSlice_convex_gap {m m1 m2 : ℝ → ℝ} {s β κ : ℝ} (hβ : β = s + 2)
    (hm : ∀ η, HasDerivAt m (m1 η) η) (hm1 : ∀ η, HasDerivAt m1 (m2 η) η)
    (hc : ∀ η ∈ Icc s β, κ ≤ m2 η) :
    m (s + 1) + κ / 2 ≤ (m s + m β) / 2 := by
  subst hβ
  have hg1 : ∀ η : ℝ, HasDerivAt (fun x => m x + κ / 2 * ((x - s) * (s + 2 - x)))
      (m1 η + κ / 2 * (s + 2 + s - 2 * η)) η := by
    intro η
    have h0 : HasDerivAt (fun x : ℝ => (x - s) * (s + 2 - x))
        (1 * (s + 2 - η) + (η - s) * (0 - 1)) η :=
      ((hasDerivAt_id' η).sub_const s).mul ((hasDerivAt_const η (s + 2)).sub (hasDerivAt_id' η))
    have h := (hm η).add (h0.const_mul (κ / 2))
    exact h.congr_deriv (by ring)
  have hg2 : ∀ η : ℝ, HasDerivAt (fun x => m1 x + κ / 2 * (s + 2 + s - 2 * x))
      (m2 η + κ / 2 * -(2 * 1)) η := by
    intro η
    have hl : HasDerivAt (fun x : ℝ => s + 2 + s - 2 * x) (-(2 * 1)) η :=
      ((hasDerivAt_id' η).const_mul 2).const_sub (s + 2 + s)
    exact (hm1 η).add (hl.const_mul (κ / 2))
  have hcont : ContinuousOn (fun x => m x + κ / 2 * ((x - s) * (s + 2 - x))) (Icc s (s + 2)) :=
    fun η _ => (hg1 η).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun x => m x + κ / 2 * ((x - s) * (s + 2 - x)))
      (interior (Icc s (s + 2))) :=
    fun η _ => (hg1 η).differentiableAt.differentiableWithinAt
  have hderiv : deriv (fun x => m x + κ / 2 * ((x - s) * (s + 2 - x)))
      = fun x => m1 x + κ / 2 * (s + 2 + s - 2 * x) :=
    funext fun η => (hg1 η).deriv
  have hdiff2 : DifferentiableOn ℝ (deriv (fun x => m x + κ / 2 * ((x - s) * (s + 2 - x))))
      (interior (Icc s (s + 2))) := by
    rw [hderiv]
    exact fun η _ => (hg2 η).differentiableAt.differentiableWithinAt
  have hnn : ∀ x ∈ interior (Icc s (s + 2)),
      0 ≤ deriv^[2] (fun x => m x + κ / 2 * ((x - s) * (s + 2 - x))) x := by
    intro x hx
    have hcx := hc x (interior_subset hx)
    show 0 ≤ deriv (deriv (fun x => m x + κ / 2 * ((x - s) * (s + 2 - x)))) x
    rw [hderiv, (hg2 x).deriv]
    linarith
  have hconv := convexOn_of_deriv2_nonneg (convex_Icc s (s + 2)) hcont hdiff hdiff2 hnn
  have hs : s ∈ Icc s (s + 2) := ⟨le_refl s, by linarith⟩
  have ht : s + 2 ∈ Icc s (s + 2) := ⟨by linarith, le_refl _⟩
  have hcomb := hconv.2 hs ht (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  have hmid : (1 / 2 : ℝ) • s + (1 / 2 : ℝ) • (s + 2) = s + 1 := by
    simp only [smul_eq_mul]
    ring
  rw [hmid] at hcomb
  simp only [smul_eq_mul] at hcomb
  have e1 : (s + 1 - s) * (s + 2 - (s + 1)) = 1 := by ring
  have e2 : (s - s) * (s + 2 - s) = 0 := by ring
  have e3 : (s + 2 - s) * (s + 2 - (s + 2)) = 0 := by ring
  rw [e1, e2, e3] at hcomb
  linarith

/-- **Window lemma**: if `m' = m1`, `m1' = m2`, `m2 ≥ 2P - 2|F|`, `|F| ≤ κ/2` on `[s, s+2]`,
`m(s), m(s+2) < ν` and `2ν ≤ κ`, then `P(a) ≤ κ` for some `a ∈ [s, s+2]`. -/
theorem goodSlice_exists_small_P {m m1 m2 P F : ℝ → ℝ} {s β κ ν : ℝ} (hβ : β = s + 2)
    (hm : ∀ η, HasDerivAt m (m1 η) η) (hm1 : ∀ η, HasDerivAt m1 (m2 η) η)
    (hm0 : ∀ η, 0 ≤ m η) (hid : ∀ η, 2 * P η - 2 * |F η| ≤ m2 η)
    (hF : ∀ η ∈ Icc s β, |F η| ≤ κ / 2)
    (hms : m s < ν) (hmβ : m β < ν) (h2ν : 2 * ν ≤ κ) :
    ∃ a ∈ Icc s β, P a ≤ κ := by
  by_contra hcon
  push_neg at hcon
  have hcurv : ∀ η ∈ Icc s β, κ ≤ m2 η := by
    intro η hη
    have h1 := hcon η hη
    have h2 := hF η hη
    have h3 := hid η
    linarith
  have hgap := goodSlice_convex_gap hβ hm hm1 hcurv
  have h0 := hm0 (s + 1)
  linarith

/-- **Good slices** (source line 447): since the slice energy `m → 0`, near every far `η0` there are
slices `a ∈ [η0 - 2, η0]` and `b ∈ [η0, η0 + 2]` on which `sup_q w²` is at most `ε`. -/
theorem goodSliceSup : GoodSliceSup := by
  intro c w hc hZ hE ε hε
  obtain ⟨M, hM⟩ := hZ.bounded
  have hc0 : c ≠ 0 := hc.ne'
  -- the constant `ν`; the curvature threshold is `κ = 2ν`
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν = min (ε * c / 4) (ε / (4 * c)) := ⟨_, rfl⟩
  have hνpos : 0 < ν := by
    rw [hν]
    exact lt_min (by positivity) (by positivity)
  have hν1 : ν ≤ ε * c / 4 := by
    rw [hν]
    exact min_le_left _ _
  have hν2 : ν ≤ ε / (4 * c) := by
    rw [hν]
    exact min_le_right _ _
  have hA : c⁻¹ * ν ≤ ε / 4 := by
    calc c⁻¹ * ν ≤ c⁻¹ * (ε * c / 4) := mul_le_mul_of_nonneg_left hν1 (inv_nonneg.mpr hc.le)
      _ = ε / 4 := by field_simp
  have hB : c * ν ≤ ε / 4 := by
    calc c * ν ≤ c * (ε / (4 * c)) := mul_le_mul_of_nonneg_left hν2 hc.le
      _ = ε / 4 := by field_simp
  -- the far region of the slice energy and of the Laplacian
  obtain ⟨R1, hR1⟩ := (osc_tendsto_iff _).1 hE ν hνpos
  obtain ⟨Mb, hMb⟩ : ∃ Mb : ℝ, Mb = |M| + 1 := ⟨_, rfl⟩
  have hMbpos : 0 < Mb := by
    rw [hMb]
    positivity
  have hMb0 : Mb ≠ 0 := hMbpos.ne'
  have hwM : ∀ z : Plane, |w z| ≤ Mb := fun z => by
    rw [hMb]
    linarith [hM z, le_abs_self M]
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ν / (Mb * c) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by
    rw [hδ]
    exact div_pos hνpos (mul_pos hMbpos hc)
  obtain ⟨R2, hR2⟩ := (osc_tendsto_iff _).1 hZ.lap_decay δ hδpos
  have hvol : (volume : Measure ℝ).real (Ioc (-c / 2) (c / 2)) = c := by
    rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  -- the forcing `F = ∫ w Δw` is at most `ν` for large `|η|`
  have hFb : ∀ η : ℝ, R2 ≤ |η| →
      |∫ q in Ioc (-c / 2) (c / 2), w (q, η) * Train.lapS w (q, η)| ≤ ν := by
    intro η hη
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (-c / 2) (c / 2))
      (f := fun q => w (q, η) * Train.lapS w (q, η)) (C := Mb * δ) (by simp) (fun q _ => by
        show ‖w (q, η) * Train.lapS w (q, η)‖ ≤ Mb * δ
        have h1 : |Train.lapS w (q, η)| < δ := hR2 (q, η) hη
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hwM (q, η)) h1.le (abs_nonneg _) hMbpos.le)
    rw [hvol, Real.norm_eq_abs] at h
    have e : Mb * δ * c = ν := by
      rw [hδ]
      field_simp
    exact h.trans e.le
  -- the slice energy identity and its consequences
  obtain ⟨m1, m2, hm, hm1, hm2eq⟩ := sliceEnergyIdentity c w hc hZ.smooth hZ.periodic
  have hm0 : ∀ η : ℝ, 0 ≤ ∫ q in Ioc (-c / 2) (c / 2), w (q, η) ^ 2 :=
    fun η => setIntegral_nonneg measurableSet_Ioc (fun q _ => sq_nonneg _)
  have hid : ∀ η : ℝ, 2 * (∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ w (q, η) ^ 2)
      - 2 * |∫ q in Ioc (-c / 2) (c / 2), w (q, η) * Train.lapS w (q, η)| ≤ m2 η := by
    intro η
    have hQ : 0 ≤ ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialEta w (q, η) ^ 2 :=
      setIntegral_nonneg measurableSet_Ioc (fun q _ => sq_nonneg _)
    have hFn := neg_abs_le (∫ q in Ioc (-c / 2) (c / 2), w (q, η) * Train.lapS w (q, η))
    have he := hm2eq η
    linarith
  have hmlt : ∀ η : ℝ, R1 ≤ |η| → ∫ q in Ioc (-c / 2) (c / 2), w (q, η) ^ 2 < ν := by
    intro η hη
    exact (abs_lt.mp (hR1 (0, η) hη)).2
  refine ⟨max R1 R2 + 2, fun η0 hη0 => ?_⟩
  have hnear : ∀ η : ℝ, η0 - 2 ≤ η → η ≤ η0 + 2 → max R1 R2 ≤ |η| := by
    intro η h1 h2
    have h3 := abs_sub_abs_le_abs_sub η0 η
    have h4 : |η0 - η| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hR1' : ∀ η : ℝ, η0 - 2 ≤ η → η ≤ η0 + 2 → R1 ≤ |η| :=
    fun η h1 h2 => le_trans (le_max_left _ _) (hnear η h1 h2)
  have hR2' : ∀ η : ℝ, η0 - 2 ≤ η → η ≤ η0 + 2 → R2 ≤ |η| :=
    fun η h1 h2 => le_trans (le_max_right _ _) (hnear η h1 h2)
  -- the good slice `a` in `[η0 - 2, η0]`
  have hFa : ∀ η ∈ Icc (η0 - 2) η0,
      |∫ q in Ioc (-c / 2) (c / 2), w (q, η) * Train.lapS w (q, η)| ≤ 2 * ν / 2 := fun η hη => by
    have := hFb η (hR2' η hη.1 (by linarith [hη.2]))
    linarith
  obtain ⟨a, ha, hPa⟩ := goodSlice_exists_small_P (m := fun η => ∫ q in Ioc (-c / 2) (c / 2), w (q, η) ^ 2)
    (m1 := m1) (m2 := m2)
    (P := fun η => ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ w (q, η) ^ 2)
    (F := fun η => ∫ q in Ioc (-c / 2) (c / 2), w (q, η) * Train.lapS w (q, η))
    (s := η0 - 2) (β := η0) (κ := 2 * ν) (ν := ν) (by ring) hm hm1 hm0 hid hFa
    (hmlt (η0 - 2) (hR1' (η0 - 2) le_rfl (by linarith)))
    (hmlt η0 (hR1' η0 (by linarith) (by linarith)))
    (by linarith)
  -- the good slice `b` in `[η0, η0 + 2]`
  have hFb2 : ∀ η ∈ Icc η0 (η0 + 2),
      |∫ q in Ioc (-c / 2) (c / 2), w (q, η) * Train.lapS w (q, η)| ≤ 2 * ν / 2 := fun η hη => by
    have := hFb η (hR2' η (by linarith [hη.1]) (by linarith [hη.2]))
    linarith
  obtain ⟨b, hb, hPb⟩ := goodSlice_exists_small_P (m := fun η => ∫ q in Ioc (-c / 2) (c / 2), w (q, η) ^ 2)
    (m1 := m1) (m2 := m2)
    (P := fun η => ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ w (q, η) ^ 2)
    (F := fun η => ∫ q in Ioc (-c / 2) (c / 2), w (q, η) * Train.lapS w (q, η))
    (s := η0) (β := η0 + 2) (κ := 2 * ν) (ν := ν) rfl hm hm1 hm0 hid hFb2
    (hmlt η0 (hR1' η0 (by linarith) (by linarith)))
    (hmlt (η0 + 2) (hR1' (η0 + 2) (by linarith) le_rfl))
    (by linarith)
  have hPa' : ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ w (q, a) ^ 2 ≤ 2 * ν := hPa
  have hPb' : ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ w (q, b) ^ 2 ≤ 2 * ν := hPb
  have hmA : ∫ q in Ioc (-c / 2) (c / 2), w (q, a) ^ 2 < ν :=
    hmlt a (hR1' a ha.1 (by linarith [ha.2]))
  have hmB : ∫ q in Ioc (-c / 2) (c / 2), w (q, b) ^ 2 < ν :=
    hmlt b (hR1' b (by linarith [hb.1]) hb.2)
  -- the sup bound on a slice with small energy and small `∂_q`-energy
  have hsup : ∀ x : ℝ, ∫ q in Ioc (-c / 2) (c / 2), w (q, x) ^ 2 < ν →
      ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ w (q, x) ^ 2 ≤ 2 * ν →
      ∀ q : ℝ, w (q, x) ^ 2 ≤ ε := by
    intro x hmx hPx q
    have h : w (q, x) ^ 2 ≤ 2 * c⁻¹ * (∫ q' in Ioc (-c / 2) (c / 2), w (q', x) ^ 2) +
        c * ∫ q' in Ioc (-c / 2) (c / 2), Cyl.partialQ w (q', x) ^ 2 :=
      goodSlice_sup_sq_le hc hZ.smooth hZ.periodic (q, x)
    have h3 : 2 * c⁻¹ * (∫ q' in Ioc (-c / 2) (c / 2), w (q', x) ^ 2) ≤ 2 * c⁻¹ * ν :=
      mul_le_mul_of_nonneg_left hmx.le (by
        have := inv_nonneg.mpr hc.le
        linarith)
    have h4 : c * ∫ q' in Ioc (-c / 2) (c / 2), Cyl.partialQ w (q', x) ^ 2 ≤ c * (2 * ν) :=
      mul_le_mul_of_nonneg_left hPx hc.le
    linarith
  exact ⟨a, b, ha.1, ha.2, hb.1, hb.2, hsup a hmA hPa', hsup b hmB hPb'⟩

end UnforcedLeray.Short.PartI
