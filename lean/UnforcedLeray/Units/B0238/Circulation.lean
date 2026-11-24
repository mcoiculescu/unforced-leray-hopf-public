import UnforcedLeray.Units.B0238.Partials

/-!
# B0238 helpers: zero circulation of a periodic field with a decaying stream

Helper module of blueprint unit **B0238** (`unlabeled:4127`, `paper/main.tex` lines 4125–4134:
"It has zero circulation"; the train facts of tex 2178–2183: "The conservative vorticity
equation preserves its integral and its `L¹` and `L^∞` bounds").

`integral_cell_curl_eq_zero`: let `v` be a `C¹`, `c`-periodic field on the plane with a
differentiable stream `ψ`, `v = ∇^⊥ψ = (-∂_ηψ, ∂_qψ)`, decaying as `|η| → ∞` uniformly in `q`
(the decaying stream of tex 2049). If its vorticity `ω = ∂_q v₂ - ∂_η v₁` is integrable over the
centred cell `[-c/2, c/2) × ℝ`, then `∫_cell ω = 0`.

Proof. Fubini puts the `q`-integral inside. For each `η`, `∫ ∂_q v₂ dq = 0` by periodicity, and
`∫ ∂_η v₁ dq = J'(η)` with `J(η) = ∫ v₁(q,η) dq`. So `∫_cell ω = -∫_ℝ J'`, and `J'` is
integrable. `J = -Φ'` with `Φ(η) = ∫ ψ(q,η) dq → 0` at `±∞`. `J` has limits at `±∞` (its
derivative is integrable); by the mean value theorem `-J(ξ_η) = Φ(η+1) - Φ(η) → 0` along some
`ξ_η ∈ (η, η+1)`, so both limits vanish, and `∫_ℝ J' = 0 - 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace UnforcedLeray.B0238

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.GaussianVortex (perpendicularGradient partialX partialY)

/-- A function decaying as `|η| → ∞` uniformly in `q` has decaying `q`-integrals over a
bounded interval, along any filter on which `|η| → ∞`. -/
theorem tendsto_intervalIntegral_of_decay {ψ : Plane → ℝ}
    (hdecay : Tendsto ψ (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)) (a b : ℝ)
    {l : Filter ℝ} (hl : Tendsto (fun η : ℝ => |η|) l atTop) :
    Tendsto (fun η => ∫ q in a..b, ψ (q, η)) l (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hε' : 0 < ε / (|b - a| + 1) := div_pos hε (by positivity)
  have h1 := Metric.tendsto_nhds.1 hdecay _ hε'
  rw [Filter.eventually_comap] at h1
  filter_upwards [hl.eventually h1] with η hη
  have hb : ∀ q ∈ Ι a b, ‖ψ (q, η)‖ ≤ ε / (|b - a| + 1) := by
    intro q _
    have := hη (q, η) rfl
    rw [Real.dist_eq, sub_zero] at this
    rw [Real.norm_eq_abs]; exact this.le
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
  calc ‖∫ q in a..b, ψ (q, η)‖ ≤ ε / (|b - a| + 1) * |b - a| := h2
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg (b - a)]

/-- If `J` has integrable derivative, `Φ' = -J`, and `Φ → 0` at `+∞`, then `J → 0` at `+∞`. -/
theorem tendsto_atTop_zero_of_primitive {J J' Φ : ℝ → ℝ} (hJ : ∀ η, HasDerivAt J (J' η) η)
    (hJ' : Integrable J') (hΦ : ∀ η, HasDerivAt Φ (-J η) η) (hΦtop : Tendsto Φ atTop (𝓝 0)) :
    Tendsto J atTop (𝓝 0) := by
  have hL := tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi (a := 0) (fun x _ => hJ x)
    hJ'.integrableOn
  have hmvt : ∀ η : ℝ, ∃ ξ ∈ Ioo η (η + 1), -J ξ = Φ (η + 1) - Φ η := by
    intro η
    obtain ⟨ξ, hξ, h⟩ := exists_hasDerivAt_eq_slope (f := Φ) (f' := fun x => -J x)
      (lt_add_one η) (fun x _ => (hΦ x).continuousAt.continuousWithinAt) (fun x _ => hΦ x)
    refine ⟨ξ, hξ, ?_⟩
    rw [h, add_sub_cancel_left, div_one]
  choose ξ hξ hξeq using hmvt
  have hξtop : Tendsto ξ atTop atTop := tendsto_atTop_mono (fun η => (hξ η).1.le) tendsto_id
  have h1 : Tendsto (fun η => -J (ξ η)) atTop (𝓝 (-limUnder atTop J)) := (hL.comp hξtop).neg
  have h2 : Tendsto (fun η => -J (ξ η)) atTop (𝓝 0) := by
    simp_rw [hξeq]
    have := (hΦtop.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)).sub hΦtop
    simpa only [sub_zero, Function.comp_def, id] using this
  have h3 : limUnder atTop J = 0 := by
    have := tendsto_nhds_unique h1 h2
    linarith
  rwa [h3] at hL

/-- If `J` has integrable derivative, `Φ' = -J`, and `Φ → 0` at `-∞`, then `J → 0` at `-∞`. -/
theorem tendsto_atBot_zero_of_primitive {J J' Φ : ℝ → ℝ} (hJ : ∀ η, HasDerivAt J (J' η) η)
    (hJ' : Integrable J') (hΦ : ∀ η, HasDerivAt Φ (-J η) η) (hΦbot : Tendsto Φ atBot (𝓝 0)) :
    Tendsto J atBot (𝓝 0) := by
  have hL := tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic (a := 0) (fun x _ => hJ x)
    hJ'.integrableOn
  have hmvt : ∀ η : ℝ, ∃ ξ ∈ Ioo η (η + 1), -J ξ = Φ (η + 1) - Φ η := by
    intro η
    obtain ⟨ξ, hξ, h⟩ := exists_hasDerivAt_eq_slope (f := Φ) (f' := fun x => -J x)
      (lt_add_one η) (fun x _ => (hΦ x).continuousAt.continuousWithinAt) (fun x _ => hΦ x)
    refine ⟨ξ, hξ, ?_⟩
    rw [h, add_sub_cancel_left, div_one]
  choose ξ hξ hξeq using hmvt
  have hξbot : Tendsto ξ atBot atBot :=
    tendsto_atBot_mono (fun η => (hξ η).2.le) (tendsto_atBot_add_const_right _ 1 tendsto_id)
  have h1 : Tendsto (fun η => -J (ξ η)) atBot (𝓝 (-limUnder atBot J)) := (hL.comp hξbot).neg
  have h2 : Tendsto (fun η => -J (ξ η)) atBot (𝓝 0) := by
    simp_rw [hξeq]
    have := (hΦbot.comp (tendsto_atBot_add_const_right _ 1 tendsto_id)).sub hΦbot
    simpa only [sub_zero, Function.comp_def, id] using this
  have h3 : limUnder atBot J = 0 := by
    have := tendsto_nhds_unique h1 h2
    linarith
  rwa [h3] at hL

/-- **Zero circulation** (tex 4131–4133, 2181–2183). A `C¹`, `c`-periodic field `v = ∇^⊥ψ` with
a differentiable stream `ψ` decaying as `|η| → ∞` (uniformly in `q`) and with vorticity
integrable over the centred cell has zero circulation: `∫_{[-c/2,c/2)×ℝ} curl v = 0`. -/
theorem integral_cell_curl_eq_zero {c : ℝ} (hc : 0 < c) {v : Plane → Vec} {ψ : Plane → ℝ}
    (hv : ContDiff ℝ 1 v) (hper : Cyl.IsPeriodic c v) (hψ : Differentiable ℝ ψ)
    (hstream : ∀ z, v z = toVec (perpendicularGradient ψ z))
    (hdecay : Tendsto ψ (comap (fun z : Plane => |z.2|) atTop) (𝓝 0))
    (hint : IntegrableOn (Cyl.curl v) (Cyl.cell c)) :
    ∫ z in Cyl.cell c, Cyl.curl v z = 0 := by
  have hab : -c / 2 ≤ c / 2 := by linarith
  have hu₁ : ContDiff ℝ 1 (fun w => v w 0) := contDiff_comp_apply hv 0
  have hu₂ : ContDiff ℝ 1 (fun w => v w 1) := contDiff_comp_apply hv 1
  have hD₁ : Continuous fun z => fderiv ℝ (fun w => v w 1) z (1, 0) :=
    continuous_fderiv_apply hu₂ _
  have hD₂ : Continuous fun z => fderiv ℝ (fun w => v w 0) z (0, 1) :=
    continuous_fderiv_apply hu₁ _
  -- the stream: `∂_η ψ = -v₁`
  have hψη : ∀ z : Plane, HasDerivAt (fun t => ψ (z.1, t)) (-v z 0) z.2 := by
    intro z
    have h := hasDerivAt_slice_eta (hψ z)
    have e : v z 0 = -partialY ψ z := by
      rw [hstream z]; rfl
    have e2 : partialY ψ z = fderiv ℝ ψ z (0, 1) := h.deriv
    have e3 : fderiv ℝ ψ z (0, 1) = -v z 0 := by
      simp only [e, e2, neg_neg]
    rwa [e3] at h
  -- inner integral over one period
  have hinner : ∀ η : ℝ, ∫ q in (-c / 2)..(c / 2), Cyl.curl v (q, η) =
      -∫ q in (-c / 2)..(c / 2), fderiv ℝ (fun w => v w 0) (q, η) (0, 1) := by
    intro η
    have hcq : Continuous fun q : ℝ => ((q, η) : Plane) := continuous_id.prodMk continuous_const
    have i1 : IntervalIntegrable (fun q : ℝ => fderiv ℝ (fun w => v w 1) (q, η) (1, 0)) volume
        (-c / 2) (c / 2) := (hD₁.comp hcq).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun q : ℝ => fderiv ℝ (fun w => v w 0) (q, η) (0, 1)) volume
        (-c / 2) (c / 2) := (hD₂.comp hcq).intervalIntegrable _ _
    simp_rw [curl_eq_fderiv hv]
    rw [intervalIntegral.integral_sub i1 i2]
    have hFTC : ∫ q in (-c / 2)..(c / 2), fderiv ℝ (fun w => v w 1) (q, η) (1, 0) =
        v (c / 2, η) 1 - v (-c / 2, η) 1 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => v (t, η) 1)
        (fun x _ => hasDerivAt_slice_q (z := (x, η)) (hu₂.differentiable one_ne_zero _)) i1
    have hper2 : v (c / 2, η) 1 = v (-c / 2, η) 1 := by
      have h := hper (-c / 2, η)
      have hb : -c / 2 + c = c / 2 := by ring
      simp only [hb] at h
      rw [h]
    rw [hFTC, hper2, sub_self, zero_sub]
  -- `J(η) = ∫ v₁(q,η) dq` and `Φ(η) = ∫ ψ(q,η) dq`
  have hJ : ∀ η, HasDerivAt (fun η => ∫ q in (-c / 2)..(c / 2), v (q, η) 0)
      (∫ q in (-c / 2)..(c / 2), fderiv ℝ (fun w => v w 0) (q, η) (0, 1)) η :=
    fun η => hasDerivAt_intervalIntegral_slice hu₁.continuous hD₂
      (fun z => hasDerivAt_slice_eta (hu₁.differentiable one_ne_zero z)) _ _ η
  have hΦ : ∀ η, HasDerivAt (fun η => ∫ q in (-c / 2)..(c / 2), ψ (q, η))
      (-(fun η => ∫ q in (-c / 2)..(c / 2), v (q, η) 0) η) η := by
    intro η
    have h := hasDerivAt_intervalIntegral_slice (G' := fun z => -v z 0) hψ.continuous
      hu₁.continuous.neg hψη (-c / 2) (c / 2) η
    rwa [intervalIntegral.integral_neg] at h
  -- Fubini
  have hIco : ∀ η : ℝ, ∫ q in Ico (-c / 2) (c / 2), Cyl.curl v (q, η) =
      ∫ q in (-c / 2)..(c / 2), Cyl.curl v (q, η) := by
    intro η
    rw [intervalIntegral.integral_of_le hab, integral_Ico_eq_integral_Ioo,
      integral_Ioc_eq_integral_Ioo]
  have hInt : Integrable (fun η => ∫ q in Ico (-c / 2) (c / 2), Cyl.curl v (q, η)) := by
    have h := hint
    rw [IntegrableOn, Cyl.volume_restrict_cell] at h
    exact h.integral_prod_right
  have hfun : (fun η => ∫ q in Ico (-c / 2) (c / 2), Cyl.curl v (q, η)) =
      fun η => -∫ q in (-c / 2)..(c / 2), fderiv ℝ (fun w => v w 0) (q, η) (0, 1) := by
    funext η; rw [hIco, hinner]
  have hJ'int : Integrable
      (fun η => ∫ q in (-c / 2)..(c / 2), fderiv ℝ (fun w => v w 0) (q, η) (0, 1)) := by
    have h := hInt
    rw [hfun] at h
    simpa only [Pi.neg_def, neg_neg] using h.neg
  have hΦtop := tendsto_intervalIntegral_of_decay hdecay (-c / 2) (c / 2) tendsto_abs_atTop_atTop
  have hΦbot := tendsto_intervalIntegral_of_decay hdecay (-c / 2) (c / 2) tendsto_abs_atBot_atTop
  have hJtop := tendsto_atTop_zero_of_primitive hJ hJ'int hΦ hΦtop
  have hJbot := tendsto_atBot_zero_of_primitive hJ hJ'int hΦ hΦbot
  rw [Cyl.integral_cell_eq_integral_integral hint, hfun, integral_neg,
    integral_of_hasDerivAt_of_tendsto hJ hJ'int hJbot hJtop, sub_zero, neg_zero]

end UnforcedLeray.B0238
