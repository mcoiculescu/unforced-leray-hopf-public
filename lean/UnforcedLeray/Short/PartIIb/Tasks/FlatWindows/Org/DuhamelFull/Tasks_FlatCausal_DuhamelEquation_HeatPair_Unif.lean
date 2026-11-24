import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatPair.Unif
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_T12_7_4

/-!
# Part II-b, task `PartII-b:T12/7/4/2` (`dfe_deqhpUnif`): uniform approximate identity

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
Write `θ = ν(s-t)`, `K_θ = flatHeatKernel θ`, `D(w) = Ψ(s, z-w)_i - Ψ(t,z)_i`. Then
`deqSmooth(s,z) - Ψ(t,z) = ∫ K_θ(w) D(w) dw`. Let `δ₁` be a uniform continuity radius of `Ψ_i`
for accuracy `ε/2`: `|D(w)| < ε/2` when `‖w‖ < δ₁` and `|s-t| < δ₁`, while `|D| ≤ 2M` always.
With `K_θ(w) e^{(|w|²-δ₁²)/(8θ)} = 2 flatHeatKernel(2θ)(w) e^{-δ₁²/(8θ)}` the integrand is
majorized by `(ε/2) K_θ + 4M e^{-δ₁²/(8θ)} flatHeatKernel(2θ)`, whose integral is
`ε/2 + 4M e^{-δ₁²/(8θ)} ≤ ε` once `θ ≤ κ = ε δ₁²/(64M+1)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Exponent identity of the Gaussian majorant (`θ > 0`, `Q = |w|²`). -/
private theorem dfe_deqhu_key (θ Q d : ℝ) (hθ : 0 < θ) :
    (4 * Real.pi * θ)⁻¹ * Real.exp (-Q / (4 * θ)) * Real.exp ((Q - d ^ 2) / (8 * θ)) =
      2 * ((4 * Real.pi * (2 * θ))⁻¹ * Real.exp (-Q / (4 * (2 * θ)))) *
        Real.exp (-d ^ 2 / (8 * θ)) := by
  have hne : θ ≠ 0 := hθ.ne'
  have h1 : Real.exp (-Q / (4 * θ)) * Real.exp ((Q - d ^ 2) / (8 * θ)) =
      Real.exp (-Q / (4 * (2 * θ))) * Real.exp (-d ^ 2 / (8 * θ)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have h2 : (4 * Real.pi * θ)⁻¹ = 2 * (4 * Real.pi * (2 * θ))⁻¹ := by
    first | (field_simp; done) | (field_simp; ring)
  calc (4 * Real.pi * θ)⁻¹ * Real.exp (-Q / (4 * θ)) * Real.exp ((Q - d ^ 2) / (8 * θ))
      = (4 * Real.pi * θ)⁻¹ * (Real.exp (-Q / (4 * θ)) * Real.exp ((Q - d ^ 2) / (8 * θ))) := by
        ring
    _ = 2 * (4 * Real.pi * (2 * θ))⁻¹ *
          (Real.exp (-Q / (4 * (2 * θ))) * Real.exp (-d ^ 2 / (8 * θ))) := by
        rw [h1, h2]
    _ = 2 * ((4 * Real.pi * (2 * θ))⁻¹ * Real.exp (-Q / (4 * (2 * θ)))) *
          Real.exp (-d ^ 2 / (8 * θ)) := by
        ring

/-- A vector of norm at least `d ≥ 0` has `d² ≤ w₁² + w₂²`. -/
private theorem dfe_deqhu_sq_le (d : ℝ) (w : ℝ × ℝ) (hd : 0 ≤ d) (hdw : d ≤ ‖w‖) :
    d ^ 2 ≤ w.1 ^ 2 + w.2 ^ 2 := by
  rw [Prod.norm_def] at hdw
  rcases le_max_iff.mp hdw with h | h
  · rw [Real.norm_eq_abs] at h
    nlinarith [sq_abs w.1, sq_nonneg w.2, abs_nonneg w.1, mul_le_mul h h hd (abs_nonneg _)]
  · rw [Real.norm_eq_abs] at h
    nlinarith [sq_abs w.2, sq_nonneg w.1, abs_nonneg w.2, mul_le_mul h h hd (abs_nonneg _)]

theorem dfe_deqhpUnif : dfe_DeqhpUnif := by
  intro ν t hν ht Ψ hΨ i ε hε
  have hgc : Continuous (fun x : Coord => Ψ x i) := (hΨ.smooth i).smooth.continuous
  obtain ⟨M, hM⟩ := hgc.bounded_above_of_compact_support (hΨ.smooth i).compact
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have huc : UniformContinuous (fun x : Coord => Ψ x i) :=
    HasCompactSupport.uniformContinuous_of_continuous (hΨ.smooth i).compact hgc
  obtain ⟨δ1, hδ1, hunif⟩ := Metric.uniformContinuous_iff.mp huc (ε / 2) (by linarith)
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = ε * δ1 ^ 2 / (64 * M + 1) := ⟨_, rfl⟩
  have hκ : 0 < κ := by
    rw [hκdef]; exact div_pos (mul_pos hε (pow_pos hδ1 2)) (by linarith)
  have hκ2 : κ * (64 * M + 1) = ε * δ1 ^ 2 := by
    rw [hκdef]; first | (field_simp; done) | (field_simp; ring)
  refine ⟨min δ1 (κ / ν), lt_min hδ1 (div_pos hκ hν), ?_⟩
  intro s hts hsδ z
  have hm1 := min_le_left δ1 (κ / ν)
  have hm2 := min_le_right δ1 (κ / ν)
  have hst1 : s - t < δ1 := by linarith
  have hst2 : s - t ≤ κ / ν := by linarith
  have hθ : 0 < ν * (s - t) := mul_pos hν (by linarith)
  have hνne : ν ≠ 0 := hν.ne'
  have hθκ : ν * (s - t) ≤ κ := by
    calc ν * (s - t) ≤ ν * (κ / ν) := mul_le_mul_of_nonneg_left hst2 hν.le
      _ = κ := by first | (field_simp; done) | (field_simp; ring)
  -- flat heat kernel facts
  have hK : ∀ θ' : ℝ, 0 < θ' → ∀ w : ℝ × ℝ, 0 ≤ flatHeatKernel θ' w := by
    intro θ' hθ' w
    rw [flatHeat_kernel_eq hθ']
    exact UnforcedLeray.B0284.heatKernel2_nonneg hθ' w
  have hKint : ∀ θ' : ℝ, 0 < θ' → Integrable (fun w : ℝ × ℝ => flatHeatKernel θ' w) := by
    intro θ' hθ'
    exact (UnforcedLeray.B0284.integrable_heatKernel2 hθ').congr
      (ae_of_all _ fun w => (flatHeat_kernel_eq hθ' w).symm)
  have hKone : ∀ θ' : ℝ, 0 < θ' → ∫ w : ℝ × ℝ, flatHeatKernel θ' w = 1 := by
    intro θ' hθ'
    simp only [flatHeat_kernel_eq hθ']
    exact UnforcedLeray.B0284.integral_heatKernel2 hθ'
  have hKmeas : ∀ θ' : ℝ, 0 < θ' → Measurable (fun w : ℝ × ℝ => flatHeatKernel θ' w) := by
    intro θ' hθ'
    have e : (fun w : ℝ × ℝ => flatHeatKernel θ' w) = UnforcedLeray.B0284.heatKernel2 θ' :=
      funext (flatHeat_kernel_eq hθ')
    rw [e]
    exact UnforcedLeray.B0284.measurable_heatKernel2_right θ'
  have h2θ : 0 < 2 * (ν * (s - t)) := by linarith
  have hgs : Continuous (fun y : ℝ × ℝ => Ψ (s, y) i) :=
    hgc.comp (continuous_const.prodMk continuous_id)
  -- pointwise bound on the difference of values
  have hD : ∀ w : ℝ × ℝ, |Ψ (s, z - w) i - Ψ (t, z) i| ≤
      ε / 2 + 2 * M * Real.exp ((w.1 ^ 2 + w.2 ^ 2 - δ1 ^ 2) / (8 * (ν * (s - t)))) := by
    intro w
    have hnn : 0 ≤ 2 * M * Real.exp ((w.1 ^ 2 + w.2 ^ 2 - δ1 ^ 2) / (8 * (ν * (s - t)))) :=
      mul_nonneg (mul_nonneg (by norm_num) hM0) (Real.exp_pos _).le
    by_cases hw : δ1 ≤ ‖w‖
    · have hsq := dfe_deqhu_sq_le δ1 w hδ1.le hw
      have hexp : 1 ≤ Real.exp ((w.1 ^ 2 + w.2 ^ 2 - δ1 ^ 2) / (8 * (ν * (s - t)))) :=
        Real.one_le_exp (div_nonneg (by linarith) (by linarith))
      have hΨ1 : ‖Ψ (s, z - w) i‖ ≤ M := hM (s, z - w)
      have hΨ2 : ‖Ψ (t, z) i‖ ≤ M := hM (t, z)
      rw [Real.norm_eq_abs] at hΨ1 hΨ2
      have h2M : |Ψ (s, z - w) i - Ψ (t, z) i| ≤ 2 * M := by
        rw [abs_le]
        rw [abs_le] at hΨ1 hΨ2
        constructor <;> linarith [hΨ1.1, hΨ1.2, hΨ2.1, hΨ2.2]
      have h2M' : 2 * M * 1 ≤ 2 * M * Real.exp ((w.1 ^ 2 + w.2 ^ 2 - δ1 ^ 2) / (8 * (ν * (s - t)))) :=
        mul_le_mul_of_nonneg_left hexp (by linarith)
      linarith
    · push_neg at hw
      have hdist : dist ((s, z - w) : Coord) ((t, z) : Coord) < δ1 := by
        rw [Prod.dist_eq]
        show max (dist s t) (dist (z - w) z) < δ1
        refine max_lt ?_ ?_
        · rw [Real.dist_eq, abs_lt]
          constructor <;> linarith
        · rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
          exact hw
      have h3 : dist (Ψ (s, z - w) i) (Ψ (t, z) i) < ε / 2 := hunif hdist
      rw [Real.dist_eq] at h3
      linarith
  -- the difference as an integral
  have hf1 : Integrable (fun w : ℝ × ℝ => flatHeatKernel (ν * (s - t)) w * Ψ (s, z - w) i) := by
    refine Integrable.mono' ((hKint (ν * (s - t)) hθ).const_mul M) ?_ ?_
    · exact (hKmeas (ν * (s - t)) hθ).aestronglyMeasurable.mul
        (hgs.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · refine ae_of_all _ fun w => ?_
      rw [norm_mul, Real.norm_of_nonneg (hK _ hθ w)]
      have hΨ' : ‖Ψ (s, z - w) i‖ ≤ M := hM (s, z - w)
      rw [mul_comm M]
      exact mul_le_mul_of_nonneg_left hΨ' (hK _ hθ w)
  have hconst : Integrable (fun w : ℝ × ℝ => Ψ (t, z) i * flatHeatKernel (ν * (s - t)) w) :=
    (hKint (ν * (s - t)) hθ).const_mul _
  have e1 : ∫ w : ℝ × ℝ, Ψ (t, z) i * flatHeatKernel (ν * (s - t)) w = Ψ (t, z) i := by
    rw [integral_const_mul, hKone _ hθ, mul_one]
  have e2 : ∫ w : ℝ × ℝ, flatHeatKernel (ν * (s - t)) w * (Ψ (s, z - w) i - Ψ (t, z) i) =
      (∫ w : ℝ × ℝ, flatHeatKernel (ν * (s - t)) w * Ψ (s, z - w) i) -
        (∫ w : ℝ × ℝ, Ψ (t, z) i * flatHeatKernel (ν * (s - t)) w) := by
    have h2 : (fun w : ℝ × ℝ => flatHeatKernel (ν * (s - t)) w * (Ψ (s, z - w) i - Ψ (t, z) i)) =
        (fun w : ℝ × ℝ => flatHeatKernel (ν * (s - t)) w * Ψ (s, z - w) i -
          Ψ (t, z) i * flatHeatKernel (ν * (s - t)) w) := by
      funext w
      ring
    rw [h2]
    exact integral_sub hf1 hconst
  have hsplit : deqSmooth ν Ψ i t s z - Ψ (t, z) i =
      ∫ w : ℝ × ℝ, flatHeatKernel (ν * (s - t)) w * (Ψ (s, z - w) i - Ψ (t, z) i) := by
    rw [e2, e1]
    simp only [deqSmooth]
  -- pointwise majorant
  have hpw : ∀ w : ℝ × ℝ,
      |flatHeatKernel (ν * (s - t)) w * (Ψ (s, z - w) i - Ψ (t, z) i)| ≤
        ε / 2 * flatHeatKernel (ν * (s - t)) w +
          4 * M * Real.exp (-δ1 ^ 2 / (8 * (ν * (s - t)))) *
            flatHeatKernel (2 * (ν * (s - t))) w := by
    intro w
    rw [abs_mul, abs_of_nonneg (hK _ hθ w)]
    have hKexp : flatHeatKernel (ν * (s - t)) w *
        Real.exp ((w.1 ^ 2 + w.2 ^ 2 - δ1 ^ 2) / (8 * (ν * (s - t)))) =
        2 * flatHeatKernel (2 * (ν * (s - t))) w * Real.exp (-δ1 ^ 2 / (8 * (ν * (s - t)))) := by
      unfold flatHeatKernel
      exact dfe_deqhu_key _ _ _ hθ
    calc flatHeatKernel (ν * (s - t)) w * |Ψ (s, z - w) i - Ψ (t, z) i|
        ≤ flatHeatKernel (ν * (s - t)) w *
            (ε / 2 + 2 * M * Real.exp ((w.1 ^ 2 + w.2 ^ 2 - δ1 ^ 2) / (8 * (ν * (s - t))))) :=
          mul_le_mul_of_nonneg_left (hD w) (hK _ hθ w)
      _ = ε / 2 * flatHeatKernel (ν * (s - t)) w +
            2 * M * (flatHeatKernel (ν * (s - t)) w *
              Real.exp ((w.1 ^ 2 + w.2 ^ 2 - δ1 ^ 2) / (8 * (ν * (s - t))))) := by ring
      _ = ε / 2 * flatHeatKernel (ν * (s - t)) w +
            4 * M * Real.exp (-δ1 ^ 2 / (8 * (ν * (s - t)))) *
              flatHeatKernel (2 * (ν * (s - t))) w := by
            rw [hKexp]; ring
  -- smallness of the Gaussian term
  have hsmall : 4 * M * Real.exp (-δ1 ^ 2 / (8 * (ν * (s - t)))) ≤ ε / 2 := by
    set θ := ν * (s - t) with hθdef
    have hθne : θ ≠ 0 := hθ.ne'
    set u := Real.exp (-δ1 ^ 2 / (8 * θ)) with hudef
    have hu0 : 0 < u := Real.exp_pos _
    have hu : u * Real.exp (δ1 ^ 2 / (8 * θ)) = 1 := by
      rw [hudef, ← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero]
    have hx1 : δ1 ^ 2 / (8 * θ) + 1 ≤ Real.exp (δ1 ^ 2 / (8 * θ)) :=
      Real.add_one_le_exp _
    have hux : u * (δ1 ^ 2 / (8 * θ)) ≤ 1 := by
      nlinarith [hu, hx1, hu0]
    have hu2 : u * δ1 ^ 2 ≤ 8 * θ * 1 := by
      have e : u * δ1 ^ 2 = 8 * θ * (u * (δ1 ^ 2 / (8 * θ))) := by
        first | (field_simp; done) | (field_simp; ring)
      rw [e]
      exact mul_le_mul_of_nonneg_left hux (by linarith)
    have hB : 4 * M * u * δ1 ^ 2 ≤ ε / 2 * δ1 ^ 2 := by
      have h8 : 4 * M * u * δ1 ^ 2 ≤ 4 * M * (8 * κ) := by
        have : 4 * M * u * δ1 ^ 2 = 4 * M * (u * δ1 ^ 2) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have h9 : 4 * M * (8 * κ) ≤ ε / 2 * δ1 ^ 2 := by
        nlinarith [hκ2, hκ, hM0]
      linarith
    exact le_of_mul_le_mul_right hB (pow_pos hδ1 2)
  -- integrate the majorant
  have hg_int : Integrable (fun w : ℝ × ℝ =>
      ε / 2 * flatHeatKernel (ν * (s - t)) w +
        4 * M * Real.exp (-δ1 ^ 2 / (8 * (ν * (s - t)))) *
          flatHeatKernel (2 * (ν * (s - t))) w) :=
    ((hKint (ν * (s - t)) hθ).const_mul _).add ((hKint (2 * (ν * (s - t))) h2θ).const_mul _)
  have hgI : ∫ w : ℝ × ℝ, (ε / 2 * flatHeatKernel (ν * (s - t)) w +
        4 * M * Real.exp (-δ1 ^ 2 / (8 * (ν * (s - t)))) *
          flatHeatKernel (2 * (ν * (s - t))) w) =
      ε / 2 + 4 * M * Real.exp (-δ1 ^ 2 / (8 * (ν * (s - t)))) := by
    rw [integral_add ((hKint (ν * (s - t)) hθ).const_mul _)
        ((hKint (2 * (ν * (s - t))) h2θ).const_mul _),
      integral_const_mul, integral_const_mul, hKone _ hθ, hKone _ h2θ]
    ring
  have hmain := norm_integral_le_of_norm_le hg_int
    (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hpw w)
  rw [hgI] at hmain
  have hfinal : ‖∫ w : ℝ × ℝ, flatHeatKernel (ν * (s - t)) w * (Ψ (s, z - w) i - Ψ (t, z) i)‖ ≤
      ε / 2 + 4 * M * Real.exp (-δ1 ^ 2 / (8 * (ν * (s - t)))) := by
    refine le_trans (le_of_eq rfl) ?_
    exact hmain
  rw [← Real.norm_eq_abs, hsplit]
  linarith

end UnforcedLeray.Short.IIb

end
