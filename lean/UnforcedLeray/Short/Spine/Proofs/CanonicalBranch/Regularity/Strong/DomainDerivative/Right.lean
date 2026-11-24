import UnforcedLeray.Short.Spine.Sub.SP_CAN4_2_1
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Strong.DomainDerivative.Duhamel
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Strong.DomainDerivative.ExpDZero
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Strong.DomainDerivative.ExpDJoint

/-!
# Spine: right one-sided derivative of a mild domain solution (task `Spine:SP-CAN/4/2/1/5`)

Target `MDRight` (`Sub/SP_CAN4_2_1.lean`). Source: `the November 2 reference manuscript`
line 1086 and lines 1134-1145.

For `s > θ`, `mdDuhamel` at `(θ, s)` gives `V θ = e^{h D} (V s) + K(s)` with `h = log s - log θ` and
`K(s) = ∫_{-s}^{-θ} e^{(log(-u) - log θ) D} L₀ V(-u) du`. Writing `e^{hD} z - z = ∫_0^h e^{rD} (D z) dr`
(`expD_integral_generator`) and splitting every integrand into its value at the base point plus a
remainder gives, with `t = s - θ`,
`V s - V θ - t • L' = -A - B - (h - t/θ) • D V θ`,
where `A = ∫_0^h (e^{rD} D V s - D V θ) dr` and `B = ∫_{-s}^{-θ} (integrand - L₀ V θ) du`.
Each piece is `o(t)`: `A` because `D V s → D V θ` (`V - U₂` continuous at `θ`), `B` by continuity of
`u ↦ L₀ V(-u)` at `-θ`, and `h - t/θ` by the logarithm inequalities of `mdr_log_bound`.
No joint continuity on a product space is used.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- `(I - D)^0` is the identity. -/
theorem mdr_idpow_eq_self {s : ℝ} (hs : s = 0) (x : XG) (hx : x ∈ (B0123.IDpow s).domain) :
    B0123.IDpow s ⟨x, hx⟩ = x := by
  subst hs
  apply B0094.ext_inner_basis
  intro n
  rw [B0123.inner_IDpow, B0123.idMult]
  simp

/-- Index change for `(I - D)^s`. -/
theorem mdr_idpow_index {s t : ℝ} (h : s = t) (x : XG) (hx : x ∈ (B0123.IDpow s).domain)
    (hy : x ∈ (B0123.IDpow t).domain) : B0123.IDpow s ⟨x, hx⟩ = B0123.IDpow t ⟨x, hy⟩ := by
  subst h
  rfl

/-- `V` is continuous on `(0, ∞)` when it is continuous into `X_{G,0}`. -/
theorem mdr_contOn (V : ℝ → XG) (hC : IsXGjContinuous V) : ContinuousOn V (Ioi 0) := by
  obtain ⟨U, hU, hUc⟩ := hC 0
  refine hUc.congr (fun θ hθ => ?_)
  obtain ⟨h, e⟩ := hU θ hθ
  have h0 := mdr_idpow_eq_self (s := ((0 : ℕ) : ℝ) / 2) (by norm_num) (V θ) h
  exact h0.symm.trans e

/-- Triangle estimate for the exponential: `‖e^{aD} x - w‖ ≤ ‖x - w‖ + ‖e^{aD} w - w‖`. -/
theorem mdr_expD_triangle (a : ℝ) (x w : XG) :
    ‖B0123.expD a x - w‖ ≤ ‖x - w‖ + ‖B0123.expD a w - w‖ := by
  have e : B0123.expD a x - w = B0123.expD a (x - w) + (B0123.expD a w - w) := by
    rw [map_sub]; abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  exact ((B0123.expD a).le_opNorm (x - w)).trans
    (mul_le_of_le_one_left (norm_nonneg _) (B0123.norm_expD_le a))

/-- Small exponents: `‖e^{aD} w0 - w0‖ ≤ ε` for `|a| < η`. -/
theorem mdr_expD_small {w0 : XG} {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ a : ℝ, |a| < η → ‖B0123.expD a w0 - w0‖ ≤ ε := by
  have hc : Continuous (fun a : ℝ => B0123.expD a w0) :=
    UnforcedLeray.Cons.G3b.continuous_expD_apply w0
  obtain ⟨η, hη, hball⟩ := Metric.continuousAt_iff.1 hc.continuousAt ε hε
  refine ⟨η, hη, fun a ha => ?_⟩
  have hd : dist a 0 < η := by rw [Real.dist_eq, sub_zero]; exact ha
  have h := hball hd
  have h0 : B0123.expD 0 w0 = w0 := by
    rw [B0123.expD_zero, ContinuousLinearMap.one_apply]
  simp only [h0, dist_eq_norm] at h
  exact h.le

/-- Continuity of `u ↦ e^{a(u) D} w(u)` at a point, from continuity of `a` and `w`. -/
theorem mdr_joint_at {a : ℝ → ℝ} {w : ℝ → XG} {u0 : ℝ} (ha : ContinuousAt a u0)
    (hw : ContinuousAt w u0) :
    ContinuousAt (fun u => B0123.expD (a u) (w u)) u0 := by
  have hc : ContinuousAt (fun u => B0123.expD (a u) (w u0)) u0 :=
    (UnforcedLeray.Cons.G3b.continuous_expD_apply (w u0)).continuousAt.comp ha
  have hsplit : ∀ u, ‖B0123.expD (a u) (w u) - B0123.expD (a u0) (w u0)‖
      ≤ ‖w u - w u0‖ + ‖B0123.expD (a u) (w u0) - B0123.expD (a u0) (w u0)‖ := by
    intro u
    have e : B0123.expD (a u) (w u) - B0123.expD (a u0) (w u0)
        = B0123.expD (a u) (w u - w u0)
          + (B0123.expD (a u) (w u0) - B0123.expD (a u0) (w u0)) := by
      rw [map_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact ((B0123.expD (a u)).le_opNorm (w u - w u0)).trans
      (mul_le_of_le_one_left (norm_nonneg _) (B0123.norm_expD_le _))
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun u => norm_nonneg _) hsplit ?_
  have h1 : Tendsto (fun u => ‖w u - w u0‖) (𝓝 u0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hw
  have h2 : Tendsto (fun u => ‖B0123.expD (a u) (w u0) - B0123.expD (a u0) (w u0)‖) (𝓝 u0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hc
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact h3

/-- Continuity of the right integrand `u ↦ e^{(log(-u) - log θ) D} L₀ V(-u)` on `[-s, -θ]`. -/
theorem mdr_integrand_cont {V : ℝ → XG} (hVc : ContinuousOn V (Ioi 0)) {θ s : ℝ} (hθ : 0 < θ)
    (hle : -s ≤ -θ) :
    ContinuousOn (fun u : ℝ => B0123.expD (Real.log (-u) - Real.log θ) (B0012.L0 (V (-u))))
      (uIcc (-s) (-θ)) := by
  intro u hu
  have hu0 : 0 < -u := by
    rw [uIcc_of_le hle] at hu
    linarith [hu.2]
  have hA : ContinuousAt (fun u : ℝ => Real.log (-u) - Real.log θ) u :=
    ((continuous_neg.continuousAt).log hu0.ne').sub continuousAt_const
  have hVu : ContinuousAt (fun u : ℝ => V (-u)) u :=
    (hVc.continuousAt (Ioi_mem_nhds hu0)).comp continuous_neg.continuousAt
  have hB : ContinuousAt (fun u : ℝ => B0012.L0 (V (-u))) u :=
    B0012.L0.continuous.continuousAt.comp hVu
  exact (mdr_joint_at hA hB).continuousWithinAt

/-- Subtracting a constant from an integrand. -/
theorem mdr_split {F : ℝ → XG} {a b : ℝ} (hF : ContinuousOn F (uIcc a b)) (L : XG) :
    (∫ u in a..b, F u) = (∫ u in a..b, (F u - L)) + (b - a) • L := by
  rw [intervalIntegral.integral_sub hF.intervalIntegrable intervalIntegrable_const,
    intervalIntegral.integral_const, sub_add_cancel]

/-- Logarithm bounds for `s ≥ θ > 0`, with `L = log s - log θ` and `t = s - θ`:
`0 ≤ L`, `L θ ≤ t`, and `|L - t/θ| θ² ≤ t²`. -/
theorem mdr_log_bound {θ s : ℝ} (hθ : 0 < θ) (hs : θ ≤ s) :
    0 ≤ Real.log s - Real.log θ ∧ (Real.log s - Real.log θ) * θ ≤ s - θ ∧
      |Real.log s - Real.log θ - (s - θ) / θ| * θ ^ 2 ≤ (s - θ) ^ 2 := by
  have hs0 : 0 < s := lt_of_lt_of_le hθ hs
  have hL0 : 0 ≤ Real.log s - Real.log θ := by
    have := Real.log_le_log hθ hs
    linarith
  have hU1 : Real.log s - Real.log θ ≤ (s - θ) / θ := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hs0 hθ)
    rw [Real.log_div hs0.ne' hθ.ne'] at h1
    have e : (s - θ) / θ = s / θ - 1 := by rw [sub_div, div_self hθ.ne']
    linarith
  have hL1 : (s - θ) / s ≤ Real.log s - Real.log θ := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hθ hs0)
    rw [Real.log_div hθ.ne' hs0.ne'] at h1
    have e : (s - θ) / s = 1 - θ / s := by rw [sub_div, div_self hs0.ne']
    linarith
  refine ⟨hL0, (le_div_iff₀ hθ).1 hU1, ?_⟩
  have hx : Real.log s - Real.log θ - (s - θ) / θ ≤ 0 := by linarith
  rw [abs_of_nonpos hx]
  have e3 : (s - θ) / θ - (s - θ) / s = (s - θ) ^ 2 / (θ * s) := by
    rw [div_sub_div _ _ hθ.ne' hs0.ne']; ring
  have h4 : (s - θ) ^ 2 / (θ * s) * θ ^ 2 ≤ (s - θ) ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos hθ hs0)]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (s - θ)) hθ.le) (sub_nonneg.2 hs)]
  have h5 : -(Real.log s - Real.log θ - (s - θ) / θ) ≤ (s - θ) ^ 2 / (θ * s) := by
    linarith
  calc -(Real.log s - Real.log θ - (s - θ) / θ) * θ ^ 2
      ≤ (s - θ) ^ 2 / (θ * s) * θ ^ 2 := mul_le_mul_of_nonneg_right h5 (by positivity)
    _ ≤ (s - θ) ^ 2 := h4

set_option maxHeartbeats 1000000 in
/-- **Right derivative** (shorter proof lines 1134-1145): `MDRight`. -/
theorem mdRight : MDRight := by
  intro _hE V hV hC θ hθ h
  have hVc := mdr_contOn V hC
  obtain ⟨U, hU, hUc⟩ := hC 2
  have hDdom : ∀ t : ℝ, 0 < t → V t ∈ B0094.D.domain := by
    intro t ht
    obtain ⟨h2, _⟩ := hU t ht
    rw [← B0123.XGj_two]
    exact h2
  have hDsub : ∀ t : ℝ, ∀ ht : 0 < t, B0094.D ⟨V t, hDdom t ht⟩ = V t - U t := by
    intro t ht
    obtain ⟨h2, e2⟩ := hU t ht
    have h1 : V t ∈ (B0123.IDpow 1).domain := by
      rw [B0123.IDpow_one_domain]
      exact hDdom t ht
    have hidx : ((2 : ℕ) : ℝ) / 2 = 1 := by norm_num
    have e1 : B0123.IDpow 1 ⟨V t, h1⟩ = U t :=
      (mdr_idpow_index hidx (V t) h2 h1).symm.trans e2
    have hD1 : B0123.IDpow 1 ⟨V t, h1⟩ = V t - B0094.D ⟨V t, hDdom t ht⟩ :=
      B0123.IDpow_one_apply ⟨V t, h1⟩ (hDdom t ht)
    rw [← e1, hD1]
    abel
  have hVat : ContinuousAt V θ := hVc.continuousAt (Ioi_mem_nhds hθ)
  have hUat : ContinuousAt U θ := hUc.continuousAt (Ioi_mem_nhds hθ)
  have hdz : B0094.D ⟨V θ, h⟩ = V θ - U θ := hDsub θ hθ
  have hfc : ContinuousAt (fun t => V t - U t) θ := hVat.sub hUat
  have hVθ' : ContinuousAt V (-(-θ)) := by
    rw [neg_neg]; exact hVat
  have hw : ContinuousAt (fun u : ℝ => B0012.L0 (V (-u))) (-θ) :=
    B0012.L0.continuous.continuousAt.comp (hVθ'.comp continuous_neg.continuousAt)
  have hderiv : HasDerivWithinAt V (-(B0012.L0 (V θ)) + (-θ⁻¹) • B0094.D ⟨V θ, h⟩) (Ici θ) θ := by
    rw [hasDerivWithinAt_iff_isLittleO]
    refine Asymptotics.isLittleO_iff.2 (fun c hc => ?_)
    have hcθ : 0 < c * θ / 12 := div_pos (mul_pos hc hθ) (by norm_num)
    have hc6 : 0 < c / 6 := div_pos hc (by norm_num)
    obtain ⟨δf, hδf, hfball⟩ := Metric.continuousAt_iff.1 hfc (c * θ / 12) hcθ
    obtain ⟨ηd, hηd, hdexp⟩ := mdr_expD_small (w0 := B0094.D ⟨V θ, h⟩) hcθ
    obtain ⟨ηe, hηe, hexp⟩ := mdr_expD_small (w0 := B0012.L0 (V θ)) hc6
    obtain ⟨δw, hδw, hwball⟩ := Metric.continuousAt_iff.1 hw (c / 6) hc6
    have hw'' : ∀ u : ℝ, dist u (-θ) < δw →
        ‖B0012.L0 (V (-u)) - B0012.L0 (V θ)‖ < c / 6 := by
      intro u hu
      have h' := hwball hu
      simp only [neg_neg, dist_eq_norm] at h'
      exact h'
    have hM0 : 0 ≤ ‖B0094.D ⟨V θ, h⟩‖ := norm_nonneg _
    have hκ : 0 < c * θ ^ 2 / (3 * (‖B0094.D ⟨V θ, h⟩‖ + 1)) :=
      div_pos (mul_pos hc (pow_pos hθ 2)) (by linarith)
    have hηdθ : 0 < ηd * θ := mul_pos hηd hθ
    have hηeθ : 0 < ηe * θ := mul_pos hηe hθ
    obtain ⟨δ, hδpos, hδf', hδd', hδe', hδw', hδκ⟩ :
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ δf ∧ δ ≤ ηd * θ ∧ δ ≤ ηe * θ ∧ δ ≤ δw ∧
          δ ≤ c * θ ^ 2 / (3 * (‖B0094.D ⟨V θ, h⟩‖ + 1)) :=
      ⟨min (min (min (min δf (ηd * θ)) (ηe * θ)) δw) (c * θ ^ 2 / (3 * (‖B0094.D ⟨V θ, h⟩‖ + 1))),
        lt_min (lt_min (lt_min (lt_min hδf hηdθ) hηeθ) hδw) hκ,
        (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))),
        (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))),
        (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)),
        (min_le_left _ _).trans (min_le_right _ _),
        min_le_right _ _⟩
    refine eventually_nhdsWithin_iff.2 ?_
    refine Metric.eventually_nhds_iff.2 ⟨δ, hδpos, fun s hs hsθ' => ?_⟩
    have hsθ : θ ≤ s := hsθ'
    have hs' : |s - θ| < δ := by rwa [Real.dist_eq] at hs
    have ht0 : 0 ≤ s - θ := by linarith
    have ht : s - θ < δ := by rwa [abs_of_nonneg ht0] at hs'
    have hs0 : 0 < s := by linarith
    have hDs := hDsub s hs0
    obtain ⟨hL0, hLt, hCb⟩ := mdr_log_bound hθ hsθ
    have hLd : Real.log s - Real.log θ < ηd := by nlinarith
    have hLe : Real.log s - Real.log θ < ηe := by nlinarith
    have hid := mdDuhamel V hV θ s hθ hsθ
    have hE : B0123.expD (Real.log s - Real.log θ) (V s)
        = V s + ∫ u in (0 : ℝ)..(Real.log s - Real.log θ),
            B0123.expD u (B0094.D ⟨V s, hDdom s hs0⟩) :=
      UnforcedLeray.Cons.G3b.expD_integral_generator hL0 ⟨V s, hDdom s hs0⟩
    have hVrel : V s - V θ
        = -(∫ u in (0 : ℝ)..(Real.log s - Real.log θ),
              B0123.expD u (B0094.D ⟨V s, hDdom s hs0⟩))
          - ∫ u in (-s)..(-θ),
              B0123.expD (Real.log (-u) - Real.log θ) (B0012.L0 (V (-u))) := by
      rw [hid, hE]
      abel
    have hF : ContinuousOn (fun u : ℝ => B0123.expD u (B0094.D ⟨V s, hDdom s hs0⟩))
        (uIcc 0 (Real.log s - Real.log θ)) :=
      (UnforcedLeray.Cons.G3b.continuous_expD_apply _).continuousOn
    have hPs := mdr_split hF (B0094.D ⟨V θ, h⟩)
    have hΨ := mdr_integrand_cont hVc hθ (show -s ≤ -θ by linarith)
    have hKs := mdr_split hΨ (B0012.L0 (V θ))
    -- the first remainder `A`
    have hAb : ‖∫ u in (0 : ℝ)..(Real.log s - Real.log θ),
        (B0123.expD u (B0094.D ⟨V s, hDdom s hs0⟩) - B0094.D ⟨V θ, h⟩)‖ ≤ c / 6 * (s - θ) := by
      have hn := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := Real.log s - Real.log θ) (C := c * θ / 6)
        (f := fun u : ℝ => B0123.expD u (B0094.D ⟨V s, hDdom s hs0⟩) - B0094.D ⟨V θ, h⟩)
        (fun r hr => by
          rw [uIoc_of_le hL0] at hr
          have t1 := mdr_expD_triangle r (B0094.D ⟨V s, hDdom s hs0⟩) (B0094.D ⟨V θ, h⟩)
          have t2 : ‖B0094.D ⟨V s, hDdom s hs0⟩ - B0094.D ⟨V θ, h⟩‖ < c * θ / 12 := by
            rw [hDs, hdz]
            have h2 := hfball (x := s)
              (by rw [Real.dist_eq, abs_of_nonneg ht0]; exact lt_of_lt_of_le ht hδf')
            simp only [dist_eq_norm] at h2
            exact h2
          have t3 := hdexp r (by
            rw [abs_of_nonneg hr.1.le]
            exact lt_of_le_of_lt hr.2 hLd)
          show ‖B0123.expD r (B0094.D ⟨V s, hDdom s hs0⟩) - B0094.D ⟨V θ, h⟩‖ ≤ c * θ / 6
          linarith)
      calc _ ≤ c * θ / 6 * |Real.log s - Real.log θ - 0| := hn
        _ = c / 6 * ((Real.log s - Real.log θ) * θ) := by
          rw [sub_zero, abs_of_nonneg hL0]; ring
        _ ≤ c / 6 * (s - θ) := mul_le_mul_of_nonneg_left hLt hc6.le
    -- the second remainder `B`
    have hBb : ‖∫ u in (-s)..(-θ),
        (B0123.expD (Real.log (-u) - Real.log θ) (B0012.L0 (V (-u))) - B0012.L0 (V θ))‖
        ≤ c / 3 * (s - θ) := by
      have hn := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := -s) (b := -θ) (C := c / 3)
        (f := fun u : ℝ =>
          B0123.expD (Real.log (-u) - Real.log θ) (B0012.L0 (V (-u))) - B0012.L0 (V θ))
        (fun u hu => by
          rw [uIoc_of_le (show -s ≤ -θ by linarith)] at hu
          have hu1 : dist u (-θ) < δw := by
            rw [Real.dist_eq, abs_lt]
            constructor <;> linarith [hu.1, hu.2]
          have hpos : 0 < -u := by linarith [hu.2]
          have ha0 : 0 ≤ Real.log (-u) - Real.log θ := by
            have := Real.log_le_log hθ (show θ ≤ -u by linarith [hu.2])
            linarith
          have ha1 : Real.log (-u) - Real.log θ ≤ Real.log s - Real.log θ := by
            have := Real.log_le_log hpos (show -u ≤ s by linarith [hu.1])
            linarith
          have hab : |Real.log (-u) - Real.log θ| < ηe := by
            rw [abs_of_nonneg ha0]
            linarith
          have t1 := mdr_expD_triangle (Real.log (-u) - Real.log θ) (B0012.L0 (V (-u)))
            (B0012.L0 (V θ))
          have t2 := hexp _ hab
          have t3 := hw'' u hu1
          show ‖B0123.expD (Real.log (-u) - Real.log θ) (B0012.L0 (V (-u)))
            - B0012.L0 (V θ)‖ ≤ c / 3
          linarith)
      have e4 : |(-θ) - (-s)| = s - θ := by
        rw [show (-θ) - (-s) = s - θ by ring, abs_of_nonneg ht0]
      calc _ ≤ c / 3 * |(-θ) - (-s)| := hn
        _ = c / 3 * (s - θ) := by rw [e4]
    -- the third remainder `(h - t/θ) • D V θ`
    have hCM : |Real.log s - Real.log θ - (s - θ) / θ| * ‖B0094.D ⟨V θ, h⟩‖
        ≤ c / 3 * (s - θ) := by
      have h3 : (s - θ) * (3 * (‖B0094.D ⟨V θ, h⟩‖ + 1))
          < c * θ ^ 2 := by
        have h' : s - θ < c * θ ^ 2 / (3 * (‖B0094.D ⟨V θ, h⟩‖ + 1)) := lt_of_lt_of_le ht hδκ
        exact (lt_div_iff₀ (by linarith)).1 h'
      have k2 : 3 * ‖B0094.D ⟨V θ, h⟩‖ * (s - θ) ≤ c * θ ^ 2 := by
        nlinarith
      have k3 : |Real.log s - Real.log θ - (s - θ) / θ| * θ ^ 2 * (3 * ‖B0094.D ⟨V θ, h⟩‖)
          ≤ (s - θ) ^ 2 * (3 * ‖B0094.D ⟨V θ, h⟩‖) :=
        mul_le_mul_of_nonneg_right hCb (by positivity)
      have k4 : (s - θ) ^ 2 * (3 * ‖B0094.D ⟨V θ, h⟩‖) ≤ (s - θ) * (c * θ ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_left k2 ht0]
      have k5 : |Real.log s - Real.log θ - (s - θ) / θ| * ‖B0094.D ⟨V θ, h⟩‖ * 3 * θ ^ 2
          ≤ c * (s - θ) * θ ^ 2 := by
        nlinarith [k3, k4]
      have k6 : |Real.log s - Real.log θ - (s - θ) / θ| * ‖B0094.D ⟨V θ, h⟩‖ * 3
          ≤ c * (s - θ) :=
        le_of_mul_le_mul_right (by linarith [k5]) (pow_pos hθ 2)
      linarith
    -- algebraic identity for the remainder
    have hRid : V s - V θ - (s - θ) • (-(B0012.L0 (V θ)) + (-θ⁻¹) • B0094.D ⟨V θ, h⟩)
        = -(∫ u in (-s)..(-θ),
              (B0123.expD (Real.log (-u) - Real.log θ) (B0012.L0 (V (-u))) - B0012.L0 (V θ)))
          - (∫ u in (0 : ℝ)..(Real.log s - Real.log θ),
              (B0123.expD u (B0094.D ⟨V s, hDdom s hs0⟩) - B0094.D ⟨V θ, h⟩))
          - (Real.log s - Real.log θ - (s - θ) / θ) • B0094.D ⟨V θ, h⟩ := by
      rw [hVrel, hPs, hKs]
      module
    try dsimp only
    have hsn : c * ‖s - θ‖ = c * (s - θ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg ht0]
    have hT : ‖-(∫ u in (-s)..(-θ),
              (B0123.expD (Real.log (-u) - Real.log θ) (B0012.L0 (V (-u))) - B0012.L0 (V θ)))
          - (∫ u in (0 : ℝ)..(Real.log s - Real.log θ),
              (B0123.expD u (B0094.D ⟨V s, hDdom s hs0⟩) - B0094.D ⟨V θ, h⟩))
          - (Real.log s - Real.log θ - (s - θ) / θ) • B0094.D ⟨V θ, h⟩‖
        ≤ ‖∫ u in (0 : ℝ)..(Real.log s - Real.log θ),
              (B0123.expD u (B0094.D ⟨V s, hDdom s hs0⟩) - B0094.D ⟨V θ, h⟩)‖
          + ‖∫ u in (-s)..(-θ),
              (B0123.expD (Real.log (-u) - Real.log θ) (B0012.L0 (V (-u))) - B0012.L0 (V θ))‖
          + |Real.log s - Real.log θ - (s - θ) / θ| * ‖B0094.D ⟨V θ, h⟩‖ := by
      have s1 := norm_sub_le
        (-(∫ u in (-s)..(-θ),
              (B0123.expD (Real.log (-u) - Real.log θ) (B0012.L0 (V (-u))) - B0012.L0 (V θ)))
          - (∫ u in (0 : ℝ)..(Real.log s - Real.log θ),
              (B0123.expD u (B0094.D ⟨V s, hDdom s hs0⟩) - B0094.D ⟨V θ, h⟩)))
        ((Real.log s - Real.log θ - (s - θ) / θ) • B0094.D ⟨V θ, h⟩)
      have s2 := norm_sub_le
        (-(∫ u in (-s)..(-θ),
              (B0123.expD (Real.log (-u) - Real.log θ) (B0012.L0 (V (-u))) - B0012.L0 (V θ))))
        (∫ u in (0 : ℝ)..(Real.log s - Real.log θ),
              (B0123.expD u (B0094.D ⟨V s, hDdom s hs0⟩) - B0094.D ⟨V θ, h⟩))
      have s3 : ‖(Real.log s - Real.log θ - (s - θ) / θ) • B0094.D ⟨V θ, h⟩‖
          = |Real.log s - Real.log θ - (s - θ) / θ| * ‖B0094.D ⟨V θ, h⟩‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      have s4 : ‖-(∫ u in (-s)..(-θ),
              (B0123.expD (Real.log (-u) - Real.log θ) (B0012.L0 (V (-u))) - B0012.L0 (V θ)))‖
          = ‖∫ u in (-s)..(-θ),
              (B0123.expD (Real.log (-u) - Real.log θ) (B0012.L0 (V (-u))) - B0012.L0 (V θ))‖ :=
        norm_neg _
      linarith [s1, s2, s3, s4]
    have hnl : 0 ≤ c * (s - θ) := mul_nonneg hc.le ht0
    refine le_trans (le_of_eq (congrArg (fun x : XG => ‖x‖) hRid)) (le_trans hT ?_)
    rw [hsn]
    linarith [hAb, hBb, hCM, hnl]
  have hder : -(B0012.L0 (V θ)) + (-θ⁻¹) • B0094.D ⟨V θ, h⟩
      = -(B0012.L0 (V θ) + ((θ : ℂ)⁻¹) • B0094.D ⟨V θ, h⟩) := by
    have e1 : (-θ⁻¹ : ℝ) • B0094.D ⟨V θ, h⟩
        = (((-θ⁻¹ : ℝ)) : ℂ) • B0094.D ⟨V θ, h⟩ := (Complex.coe_smul _ _).symm
    have e : (-θ⁻¹ : ℝ) • B0094.D ⟨V θ, h⟩ = -(((θ : ℂ)⁻¹) • B0094.D ⟨V θ, h⟩) := by
      rw [e1]
      push_cast
      rw [neg_smul]
    rw [e]
    abel
  exact hderiv.congr_deriv hder

end UnforcedLeray.Short.Spine
