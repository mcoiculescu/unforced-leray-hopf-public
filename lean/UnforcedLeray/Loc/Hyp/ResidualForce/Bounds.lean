import UnforcedLeray.Loc.Hyp.ResidualForce.Continuity

/-!
# `H-Residual`, helpers: pointwise bounds for `H_h[u_dss]` and the heat tail

Support for `Loc/Hyp/ResidualForce.lean` (`paper/main.tex` lines 474–491, blueprint B0722).

* `H = H_h[u_dss]` (line 160): `u_dss` is smooth off zero with `|D^k u_dss| ≤ C|x|^{-1-k}`
  (lines 155–156, package field `udss_bounds`), so `u_dss ∈ 𝒦₂(C)` and the compiled
  `Heat.simHeat_decay` (B0710, tex 275–278) gives `|D^a H(y,τ)| ≤ C(1 + |y|)^{-1-a}`, `a ≤ 2`,
  uniformly in `τ` (`heatProfile_decayW`). This is the decay `|D^j H| ≤ C⟨y⟩^{-1-j}`.
* `K_loc = H_h[d_loc]`, `d_loc = u₀ - u_dss` (line 446). The defect vanishes near zero
  (`IsCompactDatum.agrees_near_zero`) and equals `-u_dss` outside the support of `u₀`, so its
  smoothing `d̃` across zero (`L09.smoothDefect`) is `C^∞` with
  `|D^b d̃(x)| ≤ M(1 + |x|)^{-1-b}`, `b ≤ 2` (`defect_weighted`). Derivatives commute with the
  heat flow (`Heat.iteratedFDeriv_average`) and the flow preserves the weight for heat times
  `t ≤ h` (`Heat.norm_average_le_weight`, Peetre), so with `δ = e^{τ/4}` (`δ² = √t/√h`):
  `|D^b K_loc(y,τ)| ≤ C δ^{2b+2}(1 + δ²|y|)^{-1-b}` for `τ ≤ 0` (`tail_decayK`). This one
  bound contains both the super-polynomial smallness on the inner ball and the `⟨x⟩^{-1-b}`
  decay outside it used at lines 479–484.

Main declarations: `udss_invDistClass`, `heatProfile_decayW`, `defect_weighted`,
`heatTail_eq`, `tail_decayK`, `DecayW.add_smul`, `dpart_add_smul`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.ResidualForceHyp

open UnforcedLeray.Blueprint UnforcedLeray.Blueprint.L10

theorem rpow_neg_nat_eq (y : Space) (n : ℕ) :
    (1 + ‖y‖) ^ (-(n : ℝ)) = 1 / (1 + ‖y‖) ^ n := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, one_div]

/-! ## `H_h[u_dss]` -/

/-- `u_dss ∈ 𝒦₂(C)` (lines 152–156). -/
theorem udss_invDistClass {B : BackgroundCore} (hB : IsExactBackground B) :
    ∃ C : ℝ, Heat.InvDistClass 2 C B.udss := by
  obtain ⟨C0, hC0⟩ := hB.udss_bounds 0 (by norm_num)
  obtain ⟨C1, hC1⟩ := hB.udss_bounds 1 (by norm_num)
  obtain ⟨C2, hC2⟩ := hB.udss_bounds 2 (by norm_num)
  set C := max C0 (max C1 C2) with hCdef
  refine ⟨C, ⟨contDiffOn_infty.mp hB.udss_smooth 2, fun j hj x hx => ?_⟩⟩
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have key : ∀ (k : ℕ) (Ck : ℝ), Ck ≤ C →
      (∀ x : Space, x ≠ 0 → ‖iteratedFDeriv ℝ k B.udss x‖ * ‖x‖ ^ (k + 1) ≤ Ck) →
      ‖iteratedFDeriv ℝ k B.udss x‖ ≤ C * ‖x‖ ^ (-(1 + k : ℝ)) := by
    intro k Ck hCk h
    have h1 := h x hx
    rw [Real.rpow_neg hx0.le, show (1 + k : ℝ) = ((k + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact h1.trans hCk
  interval_cases j
  · exact key 0 C0 (le_max_left _ _) hC0
  · exact key 1 C1 ((le_max_left _ _).trans (le_max_right _ _)) hC1
  · exact key 2 C2 ((le_max_right _ _).trans (le_max_right _ _)) hC2

/-- `|u_dss(x)| ≤ C|x|^{-1}` and continuity off zero. -/
theorem udss_invBound {B : BackgroundCore} (hB : IsExactBackground B) :
    ∃ C : ℝ, InvBound B.udss C := by
  obtain ⟨C, hC⟩ := udss_invDistClass hB
  refine ⟨C, hB.udss_smooth.continuousOn, fun x hx => ?_⟩
  have h := hC.bound 0 (by norm_num) x hx
  rwa [norm_iteratedFDeriv_zero, Nat.cast_zero, add_zero, Real.rpow_neg_one] at h

/-- **The decay of `H_h[u_dss]`** (B0710): `DecayW` uniformly in `τ ∈ ℝ`. -/
theorem heatProfile_decayW {B : BackgroundCore} (hB : IsExactBackground B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, DecayW (heatProfile B.h B.udss τ) C := by
  obtain ⟨Cu, hCu⟩ := udss_invDistClass hB
  obtain ⟨K0, hK0⟩ := Heat.simHeat_decay hB.h_pos hCu (j := 0) (by norm_num)
  obtain ⟨K1, hK1⟩ := Heat.simHeat_decay hB.h_pos hCu (j := 1) (by norm_num)
  obtain ⟨K2, hK2⟩ := Heat.simHeat_decay hB.h_pos hCu (j := 2) (by norm_num)
  set C := max 0 (max K0 (max K1 K2)) with hCdef
  refine ⟨C, le_max_left _ _, fun τ y => ?_⟩
  have hp : 0 < 1 + ‖y‖ := by positivity
  have e : heatProfile B.h B.udss τ = Heat.simHeat B.h B.udss τ := rfl
  have b0 := hK0 τ y
  have b1 := hK1 τ y
  have b2 := hK2 τ y
  rw [← e, rpow_neg_nat_eq] at b0 b1 b2
  rw [norm_iteratedFDeriv_zero] at b0
  rw [norm_iteratedFDeriv_one] at b1
  norm_num at b0 b1 b2
  refine ⟨b0.trans ?_, b1.trans ?_, b2.trans ?_⟩
  · rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (le_max_of_le_right (le_max_left _ _)) hp.le
  · rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))) (by positivity)
  · rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right
      (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))) (by positivity)

theorem heatProfile_contDiff {B : BackgroundCore} (hB : IsExactBackground B) (τ : ℝ) :
    ContDiff ℝ ∞ (heatProfile B.h B.udss τ) := by
  obtain ⟨C, hC⟩ := udss_invBound hB
  exact Heat.simHeat_contDiff hB.h_pos hC.heatAdmissible τ

/-! ## The defect and the heat tail -/

section Defect

variable {D : BackgroundData} {u₀ : SpatialField}

/-- The radius on which `d_loc = u₀ - u_dss` vanishes (line 452). -/
theorem defect_vanishes (hu : IsCompactDatum D u₀) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : Space, x ≠ 0 → ‖x‖ < r → (u₀ - D.udss) x = 0 := by
  obtain ⟨r, hr, h⟩ := hu.agrees_near_zero
  exact ⟨r, hr, fun x hx hxr => by rw [Pi.sub_apply, h x hx hxr, sub_self]⟩

theorem defect_smooth (hD : IsUnstableBackground D) (hu : IsCompactDatum D u₀) :
    ContDiffOn ℝ ∞ (u₀ - D.udss) {0}ᶜ :=
  hu.smooth_away.sub hD.background.udss_smooth

/-- **The smoothed defect has weighted derivative bounds**: `|D^b d̃(x)|(1 + |x|)^{b+1} ≤ M`
for `b ≤ 4` (lines 155, 446–452). -/
theorem defect_weighted (hD : IsUnstableBackground D) (hu : IsCompactDatum D u₀) {r : ℝ}
    (hr : 0 < r) (hd0 : ∀ x : Space, x ≠ 0 → ‖x‖ < r → (u₀ - D.udss) x = 0) (b : ℕ)
    (hb : b ≤ 4) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Space,
      ‖iteratedFDeriv ℝ b (L09.smoothDefect r (u₀ - D.udss)) x‖ * (1 + ‖x‖) ^ (b + 1) ≤ M := by
  set d := u₀ - D.udss with hd
  have hs : ContDiff ℝ ∞ (L09.smoothDefect r d) :=
    L09.smoothDefect_contDiff hr hd0 (defect_smooth hD hu)
  obtain ⟨R, hR⟩ : ∃ R : ℝ, tsupport u₀ ⊆ Metric.closedBall (0 : Space) R :=
    hu.datum.compact.isCompact.isBounded.subset_closedBall 0
  set R' := max R 1 with hR'
  have hR'1 : 1 ≤ R' := le_max_right _ _
  obtain ⟨Ck, hCk⟩ := hD.background.udss_bounds b hb
  have hcont : Continuous (iteratedFDeriv ℝ b (L09.smoothDefect r d)) :=
    hs.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨M₁, hM₁⟩ := (isCompact_closedBall (0 : Space) R').exists_bound_of_continuousOn
    hcont.continuousOn
  set M := max 0 (max (M₁ * (1 + R') ^ (b + 1)) (Ck * 2 ^ (b + 1))) with hM
  refine ⟨M, le_max_left _ _, fun x => ?_⟩
  by_cases hx : ‖x‖ ≤ R'
  · have h1 := hM₁ x (by simpa using hx)
    have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans h1
    calc ‖iteratedFDeriv ℝ b (L09.smoothDefect r d) x‖ * (1 + ‖x‖) ^ (b + 1)
        ≤ M₁ * (1 + R') ^ (b + 1) :=
          mul_le_mul h1 (pow_le_pow_left₀ (by positivity) (by linarith) _) (by positivity) hM₁0
      _ ≤ M := le_max_of_le_right (le_max_left _ _)
  · rw [not_le] at hx
    have hx1 : 1 ≤ ‖x‖ := hR'1.trans hx.le
    have hx0 : x ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hx1; linarith
    have hxs : x ∉ tsupport u₀ := by
      intro hm
      have := hR hm
      rw [Metric.mem_closedBall, dist_zero_right] at this
      linarith [le_max_left R 1]
    have hu0 : u₀ =ᶠ[𝓝 x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hxs
    have heq : L09.smoothDefect r d =ᶠ[𝓝 x] -D.udss := by
      filter_upwards [L09.smoothDefect_eventuallyEq hd0 hx0, hu0] with z hz hz0
      rw [hz, hd, Pi.sub_apply, hz0, zero_sub, Pi.neg_apply]
    rw [(heq.iteratedFDeriv ℝ b).eq_of_nhds, iteratedFDeriv_neg_apply, norm_neg]
    have h1 := hCk x hx0
    have h2 : (1 + ‖x‖) ^ (b + 1) ≤ 2 ^ (b + 1) * ‖x‖ ^ (b + 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    calc ‖iteratedFDeriv ℝ b D.udss x‖ * (1 + ‖x‖) ^ (b + 1)
        ≤ ‖iteratedFDeriv ℝ b D.udss x‖ * (2 ^ (b + 1) * ‖x‖ ^ (b + 1)) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = (‖iteratedFDeriv ℝ b D.udss x‖ * ‖x‖ ^ (b + 1)) * 2 ^ (b + 1) := by ring
      _ ≤ Ck * 2 ^ (b + 1) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ M := le_max_of_le_right (le_max_right _ _)

/-- `K_loc(τ) = H_h[d̃](τ)`: the heat average does not see the value of `d_loc` at `0`. -/
theorem heatTail_eq {r : ℝ} (hd0 : ∀ x : Space, x ≠ 0 → ‖x‖ < r → (u₀ - D.udss) x = 0)
    (τ : ℝ) : heatTail D u₀ τ = heatProfile D.h (L09.smoothDefect r (u₀ - D.udss)) τ :=
  L09.heatProfile_smoothDefect hd0 D.h τ

/-- **The heat tail at scale `δ = e^{τ/4}`** (`loc:eq:heat-correction` refined, lines 455–458,
479–484): `DecayK (K_loc(τ)) C δ` for every `τ ≤ 0`. -/
theorem tail_decayK (hD : IsUnstableBackground D) (hu : IsCompactDatum D u₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, τ ≤ 0 → DecayK (heatTail D u₀ τ) C (Real.exp (τ / 4)) := by
  obtain ⟨r, hr, hd0⟩ := defect_vanishes hu
  set d := L09.smoothDefect r (u₀ - D.udss) with hd
  have hs : ContDiff ℝ ∞ d := L09.smoothDefect_contDiff hr hd0 (defect_smooth hD hu)
  obtain ⟨M0, hM00, hM0⟩ := defect_weighted hD hu hr hd0 0 (by norm_num)
  obtain ⟨M1, hM10, hM1⟩ := defect_weighted hD hu hr hd0 1 (by norm_num)
  obtain ⟨M2, hM20, hM2⟩ := defect_weighted hD hu hr hd0 2 (by norm_num)
  set M := max M0 (max M1 M2) with hMdef
  have hM : ∀ b ≤ 2, ∀ x : Space, ‖iteratedFDeriv ℝ b d x‖ * (1 + ‖x‖) ^ (b + 1) ≤ M := by
    intro b hb x
    interval_cases b
    · exact (hM0 x).trans (le_max_left _ _)
    · exact (hM1 x).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (hM2 x).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hM0' : 0 ≤ M := hM00.trans (le_max_left _ _)
  have hbdd : ∀ k ≤ 2, ∀ x : Space, ‖iteratedFDeriv ℝ k d x‖ ≤ M := by
    intro k hk x
    have h1 := hM k hk x
    have h2 : 1 ≤ (1 + ‖x‖) ^ (k + 1) := one_le_pow₀ (by linarith [norm_nonneg x])
    nlinarith [norm_nonneg (iteratedFDeriv ℝ k d x)]
  have hw : ∀ b ≤ 2, ∀ x : Space,
      ‖iteratedFDeriv ℝ b d x‖ ≤ M * (1 + ‖x‖) ^ (-((b : ℝ) + 1)) := by
    intro b hb x
    have h1 := hM b hb x
    have e : (1 + ‖x‖) ^ (-((b : ℝ) + 1)) = 1 / (1 + ‖x‖) ^ (b + 1) := by
      rw [show ((b : ℝ) + 1) = ((b + 1 : ℕ) : ℝ) by push_cast; ring, rpow_neg_nat_eq]
    rw [e, mul_one_div, le_div_iff₀ (by positivity)]
    exact h1
  set mc := max (Heat.momentConst 1 D.h) (max (Heat.momentConst 2 D.h) (Heat.momentConst 3 D.h))
    with hmc
  have hmc0 : 0 ≤ mc := (Heat.momentConst_nonneg _).trans (le_max_left _ _)
  have hh := hD.background.h_pos
  -- the key estimate for each order `b ≤ 2`
  have key : ∀ τ : ℝ, τ ≤ 0 → ∀ b ≤ 2, ∀ y : Space,
      ‖iteratedFDeriv ℝ b (heatTail D u₀ τ) y‖ ≤
        mc * M * Real.exp (τ / 4) ^ (2 * b + 2) / (1 + Real.exp (τ / 4) ^ 2 * ‖y‖) ^ (b + 1) := by
    intro τ hτ b hb y
    set δ := Real.exp (τ / 4) with hδ
    have hδ0 : 0 < δ := Real.exp_pos _
    have hε : Real.exp (τ / 2) = δ ^ 2 := by
      rw [hδ, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have ht : 0 < D.h * Real.exp τ := mul_pos hh (Real.exp_pos τ)
    have htle : D.h * Real.exp τ ≤ D.h :=
      mul_le_of_le_one_right hh.le (Real.exp_le_one_iff.mpr hτ)
    have e1 : heatTail D u₀ τ =
        fun y => Real.exp (τ / 2) • Heat.average (D.h * Real.exp τ) d (Real.exp (τ / 2) • y) :=
      L09.heatProfile_smoothDefect hd0 D.h τ
    rw [e1, Gaussian.iteratedFDeriv_comp_smul b (Heat.average (D.h * Real.exp τ) d)
      (Real.exp (τ / 2)) (Real.exp (τ / 2)) y, norm_smul,
      Heat.iteratedFDeriv_average ht (n := 2) (contDiff_infty.mp hs 2) hbdd b hb]
    have hav := Heat.norm_average_le_weight ht htle (hw b hb) (Real.exp (τ / 2) • y)
    have habs : |(-((b : ℝ) + 1))| = (b : ℝ) + 1 := by
      rw [abs_neg, abs_of_pos (by positivity)]
    rw [habs, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, hε] at hav
    have hmcb : Heat.momentConst ((b : ℝ) + 1) D.h ≤ mc := by
      interval_cases b
      · norm_num [hmc]
      · norm_num [hmc]
      · norm_num [hmc]
    have hpow : (1 + δ ^ 2 * ‖y‖) ^ (-((b : ℝ) + 1)) = 1 / (1 + δ ^ 2 * ‖y‖) ^ (b + 1) := by
      rw [Real.rpow_neg (by positivity), show ((b : ℝ) + 1) = ((b + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast, one_div]
    rw [hpow] at hav
    rw [Real.norm_of_nonneg (by positivity), hε]
    calc δ ^ 2 * (δ ^ 2) ^ b * ‖Heat.average (D.h * Real.exp τ) (iteratedFDeriv ℝ b d)
          (δ ^ 2 • y)‖
        ≤ δ ^ 2 * (δ ^ 2) ^ b * (Heat.momentConst ((b : ℝ) + 1) D.h * M *
          (1 / (1 + δ ^ 2 * ‖y‖) ^ (b + 1))) :=
          mul_le_mul_of_nonneg_left hav (by positivity)
      _ ≤ δ ^ 2 * (δ ^ 2) ^ b * (mc * M * (1 / (1 + δ ^ 2 * ‖y‖) ^ (b + 1))) := by
          gcongr
      _ = mc * M * δ ^ (2 * b + 2) / (1 + δ ^ 2 * ‖y‖) ^ (b + 1) := by
          rw [← pow_mul]; ring
  refine ⟨mc * M, mul_nonneg hmc0 hM0', fun τ hτ y => ⟨?_, ?_, ?_⟩⟩
  · have h := key τ hτ 0 (by norm_num) y
    rw [norm_iteratedFDeriv_zero] at h
    simpa using h
  · have h := key τ hτ 1 (by norm_num) y
    rw [norm_iteratedFDeriv_one] at h
    simpa using h
  · have h := key τ hτ 2 (by norm_num) y
    simpa using h

/-- The smoothed defect is a `|x|^{-1}` field (for the phase continuity of `K_loc`). -/
theorem defect_invBound (hD : IsUnstableBackground D) (hu : IsCompactDatum D u₀) {r : ℝ}
    (hr : 0 < r) (hd0 : ∀ x : Space, x ≠ 0 → ‖x‖ < r → (u₀ - D.udss) x = 0) :
    ∃ C : ℝ, InvBound (L09.smoothDefect r (u₀ - D.udss)) C := by
  have hs := L09.smoothDefect_contDiff hr hd0 (defect_smooth hD hu)
  obtain ⟨M, hM0, hM⟩ := defect_weighted hD hu hr hd0 0 (by norm_num)
  refine ⟨M, hs.continuous.continuousOn, fun x hx => ?_⟩
  have h := hM x
  rw [norm_iteratedFDeriv_zero, zero_add, pow_one] at h
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [← div_eq_mul_inv, le_div_iff₀ hx0]
  nlinarith [norm_nonneg (L09.smoothDefect r (u₀ - D.udss) x)]

end Defect

/-! ## `W = H + ½ K` -/

theorem dpart_add_smul {F G : SpatialField} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (c : ℝ) (i : Fin 3) :
    dpart (F + c • G) i = fun y => dpart F i y + c • dpart G i y := by
  funext y
  unfold dpart
  rw [fderiv_add (hF y) ((hG y).const_smul c), fderiv_const_smul (hG y) c]
  rfl

theorem dpart_dpart_add_smul {F G : SpatialField} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (c : ℝ) (i l : Fin 3) (y : Space) :
    dpart (dpart (F + c • G) i) l y = dpart (dpart F i) l y + c • dpart (dpart G i) l y := by
  rw [dpart_add_smul (hF.differentiable (by simp)) (hG.differentiable (by simp)) c i]
  have e : (fun y => dpart F i y + c • dpart G i y) = dpart F i + c • dpart G i := rfl
  rw [e, dpart_add_smul ((contDiff_dpart hF i).differentiable (by simp))
    ((contDiff_dpart hG i).differentiable (by simp)) c l]

theorem DecayW.add_smul {F G : SpatialField} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    {C₁ C₂ c : ℝ} (hc : |c| ≤ 1) (hC₂ : 0 ≤ C₂) (hFd : DecayW F C₁) (hGd : DecayW G C₂) :
    DecayW (F + c • G) (C₁ + C₂) := by
  intro y
  obtain ⟨f0, f1, f2⟩ := hFd y
  obtain ⟨g0, g1, g2⟩ := hGd y
  have hp : 0 < 1 + ‖y‖ := by positivity
  have hcG : ∀ a : ℝ, 0 ≤ a → |c| * a ≤ a := fun a ha => mul_le_of_le_one_left ha hc
  refine ⟨?_, ?_, ?_⟩
  · rw [Pi.add_apply, Pi.smul_apply]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, add_div]
    have := hcG (C₂ / (1 + ‖y‖)) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left g0 (abs_nonneg c)]
  · rw [fderiv_add (hF.differentiable (by simp) y)
      ((hG.differentiable (by simp) y).const_smul c),
      fderiv_const_smul (hG.differentiable (by simp) y) c]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, add_div]
    have := hcG (C₂ / (1 + ‖y‖) ^ 2) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left g1 (abs_nonneg c)]
  · have hF2 : ContDiffAt ℝ 2 F y := (contDiff_infty.mp hF 2).contDiffAt
    have hG2 : ContDiffAt ℝ 2 G y := (contDiff_infty.mp hG 2).contDiffAt
    have hcG2 : ContDiffAt ℝ 2 (c • G) y := hG2.const_smul c
    rw [iteratedFDeriv_add_apply hF2 hcG2, iteratedFDeriv_const_smul_apply hG2]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, add_div]
    have := hcG (C₂ / (1 + ‖y‖) ^ 3) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left g2 (abs_nonneg c)]

end UnforcedLeray.ResidualForceHyp
