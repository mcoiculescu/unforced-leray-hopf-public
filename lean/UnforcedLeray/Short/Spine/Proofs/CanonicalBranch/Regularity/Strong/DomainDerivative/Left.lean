import UnforcedLeray.Short.Spine.Sub.SP_CAN4_2_1
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Strong.DomainDerivative.Duhamel
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Strong.DomainDerivative.ExpDZero
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Strong.DomainDerivative.ExpDJoint

/-!
# Spine: left one-sided derivative of a mild domain solution (task `Spine:SP-CAN/4/2/1/4`)

Target `MDLeft` (`Sub/SP_CAN4_2_1.lean`). Source: `the November 2 reference manuscript`
line 1086 and lines 1134-1145.

For `0 < s ≤ θ`, `mdDuhamel` gives `V s = e^{(log θ - log s) D} (V θ) + J(s)` with
`J(s) = ∫_{-θ}^{-s} e^{(log(-u) - log s) D} L₀ V(-u) du`. The first term is differentiated by the chain
rule through `hasDerivWithinAt_expD_zero_domain`. For `J`, the little-o estimate is
`J(s) - (θ - s) L₀ V θ = ∫_{-θ}^{-s} (integrand - L₀ V θ) du`, and the integrand is within `c` of
`L₀ V θ` because the exponent `log(-u) - log s` lies in `[0, log θ - log s]` (small) and
`u ↦ L₀ V(-u)` is continuous at `-θ`.

The proof avoids joint continuity on `ℝ × XG`: the splitting
`e^{aD} x - w = e^{aD}(x - w) + (e^{aD} w - w)` with `‖e^{aD}‖ ≤ 1` gives every estimate.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- `(I - D)^0` is the identity. -/
theorem mdl_idpow_eq_self {s : ℝ} (hs : s = 0) (x : XG) (hx : x ∈ (B0123.IDpow s).domain) :
    B0123.IDpow s ⟨x, hx⟩ = x := by
  subst hs
  apply B0094.ext_inner_basis
  intro n
  rw [B0123.inner_IDpow, B0123.idMult]
  simp

/-- `V` is continuous on `(0, ∞)` when it is continuous into `X_{G,0}`. -/
theorem mdl_contOn (V : ℝ → XG) (hC : IsXGjContinuous V) : ContinuousOn V (Ioi 0) := by
  obtain ⟨U, hU, hUc⟩ := hC 0
  refine hUc.congr (fun θ hθ => ?_)
  obtain ⟨h, e⟩ := hU θ hθ
  have h0 := mdl_idpow_eq_self (s := ((0 : ℕ) : ℝ) / 2) (by norm_num) (V θ) h
  exact h0.symm.trans e

/-- The Gaussian part: `s ↦ e^{(log θ - log s) D} z` has derivative `(0 - θ⁻¹) • D z` within `Iic θ`. -/
theorem mdl_gauss {θ : ℝ} (hθ : 0 < θ) (z : B0094.D.domain) :
    HasDerivWithinAt (fun s : ℝ => B0123.expD (Real.log θ - Real.log s) (z : XG))
      ((0 - θ⁻¹) • B0094.D z) (Iic θ) θ := by
  have hlog : HasDerivAt (fun s : ℝ => Real.log θ - Real.log s) (0 - θ⁻¹) θ :=
    (hasDerivAt_const θ (Real.log θ)).sub (Real.hasDerivAt_log hθ.ne')
  have hmaps : MapsTo (fun s : ℝ => Real.log θ - Real.log s) (Ioc 0 θ) (Ici 0) := by
    intro s hs
    have := Real.log_le_log hs.1 hs.2
    show 0 ≤ Real.log θ - Real.log s
    linarith
  have h1 := hasDerivWithinAt_expD_zero_domain z
  have hs0 : Real.log θ - Real.log θ = 0 := sub_self _
  have h2 : HasDerivWithinAt (fun a : ℝ => B0123.expD a (z : XG)) (B0094.D z) (Ici 0)
      (Real.log θ - Real.log θ) := by
    rw [hs0]; exact h1
  have hc := h2.scomp θ hlog.hasDerivWithinAt hmaps
  exact hc.mono_of_mem_nhdsWithin (Ioc_mem_nhdsLE hθ)

/-- Triangle estimate for the exponential: `‖e^{aD} x - w‖ ≤ ‖x - w‖ + ‖e^{aD} w - w‖`. -/
theorem mdl_expD_triangle (a : ℝ) (x w : XG) :
    ‖B0123.expD a x - w‖ ≤ ‖x - w‖ + ‖B0123.expD a w - w‖ := by
  have e : B0123.expD a x - w = B0123.expD a (x - w) + (B0123.expD a w - w) := by
    rw [map_sub]; abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  exact ((B0123.expD a).le_opNorm (x - w)).trans
    (mul_le_of_le_one_left (norm_nonneg _) (B0123.norm_expD_le a))

/-- Small exponents: `‖e^{aD} w0 - w0‖ ≤ ε` for `|a| < η`. -/
theorem mdl_expD_small {w0 : XG} {ε : ℝ} (hε : 0 < ε) :
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

/-- Joint continuity of `(a, x) ↦ e^{aD} x` along two functions, proved without a product space. -/
theorem mdl_joint_at {a : ℝ → ℝ} {w : ℝ → XG} {u0 : ℝ} (ha : ContinuousAt a u0)
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

/-- Continuity of the left integrand in `u` on `[-θ, -s]` for `0 < s ≤ θ`. -/
theorem mdl_integrand_cont {V : ℝ → XG} (hVc : ContinuousOn V (Ioi 0)) {θ s : ℝ} (hs : 0 < s)
    (hle : -θ ≤ -s) :
    ContinuousOn (fun u : ℝ => B0123.expD (Real.log (-u) - Real.log s) (B0012.L0 (V (-u))))
      (uIcc (-θ) (-s)) := by
  intro u hu
  have hu0 : 0 < -u := by
    rw [uIcc_of_le hle] at hu
    linarith [hu.2]
  have hA : ContinuousAt (fun u : ℝ => Real.log (-u) - Real.log s) u :=
    ((continuous_neg.continuousAt).log hu0.ne').sub continuousAt_const
  have hVu : ContinuousAt (fun u : ℝ => V (-u)) u :=
    (hVc.continuousAt (Ioi_mem_nhds hu0)).comp continuous_neg.continuousAt
  have hB : ContinuousAt (fun u : ℝ => B0012.L0 (V (-u))) u :=
    B0012.L0.continuous.continuousAt.comp hVu
  exact (mdl_joint_at hA hB).continuousWithinAt

/-- Subtracting a constant from an integrand. -/
theorem mdl_split {F : ℝ → XG} {a b : ℝ} (hF : ContinuousOn F (uIcc a b)) (L : XG) :
    (∫ u in a..b, F u) = (∫ u in a..b, (F u - L)) + (b - a) • L := by
  rw [intervalIntegral.integral_sub hF.intervalIntegrable intervalIntegrable_const,
    intervalIntegral.integral_const, sub_add_cancel]

set_option maxHeartbeats 1000000 in
/-- Left derivative of the Duhamel integral `J(s) = ∫_{-θ}^{-s} e^{(log(-u) - log s) D} L₀ V(-u) du`
at `θ`, within `Iic θ`, equal to `-(L₀ V θ)`. -/
theorem mdl_J {V : ℝ → XG} (hVc : ContinuousOn V (Ioi 0)) {θ : ℝ} (hθ : 0 < θ) :
    HasDerivWithinAt
      (fun s : ℝ => ∫ u in (-θ)..(-s),
        B0123.expD (Real.log (-u) - Real.log s) (B0012.L0 (V (-u))))
      (-(B0012.L0 (V θ))) (Iic θ) θ := by
  rw [hasDerivWithinAt_iff_isLittleO]
  refine Asymptotics.isLittleO_iff.2 (fun c hc => ?_)
  have hc2 : 0 < c / 2 := by linarith
  have hVθ : ContinuousAt V (-(-θ)) := by
    rw [neg_neg]; exact hVc.continuousAt (Ioi_mem_nhds hθ)
  have hw : ContinuousAt (fun u : ℝ => B0012.L0 (V (-u))) (-θ) :=
    B0012.L0.continuous.continuousAt.comp (hVθ.comp continuous_neg.continuousAt)
  obtain ⟨δ1, hδ1, hwball⟩ := Metric.continuousAt_iff.1 hw (c / 2) hc2
  have hw' : ∀ u : ℝ, dist u (-θ) < δ1 →
      ‖B0012.L0 (V (-u)) - B0012.L0 (V θ)‖ < c / 2 := by
    intro u hu
    have h := hwball hu
    simp only [neg_neg, dist_eq_norm] at h
    exact h
  obtain ⟨η, hη, hexp⟩ := mdl_expD_small (w0 := B0012.L0 (V θ)) hc2
  have hηθ : 0 < η * θ / 2 := div_pos (mul_pos hη hθ) two_pos
  obtain ⟨δ, hδpos, hδa, hδb, hδc⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ1 ∧ δ ≤ θ / 2 ∧ δ ≤ η * θ / 2 :=
    ⟨min (min δ1 (θ / 2)) (η * θ / 2), lt_min (lt_min hδ1 (by linarith)) hηθ,
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      min_le_right _ _⟩
  refine eventually_nhdsWithin_iff.2 ?_
  refine Metric.eventually_nhds_iff.2 ⟨δ, hδpos, fun s hs hsθ' => ?_⟩
  have hsθ : s ≤ θ := hsθ'
  have hs' : |s - θ| < δ := by rwa [Real.dist_eq] at hs
  have hsabs : -δ < s - θ ∧ s - θ < δ := abs_lt.1 hs'
  have hs2 : θ / 2 ≤ s := by linarith [hsabs.1]
  have hspos : 0 < s := by linarith
  have hle : -θ ≤ -s := by linarith
  have hes : η * (θ / 2) ≤ η * s := mul_le_mul_of_nonneg_left hs2 hη.le
  have hlog : Real.log θ - Real.log s < η := by
    have h1 : Real.log (θ / s) ≤ θ / s - 1 := Real.log_le_sub_one_of_pos (div_pos hθ hspos)
    rw [Real.log_div hθ.ne' hspos.ne'] at h1
    have h2 : θ / s < 1 + η := by
      rw [div_lt_iff₀ hspos]
      nlinarith
    linarith
  have hbound : ∀ u ∈ Ioc (-θ) (-s),
      ‖B0123.expD (Real.log (-u) - Real.log s) (B0012.L0 (V (-u))) - B0012.L0 (V θ)‖ ≤ c := by
    intro u hu
    have hu1 : dist u (-θ) < δ1 := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1, hu.2, hsabs.1, hsabs.2, hδa]
    have hpos : 0 < -u := by linarith [hu.2]
    have ha0 : 0 ≤ Real.log (-u) - Real.log s := by
      have := Real.log_le_log hspos (show s ≤ -u by linarith [hu.2])
      linarith
    have ha1 : Real.log (-u) - Real.log s < η := by
      have := Real.log_le_log hpos (show -u ≤ θ by linarith [hu.1])
      linarith
    have hab : |Real.log (-u) - Real.log s| < η := by
      rw [abs_lt]; constructor <;> linarith
    have h1 := mdl_expD_triangle (Real.log (-u) - Real.log s) (B0012.L0 (V (-u)))
      (B0012.L0 (V θ))
    have h2 := hexp _ hab
    have h3 := hw' u hu1
    linarith
  have hcont := mdl_integrand_cont hVc hspos hle
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -θ) (b := -s) (C := c)
    (f := fun u : ℝ =>
      B0123.expD (Real.log (-u) - Real.log s) (B0012.L0 (V (-u))) - B0012.L0 (V θ))
    (fun u hu => by
      rw [uIoc_of_le hle] at hu
      exact hbound u hu)
  have hsplit := mdl_split hcont (B0012.L0 (V θ))
  have e2 : (-s - -θ) = -(s - θ) := by ring
  have hkey : ∀ I : XG, I + (-s - -θ) • B0012.L0 (V θ) - 0 - (s - θ) • (-(B0012.L0 (V θ)))
      = I := fun I => by module
  try dsimp only
  rw [intervalIntegral.integral_same, hsplit, hkey]
  rw [e2, abs_neg] at hnorm
  simp only [Real.norm_eq_abs]
  exact hnorm

/-- **Left derivative** (shorter proof lines 1134-1145): `MDLeft`. -/
theorem mdLeft : MDLeft := by
  intro _hE V hV hC θ hθ h
  have hVc := mdl_contOn V hC
  have hG := mdl_gauss hθ ⟨V θ, h⟩
  have hJ := mdl_J hVc hθ
  have hsum := hG.add hJ
  have hid : ∀ s : ℝ, 0 < s → s ≤ θ →
      V s = B0123.expD (Real.log θ - Real.log s) (V θ) +
        ∫ u in (-θ)..(-s), B0123.expD (Real.log (-u) - Real.log s) (B0012.L0 (V (-u))) :=
    fun s hs hsθ => mdDuhamel V hV s θ hs hsθ
  have hev : V =ᶠ[𝓝[Iic θ] θ] (fun s : ℝ => B0123.expD (Real.log θ - Real.log s) (V θ) +
        ∫ u in (-θ)..(-s), B0123.expD (Real.log (-u) - Real.log s) (B0012.L0 (V (-u)))) := by
    filter_upwards [Ioc_mem_nhdsLE hθ] with s hs
    exact hid s hs.1 hs.2
  have hx := hid θ hθ le_rfl
  have hres := hsum.congr_of_eventuallyEq hev hx
  have hder : (0 - θ⁻¹) • B0094.D ⟨V θ, h⟩ + -(B0012.L0 (V θ))
      = -(B0012.L0 (V θ) + ((θ : ℂ)⁻¹) • B0094.D ⟨V θ, h⟩) := by
    have e1 : (0 - θ⁻¹ : ℝ) • B0094.D ⟨V θ, h⟩
        = (((0 - θ⁻¹ : ℝ)) : ℂ) • B0094.D ⟨V θ, h⟩ := (Complex.coe_smul _ _).symm
    have e : (0 - θ⁻¹ : ℝ) • B0094.D ⟨V θ, h⟩ = -(((θ : ℂ)⁻¹) • B0094.D ⟨V θ, h⟩) := by
      rw [e1]
      push_cast
      rw [zero_sub, neg_smul]
    rw [e]
    abel
  exact hres.congr_deriv hder

end UnforcedLeray.Short.Spine
