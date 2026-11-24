import UnforcedLeray.Short.PartIIb.Tasks.StrongFirstDerivative.DifferentiatedEquation.QuadBound.InletHess

/-!
# Global quantitative bounds on the affine inlet (helper for `PartII-b:S1/1/2`)

Source `the November 2 reference manuscript`, lines
2385-2387, 2528-2531.

* `inlet_dydy_phaseLpNorm_le`: `‖∂_j∂_l e‖_{Y_{q₀}} ≤ C ν^{-k} ‖z‖` for `e = E_bg α`, `α = coord z`
  (ring envelope `inlet_dydy_ptw`, `eLpNorm_le_of_ringEnv1`, `R^{8/11} ‖α‖ ≤ ‖z‖`).
* `inlet_sup_le`: `‖e‖ ≤ C ν^{-k} ‖z‖` and `‖∂_j e‖ ≤ C ν^{-k} ‖z‖` at every point.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.QuadBoundSub

open UnforcedLeray.PhaseSpace UnforcedLeray.Blueprint UnforcedLeray.B0412 UnforcedLeray.Axi
open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Short.PartIIIb.Concrete.ES326Inlet

/-- Global `Y_{q₀}` bound on the inlet Hessian. -/
theorem inlet_dydy_phaseLpNorm_le
    (Sig : ℝ) (lam : ℂ) (q : Planar.Profile) (hSig : 0 < Sig)
    (hq : Planar.IsGrowingEigenpair lam q) (dm dp : ℝ) (hdm : 0 < dm) :
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
        ∀ (z : p.Z) (j l : Fin 3),
          phaseLpNorm p.period bgp (dy j (dy l (p.eFun (p.coord z)))) ≤
            ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * ‖z‖) := by
  obtain ⟨B, κ, k, ν₀, hB, hκ, hν₀, hν₀1, HP⟩ := inlet_dydy_ptw Sig lam q hSig hq dm dp hdm
  obtain ⟨K, hK, HK⟩ := eLpNorm_le_of_ringEnv1 2 hκ
  have hSig0 : 0 < 1 + Sig := by linarith
  refine ⟨K * B * (1 + Sig) ^ 4, k + 10, ν₀, by positivity, hν₀, hν₀1, ?_⟩
  intro p d hreg hν hS hm z j l
  have hνpos : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ 1 := hν.trans hν₀1
  set u : ℝ := p.ν⁻¹ with hu
  have hu1 : 1 ≤ u := by
    rw [hu]
    exact (one_le_inv₀ hνpos).2 hν1
  have hpow : ∀ m : ℕ, (p.ν ^ m)⁻¹ = u ^ m := fun m => by rw [hu, inv_pow]
  have hc : p.c = u ^ 2 := by rw [hreg.c_eq, hpow]
  have hc1 : 1 ≤ p.c := by
    rw [hc]
    exact one_le_pow₀ hu1
  have hHpos : 0 < p.H := p.H_pos
  have hH : 1 + p.H ≤ (1 + Sig) * u := by
    have e : p.H = Sig * u := by
      rw [Params.H, hS, hu, div_eq_mul_inv]
    rw [e]
    nlinarith
  have hRpos : 0 < p.R := p.R_pos
  refine phaseLpNorm_bgp_le_of_slice p.period_pos (by positivity) fun τ => ?_
  have hM : 0 ≤ B * (1 + p.H) ^ 3 * (p.ν ^ k)⁻¹ * ‖p.coord z‖ := by positivity
  refine (HK p.R p.c p.H _ (fun y => dy j (dy l (p.eFun (p.coord z))) (τ, y)) hRpos hc1 hHpos hM
    (HP p d hreg hν hS hm (p.coord z) j l τ)).trans (ENNReal.ofReal_le_ofReal ?_)
  have hRz : p.R ^ (8 / 11 : ℝ) * ‖p.coord z‖ ≤ ‖z‖ := R_rpow_mul_norm_coord_le p z
  have hH0 : 0 ≤ 1 + p.H := by linarith
  rw [hpow, hpow, hc]
  calc K * (B * (1 + p.H) ^ 3 * u ^ k * ‖p.coord z‖) * (1 + p.H) * (u ^ 2) ^ (2 + 1) *
        p.R ^ (8 / 11 : ℝ)
      = K * B * (1 + p.H) ^ 4 * u ^ k * (u ^ 2) ^ 3 *
          (p.R ^ (8 / 11 : ℝ) * ‖p.coord z‖) := by ring
    _ ≤ K * B * ((1 + Sig) * u) ^ 4 * u ^ k * (u ^ 2) ^ 3 * ‖z‖ := by
        gcongr
    _ = K * B * (1 + Sig) ^ 4 * u ^ (k + 10) * ‖z‖ := by ring

/-- `(1 + x) e^{-a x} ≤ 1 + 1/a` for `x ≥ 0`, `a > 0`. -/
theorem one_add_mul_exp_le {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    (1 + x) * Real.exp (-(a * x)) ≤ 1 + 1 / a := by
  have h1 : a * x + 1 ≤ Real.exp (a * x) := Real.add_one_le_exp (a * x)
  have hE : 0 < Real.exp (a * x) := Real.exp_pos _
  have hx' : (1 / a) * (a * x) = x := by field_simp
  have hax : 0 ≤ a * x := mul_nonneg ha.le hx
  have hia : 0 < 1 / a := by positivity
  have h2 : 1 + x ≤ (1 + 1 / a) * Real.exp (a * x) := by
    calc 1 + x ≤ a * x + 1 + (1 / a) * (a * x) + 1 / a := by rw [hx']; linarith
      _ = (1 + 1 / a) * (a * x + 1) := by ring
      _ ≤ (1 + 1 / a) * Real.exp (a * x) := mul_le_mul_of_nonneg_left h1 (by positivity)
  rw [Real.exp_neg]
  calc (1 + x) * (Real.exp (a * x))⁻¹ ≤ ((1 + 1 / a) * Real.exp (a * x)) * (Real.exp (a * x))⁻¹ :=
        mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 hE.le)
    _ = 1 + 1 / a := by field_simp

/-- Supremum of the linear ring envelope. -/
theorem ringEnv1_one_le {H M κ c : ℝ} (hH : 0 < H) (hM : 0 ≤ M) (hκ : 0 < κ) (hc : 0 < c)
    (s η : ℝ) : ringEnv1 H M κ c 1 s η ≤ M * (H / 2) * (1 + c / κ) := by
  have hR0 : 0 ≤ M * (H / 2) * (1 + c / κ) := by positivity
  unfold ringEnv1
  by_cases hs : s ∈ Ioc 0 (H / 2)
  · rw [indicator_of_mem hs, pow_one]
    have hexp : (1 + |η|) * Real.exp (-(κ * |η| / c)) ≤ 1 + c / κ := by
      have h := one_add_mul_exp_le (a := κ / c) (x := |η|) (by positivity) (abs_nonneg η)
      have e1 : κ / c * |η| = κ * |η| / c := by ring
      have e2 : 1 / (κ / c) = c / κ := by field_simp
      rw [e1, e2] at h
      exact h
    have hMs : M * s ≤ M * (H / 2) := mul_le_mul_of_nonneg_left hs.2 hM
    have hp : 0 ≤ (1 + |η|) * Real.exp (-(κ * |η| / c)) := by positivity
    exact mul_le_mul hMs hexp hp (by positivity)
  · rw [indicator_of_notMem hs, zero_mul]
    exact hR0

/-- `‖coord z‖ ≤ ‖z‖` in the regime (`R ≥ 1`). -/
theorem norm_coord_le {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp) (z : p.Z) :
    ‖p.coord z‖ ≤ ‖z‖ := by
  have hR1 : 1 ≤ p.R := one_le_R_of hreg
  have hR8 : 1 ≤ p.R ^ (8 / 11 : ℝ) := Real.one_le_rpow hR1 (by norm_num)
  have hRz : p.R ^ (8 / 11 : ℝ) * ‖p.coord z‖ ≤ ‖z‖ := R_rpow_mul_norm_coord_le p z
  calc ‖p.coord z‖ = 1 * ‖p.coord z‖ := (one_mul _).symm
    _ ≤ p.R ^ (8 / 11 : ℝ) * ‖p.coord z‖ := mul_le_mul_of_nonneg_right hR8 (norm_nonneg _)
    _ ≤ ‖z‖ := hRz

/-- **Supremum bounds on the affine inlet and its gradient.** -/
theorem inlet_sup_le
    (Sig : ℝ) (lam : ℂ) (q : Planar.Profile) (hSig : 0 < Sig)
    (hq : Planar.IsGrowingEigenpair lam q) (dm dp : ℝ) (hdm : 0 < dm) :
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
        ∀ (z : p.Z) (x : ℝ × Space),
          ‖p.eFun (p.coord z) x‖ ≤ C * (p.ν ^ k)⁻¹ * ‖z‖ ∧
          ∀ j : Fin 3, ‖dy j (p.eFun (p.coord z)) x‖ ≤ C * (p.ν ^ k)⁻¹ * ‖z‖ := by
  obtain ⟨CJ, κJ, kJ, νJ, hCJ, hκJ, hνJ, hνJ1, HJ⟩ :=
    inletJetDecay Sig lam q hSig hq dm dp hdm
  obtain ⟨νV, hνV, HV⟩ :=
    inletProfileSmoothVanish Sig lam q hSig hq dm dp hdm
  obtain ⟨B, κ, k1, ν1, hB, hκ, hν1pos, hν11, HP⟩ := inlet_dy_ptw Sig lam q hSig hq dm dp hdm
  have hSig0 : 0 < 1 + Sig := by linarith
  refine ⟨2 * CJ * (1 + Sig) + B * (1 + Sig) ^ 2 * (1 + 1 / κ), kJ + k1 + 4,
    min (min νJ νV) ν1, by positivity, lt_min (lt_min hνJ hνV) hν1pos,
    (min_le_left _ _).trans ((min_le_left _ _).trans hνJ1), ?_⟩
  intro p d hreg hν hS hm z x
  have h0 : p.ν ≤ νJ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h1 : p.ν ≤ νV := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h2 : p.ν ≤ ν1 := hν.trans (min_le_right _ _)
  have hν1 : p.ν ≤ 1 := h0.trans hνJ1
  have hνpos : 0 < p.ν := p.ν_pos
  have hHpos : 0 < p.H := p.H_pos
  have hRpos : 0 < p.R := p.R_pos
  set u : ℝ := p.ν⁻¹ with hu
  have hu1 : 1 ≤ u := by
    rw [hu]
    exact (one_le_inv₀ hνpos).2 hν1
  have hu0 : 0 ≤ u := by linarith
  have hpow : ∀ m : ℕ, (p.ν ^ m)⁻¹ = u ^ m := fun m => by rw [hu, inv_pow]
  have hc : p.c = u ^ 2 := by rw [hreg.c_eq, hpow]
  have hcpos : 0 < p.c := p.c_pos
  have eH : p.H = Sig * u := by
    rw [Params.H, hS, hu, div_eq_mul_inv]
  have hH : 1 + p.H ≤ (1 + Sig) * u := by
    rw [eH]
    nlinarith
  have hH2 : p.H / 2 ≤ (1 + Sig) * u := by
    rw [eH]
    nlinarith
  have hcκ : 1 + p.c / κ ≤ (1 + 1 / κ) * u ^ 2 := by
    rw [hc]
    have hu2 : 1 ≤ u ^ 2 := one_le_pow₀ hu1
    have : u ^ 2 / κ = (1 / κ) * u ^ 2 := by ring
    rw [this]
    nlinarith
  have hαz : ‖p.coord z‖ ≤ ‖z‖ := norm_coord_le hreg z
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hk1 : u ^ (kJ + 1) ≤ u ^ (kJ + k1 + 4) := pow_le_pow_right₀ hu1 (by omega)
  have hk2 : u ^ (k1 + 4) ≤ u ^ (kJ + k1 + 4) := pow_le_pow_right₀ hu1 (by omega)
  rw [hpow]
  set α : Fin 2 → ℝ := p.coord z with hα
  have HJ' := HJ p d ⟨hreg, h0, hS, hm⟩
  have HV' := HV p d hreg h1 hS hm
  set e : ℝ × (ℝ × ℝ) → Merid := α 0 • p.inletProfile 0 + α 1 • p.inletProfile 1 with he
  have hvan : ∀ m : ℝ × (ℝ × ℝ), p.H / 2 < m.1 → e m = 0 := by
    intro m hm'
    have hz0 := (HV' 0).2 m hm'
    have hz1 := (HV' 1).2 m hm'
    simp [he, hz0, hz1]
  have heFun : p.eFun α = fun q : ℝ × Space => realC (Nv p.R e q.1 q.2) := by
    funext q
    simp only [Params.eFun, Params.inlet, Fin.sum_univ_two, he, Nv_add, Nv_smul]
  have hCtot1 : 2 * CJ * (1 + Sig) ≤ 2 * CJ * (1 + Sig) + B * (1 + Sig) ^ 2 * (1 + 1 / κ) := by
    have : 0 ≤ B * (1 + Sig) ^ 2 * (1 + 1 / κ) := by positivity
    linarith
  have hCtot2 : B * (1 + Sig) ^ 2 * (1 + 1 / κ) ≤
      2 * CJ * (1 + Sig) + B * (1 + Sig) ^ 2 * (1 + 1 / κ) := by
    have : 0 ≤ 2 * CJ * (1 + Sig) := by positivity
    linarith
  obtain ⟨τ, y⟩ := x
  refine ⟨?_, ?_⟩
  · -- the inlet itself
    have hb : ‖p.eFun α (τ, y)‖ ≤ (1 + p.H) * (2 * ‖α‖ * (CJ * u ^ kJ)) := by
      rw [heFun]
      show ‖realC (Nv p.R e τ y)‖ ≤ _
      rw [norm_realC]
      have hM0 : 0 ≤ (1 + p.H) * (2 * ‖α‖ * (CJ * u ^ kJ)) := by positivity
      by_cases hax : y ∈ axis
      · have hϱ : ϱ y = 0 := (mem_axis_iff y).1 hax
        have hage : age p.R y = 0 := by
          unfold age
          rw [hϱ]
          simp
        rw [Nv, hage, Real.sqrt_zero, zero_smul, norm_zero]
        exact hM0
      · rw [norm_Nv p.R e τ hax]
        by_cases hle : age p.R y ≤ p.H / 2
        · have hsq : √(age p.R y) ≤ 1 + p.H := aux_sqrt_le hHpos hle
          have hj := comb_jets HJ' α 0 (by norm_num) (chart p.R τ y)
          rw [norm_iteratedFDeriv_zero] at hj
          have hE1 : Real.exp (-(κJ * |(chart p.R τ y).2.2| / p.c)) ≤ 1 := by
            rw [Real.exp_le_one_iff]
            have : 0 ≤ κJ * |(chart p.R τ y).2.2| / p.c := by positivity
            linarith
          have hj' : ‖e (chart p.R τ y)‖ ≤ 2 * ‖α‖ * (CJ * u ^ kJ) := by
            refine hj.trans ?_
            rw [hpow]
            have : 0 ≤ 2 * ‖α‖ * (CJ * u ^ kJ) := by positivity
            calc 2 * ‖α‖ * (CJ * u ^ kJ * Real.exp (-(κJ * |(chart p.R τ y).2.2| / p.c)))
                ≤ 2 * ‖α‖ * (CJ * u ^ kJ * 1) := by gcongr
              _ = 2 * ‖α‖ * (CJ * u ^ kJ) := by ring
          exact mul_le_mul hsq hj' (norm_nonneg _) (by linarith)
        · rw [hvan _ (not_le.1 hle), norm_zero, mul_zero]
          exact hM0
    refine hb.trans ?_
    calc (1 + p.H) * (2 * ‖α‖ * (CJ * u ^ kJ))
        ≤ ((1 + Sig) * u) * (2 * ‖z‖ * (CJ * u ^ kJ)) := by gcongr
      _ = 2 * CJ * (1 + Sig) * u ^ (kJ + 1) * ‖z‖ := by ring
      _ ≤ (2 * CJ * (1 + Sig) + B * (1 + Sig) ^ 2 * (1 + 1 / κ)) * u ^ (kJ + k1 + 4) * ‖z‖ := by
          gcongr
  · -- the gradient
    intro j
    have hM0 : 0 ≤ B * (1 + p.H) * (p.ν ^ k1)⁻¹ * ‖α‖ := by positivity
    have hb : ‖dy j (p.eFun α) (τ, y)‖ ≤
        B * (1 + p.H) * (p.ν ^ k1)⁻¹ * ‖α‖ * (p.H / 2) * (1 + p.c / κ) := by
      by_cases hax : y ∈ axis
      · have hvanH : ∀ m : ℝ × (ℝ × ℝ), p.H ≤ m.1 → e m = 0 :=
          fun m hm' => hvan m (by linarith)
        have hev : ∀ᶠ q in 𝓝 (τ, y), p.eFun α q = 0 := by
          have h1 := nv_eventually_zero p.R_pos hvanH (Or.inl hax)
          have h2 := (continuous_snd.tendsto (τ, y)).eventually h1
          filter_upwards [h2] with q hq
          rw [heFun]
          simp [hq q.1, realC]
        rw [dy_eq_zero hev j, norm_zero]
        positivity
      · exact (HP p d hreg h2 hS hm α j τ y hax).trans
          (ringEnv1_one_le hHpos hM0 hκ hcpos _ _)
    refine hb.trans ?_
    rw [hpow]
    have hcκ0 : 0 ≤ 1 + p.c / κ := by positivity
    have hH20 : 0 ≤ p.H / 2 := by positivity
    calc B * (1 + p.H) * u ^ k1 * ‖α‖ * (p.H / 2) * (1 + p.c / κ)
        ≤ B * ((1 + Sig) * u) * u ^ k1 * ‖z‖ * ((1 + Sig) * u) * ((1 + 1 / κ) * u ^ 2) := by
          gcongr
      _ = B * (1 + Sig) ^ 2 * (1 + 1 / κ) * u ^ (k1 + 4) * ‖z‖ := by ring
      _ ≤ (2 * CJ * (1 + Sig) + B * (1 + Sig) ^ 2 * (1 + 1 / κ)) * u ^ (kJ + k1 + 4) * ‖z‖ := by
          gcongr

end UnforcedLeray.Short.IIb.QuadBoundSub
