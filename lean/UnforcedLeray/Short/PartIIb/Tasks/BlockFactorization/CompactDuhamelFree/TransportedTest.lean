import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_4
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.FrozenTransportCont.Meas
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.TrainGap

/-!
# Transported smooth test helper for `PartII-b:F2/4/1` (`CompactDuhamelFree`)

Constructs the frozen-radial-transported test `psi0` and its `c`-periodization `periodizePsi0`,
proving the frozen transport cancellation `∂_r ψ₀ + isoVelocity(ν, t)·∇ψ₀ = 0`, uniform bounds on
`∇ψ₀` and `Δψ₀`, agreement on `B0579.cell c`, and membership in `CylEtaTest`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.IIb.CompactDuhamelFreeHelp

open PartIIbF23Sub FrozenTransportContHelp

theorem exp_le_one_add_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + 2 * x := by
  have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have h2 : 1 ≤ (1 - x) * (1 + 2 * x) := by nlinarith
  have h3 : 0 ≤ 1 + 2 * x := by linarith
  have h4 : (1 - x) * (1 + 2 * x) ≤ Real.exp (-x) * (1 + 2 * x) :=
    mul_le_mul_of_nonneg_right h1 h3
  have hexp_pos : 0 < Real.exp x := Real.exp_pos x
  have hcancel : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc Real.exp x = Real.exp x * 1 := (mul_one _).symm
    _ ≤ Real.exp x * ((1 - x) * (1 + 2 * x)) := mul_le_mul_of_nonneg_left h2 hexp_pos.le
    _ ≤ Real.exp x * (Real.exp (-x) * (1 + 2 * x)) := mul_le_mul_of_nonneg_left h4 hexp_pos.le
    _ = (Real.exp x * Real.exp (-x)) * (1 + 2 * x) := by ring
    _ = 1 + 2 * x := by rw [hcancel, one_mul]

theorem exp_neg_sq_le_inv {b c : ℝ} (hb : 0 < b) (hc : 1 ≤ c) :
    Real.exp (-b * c ^ 2) ≤ (b * c)⁻¹ := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  have hbc : 0 < b * c := mul_pos hb hc0
  have hc_sq : c ≤ c ^ 2 := by nlinarith
  have h1 : b * c ≤ Real.exp (b * c ^ 2) := by
    calc b * c ≤ 1 + b * c := by linarith
      _ ≤ Real.exp (b * c) := by linarith [Real.add_one_le_exp (b * c)]
      _ ≤ Real.exp (b * c ^ 2) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hc_sq hb.le)
  rw [show -b * c ^ 2 = -(b * c ^ 2) by ring, Real.exp_neg]
  exact inv_anti₀ hbc h1

theorem jb_frozenRadialFlow (σ τ : ℝ) (x : B0579.Plane) :
    B0579.jb (frozenRadialFlow σ τ x) = B0579.jb x := by
  unfold B0579.jb
  linarith [flow_sq σ τ x]

theorem isoVelocity_eq_frozenOmega {ν t : ℝ} (hσ : 0 < 1 + ν * t) (x : B0579.Plane) :
    (UnforcedLeray.B0146.isoVelocity ν t x).1 = -frozenOmega (ν * t) x * x.2 ∧
      (UnforcedLeray.B0146.isoVelocity ν t x).2 = frozenOmega (ν * t) x * x.1 := by
  rw [trainGap_iso_fst, trainGap_iso_snd]
  unfold UnforcedLeray.B0146.u1 UnforcedLeray.B0146.u2 UnforcedLeray.B0113.gw
    UnforcedLeray.GaussianVortex.radiusSq
  rw [frozenOmega_eq]
  have hsq : Real.sqrt (1 + ν * t) ^ 2 = 1 + ν * t := Real.sq_sqrt hσ.le
  have hexp : -(((x.1 / Real.sqrt (1 + ν * t)) ^ 2 + (x.2 / Real.sqrt (1 + ν * t)) ^ 2) / 4) =
      -((1 + ν * t)⁻¹ * (x.1 ^ 2 + x.2 ^ 2) / 4) := by
    rw [div_pow, div_pow, hsq]
    field_simp [hσ.ne']
  rw [hexp, inv_pow]
  constructor <;> ring

theorem exists_isoVelocity_age_lip {Sig : ℝ} (_hSig : 0 < Sig) :
    ∃ C_lip : ℝ, 0 < C_lip ∧
      ∀ (ν t r : ℝ), 0 < ν → 0 ≤ t → t ≤ r → ν * r ≤ Sig → ∀ x : B0579.Plane,
        |(UnforcedLeray.B0146.isoVelocity ν r x).1 - (UnforcedLeray.B0146.isoVelocity ν t x).1| +
          |(UnforcedLeray.B0146.isoVelocity ν r x).2 - (UnforcedLeray.B0146.isoVelocity ν t x).2|
          ≤ C_lip * (ν * (r - t)) := by
  obtain ⟨K₁, β₁, hK₁, hβ₁, hu1a⟩ :=
    UnforcedLeray.B0146.gf_u1a (A₁ := 1) (A₂ := 1 + Sig) one_pos
  obtain ⟨K₂, β₂, hK₂, hβ₂, hu2a⟩ :=
    UnforcedLeray.B0146.gf_u2a (A₁ := 1) (A₂ := 1 + Sig) one_pos
  refine ⟨K₁ + K₂ + 1, by linarith, fun ν t r hν ht0 htr hνr x => ?_⟩
  set a₁ : ℝ := 1 + ν * t
  set a₂ : ℝ := 1 + ν * r
  have ha₁_ge : 1 ≤ a₁ := by dsimp [a₁]; nlinarith
  have ha₁₂ : a₁ ≤ a₂ := by dsimp [a₁, a₂]; nlinarith
  have ha₂_le : a₂ ≤ 1 + Sig := by dsimp [a₂]; linarith
  have hrad_nn : 0 ≤ UnforcedLeray.GaussianVortex.radiusSq x :=
    UnforcedLeray.B0146.radiusSq_nonneg x
  have hd1_bd : ∀ b ∈ Icc (1 : ℝ) (1 + Sig), ‖UnforcedLeray.B0146.u1a b x‖ ≤ K₁ := by
    intro b hb
    rw [Real.norm_eq_abs]
    calc |UnforcedLeray.B0146.u1a b x|
        ≤ K₁ * Real.exp (-(β₁ * UnforcedLeray.GaussianVortex.radiusSq x)) := hu1a b hb x
      _ ≤ K₁ * 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.2 (by nlinarith [hβ₁.le])) hK₁
      _ = K₁ := mul_one K₁
  have hd2_bd : ∀ b ∈ Icc (1 : ℝ) (1 + Sig), ‖UnforcedLeray.B0146.u2a b x‖ ≤ K₂ := by
    intro b hb
    rw [Real.norm_eq_abs]
    calc |UnforcedLeray.B0146.u2a b x|
        ≤ K₂ * Real.exp (-(β₂ * UnforcedLeray.GaussianVortex.radiusSq x)) := hu2a b hb x
      _ ≤ K₂ * 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.2 (by nlinarith [hβ₂.le])) hK₂
      _ = K₂ := mul_one K₂
  have hmvt1 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun b => UnforcedLeray.B0146.u1 b x)
    (f' := fun b => UnforcedLeray.B0146.u1a b x)
    (s := Icc 1 (1 + Sig))
    (fun b hb => (UnforcedLeray.B0146.ha_u1 (by linarith [hb.1]) x).hasDerivWithinAt)
    hd1_bd (convex_Icc 1 (1 + Sig)) ⟨ha₁_ge, ha₁₂.trans ha₂_le⟩ ⟨ha₁_ge.trans ha₁₂, ha₂_le⟩
  have hmvt2 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun b => UnforcedLeray.B0146.u2 b x)
    (f' := fun b => UnforcedLeray.B0146.u2a b x)
    (s := Icc 1 (1 + Sig))
    (fun b hb => (UnforcedLeray.B0146.ha_u2 (by linarith [hb.1]) x).hasDerivWithinAt)
    hd2_bd (convex_Icc 1 (1 + Sig)) ⟨ha₁_ge, ha₁₂.trans ha₂_le⟩ ⟨ha₁_ge.trans ha₁₂, ha₂_le⟩
  rw [trainGap_iso_fst, trainGap_iso_fst, trainGap_iso_snd, trainGap_iso_snd]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 ha₁₂)] at hmvt1 hmvt2
  have hsub_eq : a₂ - a₁ = ν * (r - t) := by dsimp [a₁, a₂]; ring
  rw [hsub_eq] at hmvt1 hmvt2
  have hnn : 0 ≤ ν * (r - t) := mul_nonneg hν.le (sub_nonneg.2 htr)
  nlinarith

/-! ### Smooth directional derivatives on `ℝ × B0579.Plane` -/

private def dSpaceTime (Φ : ℝ × B0579.Plane → ℝ) (v : ℝ × B0579.Plane)
    (z : ℝ × B0579.Plane) : ℝ :=
  fderiv ℝ Φ z v

private theorem contDiff_dSpaceTime {Φ : ℝ × B0579.Plane → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (v : ℝ × B0579.Plane) : ContDiff ℝ ∞ (dSpaceTime Φ v) :=
  ((contDiff_infty_iff_fderiv.1 hΦ).2).clm_apply contDiff_const

private theorem deriv_time_eq_dSpaceTime {Φ : ℝ × B0579.Plane → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (r : ℝ) (x : B0579.Plane) :
    deriv (fun r' => Φ (r', x)) r = dSpaceTime Φ (1, (0, 0)) (r, x) := by
  have h1 : HasDerivAt (fun r' : ℝ => (r', x)) (1, (0, 0)) r :=
    (hasDerivAt_id r).prodMk (hasDerivAt_const r x)
  have h2 : DifferentiableAt ℝ Φ (r, x) := (hΦ.differentiable (by simp)).differentiableAt
  exact (h2.hasFDerivAt.comp_hasDerivAt r h1).deriv

private theorem pd_space_eq_dSpaceTime {Φ : ℝ × B0579.Plane → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (j : Fin 2) (r : ℝ) (x : B0579.Plane) :
    B0579.pd j (fun y => Φ (r, y)) x = dSpaceTime Φ (0, B0579.dir j) (r, x) := by
  have hinr : HasFDerivAt (fun y : B0579.Plane => (r, y))
      (ContinuousLinearMap.inr ℝ ℝ B0579.Plane) x :=
    (hasFDerivAt_const r x).prodMk (hasFDerivAt_id x)
  have h2 : DifferentiableAt ℝ Φ (r, x) := (hΦ.differentiable (by simp)).differentiableAt
  have hcomp := (h2.hasFDerivAt.comp x hinr).fderiv
  unfold B0579.pd dSpaceTime
  change (fderiv ℝ (Φ ∘ Prod.mk r) x) (B0579.dir j) = _
  rw [hcomp]
  rfl

private theorem dSpaceTime_shift {Φ : ℝ × B0579.Plane → ℝ} (d : ℝ)
    (hper : ∀ z : ℝ × B0579.Plane, Φ (z.1, (z.2.1 + d, z.2.2)) = Φ z)
    (v : ℝ × B0579.Plane) (z : ℝ × B0579.Plane) :
    dSpaceTime Φ v (z.1, (z.2.1 + d, z.2.2)) = dSpaceTime Φ v z := by
  set a : ℝ × B0579.Plane := (0, (d, 0))
  have hfun : (fun w : ℝ × B0579.Plane => Φ (w + a)) = Φ := by
    funext w
    have hw : w + a = (w.1, (w.2.1 + d, w.2.2)) := by
      dsimp [a]; ext <;> simp
    rw [hw]
    exact hper w
  have hz : z + a = (z.1, (z.2.1 + d, z.2.2)) := by
    dsimp [a]; ext <;> simp
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := Φ) (x := z) a
  rw [hfun, hz] at h
  unfold dSpaceTime
  rw [← h]

/-! ### Transported test `psi0` and its PDE / uniform bounds -/

def psi0 (g_w : B0579.Plane → ℝ) (σ t₁ r : ℝ) (x : B0579.Plane) : ℝ :=
  g_w (frozenRadialFlow σ (r - t₁) x)

theorem contDiff_psi0 {g_w : B0579.Plane → ℝ} (hg : ContDiff ℝ ∞ g_w) (σ t₁ : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × B0579.Plane => psi0 g_w σ t₁ z.1 z.2) := by
  have hω : ContDiff ℝ ∞ (frozenOmega σ) := contDiff_frozenOmega σ
  unfold psi0 frozenRadialFlow
  simp only
  fun_prop

theorem transport_pde_psi0 {g_w : B0579.Plane → ℝ} (hg : ContDiff ℝ ∞ g_w)
    {σ : ℝ} (hσ : 0 ≤ 1 + σ) (t₁ r : ℝ) (x : B0579.Plane) :
    deriv (fun r' => psi0 g_w σ t₁ r' x) r +
      (-frozenOmega σ x * x.2) * B0579.pd 0 (psi0 g_w σ t₁ r) x +
      (frozenOmega σ x * x.1) * B0579.pd 1 (psi0 g_w σ t₁ r) x = 0 := by
  set Ψ : ℝ × B0579.Plane → ℝ := fun z => psi0 g_w σ t₁ z.1 z.2
  have hΨ : ContDiff ℝ ∞ Ψ := contDiff_psi0 hg σ t₁
  set ω₀ : ℝ := frozenOmega σ x
  set γ : ℝ → ℝ × B0579.Plane := fun α => (r + α, frozenRadialFlow σ (-α) x)
  have hconst : (fun α : ℝ => Ψ (γ α)) = fun _ => Ψ (r, x) := by
    funext α
    dsimp [Ψ, γ, psi0]
    rw [flow_add σ hσ (r + α - t₁) (-α) x]
    have heq : r + α - t₁ + -α = r - t₁ := by ring
    rw [heq]
  have hd_zero : HasDerivAt (fun α : ℝ => Ψ (γ α)) 0 0 := by
    rw [hconst]
    exact hasDerivAt_const 0 (Ψ (r, x))
  have hθ : HasDerivAt (fun α : ℝ => -(-α) * ω₀) ω₀ 0 := by
    have h1 : (fun α : ℝ => -(-α) * ω₀) = fun α => α * ω₀ := by funext α; ring
    rw [h1]
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const ω₀
  have hθ0 : -(-(0 : ℝ)) * ω₀ = 0 := by ring
  have hcos : HasDerivAt (fun α : ℝ => Real.cos (-(-α) * ω₀)) 0 0 := by
    have h := (Real.hasDerivAt_cos (-(-(0 : ℝ)) * ω₀)).comp (0 : ℝ) hθ
    rw [hθ0, Real.sin_zero, neg_zero, zero_mul] at h
    exact h
  have hsin : HasDerivAt (fun α : ℝ => Real.sin (-(-α) * ω₀)) ω₀ 0 := by
    have h := (Real.hasDerivAt_sin (-(-(0 : ℝ)) * ω₀)).comp (0 : ℝ) hθ
    rw [hθ0, Real.cos_zero, one_mul] at h
    exact h
  have hfl1 : HasDerivAt (fun α : ℝ => (frozenRadialFlow σ (-α) x).1) (-ω₀ * x.2) 0 := by
    have h := (hcos.mul_const x.1).sub (hsin.mul_const x.2)
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun α => rfl) |>.congr_deriv ?_
    ring
  have hfl2 : HasDerivAt (fun α : ℝ => (frozenRadialFlow σ (-α) x).2) (ω₀ * x.1) 0 := by
    have h := (hsin.mul_const x.1).add (hcos.mul_const x.2)
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun α => rfl) |>.congr_deriv ?_
    ring
  have hγ0 : γ 0 = (r, x) := by
    dsimp [γ]
    rw [add_zero, neg_zero, flow_zero]
  have hγ : HasDerivAt γ (1, (-ω₀ * x.2, ω₀ * x.1)) 0 := by
    have hr_d : HasDerivAt (fun α : ℝ => r + α) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add r
    exact hr_d.prodMk (hfl1.prodMk hfl2)
  have hΨ_diff : DifferentiableAt ℝ Ψ (r, x) := (hΨ.differentiable (by simp)).differentiableAt
  have hd_chain : HasDerivAt (fun α : ℝ => Ψ (γ α))
      (fderiv ℝ Ψ (r, x) (1, (-ω₀ * x.2, ω₀ * x.1))) 0 := by
    have hΨ_at : HasFDerivAt Ψ (fderiv ℝ Ψ (r, x)) (γ 0) :=
      hγ0.symm ▸ hΨ_diff.hasFDerivAt
    exact hΨ_at.comp_hasDerivAt 0 hγ
  have heq0 := hd_chain.unique hd_zero
  have hv_decomp : ((1 : ℝ), (-ω₀ * x.2, ω₀ * x.1)) =
      (1, (0, 0)) + (-ω₀ * x.2) • (0, B0579.dir 0) + (ω₀ * x.1) • (0, B0579.dir 1) := by
    ext <;> simp [B0579.dir]
  rw [hv_decomp, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at heq0
  have h_dr := deriv_time_eq_dSpaceTime hΨ r x
  have h_pd0 := pd_space_eq_dSpaceTime hΨ 0 r x
  have h_pd1 := pd_space_eq_dSpaceTime hΨ 1 r x
  unfold dSpaceTime at h_dr h_pd0 h_pd1
  change deriv (fun r' => Ψ (r', x)) r +
      (-ω₀ * x.2) * B0579.pd 0 (fun y => Ψ (r, y)) x +
      (ω₀ * x.1) * B0579.pd 1 (fun y => Ψ (r, y)) x = 0
  rw [h_dr, h_pd0, h_pd1]
  exact heq0

theorem psi0_vanish_of_sq_gt {g_w : B0579.Plane → ℝ} {R₀ : ℝ}
    (hg_supp : ∀ y : B0579.Plane, R₀ ^ 2 < y.1 ^ 2 + y.2 ^ 2 → g_w y = 0)
    (σ t₁ r : ℝ) {x : B0579.Plane} (hx : R₀ ^ 2 < x.1 ^ 2 + x.2 ^ 2) :
    psi0 g_w σ t₁ r x = 0 ∧
      B0579.pd 0 (psi0 g_w σ t₁ r) x = 0 ∧
      B0579.pd 1 (psi0 g_w σ t₁ r) x = 0 ∧
      lapP (psi0 g_w σ t₁ r) x = 0 := by
  have hU_open : IsOpen {y : B0579.Plane | R₀ ^ 2 < y.1 ^ 2 + y.2 ^ 2} :=
    isOpen_lt continuous_const (by fun_prop)
  have hzero_on : ∀ y : B0579.Plane, R₀ ^ 2 < y.1 ^ 2 + y.2 ^ 2 → psi0 g_w σ t₁ r y = 0 := by
    intro y hy
    unfold psi0
    apply hg_supp
    rwa [flow_sq]
  have hev : psi0 g_w σ t₁ r =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hU_open.mem_nhds hx) hzero_on
  have hpd_zero : ∀ j : Fin 2, ∀ y : B0579.Plane, R₀ ^ 2 < y.1 ^ 2 + y.2 ^ 2 →
      B0579.pd j (psi0 g_w σ t₁ r) y = 0 := by
    intro j y hy
    have hevy : psi0 g_w σ t₁ r =ᶠ[𝓝 y] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (hU_open.mem_nhds hy) hzero_on
    unfold B0579.pd
    rw [hevy.fderiv_eq]
    simp
  have hpd2_zero : ∀ j : Fin 2, B0579.pd j (B0579.pd j (psi0 g_w σ t₁ r)) x = 0 := by
    intro j
    have hevj : B0579.pd j (psi0 g_w σ t₁ r) =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (hU_open.mem_nhds hx) (hpd_zero j)
    change (fderiv ℝ (B0579.pd j (psi0 g_w σ t₁ r)) x) (B0579.dir j) = 0
    rw [hevj.fderiv_eq]
    simp
  exact ⟨hzero_on x hx, hpd_zero 0 x hx, hpd_zero 1 x hx, by
    unfold lapP; rw [hpd2_zero 0, hpd2_zero 1, add_zero]⟩

theorem sq_gt_of_not_mem_box {R₀ : ℝ} (hR₀ : 1 ≤ R₀) {x : B0579.Plane}
    (hx : x ∉ Icc (-(R₀ + 1)) (R₀ + 1) ×ˢ Icc (-(R₀ + 1)) (R₀ + 1)) :
    R₀ ^ 2 < x.1 ^ 2 + x.2 ^ 2 := by
  by_contra hle
  rw [not_lt] at hle
  apply hx
  have hRpos : 0 ≤ R₀ := by linarith
  have h1 : x.1 ^ 2 ≤ (R₀ + 1) ^ 2 := by nlinarith [sq_nonneg x.2]
  have h2 : x.2 ^ 2 ≤ (R₀ + 1) ^ 2 := by nlinarith [sq_nonneg x.1]
  have ha1 : |x.1| ≤ R₀ + 1 := by
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (by linarith)] at this
  have ha2 : |x.2| ≤ R₀ + 1 := by
    have := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (by linarith)] at this
  exact ⟨abs_le.1 ha1, abs_le.1 ha2⟩

private def safeWidth (σ : ℝ) : ℝ :=
  1 + Real.smoothTransition (2 * σ + 1) * σ

private theorem safeWidth_eq_of_nonneg {σ : ℝ} (hσ : 0 ≤ σ) : safeWidth σ = 1 + σ := by
  unfold safeWidth
  rw [Real.smoothTransition.one_of_one_le (by linarith), one_mul]

private theorem half_le_safeWidth (σ : ℝ) : 1 / 2 ≤ safeWidth σ := by
  unfold safeWidth
  rcases le_or_gt σ (-1 / 2) with hle | hgt
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul, add_zero]
    norm_num
  · rcases le_or_gt 0 σ with h0 | hneg
    · have hnn : 0 ≤ Real.smoothTransition (2 * σ + 1) * σ :=
        mul_nonneg (Real.smoothTransition.nonneg _) h0
      linarith
    · have hle1 : Real.smoothTransition (2 * σ + 1) ≤ 1 := Real.smoothTransition.le_one _
      have hnn : 0 ≤ Real.smoothTransition (2 * σ + 1) := Real.smoothTransition.nonneg _
      nlinarith

private theorem contDiff_safeWidth : ContDiff ℝ ∞ safeWidth := by
  unfold safeWidth
  have hst : ContDiff ℝ ∞ Real.smoothTransition :=
    Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))
  exact contDiff_const.add ((hst.comp (by fun_prop)).mul contDiff_id)

private def safeOmega (σ : ℝ) (x : B0579.Plane) : ℝ :=
  ((safeWidth σ) ^ 2)⁻¹ * Real.exp (-((x.1 ^ 2 + x.2 ^ 2) / (4 * safeWidth σ)))

private theorem safeOmega_eq_frozenOmega {σ : ℝ} (hσ : 0 ≤ σ) (x : B0579.Plane) :
    safeOmega σ x = frozenOmega σ x := by
  unfold safeOmega
  rw [safeWidth_eq_of_nonneg hσ, frozenOmega_eq]
  have h1 : 0 < 1 + σ := by linarith
  have hsq : Real.sqrt (1 + σ) ^ 2 = 1 + σ := Real.sq_sqrt h1.le
  congr 2
  rw [div_pow, div_pow, hsq]
  field_simp [h1.ne']

private def safeFlow (σ u : ℝ) (x : B0579.Plane) : B0579.Plane :=
  let θ : ℝ := -u * safeOmega σ x
  (Real.cos θ * x.1 - Real.sin θ * x.2, Real.sin θ * x.1 + Real.cos θ * x.2)

private theorem safeFlow_eq_frozenRadialFlow {σ : ℝ} (hσ : 0 ≤ σ) (u : ℝ) (x : B0579.Plane) :
    safeFlow σ u x = frozenRadialFlow σ u x := by
  unfold safeFlow frozenRadialFlow
  rw [safeOmega_eq_frozenOmega hσ x]

theorem exists_psi0_deriv_bound {Sig Lmax R₀ : ℝ} (_hSig : 0 < Sig) (_hLmax : 0 < Lmax)
    (hR₀ : 1 ≤ R₀) {g_w : B0579.Plane → ℝ} (hg : ContDiff ℝ ∞ g_w)
    (hg_supp : ∀ y : B0579.Plane, R₀ ^ 2 < y.1 ^ 2 + y.2 ^ 2 → g_w y = 0) :
    ∃ M_psi : ℝ, 0 < M_psi ∧
      ∀ σ ∈ Icc 0 Sig, ∀ t₁ r : ℝ, r - t₁ ∈ Icc (-Lmax) 0 → ∀ x : B0579.Plane,
        |B0579.pd 0 (psi0 g_w σ t₁ r) x| ≤ M_psi ∧
          |B0579.pd 1 (psi0 g_w σ t₁ r) x| ≤ M_psi ∧
          |lapP (psi0 g_w σ t₁ r) x| ≤ M_psi := by
  set G_tot : (ℝ × ℝ) × B0579.Plane → ℝ := fun q => g_w (safeFlow q.1.1 q.1.2 q.2)
  have hsw_ne : ∀ q : (ℝ × ℝ) × B0579.Plane, safeWidth q.1.1 ≠ 0 := fun q => by
    have := half_le_safeWidth q.1.1; linarith
  have hsw2_ne : ∀ q : (ℝ × ℝ) × B0579.Plane, (safeWidth q.1.1) ^ 2 ≠ 0 :=
    fun q => pow_ne_zero 2 (hsw_ne q)
  have hsw4_ne : ∀ q : (ℝ × ℝ) × B0579.Plane, 4 * safeWidth q.1.1 ≠ 0 := fun q => by
    have := half_le_safeWidth q.1.1; linarith
  have h_sw_cd : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × B0579.Plane => safeWidth q.1.1) :=
    contDiff_safeWidth.comp (by fun_prop)
  have h_so_cd : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × B0579.Plane => safeOmega q.1.1 q.2) := by
    change ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × B0579.Plane =>
      ((safeWidth q.1.1) ^ 2)⁻¹ * Real.exp (-((q.2.1 ^ 2 + q.2.2 ^ 2) / (4 * safeWidth q.1.1))))
    refine ContDiff.mul ((h_sw_cd.pow 2).inv hsw2_ne) ?_
    exact Real.contDiff_exp.comp (((by fun_prop : ContDiff ℝ ∞
      (fun q : (ℝ × ℝ) × B0579.Plane => q.2.1 ^ 2 + q.2.2 ^ 2)).div
        (contDiff_const.mul h_sw_cd) hsw4_ne).neg)
  have hG_cd : ContDiff ℝ ∞ G_tot := by
    dsimp [G_tot, safeFlow]
    have := h_so_cd
    fun_prop
  set D_tot := fun (v : B0579.Plane) (H : (ℝ × ℝ) × B0579.Plane → ℝ)
      (q : (ℝ × ℝ) × B0579.Plane) =>
    fderiv ℝ H q ((0, 0), v)
  have hD_cd : ∀ (v : B0579.Plane) {H : (ℝ × ℝ) × B0579.Plane → ℝ}, ContDiff ℝ ∞ H →
      ContDiff ℝ ∞ (D_tot v H) := fun v _ hH =>
    ((contDiff_infty_iff_fderiv.1 hH).2).clm_apply contDiff_const
  have hD_eq : ∀ (j : Fin 2) {H : (ℝ × ℝ) × B0579.Plane → ℝ}, ContDiff ℝ ∞ H →
      ∀ (p_su : ℝ × ℝ) (x : B0579.Plane),
        B0579.pd j (fun y => H (p_su, y)) x = D_tot (B0579.dir j) H (p_su, x) := by
    intro j H hH p_su x
    have hinr : HasFDerivAt (fun y : B0579.Plane => (p_su, y))
        (ContinuousLinearMap.inr ℝ (ℝ × ℝ) B0579.Plane) x :=
      (hasFDerivAt_const p_su x).prodMk (hasFDerivAt_id x)
    have hdiff : DifferentiableAt ℝ H (p_su, x) := (hH.differentiable (by simp)).differentiableAt
    have hcomp := (hdiff.hasFDerivAt.comp x hinr).fderiv
    unfold B0579.pd
    change (fderiv ℝ (H ∘ Prod.mk p_su) x) (B0579.dir j) = _
    rw [hcomp]
    rfl
  set P0 := D_tot (B0579.dir 0) G_tot
  set P1 := D_tot (B0579.dir 1) G_tot
  set L_tot := fun q => D_tot (B0579.dir 0) P0 q + D_tot (B0579.dir 1) P1 q
  have hP0_cd : ContDiff ℝ ∞ P0 := hD_cd (B0579.dir 0) hG_cd
  have hP1_cd : ContDiff ℝ ∞ P1 := hD_cd (B0579.dir 1) hG_cd
  have hL_cd : ContDiff ℝ ∞ L_tot :=
    (hD_cd (B0579.dir 0) hP0_cd).add (hD_cd (B0579.dir 1) hP1_cd)
  set K_box : Set ((ℝ × ℝ) × B0579.Plane) :=
    (Icc 0 Sig ×ˢ Icc (-Lmax) 0) ×ˢ (Icc (-(R₀ + 1)) (R₀ + 1) ×ˢ Icc (-(R₀ + 1)) (R₀ + 1))
  have hK_comp : IsCompact K_box :=
    (isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨M0, hM0⟩ := hK_comp.exists_bound_of_continuousOn hP0_cd.continuous.continuousOn
  obtain ⟨M1, hM1⟩ := hK_comp.exists_bound_of_continuousOn hP1_cd.continuous.continuousOn
  obtain ⟨ML, hML⟩ := hK_comp.exists_bound_of_continuousOn hL_cd.continuous.continuousOn
  set M_psi : ℝ := max 1 (max M0 (max M1 ML))
  refine ⟨M_psi, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro σ hσ t₁ r hrt x
  by_cases hx : x ∈ Icc (-(R₀ + 1)) (R₀ + 1) ×ˢ Icc (-(R₀ + 1)) (R₀ + 1)
  · have hfn_eq : psi0 g_w σ t₁ r = fun y => G_tot ((σ, r - t₁), y) := by
      funext y
      dsimp [psi0, G_tot]
      rw [safeFlow_eq_frozenRadialFlow hσ.1]
    have hq_mem : ((σ, r - t₁), x) ∈ K_box := ⟨⟨hσ, hrt⟩, hx⟩
    have h_pd0_eq : B0579.pd 0 (psi0 g_w σ t₁ r) x = P0 ((σ, r - t₁), x) := by
      rw [hfn_eq, hD_eq 0 hG_cd]
    have h_pd1_eq : B0579.pd 1 (psi0 g_w σ t₁ r) x = P1 ((σ, r - t₁), x) := by
      rw [hfn_eq, hD_eq 1 hG_cd]
    have h_lap_eq : lapP (psi0 g_w σ t₁ r) x = L_tot ((σ, r - t₁), x) := by
      unfold lapP
      have e0 : B0579.pd 0 (psi0 g_w σ t₁ r) = fun y => P0 ((σ, r - t₁), y) := by
        funext y; rw [hfn_eq, hD_eq 0 hG_cd]
      have e1 : B0579.pd 1 (psi0 g_w σ t₁ r) = fun y => P1 ((σ, r - t₁), y) := by
        funext y; rw [hfn_eq, hD_eq 1 hG_cd]
      rw [e0, e1, hD_eq 0 hP0_cd, hD_eq 1 hP1_cd]
    rw [h_pd0_eq, h_pd1_eq, h_lap_eq]
    have b0 := hM0 _ hq_mem
    have b1 := hM1 _ hq_mem
    have bL := hML _ hq_mem
    rw [Real.norm_eq_abs] at b0 b1 bL
    refine ⟨b0.trans ((le_max_left _ _).trans (le_max_right _ _)),
      b1.trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))),
      bL.trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))⟩
  · obtain ⟨_, hp0, hp1, hlp⟩ := psi0_vanish_of_sq_gt hg_supp σ t₁ r (sq_gt_of_not_mem_box hR₀ hx)
    rw [hp0, hp1, hlp, abs_zero]
    have hpos : 0 ≤ M_psi := (lt_of_lt_of_le one_pos (le_max_left _ _)).le
    exact ⟨hpos, hpos, hpos⟩

/-! ### `c`-periodization `periodizePsi0` -/

def periodizePsi0 (c : ℝ) (g_w : B0579.Plane → ℝ) (σ t₁ r : ℝ) (x : B0579.Plane) : ℝ :=
  ∑' n : ℤ, psi0 g_w σ t₁ r (x.1 - (n : ℝ) * c, x.2)

theorem periodic_periodizePsi0 (c : ℝ) (g_w : B0579.Plane → ℝ) (σ t₁ r : ℝ) (x : B0579.Plane) :
    periodizePsi0 c g_w σ t₁ r (x.1 + c, x.2) = periodizePsi0 c g_w σ t₁ r x := by
  unfold periodizePsi0
  have hshift : (fun n : ℤ => psi0 g_w σ t₁ r (x.1 + c - (n : ℝ) * c, x.2)) =
      fun n : ℤ => psi0 g_w σ t₁ r (x.1 - ((n - 1 : ℤ) : ℝ) * c, x.2) := by
    funext n
    congr 2
    push_cast
    ring
  rw [hshift]
  exact (Equiv.subRight (1 : ℤ)).tsum_eq (fun m : ℤ => psi0 g_w σ t₁ r (x.1 - (m : ℝ) * c, x.2))

theorem periodizePsi0_eq_shift_on_strip {c R₀ : ℝ} (hR₀ : 1 ≤ R₀) (hc : 4 * (R₀ + 1) ≤ c)
    {g_w : B0579.Plane → ℝ}
    (hg_supp : ∀ y : B0579.Plane, R₀ ^ 2 < y.1 ^ 2 + y.2 ^ 2 → g_w y = 0)
    (σ t₁ : ℝ) (k : ℤ) (r : ℝ) {x : B0579.Plane} (hx : |x.1 - (k : ℝ) * c| < 3 * c / 4) :
    periodizePsi0 c g_w σ t₁ r x = psi0 g_w σ t₁ r (x.1 - (k : ℝ) * c, x.2) := by
  unfold periodizePsi0
  refine tsum_eq_single k fun n hn => ?_
  have hc_pos : 0 < c := by linarith
  have hnk_ne : n - k ≠ 0 := sub_ne_zero.2 hn
  have hnk_one : (1 : ℝ) ≤ |((n - k : ℤ) : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |n - k| := Int.one_le_abs hnk_ne
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|n - k| : ℤ) : ℝ) := Int.cast_le.2 h1
    rw [Int.cast_abs] at h2
    simpa using h2
  have hsep : c ≤ |((n - k : ℤ) : ℝ) * c| := by
    rw [abs_mul, abs_of_pos hc_pos]
    nlinarith
  have hdiff_eq : x.1 - (n : ℝ) * c = (x.1 - (k : ℝ) * c) - ((n - k : ℤ) : ℝ) * c := by
    push_cast; ring
  have htri := abs_sub_abs_le_abs_sub (((n - k : ℤ) : ℝ) * c) (x.1 - (k : ℝ) * c)
  rw [abs_sub_comm (((n - k : ℤ) : ℝ) * c) (x.1 - (k : ℝ) * c)] at htri
  have habs_gt : R₀ + 1 < |x.1 - (n : ℝ) * c| := by
    rw [hdiff_eq]
    linarith
  have hsq_gt : R₀ ^ 2 < (x.1 - (n : ℝ) * c) ^ 2 + x.2 ^ 2 := by
    have h1 : (R₀ + 1) ^ 2 < |x.1 - (n : ℝ) * c| ^ 2 :=
      pow_lt_pow_left₀ habs_gt (by linarith) two_ne_zero
    rw [sq_abs] at h1
    nlinarith [sq_nonneg x.2]
  exact (psi0_vanish_of_sq_gt hg_supp σ t₁ r hsq_gt).1

private theorem contDiff_psi0_shift {g_w : B0579.Plane → ℝ} (hg : ContDiff ℝ ∞ g_w)
    (σ t₁ d : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × B0579.Plane => psi0 g_w σ t₁ z.1 (z.2.1 - d, z.2.2)) := by
  have hω : ContDiff ℝ ∞ (frozenOmega σ) := contDiff_frozenOmega σ
  unfold psi0 frozenRadialFlow
  simp only
  fun_prop

private theorem exists_int_shift_lt {c : ℝ} (hc : 0 < c) (q : ℝ) :
    ∃ k : ℤ, |q - (k : ℝ) * c| < 3 * c / 4 := by
  have hwrap := qwrap_mem_Ico hc q
  unfold qwrap at hwrap
  refine ⟨⌊(q + c / 2) / c⌋, ?_⟩
  set m : ℤ := ⌊(q + c / 2) / c⌋
  have hm : (m : ℝ) * c = c * (m : ℝ) := mul_comm _ _
  rw [hm, abs_lt]
  exact ⟨by linarith [hwrap.1], by linarith [hwrap.2]⟩

theorem contDiff_periodizePsi0 {c R₀ : ℝ} (hR₀ : 1 ≤ R₀) (hc : 4 * (R₀ + 1) ≤ c)
    {g_w : B0579.Plane → ℝ} (hg : ContDiff ℝ ∞ g_w)
    (hg_supp : ∀ y : B0579.Plane, R₀ ^ 2 < y.1 ^ 2 + y.2 ^ 2 → g_w y = 0)
    (σ t₁ : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × B0579.Plane => periodizePsi0 c g_w σ t₁ z.1 z.2) := by
  have hc_pos : 0 < c := by linarith
  rw [contDiff_iff_contDiffAt]
  intro z₀
  obtain ⟨k, hk_abs⟩ := exists_int_shift_lt hc_pos z₀.2.1
  have hV_open : IsOpen {z : ℝ × B0579.Plane | |z.2.1 - (k : ℝ) * c| < 3 * c / 4} :=
    isOpen_lt (((continuous_fst.comp continuous_snd).sub continuous_const).abs) continuous_const
  have hloc_cd : ContDiffAt ℝ ∞
      (fun z : ℝ × B0579.Plane => psi0 g_w σ t₁ z.1 (z.2.1 - (k : ℝ) * c, z.2.2)) z₀ :=
    (contDiff_psi0_shift hg σ t₁ ((k : ℝ) * c)).contDiffAt
  exact hloc_cd.congr_of_eventuallyEq
    (Filter.eventually_of_mem (hV_open.mem_nhds hk_abs) fun z hz =>
      periodizePsi0_eq_shift_on_strip hR₀ hc hg_supp σ t₁ k z.1 hz)

theorem periodizePsi0_on_cell {c R₀ : ℝ} (hR₀ : 1 ≤ R₀) (hc : 4 * (R₀ + 1) ≤ c)
    {g_w : B0579.Plane → ℝ}
    (hg_supp : ∀ y : B0579.Plane, R₀ ^ 2 < y.1 ^ 2 + y.2 ^ 2 → g_w y = 0)
    (σ t₁ r : ℝ) {x : B0579.Plane} (hx : x ∈ B0579.cell c) :
    periodizePsi0 c g_w σ t₁ r x = psi0 g_w σ t₁ r x ∧
      B0579.pd 0 (periodizePsi0 c g_w σ t₁ r) x = B0579.pd 0 (psi0 g_w σ t₁ r) x ∧
      B0579.pd 1 (periodizePsi0 c g_w σ t₁ r) x = B0579.pd 1 (psi0 g_w σ t₁ r) x ∧
      lapP (periodizePsi0 c g_w σ t₁ r) x = lapP (psi0 g_w σ t₁ r) x ∧
      deriv (fun r' => periodizePsi0 c g_w σ t₁ r' x) r =
        deriv (fun r' => psi0 g_w σ t₁ r' x) r := by
  have hx1 : |x.1| < 3 * c / 4 := by
    have hmem : x.1 ∈ Ico (-(c / 2)) (c / 2) := hx.1
    rw [abs_lt]
    exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  set S₀ : Set B0579.Plane := {y | |y.1| < 3 * c / 4}
  have hS₀_open : IsOpen S₀ := isOpen_lt continuous_fst.abs continuous_const
  have heq_on : ∀ r' : ℝ, ∀ y ∈ S₀, periodizePsi0 c g_w σ t₁ r' y = psi0 g_w σ t₁ r' y := by
    intro r' y hy
    have hy0 : |y.1| < 3 * c / 4 := hy
    have hy' : |y.1 - ((0 : ℤ) : ℝ) * c| < 3 * c / 4 := by simpa using hy0
    simpa using periodizePsi0_eq_shift_on_strip hR₀ hc hg_supp σ t₁ 0 r' hy'
  have hpd_on : ∀ (j : Fin 2), ∀ y ∈ S₀,
      B0579.pd j (periodizePsi0 c g_w σ t₁ r) y = B0579.pd j (psi0 g_w σ t₁ r) y := by
    intro j y hy
    have hevy : periodizePsi0 c g_w σ t₁ r =ᶠ[𝓝 y] psi0 g_w σ t₁ r :=
      Filter.eventually_of_mem (hS₀_open.mem_nhds hy) (heq_on r)
    unfold B0579.pd
    rw [hevy.fderiv_eq]
  have hpd2_eq : ∀ j : Fin 2,
      B0579.pd j (B0579.pd j (periodizePsi0 c g_w σ t₁ r)) x =
        B0579.pd j (B0579.pd j (psi0 g_w σ t₁ r)) x := by
    intro j
    have hevj : B0579.pd j (periodizePsi0 c g_w σ t₁ r) =ᶠ[𝓝 x] B0579.pd j (psi0 g_w σ t₁ r) :=
      Filter.eventually_of_mem (hS₀_open.mem_nhds hx1) (hpd_on j)
    change (fderiv ℝ (B0579.pd j (periodizePsi0 c g_w σ t₁ r)) x) (B0579.dir j) =
      (fderiv ℝ (B0579.pd j (psi0 g_w σ t₁ r)) x) (B0579.dir j)
    rw [hevj.fderiv_eq]
  have hr_eq : (fun r' => periodizePsi0 c g_w σ t₁ r' x) = fun r' => psi0 g_w σ t₁ r' x :=
    funext fun r' => heq_on r' x hx1
  exact ⟨heq_on r x hx1, hpd_on 0 x hx1, hpd_on 1 x hx1,
    by unfold lapP; rw [hpd2_eq 0, hpd2_eq 1],
    by rw [hr_eq]⟩

theorem isCylEtaTest_periodizePsi0 {c R₀ : ℝ} (hR₀ : 1 ≤ R₀) (hc : 4 * (R₀ + 1) ≤ c)
    {g_w : B0579.Plane → ℝ} (hg : ContDiff ℝ ∞ g_w)
    (hg_supp : ∀ y : B0579.Plane, R₀ ^ 2 < y.1 ^ 2 + y.2 ^ 2 → g_w y = 0)
    (σ t t₁ : ℝ) :
    CylEtaTest c t t₁ (periodizePsi0 c g_w σ t₁) := by
  have hc_pos : 0 < c := by linarith
  set Φ : ℝ × B0579.Plane → ℝ := fun z => periodizePsi0 c g_w σ t₁ z.1 z.2
  have hΦ_cd : ContDiff ℝ ∞ Φ := contDiff_periodizePsi0 hR₀ hc hg hg_supp σ t₁
  have hΦ_per : ∀ (d_int : ℤ) (z : ℝ × B0579.Plane),
      Φ (z.1, (z.2.1 + (d_int : ℝ) * c, z.2.2)) = Φ z := by
    intro d_int z
    have hp : Function.Periodic (fun q : ℝ => periodizePsi0 c g_w σ t₁ z.1 (q, z.2.2)) c :=
      fun q => periodic_periodizePsi0 c g_w σ t₁ z.1 (q, z.2.2)
    exact hp.int_mul d_int z.2.1
  have hvan_eta : ∀ (r : ℝ) {y : B0579.Plane}, R₀ + 1 < |y.2| → Φ (r, y) = 0 := by
    intro r y hy
    dsimp [Φ, periodizePsi0]
    have hz : (fun n : ℤ => psi0 g_w σ t₁ r (y.1 - (n : ℝ) * c, y.2)) = fun _ => 0 := by
      funext n
      have hsq : R₀ ^ 2 < (y.1 - (n : ℝ) * c) ^ 2 + y.2 ^ 2 := by
        have h1 : (R₀ + 1) ^ 2 < |y.2| ^ 2 := pow_lt_pow_left₀ hy (by linarith) two_ne_zero
        rw [sq_abs] at h1
        nlinarith [sq_nonneg (y.1 - (n : ℝ) * c)]
      exact (psi0_vanish_of_sq_gt hg_supp σ t₁ r hsq).1
    rw [hz, tsum_zero]
  have hU_eta : IsOpen {y : B0579.Plane | R₀ + 1 < |y.2|} :=
    isOpen_lt continuous_const continuous_snd.abs
  set drPhi := dSpaceTime Φ (1, (0, 0))
  set p0Phi := dSpaceTime Φ (0, B0579.dir 0)
  set p1Phi := dSpaceTime Φ (0, B0579.dir 1)
  set lapPhi := fun z => dSpaceTime p0Phi (0, B0579.dir 0) z + dSpaceTime p1Phi (0, B0579.dir 1) z
  have hdr_cd : ContDiff ℝ ∞ drPhi := contDiff_dSpaceTime hΦ_cd _
  have hp0_cd : ContDiff ℝ ∞ p0Phi := contDiff_dSpaceTime hΦ_cd _
  have hp1_cd : ContDiff ℝ ∞ p1Phi := contDiff_dSpaceTime hΦ_cd _
  have hlap_cd : ContDiff ℝ ∞ lapPhi :=
    (contDiff_dSpaceTime hp0_cd _).add (contDiff_dSpaceTime hp1_cd _)
  refine ⟨hΦ_cd.contDiffOn, fun r _ x => periodic_periodizePsi0 c g_w σ t₁ r x, ?_, ?_⟩
  · intro N
    set F_sp : ℝ × B0579.Plane → ℝ := fun z =>
      (|Φ z| + |p0Phi z| + |p1Phi z| + |lapPhi z|) * (1 + z.2.2 ^ 2) ^ N
    have hF_cont : Continuous F_sp := by
      refine Continuous.mul ?_ ?_
      · exact (((hΦ_cd.continuous.abs.add hp0_cd.continuous.abs).add
          hp1_cd.continuous.abs).add hlap_cd.continuous.abs)
      · exact (continuous_const.add (continuous_snd.comp continuous_snd |>.pow 2)).rpow_const
          fun z => Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)))
    set B_c : Set (ℝ × B0579.Plane) :=
      Icc t t₁ ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-(R₀ + 1)) (R₀ + 1))
    have hB_comp : IsCompact B_c :=
      isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    obtain ⟨C, hC⟩ := hB_comp.exists_bound_of_continuousOn hF_cont.continuousOn
    refine ⟨max C 0, fun r hr x => ?_⟩
    by_cases hy : R₀ + 1 < |x.2|
    · have hzero_y : ∀ y : B0579.Plane, R₀ + 1 < |y.2| → periodizePsi0 c g_w σ t₁ r y = 0 :=
        fun y hy' => hvan_eta r hy'
      have hpd_y : ∀ (j : Fin 2) (y : B0579.Plane), R₀ + 1 < |y.2| →
          B0579.pd j (periodizePsi0 c g_w σ t₁ r) y = 0 := by
        intro j y hy'
        have hevy : periodizePsi0 c g_w σ t₁ r =ᶠ[𝓝 y] fun _ => (0 : ℝ) :=
          Filter.eventually_of_mem (hU_eta.mem_nhds hy') hzero_y
        unfold B0579.pd; rw [hevy.fderiv_eq]; simp
      have hpd2_x : ∀ j : Fin 2, B0579.pd j (B0579.pd j (periodizePsi0 c g_w σ t₁ r)) x = 0 := by
        intro j
        have hevj : B0579.pd j (periodizePsi0 c g_w σ t₁ r) =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
          Filter.eventually_of_mem (hU_eta.mem_nhds hy) (hpd_y j)
        change (fderiv ℝ (B0579.pd j (periodizePsi0 c g_w σ t₁ r)) x) (B0579.dir j) = 0
        rw [hevj.fderiv_eq]; simp
      have hlap_x : lapP (periodizePsi0 c g_w σ t₁ r) x = 0 := by
        unfold lapP; rw [hpd2_x 0, hpd2_x 1, add_zero]
      rw [hzero_y x hy, hpd_y 0 x hy, hpd_y 1 x hy, hlap_x]
      simp only [abs_zero, add_zero, zero_mul]
      exact le_max_right C 0
    · rw [not_lt] at hy
      set k : ℤ := ⌊(x.1 + c / 2) / c⌋
      have hwrap := qwrap_mem_Ico hc_pos x.1
      unfold qwrap at hwrap
      set y : B0579.Plane := (x.1 + ((-k : ℤ) : ℝ) * c, x.2)
      have hy_mem : (r, y) ∈ B_c := by
        refine ⟨hr, ?_, abs_le.1 hy⟩
        have h1 : -(c / 2) ≤ x.1 - c * (k : ℝ) := hwrap.1
        have h2 : x.1 - c * (k : ℝ) < c / 2 := hwrap.2
        dsimp [y]; push_cast
        exact ⟨by linarith, by linarith⟩
      have hd_per : ∀ z : ℝ × B0579.Plane,
          Φ (z.1, (z.2.1 + ((-k : ℤ) : ℝ) * c, z.2.2)) = Φ z := hΦ_per (-k)
      have hp0_per : ∀ z : ℝ × B0579.Plane,
          p0Phi (z.1, (z.2.1 + ((-k : ℤ) : ℝ) * c, z.2.2)) = p0Phi z :=
        dSpaceTime_shift _ hd_per _
      have hp1_per : ∀ z : ℝ × B0579.Plane,
          p1Phi (z.1, (z.2.1 + ((-k : ℤ) : ℝ) * c, z.2.2)) = p1Phi z :=
        dSpaceTime_shift _ hd_per _
      have hlap_per : lapPhi (r, y) = lapPhi (r, x) := by
        dsimp [lapPhi, y]
        rw [dSpaceTime_shift _ hp0_per _ (r, x), dSpaceTime_shift _ hp1_per _ (r, x)]
      have h_eq0 : B0579.pd 0 (periodizePsi0 c g_w σ t₁ r) x = p0Phi (r, x) :=
        pd_space_eq_dSpaceTime hΦ_cd 0 r x
      have h_eq1 : B0579.pd 1 (periodizePsi0 c g_w σ t₁ r) x = p1Phi (r, x) :=
        pd_space_eq_dSpaceTime hΦ_cd 1 r x
      have h_eql : lapP (periodizePsi0 c g_w σ t₁ r) x = lapPhi (r, x) := by
        unfold lapP
        have e0 : B0579.pd 0 (periodizePsi0 c g_w σ t₁ r) = fun w => p0Phi (r, w) :=
          funext fun w => pd_space_eq_dSpaceTime hΦ_cd 0 r w
        have e1 : B0579.pd 1 (periodizePsi0 c g_w σ t₁ r) = fun w => p1Phi (r, w) :=
          funext fun w => pd_space_eq_dSpaceTime hΦ_cd 1 r w
        rw [e0, e1, pd_space_eq_dSpaceTime hp0_cd 0 r x, pd_space_eq_dSpaceTime hp1_cd 1 r x]
      have hF_eq : (|periodizePsi0 c g_w σ t₁ r x| +
          |B0579.pd 0 (periodizePsi0 c g_w σ t₁ r) x| +
          |B0579.pd 1 (periodizePsi0 c g_w σ t₁ r) x| +
          |lapP (periodizePsi0 c g_w σ t₁ r) x|) * (1 + x.2 ^ 2) ^ N = F_sp (r, y) := by
        rw [h_eq0, h_eq1, h_eql]
        dsimp [F_sp, y]
        rw [hd_per (r, x), hp0_per (r, x), hp1_per (r, x), hlap_per]
      rw [hF_eq]
      have hb := hC _ hy_mem
      have hsum_nn : 0 ≤ |Φ (r, y)| + |p0Phi (r, y)| + |p1Phi (r, y)| + |lapPhi (r, y)| :=
        add_nonneg (add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
          (abs_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hsum_nn
        (Real.rpow_nonneg (add_nonneg zero_le_one (sq_nonneg _)) N))] at hb
      exact hb.trans (le_max_left C 0)
  · intro N
    set F_r : ℝ × B0579.Plane → ℝ := fun z => |drPhi z| * (1 + z.2.2 ^ 2) ^ N
    have hFr_cont : Continuous F_r :=
      hdr_cd.continuous.abs.mul
        ((continuous_const.add (continuous_snd.comp continuous_snd |>.pow 2)).rpow_const
          fun z => Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _))))
    set B_c : Set (ℝ × B0579.Plane) :=
      Icc t t₁ ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-(R₀ + 1)) (R₀ + 1))
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).exists_bound_of_continuousOn
      hFr_cont.continuousOn
    refine ⟨max C 0, fun r hr x => ?_⟩
    by_cases hy : R₀ + 1 < |x.2|
    · have hr_zero : (fun r' => periodizePsi0 c g_w σ t₁ r' x) = fun _ => (0 : ℝ) :=
        funext fun r' => hvan_eta r' hy
      rw [hr_zero, deriv_const, abs_zero, zero_mul]
      exact le_max_right C 0
    · rw [not_lt] at hy
      set k : ℤ := ⌊(x.1 + c / 2) / c⌋
      have hwrap := qwrap_mem_Ico hc_pos x.1
      unfold qwrap at hwrap
      set y : B0579.Plane := (x.1 + ((-k : ℤ) : ℝ) * c, x.2)
      have hy_mem : (r, y) ∈ B_c := by
        refine ⟨Ioo_subset_Icc_self hr, ?_, abs_le.1 hy⟩
        have h1 : -(c / 2) ≤ x.1 - c * (k : ℝ) := hwrap.1
        have h2 : x.1 - c * (k : ℝ) < c / 2 := hwrap.2
        dsimp [y]; push_cast
        exact ⟨by linarith, by linarith⟩
      have hdr_eq : deriv (fun r' => periodizePsi0 c g_w σ t₁ r' x) r = drPhi (r, x) :=
        deriv_time_eq_dSpaceTime hΦ_cd r x
      have hdr_per : drPhi (r, y) = drPhi (r, x) :=
        dSpaceTime_shift _ (hΦ_per (-k)) _ (r, x)
      have hF_eq : |deriv (fun r' => periodizePsi0 c g_w σ t₁ r' x) r| * (1 + x.2 ^ 2) ^ N =
          F_r (r, y) := by
        rw [hdr_eq]
        dsimp [F_r, y]
        rw [hdr_per]
      rw [hF_eq]
      have hb := hC _ hy_mem
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
        (Real.rpow_nonneg (add_nonneg zero_le_one (sq_nonneg _)) N))] at hb
      exact hb.trans (le_max_left C 0)

end UnforcedLeray.Short.IIb.CompactDuhamelFreeHelp
