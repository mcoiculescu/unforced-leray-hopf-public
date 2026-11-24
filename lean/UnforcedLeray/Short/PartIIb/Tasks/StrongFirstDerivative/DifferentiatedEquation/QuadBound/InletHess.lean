import UnforcedLeray.Short.PartIIb.Tasks.QuadraticEstimate.InletLp
import UnforcedLeray.Short.PartIIb.Tasks.StrongFirstDerivative.DifferentiatedEquation.QuadBound.NvJets

/-!
# Quantitative global bounds on the affine inlet (helper for `PartII-b:S1/1/2`)

Source `the November 2 reference manuscript`, lines
2385-2387 (the inlet jets decay in `η`), 2528-2531 (every differentiated term is in `Y_p`).

* `inlet_dydy_ptw`: off the axis, `‖∂_j∂_l e(τ, y)‖` is bounded by the ring envelope
  `M s (1+|η|)² e^{-κ|η|/c}` on `0 < s ≤ H/2` (and vanishes beyond), with
  `M = B (1+H)³ ν^{-k} ‖α‖` (second-order chain rule `nv_jetsQ`, `s^{3/2} = s · √s ≤ (1+H) s`).
* `inlet_dydy_phaseLpNorm_le`: the global `Y_{q₀}` bound
  `‖∂_j∂_l e‖_{Y_{q₀}} ≤ C ν^{-k} ‖z‖` (`eLpNorm_le_of_ringEnv1`, `R^{8/11} ‖α‖ ≤ ‖z‖`).
* `inlet_sup_le`: `‖e‖ ≤ C ν^{-k} ‖z‖` and `‖∂_j e‖ ≤ C ν^{-k} ‖z‖` everywhere.
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

/-- Jets of the inlet combination `α₀ψ₀ + α₁ψ₁` from the jets of the columns. -/
theorem comb_jets {p : Params} {CJ κ : ℝ} {kJ : ℕ}
    (HJ' : ∀ i : Fin 2, ContDiff ℝ ∞ (p.inletProfile i) ∧
      ∀ l ≤ 2, ∀ x : Coord, ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤
        CJ * (p.ν ^ kJ)⁻¹ * Real.exp (-(κ * |x.2.2| / p.c)))
    (α : Fin 2 → ℝ) (l : ℕ) (hl : l ≤ 2) (x : Coord) :
    ‖iteratedFDeriv ℝ l (α 0 • p.inletProfile 0 + α 1 • p.inletProfile 1) x‖ ≤
      2 * ‖α‖ * (CJ * (p.ν ^ kJ)⁻¹ * Real.exp (-(κ * |x.2.2| / p.c))) := by
  have hcd0 := (HJ' 0).1
  have hcd1 := (HJ' 1).1
  have hc0 : ContDiffAt ℝ l (α 0 • p.inletProfile 0) x :=
    ((hcd0.const_smul (α 0)).of_le (by exact_mod_cast le_top)).contDiffAt
  have hc1 : ContDiffAt ℝ l (α 1 • p.inletProfile 1) x :=
    ((hcd1.const_smul (α 1)).of_le (by exact_mod_cast le_top)).contDiffAt
  have hc0' : ContDiffAt ℝ l (p.inletProfile 0) x :=
    (hcd0.of_le (by exact_mod_cast le_top)).contDiffAt
  have hc1' : ContDiffAt ℝ l (p.inletProfile 1) x :=
    (hcd1.of_le (by exact_mod_cast le_top)).contDiffAt
  rw [iteratedFDeriv_add_apply hc0 hc1, iteratedFDeriv_const_smul_apply hc0',
    iteratedFDeriv_const_smul_apply hc1']
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul]
  have b0 := (HJ' 0).2 l hl x
  have b1 := (HJ' 1).2 l hl x
  have ha0 : ‖α 0‖ ≤ ‖α‖ := norm_le_pi_norm α 0
  have ha1 : ‖α 1‖ ≤ ‖α‖ := norm_le_pi_norm α 1
  calc ‖α 0‖ * ‖iteratedFDeriv ℝ l (p.inletProfile 0) x‖ +
        ‖α 1‖ * ‖iteratedFDeriv ℝ l (p.inletProfile 1) x‖
      ≤ ‖α‖ * (CJ * (p.ν ^ kJ)⁻¹ * Real.exp (-(κ * |x.2.2| / p.c))) +
          ‖α‖ * (CJ * (p.ν ^ kJ)⁻¹ * Real.exp (-(κ * |x.2.2| / p.c))) :=
        add_le_add (mul_le_mul ha0 b0 (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul ha1 b1 (norm_nonneg _) (norm_nonneg _))
    _ = 2 * ‖α‖ * (CJ * (p.ν ^ kJ)⁻¹ * Real.exp (-(κ * |x.2.2| / p.c))) := by ring

/-- `1 ≤ R` in the regime. -/
theorem one_le_R_of {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp) : 1 ≤ p.R := by
  have hνpos : 0 < p.ν := p.ν_pos
  have hRe : p.R⁻¹ = p.ε := by simp [Params.R]
  have hε1 : p.R⁻¹ ≤ 1 := by
    rw [hRe, hreg.eps_eq, Real.exp_le_one_iff]
    have := hreg.dm_le
    have := hreg.dm_pos
    have : 0 ≤ d / p.ν := div_nonneg (by linarith) hνpos.le
    rw [neg_div]
    linarith
  exact (inv_le_one₀ p.R_pos).1 hε1

/-- Small arithmetic facts used below. -/
theorem aux_sqrt_le {s H : ℝ} (hH : 0 < H) (hs : s ≤ H / 2) : √s ≤ 1 + H := by
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

theorem aux_W {s H η : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ H / 2) (hH : 0 < H) (hη : 0 ≤ η) :
    1 + s + η ≤ (1 + H) * (1 + η) := by
  nlinarith

theorem aux_R2 {R : ℝ} (hR : 1 ≤ R) : (1 + R) ^ 2 ≤ 4 * R ^ 2 := by
  nlinarith

/-- **Pointwise ring envelope of the inlet Hessian** off the axis. -/
theorem inlet_dydy_ptw
    (Sig : ℝ) (lam : ℂ) (q : Planar.Profile) (hSig : 0 < Sig)
    (hq : Planar.IsGrowingEigenpair lam q) (dm dp : ℝ) (hdm : 0 < dm) :
    ∃ (B κ : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < B ∧ 0 < κ ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
        ∀ (α : Fin 2 → ℝ) (j l : Fin 3) (τ : ℝ) (y : Space), y ∉ axis →
          ‖dy j (dy l (p.eFun α)) (τ, y)‖ ≤
            ringEnv1 p.H (B * (1 + p.H) ^ 3 * (p.ν ^ k)⁻¹ * ‖α‖) κ p.c 2
              (age p.R y) (trans p.R y) := by
  obtain ⟨CJ, κ, kJ, νJ, hCJ, hκ, hνJ, hνJ1, HJ⟩ :=
    inletJetDecay Sig lam q hSig hq dm dp hdm
  obtain ⟨νV, hνV, HV⟩ :=
    inletProfileSmoothVanish Sig lam q hSig hq dm dp hdm
  obtain ⟨K0, hK0, HN⟩ := nv_jetsQ
  refine ⟨8 * K0 * CJ, κ, kJ, min νJ νV, by positivity, hκ, lt_min hνJ hνV,
    (min_le_left _ _).trans hνJ1, ?_⟩
  intro p d hreg hν hS hm α j l τ y hy
  have h0 : p.ν ≤ νJ := hν.trans (min_le_left _ _)
  have h1 : p.ν ≤ νV := hν.trans (min_le_right _ _)
  have hν1 : p.ν ≤ 1 := h0.trans hνJ1
  have hνpos : 0 < p.ν := p.ν_pos
  have hHpos : 0 < p.H := p.H_pos
  have HJ' := HJ p d ⟨hreg, h0, hS, hm⟩
  have HV' := HV p d hreg h1 hS hm
  set e : ℝ × (ℝ × ℝ) → Merid := α 0 • p.inletProfile 0 + α 1 • p.inletProfile 1 with he
  have hcd0 : ContDiff ℝ ∞ (p.inletProfile 0) := (HV' 0).1
  have hcd1 : ContDiff ℝ ∞ (p.inletProfile 1) := (HV' 1).1
  have hecd : ContDiff ℝ ∞ e := (hcd0.const_smul (α 0)).add (hcd1.const_smul (α 1))
  have hvan : ∀ m : ℝ × (ℝ × ℝ), p.H / 2 < m.1 → e m = 0 := by
    intro m hm'
    have hz0 := (HV' 0).2 m hm'
    have hz1 := (HV' 1).2 m hm'
    simp [he, hz0, hz1]
  have heFun : p.eFun α = fun q : ℝ × Space => realC (Nv p.R e q.1 q.2) := by
    funext q
    simp only [Params.eFun, Params.inlet, Fin.sum_univ_two, he, Nv_add, Nv_smul]
  have hΦ : ContDiff ℝ ∞ (p.eFun α) := by
    unfold Params.eFun
    refine contDiff_realC.comp ?_
    refine ContDiff.sum fun l _ => ?_
    exact (inlet_contDiff_joint lam q hq hreg hν1 hm l).const_smul _
  have hM : 0 ≤ 8 * K0 * CJ * (1 + p.H) ^ 3 * (p.ν ^ kJ)⁻¹ * ‖α‖ := by positivity
  by_cases hle : age p.R y ≤ p.H / 2
  · have hRpos : 0 < p.R := p.R_pos
    have hR1 : 1 ≤ p.R := one_le_R_of hreg
    have hs0 : 0 < age p.R y := Axi.age_pos hRpos.ne' hy
    rw [ringEnv1_of_mem hs0 hle]
    have hNvs : ContDiff ℝ ∞ (fun x : ℝ × Space => Nv p.R e x.1 x.2) :=
      NicePT.contDiff_Nv hRpos hecd (s1 := p.H / 2) hvan
    have hsl : ContDiff ℝ ∞ (Nv p.R e τ) := by
      have hg : ContDiff ℝ ∞ (fun z : Space => ((τ, z) : ℝ × Space)) :=
        contDiff_const.prodMk contDiff_id
      have h2 : Nv p.R e τ = (fun x : ℝ × Space => Nv p.R e x.1 x.2) ∘
          (fun z : Space => ((τ, z) : ℝ × Space)) := by funext z; rfl
      rw [h2]
      exact hNvs.comp hg
    have hL : ‖dy j (dy l (p.eFun α)) (τ, y)‖ ≤ ‖iteratedFDeriv ℝ 2 (Nv p.R e τ) y‖ := by
      refine (dy_dy_le hΦ j l τ y).trans ?_
      have hsl' : (fun z : Space => p.eFun α (τ, z)) =
          fun z : Space => realC (Nv p.R e τ z) := by
        funext z; rw [heFun]
      rw [hsl']
      exact iter_realC_le hsl 2 y
    set x := chart p.R τ y with hxdef
    have hx1 : x.1 = age p.R y := rfl
    have hx2 : x.2.2 = trans p.R y := rfl
    set E := Real.exp (-(κ * |x.2.2| / p.c)) with hEd
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    set J := CJ * (p.ν ^ kJ)⁻¹ * E with hJ
    have hJ0 : 0 ≤ J := by positivity
    have hCm : ∀ i ≤ 2, ‖iteratedFDeriv ℝ i e x‖ ≤ 2 * ‖α‖ * J := by
      intro i hi
      exact comb_jets HJ' α i hi x
    have hD2 := HN p.R τ e hRpos hecd y hy (2 * ‖α‖ * J) hCm
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (ϱ y)⁻¹ := ⟨_, rfl⟩
    have ht0 : 0 ≤ t := by rw [ht]; exact inv_nonneg.2 (ϱ_nonneg y)
    have hs : age p.R y = p.R ^ 2 * t ^ 2 := by rw [age_eq_sq, ht]
    have hRt : p.R * t = √(age p.R y) := by rw [sqrt_age_eq_at hRpos, ht]
    have hsq : √(age p.R y) ≤ 1 + p.H := aux_sqrt_le hHpos hle
    rw [← ht] at hD2
    have hW : 1 + age p.R y + |trans p.R y| ≤ (1 + p.H) * (1 + |trans p.R y|) :=
      aux_W hs0.le hle hHpos (abs_nonneg _)
    have hW0 : 0 ≤ 1 + age p.R y + |trans p.R y| := by
      have : 0 ≤ |trans p.R y| := abs_nonneg _
      linarith
    have hW2 : (1 + age p.R y + |trans p.R y|) ^ 2 ≤ ((1 + p.H) * (1 + |trans p.R y|)) ^ 2 :=
      pow_le_pow_left₀ hW0 hW 2
    have hR2 : (1 + p.R) ^ 2 ≤ 4 * p.R ^ 2 := aux_R2 hR1
    have hαJ : 0 ≤ 2 * ‖α‖ * J := by positivity
    refine hL.trans (hD2.trans ?_)
    have hst : p.R * t ^ 3 * p.R ^ 2 = age p.R y * (p.R * t) := by rw [hs]; ring
    calc K0 * (1 + p.R) ^ 2 * p.R * (2 * ‖α‖ * J) * t ^ 3 *
          (1 + age p.R y + |trans p.R y|) ^ 2
        ≤ K0 * (4 * p.R ^ 2) * p.R * (2 * ‖α‖ * J) * t ^ 3 *
            ((1 + p.H) * (1 + |trans p.R y|)) ^ 2 := by
          gcongr
      _ = 8 * K0 * ‖α‖ * J * (p.R * t ^ 3 * p.R ^ 2) *
            ((1 + p.H) * (1 + |trans p.R y|)) ^ 2 := by ring
      _ = 8 * K0 * ‖α‖ * J * (age p.R y * (p.R * t)) *
            ((1 + p.H) * (1 + |trans p.R y|)) ^ 2 := by rw [hst]
      _ ≤ 8 * K0 * ‖α‖ * J * (age p.R y * (1 + p.H)) *
            ((1 + p.H) * (1 + |trans p.R y|)) ^ 2 := by
          rw [hRt]
          gcongr
      _ = 8 * K0 * CJ * (1 + p.H) ^ 3 * (p.ν ^ kJ)⁻¹ * ‖α‖ * age p.R y *
            ((1 + |trans p.R y|) ^ 2 * Real.exp (-(κ * |trans p.R y| / p.c))) := by
          rw [hJ, hEd, hx2]
          ring
  · set T := (p.H / 2 + age p.R y) / 2 with hTdef
    have hHT : p.H / 2 < T := by rw [hTdef]; linarith [not_le.1 hle]
    have hTa : T < age p.R y := by rw [hTdef]; linarith [not_le.1 hle]
    have hvanT : ∀ m : ℝ × (ℝ × ℝ), T ≤ m.1 → e m = 0 :=
      fun m hm' => hvan m (hHT.trans_le hm')
    have hev : ∀ᶠ q in 𝓝 (τ, y), p.eFun α q = 0 := by
      have h1 := nv_eventually_zero p.R_pos hvanT (Or.inr hTa)
      have h2 := (continuous_snd.tendsto (τ, y)).eventually h1
      filter_upwards [h2] with q hq
      rw [heFun]
      simp [hq q.1, realC]
    rw [dydy_eq_zero hev j l, norm_zero]
    exact ringEnv1_nonneg hM _ _

end UnforcedLeray.Short.IIb.QuadBoundSub
