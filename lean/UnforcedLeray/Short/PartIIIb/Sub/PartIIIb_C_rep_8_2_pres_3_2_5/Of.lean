import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1.Sub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.Core
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.InletProfileJetsAt
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSup

/-!
# `exactGradBound` from `PartIIa.RingBoundedDerivs` (task `PartIII-b:C/rep/8/2/pres/3/2/5`, step)

Source `the November 2 reference manuscript`
lines 1217-1219, 1322-1325 (the raw lift has globally bounded fixed derivatives, `P_k`, task
`PartII-a:R07`), 2697-2713, 5287-5289 and 2383 (`‖E_εα‖_{W^{j,∞}} ≤ P_{ν,j}|α|`, `|α_i| ≤ ρ_b`),
5134-5139 (`‖∇r_b‖_∞ ≤ P_νρ`).

`U = V + r_b`, `V = U_raw + Σ α_i E_i`; `U`, `U_raw`, `E_i` are smooth, so `r_b` is, and
`∇U = ∇U_raw + Σ α_i ∇E_i + ∇r_b`, each term `≤ C ν^{-k}` at every point.
Only `RingBoundedDerivs` (PartII-a:R07, unproved) is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set Filter Topology
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params)
open UnforcedLeray UnforcedLeray.Short.IIb

namespace ExGradOf

/-- The raw lift is smooth with `‖∇ raw‖ ≤ C ν^{-k}`, from `RingBoundedDerivs` at `ρ = 2`. -/
theorem rawGrad_of (h : Short.PartIIa.RingBoundedDerivs) (dm dp : ℝ) (hdm : 0 < dm) :
    ∃ (ν₀ C : ℝ) (k : ℕ), 0 < ν₀ ∧ ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ τ, ContDiff ℝ ∞ (p.raw τ) ∧ ∀ y, ‖fderiv ℝ (p.raw τ) y‖ ≤ C * p.ν⁻¹ ^ k := by
  obtain ⟨ν₀, hν₀, C, d, H⟩ := h 2 1 (by norm_num)
  refine ⟨min (ν₀ / 2) (min dm 1), |C| * 3 ^ d, 2 * d, lt_min (by linarith) (lt_min hdm one_pos),
    fun p dd hreg hν τ => ?_⟩
  have hb := hreg.train_buc
  have hν1 : p.ν ≤ ν₀ / 2 := hν.trans (min_le_left _ _)
  have hν2 : p.ν ≤ dm := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν3 : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hνp := p.ν_pos
  obtain ⟨U, hU, hoff, hB⟩ := H p.ν ⟨hνp, by linarith⟩ _ _
    (isExactPlanarTrain_params_rpow p hb hreg.c_eq) p.R (R_ge_two hreg hν2)
  have hcont : ∀ τ, Continuous (fun y => U τ y) := fun τ => (hU τ).continuous
  have hraw : ∀ τ, p.raw τ = U τ := fun τ =>
    raw_eq_of hb (fun x => U x.1 x.2) hcont (fun x hx => hoff x.1 x.2 hx) τ
  rw [hraw τ]
  refine ⟨hU τ, fun y => ?_⟩
  have h1 := hB 1 le_rfl τ y
  rw [norm_iteratedFDeriv_one] at h1
  refine h1.trans ?_
  unfold Short.PartIIa.polyConst
  have ha : 1 ≤ p.ν⁻¹ := one_le_inv_iff₀.2 ⟨hνp, hν3⟩
  have hr : p.ν ^ (-(2 : ℝ)) = p.ν⁻¹ ^ 2 := by
    rw [Real.rpow_neg hνp.le]; norm_num
  rw [hr]
  have hs : 1 + p.ν⁻¹ ^ 2 + p.ν⁻¹ ≤ 3 * p.ν⁻¹ ^ 2 := by nlinarith
  have hp : (1 + p.ν⁻¹ ^ 2 + p.ν⁻¹) ^ d ≤ (3 * p.ν⁻¹ ^ 2) ^ d :=
    pow_le_pow_left₀ (by positivity) hs d
  calc C * (1 + p.ν⁻¹ ^ 2 + p.ν⁻¹) ^ d ≤ |C| * (3 * p.ν⁻¹ ^ 2) ^ d :=
        mul_le_mul (le_abs_self C) hp (by positivity) (abs_nonneg _)
    _ = |C| * 3 ^ d * p.ν⁻¹ ^ (2 * d) := by rw [mul_pow, ← pow_mul]; ring

theorem norm_E2_le (a : Fin 2 → ℝ) :
    ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin 2))‖ ≤ |a 0| + |a 1| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs]
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg (a 0), abs_nonneg (a 1), sq_abs (a 0), sq_abs (a 1)]

end ExGradOf

namespace SeqData

/-- **`exactGradBound` from `RingBoundedDerivs`** (source 1217-1219, 1322-1325, 2383, 2697-2713,
5134-5139). -/
theorem exactGradBound_of (h : Short.PartIIa.RingBoundedDerivs) (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) : D.ExactGradBound := by
  obtain ⟨ν₁, C1, k1, hν₁, H1⟩ := ExGradOf.rawGrad_of h dm dp hst.dm_pos
  obtain ⟨C2, k2, ν₂, hC2, hν₂, H2⟩ := inletSupBound D.Sig D.Pl.eigenvalue D.Pl.mode D.Sig_pos
    hst.planar.eigenpair dm dp hst.dm_pos 1
  obtain ⟨C3, k3, hrep⟩ := hst.repairDeriv
  have hC0 := hst.C0_pos
  have hm : 0 < min ν₁ (min ν₂ 1) := lt_min hν₁ (lt_min hν₂ one_pos)
  refine ⟨|C1| + 2 * C2 * D.K.C0 + |C3|, max k1 (max (k2 + D.K.k0) k3), ?_⟩
  have hνev : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ min ν₁ (min ν₂ 1) :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds hm)
  filter_upwards [hst.actual, hνev, rhoRep_le_one_eventually D hst, hrep] with n hn hν hρ hr
  have hνa : (D.level n).ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hνb : (D.level n).ν ≤ ν₂ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνc : (D.level n).ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  set L := D.level n with hL
  have hνp : 0 < L.ν := L.ν_pos
  have ha : 1 ≤ L.ν⁻¹ := one_le_inv_iff₀.2 ⟨hνp, hνc⟩
  have hreg := hn.regime
  obtain ⟨z, -, hV, -, hα⟩ := hn.split.state
  have hq := hst.planar.eigenpair
  have hall : ∀ (τ : ℝ) (y : Space), ‖fderiv ℝ (L.U τ) y‖ ≤
      (|C1| + 2 * C2 * D.K.C0 + |C3|) * L.ν⁻¹ ^ (max k1 (max (k2 + D.K.k0) k3)) := by
    intro τ y
    obtain ⟨hrawsm, hrawb⟩ := H1 (L.params D.Pl) _ hreg hνa τ
    have hinl : ∀ i : Fin 2, ContDiff ℝ 2 ((L.params D.Pl).inlet i τ) := fun i =>
      (bgInletColumnJets_of bgInletProfileJetsAt D.Pl.eigenvalue D.Pl.mode hq (L.params D.Pl) _ dm dp
        hreg hνc rfl i).1 τ
    set S : Space → Space := fun w => ∑ i : Fin 2, (L.params D.Pl).coord z i •
      (L.params D.Pl).inlet i τ w with hS
    have hSd : Differentiable ℝ S :=
      (ContDiff.sum fun i _ => (hinl i).const_smul _).differentiable (by norm_num)
    have hVeq : L.V τ = fun w => (L.params D.Pl).raw τ w + S w := funext (hV τ)
    have hUd : Differentiable ℝ (L.U τ) := by
      have h1 := hn.profile.smoothU.comp (contDiff_const.prodMk contDiff_id :
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' : Space => ((τ, y') : ℝ × Space)))
      exact h1.differentiable (by simp)
    have hVd : Differentiable ℝ (L.V τ) := by
      rw [hVeq]; exact (hrawsm.differentiable (by simp)).add hSd
    have hrbd : Differentiable ℝ (L.rb τ) := by
      have : L.rb τ = fun w => L.U τ w - L.V τ w := by
        funext w; simp [ReturnLevel.U]
      rw [this]; exact hUd.sub hVd
    have e1 : fderiv ℝ (L.U τ) y = fderiv ℝ (L.V τ) y + fderiv ℝ (L.rb τ) y := by
      have : L.U τ = fun w => L.V τ w + L.rb τ w := rfl
      rw [this]; exact fderiv_add (hVd y) (hrbd y)
    have e2 : fderiv ℝ (L.V τ) y = fderiv ℝ ((L.params D.Pl).raw τ) y + fderiv ℝ S y := by
      rw [hVeq]; exact fderiv_add (hrawsm.differentiable (by simp) y) (hSd y)
    -- the three terms
    have T1 := hrawb y
    have T2 : ‖fderiv ℝ S y‖ ≤ C2 * ((L.params D.Pl).ν ^ k2)⁻¹ *
        ‖(WithLp.toLp 2 ((L.params D.Pl).coord z) : EuclideanSpace ℝ (Fin 2))‖ := by
      have := H2 (L.params D.Pl) _ hreg hνb rfl rfl
        (WithLp.toLp 2 ((L.params D.Pl).coord z)) τ y
      rw [norm_iteratedFDeriv_one] at this
      exact this
    have T3 := (hr.1 τ y)
    have hρ0 := rhoRep_nonneg D.K L
    have hρb : L.ρb D.Pl D.K = D.K.C0 * L.ν⁻¹ ^ D.K.k0 * rhoRep D.K L := rhoB_eq D.Pl D.K L
    have hα0 : |(L.params D.Pl).coord z 0| ≤ L.ρb D.Pl D.K := hα 0
    have hα1 : |(L.params D.Pl).coord z 1| ≤ L.ρb D.Pl D.K := hα 1
    have hαn : ‖(WithLp.toLp 2 ((L.params D.Pl).coord z) : EuclideanSpace ℝ (Fin 2))‖ ≤
        2 * (D.K.C0 * L.ν⁻¹ ^ D.K.k0) := by
      refine (ExGradOf.norm_E2_le _).trans ?_
      have hρc : D.K.C0 * L.ν⁻¹ ^ D.K.k0 * rhoRep D.K L ≤ D.K.C0 * L.ν⁻¹ ^ D.K.k0 := by
        calc _ ≤ D.K.C0 * L.ν⁻¹ ^ D.K.k0 * 1 :=
              mul_le_mul_of_nonneg_left hρ (by positivity)
          _ = _ := mul_one _
      rw [hρb] at hα0 hα1
      linarith
    have hpow : ∀ j : ℕ, j ≤ max k1 (max (k2 + D.K.k0) k3) → L.ν⁻¹ ^ j ≤
        L.ν⁻¹ ^ (max k1 (max (k2 + D.K.k0) k3)) := fun j hj => pow_le_pow_right₀ ha hj
    have hν' : (L.params D.Pl).ν = L.ν := rfl
    rw [hν'] at T1 T2
    have c1 : C1 * L.ν⁻¹ ^ k1 ≤ |C1| * L.ν⁻¹ ^ (max k1 (max (k2 + D.K.k0) k3)) :=
      mul_le_mul (le_abs_self _) (hpow _ (le_max_left _ _)) (by positivity) (abs_nonneg _)
    have c2 : C2 * (L.ν ^ k2)⁻¹ * (2 * (D.K.C0 * L.ν⁻¹ ^ D.K.k0)) ≤
        2 * C2 * D.K.C0 * L.ν⁻¹ ^ (max k1 (max (k2 + D.K.k0) k3)) := by
      have : C2 * (L.ν ^ k2)⁻¹ * (2 * (D.K.C0 * L.ν⁻¹ ^ D.K.k0)) =
          2 * C2 * D.K.C0 * L.ν⁻¹ ^ (k2 + D.K.k0) := by
        rw [inv_pow, pow_add]; ring
      rw [this]
      refine mul_le_mul_of_nonneg_left (hpow _ ?_) (by positivity)
      exact (le_max_left _ _).trans (le_max_right _ _)
    have c3 : C3 * L.ν⁻¹ ^ k3 * rhoRep D.K L ≤
        |C3| * L.ν⁻¹ ^ (max k1 (max (k2 + D.K.k0) k3)) := by
      have hk : 0 ≤ L.ν⁻¹ ^ k3 := by positivity
      calc C3 * L.ν⁻¹ ^ k3 * rhoRep D.K L ≤ |C3| * L.ν⁻¹ ^ k3 * rhoRep D.K L :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hk) hρ0
        _ ≤ |C3| * L.ν⁻¹ ^ k3 * 1 :=
            mul_le_mul_of_nonneg_left hρ (mul_nonneg (abs_nonneg _) hk)
        _ = |C3| * L.ν⁻¹ ^ k3 := mul_one _
        _ ≤ |C3| * L.ν⁻¹ ^ (max k1 (max (k2 + D.K.k0) k3)) :=
            mul_le_mul_of_nonneg_left (hpow _ ((le_max_right _ _).trans' (le_max_right _ _)))
              (abs_nonneg _)
    rw [e1, e2]
    have hn0 : 0 ≤ (L.ν ^ k2)⁻¹ := by positivity
    have hS2 : ‖fderiv ℝ S y‖ ≤ 2 * C2 * D.K.C0 * L.ν⁻¹ ^ (max k1 (max (k2 + D.K.k0) k3)) :=
      T2.trans ((mul_le_mul_of_nonneg_left hαn (mul_nonneg hC2.le hn0)).trans c2)
    have hr3 : ‖fderiv ℝ (L.rb τ) y‖ ≤ |C3| * L.ν⁻¹ ^ (max k1 (max (k2 + D.K.k0) k3)) :=
      T3.trans c3
    have hT1 := T1.trans c1
    have t1 := norm_add_le (fderiv ℝ ((L.params D.Pl).raw τ) y) (fderiv ℝ S y)
    have t2 := norm_add_le (fderiv ℝ ((L.params D.Pl).raw τ) y + fderiv ℝ S y)
      (fderiv ℝ (L.rb τ) y)
    nlinarith [hT1, hS2, hr3, t1, t2]
  intro p _
  exact hall _ _

end SeqData

end UnforcedLeray.Short.PartIIIb.Concrete

#print axioms UnforcedLeray.Short.PartIIIb.Concrete.SeqData.exactGradBound_of
