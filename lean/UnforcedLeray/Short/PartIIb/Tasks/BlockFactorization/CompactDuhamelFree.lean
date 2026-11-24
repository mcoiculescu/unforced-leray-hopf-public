import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.CompactDuhamelFree.TransportedTest
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_2
import UnforcedLeray.Short.PartIIb.Tasks.FreeCylinderBound
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# `PartII-b:F2/4/1` (`CompactDuhamelFree.lean`): Free transport comparison on finite blocks

Source of record: `the November 2 reference manuscript`, lines 2104–2115.

Proves `freeTransportComparison_proof : UnforcedLeray.Short.IIb.FreeTransportComparison`:
for `m > 8` and `Sig, Lmax > 0`, the lifted free cylinder propagator `J_c ∘ Sc(t + L, t) ∘ R_c`
converges strongly on compact subsets of `X_m` to the frozen radial transport `T_pl(ν t, L)`
(equivalently `W_{ν,t} = J_c ∘ Sc(t + L, t) ∘ R_c ∘ T_pl(ν t, -L) → I` strongly on compact sets)
along with the operator-norm bound `‖Sc(t + L, t)‖ ≤ 1 + ε`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.IIb.CompactDuhamelFreeHelp

open UnforcedLeray.Cons.C03.Concrete PartIIbF23Sub FrozenTransportContHelp

private theorem contDiff_jb_rpow (m : ℝ) : ContDiff ℝ ∞ (fun y : B0579.Plane => B0579.jb y ^ m) := by
  have hjb_cd : ContDiff ℝ ∞ B0579.jb := by unfold B0579.jb; fun_prop
  have hlog : ContDiff ℝ ∞ (fun y : B0579.Plane => Real.log (B0579.jb y) * m) :=
    (hjb_cd.log fun y => (B0579.jb_pos y).ne').mul contDiff_const
  have heq : (fun y : B0579.Plane => B0579.jb y ^ m) =
      fun y => Real.exp (Real.log (B0579.jb y) * m) := by
    funext y
    exact Real.rpow_def_of_pos (B0579.jb_pos y) m
  rw [heq]
  exact Real.contDiff_exp.comp hlog

private theorem exists_radius_of_hasCompactSupport {g : B0579.Plane → ℝ} (hg : HasCompactSupport g) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ y : B0579.Plane, R₀ ^ 2 < y.1 ^ 2 + y.2 ^ 2 → g y = 0 := by
  obtain ⟨R₁, hR₁⟩ := hg.isCompact.isBounded.subset_closedBall (0 : B0579.Plane)
  set R₂ : ℝ := max R₁ 0
  set R₀ : ℝ := max 1 (2 * R₂ + 1)
  refine ⟨R₀, le_max_left _ _, fun y hy => ?_⟩
  by_contra hgy
  have hmem : y ∈ Metric.closedBall (0 : B0579.Plane) R₁ := hR₁ (subset_tsupport g hgy)
  rw [Metric.mem_closedBall, dist_zero_right] at hmem
  have hy1 : |y.1| ≤ R₂ := ((le_max_left |y.1| |y.2|).trans hmem).trans (le_max_left R₁ 0)
  have hy2 : |y.2| ≤ R₂ := ((le_max_right |y.1| |y.2|).trans hmem).trans (le_max_left R₁ 0)
  have hR₂_nn : 0 ≤ R₂ := le_max_right R₁ 0
  have hsq1 : y.1 ^ 2 ≤ R₂ ^ 2 := by
    rw [← sq_abs y.1]
    exact pow_le_pow_left₀ (abs_nonneg _) hy1 2
  have hsq2 : y.2 ^ 2 ≤ R₂ ^ 2 := by
    rw [← sq_abs y.2]
    exact pow_le_pow_left₀ (abs_nonneg _) hy2 2
  have hR₀_ge : 2 * R₂ + 1 ≤ R₀ := le_max_right 1 _
  have hR₀_sq : (2 * R₂ + 1) ^ 2 ≤ R₀ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hR₀_ge 2
  nlinarith

private theorem sq_gt_of_not_mem_cell {c R₀ : ℝ} (hR₀ : 1 ≤ R₀) (hc : 4 * (R₀ + 1) ≤ c)
    {x : B0579.Plane} (hx : x ∉ B0579.cell c) : R₀ ^ 2 < x.1 ^ 2 + x.2 ^ 2 := by
  have hx1_not : x.1 ∉ Ico (-(c / 2)) (c / 2) := fun h1 => hx ⟨h1, trivial⟩
  have habs : c / 2 ≤ |x.1| := by
    by_contra hlt
    rw [not_le, abs_lt] at hlt
    exact hx1_not ⟨hlt.1.le, hlt.2⟩
  have hgt : R₀ + 1 < |x.1| := by linarith
  have hsq : (R₀ + 1) ^ 2 < |x.1| ^ 2 := pow_lt_pow_left₀ hgt (by linarith) two_ne_zero
  rw [sq_abs] at hsq
  nlinarith [sq_nonneg x.2]

private theorem inner_Xm_eq_plane_integral (m : ℝ) (u v : Xm m) :
    inner ℝ u v = ∫ x : B0579.Plane, u x * (B0579.jb x ^ m * v x) := by
  rw [L2.inner_def]
  unfold planeMeasure
  rw [integral_withDensity_eq_integral_smul (B0579.measurable_density m)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, B0579.coe_density, Real.inner_apply]
  ring

private theorem integral_cell_density_sq {c m : ℝ} {u : B0579.Plane → ℝ}
    (hu : MemLp u 2 (B0579.cellMeasure c m)) :
    IntegrableOn (fun x => (B0579.density m x : ℝ) * u x ^ 2) (B0579.cell c) volume ∧
      ∫ x in B0579.cell c, (B0579.density m x : ℝ) * u x ^ 2 = ‖hu.toLp u‖ ^ 2 := by
  set w : Xmc c m := hu.toLp u
  have hw_ae : (w : B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell c)] u :=
    ae_restrict_cell_of_cellMeasure (MemLp.coeFn_toLp hu)
  have hint0 := (B0579.integrable_cellMeasure_iff c m).1 (L2.integrable_inner (𝕜 := ℝ) w w)
  have hint_w : IntegrableOn (fun x => (B0579.density m x : ℝ) * w x ^ 2) (B0579.cell c) volume := by
    refine hint0.congr_fun_ae (Eventually.of_forall fun x => ?_)
    simp only [NNReal.smul_def, smul_eq_mul, Real.inner_apply]
    ring
  have hint_u : IntegrableOn (fun x => (B0579.density m x : ℝ) * u x ^ 2) (B0579.cell c) volume := by
    refine hint_w.congr_fun_ae ?_
    filter_upwards [hw_ae] with x hx
    rw [hx]
  refine ⟨hint_u, ?_⟩
  have hnorm_sq : ‖w‖ ^ 2 = inner ℝ w w := (real_inner_self_eq_norm_sq w).symm
  rw [hnorm_sq, L2.inner_def, B0579.integral_cellMeasure]
  refine integral_congr_ae ?_
  filter_upwards [hw_ae] with x hx
  simp only [NNReal.smul_def, smul_eq_mul, Real.inner_apply]
  rw [hx]
  ring

private theorem inner_Jc_eq_cell_integral {c m R₀ σ t₁ : ℝ} (hR₀ : 1 ≤ R₀)
    (hc : 4 * (R₀ + 1) ≤ c) (u₁ : Xmc c m) {ω_t1 : B0579.Plane → ℝ}
    (hω_t1 : (u₁ : B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell c)] ω_t1)
    {h : Xm m} {g : B0579.Plane → ℝ} (hhg : (h : B0579.Plane → ℝ) =ᵐ[planeMeasure m] g)
    (hg_supp : ∀ y : B0579.Plane, R₀ ^ 2 < y.1 ^ 2 + y.2 ^ 2 → g y = 0) :
    ∫ x in B0579.cell c,
        ω_t1 x * periodizePsi0 c (fun y => B0579.jb y ^ m * g y) σ t₁ t₁ x =
      inner ℝ (Jc c m u₁) h := by
  set g_w : B0579.Plane → ℝ := fun y => B0579.jb y ^ m * g y
  have hg_w_supp : ∀ y : B0579.Plane, R₀ ^ 2 < y.1 ^ 2 + y.2 ^ 2 → g_w y = 0 := by
    intro y hy; dsimp [g_w]; rw [hg_supp y hy, mul_zero]
  rw [inner_Xm_eq_plane_integral]
  have hJc_ae : (Jc c m u₁ : B0579.Plane → ℝ) =ᵐ[volume] (B0579.cell c).indicator u₁ :=
    (volume_ac_pm m).ae_le (coeFn_zeroExtFun c m u₁)
  have hh_ae : (h : B0579.Plane → ℝ) =ᵐ[volume] g := (volume_ac_pm m).ae_le hhg
  have h1 : (∫ x : B0579.Plane, (Jc c m u₁) x * (B0579.jb x ^ m * h x)) =
      ∫ x : B0579.Plane, (B0579.cell c).indicator (fun x => u₁ x * g_w x) x := by
    refine integral_congr_ae ?_
    filter_upwards [hJc_ae, hh_ae] with x hx1 hx2
    rw [hx1, hx2]
    by_cases hxc : x ∈ B0579.cell c
    · simp only [indicator_of_mem hxc, g_w]
    · simp only [indicator_of_notMem hxc, zero_mul]
  rw [h1, integral_indicator (B0579.measurableSet_cell c)]
  refine integral_congr_ae ?_
  filter_upwards [hω_t1, ae_restrict_mem (B0579.measurableSet_cell c)] with x hx_ae hx_mem
  rw [hx_ae, (periodizePsi0_on_cell hR₀ hc hg_w_supp σ t₁ t₁ hx_mem).1]
  unfold psi0
  rw [sub_self, flow_zero]

private theorem norm_sq_eq_cell_integral_transport {c m Sig R₀ σ t L : ℝ}
    {T_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m)} (hT : IsFrozenRadialTransport m Sig T_pl)
    (hσ : σ ∈ Icc 0 Sig) (hR₀ : 1 ≤ R₀) (hc : 4 * (R₀ + 1) ≤ c)
    {h : Xm m} {g : B0579.Plane → ℝ} (hhg : (h : B0579.Plane → ℝ) =ᵐ[planeMeasure m] g)
    (hg_supp : ∀ y : B0579.Plane, R₀ ^ 2 < y.1 ^ 2 + y.2 ^ 2 → g y = 0) :
    ∫ x in B0579.cell c,
        (Rc c m (T_pl σ (-L) h)) x *
          periodizePsi0 c (fun y => B0579.jb y ^ m * g y) σ (t + L) t x =
      ‖h‖ ^ 2 := by
  set g_w : B0579.Plane → ℝ := fun y => B0579.jb y ^ m * g y
  set g_tr : B0579.Plane → ℝ := fun x => g (frozenRadialFlow σ (-L) x)
  set k₀ : Xm m := T_pl σ (-L) h
  have hg_w_supp : ∀ y : B0579.Plane, R₀ ^ 2 < y.1 ^ 2 + y.2 ^ 2 → g_w y = 0 := by
    intro y hy; dsimp [g_w]; rw [hg_supp y hy, mul_zero]
  have hk₀_norm : ‖h‖ ^ 2 = inner ℝ k₀ k₀ := by
    rw [← hT.isometry σ hσ (-L) h, ← real_inner_self_eq_norm_sq]
  have hσ1 : 0 ≤ 1 + σ := by linarith [hσ.1]
  have hk₀_pm : (k₀ : B0579.Plane → ℝ) =ᵐ[planeMeasure m] g_tr :=
    (hT.flow σ hσ (-L) h).trans (hhg.comp_tendsto (flow_qmp m σ hσ1 (-L)).tendsto_ae)
  have hk₀_vol : (k₀ : B0579.Plane → ℝ) =ᵐ[volume] g_tr := (volume_ac_pm m).ae_le hk₀_pm
  have hf₀_cell : (Rc c m k₀ : B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell c)] g_tr := by
    refine ae_restrict_cell_of_cellMeasure ((coeFn_restrictCellFun c m k₀).trans ?_)
    rw [cellMeasure_eq_restrict_planeMeasure]
    exact ae_restrict_of_ae hk₀_pm
  rw [hk₀_norm, inner_Xm_eq_plane_integral]
  have h1 : (∫ x : B0579.Plane, k₀ x * (B0579.jb x ^ m * k₀ x)) =
      ∫ x : B0579.Plane, (B0579.cell c).indicator (fun x => g_tr x * (B0579.jb x ^ m * g_tr x)) x := by
    refine integral_congr_ae ?_
    filter_upwards [hk₀_vol] with x hx
    rw [hx]
    by_cases hxc : x ∈ B0579.cell c
    · simp only [indicator_of_mem hxc]
    · simp only [indicator_of_notMem hxc]
      have hgt : R₀ ^ 2 < (frozenRadialFlow σ (-L) x).1 ^ 2 + (frozenRadialFlow σ (-L) x).2 ^ 2 := by
        rw [flow_sq]
        exact sq_gt_of_not_mem_cell hR₀ hc hxc
      have hz : g_tr x = 0 := hg_supp _ hgt
      rw [hz, zero_mul]
  rw [h1, integral_indicator (B0579.measurableSet_cell c)]
  refine integral_congr_ae ?_
  filter_upwards [hf₀_cell, ae_restrict_mem (B0579.measurableSet_cell c)] with x hx_ae hx_mem
  rw [hx_ae, (periodizePsi0_on_cell hR₀ hc hg_w_supp σ (t + L) t hx_mem).1]
  unfold psi0
  have hsub : t - (t + L) = -L := by ring
  rw [hsub]
  dsimp [g_w, g_tr]
  rw [jb_frozenRadialFlow]

private theorem exists_free_prop_op_bound {m Sig Lmax : ℝ} (hm : 8 < m) (hSig : 0 < Sig)
    (hLmax : 0 < Lmax) {ε_op : ℝ} (hε_op : 0 < ε_op) :
    ∃ (Cm C_fb b_fb δ_op ν_op : ℝ),
      0 < Cm ∧ 0 < C_fb ∧ 0 < b_fb ∧
      0 < δ_op ∧ δ_op ≤ 1 ∧ 0 < ν_op ∧ ν_op ≤ 1 ∧
      (∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ageCut = Sig →
        ∀ δ : ℝ, 0 ≤ δ → TrainCloseM m p.train Sig δ →
        ∀ s r : ℝ, 0 ≤ s → (hsr : s ≤ r) → r ≤ p.H →
        ∀ (f₀ : B0579.Plane → ℝ) (hf₀ : MemLp f₀ 2 (B0579.cellMeasure p.c m))
          (wfl : ℝ → B0579.Plane → ℝ) (hwfl : IsFreeCylFlow m p.train s f₀ wfl),
          ‖(hwfl.memX r hsr).toLp (wfl r)‖ ≤
            Real.exp ((Cm * p.ν + C_fb * δ + C_fb * Real.exp (-b_fb * p.c ^ 2)) * (r - s)) *
              ‖hf₀.toLp f₀‖) ∧
      (∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ ν_op → p.ageCut = Sig →
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ δ_op → TrainCloseM m p.train Sig δ →
        ∀ Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m), IsFreeCylPropagator m p Sc →
        ∀ t L : ℝ, 0 ≤ t → 0 ≤ L → L ≤ Lmax → t + L ≤ p.H →
          ‖Sc (t + L) t‖ ≤ 1 + ε_op) := by
  obtain ⟨Cm, C_fb, b_fb, hCm, hC_fb, hb_fb, hFCB⟩ := freeCylinderBound_proof m hm Sig hSig
  have hflow_bd : ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ageCut = Sig →
      ∀ δ : ℝ, 0 ≤ δ → TrainCloseM m p.train Sig δ →
      ∀ s r : ℝ, 0 ≤ s → (hsr : s ≤ r) → r ≤ p.H →
      ∀ (f₀ : B0579.Plane → ℝ) (hf₀ : MemLp f₀ 2 (B0579.cellMeasure p.c m))
        (wfl : ℝ → B0579.Plane → ℝ) (hwfl : IsFreeCylFlow m p.train s f₀ wfl),
        ‖(hwfl.memX r hsr).toLp (wfl r)‖ ≤
          Real.exp ((Cm * p.ν + C_fb * δ + C_fb * Real.exp (-b_fb * p.c ^ 2)) * (r - s)) *
            ‖hf₀.toLp f₀‖ := by
    intro p d dm dp hbg hAge δ hδ0 hcloseM s r hs0 hsr hrH f₀ hf₀ wfl hwfl
    have hrSig : r ≤ Sig / p.ν := by
      have hH_eq : p.H = Sig / p.ν := by unfold Params.H; rw [hAge]
      linarith
    obtain ⟨wfl₀, _hwfl₀, huniq, heLp⟩ :=
      hFCB p d dm dp hbg δ hδ0 (hcloseM.toTrainClose (by linarith)) s r hs0 hsr hrSig f₀ hf₀
    have hae_cell : wfl r =ᵐ[B0579.cellMeasure p.c m] wfl₀ r :=
      ae_cellMeasure_of_restrict_cell (huniq wfl hwfl r hsr)
    set K_exp : ℝ :=
      Real.exp ((Cm * p.ν + C_fb * δ + C_fb * Real.exp (-b_fb * p.c ^ 2)) * (r - s))
    have hK_nn : 0 ≤ K_exp := (Real.exp_pos _).le
    have heLp' : eLpNorm (wfl r) 2 (B0579.cellMeasure p.c m) ≤
        ENNReal.ofReal K_exp * eLpNorm f₀ 2 (B0579.cellMeasure p.c m) := by
      rw [eLpNorm_congr_ae hae_cell]
      exact heLp
    rw [Lp.norm_toLp, Lp.norm_toLp]
    have hfin : ENNReal.ofReal K_exp * eLpNorm f₀ 2 (B0579.cellMeasure p.c m) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf₀.eLpNorm_ne_top
    have htr := ENNReal.toReal_mono hfin heLp'
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK_nn] at htr
  set η_r : ℝ := min (1 / (6 * Lmax)) (ε_op / (6 * Lmax))
  have hη_r : 0 < η_r := lt_min (by positivity) (by positivity)
  set δ_op : ℝ := min 1 (η_r / C_fb)
  have hδ_op_pos : 0 < δ_op := lt_min one_pos (div_pos hη_r hC_fb)
  set c_req : ℝ := max 1 (C_fb / (b_fb * η_r))
  have hc_req_pos : 0 < c_req := lt_of_lt_of_le one_pos (le_max_left _ _)
  set ν_op : ℝ := min 1 (min (η_r / Cm) (Real.sqrt c_req)⁻¹)
  have hν_op_pos : 0 < ν_op :=
    lt_min one_pos (lt_min (div_pos hη_r hCm) (inv_pos.2 (Real.sqrt_pos.2 hc_req_pos)))
  refine ⟨Cm, C_fb, b_fb, δ_op, ν_op, hCm, hC_fb, hb_fb, hδ_op_pos, min_le_left _ _,
    hν_op_pos, min_le_left _ _, hflow_bd, ?_⟩
  intro p d dm dp hbg hν_le hAge δ hδ0 hδ_le hcloseM Sc hSc t L ht0 hL0 hL_le htLH
  have hν_η : Cm * p.ν ≤ η_r := by
    have h1 : p.ν ≤ η_r / Cm := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
    exact (le_div_iff₀' hCm).1 h1
  have hδ_η : C_fb * δ ≤ η_r := by
    have h1 : δ ≤ η_r / C_fb := hδ_le.trans (min_le_right _ _)
    exact (le_div_iff₀' hC_fb).1 h1
  have hc_ge : c_req ≤ p.c :=
    bgRegime_c_ge hbg hc_req_pos (hν_le.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hc_one : 1 ≤ p.c := (le_max_left 1 _).trans hc_ge
  have hexp_η : C_fb * Real.exp (-b_fb * p.c ^ 2) ≤ η_r := by
    have h1 := exp_neg_sq_le_inv hb_fb hc_one
    have h2 : C_fb / (b_fb * η_r) ≤ p.c := (le_max_right 1 _).trans hc_ge
    have h3 : C_fb ≤ η_r * (b_fb * p.c) := by
      have := (div_le_iff₀ (mul_pos hb_fb hη_r)).1 h2
      linarith
    have hbpc : 0 < b_fb * p.c := mul_pos hb_fb (lt_of_lt_of_le one_pos hc_one)
    calc C_fb * Real.exp (-b_fb * p.c ^ 2)
        ≤ C_fb * (b_fb * p.c)⁻¹ := mul_le_mul_of_nonneg_left h1 hC_fb.le
      _ ≤ η_r := (mul_inv_le_iff₀ hbpc).2 h3
  set rate : ℝ := Cm * p.ν + C_fb * δ + C_fb * Real.exp (-b_fb * p.c ^ 2)
  have hrate_nn : 0 ≤ rate := by
    dsimp [rate]
    positivity [p.ν_pos.le]
  have hrate_le : rate ≤ 3 * η_r := by dsimp [rate]; linarith
  have hrateL_nn : 0 ≤ rate * L := mul_nonneg hrate_nn hL0
  have hrateL_half : rate * L ≤ 1 / 2 := by
    have h1 : η_r ≤ 1 / (6 * Lmax) := min_le_left _ _
    have h2 : 6 * Lmax * η_r ≤ 1 := by
      have := (le_div_iff₀' (by positivity : 0 < 6 * Lmax)).1 h1
      linarith
    calc rate * L ≤ (3 * η_r) * Lmax := mul_le_mul hrate_le hL_le hL0 (by positivity)
      _ ≤ 1 / 2 := by linarith
  have hrateL_ε : 2 * (rate * L) ≤ ε_op := by
    have h1 : η_r ≤ ε_op / (6 * Lmax) := min_le_right _ _
    have h2 : 6 * Lmax * η_r ≤ ε_op := (le_div_iff₀' (by positivity : 0 < 6 * Lmax)).1 h1
    calc 2 * (rate * L) ≤ 2 * ((3 * η_r) * Lmax) := by
          nlinarith [mul_le_mul hrate_le hL_le hL0 (by positivity)]
      _ ≤ ε_op := by linarith
  have hexp_le : Real.exp (rate * L) ≤ 1 + ε_op :=
    (exp_le_one_add_two_mul hrateL_nn hrateL_half).trans (by linarith)
  refine (ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le fun f₀ => ?_).trans hexp_le
  obtain ⟨wfl, hwfl, hwfl_ae⟩ := hSc.flow t ⟨ht0, by linarith⟩ f₀
  have h_ae_cell : (Sc (t + L) t f₀ : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure p.c m] wfl (t + L) :=
    ae_cellMeasure_of_restrict_cell (hwfl_ae (t + L) ⟨by linarith, htLH⟩)
  have hLp_eq : Sc (t + L) t f₀ = (hwfl.memX (t + L) (by linarith)).toLp (wfl (t + L)) := by
    refine Lp.ext ?_
    exact h_ae_cell.trans (MemLp.coeFn_toLp _).symm
  have hf₀_eq : (Lp.memLp f₀).toLp f₀ = f₀ := by
    refine Lp.ext ?_
    exact MemLp.coeFn_toLp (Lp.memLp f₀)
  rw [hLp_eq]
  have hbd := hflow_bd p d dm dp hbg hAge δ hδ0 hcloseM t (t + L) ht0 (by linarith) htLH
    f₀ (Lp.memLp f₀) wfl hwfl
  rw [hf₀_eq] at hbd
  have hrate_eq :
      (Cm * p.ν + C_fb * δ + C_fb * Real.exp (-b_fb * p.c ^ 2)) * (t + L - t) = rate * L := by
    dsimp [rate]
    ring
  rwa [hrate_eq] at hbd

private theorem sq_one_add_mul_sub_le {a x : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ((1 + a) * x) ^ 2 - x ^ 2 ≤ 3 * a * (x ^ 2 + 1) := by
  have ha2 : a ^ 2 ≤ a := by nlinarith
  have hexp : ((1 + a) * x) ^ 2 - x ^ 2 = (2 * a + a ^ 2) * x ^ 2 := by ring
  rw [hexp]
  nlinarith [sq_nonneg x]

private theorem amgm_density_mul_sq {m : ℝ} (hm : 0 ≤ m) (x : B0579.Plane) (w : ℝ) :
    |w| ≤ ((B0579.density m x : ℝ) * w ^ 2 + 1) / 2 := by
  have hjb1 : 1 ≤ B0579.jb x := by
    unfold B0579.jb
    have h0 : 0 ≤ x.1 ^ 2 + x.2 ^ 2 := add_nonneg (sq_nonneg x.1) (sq_nonneg x.2)
    linarith
  have hdens1 : 1 ≤ (B0579.density m x : ℝ) := by
    rw [B0579.coe_density]
    exact Real.one_le_rpow hjb1 hm
  have hsq : 2 * |w| ≤ w ^ 2 + 1 := by
    have h1 : 0 ≤ (|w| - 1) ^ 2 := sq_nonneg _
    have h2 : |w| ^ 2 = w ^ 2 := sq_abs w
    linarith
  have hw2 : w ^ 2 ≤ (B0579.density m x : ℝ) * w ^ 2 :=
    le_mul_of_one_le_left (sq_nonneg w) hdens1
  linarith

private theorem pointwise_pde_rem_le {m R₀ M_psi η_rem_target η_part ν c t L r : ℝ}
    (hm0 : 0 ≤ m) (hR₀ : 1 ≤ R₀) (hM_psi : 0 < M_psi) (hη_rem : 0 < η_rem_target)
    (hη_part_def : η_part = η_rem_target / (4 * M_psi))
    (hν_pos : 0 < ν) (hν_part : ν ≤ η_part) (ht0 : 0 ≤ t) (hc_cell : 4 * (R₀ + 1) ≤ c)
    {g_w : B0579.Plane → ℝ} (hg_w_cd : ContDiff ℝ ∞ g_w)
    (hg_w_supp : ∀ y : B0579.Plane, R₀ ^ 2 < y.1 ^ 2 + y.2 ^ 2 → g_w y = 0)
    (hpsi_bd : ∀ x : B0579.Plane,
      |B0579.pd 0 (psi0 g_w (ν * t) (t + L) r) x| ≤ M_psi ∧
        |B0579.pd 1 (psi0 g_w (ν * t) (t + L) r) x| ≤ M_psi ∧
        |lapP (psi0 g_w (ν * t) (t + L) r) x| ≤ M_psi)
    {v0 v1 : B0579.Plane → ℝ}
    (hdv_bd : ∀ x ∈ B0579.cell c,
      |v0 x - (UnforcedLeray.B0146.isoVelocity ν t x).1| +
        |v1 x - (UnforcedLeray.B0146.isoVelocity ν t x).2| ≤ 3 * η_part)
    (w : B0579.Plane → ℝ) {x : B0579.Plane} (hx_cell : x ∈ B0579.cell c) :
    ‖w x * (deriv (fun r' => periodizePsi0 c g_w (ν * t) (t + L) r' x) r +
      ν * lapP (periodizePsi0 c g_w (ν * t) (t + L) r) x +
      (v0 x * B0579.pd 0 (periodizePsi0 c g_w (ν * t) (t + L) r) x +
        v1 x * B0579.pd 1 (periodizePsi0 c g_w (ν * t) (t + L) r) x))‖ ≤
      (η_rem_target / 2) * ((B0579.density m x : ℝ) * w x ^ 2) +
        (η_rem_target / 2) *
          (Icc (-(R₀ + 1)) (R₀ + 1) ×ˢ Icc (-(R₀ + 1)) (R₀ + 1)).indicator (fun _ => (1 : ℝ)) x := by
  have hσ_pos : 0 < 1 + ν * t := by
    have : 0 ≤ ν * t := mul_nonneg hν_pos.le ht0
    linarith
  obtain ⟨_, hp0, hp1, hlp, hdr⟩ :=
    periodizePsi0_on_cell hR₀ hc_cell hg_w_supp (ν * t) (t + L) r hx_cell
  rw [hdr, hlp, hp0, hp1]
  have hpde := transport_pde_psi0 hg_w_cd (σ := ν * t) hσ_pos.le (t + L) r x
  obtain ⟨hiso1, hiso2⟩ := isoVelocity_eq_frozenOmega (ν := ν) (t := t) hσ_pos x
  have hrem_eq : deriv (fun r' => psi0 g_w (ν * t) (t + L) r' x) r +
      ν * lapP (psi0 g_w (ν * t) (t + L) r) x +
      (v0 x * B0579.pd 0 (psi0 g_w (ν * t) (t + L) r) x +
        v1 x * B0579.pd 1 (psi0 g_w (ν * t) (t + L) r) x) =
      ν * lapP (psi0 g_w (ν * t) (t + L) r) x +
        (v0 x - (UnforcedLeray.B0146.isoVelocity ν t x).1) *
          B0579.pd 0 (psi0 g_w (ν * t) (t + L) r) x +
        (v1 x - (UnforcedLeray.B0146.isoVelocity ν t x).2) *
          B0579.pd 1 (psi0 g_w (ν * t) (t + L) r) x := by
    rw [hiso1, hiso2]
    linarith
  rw [hrem_eq]
  set D_box : Set B0579.Plane := Icc (-(R₀ + 1)) (R₀ + 1) ×ˢ Icc (-(R₀ + 1)) (R₀ + 1)
  by_cases hx_box : x ∈ D_box
  · obtain ⟨hb_p0, hb_p1, hb_lp⟩ := hpsi_bd x
    set dv0 : ℝ := v0 x - (UnforcedLeray.B0146.isoVelocity ν t x).1
    set dv1 : ℝ := v1 x - (UnforcedLeray.B0146.isoVelocity ν t x).2
    have hdv_sum : |dv0| + |dv1| ≤ 3 * η_part := hdv_bd x hx_cell
    set rem_val : ℝ := ν * lapP (psi0 g_w (ν * t) (t + L) r) x +
      dv0 * B0579.pd 0 (psi0 g_w (ν * t) (t + L) r) x +
      dv1 * B0579.pd 1 (psi0 g_w (ν * t) (t + L) r) x
    have hrem_abs : |rem_val| ≤ η_rem_target := by
      have a1 : |ν * lapP (psi0 g_w (ν * t) (t + L) r) x| ≤ ν * M_psi := by
        rw [abs_mul, abs_of_pos hν_pos]
        exact mul_le_mul_of_nonneg_left hb_lp hν_pos.le
      have a2 : |dv0 * B0579.pd 0 (psi0 g_w (ν * t) (t + L) r) x| ≤ |dv0| * M_psi := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hb_p0 (abs_nonneg _)
      have a3 : |dv1 * B0579.pd 1 (psi0 g_w (ν * t) (t + L) r) x| ≤ |dv1| * M_psi := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hb_p1 (abs_nonneg _)
      have tri1 := abs_add_le
        (ν * lapP (psi0 g_w (ν * t) (t + L) r) x + dv0 * B0579.pd 0 (psi0 g_w (ν * t) (t + L) r) x)
        (dv1 * B0579.pd 1 (psi0 g_w (ν * t) (t + L) r) x)
      have tri2 := abs_add_le
        (ν * lapP (psi0 g_w (ν * t) (t + L) r) x)
        (dv0 * B0579.pd 0 (psi0 g_w (ν * t) (t + L) r) x)
      have h4M : 4 * η_part * M_psi = η_rem_target := by
        rw [hη_part_def]
        field_simp [hM_psi.ne']
      have hsum_le : ν + |dv0| + |dv1| ≤ 4 * η_part := by linarith
      have hmul_le : (ν + |dv0| + |dv1|) * M_psi ≤ 4 * η_part * M_psi :=
        mul_le_mul_of_nonneg_right hsum_le hM_psi.le
      linarith
    have hamgm := amgm_density_mul_sq hm0 x (w x)
    rw [Real.norm_eq_abs, abs_mul, indicator_of_mem hx_box]
    calc |w x| * |rem_val|
        ≤ (((B0579.density m x : ℝ) * w x ^ 2 + 1) / 2) * η_rem_target :=
          mul_le_mul hamgm hrem_abs (abs_nonneg _) (by linarith [abs_nonneg (w x)])
      _ = (η_rem_target / 2) * ((B0579.density m x : ℝ) * w x ^ 2) +
            (η_rem_target / 2) * 1 := by ring
  · obtain ⟨_, z0, z1, zl⟩ :=
      psi0_vanish_of_sq_gt hg_w_supp (ν * t) (t + L) r (sq_gt_of_not_mem_box hR₀ hx_box)
    rw [zl, z0, z1]
    simp only [mul_zero, add_zero, norm_zero]
    rw [indicator_of_notMem hx_box, mul_zero, add_zero]
    exact mul_nonneg (div_nonneg hη_rem.le zero_le_two)
      (mul_nonneg (B0579.density_pos m x).le (sq_nonneg _))

private theorem single_smooth_conv {m Sig Lmax : ℝ} (hm : 8 < m) (hSig : 0 < Sig)
    (hLmax : 0 < Lmax) {T_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m)}
    (hT : IsFrozenRadialTransport m Sig T_pl)
    {h : Xm m} {g : B0579.Plane → ℝ} (hhg : (h : B0579.Plane → ℝ) =ᵐ[planeMeasure m] g)
    (hg_supp_compact : HasCompactSupport g) (hg_cd : ContDiff ℝ ∞ g)
    {ε_s : ℝ} (hε_s : 0 < ε_s) :
    ∃ (δ_s ν_s : ℝ), 0 < δ_s ∧ δ_s ≤ 1 ∧ 0 < ν_s ∧ ν_s ≤ 1 ∧
      ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ ν_s → p.ageCut = Sig →
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ δ_s → TrainCloseM m p.train Sig δ →
        ∀ Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m), IsFreeCylPropagator m p Sc →
        ∀ t L : ℝ, 0 ≤ t → 0 ≤ L → L ≤ Lmax → t + L ≤ p.H →
          ‖Jc p.c m (Sc (t + L) t (Rc p.c m (T_pl (p.ν * t) (-L) h))) - h‖ ≤ ε_s := by
  obtain ⟨R₀, hR₀, hg_supp⟩ := exists_radius_of_hasCompactSupport hg_supp_compact
  set g_w : B0579.Plane → ℝ := fun y => B0579.jb y ^ m * g y
  have hg_w_cd : ContDiff ℝ ∞ g_w := (contDiff_jb_rpow m).mul hg_cd
  have hg_w_supp : ∀ y : B0579.Plane, R₀ ^ 2 < y.1 ^ 2 + y.2 ^ 2 → g_w y = 0 := by
    intro y hy; dsimp [g_w]; rw [hg_supp y hy, mul_zero]
  obtain ⟨M_psi, hM_psi, hpsi_bd⟩ := exists_psi0_deriv_bound hSig hLmax hR₀ hg_w_cd hg_w_supp
  obtain ⟨C_gap, b_gap, hC_gap, hb_gap, hGap⟩ := cylTrainGap Sig hSig
  obtain ⟨C_lip, hC_lip, hLip⟩ := exists_isoVelocity_age_lip hSig
  set D_box : Set B0579.Plane := Icc (-(R₀ + 1)) (R₀ + 1) ×ˢ Icc (-(R₀ + 1)) (R₀ + 1)
  have hD_comp : IsCompact D_box := isCompact_Icc.prod isCompact_Icc
  have hD_meas : MeasurableSet D_box := hD_comp.measurableSet
  have hD_fin : (volume : Measure B0579.Plane) D_box < ⊤ := hD_comp.measure_lt_top
  obtain ⟨V_box, hV_def⟩ : ∃ x : ℝ, x = ((volume : Measure B0579.Plane) D_box).toReal := ⟨_, rfl⟩
  have hV_nn : 0 ≤ V_box := hV_def ▸ ENNReal.toReal_nonneg
  obtain ⟨B_norm, hB_def⟩ : ∃ x : ℝ, x = 4 * ‖h‖ ^ 2 + V_box + 1 := ⟨_, rfl⟩
  have hB_pos : 0 < B_norm := by rw [hB_def]; positivity
  obtain ⟨η_op, hη_op_def⟩ : ∃ x : ℝ, x = min 1 (ε_s ^ 2 / (6 * (‖h‖ ^ 2 + 1))) := ⟨_, rfl⟩
  have hη_op_pos : 0 < η_op := by rw [hη_op_def]; exact lt_min one_pos (by positivity)
  have hη_op_le1 : η_op ≤ 1 := hη_op_def ▸ min_le_left _ _
  have hη_op_le2 : η_op ≤ ε_s ^ 2 / (6 * (‖h‖ ^ 2 + 1)) := hη_op_def ▸ min_le_right _ _
  obtain ⟨_Cm, _C_fb, _b_fb, δ_fb, ν_fb, _hCm, _hC_fb, _hb_fb, hδ_fb_pos, hδ_fb_le,
      hν_fb_pos, hν_fb_le, _hflow_bd, hop_bd⟩ :=
    exists_free_prop_op_bound hm hSig hLmax hη_op_pos
  obtain ⟨η_rem_target, hη_rem_def⟩ : ∃ x : ℝ, x = ε_s ^ 2 / (2 * Lmax * B_norm) := ⟨_, rfl⟩
  have hη_rem_pos : 0 < η_rem_target := by rw [hη_rem_def]; positivity
  obtain ⟨η_part, hη_part_def⟩ : ∃ x : ℝ, x = η_rem_target / (4 * M_psi) := ⟨_, rfl⟩
  have hη_part_pos : 0 < η_part := by rw [hη_part_def]; exact div_pos hη_rem_pos (by positivity)
  set δ_s : ℝ := min δ_fb (η_part / C_gap)
  have hδ_s_pos : 0 < δ_s := lt_min hδ_fb_pos (div_pos hη_part_pos hC_gap)
  obtain ⟨c_req, hc_req_def⟩ : ∃ x : ℝ, x = max (4 * (R₀ + 1)) (C_gap / (b_gap * η_part)) :=
    ⟨_, rfl⟩
  have hc_req_pos : 0 < c_req := by
    rw [hc_req_def]
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  set ν_s : ℝ := min ν_fb (min η_part (min (η_part / (C_lip * Lmax)) (Real.sqrt c_req)⁻¹))
  have hν_s_pos : 0 < ν_s :=
    lt_min hν_fb_pos (lt_min hη_part_pos
      (lt_min (div_pos hη_part_pos (mul_pos hC_lip hLmax))
        (inv_pos.2 (Real.sqrt_pos.2 hc_req_pos))))
  refine ⟨δ_s, ν_s, hδ_s_pos, (min_le_left _ _).trans hδ_fb_le,
    hν_s_pos, (min_le_left _ _).trans hν_fb_le, ?_⟩
  intro p d dm dp hbg hν_le hAge δ hδ0 hδ_le hcloseM Sc hSc t L ht0 hL0 hL_le htLH
  have hH_eq : p.H = Sig / p.ν := by unfold Params.H; rw [hAge]
  have hσ_mem : p.ν * t ∈ Icc 0 Sig := by
    refine ⟨mul_nonneg p.ν_pos.le ht0, ?_⟩
    have htSig : t ≤ Sig / p.ν := by linarith
    have := (le_div_iff₀ p.ν_pos).1 htSig
    linarith
  have hc_ge : c_req ≤ p.c :=
    bgRegime_c_ge hbg hc_req_pos
      (hν_le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hc_cell : 4 * (R₀ + 1) ≤ p.c := by
    have h1 : 4 * (R₀ + 1) ≤ c_req := hc_req_def ▸ le_max_left _ _
    exact h1.trans hc_ge
  have hc_one : 1 ≤ p.c := by linarith
  set σ : ℝ := p.ν * t
  obtain ⟨f₀, hf₀_def⟩ : ∃ x : Xmc p.c m, x = Rc p.c m (T_pl σ (-L) h) := ⟨_, rfl⟩
  obtain ⟨u₁, hu₁_def⟩ : ∃ x : Xmc p.c m, x = Sc (t + L) t f₀ := ⟨_, rfl⟩
  obtain ⟨W_h, hW_def⟩ : ∃ x : Xm m, x = Jc p.c m u₁ := ⟨_, rfl⟩
  have hSc_op : ‖Sc (t + L) t‖ ≤ 1 + η_op :=
    hop_bd p d dm dp hbg (hν_le.trans (min_le_left _ _)) hAge δ hδ0
      (hδ_le.trans (min_le_left _ _)) hcloseM Sc hSc t L ht0 hL0 hL_le htLH
  have hf₀_norm : ‖f₀‖ ≤ ‖h‖ := by
    rw [hf₀_def]
    exact (norm_Rc_apply_le p.c m _).trans (hT.isometry σ hσ_mem (-L) h).le
  have hW_norm : ‖W_h‖ ≤ (1 + η_op) * ‖h‖ := by
    rw [hW_def, norm_Jc_apply, hu₁_def]
    calc ‖Sc (t + L) t f₀‖ ≤ ‖Sc (t + L) t‖ * ‖f₀‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1 + η_op) * ‖h‖ :=
        mul_le_mul hSc_op hf₀_norm (norm_nonneg _) (by linarith)
  have hnorm_diff : ‖W_h‖ ^ 2 - ‖h‖ ^ 2 ≤ ε_s ^ 2 / 2 := by
    have h1 : ‖W_h‖ ^ 2 ≤ ((1 + η_op) * ‖h‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hW_norm 2
    have h6 : 6 * (‖h‖ ^ 2 + 1) * η_op ≤ ε_s ^ 2 :=
      (le_div_iff₀' (by positivity : 0 < 6 * (‖h‖ ^ 2 + 1))).1 hη_op_le2
    have hsq_exp := sq_one_add_mul_sub_le hη_op_pos.le hη_op_le1 (x := ‖h‖)
    linarith
  obtain ⟨wfl, hwfl, hwfl_ae⟩ := hSc.flow t ⟨ht0, by linarith⟩ f₀
  have hwfl_t1 : (u₁ : B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell p.c)] wfl (t + L) := by
    rw [hu₁_def]
    exact hwfl_ae (t + L) ⟨by linarith, htLH⟩
  set φ : ℝ → B0579.Plane → ℝ := periodizePsi0 p.c g_w σ (t + L)
  have hφ_test : CylEtaTest p.c t (t + L) φ :=
    isCylEtaTest_periodizePsi0 hR₀ hc_cell hg_w_cd hg_w_supp σ t (t + L)
  have hclose : TrainClose p.train Sig δ := hcloseM.toTrainClose (by linarith)
  have hv_bdd : ∃ M : ℝ, ∀ r ∈ Icc t (t + L), ∀ x : B0579.Plane,
      |p.train.v r x 0| + |p.train.v r x 1| ≤ M := by
    refine ⟨C_gap * (δ + 1), fun r hr x => ?_⟩
    have hr_mem : r ∈ Icc 0 (Sig / p.ν) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    exact (hGap p.ν p.c δ p.ν_pos hc_one hδ0 p.train hclose r hr_mem).1 x
  have hweak := cylWeakTimeDep m hm p.ν p.c p.train t f₀ wfl p.c_pos hwfl (t + L) φ
    (by linarith) hφ_test hv_bdd
  have hterm_eq : (∫ x in B0579.cell p.c, wfl (t + L) x * φ (t + L) x) = inner ℝ W_h h := by
    rw [hW_def]
    exact inner_Jc_eq_cell_integral hR₀ hc_cell u₁ hwfl_t1 hhg hg_supp
  have hinit_eq : (∫ x in B0579.cell p.c, f₀ x * φ t x) = ‖h‖ ^ 2 := by
    rw [hf₀_def]
    exact norm_sq_eq_cell_integral_transport hT hσ_mem hR₀ hc_cell hhg hg_supp
  rw [hterm_eq, hinit_eq] at hweak
  -- Bound the remainder integral on `[t, t + L] × cell p.c`
  have hν_part : p.ν ≤ η_part :=
    hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ_part : C_gap * δ ≤ η_part := by
    have h1 : δ ≤ η_part / C_gap := hδ_le.trans (min_le_right _ _)
    exact (le_div_iff₀' hC_gap).1 h1
  have hexp_part : C_gap * Real.exp (-b_gap * p.c ^ 2) ≤ η_part := by
    have h1 := exp_neg_sq_le_inv hb_gap hc_one
    have h2 : C_gap / (b_gap * η_part) ≤ p.c :=
      (hc_req_def ▸ le_max_right _ _).trans hc_ge
    have h3 : C_gap ≤ η_part * (b_gap * p.c) := by
      have := (div_le_iff₀ (mul_pos hb_gap hη_part_pos)).1 h2
      linarith
    have hbgc : 0 < b_gap * p.c := mul_pos hb_gap p.c_pos
    calc C_gap * Real.exp (-b_gap * p.c ^ 2)
        ≤ C_gap * (b_gap * p.c)⁻¹ := mul_le_mul_of_nonneg_left h1 hC_gap.le
      _ ≤ η_part := (mul_inv_le_iff₀ hbgc).2 h3
  have hlip_part : C_lip * (p.ν * Lmax) ≤ η_part := by
    have h1 : p.ν ≤ η_part / (C_lip * Lmax) :=
      hν_le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have := (le_div_iff₀' (mul_pos hC_lip hLmax)).1 h1
    linarith
  have hslice_bd : ∀ r ∈ Icc t (t + L),
      ‖∫ x in B0579.cell p.c, wfl r x *
        (deriv (fun r' => φ r' x) r + p.ν * lapP (φ r) x +
          (p.train.v r x 0 * B0579.pd 0 (φ r) x + p.train.v r x 1 * B0579.pd 1 (φ r) x))‖ ≤
        (η_rem_target / 2) * B_norm := by
    intro r hr
    have htr : t ≤ r := hr.1
    have hrH : r ≤ p.H := hr.2.trans htLH
    have hrSig : r ≤ Sig / p.ν := by linarith
    have hνr_le : p.ν * r ≤ Sig := by
      have := (le_div_iff₀ p.ν_pos).1 hrSig
      linarith
    have hwflr_norm : ‖(hwfl.memX r htr).toLp (wfl r)‖ ≤ 2 * ‖h‖ := by
      have h_ae_r : (Sc r t f₀ : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure p.c m] wfl r :=
        ae_cellMeasure_of_restrict_cell (hwfl_ae r ⟨htr, hrH⟩)
      have hLp_r : (hwfl.memX r htr).toLp (wfl r) = Sc r t f₀ :=
        Lp.ext ((MemLp.coeFn_toLp _).trans h_ae_r.symm)
      rw [hLp_r]
      have hSc_r0 :=
        hop_bd p d dm dp hbg (hν_le.trans (min_le_left _ _)) hAge δ hδ0
          (hδ_le.trans (min_le_left _ _)) hcloseM Sc hSc t (r - t) ht0
          (sub_nonneg.2 htr) (by linarith [hr.2]) (by rw [add_sub_cancel]; exact hrH)
      rw [add_sub_cancel] at hSc_r0
      calc ‖Sc r t f₀‖ ≤ ‖Sc r t‖ * ‖f₀‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (1 + η_op) * ‖h‖ := mul_le_mul hSc_r0 hf₀_norm (norm_nonneg _) (by linarith)
        _ ≤ 2 * ‖h‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg h)
    obtain ⟨hint_dens, hint_dens_eq⟩ := integral_cell_density_sq (hwfl.memX r htr)
    have h_ind_int : Integrable (D_box.indicator (fun _ => (1 : ℝ))) volume :=
      (integrable_indicator_iff hD_meas).2 (integrableOn_const hD_fin.ne)
    have h_ind_cell : IntegrableOn (D_box.indicator (fun _ => (1 : ℝ))) (B0579.cell p.c) volume :=
      h_ind_int.integrableOn
    set maj : B0579.Plane → ℝ := fun x =>
      (η_rem_target / 2) * ((B0579.density m x : ℝ) * wfl r x ^ 2) +
        (η_rem_target / 2) * D_box.indicator (fun _ => (1 : ℝ)) x
    have hmaj_int : Integrable maj (volume.restrict (B0579.cell p.c)) :=
      (hint_dens.const_mul (η_rem_target / 2)).add (h_ind_cell.const_mul (η_rem_target / 2))
    have hpt : ∀ᵐ x ∂volume.restrict (B0579.cell p.c),
        ‖wfl r x * (deriv (fun r' => φ r' x) r + p.ν * lapP (φ r) x +
          (p.train.v r x 0 * B0579.pd 0 (φ r) x +
            p.train.v r x 1 * B0579.pd 1 (φ r) x))‖ ≤ maj x := by
      have hrt_mem : r - (t + L) ∈ Icc (-Lmax) 0 := ⟨by linarith [hr.1], by linarith [hr.2]⟩
      have hlip_le : C_lip * (p.ν * (r - t)) ≤ η_part := by
        have hr_diff : r - t ≤ Lmax := by linarith [hr.2]
        calc C_lip * (p.ν * (r - t)) ≤ C_lip * (p.ν * Lmax) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hr_diff p.ν_pos.le) hC_lip.le
          _ ≤ η_part := hlip_part
      have hdv_bd : ∀ x ∈ B0579.cell p.c,
          |p.train.v r x 0 - (UnforcedLeray.B0146.isoVelocity p.ν t x).1| +
            |p.train.v r x 1 - (UnforcedLeray.B0146.isoVelocity p.ν t x).2| ≤ 3 * η_part := by
        intro x hx_cell
        have hgap_x :=
          (hGap p.ν p.c δ p.ν_pos hc_one hδ0 p.train hclose r ⟨by linarith, hrSig⟩).2 x hx_cell
        have hlip_x := hLip p.ν t r p.ν_pos ht0 htr hνr_le x
        have t0 := abs_sub_le (p.train.v r x 0)
          (UnforcedLeray.B0146.isoVelocity p.ν r x).1
          (UnforcedLeray.B0146.isoVelocity p.ν t x).1
        have t1 := abs_sub_le (p.train.v r x 1)
          (UnforcedLeray.B0146.isoVelocity p.ν r x).2
          (UnforcedLeray.B0146.isoVelocity p.ν t x).2
        have hgap_exp : C_gap * (δ + Real.exp (-b_gap * p.c ^ 2)) =
            C_gap * δ + C_gap * Real.exp (-b_gap * p.c ^ 2) := by ring
        linarith
      filter_upwards [ae_restrict_mem (B0579.measurableSet_cell p.c)] with x hx_cell
      exact pointwise_pde_rem_le (by linarith) hR₀ hM_psi hη_rem_pos hη_part_def
        p.ν_pos hν_part ht0 hc_cell hg_w_cd hg_w_supp (hpsi_bd σ hσ_mem (t + L) r hrt_mem)
        hdv_bd (wfl r) hx_cell
    have hint_le := MeasureTheory.norm_integral_le_of_norm_le hmaj_int hpt
    have hmaj_val : (∫ x in B0579.cell p.c, maj x) ≤ (η_rem_target / 2) * B_norm := by
      dsimp [maj]
      rw [integral_add (hint_dens.const_mul _) (h_ind_cell.const_mul _),
        integral_const_mul, integral_const_mul, hint_dens_eq]
      have hind_le : (∫ x in B0579.cell p.c, D_box.indicator (fun _ => (1 : ℝ)) x) ≤ V_box := by
        have hmono : (∫ x in B0579.cell p.c, D_box.indicator (fun _ => (1 : ℝ)) x) ≤
            ∫ x : B0579.Plane, D_box.indicator (fun _ => (1 : ℝ)) x :=
          integral_mono_measure Measure.restrict_le_self
            (Eventually.of_forall fun x => indicator_nonneg (fun _ _ => zero_le_one) x)
            h_ind_int
        have hrhs_ind : (∫ x : B0579.Plane, D_box.indicator (fun _ => (1 : ℝ)) x) = V_box := by
          rw [integral_indicator hD_meas, setIntegral_const, smul_eq_mul, mul_one,
            Measure.real_def, ← hV_def]
        exact hmono.trans_eq hrhs_ind
      have hsq_4 : ‖(hwfl.memX r htr).toLp (wfl r)‖ ^ 2 ≤ 4 * ‖h‖ ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg _) hwflr_norm 2
        linarith
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hB_def]
      linarith
    exact hint_le.trans hmaj_val
  have hrhs_bd : ‖∫ r in t..(t + L), ∫ x in B0579.cell p.c, wfl r x *
      (deriv (fun r' => φ r' x) r + p.ν * lapP (φ r) x +
        (p.train.v r x 0 * B0579.pd 0 (φ r) x + p.train.v r x 1 * B0579.pd 1 (φ r) x))‖ ≤
      Lmax * ((η_rem_target / 2) * B_norm) := by
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t) (b := t + L) (C := (η_rem_target / 2) * B_norm) fun r hr => by
        rw [uIoc_of_le (by linarith)] at hr
        exact hslice_bd r (Ioc_subset_Icc_self hr)
    have habs_L : |t + L - t| = L := by
      have : t + L - t = L := by ring
      rw [this, abs_of_nonneg hL0]
    rw [habs_L] at h1
    have hCL : ((η_rem_target / 2) * B_norm) * L ≤ Lmax * ((η_rem_target / 2) * B_norm) := by
      have hc_nn : 0 ≤ (η_rem_target / 2) * B_norm := mul_nonneg (by positivity) hB_pos.le
      calc ((η_rem_target / 2) * B_norm) * L
          ≤ ((η_rem_target / 2) * B_norm) * Lmax := mul_le_mul_of_nonneg_left hL_le hc_nn
        _ = Lmax * ((η_rem_target / 2) * B_norm) := mul_comm _ _
    exact h1.trans hCL
  have hinner_diff : 2 * (‖h‖ ^ 2 - inner ℝ W_h h) ≤ ε_s ^ 2 / 2 := by
    rw [Real.norm_eq_abs, ← hweak] at hrhs_bd
    have h1 : ‖h‖ ^ 2 - inner ℝ W_h h ≤ |inner ℝ W_h h - ‖h‖ ^ 2| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    have h2 : 2 * (Lmax * ((η_rem_target / 2) * B_norm)) = ε_s ^ 2 / 2 := by
      rw [hη_rem_def]
      field_simp [hLmax.ne', hB_pos.ne']
    linarith
  have hsub_sq : ‖W_h - h‖ ^ 2 ≤ ε_s ^ 2 := by
    rw [norm_sub_sq_real]
    linarith
  have hsqrt := Real.sqrt_le_sqrt hsub_sq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hε_s.le] at hsqrt
  rwa [hW_def, hu₁_def, hf₀_def] at hsqrt

private theorem exists_pos_le_finset {α : Type*} (S : Finset α) (val : α → ℝ)
    (hpos : ∀ a ∈ S, 0 < val a) (hle1 : ∀ a ∈ S, val a ≤ 1) :
    ∃ v : ℝ, 0 < v ∧ v ≤ 1 ∧ ∀ a ∈ S, v ≤ val a := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, le_rfl, fun _ h => False.elim (Finset.notMem_empty _ h)⟩
  | @insert b s hb ih =>
    obtain ⟨v₀, hv₀_pos, hv₀_le1, hv₀⟩ :=
      ih (fun a ha => hpos a (Finset.mem_insert_of_mem ha))
        (fun a ha => hle1 a (Finset.mem_insert_of_mem ha))
    refine ⟨min (val b) v₀, lt_min (hpos b (Finset.mem_insert_self b s)) hv₀_pos,
      (min_le_right _ _).trans hv₀_le1, fun a ha => ?_⟩
    rcases Finset.mem_insert.1 ha with rfl | has
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hv₀ a has)

end UnforcedLeray.Short.IIb.CompactDuhamelFreeHelp

open UnforcedLeray.Short.IIb UnforcedLeray.Short.IIb.CompactDuhamelFreeHelp in
/-- **Main theorem (`PartII-b:F2/4/1`)**: free cylinder transport comparison on finite blocks. -/
theorem freeTransportComparison_proof : UnforcedLeray.Short.IIb.FreeTransportComparison := by
  intro m hm Sig Lmax hSig hLmax T_pl hT dm dp _hdm K hK ε hε
  obtain ⟨_Cm, _C_fb, _b_fb, δ_op, ν_op, _, _, _, hδ_op_pos, hδ_op_le,
      hν_op_pos, hν_op_le, _hflow_bd, hop_bd⟩ :=
    exists_free_prop_op_bound hm hSig hLmax (lt_min hε one_pos)
  have hε8 : 0 < ε / 8 := by positivity
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨t_net, ht_fin, ht_cov⟩ := Metric.totallyBounded_iff.1 hK.totallyBounded (ε / 8) hε8
  let S : Finset (Xm m) := ht_fin.toFinset
  have hd : Dense {f : Xm m | ∃ g : UnforcedLeray.B0579.Plane → ℝ, f =ᵐ[planeMeasure m] g ∧
      HasCompactSupport g ∧ ContDiff ℝ ∞ g} :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff (p := 2) (μ := planeMeasure m) (F := ℝ)
      (by simp)
  have hex_approx : ∀ y : Xm m, ∃ (h_y : Xm m) (δ_y ν_y : ℝ),
      ‖y - h_y‖ ≤ ε / 8 ∧ 0 < δ_y ∧ δ_y ≤ 1 ∧ 0 < ν_y ∧ ν_y ≤ 1 ∧
      ∀ (p : UnforcedLeray.Cons.C03.Concrete.Params) (d : ℝ),
        BgRegime p d dm dp → p.ν ≤ ν_y → p.ageCut = Sig →
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ δ_y → TrainCloseM m p.train Sig δ →
        ∀ Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m), IsFreeCylPropagator m p Sc →
        ∀ t L : ℝ, 0 ≤ t → 0 ≤ L → L ≤ Lmax → t + L ≤ p.H →
          ‖Jc p.c m (Sc (t + L) t (Rc p.c m (T_pl (p.ν * t) (-L) h_y))) - h_y‖ ≤ ε / 4 := by
    intro y
    obtain ⟨h_y, ⟨g_y, hhg_y, hgc_y, hgd_y⟩, hdist_y⟩ := hd.exists_dist_lt y hε8
    obtain ⟨δ_y, ν_y, hδ_pos, hδ_le, hν_pos, hν_le, hconv_y⟩ :=
      single_smooth_conv hm hSig hLmax hT hhg_y hgc_y hgd_y hε4
    have hnorm_y : ‖y - h_y‖ ≤ ε / 8 := by
      rw [← dist_eq_norm]
      exact hdist_y.le
    exact ⟨h_y, δ_y, ν_y, hnorm_y, hδ_pos, hδ_le, hν_pos, hν_le,
      fun p d hbg hν hAge δ hδ0 hδ hclose Sc hSc t L ht0 hL0 hL htLH =>
        hconv_y p d dm dp hbg hν hAge δ hδ0 hδ hclose Sc hSc t L ht0 hL0 hL htLH⟩
  choose h_approx δ_approx ν_approx h_spec using hex_approx
  obtain ⟨δ_fin, hδ_fin_pos, hδ_fin_le, hδ_fin⟩ :=
    exists_pos_le_finset S δ_approx
      (fun y _ => (h_spec y).2.1) (fun y _ => (h_spec y).2.2.1)
  obtain ⟨ν_fin, hν_fin_pos, hν_fin_le, hν_fin⟩ :=
    exists_pos_le_finset S ν_approx
      (fun y _ => (h_spec y).2.2.2.1) (fun y _ => (h_spec y).2.2.2.2.1)
  set δ : ℝ := min δ_op δ_fin
  set ν₀ : ℝ := min ν_op ν_fin
  refine ⟨δ, ν₀, lt_min hδ_op_pos hδ_fin_pos, (min_le_left _ _).trans hδ_op_le,
    lt_min hν_op_pos hν_fin_pos, (min_le_left _ _).trans hν_op_le, ?_⟩
  intro p d hbg hν_le hAge hcloseM Sc hSc t L ht0 hL0 hL_le htLH
  have hδ0 : 0 ≤ δ := (lt_min hδ_op_pos hδ_fin_pos).le
  have hSc_min : ‖Sc (t + L) t‖ ≤ 1 + min ε 1 :=
    hop_bd p d dm dp hbg (hν_le.trans (min_le_left _ _)) hAge δ hδ0
      (min_le_left _ _) hcloseM Sc hSc t L ht0 hL0 hL_le htLH
  have hSc_ε : ‖Sc (t + L) t‖ ≤ 1 + ε := hSc_min.trans (by linarith [min_le_left ε 1])
  have hSc_2 : ‖Sc (t + L) t‖ ≤ 2 := hSc_min.trans (by linarith [min_le_right ε 1])
  refine ⟨hSc_ε, fun f hfK => ?_⟩
  have hσ_mem : p.ν * t ∈ Icc 0 Sig := by
    refine ⟨mul_nonneg p.ν_pos.le ht0, ?_⟩
    have hH_eq : p.H = Sig / p.ν := by unfold UnforcedLeray.Cons.C03.Concrete.Params.H; rw [hAge]
    have htSig : t ≤ Sig / p.ν := by linarith
    have := (le_div_iff₀ p.ν_pos).1 htSig
    linarith
  have hf_cov := ht_cov hfK
  rw [mem_iUnion₂] at hf_cov
  obtain ⟨y, hy_t, hfy_ball⟩ := hf_cov
  have hy_S : y ∈ S := ht_fin.mem_toFinset.2 hy_t
  set h_y : Xm m := h_approx y
  have hfy_norm : ‖f - y‖ ≤ ε / 8 := by
    rw [Metric.mem_ball, dist_eq_norm] at hfy_ball
    exact hfy_ball.le
  have hyh_norm : ‖y - h_y‖ ≤ ε / 8 := (h_spec y).1
  have hfh_norm : ‖f - h_y‖ ≤ ε / 4 := by
    have heq : f - h_y = (f - y) + (y - h_y) := by abel
    rw [heq]
    exact (norm_add_le _ _).trans (by linarith)
  set W : Xm m →L[ℝ] Xm m :=
    (Jc p.c m).comp ((Sc (t + L) t).comp ((Rc p.c m).comp (T_pl (p.ν * t) (-L))))
  have hW_sub_bd : ‖W (f - h_y)‖ ≤ 2 * ‖f - h_y‖ := by
    dsimp [W]
    rw [norm_Jc_apply]
    calc ‖Sc (t + L) t (Rc p.c m (T_pl (p.ν * t) (-L) (f - h_y)))‖
        ≤ ‖Sc (t + L) t‖ * ‖Rc p.c m (T_pl (p.ν * t) (-L) (f - h_y))‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 2 * ‖T_pl (p.ν * t) (-L) (f - h_y)‖ :=
          mul_le_mul hSc_2 (norm_Rc_apply_le p.c m _) (norm_nonneg _) zero_le_two
      _ = 2 * ‖f - h_y‖ := by rw [hT.isometry (p.ν * t) hσ_mem (-L)]
  have hW_hy : ‖W h_y - h_y‖ ≤ ε / 4 :=
    (h_spec y).2.2.2.2.2 p d hbg
      (hν_le.trans ((min_le_right _ _).trans (hν_fin y hy_S))) hAge δ hδ0
      ((min_le_right _ _).trans (hδ_fin y hy_S)) hcloseM Sc hSc t L ht0 hL0 hL_le htLH
  have hdecomp : W f - f = W (f - h_y) + (W h_y - h_y) - (f - h_y) := by
    rw [map_sub]
    abel
  change ‖W f - f‖ ≤ ε
  rw [hdecomp]
  calc ‖W (f - h_y) + (W h_y - h_y) - (f - h_y)‖
      ≤ ‖W (f - h_y) + (W h_y - h_y)‖ + ‖f - h_y‖ := norm_sub_le _ _
    _ ≤ ‖W (f - h_y)‖ + ‖W h_y - h_y‖ + ‖f - h_y‖ := by
        linarith [norm_add_le (W (f - h_y)) (W h_y - h_y)]
    _ ≤ 2 * (ε / 4) + ε / 4 + ε / 4 := by linarith
    _ = ε := by ring
