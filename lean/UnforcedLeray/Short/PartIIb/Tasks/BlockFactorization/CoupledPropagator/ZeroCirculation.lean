import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.CoupledPropagator.ZeroCirculation.EtaCutoff
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.CoupledPropagator.ZeroCirculation.KernelDivFree
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N4
import UnforcedLeray.Short.PartIIb.Tasks.InteractionCylinder.TrainGradCoeff

/-!
# `PartII-b:F2/2/2` — Zero-Circulation Preservation of `Sc` and Zero Circulation of `Ac`

Source of record: `the November 2 reference manuscript` (SP), lines 2076–2083,
2117–2123.

Proves `freeAndInteractionZeroCircStep_proof : UnforcedLeray.Short.IIb.FreeAndInteractionZeroCircStep`:
1. The free cylinder propagator `Sc` (`IsFreeCylPropagator m p Sc`) preserves `HasZeroCirculationR p.c`
   on `0 ≤ s ≤ t ≤ p.H`, via smooth `η`-cutoffs `etaCut R` (`R → ∞`) in `hSc.weak` and `cylTrainBound`;
2. Every cylinder interaction output `Ac r g` (`r ∈ Icc 0 p.H`, `IsCylInteractionOp p.train m r (Ac r)`)
   satisfies `HasZeroCirculationR p.c (Ac r g)`, via `integral_K_dot_grad_test_eq_zero` against
   `etaCut R * Ec` and weighted `Ec` decay on `B0579.cell p.c`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.ZeroCircAux

open UnforcedLeray
open UnforcedLeray.Cons.C03.Concrete

/-! ## 1. Real `L¹(cell)` bound from `CCP.exists_L1_const` -/

private theorem integral_norm_le_of_Xmc {c m : ℝ} (hm : 1 / 2 < m) {C1 : ℝ} (hC1 : 0 ≤ C1)
    (hL1 : ∀ w : Xmc c m,
      eLpNorm (⇑w) 1 (volume.restrict (B0579.cell c)) ≤ ENNReal.ofReal C1 * ‖w‖ₑ)
    (w : Xmc c m) :
    ∫ x in B0579.cell c, ‖w x‖ ≤ C1 * ‖w‖ := by
  have hw_int := PartIIbF22Aux.integrableOn_cell_of_Xmc c m hm w
  rw [integral_norm_eq_lintegral_enorm hw_int.aestronglyMeasurable]
  have h1 := hL1 w
  rw [eLpNorm_one_eq_lintegral_enorm, ← enorm_norm w,
    Real.enorm_eq_ofReal (norm_nonneg w), ← ENNReal.ofReal_mul hC1] at h1
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h1).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg hC1 (norm_nonneg w)))

/-! ## 2. Part 1: Free propagator `Sc` preserves `HasZeroCirculationR` -/

theorem free_zero_circ
    {m Sig : ℝ} (hm : 8 < m) (hSig : 0 < Sig)
    {p : Params} {d dm dp : ℝ} (_hbg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1)
    (hAge : p.ageCut = Sig)
    {δ : ℝ} (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1) (hTCM : TrainCloseM m p.train Sig δ)
    {Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)} (hSc : IsFreeCylPropagator m p Sc)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ p.H)
    (f : Xmc p.c m) (hf : HasZeroCirculationR p.c f) :
    HasZeroCirculationR p.c (Sc t s f) := by
  have hν : 0 < p.ν := p.ν_pos
  have hH_eq : p.H = Sig / p.ν := by rw [Params.H, hAge]
  have hm_half : 1 / 2 < m := by linarith
  have hTC : TrainClose p.train Sig δ := hTCM.toTrainClose (by linarith)
  obtain ⟨Mv0, hMv0⟩ := cylTrainBound Sig p.ν p.c δ hSig hν p.c_pos hδ0.le p.train hTC
  set Mv : ℝ := max Mv0 0
  have hMv_nn : 0 ≤ Mv := le_max_right _ _
  have hMv : ∀ r ∈ Icc 0 p.H, ∀ x : B0579.Plane,
      |p.train.v r x 0| + |p.train.v r x 1| ≤ Mv := by
    intro r hr x
    exact (hMv0 r hr.1 (hr.2.trans_eq hH_eq) x).trans (le_max_left _ _)
  obtain ⟨C_B, hCB, hCut⟩ := exists_etaCut_deriv_bound
  obtain ⟨C1, hC1, hL1⟩ := CCP.exists_L1_const p.c m hm_half
  have hcont_Sc : ContinuousOn (fun r => Sc r s f) (Icc s t) :=
    (hSc.strongCont s ⟨hs, hst.trans ht⟩ f).mono (Icc_subset_Icc_right ht)
  obtain ⟨MS0, hMS0⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_Sc
  set MS : ℝ := max MS0 0
  have hMS_nn : 0 ≤ MS := le_max_right _ _
  have hMS : ∀ r ∈ Icc s t, ‖Sc r s f‖ ≤ MS := fun r hr =>
    (hMS0 r hr).trans (le_max_left _ _)
  let K_tot : ℝ := (1 + Mv) * C_B * C1 * MS * (t - s)
  have h_rem_bd : ∀ R : ℝ, 1 ≤ R →
      ‖∫ r in s..t, ∫ x in B0579.cell p.c,
          cylFreeIntegrand p.train (Sc r s f) r (etaCut R) x‖ ≤ K_tot / R := by
    intro R hR1
    have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
    have hφR : B0579.IsCylTest p.c (etaCut R) := isCylTest_etaCut p.c hR0
    have hslice : ∀ r ∈ uIoc s t,
        ‖∫ x in B0579.cell p.c, cylFreeIntegrand p.train (Sc r s f) r (etaCut R) x‖ ≤
          ((1 + Mv) * C_B / R) * (C1 * MS) := by
      intro r hr_u
      rw [uIoc_of_le hst] at hr_u
      have hr_st : r ∈ Icc s t := ⟨hr_u.1.le, hr_u.2⟩
      have hr_0H : r ∈ Icc 0 p.H := ⟨hs.trans hr_st.1, hr_st.2.trans ht⟩
      have hint_free : IntegrableOn
          (cylFreeIntegrand p.train (Sc r s f) r (etaCut R)) (B0579.cell p.c) volume :=
        hSc.integrable hφR hs hr_st.1 hr_0H.2 f
      have hint_w : IntegrableOn (Sc r s f) (B0579.cell p.c) volume :=
        PartIIbF22Aux.integrableOn_cell_of_Xmc p.c m hm_half (Sc r s f)
      have hpw : ∀ x : B0579.Plane,
          ‖cylFreeIntegrand p.train (Sc r s f) r (etaCut R) x‖ ≤
            ((1 + Mv) * C_B / R) * ‖(Sc r s f) x‖ := by
        intro x
        obtain ⟨hpd0, hpd1, hlap⟩ := hCut R hR1 x
        have hv1 : |p.train.v r x 1| ≤ Mv := by
          linarith [abs_nonneg (p.train.v r x 0), hMv r hr_0H x]
        have hcoef :
            |p.ν * lapP (etaCut R) x +
              (p.train.v r x 0 * B0579.pd 0 (etaCut R) x +
                p.train.v r x 1 * B0579.pd 1 (etaCut R) x)| ≤ (1 + Mv) * C_B / R := by
          rw [hpd0, mul_zero, zero_add]
          have h1 : |p.ν * lapP (etaCut R) x| ≤ 1 * (C_B / R) := by
            rw [abs_mul, abs_of_pos hν]
            exact mul_le_mul hν1 hlap (abs_nonneg _) zero_le_one
          have h2 : |p.train.v r x 1 * B0579.pd 1 (etaCut R) x| ≤ Mv * (C_B / R) := by
            rw [abs_mul]
            exact mul_le_mul hv1 hpd1 (abs_nonneg _) hMv_nn
          calc |p.ν * lapP (etaCut R) x + p.train.v r x 1 * B0579.pd 1 (etaCut R) x|
              ≤ |p.ν * lapP (etaCut R) x| + |p.train.v r x 1 * B0579.pd 1 (etaCut R) x| :=
                abs_add_le _ _
            _ ≤ 1 * (C_B / R) + Mv * (C_B / R) := add_le_add h1 h2
            _ = (1 + Mv) * C_B / R := by ring
        unfold cylFreeIntegrand
        rw [norm_mul, mul_comm ‖(Sc r s f) x‖, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
      calc ‖∫ x in B0579.cell p.c, cylFreeIntegrand p.train (Sc r s f) r (etaCut R) x‖
          ≤ ∫ x in B0579.cell p.c, ‖cylFreeIntegrand p.train (Sc r s f) r (etaCut R) x‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x in B0579.cell p.c, ((1 + Mv) * C_B / R) * ‖(Sc r s f) x‖ :=
            integral_mono hint_free.norm (hint_w.norm.const_mul _) hpw
        _ = ((1 + Mv) * C_B / R) * ∫ x in B0579.cell p.c, ‖(Sc r s f) x‖ :=
            integral_const_mul _ _
        _ ≤ ((1 + Mv) * C_B / R) * (C1 * ‖Sc r s f‖) :=
            mul_le_mul_of_nonneg_left (integral_norm_le_of_Xmc hm_half hC1 hL1 (Sc r s f))
              (div_nonneg (mul_nonneg (by positivity) hCB) hR0.le)
        _ ≤ ((1 + Mv) * C_B / R) * (C1 * MS) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hMS r hr_st) hC1)
              (div_nonneg (mul_nonneg (by positivity) hCB) hR0.le)
    have hint_t := intervalIntegral.norm_integral_le_of_norm_le_const hslice
    rw [abs_of_nonneg (sub_nonneg.2 hst)] at hint_t
    refine hint_t.trans_eq ?_
    dsimp [K_tot]
    ring
  have htend_rem : Tendsto
      (fun R : ℝ => ∫ r in s..t, ∫ x in B0579.cell p.c,
        cylFreeIntegrand p.train (Sc r s f) r (etaCut R) x)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_
      ((tendsto_const_nhds (x := K_tot)).div_atTop tendsto_id)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR1
    exact h_rem_bd R hR1
  have htend_f : Tendsto (fun R : ℝ => ∫ x in B0579.cell p.c, f x * etaCut R x)
      atTop (𝓝 0) := by
    have h := tendsto_integral_mul_etaCut hf.1
    rwa [hf.2] at h
  have htend_rhs : Tendsto (fun R : ℝ => ∫ x in B0579.cell p.c, (Sc t s f) x * etaCut R x)
      atTop (𝓝 0) := by
    have hsum : Tendsto
        (fun R : ℝ => (∫ x in B0579.cell p.c, f x * etaCut R x) +
          ∫ r in s..t, ∫ x in B0579.cell p.c,
            cylFreeIntegrand p.train (Sc r s f) r (etaCut R) x)
        atTop (𝓝 (0 + 0)) := htend_f.add htend_rem
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR1
    have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
    exact (hSc.weak (isCylTest_etaCut p.c hR0) hs hst ht f).symm
  have hint_Sc := PartIIbF22Aux.integrableOn_cell_of_Xmc p.c m hm_half (Sc t s f)
  have htend_lhs := tendsto_integral_mul_etaCut hint_Sc
  exact ⟨hint_Sc, tendsto_nhds_unique htend_lhs htend_rhs⟩

/-! ## 3. Part 2: Interaction operator `Ac r g` has `HasZeroCirculationR` -/

private theorem rpow_jb_mul_exp_neg_le (k : ℝ) (_hk : 0 ≤ k) {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : B0579.Plane,
      B0579.jb x ^ k * Real.exp (-(β * GaussianVortex.radiusSq x)) ≤ C := by
  set N : ℕ := ⌈k⌉₊ + 1
  have hkN : k ≤ (N : ℝ) := by
    dsimp [N]; push_cast; linarith [Nat.le_ceil k]
  refine ⟨(N.factorial : ℝ) * (1 / β) ^ N * Real.exp β, by positivity, fun x => ?_⟩
  set s : ℝ := GaussianVortex.radiusSq x
  have hs : 0 ≤ s := by unfold s GaussianVortex.radiusSq; positivity
  have hjb_eq : B0579.jb x = 1 + s := by unfold B0579.jb s GaussianVortex.radiusSq; ring
  have h1s : 1 ≤ 1 + s := by linarith
  have hrpow : (1 + s) ^ k ≤ (1 + s) ^ N := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le h1s hkN
  set u : ℝ := β * (1 + s)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have h1 : u ^ N / (N.factorial : ℝ) ≤ Real.exp u := Real.pow_div_factorial_le_exp u hu N
  have hfac : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have h2 : u ^ N ≤ (N.factorial : ℝ) * Real.exp u := by
    have h3 := (div_le_iff₀ hfac).mp h1
    linarith [mul_comm (Real.exp u) (N.factorial : ℝ)]
  have h3 : u ^ N = β ^ N * (1 + s) ^ N := by dsimp [u]; rw [mul_pow]
  have hc : (1 / β) ^ N * β ^ N = 1 := by
    rw [← mul_pow, one_div_mul_cancel hβ.ne', one_pow]
  have h4 : (1 + s) ^ N ≤ ((N.factorial : ℝ) * (1 / β) ^ N) * Real.exp u := by
    calc (1 + s) ^ N = (1 / β) ^ N * (β ^ N * (1 + s) ^ N) := by rw [← mul_assoc, hc, one_mul]
      _ ≤ (1 / β) ^ N * ((N.factorial : ℝ) * Real.exp u) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← h3]; exact h2
      _ = ((N.factorial : ℝ) * (1 / β) ^ N) * Real.exp u := by ring
  have hexp : Real.exp u * Real.exp (-(β * s)) = Real.exp β := by
    rw [← Real.exp_add]
    congr 1
    dsimp [u]; ring
  rw [hjb_eq]
  calc (1 + s) ^ k * Real.exp (-(β * s))
      ≤ (1 + s) ^ N * Real.exp (-(β * s)) :=
        mul_le_mul_of_nonneg_right hrpow (Real.exp_pos _).le
    _ ≤ (((N.factorial : ℝ) * (1 / β) ^ N) * Real.exp u) * Real.exp (-(β * s)) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = ((N.factorial : ℝ) * (1 / β) ^ N) * (Real.exp u * Real.exp (-(β * s))) := by ring
    _ = (N.factorial : ℝ) * (1 / β) ^ N * Real.exp β := by rw [hexp]

/-- Weighted decay `|Ec(r, x)| * jb(x)^{m/2 + 1} ≤ C_E` on `B0579.cell p.c`. -/
private theorem exists_Ec_weighted_bound
    {m Sig : ℝ} (hm : 8 < m) (_hSig : 0 < Sig)
    {p : Params} {d dm dp : ℝ} (hbg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1)
    (hAge : p.ageCut = Sig)
    {δ : ℝ} (hδ0 : 0 < δ) (hTCM : TrainCloseM m p.train Sig δ)
    {r : ℝ} (hr : r ∈ Icc 0 p.H) :
    ∃ C_E : ℝ, 0 ≤ C_E ∧ ∀ x ∈ B0579.cell p.c,
      |B0238.Ec p.train r x| * B0579.jb x ^ (m / 2 + 1) ≤ C_E := by
  have hc1 : 1 ≤ p.c := bgRegime_c_ge_one hbg hν1
  have hc_pos : 0 < p.c := p.c_pos
  have hν : 0 < p.ν := p.ν_pos
  have hH_eq : p.H = Sig / p.ν := by rw [Params.H, hAge]
  have hr_Sg : r ≤ Sig / p.ν := hr.2.trans_eq hH_eq
  set σ : ℝ := p.ν * r
  have hσ0 : 0 ≤ σ := mul_nonneg hν.le hr.1
  have hσ1 : σ ≤ Sig := by
    dsimp [σ]
    have h1 := mul_le_mul_of_nonneg_left hr_Sg hν.le
    rwa [mul_div_cancel₀ _ hν.ne'] at h1
  have ha_mem : 1 + σ ∈ Icc 1 (1 + Sig) := ⟨by linarith, by linarith⟩
  have hk_nn : 0 ≤ m / 2 + 1 := by linarith
  obtain ⟨C_tail, hC_tail, htail⟩ := gf_cell_tail_weighted_bound (Sg := Sig) hk_nn gf_eExp
  obtain ⟨K0, β0, hK0, hβ0, hbd0⟩ := (gf_eExp (A₂ := 1 + Sig))
  obtain ⟨C_gauss, hC_gauss, hgauss⟩ := rpow_jb_mul_exp_neg_le (m / 2 + 1) hk_nn hβ0
  set C_E : ℝ := K0 * C_gauss + C_tail * p.c ^ (-2 : ℝ) + 2 * δ
  have hC_E_nn : 0 ≤ C_E := by
    have hc_rpow : 0 ≤ p.c ^ (-2 : ℝ) := Real.rpow_nonneg hc_pos.le _
    dsimp [C_E]; positivity
  refine ⟨C_E, hC_E_nn, fun x hx => ?_⟩
  have hsmV : ContDiff ℝ ∞ (p.train.v r) := B0238.contDiff_Vc p.train hr.1
  have hsmVc : ContDiff ℝ ∞ (Train.Vc p.ν p.c r) :=
    UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc_pos
      (UnforcedLeray.Short.Spine.vcReg_width_pos hν hr.1)
  let w : B0579.Plane → Cyl.Vec2 := fun z => p.train.v r z - Train.Vc p.ν p.c r z
  have hsmW : ContDiff ℝ ∞ w := hsmV.sub hsmVc
  have hv_split : p.train.v r = fun z => Train.Vc p.ν p.c r z + w z := by
    funext z; simp [w]
  have hEc_split : B0238.Ec p.train r x =
      Cyl.curl (Train.Vc p.ν p.c r) x + Cyl.curl w x := by
    change Cyl.curl (p.train.v r) x = _
    rw [hv_split, curl_add_smooth hsmVc hsmW]
  have hjb_nn : 0 ≤ B0579.jb x ^ (m / 2 + 1) := Real.rpow_nonneg (B0579.jb_pos x).le _
  have hw_bd : |Cyl.curl w x| * B0579.jb x ^ (m / 2 + 1) ≤ 2 * δ := by
    have hcurl_w : Cyl.curl w x = curlLam (fderiv ℝ w x) :=
      congrFun (curl_eq_curlLam_fderiv hsmW) x
    have h1 : |Cyl.curl w x| ≤ 2 * ‖iteratedFDeriv ℝ 1 w x‖ := by
      rw [hcurl_w, ← Real.norm_eq_abs, norm_iteratedFDeriv_one]
      exact (curlLam.le_opNorm (fderiv ℝ w x)).trans
        (mul_le_mul_of_nonneg_right norm_curlLam_le (norm_nonneg _))
    calc |Cyl.curl w x| * B0579.jb x ^ (m / 2 + 1)
        ≤ (2 * ‖iteratedFDeriv ℝ 1 w x‖) * B0579.jb x ^ (m / 2 + 1) :=
          mul_le_mul_of_nonneg_right h1 hjb_nn
      _ = 2 * (‖iteratedFDeriv ℝ 1 w x‖ * B0579.jb x ^ (m / 2 + 1)) := by ring
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left (hTCM r hr.1 hr_Sg x hx 1 (by norm_num)) (by norm_num)
  have hVc_eq : Cyl.curl (Train.Vc p.ν p.c r) x =
      B0146.latticeSum p.c (B0113.eExp (1 + σ)) x := by
    rw [Train.Vc_curl hν hc_pos.ne' hr.1 x]
    rfl
  have hsh0 : B0146.shift p.c 0 x = x := by ext <;> simp [B0146.shift]
  have h0_bd : |B0113.eExp (1 + σ) (B0146.shift p.c 0 x)| * B0579.jb x ^ (m / 2 + 1) ≤
      K0 * C_gauss := by
    rw [hsh0]
    calc |B0113.eExp (1 + σ) x| * B0579.jb x ^ (m / 2 + 1)
        ≤ (K0 * Real.exp (-(β0 * GaussianVortex.radiusSq x))) * B0579.jb x ^ (m / 2 + 1) :=
          mul_le_mul_of_nonneg_right (hbd0 (1 + σ) ha_mem x) hjb_nn
      _ = K0 * (B0579.jb x ^ (m / 2 + 1) * Real.exp (-(β0 * GaussianVortex.radiusSq x))) := by ring
      _ ≤ K0 * C_gauss := mul_le_mul_of_nonneg_left (hgauss x) hK0
  have htail_x := htail p.c hc1 (1 + σ) ha_mem x hx
  have hVc_bd : |Cyl.curl (Train.Vc p.ν p.c r) x| * B0579.jb x ^ (m / 2 + 1) ≤
      K0 * C_gauss + C_tail * p.c ^ (-2 : ℝ) := by
    rw [hVc_eq]
    have htri : |B0146.latticeSum p.c (B0113.eExp (1 + σ)) x| ≤
        |B0113.eExp (1 + σ) (B0146.shift p.c 0 x)| +
          |B0146.latticeSum p.c (B0113.eExp (1 + σ)) x -
            B0113.eExp (1 + σ) (B0146.shift p.c 0 x)| := by
      have heq : B0146.latticeSum p.c (B0113.eExp (1 + σ)) x =
          B0113.eExp (1 + σ) (B0146.shift p.c 0 x) +
            (B0146.latticeSum p.c (B0113.eExp (1 + σ)) x -
              B0113.eExp (1 + σ) (B0146.shift p.c 0 x)) := by ring
      conv_lhs => rw [heq]
      exact abs_add_le _ _
    calc |B0146.latticeSum p.c (B0113.eExp (1 + σ)) x| * B0579.jb x ^ (m / 2 + 1)
        ≤ (|B0113.eExp (1 + σ) (B0146.shift p.c 0 x)| +
            |B0146.latticeSum p.c (B0113.eExp (1 + σ)) x -
              B0113.eExp (1 + σ) (B0146.shift p.c 0 x)|) * B0579.jb x ^ (m / 2 + 1) :=
          mul_le_mul_of_nonneg_right htri hjb_nn
      _ = |B0113.eExp (1 + σ) (B0146.shift p.c 0 x)| * B0579.jb x ^ (m / 2 + 1) +
            |B0146.latticeSum p.c (B0113.eExp (1 + σ)) x -
              B0113.eExp (1 + σ) (B0146.shift p.c 0 x)| * B0579.jb x ^ (m / 2 + 1) :=
          add_mul _ _ _
      _ ≤ K0 * C_gauss + C_tail * p.c ^ (-2 : ℝ) := add_le_add h0_bd htail_x
  rw [hEc_split]
  calc |Cyl.curl (Train.Vc p.ν p.c r) x + Cyl.curl w x| * B0579.jb x ^ (m / 2 + 1)
      ≤ (|Cyl.curl (Train.Vc p.ν p.c r) x| + |Cyl.curl w x|) * B0579.jb x ^ (m / 2 + 1) :=
        mul_le_mul_of_nonneg_right (abs_add_le _ _) hjb_nn
    _ = |Cyl.curl (Train.Vc p.ν p.c r) x| * B0579.jb x ^ (m / 2 + 1) +
          |Cyl.curl w x| * B0579.jb x ^ (m / 2 + 1) := add_mul _ _ _
    _ ≤ (K0 * C_gauss + C_tail * p.c ^ (-2 : ℝ)) + 2 * δ := add_le_add hVc_bd hw_bd
    _ = C_E := rfl

private theorem isPeriodic_Ec {ν c : ℝ} (tr : B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) :
    ∀ x : B0579.Plane, B0238.Ec tr r (x.1 + c, x.2) = B0238.Ec tr r x := by
  intro x
  have hsm : ContDiff ℝ ∞ (tr.v r) := B0238.contDiff_Vc tr hr
  have hfun : (fun y : B0579.Plane => tr.v r (y + ((c, 0) : B0579.Plane))) = tr.v r := by
    funext y
    have hy : y + ((c, 0) : B0579.Plane) = (y.1 + c, y.2) := by ext <;> simp
    rw [hy]
    exact tr.isTrain.periodic_v r hr y
  have hfd := fderiv_comp_add_right (𝕜 := ℝ) (f := tr.v r) (x := x) ((c, 0) : B0579.Plane)
  rw [hfun] at hfd
  have hx : x + ((c, 0) : B0579.Plane) = (x.1 + c, x.2) := by ext <;> simp
  rw [hx] at hfd
  unfold B0238.Ec
  rw [curl_eq_curlLam_fderiv hsm]
  change curlLam (fderiv ℝ (tr.v r) (x.1 + c, x.2)) = curlLam (fderiv ℝ (tr.v r) x)
  rw [← hfd]

/-- Integrability of `x ↦ |Cyl.K c g x 1| * jb(x)^{-(m/2 + 1)}` on `B0579.cell c`. -/
private theorem integrableOn_abs_K_one_mul_jb_neg {c m : ℝ} (hc : 1 ≤ c) (hm : 8 < m)
    (g : Xmc c m) :
    IntegrableOn (fun x => |Cyl.K c g x 1| * B0579.jb x ^ (-(m / 2 + 1)))
      (B0579.cell c) volume := by
  have hm1 : 1 < m := by linarith
  have hm_half : 1 / 2 < m := by linarith
  let b_wt : B0579.Plane → B0579.Plane := fun x => (0, B0579.jb x ^ (-(m / 2 + 1)))
  have hjb_cont : Continuous B0579.jb := by
    unfold B0579.jb; fun_prop
  have hb_cont : Continuous b_wt :=
    continuous_const.prodMk
      (hjb_cont.rpow_const fun x => Or.inl (B0579.jb_pos x).ne')
  have hb_wt : IsCylWeightedCoeff c m 1 b_wt := by
    refine ⟨hb_cont, fun x _hx => ?_⟩
    have hnn : 0 ≤ B0579.jb x ^ (-(m / 2 + 1)) := Real.rpow_nonneg (B0579.jb_pos x).le _
    simp only [b_wt, abs_zero, zero_add, abs_of_nonneg hnn]
    rw [← Real.rpow_add (B0579.jb_pos x), neg_add_cancel, Real.rpow_zero]
  let w_wt : Xmc c m := cylWeightedLpFun hc hm1 zero_le_one hb_wt g
  have hw_int : IntegrableOn (fun x => ‖w_wt x‖) (B0579.cell c) volume :=
    (PartIIbF22Aux.integrableOn_cell_of_Xmc c m hm_half w_wt).norm
  have hw_ae := ae_restrict_cell_of_cellMeasure (coeFn_cylWeightedLpFun hc hm1 zero_le_one hb_wt g)
  refine hw_int.congr ?_
  filter_upwards [hw_ae] with x hx
  have hnn : 0 ≤ B0579.jb x ^ (-(m / 2 + 1)) := Real.rpow_nonneg (B0579.jb_pos x).le _
  rw [Real.norm_eq_abs, hx]
  simp only [cylWeightedOpFun, b_wt, mul_zero, zero_add, abs_neg, abs_mul, abs_of_nonneg hnn]

theorem interaction_zero_circ
    {m Sig : ℝ} (hm : 8 < m) (hSig : 0 < Sig)
    {p : Params} {d dm dp : ℝ} (hbg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1)
    (hAge : p.ageCut = Sig)
    {δ : ℝ} (hδ0 : 0 < δ) (hTCM : TrainCloseM m p.train Sig δ)
    {Ac : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)}
    (hAc : ∀ s ∈ Icc 0 p.H, IsCylInteractionOp p.train m s (Ac s))
    {r : ℝ} (hr : r ∈ Icc 0 p.H) (g : Xmc p.c m) :
    HasZeroCirculationR p.c (Ac r g) := by
  have hc1 : 1 ≤ p.c := bgRegime_c_ge_one hbg hν1
  have hm1 : 1 < m := by linarith
  have hm_half : 1 / 2 < m := by linarith
  obtain ⟨C_B, hCB, hCut⟩ := exists_etaCut_deriv_bound
  obtain ⟨C_E, hCE, hE_bd⟩ := exists_Ec_weighted_bound hm hSig hbg hν1 hAge hδ0 hTCM hr
  let E : B0579.Plane → ℝ := B0238.Ec p.train r
  have hE_sm : ContDiff ℝ ∞ E := contDiff_curl (B0238.contDiff_Vc p.train hr.1)
  have hE_diff : Differentiable ℝ E := hE_sm.differentiable (by simp)
  have hE_per : ∀ x : B0579.Plane, E (x.1 + p.c, x.2) = E x := isPeriodic_Ec p.train hr.1
  have hint_Ac : IntegrableOn (Ac r g) (B0579.cell p.c) volume :=
    PartIIbF22Aux.integrableOn_cell_of_Xmc p.c m hm_half (Ac r g)
  have hae_Ac : (Ac r g : B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell p.c)]
      cylAc p.train r g :=
    ae_restrict_cell_of_cellMeasure (hAc r hr g)
  let majK : B0579.Plane → ℝ := fun x => |Cyl.K p.c g x 1| * B0579.jb x ^ (-(m / 2 + 1))
  have hmajK_int : IntegrableOn majK (B0579.cell p.c) volume :=
    integrableOn_abs_K_one_mul_jb_neg hc1 hm g
  let I_maj : ℝ := ∫ x in B0579.cell p.c, majK x
  have h_cut_bd : ∀ R : ℝ, 1 ≤ R →
      ‖∫ x in B0579.cell p.c, (Ac r g) x * etaCut R x‖ ≤ (C_B * C_E * I_maj) / R := by
    intro R hR1
    have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
    let φ_R : B0579.Plane → ℝ := fun z => etaCut R z * E z
    have hφ_R : B0579.IsCylTest p.c φ_R := isCylTest_etaCut_mul hR0 hE_sm hE_per
    have hint_Ac_cut : IntegrableOn (fun x => (Ac r g) x * etaCut R x) (B0579.cell p.c) volume := by
      refine Integrable.mono' hint_Ac.norm
        (hint_Ac.aestronglyMeasurable.mul (continuous_etaCut R).aestronglyMeasurable.restrict)
        (Eventually.of_forall fun x => ?_)
      rw [norm_mul, Real.norm_of_nonneg (etaCut_nonneg R x)]
      exact mul_le_of_le_one_right (norm_nonneg _) (etaCut_le_one R x)
    have hae_cut : (fun x => (Ac r g) x * etaCut R x) =ᵐ[volume.restrict (B0579.cell p.c)]
        fun x => cylAc p.train r g x * etaCut R x := by
      filter_upwards [hae_Ac] with x hx
      rw [hx]
    have hint_cylAc_cut : IntegrableOn (fun x => cylAc p.train r g x * etaCut R x)
        (B0579.cell p.c) volume :=
      hint_Ac_cut.congr hae_cut
    let D_R : B0579.Plane → ℝ := fun x =>
      -(Cyl.K p.c g x 0 * B0579.pd 0 φ_R x + Cyl.K p.c g x 1 * B0579.pd 1 φ_R x)
    have hint_DR : IntegrableOn D_R (B0579.cell p.c) volume :=
      ((integrableOn_K_mul_test hc1 hm1 g (hφ_R.pd 0) 0).add
        (integrableOn_K_mul_test hc1 hm1 g (hφ_R.pd 1) 1)).neg
    have hint_DR_zero : ∫ x in B0579.cell p.c, D_R x = 0 := by
      dsimp only [D_R]
      rw [integral_neg, integral_K_dot_grad_test_eq_zero hc1 hm1 g hφ_R, neg_zero]
    let rem_R : B0579.Plane → ℝ := fun x =>
      Cyl.K p.c g x 1 * B0579.pd 1 (etaCut R) x * E x
    have hrem_eq : rem_R = fun x => cylAc p.train r g x * etaCut R x - D_R x := by
      funext x
      obtain ⟨hpd0, hpd1⟩ := pd_etaCut_mul R hE_diff x
      dsimp only [rem_R, D_R, φ_R, cylAc, E]
      rw [hpd0, hpd1]
      ring
    have hint_rem : IntegrableOn rem_R (B0579.cell p.c) volume := by
      rw [hrem_eq]
      exact hint_cylAc_cut.sub hint_DR
    have hint_eq : ∫ x in B0579.cell p.c, (Ac r g) x * etaCut R x =
        ∫ x in B0579.cell p.c, rem_R x := by
      rw [integral_congr_ae hae_cut]
      have h1 : ∫ x in B0579.cell p.c, rem_R x =
          (∫ x in B0579.cell p.c, cylAc p.train r g x * etaCut R x) -
            ∫ x in B0579.cell p.c, D_R x := by
        rw [hrem_eq]
        exact integral_sub hint_cylAc_cut hint_DR
      rw [h1, hint_DR_zero, sub_zero]
    have hpw : ∀ᵐ x ∂(volume.restrict (B0579.cell p.c)),
        ‖rem_R x‖ ≤ (C_B * C_E / R) * majK x := by
      refine (ae_restrict_iff' (B0579.measurableSet_cell p.c)).2 (Eventually.of_forall fun x hx => ?_)
      obtain ⟨_, hpd1_bd, _⟩ := hCut R hR1 x
      have hEx_bd : |E x| ≤ C_E * B0579.jb x ^ (-(m / 2 + 1)) := by
        have hjb_neg_nn : 0 ≤ B0579.jb x ^ (-(m / 2 + 1)) :=
          Real.rpow_nonneg (B0579.jb_pos x).le _
        have h1 := mul_le_mul_of_nonneg_right (hE_bd x hx) hjb_neg_nn
        rwa [mul_assoc, ← Real.rpow_add (B0579.jb_pos x), add_neg_cancel,
          Real.rpow_zero, mul_one] at h1
      dsimp only [rem_R, majK]
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |Cyl.K p.c g x 1| * |B0579.pd 1 (etaCut R) x| * |E x|
          ≤ |Cyl.K p.c g x 1| * (C_B / R) * (C_E * B0579.jb x ^ (-(m / 2 + 1))) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hpd1_bd (abs_nonneg _)) hEx_bd
              (abs_nonneg _) (mul_nonneg (abs_nonneg _) (div_nonneg hCB hR0.le))
        _ = (C_B * C_E / R) * (|Cyl.K p.c g x 1| * B0579.jb x ^ (-(m / 2 + 1))) := by ring
    rw [hint_eq]
    calc ‖∫ x in B0579.cell p.c, rem_R x‖
        ≤ ∫ x in B0579.cell p.c, ‖rem_R x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x in B0579.cell p.c, (C_B * C_E / R) * majK x :=
          integral_mono_ae hint_rem.norm (hmajK_int.const_mul _) hpw
      _ = (C_B * C_E / R) * I_maj := integral_const_mul _ _
      _ = (C_B * C_E * I_maj) / R := by ring
  have htend_zero : Tendsto (fun R : ℝ => ∫ x in B0579.cell p.c, (Ac r g) x * etaCut R x)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_
      ((tendsto_const_nhds (x := C_B * C_E * I_maj)).div_atTop tendsto_id)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR1
    exact h_cut_bd R hR1
  have htend_lhs := tendsto_integral_mul_etaCut hint_Ac
  exact ⟨hint_Ac, tendsto_nhds_unique htend_lhs htend_zero⟩

end UnforcedLeray.Short.IIb.ZeroCircAux

/-- **Main theorem (`PartII-b:F2/2/2`, `FreeAndInteractionZeroCircStep`, SP 2076–2083, 2117–2123)**:
zero-circulation preservation of `Sc` and zero circulation of `Ac`. -/
theorem freeAndInteractionZeroCircStep_proof :
    UnforcedLeray.Short.IIb.FreeAndInteractionZeroCircStep := by
  intro m hm Sig hSig p d dm dp hbg hν1 hAge δ hδ0 hδ1 hTCM Sc hSc Ac hAc
  refine ⟨?_, ?_⟩
  · intro s t hs hst ht f hf
    exact UnforcedLeray.Short.IIb.ZeroCircAux.free_zero_circ
      hm hSig hbg hν1 hAge hδ0 hδ1 hTCM hSc hs hst ht f hf
  · intro r hr g
    exact UnforcedLeray.Short.IIb.ZeroCircAux.interaction_zero_circ
      hm hSig hbg hν1 hAge hδ0 hTCM hAc hr g

end
