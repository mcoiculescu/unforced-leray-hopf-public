import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Helper 3 for `PartII-b:F2/3/2` (`PeriodizedCylinderCoord`): Restricted dual approximation & 2×2 inverse

Source of record: `the November 2 reference manuscript`, lines 2167–2171.

Proves:
1. Uniform-in-`σ ∈ Icc 0 Sig` operator-norm convergence `‖(π_pl σ).comp (Jc c m ∘L Rc c m - id)‖ → 0`
   as `c → ∞` for any continuous family `π_pl : ℝ → (Xm m →L[ℝ] E2)`;
2. Quantitative Neumann-series left inverse `U` of `G : E2 →L[ℝ] E2` when `‖G - id‖ ≤ 1 / 2`,
   with `‖U‖ ≤ 2` and `‖U - id‖ ≤ 2 * ‖G - id‖`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.PeriodizedCylCoordAux

open UnforcedLeray.Short.IIb UnforcedLeray.Cons.C03.Concrete

lemma norm_Jc_le_one (c m : ℝ) : ‖Jc c m‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [norm_Jc_apply, one_mul]

lemma norm_Jc_comp_Rc_le_one (c m : ℝ) : ‖(Jc c m).comp (Rc c m)‖ ≤ 1 := by
  calc ‖(Jc c m).comp (Rc c m)‖
      ≤ ‖Jc c m‖ * ‖Rc c m‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul (norm_Jc_le_one c m) (norm_Rc_le c m) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma coeFn_Jc_Rc_sub_self (c m : ℝ) (k : Xm m) :
    ((((Jc c m).comp (Rc c m)) k - k : Xm m) : B0579.Plane → ℝ) =ᵐ[planeMeasure m]
      -((B0579.cell c)ᶜ.indicator (k : B0579.Plane → ℝ)) := by
  have hrc : (Rc c m k : B0579.Plane → ℝ) =ᵐ[(planeMeasure m).restrict (B0579.cell c)] k := by
    rw [← cellMeasure_eq_restrict_planeMeasure]
    exact coeFn_restrictCellFun c m k
  have hrc' : ∀ᵐ x ∂(planeMeasure m), x ∈ B0579.cell c → Rc c m k x = k x :=
    (ae_restrict_iff' (B0579.measurableSet_cell c)).mp hrc
  filter_upwards [Lp.coeFn_sub (((Jc c m).comp (Rc c m)) k) k,
    coeFn_zeroExtFun c m (Rc c m k), hrc'] with x hsub hjc hcell
  change (((Jc c m).comp (Rc c m)) k - k : Xm m) x =
    -((B0579.cell c)ᶜ.indicator (k : B0579.Plane → ℝ) x)
  rw [hsub, Pi.sub_apply]
  change Jc c m (Rc c m k) x - k x = _
  have hjc' : Jc c m (Rc c m k) x = (B0579.cell c).indicator (Rc c m k) x := hjc
  rw [hjc']
  by_cases hx : x ∈ B0579.cell c
  · simp [hx, hcell hx]
  · simp [hx]

lemma norm_Jc_Rc_sub_self_eq_compl (c m : ℝ) (k : Xm m) :
    ‖((Jc c m).comp (Rc c m)) k - k‖ =
      (eLpNorm ((B0579.cell c)ᶜ.indicator (k : B0579.Plane → ℝ)) 2 (planeMeasure m)).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_Jc_Rc_sub_self c m k), eLpNorm_neg]

lemma norm_Jc_Rc_sub_self_anti {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂) (m : ℝ) (k : Xm m) :
    ‖((Jc c₂ m).comp (Rc c₂ m)) k - k‖ ≤ ‖((Jc c₁ m).comp (Rc c₁ m)) k - k‖ := by
  rw [norm_Jc_Rc_sub_self_eq_compl, norm_Jc_Rc_sub_self_eq_compl]
  have hsub : B0579.cell c₁ ⊆ B0579.cell c₂ := by
    intro x hx
    exact ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩, trivial⟩
  have hle : eLpNorm ((B0579.cell c₂)ᶜ.indicator (k : B0579.Plane → ℝ)) 2 (planeMeasure m) ≤
      eLpNorm ((B0579.cell c₁)ᶜ.indicator (k : B0579.Plane → ℝ)) 2 (planeMeasure m) := by
    refine eLpNorm_mono fun x => ?_
    by_cases hx2 : x ∈ (B0579.cell c₂)ᶜ
    · have hx1 : x ∈ (B0579.cell c₁)ᶜ := fun h1 => hx2 (hsub h1)
      simp [hx1, hx2]
    · simp [hx2]
  have hfin : eLpNorm ((B0579.cell c₁)ᶜ.indicator (k : B0579.Plane → ℝ)) 2 (planeMeasure m) ≠ ⊤ := by
    have hle_k : eLpNorm ((B0579.cell c₁)ᶜ.indicator (k : B0579.Plane → ℝ)) 2 (planeMeasure m) ≤
        eLpNorm (k : B0579.Plane → ℝ) 2 (planeMeasure m) :=
      eLpNorm_mono fun x => norm_indicator_le_norm_self _ _
    exact (lt_of_le_of_lt hle_k (Lp.memLp k).2).ne
  exact ENNReal.toReal_mono hfin hle

lemma tendsto_norm_Jc_Rc_sub_self_nat (m : ℝ) (k : Xm m) :
    Tendsto (fun n : ℕ => ‖((Jc (n : ℝ) m).comp (Rc (n : ℝ) m)) k - k‖) atTop (𝓝 0) := by
  have hk : MemLp (k : B0579.Plane → ℝ) 2 (planeMeasure m) := Lp.memLp k
  set F : ℕ → B0579.Plane → ℝ≥0∞ := fun n x =>
    ‖(B0579.cell (n : ℝ))ᶜ.indicator (k : B0579.Plane → ℝ) x‖ₑ ^ (2 : ℝ)
  set bound : B0579.Plane → ℝ≥0∞ := fun x => ‖(k : B0579.Plane → ℝ) x‖ₑ ^ (2 : ℝ)
  have hF_meas : ∀ n : ℕ, AEMeasurable (F n) (planeMeasure m) := fun n =>
    ((hk.1.indicator (B0579.measurableSet_cell (n : ℝ)).compl).enorm).pow_const (2 : ℝ)
  have h_bound : ∀ n : ℕ, F n ≤ᵐ[planeMeasure m] bound := fun n =>
    Eventually.of_forall fun x =>
      ENNReal.rpow_le_rpow (enorm_le_iff_norm_le.mpr (norm_indicator_le_norm_self _ _))
        (by norm_num)
  have h_fin : ∫⁻ x, bound x ∂(planeMeasure m) ≠ ⊤ := by
    have heq := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := planeMeasure m)
      (f := (k : B0579.Plane → ℝ)) (p := 2) (by norm_num) (by norm_num)
    simp only [ENNReal.toReal_ofNat, one_div] at heq
    intro htop
    have hk_ne : eLpNorm (k : B0579.Plane → ℝ) 2 (planeMeasure m) ≠ ⊤ := hk.2.ne
    rw [heq] at hk_ne
    change (∫⁻ x, bound x ∂(planeMeasure m)) ^ (2 : ℝ)⁻¹ ≠ ⊤ at hk_ne
    rw [htop, ENNReal.top_rpow_of_pos (by positivity)] at hk_ne
    exact hk_ne rfl
  have h_lim : ∀ᵐ x ∂(planeMeasure m), Tendsto (fun n : ℕ => F n x) atTop (𝓝 0) := by
    refine Eventually.of_forall fun x => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * |x.1|)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [ eventually_ge_atTop N ] with n hn
    have hnr : 2 * |x.1| < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hn)
    have habs : |x.1| < (n : ℝ) / 2 := by linarith
    obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
    have hmem : x ∈ B0579.cell (n : ℝ) := ⟨⟨by linarith, hhi⟩, trivial⟩
    have hnot : x ∉ (B0579.cell (n : ℝ))ᶜ := fun hc => hc hmem
    dsimp [F]
    rw [indicator_of_notMem hnot, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
  have hlint := tendsto_lintegral_of_dominated_convergence' bound hF_meas h_bound h_fin h_lim
  simp only [lintegral_zero] at hlint
  have hrpow : Tendsto (fun t : ℝ≥0∞ => t ^ (1 / 2 : ℝ)) (𝓝 0) (𝓝 0) := by
    have h := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  have htoReal : Tendsto (fun t : ℝ≥0∞ => (t ^ (1 / 2 : ℝ)).toReal) (𝓝 0) (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hrpow
    rwa [ENNReal.toReal_zero] at h
  refine (htoReal.comp hlint).congr fun n => ?_
  dsimp only [Function.comp_apply]
  rw [norm_Jc_Rc_sub_self_eq_compl,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  rfl

lemma norm_adjoint_apply_sub_sq_le_of_contraction {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] (W : X →L[ℝ] X) (hW : ‖W‖ ≤ 1) (k : X) :
    ‖ContinuousLinearMap.adjoint W k - k‖ ^ 2 ≤ 2 * ‖k‖ * ‖W k - k‖ := by
  have h1 := norm_sub_sq_real (ContinuousLinearMap.adjoint W k) k
  have h2 : inner ℝ (ContinuousLinearMap.adjoint W k) k = inner ℝ k (W k) :=
    ContinuousLinearMap.adjoint_inner_left W k k
  have h3 : ‖ContinuousLinearMap.adjoint W k‖ ≤ ‖k‖ := by
    calc ‖ContinuousLinearMap.adjoint W k‖
        ≤ ‖ContinuousLinearMap.adjoint W‖ * ‖k‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖W‖ * ‖k‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ 1 * ‖k‖ := mul_le_mul_of_nonneg_right hW (norm_nonneg _)
      _ = ‖k‖ := one_mul _
  have h4 : inner ℝ k (W k) = ‖k‖ ^ 2 + inner ℝ k (W k - k) := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq]; ring
  have h5 : |inner ℝ k (W k - k)| ≤ ‖k‖ * ‖W k - k‖ := abs_real_inner_le_norm _ _
  have h6 : ‖ContinuousLinearMap.adjoint W k‖ ^ 2 ≤ ‖k‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h3 2
  have h7 := neg_abs_le (inner ℝ k (W k - k))
  rw [h1, h2, h4]
  nlinarith [h5, h6, h7]

/-- Uniform-in-`σ ∈ Icc 0 Sig` operator-norm approximation of `π_pl σ` by `(π_pl σ) ∘ Jc ∘ Rc`. -/
theorem exists_c_norm_comp_Jc_Rc_sub_id_le {m Sig : ℝ}
    (π_pl : ℝ → (Xm m →L[ℝ] E2)) (hπ_cont : ContinuousOn π_pl (Icc 0 Sig))
    {η : ℝ} (hη : 0 < η) :
    ∃ c₁ : ℝ, 1 ≤ c₁ ∧ ∀ c : ℝ, c₁ ≤ c → ∀ σ ∈ Icc 0 Sig,
      ‖(π_pl σ).comp ((Jc c m).comp (Rc c m) - ContinuousLinearMap.id ℝ (Xm m))‖ ≤ η := by
  set K : Set (Xm m) :=
    (fun z : ℝ × E2 => ContinuousLinearMap.adjoint (π_pl z.1) z.2) ''
      (Icc 0 Sig ×ˢ closedBall (0 : E2) 1)
  have hπ_adj_cont : ContinuousOn (fun σ => ContinuousLinearMap.adjoint (π_pl σ)) (Icc 0 Sig) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Xm m) (F := E2)).continuous.comp_continuousOn
      hπ_cont
  have hK : IsCompact K := by
    refine (isCompact_Icc.prod (isCompact_closedBall (0 : E2) 1)).image_of_continuousOn ?_
    exact (hπ_adj_cont.comp continuousOn_fst (fun z hz => hz.1)).clm_apply continuousOn_snd
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall (0 : Xm m)
  set B : ℝ := max 1 R
  have hB_pos : 0 < B := lt_of_lt_of_le one_pos (le_max_left 1 R)
  have hK_norm : ∀ k ∈ K, ‖k‖ ≤ B := fun k hk => by
    have hmem := hKR hk
    rw [mem_closedBall_zero_iff] at hmem
    exact hmem.trans (le_max_right 1 R)
  set δ : ℝ := η ^ 2 / (2 * B)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨t, ht_cov⟩ := hK.elim_finite_subcover (fun k₀ : Xm m => ball k₀ (δ / 4))
    (fun _ => isOpen_ball)
    (fun k _ => mem_iUnion.mpr ⟨k, mem_ball_self (by linarith)⟩)
  have hex_N : ∀ k₀ : Xm m, ∃ n : ℕ,
      ‖((Jc (n : ℝ) m).comp (Rc (n : ℝ) m)) k₀ - k₀‖ < δ / 2 := fun k₀ => by
    have hev := (tendsto_norm_Jc_Rc_sub_self_nat m k₀).eventually (gt_mem_nhds (half_pos hδ))
    exact hev.exists
  choose N_of hN_of using hex_N
  set N_max : ℕ := t.sup N_of
  set c₁ : ℝ := max 1 (N_max : ℝ)
  refine ⟨c₁, le_max_left _ _, fun c hc σ hσ => ?_⟩
  set Pc : Xm m →L[ℝ] Xm m := (Jc c m).comp (Rc c m)
  have hPc_le : ‖Pc‖ ≤ 1 := norm_Jc_comp_Rc_le_one c m
  have hK_small : ∀ k ∈ K, ‖Pc k - k‖ ≤ δ := fun k hk => by
    have hk_u := ht_cov hk
    rw [mem_iUnion₂] at hk_u
    obtain ⟨k₀, hk₀_t, hk_ball⟩ := hk_u
    rw [mem_ball, dist_eq_norm] at hk_ball
    have hNk₀_le_c : (N_of k₀ : ℝ) ≤ c := by
      have h1 : N_of k₀ ≤ N_max := Finset.le_sup hk₀_t
      have h2 : (N_of k₀ : ℝ) ≤ (N_max : ℝ) := by exact_mod_cast h1
      exact h2.trans ((le_max_right 1 (N_max : ℝ)).trans hc)
    have h_at_c : ‖Pc k₀ - k₀‖ ≤ δ / 2 :=
      (norm_Jc_Rc_sub_self_anti hNk₀_le_c m k₀).trans (hN_of k₀).le
    have h_lip : ‖(Pc k - k) - (Pc k₀ - k₀)‖ ≤ 2 * ‖k - k₀‖ := by
      have heq : (Pc k - k) - (Pc k₀ - k₀) = Pc (k - k₀) - (k - k₀) := by
        rw [map_sub]; abel
      rw [heq]
      calc ‖Pc (k - k₀) - (k - k₀)‖
          ≤ ‖Pc (k - k₀)‖ + ‖k - k₀‖ := norm_sub_le _ _
        _ ≤ ‖Pc‖ * ‖k - k₀‖ + ‖k - k₀‖ :=
            add_le_add (ContinuousLinearMap.le_opNorm Pc (k - k₀)) le_rfl
        _ ≤ 1 * ‖k - k₀‖ + ‖k - k₀‖ :=
            add_le_add (mul_le_mul_of_nonneg_right hPc_le (norm_nonneg _)) le_rfl
        _ = 2 * ‖k - k₀‖ := by ring
    have htri : ‖Pc k - k‖ ≤ ‖(Pc k - k) - (Pc k₀ - k₀)‖ + ‖Pc k₀ - k₀‖ := by
      simpa using norm_add_le ((Pc k - k) - (Pc k₀ - k₀)) (Pc k₀ - k₀)
    linarith
  have hadj : ‖(π_pl σ).comp (Pc - ContinuousLinearMap.id ℝ (Xm m))‖ =
      ‖ContinuousLinearMap.adjoint ((π_pl σ).comp (Pc - ContinuousLinearMap.id ℝ (Xm m)))‖ :=
    (LinearIsometryEquiv.norm_map _ _).symm
  rw [hadj, ContinuousLinearMap.adjoint_comp, map_sub, ContinuousLinearMap.adjoint_id]
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hη.le fun α hα => ?_
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.id_apply]
  set k : Xm m := ContinuousLinearMap.adjoint (π_pl σ) α
  have hk_mem : k ∈ K := ⟨(σ, α), ⟨hσ, mem_closedBall_zero_iff.mpr hα.le⟩, rfl⟩
  have hsq := norm_adjoint_apply_sub_sq_le_of_contraction Pc hPc_le k
  have hsq_le : ‖ContinuousLinearMap.adjoint Pc k - k‖ ^ 2 ≤ η ^ 2 := by
    calc ‖ContinuousLinearMap.adjoint Pc k - k‖ ^ 2
        ≤ 2 * ‖k‖ * ‖Pc k - k‖ := hsq
      _ ≤ 2 * B * δ := by
          have h1 : 2 * ‖k‖ ≤ 2 * B := by linarith [hK_norm k hk_mem]
          exact mul_le_mul h1 (hK_small k hk_mem) (norm_nonneg _) (by positivity)
      _ = η ^ 2 := by dsimp [δ]; field_simp [hB_pos.ne']
  nlinarith [norm_nonneg (ContinuousLinearMap.adjoint Pc k - k),
    sq_nonneg (‖ContinuousLinearMap.adjoint Pc k - k‖ - η)]

/-- Quantitative 2×2 left inverse near the identity on `E2`. -/
theorem invertible_e2_of_sub_id_le {G : E2 →L[ℝ] E2}
    (hG : ‖G - ContinuousLinearMap.id ℝ E2‖ ≤ 1 / 2) :
    ∃ U : E2 →L[ℝ] E2,
      U.comp G = ContinuousLinearMap.id ℝ E2 ∧
      ‖U‖ ≤ 2 ∧
      ‖U - ContinuousLinearMap.id ℝ E2‖ ≤ 2 * ‖G - ContinuousLinearMap.id ℝ E2‖ := by
  have hdiff : ‖G - (1 : E2 →L[ℝ] E2)‖ ≤ (2 * (1 : ℝ))⁻¹ := by
    rw [ContinuousLinearMap.one_def, mul_one, ← one_div]
    exact hG
  obtain ⟨U, hUG, _, hUnorm⟩ := invertible_two_by_two_of_close
    (a_pl := (1 : E2 →L[ℝ] E2)) (ainv_pl := (1 : E2 →L[ℝ] E2)) (a_n := G) (M := 1)
    one_pos (mul_one 1) (mul_one 1) ContinuousLinearMap.norm_id_le hdiff
  refine ⟨U, hUG, by linarith, ?_⟩
  have hsub : U - (1 : E2 →L[ℝ] E2) = U * ((1 : E2 →L[ℝ] E2) - G) := by
    rw [mul_sub, mul_one, hUG]
  change ‖U - (1 : E2 →L[ℝ] E2)‖ ≤ 2 * ‖G - (1 : E2 →L[ℝ] E2)‖
  rw [hsub]
  calc ‖U * ((1 : E2 →L[ℝ] E2) - G)‖
      ≤ ‖U‖ * ‖(1 : E2 →L[ℝ] E2) - G‖ := norm_mul_le _ _
    _ = ‖U‖ * ‖G - (1 : E2 →L[ℝ] E2)‖ := by rw [norm_sub_rev]
    _ ≤ 2 * ‖G - (1 : E2 →L[ℝ] E2)‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

end UnforcedLeray.Short.IIb.PeriodizedCylCoordAux
