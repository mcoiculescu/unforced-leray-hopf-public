import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_2_3_2_3_1
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity3.LeafB
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.TailContinuation.TailEnergyBound

/-!
# `PartIII-a:T19/2/3/2/3/1/2`: `CoreDuhamelDensity` (SP 3427-3440, 3481-3496, 3518-3527)

Source of record: `the November 2 reference manuscript` (SP), lines 3427-3440,
3481-3496, and 3518-3527.

Proves `coreDuhamelDensity_proof : UnforcedLeray.Short.IIIa.CoreDuhamelDensity`:
1. `freeCausalEnergyBound` and `causalSolSub` yield geometric convergence (`O(2^{-n})`) in
   `hCalNorm` and `tCalNorm` for both `b₀n n - b₀`, `G₀n n - G₀` and consecutive differences
   `b₀n (n + 1) - b₀n n`, `G₀n (n + 1) - G₀n n`.
2. `coreSourceNegBound` (`C_dual = 8`), weighted AM-GM (`a_n(t) = 2^{-n} t^a`), and Tonelli with
   `∫_t^H (1 + (s - t)^{-1/2}) ds ≤ H + 2 √H` imply that `ks (n + 1) t - ks n t` is summable in
   `L¹((0, s); X_{9,c})` for a.e. `s ∈ (0, H)`.
3. A jointly measurable telescoping limit `k` in `X_{9,c}^0` is constructed on the measurable
   convergence set `{p | ∑' n, ‖ks (n + 1) p.1 p.2 - ks n p.1 p.2‖ₑ < ⊤}`, satisfying the
   weak-source clock bound at `(b₀, G₀)` and `L²(cell c)` convergence of `∫_0^s ks n t · dt` to
   `∫_0^s k t · dt`.
4. `trainAdvectionEnergyIdentity` tested with `exp(-2 M_L s) rampPsi δ H s` on `(0, 2H)` gives
   geometric convergence of `G_sol_n n - G_sol` on `(0, H)`, identifying `corePerturbVort` at
   `(G₀, G_sol)` with `fun x => ∫ t in Ioo 0 s, k t x` for a.e. `s ∈ (0, H)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped NNReal ENNReal ContDiff

namespace CoreDuhamelDensityAux

open UnforcedLeray.Short.IIIa

/-! ## 1. Elementary `ℝ≥0∞` series and AM-GM helpers -/

private theorem ennreal_le_sq_div_add {x a : ℝ≥0∞} (ha0 : a ≠ 0) (hat : a ≠ ⊤) :
    x ≤ x ^ 2 * a⁻¹ + a := by
  rcases le_total x a with hxa | hax
  · exact hxa.trans le_add_self
  · calc x = x * 1 := (mul_one x).symm
      _ = x * (a * a⁻¹) := by rw [ENNReal.mul_inv_cancel ha0 hat]
      _ = x * a * a⁻¹ := by ring
      _ ≤ x * x * a⁻¹ := by gcongr
      _ = x ^ 2 * a⁻¹ := by rw [sq]
      _ ≤ x ^ 2 * a⁻¹ + a := le_self_add

private theorem ennreal_tsum_nat_add_tendsto_zero {f : ℕ → ℝ≥0∞} (hf : ∑' n, f n ≠ ⊤) :
    Tendsto (fun N : ℕ => ∑' m : ℕ, f (N + m)) atTop (𝓝 0) := by
  have hne : ∀ n, f n ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top hf
  have hg : Summable fun n : ℕ => (f n).toReal := ENNReal.summable_toReal hf
  have hlim := ENNReal.tendsto_ofReal (tendsto_sum_nat_add fun n : ℕ => (f n).toReal)
  rw [ENNReal.ofReal_zero] at hlim
  refine hlim.congr fun N => ?_
  rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => ENNReal.toReal_nonneg)
    ((summable_nat_add_iff N).2 hg)]
  refine tsum_congr fun m => ?_
  rw [Nat.add_comm m N, ENNReal.ofReal_toReal (hne (N + m))]

private theorem tsum_ofReal_half_pow_lt_top :
    (∑' n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) < ⊤ := by
  have heq : ∀ n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ n) = (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n
    rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos zero_lt_two,
      ENNReal.ofReal_ofNat]
  simp_rw [heq]
  rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.ofNat_lt_top

private theorem tsum_ofReal_quarter_pow_lt_top :
    (∑' n : ℕ, ENNReal.ofReal ((1 / 4 : ℝ) ^ n)) < ⊤ := by
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun n => ?_) tsum_ofReal_half_pow_lt_top
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by norm_num) (by norm_num) n)

/-! ## 2. Curl duality at `C_dual = 8` and subadditivity of `coreSrcNorm` -/

private theorem cDualClause_eight : CDualClause 8 :=
  fun _ _ hc hAm _ hv hv_bd _ _ hu hG =>
    ⟨advStretch_weighted_l2_bound hc hAm hv hv_bd hu hG,
      negNorm_le_of_advStretch_pairing hc hAm hv hv_bd hu hG⟩

private theorem coreSrcNorm_le_add_diff {ν b A_m γ : ℝ} (hν : 0 < ν) (hAm : 0 ≤ A_m)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hbd : ∀ s ∈ Ioc (0 : ℝ) (coreEnd ν b), ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      B0579.bracket x ^ (9 : ℝ) * (‖tr.v s x‖ + ‖fderiv ℝ (tr.v s) x‖) ≤ A_m)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (coreEnd ν b))
    {b₁ b₂ : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G₁ G₂ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hb₁m : ∀ i, Measurable fun p => b₁ p i) (hG₁m : ∀ i j, Measurable fun p => G₁ p i j)
    (hb₂m : ∀ i, Measurable fun p => b₂ p i) (hG₂m : ∀ i j, Measurable fun p => G₂ p i j)
    (hb₁_lp : ∀ i, MemLp (fun x => gainConj γ ν b₁ (t, x) i) 2
      (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))))
    (hG₁_lp : ∀ i j, MemLp (fun x => gainConj γ ν G₁ (t, x) i j) 2
      (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))))
    (hb₂_lp : ∀ i, MemLp (fun x => gainConj γ ν b₂ (t, x) i) 2
      (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))))
    (hG₂_lp : ∀ i j, MemLp (fun x => gainConj γ ν G₂ (t, x) i j) 2
      (volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))) :
    coreSrcNorm (ν ^ (-2 : ℝ)) 9 (coreAdvSlice γ tr b₁ G₁ t) ≤
      coreSrcNorm (ν ^ (-2 : ℝ)) 9 (coreAdvSlice γ tr b₂ G₂ t) +
        coreSrcNorm (ν ^ (-2 : ℝ)) 9
          (coreAdvSlice γ tr (fun p i => b₁ p i - b₂ p i)
            (fun p i j => G₁ p i j - G₂ p i j) t) := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  have hv := contDiff_trainVel tr ht.1
  have hv_bd := CoreDuhamelRepSub.trainVel_weighted_bound hbd ⟨ht.1, ht.2.le⟩
  have hu₂ : ∀ i, Measurable fun x : ℝ × ℝ => gainConj γ ν b₂ (t, x) i := by
    intro i; simp only [gainConj, Pi.smul_apply]
    exact ((hb₂m i).comp measurable_prodMk_left).const_smul _
  have hG₂ : ∀ i j, Measurable fun x : ℝ × ℝ => gainConj γ ν G₂ (t, x) i j := by
    intro i j; simp only [gainConj, Pi.smul_apply]
    exact ((hG₂m i j).comp measurable_prodMk_left).const_smul _
  let bd : ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun p i => b₁ p i - b₂ p i
  let Gd : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun p i j => G₁ p i j - G₂ p i j
  have hud : ∀ i, Measurable fun x : ℝ × ℝ => gainConj γ ν bd (t, x) i := by
    intro i; simp only [bd, gainConj, Pi.smul_apply]
    exact (((hb₁m i).sub (hb₂m i)).comp measurable_prodMk_left).const_smul _
  have hGd : ∀ i j, Measurable fun x : ℝ × ℝ => gainConj γ ν Gd (t, x) i j := by
    intro i j; simp only [Gd, gainConj, Pi.smul_apply]
    exact (((hG₁m i j).sub (hG₂m i j)).comp measurable_prodMk_left).const_smul _
  have hbd_lp : ∀ i, MemLp (fun x => gainConj γ ν bd (t, x) i) 2 (volume.restrict (B0579.cell c)) := by
    intro i
    have heq : (fun x => gainConj γ ν bd (t, x) i) =
        fun x => gainConj γ ν b₁ (t, x) i - gainConj γ ν b₂ (t, x) i := by
      funext x; simp [bd, gainConj, smul_sub]
    rw [heq]
    exact (hb₁_lp i).sub (hb₂_lp i)
  have hGd_lp : ∀ i j, MemLp (fun x => gainConj γ ν Gd (t, x) i j) 2
      (volume.restrict (B0579.cell c)) := by
    intro i j
    have heq : (fun x => gainConj γ ν Gd (t, x) i j) =
        fun x => gainConj γ ν G₁ (t, x) i j - gainConj γ ν G₂ (t, x) i j := by
      funext x; simp [Gd, gainConj, smul_sub]
    rw [heq]
    exact (hG₁_lp i j).sub (hG₂_lp i j)
  refine iSup₂_le fun φ g => iSup₂_le fun hg hh1 => ?_
  have Ia₂ : IntegrableOn
      (fun x => coreAdvSlice γ tr b₂ G₂ t x 1 * g 0 x - coreAdvSlice γ tr b₂ G₂ t x 0 * g 1 x)
      (B0579.cell c) :=
    CoreDuhamelRepSub.integrableOn_coreSrc_of_slice hc hAm hv hv_bd hu₂ hG₂ hb₂_lp hG₂_lp hg hh1
  have Iad : IntegrableOn
      (fun x => coreAdvSlice γ tr bd Gd t x 1 * g 0 x - coreAdvSlice γ tr bd Gd t x 0 * g 1 x)
      (B0579.cell c) :=
    CoreDuhamelRepSub.integrableOn_coreSrc_of_slice hc hAm hv hv_bd hud hGd hbd_lp hGd_lp hg hh1
  have hfun_eq : coreSrcFun c (coreAdvSlice γ tr b₁ G₁ t) g =
      coreSrcFun c (coreAdvSlice γ tr b₂ G₂ t) g + coreSrcFun c (coreAdvSlice γ tr bd Gd t) g := by
    unfold coreSrcFun
    rw [← integral_add Ia₂ Iad]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have h0 := CoreDuhamelRepSub.coreAdvSlice_sub γ tr b₁ b₂ G₁ G₂ t x 0
    have h1 := CoreDuhamelRepSub.coreAdvSlice_sub γ tr b₁ b₂ G₁ G₂ t x 1
    dsimp [bd, Gd] at h0 h1 ⊢
    rw [h0, h1]
    ring
  rw [hfun_eq]
  calc ENNReal.ofReal ‖coreSrcFun c (coreAdvSlice γ tr b₂ G₂ t) g +
          coreSrcFun c (coreAdvSlice γ tr bd Gd t) g‖
      ≤ ENNReal.ofReal (‖coreSrcFun c (coreAdvSlice γ tr b₂ G₂ t) g‖ +
          ‖coreSrcFun c (coreAdvSlice γ tr bd Gd t) g‖) :=
        ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ = ENNReal.ofReal ‖coreSrcFun c (coreAdvSlice γ tr b₂ G₂ t) g‖ +
          ENNReal.ofReal ‖coreSrcFun c (coreAdvSlice γ tr bd Gd t) g‖ :=
        ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
    _ ≤ coreSrcNorm c 9 (coreAdvSlice γ tr b₂ G₂ t) +
          coreSrcNorm c 9 (coreAdvSlice γ tr bd Gd t) := by
        refine add_le_add ?_ ?_
        · exact le_iSup₂_of_le φ g (le_iSup₂_of_le hg hh1 le_rfl)
        · exact le_iSup₂_of_le φ g (le_iSup₂_of_le hg hh1 le_rfl)

/-! ## 3. Weighted AM-GM and Hardy-Tonelli `L¹(0, H)` bounds for Duhamel source differences -/

private theorem lintegral_rpow_neg_half_le {H : ℝ} (hH : 0 < H) :
    ∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) ≤ ENNReal.ofReal (2 * Real.sqrt H) := by
  refine (lintegral_mono_set Ioo_subset_Ioc_self).trans ?_
  have hint : IntervalIntegrable (fun s : ℝ => s ^ (-1 / 2 : ℝ)) volume 0 H :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hnn : ∀ s ∈ Ioc (0 : ℝ) H, 0 ≤ s ^ (-1 / 2 : ℝ) := fun s hs =>
    Real.rpow_nonneg hs.1.le _
  have hint_on : IntegrableOn (fun s : ℝ => s ^ (-1 / 2 : ℝ)) (Ioc 0 H) volume := by
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hH.le] at hint
  rw [← ofReal_integral_eq_lintegral_ofReal hint_on (ae_restrict_of_forall_mem measurableSet_Ioc hnn)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← intervalIntegral.integral_of_le hH.le,
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))]
  have h0 : (0 : ℝ) ^ ((-1 / 2 : ℝ) + 1) = 0 := by
    rw [Real.zero_rpow (by norm_num)]
  rw [h0, sub_zero, show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
  ring_nf
  exact le_rfl

private theorem lintegral_kernel_s_le {H t : ℝ} (hH : 0 < H) (ht : t ∈ Ioo (0 : ℝ) H) :
    ∫⁻ s in Ioo t H, ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) ≤
      ENNReal.ofReal (H + 2 * Real.sqrt H) := by
  have hsub : ∫⁻ s in Ioo t H, ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) =
      ∫⁻ u in Ioo (0 : ℝ) (H - t), ENNReal.ofReal (1 + u ^ (-1 / 2 : ℝ)) := by
    have hmp : MeasurePreserving (fun u : ℝ => u + t) volume volume :=
      measurePreserving_add_right volume t
    rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo]
    have hm_ind : Measurable
        ((Ioo t H).indicator (fun s : ℝ => ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)))) :=
      (ENNReal.measurable_ofReal.comp
        (measurable_const.add ((measurable_id.sub_const t).pow_const _))).indicator measurableSet_Ioo
    rw [← hmp.lintegral_comp hm_ind]
    refine lintegral_congr fun u => ?_
    by_cases hu : u ∈ Ioo (0 : ℝ) (H - t)
    · have hut : u + t ∈ Ioo t H := ⟨by linarith [hu.1], by linarith [hu.2]⟩
      simp [hu, hut]
    · have hut : u + t ∉ Ioo t H := fun h => hu ⟨by linarith [h.1], by linarith [h.2]⟩
      simp [hu, hut]
  rw [hsub]
  have hmono : ∫⁻ u in Ioo (0 : ℝ) (H - t), ENNReal.ofReal (1 + u ^ (-1 / 2 : ℝ)) ≤
      ∫⁻ u in Ioo (0 : ℝ) H, ENNReal.ofReal (1 + u ^ (-1 / 2 : ℝ)) :=
    lintegral_mono_set (Ioo_subset_Ioo le_rfl (by linarith [ht.1]))
  refine hmono.trans ?_
  have hadd : ∀ u ∈ Ioo (0 : ℝ) H, ENNReal.ofReal (1 + u ^ (-1 / 2 : ℝ)) =
      1 + ENNReal.ofReal (u ^ (-1 / 2 : ℝ)) := fun u hu => by
    rw [ENNReal.ofReal_add zero_le_one (Real.rpow_nonneg hu.1.le _), ENNReal.ofReal_one]
  rw [setLIntegral_congr_fun measurableSet_Ioo hadd,
    lintegral_add_left measurable_const, setLIntegral_const, Real.volume_Ioo, sub_zero, one_mul]
  exact (add_le_add le_rfl (lintegral_rpow_neg_half_le hH)).trans_eq
    (ENNReal.ofReal_add hH.le (by positivity)).symm

private theorem weighted_sliceVel_sq_le {c H : ℝ} (hc : 0 < c)
    {u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} (hu : ∀ i, Measurable fun p => u p i) :
    ∫⁻ t in Ioo (0 : ℝ) H,
        ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * unnormSliceVel c u t ^ 2 ≤
      ENNReal.ofReal c * hCalNorm c u ^ (2 : ℝ) := by
  have hm_u : Measurable fun p : ℝ × (ℝ × ℝ) => vnorm2 (u p) ^ 2 :=
    (causalLin_measurable_vnorm2 hu).pow_const 2
  have hm_vel : Measurable (unnormSliceVel c u) := measurable_unnormSliceVel c hu
  have h1 : ∫⁻ p in Iio H ×ˢ (univ : Set (ℝ × ℝ)),
      ENNReal.ofReal (vnorm2 (u p) ^ 2) ∂(ageμ c (-3 / 2)) ≤
      hCalNorm c u ^ (2 : ℝ) := by
    have heq := eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (f := fun p => vnorm2 (u p)) (μ := ageμ c (-3 / 2))
    have hpow : hCalNorm c u ^ (2 : ℝ) =
        ∫⁻ p, ENNReal.ofReal (vnorm2 (u p) ^ 2) ∂(ageμ c (-3 / 2)) := by
      rw [hCalNorm, heq, ← ENNReal.rpow_mul]
      norm_num
      refine lintegral_congr fun p => ?_
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    rw [hpow]
    exact setLIntegral_le_lintegral _ _
  rw [lintegral_Iio_ageμ_eq hc _ hm_u] at h1
  have hm_int : Measurable fun s : ℝ =>
      ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * unnormSliceVel c u s ^ 2 :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul (hm_vel.pow_const 2)
  have heq_int : ENNReal.ofReal c⁻¹ * ∫⁻ s in Ioo (0 : ℝ) H,
      ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * unnormSliceVel c u s ^ 2 =
      ∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
        (ENNReal.ofReal c⁻¹ *
          ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u (s, x)) ^ 2)) := by
    rw [← lintegral_const_mul _ hm_int]
    refine setLIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
    have hsq : unnormSliceVel c u s ^ 2 =
        ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u (s, x)) ^ 2) := by
      unfold unnormSliceVel
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    rw [hsq]
    ring
  have h2 : ENNReal.ofReal c⁻¹ * ∫⁻ s in Ioo (0 : ℝ) H,
      ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * unnormSliceVel c u s ^ 2 ≤ hCalNorm c u ^ (2 : ℝ) :=
    heq_int.trans_le h1
  calc ∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * unnormSliceVel c u s ^ 2
      = (ENNReal.ofReal c * ENNReal.ofReal c⁻¹) * ∫⁻ s in Ioo (0 : ℝ) H,
          ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * unnormSliceVel c u s ^ 2 := by
        rw [← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one, one_mul]
    _ = ENNReal.ofReal c * (ENNReal.ofReal c⁻¹ * ∫⁻ s in Ioo (0 : ℝ) H,
          ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * unnormSliceVel c u s ^ 2) := mul_assoc _ _ _
    _ ≤ ENNReal.ofReal c * hCalNorm c u ^ (2 : ℝ) := mul_le_mul_of_nonneg_left h2 bot_le

private theorem weighted_sliceGrad_sq_le {c H : ℝ} (hc : 0 < c)
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} (hG : ∀ i j, Measurable fun p => G p i j) :
    ∫⁻ t in Ioo (0 : ℝ) H,
        ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * unnormSliceGrad c G t ^ 2 ≤
      ENNReal.ofReal c * tCalNorm c G ^ (2 : ℝ) := by
  have hm_G : Measurable fun p : ℝ × (ℝ × ℝ) => tnorm2 (G p) ^ 2 :=
    (causalLin_measurable_tnorm2 hG).pow_const 2
  have hm_grad : Measurable (unnormSliceGrad c G) := measurable_unnormSliceGrad c hG
  have h1 : ∫⁻ p in Iio H ×ˢ (univ : Set (ℝ × ℝ)),
      ENNReal.ofReal (tnorm2 (G p) ^ 2) ∂(ageμ c (-1 / 2)) ≤
      tCalNorm c G ^ (2 : ℝ) := by
    have heq := eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (f := fun p => tnorm2 (G p)) (μ := ageμ c (-1 / 2))
    have hpow : tCalNorm c G ^ (2 : ℝ) =
        ∫⁻ p, ENNReal.ofReal (tnorm2 (G p) ^ 2) ∂(ageμ c (-1 / 2)) := by
      rw [tCalNorm, heq, ← ENNReal.rpow_mul]
      norm_num
      refine lintegral_congr fun p => ?_
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    rw [hpow]
    exact setLIntegral_le_lintegral _ _
  rw [lintegral_Iio_ageμ_eq hc _ hm_G] at h1
  have hm_int : Measurable fun s : ℝ =>
      ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * unnormSliceGrad c G s ^ 2 :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul (hm_grad.pow_const 2)
  have heq_int : ENNReal.ofReal c⁻¹ * ∫⁻ s in Ioo (0 : ℝ) H,
      ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * unnormSliceGrad c G s ^ 2 =
      ∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
        (ENNReal.ofReal c⁻¹ *
          ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G (s, x)) ^ 2)) := by
    rw [← lintegral_const_mul _ hm_int]
    refine setLIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
    have hsq : unnormSliceGrad c G s ^ 2 =
        ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G (s, x)) ^ 2) := by
      unfold unnormSliceGrad
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    rw [hsq]
    ring
  have h2 : ENNReal.ofReal c⁻¹ * ∫⁻ s in Ioo (0 : ℝ) H,
      ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * unnormSliceGrad c G s ^ 2 ≤ tCalNorm c G ^ (2 : ℝ) :=
    heq_int.trans_le h1
  calc ∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * unnormSliceGrad c G s ^ 2
      = (ENNReal.ofReal c * ENNReal.ofReal c⁻¹) * ∫⁻ s in Ioo (0 : ℝ) H,
          ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * unnormSliceGrad c G s ^ 2 := by
        rw [← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one, one_mul]
    _ = ENNReal.ofReal c * (ENNReal.ofReal c⁻¹ * ∫⁻ s in Ioo (0 : ℝ) H,
          ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * unnormSliceGrad c G s ^ 2) := mul_assoc _ _ _
    _ ≤ ENNReal.ofReal c * tCalNorm c G ^ (2 : ℝ) := mul_le_mul_of_nonneg_left h2 bot_le

private theorem lintegral_sliceVel_le_of_hCalNorm {c H B r : ℝ} (hc : 0 < c) (hH : 0 < H)
    (hB : 0 ≤ B) (hr : 0 < r)
    {u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} (hu : ∀ i, Measurable fun p => u p i)
    (hnorm : hCalNorm c u ≤ ENNReal.ofReal B * ENNReal.ofReal r) :
    ∫⁻ t in Ioo (0 : ℝ) H, unnormSliceVel c u t ≤
      ENNReal.ofReal ((c * B ^ 2 + H * H ^ (3 / 2 : ℝ)) * r) := by
  have hm_vel : Measurable (unnormSliceVel c u) := measurable_unnormSliceVel c hu
  have hm1 : Measurable fun t : ℝ =>
      ENNReal.ofReal r⁻¹ * (ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * unnormSliceVel c u t ^ 2) :=
    measurable_const.mul ((ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul
      (hm_vel.pow_const 2))
  have hpt : ∀ t ∈ Ioo (0 : ℝ) H,
      unnormSliceVel c u t ≤
        ENNReal.ofReal r⁻¹ * (ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * unnormSliceVel c u t ^ 2) +
          ENNReal.ofReal (r * t ^ (3 / 2 : ℝ)) := by
    intro t ht
    have ht_pos : 0 < t ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos ht.1 _
    have ha_pos : 0 < r * t ^ (3 / 2 : ℝ) := mul_pos hr ht_pos
    have ha0 : ENNReal.ofReal (r * t ^ (3 / 2 : ℝ)) ≠ 0 := ENNReal.ofReal_pos.2 ha_pos |>.ne'
    have hat : ENNReal.ofReal (r * t ^ (3 / 2 : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hinv : (ENNReal.ofReal (r * t ^ (3 / 2 : ℝ)))⁻¹ =
        ENNReal.ofReal r⁻¹ * ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) := by
      rw [← ENNReal.ofReal_inv_of_pos ha_pos, mul_inv,
        ENNReal.ofReal_mul (inv_nonneg.2 hr.le), ← Real.rpow_neg ht.1.le]
      norm_num
    refine (ennreal_le_sq_div_add ha0 hat).trans_eq ?_
    rw [hinv]
    ring
  have h1 : ∫⁻ t in Ioo (0 : ℝ) H,
      ENNReal.ofReal r⁻¹ * (ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * unnormSliceVel c u t ^ 2) ≤
      ENNReal.ofReal (c * B ^ 2 * r) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hsq : hCalNorm c u ^ (2 : ℝ) ≤ ENNReal.ofReal (B ^ 2 * r ^ 2) := by
      calc hCalNorm c u ^ (2 : ℝ)
          ≤ (ENNReal.ofReal B * ENNReal.ofReal r) ^ (2 : ℝ) :=
            ENNReal.rpow_le_rpow hnorm (by norm_num)
        _ = ENNReal.ofReal (B * r) ^ (2 : ℝ) := by rw [ENNReal.ofReal_mul hB]
        _ = ENNReal.ofReal ((B * r) ^ 2) := by
            rw [ENNReal.rpow_two, ENNReal.ofReal_pow (mul_nonneg hB hr.le)]
        _ = ENNReal.ofReal (B ^ 2 * r ^ 2) := by ring_nf
    calc ENNReal.ofReal r⁻¹ * ∫⁻ t in Ioo (0 : ℝ) H,
          ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * unnormSliceVel c u t ^ 2
        ≤ ENNReal.ofReal r⁻¹ * (ENNReal.ofReal c * hCalNorm c u ^ (2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (weighted_sliceVel_sq_le hc hu) bot_le
      _ ≤ ENNReal.ofReal r⁻¹ * (ENNReal.ofReal c * ENNReal.ofReal (B ^ 2 * r ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq bot_le) bot_le
      _ = ENNReal.ofReal (c * B ^ 2 * r) := by
          rw [← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_mul (inv_nonneg.2 hr.le)]
          congr 1
          field_simp [hr.ne']
  have h2 : ∫⁻ t in Ioo (0 : ℝ) H, ENNReal.ofReal (r * t ^ (3 / 2 : ℝ)) ≤
      ENNReal.ofReal (H * H ^ (3 / 2 : ℝ) * r) := by
    calc ∫⁻ t in Ioo (0 : ℝ) H, ENNReal.ofReal (r * t ^ (3 / 2 : ℝ))
        ≤ ∫⁻ _t in Ioo (0 : ℝ) H, ENNReal.ofReal (r * H ^ (3 / 2 : ℝ)) := by
          refine setLIntegral_mono' measurableSet_Ioo fun t ht => ENNReal.ofReal_le_ofReal ?_
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.1.le ht.2.le (by norm_num)) hr.le
      _ = ENNReal.ofReal (r * H ^ (3 / 2 : ℝ)) * ENNReal.ofReal H := by
          rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
      _ = ENNReal.ofReal (H * H ^ (3 / 2 : ℝ) * r) := by
          rw [← ENNReal.ofReal_mul (mul_nonneg hr.le (Real.rpow_nonneg hH.le _))]
          ring_nf
  calc ∫⁻ t in Ioo (0 : ℝ) H, unnormSliceVel c u t
      ≤ ∫⁻ t in Ioo (0 : ℝ) H,
          (ENNReal.ofReal r⁻¹ * (ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * unnormSliceVel c u t ^ 2) +
            ENNReal.ofReal (r * t ^ (3 / 2 : ℝ))) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ = (∫⁻ t in Ioo (0 : ℝ) H,
          ENNReal.ofReal r⁻¹ * (ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * unnormSliceVel c u t ^ 2)) +
        ∫⁻ t in Ioo (0 : ℝ) H, ENNReal.ofReal (r * t ^ (3 / 2 : ℝ)) :=
        lintegral_add_left hm1 _
    _ ≤ ENNReal.ofReal (c * B ^ 2 * r) + ENNReal.ofReal (H * H ^ (3 / 2 : ℝ) * r) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal ((c * B ^ 2 + H * H ^ (3 / 2 : ℝ)) * r) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

private theorem lintegral_sliceGrad_le_of_tCalNorm {c H B r : ℝ} (hc : 0 < c) (hH : 0 < H)
    (hB : 0 ≤ B) (hr : 0 < r)
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} (hG : ∀ i j, Measurable fun p => G p i j)
    (hnorm : tCalNorm c G ≤ ENNReal.ofReal B * ENNReal.ofReal r) :
    ∫⁻ t in Ioo (0 : ℝ) H, unnormSliceGrad c G t ≤
      ENNReal.ofReal ((c * B ^ 2 + H * H ^ (1 / 2 : ℝ)) * r) := by
  have hm_grad : Measurable (unnormSliceGrad c G) := measurable_unnormSliceGrad c hG
  have hm1 : Measurable fun t : ℝ =>
      ENNReal.ofReal r⁻¹ * (ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * unnormSliceGrad c G t ^ 2) :=
    measurable_const.mul ((ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul
      (hm_grad.pow_const 2))
  have hpt : ∀ t ∈ Ioo (0 : ℝ) H,
      unnormSliceGrad c G t ≤
        ENNReal.ofReal r⁻¹ * (ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * unnormSliceGrad c G t ^ 2) +
          ENNReal.ofReal (r * t ^ (1 / 2 : ℝ)) := by
    intro t ht
    have ht_pos : 0 < t ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos ht.1 _
    have ha_pos : 0 < r * t ^ (1 / 2 : ℝ) := mul_pos hr ht_pos
    have ha0 : ENNReal.ofReal (r * t ^ (1 / 2 : ℝ)) ≠ 0 := ENNReal.ofReal_pos.2 ha_pos |>.ne'
    have hat : ENNReal.ofReal (r * t ^ (1 / 2 : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hinv : (ENNReal.ofReal (r * t ^ (1 / 2 : ℝ)))⁻¹ =
        ENNReal.ofReal r⁻¹ * ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) := by
      rw [← ENNReal.ofReal_inv_of_pos ha_pos, mul_inv,
        ENNReal.ofReal_mul (inv_nonneg.2 hr.le), ← Real.rpow_neg ht.1.le]
      norm_num
    refine (ennreal_le_sq_div_add ha0 hat).trans_eq ?_
    rw [hinv]
    ring
  have h1 : ∫⁻ t in Ioo (0 : ℝ) H,
      ENNReal.ofReal r⁻¹ * (ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * unnormSliceGrad c G t ^ 2) ≤
      ENNReal.ofReal (c * B ^ 2 * r) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hsq : tCalNorm c G ^ (2 : ℝ) ≤ ENNReal.ofReal (B ^ 2 * r ^ 2) := by
      calc tCalNorm c G ^ (2 : ℝ)
          ≤ (ENNReal.ofReal B * ENNReal.ofReal r) ^ (2 : ℝ) :=
            ENNReal.rpow_le_rpow hnorm (by norm_num)
        _ = ENNReal.ofReal (B * r) ^ (2 : ℝ) := by rw [ENNReal.ofReal_mul hB]
        _ = ENNReal.ofReal ((B * r) ^ 2) := by
            rw [ENNReal.rpow_two, ENNReal.ofReal_pow (mul_nonneg hB hr.le)]
        _ = ENNReal.ofReal (B ^ 2 * r ^ 2) := by ring_nf
    calc ENNReal.ofReal r⁻¹ * ∫⁻ t in Ioo (0 : ℝ) H,
          ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * unnormSliceGrad c G t ^ 2
        ≤ ENNReal.ofReal r⁻¹ * (ENNReal.ofReal c * tCalNorm c G ^ (2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (weighted_sliceGrad_sq_le hc hG) bot_le
      _ ≤ ENNReal.ofReal r⁻¹ * (ENNReal.ofReal c * ENNReal.ofReal (B ^ 2 * r ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq bot_le) bot_le
      _ = ENNReal.ofReal (c * B ^ 2 * r) := by
          rw [← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_mul (inv_nonneg.2 hr.le)]
          congr 1
          field_simp [hr.ne']
  have h2 : ∫⁻ t in Ioo (0 : ℝ) H, ENNReal.ofReal (r * t ^ (1 / 2 : ℝ)) ≤
      ENNReal.ofReal (H * H ^ (1 / 2 : ℝ) * r) := by
    calc ∫⁻ t in Ioo (0 : ℝ) H, ENNReal.ofReal (r * t ^ (1 / 2 : ℝ))
        ≤ ∫⁻ _t in Ioo (0 : ℝ) H, ENNReal.ofReal (r * H ^ (1 / 2 : ℝ)) := by
          refine setLIntegral_mono' measurableSet_Ioo fun t ht => ENNReal.ofReal_le_ofReal ?_
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.1.le ht.2.le (by norm_num)) hr.le
      _ = ENNReal.ofReal (r * H ^ (1 / 2 : ℝ)) * ENNReal.ofReal H := by
          rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
      _ = ENNReal.ofReal (H * H ^ (1 / 2 : ℝ) * r) := by
          rw [← ENNReal.ofReal_mul (mul_nonneg hr.le (Real.rpow_nonneg hH.le _))]
          ring_nf
  calc ∫⁻ t in Ioo (0 : ℝ) H, unnormSliceGrad c G t
      ≤ ∫⁻ t in Ioo (0 : ℝ) H,
          (ENNReal.ofReal r⁻¹ * (ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * unnormSliceGrad c G t ^ 2) +
            ENNReal.ofReal (r * t ^ (1 / 2 : ℝ))) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ = (∫⁻ t in Ioo (0 : ℝ) H,
          ENNReal.ofReal r⁻¹ * (ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * unnormSliceGrad c G t ^ 2)) +
        ∫⁻ t in Ioo (0 : ℝ) H, ENNReal.ofReal (r * t ^ (1 / 2 : ℝ)) :=
        lintegral_add_left hm1 _
    _ ≤ ENNReal.ofReal (c * B ^ 2 * r) + ENNReal.ofReal (H * H ^ (1 / 2 : ℝ) * r) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal ((c * B ^ 2 + H * H ^ (1 / 2 : ℝ)) * r) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

private theorem lintegral_duhamel_slice_le {C_clock ν H : ℝ} {P : PlanarData} {μ : ℂ}
    (hν : 0 < ν) (hH : 0 < H) (hμ_pos : 0 < μ.re)
    {M_src : ℝ → ℝ≥0∞} (hM : Measurable M_src) :
    ∫⁻ s in Ioo (0 : ℝ) H, ∫⁻ t in Ioo (0 : ℝ) s,
        ENNReal.ofReal (vortKernel C_clock P ν μ s t) * M_src t ≤
      ENNReal.ofReal (|C_clock| * ν ^ (-(weakDegree 9 P.kappa : ℝ)) * (H + 2 * Real.sqrt H)) *
        ∫⁻ t in Ioo (0 : ℝ) H, M_src t := by
  set Kc : ℝ := |C_clock| * ν ^ (-(weakDegree 9 P.kappa : ℝ))
  have hKc_nn : 0 ≤ Kc := mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hν.le _)
  have hvort_le : ∀ s ∈ Ioo (0 : ℝ) H, ∀ t ∈ Ioo (0 : ℝ) s,
      ENNReal.ofReal (vortKernel C_clock P ν μ s t) ≤
        ENNReal.ofReal Kc * ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) := by
    intro s _ t ht
    have hs0 : 0 < s := ht.1.trans ht.2
    have hts_le : t / s ≤ 1 := (div_le_one hs0).2 ht.2.le
    have hrpow_le : (t / s) ^ μ.re ≤ 1 := by
      calc (t / s) ^ μ.re ≤ (1 : ℝ) ^ μ.re :=
            Real.rpow_le_rpow (div_nonneg ht.1.le hs0.le) hts_le hμ_pos.le
        _ = 1 := Real.one_rpow _
    have hker_nn : 0 ≤ 1 + (s - t) ^ (-1 / 2 : ℝ) :=
      add_nonneg zero_le_one (Real.rpow_nonneg (sub_nonneg.2 ht.2.le) _)
    rw [← ENNReal.ofReal_mul hKc_nn]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold vortKernel
    calc Kc * (t / s) ^ μ.re * (1 + (s - t) ^ (-1 / 2 : ℝ))
        ≤ Kc * 1 * (1 + (s - t) ^ (-1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrpow_le hKc_nn) hker_nn
      _ = Kc * (1 + (s - t) ^ (-1 / 2 : ℝ)) := by ring
  let Φ : ℝ → ℝ → ℝ≥0∞ := fun s t =>
    if t < s then ENNReal.ofReal Kc * ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) * M_src t else 0
  have hΦ_meas : Measurable (Function.uncurry Φ) := by
    have hlt_meas : MeasurableSet {q : ℝ × ℝ | q.2 < q.1} :=
      measurableSet_lt measurable_snd measurable_fst
    have hker_meas : Measurable fun q : ℝ × ℝ =>
        ENNReal.ofReal Kc * ENNReal.ofReal (1 + (q.1 - q.2) ^ (-1 / 2 : ℝ)) * M_src q.2 :=
      (measurable_const.mul (ENNReal.measurable_ofReal.comp
        (measurable_const.add ((measurable_fst.sub measurable_snd).pow_const _)))).mul
        (hM.comp measurable_snd)
    exact Measurable.ite hlt_meas hker_meas measurable_const
  have hstep1 : ∫⁻ s in Ioo (0 : ℝ) H, ∫⁻ t in Ioo (0 : ℝ) s,
        ENNReal.ofReal (vortKernel C_clock P ν μ s t) * M_src t ≤
      ∫⁻ s in Ioo (0 : ℝ) H, ∫⁻ t in Ioo (0 : ℝ) H, Φ s t := by
    refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
    calc ∫⁻ t in Ioo (0 : ℝ) s, ENNReal.ofReal (vortKernel C_clock P ν μ s t) * M_src t
        ≤ ∫⁻ t in Ioo (0 : ℝ) s, Φ s t := by
          refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
          simp only [Φ, ht.2, ↓reduceIte]
          exact mul_le_mul_of_nonneg_right (hvort_le s hs t ht) bot_le
      _ ≤ ∫⁻ t in Ioo (0 : ℝ) H, Φ s t :=
          lintegral_mono_set (Ioo_subset_Ioo le_rfl hs.2.le)
  have htonelli : ∫⁻ s in Ioo (0 : ℝ) H, ∫⁻ t in Ioo (0 : ℝ) H, Φ s t =
      ∫⁻ t in Ioo (0 : ℝ) H, ∫⁻ s in Ioo (0 : ℝ) H, Φ s t :=
    lintegral_lintegral_swap hΦ_meas.aemeasurable
  have hinner : ∀ t ∈ Ioo (0 : ℝ) H,
      ∫⁻ s in Ioo (0 : ℝ) H, Φ s t ≤
        (ENNReal.ofReal Kc * ENNReal.ofReal (H + 2 * Real.sqrt H)) * M_src t := by
    intro t ht
    have hind_eq : ∀ s ∈ Ioo (0 : ℝ) H,
        Φ s t = (Ioo t H).indicator
          (fun s => ENNReal.ofReal Kc * ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) * M_src t) s := by
      intro s hs
      by_cases hts : t < s
      · have hmem : s ∈ Ioo t H := ⟨hts, hs.2⟩
        simp [Φ, hts, hmem]
      · have hmem : s ∉ Ioo t H := fun h => hts h.1
        simp [Φ, hts, hmem]
    rw [setLIntegral_congr_fun measurableSet_Ioo hind_eq,
      lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
      inter_eq_self_of_subset_left (Ioo_subset_Ioo ht.1.le le_rfl)]
    have hm_k : Measurable fun s : ℝ => ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) :=
      ENNReal.measurable_ofReal.comp (measurable_const.add ((measurable_id.sub_const t).pow_const _))
    have hfactor : ∫⁻ s in Ioo t H,
        ENNReal.ofReal Kc * ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) * M_src t =
        ENNReal.ofReal Kc * (∫⁻ s in Ioo t H, ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ))) *
          M_src t := by
      have heq_f : (fun s : ℝ =>
          ENNReal.ofReal Kc * ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) * M_src t) =
          fun s => (ENNReal.ofReal Kc * M_src t) * ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) := by
        funext s; ring
      rw [heq_f, lintegral_const_mul _ hm_k]
      ring
    rw [hfactor]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (lintegral_kernel_s_le hH ht) bot_le) bot_le
  calc ∫⁻ s in Ioo (0 : ℝ) H, ∫⁻ t in Ioo (0 : ℝ) s,
        ENNReal.ofReal (vortKernel C_clock P ν μ s t) * M_src t
      ≤ ∫⁻ t in Ioo (0 : ℝ) H, ∫⁻ s in Ioo (0 : ℝ) H, Φ s t := by
        rw [← htonelli]; exact hstep1
    _ ≤ ∫⁻ t in Ioo (0 : ℝ) H,
          (ENNReal.ofReal Kc * ENNReal.ofReal (H + 2 * Real.sqrt H)) * M_src t :=
        setLIntegral_mono' measurableSet_Ioo hinner
    _ = ENNReal.ofReal (Kc * (H + 2 * Real.sqrt H)) * ∫⁻ t in Ioo (0 : ℝ) H, M_src t := by
        rw [lintegral_const_mul _ hM, ENNReal.ofReal_mul hKc_nn]

/-! ## 4. Measurable `X_{9,c}` slice norms, telescoping limit, and `L²(cell c)` convergence -/

private theorem measurable_xNorm_slice (c : ℝ) {g : ℝ → ℝ × ℝ → ℂ}
    (hg : Measurable (Function.uncurry g)) :
    Measurable fun t : ℝ => xNorm c 9 (g t) := by
  have heq : (fun t : ℝ => xNorm c 9 (g t)) =
      fun t => (∫⁻ x, ‖g t x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure c 9)) ^ (1 / 2 : ℝ) := by
    funext t
    rw [xNorm, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    norm_num
  rw [heq]
  have hm : Measurable fun p : ℝ × (ℝ × ℝ) => ‖g p.1 p.2‖ₑ ^ (2 : ℝ) :=
    hg.enorm.pow_const (2 : ℝ)
  exact hm.lintegral_prod_right'.pow_const (1 / 2 : ℝ)

private theorem eLpNorm_cell_le_xNorm {c : ℝ} {f : ℝ × ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (B0579.cell c))) :
    eLpNorm f 2 (volume.restrict (B0579.cell c)) ≤ xNorm c 9 f := by
  rw [xNorm, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  norm_num
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  have hd : Measurable fun x => (B0579.density 9 x : ℝ≥0∞) :=
    (B0579.measurable_density 9).coe_nnreal_ennreal
  unfold B0579.cellMeasure
  rw [lintegral_withDensity_eq_lintegral_mul₀ hd.aemeasurable (hf.enorm.pow_const 2)]
  refine lintegral_mono fun x => ?_
  have hjb1 : 1 ≤ B0579.jb x := by
    unfold B0579.jb
    nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  have hd1 : (1 : ℝ≥0∞) ≤ (B0579.density 9 x : ℝ≥0∞) := by
    change (1 : ℝ≥0∞) ≤ ENNReal.ofReal (B0579.jb x ^ (9 : ℝ))
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow hjb1 (by norm_num))
  simpa only [Pi.mul_apply, one_mul] using
    mul_le_mul_of_nonneg_right hd1 (bot_le : (0 : ℝ≥0∞) ≤ ‖f x‖ₑ ^ 2)

private def teleConvSet (ks : ℕ → ℝ → ℝ × ℝ → ℂ) : Set (ℝ × (ℝ × ℝ)) :=
  {p | (∑' n : ℕ, ‖ks (n + 1) p.1 p.2 - ks n p.1 p.2‖ₑ) < ⊤}

private def teleLimit (ks : ℕ → ℝ → ℝ × ℝ → ℂ) (t : ℝ) (x : ℝ × ℝ) : ℂ :=
  (teleConvSet ks).indicator
    (fun p => ks 0 p.1 p.2 + ∑' n : ℕ, (ks (n + 1) p.1 p.2 - ks n p.1 p.2)) (t, x)

private theorem measurableSet_teleConvSet {ks : ℕ → ℝ → ℝ × ℝ → ℂ}
    (hks : ∀ n, Measurable (Function.uncurry (ks n))) :
    MeasurableSet (teleConvSet ks) := by
  have hm : Measurable fun p : ℝ × (ℝ × ℝ) => ∑' n : ℕ, ‖ks (n + 1) p.1 p.2 - ks n p.1 p.2‖ₑ :=
    Measurable.tsum fun n => ((hks (n + 1)).sub (hks n)).enorm
  exact measurableSet_Iio.preimage hm

private theorem summable_of_mem_teleConvSet {ks : ℕ → ℝ → ℝ × ℝ → ℂ} {t : ℝ} {x : ℝ × ℝ}
    (hp : (t, x) ∈ teleConvSet ks) :
    Summable fun n : ℕ => ‖ks (n + 1) t x - ks n t x‖ := by
  have hne : (∑' n : ℕ, (‖ks (n + 1) t x - ks n t x‖₊ : ℝ≥0∞)) ≠ ⊤ := hp.ne
  exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 hne)

private theorem teleLimit_sub_enorm_le {ks : ℕ → ℝ → ℝ × ℝ → ℂ} {t : ℝ} {x : ℝ × ℝ}
    (hp : (t, x) ∈ teleConvSet ks) (N : ℕ) :
    ‖teleLimit ks t x - ks N t x‖ₑ ≤
      ∑' m : ℕ, ‖ks (N + m + 1) t x - ks (N + m) t x‖ₑ := by
  have hsum_norm := summable_of_mem_teleConvSet hp
  have hsum := hsum_norm.of_norm
  have htel : ks N t x = ks 0 t x + ∑ i ∈ Finset.range N, (ks (i + 1) t x - ks i t x) := by
    rw [Finset.sum_range_sub (fun n => ks n t x) N]
    ring
  have hsplit := hsum.sum_add_tsum_nat_add N
  have hshift : (∑' i : ℕ, (ks (i + N + 1) t x - ks (i + N) t x)) =
      ∑' m : ℕ, (ks (N + m + 1) t x - ks (N + m) t x) :=
    tsum_congr fun m => by rw [Nat.add_comm m N]
  have hdiff : teleLimit ks t x - ks N t x =
      ∑' m : ℕ, (ks (N + m + 1) t x - ks (N + m) t x) := by
    unfold teleLimit
    rw [indicator_of_mem hp, htel, ← hsplit, hshift]
    abel
  rw [hdiff, ← ofReal_norm]
  have htail_norm : Summable fun m : ℕ => ‖ks (N + m + 1) t x - ks (N + m) t x‖ :=
    hsum_norm.comp_injective (add_right_injective N)
  calc ENNReal.ofReal ‖∑' m : ℕ, (ks (N + m + 1) t x - ks (N + m) t x)‖
      ≤ ENNReal.ofReal (∑' m : ℕ, ‖ks (N + m + 1) t x - ks (N + m) t x‖) :=
        ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm htail_norm)
    _ = ∑' m : ℕ, ENNReal.ofReal ‖ks (N + m + 1) t x - ks (N + m) t x‖ :=
        ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) htail_norm
    _ = ∑' m : ℕ, ‖ks (N + m + 1) t x - ks (N + m) t x‖ₑ := by
        refine tsum_congr fun m => ofReal_norm _

private theorem measurable_uncurry_teleLimit {ks : ℕ → ℝ → ℝ × ℝ → ℂ}
    (hks : ∀ n, Measurable (Function.uncurry (ks n))) :
    Measurable (Function.uncurry (teleLimit ks)) := by
  have hS : MeasurableSet (teleConvSet ks) := measurableSet_teleConvSet hks
  let g : ℕ → ℝ × (ℝ × ℝ) → ℂ := fun N => (teleConvSet ks).indicator (Function.uncurry (ks N))
  have hg : ∀ N, Measurable (g N) := fun N => (hks N).indicator hS
  refine measurable_of_tendsto_metrizable hg (tendsto_pi_nhds.2 fun p => ?_)
  rcases p with ⟨t, x⟩
  by_cases hp : (t, x) ∈ teleConvSet ks
  · have hsum : Summable fun n : ℕ => ks (n + 1) t x - ks n t x :=
      (summable_of_mem_teleConvSet hp).of_norm
    have hge : ∀ N, g N (t, x) = ks 0 t x +
        ∑ i ∈ Finset.range N, (ks (i + 1) t x - ks i t x) := by
      intro N
      simp only [g, indicator_of_mem hp, Function.uncurry_apply_pair]
      rw [Finset.sum_range_sub (fun n => ks n t x) N]
      ring
    have hk : Function.uncurry (teleLimit ks) (t, x) =
        ks 0 t x + ∑' n : ℕ, (ks (n + 1) t x - ks n t x) := by
      simp [teleLimit, indicator_of_mem hp]
    simp_rw [hge, hk]
    exact tendsto_const_nhds.add hsum.hasSum.tendsto_sum_nat
  · have hge : ∀ N, g N (t, x) = 0 := fun N => indicator_of_notMem hp _
    have hk : Function.uncurry (teleLimit ks) (t, x) = 0 := by
      simp [teleLimit, indicator_of_notMem hp]
    simp_rw [hge, hk]
    exact tendsto_const_nhds

attribute [irreducible] teleLimit

private theorem xNorm_le_sub_add (c : ℝ) {f g : ℝ × ℝ → ℂ}
    (hf : Measurable f) (hg : Measurable g) :
    xNorm c 9 f ≤ xNorm c 9 (fun x => f x - g x) + xNorm c 9 g := by
  have heq : f = (f - g) + g := by funext x; simp
  calc xNorm c 9 f
      = eLpNorm ((f - g) + g) 2 (B0579.cellMeasure c 9) :=
        congrArg (eLpNorm · 2 (B0579.cellMeasure c 9)) heq
    _ ≤ eLpNorm (f - g) 2 (B0579.cellMeasure c 9) +
          eLpNorm g 2 (B0579.cellMeasure c 9) :=
        eLpNorm_add_le (hf.sub hg).aestronglyMeasurable hg.aestronglyMeasurable one_le_two
    _ = xNorm c 9 (fun x => f x - g x) + xNorm c 9 g := rfl

private theorem xNorm_le_add_sub (c : ℝ) {f g : ℝ × ℝ → ℂ}
    (hf : Measurable f) (hg : Measurable g) :
    xNorm c 9 g ≤ xNorm c 9 f + xNorm c 9 (fun x => f x - g x) := by
  have heq : g = f - (f - g) := by funext x; simp
  calc xNorm c 9 g
      = eLpNorm (f - (f - g)) 2 (B0579.cellMeasure c 9) :=
        congrArg (eLpNorm · 2 (B0579.cellMeasure c 9)) heq
    _ ≤ eLpNorm f 2 (B0579.cellMeasure c 9) +
          eLpNorm (f - g) 2 (B0579.cellMeasure c 9) :=
        eLpNorm_sub_le hf.aestronglyMeasurable (hf.sub hg).aestronglyMeasurable one_le_two
    _ = xNorm c 9 f + xNorm c 9 (fun x => f x - g x) := rfl

private theorem xNorm_teleLimit_sub_le {c : ℝ} {ks : ℕ → ℝ → ℝ × ℝ → ℂ}
    (hks : ∀ n, Measurable (Function.uncurry (ks n))) {t : ℝ}
    (ht_sum : (∑' n : ℕ, xNorm c 9 (fun x => ks (n + 1) t x - ks n t x)) < ⊤) (N : ℕ) :
    xNorm c 9 (fun x => teleLimit ks t x - ks N t x) ≤
      ∑' m : ℕ, xNorm c 9 (fun x => ks (N + m + 1) t x - ks (N + m) t x) := by
  have hks_t : ∀ n, Measurable (ks n t) := fun n =>
    (hks n).comp (measurable_const.prodMk measurable_id)
  let R : ℕ → (ℝ × ℝ) → ℝ≥0∞ := fun M x =>
    ∑' m : ℕ, ‖ks (M + m + 1) t x - ks (M + m) t x‖ₑ
  have hR_bound : ∀ M : ℕ, eLpNorm (R M) 2 (B0579.cellMeasure c 9) ≤
      ∑' m : ℕ, xNorm c 9 (fun x => ks (M + m + 1) t x - ks (M + m) t x) := by
    intro M
    let F : (ℝ × ℝ) → ℕ → ℝ≥0∞ := fun x m => ‖ks (M + m + 1) t x - ks (M + m) t x‖ₑ
    have hFm : Measurable (Function.uncurry F) :=
      measurable_from_prod_countable_left fun m => ((hks_t (M + m + 1)).sub (hks_t (M + m))).enorm
    have hmink := UnforcedLeray.PlanarBS.Conv.eLpNorm_lintegral_le
      (μ := B0579.cellMeasure c 9) (ν := (Measure.count : Measure ℕ)) hFm.aemeasurable
      (p := 2) (by norm_num) (by norm_num)
    have hR_eq : R M = fun x => ∫⁻ m, F x m ∂Measure.count := by
      funext x; exact (lintegral_count (F x)).symm
    rw [hR_eq]
    refine hmink.trans_eq ?_
    rw [lintegral_count]
    refine tsum_congr fun m => ?_
    rw [xNorm, eLpNorm_enorm]
  have hR0_lt : eLpNorm (R 0) 2 (B0579.cellMeasure c 9) < ⊤ := by
    refine (hR_bound 0).trans_lt ?_
    simpa only [zero_add] using ht_sum
  have hR0_m : Measurable (R 0) :=
    Measurable.tsum fun m => ((hks_t (0 + m + 1)).sub (hks_t (0 + m))).enorm
  have hR0_ae : ∀ᵐ x ∂(B0579.cellMeasure c 9), (t, x) ∈ teleConvSet ks := by
    have hlt := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero
      ENNReal.ofNat_ne_top).1 hR0_lt
    have hm_sq : Measurable fun x => ‖R 0 x‖ₑ ^ ENNReal.toReal 2 :=
      hR0_m.enorm.pow_const _
    filter_upwards [ae_lt_top hm_sq hlt.ne] with x hx
    simp only [enorm_eq_self, ENNReal.toReal_ofNat] at hx
    have hx1 : R 0 x < ⊤ := by
      have := ENNReal.rpow_lt_top_of_nonneg (y := 1 / 2) (by norm_num) hx.ne
      rwa [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one] at this
    change (∑' n : ℕ, ‖ks (n + 1) t x - ks n t x‖ₑ) < ⊤
    simpa only [R, zero_add] using hx1
  have hae_le : ∀ᵐ x ∂(B0579.cellMeasure c 9), ‖teleLimit ks t x - ks N t x‖ₑ ≤ R N x := by
    filter_upwards [hR0_ae] with x hx
    exact teleLimit_sub_enorm_le hx N
  have hmono : xNorm c 9 (fun x => teleLimit ks t x - ks N t x) ≤
      eLpNorm (R N) 2 (B0579.cellMeasure c 9) := by
    rw [xNorm, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    refine ENNReal.rpow_le_rpow (lintegral_mono_ae ?_) (by norm_num)
    filter_upwards [hae_le] with x hx
    rw [enorm_eq_self]
    exact ENNReal.rpow_le_rpow hx (by norm_num)
  exact hmono.trans (hR_bound N)

/-! ## 5. Pointwise slice convergence from geometric weighted `L²` decay -/

private theorem ae_slice_tendsto_zero_of_weighted_sq_geom {c H a B : ℝ} (hc : 0 < c)
    {X : ℕ → ℝ → ℝ≥0∞} (hXm : ∀ n, Measurable (X n))
    (hbd : ∀ n, ∫⁻ s in Ioo (0 : ℝ) H,
      ENNReal.ofReal (s ^ a) * (ENNReal.ofReal c⁻¹ * X n s ^ 2) ≤
        ENNReal.ofReal B * ENNReal.ofReal ((1 / 4 : ℝ) ^ n)) :
    ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) H → Tendsto (fun n => X n s) atTop (𝓝 0) := by
  let term : ℕ → ℝ → ℝ≥0∞ := fun n s =>
    ENNReal.ofReal (s ^ a) * (ENNReal.ofReal c⁻¹ * X n s ^ 2)
  have htm : ∀ n, Measurable (term n) := fun n =>
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const a)).mul
      (measurable_const.mul ((hXm n).pow_const 2))
  have hsum_int : ∫⁻ s in Ioo (0 : ℝ) H, ∑' n : ℕ, term n s < ⊤ := by
    rw [lintegral_tsum fun n => (htm n).aemeasurable]
    calc (∑' n : ℕ, ∫⁻ s in Ioo (0 : ℝ) H, term n s)
        ≤ ∑' n : ℕ, ENNReal.ofReal B * ENNReal.ofReal ((1 / 4 : ℝ) ^ n) :=
          ENNReal.tsum_le_tsum hbd
      _ = ENNReal.ofReal B * ∑' n : ℕ, ENNReal.ofReal ((1 / 4 : ℝ) ^ n) :=
          ENNReal.tsum_mul_left
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top tsum_ofReal_quarter_pow_lt_top
  have hae_fin : ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) H)), (∑' n : ℕ, term n s) < ⊤ :=
    ae_lt_top (Measurable.tsum htm) hsum_int.ne
  rw [ae_restrict_iff' measurableSet_Ioo] at hae_fin
  filter_upwards [hae_fin] with s hs hsH
  have hs_fin : (∑' n : ℕ, term n s) < ⊤ := hs hsH
  set w : ℝ≥0∞ := ENNReal.ofReal (s ^ a) * ENNReal.ofReal c⁻¹
  have hw0 : w ≠ 0 := by
    dsimp [w]
    exact mul_ne_zero (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hsH.1 a)).ne'
      (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne'
  have htsum_eq : ∑' n : ℕ, term n s = w * ∑' n : ℕ, X n s ^ 2 := by
    have heq : ∀ n, term n s = w * X n s ^ 2 := fun n => by dsimp [term, w]; ring
    simp_rw [heq, ENNReal.tsum_mul_left]
  rw [htsum_eq] at hs_fin
  have hsq_sum_lt : (∑' n : ℕ, X n s ^ 2) < ⊤ := by
    rcases ENNReal.mul_lt_top_iff.1 hs_fin with ⟨_, h2⟩ | h0 | h0
    · exact h2
    · exact absurd h0 hw0
    · rw [h0]; exact ENNReal.zero_lt_top
  have hsq_lim : Tendsto (fun n => X n s ^ 2) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsq_sum_lt.ne
  have hrpow_lim : Tendsto (fun n => (X n s ^ 2) ^ (1 / 2 : ℝ)) atTop
      (𝓝 ((0 : ℝ≥0∞) ^ (1 / 2 : ℝ))) :=
    (ENNReal.continuous_rpow_const.tendsto 0).comp hsq_lim
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hrpow_lim
  refine hrpow_lim.congr fun n => ?_
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-! ## 6. Core train advection Gronwall bound on `(0, H)` -/

private def coreExpRamp (L δ H s : ℝ) : ℝ :=
  Real.exp (-L * s) * rampPsi δ H s

private theorem coreExpRamp_contDiff (L δ H : ℝ) : ContDiff ℝ 1 (coreExpRamp L δ H) := by
  unfold coreExpRamp
  exact (((contDiff_const (c := -L)).mul contDiff_id).exp).mul (TailEnergyBoundAux.rampPsi_contDiff δ H)

private theorem coreExpRamp_nonneg (L δ H s : ℝ) : 0 ≤ coreExpRamp L δ H s :=
  mul_nonneg (Real.exp_nonneg _) (rampPsi_nonneg δ H s)

private theorem coreExpRamp_le_one {L δ H s : ℝ} (hL : 0 ≤ L) (hs : 0 ≤ s) :
    coreExpRamp L δ H s ≤ 1 := by
  unfold coreExpRamp
  have hexp : Real.exp (-L * s) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  exact mul_le_one₀ hexp (rampPsi_nonneg δ H s) (rampPsi_le_one δ H s)

private theorem coreExpRamp_eq_zero_of_not_mem {L δ H s : ℝ} (hδ : 0 < δ) (hH : 0 < H)
    (hs : s ∉ Icc δ (2 * H)) : coreExpRamp L δ H s = 0 := by
  unfold coreExpRamp
  rw [rampPsi_eq_zero_of_not_mem hδ hH hs, mul_zero]

private theorem coreExpRamp_tsupport_subset {L δ H : ℝ} (hδ : 0 < δ) (hH : 0 < H) :
    tsupport (coreExpRamp L δ H) ⊆ Icc δ (2 * H) := by
  refine closure_minimal (fun s hs => ?_) isClosed_Icc
  by_contra hs'
  exact hs (coreExpRamp_eq_zero_of_not_mem hδ hH hs')

private theorem coreExpRamp_ge_on_Icc {L δ H s : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) (hH : 0 < H)
    (hs : s ∈ Icc (2 * δ) H) : Real.exp (-L * H) ≤ coreExpRamp L δ H s := by
  unfold coreExpRamp
  rw [rampPsi_one hδ hH hs, mul_one]
  exact Real.exp_le_exp.2 (by nlinarith [hs.2])

private theorem coreExpRamp_deriv_add (L δ H s : ℝ) :
    deriv (coreExpRamp L δ H) s + L * coreExpRamp L δ H s =
      Real.exp (-L * s) * deriv (rampPsi δ H) s := by
  have h1 : HasDerivAt (fun y : ℝ => Real.exp (-L * y)) (Real.exp (-L * s) * (-L * 1)) s :=
    HasDerivAt.exp ((hasDerivAt_id' s).const_mul (-L))
  have h2 : HasDerivAt (rampPsi δ H) (deriv (rampPsi δ H) s) s :=
    ((TailEnergyBoundAux.rampPsi_contDiff δ H).differentiable one_ne_zero s).hasDerivAt
  have hd : deriv (coreExpRamp L δ H) s =
      Real.exp (-L * s) * (-L * 1) * rampPsi δ H s +
        Real.exp (-L * s) * deriv (rampPsi δ H) s := by
    unfold coreExpRamp
    exact (h1.mul h2).deriv
  rw [hd]
  unfold coreExpRamp
  ring

private theorem coreExpRamp_strain_deriv_le {K M_L δ H : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ x, |deriv Real.smoothTransition x| ≤ K)
    (hML0 : 0 ≤ M_L) (hδ : 0 < δ) (hH2 : 2 * δ < H)
    {L_str : ℝ → ℝ} (hL_bd : ∀ s ∈ Icc (0 : ℝ) (2 * H), L_str s ≤ M_L) (s : ℝ) :
    deriv (coreExpRamp (2 * M_L) δ H) s + 2 * L_str s * coreExpRamp (2 * M_L) δ H s ≤
      (2 * K + 1) / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s := by
  have hH : 0 < H := by linarith
  by_cases hs_supp : s ∈ Icc δ (2 * H)
  · have hs_Icc : s ∈ Icc (0 : ℝ) (2 * H) := ⟨hδ.le.trans hs_supp.1, hs_supp.2⟩
    have hstr : 2 * L_str s * coreExpRamp (2 * M_L) δ H s ≤
        (2 * M_L) * coreExpRamp (2 * M_L) δ H s :=
      mul_le_mul_of_nonneg_right (by linarith [hL_bd s hs_Icc]) (coreExpRamp_nonneg _ _ _ s)
    calc deriv (coreExpRamp (2 * M_L) δ H) s + 2 * L_str s * coreExpRamp (2 * M_L) δ H s
        ≤ deriv (coreExpRamp (2 * M_L) δ H) s + (2 * M_L) * coreExpRamp (2 * M_L) δ H s := by
          linarith
      _ = Real.exp (-(2 * M_L) * s) * deriv (rampPsi δ H) s :=
          coreExpRamp_deriv_add (2 * M_L) δ H s
      _ ≤ Real.exp (-(2 * M_L) * s) *
            ((2 * K + 1) / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s) :=
          mul_le_mul_of_nonneg_left
            (TailEnergyBoundAux.rampPsi_deriv_le hK0 hK hδ hH2 s) (Real.exp_nonneg _)
      _ ≤ (2 * K + 1) / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s := by
          by_cases hs2 : s ∈ Icc δ (2 * δ)
          · rw [indicator_of_mem hs2, mul_one]
            have hexp1 : Real.exp (-(2 * M_L) * s) ≤ 1 :=
              Real.exp_le_one_iff.2 (by nlinarith [hs_Icc.1])
            exact mul_le_of_le_one_left (by positivity) hexp1
          · rw [indicator_of_notMem hs2, mul_zero, mul_zero]
  · have hnot_tsupp : s ∉ tsupport (coreExpRamp (2 * M_L) δ H) := fun h =>
      hs_supp (coreExpRamp_tsupport_subset hδ hH h)
    have hψz : coreExpRamp (2 * M_L) δ H s = 0 := coreExpRamp_eq_zero_of_not_mem hδ hH hs_supp
    have hev : coreExpRamp (2 * M_L) δ H =ᶠ[𝓝 s] 0 :=
      notMem_tsupport_iff_eventuallyEq.1 hnot_tsupp
    have hdz : deriv (coreExpRamp (2 * M_L) δ H) s = 0 := by
      rw [hev.deriv_eq]; simp
    rw [hdz, hψz, mul_zero, add_zero]
    by_cases hs2 : s ∈ Icc δ (2 * δ)
    · exact absurd ⟨hs2.1, by linarith [hs2.2]⟩ hs_supp
    · rw [indicator_of_notMem hs2, mul_zero]

private theorem train_core_grad_sq_le {c ν γ H : ℝ} {μ : ℂ}
    (hc : 0 < c) (hν0 : 0 < ν) (hγ : 0 ≤ γ) (hH : 0 < H) (hμre : 0 < μ.re)
    {tr : UnforcedLeray.B0140.TrainSol ν c} (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {M_L : ℝ} (hML0 : 0 ≤ M_L)
    (hML : ∀ s ∈ Icc (0 : ℝ) (2 * H), (UnforcedLeray.B0277.supNormD 1 (tr.v s)).toReal ≤ M_L)
    {Fd : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {d : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {Gd : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hFm : ∀ i j, Measurable fun p => Fd p i j)
    (hFfin : tCalNorm c (gainConj γ ν Fd) < ⊤)
    (hsol : IsCausalEnergySolution c ν μ (trainVel tr) Fd d Gd) :
    ∫⁻ s in Ioo (0 : ℝ) H,
        ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
          (ENNReal.ofReal c⁻¹ * unnormSliceGrad c (gainConj γ ν Gd) s ^ 2) ≤
      ENNReal.ofReal (Real.exp (2 * M_L * H) * (ν ^ 2)⁻¹) *
        tCalNorm c (gainConj γ ν Fd) ^ 2 := by
  have hBG := gainLocBG c ν γ hγ hν0 d Gd hsol.energyLoc
  have hFl := gainLocF c ν γ hc hγ hν0 Fd hFm hFfin
  have hdm' := measurable_gainConj_vec (γ := γ) (ν := ν) hsol.measurable
  have hGdm' := measurable_gainConj_ten γ ν hsol.gradMeasurable
  have hFm' := measurable_gainConj_ten γ ν hFm
  let gV : ℝ × (ℝ × ℝ) → ℝ := fun p => vnorm2 (gainConj γ ν d p) ^ 2
  let gN : ℝ × (ℝ × ℝ) → ℝ := fun p => tnorm2 (gainConj γ ν Gd p) ^ 2
  let gQ : ℝ × (ℝ × ℝ) → ℝ := fun p => tnorm2 (gainConj γ ν Fd p) ^ 2
  have hgVm : Measurable gV := measurable_vnorm2_sq hdm'
  have hgNm : Measurable gN := (measurable_tnorm2 hGdm').pow_const 2
  have hgQm : Measurable gQ := (measurable_tnorm2 hFm').pow_const 2
  have hgV0 : ∀ p, 0 ≤ gV p := fun _ => sq_nonneg _
  have hgN0 : ∀ p, 0 ≤ gN p := fun _ => sq_nonneg _
  have hgQ0 : ∀ p, 0 ≤ gQ p := fun _ => sq_nonneg _
  obtain ⟨_, hVi, _⟩ := sliceLoc c gV hc hgVm hgV0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).1
  obtain ⟨_, hNi, _⟩ := sliceLoc c gN hc hgNm hgN0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).2
  obtain ⟨_, hQi, _⟩ := sliceLoc c gQ hc hgQm hgQ0 fun s₁ s₂ h1 h2 => (hFl s₁ s₂ h1 h2).2
  let A : ℝ → ℝ := sliceSq c gV
  let N : ℝ → ℝ := sliceSq c gN
  let M_slice : ℝ → ℝ :=
    sliceSq c (fun p => tnorm2 (gainConj γ ν Fd p) * tnorm2 (gainConj γ ν Gd p))
  let Q : ℝ → ℝ := sliceSq c gQ
  have hnn : ∀ s, 0 ≤ A s ∧ 0 ≤ N s ∧ 0 ≤ M_slice s ∧ 0 ≤ Q s :=
    fun s => ⟨sliceSq_nonneg hgV0 s, sliceSq_nonneg hgN0 s,
      sliceSq_nonneg (fun p => mul_nonneg (tnorm2_nonneg _) (tnorm2_nonneg _)) s,
      sliceSq_nonneg hgQ0 s⟩
  have hAdv_sol := trainAdvectionEnergyIdentity c ν γ μ hc hν0 hγ tr htr Fd d Gd
    (fun s₁ s₂ h1 h2 => (hFl s₁ s₂ h1 h2).1) hFm hsol
  have hY := youngSlice c (gainConj γ ν Fd) (gainConj γ ν Gd) hc hFm' hGdm'
    (fun s₁ s₂ h1 h2 => (hFl s₁ s₂ h1 h2).2)
    (fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).2) ν hν0
  -- Zero-entrance finiteness for A
  obtain ⟨δ0, hδ0, hfinA⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∫⁻ s in Ioo 0 δ, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) < ⊤ := by
    obtain ⟨δ, hδ, hfin⟩ := hsol.zeroEntrance
    refine ⟨δ, hδ, ?_⟩
    obtain ⟨-, h2⟩ := ageSlice c (-3 / 2) gV hc hgVm hgV0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).1
    have hle : ∫⁻ p, ENNReal.ofReal (gV p)
        ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) ≤
        ∫⁻ p, ENNReal.ofReal (vnorm2 (d p) ^ 2)
        ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) := by
      refine lintegral_mono_ae ?_
      have hm : MeasurableSet (Ioo (0 : ℝ) δ ×ˢ (univ : Set (ℝ × ℝ))) :=
        measurableSet_Ioo.prod MeasurableSet.univ
      filter_upwards [ae_restrict_mem hm] with p hp
      apply ENNReal.ofReal_le_ofReal
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _)
        (vnorm2_smul_le (inv_nonneg.2 (Real.exp_pos _).le) (gainG_inv_le_one hγ hν0 hp.1.1) _) 2
    have hlt := hle.trans_lt hfin
    rw [h2 δ] at hlt
    have hc' : ENNReal.ofReal c⁻¹ ≠ 0 := by simpa using inv_pos.2 hc
    rcases ENNReal.mul_lt_top_iff.1 hlt with h | h | h
    · exact h.2
    · exact absurd h hc'
    · simp [A, h]
  obtain ⟨Kσ, hKσ0, hKσ⟩ := sigma_deriv_bound
  set C_ramp : ℝ := 2 * Kσ + 1
  have hC_ramp : 0 < C_ramp := by unfold C_ramp; linarith
  let L_str : ℝ → ℝ := fun s => (UnforcedLeray.B0277.supNormD 1 (tr.v s)).toReal
  -- Step 1: Bound on `Icc a H` for every `0 < a < H`
  have hIcc_le : ∀ a : ℝ, 0 < a → a < H →
      ENNReal.ofReal (Real.exp (-2 * M_L * H) * ν) *
          (∫⁻ s in Icc a H, ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s)) ≤
        ENNReal.ofReal ν⁻¹ * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s) := by
    intro a ha haH
    have hdelta : ∀ δ : ℝ, 0 < δ → 2 * δ ≤ a →
        ENNReal.ofReal (Real.exp (-2 * M_L * H) * ν) *
            (∫⁻ s in Icc a H, ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s)) ≤
          ENNReal.ofReal (2 * C_ramp) *
              (∫⁻ s in Ioo 0 (3 * δ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) +
            ENNReal.ofReal ν⁻¹ *
              ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s) := by
      intro δ hδ h2δa
      have hH2 : 2 * δ < H := lt_of_le_of_lt h2δa haH
      have hδ2H : δ < 2 * H := by linarith
      set ψ : ℝ → ℝ := coreExpRamp (2 * M_L) δ H
      have hc1 : ContDiff ℝ 1 ψ := coreExpRamp_contDiff (2 * M_L) δ H
      have hsupp : tsupport ψ ⊆ Icc δ (2 * H) := coreExpRamp_tsupport_subset hδ hH
      have hcs : HasCompactSupport ψ :=
        IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hsupp
      have hts : tsupport ψ ⊆ Ioi 0 := hsupp.trans fun s hs => lt_of_lt_of_le hδ hs.1
      have hψ0 : ∀ s, 0 ≤ ψ s := coreExpRamp_nonneg (2 * M_L) δ H
      obtain ⟨hint, hle⟩ := TailEnergyBoundAux.advection_cutoff_young
        (k := 1 / 4) (ν := ν) (α := 1 / 2 + 2 * μ.re)
        (A := A) (N := N) (M := M_slice) (Q := Q) (ψ := ψ)
        (D := fun s => deriv ψ s + 2 * L_str s * ψ s) (a := δ) (b := 2 * H)
        hν0 (by linarith) hnn
        (hVi δ (2 * H) hδ hδ2H) (hNi δ (2 * H) hδ hδ2H) (hQi δ (2 * H) hδ hδ2H)
        hY hc1 hδ hsupp hψ0 (hAdv_sol ψ hc1 hcs hts hψ0)
      -- Convert LHS integral to lintegral and lower bound over `[a, H]`
      have s2 : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (ψ s * cutG (1 / 4) ν ν A N s) =
          ENNReal.ofReal (∫ s in Ioi (0 : ℝ), ψ s * cutG (1 / 4) ν ν A N s) := by
        refine (ofReal_integral_eq_lintegral_ofReal hint ?_).symm
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hs0 : 0 ≤ s := le_of_lt hs
        have hA0 := mul_nonneg (Real.rpow_nonneg hs0 (-3 / 2 : ℝ)) (hnn s).1
        have hN0 := mul_nonneg (Real.rpow_nonneg hs0 (-1 / 2 : ℝ)) (hnn s).2.1
        have hcut0 : 0 ≤ cutG (1 / 4) ν ν A N s := by
          unfold cutG; nlinarith
        exact mul_nonneg (hψ0 s) hcut0
      have hLHS_le : ENNReal.ofReal (Real.exp (-2 * M_L * H) * ν) *
            (∫⁻ s in Icc a H, ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s)) ≤
          ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (ψ s * cutG (1 / 4) ν ν A N s) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine (setLIntegral_mono' measurableSet_Icc fun s hs => ?_).trans
          (lintegral_mono_set fun s hs => lt_of_lt_of_le ha hs.1)
        have hs0 : 0 ≤ s := le_trans ha.le hs.1
        have hsIcc : s ∈ Icc (2 * δ) H := ⟨le_trans h2δa hs.1, hs.2⟩
        have hψ_ge : Real.exp (-(2 * M_L) * H) ≤ ψ s :=
          coreExpRamp_ge_on_Icc (by positivity) hδ hH hsIcc
        have hexp_eq : -(2 * M_L) * H = -2 * M_L * H := by ring
        rw [hexp_eq] at hψ_ge
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hA0 := mul_nonneg (Real.rpow_nonneg hs0 (-3 / 2 : ℝ)) (hnn s).1
        have hN0 := mul_nonneg (Real.rpow_nonneg hs0 (-1 / 2 : ℝ)) (hnn s).2.1
        have hcut_ge : ν * (s ^ (-1 / 2 : ℝ) * N s) ≤ cutG (1 / 4) ν ν A N s := by
          unfold cutG; nlinarith
        calc (Real.exp (-2 * M_L * H) * ν) * (s ^ (-1 / 2 : ℝ) * N s)
            = Real.exp (-2 * M_L * H) * (ν * (s ^ (-1 / 2 : ℝ) * N s)) := by ring
          _ ≤ ψ s * (ν * (s ^ (-1 / 2 : ℝ) * N s)) :=
              mul_le_mul_of_nonneg_right hψ_ge (by positivity)
          _ ≤ ψ s * cutG (1 / 4) ν ν A N s :=
              mul_le_mul_of_nonneg_left hcut_ge (hψ0 s)
      -- Bound the D-term on `(0, 3δ)` and Q-term on `Ioi 0`
      have hD_le : ENNReal.ofReal
            (∫ s in Ioi (0 : ℝ), (deriv ψ s + 2 * L_str s * ψ s) * (s ^ (-1 / 2 : ℝ) * A s)) ≤
          ENNReal.ofReal (2 * C_ramp) *
            ∫⁻ s in Ioo 0 (3 * δ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) := by
        have hIntD : Integrable
            (fun s => (deriv ψ s + 2 * L_str s * ψ s) * (s ^ (-1 / 2 : ℝ) * A s))
            (volume.restrict (Ioi (0 : ℝ))) := by
          have hI1 : Integrable (fun s => deriv ψ s * (s ^ (-1 / 2 : ℝ) * A s))
              (volume.restrict (Ioi (0 : ℝ))) :=
            integrable_contcutoff_mul (hc1.continuous_deriv le_rfl) hδ
              (tsupport_deriv_subset.trans hsupp) (intOn_rpow_mul hδ (hVi δ (2 * H) hδ hδ2H) _)
          have hI2_dom : Integrable (fun s => (2 * M_L) * (ψ s * (s ^ (-1 / 2 : ℝ) * A s)))
              (volume.restrict (Ioi (0 : ℝ))) :=
            (integrable_cutoff_mul hc1 hδ hsupp
              (intOn_rpow_mul hδ (hVi δ (2 * H) hδ hδ2H) _)).const_mul (2 * M_L)
          have hLm : Measurable fun s : ℝ => if 0 < s then L_str s else 0 :=
            AdvectionEnergyAux.measurable_supNormD_one_toReal_ite tr
          have hI2 : Integrable (fun s => (2 * L_str s * ψ s) * (s ^ (-1 / 2 : ℝ) * A s))
              (volume.restrict (Ioi (0 : ℝ))) := by
            refine hI2_dom.mono' ?_ ?_
            · have hcongr : (fun s : ℝ => (2 * L_str s * ψ s) * (s ^ (-1 / 2 : ℝ) * A s))
                  =ᵐ[volume.restrict (Ioi (0 : ℝ))]
                fun s => (2 * (if 0 < s then L_str s else 0) * ψ s) * (s ^ (-1 / 2 : ℝ) * A s) := by
                filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
                have hs0 : 0 < s := hs
                simp [hs0]
              refine AEStronglyMeasurable.congr ?_ hcongr.symm
              exact (((measurable_const.mul hLm).mul hc1.continuous.measurable).aestronglyMeasurable.restrict).mul
                (((measurable_id.pow_const _).aestronglyMeasurable.restrict).mul
                  (sliceLoc c gV hc hgVm hgV0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).1).1.aestronglyMeasurable.restrict)
            · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
              have hs0 : 0 < s := hs
              by_cases hs_mem : s ∈ Icc δ (2 * H)
              · have hLs : L_str s ≤ M_L := hML s ⟨hs0.le, hs_mem.2⟩
                have hLnn : 0 ≤ L_str s := ENNReal.toReal_nonneg
                have hAnn : 0 ≤ s ^ (-1 / 2 : ℝ) * A s :=
                  mul_nonneg (Real.rpow_nonneg hs0.le _) (hnn s).1
                rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (by positivity) (hψ0 s)) hAnn)]
                nlinarith [mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right (by linarith : 2 * L_str s ≤ 2 * M_L) (hψ0 s)) hAnn]
              · have hψz : ψ s = 0 := coreExpRamp_eq_zero_of_not_mem hδ hH hs_mem
                simp [hψz]
          refine (hI1.add hI2).congr (Eventually.of_forall fun s => ?_)
          simp only [Pi.add_apply]; ring
        refine (ofReal_integral_le_lintegral' hIntD).trans ?_
        have hdb := coreExpRamp_strain_deriv_le hKσ0 hKσ hML0 hδ hH2 hML
        calc ∫⁻ s in Ioi (0 : ℝ),
              ENNReal.ofReal ((deriv ψ s + 2 * L_str s * ψ s) * (s ^ (-1 / 2 : ℝ) * A s))
            ≤ ∫⁻ s in Ioi (0 : ℝ), (Ioo (0 : ℝ) (3 * δ)).indicator
                (fun s => ENNReal.ofReal (2 * C_ramp) *
                  ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) s := by
              refine lintegral_mono_ae ?_
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
              have hs0 : 0 < s := hs
              by_cases hmem : s ∈ Icc δ (2 * δ)
              · have hIoo : s ∈ Ioo (0 : ℝ) (3 * δ) := ⟨hs0, by linarith [hmem.2]⟩
                rw [indicator_of_mem hIoo, ← ENNReal.ofReal_mul (by positivity)]
                refine ENNReal.ofReal_le_ofReal ?_
                have hd := hdb s
                rw [indicator_of_mem hmem] at hd
                have hr : s ^ (-1 / 2 : ℝ) = s ^ (-3 / 2 : ℝ) * s := by
                  rw [← Real.rpow_add_one hs0.ne']; norm_num
                have hx : 0 ≤ s ^ (-3 / 2 : ℝ) * A s :=
                  mul_nonneg (Real.rpow_nonneg hs0.le _) (hnn s).1
                have h1 : s ^ (-1 / 2 : ℝ) * A s ≤ 2 * δ * (s ^ (-3 / 2 : ℝ) * A s) := by
                  rw [hr]; nlinarith [mul_le_mul_of_nonneg_right hmem.2 hx]
                have hp : 0 ≤ s ^ (-1 / 2 : ℝ) * A s :=
                  mul_nonneg (Real.rpow_nonneg hs0.le _) (hnn s).1
                calc (deriv ψ s + 2 * L_str s * ψ s) * (s ^ (-1 / 2 : ℝ) * A s)
                    ≤ C_ramp / δ * 1 * (s ^ (-1 / 2 : ℝ) * A s) :=
                      mul_le_mul_of_nonneg_right hd hp
                  _ ≤ C_ramp / δ * 1 * (2 * δ * (s ^ (-3 / 2 : ℝ) * A s)) :=
                      mul_le_mul_of_nonneg_left h1 (by positivity)
                  _ = 2 * C_ramp * (s ^ (-3 / 2 : ℝ) * A s) := by field_simp
              · have hd := hdb s
                rw [indicator_of_notMem hmem, mul_zero] at hd
                have hp : 0 ≤ s ^ (-1 / 2 : ℝ) * A s :=
                  mul_nonneg (Real.rpow_nonneg hs0.le _) (hnn s).1
                rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hd hp)]
                exact zero_le
          _ = ENNReal.ofReal (2 * C_ramp) *
                ∫⁻ s in Ioo 0 (3 * δ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) := by
              have hinter : Ioo (0 : ℝ) (3 * δ) ∩ Ioi 0 = Ioo 0 (3 * δ) :=
                inter_eq_left.2 fun _ hx => hx.1
              rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
                hinter, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have hQ_nn : 0 ≤ ν⁻¹ * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * Q s) := by
        refine mul_nonneg (inv_nonneg.2 hν0.le) (setIntegral_nonneg measurableSet_Ioi fun s hs => ?_)
        exact mul_nonneg (hψ0 s) (mul_nonneg (Real.rpow_nonneg (le_of_lt hs) _) (hnn s).2.2.2)
      have hQ_le : ENNReal.ofReal (ν⁻¹ * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * Q s)) ≤
          ENNReal.ofReal ν⁻¹ * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s) := by
        have iQ : Integrable (fun s => ψ s * (s ^ (-1 / 2 : ℝ) * Q s))
            (volume.restrict (Ioi (0 : ℝ))) :=
          integrable_cutoff_mul hc1 hδ hsupp (intOn_rpow_mul hδ (hQi δ (2 * H) hδ hδ2H) _)
        rw [ENNReal.ofReal_mul (inv_nonneg.2 hν0.le)]
        refine mul_le_mul_of_nonneg_left ((ofReal_integral_le_lintegral' iQ).trans ?_) bot_le
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hs0 : 0 ≤ s := le_of_lt hs
        have hψ1 : ψ s ≤ 1 := coreExpRamp_le_one (by positivity) hs0
        refine ENNReal.ofReal_le_ofReal ?_
        exact mul_le_of_le_one_left (mul_nonneg (Real.rpow_nonneg hs0 _) (hnn s).2.2.2) hψ1
      have hRHS_split : ENNReal.ofReal
            ((∫ s in Ioi (0 : ℝ), (deriv ψ s + 2 * L_str s * ψ s) * (s ^ (-1 / 2 : ℝ) * A s)) +
              ν⁻¹ * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * Q s)) ≤
          ENNReal.ofReal
              (∫ s in Ioi (0 : ℝ), (deriv ψ s + 2 * L_str s * ψ s) * (s ^ (-1 / 2 : ℝ) * A s)) +
            ENNReal.ofReal (ν⁻¹ * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * Q s)) := by
        set X_int := ∫ s in Ioi (0 : ℝ), (deriv ψ s + 2 * L_str s * ψ s) * (s ^ (-1 / 2 : ℝ) * A s)
        set Y_int := ν⁻¹ * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * Q s)
        by_cases hX0 : 0 ≤ X_int
        · rw [ENNReal.ofReal_add hX0 hQ_nn]
        · calc ENNReal.ofReal (X_int + Y_int) ≤ ENNReal.ofReal Y_int :=
                ENNReal.ofReal_le_ofReal (by linarith)
            _ ≤ ENNReal.ofReal X_int + ENNReal.ofReal Y_int := le_add_self
      exact hLHS_le.trans (s2.le.trans ((ENNReal.ofReal_le_ofReal hle).trans
        (hRHS_split.trans (add_le_add hD_le hQ_le))))
    -- Pass `δ_n = a / (3 * (n + 1)) → 0`
    set dseq : ℕ → ℝ := fun n => a / (3 * ((n : ℝ) + 1))
    have hdpos : ∀ n : ℕ, 0 < dseq n := fun n => by unfold dseq; positivity
    have hd2a : ∀ n : ℕ, 2 * dseq n ≤ a := by
      intro n; unfold dseq
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    have hdlim : Tendsto (fun n : ℕ => 3 * dseq n) atTop (𝓝 0) := by
      have heq : (fun n : ℕ => 3 * dseq n) = fun n : ℕ => a * (1 / ((n : ℝ) + 1)) := by
        funext n; unfold dseq; field_simp
      rw [heq]
      have h0 := (tendsto_const_nhds (x := a)).mul tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [mul_zero] at h0
    have hE : Tendsto (fun n => ∫⁻ s in Ioo 0 (3 * dseq n), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s))
        atTop (𝓝 0) := by
      have hE0 : Tendsto (fun n => ∫⁻ s in Ioo 0 (3 * dseq n),
          ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) ∂(volume.restrict (Ioo 0 δ0))) atTop (𝓝 0) := by
        refine tendsto_setLIntegral_zero (μ := volume.restrict (Ioo 0 δ0))
          (f := fun s => ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) hfinA.ne ?_
        have hup : Tendsto (fun n => ENNReal.ofReal (3 * dseq n)) atTop (𝓝 0) := by
          simpa using ENNReal.tendsto_ofReal hdlim
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
          (fun _ => zero_le) fun n => ?_
        calc (volume.restrict (Ioo 0 δ0)) (Ioo 0 (3 * dseq n)) ≤ volume (Ioo 0 (3 * dseq n)) :=
              Measure.restrict_le_self _
          _ = ENNReal.ofReal (3 * dseq n) := by simp
      have hev : ∀ᶠ n : ℕ in atTop, 3 * dseq n < δ0 :=
        (tendsto_order.1 hdlim).2 δ0 (by simpa using hδ0)
      refine hE0.congr' (hev.mono fun n hn => ?_)
      rw [Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.2 (Ioo_subset_Ioo le_rfl hn.le)]
    have hRHS_lim : Tendsto
        (fun n => ENNReal.ofReal (2 * C_ramp) *
            (∫⁻ s in Ioo 0 (3 * dseq n), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) +
          ENNReal.ofReal ν⁻¹ * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s))
        atTop (𝓝 (ENNReal.ofReal ν⁻¹ *
          ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s))) := by
      have h0 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (2 * C_ramp)) hE
        (Or.inr ENNReal.ofReal_ne_top)
      rw [mul_zero] at h0
      simpa only [zero_add] using h0.add tendsto_const_nhds
    exact ge_of_tendsto' hRHS_lim fun n => hdelta (dseq n) (hdpos n) (hd2a n)
  -- Step 2: Monotone exhaustion of `Ioo 0 H` by `Icc (H / (m + 2)) H`
  have hIoo_le : ENNReal.ofReal (Real.exp (-2 * M_L * H) * ν) *
        (∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s)) ≤
      ENNReal.ofReal ν⁻¹ * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s) := by
    let am : ℕ → ℝ := fun m => H / ((m : ℝ) + 2)
    have ham_pos : ∀ m, 0 < am m := fun m => by unfold am; positivity
    have ham_lt : ∀ m, am m < H := by
      intro m; unfold am
      refine div_lt_self hH ?_
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    let fm : ℕ → ℝ → ℝ≥0∞ := fun m =>
      (Icc (am m) H).indicator (fun s => ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s))
    have hNm_meas : Measurable N :=
      (sliceLoc c gN hc hgNm hgN0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).2).1
    have hfm_meas : ∀ m, Measurable (fm m) := fun m =>
      (ENNReal.measurable_ofReal.comp ((measurable_id.pow_const _).mul hNm_meas)).indicator
        measurableSet_Icc
    have hfm_mono : Monotone fm := by
      intro m₁ m₂ hm s
      refine indicator_le_indicator_of_subset (Icc_subset_Icc ?_ le_rfl) (fun _ => bot_le) s
      unfold am
      refine div_le_div_of_nonneg_left hH.le (by positivity) ?_
      have : (m₁ : ℝ) ≤ m₂ := Nat.cast_le.2 hm
      linarith
    have hpt_sup : ∀ s,
        (Ioo (0 : ℝ) H).indicator (fun s => ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s)) s ≤
          ⨆ m : ℕ, fm m s := by
      intro s
      by_cases hs : s ∈ Ioo (0 : ℝ) H
      · rw [indicator_of_mem hs]
        obtain ⟨k, hk⟩ := exists_nat_gt (H / s)
        have hmem : s ∈ Icc (am k) H := by
          refine ⟨?_, hs.2.le⟩
          unfold am
          rw [div_le_iff₀ (by positivity)]
          have hk' : H < (k : ℝ) * s := (div_lt_iff₀ hs.1).1 hk
          nlinarith [hs.1, hk']
        exact le_iSup_of_le k (by simp [fm, hmem])
      · rw [indicator_of_notMem hs]; exact bot_le
    have hsup_int : ∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s) ≤
        ⨆ m : ℕ, ∫⁻ s in Icc (am m) H, ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s) := by
      rw [← lintegral_indicator measurableSet_Ioo]
      calc ∫⁻ s, (Ioo (0 : ℝ) H).indicator (fun s => ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s)) s
          ≤ ∫⁻ s, ⨆ m : ℕ, fm m s := lintegral_mono hpt_sup
        _ = ⨆ m : ℕ, ∫⁻ s, fm m s := lintegral_iSup hfm_meas hfm_mono
        _ = ⨆ m : ℕ, ∫⁻ s in Icc (am m) H, ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s) := by
            refine iSup_congr fun m => lintegral_indicator measurableSet_Icc _
    calc ENNReal.ofReal (Real.exp (-2 * M_L * H) * ν) *
          (∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s))
        ≤ ENNReal.ofReal (Real.exp (-2 * M_L * H) * ν) *
            ⨆ m : ℕ, ∫⁻ s in Icc (am m) H, ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s) :=
          mul_le_mul_of_nonneg_left hsup_int bot_le
      _ = ⨆ m : ℕ, ENNReal.ofReal (Real.exp (-2 * M_L * H) * ν) *
            ∫⁻ s in Icc (am m) H, ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s) := ENNReal.mul_iSup _ _
      _ ≤ ENNReal.ofReal ν⁻¹ * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s) :=
          iSup_le fun m => hIcc_le (am m) (ham_pos m) (ham_lt m)
  -- Step 3: Convert `N` and `Q` integrals to `unnormSliceGrad` and `tCalNorm` via `ageSlice`
  have heqN : ENNReal.ofReal c⁻¹ *
      ∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s) =
      ∫⁻ s in Ioo (0 : ℝ) H,
        ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
          (ENNReal.ofReal c⁻¹ * unnormSliceGrad c (gainConj γ ν Gd) s ^ 2) := by
    have hageN := (ageSlice c (-1 / 2) gN hc hgNm hgN0
      fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).2).2 H
    have hres : ((ageμ c (-1 / 2)).restrict (Ioo 0 H ×ˢ (univ : Set (ℝ × ℝ)))) =
        (ageμ c (-1 / 2)).restrict (Iio H ×ˢ (univ : Set (ℝ × ℝ))) := by
      refine Measure.restrict_congr_set ?_
      filter_upwards [ae_ageμ_mem hc (-1 / 2)] with p hp
      exact propext ⟨fun (h : p ∈ Ioo 0 H ×ˢ univ) => ⟨h.1.2, trivial⟩,
        fun (h : p ∈ Iio H ×ˢ univ) => ⟨⟨hp.1, h.1⟩, trivial⟩⟩
    rw [← hageN, hres, lintegral_Iio_ageμ_eq hc gN hgNm]
    refine setLIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
    have hsq : unnormSliceGrad c (gainConj γ ν Gd) s ^ 2 =
        ∫⁻ x in B0579.cell c, ENNReal.ofReal (gN (s, x)) := by
      unfold unnormSliceGrad gN
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    rw [hsq]
  have heqQ : ENNReal.ofReal c⁻¹ *
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s) =
      tCalNorm c (gainConj γ ν Fd) ^ 2 := by
    rw [normSq.2]
    exact ((ageSlice c (-1 / 2) gQ hc hgQm hgQ0 fun s₁ s₂ h1 h2 => (hFl s₁ s₂ h1 h2).2).1).symm
  have hmul_c := mul_le_mul_of_nonneg_left hIoo_le (bot_le : 0 ≤ ENNReal.ofReal c⁻¹)
  have hL_assoc : ENNReal.ofReal c⁻¹ * (ENNReal.ofReal (Real.exp (-2 * M_L * H) * ν) *
      ∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s)) =
      ENNReal.ofReal (Real.exp (-2 * M_L * H) * ν) *
        (ENNReal.ofReal c⁻¹ * ∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s)) := by
    ring
  have hR_assoc : ENNReal.ofReal c⁻¹ * (ENNReal.ofReal ν⁻¹ *
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s)) =
      ENNReal.ofReal ν⁻¹ *
        (ENNReal.ofReal c⁻¹ * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s)) := by
    ring
  rw [hL_assoc, heqN, hR_assoc, heqQ] at hmul_c
  set LHS_G := ∫⁻ s in Ioo (0 : ℝ) H,
    ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
      (ENNReal.ofReal c⁻¹ * unnormSliceGrad c (gainConj γ ν Gd) s ^ 2)
  have hinv_cancel : (Real.exp (2 * M_L * H) * ν⁻¹) * (Real.exp (-2 * M_L * H) * ν) = 1 := by
    have hexp_mul : Real.exp (2 * M_L * H) * Real.exp (-2 * M_L * H) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    calc (Real.exp (2 * M_L * H) * ν⁻¹) * (Real.exp (-2 * M_L * H) * ν)
        = (Real.exp (2 * M_L * H) * Real.exp (-2 * M_L * H)) * (ν⁻¹ * ν) := by ring
      _ = 1 * 1 := by rw [hexp_mul, inv_mul_cancel₀ hν0.ne']
      _ = 1 := one_mul 1
  calc LHS_G
      = ENNReal.ofReal ((Real.exp (2 * M_L * H) * ν⁻¹) * (Real.exp (-2 * M_L * H) * ν)) * LHS_G := by
        rw [hinv_cancel, ENNReal.ofReal_one, one_mul]
    _ = ENNReal.ofReal (Real.exp (2 * M_L * H) * ν⁻¹) *
          (ENNReal.ofReal (Real.exp (-2 * M_L * H) * ν) * LHS_G) := by
        rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ ≤ ENNReal.ofReal (Real.exp (2 * M_L * H) * ν⁻¹) *
          (ENNReal.ofReal ν⁻¹ * tCalNorm c (gainConj γ ν Fd) ^ 2) :=
        mul_le_mul_of_nonneg_left hmul_c bot_le
    _ = ENNReal.ofReal (Real.exp (2 * M_L * H) * (ν ^ 2)⁻¹) *
          tCalNorm c (gainConj γ ν Fd) ^ 2 := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp [hν0.ne']

/-! ## 7. `L²(cell c)` vorticity perturbation bound -/

private theorem eLpNorm_curl_slice_le {c : ℝ} {T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} (s : ℝ) :
    eLpNorm (fun x => T (s, x) 1 0 - T (s, x) 0 1) 2 (volume.restrict (B0579.cell c)) ≤
      ENNReal.ofReal (Real.sqrt 2) * unnormSliceGrad c T s := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  norm_num
  have hpt : ∀ x : ℝ × ℝ,
      ‖T (s, x) 1 0 - T (s, x) 0 1‖ₑ ^ 2 ≤
        ENNReal.ofReal 2 * ENNReal.ofReal (tnorm2 (T (s, x)) ^ 2) := by
    intro x
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul zero_le_two]
    refine ENNReal.ofReal_le_ofReal ?_
    have htri : ‖T (s, x) 1 0 - T (s, x) 0 1‖ ≤ ‖T (s, x) 1 0‖ + ‖T (s, x) 0 1‖ :=
      norm_sub_le _ _
    have hsq1 : ‖T (s, x) 1 0 - T (s, x) 0 1‖ ^ 2 ≤ (‖T (s, x) 1 0‖ + ‖T (s, x) 0 1‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hsq2 : (‖T (s, x) 1 0‖ + ‖T (s, x) 0 1‖) ^ 2 ≤
        2 * (‖T (s, x) 1 0‖ ^ 2 + ‖T (s, x) 0 1‖ ^ 2) := by
      nlinarith [sq_nonneg (‖T (s, x) 1 0‖ - ‖T (s, x) 0 1‖)]
    have htsq : tnorm2 (T (s, x)) ^ 2 =
        (‖T (s, x) 0 0‖ ^ 2 + ‖T (s, x) 0 1‖ ^ 2) +
          (‖T (s, x) 1 0‖ ^ 2 + ‖T (s, x) 1 1‖ ^ 2) := by
      unfold tnorm2
      rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _),
        Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    rw [htsq]
    nlinarith [sq_nonneg ‖T (s, x) 0 0‖, sq_nonneg ‖T (s, x) 1 1‖]
  calc (∫⁻ x in B0579.cell c, ‖T (s, x) 1 0 - T (s, x) 0 1‖ₑ ^ 2) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ x in B0579.cell c,
          ENNReal.ofReal 2 * ENNReal.ofReal (tnorm2 (T (s, x)) ^ 2)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (lintegral_mono hpt) (by norm_num)
    _ = (ENNReal.ofReal 2 *
          ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (T (s, x)) ^ 2)) ^ (1 / 2 : ℝ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal 2 ^ (1 / 2 : ℝ) * unnormSliceGrad c T s := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]; rfl
    _ = ENNReal.ofReal (Real.sqrt 2) * unnormSliceGrad c T s := by
        rw [ENNReal.ofReal_rpow_of_nonneg zero_le_two (by norm_num), ← Real.sqrt_eq_rpow]

private theorem eLpNorm_corePerturbVort_sub_le {c γ ν : ℝ}
    {G₀₁ G_sol₁ G₀₂ G_sol₂ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hG₀₁ : ∀ i j, Measurable fun p => G₀₁ p i j)
    (hG_sol₁ : ∀ i j, Measurable fun p => G_sol₁ p i j)
    (hG₀₂ : ∀ i j, Measurable fun p => G₀₂ p i j)
    (hG_sol₂ : ∀ i j, Measurable fun p => G_sol₂ p i j) (s : ℝ) :
    eLpNorm (fun x => corePerturbVort γ ν G₀₁ G_sol₁ s x - corePerturbVort γ ν G₀₂ G_sol₂ s x) 2
        (volume.restrict (B0579.cell c)) ≤
      ENNReal.ofReal (Real.sqrt 2) *
        (unnormSliceGrad c (gainConj γ ν (fun p i j => G_sol₁ p i j - G_sol₂ p i j)) s +
          unnormSliceGrad c (gainConj γ ν (fun p i j => G₀₁ p i j - G₀₂ p i j)) s) := by
  let Ts : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ :=
    gainConj γ ν (fun p i j => G_sol₁ p i j - G_sol₂ p i j)
  let T0 : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ :=
    gainConj γ ν (fun p i j => G₀₁ p i j - G₀₂ p i j)
  have heq : (fun x => corePerturbVort γ ν G₀₁ G_sol₁ s x - corePerturbVort γ ν G₀₂ G_sol₂ s x) =
      (fun x => Ts (s, x) 1 0 - Ts (s, x) 0 1) - (fun x => T0 (s, x) 1 0 - T0 (s, x) 0 1) := by
    funext x
    simp only [Pi.sub_apply, corePerturbVort, corePerturbGrad, Ts, T0, gainConj,
      Pi.smul_apply, Complex.real_smul]
    ring
  have hTs_m : Measurable fun x => Ts (s, x) 1 0 - Ts (s, x) 0 1 := by
    have hm := measurable_gainConj_ten γ ν (fun i j => (hG_sol₁ i j).sub (hG_sol₂ i j))
    exact ((hm 1 0).comp measurable_prodMk_left).sub ((hm 0 1).comp measurable_prodMk_left)
  have hT0_m : Measurable fun x => T0 (s, x) 1 0 - T0 (s, x) 0 1 := by
    have hm := measurable_gainConj_ten γ ν (fun i j => (hG₀₁ i j).sub (hG₀₂ i j))
    exact ((hm 1 0).comp measurable_prodMk_left).sub ((hm 0 1).comp measurable_prodMk_left)
  rw [heq]
  calc eLpNorm ((fun x => Ts (s, x) 1 0 - Ts (s, x) 0 1) -
          (fun x => T0 (s, x) 1 0 - T0 (s, x) 0 1)) 2 (volume.restrict (B0579.cell c))
      ≤ eLpNorm (fun x => Ts (s, x) 1 0 - Ts (s, x) 0 1) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun x => T0 (s, x) 1 0 - T0 (s, x) 0 1) 2 (volume.restrict (B0579.cell c)) :=
        eLpNorm_sub_le hTs_m.aestronglyMeasurable hT0_m.aestronglyMeasurable one_le_two
    _ ≤ ENNReal.ofReal (Real.sqrt 2) * unnormSliceGrad c Ts s +
          ENNReal.ofReal (Real.sqrt 2) * unnormSliceGrad c T0 s :=
        add_le_add (eLpNorm_curl_slice_le s) (eLpNorm_curl_slice_le s)
    _ = ENNReal.ofReal (Real.sqrt 2) * (unnormSliceGrad c Ts s + unnormSliceGrad c T0 s) := by
        rw [mul_add]

private theorem teleLimit_duhamel_rep {c γ ν s : ℝ}
    {G₀ G_sol : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {G₀n G_sol_n : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hG₀m : ∀ i j, Measurable fun p => G₀ p i j)
    (hGsolm : ∀ i j, Measurable fun p => G_sol p i j)
    (hG₀nm : ∀ n i j, Measurable fun p => G₀n n p i j)
    (hGsolnm : ∀ n i j, Measurable fun p => G_sol_n n p i j)
    {ks : ℕ → ℝ → ℝ × ℝ → ℂ}
    (hks_m : ∀ n, Measurable (Function.uncurry (ks n)))
    (hks_rep : ∀ n, corePerturbVort γ ν (G₀n n) (G_sol_n n) s
      =ᵐ[volume.restrict (B0579.cell c)] fun x => ∫ t in Ioo 0 s, ks n t x)
    (hsum_diff : (∑' n : ℕ, ∫⁻ t in Ioo (0 : ℝ) s,
      xNorm c 9 (fun x => ks (n + 1) t x - ks n t x)) < ⊤)
    (hks0_int_lt : ∫⁻ t in Ioo (0 : ℝ) s, xNorm c 9 (ks 0 t) < ⊤)
    (hs_G0_lim : Tendsto
      (fun n => unnormSliceGrad c (gainConj γ ν (fun p i j => G₀n n p i j - G₀ p i j)) s)
      atTop (𝓝 0))
    (hs_Gsol_lim : Tendsto
      (fun n => unnormSliceGrad c (gainConj γ ν (fun p i j => G_sol_n n p i j - G_sol p i j)) s)
      atTop (𝓝 0)) :
    corePerturbVort γ ν G₀ G_sol s =ᵐ[volume.restrict (B0579.cell c)]
      fun x => ∫ t in Ioo 0 s, teleLimit ks t x := by
  have hkm : Measurable (Function.uncurry (teleLimit ks)) := measurable_uncurry_teleLimit hks_m
  have hm_xndiff : ∀ n, Measurable fun t : ℝ => xNorm c 9 (fun x => ks (n + 1) t x - ks n t x) :=
    fun n => measurable_xNorm_slice c ((hks_m (n + 1)).sub (hks_m n))
  have hae_t_sum : ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) s →
      (∑' n : ℕ, xNorm c 9 (fun x => ks (n + 1) t x - ks n t x)) < ⊤ := by
    have htot : ∫⁻ t in Ioo (0 : ℝ) s,
        ∑' n : ℕ, xNorm c 9 (fun x => ks (n + 1) t x - ks n t x) < ⊤ := by
      rw [lintegral_tsum fun n => (hm_xndiff n).aemeasurable]
      exact hsum_diff
    have hae := ae_lt_top (Measurable.tsum hm_xndiff) htot.ne
    rwa [ae_restrict_iff' measurableSet_Ioo] at hae
  have hint_err : ∀ N : ℕ,
      ∫⁻ t in Ioo (0 : ℝ) s, xNorm c 9 (fun x => teleLimit ks t x - ks N t x) ≤
        ∑' m : ℕ, ∫⁻ t in Ioo (0 : ℝ) s,
          xNorm c 9 (fun x => ks (N + m + 1) t x - ks (N + m) t x) := by
    intro N
    rw [← lintegral_tsum fun m => (hm_xndiff (N + m)).aemeasurable]
    refine setLIntegral_mono_ae' measurableSet_Ioo ?_
    filter_upwards [hae_t_sum] with t ht hts
    exact xNorm_teleLimit_sub_le hks_m (ht hts) N
  have hint_err_lim : Tendsto
      (fun N => ∫⁻ t in Ioo (0 : ℝ) s, xNorm c 9 (fun x => teleLimit ks t x - ks N t x))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ennreal_tsum_nat_add_tendsto_zero hsum_diff.ne) (fun _ => bot_le) hint_err
  have hk_int_lt : ∫⁻ t in Ioo (0 : ℝ) s, xNorm c 9 (teleLimit ks t) < ⊤ := by
    have hm_sub0 : Measurable fun t : ℝ => xNorm c 9 (fun x => teleLimit ks t x - ks 0 t x) :=
      measurable_xNorm_slice c (hkm.sub (hks_m 0))
    have htri : ∀ t, xNorm c 9 (teleLimit ks t) ≤
        xNorm c 9 (fun x => teleLimit ks t x - ks 0 t x) + xNorm c 9 (ks 0 t) := fun t =>
      xNorm_le_sub_add c (hkm.comp (measurable_const.prodMk measurable_id))
        ((hks_m 0).comp (measurable_const.prodMk measurable_id))
    calc ∫⁻ t in Ioo (0 : ℝ) s, xNorm c 9 (teleLimit ks t)
        ≤ ∫⁻ t in Ioo (0 : ℝ) s,
            (xNorm c 9 (fun x => teleLimit ks t x - ks 0 t x) + xNorm c 9 (ks 0 t)) :=
          lintegral_mono htri
      _ = (∫⁻ t in Ioo (0 : ℝ) s, xNorm c 9 (fun x => teleLimit ks t x - ks 0 t x)) +
            ∫⁻ t in Ioo (0 : ℝ) s, xNorm c 9 (ks 0 t) :=
          lintegral_add_left hm_sub0 _
      _ < ⊤ := ENNReal.add_lt_top.2
          ⟨(hint_err 0).trans_lt (by simpa only [zero_add] using hsum_diff), hks0_int_lt⟩
  have hksN_int_lt : ∀ N : ℕ, ∫⁻ t in Ioo (0 : ℝ) s, xNorm c 9 (ks N t) < ⊤ := by
    intro N
    have hm_k : Measurable fun t : ℝ => xNorm c 9 (teleLimit ks t) :=
      measurable_xNorm_slice c hkm
    have htri : ∀ t, xNorm c 9 (ks N t) ≤
        xNorm c 9 (teleLimit ks t) + xNorm c 9 (fun x => teleLimit ks t x - ks N t x) := fun t =>
      xNorm_le_add_sub c (hkm.comp (measurable_const.prodMk measurable_id))
        ((hks_m N).comp (measurable_const.prodMk measurable_id))
    calc ∫⁻ t in Ioo (0 : ℝ) s, xNorm c 9 (ks N t)
        ≤ (∫⁻ t in Ioo (0 : ℝ) s, xNorm c 9 (teleLimit ks t)) +
            ∫⁻ t in Ioo (0 : ℝ) s, xNorm c 9 (fun x => teleLimit ks t x - ks N t x) := by
          rw [← lintegral_add_left hm_k]
          exact lintegral_mono htri
      _ < ⊤ := ENNReal.add_lt_top.2
          ⟨hk_int_lt, (hint_err N).trans_lt
            (lt_of_le_of_lt
              (ENNReal.tsum_comp_le_tsum_of_injective (add_right_injective N)
                (fun n => ∫⁻ t in Ioo (0 : ℝ) s, xNorm c 9 (fun x => ks (n + 1) t x - ks n t x)))
              hsum_diff)⟩
  set C_jb : ℝ≥0∞ :=
    (∫⁻ x in B0579.cell c, ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ))) ^ (1 / 2 : ℝ)
  have hCjb_lt : C_jb < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) (V3.lint_jb_cell_lt_top c).ne
  have hprod_int_of : ∀ {g : ℝ → ℝ × ℝ → ℂ}, Measurable (Function.uncurry g) →
      ∫⁻ t in Ioo (0 : ℝ) s, xNorm c 9 (g t) < ⊤ →
      Integrable (Function.uncurry g)
        ((volume.restrict (Ioo (0 : ℝ) s)).prod (volume.restrict (B0579.cell c))) := by
    intro g hgm hg_lt
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod _ hgm.enorm.aemeasurable]
    have hgt : ∀ t, AEMeasurable (g t) (B0579.cellMeasure c 9) := fun t =>
      (hgm.comp (measurable_const.prodMk measurable_id)).aemeasurable
    calc ∫⁻ t in Ioo (0 : ℝ) s, ∫⁻ x in B0579.cell c, ‖g t x‖ₑ
        ≤ ∫⁻ t in Ioo (0 : ℝ) s, xNorm c 9 (g t) * C_jb :=
          lintegral_mono fun t => V3.lint_cell_le (hgt t)
      _ = (∫⁻ t in Ioo (0 : ℝ) s, xNorm c 9 (g t)) * C_jb :=
          lintegral_mul_const' _ _ hCjb_lt.ne
      _ < ⊤ := ENNReal.mul_lt_top hg_lt hCjb_lt
  have hint_k_prod := hprod_int_of hkm hk_int_lt
  have hint_ksN_prod : ∀ N, Integrable (Function.uncurry (ks N))
      ((volume.restrict (Ioo (0 : ℝ) s)).prod (volume.restrict (B0579.cell c))) :=
    fun N => hprod_int_of (hks_m N) (hksN_int_lt N)
  set I_k : ℝ × ℝ → ℂ := fun x => ∫ t in Ioo 0 s, teleLimit ks t x
  set I_ks : ℕ → ℝ × ℝ → ℂ := fun N x => ∫ t in Ioo 0 s, ks N t x
  set om : ℝ × ℝ → ℂ := corePerturbVort γ ν G₀ G_sol s
  set om_n : ℕ → ℝ × ℝ → ℂ := fun N => corePerturbVort γ ν (G₀n N) (G_sol_n N) s
  have hIk_aesm : AEStronglyMeasurable I_k (volume.restrict (B0579.cell c)) :=
    hint_k_prod.integral_prod_right.1
  have hIks_aesm : ∀ N, AEStronglyMeasurable (I_ks N) (volume.restrict (B0579.cell c)) :=
    fun N => (hint_ksN_prod N).integral_prod_right.1
  have hom_m : Measurable om := by
    have hm := measurable_corePerturbGrad γ ν hG₀m hGsolm
    exact ((hm 1 0).comp measurable_prodMk_left).sub ((hm 0 1).comp measurable_prodMk_left)
  have homn_m : ∀ N, Measurable (om_n N) := by
    intro N
    have hm := measurable_corePerturbGrad γ ν (hG₀nm N) (hGsolnm N)
    exact ((hm 1 0).comp measurable_prodMk_left).sub ((hm 0 1).comp measurable_prodMk_left)
  have hI_lim : Tendsto (fun N => eLpNorm (I_ks N - I_k) 2 (volume.restrict (B0579.cell c)))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hint_err_lim
      (fun _ => bot_le) fun N => ?_
    have hae_sub : (I_ks N - I_k) =ᵐ[volume.restrict (B0579.cell c)]
        fun x => ∫ t in Ioo 0 s, (ks N t x - teleLimit ks t x) := by
      filter_upwards [(hint_ksN_prod N).prod_left_ae, hint_k_prod.prod_left_ae] with x hxN hxk
      simp only [Pi.sub_apply, I_ks, I_k]
      exact (integral_sub hxN hxk).symm
    have hdiff_swap : AEStronglyMeasurable
        (Function.uncurry fun (x : ℝ × ℝ) (t : ℝ) => ks N t x - teleLimit ks t x)
        ((B0579.cellMeasure c 9).prod (volume.restrict (Ioo (0 : ℝ) s))) :=
      (((hks_m N).sub hkm).comp measurable_swap).aestronglyMeasurable
    have hmink := UnforcedLeray.PlanarBS.Conv.eLpNorm_integral_le (μ := B0579.cellMeasure c 9)
      (ν := volume.restrict (Ioo (0 : ℝ) s)) hdiff_swap (p := 2) (by norm_num) (by norm_num)
    calc eLpNorm (I_ks N - I_k) 2 (volume.restrict (B0579.cell c))
        = eLpNorm (fun x => ∫ t in Ioo 0 s, (ks N t x - teleLimit ks t x)) 2
            (volume.restrict (B0579.cell c)) :=
          eLpNorm_congr_ae hae_sub
      _ ≤ xNorm c 9 (fun x => ∫ t in Ioo 0 s, (ks N t x - teleLimit ks t x)) :=
          eLpNorm_cell_le_xNorm (((hIks_aesm N).sub hIk_aesm).congr hae_sub)
      _ ≤ ∫⁻ t in Ioo (0 : ℝ) s,
            eLpNorm (fun x => ks N t x - teleLimit ks t x) 2 (B0579.cellMeasure c 9) := hmink
      _ = ∫⁻ t in Ioo (0 : ℝ) s, xNorm c 9 (fun x => teleLimit ks t x - ks N t x) := by
          refine lintegral_congr fun t => ?_
          rw [xNorm]
          have hneg : (fun x => ks N t x - teleLimit ks t x) =
              -(fun x => teleLimit ks t x - ks N t x) := by
            funext x; simp
          rw [hneg, eLpNorm_neg]
  have hom_lim : Tendsto (fun N => eLpNorm (om - om_n N) 2 (volume.restrict (B0579.cell c)))
      atTop (𝓝 0) := by
    have hsum_lim : Tendsto
        (fun N => ENNReal.ofReal (Real.sqrt 2) *
          (unnormSliceGrad c (gainConj γ ν (fun p i j => G_sol_n N p i j - G_sol p i j)) s +
            unnormSliceGrad c (gainConj γ ν (fun p i j => G₀n N p i j - G₀ p i j)) s))
        atTop (𝓝 0) := by
      have hadd0 : Tendsto
          (fun N => unnormSliceGrad c (gainConj γ ν (fun p i j => G_sol_n N p i j - G_sol p i j)) s +
            unnormSliceGrad c (gainConj γ ν (fun p i j => G₀n N p i j - G₀ p i j)) s)
          atTop (𝓝 0) := by
        simpa only [add_zero] using hs_Gsol_lim.add hs_G0_lim
      have h0 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Real.sqrt 2)) hadd0
        (Or.inr ENNReal.ofReal_ne_top)
      rwa [mul_zero] at h0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum_lim
      (fun _ => bot_le) fun N => ?_
    have hneg : om - om_n N = -(om_n N - om) := by funext x; simp
    rw [hneg, eLpNorm_neg]
    exact eLpNorm_corePerturbVort_sub_le (hG₀nm N) (hGsolnm N) hG₀m hGsolm s
  have hnorm_zero : eLpNorm (om - I_k) 2 (volume.restrict (B0579.cell c)) = 0 := by
    have hrhs_lim : Tendsto
        (fun N => eLpNorm (om - om_n N) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (I_ks N - I_k) 2 (volume.restrict (B0579.cell c)))
        atTop (𝓝 0) := by
      simpa using hom_lim.add hI_lim
    refine le_antisymm (ge_of_tendsto' hrhs_lim fun N => ?_) bot_le
    have hae_eq : om - I_k =ᵐ[volume.restrict (B0579.cell c)] (om - om_n N) + (I_ks N - I_k) := by
      filter_upwards [hks_rep N] with x hx
      simp only [Pi.sub_apply, Pi.add_apply, om_n, I_ks] at hx ⊢
      rw [hx]
      ring
    rw [eLpNorm_congr_ae hae_eq]
    exact eLpNorm_add_le (hom_m.sub (homn_m N)).aestronglyMeasurable
      ((hIks_aesm N).sub hIk_aesm) one_le_two
  have hae_sub_zero := (eLpNorm_eq_zero_iff
    (hom_m.aestronglyMeasurable.sub hIk_aesm) two_ne_zero).1 hnorm_zero
  filter_upwards [hae_sub_zero] with x hx
  exact sub_eq_zero.1 hx

end CoreDuhamelDensityAux

namespace UnforcedLeray.Short.IIIa

/-- **Leaf (ii) `CoreDuhamelDensity`** (`PartIII-a:T19/2/3/2/3/1/2`, SP 3427-3440, 3481-3496,
3518-3527): passage to the `Z^{-1}_{9,c}` density limit along a geometrically converging sequence
of nice forces (`NiceDuhamelApprox`). -/
theorem coreDuhamelDensity_proof : UnforcedLeray.Short.IIIa.CoreDuhamelDensity := by
  intro P hP K hK b hb
  obtain ⟨ν_free, hν_free, hFreeEB⟩ := freeCausalEnergyBound P hP K hK
  obtain ⟨ν_fin, hν_fin, hFinSrc⟩ := coreSourceFinite_proof 8 (by norm_num) P hP K hK b hb
  set ν_lim : ℝ := min (min ν_free ν_fin) (min (1 / 2) ((2 * b)⁻¹))
  have hν_lim : 0 < ν_lim :=
    lt_min (lt_min hν_free hν_fin) (lt_min (by norm_num) (inv_pos.2 (by linarith)))
  refine ⟨ν_lim, hν_lim,
    fun ν hν tr μ A_m C_clock _hclock F b₀ G₀ b_sol G_sol hd _hweak
      Fn b₀n G₀n b_sol_n G_sol_n happrox => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hν_le_free : ν ≤ ν_free := hν.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_le_fin : ν ≤ ν_fin := hν.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_half : ν ≤ 1 / 2 := hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_2b : ν ≤ (2 * b)⁻¹ := hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν0 _
  let γ : ℝ := P.eigenvalue.re
  have hγ : 0 ≤ γ := hP.eigenpair.re_pos.le
  let H : ℝ := coreEnd ν b
  have hH : 0 < H := zero_lt_one.trans (coreEnd_bounds hb hν0 hν_half hν_2b).1
  obtain ⟨hbuc, hμ, hAm, hbd, hFsym, hFmeas, hFtc, hfree, hsol⟩ := hd
  obtain ⟨hhd_n, hFn_err, happrox_s⟩ := happrox
  have hμ_pos : 0 < μ.re := (hK.2 μ hμ).1
  have hk_ge : (1 / 4 : ℝ) ≤ ⨅ μ' : K, μ'.1.re + 1 / 4 :=
    kStar_ge hμ (fun μ' h => (hK.2 μ' h).1)
  set C_fv : ℝ := (2 * Real.sqrt ((⨅ μ' : K, μ'.1.re + 1 / 4) * ν))⁻¹
  set C_fg : ℝ := ν⁻¹
  have hCfv_nn : 0 ≤ C_fv := by
    unfold C_fv
    exact inv_nonneg.2 (mul_nonneg zero_le_two (Real.sqrt_nonneg _))
  have hCfg_nn : 0 ≤ C_fg := inv_nonneg.2 hν0.le
  -- Step 1: Free causal difference bounds (against `(b₀, G₀)` and consecutive `n + 1` vs `n`)
  let Fd : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun n p i j => Fn n p i j - F p i j
  let b₀d : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun n p i => b₀n n p i - b₀ p i
  let G₀d : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun n p i j => G₀n n p i j - G₀ p i j
  let b_sold : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun n p i => b_sol_n n p i - b_sol p i
  let G_sold : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ :=
    fun n p i j => G_sol_n n p i j - G_sol p i j
  have hFn_sym : ∀ n p i j, Fn n p i j = Fn n p j i := fun n => (hhd_n n).2.2.2.2.1
  have hFn_meas : ∀ n i j, Measurable fun p => Fn n p i j := fun n => (hhd_n n).2.2.2.2.2.1
  have hfree_n : ∀ n, IsCausalEnergySolution c ν μ (fun _ _ _ => 0) (Fn n) (b₀n n) (G₀n n) :=
    fun n => (hhd_n n).2.2.2.2.2.2.2.1
  have hsol_n : ∀ n, IsCausalEnergySolution c ν μ (trainVel tr) (Fn n) (b_sol_n n) (G_sol_n n) :=
    fun n => (hhd_n n).2.2.2.2.2.2.2.2
  have hFd_eb : ∀ n,
      hCalNorm c (gainConj γ ν (b₀d n)) ≤ ENNReal.ofReal C_fv * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) ∧
      tCalNorm c (gainConj γ ν (G₀d n)) ≤ ENNReal.ofReal C_fg * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
    intro n
    have hsym : ∀ p i j, Fd n p i j = Fd n p j i := fun p i j => by
      simp [Fd, hFn_sym n p i j, hFsym p i j]
    have hmeas : ∀ i j, Measurable fun p => Fd n p i j := fun i j => (hFn_meas n i j).sub (hFmeas i j)
    have htc : tCalNorm c (gainConj γ ν (Fd n)) < ⊤ := (hFn_err n).trans_lt ENNReal.ofReal_lt_top
    have hsub_sol := causalSolSub c ν μ (fun _ _ _ => 0) (Fn n) F (b₀n n) b₀ (G₀n n) G₀
      (hfree_n n) hfree
    obtain ⟨h1, h2⟩ := hFreeEB ν ⟨hν0, hν_le_free⟩ μ hμ (Fd n) hsym hmeas htc (b₀d n) (G₀d n) hsub_sol
    exact ⟨h1.trans (mul_le_mul_of_nonneg_left (hFn_err n) bot_le),
      h2.trans (mul_le_mul_of_nonneg_left (hFn_err n) bot_le)⟩
  -- Consecutive differences `ΔF n`, `Δb₀ n`, `ΔG₀ n`
  let ΔF : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun n p i j => Fn (n + 1) p i j - Fn n p i j
  let Δb₀ : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun n p i => b₀n (n + 1) p i - b₀n n p i
  let ΔG₀ : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun n p i j => G₀n (n + 1) p i j - G₀n n p i j
  let Δbs : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun n p i => b_sol_n (n + 1) p i - b_sol_n n p i
  let ΔGs : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ :=
    fun n p i j => G_sol_n (n + 1) p i j - G_sol_n n p i j
  have hΔF_err : ∀ n, tCalNorm c (gainConj γ ν (ΔF n)) ≤
      ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ n) := by
    intro n
    have htri := tCalNormTriangle c ν γ (Fn (n + 1)) F (Fn n)
      (hFn_meas (n + 1)) hFmeas (hFn_meas n)
    calc tCalNorm c (gainConj γ ν (ΔF n))
        ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) + ENNReal.ofReal ((1 / 2 : ℝ) ^ n) :=
          htri.trans (add_le_add (hFn_err (n + 1)) (hFn_err n))
      _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1) + (1 / 2 : ℝ) ^ n) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ n) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [pow_succ]
          have : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
          linarith
  have hΔ_vort : ∀ n, VortData P K b ν tr μ A_m (ΔF n) (Δb₀ n) (ΔG₀ n) (Δbs n) (ΔGs n) := by
    intro n
    refine ⟨hbuc, hμ, hAm, hbd,
      fun p i j => by simp [ΔF, hFn_sym (n + 1) p i j, hFn_sym n p i j],
      fun i j => (hFn_meas (n + 1) i j).sub (hFn_meas n i j),
      (hΔF_err n).trans_lt ENNReal.ofReal_lt_top,
      causalSolSub c ν μ (fun _ _ _ => 0) (Fn (n + 1)) (Fn n) (b₀n (n + 1)) (b₀n n)
        (G₀n (n + 1)) (G₀n n) (hfree_n (n + 1)) (hfree_n n),
      causalSolSub c ν μ (trainVel tr) (Fn (n + 1)) (Fn n) (b_sol_n (n + 1)) (b_sol_n n)
        (G_sol_n (n + 1)) (G_sol_n n) (hsol_n (n + 1)) (hsol_n n)⟩
  have hΔ_eb : ∀ n,
      hCalNorm c (gainConj γ ν (Δb₀ n)) ≤
        ENNReal.ofReal (2 * C_fv) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) ∧
      tCalNorm c (gainConj γ ν (ΔG₀ n)) ≤
        ENNReal.ofReal (2 * C_fg) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
    intro n
    obtain ⟨_, _, _, _, hsym, hmeas, htc, hsub_free, _⟩ := hΔ_vort n
    obtain ⟨h1, h2⟩ := hFreeEB ν ⟨hν0, hν_le_free⟩ μ hμ (ΔF n) hsym hmeas htc (Δb₀ n) (ΔG₀ n)
      hsub_free
    have hfac1 : ENNReal.ofReal C_fv * ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ n) =
        ENNReal.ofReal (2 * C_fv) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
      rw [← ENNReal.ofReal_mul hCfv_nn, ← ENNReal.ofReal_mul (mul_nonneg zero_le_two hCfv_nn)]
      ring_nf
    have hfac2 : ENNReal.ofReal C_fg * ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ n) =
        ENNReal.ofReal (2 * C_fg) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
      rw [← ENNReal.ofReal_mul hCfg_nn, ← ENNReal.ofReal_mul (mul_nonneg zero_le_two hCfg_nn)]
      ring_nf
    exact ⟨(h1.trans (mul_le_mul_of_nonneg_left (hΔF_err n) bot_le)).trans_eq hfac1,
      (h2.trans (mul_le_mul_of_nonneg_left (hΔF_err n) bot_le)).trans_eq hfac2⟩
  -- Step 2: Summability of Duhamel difference upper bounds for a.e. `s ∈ (0, H)`
  let M_Δ : ℕ → ℝ → ℝ≥0∞ := fun n t =>
    ENNReal.ofReal (8 * A_m) *
      (unnormSliceVel c (gainConj γ ν (Δb₀ n)) t + unnormSliceGrad c (gainConj γ ν (ΔG₀ n)) t)
  have hMΔ_meas : ∀ n, Measurable (M_Δ n) := by
    intro n
    have hbm := measurable_gainConj_vec (γ := γ) (ν := ν) (hΔ_vort n).2.2.2.2.2.2.2.1.measurable
    have hGm := measurable_gainConj_ten γ ν (hΔ_vort n).2.2.2.2.2.2.2.1.gradMeasurable
    exact measurable_const.mul ((measurable_unnormSliceVel c hbm).add (measurable_unnormSliceGrad c hGm))
  have hsrc_Δ : ∀ n, ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) H →
      coreSrcNorm c 9 (coreAdvSlice γ tr (Δb₀ n) (ΔG₀ n) t) ≤ M_Δ n t :=
    fun n => coreSourceNegBound 8 (by norm_num) CoreDuhamelDensityAux.cDualClause_eight
      P hP K hK b hb ν hν0 tr μ A_m (ΔF n) (Δb₀ n) (ΔG₀ n) (Δbs n) (ΔGs n) (hΔ_vort n)
  let I_Δ : ℕ → ℝ → ℝ≥0∞ := fun n s =>
    ∫⁻ t in Ioo (0 : ℝ) s, ENNReal.ofReal (vortKernel C_clock P ν μ s t) * M_Δ n t
  have hIΔ_meas : ∀ n, Measurable (I_Δ n) := by
    intro n
    let Ψ : ℝ → ℝ → ℝ≥0∞ := fun s t =>
      if 0 < t ∧ t < s then ENNReal.ofReal (vortKernel C_clock P ν μ s t) * M_Δ n t else 0
    have hΨm : Measurable (Function.uncurry Ψ) := by
      have hset : MeasurableSet {q : ℝ × ℝ | 0 < q.2 ∧ q.2 < q.1} :=
        (measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_lt measurable_snd measurable_fst)
      have hvort_m : Measurable fun q : ℝ × ℝ =>
          ENNReal.ofReal (vortKernel C_clock P ν μ q.1 q.2) * M_Δ n q.2 := by
        unfold vortKernel
        exact (ENNReal.measurable_ofReal.comp
          (((measurable_const.mul ((measurable_snd.div measurable_fst).pow_const _)).mul
            (measurable_const.add ((measurable_fst.sub measurable_snd).pow_const _))))).mul
          ((hMΔ_meas n).comp measurable_snd)
      exact Measurable.ite hset hvort_m measurable_const
    have heq : I_Δ n = fun s => ∫⁻ t, Ψ s t := by
      funext s
      dsimp only [I_Δ]
      rw [← lintegral_indicator measurableSet_Ioo]
      refine lintegral_congr fun t => ?_
      by_cases ht : t ∈ Ioo (0 : ℝ) s
      · simp [Ψ, ht, ht.1, ht.2]
      · have hnot : ¬(0 < t ∧ t < s) := ht
        simp [Ψ, ht, hnot]
    rw [heq]
    exact hΨm.lintegral_prod_right'
  have hsum_IΔ_ae : ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) H → (∑' n : ℕ, I_Δ n s) < ⊤ := by
    set C_slice : ℝ := 8 * A_m *
      ((c * (2 * C_fv) ^ 2 + H * H ^ (3 / 2 : ℝ)) +
        (c * (2 * C_fg) ^ 2 + H * H ^ (1 / 2 : ℝ)))
    set C_ker : ℝ := |C_clock| * ν ^ (-(weakDegree 9 P.kappa : ℝ)) * (H + 2 * Real.sqrt H)
    have hCslice_nn : 0 ≤ C_slice := by unfold C_slice; positivity
    have hCker_nn : 0 ≤ C_ker := by unfold C_ker; positivity
    have hMΔ_int : ∀ n, ∫⁻ t in Ioo (0 : ℝ) H, M_Δ n t ≤
        ENNReal.ofReal (C_slice * (1 / 2 : ℝ) ^ n) := by
      intro n
      have hbm := measurable_gainConj_vec (γ := γ) (ν := ν) (hΔ_vort n).2.2.2.2.2.2.2.1.measurable
      have hGm := measurable_gainConj_ten γ ν (hΔ_vort n).2.2.2.2.2.2.2.1.gradMeasurable
      have hr : 0 < (1 / 2 : ℝ) ^ n := by positivity
      have hv_le := CoreDuhamelDensityAux.lintegral_sliceVel_le_of_hCalNorm hc hH
        (mul_nonneg zero_le_two hCfv_nn) hr hbm (hΔ_eb n).1
      have hg_le := CoreDuhamelDensityAux.lintegral_sliceGrad_le_of_tCalNorm hc hH
        (mul_nonneg zero_le_two hCfg_nn) hr hGm (hΔ_eb n).2
      dsimp [M_Δ]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left (measurable_unnormSliceVel c hbm)]
      calc ENNReal.ofReal (8 * A_m) *
            ((∫⁻ t in Ioo (0 : ℝ) H, unnormSliceVel c (gainConj γ ν (Δb₀ n)) t) +
              ∫⁻ t in Ioo (0 : ℝ) H, unnormSliceGrad c (gainConj γ ν (ΔG₀ n)) t)
          ≤ ENNReal.ofReal (8 * A_m) *
              (ENNReal.ofReal ((c * (2 * C_fv) ^ 2 + H * H ^ (3 / 2 : ℝ)) * (1 / 2 : ℝ) ^ n) +
                ENNReal.ofReal ((c * (2 * C_fg) ^ 2 + H * H ^ (1 / 2 : ℝ)) * (1 / 2 : ℝ) ^ n)) :=
            mul_le_mul_of_nonneg_left (add_le_add hv_le hg_le) bot_le
        _ = ENNReal.ofReal (C_slice * (1 / 2 : ℝ) ^ n) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_mul (by positivity)]
            dsimp [C_slice]; ring_nf
    have hIΔ_int : ∀ n, ∫⁻ s in Ioo (0 : ℝ) H, I_Δ n s ≤
        ENNReal.ofReal (C_ker * C_slice) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
      intro n
      calc ∫⁻ s in Ioo (0 : ℝ) H, I_Δ n s
          ≤ ENNReal.ofReal C_ker * ∫⁻ t in Ioo (0 : ℝ) H, M_Δ n t :=
            CoreDuhamelDensityAux.lintegral_duhamel_slice_le hν0 hH hμ_pos (hMΔ_meas n)
        _ ≤ ENNReal.ofReal C_ker * ENNReal.ofReal (C_slice * (1 / 2 : ℝ) ^ n) :=
            mul_le_mul_of_nonneg_left (hMΔ_int n) bot_le
        _ = ENNReal.ofReal (C_ker * C_slice) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
            rw [ENNReal.ofReal_mul hCslice_nn, ← mul_assoc, ENNReal.ofReal_mul hCker_nn]
    have htot : ∫⁻ s in Ioo (0 : ℝ) H, ∑' n : ℕ, I_Δ n s < ⊤ := by
      rw [lintegral_tsum fun n => (hIΔ_meas n).aemeasurable]
      calc (∑' n : ℕ, ∫⁻ s in Ioo (0 : ℝ) H, I_Δ n s)
          ≤ ∑' n : ℕ, ENNReal.ofReal (C_ker * C_slice) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) :=
            ENNReal.tsum_le_tsum hIΔ_int
        _ = ENNReal.ofReal (C_ker * C_slice) * ∑' n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ n) :=
            ENNReal.tsum_mul_left
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            CoreDuhamelDensityAux.tsum_ofReal_half_pow_lt_top
    have hae := ae_lt_top (Measurable.tsum hIΔ_meas) htot.ne
    rw [ae_restrict_iff' measurableSet_Ioo] at hae
    exact hae
  -- Base `n = 0` finiteness from `coreSourceFinite_proof` + `coreSourceNegBound`
  have hfin_0_ae := hFinSrc ν ⟨hν0, hν_le_fin⟩ tr μ A_m C_clock (Fn 0) (b₀n 0) (G₀n 0)
    (b_sol_n 0) (G_sol_n 0) (hhd_n 0)
  have hsrc_0 := coreSourceNegBound 8 (by norm_num) CoreDuhamelDensityAux.cDualClause_eight
    P hP K hK b hb ν hν0 tr μ A_m (Fn 0) (b₀n 0) (G₀n 0) (b_sol_n 0) (G_sol_n 0) (hhd_n 0)
  -- Step 3: Slice convergence of `b₀d n`, `G₀d n`, and `G_sold n` for a.e. age in `(0, H)`
  have hb₀d_lim_ae : ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) H →
      Tendsto (fun n => unnormSliceVel c (gainConj γ ν (b₀d n)) t) atTop (𝓝 0) := by
    refine CoreDuhamelDensityAux.ae_slice_tendsto_zero_of_weighted_sq_geom
      (c := c) (H := H) (a := -3 / 2) (B := C_fv ^ 2) hc
      (fun n => measurable_unnormSliceVel c
        (measurable_gainConj_vec (γ := γ) (ν := ν)
          (fun i => ((hfree_n n).measurable i).sub (hfree.measurable i))))
      fun n => ?_
    have hbm := measurable_gainConj_vec (γ := γ) (ν := ν)
      (fun i => ((hfree_n n).measurable i).sub (hfree.measurable i))
    have hm_int : Measurable fun s : ℝ =>
        ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * unnormSliceVel c (gainConj γ ν (b₀d n)) s ^ 2 :=
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul
        ((measurable_unnormSliceVel c hbm).pow_const 2)
    have heq : ∫⁻ s in Ioo (0 : ℝ) H,
        ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
          (ENNReal.ofReal c⁻¹ * unnormSliceVel c (gainConj γ ν (b₀d n)) s ^ 2) =
        ENNReal.ofReal c⁻¹ * ∫⁻ s in Ioo (0 : ℝ) H,
          ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * unnormSliceVel c (gainConj γ ν (b₀d n)) s ^ 2 := by
      rw [← lintegral_const_mul _ hm_int]
      refine setLIntegral_congr_fun measurableSet_Ioo fun s _ => by ring
    rw [heq]
    calc ENNReal.ofReal c⁻¹ * ∫⁻ s in Ioo (0 : ℝ) H,
          ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * unnormSliceVel c (gainConj γ ν (b₀d n)) s ^ 2
        ≤ ENNReal.ofReal c⁻¹ * (ENNReal.ofReal c * hCalNorm c (gainConj γ ν (b₀d n)) ^ (2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (CoreDuhamelDensityAux.weighted_sliceVel_sq_le hc hbm) bot_le
      _ = hCalNorm c (gainConj γ ν (b₀d n)) ^ (2 : ℝ) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ (ENNReal.ofReal C_fv * ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow (hFd_eb n).1 (by norm_num)
      _ = ENNReal.ofReal (C_fv ^ 2) * ENNReal.ofReal ((1 / 4 : ℝ) ^ n) := by
          rw [← ENNReal.ofReal_mul hCfv_nn, ENNReal.rpow_two,
            ← ENNReal.ofReal_pow (mul_nonneg hCfv_nn (by positivity)),
            ← ENNReal.ofReal_mul (sq_nonneg C_fv)]
          congr 1
          rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
          norm_num
  have hG₀d_lim_ae : ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) H →
      Tendsto (fun n => unnormSliceGrad c (gainConj γ ν (G₀d n)) t) atTop (𝓝 0) := by
    refine CoreDuhamelDensityAux.ae_slice_tendsto_zero_of_weighted_sq_geom
      (c := c) (H := H) (a := -1 / 2) (B := C_fg ^ 2) hc
      (fun n => measurable_unnormSliceGrad c
        (measurable_gainConj_ten γ ν (fun i j => ((hfree_n n).gradMeasurable i j).sub
          (hfree.gradMeasurable i j))))
      fun n => ?_
    have hGm := measurable_gainConj_ten γ ν
      (fun i j => ((hfree_n n).gradMeasurable i j).sub (hfree.gradMeasurable i j))
    have hm_int : Measurable fun s : ℝ =>
        ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * unnormSliceGrad c (gainConj γ ν (G₀d n)) s ^ 2 :=
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul
        ((measurable_unnormSliceGrad c hGm).pow_const 2)
    have heq : ∫⁻ s in Ioo (0 : ℝ) H,
        ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
          (ENNReal.ofReal c⁻¹ * unnormSliceGrad c (gainConj γ ν (G₀d n)) s ^ 2) =
        ENNReal.ofReal c⁻¹ * ∫⁻ s in Ioo (0 : ℝ) H,
          ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * unnormSliceGrad c (gainConj γ ν (G₀d n)) s ^ 2 := by
      rw [← lintegral_const_mul _ hm_int]
      refine setLIntegral_congr_fun measurableSet_Ioo fun s _ => by ring
    rw [heq]
    calc ENNReal.ofReal c⁻¹ * ∫⁻ s in Ioo (0 : ℝ) H,
          ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * unnormSliceGrad c (gainConj γ ν (G₀d n)) s ^ 2
        ≤ ENNReal.ofReal c⁻¹ * (ENNReal.ofReal c * tCalNorm c (gainConj γ ν (G₀d n)) ^ (2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (CoreDuhamelDensityAux.weighted_sliceGrad_sq_le hc hGm) bot_le
      _ = tCalNorm c (gainConj γ ν (G₀d n)) ^ (2 : ℝ) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ (ENNReal.ofReal C_fg * ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow (hFd_eb n).2 (by norm_num)
      _ = ENNReal.ofReal (C_fg ^ 2) * ENNReal.ofReal ((1 / 4 : ℝ) ^ n) := by
          rw [← ENNReal.ofReal_mul hCfg_nn, ENNReal.rpow_two,
            ← ENNReal.ofReal_pow (mul_nonneg hCfg_nn (by positivity)),
            ← ENNReal.ofReal_mul (sq_nonneg C_fg)]
          congr 1
          rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
          norm_num
  -- Train advection Gronwall slice convergence for `G_sold n`
  obtain ⟨M_L, hML0, hML_all⟩ :=
    AdvectionEnergyAux.supNormD_one_bound_on tr hbuc (by linarith : (0 : ℝ) ≤ 2 * H)
  have hGsold_lim_ae : ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) H →
      Tendsto (fun n => unnormSliceGrad c (gainConj γ ν (G_sold n)) s) atTop (𝓝 0) := by
    refine CoreDuhamelDensityAux.ae_slice_tendsto_zero_of_weighted_sq_geom
      (c := c) (H := H) (a := -1 / 2) (B := Real.exp (2 * M_L * H) * (ν ^ 2)⁻¹) hc
      (fun n => measurable_unnormSliceGrad c
        (measurable_gainConj_ten γ ν (fun i j => ((hsol_n n).gradMeasurable i j).sub
          (hsol.gradMeasurable i j))))
      fun n => ?_
    have hsub_sol := causalSolSub c ν μ (trainVel tr) (Fn n) F (b_sol_n n) b_sol (G_sol_n n) G_sol
      (hsol_n n) hsol
    have hgron := CoreDuhamelDensityAux.train_core_grad_sq_le hc hν0 hγ hH hμ_pos hbuc hML0
      (fun s hs => (hML_all s hs).2.1)
      (fun i j => (hFn_meas n i j).sub (hFmeas i j))
      ((hFn_err n).trans_lt ENNReal.ofReal_lt_top) hsub_sol
    calc ∫⁻ s in Ioo (0 : ℝ) H,
          ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
            (ENNReal.ofReal c⁻¹ * unnormSliceGrad c (gainConj γ ν (G_sold n)) s ^ 2)
        ≤ ENNReal.ofReal (Real.exp (2 * M_L * H) * (ν ^ 2)⁻¹) *
            tCalNorm c (gainConj γ ν (Fd n)) ^ 2 := hgron
      _ ≤ ENNReal.ofReal (Real.exp (2 * M_L * H) * (ν ^ 2)⁻¹) *
            ENNReal.ofReal ((1 / 2 : ℝ) ^ n) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ bot_le (hFn_err n) 2) bot_le
      _ = ENNReal.ofReal (Real.exp (2 * M_L * H) * (ν ^ 2)⁻¹) *
            ENNReal.ofReal ((1 / 4 : ℝ) ^ n) := by
          congr 1
          rw [← ENNReal.ofReal_pow (by positivity), ← pow_mul, mul_comm n 2, pow_mul]
          norm_num
  -- Slice `MemLp` and `coreSourceNegBound` for `b₀d n, G₀d n` at a.e. `t ∈ (0, H)`
  have hmem_0_ae := CoreDuhamelRepSub.ae_freeSlice_memLp (γ := γ) hν0 hH hfree
  have hmem_n_ae : ∀ᵐ t ∂volume, ∀ n, t ∈ Ioo (0 : ℝ) H →
      (∀ i, MemLp (fun x => gainConj γ ν (b₀n n) (t, x) i) 2 (volume.restrict (B0579.cell c))) ∧
      (∀ i j, MemLp (fun x => gainConj γ ν (G₀n n) (t, x) i j) 2
        (volume.restrict (B0579.cell c))) :=
    ae_all_iff.2 fun n => CoreDuhamelRepSub.ae_freeSlice_memLp (γ := γ) hν0 hH (hfree_n n)
  have hsrc_d_all : ∀ᵐ t ∂volume, ∀ n, t ∈ Ioo (0 : ℝ) H →
      coreSrcNorm c 9 (coreAdvSlice γ tr (b₀d n) (G₀d n) t) ≤
        ENNReal.ofReal (8 * A_m) *
          (unnormSliceVel c (gainConj γ ν (b₀d n)) t +
            unnormSliceGrad c (gainConj γ ν (G₀d n)) t) := by
    refine ae_all_iff.2 fun n => ?_
    have hvd : VortData P K b ν tr μ A_m (Fd n) (b₀d n) (G₀d n) (b_sold n) (G_sold n) :=
      ⟨hbuc, hμ, hAm, hbd,
        fun p i j => by simp [Fd, hFn_sym n p i j, hFsym p i j],
        fun i j => (hFn_meas n i j).sub (hFmeas i j),
        (hFn_err n).trans_lt ENNReal.ofReal_lt_top,
        causalSolSub c ν μ (fun _ _ _ => 0) (Fn n) F (b₀n n) b₀ (G₀n n) G₀ (hfree_n n) hfree,
        causalSolSub c ν μ (trainVel tr) (Fn n) F (b_sol_n n) b_sol (G_sol_n n) G_sol
          (hsol_n n) hsol⟩
    exact coreSourceNegBound 8 (by norm_num) CoreDuhamelDensityAux.cDualClause_eight
      P hP K hK b hb ν hν0 tr μ A_m (Fd n) (b₀d n) (G₀d n) (b_sold n) (G_sold n) hvd
  have hsrc_Δ_all : ∀ᵐ t ∂volume, ∀ n, t ∈ Ioo (0 : ℝ) H →
      coreSrcNorm c 9 (coreAdvSlice γ tr (Δb₀ n) (ΔG₀ n) t) ≤ M_Δ n t :=
    ae_all_iff.2 hsrc_Δ
  -- Step 4: For each good `s ∈ (0, H)`, build the telescoping limit `k` and prove all properties
  filter_upwards [happrox_s, hsum_IΔ_ae, hfin_0_ae, hG₀d_lim_ae, hGsold_lim_ae] with
    s hs_approx hs_sum hs_fin0 hs_G0_lim hs_Gsol_lim hsH
  obtain ⟨ks, hks_m, hks_rep, hks_ae⟩ := hs_approx hsH
  let k : ℝ → ℝ × ℝ → ℂ := CoreDuhamelDensityAux.teleLimit ks
  have hkm : Measurable (Function.uncurry k) := CoreDuhamelDensityAux.measurable_uncurry_teleLimit hks_m
  -- Bound `∫⁻ t in Ioo 0 s, xNorm c 9 (ks (n+1) t - ks n t) ≤ I_Δ n s` and `n = 0` integral `< ⊤`
  have hdiff_int_le : ∀ n,
      ∫⁻ t in Ioo (0 : ℝ) s, xNorm c 9 (fun x => ks (n + 1) t x - ks n t x) ≤ I_Δ n s := by
    intro n
    refine setLIntegral_mono_ae' measurableSet_Ioo ?_
    filter_upwards [hks_ae, hsrc_Δ_all] with t ht hst hts
    have htH : t ∈ Ioo (0 : ℝ) H := ⟨hts.1, hts.2.trans hsH.2⟩
    exact ((ht hts).2 (n + 1) n).trans (mul_le_mul_of_nonneg_left (hst n htH) bot_le)
  have hsum_diff : (∑' n : ℕ, ∫⁻ t in Ioo (0 : ℝ) s,
      xNorm c 9 (fun x => ks (n + 1) t x - ks n t x)) < ⊤ :=
    lt_of_le_of_lt (ENNReal.tsum_le_tsum hdiff_int_le) (hs_sum hsH)
  have hks0_int_lt : ∫⁻ t in Ioo (0 : ℝ) s, xNorm c 9 (ks 0 t) < ⊤ := by
    refine lt_of_le_of_lt ?_ (hs_fin0 hsH)
    refine setLIntegral_mono_ae' measurableSet_Ioo ?_
    filter_upwards [hks_ae, hsrc_0] with t ht hst0 hts
    have htH : t ∈ Ioo (0 : ℝ) H := ⟨hts.1, hts.2.trans hsH.2⟩
    exact ((ht hts).1 0).2.2.trans (mul_le_mul_of_nonneg_left (hst0 htH) bot_le)
  have hm_xndiff : ∀ n, Measurable fun t : ℝ => xNorm c 9 (fun x => ks (n + 1) t x - ks n t x) :=
    fun n => CoreDuhamelDensityAux.measurable_xNorm_slice c ((hks_m (n + 1)).sub (hks_m n))
  have hm_xn0 : Measurable fun t : ℝ => xNorm c 9 (ks 0 t) :=
    CoreDuhamelDensityAux.measurable_xNorm_slice c (hks_m 0)
  have hae_t_sum : ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) s →
      (∑' n : ℕ, xNorm c 9 (fun x => ks (n + 1) t x - ks n t x)) < ⊤ := by
    have htot : ∫⁻ t in Ioo (0 : ℝ) s,
        ∑' n : ℕ, xNorm c 9 (fun x => ks (n + 1) t x - ks n t x) < ⊤ := by
      rw [lintegral_tsum fun n => (hm_xndiff n).aemeasurable]
      exact hsum_diff
    have hae := ae_lt_top (Measurable.tsum hm_xndiff) htot.ne
    rwa [ae_restrict_iff' measurableSet_Ioo] at hae
  have hae_t_0 : ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) s → xNorm c 9 (ks 0 t) < ⊤ := by
    have hae := ae_lt_top hm_xn0 hks0_int_lt.ne
    rwa [ae_restrict_iff' measurableSet_Ioo] at hae
  -- Part A: a.e. `t ∈ Ioo 0 s` properties of `k t`
  have hk_t_props : ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) s →
      MemLp (k t) 2 (B0579.cellMeasure c 9) ∧
      HasZeroCirculation c (k t) ∧
      xNorm c 9 (k t) ≤
        ENNReal.ofReal (vortKernel C_clock P ν μ s t) *
          coreSrcNorm c 9 (coreAdvSlice γ tr b₀ G₀ t) := by
    filter_upwards [hks_ae, hae_t_sum, hae_t_0, hb₀d_lim_ae, hG₀d_lim_ae,
      hmem_0_ae, hmem_n_ae, hsrc_d_all] with
      t hks_t ht_sum ht_0 hvel_lim hgrad_lim hmem0 hmemn hsrc_d hts
    have htH : t ∈ Ioo (0 : ℝ) H := ⟨hts.1, hts.2.trans hsH.2⟩
    have hsum_t : (∑' n : ℕ, xNorm c 9 (fun x => ks (n + 1) t x - ks n t x)) < ⊤ := ht_sum hts
    have hk_tm : Measurable (k t) := hkm.comp (measurable_const.prodMk measurable_id)
    have hks_tm : ∀ n, Measurable (ks n t) := fun n =>
      (hks_m n).comp (measurable_const.prodMk measurable_id)
    have herr_N : ∀ N : ℕ, xNorm c 9 (fun x => k t x - ks N t x) ≤
        ∑' m : ℕ, xNorm c 9 (fun x => ks (N + m + 1) t x - ks (N + m) t x) :=
      CoreDuhamelDensityAux.xNorm_teleLimit_sub_le hks_m hsum_t
    have herr_lim : Tendsto (fun N => xNorm c 9 (fun x => k t x - ks N t x)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (CoreDuhamelDensityAux.ennreal_tsum_nat_add_tendsto_zero hsum_t.ne)
        (fun _ => bot_le) herr_N
    -- `MemLp (k t) 2 (B0579.cellMeasure c 9)`
    have hkt_mem : MemLp (k t) 2 (B0579.cellMeasure c 9) := by
      refine ⟨hk_tm.aestronglyMeasurable, ?_⟩
      have hadd : k t = (fun x => k t x - ks 0 t x) + ks 0 t := by
        funext x; simp
      rw [hadd]
      refine (eLpNorm_add_le (hk_tm.sub (hks_tm 0)).aestronglyMeasurable
        (hks_tm 0).aestronglyMeasurable one_le_two).trans_lt ?_
      refine ENNReal.add_lt_top.2 ⟨?_, ht_0 hts⟩
      exact (herr_N 0).trans_lt (by simpa only [zero_add] using hsum_t)
    -- `HasZeroCirculation c (k t)`
    have hkt_zc : HasZeroCirculation c (k t) := by
      set C_jb : ℝ≥0∞ :=
        (∫⁻ x in B0579.cell c, ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ))) ^ (1 / 2 : ℝ)
      have hCjb_lt : C_jb < ⊤ :=
        ENNReal.rpow_lt_top_of_nonneg (by norm_num) (V3.lint_jb_cell_lt_top c).ne
      have hint_kt : IntegrableOn (k t) (B0579.cell c) := by
        refine ⟨hk_tm.aestronglyMeasurable, ?_⟩
        rw [HasFiniteIntegral]
        exact (V3.lint_cell_le hk_tm.aemeasurable).trans_lt (ENNReal.mul_lt_top hkt_mem.2 hCjb_lt)
      refine ⟨hint_kt, ?_⟩
      have hint_eq_zero : ‖∫ x in B0579.cell c, k t x‖ₑ ≤ 0 := by
        have hlim_rhs : Tendsto
            (fun N => xNorm c 9 (fun x => k t x - ks N t x) * C_jb) atTop (𝓝 0) := by
          simpa using ENNReal.Tendsto.mul_const herr_lim (Or.inr hCjb_lt.ne)
        refine ge_of_tendsto' hlim_rhs fun N => ?_
        obtain ⟨hint_ksN, hzero_ksN⟩ := ((hks_t hts).1 N).2.1
        have hsub_int : ∫ x in B0579.cell c, k t x =
            ∫ x in B0579.cell c, (k t x - ks N t x) := by
          rw [integral_sub hint_kt hint_ksN, hzero_ksN, sub_zero]
        rw [hsub_int]
        exact (enorm_integral_le_lintegral_enorm _).trans
          (V3.lint_cell_le (hk_tm.sub (hks_tm N)).aemeasurable)
      exact enorm_eq_zero.1 (le_antisymm hint_eq_zero bot_le)
    -- Weak-source clock bound at `(b₀, G₀)`
    have hkt_bd : xNorm c 9 (k t) ≤
        ENNReal.ofReal (vortKernel C_clock P ν μ s t) *
          coreSrcNorm c 9 (coreAdvSlice γ tr b₀ G₀ t) := by
      set Kv : ℝ≥0∞ := ENNReal.ofReal (vortKernel C_clock P ν μ s t)
      set target : ℝ≥0∞ := Kv * coreSrcNorm c 9 (coreAdvSlice γ tr b₀ G₀ t)
      let err_seq : ℕ → ℝ≥0∞ := fun N =>
        xNorm c 9 (fun x => k t x - ks N t x) +
          Kv * (ENNReal.ofReal (8 * A_m) *
            (unnormSliceVel c (gainConj γ ν (b₀d N)) t +
              unnormSliceGrad c (gainConj γ ν (G₀d N)) t))
      have herr_seq_lim : Tendsto (fun N => target + err_seq N) atTop (𝓝 target) := by
        have hsum_vg : Tendsto
            (fun N => unnormSliceVel c (gainConj γ ν (b₀d N)) t +
              unnormSliceGrad c (gainConj γ ν (G₀d N)) t) atTop (𝓝 0) := by
          simpa only [add_zero] using (hvel_lim htH).add (hgrad_lim htH)
        have hm1 : Tendsto
            (fun N => ENNReal.ofReal (8 * A_m) *
              (unnormSliceVel c (gainConj γ ν (b₀d N)) t +
                unnormSliceGrad c (gainConj γ ν (G₀d N)) t)) atTop (𝓝 0) := by
          simpa only [mul_zero] using ENNReal.Tendsto.const_mul
            (a := ENNReal.ofReal (8 * A_m)) hsum_vg (Or.inr ENNReal.ofReal_ne_top)
        have hm2 : Tendsto
            (fun N => Kv * (ENNReal.ofReal (8 * A_m) *
              (unnormSliceVel c (gainConj γ ν (b₀d N)) t +
                unnormSliceGrad c (gainConj γ ν (G₀d N)) t))) atTop (𝓝 0) := by
          simpa only [mul_zero] using ENNReal.Tendsto.const_mul
            (a := Kv) hm1 (Or.inr ENNReal.ofReal_ne_top)
        have herr0 : Tendsto err_seq atTop (𝓝 0) := by
          simpa only [add_zero] using herr_lim.add hm2
        simpa only [add_zero] using tendsto_const_nhds.add herr0
      refine ge_of_tendsto' herr_seq_lim fun N => ?_
      have htri_x : xNorm c 9 (k t) ≤
          xNorm c 9 (fun x => k t x - ks N t x) + xNorm c 9 (ks N t) :=
        CoreDuhamelDensityAux.xNorm_le_sub_add c hk_tm (hks_tm N)
      have hsub_src := CoreDuhamelDensityAux.coreSrcNorm_le_add_diff hν0 hAm hbd htH
        (hfree_n N).measurable (hfree_n N).gradMeasurable hfree.measurable hfree.gradMeasurable
        (hmemn N htH).1 (hmemn N htH).2 (hmem0 htH).1 (hmem0 htH).2
      have hksN_bd : xNorm c 9 (ks N t) ≤
          target + Kv * (ENNReal.ofReal (8 * A_m) *
            (unnormSliceVel c (gainConj γ ν (b₀d N)) t +
              unnormSliceGrad c (gainConj γ ν (G₀d N)) t)) := by
        calc xNorm c 9 (ks N t)
            ≤ Kv * coreSrcNorm c 9 (coreAdvSlice γ tr (b₀n N) (G₀n N) t) :=
              ((hks_t hts).1 N).2.2
          _ ≤ Kv * (coreSrcNorm c 9 (coreAdvSlice γ tr b₀ G₀ t) +
                coreSrcNorm c 9 (coreAdvSlice γ tr (b₀d N) (G₀d N) t)) :=
              mul_le_mul_of_nonneg_left hsub_src bot_le
          _ ≤ Kv * (coreSrcNorm c 9 (coreAdvSlice γ tr b₀ G₀ t) +
                ENNReal.ofReal (8 * A_m) *
                  (unnormSliceVel c (gainConj γ ν (b₀d N)) t +
                    unnormSliceGrad c (gainConj γ ν (G₀d N)) t)) :=
              mul_le_mul_of_nonneg_left (add_le_add le_rfl (hsrc_d N htH)) bot_le
          _ = target + Kv * (ENNReal.ofReal (8 * A_m) *
                (unnormSliceVel c (gainConj γ ν (b₀d N)) t +
                  unnormSliceGrad c (gainConj γ ν (G₀d N)) t)) := by
              rw [mul_add]
      calc xNorm c 9 (k t)
          ≤ xNorm c 9 (fun x => k t x - ks N t x) +
              (target + Kv * (ENNReal.ofReal (8 * A_m) *
                (unnormSliceVel c (gainConj γ ν (b₀d N)) t +
                  unnormSliceGrad c (gainConj γ ν (G₀d N)) t))) :=
            htri_x.trans (add_le_add le_rfl hksN_bd)
        _ = target + err_seq N := by dsimp [err_seq]; ac_rfl
    exact ⟨hkt_mem, hkt_zc, hkt_bd⟩
  -- Part B: Identify `corePerturbVort γ ν G₀ G_sol s` with `fun x => ∫ t in Ioo 0 s, k t x`
  have hrep_lim : corePerturbVort γ ν G₀ G_sol s =ᵐ[volume.restrict (B0579.cell c)]
      fun x => ∫ t in Ioo 0 s, k t x :=
    CoreDuhamelDensityAux.teleLimit_duhamel_rep hfree.gradMeasurable hsol.gradMeasurable
      (fun N => (hfree_n N).gradMeasurable) (fun N => (hsol_n N).gradMeasurable)
      hks_m hks_rep hsum_diff hks0_int_lt (hs_G0_lim hsH) (hs_Gsol_lim hsH)
  exact ⟨k, hkm, hk_t_props, hrep_lim⟩

end UnforcedLeray.Short.IIIa

end
