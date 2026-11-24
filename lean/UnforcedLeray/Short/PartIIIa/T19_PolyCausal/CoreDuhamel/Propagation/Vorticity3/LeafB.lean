import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity3.Leaves
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.WeakCellAeUnique

/-!
# `PartIII-a:T19/2/3/2/3/2`: `CoreSourceFinite`

Source of record: `the November 2 reference manuscript` (SP), lines 3481–3488.

Proves `coreSourceFinite_proof : CoreSourceFinite`:
1. `freeCausalExistsUnique` gives `(b*, G*)` with finite `hCalNorm` and `tCalNorm`, and
   `b₀ = b*` a.e. on `(0, ∞) × cell c`.
2. `weakCellAeUnique_proof` transfers `G₀ = G*` a.e. on `cell c` for a.e. `t > 0`.
3. By AM-GM (`x ≤ x² a⁻¹ + a`), `unnormSliceVel (g⁻¹ b₀)` and `unnormSliceGrad (g⁻¹ G₀)` are
   `L¹(0, H)`.
4. Since `(t / s)^{Re μ} ≤ 1` for `0 < t < s` (`Re μ > 0`), Tonelli in `(s, t)` and
   `∫_t^H (1 + (s - t)^{-1/2}) ds ≤ H + 2 √H` show the Duhamel source integral is finite for a.e.
   `s ∈ (0, H)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

namespace LeafBAux

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

private theorem hasWeakCellDerivC_congr_fun {c : ℝ} {j : Fin 2} {φ₁ φ₂ g : ℝ × ℝ → ℂ}
    (h : φ₁ =ᵐ[volume.restrict (B0579.cell c)] φ₂) (hD : HasWeakCellDerivC c j φ₁ g) :
    HasWeakCellDerivC c j φ₂ g := by
  refine ⟨fun θ hθ => ⟨?_, (hD.1 θ hθ).2⟩, fun θ hθ => ?_⟩
  · exact (hD.1 θ hθ).1.congr_fun_ae (by
      filter_upwards [h] with x hx
      simp [hx])
  · rw [← hD.2 θ hθ]
    refine setIntegral_congr_ae (B0579.measurableSet_cell c) ?_
    filter_upwards [ae_imp_of_ae_restrict h] with x hx hxc
    simp [hx hxc]

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
    have hm_ind : Measurable ((Ioo t H).indicator (fun s : ℝ => ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)))) :=
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

end LeafBAux

/-- **Leaf (ii) `CoreSourceFinite`** (SP 3481–3488). -/
theorem coreSourceFinite_proof : CoreSourceFinite := by
  intro C_dual hCdual P hP K hK b hb
  obtain ⟨ν₀, hν₀, hFree⟩ := freeCausalExistsUnique P hP K hK
  refine ⟨min ν₀ (2 * b)⁻¹, lt_min hν₀ (inv_pos.2 (by linarith)), ?_⟩
  intro ν hν tr μ A_m C_clock F b₀ G₀ b_sol G_sol hV
  have hν0 : 0 < ν := hν.1
  have hν_le₀ : ν ≤ ν₀ := hν.2.trans (min_le_left _ _)
  have hν_half : ν ≤ (2 * b)⁻¹ := hν.2.trans (min_le_right _ _)
  have hν_half' : ν ≤ 1 / 2 :=
    hν_half.trans (by rw [one_div]; exact inv_anti₀ (by norm_num) (by linarith))
  set c : ℝ := ν ^ (-2 : ℝ) with hc_def
  have hc : 0 < c := Real.rpow_pos_of_pos hν0 _
  set H : ℝ := coreEnd ν b with hH_def
  have hH : 0 < H := zero_lt_one.trans (coreEnd_bounds hb hν0 hν_half' hν_half).1
  obtain ⟨_htr, hμK, hAm, _hAm_bd, hFsym, hFmeas, hFtCal, hb₀_sol, _hbsol⟩ := hV
  obtain ⟨b_star, G_star, hb_star, hb_star_hCal, hG_star_tCal, hb₀_ae_all⟩ :=
    hFree ν ⟨hν0, hν_le₀⟩ μ hμK F hFsym hFmeas hFtCal
  have hb₀_ae : b₀ =ᵐ[volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)] b_star :=
    hb₀_ae_all b₀ G₀ hb₀_sol
  have hμ_pos : 0 < μ.re := (hK.2 μ hμK).1
  -- Finite `hCalNorm` and `tCalNorm` for `b_star` and `G_star`.
  have hb_star_fin : hCalNorm c (gainConj P.eigenvalue.re ν b_star) < ⊤ :=
    hb_star_hCal.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hFtCal)
  have hG_star_fin : tCalNorm c (gainConj P.eigenvalue.re ν G_star) < ⊤ :=
    hG_star_tCal.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hFtCal)
  -- `b₀ = b_star` a.e. on `cell c` for a.e. `t ∈ Ioo 0 H`, and `G₀ = G_star` a.e. via `weakCellAeUnique_proof`.
  have hb₀_ae' : b₀ =ᵐ[(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (B0579.cell c))] b_star := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hb₀_ae
    exact hb₀_ae
  have hprod_ae : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ᵐ x ∂(volume.restrict (B0579.cell c)), b₀ (t, x) = b_star (t, x) :=
    Measure.ae_ae_of_ae_prod hb₀_ae'
  have hvel_eq : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) H)),
      unnormSliceVel c (gainConj P.eigenvalue.re ν b₀) t =
        unnormSliceVel c (gainConj P.eigenvalue.re ν b_star) t := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self hprod_ae] with t ht
    unfold unnormSliceVel gainConj
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [ht] with x hx
    simp [hx]
  have hgrad_eq : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) H)),
      unnormSliceGrad c (gainConj P.eigenvalue.re ν G₀) t =
        unnormSliceGrad c (gainConj P.eigenvalue.re ν G_star) t := by
    have hIoo_ae : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) H)),
        ∀ᵐ x ∂(volume.restrict (B0579.cell c)), b₀ (t, x) = b_star (t, x) :=
      ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self hprod_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hIoo_ae] with t ht hbt
    have hG_ae : ∀ i j : Fin 2,
        (fun x => G₀ (t, x) i j) =ᵐ[volume.restrict (B0579.cell c)] fun x => G_star (t, x) i j := by
      intro i j
      have hbi : (fun x => b₀ (t, x) i) =ᵐ[volume.restrict (B0579.cell c)] fun x => b_star (t, x) i := by
        filter_upwards [hbt] with x hx
        exact congrFun hx i
      have hD1 := hb₀_sol.weakGrad t ht.1 i j
      have hD2 := LeafBAux.hasWeakCellDerivC_congr_fun hbi.symm (hb_star.weakGrad t ht.1 i j)
      exact weakCellAeUnique c j (fun x => b₀ (t, x) i) _ _ hD1 hD2
    unfold unnormSliceGrad gainConj tnorm2
    congr 1
    refine lintegral_congr_ae ?_
    have h00 := hG_ae 0 0
    have h01 := hG_ae 0 1
    have h10 := hG_ae 1 0
    have h11 := hG_ae 1 1
    filter_upwards [h00, h01, h10, h11] with x hx00 hx01 hx10 hx11
    have hGeq : G₀ (t, x) = G_star (t, x) := by
      ext i j
      fin_cases i <;> fin_cases j <;> assumption
    simp [hGeq]
  -- `L²` weighted slice bounds on `(0, H)` for `b_star` and `G_star`.
  have hm_gain : Measurable fun p : ℝ × (ℝ × ℝ) => (gainG P.eigenvalue.re ν p.1)⁻¹ := by
    unfold gainG; fun_prop
  have hm_b_star : Measurable fun p : ℝ × (ℝ × ℝ) =>
      vnorm2 (gainConj P.eigenvalue.re ν b_star p) ^ 2 := by
    have hm1 : ∀ i, Measurable fun p => gainConj P.eigenvalue.re ν b_star p i := fun i =>
      Measurable.smul hm_gain (hb_star.measurable i)
    exact (causalLin_measurable_vnorm2 hm1).pow_const 2
  have hm_G_star : Measurable fun p : ℝ × (ℝ × ℝ) =>
      tnorm2 (gainConj P.eigenvalue.re ν G_star p) ^ 2 := by
    have hm1 : ∀ i j, Measurable fun p => gainConj P.eigenvalue.re ν G_star p i j := fun i j =>
      Measurable.smul hm_gain (hb_star.gradMeasurable i j)
    exact (causalLin_measurable_tnorm2 hm1).pow_const 2
  have hm_vel_star : Measurable (unnormSliceVel c (gainConj P.eigenvalue.re ν b_star)) :=
    measurable_unnormSliceVel c fun i => Measurable.smul hm_gain (hb_star.measurable i)
  have hm_grad_star : Measurable (unnormSliceGrad c (gainConj P.eigenvalue.re ν G_star)) :=
    measurable_unnormSliceGrad c fun i j => Measurable.smul hm_gain (hb_star.gradMeasurable i j)
  have hb_star_slice_int : ∫⁻ t in Ioo (0 : ℝ) H,
      ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) *
        unnormSliceVel c (gainConj P.eigenvalue.re ν b_star) t ^ 2 < ⊤ := by
    have h1 : ∫⁻ p in Iio H ×ˢ (univ : Set (ℝ × ℝ)),
        ENNReal.ofReal (vnorm2 (gainConj P.eigenvalue.re ν b_star p) ^ 2) ∂(ageμ c (-3 / 2)) ≤
        hCalNorm c (gainConj P.eigenvalue.re ν b_star) ^ (2 : ℝ) := by
      have heq := eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
        (f := fun p => vnorm2 (gainConj P.eigenvalue.re ν b_star p)) (μ := ageμ c (-3 / 2))
      have hpow : hCalNorm c (gainConj P.eigenvalue.re ν b_star) ^ (2 : ℝ) =
          ∫⁻ p, ENNReal.ofReal (vnorm2 (gainConj P.eigenvalue.re ν b_star p) ^ 2) ∂(ageμ c (-3 / 2)) := by
        rw [hCalNorm, heq, ← ENNReal.rpow_mul]
        norm_num
        refine lintegral_congr fun p => ?_
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      rw [hpow]
      exact setLIntegral_le_lintegral _ _
    rw [lintegral_Iio_ageμ_eq hc _ hm_b_star] at h1
    have h2 : ∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
        (ENNReal.ofReal c⁻¹ * unnormSliceVel c (gainConj P.eigenvalue.re ν b_star) s ^ 2) < ⊤ := by
      refine (le_trans (le_of_eq ?_) h1).trans_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hb_star_fin.ne)
      refine setLIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
      unfold unnormSliceVel
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    have hc_inv_pos : ENNReal.ofReal c⁻¹ ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 (inv_pos.2 hc)
    have hm_integrand : Measurable fun s : ℝ =>
        ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * unnormSliceVel c (gainConj P.eigenvalue.re ν b_star) s ^ 2 :=
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul (hm_vel_star.pow_const 2)
    have hm_rhs : Measurable fun s : ℝ =>
        ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * (ENNReal.ofReal c⁻¹ * unnormSliceVel c (gainConj P.eigenvalue.re ν b_star) s ^ 2) :=
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul (measurable_const.mul (hm_vel_star.pow_const 2))
    have h3 : ENNReal.ofReal c⁻¹ * ∫⁻ s in Ioo (0 : ℝ) H,
        ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * unnormSliceVel c (gainConj P.eigenvalue.re ν b_star) s ^ 2 < ⊤ := by
      rw [← lintegral_const_mul _ hm_integrand]
      refine h2.trans_le' (setLIntegral_mono_ae hm_rhs.aemeasurable (Eventually.of_forall fun s _ => ?_))
      ring_nf
      exact le_rfl
    rcases ENNReal.mul_lt_top_iff.1 h3 with ⟨_, h_lt⟩ | h0 | h0
    · exact h_lt
    · exact absurd h0 hc_inv_pos
    · rw [h0]; exact ENNReal.zero_lt_top
  have hG_star_slice_int : ∫⁻ t in Ioo (0 : ℝ) H,
      ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) *
        unnormSliceGrad c (gainConj P.eigenvalue.re ν G_star) t ^ 2 < ⊤ := by
    have h1 : ∫⁻ p in Iio H ×ˢ (univ : Set (ℝ × ℝ)),
        ENNReal.ofReal (tnorm2 (gainConj P.eigenvalue.re ν G_star p) ^ 2) ∂(ageμ c (-1 / 2)) ≤
        tCalNorm c (gainConj P.eigenvalue.re ν G_star) ^ (2 : ℝ) := by
      have heq := eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
        (f := fun p => tnorm2 (gainConj P.eigenvalue.re ν G_star p)) (μ := ageμ c (-1 / 2))
      have hpow : tCalNorm c (gainConj P.eigenvalue.re ν G_star) ^ (2 : ℝ) =
          ∫⁻ p, ENNReal.ofReal (tnorm2 (gainConj P.eigenvalue.re ν G_star p) ^ 2) ∂(ageμ c (-1 / 2)) := by
        rw [tCalNorm, heq, ← ENNReal.rpow_mul]
        norm_num
        refine lintegral_congr fun p => ?_
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      rw [hpow]
      exact setLIntegral_le_lintegral _ _
    rw [lintegral_Iio_ageμ_eq hc _ hm_G_star] at h1
    have h2 : ∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
        (ENNReal.ofReal c⁻¹ * unnormSliceGrad c (gainConj P.eigenvalue.re ν G_star) s ^ 2) < ⊤ := by
      refine (le_trans (le_of_eq ?_) h1).trans_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hG_star_fin.ne)
      refine setLIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
      unfold unnormSliceGrad
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    have hc_inv_pos : ENNReal.ofReal c⁻¹ ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 (inv_pos.2 hc)
    have hm_integrand : Measurable fun s : ℝ =>
        ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * unnormSliceGrad c (gainConj P.eigenvalue.re ν G_star) s ^ 2 :=
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul (hm_grad_star.pow_const 2)
    have hm_rhs : Measurable fun s : ℝ =>
        ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal c⁻¹ * unnormSliceGrad c (gainConj P.eigenvalue.re ν G_star) s ^ 2) :=
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul (measurable_const.mul (hm_grad_star.pow_const 2))
    have h3 : ENNReal.ofReal c⁻¹ * ∫⁻ s in Ioo (0 : ℝ) H,
        ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * unnormSliceGrad c (gainConj P.eigenvalue.re ν G_star) s ^ 2 < ⊤ := by
      rw [← lintegral_const_mul _ hm_integrand]
      refine h2.trans_le' (setLIntegral_mono_ae hm_rhs.aemeasurable (Eventually.of_forall fun s _ => ?_))
      ring_nf
      exact le_rfl
    rcases ENNReal.mul_lt_top_iff.1 h3 with ⟨_, h_lt⟩ | h0 | h0
    · exact h_lt
    · exact absurd h0 hc_inv_pos
    · rw [h0]; exact ENNReal.zero_lt_top
  -- AM-GM: `V(t) + W(t)` is `L¹(Ioo 0 H)`.
  have hm_V0 : Measurable (unnormSliceVel c (gainConj P.eigenvalue.re ν b₀)) :=
    measurable_unnormSliceVel c fun i => Measurable.smul hm_gain (hb₀_sol.measurable i)
  have hm_W0 : Measurable (unnormSliceGrad c (gainConj P.eigenvalue.re ν G₀)) :=
    measurable_unnormSliceGrad c fun i j => Measurable.smul hm_gain (hb₀_sol.gradMeasurable i j)
  have hV_L1 : ∫⁻ t in Ioo (0 : ℝ) H, unnormSliceVel c (gainConj P.eigenvalue.re ν b₀) t < ⊤ := by
    have hle : ∫⁻ t in Ioo (0 : ℝ) H, unnormSliceVel c (gainConj P.eigenvalue.re ν b₀) t ≤
        ∫⁻ t in Ioo (0 : ℝ) H,
          (unnormSliceVel c (gainConj P.eigenvalue.re ν b_star) t ^ 2 *
            ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) + ENNReal.ofReal (t ^ (3 / 2 : ℝ))) := by
      refine setLIntegral_mono_ae
        (((hm_vel_star.pow_const 2).mul (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))).add
          (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))).aemeasurable ?_
      filter_upwards [ae_imp_of_ae_restrict hvel_eq] with t hve ht
      rw [hve ht]
      have ha0 : ENNReal.ofReal (t ^ (3 / 2 : ℝ)) ≠ 0 :=
        ENNReal.ofReal_ne_zero_iff.2 (Real.rpow_pos_of_pos ht.1 _)
      have hat : ENNReal.ofReal (t ^ (3 / 2 : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
      have hinv : (ENNReal.ofReal (t ^ (3 / 2 : ℝ)))⁻¹ = ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) := by
        rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos ht.1 _),
          ← Real.rpow_neg ht.1.le]
        norm_num
      rw [← hinv]
      exact LeafBAux.ennreal_le_sq_div_add ha0 hat
    refine hle.trans_lt ?_
    rw [lintegral_add_right _ (by fun_prop)]
    refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
    · refine hb_star_slice_int.trans_le' (setLIntegral_mono_ae (by fun_prop) (Eventually.of_forall fun t _ => ?_))
      rw [mul_comm]
    · have hbd : ∫⁻ t in Ioo (0 : ℝ) H, ENNReal.ofReal (t ^ (3 / 2 : ℝ)) ≤
          ∫⁻ _t in Ioo (0 : ℝ) H, ENNReal.ofReal (H ^ (3 / 2 : ℝ)) :=
        setLIntegral_mono_ae (by fun_prop) (Eventually.of_forall fun t ht =>
          ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ht.1.le ht.2.le (by norm_num)))
      rw [setLIntegral_const, Real.volume_Ioo, sub_zero] at hbd
      exact hbd.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hW_L1 : ∫⁻ t in Ioo (0 : ℝ) H, unnormSliceGrad c (gainConj P.eigenvalue.re ν G₀) t < ⊤ := by
    have hle : ∫⁻ t in Ioo (0 : ℝ) H, unnormSliceGrad c (gainConj P.eigenvalue.re ν G₀) t ≤
        ∫⁻ t in Ioo (0 : ℝ) H,
          (unnormSliceGrad c (gainConj P.eigenvalue.re ν G_star) t ^ 2 *
            ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) + ENNReal.ofReal (t ^ (1 / 2 : ℝ))) := by
      refine setLIntegral_mono_ae
        (((hm_grad_star.pow_const 2).mul (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))).add
          (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))).aemeasurable ?_
      filter_upwards [ae_imp_of_ae_restrict hgrad_eq] with t hge ht
      rw [hge ht]
      have ha0 : ENNReal.ofReal (t ^ (1 / 2 : ℝ)) ≠ 0 :=
        ENNReal.ofReal_ne_zero_iff.2 (Real.rpow_pos_of_pos ht.1 _)
      have hat : ENNReal.ofReal (t ^ (1 / 2 : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
      have hinv : (ENNReal.ofReal (t ^ (1 / 2 : ℝ)))⁻¹ = ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) := by
        rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos ht.1 _),
          ← Real.rpow_neg ht.1.le]
        norm_num
      rw [← hinv]
      exact LeafBAux.ennreal_le_sq_div_add ha0 hat
    refine hle.trans_lt ?_
    rw [lintegral_add_right _ (by fun_prop)]
    refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
    · refine hG_star_slice_int.trans_le' (setLIntegral_mono_ae (by fun_prop) (Eventually.of_forall fun t _ => ?_))
      rw [mul_comm]
    · have hbd : ∫⁻ t in Ioo (0 : ℝ) H, ENNReal.ofReal (t ^ (1 / 2 : ℝ)) ≤
          ∫⁻ _t in Ioo (0 : ℝ) H, ENNReal.ofReal (H ^ (1 / 2 : ℝ)) :=
        setLIntegral_mono_ae (by fun_prop) (Eventually.of_forall fun t ht =>
          ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ht.1.le ht.2.le (by norm_num)))
      rw [setLIntegral_const, Real.volume_Ioo, sub_zero] at hbd
      exact hbd.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  -- Tonelli on `Ioo 0 H`
  set C₀ : ℝ := |C_clock| * ν ^ (-(weakDegree 9 P.kappa : ℝ)) * (C_dual * A_m) with hC₀_def
  set U : ℝ → ℝ≥0∞ := fun t =>
    unnormSliceVel c (gainConj P.eigenvalue.re ν b₀) t +
      unnormSliceGrad c (gainConj P.eigenvalue.re ν G₀) t with hU_def
  have hmU : Measurable U := hm_V0.add hm_W0
  have hU_L1 : ∫⁻ t in Ioo (0 : ℝ) H, U t < ⊤ := by
    rw [hU_def, lintegral_add_left hm_V0]
    exact ENNReal.add_lt_top.2 ⟨hV_L1, hW_L1⟩
  have hm_prod : Measurable fun p : ℝ × ℝ =>
      (if p.1 ∈ Ioo (0 : ℝ) H ∧ p.2 ∈ Ioo (0 : ℝ) p.1 then (1 : ℝ≥0∞) else 0) *
        (ENNReal.ofReal (1 + (p.1 - p.2) ^ (-1 / 2 : ℝ)) * U p.2) := by
    refine Measurable.mul ?_ ?_
    · refine Measurable.ite ?_ measurable_const measurable_const
      exact (measurableSet_Ioo.preimage measurable_fst).inter
        ((measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_lt measurable_snd measurable_fst))
    · refine (ENNReal.measurable_ofReal.comp (measurable_const.add
        ((measurable_fst.sub measurable_snd).pow_const _))).mul (hmU.comp measurable_snd)
  have hL : ∫⁻ s in Ioo (0 : ℝ) H, ∫⁻ t in Ioo (0 : ℝ) s,
      ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) * U t =
      ∫⁻ s, ∫⁻ t, (if s ∈ Ioo (0 : ℝ) H ∧ t ∈ Ioo (0 : ℝ) s then (1 : ℝ≥0∞) else 0) *
        (ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) * U t) := by
    rw [← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun s => ?_
    by_cases hs : s ∈ Ioo (0 : ℝ) H
    · rw [Set.indicator_of_mem hs, ← lintegral_indicator measurableSet_Ioo]
      refine lintegral_congr fun t => ?_
      by_cases ht : t ∈ Ioo (0 : ℝ) s <;> simp [hs, ht]
    · rw [Set.indicator_of_notMem hs]
      simp [hs]
  have hTonelli : ∫⁻ s, ∫⁻ t, (if s ∈ Ioo (0 : ℝ) H ∧ t ∈ Ioo (0 : ℝ) s then (1 : ℝ≥0∞) else 0) *
      (ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) * U t) < ⊤ := by
    have h_swap : ∫⁻ s in Ioo (0 : ℝ) H, ∫⁻ t in Ioo (0 : ℝ) s,
        ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) * U t =
        ∫⁻ t in Ioo (0 : ℝ) H, U t *
          ∫⁻ s in Ioo t H, ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) := by
      have hR : ∫⁻ t in Ioo (0 : ℝ) H, U t *
          ∫⁻ s in Ioo t H, ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) =
          ∫⁻ t, ∫⁻ s, (if s ∈ Ioo (0 : ℝ) H ∧ t ∈ Ioo (0 : ℝ) s then (1 : ℝ≥0∞) else 0) *
            (ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) * U t) := by
        rw [← lintegral_indicator measurableSet_Ioo]
        refine lintegral_congr fun t => ?_
        by_cases ht : t ∈ Ioo (0 : ℝ) H
        · rw [Set.indicator_of_mem ht, ← lintegral_const_mul _ (by fun_prop),
            ← lintegral_indicator measurableSet_Ioo]
          refine lintegral_congr fun s => ?_
          by_cases hs : s ∈ Ioo t H
          · have hsH : s ∈ Ioo (0 : ℝ) H := ⟨ht.1.trans hs.1, hs.2⟩
            have hts : t ∈ Ioo (0 : ℝ) s := ⟨ht.1, hs.1⟩
            simp [hs, hsH, hts, mul_comm]
          · have hnot : ¬ (s ∈ Ioo (0 : ℝ) H ∧ t ∈ Ioo (0 : ℝ) s) := by
              rintro ⟨hs1, hs2⟩
              exact hs ⟨hs2.2, hs1.2⟩
            rw [Set.indicator_of_notMem hs, ite_eq_right_iff.2 (fun h => absurd h hnot), zero_mul]
        · rw [Set.indicator_of_notMem ht]
          symm
          have hzero : ∀ s, (if s ∈ Ioo (0 : ℝ) H ∧ t ∈ Ioo (0 : ℝ) s then (1 : ℝ≥0∞) else 0) *
              (ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) * U t) = 0 := fun s => by
            have hnot : ¬ (s ∈ Ioo (0 : ℝ) H ∧ t ∈ Ioo (0 : ℝ) s) := by
              rintro ⟨hs1, hs2⟩
              exact ht ⟨hs2.1, hs2.2.trans hs1.2⟩
            rw [ite_eq_right_iff.2 (fun h => absurd h hnot), zero_mul]
          simp_rw [hzero, lintegral_zero]
      rw [hL, hR, lintegral_lintegral_swap hm_prod.aemeasurable]
    rw [← hL, h_swap]
    have hle : ∫⁻ t in Ioo (0 : ℝ) H, U t *
        ∫⁻ s in Ioo t H, ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) ≤
        ENNReal.ofReal (H + 2 * Real.sqrt H) * ∫⁻ t in Ioo (0 : ℝ) H, U t := by
      rw [← lintegral_const_mul _ hmU]
      refine setLIntegral_mono_ae (hmU.const_mul _).aemeasurable ?_
      filter_upwards with t ht
      rw [mul_comm]
      have hker := LeafBAux.lintegral_kernel_s_le hH ht
      gcongr
    exact hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hU_L1)
  have hae_fin := ae_lt_top' hm_prod.lintegral_prod_right'.aemeasurable hTonelli.ne
  filter_upwards [hae_fin] with s hs_fin_prod hs
  have hs_fin : ∫⁻ t in Ioo (0 : ℝ) s, ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) * U t < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq ?_) hs_fin_prod
    rw [← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun t => ?_
    by_cases ht : t ∈ Ioo (0 : ℝ) s <;> simp [hs, ht]
  have hm_rhs_s : Measurable fun t : ℝ => ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) * U t :=
    (ENNReal.measurable_ofReal.comp (measurable_const.add ((measurable_const.sub measurable_id).pow_const _))).mul hmU
  have hle_s : ∫⁻ t in Ioo (0 : ℝ) s, ENNReal.ofReal (vortKernel C_clock P ν μ s t) *
      (ENNReal.ofReal (C_dual * A_m) * U t) ≤
      ENNReal.ofReal C₀ * ∫⁻ t in Ioo (0 : ℝ) s,
        ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) * U t := by
    rw [← lintegral_const_mul _ hm_rhs_s]
    refine setLIntegral_mono_ae (hm_rhs_s.const_mul _).aemeasurable ?_
    filter_upwards with t ht
    have hts1 : t / s ≤ 1 := (div_le_one hs.1).2 ht.2.le
    have hrpow1 : (t / s) ^ μ.re ≤ 1 := Real.rpow_le_one (div_nonneg ht.1.le hs.1.le) hts1 hμ_pos.le
    have hker : vortKernel C_clock P ν μ s t * (C_dual * A_m) ≤
        C₀ * (1 + (s - t) ^ (-1 / 2 : ℝ)) := by
      unfold vortKernel
      rw [hC₀_def]
      have h1 : |C_clock| * ν ^ (-(weakDegree 9 P.kappa : ℝ)) * (t / s) ^ μ.re *
          (1 + (s - t) ^ (-1 / 2 : ℝ)) * (C_dual * A_m) ≤
          |C_clock| * ν ^ (-(weakDegree 9 P.kappa : ℝ)) * 1 *
            (1 + (s - t) ^ (-1 / 2 : ℝ)) * (C_dual * A_m) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hrpow1 (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hν0.le _)))
            (add_nonneg zero_le_one (Real.rpow_nonneg (sub_nonneg.2 ht.2.le) _)))
          (mul_nonneg hCdual hAm)
      calc |C_clock| * ν ^ (-(weakDegree 9 P.kappa : ℝ)) * (t / s) ^ μ.re *
            (1 + (s - t) ^ (-1 / 2 : ℝ)) * (C_dual * A_m)
          ≤ |C_clock| * ν ^ (-(weakDegree 9 P.kappa : ℝ)) * 1 *
              (1 + (s - t) ^ (-1 / 2 : ℝ)) * (C_dual * A_m) := h1
        _ = |C_clock| * ν ^ (-(weakDegree 9 P.kappa : ℝ)) * (C_dual * A_m) *
              (1 + (s - t) ^ (-1 / 2 : ℝ)) := by ring
    calc ENNReal.ofReal (vortKernel C_clock P ν μ s t) * (ENNReal.ofReal (C_dual * A_m) * U t)
        = ENNReal.ofReal (vortKernel C_clock P ν μ s t * (C_dual * A_m)) * U t := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by
            unfold vortKernel
            exact mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hν0.le _))
              (Real.rpow_nonneg (div_nonneg ht.1.le hs.1.le) _))
              (add_nonneg zero_le_one (Real.rpow_nonneg (sub_nonneg.2 ht.2.le) _)))]
      _ ≤ ENNReal.ofReal (C₀ * (1 + (s - t) ^ (-1 / 2 : ℝ))) * U t := by
          gcongr
      _ = ENNReal.ofReal C₀ * (ENNReal.ofReal (1 + (s - t) ^ (-1 / 2 : ℝ)) * U t) := by
          rw [ENNReal.ofReal_mul (by
            rw [hC₀_def]
            exact mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hν0.le _))
              (mul_nonneg hCdual hAm)), mul_assoc]
  exact hle_s.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hs_fin)

end UnforcedLeray.Short.IIIa
