import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3_1_1.Transport
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3_1_1.Interaction

/-!
# `PartII-b:F2/3/1/1` (`Sub/PartII-b_F2_3_1_1.lean`): `PlanarEulerFamily`

Source of record: `the November 2 reference manuscript` (SP) lines 841-852,
931-953, 2121-2123.

Constructs the frozen planar Euler semigroup `E_pl m σ τ` on `Xm m` as the realification of
`Planar.eulerGroupDil hm ha τ` on `Planar.L2w m`, proves real-preservation of `eulerGroupW` and
the Duhamel identity against `T_pl m σ` and any `IsPlanarInteractionOp m σ A`, and establishes
uniqueness of any `(E, T)` satisfying `EulerData m Sig E T`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIb

namespace PlanarEulerBridge

/-! ## 1. Real-preservation of `eulerGroupW` and `eulerGroupDil` -/

theorem dilW_inv_apply {m : ℝ} (hm : 1 < m) {a : ℝ} (ha : 0 < a) (z : Planar.L2w m) :
    Planar.dilW hm (inv_pos.2 ha) (Planar.dilW hm ha z) = z := by
  have h := congrArg (fun L : Planar.L2w m →L[ℂ] Planar.L2w m => L z) (Planar.dilW_inv_comp hm ha)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] using h

theorem dilW_comp_inv_apply {m : ℝ} (hm : 1 < m) {a : ℝ} (ha : 0 < a) (z : Planar.L2w m) :
    Planar.dilW hm ha (Planar.dilW hm (inv_pos.2 ha) z) = z := by
  have h := congrArg (fun L : Planar.L2w m →L[ℂ] Planar.L2w m => L z) (Planar.dilW_comp_inv hm ha)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] using h

theorem preservesReal_eulerGroupW {m : ℝ} (hm : 1 < m) {t : ℝ} (ht : 0 ≤ t) :
    PreservesReal (Planar.eulerGroupW hm t) := by
  intro f
  let u : ℝ → Xm m := fun s => imXm m (Planar.eulerGroupW hm s (toL2w m f))
  have hu_cont : Continuous u :=
    (imXm m).continuous.comp (Planar.continuous_eulerGroupW_apply hm (toL2w m f))
  set K : ℝ := ‖realify (Planar.couplingW hm)‖
  have hbound : ∀ s ∈ Icc 0 t, ‖u s‖ ≤ K * ∫ r in (0 : ℝ)..s, ‖u r‖ := by
    intro s hs
    let G : ℝ → Planar.L2w m := fun r =>
      Planar.transportGroupW m (s - r)
        (Planar.couplingW hm (Planar.eulerGroupW hm r (toL2w m f)))
    have hG_cont : Continuous G := by
      rw [ ← continuousOn_univ]
      exact continuousOn_strong_apply (Planar.norm_transportGroupW_le m)
        (Planar.continuous_transportGroupW_apply m)
        (continuous_const.sub continuous_id).continuousOn
        ((Planar.couplingW hm).continuous.comp
          (Planar.continuous_eulerGroupW_apply hm (toL2w m f))).continuousOn
    have hG_int : IntervalIntegrable G volume 0 s := hG_cont.intervalIntegrable 0 s
    have hduh := congrArg (imXm m) (Planar.eulerGroupW_eq_duhamel hm s (toL2w m f))
    rw [map_add, preservesReal_transportGroupW m s f, zero_add,
      ← (imXm m).intervalIntegral_comp_comm hG_int] at hduh
    change u s = ∫ r in (0 : ℝ)..s, imXm m (G r) at hduh
    rw [hduh]
    have hnorm_le : ∀ r ∈ Icc 0 s, ‖imXm m (G r)‖ ≤ K * ‖u r‖ := by
      intro r _
      have him : imXm m (G r) =
          realify (Planar.transportGroupW m (s - r)) (realify (Planar.couplingW hm) (u r)) := by
        dsimp [G, u]
        rw [(preservesReal_transportGroupW m (s - r)).imXm_apply,
          (preservesReal_couplingW hm).imXm_apply]
      rw [him]
      have htr1 : ‖realify (Planar.transportGroupW m (s - r))‖ ≤ 1 :=
        (norm_realify_le _).trans (Planar.norm_transportGroupW_le m (s - r))
      calc ‖realify (Planar.transportGroupW m (s - r)) (realify (Planar.couplingW hm) (u r))‖
          ≤ ‖realify (Planar.transportGroupW m (s - r))‖ *
              ‖realify (Planar.couplingW hm) (u r)‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * (K * ‖u r‖) := mul_le_mul htr1 (ContinuousLinearMap.le_opNorm _ _)
            (norm_nonneg _) zero_le_one
        _ = K * ‖u r‖ := one_mul _
    calc ‖∫ r in (0 : ℝ)..s, imXm m (G r)‖
        ≤ ∫ r in (0 : ℝ)..s, K * ‖u r‖ :=
          intervalIntegral.norm_integral_le_of_norm_le hs.1
            (Eventually.of_forall fun r hr => hnorm_le r ⟨hr.1.le, hr.2⟩)
            ((hu_cont.norm.const_mul K).intervalIntegrable 0 s)
      _ = K * ∫ r in (0 : ℝ)..s, ‖u r‖ := intervalIntegral.integral_const_mul K _
  have hzero := gronwall_zero_Icc ht (norm_nonneg _) hu_cont.norm.continuousOn
    (fun _ _ => norm_nonneg _) hbound t ⟨ht, le_rfl⟩
  exact norm_eq_zero.1 hzero

theorem preservesReal_eulerGroupDil {m : ℝ} (hm : 1 < m) {σ : ℝ} (ha : 0 < 1 + σ)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    PreservesReal (Planar.eulerGroupDil hm ha τ) := by
  rw [Planar.dilation_conj hm ha τ]
  exact (preservesReal_dilW hm ha).comp
    ((preservesReal_eulerGroupW hm (div_nonneg hτ (sq_nonneg _))).comp
      (preservesReal_dilW hm (inv_pos.2 ha)))

/-! ## 2. The frozen planar Euler semigroup `E_pl` on `Xm m` -/

/-- Frozen planar Euler semigroup `E_pl m σ τ` on `Xm m`. -/
def E_pl (m σ τ : ℝ) : Xm m →L[ℝ] Xm m :=
  if h : 1 < m ∧ 0 < 1 + σ then realify (Planar.eulerGroupDil h.1 h.2 τ)
  else ContinuousLinearMap.id ℝ (Xm m)

theorem E_pl_eq {m : ℝ} (hm : 1 < m) {σ : ℝ} (ha : 0 < 1 + σ) (τ : ℝ) :
    E_pl m σ τ = realify (Planar.eulerGroupDil hm ha τ) :=
  dif_pos ⟨hm, ha⟩

theorem toL2w_E_pl {m : ℝ} (hm : 1 < m) {σ : ℝ} (ha : 0 < 1 + σ) {τ : ℝ} (hτ : 0 ≤ τ)
    (f : Xm m) :
    toL2w m (E_pl m σ τ f) = Planar.eulerGroupDil hm ha τ (toL2w m f) := by
  rw [E_pl_eq hm ha τ]
  exact (preservesReal_eulerGroupDil hm ha hτ).toL2w_realify f

theorem eulerGroupDil_zero {m : ℝ} (hm : 1 < m) {a : ℝ} (ha : 0 < a) :
    Planar.eulerGroupDil hm ha 0 = 1 := by
  rw [Planar.dilation_conj hm ha 0, zero_div, Planar.eulerGroupW_zero hm]
  ext1 z
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]
  exact dilW_comp_inv_apply hm ha z

theorem eulerGroupDil_add {m : ℝ} (hm : 1 < m) {a : ℝ} (ha : 0 < a) (τ₁ τ₂ : ℝ) :
    Planar.eulerGroupDil hm ha (τ₁ + τ₂) =
      Planar.eulerGroupDil hm ha τ₁ ∘L Planar.eulerGroupDil hm ha τ₂ := by
  rw [Planar.dilation_conj hm ha (τ₁ + τ₂), Planar.dilation_conj hm ha τ₁,
    Planar.dilation_conj hm ha τ₂, add_div, Planar.eulerGroupW_add hm]
  ext1 z
  simp only [ContinuousLinearMap.comp_apply, dilW_inv_apply hm ha]

theorem E_pl_zero {m : ℝ} (hm : 1 < m) {σ : ℝ} (ha : 0 < 1 + σ) :
    E_pl m σ 0 = ContinuousLinearMap.id ℝ (Xm m) := by
  rw [E_pl_eq hm ha 0, eulerGroupDil_zero hm ha, realify_one]

theorem E_pl_add {m : ℝ} (hm : 1 < m) {σ : ℝ} (ha : 0 < 1 + σ)
    {τ₁ τ₂ : ℝ} (hτ₁ : 0 ≤ τ₁) (hτ₂ : 0 ≤ τ₂) :
    E_pl m σ (τ₁ + τ₂) = (E_pl m σ τ₁).comp (E_pl m σ τ₂) := by
  rw [E_pl_eq hm ha (τ₁ + τ₂), E_pl_eq hm ha τ₁, E_pl_eq hm ha τ₂, eulerGroupDil_add hm ha]
  exact (preservesReal_eulerGroupDil hm ha hτ₁).realify_comp
    (preservesReal_eulerGroupDil hm ha hτ₂)

theorem continuous_E_pl_apply {m : ℝ} (hm : 1 < m) {σ : ℝ} (ha : 0 < 1 + σ) (f : Xm m) :
    Continuous fun τ => E_pl m σ τ f := by
  let W₀ : Planar.L2w m := Planar.dilW hm (inv_pos.2 ha) (toL2w m f)
  have heq : (fun τ => E_pl m σ τ f) = fun τ =>
      reXm m (Planar.dilW hm ha (Planar.eulerGroupW hm (τ / (1 + σ) ^ 2) W₀)) := by
    funext τ
    rw [E_pl_eq hm ha τ, realify_apply, Planar.dilation_conj hm ha τ]
    rfl
  rw [heq]
  have h1 : Continuous fun τ : ℝ => Planar.eulerGroupW hm (τ / (1 + σ) ^ 2) W₀ :=
    (Planar.continuous_eulerGroupW_apply hm W₀).comp (continuous_id.div_const _)
  have h2 : Continuous fun τ : ℝ =>
      Planar.dilW hm ha (Planar.eulerGroupW hm (τ / (1 + σ) ^ 2) W₀) :=
    (Planar.dilW hm ha).continuous.comp h1
  exact (reXm m).continuous.comp h2

theorem duhamel_E_pl {m : ℝ} (hm : 1 < m) {σ : ℝ} (ha : 0 < 1 + σ)
    {A : Xm m →L[ℝ] Xm m} (hA : IsPlanarInteractionOp m σ A)
    {τ : ℝ} (hτ : 0 ≤ τ) (f : Xm m) :
    IntervalIntegrable (fun r => T_pl m σ (τ - r) (A (E_pl m σ r f))) volume 0 τ ∧
      E_pl m σ τ f = T_pl m σ τ f + ∫ r in (0 : ℝ)..τ, T_pl m σ (τ - r) (A (E_pl m σ r f)) := by
  have hA_eq : A = A_pl m σ := IsPlanarInteractionOp.unique hA (isPlanarInteractionOp_A_pl hm ha)
  rw [hA_eq]
  have hint_cont : Continuous fun r => T_pl m σ (τ - r) (A_pl m σ (E_pl m σ r f)) := by
    rw [← continuousOn_univ]
    exact continuousOn_strong_apply (norm_T_pl_le m σ) (continuous_T_pl_apply hm ha)
      (continuous_const.sub continuous_id).continuousOn
      ((A_pl m σ).continuous.comp (continuous_E_pl_apply hm ha f)).continuousOn
  have hint : IntervalIntegrable
      (fun r => T_pl m σ (τ - r) (A_pl m σ (E_pl m σ r f))) volume 0 τ :=
    hint_cont.intervalIntegrable 0 τ
  refine ⟨hint, (toL2w m).injective ?_⟩
  set a : ℝ := 1 + σ
  let y₀ : Planar.L2w m := Planar.dilW hm (inv_pos.2 ha) (toL2w m f)
  let F : ℝ → Planar.L2w m := fun u =>
    Planar.transportGroupW m (τ / a ^ 2 - u)
      (Planar.couplingW hm (Planar.eulerGroupW hm u y₀))
  have hF_cont : Continuous F := by
    rw [← continuousOn_univ]
    exact continuousOn_strong_apply (Planar.norm_transportGroupW_le m)
      (Planar.continuous_transportGroupW_apply m)
      (continuous_const.sub continuous_id).continuousOn
      ((Planar.couplingW hm).continuous.comp
        (Planar.continuous_eulerGroupW_apply hm y₀)).continuousOn
  have hintF : IntervalIntegrable (fun r => F (r / a ^ 2)) volume 0 τ :=
    (hF_cont.comp (continuous_id.div_const (a ^ 2))).intervalIntegrable 0 τ
  let D : Planar.L2w m →L[ℂ] Planar.L2w m := (((a ^ 2)⁻¹ : ℝ) : ℂ) • Planar.dilW hm ha
  rw [toL2w_E_pl hm ha hτ f, map_add, toL2w_T_pl hm ha τ f]
  have hcomm := (toL2w m).toContinuousLinearMap.intervalIntegral_comp_comm hint
  change (∫ r in (0 : ℝ)..τ, (toL2w m) (T_pl m σ (τ - r) (A_pl m σ (E_pl m σ r f)))) =
    (toL2w m) (∫ r in (0 : ℝ)..τ, T_pl m σ (τ - r) (A_pl m σ (E_pl m σ r f))) at hcomm
  rw [← hcomm]
  have hcongr : (∫ r in (0 : ℝ)..τ,
      (toL2w m) (T_pl m σ (τ - r) (A_pl m σ (E_pl m σ r f)))) =
      ∫ r in (0 : ℝ)..τ, D (F (r / a ^ 2)) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hτ] at hr
    rw [toL2w_T_pl hm ha (τ - r), toL2w_A_pl hm ha, toL2w_E_pl hm ha hr.1,
      Planar.dilation_conj hm ha r]
    unfold transportDil couplingDil D F y₀
    simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul,
      dilW_inv_apply hm ha, sub_div]
    rfl
  have hcommD := (D.restrictScalars ℝ).intervalIntegral_comp_comm hintF
  change (∫ r in (0 : ℝ)..τ, D (F (r / a ^ 2))) =
    D (∫ r in (0 : ℝ)..τ, F (r / a ^ 2)) at hcommD
  rw [hcongr, hcommD]
  change Planar.eulerGroupDil hm ha τ (toL2w m f) =
    transportDil hm ha τ (toL2w m f) + D (∫ r in (0 : ℝ)..τ, F (r / a ^ 2))
  have hD_int : D (∫ r in (0 : ℝ)..τ, F (r / a ^ 2)) =
      Planar.dilW hm ha (∫ u in (0 : ℝ)..(τ / a ^ 2), F u) := by
    change (((a ^ 2)⁻¹ : ℝ) : ℂ) • Planar.dilW hm ha (∫ r in (0 : ℝ)..τ, F (r / a ^ 2)) = _
    rw [← map_smul]
    congr 1
    rw [Complex.coe_smul]
    exact (intervalIntegral.inv_smul_integral_comp_div F (a ^ 2)).trans (by rw [zero_div])
  rw [hD_int, Planar.dilation_conj hm ha τ]
  unfold transportDil
  simp only [ContinuousLinearMap.comp_apply, ← map_add]
  congr 1
  exact Planar.eulerGroupW_eq_duhamel hm (τ / a ^ 2) y₀

/-! ## 3. `EulerData` verification and uniqueness -/

theorem eulerData_E_pl_T_pl {m Sig : ℝ} (hm : 8 < m) :
    PlanarFrozenF231.EulerData m Sig (E_pl m) (T_pl m) := by
  have hm1 : 1 < m := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ hσ
    have ha : 0 < 1 + σ := by linarith [hσ.1]
    exact ⟨E_pl_zero hm1 ha, fun τ₁ τ₂ h1 h2 => E_pl_add hm1 ha h1 h2,
      fun f => (continuous_E_pl_apply hm1 ha f).continuousOn⟩
  · intro σ hσ
    have ha : 0 < 1 + σ := by linarith [hσ.1]
    exact ⟨T_pl_zero m σ, T_pl_add m σ ha.le, norm_T_pl_apply m σ,
      continuous_T_pl_apply hm1 ha, coeFn_T_pl m σ⟩
  · intro σ hσ
    have ha : 0 < 1 + σ := by linarith [hσ.1]
    exact ⟨A_pl m σ, isPlanarInteractionOp_A_pl hm1 ha⟩
  · intro σ hσ A hA τ hτ f
    have ha : 0 < 1 + σ := by linarith [hσ.1]
    exact duhamel_E_pl hm1 ha hA hτ f

/-- Uniqueness of `EulerData`: any `(E, T)` satisfying `EulerData m Sig E T` coincides with
`(E_pl m, T_pl m)` for all `σ ∈ Icc 0 Sig` and `τ ≥ 0`. -/
theorem eulerData_unique {m Sig : ℝ} (hm : 8 < m)
    {E T : ℝ → ℝ → (Xm m →L[ℝ] Xm m)} (hD : PlanarFrozenF231.EulerData m Sig E T)
    {σ : ℝ} (hσ : σ ∈ Icc 0 Sig) :
    (∀ τ : ℝ, T σ τ = T_pl m σ τ) ∧ (∀ τ : ℝ, 0 ≤ τ → E σ τ = E_pl m σ τ) := by
  have hm1 : 1 < m := by linarith
  have ha : 0 < 1 + σ := by linarith [hσ.1]
  obtain ⟨hE, hT, -, hduh⟩ := hD
  have hT_eq : ∀ τ : ℝ, T σ τ = T_pl m σ τ := by
    intro τ
    ext1 f
    exact Lp.ext (((hT σ hσ).2.2.2.2 τ f).trans (coeFn_T_pl m σ τ f).symm)
  refine ⟨hT_eq, fun τ hτ => ?_⟩
  ext1 f
  let A₀ : Xm m →L[ℝ] Xm m := A_pl m σ
  have hA₀ : IsPlanarInteractionOp m σ A₀ := isPlanarInteractionOp_A_pl hm1 ha
  let d : ℝ → Xm m := fun s => E σ s f - E_pl m σ s f
  have hd_cont : ContinuousOn d (Icc 0 τ) :=
    (((hE σ hσ).2.2 f).sub (continuous_E_pl_apply hm1 ha f).continuousOn).mono
      (Icc_subset_Ici_self)
  have hbound : ∀ s ∈ Icc 0 τ, ‖d s‖ ≤ ‖A₀‖ * ∫ r in (0 : ℝ)..s, ‖d r‖ := by
    intro s hs
    obtain ⟨hint1, heq1⟩ := hduh σ hσ A₀ hA₀ s hs.1 f
    obtain ⟨hint2, heq2⟩ := duhamel_E_pl hm1 ha hA₀ hs.1 f
    have hsub : d s =
        ∫ r in (0 : ℝ)..s,
          (T σ (s - r) (A₀ (E σ r f)) - T_pl m σ (s - r) (A₀ (E_pl m σ r f))) := by
      dsimp [d]
      rw [heq1, heq2, hT_eq s, add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub hint1 hint2]
    have hcongr : (∫ r in (0 : ℝ)..s,
        (T σ (s - r) (A₀ (E σ r f)) - T_pl m σ (s - r) (A₀ (E_pl m σ r f)))) =
        ∫ r in (0 : ℝ)..s, T_pl m σ (s - r) (A₀ (d r)) := by
      refine intervalIntegral.integral_congr fun r _ => ?_
      rw [hT_eq (s - r), ← map_sub, ← map_sub]
    rw [hsub, hcongr]
    have hd_s : ContinuousOn (fun r => ‖A₀‖ * ‖d r‖) (Icc 0 s) :=
      (hd_cont.mono (Icc_subset_Icc le_rfl hs.2)).norm.const_mul ‖A₀‖
    have hint_norm : IntervalIntegrable (fun r => ‖A₀‖ * ‖d r‖) volume 0 s := by
      apply ContinuousOn.intervalIntegrable
      rwa [uIcc_of_le hs.1]
    calc ‖∫ r in (0 : ℝ)..s, T_pl m σ (s - r) (A₀ (d r))‖
        ≤ ∫ r in (0 : ℝ)..s, ‖A₀‖ * ‖d r‖ :=
          intervalIntegral.norm_integral_le_of_norm_le hs.1
            (Eventually.of_forall fun r _ => by
              rw [norm_T_pl_apply]
              exact A₀.le_opNorm (d r))
            hint_norm
      _ = ‖A₀‖ * ∫ r in (0 : ℝ)..s, ‖d r‖ := intervalIntegral.integral_const_mul ‖A₀‖ _
  have hzero := gronwall_zero_Icc hτ (norm_nonneg A₀) hd_cont.norm
    (fun _ _ => norm_nonneg _) hbound τ ⟨hτ, le_rfl⟩
  exact sub_eq_zero.1 (norm_eq_zero.1 hzero)

end PlanarEulerBridge

/-- **Leaf `PartII-b:F2/3/1/1`**: existence of the frozen planar Euler family `(E_pl, T_pl)`. -/
theorem planarEulerFamily : UnforcedLeray.Short.IIb.PlanarFrozenF231.PlanarEulerFamily := by
  intro m hm Sig _hSig
  exact ⟨PlanarEulerBridge.E_pl m, PlanarEulerBridge.T_pl m,
    PlanarEulerBridge.eulerData_E_pl_T_pl hm⟩

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.planarEulerFamily
