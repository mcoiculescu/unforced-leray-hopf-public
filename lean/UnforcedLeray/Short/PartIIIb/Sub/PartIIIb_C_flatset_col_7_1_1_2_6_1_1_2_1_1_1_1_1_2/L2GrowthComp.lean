import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1_1_2

/-!
# Polynomial growth of parametric derivatives (`T0gGrowthComp`)

Source `the November 2 reference manuscript`
lines 1640-1656. The map `y ↦ (y.2.1, y.2.2 - planeι (y.1 • w))` is linear in `y` with operator
norm `≤ 1 + ‖w‖`. The `k`-th derivative of `F ∘ L_w` is the `k`-th derivative of `F` composed
with `k` copies of `L_w`, so its norm is `≤ C_k ‖L_w‖^k ≤ C_k (1+‖w‖)^k`. Take `N = k`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

/-- The linear part `y ↦ (y.2.1, y.2.2 - planeι (y.1 • w))`. -/
def t0g_linW (w : UnforcedLeray.Gaussian.Euc 2) :
    (ℝ × ℝ × (ℝ × ℝ)) →ₗ[ℝ] (ℝ × ℝ × ℝ) where
  toFun y := (y.2.1, y.2.2 - UnforcedLeray.B0224.planeι (y.1 • w))
  map_add' y z := by
    refine Prod.ext rfl ?_
    simp only [Prod.fst_add, Prod.snd_add, add_smul, map_add]
    abel
  map_smul' c y := by
    refine Prod.ext rfl ?_
    have hp : ∀ (a : ℝ) (v : UnforcedLeray.Gaussian.Euc 2),
        UnforcedLeray.B0224.planeι (a • v) = a • UnforcedLeray.B0224.planeι v := by
      intro a v
      rw [UnforcedLeray.B0224.planeι_apply, UnforcedLeray.B0224.planeι_apply]
      ext <;> simp
    simp only [RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul, hp,
      Prod.smul_mk, smul_sub]

theorem t0g_linW_norm (w : UnforcedLeray.Gaussian.Euc 2) (y : ℝ × ℝ × (ℝ × ℝ)) :
    ‖t0g_linW w y‖ ≤ (1 + ‖w‖) * ‖y‖ := by
  have hpl : ∀ v : UnforcedLeray.Gaussian.Euc 2,
      ‖UnforcedLeray.B0224.planeι v‖ ≤ ‖v‖ := by
    intro v
    rw [UnforcedLeray.B0224.planeι_apply, Prod.norm_def]
    exact max_le (PiLp.norm_apply_le v 0) (PiLp.norm_apply_le v 1)
  have hv : ‖UnforcedLeray.B0224.planeι (y.1 • w)‖ ≤ ‖y‖ * ‖w‖ := by
    refine (hpl _).trans ?_
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (norm_fst_le y) (norm_nonneg _)
  have h1 : ‖y.2.1‖ ≤ ‖y‖ := (norm_fst_le y.2).trans (norm_snd_le y)
  have h2 : ‖y.2.2‖ ≤ ‖y‖ := (norm_snd_le y.2).trans (norm_snd_le y)
  show ‖((y.2.1, y.2.2 - UnforcedLeray.B0224.planeι (y.1 • w)) : ℝ × ℝ × ℝ)‖ ≤ _
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · exact h1.trans (le_mul_of_one_le_left (norm_nonneg y) (by linarith [norm_nonneg w]))
  · calc ‖y.2.2 - UnforcedLeray.B0224.planeι (y.1 • w)‖
        ≤ ‖y.2.2‖ + ‖UnforcedLeray.B0224.planeι (y.1 • w)‖ := norm_sub_le _ _
      _ ≤ ‖y‖ + ‖y‖ * ‖w‖ := add_le_add h2 hv
      _ = (1 + ‖w‖) * ‖y‖ := by ring

/-- The linear part as a continuous linear map, with norm `≤ 1 + ‖w‖`. -/
def t0g_clmW (w : UnforcedLeray.Gaussian.Euc 2) :
    (ℝ × ℝ × (ℝ × ℝ)) →L[ℝ] (ℝ × ℝ × ℝ) :=
  LinearMap.mkContinuous (t0g_linW w) (1 + ‖w‖) (fun y => t0g_linW_norm w y)

theorem t0g_clmW_norm_le (w : UnforcedLeray.Gaussian.Euc 2) :
    ‖t0g_clmW w‖ ≤ 1 + ‖w‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

theorem t0g_growthComp :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gGrowthComp := by
  unfold UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gGrowthComp
  intro F hF hbd k
  obtain ⟨C, hC⟩ := hbd k
  refine ⟨C, k, fun x w => ?_⟩
  have hfun : (fun y : ℝ × ℝ × (ℝ × ℝ) =>
      F (y.2.1, y.2.2 - UnforcedLeray.B0224.planeι (y.1 • w))) = F ∘ (t0g_clmW w) := rfl
  have hk : ((k : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_top
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right (t0g_clmW w) hF x hk]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  exact mul_le_mul (hC _) (pow_le_pow_left₀ (norm_nonneg _) (t0g_clmW_norm_le w) k)
    (by positivity) hC0

end
