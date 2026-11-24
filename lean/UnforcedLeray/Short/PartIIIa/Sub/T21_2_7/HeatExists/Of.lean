import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.Leaves
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.Pairing

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8`: `AdjHeatExists m` from the leaves H1-H6

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
(the free part of the Volterra iteration: the periodic heat semigroup of diffusivity `ν` and its
heat-divergence response on `X_{-m,c}`, at fixed `ν > 0`, `c > 0`). Leaves:
`HeatExists/Leaves.lean`.

Construction at fixed `ν, c` (`AdjFreeData` bundles the conclusions of H1-H4):
* `S₀(τ)` (`AdjFreeData.S0`) is the bounded operator `kerCLM` of the Gaussian `G_{ντ}` for
  `τ ∈ (0, 1]` (H1) and the identity otherwise (in particular `S₀(0) = 1`);
* `S(τ)(F, h) = -(K₀(τ)F₀ + K₁(τ)F₁) + S₀(τ)h` (`AdjFreeData.S`), `K_j(τ)` the bounded operator
  of `∂_j G_{ντ}` (H2), so `S(τ)` acts as `adjSFun` (`coeFn_S`) with
  `‖S(τ)‖ ≤ (2C₁ + M₀) τ^{-1/2}`;
* the semigroup laws come from H4 through the a.e. representatives; strong continuity of `S₀`
  on `[0, 1]` from H3 (right continuity at `0`), the semigroup law and the uniform bound; that of
  `S` on `(0, 1]` from `S(τ) = S₀(τ - τ₀/2) S(τ₀/2)`;
* the weak identities: (a) is H5 through the representatives; (b) is H6 after commuting the test
  pairing (`adjPairing`) with the Bochner integral (`adjHeat_duhamel_pair`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Infra.VolterraEvolution

/-! ## Duhamel integrals of a square-root smoothing family -/

/-- The Duhamel integrand `r ↦ S(u - r) F(r)` is interval integrable on `[a, u]` for a
continuous source path `F` on `[a, b] ⊆ [a, a + 1]` (`‖S(τ)‖ ≤ C τ^{-1/2}`, strong continuity on
`(0, 1]`). -/
theorem adjHeat_duhamel_intervalIntegrable {c m C : ℝ} (S : ℝ → AdjY c m →L[ℂ] AdjX c m)
    (hC : 0 ≤ C)
    (hS : ∀ τ, 0 < τ → τ ≤ 1 → ‖S τ‖ ≤ C * τ ^ (-(1 / 2 : ℝ)))
    (hSc : ∀ y, ContinuousOn (fun τ => S τ y) (Ioc 0 1))
    {F : ℝ → AdjY c m} {a b u : ℝ} (hb : b ≤ a + 1) (hF : ContinuousOn F (Icc a b))
    (hu : u ∈ Icc a b) :
    IntervalIntegrable (fun r => S (u - r) (F r)) volume a u := by
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hu.1]
  have hg : IntervalIntegrable (fun r => C * (u - r) ^ (-(1 / 2 : ℝ)) * A) volume a u :=
    ((intervalIntegrable_kernel u a u).const_mul C).mul_const A
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hu.1] at hg
  have hcont : ContinuousOn (fun r => S (u - r) (F r)) (Ioo a u) := by
    refine continuousOn_clm_apply (K := fun r => S (u - r)) ?_ ?_
      (hF.mono fun r hr => ⟨hr.1.le, hr.2.le.trans hu.2⟩)
    · intro y
      refine (hSc y).comp (continuousOn_const.sub continuousOn_id) ?_
      intro r hr
      exact ⟨by linarith [hr.2], by linarith [hr.1, hu.2]⟩
    · intro r₀ hr₀
      have hpos : 0 < u - r₀ := by linarith [hr₀.2]
      refine ⟨C * ((u - r₀) / 2) ^ (-(1 / 2 : ℝ)), ?_⟩
      have ht : Tendsto (fun r => u - r) (𝓝 r₀) (𝓝 (u - r₀)) :=
        tendsto_const_nhds.sub tendsto_id
      have hnear : ∀ᶠ r in 𝓝 r₀, (u - r₀) / 2 < u - r :=
        ht.eventually (lt_mem_nhds (half_lt_self hpos))
      filter_upwards [nhdsWithin_le_nhds hnear, self_mem_nhdsWithin] with r hr hrU
      have h0 : 0 < u - r := lt_trans (half_pos hpos) hr
      have h1 : u - r ≤ 1 := by linarith [hrU.1, hu.2]
      refine (hS (u - r) h0 h1).trans ?_
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (half_pos hpos) hr.le (by norm_num)) hC
  refine Integrable.mono' hg (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun r hr => ?_)
  have h0 : 0 < u - r := by linarith [hr.2]
  have h1 : u - r ≤ 1 := by linarith [hr.1, hu.2]
  calc ‖S (u - r) (F r)‖ ≤ ‖S (u - r)‖ * ‖F r‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (C * (u - r) ^ (-(1 / 2 : ℝ))) * A :=
        mul_le_mul (hS _ h0 h1) (hA r ⟨hr.1.le, hr.2.le.trans hu.2⟩) (norm_nonneg _)
          (mul_nonneg hC (Real.rpow_nonneg h0.le _))

/-- The test pairing commutes with the Duhamel integral (`adjPairing`). -/
theorem adjHeat_duhamel_pair {c m C : ℝ} (hc : 0 < c) (S : ℝ → AdjY c m →L[ℂ] AdjX c m)
    (hC : 0 ≤ C)
    (hS : ∀ τ, 0 < τ → τ ≤ 1 → ‖S τ‖ ≤ C * τ ^ (-(1 / 2 : ℝ)))
    (hSc : ∀ y, ContinuousOn (fun τ => S τ y) (Ioc 0 1))
    {F : ℝ → AdjY c m} {a b u : ℝ} (hb : b ≤ a + 1) (hF : ContinuousOn F (Icc a b))
    (hu : u ∈ Icc a b) {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ) :
    ∫ x in B0579.cell c, (∫ r in a..u, S (u - r) (F r)) x * (φ x : ℂ) =
      ∫ r in a..u, ∫ x in B0579.cell c, (S (u - r) (F r)) x * (φ x : ℂ) := by
  obtain ⟨-, L, hL⟩ := adjPairing c m hc φ hφ
  rw [← hL (∫ r in a..u, S (u - r) (F r)),
    ← ContinuousLinearMap.intervalIntegral_comp_comm L
      (adjHeat_duhamel_intervalIntegrable S hC hS hSc hb hF hu)]
  exact intervalIntegral.integral_congr fun r _ => hL _

/-- Cell integrals against a test only see the `X_{-m,c}`-class. -/
theorem adjHeat_cell_integral_congr {c m : ℝ} {f g : ℝ × ℝ → ℂ}
    (h : f =ᵐ[B0579.cellMeasure c (-m)] g) (ψ : ℝ × ℝ → ℝ) :
    ∫ x in B0579.cell c, f x * (ψ x : ℂ) = ∫ x in B0579.cell c, g x * (ψ x : ℂ) := by
  refine integral_congr_ae ?_
  filter_upwards [(B0579.ac_cellMeasure c (-m)).ae_le h] with x hx
  rw [hx]

/-! ## The concrete free part at fixed `ν, c` -/

/-- The conclusions of H1-H4 at fixed `ν, c` (the Young constants `M₀`, `C₁` are data). -/
structure AdjFreeData (ν c m : ℝ) where
  hc : 0 < c
  M₀ : ℝ
  C₁ : ℝ
  hM₀ : 0 ≤ M₀
  hC₁ : 0 ≤ C₁
  young0 : ∀ τ ∈ Ioc (0 : ℝ) 1, KerYoung c m (adjHeatKer ν τ) M₀
  young1 : ∀ τ ∈ Ioc (0 : ℝ) 1, ∀ j : Fin 2,
    KerYoung c m (adjHeatGradKer ν τ j) (C₁ * τ ^ (-(1 / 2 : ℝ)))
  strong0 : ∀ w : AdjX c m,
    Tendsto (fun τ => eLpNorm (fun x => adjS0Fun ν c τ (⇑w) x - w x) 2
      (B0579.cellMeasure c (-m))) (𝓝[>] 0) (𝓝 0)
  semi0 : ∀ a b : ℝ, 0 < a → 0 < b → a + b ≤ 1 → ∀ w : AdjX c m,
    adjS0Fun ν c a (adjS0Fun ν c b ⇑w) =ᵐ[B0579.cellMeasure c (-m)] adjS0Fun ν c (a + b) ⇑w
  semi1 : ∀ a b : ℝ, 0 < a → 0 < b → a + b ≤ 1 → ∀ (j : Fin 2) (w : AdjX c m),
    adjS0Fun ν c a (adjKerOp c (adjHeatGradKer ν b j) ⇑w) =ᵐ[B0579.cellMeasure c (-m)]
      adjKerOp c (adjHeatGradKer ν (a + b) j) ⇑w

namespace AdjFreeData

variable {ν c m : ℝ} (D : AdjFreeData ν c m)

/-- `e^{ντΔ}` on `X_{-m,c}` for `τ ∈ (0, 1]` (`0` otherwise). -/
def S0Pos (τ : ℝ) : AdjX c m →L[ℂ] AdjX c m :=
  if h : τ ∈ Ioc (0 : ℝ) 1 then kerCLM D.hc (continuous_adjHeatKer ν τ) D.hM₀ (D.young0 τ h)
  else 0

/-- `S₀(τ)`: `e^{ντΔ}` for `τ ∈ (0, 1]`, the identity otherwise (`S₀(0) = 1`). -/
def S0 (τ : ℝ) : AdjX c m →L[ℂ] AdjX c m :=
  if τ ∈ Ioc (0 : ℝ) 1 then D.S0Pos τ else ContinuousLinearMap.id ℂ (AdjX c m)

/-- The convolution with `∂_j G_{ντ}` on `X_{-m,c}` for `τ ∈ (0, 1]` (`0` otherwise). -/
def GradPos (τ : ℝ) (j : Fin 2) : AdjX c m →L[ℂ] AdjX c m :=
  if h : τ ∈ Ioc (0 : ℝ) 1 then
    kerCLM D.hc (continuous_adjHeatGradKer ν τ j)
      (mul_nonneg D.hC₁ (Real.rpow_nonneg h.1.le _)) (D.young1 τ h j)
  else 0

/-- `S(τ)(F, h) = e^{ντΔ}(-∇·F + h) = -(K₀(τ)F₀ + K₁(τ)F₁) + e^{ντΔ}h`. -/
def S (τ : ℝ) : AdjY c m →L[ℂ] AdjX c m :=
  -((D.GradPos τ 0).comp ((ContinuousLinearMap.proj 0).comp
      (ContinuousLinearMap.fst ℂ (Fin 2 → AdjX c m) (AdjX c m))) +
    (D.GradPos τ 1).comp ((ContinuousLinearMap.proj 1).comp
      (ContinuousLinearMap.fst ℂ (Fin 2 → AdjX c m) (AdjX c m)))) +
  (D.S0Pos τ).comp (ContinuousLinearMap.snd ℂ (Fin 2 → AdjX c m) (AdjX c m))

theorem S_apply (τ : ℝ) (y : AdjY c m) :
    D.S τ y = -(D.GradPos τ 0 (y.1 0) + D.GradPos τ 1 (y.1 1)) + D.S0Pos τ y.2 := by
  simp [S]

theorem S0_of_mem {τ : ℝ} (hτ : τ ∈ Ioc (0 : ℝ) 1) : D.S0 τ = D.S0Pos τ := by
  simp [S0, hτ]

theorem S0_of_not_mem {τ : ℝ} (hτ : τ ∉ Ioc (0 : ℝ) 1) :
    D.S0 τ = ContinuousLinearMap.id ℂ (AdjX c m) := by
  simp [S0, hτ]

theorem S0_zero : D.S0 0 = ContinuousLinearMap.id ℂ (AdjX c m) :=
  D.S0_of_not_mem (by simp)

theorem coeFn_S0Pos {τ : ℝ} (hτ : τ ∈ Ioc (0 : ℝ) 1) (w : AdjX c m) :
    ⇑(D.S0Pos τ w) =ᵐ[B0579.cellMeasure c (-m)] adjS0Fun ν c τ ⇑w := by
  simp only [S0Pos, hτ, ↓reduceDIte]
  exact coeFn_kerCLM _ _ _ _ w

theorem coeFn_GradPos {τ : ℝ} (hτ : τ ∈ Ioc (0 : ℝ) 1) (j : Fin 2) (w : AdjX c m) :
    ⇑(D.GradPos τ j w) =ᵐ[B0579.cellMeasure c (-m)] adjKerOp c (adjHeatGradKer ν τ j) ⇑w := by
  simp only [GradPos, hτ, ↓reduceDIte]
  exact coeFn_kerCLM _ _ _ _ w

theorem norm_S0Pos_le {τ : ℝ} (hτ : τ ∈ Ioc (0 : ℝ) 1) : ‖D.S0Pos τ‖ ≤ D.M₀ := by
  simp only [S0Pos, hτ, ↓reduceDIte]
  exact norm_kerCLM_le _ _ _ _

theorem norm_GradPos_le {τ : ℝ} (hτ : τ ∈ Ioc (0 : ℝ) 1) (j : Fin 2) :
    ‖D.GradPos τ j‖ ≤ D.C₁ * τ ^ (-(1 / 2 : ℝ)) := by
  simp only [GradPos, hτ, ↓reduceDIte]
  exact norm_kerCLM_le _ _ _ _

theorem norm_S0_le (τ : ℝ) : ‖D.S0 τ‖ ≤ max 1 D.M₀ := by
  by_cases hτ : τ ∈ Ioc (0 : ℝ) 1
  · rw [D.S0_of_mem hτ]
    exact (D.norm_S0Pos_le hτ).trans (le_max_right _ _)
  · rw [D.S0_of_not_mem hτ]
    exact ContinuousLinearMap.norm_id_le.trans (le_max_left _ _)

theorem norm_S_le {τ : ℝ} (hτ : τ ∈ Ioc (0 : ℝ) 1) :
    ‖D.S τ‖ ≤ (2 * D.C₁ + D.M₀) * τ ^ (-(1 / 2 : ℝ)) := by
  have hpow : 1 ≤ τ ^ (-(1 / 2 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hτ.1 hτ.2 (by norm_num)
  have hCt : 0 ≤ D.C₁ * τ ^ (-(1 / 2 : ℝ)) := mul_nonneg D.hC₁ (by linarith)
  have hK : 0 ≤ (2 * D.C₁ + D.M₀) * τ ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (by linarith [D.hC₁, D.hM₀]) (by linarith)
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun y => ?_
  rw [D.S_apply]
  have h0 : ‖y.1 0‖ ≤ ‖y‖ := (norm_le_pi_norm y.1 0).trans (norm_fst_le y)
  have h1 : ‖y.1 1‖ ≤ ‖y‖ := (norm_le_pi_norm y.1 1).trans (norm_fst_le y)
  have h2 : ‖y.2‖ ≤ ‖y‖ := norm_snd_le y
  have g0 : ‖D.GradPos τ 0 (y.1 0)‖ ≤ D.C₁ * τ ^ (-(1 / 2 : ℝ)) * ‖y‖ :=
    ((D.GradPos τ 0).le_opNorm _).trans
      (mul_le_mul (D.norm_GradPos_le hτ 0) h0 (norm_nonneg _) hCt)
  have g1 : ‖D.GradPos τ 1 (y.1 1)‖ ≤ D.C₁ * τ ^ (-(1 / 2 : ℝ)) * ‖y‖ :=
    ((D.GradPos τ 1).le_opNorm _).trans
      (mul_le_mul (D.norm_GradPos_le hτ 1) h1 (norm_nonneg _) hCt)
  have s0 : ‖D.S0Pos τ y.2‖ ≤ D.M₀ * ‖y‖ :=
    ((D.S0Pos τ).le_opNorm _).trans (mul_le_mul (D.norm_S0Pos_le hτ) h2 (norm_nonneg _) D.hM₀)
  have hsum : ‖-(D.GradPos τ 0 (y.1 0) + D.GradPos τ 1 (y.1 1)) + D.S0Pos τ y.2‖ ≤
      ‖D.GradPos τ 0 (y.1 0)‖ + ‖D.GradPos τ 1 (y.1 1)‖ + ‖D.S0Pos τ y.2‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
    linarith [norm_add_le (D.GradPos τ 0 (y.1 0)) (D.GradPos τ 1 (y.1 1))]
  have hextra : 0 ≤ D.M₀ * ‖y‖ * (τ ^ (-(1 / 2 : ℝ)) - 1) :=
    mul_nonneg (mul_nonneg D.hM₀ (norm_nonneg y)) (by linarith)
  nlinarith [hsum, g0, g1, s0, hextra]

theorem coeFn_S {τ : ℝ} (hτ : τ ∈ Ioc (0 : ℝ) 1) (y : AdjY c m) :
    ⇑(D.S τ y) =ᵐ[B0579.cellMeasure c (-m)] adjSFun ν c τ (fun j => ⇑(y.1 j)) ⇑y.2 := by
  rw [D.S_apply]
  filter_upwards [Lp.coeFn_add (-(D.GradPos τ 0 (y.1 0) + D.GradPos τ 1 (y.1 1)))
      (D.S0Pos τ y.2),
    Lp.coeFn_neg (D.GradPos τ 0 (y.1 0) + D.GradPos τ 1 (y.1 1)),
    Lp.coeFn_add (D.GradPos τ 0 (y.1 0)) (D.GradPos τ 1 (y.1 1)),
    D.coeFn_GradPos hτ 0 (y.1 0), D.coeFn_GradPos hτ 1 (y.1 1), D.coeFn_S0Pos hτ y.2]
    with x h1 h2 h3 h4 h5 h6
  rw [h1, Pi.add_apply, h2, Pi.neg_apply, h3, Pi.add_apply, h4, h5, h6]
  simp only [adjSFun, adjDivFun_eq, Fin.sum_univ_two]

/-! ### Semigroup laws -/

theorem S0Pos_comp {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1) :
    (D.S0Pos a).comp (D.S0Pos b) = D.S0Pos (a + b) := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [ContinuousLinearMap.comp_apply]
  apply Lp.ext
  have hA : a ∈ Ioc (0 : ℝ) 1 := ⟨ha, by linarith⟩
  have hB : b ∈ Ioc (0 : ℝ) 1 := ⟨hb, by linarith⟩
  have hAB : a + b ∈ Ioc (0 : ℝ) 1 := ⟨by linarith, hab⟩
  have hcong : adjS0Fun ν c a ⇑(D.S0Pos b w) = adjS0Fun ν c a (adjS0Fun ν c b ⇑w) := by
    rw [adjS0Fun_eq_adjKerOp]
    exact adjKerOp_congr_ae D.hc _ (D.coeFn_S0Pos hB w)
  filter_upwards [D.coeFn_S0Pos hA (D.S0Pos b w), D.coeFn_S0Pos hAB w,
    D.semi0 a b ha hb hab w] with x h1 h2 h3
  rw [h1, hcong, h3, h2]

theorem S0Pos_comp_GradPos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1) (j : Fin 2) :
    (D.S0Pos a).comp (D.GradPos b j) = D.GradPos (a + b) j := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [ContinuousLinearMap.comp_apply]
  apply Lp.ext
  have hA : a ∈ Ioc (0 : ℝ) 1 := ⟨ha, by linarith⟩
  have hB : b ∈ Ioc (0 : ℝ) 1 := ⟨hb, by linarith⟩
  have hAB : a + b ∈ Ioc (0 : ℝ) 1 := ⟨by linarith, hab⟩
  have hcong : adjS0Fun ν c a ⇑(D.GradPos b j w) =
      adjS0Fun ν c a (adjKerOp c (adjHeatGradKer ν b j) ⇑w) := by
    rw [adjS0Fun_eq_adjKerOp]
    exact adjKerOp_congr_ae D.hc _ (D.coeFn_GradPos hB j w)
  filter_upwards [D.coeFn_S0Pos hA (D.GradPos b j w), D.coeFn_GradPos hAB j w,
    D.semi1 a b ha hb hab j w] with x h1 h2 h3
  rw [h1, hcong, h3, h2]

theorem S0_comp_S0 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (D.S0 a).comp (D.S0 b) = D.S0 (a + b) := by
  rcases eq_or_lt_of_le ha with h | ha'
  · subst h
    rw [D.S0_zero, zero_add, ContinuousLinearMap.id_comp]
  rcases eq_or_lt_of_le hb with h | hb'
  · subst h
    rw [D.S0_zero, add_zero, ContinuousLinearMap.comp_id]
  rw [D.S0_of_mem ⟨ha', by linarith⟩, D.S0_of_mem ⟨hb', by linarith⟩,
    D.S0_of_mem ⟨by linarith, hab⟩]
  exact D.S0Pos_comp ha' hb' hab

theorem S0_comp_S {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b ≤ 1) :
    (D.S0 a).comp (D.S b) = D.S (a + b) := by
  rcases eq_or_lt_of_le ha with h | ha'
  · subst h
    rw [D.S0_zero, zero_add, ContinuousLinearMap.id_comp]
  rw [D.S0_of_mem ⟨ha', by linarith⟩]
  refine ContinuousLinearMap.ext fun y => ?_
  rw [ContinuousLinearMap.comp_apply, D.S_apply, D.S_apply, map_add, map_neg, map_add]
  have h0 := congrArg (fun L => L (y.1 0)) (D.S0Pos_comp_GradPos ha' hb hab 0)
  have h1 := congrArg (fun L => L (y.1 1)) (D.S0Pos_comp_GradPos ha' hb hab 1)
  have h2 := congrArg (fun L => L y.2) (D.S0Pos_comp ha' hb hab)
  simp only [ContinuousLinearMap.comp_apply] at h0 h1 h2
  rw [h0, h1, h2]

/-! ### Strong continuity -/

theorem tendsto_S0_zero (w : AdjX c m) : Tendsto (fun τ => D.S0 τ w) (𝓝[>] 0) (𝓝 w) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ ∈ Ioc (0 : ℝ) 1 := Ioc_mem_nhdsGT one_pos
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (D.strong0 w)
  rw [ENNReal.toReal_zero] at h
  refine h.congr' ?_
  filter_upwards [hev] with τ hτ
  rw [Function.comp_apply, D.S0_of_mem hτ]
  simp only [S0Pos, hτ, ↓reduceDIte]
  exact (norm_kerCLM_sub D.hc _ D.hM₀ (D.young0 τ hτ) w).symm

theorem continuousOn_S0 (w : AdjX c m) : ContinuousOn (fun τ => D.S0 τ w) (Icc 0 1) := by
  have hKpos : 0 < max 1 D.M₀ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hsmall : ∀ ε > 0, ∃ δ > 0, ∀ s : ℝ, 0 ≤ s → s < δ → ‖D.S0 s w - w‖ < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := Metric.tendsto_nhdsWithin_nhds.1 (D.tendsto_S0_zero w) ε hε
    refine ⟨δ, hδ, fun s hs0 hsδ => ?_⟩
    rcases eq_or_lt_of_le hs0 with h | h
    · subst h
      rw [D.S0_zero, ContinuousLinearMap.id_apply, sub_self, norm_zero]
      exact hε
    · have hd := hδ' (show s ∈ Ioi 0 from h)
        (by rw [Real.dist_eq, sub_zero, abs_of_pos h]; exact hsδ)
      rwa [dist_eq_norm] at hd
  rw [Metric.continuousOn_iff]
  intro τ₀ hτ₀ ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hsmall (ε / max 1 D.M₀) (div_pos hε hKpos)
  refine ⟨δ, hδ, fun τ hτ hdist => ?_⟩
  rw [dist_eq_norm]
  rw [Real.dist_eq] at hdist
  have hbound : ∀ (s : ℝ) (z : AdjX c m), ‖D.S0 s z‖ ≤ max 1 D.M₀ * ‖z‖ := fun s z =>
    ((D.S0 s).le_opNorm z).trans (mul_le_mul_of_nonneg_right (D.norm_S0_le s) (norm_nonneg _))
  rcases le_total τ₀ τ with h | h
  · have hcomp := D.S0_comp_S0 (a := τ₀) (b := τ - τ₀) hτ₀.1 (by linarith)
      (by linarith [hτ.2])
    have e := congrArg (fun L => L w) hcomp
    simp only [ContinuousLinearMap.comp_apply, add_sub_cancel] at e
    have hlt : ‖D.S0 (τ - τ₀) w - w‖ < ε / max 1 D.M₀ :=
      hδ' (τ - τ₀) (by linarith) (by rw [abs_lt] at hdist; linarith [hdist.2])
    calc ‖D.S0 τ w - D.S0 τ₀ w‖ = ‖D.S0 τ₀ (D.S0 (τ - τ₀) w - w)‖ := by
          rw [map_sub, e]
      _ ≤ max 1 D.M₀ * ‖D.S0 (τ - τ₀) w - w‖ := hbound _ _
      _ < max 1 D.M₀ * (ε / max 1 D.M₀) := mul_lt_mul_of_pos_left hlt hKpos
      _ = ε := by field_simp
  · have hcomp := D.S0_comp_S0 (a := τ) (b := τ₀ - τ) hτ.1 (by linarith)
      (by linarith [hτ₀.2])
    have e := congrArg (fun L => L w) hcomp
    simp only [ContinuousLinearMap.comp_apply, add_sub_cancel] at e
    have hlt : ‖D.S0 (τ₀ - τ) w - w‖ < ε / max 1 D.M₀ :=
      hδ' (τ₀ - τ) (by linarith) (by rw [abs_lt] at hdist; linarith [hdist.1])
    calc ‖D.S0 τ w - D.S0 τ₀ w‖ = ‖D.S0 τ (D.S0 (τ₀ - τ) w - w)‖ := by
          rw [map_sub, e, norm_sub_rev]
      _ ≤ max 1 D.M₀ * ‖D.S0 (τ₀ - τ) w - w‖ := hbound _ _
      _ < max 1 D.M₀ * (ε / max 1 D.M₀) := mul_lt_mul_of_pos_left hlt hKpos
      _ = ε := by field_simp

theorem continuousOn_S (y : AdjY c m) : ContinuousOn (fun τ => D.S τ y) (Ioc 0 1) := by
  intro τ₀ hτ₀
  have hb0 : 0 < τ₀ / 2 := half_pos hτ₀.1
  have hbτ : τ₀ / 2 < τ₀ := half_lt_self hτ₀.1
  have hg : ContinuousOn (fun τ => D.S0 (τ - τ₀ / 2) (D.S (τ₀ / 2) y))
      (Icc (τ₀ / 2) (1 + τ₀ / 2)) := by
    refine (D.continuousOn_S0 (D.S (τ₀ / 2) y)).comp
      (continuousOn_id.sub continuousOn_const) ?_
    intro τ hτ
    exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hgτ₀ : ContinuousWithinAt (fun τ => D.S0 (τ - τ₀ / 2) (D.S (τ₀ / 2) y))
      (Ioc 0 1 ∩ Ioi (τ₀ / 2)) τ₀ :=
    (hg τ₀ ⟨hbτ.le, by linarith [hτ₀.2]⟩).mono fun τ hτ =>
      ⟨(Set.mem_Ioi.1 hτ.2).le, by linarith [hτ.1.2]⟩
  have heq : ∀ τ ∈ Ioc (0 : ℝ) 1 ∩ Ioi (τ₀ / 2),
      D.S τ y = D.S0 (τ - τ₀ / 2) (D.S (τ₀ / 2) y) := by
    intro τ hτ
    have hcomp := D.S0_comp_S (a := τ - τ₀ / 2) (b := τ₀ / 2)
      (by linarith [Set.mem_Ioi.1 hτ.2]) hb0 (by linarith [hτ.1.2])
    have e := congrArg (fun L => L y) hcomp
    simp only [ContinuousLinearMap.comp_apply, sub_add_cancel] at e
    exact e.symm
  have hfτ₀ : ContinuousWithinAt (fun τ => D.S τ y) (Ioc 0 1 ∩ Ioi (τ₀ / 2)) τ₀ :=
    hgτ₀.congr (fun τ hτ => heq τ hτ) (heq τ₀ ⟨hτ₀, hbτ⟩)
  exact (continuousWithinAt_inter (Ioi_mem_nhds hbτ)).1 hfτ₀

/-! ### The supplier and its weak identities -/

/-- **The concrete free part** (SP 2819-2836): `S₀ = e^{ντΔ}`, `S = e^{ντΔ}(-∇· , +)`. -/
def supplier : AdjHeatSupplier c m where
  S₀ := D.S0
  S := D.S
  M₀ := max 1 D.M₀
  C₀ := 2 * D.C₁ + D.M₀
  S₀_zero := D.S0_zero
  norm_S₀_le := fun τ _ _ => D.norm_S0_le τ
  norm_S_le := fun _ h0 h1 => D.norm_S_le ⟨h0, h1⟩
  continuousOn_S₀ := D.continuousOn_S0
  continuousOn_S := D.continuousOn_S
  S₀_comp_S₀ := fun _ _ ha hb hab => D.S0_comp_S0 ha hb hab
  S₀_comp_S := fun _ _ ha hb hab => D.S0_comp_S ha hb hab

theorem supplier_weak (hν : 0 < ν) (h5 : AdjHeatS0Weak m) (h6 : AdjHeatDuhamelWeak m) :
    AdjHeatWeak ν c m D.supplier := by
  have hC : 0 ≤ 2 * D.C₁ + D.M₀ := by linarith [D.hC₁, D.hM₀]
  refine ⟨fun w ψ hψ τ hτ => ?_, fun F a b hab hb hF ψ hψ τ hτ => ?_⟩
  · change ∫ x in B0579.cell c, (D.S0 τ w) x * (ψ x : ℂ) =
      (∫ x in B0579.cell c, w x * (ψ x : ℂ)) +
        ∫ r in (0 : ℝ)..τ, (ν : ℂ) * ∫ x in B0579.cell c, (D.S0 r w) x * (lapP ψ x : ℂ)
    rcases eq_or_lt_of_le hτ.1 with h0 | hpos
    · subst h0
      simp [D.S0_zero]
    · have hτ' : τ ∈ Ioc (0 : ℝ) 1 := ⟨hpos, hτ.2⟩
      rw [D.S0_of_mem hτ', adjHeat_cell_integral_congr (D.coeFn_S0Pos hτ' w) ψ,
        h5 ν c hν D.hc w ψ hψ τ hτ']
      congr 1
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hr => ?_)
      rw [Set.uIoc_of_le hτ.1] at hr
      have hr' : r ∈ Ioc (0 : ℝ) 1 := ⟨hr.1, hr.2.trans hτ.2⟩
      rw [D.S0_of_mem hr', adjHeat_cell_integral_congr (D.coeFn_S0Pos hr' w) (lapP ψ)]
  · have hstep : ∀ u ∈ Icc a b, ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest c φ →
        ∫ x in B0579.cell c, (∫ r in a..u, D.S (u - r) (F r)) x * (φ x : ℂ) =
          ∫ r in a..u, adjRespPair ν c (u - r) (F r) φ := by
      intro u hu φ hφ
      rw [adjHeat_duhamel_pair D.hc D.S hC (fun τ h0 h1 => D.norm_S_le ⟨h0, h1⟩)
        D.continuousOn_S hb hF hu hφ]
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [ae_ne_real u] with r hru hr
      rw [Set.uIoc_of_le hu.1] at hr
      have h0 : 0 < u - r := sub_pos.2 (lt_of_le_of_ne hr.2 hru)
      have h1 : u - r ≤ 1 := by linarith [hr.1, hu.2]
      exact adjHeat_cell_integral_congr (D.coeFn_S ⟨h0, h1⟩ (F r)) φ
    change ∫ x in B0579.cell c, (∫ r in a..τ, D.S (τ - r) (F r)) x * (ψ x : ℂ) =
      (∫ r in a..τ, (ν : ℂ) * ∫ x in B0579.cell c,
          (∫ σ in a..r, D.S (r - σ) (F σ)) x * (lapP ψ x : ℂ)) +
        ∫ r in a..τ, adjFluxPair (F r) ψ
    rw [hstep τ hτ ψ hψ, h6 ν c hν D.hc F a b hab hb hF ψ hψ τ hτ]
    congr 1
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le hτ.1] at hr
    rw [hstep r ⟨hr.1, hr.2.trans hτ.2⟩ (lapP ψ) (Exist.cylTest_lapP hψ)]

end AdjFreeData

/-- **`AdjHeatExists m` from the leaves H1-H6** (SP 2819-2836): for every `ν > 0`, `c > 0`
the concrete free part `AdjFreeData.supplier` (periodic heat semigroup of diffusivity `ν` and
its heat-divergence response on `X_{-m,c}`) is an `AdjHeatSupplier` with the weak identities
`AdjHeatWeak ν`. -/
theorem adjHeatExists_of (m : ℝ) (h1 : AdjHeatS0Young m) (h2 : AdjHeatGradYoung m)
    (h3 : AdjHeatS0StrongZero m) (h4 : AdjHeatSemigroup m) (h5 : AdjHeatS0Weak m)
    (h6 : AdjHeatDuhamelWeak m) : AdjHeatExists m := by
  intro ν c hν hc
  obtain ⟨M₀, hM₀, hY0⟩ := h1 ν c hν hc
  obtain ⟨C₁, hC₁, hY1⟩ := h2 ν c hν hc
  let D : AdjFreeData ν c m :=
    { hc := hc, M₀ := M₀, C₁ := C₁, hM₀ := hM₀, hC₁ := hC₁, young0 := hY0, young1 := hY1,
      strong0 := h3 ν c hν hc, semi0 := h4.1 ν c hν hc, semi1 := h4.2 ν c hν hc }
  exact ⟨D.supplier, D.supplier_weak hν h5 h6⟩

end UnforcedLeray.Short.IIIa
