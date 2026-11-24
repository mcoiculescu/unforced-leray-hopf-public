import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.BlockPropagator.RelBlockDiagonal.Pins
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3

/-!
# Part III-a, `PartIII-a:T21/c3/2/1/1/org/3/a/2`: the norm limit of the relative free block

Source: `the November 2 reference manuscript` (SP) 2937-2965.

`RelFreeNormLimit κ`: in the successive limit, `‖F_rel τ σ‖ ≤ e^{-γ(τ-σ)} + ε` with `γ = Re λ`
(`eq:short-causal-free-moving`, SP 2958-2961; "the undamped norms have limiting upper bound one",
SP 2964-2965).

The periodized extension `\bar F(z,t) = I_z F(z,t) R_t + S(z,t)(I - Π_t)` (SP 2941) has
disjoint entrance and exit supports (SP 2943):
* on data supported in the entrance cell `d(s)`, `F_rel τ σ` lands in the exit cell `d(t)`
  (`freeBlock_cell_to_cell`) with norm at most `e^{(-γ + (C_m + |Re κ|)/b + ε')(τ-σ)}`: on a real
  cylinder test the pin of `IsPeriodizedRelFreeBlockEvol` is `N⁻¹ I_t J_t⁻¹ ω₀(t)`, bounded by
  `relFreeMovingEnergy`; real tests give real images, so `testW φ₁ + i testW φ₂` is handled by
  Pythagoras, and density (`exists_test_approx_cell`) extends the bound;
* on data vanishing on the entrance cell, `F_rel τ σ = N⁻¹ S(t,s)` lands outside the exit cell,
  with `‖S‖ ≤ e^{3(τ-σ)/(2b)}` (`norm_extDilW_cellLen_le_exp`) and
  `N ≥ e^{(γ - |Re κ|/b)(τ-σ)}` (`exp_beta0_le_clockN`, SP 2919: real damping `Re λ`);
* the two parts are orthogonal, so `‖F_rel τ σ‖ ≤ max` of the two factors, and both are at most
  `e^{-γ(τ-σ)} + ε` once `b` is large and `ε'` small.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub BlockPropagatorInteriorSub
  OrgSplit OrgSplit3 RelExteriorSub RelBlockDiagonalSub VariationOfConstantsSub

namespace RelFreeNormSub

/-! ## 1. Real vectors and orthogonality -/

/-- `X` takes real values a.e. -/
def IsRealW {m : ℝ} (X : Planar.L2w m) : Prop :=
  ∀ᵐ z ∂(Planar.wMeasure m), ((X : ℂ → ℂ) z).im = 0

theorem inner_im_eq_zero {m : ℝ} {X Y : Planar.L2w m} (hX : IsRealW X) (hY : IsRealW Y) :
    (⟪X, Y⟫_ℂ).im = 0 := by
  rw [MeasureTheory.L2.inner_def]
  have hint := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) X Y
  have h := integral_im hint
  have h' : (∫ a, ⟪(X : ℂ → ℂ) a, (Y : ℂ → ℂ) a⟫_ℂ ∂(Planar.wMeasure m)).im =
      ∫ a, RCLike.im ⟪(X : ℂ → ℂ) a, (Y : ℂ → ℂ) a⟫_ℂ ∂(Planar.wMeasure m) := h.symm
  rw [h']
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hX, hY] with z hx hy
  rw [RCLike.inner_apply']
  simp [hx, hy]

/-- Pythagoras for real vectors: `‖X + i Y‖² = ‖X‖² + ‖Y‖²`. -/
theorem norm_add_I_smul_sq {m : ℝ} {X Y : Planar.L2w m} (hX : IsRealW X) (hY : IsRealW Y) :
    ‖X + Complex.I • Y‖ ^ 2 = ‖X‖ ^ 2 + ‖Y‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul, Complex.norm_I, one_mul]
  have h := inner_im_eq_zero hX hY
  have h0 : RCLike.re (Complex.I * ⟪X, Y⟫_ℂ) = 0 := by
    change (Complex.I * ⟪X, Y⟫_ℂ).re = 0
    simp [Complex.mul_re, h]
  rw [h0]
  ring

/-- Cell-supported and exterior-supported data are orthogonal. -/
theorem inner_eq_zero_of_cell_ext {m d : ℝ} {X Y : Planar.L2w m} (hX : IsCellSupportedW d X)
    (hY : IsExteriorSupportedW d Y) : ⟪X, Y⟫_ℂ = 0 := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  have hX' := (Planar.wMeasure_ac m).ae_le hX
  have hY' := (Planar.wMeasure_ac m).ae_le hY
  filter_upwards [hX', hY'] with z hx hy
  by_cases hz : cToPlane z ∈ B0579.cell d
  · simp [hy hz]
  · simp [hx hz]

theorem norm_add_sq_cell_ext {m d : ℝ} {X Y : Planar.L2w m} (hX : IsCellSupportedW d X)
    (hY : IsExteriorSupportedW d Y) : ‖X + Y‖ ^ 2 = ‖X‖ ^ 2 + ‖Y‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero X Y
    (inner_eq_zero_of_cell_ext hX hY)
  simpa [sq] using h

/-! ## 2. The cell projection -/

theorem cellProjW_cellSupported {m : ℝ} (d : ℝ) (W : Planar.L2w m) :
    IsCellSupportedW d (cellProjW m d W) := by
  have happ : cellProjW m d W = ((Lp.memLp W).indicator (measurableSet_cellC d)).toLp _ := rfl
  have h1 := (Planar.volume_ac m).ae_le
    ((Lp.memLp W).indicator (measurableSet_cellC d)).coeFn_toLp
  filter_upwards [h1] with z hz hnot
  rw [happ, hz, Set.indicator_of_notMem (show z ∉ {z : ℂ | cToPlane z ∈ B0579.cell d} from hnot)]

theorem sub_cellProjW_exteriorSupported {m : ℝ} (d : ℝ) (W : Planar.L2w m) :
    IsExteriorSupportedW d (W - cellProjW m d W) := by
  have happ : cellProjW m d W = ((Lp.memLp W).indicator (measurableSet_cellC d)).toLp _ := rfl
  have h1 := (Planar.volume_ac m).ae_le
    ((Lp.memLp W).indicator (measurableSet_cellC d)).coeFn_toLp
  have h2 := (Planar.volume_ac m).ae_le (Lp.coeFn_sub W (cellProjW m d W))
  filter_upwards [h1, h2] with z hz1 hz2 hmem
  rw [hz2, Pi.sub_apply, happ, hz1,
    Set.indicator_of_mem (show z ∈ {z : ℂ | cToPlane z ∈ B0579.cell d} from hmem), sub_self]

/-- The block norm bound from the two diagonal parts. -/
theorem opNorm_le_of_cell_ext {m d_s d_t M : ℝ} (F : Planar.L2w m →L[ℂ] Planar.L2w m)
    (hM : 0 ≤ M)
    (hcell : ∀ V : Planar.L2w m, IsCellSupportedW d_s V →
      ‖F V‖ ≤ M * ‖V‖ ∧ IsCellSupportedW d_t (F V))
    (hext : ∀ Y : Planar.L2w m, IsExteriorSupportedW d_s Y →
      ‖F Y‖ ≤ M * ‖Y‖ ∧ IsExteriorSupportedW d_t (F Y)) :
    ‖F‖ ≤ M := by
  refine ContinuousLinearMap.opNorm_le_bound F hM fun W => ?_
  obtain ⟨V, hVdef⟩ : ∃ V : Planar.L2w m, V = cellProjW m d_s W := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : Planar.L2w m, Y = W - V := ⟨_, rfl⟩
  have hV : IsCellSupportedW d_s V := hVdef ▸ cellProjW_cellSupported d_s W
  have hY : IsExteriorSupportedW d_s Y := by
    rw [hYdef, hVdef]; exact sub_cellProjW_exteriorSupported d_s W
  have hW : W = V + Y := by rw [hYdef]; abel
  obtain ⟨hV1, hV2⟩ := hcell V hV
  obtain ⟨hY1, hY2⟩ := hext Y hY
  have hFW : F W = F V + F Y := by rw [hW, map_add]
  have hWsq : ‖W‖ ^ 2 = ‖V‖ ^ 2 + ‖Y‖ ^ 2 := by rw [hW]; exact norm_add_sq_cell_ext hV hY
  have hsq : ‖F W‖ ^ 2 ≤ (M * ‖W‖) ^ 2 := by
    rw [hFW, norm_add_sq_cell_ext hV2 hY2, mul_pow, hWsq]
    have h1 : ‖F V‖ ^ 2 ≤ (M * ‖V‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hV1 2
    have h2 : ‖F Y‖ ^ 2 ≤ (M * ‖Y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hY1 2
    nlinarith [h1, h2]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).1 hsq

/-! ## 3. Real cylinder tests -/

theorem isRealW_testW (m : ℝ) {d : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest d φ) :
    IsRealW (testW m hφ) := by
  filter_upwards [coeFn_testW m hφ] with z hz
  rw [hz]
  by_cases hmem : cToPlane z ∈ B0579.cell d
  · simp [cellZeroExt, Set.indicator_of_mem hmem]
  · simp [cellZeroExt, Set.indicator_of_notMem hmem]

theorem norm_testW (m : ℝ) {d : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest d φ) :
    ENNReal.ofReal ‖testW m hφ‖ = xNorm d m (fun y => ((φ y : ℝ) : ℂ)) := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
    eLpNorm_congr_ae (coeFn_testW m hφ),
    eLpNorm_cellZeroExt_cToPlane d m (show AEStronglyMeasurable (fun y => ((φ y : ℝ) : ℂ))
      (B0579.cellMeasure d m) from ((hφ.memLp m).ofReal (K := ℂ)).1)]

/-- If `F` sends real cylinder tests of period `d` to real data with norm factor `K`, then
`‖F V‖ ≤ K ‖V‖` on all data supported in the cell `d` (Pythagoras and density). -/
theorem norm_apply_le_of_tests {m d K : ℝ} (hd : 0 < d) (hK : 0 ≤ K)
    (F : Planar.L2w m →L[ℂ] Planar.L2w m)
    (htest : ∀ (φ : ℝ × ℝ → ℝ) (hφ : B0579.IsCylTest d φ),
      IsRealW (F (testW m hφ)) ∧ ‖F (testW m hφ)‖ ≤ K * ‖testW m hφ‖)
    (V : Planar.L2w m) (hV : IsCellSupportedW d V) : ‖F V‖ ≤ K * ‖V‖ := by
  have hpair : ∀ (φ₁ φ₂ : ℝ × ℝ → ℝ) (h₁ : B0579.IsCylTest d φ₁) (h₂ : B0579.IsCylTest d φ₂),
      ‖F (testW m h₁ + Complex.I • testW m h₂)‖ ≤ K * ‖testW m h₁ + Complex.I • testW m h₂‖ := by
    intro φ₁ φ₂ h₁ h₂
    obtain ⟨hr₁, hb₁⟩ := htest φ₁ h₁
    obtain ⟨hr₂, hb₂⟩ := htest φ₂ h₂
    have hsq : ‖F (testW m h₁ + Complex.I • testW m h₂)‖ ^ 2 ≤
        (K * ‖testW m h₁ + Complex.I • testW m h₂‖) ^ 2 := by
      rw [map_add, map_smul, norm_add_I_smul_sq hr₁ hr₂, mul_pow,
        norm_add_I_smul_sq (isRealW_testW m h₁) (isRealW_testW m h₂)]
      have e1 : ‖F (testW m h₁)‖ ^ 2 ≤ (K * ‖testW m h₁‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb₁ 2
      have e2 : ‖F (testW m h₂)‖ ^ 2 ≤ (K * ‖testW m h₂‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb₂ 2
      nlinarith [e1, e2]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).1 hsq
  refine le_of_forall_pos_lt_add fun η hη => ?_
  have hδ : 0 < η / (K + ‖F‖ + 1) := by positivity
  obtain ⟨φ₁, φ₂, h₁, h₂, happrox⟩ := exists_test_approx_cell hd V hV hδ
  set X := testW m h₁ + Complex.I • testW m h₂ with hXdef
  have hFX := hpair φ₁ φ₂ h₁ h₂
  have hXV : ‖X‖ ≤ ‖V‖ + η / (K + ‖F‖ + 1) := by
    have := norm_le_insert' X V
    have h' : ‖V - X‖ = ‖X - V‖ := norm_sub_rev V X
    linarith
  have hFVX : ‖F V - F X‖ ≤ ‖F‖ * (η / (K + ‖F‖ + 1)) := by
    rw [← map_sub]
    exact ((F).le_opNorm _).trans (mul_le_mul_of_nonneg_left happrox.le (norm_nonneg _))
  have hFV : ‖F V‖ ≤ ‖F X‖ + ‖F V - F X‖ := norm_le_insert' (F V) (F X)
  have hsum : K * (η / (K + ‖F‖ + 1)) + ‖F‖ * (η / (K + ‖F‖ + 1)) < η := by
    rw [← add_mul, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg F]
  nlinarith [mul_le_mul_of_nonneg_left hXV hK]

/-! ## 4. The free block on data vanishing on the entrance cell -/

/-- The pin of `IsPeriodizedRelFreeBlockEvol` with `f = 0`, `ω₀ = 0` (SP 2941-2943). -/
theorem freeBlock_ext_ae {P : PlanarData} {ν m : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ B : ℝ}
    {F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (hF : IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel)
    {σ τ : ℝ} (hσ : 0 ≤ σ) (hστ : σ ≤ τ) (hτB : τ ≤ B) (W : Planar.L2w m)
    (hW : IsExteriorSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) W) :
    ⇑(F_rel τ σ W) =ᵐ[volume] fun z : ℂ =>
      ((clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ) : ℂ)⁻¹) *
        periodizedExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
          (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))
          (fun _ => 0) (fun y => (W : ℂ → ℂ) (planeToC y)) (cToPlane z) := by
  have hcell : ∀ᵐ z ∂(volume : Measure ℂ),
      cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) →
        (W : ℂ → ℂ) z = JscaleInv (clockA ν (ageAt ν t₁ σ))
          (fun x => (((fun _ : B0579.Plane => (0 : ℝ)) x : ℝ) : ℂ)) (cToPlane z) := by
    filter_upwards [hW] with z hz hmem
    rw [hz hmem]
    simp [JscaleInv]
  have h := hF σ τ hσ hστ hτB (fun _ => 0) (isCylTest_zero _) (fun _ _ => 0)
    (isFreeCylFlow_zero m tr _) W hcell
  filter_upwards [h] with z hz
  rw [hz]
  have hJ : JscaleInv (clockA ν (ageAt ν t₁ τ)) (fun x => ((((fun _ _ => (0 : ℝ)) :
      ℝ → B0579.Plane → ℝ) (ageAt ν t₁ τ) x : ℝ) : ℂ)) = fun _ => 0 := by
    funext y
    simp [JscaleInv]
  simp only [hJ]

/-- Data vanishing on the entrance cell are sent to data vanishing on the exit cell. -/
theorem freeBlock_ext_exteriorSupported {P : PlanarData} {ν m : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ B : ℝ}
    {F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (hF : IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel)
    {σ τ : ℝ} (hσ : 0 ≤ σ) (hστ : σ ≤ τ) (hτB : τ ≤ B)
    (hds : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
    (hdt : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) (W : Planar.L2w m)
    (hW : IsExteriorSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) W) :
    IsExteriorSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) (F_rel τ σ W) := by
  filter_upwards [freeBlock_ext_ae hF hσ hστ hτB W hW] with z hz hmem
  rw [hz, periodizedExt_apply_of_mem hds hdt _ _ hmem, mul_zero]

/-- On data vanishing on the entrance cell, `F_rel τ σ W = N⁻¹ • S(t, s) W` (SP 2941-2945). -/
theorem freeBlock_ext_eq_smul {P : PlanarData} {ν m : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ B : ℝ}
    {F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (hF : IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel)
    {σ τ : ℝ} (hσ : 0 ≤ σ) (hστ : σ ≤ τ) (hτB : τ ≤ B) (hm : 1 < m)
    (hds : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
    (hdt : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) (W : Planar.L2w m)
    (hW : IsExteriorSupportedW (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) W) :
    F_rel τ σ W =
      ((clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ) : ℂ)⁻¹) • extDilW hm hds hdt W := by
  set d₁ := cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)) with hd₁def
  set d₂ := cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)) with hd₂def
  set ρ : ℝ := d₁ / d₂ with hρdef
  have hρ : 0 < ρ := div_pos hds hdt
  have hpin := freeBlock_ext_ae hF hσ hστ hτB W hW
  have hW' : ∀ᵐ z ∂(volume : Measure ℂ), cToPlane (ρ • z) ∈ B0579.cell d₁ →
      (W : ℂ → ℂ) (ρ • z) = 0 :=
    (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℂ)) hρ.ne').ae hW
  set a : ℝ := ((d₁ / d₂) ^ 2)⁻¹ with hadef
  have ha : 0 < a := inv_pos.2 (sq_pos_of_pos hρ)
  have hsa : (√a)⁻¹ = ρ := by
    rw [hadef, Real.sqrt_inv, inv_inv, Real.sqrt_sq hρ.le]
  have ha2 : (a ^ 2)⁻¹ = ρ ^ 4 := by
    rw [hadef, inv_pow, inv_inv, ← pow_mul]
  have hdil := Planar.coeFn_dilW hm ha W
  have hsm := Lp.coeFn_smul ((clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ) : ℂ)⁻¹)
    (extDilW hm hds hdt W)
  refine Lp.ext ?_
  refine (Planar.wMeasure_ac m).ae_le ?_
  have hdil' := (Planar.volume_ac m).ae_le hdil
  have hsm' := (Planar.volume_ac m).ae_le hsm
  filter_upwards [hpin, hdil', hsm', hW'] with z h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply, smul_eq_mul]
  have h2' : (extDilW hm hds hdt W : ℂ → ℂ) z =
      (((a ^ 2)⁻¹ : ℝ) : ℂ) * (W : ℂ → ℂ) ((√a)⁻¹ • z) := h2
  rw [h2', hsa, ha2]
  congr 1
  have hpl : planeToC (ρ * z.re, ρ * z.im) = ρ • z := by
    apply Complex.ext <;> simp [planeToC]
  have hcp : cToPlane (ρ • z) = (ρ * z.re, ρ * z.im) := by
    simp [cToPlane]
  have hzero : ∀ (s : Set (ℝ × ℝ)) (y : ℝ × ℝ), s.indicator (fun _ => (0 : ℂ)) y = 0 :=
    fun s y => by simp
  unfold periodizedExt extDilCocycle
  simp only [cellZeroExt, hzero, zero_add, cToPlane]
  rw [← hρdef]
  by_cases hmem : (ρ * z.re, ρ * z.im) ∈ B0579.cell d₁
  · rw [Set.indicator_of_mem hmem, sub_self, mul_zero]
    have := h4 (by rw [hcp]; exact hmem)
    rw [this, mul_zero]
  · rw [Set.indicator_of_notMem hmem, sub_zero, hpl]

/-! ## 5. The free block on real cylinder tests -/

/-- The cylinder test `x ↦ a⁻² φ(x/√a)` of period `c` whose `J_a⁻¹` is `φ`. -/
def rescaleTest (a : ℝ) (φ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun x => (a ^ 2)⁻¹ * φ (x.1 / Real.sqrt a, x.2 / Real.sqrt a)

/-- The pin on a zero-extended real cylinder test: `F_rel τ σ (testW φ) = N⁻¹ I_t J_t⁻¹ ω₀(t)`
(SP 2941-2943). -/
theorem freeBlock_testW_ae {P : PlanarData} {ν m : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ B : ℝ}
    {F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (hF : IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel) (hν : 0 < ν)
    {σ τ : ℝ} (hσ : 0 ≤ σ) (hστ : σ ≤ τ) (hτB : τ ≤ B)
    (hs : 0 ≤ ageAt ν t₁ σ) (ht : 0 ≤ ageAt ν t₁ τ) {φ : ℝ × ℝ → ℝ}
    (hφ : B0579.IsCylTest (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) φ)
    {ω₀ : ℝ → B0579.Plane → ℝ}
    (hω₀ : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr (ageAt ν t₁ σ)
      (rescaleTest (clockA ν (ageAt ν t₁ σ)) φ) ω₀) :
    ⇑(F_rel τ σ (testW m hφ)) =ᵐ[volume] fun z : ℂ =>
      ((clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ) : ℂ)⁻¹) *
        cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))
          (JscaleInv (clockA ν (ageAt ν t₁ τ)) (fun x => ((ω₀ (ageAt ν t₁ τ) x : ℝ) : ℂ)))
          (cToPlane z) := by
  have ha : 0 < clockA ν (ageAt ν t₁ σ) := by unfold clockA; positivity
  have hds : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)) := cellLen_pos hν hs
  have hdt : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)) := cellLen_pos hν ht
  have hf : B0579.IsCylTest (ν ^ (-2 : ℝ)) (rescaleTest (clockA ν (ageAt ν t₁ σ)) φ) :=
    isCylTest_rescale (c := ν ^ (-2 : ℝ)) ha hφ
  have hV := coeFn_testW m hφ
  have hagree : ∀ᵐ z ∂(volume : Measure ℂ),
      cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) →
        (testW m hφ : ℂ → ℂ) z = JscaleInv (clockA ν (ageAt ν t₁ σ))
          (fun x => ((rescaleTest (clockA ν (ageAt ν t₁ σ)) φ x : ℝ) : ℂ)) (cToPlane z) := by
    filter_upwards [(Planar.volume_ac m).ae_le hV] with z hz hmem
    rw [hz, cellZeroExt, Set.indicator_of_mem hmem]
    exact (jscaleInv_rescale ha φ (cToPlane z)).symm
  have h := hF σ τ hσ hστ hτB _ hf ω₀ hω₀ (testW m hφ) hagree
  have hVext : ∀ᵐ z ∂(volume : Measure ℂ),
      cToPlane z ∉ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) →
        (testW m hφ : ℂ → ℂ) z = 0 := by
    filter_upwards [(Planar.volume_ac m).ae_le hV] with z hz hnot
    rw [hz, cellZeroExt, Set.indicator_of_notMem hnot]
  set ρ : ℝ := cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)) /
    cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)) with hρdef
  have hρ : 0 < ρ := div_pos hds hdt
  have hV' : ∀ᵐ z ∂(volume : Measure ℂ),
      cToPlane (ρ • z) ∉ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) →
        (testW m hφ : ℂ → ℂ) (ρ • z) = 0 :=
    (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℂ)) hρ.ne').ae hVext
  filter_upwards [h, hV'] with z hz hz'
  rw [hz]
  congr 1
  by_cases hmem : cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))
  · rw [periodizedExt_apply_of_mem hds hdt _ _ hmem, cellZeroExt, Set.indicator_of_mem hmem]
  · rw [periodizedExt_apply_of_notMem hds hdt _ _ hmem, cellZeroExt,
      Set.indicator_of_notMem hmem]
    have hcp : cToPlane (ρ • z) = (ρ * (cToPlane z).1, ρ * (cToPlane z).2) := by
      simp [cToPlane]
    have hpl : planeToC (ρ * (cToPlane z).1, ρ * (cToPlane z).2) = ρ • z := by
      apply Complex.ext <;> simp [planeToC, cToPlane]
    have hnot' : cToPlane (ρ • z) ∉
        B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) := by
      rw [hcp]
      exact mt (scaleMem_cell_iff hds hdt _).1 hmem
    unfold extDilCocycle
    show (((ρ) ^ 4 : ℝ) : ℂ) *
      (testW m hφ : ℂ → ℂ) (planeToC (ρ * (cToPlane z).1, ρ * (cToPlane z).2)) = 0
    rw [hpl, hz' hnot', mul_zero]

/-- The interior energy bound on a real cylinder test, from a free moving energy bound with
factor `K` (`relFreeMovingEnergy`, SP 2958-2961). The image is real. -/
theorem freeBlock_testW_bound {P : PlanarData} {ν m : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ B : ℝ}
    {F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (hF : IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel) (hν : 0 < ν) (hm : 8 < m)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {σ τ : ℝ} (hσ : 0 ≤ σ) (hστ : σ ≤ τ) (hτB : τ ≤ B)
    (hs : 0 ≤ ageAt ν t₁ σ) (hst : ageAt ν t₁ σ ≤ ageAt ν t₁ τ) {K : ℝ} (hK : 0 ≤ K)
    (hE : ∀ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
      ∀ ω₀ : ℝ → B0579.Plane → ℝ,
        UnforcedLeray.Short.IIb.IsFreeCylFlow m tr (ageAt ν t₁ σ) f ω₀ →
        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) m
            (JscaleInv (clockA ν (ageAt ν t₁ τ)) (fun x => ((ω₀ (ageAt ν t₁ τ) x : ℝ) : ℂ))) ≤
          ENNReal.ofReal (clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ)) *
            (ENNReal.ofReal K *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) m
                (JscaleInv (clockA ν (ageAt ν t₁ σ)) (fun x => ((f x : ℝ) : ℂ)))))
    (φ : ℝ × ℝ → ℝ)
    (hφ : B0579.IsCylTest (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) φ) :
    IsRealW (F_rel τ σ (testW m hφ)) ∧ ‖F_rel τ σ (testW m hφ)‖ ≤ K * ‖testW m hφ‖ := by
  have ht : 0 ≤ ageAt ν t₁ τ := hs.trans hst
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have ha : 0 < clockA ν (ageAt ν t₁ σ) := by unfold clockA; positivity
  have hf : B0579.IsCylTest (ν ^ (-2 : ℝ)) (rescaleTest (clockA ν (ageAt ν t₁ σ)) φ) :=
    isCylTest_rescale (c := ν ^ (-2 : ℝ)) ha hφ
  obtain ⟨⟨ω₀, hω₀⟩, -⟩ := UnforcedLeray.Short.IIb.free_cyl_exists_unique m ν (ν ^ (-2 : ℝ)) hm
    hν hc tr htr (ageAt ν t₁ σ) hs _ (hf.memLp m)
  have hae := freeBlock_testW_ae hF hν hσ hστ hτB hs ht hφ hω₀
  have hN : 0 < clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ) := clockN_pos P hν hs ht
  constructor
  · filter_upwards [(Planar.wMeasure_ac m).ae_le hae] with z hz
    rw [hz]
    by_cases hmem : cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))
    · rw [cellZeroExt, Set.indicator_of_mem hmem]
      simp only [JscaleInv]
      rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_im]
    · rw [cellZeroExt, Set.indicator_of_notMem hmem, mul_zero, Complex.zero_im]
  · have hVm : AEStronglyMeasurable
        (JscaleInv (clockA ν (ageAt ν t₁ τ)) (fun x => ((ω₀ (ageAt ν t₁ τ) x : ℝ) : ℂ)))
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) m) :=
      (ComplCouplingSub.memLp_JscaleInv (by linarith) (one_le_clockA hν.le ht)
        (show MemLp (fun x => ((ω₀ (ageAt ν t₁ τ) x : ℝ) : ℂ)) 2
          (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) from
          ((hω₀.memX _ hst).ofReal (K := ℂ)))).1
    have h1 : ENNReal.ofReal ‖F_rel τ σ (testW m hφ)‖ =
        ENNReal.ofReal (clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ))⁻¹ *
          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) m
            (JscaleInv (clockA ν (ageAt ν t₁ τ)) (fun x => ((ω₀ (ageAt ν t₁ τ) x : ℝ) : ℂ))) := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
        eLpNorm_congr_ae ((Planar.wMeasure_ac m).ae_le hae)]
      have e : (fun z : ℂ => ((clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ) : ℂ))⁻¹ *
          cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))
            (JscaleInv (clockA ν (ageAt ν t₁ τ)) (fun x => ((ω₀ (ageAt ν t₁ τ) x : ℝ) : ℂ)))
            (cToPlane z)) =
          ((clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ) : ℂ))⁻¹ • (fun z : ℂ =>
            cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))
              (JscaleInv (clockA ν (ageAt ν t₁ τ)) (fun x => ((ω₀ (ageAt ν t₁ τ) x : ℝ) : ℂ)))
              (cToPlane z)) := rfl
      rw [e, eLpNorm_const_smul, eLpNorm_cellZeroExt_cToPlane _ m hVm]
      congr 1
      rw [← ofReal_norm, norm_inv, Complex.norm_real, Real.norm_of_nonneg hN.le]
    have h2 := hE _ hf ω₀ hω₀
    have hJ : JscaleInv (clockA ν (ageAt ν t₁ σ))
        (fun x => ((rescaleTest (clockA ν (ageAt ν t₁ σ)) φ x : ℝ) : ℂ)) =
          fun y => ((φ y : ℝ) : ℂ) := by
      funext y
      exact jscaleInv_rescale ha φ y
    rw [hJ, ← norm_testW m hφ] at h2
    have h3 : ENNReal.ofReal ‖F_rel τ σ (testW m hφ)‖ ≤ ENNReal.ofReal (K * ‖testW m hφ‖) := by
      rw [h1, ENNReal.ofReal_mul hK]
      calc ENNReal.ofReal (clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ))⁻¹ *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) m
              (JscaleInv (clockA ν (ageAt ν t₁ τ)) (fun x => ((ω₀ (ageAt ν t₁ τ) x : ℝ) : ℂ)))
          ≤ ENNReal.ofReal (clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ))⁻¹ *
            (ENNReal.ofReal (clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ)) *
              (ENNReal.ofReal K * ENNReal.ofReal ‖testW m hφ‖)) := mul_le_mul_right h2 _
        _ = ENNReal.ofReal K * ENNReal.ofReal ‖testW m hφ‖ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hN.le), inv_mul_cancel₀ hN.ne',
            ENNReal.ofReal_one, one_mul]
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK (norm_nonneg _))).1 h3

end RelFreeNormSub

open RelFreeNormSub

/-- **Leaf N** (`PartIII-a:T21/c3/2/1/1/org/3/a/2`, SP 2937-2965): in the successive limit,
`‖F_rel τ σ‖ ≤ e^{-Re λ (τ-σ)} + ε` uniformly on the block. -/
theorem relFreeNormLimit (κ : PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3.StrongA.RelFreeNormLimit κ := by
  intro _hκ P _hP m hm _K B hB ε hε
  have hm1 : 1 < m := by linarith
  set E := Real.exp (|P.eigenvalue.re| * B) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  have hεE : 0 < ε / E := div_pos hε hE0
  set η₀ := Real.log (1 + ε / E) / B with hη₀def
  have hlog : 0 < Real.log (1 + ε / E) := Real.log_pos (by linarith)
  have hη₀ : 0 < η₀ := div_pos hlog hB
  have hexpη : Real.exp (η₀ * B) = 1 + ε / E := by
    rw [hη₀def, div_mul_cancel₀ _ hB.ne', Real.exp_log (by linarith)]
  set C' := normGrowthConst m + |P.kappa.re| + 3 / 2 with hC'def
  have hCm : 0 ≤ normGrowthConst m := by unfold normGrowthConst; nlinarith
  have hC'0 : 0 < C' := by positivity
  obtain ⟨b₁, hb₁, H⟩ := relFreeMovingEnergy P hm (half_pos hη₀)
  refine ⟨max b₁ (2 * C' / η₀), le_trans hb₁ (le_max_left _ _), fun b hb => ?_⟩
  have hb1 : b₁ ≤ b := le_trans (le_max_left _ _) hb
  have hb2 : 2 * C' / η₀ ≤ b := le_trans (le_max_right _ _) hb
  have hb0 : 0 < b := lt_of_lt_of_le one_pos (hb₁.trans hb1)
  have hCb : C' / b ≤ η₀ / 2 := by
    rw [div_le_iff₀ hb0]
    rw [div_le_iff₀ hη₀] at hb2
    linarith
  obtain ⟨ν₀, hν₀, G⟩ := H b hb1
  refine ⟨ν₀, hν₀, fun ν hν _hPF tr htr t₁ t₂ ht₁ h12 hbt hBeq F_rel hF σ τ hσ hστ hτB => ?_⟩
  have hν0 : 0 < ν := hν.1
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  have hsI := ageAt_mem_Icc hν0 ht₁ h12 hBeq ⟨hσ, hστ.trans hτB⟩
  have htI := ageAt_mem_Icc hν0 ht₁ h12 hBeq ⟨hσ.trans hστ, hτB⟩
  have hs : 0 ≤ ageAt ν t₁ σ := ht₁.trans hsI.1
  have ht : 0 ≤ ageAt ν t₁ τ := ht₁.trans htI.1
  have hst : ageAt ν t₁ σ ≤ ageAt ν t₁ τ := ageAt_mono_on_block hν0 ht₁ ht₂ hBeq hσ hστ hτB
  have hbt' : b ≤ clockTheta ν (ageAt ν t₁ τ) := hbt.trans (theta_anti hν0 ht htI.2)
  have hΔ : movingZ ν (ageAt ν t₁ τ) - movingZ ν (ageAt ν t₁ σ) = τ - σ := by
    have h1 := movingZ_ageAt_sub hν0 ht₂ hBeq hτB
    have h2 := movingZ_ageAt_sub hν0 ht₂ hBeq (hστ.trans hτB)
    linarith
  have hΔ0 : 0 ≤ τ - σ := sub_nonneg.2 hστ
  have hΔB : τ - σ ≤ B := by linarith
  -- the target factor and the key scalar inequality
  have hM0 : 0 ≤ Real.exp (-P.eigenvalue.re * (τ - σ)) + ε := by positivity
  have hkey : ∀ x : ℝ, x ≤ η₀ →
      Real.exp ((-P.eigenvalue.re + x) * (τ - σ)) ≤
        Real.exp (-P.eigenvalue.re * (τ - σ)) + ε := by
    intro x hx
    have hxΔ : x * (τ - σ) ≤ η₀ * (τ - σ) := mul_le_mul_of_nonneg_right hx hΔ0
    have e1 : Real.exp ((-P.eigenvalue.re + x) * (τ - σ)) ≤
        Real.exp (-P.eigenvalue.re * (τ - σ)) * Real.exp (η₀ * (τ - σ)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have : (-P.eigenvalue.re + x) * (τ - σ) = -P.eigenvalue.re * (τ - σ) + x * (τ - σ) := by
        ring
      linarith
    have e2 : Real.exp (-P.eigenvalue.re * (τ - σ)) ≤ E := by
      refine Real.exp_le_exp.2 ?_
      have h1 : -P.eigenvalue.re * (τ - σ) ≤ |P.eigenvalue.re| * (τ - σ) :=
        mul_le_mul_of_nonneg_right (neg_le_abs _) hΔ0
      have h2 : |P.eigenvalue.re| * (τ - σ) ≤ |P.eigenvalue.re| * B :=
        mul_le_mul_of_nonneg_left hΔB (abs_nonneg _)
      linarith
    have e3 : Real.exp (η₀ * (τ - σ)) ≤ 1 + ε / E := by
      rw [← hexpη]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hΔB hη₀.le)
    have e4 : 1 ≤ Real.exp (η₀ * (τ - σ)) := Real.one_le_exp (mul_nonneg hη₀.le hΔ0)
    have e5 : Real.exp (-P.eigenvalue.re * (τ - σ)) * (Real.exp (η₀ * (τ - σ)) - 1) ≤
        E * (ε / E) :=
      mul_le_mul e2 (by linarith) (by linarith) hE0.le
    rw [mul_div_cancel₀ _ hE0.ne'] at e5
    have e6 : Real.exp (-P.eigenvalue.re * (τ - σ)) * Real.exp (η₀ * (τ - σ)) =
        Real.exp (-P.eigenvalue.re * (τ - σ)) +
          Real.exp (-P.eigenvalue.re * (τ - σ)) * (Real.exp (η₀ * (τ - σ)) - 1) := by ring
    linarith
  have hds : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)) := cellLen_pos hν0 hs
  have hdt : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)) := cellLen_pos hν0 ht
  refine opNorm_le_of_cell_ext (d_s := cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
    (d_t := cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) (F_rel τ σ) hM0
    (fun V hV => ⟨?_, ?_⟩) (fun Y hY => ⟨?_, ?_⟩)
  · -- interior: relative free moving energy on tests, density
    set K := Real.exp ((-P.eigenvalue.re + (normGrowthConst m + |P.kappa.re|) / b + η₀ / 2) *
      (τ - σ)) with hKdef
    have hK0 : 0 ≤ K := (Real.exp_pos _).le
    have hEK : ∀ f : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) f →
        ∀ ω₀ : ℝ → B0579.Plane → ℝ,
          UnforcedLeray.Short.IIb.IsFreeCylFlow m tr (ageAt ν t₁ σ) f ω₀ →
          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) m
              (JscaleInv (clockA ν (ageAt ν t₁ τ))
                (fun x => ((ω₀ (ageAt ν t₁ τ) x : ℝ) : ℂ))) ≤
            ENNReal.ofReal (clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ)) *
              (ENNReal.ofReal K *
                xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))) m
                  (JscaleInv (clockA ν (ageAt ν t₁ σ)) (fun x => ((f x : ℝ) : ℂ)))) := by
      intro f hf ω₀ hω₀
      have := G ν hν tr htr (ageAt ν t₁ σ) (ageAt ν t₁ τ) hs hst hbt' f hf ω₀ hω₀
      rwa [hΔ] at this
    have hVK := norm_apply_le_of_tests hds hK0 (F_rel τ σ)
      (fun φ hφ => freeBlock_testW_bound hF hν0 hm htr hσ hστ hτB hs hst hK0 hEK φ hφ) V hV
    have hKM : K ≤ Real.exp (-P.eigenvalue.re * (τ - σ)) + ε := by
      have hx : (normGrowthConst m + |P.kappa.re|) / b + η₀ / 2 ≤ η₀ := by
        have : (normGrowthConst m + |P.kappa.re|) / b ≤ C' / b :=
          div_le_div_of_nonneg_right (by linarith) hb0.le
        linarith
      have := hkey _ hx
      rw [hKdef]
      calc Real.exp ((-P.eigenvalue.re + (normGrowthConst m + |P.kappa.re|) / b + η₀ / 2) *
            (τ - σ))
          = Real.exp ((-P.eigenvalue.re + ((normGrowthConst m + |P.kappa.re|) / b + η₀ / 2)) *
            (τ - σ)) := by congr 1; ring
        _ ≤ _ := this
    exact hVK.trans (mul_le_mul_of_nonneg_right hKM (norm_nonneg _))
  · exact freeBlock_cell_to_cell hF hν0 hm htr hσ hστ hτB hs ht V hV
  · -- exterior: the dilation cocycle and the normaliser
    rw [freeBlock_ext_eq_smul hF hσ hστ hτB hm1 hds hdt Y hY, norm_smul]
    set N := clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ) with hNdef
    have hN : 0 < N := clockN_pos P hν0 hs ht
    have hNinv : ‖((N : ℂ))⁻¹‖ = N⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hN.le]
    rw [hNinv]
    have hS : ‖extDilW hm1 hds hdt‖ ≤
        Real.exp ((3 / (2 * b)) * (movingZ ν (ageAt ν t₁ τ) - movingZ ν (ageAt ν t₁ σ))) :=
      norm_extDilW_cellLen_le_exp (c := ν ^ (-2 : ℝ)) hm1 (Real.rpow_pos_of_pos hν0 _) hν0 hs hst
        hb0 hbt'
    rw [hΔ] at hS
    have hNlow := exp_beta0_le_clockN P hν0 hs hst hb0 hbt'
    rw [hΔ, ← hNdef] at hNlow
    have hfac : N⁻¹ * Real.exp ((3 / (2 * b)) * (τ - σ)) ≤
        Real.exp (-P.eigenvalue.re * (τ - σ)) + ε := by
      have hx : (|P.kappa.re| + 3 / 2) / b ≤ η₀ := by
        have : (|P.kappa.re| + 3 / 2) / b ≤ C' / b :=
          div_le_div_of_nonneg_right (by linarith) hb0.le
        linarith
      refine le_trans ?_ (hkey _ hx)
      rw [inv_mul_le_iff₀ hN]
      calc Real.exp ((3 / (2 * b)) * (τ - σ))
          = Real.exp ((P.eigenvalue.re - |P.kappa.re| / b) * (τ - σ)) *
              Real.exp ((-P.eigenvalue.re + (|P.kappa.re| + 3 / 2) / b) * (τ - σ)) := by
            rw [← Real.exp_add]
            congr 1
            field_simp
            ring
        _ ≤ N * Real.exp ((-P.eigenvalue.re + (|P.kappa.re| + 3 / 2) / b) * (τ - σ)) :=
            mul_le_mul_of_nonneg_right hNlow (Real.exp_pos _).le
    calc N⁻¹ * ‖extDilW hm1 hds hdt Y‖ ≤ N⁻¹ * (‖extDilW hm1 hds hdt‖ * ‖Y‖) :=
          mul_le_mul_of_nonneg_left ((extDilW hm1 hds hdt).le_opNorm Y) (inv_nonneg.2 hN.le)
      _ ≤ N⁻¹ * (Real.exp ((3 / (2 * b)) * (τ - σ)) * ‖Y‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
            (inv_nonneg.2 hN.le)
      _ = (N⁻¹ * Real.exp ((3 / (2 * b)) * (τ - σ))) * ‖Y‖ := by ring
      _ ≤ (Real.exp (-P.eigenvalue.re * (τ - σ)) + ε) * ‖Y‖ :=
          mul_le_mul_of_nonneg_right hfac (norm_nonneg _)
  · exact freeBlock_ext_exteriorSupported hF hσ hστ hτB hds hdt Y hY

end UnforcedLeray.Short.IIIa
