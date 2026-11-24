import UnforcedLeray.Short.PartIIb.Sub.ComparisonAndStrongDesign
import UnforcedLeray.Short.PartIIb.Tasks.QuadraticEstimate.IBP
import UnforcedLeray.Short.PartIIb.Tasks.QuadraticEstimate.InletLp
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.LerayOnForce
import UnforcedLeray.Short.PartIIb.Tasks.ResponseOperator.BodySol
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.YqOfFields
import UnforcedLeray.Short.PartIIb.Tasks.QuadraticEstimate.Norm

/-!


Source of record: `the November 2 reference manuscript`, lines 2503-2518.

At fixed slow data `(Σ, λ, q)` and `dm > 0`, for `z = (w, A)` and `z' = (w', A')` in `p.Z` with
full fields `u = p.uOf z = e + w` and `u' = p.uOf z' = e' + w'`:
1. `IBP.lean` (`Tasks/QuadraticEstimate/IBP.lean`) defines the pointwise bilinear convection field
   `quadFieldPtw p z z' g g'` after one spatial integration by parts and proves `quadFieldPtw_pairF`:
   `-pairF p.period (advT (p.uOf z) Φ) (p.uOf z') = pairF p.period Φ (quadFieldPtw p z z' g g')`,
   together with periodicity (`quadFieldPtw_periodic`) and joint strong measurability
   (`stronglyMeasurable_quadFieldPtw`).
2. `InletLp.lean` (`Tasks/QuadraticEstimate/InletLp.lean`) proves `inlet_dy_phaseLpNorm_le`:
   `phaseLpNorm p.period bgp (dy j (p.eFun (p.coord z))) ≤ ENNReal.ofReal (C_de * (p.ν ^ k_de)⁻¹ * ‖z‖)`.
3. Here we prove:
   * `norm_bodyOp_zero_le_graphNormD` and `wOf_exists_grad_bound`: existence of weak spatial
     gradients `g : Fin 3 → Yq p.period q0E` of `p.wOf z` with
     `‖g j‖ ≤ (RespOp.C_graph * 23 + 1) * (p.ν ^ 1)⁻¹ * ‖z‖` (`commonBodyGraphBound`);
   * `phaseLpNorm_rep_eq`: `phaseLpNorm P bgp (fun x => rep F x.1 x.2) = ENNReal.ofReal ‖F‖`;
   * `rep_wOf_ae_bound` and `uOf_ae_bound`: `phaseμ p.period`-a.e. `L^∞` bounds on `rep (p.wOf z)`
     and `p.uOf z` from `graphSupEmbedding` and `h4 : AffineInletFacts`;
   * `forceSpace_ext_of_solTest`, `quadRel_unique`, and `quadBilinear_of_pointwise`: uniqueness of
     `b : p.Y` satisfying `p.QuadRel z z' b` (`solSeparation`) and automatic `ℝ`-bilinearity of
     the resulting operator `B : p.Z →ₗ[ℝ] p.Z →ₗ[ℝ] p.Y`;
   * `quadBound_of_leaf`: conditional assembly of `QuadBound` from `QuadFieldInYqSymm`;
   * `quadFieldInYqSymm`: proof of the leaf. Bilinearity of the convection pairing from the
     a.e. linearity of `z ↦ p.uOf z` and integrability on a phase cell (`QuadraticEstimate/PairLin`);
     `f` from `yqOfFields`, real since `u`, `∇u` are a.e. real (`grad_mem_realSub`), in the class
     (2.2) by the pairing identity `quadFieldPtw_pairF`, the chain rule `gAct_advT` and
     `phaseFundamental` (`QuadraticEstimate/Symm`); `‖f‖_{Y_p} ≤ ∑ₖ (|u'|_∞‖Dₖu‖ + |u|_∞‖Dₖu'‖)`
     (`QuadraticEstimate/Norm`);
   * `quadBound_of`: `QuadBound` from `h4 : AffineInletFacts`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Blueprint UnforcedLeray.B0411 UnforcedLeray.B0412
open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.Short.PartIIa UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Weak spatial gradient bound for `p.wOf z` in `Y_{q₀}` -/

/-- At `μ = 0`, `bodyOp P ν q0E 0 w = L0D w` has `Y_{q₀}` norm at most `graphNormD w`. -/
theorem norm_bodyOp_zero_le_graphNormD {P ν : ℝ} [Fact (0 < P)] (w : B0411.D P ν q0E) :
    ‖bodyOp P ν q0E 0 w‖ ≤ B0411.graphNormD w := by
  have heq : bodyOp P ν q0E 0 w = B0411.L0D w := by
    simp [bodyOp, B0411.L0L_apply]
  rw [heq]
  have hc : ‖(1 / 2 : ℂ)‖ ≤ 1 := by norm_num
  have h1 : ‖(1 / 2 : ℂ) • (w : Yq P q0E)‖ ≤ ‖(w : Yq P q0E)‖ := by
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) hc
  have h2 := norm_sub_le (T0D w - nuLapD w) ((1 / 2 : ℂ) • (w : Yq P q0E))
  have h3 := norm_sub_le (T0D w) (nuLapD w)
  unfold B0411.L0D B0411.graphNormD
  linarith

/-- Constant for the `Y_{q₀}` gradient bound of `p.wOf z`. -/
def C_wgrad : ℝ := RespOp.C_graph * 23 + 1

theorem C_wgrad_pos : 0 < C_wgrad := by
  unfold C_wgrad
  have := RespOp.C_graph_nonneg
  positivity

/-- For `p.period ≤ 1` and `p.ν ≤ 1`, every `z : p.Z` has a weak spatial gradient
`g : Fin 3 → Yq p.period q0E` of `p.wOf z` with `‖g j‖ ≤ C_wgrad * (p.ν ^ 1)⁻¹ * ‖z‖`. -/
theorem wOf_exists_grad_bound (p : Params) (hp1 : p.period ≤ 1) (hν1 : p.ν ≤ 1) (z : p.Z) :
    ∃ g : Fin 3 → Yq p.period q0E, HasGrad (p.wOf z) g ∧
      ∀ j : Fin 3, ‖g j‖ ≤ C_wgrad * (p.ν ^ 1)⁻¹ * ‖z‖ := by
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  let u : B0411.D p.period p.ν q0E := B0412.XToD (p.graphX z)
  have hu_coe : (u : Yq p.period q0E) = p.wOf z := rfl
  have hu_gn : B0411.graphNormD u ≤ ‖z‖ := S1Sub.graphNormD_graphX_le_norm p z
  obtain ⟨g, hgrad, hbound⟩ :=
    (commonBodyGraphBound q0E one_lt_q0E B0412.q0E_lt_three).choose_spec.2
      p.period hp1 p.ν p.ν_pos 0 RespOp.gammaR_q0E_pos u
  refine ⟨g, hu_coe ▸ hgrad, fun j => ?_⟩
  have hfac : 1 + (1 + ‖(0 : ℂ)‖) / ((0 : ℂ).re + gammaR q0E) = 23 := by
    rw [norm_zero, Complex.zero_re, zero_add, add_zero, RespOp.gammaR_q0E_eq]
    norm_num
  change B0411.graphNormD u + Real.sqrt p.ν * ∑ k, ‖g k‖ ≤
    RespOp.C_graph * (1 + (1 + ‖(0 : ℂ)‖) / ((0 : ℂ).re + gammaR q0E)) *
      ‖bodyOp p.period p.ν q0E 0 u‖ at hbound
  rw [hfac] at hbound
  have hgn0 : 0 ≤ B0411.graphNormD u := S1Sub.s1_graphNormD_nonneg u
  have hbody_le : ‖bodyOp p.period p.ν q0E 0 u‖ ≤ ‖z‖ :=
    (norm_bodyOp_zero_le_graphNormD u).trans hu_gn
  have hCg0 : 0 ≤ RespOp.C_graph * 23 := mul_nonneg RespOp.C_graph_nonneg (by norm_num)
  have hsum_le : Real.sqrt p.ν * ∑ k, ‖g k‖ ≤ C_wgrad * ‖z‖ := by
    unfold C_wgrad
    have h1 : Real.sqrt p.ν * ∑ k, ‖g k‖ ≤
        RespOp.C_graph * 23 * ‖bodyOp p.period p.ν q0E 0 u‖ := by linarith
    have h2 : RespOp.C_graph * 23 * ‖bodyOp p.period p.ν q0E 0 u‖ ≤
        RespOp.C_graph * 23 * ‖z‖ := mul_le_mul_of_nonneg_left hbody_le hCg0
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    linarith
  have hj_le_sum : ‖g j‖ ≤ ∑ k : Fin 3, ‖g k‖ :=
    Finset.single_le_sum (fun k _ => norm_nonneg (g k)) (Finset.mem_univ j)
  have hν_pos : 0 < p.ν := p.ν_pos
  have hν_le_sqrt : p.ν ≤ Real.sqrt p.ν :=
    (Real.le_sqrt hν_pos.le hν_pos.le).2 (by nlinarith [hν_pos, hν1])
  have hsum_nonneg : 0 ≤ ∑ k : Fin 3, ‖g k‖ :=
    Finset.sum_nonneg fun k _ => norm_nonneg (g k)
  have hν_gj : p.ν * ‖g j‖ ≤ C_wgrad * ‖z‖ := by
    calc p.ν * ‖g j‖
        ≤ p.ν * ∑ k : Fin 3, ‖g k‖ := mul_le_mul_of_nonneg_left hj_le_sum hν_pos.le
      _ ≤ Real.sqrt p.ν * ∑ k : Fin 3, ‖g k‖ := mul_le_mul_of_nonneg_right hν_le_sqrt hsum_nonneg
      _ ≤ C_wgrad * ‖z‖ := hsum_le
  have hinv : 0 ≤ (p.ν ^ 1)⁻¹ := by positivity
  calc ‖g j‖
      = (p.ν ^ 1)⁻¹ * (p.ν * ‖g j‖) := by
          rw [pow_one, inv_mul_cancel_left₀ hν_pos.ne']
    _ ≤ (p.ν ^ 1)⁻¹ * (C_wgrad * ‖z‖) := mul_le_mul_of_nonneg_left hν_gj hinv
    _ = C_wgrad * (p.ν ^ 1)⁻¹ * ‖z‖ := by ring

/-- The `phaseLpNorm` of `rep F` at `bgp` equals `ENNReal.ofReal ‖F‖`. -/
theorem phaseLpNorm_rep_eq (P : ℝ) [Fact (0 < P)] (F : Yq P q0E) :
    phaseLpNorm P bgp (fun x : ℝ × Space => rep F x.1 x.2) = ENNReal.ofReal ‖F‖ := by
  have hRep : UnforcedLeray.Short.PartIIa.Rep.IsRep F (fun x : ℝ × Space => rep F x.1 x.2) :=
    ⟨stronglyMeasurable_rep F, Eventually.of_forall fun τ => rep_slice F τ⟩
  have h1 := yqOfFields_norm P (fun x : ℝ × Space => rep F x.1 x.2) F hRep
  have hp : q0E.toReal = bgp := by
    rw [B0412.q0E_toReal]
    norm_num [bgp]
  have hne : q0E.toReal ≠ 0 := by rw [hp]; norm_num [bgp]
  have hI : ∫⁻ t in Ioc (0 : ℝ) P, ‖F (t : AddCircle P)‖ₑ ^ q0E.toReal =
      ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖rep F t y‖ₑ ^ q0E.toReal := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hRep.slice] with t ht
    rw [← lintegral_enorm_rpow_Lp (F (t : AddCircle P)) q0E_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [ht] with y hy
    rw [hy]
  have hmain : ‖F‖ₑ ^ q0E.toReal =
      ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖rep F t y‖ₑ ^ q0E.toReal := by
    rw [B0411.enorm_rpow_Yq F q0E_ne_top, hI]
  unfold phaseLpNorm
  rw [← hp, ← hmain, one_div, ENNReal.rpow_rpow_inv hne, ofReal_norm]

/-! ## 2. Quantitative `L^∞(phaseμ)` bounds on `rep (p.wOf z)` and `p.uOf z` -/

/-- Quantitative `phaseμ p.period`-a.e. bound on `rep (p.wOf z)` for `p.period ≤ 1`, `p.ν ≤ 1`. -/
theorem rep_wOf_ae_bound :
    ∃ C_w : ℝ, 0 < C_w ∧ ∀ (p : Params), p.period ≤ 1 → p.ν ≤ 1 → ∀ z : p.Z,
      ∀ᵐ x ∂(phaseμ p.period), ‖rep (p.wOf z) x.1 x.2‖ ≤ C_w * (p.ν ^ 1)⁻¹ * ‖z‖ := by
  have h52 : (5 / 2 : ℝ≥0∞) < q0E := by
    unfold q0E
    rw [show (5 / 2 : ℝ≥0∞) = ENNReal.ofReal (5 / 2) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num [UnforcedLeray.B0281.q0_eq])).2
      (by norm_num [UnforcedLeray.B0281.q0_eq])
  obtain ⟨C, hC0, hS⟩ := graphSupEmbedding q0E h52 q0E_ne_top
  refine ⟨C + 1, by linarith, ?_⟩
  intro p hp1 hν1 z
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  let u : B0411.D p.period p.ν q0E := B0412.XToD (p.graphX z)
  obtain ⟨W, -, hWae, hWb⟩ := hS p.period hp1 p.ν p.ν_pos u
  have hν_rpow : p.ν ^ (-(3 / (2 * q0E.toReal))) ≤ (p.ν ^ 1)⁻¹ := by
    have hexp : -(1 : ℝ) ≤ -(3 / (2 * q0E.toReal)) := by
      rw [B0412.q0E_toReal]
      norm_num
    calc p.ν ^ (-(3 / (2 * q0E.toReal)))
        ≤ p.ν ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_ge p.ν_pos hν1 hexp
      _ = (p.ν ^ 1)⁻¹ := by rw [Real.rpow_neg_one, pow_one]
  have hu_gn : B0411.graphNormD u ≤ ‖z‖ := S1Sub.graphNormD_graphX_le_norm p z
  have hgn0 : 0 ≤ B0411.graphNormD u := S1Sub.s1_graphNormD_nonneg u
  have hrp0 : 0 ≤ p.ν ^ (-(3 / (2 * q0E.toReal))) := Real.rpow_nonneg p.ν_pos.le _
  have hC1p : 0 ≤ (C + 1) * (p.ν ^ 1)⁻¹ := by have := p.ν_pos; positivity
  refine rep_ae_bound (p.wOf z) W ((C + 1) * (p.ν ^ 1)⁻¹ * ‖z‖) hWae fun τ y => ?_
  have hb := hWb τ y
  calc ‖W (τ, y)‖
      ≤ C * p.ν ^ (-(3 / (2 * q0E.toReal))) * B0411.graphNormD u := hb
    _ ≤ (C + 1) * (p.ν ^ 1)⁻¹ * ‖z‖ := by
        have : C ≤ C + 1 := by linarith
        gcongr

/-- Combined quantitative `phaseμ p.period`-a.e. bound on `rep (p.wOf z)` and `p.uOf z`
from `h4 : AffineInletFacts` and `rep_wOf_ae_bound`. -/
theorem uOf_ae_bound (h4 : AffineInletFacts)
    (Sig : ℝ) (lam : ℂ) (q : Planar.Profile) (hSig : 0 < Sig)
    (hq : Planar.IsGrowingEigenpair lam q) (dm dp : ℝ) (hdm : 0 < dm) :
    ∃ (C_u : ℝ) (k_u : ℕ) (ν_u : ℝ), 0 < C_u ∧ 0 < ν_u ∧ ν_u ≤ 1 ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν_u → p.ageCut = Sig → p.mode = q →
        p.period ≤ 1 ∧
        ∀ z : p.Z,
          (∀ᵐ x ∂(phaseμ p.period), ‖rep (p.wOf z) x.1 x.2‖ ≤ C_u * (p.ν ^ k_u)⁻¹ * ‖z‖) ∧
          (∀ᵐ x ∂(phaseμ p.period), ‖p.uOf z x‖ ≤ C_u * (p.ν ^ k_u)⁻¹ * ‖z‖) := by
  obtain ⟨C_w, hCw, Hw⟩ := rep_wOf_ae_bound
  obtain ⟨C_in, k_in, ν_in, hCin, hνin, Hin⟩ :=
    S1Sub.inlet_w1_le_of_affineInletFacts h4 Sig lam q hSig hq dm dp hdm
  set ν_u : ℝ := min (min ν_in 1) (dm ^ 3 / 12)
  have hνu_pos : 0 < ν_u := lt_min (lt_min hνin zero_lt_one) (by positivity)
  have hνu_le1 : ν_u ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  refine ⟨C_w + C_in, max 1 k_in, ν_u, by positivity, hνu_pos, hνu_le1, ?_⟩
  intro p d hreg hν hSg hmode
  have hν_in : p.ν ≤ ν_in := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν1 : p.ν ≤ 1 := hν.trans hνu_le1
  have hν_dm : p.ν ≤ dm ^ 3 / 12 := hν.trans (min_le_right _ _)
  have hp1 : p.period ≤ 1 := bgCorr_period_le_one hreg hν_dm
  refine ⟨hp1, fun z => ?_⟩
  have hk1 : (p.ν ^ 1)⁻¹ ≤ (p.ν ^ max 1 k_in)⁻¹ :=
    S1Sub.s1_inv_pow_mono_of_le_one p.ν_pos hν1 (le_max_left 1 k_in)
  have hkin : (p.ν ^ k_in)⁻¹ ≤ (p.ν ^ max 1 k_in)⁻¹ :=
    S1Sub.s1_inv_pow_mono_of_le_one p.ν_pos hν1 (le_max_right 1 k_in)
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hνp1 : 0 ≤ (p.ν ^ 1)⁻¹ := by have := p.ν_pos; positivity
  have hνp_in : 0 ≤ (p.ν ^ k_in)⁻¹ := by have := p.ν_pos; positivity
  have hw_ae : ∀ᵐ x ∂(phaseμ p.period),
      ‖rep (p.wOf z) x.1 x.2‖ ≤ (C_w + C_in) * (p.ν ^ max 1 k_in)⁻¹ * ‖z‖ := by
    filter_upwards [Hw p hp1 hν1 z] with x hx
    calc ‖rep (p.wOf z) x.1 x.2‖
        ≤ C_w * (p.ν ^ 1)⁻¹ * ‖z‖ := hx
      _ ≤ (C_w + C_in) * (p.ν ^ max 1 k_in)⁻¹ * ‖z‖ := by
          have : C_w ≤ C_w + C_in := by linarith
          gcongr
  refine ⟨hw_ae, ?_⟩
  filter_upwards [Hw p hp1 hν1 z] with x hx
  have hin_x : ‖p.eFun (p.coord z) x‖ ≤ C_in * (p.ν ^ k_in)⁻¹ * ‖z‖ := by
    have heq : p.eFun (p.coord z) x = realC (∑ i : Fin 2, p.coord z i • p.inlet i x.1 x.2) := rfl
    have hnrc : ∀ v : Space, ‖realC v‖ = ‖v‖ := fun v => by
      simp only [EuclideanSpace.norm_eq, realC_apply, Complex.norm_real]
    rw [heq, hnrc]
    exact (Hin p d hreg hν_in hSg hmode z x.1 x.2).1
  have hu_le : ‖p.uOf z x‖ ≤ ‖p.eFun (p.coord z) x‖ + ‖rep (p.wOf z) x.1 x.2‖ :=
    norm_add_le _ _
  calc ‖p.uOf z x‖
      ≤ C_in * (p.ν ^ k_in)⁻¹ * ‖z‖ + C_w * (p.ν ^ 1)⁻¹ * ‖z‖ :=
        hu_le.trans (add_le_add hin_x hx)
    _ ≤ C_in * (p.ν ^ max 1 k_in)⁻¹ * ‖z‖ + C_w * (p.ν ^ max 1 k_in)⁻¹ * ‖z‖ := by
        gcongr
    _ = (C_w + C_in) * (p.ν ^ max 1 k_in)⁻¹ * ‖z‖ := by ring

/-! ## 3. Uniqueness of `QuadRel` in `p.Y` and bilinearity from solenoidal pairings -/

/-- Elements of `p.Y = forceSpace p.period` are separated by solenoidal phase tests (`solSeparation`). -/
theorem forceSpace_ext_of_solTest (p : Params) {b₁ b₂ : p.Y}
    (h : ∀ Φ, IsSolTest p.period Φ →
      phasePair p.period q0E Φ (b₁ : Yq p.period q0E) =
        phasePair p.period q0E Φ (b₂ : Yq p.period q0E)) :
    b₁ = b₂ := by
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  apply Subtype.ext
  rw [← sub_eq_zero]
  have hsol : IsPhaseSolenoidal ((b₁ - b₂ : p.Y) : Yq p.period q0E) :=
    ((mem_forceSpace p.period).1 (b₁ - b₂).2).2.1
  refine solSeparation q0E one_lt_q0E q0E_ne_top p.period
    ((b₁ - b₂ : p.Y) : Yq p.period q0E) hsol fun Φ hΦ => ?_
  rw [Submodule.coe_sub, map_sub, h Φ hΦ, sub_self]

/-- Uniqueness of the projected quadratic source `b : p.Y` satisfying `p.QuadRel z z' b`. -/
theorem quadRel_unique (p : Params) (z z' : p.Z) {b₁ b₂ : p.Y}
    (h₁ : p.QuadRel z z' (b₁ : Yq p.period q0E))
    (h₂ : p.QuadRel z z' (b₂ : Yq p.period q0E)) :
    b₁ = b₂ :=
  forceSpace_ext_of_solTest p fun Φ hΦ => (h₁ Φ hΦ).trans (h₂ Φ hΦ).symm

/-- If for every `(z, z')` there exists `b : p.Y` satisfying `p.QuadRel z z' b` with
`‖b‖ ≤ M * ‖z‖ * ‖z'‖`, and `(z, z') ↦ -pairF p.period (advT (p.uOf z) Φ) (p.uOf z')` is
`ℝ`-bilinear on solenoidal phase tests `Φ`, then `b(z, z')` forms an `ℝ`-bilinear map
`B : p.Z →ₗ[ℝ] p.Z →ₗ[ℝ] p.Y`. -/
theorem quadBilinear_of_pointwise (p : Params) (M : ℝ)
    (hex : ∀ z z' : p.Z, ∃ b : p.Y, p.QuadRel z z' (b : Yq p.period q0E) ∧ ‖b‖ ≤ M * ‖z‖ * ‖z'‖)
    (hadd_left : ∀ z₁ z₂ z' : p.Z, ∀ Φ, IsSolTest p.period Φ →
      -pairF p.period (advT (p.uOf (z₁ + z₂)) Φ) (p.uOf z') =
        -pairF p.period (advT (p.uOf z₁) Φ) (p.uOf z') +
          -pairF p.period (advT (p.uOf z₂) Φ) (p.uOf z'))
    (hsmul_left : ∀ (a : ℝ) (z z' : p.Z) (Φ), IsSolTest p.period Φ →
      -pairF p.period (advT (p.uOf (a • z)) Φ) (p.uOf z') =
        (a : ℂ) * (-pairF p.period (advT (p.uOf z) Φ) (p.uOf z')))
    (hadd_right : ∀ z z₁' z₂' : p.Z, ∀ Φ, IsSolTest p.period Φ →
      -pairF p.period (advT (p.uOf z) Φ) (p.uOf (z₁' + z₂')) =
        -pairF p.period (advT (p.uOf z) Φ) (p.uOf z₁') +
          -pairF p.period (advT (p.uOf z) Φ) (p.uOf z₂'))
    (hsmul_right : ∀ (a : ℝ) (z z' : p.Z) (Φ), IsSolTest p.period Φ →
      -pairF p.period (advT (p.uOf z) Φ) (p.uOf (a • z')) =
        (a : ℂ) * (-pairF p.period (advT (p.uOf z) Φ) (p.uOf z'))) :
    ∃ B : p.Z →ₗ[ℝ] p.Z →ₗ[ℝ] p.Y, (∀ z z', p.QuadRel z z' (B z z')) ∧
      ∀ z z', ‖B z z'‖ ≤ M * ‖z‖ * ‖z'‖ := by
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  choose b hb_rel hb_norm using hex
  have hsmY : ∀ (a : ℝ) (u : Yq p.period q0E) (Φ : ℝ × Space → CVec3),
      phasePair p.period q0E Φ (a • u) = (a : ℂ) * phasePair p.period q0E Φ u := by
    intro a u Φ
    rw [ContinuousLinearMap.map_smul_of_tower, Complex.real_smul]
  let Bz (z : p.Z) : p.Z →ₗ[ℝ] p.Y :=
    { toFun := fun z' => b z z'
      map_add' := fun z₁' z₂' => by
        refine forceSpace_ext_of_solTest p fun Φ hΦ => ?_
        rw [Submodule.coe_add, map_add, hb_rel z (z₁' + z₂') Φ hΦ,
          hb_rel z z₁' Φ hΦ, hb_rel z z₂' Φ hΦ, hadd_right z z₁' z₂' Φ hΦ]
      map_smul' := fun a z' => by
        refine forceSpace_ext_of_solTest p fun Φ hΦ => ?_
        simp only [RingHom.id_apply, Submodule.coe_smul_of_tower, hsmY,
          hb_rel z (a • z') Φ hΦ, hb_rel z z' Φ hΦ, hsmul_right a z z' Φ hΦ] }
  let B : p.Z →ₗ[ℝ] p.Z →ₗ[ℝ] p.Y :=
    { toFun := Bz
      map_add' := fun z₁ z₂ => by
        ext z' : 1
        refine forceSpace_ext_of_solTest p fun Φ hΦ => ?_
        change phasePair p.period q0E Φ (b (z₁ + z₂) z' : Yq p.period q0E) =
          phasePair p.period q0E Φ ((b z₁ z' + b z₂ z' : p.Y) : Yq p.period q0E)
        rw [Submodule.coe_add, map_add, hb_rel (z₁ + z₂) z' Φ hΦ,
          hb_rel z₁ z' Φ hΦ, hb_rel z₂ z' Φ hΦ, hadd_left z₁ z₂ z' Φ hΦ]
      map_smul' := fun a z => by
        ext z' : 1
        refine forceSpace_ext_of_solTest p fun Φ hΦ => ?_
        change phasePair p.period q0E Φ (b (a • z) z' : Yq p.period q0E) =
          phasePair p.period q0E Φ ((a • b z z' : p.Y) : Yq p.period q0E)
        rw [Submodule.coe_smul_of_tower, hsmY,
          hb_rel (a • z) z' Φ hΦ, hb_rel z z' Φ hΦ, hsmul_left a z z' Φ hΦ] }
  exact ⟨B, hb_rel, hb_norm⟩

/-! ## 4. Packaging leaf for `quadFieldPtw` and conditional assembly of `QuadBound` -/

/-- **Remaining leaf for `PartII-b:Q1` (`QuadFieldInYqSymm`)**:
Given the `L^∞(phaseμ)` bounds on `p.uOf z, p.uOf z'` (`uOf_ae_bound`) and the `Y_{q₀}` bounds on
`dy k (p.eFun (p.coord z))` (`inlet_dy_phaseLpNorm_le`) and `g, g'` (`wOf_exists_grad_bound`),
the pointwise bilinear field `quadFieldPtw p z z' g g'` (`IBP.lean`) represents a real
`𝒪`-invariant element `f ∈ Yq p.period q0E` with
`‖f‖ ≤ C_f * (p.ν ^ k_f)⁻¹ * ‖z‖ * ‖z'‖`, and the pairing
`(z, z') ↦ -pairF p.period (advT (p.uOf z) Φ) (p.uOf z')` is `ℝ`-bilinear on solenoidal tests. -/
def QuadFieldInYqSymm : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Planar.Profile), 0 < Sig →
    Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm →
  ∀ (C_u C_de : ℝ) (k_u k_de : ℕ), 0 < C_u → 0 < C_de →
    ∃ (C_f : ℝ) (k_f : ℕ), 0 < C_f ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.period ≤ 1 → p.ν ≤ 1 →
        p.ageCut = Sig → p.mode = q →
        (∀ z : p.Z,
          (∀ᵐ x ∂(phaseμ p.period), ‖rep (p.wOf z) x.1 x.2‖ ≤ C_u * (p.ν ^ k_u)⁻¹ * ‖z‖) ∧
          (∀ᵐ x ∂(phaseμ p.period), ‖p.uOf z x‖ ≤ C_u * (p.ν ^ k_u)⁻¹ * ‖z‖) ∧
          (∀ j : Fin 3, phaseLpNorm p.period bgp (dy j (p.eFun (p.coord z))) ≤
            ENNReal.ofReal (C_de * (p.ν ^ k_de)⁻¹ * ‖z‖))) →
        ((∀ z₁ z₂ z' : p.Z, ∀ Φ, IsSolTest p.period Φ →
            -pairF p.period (advT (p.uOf (z₁ + z₂)) Φ) (p.uOf z') =
              -pairF p.period (advT (p.uOf z₁) Φ) (p.uOf z') +
                -pairF p.period (advT (p.uOf z₂) Φ) (p.uOf z')) ∧
          (∀ (a : ℝ) (z z' : p.Z) (Φ), IsSolTest p.period Φ →
            -pairF p.period (advT (p.uOf (a • z)) Φ) (p.uOf z') =
              (a : ℂ) * (-pairF p.period (advT (p.uOf z) Φ) (p.uOf z'))) ∧
          (∀ z z₁' z₂' : p.Z, ∀ Φ, IsSolTest p.period Φ →
            -pairF p.period (advT (p.uOf z) Φ) (p.uOf (z₁' + z₂')) =
              -pairF p.period (advT (p.uOf z) Φ) (p.uOf z₁') +
                -pairF p.period (advT (p.uOf z) Φ) (p.uOf z₂')) ∧
          (∀ (a : ℝ) (z z' : p.Z) (Φ), IsSolTest p.period Φ →
            -pairF p.period (advT (p.uOf z) Φ) (p.uOf (a • z')) =
              (a : ℂ) * (-pairF p.period (advT (p.uOf z) Φ) (p.uOf z')))) ∧
        ∀ (z z' : p.Z) (g g' : Fin 3 → Yq p.period q0E),
          HasGrad (p.wOf z) g → HasGrad (p.wOf z') g' →
          (∀ j : Fin 3, ‖g j‖ ≤ C_wgrad * (p.ν ^ 1)⁻¹ * ‖z‖) →
          (∀ j : Fin 3, ‖g' j‖ ≤ C_wgrad * (p.ν ^ 1)⁻¹ * ‖z'‖) →
          ∃ f : Yq p.period q0E,
            f ∈ realSub p.period q0E ∧ f ∈ Osym p.period q0E ∧
            HasRep f (quadFieldPtw p z z' g g') ∧
            ‖f‖ ≤ C_f * (p.ν ^ k_f)⁻¹ * ‖z‖ * ‖z'‖

/-- **Conditional assembly of `QuadBound` (`PartII-b:Q1`, SP 2503-2518)** from
`h4 : AffineInletFacts`, `inlet_dy_phaseLpNorm_le`, `wOf_exists_grad_bound`, `uOf_ae_bound`,
`quadFieldPtw_pairF`, `lerayOnForce_proof`, `quadBilinear_of_pointwise`, and `QuadFieldInYqSymm`. -/
theorem quadBound_of_leaf (hLeaf : QuadFieldInYqSymm) (h4 : AffineInletFacts) :
    QuadBound := by
  obtain ⟨K_L, hKL, HLeray⟩ := lerayOnForce_proof
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨C_u, k_u, ν_u, hCu, hνu, hνu1, Hu⟩ := uOf_ae_bound h4 Sig lam q hSig hq dm dp hdm
  obtain ⟨C_de, k_de, ν_de, hCde, hνde, hνde1, Hde⟩ :=
    inlet_dy_phaseLpNorm_le Sig lam q hSig hq dm dp hdm
  obtain ⟨C_f, k_f, hCf, Hleaf⟩ :=
    hLeaf Sig lam q hSig hq dm dp hdm C_u C_de k_u k_de hCu hCde
  refine ⟨K_L * C_f, k_f, min ν_u ν_de, mul_pos hKL hCf, lt_min hνu hνde, ?_⟩
  intro p d hreg hν hSg hmode
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  have hν_u : p.ν ≤ ν_u := hν.trans (min_le_left _ _)
  have hν_de : p.ν ≤ ν_de := hν.trans (min_le_right _ _)
  have hν1 : p.ν ≤ 1 := hν_u.trans hνu1
  obtain ⟨hp1, Hu_p⟩ := Hu p d hreg hν_u hSg hmode
  have Hde_p := Hde p d hreg hν_de hSg hmode
  have hcomb : ∀ z : p.Z,
      (∀ᵐ x ∂(phaseμ p.period), ‖rep (p.wOf z) x.1 x.2‖ ≤ C_u * (p.ν ^ k_u)⁻¹ * ‖z‖) ∧
      (∀ᵐ x ∂(phaseμ p.period), ‖p.uOf z x‖ ≤ C_u * (p.ν ^ k_u)⁻¹ * ‖z‖) ∧
      (∀ j : Fin 3, phaseLpNorm p.period bgp (dy j (p.eFun (p.coord z))) ≤
        ENNReal.ofReal (C_de * (p.ν ^ k_de)⁻¹ * ‖z‖)) :=
    fun z => ⟨(Hu_p z).1, (Hu_p z).2, Hde_p z⟩
  obtain ⟨⟨hadd_l, hsmul_l, hadd_r, hsmul_r⟩, Hfq⟩ :=
    Hleaf p d hreg hp1 hν1 hSg hmode hcomb
  refine quadBilinear_of_pointwise p (K_L * C_f * (p.ν ^ k_f)⁻¹) ?_
    hadd_l hsmul_l hadd_r hsmul_r
  intro z z'
  obtain ⟨g, hg_grad, hg_bd⟩ := wOf_exists_grad_bound p hp1 hν1 z
  obtain ⟨g', hg'_grad, hg'_bd⟩ := wOf_exists_grad_bound p hp1 hν1 z'
  obtain ⟨f, hf_real, hf_osym, hf_rep, hf_norm⟩ :=
    Hfq z z' g g' hg_grad hg'_grad hg_bd hg'_bd
  obtain ⟨b, hb_norm, hb_pair⟩ := HLeray p f hf_real hf_osym
  refine ⟨b, ?_, ?_⟩
  · intro Φ hΦ
    rw [hb_pair Φ hΦ, phasePair_eq_pairF_rep hΦ.1 f,
      pairF_rep_eq p.period f (quadFieldPtw p z z' g g') hf_rep Φ,
      ← quadFieldPtw_pairF lam q hq hreg hν1 hmode z z' g g' hg_grad hg'_grad
        (Hu_p z).1 (Hu_p z').1 Φ hΦ.1]
  · calc ‖b‖
        ≤ K_L * ‖f‖ := hb_norm
      _ ≤ K_L * (C_f * (p.ν ^ k_f)⁻¹ * ‖z‖ * ‖z'‖) :=
          mul_le_mul_of_nonneg_left hf_norm hKL.le
      _ = K_L * C_f * (p.ν ^ k_f)⁻¹ * ‖z‖ * ‖z'‖ := by ring

/-! ## 5. Proof of the packaging leaf and `QuadBound` -/

/-- Pointwise domination `|W| ≤ ∑ₖ (|Dₖu| |u'| + |u| |Dₖu'|)` of the quadratic convection field. -/
theorem norm_quadFieldPtw_le (p : Params) (z z' : p.Z) (g g' : Fin 3 → Yq p.period q0E)
    (x : ℝ × Space) :
    ‖quadFieldPtw p z z' g g' x‖ ≤ ∑ k : Fin 3,
      (‖GEQDu p z g k x‖ * ‖p.uOf z' x‖ + ‖p.uOf z x‖ * ‖GEQDu p z' g' k x‖) := by
  have hrepr : quadFieldPtw p z z' g g' x = ∑ k : Fin 3,
      (GEQDu p z g k x k • p.uOf z' x + p.uOf z x k • GEQDu p z' g' k x) := by
    ext i
    simp [quadFieldPtw_apply, WithLp.ofLp_sum, Finset.sum_apply]
  rw [hrepr]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le _ k) (norm_nonneg _)
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le _ k) (norm_nonneg _)

set_option maxHeartbeats 1000000 in
/-- **The packaging leaf `QuadFieldInYqSymm`** (SP 2503-2518): bilinearity of the convection
pairing and the real `𝒪`-invariant `Y_{q₀}` element `f` represented by `quadFieldPtw`, with
`‖f‖ ≤ 6 C_u (C_de + C_wgrad) ν^{-(k_u + max k_de 1)} ‖z‖ ‖z'‖`. -/
theorem quadFieldInYqSymm : QuadFieldInYqSymm := by
  intro Sig lam q hSig hq dm dp hdm C_u C_de k_u k_de hCu hCde
  have hCw := C_wgrad_pos
  refine ⟨6 * C_u * (C_de + C_wgrad), k_u + max k_de 1, by positivity, ?_⟩
  intro p d hreg hp1 hν1 hSg hmode hcomb
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  have hP : 0 < p.period := p.period_pos
  have hνpos : 0 < p.ν := p.ν_pos
  have heC : ∀ w : p.Z, ContDiff ℝ ∞ (p.eFun (p.coord w)) := fun w => by
    unfold Params.eFun
    refine UnforcedLeray.Short.PartIIIb.Concrete.contDiff_realC.comp ?_
    refine ContDiff.sum fun l _ => ?_
    exact (inlet_contDiff_joint lam q hq hreg hν1 hmode l).const_smul _
  have hsU : ∀ w : p.Z, AEStronglyMeasurable (p.uOf w) volume := fun w =>
    ((heC w).continuous.stronglyMeasurable.add
      (UnforcedLeray.Cons.C03.Concrete.stronglyMeasurable_rep (p.wOf w))).aestronglyMeasurable
  have hUb : ∀ w : p.Z, ∀ᵐ x ∂(QuadLeaf.cellμ p.period),
      ‖p.uOf w x‖ ≤ C_u * (p.ν ^ k_u)⁻¹ * ‖w‖ := fun w => (hcomb w).2.1
  have hInt : ∀ (w w' : p.Z) (Φ : ℝ × Space → CVec3), IsPhaseTest p.period Φ →
      Integrable (fun x => dotL (advT (p.uOf w) Φ x) (p.uOf w' x)) (QuadLeaf.cellμ p.period) :=
    fun w w' Φ hΦ => QuadLeaf.integrable_advT_pair hΦ
      ((hsU w).mono_ac (QuadLeaf.cellμ_ac _)) ((hsU w').mono_ac (QuadLeaf.cellμ_ac _))
      (hUb w) (hUb w')
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro z₁ z₂ z' Φ hΦ
    exact QuadLeaf.pairF_advT_add_left Φ (QuadLeaf.uOf_add_ae p z₁ z₂) (hInt z₁ z' Φ hΦ.1)
      (hInt z₂ z' Φ hΦ.1)
  · intro a z z' Φ _
    exact QuadLeaf.pairF_advT_smul_left p.period Φ a (QuadLeaf.uOf_smul_ae p a z)
  · intro z z₁' z₂' Φ hΦ
    exact QuadLeaf.pairF_advT_add_right Φ (QuadLeaf.uOf_add_ae p z₁' z₂') (hInt z z₁' Φ hΦ.1)
      (hInt z z₂' Φ hΦ.1)
  · intro a z z' Φ _
    exact QuadLeaf.pairF_advT_smul_right p.period Φ a (QuadLeaf.uOf_smul_ae p a z')
  intro z z' g g' hg hg' hgb hg'b
  have hWm : AEStronglyMeasurable (quadFieldPtw p z z' g g') volume :=
    (stronglyMeasurable_quadFieldPtw lam q hq hreg hν1 hmode z z' g g').aestronglyMeasurable
  have hDm : ∀ (w : p.Z) (gw : Fin 3 → Yq p.period q0E) (k : Fin 3),
      AEStronglyMeasurable (GEQDu p w gw k) volume := fun w gw k =>
    ((dy_contDiff' (heC w) k).continuous.stronglyMeasurable.add
      (UnforcedLeray.Cons.C03.Concrete.stronglyMeasurable_rep (gw k))).aestronglyMeasurable
  -- `Y_p` bounds of `Dₖu = ∂ₖe + gₖ`
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = C_de * (p.ν ^ k_de)⁻¹ + C_wgrad * (p.ν ^ 1)⁻¹ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hDb : ∀ (w : p.Z) (gw : Fin 3 → Yq p.period q0E),
      (∀ j : Fin 3, ‖gw j‖ ≤ C_wgrad * (p.ν ^ 1)⁻¹ * ‖w‖) → ∀ k : Fin 3,
      phaseLpNorm p.period bgp (GEQDu p w gw k) ≤ ENNReal.ofReal (A * ‖w‖) := by
    intro w gw hgw k
    have h1 := QuadLeaf.phaseLpNorm_add_le' p.period
      ((dy_contDiff' (heC w) k).continuous.aestronglyMeasurable)
      ((UnforcedLeray.Cons.C03.Concrete.stronglyMeasurable_rep (gw k)).aestronglyMeasurable)
    have h2 : phaseLpNorm p.period bgp (dy k (p.eFun (p.coord w))) ≤
        ENNReal.ofReal (C_de * (p.ν ^ k_de)⁻¹ * ‖w‖) := (hcomb w).2.2 k
    have h3 : phaseLpNorm p.period bgp (fun x : ℝ × Space => rep (gw k) x.1 x.2) ≤
        ENNReal.ofReal (C_wgrad * (p.ν ^ 1)⁻¹ * ‖w‖) := by
      rw [phaseLpNorm_rep_eq p.period (gw k)]
      exact ENNReal.ofReal_le_ofReal (hgw k)
    have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
    calc phaseLpNorm p.period bgp (GEQDu p w gw k)
        ≤ phaseLpNorm p.period bgp (dy k (p.eFun (p.coord w))) +
            phaseLpNorm p.period bgp (fun x : ℝ × Space => rep (gw k) x.1 x.2) := h1
      _ ≤ ENNReal.ofReal (C_de * (p.ν ^ k_de)⁻¹ * ‖w‖) +
            ENNReal.ofReal (C_wgrad * (p.ν ^ 1)⁻¹ * ‖w‖) := add_le_add h2 h3
      _ = ENNReal.ofReal (A * ‖w‖) := by
          have hcd : 0 ≤ C_de * (p.ν ^ k_de)⁻¹ := by positivity
          have hcw : 0 ≤ C_wgrad * (p.ν ^ 1)⁻¹ := by positivity
          rw [← ENNReal.ofReal_add (mul_nonneg hcd hw0) (mul_nonneg hcw hw0), hAdef]
          congr 1
          ring
  -- `Y_p` bound of `W`
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = C_u * (p.ν ^ k_u)⁻¹ * ‖z‖ := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = C_u * (p.ν ^ k_u)⁻¹ * ‖z'‖ := ⟨_, rfl⟩
  have hCν : 0 ≤ C_u * (p.ν ^ k_u)⁻¹ := by positivity
  have hM0 : 0 ≤ M := hMdef ▸ mul_nonneg hCν (norm_nonneg z)
  have hN0 : 0 ≤ N := hNdef ▸ mul_nonneg hCν (norm_nonneg z')
  have hWb := QuadLeaf.phaseLpNorm_bilin_le p.period hWm (hDm z g) (hDm z' g') hM0 hN0
    (hMdef ▸ hUb z) (hNdef ▸ hUb z') (norm_quadFieldPtw_le p z z' g g')
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = 6 * C_u * (p.ν ^ k_u)⁻¹ * A * ‖z‖ * ‖z'‖ := ⟨_, rfl⟩
  have h6 : 0 ≤ 6 * C_u * (p.ν ^ k_u)⁻¹ := by positivity
  have hX0 : 0 ≤ X := hXdef ▸ mul_nonneg (mul_nonneg (mul_nonneg h6 hA0) (norm_nonneg _))
    (norm_nonneg _)
  have hWX : phaseLpNorm p.period bgp (quadFieldPtw p z z' g g') ≤ ENNReal.ofReal X := by
    refine hWb.trans ?_
    calc ∑ k : Fin 3, (ENNReal.ofReal N * phaseLpNorm p.period bgp (GEQDu p z g k) +
          ENNReal.ofReal M * phaseLpNorm p.period bgp (GEQDu p z' g' k))
        ≤ ∑ k : Fin 3, (ENNReal.ofReal N * ENNReal.ofReal (A * ‖z‖) +
          ENNReal.ofReal M * ENNReal.ofReal (A * ‖z'‖)) := by
          refine Finset.sum_le_sum fun k _ => add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left (hDb z g hgb k) (by positivity)
          · exact mul_le_mul_of_nonneg_left (hDb z' g' hg'b k) (by positivity)
      _ = ENNReal.ofReal (∑ k : Fin 3, (N * (A * ‖z‖) + M * (A * ‖z'‖))) := by
          have hterm : 0 ≤ N * (A * ‖z‖) + M * (A * ‖z'‖) :=
            add_nonneg (mul_nonneg hN0 (mul_nonneg hA0 (norm_nonneg _)))
              (mul_nonneg hM0 (mul_nonneg hA0 (norm_nonneg _)))
          rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => hterm)]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [ENNReal.ofReal_add (mul_nonneg hN0 (mul_nonneg hA0 (norm_nonneg _)))
            (mul_nonneg hM0 (mul_nonneg hA0 (norm_nonneg _))), ENNReal.ofReal_mul hN0,
            ENNReal.ofReal_mul hM0]
      _ = ENNReal.ofReal X := by
          congr 1
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [hXdef, hMdef, hNdef]
          push_cast
          ring
  have hWY : IsInYr p.period bgp (quadFieldPtw p z z' g g') :=
    ⟨Eventually.of_forall fun x => quadFieldPtw_periodic p z z' g g' x, hWm,
      lt_of_le_of_lt hWX ENNReal.ofReal_lt_top⟩
  obtain ⟨f, hfrep, hfnorm⟩ := yqOfFields p.period (quadFieldPtw p z z' g g') hWY
  -- realness: `u`, `u'`, `Du`, `Du'` are a.e. real
  have hreal : ∀ᵐ x ∂(volume : Measure (ℝ × Space)), ∀ i : Fin 3, (quadFieldPtw p z z' g g' x i).im = 0 := by
    have hgR : ∀ k, g k ∈ realSub p.period q0E :=
      QuadLeaf.grad_mem_realSub (QuadLeaf.wOf_mem p z).1 hg
    have hg'R : ∀ k, g' k ∈ realSub p.period q0E :=
      QuadLeaf.grad_mem_realSub (QuadLeaf.wOf_mem p z').1 hg'
    have hdyR : ∀ (w : p.Z) (k : Fin 3) (x : ℝ × Space) (i : Fin 3),
        (dy k (p.eFun (p.coord w)) x i).im = 0 := by
      intro w k x i
      have hφ : Differentiable ℝ
          (fun x : ℝ × Space => ∑ l : Fin 2, p.coord w l • p.inlet l x.1 x.2) :=
        (ContDiff.sum fun l _ =>
          (inlet_contDiff_joint lam q hq hreg hν1 hmode l).const_smul _).differentiable (by simp)
      have heq : p.eFun (p.coord w) =
          fun x => realC (∑ l : Fin 2, p.coord w l • p.inlet l x.1 x.2) := rfl
      rw [heq, QuadLeaf.dy_realC hφ k]
      simp [realC_apply]
    filter_upwards [QuadLeaf.uOf_im_zero_ae p z, QuadLeaf.uOf_im_zero_ae p z',
      ae_all_iff.2 fun k => QuadLeaf.rep_im_zero_ae (hgR k),
      ae_all_iff.2 fun k => QuadLeaf.rep_im_zero_ae (hg'R k)] with x hu hu' hgk hg'k i
    have hD : ∀ k j, (GEQDu p z g k x j).im = 0 := fun k j => by
      simp only [GEQDu, PiLp.add_apply, Complex.add_im, hdyR, hgk k j, add_zero]
    have hD' : ∀ k j, (GEQDu p z' g' k x j).im = 0 := fun k j => by
      simp only [GEQDu, PiLp.add_apply, Complex.add_im, hdyR, hg'k k j, add_zero]
    simp only [quadFieldPtw_apply, Complex.im_sum, Complex.add_im, Complex.mul_im, hD, hD',
      hu, hu', mul_zero, zero_mul, add_zero, Finset.sum_const_zero]
  have hfR : f ∈ realSub p.period q0E := QuadLeaf.mem_realSub_of_ae hfrep hreal
  -- `𝒪`-symmetry from the pairing identity
  have hpair : ∀ Φ, IsPhaseTest p.period Φ →
      pairF p.period Φ (quadFieldPtw p z z' g g') = -pairF p.period (advT (p.uOf z) Φ) (p.uOf z') := fun Φ hΦ =>
    (quadFieldPtw_pairF lam q hq hreg hν1 hmode z z' g g' hg hg' (hcomb z).1 (hcomb z').1
      Φ hΦ).symm
  have hfO : f ∈ Osym p.period q0E := QuadLeaf.mem_Osym_of_ae hfrep fun γ hγ =>
    QuadLeaf.ae_gAct_of_pair hP hWY hpair (QuadLeaf.gAct_uOf_ae p z hγ)
      (QuadLeaf.gAct_uOf_ae p z' hγ)
  refine ⟨f, hfR, hfO, hfrep, ?_⟩
  -- the norm
  rw [hfnorm]
  refine (ENNReal.toReal_le_of_le_ofReal hX0 hWX).trans ?_
  have hk1 : (p.ν ^ k_de)⁻¹ ≤ (p.ν ^ max k_de 1)⁻¹ :=
    S1Sub.s1_inv_pow_mono_of_le_one p.ν_pos hν1 (le_max_left _ _)
  have hk2 : (p.ν ^ 1)⁻¹ ≤ (p.ν ^ max k_de 1)⁻¹ :=
    S1Sub.s1_inv_pow_mono_of_le_one p.ν_pos hν1 (le_max_right _ _)
  have hAle : A ≤ (C_de + C_wgrad) * (p.ν ^ max k_de 1)⁻¹ := by
    rw [hAdef]
    nlinarith [mul_le_mul_of_nonneg_left hk1 hCde.le, mul_le_mul_of_nonneg_left hk2 hCw.le]
  have hpow : (p.ν ^ (k_u + max k_de 1))⁻¹ = (p.ν ^ k_u)⁻¹ * (p.ν ^ max k_de 1)⁻¹ := by
    rw [pow_add, mul_inv]
  calc X = 6 * C_u * (p.ν ^ k_u)⁻¹ * A * ‖z‖ * ‖z'‖ := hXdef
    _ ≤ 6 * C_u * (p.ν ^ k_u)⁻¹ * ((C_de + C_wgrad) * (p.ν ^ max k_de 1)⁻¹) * ‖z‖ * ‖z'‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hAle h6) (norm_nonneg _)) (norm_nonneg _)
    _ = 6 * C_u * (C_de + C_wgrad) * (p.ν ^ (k_u + max k_de 1))⁻¹ * ‖z‖ * ‖z'‖ := by
        rw [hpow]
        ring

/-- **`PartII-b:Q1` (`QuadBound`, SP 2503-2518)**: the polarized quadratic estimate, from
`h4 : AffineInletFacts`. -/
theorem quadBound_of (h4 : UnforcedLeray.Short.IIb.AffineInletFacts) :
    UnforcedLeray.Short.IIb.QuadBound :=
  quadBound_of_leaf quadFieldInYqSymm h4

end UnforcedLeray.Short.IIb
