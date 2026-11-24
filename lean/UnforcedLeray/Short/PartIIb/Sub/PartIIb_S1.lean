import UnforcedLeray.Short.PartIIb.Sub.ComparisonAndStrongDesign
import UnforcedLeray.Short.PartIIa.Tasks.F11SupEmbedding
import UnforcedLeray.Cons.L2.BackgroundConcrete.GraphStateL4

/-!
# `PartII-b:S1` decomposition (`Sub/PartII-b_S1.lean`, SP 2525-2541)

Source of record: `the November 2 reference manuscript`
(SP), lines 2525-2541 (display `short-bg:strong` at 2538-2541).

## Proved here (zero `sorry`)

1. `S1Sub.contRep_eq_globalRealChartRep` and `S1Sub.exists_contRep_sup_bound`: for any
   `u ∈ D_p = B0411.D P ν q0E` (`0 < P ≤ 1`, `0 < ν ≤ 1`), the continuous representative
   `contRep (u : Yq P q0E)` agrees everywhere with `B0449.globalRealChartRep` and satisfies the
   quantitative supremum bound
   `‖contRep (u : Yq P q0E) τ y‖ ≤ C_sup * (ν ^ 1)⁻¹ * B0411.graphNormD u` from
   `exists_globalChartRep_bound_explicit chartCutoffExplicit` (`PartII-a:F11`, SP 1524-1531).
2. `S1Sub.corr_eLpNorm_bgp_le_of_period_le_one`: for any `z : p.Z` (`p.period ≤ 1`),
   `eLpNorm (p.corr z τ) (ENNReal.ofReal bgp) volume ≤ ENNReal.ofReal ‖z‖` at every phase `τ`
   from `PhaseTrace.norm_phaseRep_le` (`PartII-a:F10`, SP 1517-1523).
3. `S1Sub.inlet_w1_le_of_affineInletFacts`: from `h4 : AffineInletFacts` (`InletSupBound` at
   `j = 0, 1`, SP after 2383) and `‖p.coord z‖ ≤ ‖z‖` (`coord z = ε^{8/11} A`, `ε ≤ 1`), both
   `‖∑ i : Fin 2, p.coord z i • p.inlet i τ y‖` and
   `‖fderiv ℝ (fun y' => ∑ i : Fin 2, p.coord z i • p.inlet i τ y') y‖` are bounded by
   `C_in * (p.ν ^ k_in)⁻¹ * ‖z‖`.
4. `strongFirstDerivative_of_parts`: conditional assembly of `StrongFirstDerivative` from
   `h4 : AffineInletFacts`, `hQ1 : QuadBound`, and the two leaves:
   * `DifferentiatedEquationGraphBound` (`PartII-b:S1/1`, SP 2525-2537): for any solution `z` of
     `ProjectedEquation p z` in the contraction ball (`2m < 3d₋/11`), the distributional spatial
     derivatives `∂_j w` lie in `B0411.D p.period p.ν q0E` with
     `B0411.graphNormD (g j) ≤ C_g * (p.ν ^ k_g)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)`;
   * `ContRepFDerivLeSumGrad` (`PartII-b:S1/2`, SP 2537-2541): for `u : B0411.D P ν q0E`
     (`P ≤ 1`, `ν > 0`) with distributional spatial derivatives `g j : B0411.D P ν q0E`,
     `‖fderiv ℝ (contRep (u : Yq P q0E) τ) y‖ ≤ ∑ j : Fin 3, ‖contRep (g j : Yq P q0E) τ y‖`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
  UnforcedLeray.PhaseTrace UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.B0449
  UnforcedLeray.Blueprint

namespace S1Sub

local instance fact_q0_ge_one_s1 : Fact (1 ≤ ENNReal.ofReal B0281.q0) :=
  inferInstanceAs (Fact (1 ≤ q0E))

theorem s1_q0_holder : B0281.q0.HolderConjugate (11 / 7 : ℝ) := by
  rw [B0281.q0_eq]
  exact B0276.holderConjugate

theorem s1_q0_gt : 5 / 2 < B0281.q0 := by
  norm_num [B0281.q0]

theorem s1_bgp_eq_q0 : bgp = B0281.q0 := by
  rw [B0281.q0_eq]
  rfl

theorem s1_ofReal_bgp_eq_q0E : ENNReal.ofReal bgp = q0E := by
  rw [s1_bgp_eq_q0]
  rfl

theorem s1_inv_pow_mono_of_le_one {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) {j k : ℕ}
    (hjk : j ≤ k) : (ν ^ j)⁻¹ ≤ (ν ^ k)⁻¹ := by
  rw [inv_le_inv₀ (pow_pos hν0 j) (pow_pos hν0 k)]
  exact pow_le_pow_of_le_one hν0.le hν1 hjk

/-! ## 1. Quantitative supremum and `L^p` trace bounds on `D_p` and `p.corr z` -/

/-- For any `u : B0411.D P ν q0E` (`P ≤ 1`, `ν > 0`), the selected continuous representative
`contRep (u : Yq P q0E)` agrees everywhere with `B0449.globalRealChartRep`. -/
theorem contRep_eq_globalRealChartRep {P : ℝ} [Fact (0 < P)] (hP1 : P ≤ 1) {ν : ℝ} (hν : 0 < ν)
    (u : B0411.D P ν q0E) (τ : ℝ) (y : Space) :
    contRep (u : Yq P q0E) τ y =
      globalRealChartRep hP1 s1_q0_holder s1_q0_gt hν (hasPhaseOp_T0D u) (hasPhaseOp_nuLapD u)
        τ y := by
  let hTime := hasPhaseOp_T0D u
  let hLap := hasPhaseOp_nuLapD u
  let F : ℝ → SpatialField := globalRealChartRep hP1 s1_q0_holder s1_q0_gt hν hTime hLap
  have hF : IsContRep (u : Yq P q0E) F :=
    graph_globalRealChartRep_isContRep hP1 s1_q0_holder s1_q0_gt hν hTime hLap
  have hcont : IsContRep (u : Yq P q0E) (contRep (u : Yq P q0E)) :=
    contRep_spec ⟨F, hF⟩
  have hEq : (fun x : ℝ × Space => contRep (u : Yq P q0E) x.1 x.2) =
      fun x => F x.1 x.2 :=
    (Continuous.ae_eq_iff_eq volume hcont.1 hF.1).mp (hcont.2.trans hF.2.symm)
  exact congrFun hEq (τ, y)

/-- Euclidean norm of a real 3-vector is at most the sum of its coordinate absolute values. -/
theorem norm_space_le_sum (v : Space) : ‖v‖ ≤ |v 0| + |v 1| + |v 2| := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  simp only [Fin.sum_univ_three, Real.norm_eq_abs]
  nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), abs_nonneg (v 2)]

theorem s1_graphNormD_nonneg {P ν : ℝ} [Fact (0 < P)] (u : B0411.D P ν q0E) :
    0 ≤ B0411.graphNormD u := by
  unfold B0411.graphNormD
  positivity

/-- Quantitative supremum bound on `contRep (u : Yq P q0E)` for any `u : B0411.D P ν q0E`
(`0 < P ≤ 1`, `0 < ν ≤ 1`), derived from `exists_globalChartRep_bound_explicit` and
`chartCutoffExplicit` (`PartII-a:F11`, SP 1524-1531). -/
theorem exists_contRep_sup_bound :
    ∃ C_sup : ℝ, 0 < C_sup ∧ ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ν ≤ 1 →
      ∀ (u : B0411.D P ν q0E) (τ : ℝ) (y : Space),
        ‖contRep (u : Yq P q0E) τ y‖ ≤ C_sup * (ν ^ 1)⁻¹ * B0411.graphNormD u := by
  obtain ⟨K, hK0, hKb⟩ := Short.PartIIa.exists_globalChartRep_bound_explicit
    Short.PartIIa.chartCutoffExplicit s1_q0_holder s1_q0_gt
  refine ⟨3 * K + 1, by positivity, ?_⟩
  intro P _ hP1 ν hν hν1 u τ y
  rw [contRep_eq_globalRealChartRep hP1 hν u τ y]
  let hTime := hasPhaseOp_T0D u
  let hLap := hasPhaseOp_nuLapD u
  have hcoord : ∀ i : Fin 3,
      |(globalRealChartRep hP1 s1_q0_holder s1_q0_gt hν hTime hLap τ y) i| ≤
        K * ν ^ (-(3 / (2 * B0281.q0))) * B0411.graphNormD u := by
    intro i
    have hre : |(globalRealChartRep hP1 s1_q0_holder s1_q0_gt hν hTime hLap τ y) i| ≤
        ‖globalChartRep hP1 s1_q0_holder s1_q0_gt hν hTime hLap (complexCoordinate i) τ y‖ := by
      exact Complex.abs_re_le_norm _
    have hbi := hKb P hP1 ν hν (u : Yq P q0E) (nuLapD u) (T0D u) hTime hLap
      (complexCoordinate i) τ y
    have hdot : ‖dotL (complexCoordinate i)‖ ≤ 1 := Short.PartIIa.supEmb_norm_dotL_cc_le i
    have hbi' : ‖globalChartRep hP1 s1_q0_holder s1_q0_gt hν hTime hLap
          (complexCoordinate i) τ y‖ ≤
        K * ‖dotL (complexCoordinate i)‖ * ν ^ (-(3 / (2 * B0281.q0))) *
          B0411.graphNormD u := by
      unfold B0411.graphNormD q0E
      linarith [hbi]
    have hle1 : K * ‖dotL (complexCoordinate i)‖ * ν ^ (-(3 / (2 * B0281.q0))) *
          B0411.graphNormD u ≤
        K * 1 * ν ^ (-(3 / (2 * B0281.q0))) * B0411.graphNormD u := by
      have hgn0 : 0 ≤ B0411.graphNormD u := s1_graphNormD_nonneg u
      have hrp0 : 0 ≤ ν ^ (-(3 / (2 * B0281.q0))) := Real.rpow_nonneg hν.le _
      gcongr
    rw [mul_one] at hle1
    exact hre.trans (hbi'.trans hle1)
  have hν_rpow : ν ^ (-(3 / (2 * B0281.q0))) ≤ (ν ^ 1)⁻¹ := by
    have hexp : -(1 : ℝ) ≤ -(3 / (2 * B0281.q0)) := by
      rw [B0281.q0_eq]
      norm_num
    calc ν ^ (-(3 / (2 * B0281.q0))) ≤ ν ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hν hν1 hexp
      _ = (ν ^ 1)⁻¹ := by rw [Real.rpow_neg_one, pow_one]
  have hgn0 : 0 ≤ B0411.graphNormD u := s1_graphNormD_nonneg u
  have hsum := (norm_space_le_sum
    (globalRealChartRep hP1 s1_q0_holder s1_q0_gt hν hTime hLap τ y)).trans
    (add_le_add (add_le_add (hcoord 0) (hcoord 1)) (hcoord 2))
  calc ‖globalRealChartRep hP1 s1_q0_holder s1_q0_gt hν hTime hLap τ y‖
      ≤ 3 * (K * ν ^ (-(3 / (2 * B0281.q0))) * B0411.graphNormD u) := by linarith
    _ = 3 * K * ν ^ (-(3 / (2 * B0281.q0))) * B0411.graphNormD u := by ring
    _ ≤ (3 * K + 1) * (ν ^ 1)⁻¹ * B0411.graphNormD u := by
        have : 3 * K ≤ 3 * K + 1 := by linarith
        gcongr

/-- The graph norm of the first component `p.wOf z` of `z : p.Z` is at most `‖z‖`. -/
theorem graphNormD_graphX_le_norm (p : Params) (z : p.Z) :
    B0411.graphNormD (B0412.XToD (p.graphX z)) ≤ ‖z‖ := by
  have heq := norm_eq_normX_add (P := p.period) (ν := p.ν) z
  have hX : (⟨cw p.period z, cw_mem_X z⟩ : X p.period p.ν q0E) = p.graphX z := rfl
  rw [hX, B0412.normX_eq_graphNormD] at heq
  linarith [norm_nonneg (cA p.period (z : Amb p.period))]

/-- Pointwise norm of `realPartVector v` is at most `‖v‖`. -/
theorem norm_realPartVector_le (v : CVec3) : ‖realPartVector v‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Real.norm_eq_abs]
  change |(v i).re| ^ 2 ≤ ‖v i‖ ^ 2
  exact sq_le_sq.mpr (by simpa using Complex.abs_re_le_norm (v i))

/-- Phasewise `L^{bgp}(ℝ³)` bound on `p.corr z τ` for `p.period ≤ 1` (`PartII-a:F10`, SP 1517-1523):
`eLpNorm (p.corr z τ) (ENNReal.ofReal bgp) volume ≤ ENNReal.ofReal ‖z‖`. -/
theorem corr_eLpNorm_bgp_le_of_period_le_one (p : Params) (hP1 : p.period ≤ 1) (z : p.Z)
    (τ : ℝ) :
    eLpNorm (p.corr z τ) (ENNReal.ofReal bgp) volume ≤ ENNReal.ofReal ‖z‖ := by
  rw [s1_ofReal_bgp_eq_q0E]
  let u : B0411.D p.period p.ν q0E := B0412.XToD (p.graphX z)
  let hTime := hasPhaseOp_T0D u
  let hLap := hasPhaseOp_nuLapD u
  have hcorr_eq : p.corr z τ =
      globalRealChartRep hP1 s1_q0_holder s1_q0_gt p.ν_pos hTime hLap τ := by
    funext y
    exact (contRep_eq_globalRealChartRep hP1 p.ν_pos u τ y)
  have hae := globalRealChartRep_ae_phaseRepC hP1 s1_q0_holder s1_q0_gt p.ν_pos hTime hLap τ
  have hqtop : q0E ≠ ⊤ := ENNReal.ofReal_ne_top
  let Wτ : Lp CVec3 q0E (volume : Measure Space) :=
    phaseRepC (q := q0E) hqtop hTime (τ : AddCircle p.period)
  have hptw : ∀ᵐ y ∂(volume : Measure Space), ‖p.corr z τ y‖ ≤ ‖(Wτ : Space → CVec3) y‖ := by
    rw [hcorr_eq]
    filter_upwards [hae] with y hy
    rw [hy]
    exact norm_realPartVector_le _
  have hmono : eLpNorm (p.corr z τ) q0E volume ≤ eLpNorm Wτ q0E volume :=
    eLpNorm_mono_ae hptw
  have hWnorm : eLpNorm Wτ q0E volume = ENNReal.ofReal ‖Wτ‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top Wτ)]
  have htrace : ‖Wτ‖ ≤ B0411.graphNormD u := by
    dsimp [Wτ]
    rw [phaseRepC_coe hqtop hTime τ]
    have hb := norm_phaseRep_le hqtop hTime τ
    have hP0 : 0 ≤ p.period := p.period_pos.le
    have hT0 : 0 ≤ ‖T0D u‖ := norm_nonneg _
    have hPT : p.period * ‖T0D u‖ ≤ 1 * ‖T0D u‖ := mul_le_mul_of_nonneg_right hP1 hT0
    have hnu : 0 ≤ ‖nuLapD u‖ := norm_nonneg _
    unfold B0411.graphNormD
    linarith
  exact hmono.trans (hWnorm.trans_le (ENNReal.ofReal_le_ofReal
    (htrace.trans (graphNormD_graphX_le_norm p z))))

/-! ## 2. Affine inlet `W^{1,∞}` bound from `h4 : AffineInletFacts` -/

/-- The scaled inlet coordinate vector `p.coord z` as an element of `E2 = EuclideanSpace ℝ (Fin 2)`
has norm at most `‖z‖` whenever `p.ε ≤ 1`. -/
theorem norm_coord_le_norm (p : Params) (hε1 : p.ε ≤ 1) (z : p.Z) :
    ‖(WithLp.toLp 2 (p.coord z) : E2)‖ ≤ ‖z‖ := by
  have hε0 : 0 ≤ p.ε := p.ε_pos.le
  have hsmul : (WithLp.toLp 2 (p.coord z) : E2) =
      p.ε ^ (8 / 11 : ℝ) • cA p.period (z : Amb p.period) := by
    ext i
    simp [Params.coord]
  rw [hsmul, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hε0 _)]
  have hrpow1 : p.ε ^ (8 / 11 : ℝ) ≤ 1 := Real.rpow_le_one hε0 hε1 (by norm_num)
  have hcA : ‖cA p.period (z : Amb p.period)‖ ≤ ‖z‖ := by
    have heq := norm_eq_normX_add (P := p.period) (ν := p.ν) z
    have hX0 : 0 ≤ B0412.normX (⟨cw p.period z, cw_mem_X z⟩ : X p.period p.ν q0E) := by
      rw [B0412.normX_eq_graphNormD]
      exact s1_graphNormD_nonneg _
    linarith
  calc p.ε ^ (8 / 11 : ℝ) * ‖cA p.period (z : Amb p.period)‖
      ≤ 1 * ‖cA p.period (z : Amb p.period)‖ :=
        mul_le_mul_of_nonneg_right hrpow1 (norm_nonneg _)
    _ = ‖cA p.period (z : Amb p.period)‖ := one_mul _
    _ ≤ ‖z‖ := hcA

/-- From `h4 : AffineInletFacts` (`InletSupBound` at `j = 0, 1`), the affine inlet
`∑ i : Fin 2, p.coord z i • p.inlet i τ` and its spatial Fréchet derivative are bounded by
`C_in * (p.ν ^ k_in)⁻¹ * ‖z‖`. -/
theorem inlet_w1_le_of_affineInletFacts (h4 : AffineInletFacts)
    (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile) (hSig : 0 < Sig)
    (hq : Blueprint.Planar.IsGrowingEigenpair lam q) (dm dp : ℝ) (hdm : 0 < dm) :
    ∃ (C_in : ℝ) (k_in : ℕ) (ν_in : ℝ), 0 < C_in ∧ 0 < ν_in ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν_in → p.ageCut = Sig → p.mode = q →
        ∀ (z : p.Z) (τ : ℝ) (y : Space),
          ‖∑ i : Fin 2, p.coord z i • p.inlet i τ y‖ ≤ C_in * (p.ν ^ k_in)⁻¹ * ‖z‖ ∧
          ‖fderiv ℝ (fun y' => ∑ i : Fin 2, p.coord z i • p.inlet i τ y') y‖ ≤
            C_in * (p.ν ^ k_in)⁻¹ * ‖z‖ := by
  obtain ⟨C₀, k₀, ν₀, hC₀, hν₀, H0⟩ := h4.2.2 Sig lam q hSig hq dm dp hdm 0
  obtain ⟨C₁, k₁, ν₁, hC₁, hν₁, H1⟩ := h4.2.2 Sig lam q hSig hq dm dp hdm 1
  refine ⟨C₀ + C₁, max k₀ k₁, min (min ν₀ ν₁) 1, by positivity,
    lt_min (lt_min hν₀ hν₁) zero_lt_one, ?_⟩
  intro p d hreg hν hSg hmode z τ y
  have hν0 : p.ν ≤ ν₀ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν1 : p.ν ≤ ν₁ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_le1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hε1 : p.ε ≤ 1 := by
    rw [hreg.eps_eq]
    apply Real.exp_le_one_iff.mpr
    have hd0 : 0 < d := lt_of_lt_of_le hdm hreg.dm_le
    have hνp : 0 < p.ν := p.ν_pos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hνp.le
  let α : E2 := WithLp.toLp 2 (p.coord z)
  have hα : ‖α‖ ≤ ‖z‖ := norm_coord_le_norm p hε1 z
  have hb0 := H0 p d hreg hν0 hSg hmode α τ y
  have hb1 := H1 p d hreg hν1 hSg hmode α τ y
  rw [norm_iteratedFDeriv_zero] at hb0
  rw [norm_iteratedFDeriv_one] at hb1
  have hk0 : (p.ν ^ k₀)⁻¹ ≤ (p.ν ^ max k₀ k₁)⁻¹ :=
    s1_inv_pow_mono_of_le_one p.ν_pos hν_le1 (le_max_left k₀ k₁)
  have hk1 : (p.ν ^ k₁)⁻¹ ≤ (p.ν ^ max k₀ k₁)⁻¹ :=
    s1_inv_pow_mono_of_le_one p.ν_pos hν_le1 (le_max_right k₀ k₁)
  have hνk0 : 0 ≤ (p.ν ^ k₀)⁻¹ := by have := p.ν_pos; positivity
  have hνk1 : 0 ≤ (p.ν ^ k₁)⁻¹ := by have := p.ν_pos; positivity
  have hC01 : 0 ≤ (C₀ + C₁) * (p.ν ^ max k₀ k₁)⁻¹ := by have := p.ν_pos; positivity
  constructor
  · calc ‖∑ i : Fin 2, p.coord z i • p.inlet i τ y‖
        ≤ C₀ * (p.ν ^ k₀)⁻¹ * ‖α‖ := hb0
      _ ≤ (C₀ + C₁) * (p.ν ^ max k₀ k₁)⁻¹ * ‖z‖ := by
          have : C₀ ≤ C₀ + C₁ := by linarith
          gcongr
  · calc ‖fderiv ℝ (fun y' => ∑ i : Fin 2, p.coord z i • p.inlet i τ y') y‖
        ≤ C₁ * (p.ν ^ k₁)⁻¹ * ‖α‖ := hb1
      _ ≤ (C₀ + C₁) * (p.ν ^ max k₀ k₁)⁻¹ * ‖z‖ := by
          have : C₁ ≤ C₀ + C₁ := by linarith
          gcongr

end S1Sub

open S1Sub

/-! ## 3. Decomposition leaves (`PartII-b:S1/1`, `PartII-b:S1/2`) and conditional assembly -/

/-- **`PartII-b:S1/1` (`DifferentiatedEquationGraphBound`)**
(`the November 2 reference manuscript`,
lines 2525-2537): at fixed slow data `(Σ, λ, q)` and `0 < m` with `2m < 3d₋/11`, using
`h4 : AffineInletFacts` and `hQ1 : QuadBound`, for any solution `z = (w, A)` of
`ProjectedEquation p z` in the contraction ball of radius `C₁ ν^{-k₁} e^{m/ν} ε^{3/11}`, the
distributional spatial derivatives `∂_j w` lie in `B0411.D p.period p.ν q0E` with
`B0411.graphNormD (g j) ≤ C₂ ν^{-k₂} e^{m/ν} ε^{3/11}`. -/
def DifferentiatedEquationGraphBound : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 → ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ (C₂ : ℝ) (k₂ : ℕ) (ν₀ : ℝ), 0 < C₂ ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ z : p.Z, ProjectedEquation p z →
      ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) →
      ∃ g : Fin 3 → B0411.D p.period p.ν q0E,
        (∀ j : Fin 3, HasPhaseOp (fun Φ => -dy j Φ) (p.wOf z) (g j : Yq p.period q0E)) ∧
        (∀ j : Fin 3, B0411.graphNormD (g j) ≤
          C₂ * (p.ν ^ k₂)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ))

/-- **`PartII-b:S1/2` (`ContRepFDerivLeSumGrad`)**
(`the November 2 reference manuscript`,
lines 2537-2541): for `0 < P ≤ 1`, `ν > 0`, `u : B0411.D P ν q0E` and
`g : Fin 3 → B0411.D P ν q0E` with `HasPhaseOp (fun Φ => -dy j Φ) (u : Yq P q0E) (g j : Yq P q0E)`
for all `j : Fin 3`, at every `(τ, y) ∈ ℝ × ℝ³`,
`‖fderiv ℝ (contRep (u : Yq P q0E) τ) y‖ ≤ ∑ j : Fin 3, ‖contRep (g j : Yq P q0E) τ y‖`. -/
def ContRepFDerivLeSumGrad : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν →
    ∀ (u : B0411.D P ν q0E) (g : Fin 3 → B0411.D P ν q0E),
      (∀ j : Fin 3, HasPhaseOp (fun Φ => -dy j Φ) (u : Yq P q0E) (g j : Yq P q0E)) →
      ∀ (τ : ℝ) (y : Space),
        ‖fderiv ℝ (contRep (u : Yq P q0E) τ) y‖ ≤
          ∑ j : Fin 3, ‖contRep (g j : Yq P q0E) τ y‖

/-- **Conditional assembly of `StrongFirstDerivative` (`PartII-b:S1`, SP 2525-2541)** from
`DifferentiatedEquationGraphBound` (`PartII-b:S1/1`), `ContRepFDerivLeSumGrad` (`PartII-b:S1/2`),
`h4 : AffineInletFacts`, and `hQ1 : QuadBound`. -/
theorem strongFirstDerivative_of_parts
    (hGrad : DifferentiatedEquationGraphBound)
    (hFDeriv : ContRepFDerivLeSumGrad)
    (h4 : AffineInletFacts)
    (_hQ1 : QuadBound) :
    StrongFirstDerivative := by
  obtain ⟨C_sup, hC_sup, Hsup⟩ := exists_contRep_sup_bound
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨C_g, k_g, ν_g, hC_g, hν_g, Hgrad⟩ :=
    hGrad Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨C_in, k_in, ν_in, hC_in, hν_in, Hin⟩ :=
    inlet_w1_le_of_affineInletFacts h4 Sig lam q hSig hq dm dp hdm
  obtain ⟨ν_per, hν_per, hper⟩ := poly_exp_small 2 dm 2 hdm
  set k₂ : ℕ := max (max (k₁ + 1) (k_g + 1)) (k_in + k₁)
  set C₂ : ℝ := C₁ + C_sup * C₁ + 3 * C_sup * C_g + C_in * C₁
  set ν₀ : ℝ := min (min ν_g ν_in) (min ν_per 1)
  have hC₂ : 0 < C₂ := by positivity
  have hν₀ : 0 < ν₀ := lt_min (lt_min hν_g hν_in) (lt_min hν_per zero_lt_one)
  refine ⟨C₂, k₂, ν₀, hC₂, hν₀, ?_⟩
  intro p d hreg hν hSg hmode z hproj hz
  have hν_g' : p.ν ≤ ν_g := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_in' : p.ν ≤ ν_in := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_per' : p.ν ≤ ν_per := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_1 : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hP1 : p.period ≤ 1 := period_le_one_of hreg (hper p.ν p.ν_pos hν_per')
  obtain ⟨g, hg_op, hg_bd⟩ := Hgrad p d hreg hν_g' hSg hmode z hproj hz
  let u0 : B0411.D p.period p.ν q0E := B0412.XToD (p.graphX z)
  have hνp : 0 < p.ν := p.ν_pos
  have hεp : 0 < p.ε := p.ε_pos
  have hexp_pos : 0 < Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) := by positivity
  have hk_base : (p.ν ^ k₁)⁻¹ ≤ (p.ν ^ k₂)⁻¹ :=
    s1_inv_pow_mono_of_le_one hνp hν_1
      ((Nat.le_succ k₁).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hk_sup0 : (p.ν ^ 1)⁻¹ * (p.ν ^ k₁)⁻¹ ≤ (p.ν ^ k₂)⁻¹ := by
    rw [← mul_inv, ← pow_add, add_comm]
    exact s1_inv_pow_mono_of_le_one hνp hν_1 ((le_max_left _ _).trans (le_max_left _ _))
  have hk_sup1 : (p.ν ^ 1)⁻¹ * (p.ν ^ k_g)⁻¹ ≤ (p.ν ^ k₂)⁻¹ := by
    rw [← mul_inv, ← pow_add, add_comm]
    exact s1_inv_pow_mono_of_le_one hνp hν_1 ((le_max_right _ _).trans (le_max_left _ _))
  have hk_in : (p.ν ^ k_in)⁻¹ * (p.ν ^ k₁)⁻¹ ≤ (p.ν ^ k₂)⁻¹ := by
    rw [← mul_inv, ← pow_add]
    exact s1_inv_pow_mono_of_le_one hνp hν_1 (le_max_right _ _)
  refine ⟨⟨g, hg_op⟩, ?_, ?_, ?_⟩
  · intro τ y
    constructor
    · have h0 := Hsup p.period hP1 p.ν hνp hν_1 u0 τ y
      have hgn0 := graphNormD_graphX_le_norm p z
      calc ‖p.corr z τ y‖
          ≤ C_sup * (p.ν ^ 1)⁻¹ * B0411.graphNormD u0 := h0
        _ ≤ C_sup * (p.ν ^ 1)⁻¹ * (C₁ * (p.ν ^ k₁)⁻¹ *
              Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) := by
            have := hgn0.trans hz
            gcongr
        _ = (C_sup * C₁) * ((p.ν ^ 1)⁻¹ * (p.ν ^ k₁)⁻¹) *
              (Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) := by ring
        _ ≤ C₂ * (p.ν ^ k₂)⁻¹ * (Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) := by
            have : C_sup * C₁ ≤ C₂ := by dsimp [C₂]; linarith [mul_pos hC_sup hC_g, mul_pos hC_in hC₁]
            gcongr
        _ = C₂ * (p.ν ^ k₂)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) := by ring
    · have hfd := hFDeriv p.period hP1 p.ν hνp u0 g hg_op τ y
      change ‖fderiv ℝ (p.corr z τ) y‖ ≤ ∑ j : Fin 3, ‖contRep (g j : Yq p.period q0E) τ y‖ at hfd
      have hj_le : ∀ j : Fin 3, ‖contRep (g j : Yq p.period q0E) τ y‖ ≤
          C_sup * C_g * (p.ν ^ k₂)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) := by
        intro j
        calc ‖contRep (g j : Yq p.period q0E) τ y‖
            ≤ C_sup * (p.ν ^ 1)⁻¹ * B0411.graphNormD (g j) :=
              Hsup p.period hP1 p.ν hνp hν_1 (g j) τ y
          _ ≤ C_sup * (p.ν ^ 1)⁻¹ *
                (C_g * (p.ν ^ k_g)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) := by
              have := hg_bd j
              gcongr
          _ = (C_sup * C_g) * ((p.ν ^ 1)⁻¹ * (p.ν ^ k_g)⁻¹) *
                (Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) := by ring
          _ ≤ (C_sup * C_g) * (p.ν ^ k₂)⁻¹ *
                (Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) := by gcongr
          _ = C_sup * C_g * (p.ν ^ k₂)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) := by ring
      have hsum_le : ∑ j : Fin 3, ‖contRep (g j : Yq p.period q0E) τ y‖ ≤
          3 * (C_sup * C_g * (p.ν ^ k₂)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) := by
        rw [Fin.sum_univ_three]
        linarith [hj_le 0, hj_le 1, hj_le 2]
      calc ‖fderiv ℝ (p.corr z τ) y‖
          ≤ 3 * C_sup * C_g * (p.ν ^ k₂)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) := by
            have := hfd.trans hsum_le
            linarith
        _ ≤ C₂ * (p.ν ^ k₂)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) := by
            have : 3 * C_sup * C_g ≤ C₂ := by
              dsimp [C₂]
              linarith [mul_pos hC_sup hC₁, mul_pos hC_in hC₁]
            gcongr
  · intro τ
    refine (corr_eLpNorm_bgp_le_of_period_le_one p hP1 z τ).trans (ENNReal.ofReal_le_ofReal ?_)
    calc ‖z‖
        ≤ C₁ * (p.ν ^ k₁)⁻¹ * (Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) := by
          linarith [hz]
      _ ≤ C₂ * (p.ν ^ k₂)⁻¹ * (Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) := by
          have : C₁ ≤ C₂ := by
            dsimp [C₂]
            linarith [mul_pos hC_sup hC₁, mul_pos hC_sup hC_g, mul_pos hC_in hC₁]
          gcongr
      _ = C₂ * (p.ν ^ k₂)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) := by ring
  · intro τ y
    obtain ⟨hin0, hin1⟩ := Hin p d hreg hν_in' hSg hmode z τ y
    have h_in_bound : C_in * (p.ν ^ k_in)⁻¹ * ‖z‖ ≤
        C₂ * (p.ν ^ k₂)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) := by
      calc C_in * (p.ν ^ k_in)⁻¹ * ‖z‖
          ≤ C_in * (p.ν ^ k_in)⁻¹ *
              (C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) := by gcongr
        _ = (C_in * C₁) * ((p.ν ^ k_in)⁻¹ * (p.ν ^ k₁)⁻¹) *
              (Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) := by ring
        _ ≤ C₂ * (p.ν ^ k₂)⁻¹ * (Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) := by
            have : C_in * C₁ ≤ C₂ := by
              dsimp [C₂]
              linarith [mul_pos hC_sup hC₁, mul_pos hC_sup hC_g]
            gcongr
        _ = C₂ * (p.ν ^ k₂)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) := by ring
    exact ⟨hin0.trans h_in_bound, hin1.trans h_in_bound⟩

end UnforcedLeray.Short.IIb

end
