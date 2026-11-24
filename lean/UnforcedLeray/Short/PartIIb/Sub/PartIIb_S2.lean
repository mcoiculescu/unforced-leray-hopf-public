import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S1
import UnforcedLeray.Short.PartIIa.Tasks.F04MaximalDomain
import UnforcedLeray.Short.PartIIa.Tasks.F06GraphBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_2.InletWeak.Bounds
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_7_2

/-!
# `Sub/PartII-b_S2`: All spatial orders in the maximal graph and `C^k` / `W^{k,4}` regularity (SP 2541-2562)

Source of record: `the November 2 reference manuscript`
(SP), lines 2541-2562.

## Proved here (zero `sorry`)

1. **Inlet piece regularity (`inlet_bounded_and_solenoidal`, unconditional)**: for every parameter
   point `p` in `BgRegime p d dm dp` with `p.ν ≤ 1` and `p.mode = q`, each inlet column `p.inlet i`
   (`i : Fin 2`) satisfies `IsBoundedBackground (p.inlet i) ∧ ∀ τ, IsSolenoidal (p.inlet i τ)`,
   completely proving the fourth conjunct of `StrongAllOrders` with zero additional hypotheses.
2. **Raw piece regularity (`raw_bounded_and_solenoidal_of`)**: from the existing pool targets
   `PartIIIb.Concrete.RawJointSmooth` (`PartIII-b:C/ward/12/3/1/2/6/1/1`) and
   `PartIIIb.Concrete.RawDerivBdd` (`PartIII-b:C/ward/12/3/1/2/6/1/3`), `p.raw` satisfies
   `IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ)`, proving the third conjunct of
   `StrongAllOrders`.
3. **Iterated maximal-graph bootstrap (`isIteratedPhaseGrad_zero`, `isIteratedPhaseGrad_one_of_first`,
   `exists_next_phaseGrad_in_Yq`, `isIteratedPhaseGrad_succ_of_eq`, `isIteratedPhaseGrad_all_of`)**:
   * `k = 0`: `p.wOf z ∈ D_p` satisfies `IsIteratedPhaseGrad p.period q0E 0 (p.wOf z) ...` (`rfl`).
   * `k = 1`: from `hS1 : StrongFirstDerivative`, the first spatial derivatives `g₁ j ∈ D_p`
     satisfy `IsIteratedPhaseGrad p.period q0E 1 (p.wOf z) (fun α => g₁ (α 0))`.
   * Inductive step `k → k + 1`: for any `g_k : (Fin k → Fin 3) → B0411.D p.period p.ν q0E`
     (`p.period ≤ 1`), `commonBodyGraphBound` (`PartII-a:F06`) produces distributional spatial
     derivatives `G α j ∈ Yq p.period q0E`; given `IteratedDiffEqInYq` (`PartII-b:S2/1`),
     `commonBodyMaximalDomain` (`PartII-a:F04`) upgrades every `G α j` to `B0411.D p.period p.ν q0E`,
     and `Fin.init`/`Fin.last`/`Fin.snoc` glues them into `IsIteratedPhaseGrad p.period q0E (k + 1)`.
4. **Uniform `L^∞`, `L^{11/4}`, and `L^4` bounds on iterated graph derivatives
   (`contRep_iterated_sum_sup_bound`, `contRep_eLpNorm_bgp_le`, `corr_iterated_eLpNorm_bgp_le`,
   `corr_iterated_eLpNorm_four_le`, `bgField_contDiff_of_corr`)**:
   * `contRep_iterated_sum_sup_bound` bounds `∑ α, ‖contRep (g α) τ y‖ ≤ M_corr` via `PartII-a:F11`;
   * `contRep_eLpNorm_bgp_le` bounds `eLpNorm (contRep (u : Yq p.period q0E) τ) (ENNReal.ofReal bgp) ≤ ENNReal.ofReal (graphNormD u)` via `PartII-a:F10`;
   * `corr_iterated_eLpNorm_bgp_le` and `corr_iterated_eLpNorm_four_le` interpolate `L^{11/4} ∩ L^∞ ⊂ L^4` (`PartIIIb.Concrete.interpL4`) to bound `D^k(p.corr z τ)` in `L^4(ℝ³)` uniformly in `τ`.
5. **Conditional assembly `strongAllOrders_of_parts`** of `StrongAllOrders` (`PartII-b:S2`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
  UnforcedLeray.PhaseTrace UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.B0449
  UnforcedLeray.Blueprint UnforcedLeray.Axi

local instance fact_q0_ge_one_s2 : Fact (1 ≤ ENNReal.ofReal B0281.q0) :=
  inferInstanceAs (Fact (1 ≤ q0E))

/-! ## 1. Unconditional proof of `IsBoundedBackground (p.inlet i) ∧ ∀ τ, IsSolenoidal (p.inlet i τ)` -/

private theorem contDiff_slice_of_joint {F : ℝ → Space → Space}
    (hF : ContDiff ℝ ∞ (fun x : ℝ × Space => F x.1 x.2)) (τ : ℝ) :
    ContDiff ℝ ∞ (F τ) :=
  hF.comp (contDiff_const.prodMk contDiff_id)

private theorem sum_physPd_eq_divergence (F : Space → Space) (y : Space) :
    (∑ j : Fin 3, UnforcedLeray.Short.PartIIIb.Concrete.physPd F j y j) = Axi.divergence F y :=
  rfl

/-- Every inlet column `p.inlet i` (`i : Fin 2`) is a smooth bounded solenoidal background field
whenever `BgRegime p d dm dp`, `p.ν ≤ 1`, and `p.mode = q` (proving the fourth conjunct of
`StrongAllOrders` unconditionally). -/
theorem inlet_bounded_and_solenoidal {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) {p : Params} {d dm dp : ℝ}
    (hreg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1) (hmode : p.mode = q) (i : Fin 2) :
    IsBoundedBackground (p.inlet i) ∧ ∀ τ : ℝ, IsSolenoidal (p.inlet i τ) := by
  have hin_joint : ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2) :=
    UnforcedLeray.Short.PartIIIb.Concrete.inlet_contDiff hq hreg hν1 hmode i
  have hin_slice : ∀ τ : ℝ, ContDiff ℝ ∞ (p.inlet i τ) :=
    contDiff_slice_of_joint hin_joint
  have hC1_slice : ∀ τ : ℝ, ContDiff ℝ 1 (p.inlet i τ) := fun τ =>
    (hin_slice τ).of_le (by exact_mod_cast le_top)
  obtain ⟨C0, hC0⟩ := inlet_jet_bound_per hq hreg hν1 hmode i 0
  obtain ⟨C1, hC1⟩ := inlet_jet_bound_per hq hreg hν1 hmode i 1
  refine ⟨?_, ?_⟩
  · refine ⟨hin_joint.continuous.aestronglyMeasurable,
      fun τ => (hC1_slice τ).differentiable one_ne_zero,
      ⟨max C0 C1, fun τ y => ⟨?_, ?_⟩⟩⟩
    · have h0 := hC0 τ y
      rw [norm_iteratedFDeriv_zero] at h0
      exact h0.trans (le_max_left C0 C1)
    · have h1 := hC1 τ y
      rw [norm_iteratedFDeriv_one] at h1
      exact h1.trans (le_max_right C0 C1)
  · intro τ
    have hdiv : ∀ y : Space,
        ∑ j : Fin 3, UnforcedLeray.Short.PartIIIb.Concrete.physPd (p.inlet i τ) j y j = 0 := by
      intro y
      rw [sum_physPd_eq_divergence]
      exact UnforcedLeray.Short.PartIIIb.Concrete.divergence_zero_of_offAxis (hC1_slice τ)
        (fun z hz => UnforcedLeray.Short.PartIIIb.Concrete.inlet_div_offAxis
          hq hreg hν1 hmode i τ hz) y
    exact UnforcedLeray.Short.PartIIIb.Concrete.isSolenoidal_of_pointwise (hC1_slice τ) hdiv

/-! ## 2. Proof of `IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ)` from `RawJointSmooth` and `RawDerivBdd` -/

/-- From `PartIIIb.Concrete.RawJointSmooth` and `PartIIIb.Concrete.RawDerivBdd` (SP 1214-1219,
1305-1325), `p.raw` is a smooth bounded solenoidal background field in the regime for small `ν`. -/
theorem raw_bounded_and_solenoidal_of
    (hRawJoint : UnforcedLeray.Short.PartIIIb.Concrete.RawJointSmooth)
    (hRawBdd : UnforcedLeray.Short.PartIIIb.Concrete.RawDerivBdd)
    {dm dp : ℝ} (hdm : 0 < dm) :
    ∃ ν_raw : ℝ, 0 < ν_raw ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν_raw →
        (∀ τ : ℝ, ContDiff ℝ ∞ (p.raw τ)) ∧
        IsBoundedBackground p.raw ∧ ∀ τ : ℝ, IsSolenoidal (p.raw τ) := by
  obtain ⟨ν₁, hν₁, HRJ⟩ := hRawJoint dm dp hdm
  obtain ⟨ν₂, hν₂, HRB⟩ := hRawBdd dm dp hdm
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, ?_⟩
  intro p d hreg hν
  have hraw_joint : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) :=
    HRJ p d hreg (hν.trans (min_le_left _ _))
  have hraw_slice : ∀ τ : ℝ, ContDiff ℝ ∞ (p.raw τ) :=
    contDiff_slice_of_joint hraw_joint
  have hC1_slice : ∀ τ : ℝ, ContDiff ℝ 1 (p.raw τ) := fun τ =>
    (hraw_slice τ).of_le (by exact_mod_cast le_top)
  obtain ⟨C0, hC0⟩ := HRB p d hreg (hν.trans (min_le_right _ _)) (0 : Fin 3)
  obtain ⟨C1, hC1⟩ := HRB p d hreg (hν.trans (min_le_right _ _)) (1 : Fin 3)
  refine ⟨hraw_slice, ?_, ?_⟩
  · refine ⟨hraw_joint.continuous.aestronglyMeasurable,
      fun τ => (hC1_slice τ).differentiable one_ne_zero,
      ⟨max C0 C1, fun τ y => ⟨?_, ?_⟩⟩⟩
    · have h0 : ‖iteratedFDeriv ℝ 0 (p.raw τ) y‖ ≤ C0 := hC0 τ y
      rw [norm_iteratedFDeriv_zero] at h0
      exact h0.trans (le_max_left C0 C1)
    · have h1 : ‖iteratedFDeriv ℝ 1 (p.raw τ) y‖ ≤ C1 := hC1 τ y
      rw [norm_iteratedFDeriv_one] at h1
      exact h1.trans (le_max_right C0 C1)
  · intro τ
    have hdiv : ∀ y : Space,
        ∑ j : Fin 3, UnforcedLeray.Short.PartIIIb.Concrete.physPd (p.raw τ) j y j = 0 := by
      intro y
      rw [sum_physPd_eq_divergence]
      exact UnforcedLeray.Short.PartIIIb.Concrete.divergence_zero_of_offAxis (hC1_slice τ)
        (fun z hz => UnforcedLeray.Short.PartIIIb.Concrete.raw_div_offAxis hreg τ hz) y
    exact UnforcedLeray.Short.PartIIIb.Concrete.isSolenoidal_of_pointwise (hC1_slice τ) hdiv

/-! ## 3. Iterated maximal-graph bootstrap (`IsIteratedPhaseGrad`) -/

/-- Base case `k = 0`: `B0412.XToD (p.graphX z)` is the order-0 iterated spatial derivative of
`p.wOf z` in `D_p`. -/
theorem isIteratedPhaseGrad_zero (p : Params) (z : p.Z) :
    IsIteratedPhaseGrad p.period q0E 0 (p.wOf z)
      (fun _ : Fin 0 → Fin 3 =>
        ((B0412.XToD (p.graphX z) : B0411.D p.period p.ν q0E) : Yq p.period q0E)) :=
  rfl

/-- Base case `k = 1`: from the first spatial derivatives `g₁ : Fin 3 → B0411.D p.period p.ν q0E`
of `StrongFirstDerivative` (`PartII-b:S1`), `fun α => g₁ (α 0)` satisfies
`IsIteratedPhaseGrad p.period q0E 1 (p.wOf z)`. -/
theorem isIteratedPhaseGrad_one_of_first (p : Params) (z : p.Z)
    (g₁ : Fin 3 → B0411.D p.period p.ν q0E)
    (hg₁ : ∀ j : Fin 3, HasPhaseOp (fun Φ => -dy j Φ) (p.wOf z) (g₁ j : Yq p.period q0E)) :
    IsIteratedPhaseGrad p.period q0E 1 (p.wOf z)
      (fun α : Fin 1 → Fin 3 => (g₁ (α 0) : Yq p.period q0E)) := by
  refine ⟨fun _ => p.wOf z, rfl, fun α j => ?_⟩
  dsimp only
  have hsnoc : Fin.snoc (α := fun _ => Fin 3) α j 0 = j := rfl
  rw [hsnoc]
  exact hg₁ j

/-- Unconditional existence of `(k+1)`-st distributional spatial derivatives in `Yq p.period q0E`
for any family `gk : (Fin k → Fin 3) → B0411.D p.period p.ν q0E` when `p.period ≤ 1`, from
`commonBodyGraphBound` (`PartII-a:F06`, SP 1351-1362). -/
theorem exists_next_phaseGrad_in_Yq (p : Params) (hP1 : p.period ≤ 1) (k : ℕ)
    (gk : (Fin k → Fin 3) → B0411.D p.period p.ν q0E) :
    ∃ G : (Fin k → Fin 3) → Fin 3 → Yq p.period q0E,
      ∀ (α : Fin k → Fin 3) (j : Fin 3),
        HasPhaseOp (fun Φ => -dy j Φ) (gk α : Yq p.period q0E) (G α j) := by
  have hGall : ∀ α : Fin k → Fin 3, ∃ Gα : Fin 3 → Yq p.period q0E,
      ∀ j : Fin 3, HasPhaseOp (fun Φ => -dy j Φ) (gk α : Yq p.period q0E) (Gα j) := by
    intro α
    obtain ⟨_, _, hC⟩ := Short.PartIIa.commonBodyGraphBound q0E
      UnforcedLeray.Short.PartIIIb.Concrete.q0E_gt_one
      UnforcedLeray.Short.PartIIIb.Concrete.q0E_lt_three
    obtain ⟨Gα, hGα, _⟩ := hC p.period hP1 p.ν p.ν_pos 0
      (by simpa using UnforcedLeray.Short.PartIIIb.Concrete.gammaR_q0E_pos) (gk α)
    exact ⟨Gα, hGα⟩
  choose G hG using hGall
  exact ⟨G, hG⟩

/-- Inductive step `k → k + 1` for `IsIteratedPhaseGrad`: given `gk` in `D_p` at order `k`, its
distributional spatial derivatives `G α j` in `Yq p.period q0E`, and the differentiated equation
`HasPhaseOp (0 • Φ + L0T p.ν Φ) (G α j) F` with `F ∈ Yq p.period q0E`, `commonBodyMaximalDomain`
(`PartII-a:F04`) upgrades every `G α j` to `D_p` and `Fin.init`/`Fin.last` glues them into an
order-`(k+1)` family in `D_p`. -/
theorem isIteratedPhaseGrad_succ_of_eq (p : Params) (hP1 : p.period ≤ 1) (z : p.Z) (k : ℕ)
    (gk : (Fin k → Fin 3) → B0411.D p.period p.ν q0E)
    (hgk : IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (gk α : Yq p.period q0E)))
    (G : (Fin k → Fin 3) → Fin 3 → Yq p.period q0E)
    (hG : ∀ (α : Fin k → Fin 3) (j : Fin 3),
      HasPhaseOp (fun Φ => -dy j Φ) (gk α : Yq p.period q0E) (G α j))
    (hEq : ∀ (α : Fin k → Fin 3) (j : Fin 3), ∃ F : Yq p.period q0E,
      HasPhaseOp (fun Φ => (0 : ℂ) • Φ + B0411.L0T p.ν Φ) (G α j) F) :
    ∃ g_next : (Fin (k + 1) → Fin 3) → B0411.D p.period p.ν q0E,
      IsIteratedPhaseGrad p.period q0E (k + 1) (p.wOf z)
        (fun β => (g_next β : Yq p.period q0E)) := by
  have hmem : ∀ (α : Fin k → Fin 3) (j : Fin 3), G α j ∈ B0411.D p.period p.ν q0E := by
    intro α j
    obtain ⟨F, hF⟩ := hEq α j
    exact Short.PartIIa.commonBodyMaximalDomain q0E
      UnforcedLeray.Short.PartIIIb.Concrete.q0E_gt_one
      UnforcedLeray.Short.PartIIIb.Concrete.q0E_lt_three
      p.period hP1 p.ν p.ν_pos 0
      (by simpa using UnforcedLeray.Short.PartIIIb.Concrete.gammaR_q0E_pos) (G α j) F hF
  let g_next : (Fin (k + 1) → Fin 3) → B0411.D p.period p.ν q0E :=
    fun β => ⟨G (Fin.init β) (β (Fin.last k)), hmem (Fin.init β) (β (Fin.last k))⟩
  refine ⟨g_next, fun α => (gk α : Yq p.period q0E), hgk, fun α j => ?_⟩
  dsimp only
  have hsnoc : (g_next (Fin.snoc α j) : Yq p.period q0E) = G α j := by
    dsimp [g_next]
    rw [Fin.init_snoc, Fin.snoc_last]
  rw [hsnoc]
  exact hG α j

/-! ## 4. Uniform `L^∞`, `L^{11/4}`, and `L^4` bounds on `contRep` of iterated graph derivatives -/

/-- For any family `g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E` (`p.period ≤ 1`, `p.ν ≤ 1`),
the sum `∑ α : Fin k → Fin 3, ‖contRep (g α : Yq p.period q0E) τ y‖` is bounded uniformly in
`(τ, y) ∈ ℝ × Space` by `exists_contRep_sup_bound` (`PartII-a:F11`, SP 1524-1531). -/
theorem contRep_iterated_sum_sup_bound (p : Params) (hP1 : p.period ≤ 1) (hν1 : p.ν ≤ 1) (k : ℕ)
    (g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E) :
    ∃ M_corr : ℝ, 0 ≤ M_corr ∧ ∀ (τ : ℝ) (y : Space),
      ∑ α : Fin k → Fin 3, ‖contRep (g α : Yq p.period q0E) τ y‖ ≤ M_corr := by
  obtain ⟨C_sup, hC_sup, Hsup⟩ := S1Sub.exists_contRep_sup_bound
  set M_corr : ℝ := ∑ α : Fin k → Fin 3, C_sup * (p.ν ^ 1)⁻¹ * B0411.graphNormD (g α)
  have hM0 : 0 ≤ M_corr := by
    refine Finset.sum_nonneg fun α _ => ?_
    have hνp : 0 < p.ν := p.ν_pos
    have hgn : 0 ≤ B0411.graphNormD (g α) := by unfold B0411.graphNormD; positivity
    positivity
  refine ⟨M_corr, hM0, fun τ y => ?_⟩
  exact Finset.sum_le_sum fun α _ => Hsup p.period hP1 p.ν p.ν_pos hν1 (g α) τ y

/-- Phasewise `L^{bgp}(ℝ³)` bound on `contRep (u : Yq P q0E) τ` for any `u : B0411.D P ν q0E`
(`0 < P ≤ 1`, `0 < ν`) from `PhaseTrace.norm_phaseRep_le` (`PartII-a:F10`, SP 1517-1523). -/
theorem contRep_eLpNorm_bgp_le {P : ℝ} [Fact (0 < P)] (hP1 : P ≤ 1) {ν : ℝ} (hν : 0 < ν)
    (u : B0411.D P ν q0E) (τ : ℝ) :
    eLpNorm (contRep (u : Yq P q0E) τ) (ENNReal.ofReal bgp) volume ≤
      ENNReal.ofReal (B0411.graphNormD u) := by
  rw [S1Sub.s1_ofReal_bgp_eq_q0E]
  let hTime := hasPhaseOp_T0D u
  let hLap := hasPhaseOp_nuLapD u
  have hcorr_eq : contRep (u : Yq P q0E) τ =
      globalRealChartRep hP1 S1Sub.s1_q0_holder S1Sub.s1_q0_gt hν hTime hLap τ := by
    funext y
    exact S1Sub.contRep_eq_globalRealChartRep hP1 hν u τ y
  have hae := globalRealChartRep_ae_phaseRepC hP1 S1Sub.s1_q0_holder S1Sub.s1_q0_gt hν hTime hLap τ
  have hqtop : q0E ≠ ⊤ := ENNReal.ofReal_ne_top
  let Wτ : Lp CVec3 q0E (volume : Measure Space) :=
    phaseRepC (q := q0E) hqtop hTime (τ : AddCircle P)
  have hptw : ∀ᵐ y ∂(volume : Measure Space),
      ‖contRep (u : Yq P q0E) τ y‖ ≤ ‖(Wτ : Space → CVec3) y‖ := by
    rw [hcorr_eq]
    filter_upwards [hae] with y hy
    rw [hy]
    exact S1Sub.norm_realPartVector_le _
  have hmono : eLpNorm (contRep (u : Yq P q0E) τ) q0E volume ≤ eLpNorm Wτ q0E volume :=
    eLpNorm_mono_ae hptw
  have hWnorm : eLpNorm Wτ q0E volume = ENNReal.ofReal ‖Wτ‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top Wτ)]
  have htrace : ‖Wτ‖ ≤ B0411.graphNormD u := by
    dsimp [Wτ]
    rw [phaseRepC_coe hqtop hTime τ]
    have hb := norm_phaseRep_le hqtop hTime τ
    have hP0 : 0 ≤ P := (Fact.out : 0 < P).le
    have hT0 : 0 ≤ ‖T0D u‖ := norm_nonneg _
    have hPT : P * ‖T0D u‖ ≤ 1 * ‖T0D u‖ := mul_le_mul_of_nonneg_right hP1 hT0
    have hnu : 0 ≤ ‖nuLapD u‖ := norm_nonneg _
    unfold B0411.graphNormD
    linarith
  exact hmono.trans (hWnorm.trans_le (ENNReal.ofReal_le_ofReal htrace))

/-- Continuity of the phase slice `contRep (u : Yq P q0E) τ` for `u : B0411.D P ν q0E`
(`0 < P ≤ 1`, `0 < ν`). -/
theorem contRep_slice_continuous {P : ℝ} [Fact (0 < P)] (hP1 : P ≤ 1) {ν : ℝ} (hν : 0 < ν)
    (u : B0411.D P ν q0E) (τ : ℝ) :
    Continuous (contRep (u : Yq P q0E) τ) := by
  let hTime := hasPhaseOp_T0D u
  let hLap := hasPhaseOp_nuLapD u
  let F : ℝ → SpatialField := globalRealChartRep hP1 S1Sub.s1_q0_holder S1Sub.s1_q0_gt hν hTime hLap
  have hF : IsContRep (u : Yq P q0E) F :=
    graph_globalRealChartRep_isContRep hP1 S1Sub.s1_q0_holder S1Sub.s1_q0_gt hν hTime hLap
  have hcont : IsContRep (u : Yq P q0E) (contRep (u : Yq P q0E)) :=
    contRep_spec ⟨F, hF⟩
  exact hcont.1.comp (continuous_const.prodMk continuous_id)

/-- Phasewise `L^{bgp}(ℝ³)` bound on `iteratedFDeriv ℝ k (p.corr z τ)` whenever
`‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ ∑ α : Fin k → Fin 3, ‖contRep (g α : Yq p.period q0E) τ y‖`. -/
theorem corr_iterated_eLpNorm_bgp_le (p : Params) (hP1 : p.period ≤ 1) (z : p.Z) (k : ℕ)
    (g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E) (τ : ℝ)
    (hle : ∀ y : Space, ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤
      ∑ α : Fin k → Fin 3, ‖contRep (g α : Yq p.period q0E) τ y‖) :
    eLpNorm (fun y => iteratedFDeriv ℝ k (p.corr z τ) y) (ENNReal.ofReal bgp) volume ≤
      ENNReal.ofReal (∑ α : Fin k → Fin 3, B0411.graphNormD (g α)) := by
  have hmono : eLpNorm (fun y => iteratedFDeriv ℝ k (p.corr z τ) y) (ENNReal.ofReal bgp) volume ≤
      eLpNorm (fun y => ∑ α : Fin k → Fin 3, ‖contRep (g α : Yq p.period q0E) τ y‖)
        (ENNReal.ofReal bgp) volume :=
    eLpNorm_mono_ae_real (Eventually.of_forall hle)
  have hsum_fn : (fun y : Space => ∑ α : Fin k → Fin 3, ‖contRep (g α : Yq p.period q0E) τ y‖) =
      ∑ α : Fin k → Fin 3, (fun y : Space => ‖contRep (g α : Yq p.period q0E) τ y‖) := by
    funext y; simp [Finset.sum_apply]
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal bgp := by
    rw [S1Sub.s1_ofReal_bgp_eq_q0E]; exact Fact.out
  have hmeas : ∀ α ∈ (Finset.univ : Finset (Fin k → Fin 3)),
      AEStronglyMeasurable (fun y : Space => ‖contRep (g α : Yq p.period q0E) τ y‖) volume := by
    intro α _
    exact (contRep_slice_continuous hP1 p.ν_pos (g α) τ).norm.aestronglyMeasurable
  have htri : eLpNorm (∑ α : Fin k → Fin 3, (fun y : Space => ‖contRep (g α : Yq p.period q0E) τ y‖))
      (ENNReal.ofReal bgp) volume ≤
      ∑ α : Fin k → Fin 3, eLpNorm (fun y : Space => ‖contRep (g α : Yq p.period q0E) τ y‖)
        (ENNReal.ofReal bgp) volume :=
    eLpNorm_sum_le hmeas hp1
  have hterm : ∑ α : Fin k → Fin 3,
      eLpNorm (fun y : Space => ‖contRep (g α : Yq p.period q0E) τ y‖) (ENNReal.ofReal bgp) volume ≤
      ENNReal.ofReal (∑ α : Fin k → Fin 3, B0411.graphNormD (g α)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun α _ => by unfold B0411.graphNormD; positivity)]
    refine Finset.sum_le_sum fun α _ => ?_
    rw [eLpNorm_norm]
    exact contRep_eLpNorm_bgp_le hP1 p.ν_pos (g α) τ
  rw [hsum_fn] at hmono
  exact hmono.trans (htri.trans hterm)

/-- Uniform `L⁴(ℝ³)` bound on `iteratedFDeriv ℝ k (p.corr z τ)` across `τ : ℝ` from the slice
derivative bound `‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ ∑ α, ‖contRep (g α) τ y‖`, via
`contRep_iterated_sum_sup_bound`, `corr_iterated_eLpNorm_bgp_le`, and `PartIIIb.Concrete.interpL4`
(`L^{11/4} ∩ L^∞ ⊂ L^4`, SP 2557-2559, 2608-2610). -/
theorem corr_iterated_eLpNorm_four_le (p : Params) (hP1 : p.period ≤ 1) (hν1 : p.ν ≤ 1)
    (z : p.Z) (k : ℕ) (g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E)
    (hle : ∀ (τ : ℝ) (y : Space), ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤
      ∑ α : Fin k → Fin 3, ‖contRep (g α : Yq p.period q0E) τ y‖) :
    ∃ M_corr_L4 : ℝ, 0 ≤ M_corr_L4 ∧ ∀ τ : ℝ,
      eLpNorm (fun y => iteratedFDeriv ℝ k (p.corr z τ) y) 4 volume ≤
        ENNReal.ofReal M_corr_L4 := by
  obtain ⟨M_sup, _, hM_sup⟩ := contRep_iterated_sum_sup_bound p hP1 hν1 k g
  set C0 : ℝ := ∑ α : Fin k → Fin 3, B0411.graphNormD (g α)
  obtain ⟨C4, hC4⟩ :=
    UnforcedLeray.Short.PartIIIb.Concrete.interpL4
      (E := ContinuousMultilinearMap ℝ (fun _ : Fin k => Space) Space) M_sup C0
  refine ⟨max C4 0, le_max_right C4 0, fun τ => ?_⟩
  have h1 := hC4 (fun y => iteratedFDeriv ℝ k (p.corr z τ) y)
    (fun y => (hle τ y).trans (hM_sup τ y))
    (corr_iterated_eLpNorm_bgp_le p hP1 z k g τ (hle τ))
  exact h1.trans (ENNReal.ofReal_le_ofReal (le_max_left C4 0))

private theorem contDiff_add3 {k : ℕ} {f g h : Space → Space}
    (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) (hh : ContDiff ℝ k h) :
    ContDiff ℝ k (fun y => f y + g y + h y) :=
  (hf.add hg).add hh

/-- If `p.raw τ` is `C^∞` and `p.corr z τ` is `C^k`, then `bgField p z τ` is `C^k` on `ℝ³`
(since each `p.inlet i τ` is `C^∞` by `inlet_contDiff`). -/
theorem bgField_contDiff_of_corr {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) {p : Params} {d dm dp : ℝ}
    (hreg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1) (hmode : p.mode = q) (z : p.Z) (k : ℕ) (τ : ℝ)
    (hraw : ContDiff ℝ ∞ (p.raw τ)) (hcorr : ContDiff ℝ k (p.corr z τ)) :
    ContDiff ℝ k (bgField p z τ) := by
  have hin : ∀ i : Fin 2, ContDiff ℝ k (p.inlet i τ) := fun i =>
    (contDiff_slice_of_joint
      (UnforcedLeray.Short.PartIIIb.Concrete.inlet_contDiff hq hreg hν1 hmode i) τ).of_le
      (by exact_mod_cast le_top)
  have hsum : ContDiff ℝ k (fun y => ∑ i : Fin 2, p.coord z i • p.inlet i τ y) :=
    ContDiff.sum fun i _ => (hin i).const_smul (p.coord z i)
  have hraw_k : ContDiff ℝ k (p.raw τ) := hraw.of_le (by exact_mod_cast le_top)
  unfold bgField
  exact contDiff_add3 hraw_k hsum hcorr

/-- Pointwise triangle inequality for `iteratedFDeriv ℝ k (bgField p z τ) y` when `p.raw τ`,
`p.inlet i τ`, and `p.corr z τ` are `C^k`. -/
theorem norm_iteratedFDeriv_bgField_le {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) {p : Params} {d dm dp : ℝ}
    (hreg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1) (hmode : p.mode = q) (z : p.Z) (k : ℕ) (τ : ℝ)
    (hraw : ContDiff ℝ ∞ (p.raw τ)) (hcorr : ContDiff ℝ k (p.corr z τ)) (y : Space) :
    ‖iteratedFDeriv ℝ k (bgField p z τ) y‖ ≤
      ‖iteratedFDeriv ℝ k (p.raw τ) y‖ +
        (|p.coord z 0| * ‖iteratedFDeriv ℝ k (p.inlet 0 τ) y‖ +
          |p.coord z 1| * ‖iteratedFDeriv ℝ k (p.inlet 1 τ) y‖) +
        ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ := by
  have hin : ∀ i : Fin 2, ContDiff ℝ k (p.inlet i τ) := fun i =>
    (contDiff_slice_of_joint
      (UnforcedLeray.Short.PartIIIb.Concrete.inlet_contDiff hq hreg hν1 hmode i) τ).of_le
      (by exact_mod_cast le_top)
  have hraw_k : ContDiff ℝ k (p.raw τ) := hraw.of_le (by exact_mod_cast le_top)
  have h0 : ContDiff ℝ k (fun y' => p.coord z 0 • p.inlet 0 τ y') :=
    (hin 0).const_smul (p.coord z 0)
  have h1 : ContDiff ℝ k (fun y' => p.coord z 1 • p.inlet 1 τ y') :=
    (hin 1).const_smul (p.coord z 1)
  have hbg : bgField p z τ =
      fun y' => (p.raw τ y' + (p.coord z 0 • p.inlet 0 τ y' + p.coord z 1 • p.inlet 1 τ y')) +
        p.corr z τ y' := by
    funext y'; simp [bgField, Fin.sum_univ_two]
  rw [hbg, fun_iteratedFDeriv_add_apply (hraw_k.add (h0.add h1)).contDiffAt hcorr.contDiffAt,
    fun_iteratedFDeriv_add_apply hraw_k.contDiffAt (h0.add h1).contDiffAt,
    fun_iteratedFDeriv_add_apply h0.contDiffAt h1.contDiffAt,
    iteratedFDeriv_const_smul_apply' (hin 0).contDiffAt,
    iteratedFDeriv_const_smul_apply' (hin 1).contDiffAt]
  calc ‖iteratedFDeriv ℝ k (p.raw τ) y +
        (p.coord z 0 • iteratedFDeriv ℝ k (p.inlet 0 τ) y +
          p.coord z 1 • iteratedFDeriv ℝ k (p.inlet 1 τ) y) +
        iteratedFDeriv ℝ k (p.corr z τ) y‖
      ≤ ‖iteratedFDeriv ℝ k (p.raw τ) y +
          (p.coord z 0 • iteratedFDeriv ℝ k (p.inlet 0 τ) y +
            p.coord z 1 • iteratedFDeriv ℝ k (p.inlet 1 τ) y)‖ +
          ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ := norm_add_le _ _
    _ ≤ ‖iteratedFDeriv ℝ k (p.raw τ) y‖ +
          (‖p.coord z 0 • iteratedFDeriv ℝ k (p.inlet 0 τ) y‖ +
            ‖p.coord z 1 • iteratedFDeriv ℝ k (p.inlet 1 τ) y‖) +
          ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ := by
        linarith [norm_add_le (iteratedFDeriv ℝ k (p.raw τ) y)
          (p.coord z 0 • iteratedFDeriv ℝ k (p.inlet 0 τ) y +
            p.coord z 1 • iteratedFDeriv ℝ k (p.inlet 1 τ) y),
          norm_add_le (p.coord z 0 • iteratedFDeriv ℝ k (p.inlet 0 τ) y)
            (p.coord z 1 • iteratedFDeriv ℝ k (p.inlet 1 τ) y)]
    _ = ‖iteratedFDeriv ℝ k (p.raw τ) y‖ +
          (|p.coord z 0| * ‖iteratedFDeriv ℝ k (p.inlet 0 τ) y‖ +
            |p.coord z 1| * ‖iteratedFDeriv ℝ k (p.inlet 1 τ) y‖) +
          ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ := by
        simp [norm_smul, Real.norm_eq_abs]

/-- Minkowski bound in `L⁴(ℝ³)` for `iteratedFDeriv ℝ k (bgField p z τ)` from the `L⁴(ℝ³)` bounds on
`iteratedFDeriv ℝ k (p.raw τ)`, `iteratedFDeriv ℝ k (p.inlet i τ)`, and
`iteratedFDeriv ℝ k (p.corr z τ)`. -/
theorem bgField_iterated_eLpNorm_four_le {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) {p : Params} {d dm dp : ℝ}
    (hreg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1) (hmode : p.mode = q) (z : p.Z) (k : ℕ)
    (hraw : ∀ τ : ℝ, ContDiff ℝ ∞ (p.raw τ))
    (hcorr : ∀ τ : ℝ, ContDiff ℝ k (p.corr z τ))
    {M_V M_corr_L4 : ℝ} (hMV0 : 0 ≤ M_V) (hMc0 : 0 ≤ M_corr_L4)
    (hraw_L4 : ∀ τ : ℝ,
      eLpNorm (fun y => iteratedFDeriv ℝ k (p.raw τ) y) 4 volume ≤ ENNReal.ofReal M_V)
    (hin_L4 : ∀ (τ : ℝ) (i : Fin 2),
      eLpNorm (fun y => iteratedFDeriv ℝ k (p.inlet i τ) y) 4 volume ≤ ENNReal.ofReal M_V)
    (hcorr_L4 : ∀ τ : ℝ,
      eLpNorm (fun y => iteratedFDeriv ℝ k (p.corr z τ) y) 4 volume ≤ ENNReal.ofReal M_corr_L4) :
    ∃ M_L4 : ℝ, 0 ≤ M_L4 ∧ ∀ τ : ℝ,
      eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal M_L4 := by
  set M_L4 : ℝ := M_V + (|p.coord z 0| + |p.coord z 1|) * M_V + M_corr_L4
  have hML40 : 0 ≤ M_L4 := by positivity
  refine ⟨M_L4, hML40, fun τ => ?_⟩
  have hin : ∀ i : Fin 2, ContDiff ℝ k (p.inlet i τ) := fun i =>
    (contDiff_slice_of_joint
      (UnforcedLeray.Short.PartIIIb.Concrete.inlet_contDiff hq hreg hν1 hmode i) τ).of_le
      (by exact_mod_cast le_top)
  have hraw_k : ContDiff ℝ k (p.raw τ) := (hraw τ).of_le (by exact_mod_cast le_top)
  have hm_raw : AEStronglyMeasurable (fun y => iteratedFDeriv ℝ k (p.raw τ) y) volume :=
    (hraw_k.continuous_iteratedFDeriv le_rfl).aestronglyMeasurable
  have hm_in0 : AEStronglyMeasurable
      (fun y => p.coord z 0 • iteratedFDeriv ℝ k (p.inlet 0 τ) y) volume :=
    ((hin 0).continuous_iteratedFDeriv le_rfl).aestronglyMeasurable.const_smul (p.coord z 0)
  have hm_in1 : AEStronglyMeasurable
      (fun y => p.coord z 1 • iteratedFDeriv ℝ k (p.inlet 1 τ) y) volume :=
    ((hin 1).continuous_iteratedFDeriv le_rfl).aestronglyMeasurable.const_smul (p.coord z 1)
  have hm_corr : AEStronglyMeasurable (fun y => iteratedFDeriv ℝ k (p.corr z τ) y) volume :=
    ((hcorr τ).continuous_iteratedFDeriv le_rfl).aestronglyMeasurable
  have hptw : ∀ y : Space, ‖iteratedFDeriv ℝ k (bgField p z τ) y‖ ≤
      ((fun y' => ‖iteratedFDeriv ℝ k (p.raw τ) y'‖) +
        ((fun y' => ‖p.coord z 0 • iteratedFDeriv ℝ k (p.inlet 0 τ) y'‖) +
          (fun y' => ‖p.coord z 1 • iteratedFDeriv ℝ k (p.inlet 1 τ) y'‖)) +
        (fun y' => ‖iteratedFDeriv ℝ k (p.corr z τ) y'‖)) y := by
    intro y
    simp only [Pi.add_apply, norm_smul, Real.norm_eq_abs]
    exact norm_iteratedFDeriv_bgField_le hq hreg hν1 hmode z k τ (hraw τ) (hcorr τ) y
  have hmono := eLpNorm_mono_ae_real (p := 4) (μ := volume) (Eventually.of_forall hptw)
  have hp1 : (1 : ℝ≥0∞) ≤ 4 := by norm_num
  have htri1 := eLpNorm_add_le (p := 4)
    (hm_raw.norm.add (hm_in0.norm.add hm_in1.norm)) hm_corr.norm hp1
  have htri2 := eLpNorm_add_le (p := 4) hm_raw.norm (hm_in0.norm.add hm_in1.norm) hp1
  have htri3 := eLpNorm_add_le (p := 4) hm_in0.norm hm_in1.norm hp1
  simp only [eLpNorm_norm] at htri1 htri2 htri3
  have hin0_bd : eLpNorm (fun y => p.coord z 0 • iteratedFDeriv ℝ k (p.inlet 0 τ) y) 4 volume ≤
      ENNReal.ofReal (|p.coord z 0| * M_V) := by
    change eLpNorm (p.coord z 0 • fun y => iteratedFDeriv ℝ k (p.inlet 0 τ) y) 4 volume ≤ _
    rw [eLpNorm_const_smul, ENNReal.ofReal_mul (abs_nonneg _), Real.enorm_eq_ofReal_abs]
    exact mul_le_mul_of_nonneg_left (hin_L4 τ 0) bot_le
  have hin1_bd : eLpNorm (fun y => p.coord z 1 • iteratedFDeriv ℝ k (p.inlet 1 τ) y) 4 volume ≤
      ENNReal.ofReal (|p.coord z 1| * M_V) := by
    change eLpNorm (p.coord z 1 • fun y => iteratedFDeriv ℝ k (p.inlet 1 τ) y) 4 volume ≤ _
    rw [eLpNorm_const_smul, ENNReal.ofReal_mul (abs_nonneg _), Real.enorm_eq_ofReal_abs]
    exact mul_le_mul_of_nonneg_left (hin_L4 τ 1) bot_le
  calc eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume
      ≤ eLpNorm (fun y => iteratedFDeriv ℝ k (p.raw τ) y) 4 volume +
          (eLpNorm (fun y => p.coord z 0 • iteratedFDeriv ℝ k (p.inlet 0 τ) y) 4 volume +
            eLpNorm (fun y => p.coord z 1 • iteratedFDeriv ℝ k (p.inlet 1 τ) y) 4 volume) +
          eLpNorm (fun y => iteratedFDeriv ℝ k (p.corr z τ) y) 4 volume :=
        hmono.trans (htri1.trans (add_le_add (htri2.trans (add_le_add le_rfl htri3)) le_rfl))
    _ ≤ ENNReal.ofReal M_V +
          (ENNReal.ofReal (|p.coord z 0| * M_V) + ENNReal.ofReal (|p.coord z 1| * M_V)) +
          ENNReal.ofReal M_corr_L4 := by
        gcongr
        · exact hraw_L4 τ
        · exact hcorr_L4 τ
    _ = ENNReal.ofReal M_L4 := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add hMV0 (by positivity),
          ← ENNReal.ofReal_add (by positivity) hMc0]
        congr 1; dsimp [M_L4]; ring

/-! ## 5. Remaining PDE leaves and conditional assembly of `StrongAllOrders` (`PartII-b:S2`) -/

/-- **Higher-order differentiated equation in `Y_p` (`PartII-b:S2/1`)**
(`the November 2 reference manuscript`,
lines 2541-2559): for `k ≥ 1`, if all order-`k` distributional spatial derivatives
`gk : (Fin k → Fin 3) → B0411.D p.period p.ν q0E` of `p.wOf z` lie in the maximal graph `D_p` and
`G α j ∈ Yq p.period q0E` is the `j`-th distributional spatial derivative of `gk α`, then `G α j`
satisfies `(0 + L₀ᵗ) (G α j) = F` in distributions for some `F ∈ Yq p.period q0E` (putting one
factor of each order-`(k+1)` derivative of `w · ∇w` in `L^∞` by `exists_contRep_sup_bound` and the
other in `Y_p` by `exists_next_phaseGrad_in_Yq`, together with the `W^{k+1, Y_p}` regularity of the
complete train and inlet sources). -/
def IteratedDiffEqInYq : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Planar.Profile), 0 < Sig →
    Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 → ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ z : p.Z, ProjectedEquation p z →
      ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) →
      ∀ (k : ℕ), 1 ≤ k →
      ∀ gk : (Fin k → Fin 3) → B0411.D p.period p.ν q0E,
        IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (gk α : Yq p.period q0E)) →
      ∀ G : (Fin k → Fin 3) → Fin 3 → Yq p.period q0E,
        (∀ (α : Fin k → Fin 3) (j : Fin 3),
          HasPhaseOp (fun Φ => -dy j Φ) (gk α : Yq p.period q0E) (G α j)) →
        ∀ (α : Fin k → Fin 3) (j : Fin 3), ∃ F : Yq p.period q0E,
          HasPhaseOp (fun Φ => (0 : ℂ) • Φ + B0411.L0T p.ν Φ) (G α j) F

/-- Induction over all spatial orders `k : ℕ`: combining `isIteratedPhaseGrad_zero` (`k = 0`),
`isIteratedPhaseGrad_one_of_first` (`k = 1` from `StrongFirstDerivative`),
`exists_next_phaseGrad_in_Yq` (`PartII-a:F06`), and `isIteratedPhaseGrad_succ_of_eq`
(`PartII-a:F04` + `IteratedDiffEqInYq`). -/
theorem isIteratedPhaseGrad_all_of (p : Params) (hP1 : p.period ≤ 1) (z : p.Z)
    (g₁ : Fin 3 → B0411.D p.period p.ν q0E)
    (hg₁ : ∀ j : Fin 3, HasPhaseOp (fun Φ => -dy j Φ) (p.wOf z) (g₁ j : Yq p.period q0E))
    (hStepEq : ∀ (k : ℕ), 1 ≤ k →
      ∀ gk : (Fin k → Fin 3) → B0411.D p.period p.ν q0E,
        IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (gk α : Yq p.period q0E)) →
      ∀ G : (Fin k → Fin 3) → Fin 3 → Yq p.period q0E,
        (∀ (α : Fin k → Fin 3) (j : Fin 3),
          HasPhaseOp (fun Φ => -dy j Φ) (gk α : Yq p.period q0E) (G α j)) →
        ∀ (α : Fin k → Fin 3) (j : Fin 3), ∃ F : Yq p.period q0E,
          HasPhaseOp (fun Φ => (0 : ℂ) • Φ + B0411.L0T p.ν Φ) (G α j) F) :
    ∀ k : ℕ, ∃ g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E,
      IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (g α : Yq p.period q0E)) := by
  intro k
  induction k with
  | zero =>
      exact ⟨fun _ => B0412.XToD (p.graphX z), isIteratedPhaseGrad_zero p z⟩
  | succ k ih =>
      rcases k with _ | k
      · exact ⟨fun α => g₁ (α 0), isIteratedPhaseGrad_one_of_first p z g₁ hg₁⟩
      · obtain ⟨gk, hgk⟩ := ih
        obtain ⟨G, hG⟩ := exists_next_phaseGrad_in_Yq p hP1 (k + 1) gk
        exact isIteratedPhaseGrad_succ_of_eq p hP1 z (k + 1) gk hgk G hG
          (hStepEq (k + 1) (Nat.succ_pos k) gk hgk G hG)

/-- **Classical slice regularity of `contRep u τ` for iterated maximal-graph states (`PartII-b:S2/2`)**
(`the November 2 reference manuscript`,
lines 2557-2559): for `0 < P ≤ 1`, `0 < ν`, and `u : Yq P q0E`, if all order-`m` distributional
spatial derivatives of `u` lie in `B0411.D P ν q0E` for every `m : ℕ`, then for every `k : ℕ` and
`g : (Fin k → Fin 3) → B0411.D P ν q0E` with `IsIteratedPhaseGrad P q0E k u (fun α => (g α : Yq P q0E))`,
every phase slice `contRep u τ` is `C^k` on `Space` with
`‖iteratedFDeriv ℝ k (contRep u τ) y‖ ≤ ∑ α : Fin k → Fin 3, ‖contRep (g α : Yq P q0E) τ y‖`. -/
def CorrSliceIteratedContDiff : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ (ν : ℝ), 0 < ν → ∀ u : Yq P q0E,
    (∀ m : ℕ, ∃ gm : (Fin m → Fin 3) → B0411.D P ν q0E,
      IsIteratedPhaseGrad P q0E m u (fun α => (gm α : Yq P q0E))) →
    ∀ (k : ℕ) (g : (Fin k → Fin 3) → B0411.D P ν q0E),
      IsIteratedPhaseGrad P q0E k u (fun α => (g α : Yq P q0E)) →
      ∀ τ : ℝ, ContDiff ℝ k (contRep u τ) ∧
        ∀ y : Space, ‖iteratedFDeriv ℝ k (contRep u τ) y‖ ≤
          ∑ α : Fin k → Fin 3, ‖contRep (g α : Yq P q0E) τ y‖

/-- **Uniform `L⁴(ℝ³)` bounds on `D^k(p.raw τ)` and `D^k(p.inlet i τ)` (`PartII-b:S2/3`)**
(`the November 2 reference manuscript`,
lines 2557-2559, 2607-2610): in the regime for small `ν`, for every spatial derivative order `k : ℕ`
there is `M_V ≥ 0` such that `eLpNorm (fun y => iteratedFDeriv ℝ k (p.raw τ) y) 4 volume ≤ ENNReal.ofReal M_V`
and `eLpNorm (fun y => iteratedFDeriv ℝ k (p.inlet i τ) y) 4 volume ≤ ENNReal.ofReal M_V` for all
`τ : ℝ` and `i : Fin 2` (from the inverse-distance decay `(1 + ‖y‖)^{-1-k}` of the train lift and
inlet columns). -/
def RawAndInletIteratedL4Bound : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Planar.Profile), 0 < Sig →
    Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ k : ℕ, ∃ M_V : ℝ, 0 ≤ M_V ∧ ∀ τ : ℝ,
        eLpNorm (fun y => iteratedFDeriv ℝ k (p.raw τ) y) 4 volume ≤ ENNReal.ofReal M_V ∧
        ∀ i : Fin 2,
          eLpNorm (fun y => iteratedFDeriv ℝ k (p.inlet i τ) y) 4 volume ≤ ENNReal.ofReal M_V

/-- **Classical slice regularity of `p.corr z τ` and uniform `L⁴(ℝ³)` bound on `D^k(bgField p z τ)`**
(`the November 2 reference manuscript`,
lines 2557-2559): when all order-`k` distributional spatial derivatives `g α` of `p.wOf z` lie in the
maximal graph `D_p` for every `k : ℕ`, each slice `p.corr z τ` is `C^k` with
`‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ ∑ α : Fin k → Fin 3, ‖contRep (g α : Yq p.period q0E) τ y‖`,
and `iteratedFDeriv ℝ k (bgField p z τ)` is uniformly bounded in `L⁴(ℝ³)` across `τ : ℝ`. -/
def CorrSliceIteratedAndBgL4Bound : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Planar.Profile), 0 < Sig →
    Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 → ∀ (C₁ : ℝ) (_k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ z : p.Z, ProjectedEquation p z →
      (∀ k : ℕ, ∃ g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E,
        IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (g α : Yq p.period q0E))) →
      ∀ (k : ℕ) (g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E),
        IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (g α : Yq p.period q0E)) →
        (∀ (τ : ℝ), ContDiff ℝ k (p.corr z τ) ∧
          ∀ y : Space, ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤
            ∑ α : Fin k → Fin 3, ‖contRep (g α : Yq p.period q0E) τ y‖) ∧
        ∃ M_L4 : ℝ, 0 ≤ M_L4 ∧ ∀ τ : ℝ,
          eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal M_L4

/-- Reduction of `CorrSliceIteratedAndBgL4Bound` to `PartIIIb.Concrete.RawJointSmooth`,
`CorrSliceIteratedContDiff` (`PartII-b:S2/2`), and `RawAndInletIteratedL4Bound` (`PartII-b:S2/3`),
using `corr_iterated_eLpNorm_four_le` and `bgField_iterated_eLpNorm_four_le`. -/
theorem corrSliceIteratedAndBgL4Bound_of
    (hRawJoint : UnforcedLeray.Short.PartIIIb.Concrete.RawJointSmooth)
    (hSlice : CorrSliceIteratedContDiff)
    (hVL4 : RawAndInletIteratedL4Bound) :
    CorrSliceIteratedAndBgL4Bound := by
  intro Sig lam q hSig hq m _ dm dp hdm _ C₁ k₁ _
  obtain ⟨ν_rj, hν_rj, HRJ⟩ := hRawJoint dm dp hdm
  obtain ⟨ν_vl4, hν_vl4, HVL4⟩ := hVL4 Sig lam q hSig hq dm dp hdm
  obtain ⟨ν_per, hν_per, hper⟩ := poly_exp_small 2 dm 2 hdm
  set ν₀ : ℝ := min (min ν_rj ν_vl4) (min ν_per 1)
  have hν₀ : 0 < ν₀ := lt_min (lt_min hν_rj hν_vl4) (lt_min hν_per zero_lt_one)
  refine ⟨ν₀, hν₀, ?_⟩
  intro p d hreg hν hSg hmode z _ hall k g hgk
  have hν_rj' : p.ν ≤ ν_rj := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_vl4' : p.ν ≤ ν_vl4 := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_per' : p.ν ≤ ν_per := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_1 : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hP1 : p.period ≤ 1 := period_le_one_of hreg (hper p.ν p.ν_pos hν_per')
  have hcorr_slice : ∀ τ : ℝ, ContDiff ℝ k (p.corr z τ) ∧
      ∀ y : Space, ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤
        ∑ α : Fin k → Fin 3, ‖contRep (g α : Yq p.period q0E) τ y‖ :=
    hSlice p.period hP1 p.ν p.ν_pos (p.wOf z) hall k g hgk
  refine ⟨hcorr_slice, ?_⟩
  have hraw_slice : ∀ τ : ℝ, ContDiff ℝ ∞ (p.raw τ) :=
    contDiff_slice_of_joint (HRJ p d hreg hν_rj')
  obtain ⟨M_V, hMV0, hMV⟩ := HVL4 p d hreg hν_vl4' hSg hmode k
  obtain ⟨M_corr_L4, hMc0, hMc⟩ :=
    corr_iterated_eLpNorm_four_le p hP1 hν_1 z k g (fun τ y => (hcorr_slice τ).2 y)
  exact bgField_iterated_eLpNorm_four_le hq hreg hν_1 hmode z k hraw_slice
    (fun τ => (hcorr_slice τ).1) hMV0 hMc0 (fun τ => (hMV τ).1) (fun τ i => (hMV τ).2 i) hMc

/-- **Conditional assembly of `StrongAllOrders` (`PartII-b:S2`, SP 2541-2562)** from
`StrongFirstDerivative` (`PartII-b:S1`), `PartIIIb.Concrete.RawJointSmooth`,
`PartIIIb.Concrete.RawDerivBdd`, `IteratedDiffEqInYq`, and `CorrSliceIteratedAndBgL4Bound`. -/
theorem strongAllOrders_of_parts
    (hRawJoint : UnforcedLeray.Short.PartIIIb.Concrete.RawJointSmooth)
    (hRawBdd : UnforcedLeray.Short.PartIIIb.Concrete.RawDerivBdd)
    (hDiffEq : IteratedDiffEqInYq)
    (hSliceL4 : CorrSliceIteratedAndBgL4Bound)
    (_h4 : AffineInletFacts)
    (_hQ1 : QuadBound)
    (hS1 : StrongFirstDerivative) :
    StrongAllOrders := by
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨_, _, ν_s1, _, hν_s1, HS1⟩ := hS1 Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν_raw, hν_raw, HRaw⟩ := raw_bounded_and_solenoidal_of hRawJoint hRawBdd hdm
  obtain ⟨ν_deq, hν_deq, HDeq⟩ := hDiffEq Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν_sl4, hν_sl4, HSl4⟩ := hSliceL4 Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν_per, hν_per, hper⟩ := poly_exp_small 2 dm 2 hdm
  set ν₀ : ℝ := min (min (min ν_s1 ν_raw) (min ν_deq ν_sl4)) (min ν_per 1)
  have hν₀ : 0 < ν₀ := lt_min
    (lt_min (lt_min hν_s1 hν_raw) (lt_min hν_deq hν_sl4))
    (lt_min hν_per zero_lt_one)
  refine ⟨ν₀, hν₀, ?_⟩
  intro p d hreg hν hSg hmode z hproj hz
  have hν_s1' : p.ν ≤ ν_s1 :=
    hν.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hν_raw' : p.ν ≤ ν_raw :=
    hν.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hν_deq' : p.ν ≤ ν_deq :=
    hν.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_left _ _))
  have hν_sl4' : p.ν ≤ ν_sl4 :=
    hν.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_right _ _))
  have hν_per' : p.ν ≤ ν_per := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_1 : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hP1 : p.period ≤ 1 := period_le_one_of hreg (hper p.ν p.ν_pos hν_per')
  obtain ⟨⟨g₁, hg₁⟩, _, _, _⟩ := HS1 p d hreg hν_s1' hSg hmode z hproj hz
  obtain ⟨hraw_slice, hraw_bg⟩ := HRaw p d hreg hν_raw'
  have hall_grad : ∀ k : ℕ, ∃ g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E,
      IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (g α : Yq p.period q0E)) :=
    isIteratedPhaseGrad_all_of p hP1 z g₁ hg₁
      (HDeq p d hreg hν_deq' hSg hmode z hproj hz)
  refine ⟨hall_grad, ?_, hraw_bg, fun i => inlet_bounded_and_solenoidal hq hreg hν_1 hmode i⟩
  intro k
  obtain ⟨gk, hgk⟩ := hall_grad k
  obtain ⟨M_corr, hM_corr0, hM_corr⟩ := contRep_iterated_sum_sup_bound p hP1 hν_1 k gk
  obtain ⟨hcorr_slice, M_L4, hM_L40, hM_L4⟩ :=
    HSl4 p d hreg hν_sl4' hSg hmode z hproj hall_grad k gk hgk
  refine ⟨max M_corr M_L4, fun τ => ⟨?_, ?_, ?_⟩⟩
  · exact bgField_contDiff_of_corr hq hreg hν_1 hmode z k τ (hraw_slice τ) (hcorr_slice τ).1
  · intro y
    exact ((hcorr_slice τ).2 y).trans ((hM_corr τ y).trans (le_max_left M_corr M_L4))
  · exact (hM_L4 τ).trans (ENNReal.ofReal_le_ofReal (le_max_right M_corr M_L4))

/-- **Direct assembly of `StrongAllOrders` (`PartII-b:S2`, SP 2541-2562)** from
`PartIIIb.Concrete.RawJointSmooth`, `PartIIIb.Concrete.RawDerivBdd`, `IteratedDiffEqInYq`
(`PartII-b:S2/1`), `CorrSliceIteratedContDiff` (`PartII-b:S2/2`), `RawAndInletIteratedL4Bound`
(`PartII-b:S2/3`), `AffineInletFacts`, `QuadBound`, and `StrongFirstDerivative` (`PartII-b:S1`). -/
theorem strongAllOrders_of_leaves
    (hRawJoint : UnforcedLeray.Short.PartIIIb.Concrete.RawJointSmooth)
    (hRawBdd : UnforcedLeray.Short.PartIIIb.Concrete.RawDerivBdd)
    (hDiffEq : IteratedDiffEqInYq)
    (hSlice : CorrSliceIteratedContDiff)
    (hVL4 : RawAndInletIteratedL4Bound)
    (h4 : AffineInletFacts)
    (hQ1 : QuadBound)
    (hS1 : StrongFirstDerivative) :
    StrongAllOrders :=
  strongAllOrders_of_parts hRawJoint hRawBdd hDiffEq
    (corrSliceIteratedAndBgL4Bound_of hRawJoint hSlice hVL4) h4 hQ1 hS1

end UnforcedLeray.Short.IIb

end
