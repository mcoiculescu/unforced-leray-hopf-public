import UnforcedLeray.Short.PartIIb.Sub.ComparisonAndStrongDesign
import UnforcedLeray.Short.PartIIb.Tasks.LpBound23over8
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Part II-b, Task `PartII-b:T20`: Local interaction comparison (`LocalInteractionComparison`, audit)

Source of record: `the November 2 reference manuscript` (SP), lines 2006–2056
(`bg:local-interaction`).

## What is proved here (zero `sorry`)
* `flatK_decomp`, `localInteraction_split`: the algebraic decomposition
  `ϑ(g_ε - K_0 b_0) = ϑ K_0(b_ε - b_0) + ϑ(g_ε - K_0 b_ε)`.
* `bgRegime_eps_le_one`, `bgRegime_c_le`, `bgRegime_c_inv_le`, `eps_le_rpow_539`: regime parameter
  and exponent bounds (`0 < ε ≤ 1`, `c, c⁻¹ ≤ Γ²`, `ε ≤ ε^{2/539}`).
* `phys_graph_at_zero`: specialization of `phys_graph_poly bgp` at shift `μ = 0` (`1/22` spectral gap).
* `hMeas_ac_restrict`, `HasWeakFO.locallyIntegrableOn`, `HasWeakVec.aestronglyMeasurable_hMeas`:
  every weak derivative `g` satisfying `HasWeakVec v d b g` on `s > 0` is locally integrable on
  `Ioi 0 ×ˢ univ` and hence `AEStronglyMeasurable g (hMeas c r)`.
* `ObsOp.mono`, `ObsOp.mono_apply`, `ObsOp.aestronglyMeasurable_apply`: parameter monotonicity and
  measurability of `ObsOp.apply`.
* Counterexample (`gε_nonper`, `isKOut_zero_gε_nonper`, `localInteractionComparison_counterexample_at_zero`)
  showing that without `InHr p.c bgp gε` (`QPeriodic p.c gε`), `IsKOut p 0 gε_nonper` holds for a
  profile `gε_nonper` supported on `s ≤ 1 ∧ q ≤ 0` that is non-zero on `(0, 1] × (-p.c/2, 0] × ℝ`,
  while the right-hand side at `F = 0, bε = 0, b0 = 0` vanishes.
* Corrected statement `LocalInteractionComparisonCorrected` (incorporating `InHr p.c bgp gε` and the
  small-viscosity threshold `∃ ν₀ > 0, ... p.ν ≤ ν₀` from SP 255–258), leaf specifications
  `FlatKObsOpPackage` (`PartII-b:T20/1`) and `LocalInteractionRemainderBound` (`PartII-b:T20/2`),
  and the conditional assembly `localInteractionComparisonCorrected_of`.
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

/-! ## Algebraic decomposition of `flatK` -/

/-- Linearity of `flatK` in `(b, gq, gη)`:
`flatK tr (bε - b0) gq_diff gη_diff + flatK tr b0 gq0 gη0 = flatK tr bε (gq_diff + gq0) (gη_diff + gη0)`. -/
theorem flatK_decomp {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (bε b0 gq_diff gη_diff gq0 gη0 : CProf) (x : Coord) :
    flatK tr (bε - b0) gq_diff gη_diff x + flatK tr b0 gq0 gη0 x =
      flatK tr bε (gq_diff + gq0) (gη_diff + gη0) x := by
  ext i
  simp only [flatK, PiLp.add_apply, PiLp.sub_apply, WithLp.ofLp_toLp, Pi.sub_apply, Pi.add_apply]
  ring

/-- Pointwise decomposition of the localized interaction difference:
`ϑ(g_ε - K_0 b_0) = ϑ K_0(b_ε - b_0) + ϑ(g_ε - K_0 b_ε)`. -/
theorem localInteraction_split {ν c : ℝ} (tr : B0140.TrainSol ν c) (ϑ : Coord → ℝ)
    (gε bε b0 gq_diff gη_diff gq0 gη0 : CProf) (x : Coord) :
    (ϑ x : ℂ) • (gε x - flatK tr b0 gq0 gη0 x) =
      (ϑ x : ℂ) • flatK tr (bε - b0) gq_diff gη_diff x +
        (ϑ x : ℂ) • (gε x - flatK tr bε (gq_diff + gq0) (gη_diff + gη0) x) := by
  rw [← smul_add, ← flatK_decomp tr bε b0 gq_diff gη_diff gq0 gη0 x]
  congr 1
  abel

/-! ## Regime arithmetic and physical graph regularity -/

/-- In `BgRegime p d dm dp`, `p.ε = e^{-d/ν} ≤ 1`. -/
theorem bgRegime_eps_le_one {p : Params} {d dm dp : ℝ} (hbg : BgRegime p d dm dp) :
    p.ε ≤ 1 := by
  rw [hbg.eps_eq, Real.exp_le_one_iff]
  have hd0 : 0 < d := lt_of_lt_of_le hbg.dm_pos hbg.dm_le
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd0.le) p.ν_pos.le

/-- In `BgRegime p d dm dp`, `p.c = (p.ν²)⁻¹ ≤ Γ²` when `p.ν⁻¹ ≤ Γ` and `1 ≤ Γ`. -/
theorem bgRegime_c_le {p : Params} {d dm dp Γ : ℝ} (hbg : BgRegime p d dm dp)
    (hΓ1 : 1 ≤ Γ) (hνi : p.ν⁻¹ ≤ Γ) :
    p.c ≤ Γ ^ 2 := by
  rw [hbg.c_eq, ← inv_pow]
  have h0 : 0 ≤ p.ν⁻¹ := inv_nonneg.mpr p.ν_pos.le
  nlinarith

/-- In `BgRegime p d dm dp`, `p.c⁻¹ = p.ν² ≤ Γ²` when `p.ν ≤ Γ` and `1 ≤ Γ`. -/
theorem bgRegime_c_inv_le {p : Params} {d dm dp Γ : ℝ} (hbg : BgRegime p d dm dp)
    (hΓ1 : 1 ≤ Γ) (hν : p.ν ≤ Γ) :
    p.c⁻¹ ≤ Γ ^ 2 := by
  rw [hbg.c_eq, inv_inv]
  have h0 : 0 ≤ p.ν := p.ν_pos.le
  nlinarith

/-- For `0 ≤ ε ≤ 1`, `ε ≤ ε^{2/539}`. -/
theorem eps_le_rpow_539 {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ε ≤ ε ^ (2 / 539 : ℝ) := by
  by_cases h0 : ε = 0
  · subst h0
    rw [Real.zero_rpow (by norm_num)]
  · have hpos : 0 < ε := lt_of_le_of_ne hε0 (Ne.symm h0)
    calc ε = ε ^ (1 : ℝ) := (Real.rpow_one ε).symm
      _ ≤ ε ^ (2 / 539 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hpos hε1 (by norm_num)

/-- Specialization of `phys_graph_poly bgp` at shift `μ = 0` (`(3 / bgp - 1) / 2 = 1 / 22`). -/
theorem phys_graph_at_zero :
    ∃ C_phys : ℝ, 0 < C_phys ∧
      ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.period ≤ 1 →
      ∀ (Γ : ℝ), 1 ≤ Γ →
      ∀ F bε : CProf, InHr p.c bgp F → IsResponse p.ν p.c p.ε 0 bgp F bε →
        ∃ Sb Qb Eb : CProf,
          HasWeakVec vS dZero bε Sb ∧ HasWeakVec (vQ p.ε) (dQ p.ε) bε Qb ∧
          HasWeakVec vEta dZero bε Eb ∧
          AEStronglyMeasurable Sb (hMeas p.c bgp) ∧
          AEStronglyMeasurable (sqrtS Qb) (hMeas p.c bgp) ∧
          AEStronglyMeasurable (sqrtS Eb) (hMeas p.c bgp) ∧
          hNorm p.c bgp bε + hNorm p.c bgp Sb +
              ENNReal.ofReal (Real.sqrt p.ν) *
                (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) ≤
            ENNReal.ofReal (C_phys * Γ ^ 2) * hNorm p.c bgp F := by
  have h1 : 1 < bgp := by unfold bgp; norm_num
  have h3 : bgp < 3 := by unfold bgp; norm_num
  obtain ⟨C₀, hC₀, hphys⟩ := phys_graph_poly bgp h1 h3
  refine ⟨C₀ * 22 ^ 2, by positivity, ?_⟩
  intro p d dm dp hbg hper Γ hΓ1 F bε hF hbε
  have hΓ22 : 1 ≤ 22 * Γ := by linarith
  have hμ0 : ‖(0 : ℂ)‖ ≤ 22 * Γ := by simp; linarith
  have hgap : (22 * Γ)⁻¹ ≤ (0 : ℂ).re + (3 / bgp - 1) / 2 := by
    rw [Complex.zero_re, zero_add]
    have hbgp_val : (3 / bgp - 1) / 2 = (22 : ℝ)⁻¹ := by unfold bgp; norm_num
    rw [hbgp_val]
    exact inv_anti₀ (by norm_num) (by linarith)
  have hε1 : p.ε ≤ 1 := bgRegime_eps_le_one hbg
  obtain ⟨Sb, Qb, Eb, hS, hQ, hE, hmS, hmQ, hmE, hbd⟩ :=
    hphys (22 * Γ) p.ν p.c p.ε 0 hΓ22 hμ0 hgap p.ν_pos p.c_pos p.ε_pos hε1 hper F bε hF hbε
  refine ⟨Sb, Qb, Eb, hS, hQ, hE, hmS, hmQ, hmE, ?_⟩
  convert hbd using 3
  ring

/-! ## Local integrability and `hMeas` measurability of weak derivatives -/

/-- `hMeas c r` is absolutely continuous with respect to `volume.restrict (Ioi 0 ×ˢ univ)`. -/
theorem hMeas_ac_restrict (c r : ℝ) :
    hMeas c r ≪ (volume : Measure Coord).restrict (Ioi (0 : ℝ) ×ˢ univ) := by
  unfold hMeas
  rw [Axi.ageμ, Measure.volume_eq_prod, ← Measure.prod_restrict]
  refine Measure.AbsolutelyContinuous.prod ?_ ?_
  · exact withDensity_absolutelyContinuous _ _
  · unfold UnforcedLeray.Cyl.avgμ
    rw [Measure.restrict_univ]
    exact (Measure.smul_absolutelyContinuous).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

/-- Any scalar weak derivative `HasWeakFO v d u g` on `s > 0` is locally integrable on
`Ioi 0 ×ˢ univ` with respect to `volume`. -/
theorem HasWeakFO.locallyIntegrableOn {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ}
    {u g : Coord → ℂ} (hw : HasWeakFO v d u g) :
    LocallyIntegrableOn g (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) volume := by
  have hUo : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUo x hx
  let β : ContDiffBump x :=
    { rIn := ε / 4
      rOut := ε / 2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  have hβsub : tsupport β ⊆ Ioi (0 : ℝ) ×ˢ univ := by
    rw [β.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hball
  have hβtest : IsCoordTest β := ⟨β.contDiff, β.hasCompactSupport, hβsub⟩
  have J1 : Integrable (fun y => g y * (β y : ℂ)) volume := (hw.1 β hβtest).2
  have hB1 : IntegrableOn g (ball x (ε / 4)) volume := by
    apply (J1.integrableOn).congr_fun _ measurableSet_ball
    intro y hy
    have h1 : β y = 1 := β.one_of_mem_closedBall (ball_subset_closedBall hy)
    simp [h1]
  have hat : IntegrableAtFilter g (nhds x) volume :=
    ⟨ball x (ε / 4), ball_mem_nhds x (by linarith), hB1⟩
  exact hat.filter_mono nhdsWithin_le_nhds

/-- Every profile weak derivative `g` satisfying `HasWeakVec v d b g` is `AEStronglyMeasurable`
with respect to `hMeas c r`. -/
theorem HasWeakVec.aestronglyMeasurable_hMeas {c r : ℝ}
    {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {b g : CProf}
    (hw : HasWeakVec v d b g) :
    AEStronglyMeasurable g (hMeas c r) := by
  have h0 : AEStronglyMeasurable (fun x : Coord => g x 0) (hMeas c r) :=
    (hw 0).locallyIntegrableOn.aestronglyMeasurable.mono_ac (hMeas_ac_restrict c r)
  have h1 : AEStronglyMeasurable (fun x : Coord => g x 1) (hMeas c r) :=
    (hw 1).locallyIntegrableOn.aestronglyMeasurable.mono_ac (hMeas_ac_restrict c r)
  have heq : g = fun x : Coord =>
      g x 0 • (WithLp.toLp 2 ![1, 0] : CMerid) +
        g x 1 • (WithLp.toLp 2 ![0, 1] : CMerid) := by
    ext x i
    fin_cases i <;> simp
  rw [heq]
  exact (h0.smul aestronglyMeasurable_const).add (h1.smul aestronglyMeasurable_const)

/-! ## `ObsOp` monotonicity and measurability -/

/-- Monotonicity of `ObsOp σ H₁ L₁ Γ` in the norm bound parameter `Γ`. -/
def ObsOp.mono {σ H₁ L₁ Γ Γ' : ℝ} (B : ObsOp σ H₁ L₁ Γ) (hΓ : Γ ≤ Γ') :
    ObsOp σ H₁ L₁ Γ' where
  Aq := B.Aq
  Aeta := B.Aeta
  A0 := B.A0
  smooth := B.smooth
  supp := B.supp
  bounded := fun k hk x =>
    ⟨(B.bounded k hk x).1.trans hΓ,
     (B.bounded k hk x).2.1.trans hΓ,
     (B.bounded k hk x).2.2.trans hΓ⟩

@[simp]
theorem ObsOp.mono_apply {σ H₁ L₁ Γ Γ' : ℝ} (B : ObsOp σ H₁ L₁ Γ) (hΓ : Γ ≤ Γ')
    (b gq gη : CProf) :
    (B.mono hΓ).apply b gq gη = B.apply b gq gη := rfl

/-- For any `ObsOp`, `B.apply b gq gη` is `AEStronglyMeasurable` whenever `b, gq, gη` are. -/
theorem ObsOp.aestronglyMeasurable_apply {σ H₁ L₁ Γ : ℝ} {μ : Measure Coord}
    (B : ObsOp σ H₁ L₁ Γ) {b gq gη : CProf}
    (hb : AEStronglyMeasurable b μ) (hgq : AEStronglyMeasurable gq μ)
    (hgη : AEStronglyMeasurable gη μ) :
    AEStronglyMeasurable (B.apply b gq gη) μ := by
  have heval : Continuous (fun p : (CMerid →L[ℂ] CMerid) × CMerid => p.1 p.2) :=
    isBoundedBilinearMap_apply.continuous
  have hAq : AEStronglyMeasurable (fun x => B.Aq x (gq x)) μ :=
    heval.comp_aestronglyMeasurable (B.smooth.1.continuous.aestronglyMeasurable.prodMk hgq)
  have hAeta : AEStronglyMeasurable (fun x => B.Aeta x (gη x)) μ :=
    heval.comp_aestronglyMeasurable (B.smooth.2.1.continuous.aestronglyMeasurable.prodMk hgη)
  have hA0 : AEStronglyMeasurable (fun x => B.A0 x (b x)) μ :=
    heval.comp_aestronglyMeasurable (B.smooth.2.2.continuous.aestronglyMeasurable.prodMk hb)
  exact (hAq.add hAeta).add hA0

/-! ## Counterexample to the un-periodic statement (missing `InHr p.c bgp gε`) -/

/-- Counterexample profile for `IsKOut p 0 gε` without `QPeriodic p.c gε` (`InHr p.c bgp gε`):
supported on `s ≤ 1 ∧ q ≤ 0`, which is disjoint from `Axi.chart p.R τ y` for all `τ > 0`
since `s ≤ 1 → log s ≤ 0 → q = R τ / 2 - (R / 2) log s > 0`, yet non-zero on
`[σ, 1] × [-p.c / 2, 0] × [-L₁, L₁] ⊆ obsBox σ H₁ L₁`. -/
def gε_nonper : CProf :=
  fun x => if x.1 ≤ 1 ∧ x.2.1 ≤ 0 then WithLp.toLp 2 (fun _ => 1) else 0

theorem gε_nonper_chart_eq_zero {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) (y : Space) :
    gε_nonper (Axi.chart R τ y) = 0 := by
  unfold gε_nonper Axi.chart
  rw [ite_eq_right_iff]
  rintro ⟨h1, h2⟩
  have hage_nn : 0 ≤ Axi.age R y := Axi.age_nonneg R y
  have hlog : Real.log (Axi.age R y) ≤ 0 := Real.log_nonpos hage_nn h1
  dsimp [Axi.phase] at h2
  have hRt : 0 < R * τ / 2 := by positivity
  have hRlog : (R / 2) * Real.log (Axi.age R y) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hlog
  linarith

theorem nvC_gε_nonper_eq_zero {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) (y : Space) :
    NvC R gε_nonper (τ, y) = 0 := by
  have hz : reM (gε_nonper (Axi.chart R τ y)) = 0 ∧ imM (gε_nonper (Axi.chart R τ y)) = 0 := by
    rw [gε_nonper_chart_eq_zero hR hτ y]
    constructor <;> (ext i; simp [reM, imM])
  unfold NvC Axi.Nv
  change B0412.realC (√(Axi.age R y) • (Axi.frameL y) (reM (gε_nonper (Axi.chart R τ y)))) +
      Complex.I • B0412.realC (√(Axi.age R y) • (Axi.frameL y) (imM (gε_nonper (Axi.chart R τ y)))) = 0
  rw [hz.1, hz.2, map_zero, smul_zero]
  ext i
  simp [B0412.realC]

theorem nvC_zero_eq_zero (R : ℝ) (x : ℝ × Space) :
    NvC R (0 : CProf) x = 0 := by
  have hz : reM ((0 : CProf) (Axi.chart R x.1 x.2)) = 0 ∧
      imM ((0 : CProf) (Axi.chart R x.1 x.2)) = 0 := by
    constructor <;> (ext i; simp [reM, imM])
  unfold NvC Axi.Nv
  change B0412.realC (√(Axi.age R x.2) • (Axi.frameL x.2) (reM ((0 : CProf) (Axi.chart R x.1 x.2)))) +
      Complex.I • B0412.realC (√(Axi.age R x.2) • (Axi.frameL x.2) (imM ((0 : CProf) (Axi.chart R x.1 x.2)))) = 0
  rw [hz.1, hz.2, map_zero, smul_zero]
  ext i
  simp [B0412.realC]

/-- `gε_nonper` satisfies `IsKOut p 0 gε_nonper` identically because `NvC p.R gε_nonper (τ, y) = 0`
for all `τ ∈ Ioc 0 p.period` (`τ > 0`), showing that `LocalInteractionComparison` requires
`InHr p.c bgp gε` (specifically `QPeriodic p.c gε` and `AEStronglyMeasurable gε (hMeas p.c bgp)`). -/
theorem isKOut_zero_gε_nonper (p : Params) : IsKOut p 0 gε_nonper := by
  intro Φ _hΦ
  unfold pairF phaseInt
  have hL : ∀ t : ℝ, (∫ y : Space, (PhaseSpace.dotL (convT p.raw Φ (t, y))) (NvC p.R 0 (t, y))) = 0 := by
    intro t
    have hpt : (fun y : Space => (PhaseSpace.dotL (convT p.raw Φ (t, y))) (NvC p.R 0 (t, y))) = 0 := by
      ext y
      rw [nvC_zero_eq_zero, map_zero]
      rfl
    rw [hpt]
    exact integral_zero _ _
  simp only [hL, integral_zero, smul_zero]
  symm
  have hR : ∀ t ∈ Ioc (0 : ℝ) p.period,
      (∫ y : Space, (PhaseSpace.dotL (Φ (t, y))) (NvC p.R gε_nonper (t, y))) = 0 := by
    intro t ht
    have hpt : (fun y : Space => (PhaseSpace.dotL (Φ (t, y))) (NvC p.R gε_nonper (t, y))) = 0 := by
      ext y
      rw [nvC_gε_nonper_eq_zero p.R_pos ht.1 y, map_zero]
      rfl
    rw [hpt]
    exact integral_zero _ _
  rw [setIntegral_congr_fun measurableSet_Ioc hR, integral_zero, smul_zero]

/-- The zero profile belongs to `InHr c r`. -/
theorem inHr_zero (c r : ℝ) : InHr c r 0 := by
  refine ⟨Filter.Eventually.of_forall (fun _ => rfl), aestronglyMeasurable_zero, ?_⟩
  simp [hNorm]

/-- The zero profile has weak derivative `0` along any `(v, d)`. -/
theorem hasWeakVec_zero (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) :
    HasWeakVec v d 0 0 := by
  intro i
  refine ⟨fun φ _ => ⟨by simp, by simp⟩, fun φ _ => by simp⟩

/-- The zero profile belongs to `InFlatClass c r`. -/
theorem inFlatClass_zero (c r : ℝ) : InFlatClass c r 0 := by
  have hsqrt0 : sqrtS 0 = 0 := by ext x i; simp [sqrtS]
  refine ⟨inHr_zero c r, ⟨0, 0, 0, hasWeakVec_zero vS dZero, hasWeakVec_zero vQ0 dZero,
    hasWeakVec_zero vEta dZero, inHr_zero c r, ?_, ?_⟩⟩ <;>
    rw [hsqrt0] <;> exact inHr_zero c r

/-- The zero profile is a flat response `IsFlatResponse ν μ 0 0`. -/
theorem isFlatResponse_zero (ν : ℝ) (μ : ℂ) : IsFlatResponse ν μ 0 0 := by
  refine ⟨fun φ _ => ⟨by simp, by simp⟩, fun Ψ _ => ?_⟩
  have hcdot : cdot 0 Ψ = 0 := by ext x; simp [cdot]
  rw [hcdot]
  refine ⟨by simp, integrable_zero _ _ _, by simp⟩

/-- `flatK tr 0 0 0 = 0`. -/
theorem flatK_zero {ν c : ℝ} (tr : B0140.TrainSol ν c) : flatK tr 0 0 0 = 0 := by
  ext x i
  simp [flatK]

/-- **Refutation of the un-periodic statement at `F = 0, bε = 0, b0 = 0`**:
For any `p : Params`, any `C, Γ : ℝ`, `k : ℕ`, and any cutoff `ϑ` with `ϑ x₀ ≠ 0` at a point `x₀`
in the left half-cell `x₀.1 ≤ 1 ∧ x₀.2.1 ≤ 0`, `gε_nonper` satisfies `IsKOut p 0 gε_nonper`,
`0` satisfies `InFlatClass p.c bgp 0`, `IsFlatResponse p.ν 0 0 0`, `HasWeakVec vQ0 dZero 0 0`,
and `HasWeakVec vEta dZero 0 0`, and the right-hand side
`ENNReal.ofReal (C * Γ ^ k * p.ε ^ (2 / 539 : ℝ)) * hNorm p.c bgp 0` is `0`, while
`(ϑ x₀ : ℂ) • (gε_nonper x₀ - flatK p.train 0 0 0 x₀) ≠ 0`. -/
theorem localInteractionComparison_counterexample_at_zero (p : Params)
    (C Γ : ℝ) (k : ℕ) (ϑ : Coord → ℝ) (x₀ : Coord)
    (hx₀ : x₀.1 ≤ 1 ∧ x₀.2.1 ≤ 0) (hϑ : ϑ x₀ ≠ 0) :
    IsKOut p 0 gε_nonper ∧
    InFlatClass p.c bgp 0 ∧
    IsFlatResponse p.ν 0 0 0 ∧
    HasWeakVec vQ0 dZero 0 0 ∧
    HasWeakVec vEta dZero 0 0 ∧
    ENNReal.ofReal (C * Γ ^ k * p.ε ^ (2 / 539 : ℝ)) * hNorm p.c bgp (0 : CProf) = 0 ∧
    (ϑ x₀ : ℂ) • (gε_nonper x₀ - flatK p.train 0 0 0 x₀) ≠ 0 := by
  refine ⟨isKOut_zero_gε_nonper p, inFlatClass_zero p.c bgp, isFlatResponse_zero p.ν 0,
    hasWeakVec_zero vQ0 dZero, hasWeakVec_zero vEta dZero, ?_, ?_⟩
  · simp [hNorm]
  · rw [flatK_zero, Pi.zero_apply, sub_zero]
    have hg : gε_nonper x₀ = WithLp.toLp 2 (fun _ => 1) := by
      simp [gε_nonper, hx₀.1, hx₀.2]
    rw [hg]
    intro hzero
    have h0 := congr_arg (fun v : CMerid => v 0) hzero
    simp only [PiLp.smul_apply, smul_eq_mul, mul_one,
      PiLp.zero_apply, Complex.ofReal_eq_zero] at h0
    exact hϑ h0

/-! ## Sub-task specifications (`PartII-b:T20/1`, `PartII-b:T20/2`) and corrected target -/

/-- **Leaf 1 (`PartII-b:T20/1`, `FlatKObsOpPackage`, SP 2019–2023)**:
On the observation box `obsBox σ H₁ L₁`, under `BgRegime p d dm dp` and `p.ν ≤ ν₀`, the cutoff
flat interaction `x ↦ (ϑ.ϑ x : ℂ) • flatK p.train b gq gη x` is realized by an
`ObsOp σ H₁ L₁ (C_B * Γ ^ k_B)`. -/
def FlatKObsOpPackage : Prop :=
  ∃ (k_B : ℕ) (C_B ν₀ : ℝ), 0 < C_B ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
    ∀ (Γ σ H₁ L₁ : ℝ), 1 ≤ Γ → p.ν ≤ Γ → p.ν⁻¹ ≤ Γ → σ⁻¹ ≤ Γ → H₁ ≤ Γ → L₁ ≤ Γ → 0 < σ →
    ∀ ϑ : ObsCut σ H₁ L₁ Γ,
      ∃ B : ObsOp σ H₁ L₁ (C_B * Γ ^ k_B),
        ∀ b gq gη : CProf, ∀ x : Coord,
          B.apply b gq gη x = (ϑ.ϑ x : ℂ) • flatK p.train b gq gη x

/-- **Leaf 2 (`PartII-b:T20/2`, `LocalInteractionRemainderBound`, SP 2024–2056)**:
On the observation box `obsBox σ H₁ L₁`, under `BgRegime p d dm dp`, `p.ν ≤ ν₀`, `p.period ≤ 1`,
and `InHr p.c bgp gε`, the `O(ε)` operator remainder
`ϑ(g_ε - flatK p.train b_ε gq_ε gη_ε) = ϑ s (B_ε - B_0) b_ε` is bounded in `H_p` by
`C_rem * Γ ^ k_rem * p.ε * ‖F‖_{H_p}`. -/
def LocalInteractionRemainderBound : Prop :=
  ∃ (k_rem : ℕ) (C_rem ν₀ : ℝ), 0 < C_rem ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.period ≤ 1 →
    ∀ (Γ σ H₁ L₁ : ℝ), 1 ≤ Γ → p.ν ≤ Γ → p.ν⁻¹ ≤ Γ → σ⁻¹ ≤ Γ → H₁ ≤ Γ → L₁ ≤ Γ → 0 < σ →
    ∀ ϑ : ObsCut σ H₁ L₁ Γ, ∀ F bε gε gqε gηε : CProf,
      InHr p.c bgp F → InHr p.c bgp bε → IsResponse p.ν p.c p.ε 0 bgp F bε →
      InHr p.c bgp gε → IsKOut p bε gε →
      HasWeakVec vQ0 dZero bε gqε → HasWeakVec vEta dZero bε gηε →
      hNorm p.c bgp (fun x => (ϑ.ϑ x : ℂ) • (gε x - flatK p.train bε gqε gηε x)) ≤
        ENNReal.ofReal (C_rem * Γ ^ k_rem * p.ε) * hNorm p.c bgp F

/-- Corrected statement of **Lemma `bg:local-interaction`** (SP 2006–2023), adding the small-viscosity
threshold `∃ ν₀ > 0, ... p.ν ≤ ν₀` (SP 255–258, matching `StrongLateCoeff`,
`YoungLateOperatorBounds`, and `WindowComparison`) and `InHr p.c bgp gε` (`c`-periodicity and
measurability of the physical output profile `gε`). -/
def LocalInteractionComparisonCorrected : Prop :=
  ∃ (k : ℕ) (C ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.period ≤ 1 →
    ∀ (Γ σ H₁ L₁ : ℝ), 1 ≤ Γ → p.ν ≤ Γ → p.ν⁻¹ ≤ Γ → σ⁻¹ ≤ Γ → H₁ ≤ Γ → L₁ ≤ Γ → 0 < σ →
    ∀ ϑ : ObsCut σ H₁ L₁ Γ, ∀ F bε b0 gε : CProf,
      InHr p.c bgp F → InHr p.c bgp bε → IsResponse p.ν p.c p.ε 0 bgp F bε →
      IsFlatResponse p.ν 0 F b0 → InFlatClass p.c bgp b0 →
      InHr p.c bgp gε → IsKOut p bε gε →
      ∃ gq gη : CProf, HasWeakVec vQ0 dZero b0 gq ∧ HasWeakVec vEta dZero b0 gη ∧
        hNorm p.c bgp (fun x => (ϑ.ϑ x : ℂ) • (gε x - flatK p.train b0 gq gη x)) ≤
          ENNReal.ofReal (C * Γ ^ k * p.ε ^ (2 / 539 : ℝ)) * hNorm p.c bgp F

/-! ## Conditional assembly -/

/-- Sum of two weak derivatives is a weak derivative of the sum. -/
theorem hasWeakVec_add {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {u1 u2 g1 g2 : CProf}
    (h1 : HasWeakVec v d u1 g1) (h2 : HasWeakVec v d u2 g2) :
    HasWeakVec v d (u1 + u2) (g1 + g2) := by
  intro i
  have hL : ∀ φ : Coord → ℝ,
      (fun x => (u1 + u2) x i * (coordTranspose v d φ x : ℂ)) =
        fun x => u1 x i * (coordTranspose v d φ x : ℂ) + u2 x i * (coordTranspose v d φ x : ℂ) := by
    intro φ; ext x; simp [Pi.add_apply, add_mul]
  have hR : ∀ φ : Coord → ℝ,
      (fun x => (g1 + g2) x i * (φ x : ℂ)) =
        fun x => g1 x i * (φ x : ℂ) + g2 x i * (φ x : ℂ) := by
    intro φ; ext x; simp [Pi.add_apply, add_mul]
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩
  · have hi1 := (h1 i).1 φ hφ
    have hi2 := (h2 i).1 φ hφ
    rw [hL φ, hR φ]
    exact ⟨hi1.1.add hi2.1, hi1.2.add hi2.2⟩
  · have hi1 := (h1 i).1 φ hφ
    have hi2 := (h2 i).1 φ hφ
    have he1 := (h1 i).2 φ hφ
    have he2 := (h2 i).2 φ hφ
    rw [hR φ, hL φ, MeasureTheory.integral_add hi1.2 hi2.2,
      MeasureTheory.integral_add hi1.1 hi2.1, he1, he2]

private theorem hNorm_add_bound {c : ℝ} {u v w F : CProf} {A₁ A₂ B₁ B₂ : ℝ}
    (hw : ∀ x, w x = u x + v x)
    (hu_m : AEStronglyMeasurable u (hMeas c bgp))
    (hv_m : AEStronglyMeasurable v (hMeas c bgp))
    (hu_bd : hNorm c bgp u ≤ ENNReal.ofReal A₁ * hNorm c bgp F)
    (hv_bd : hNorm c bgp v ≤ ENNReal.ofReal A₂ * hNorm c bgp F)
    (hB₁0 : 0 ≤ B₁) (hB₂0 : 0 ≤ B₂)
    (hA₁ : A₁ ≤ B₁) (hA₂ : A₂ ≤ B₂) :
    hNorm c bgp w ≤ ENNReal.ofReal (B₁ + B₂) * hNorm c bgp F := by
  have hw_eq : w = u + v := funext hw
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal bgp := by
    rw [ENNReal.one_le_ofReal]; unfold bgp; norm_num
  have htri : hNorm c bgp w ≤ hNorm c bgp u + hNorm c bgp v := by
    rw [hw_eq]
    exact eLpNorm_add_le hu_m hv_m hp1
  calc hNorm c bgp w
      ≤ hNorm c bgp u + hNorm c bgp v := htri
    _ ≤ ENNReal.ofReal A₁ * hNorm c bgp F + ENNReal.ofReal A₂ * hNorm c bgp F :=
        add_le_add hu_bd hv_bd
    _ ≤ ENNReal.ofReal B₁ * hNorm c bgp F + ENNReal.ofReal B₂ * hNorm c bgp F := by
        gcongr
    _ = ENNReal.ofReal (B₁ + B₂) * hNorm c bgp F := by
        rw [← add_mul, ← ENNReal.ofReal_add hB₁0 hB₂0]

/-- **Conditional assembly of `LocalInteractionComparisonCorrected`** from
`FlatKObsOpPackage` (`PartII-b:T20/1`), `LocalInteractionRemainderBound` (`PartII-b:T20/2`),
and `h19 : LpFreeComparison` (`PartII-b:T19`). -/
theorem localInteractionComparisonCorrected_of
    (hB : FlatKObsOpPackage) (hrem : LocalInteractionRemainderBound)
    (h19 : UnforcedLeray.Short.IIb.LpFreeComparison) :
    LocalInteractionComparisonCorrected := by
  obtain ⟨k_B, C_B, νB, hCB0, hνB0, hB_pkg⟩ := hB
  obtain ⟨k_rem, C_rem, νR, hCrem0, hνR0, hrem_bd⟩ := hrem
  obtain ⟨k_19, C_19, hC19_0, h19_rate⟩ := h19
  have hMB_pos : 0 < C_B + 46 := by linarith
  refine ⟨max k_B 2 * k_19 + k_rem, C_19 * (C_B + 46) ^ k_19 + C_rem, min νB νR,
    by positivity, lt_min hνB0 hνR0, ?_⟩
  intro p d dm dp hbg hν_le hper Γ σ H₁ L₁ hΓ1 hν hνi hσi hH₁ hL₁ hσ0 ϑ
    F bε b0 gε hF hbε_in hbε_resp hb0_resp hb0_class hgε_in hgε
  have hνB : p.ν ≤ νB := hν_le.trans (min_le_left _ _)
  have hνR : p.ν ≤ νR := hν_le.trans (min_le_right _ _)
  obtain ⟨Sb0, gq0, gη0, _, hgq0, hgη0, _, _, _⟩ := hb0_class.deriv
  obtain ⟨B_flat, hB_apply⟩ :=
    hB_pkg p d dm dp hbg hνB Γ σ H₁ L₁ hΓ1 hν hνi hσi hH₁ hL₁ hσ0 ϑ
  have hΓm1 : 1 ≤ Γ ^ max k_B 2 := one_le_pow₀ hΓ1
  have hΓ_le_Γm : Γ ≤ Γ ^ max k_B 2 := by
    calc Γ = Γ ^ 1 := (pow_one Γ).symm
      _ ≤ Γ ^ max k_B 2 := pow_le_pow_right₀ hΓ1 (by omega)
  have hΓ2_le_Γm : Γ ^ 2 ≤ Γ ^ max k_B 2 :=
    pow_le_pow_right₀ hΓ1 (le_max_right k_B 2)
  have hΓkB_le_Γm : Γ ^ k_B ≤ Γ ^ max k_B 2 :=
    pow_le_pow_right₀ hΓ1 (le_max_left k_B 2)
  have hΓ_le_Γ₁ : Γ ≤ (C_B + 46) * Γ ^ max k_B 2 := by nlinarith
  have hΓ2_le_Γ₁ : Γ ^ 2 ≤ (C_B + 46) * Γ ^ max k_B 2 := by nlinarith
  have hCB_le_Γ₁ : C_B * Γ ^ k_B ≤ (C_B + 46) * Γ ^ max k_B 2 :=
    mul_le_mul (by linarith) hΓkB_le_Γm (by positivity) hMB_pos.le
  have hΓ₁_46 : 46 ≤ (C_B + 46) * Γ ^ max k_B 2 := by nlinarith
  have hΓ₁_1 : 1 ≤ (C_B + 46) * Γ ^ max k_B 2 := by linarith
  have hν_1 : p.ν ≤ (C_B + 46) * Γ ^ max k_B 2 := hν.trans hΓ_le_Γ₁
  have hνi_1 : p.ν⁻¹ ≤ (C_B + 46) * Γ ^ max k_B 2 := hνi.trans hΓ_le_Γ₁
  have hc_1 : p.c ≤ (C_B + 46) * Γ ^ max k_B 2 := (bgRegime_c_le hbg hΓ1 hνi).trans hΓ2_le_Γ₁
  have hci_1 : p.c⁻¹ ≤ (C_B + 46) * Γ ^ max k_B 2 := (bgRegime_c_inv_le hbg hΓ1 hν).trans hΓ2_le_Γ₁
  have hσi_1 : σ⁻¹ ≤ (C_B + 46) * Γ ^ max k_B 2 := hσi.trans hΓ_le_Γ₁
  have hH₁_1 : H₁ ≤ (C_B + 46) * Γ ^ max k_B 2 := hH₁.trans hΓ_le_Γ₁
  have hL₁_1 : L₁ ≤ (C_B + 46) * Γ ^ max k_B 2 := hL₁.trans hΓ_le_Γ₁
  have hμ_1 : ‖(0 : ℂ)‖ ≤ (C_B + 46) * Γ ^ max k_B 2 := by simp; linarith
  have hgap_1 : ((C_B + 46) * Γ ^ max k_B 2)⁻¹ ≤ (0 : ℂ).re + 1 / 46 := by
    rw [Complex.zero_re, zero_add, one_div]
    exact inv_anti₀ (by norm_num) hΓ₁_46
  have hε1 : p.ε ≤ 1 := bgRegime_eps_le_one hbg
  obtain ⟨gq_diff, gη_diff, hgq_diff, hgη_diff, hbd_19⟩ :=
    h19_rate ((C_B + 46) * Γ ^ max k_B 2) p.ν p.c σ H₁ L₁ 0 hΓ₁_1 hν_1 hνi_1 hc_1 hci_1
      hσi_1 hH₁_1 hL₁_1 hμ_1 hgap_1 p.ν_pos p.c_pos hσ0 (B_flat.mono hCB_le_Γ₁)
      p.ε p.ε_pos hε1 hper F bε b0 hF hbε_in hbε_resp hb0_resp hb0_class
  rw [ObsOp.mono_apply] at hbd_19
  have hbε_eq : bε - b0 + b0 = bε := sub_add_cancel bε b0
  have hgqε : HasWeakVec vQ0 dZero bε (gq_diff + gq0) := by
    rw [← hbε_eq]
    exact hasWeakVec_add hgq_diff hgq0
  have hgηε : HasWeakVec vEta dZero bε (gη_diff + gη0) := by
    rw [← hbε_eq]
    exact hasWeakVec_add hgη_diff hgη0
  have hbd_rem :=
    hrem_bd p d dm dp hbg hνR hper Γ σ H₁ L₁ hΓ1 hν hνi hσi hH₁ hL₁ hσ0 ϑ
      F bε gε (gq_diff + gq0) (gη_diff + gη0) hF hbε_in hbε_resp hgε_in hgε hgqε hgηε
  have hB_meas : AEStronglyMeasurable (B_flat.apply (bε - b0) gq_diff gη_diff) (hMeas p.c bgp) :=
    B_flat.aestronglyMeasurable_apply
      (hbε_in.meas.sub hb0_class.inHr.meas)
      hgq_diff.aestronglyMeasurable_hMeas
      hgη_diff.aestronglyMeasurable_hMeas
  have hrem_meas : AEStronglyMeasurable
      (fun x => (ϑ.ϑ x : ℂ) • (gε x - flatK p.train bε (gq_diff + gq0) (gη_diff + gη0) x))
      (hMeas p.c bgp) := by
    have hϑ_meas : AEStronglyMeasurable (fun x : Coord => (ϑ.ϑ x : ℂ)) (hMeas p.c bgp) :=
      (Complex.continuous_ofReal.comp ϑ.smooth.continuous).aestronglyMeasurable
    have hBε_meas : AEStronglyMeasurable
        (B_flat.apply bε (gq_diff + gq0) (gη_diff + gη0)) (hMeas p.c bgp) :=
      B_flat.aestronglyMeasurable_apply hbε_in.meas
        hgqε.aestronglyMeasurable_hMeas hgηε.aestronglyMeasurable_hMeas
    have hrem_eq :
        (fun x => (ϑ.ϑ x : ℂ) • (gε x - flatK p.train bε (gq_diff + gq0) (gη_diff + gη0) x)) =
          (fun x => (ϑ.ϑ x : ℂ) • gε x) - B_flat.apply bε (gq_diff + gq0) (gη_diff + gη0) := by
      ext x i
      simp [hB_apply, smul_sub]
    rw [hrem_eq]
    exact (hϑ_meas.smul hgε_in.meas).sub hBε_meas
  refine ⟨gq0, gη0, hgq0, hgη0, ?_⟩
  have hw_pt : ∀ x : Coord,
      (ϑ.ϑ x : ℂ) • (gε x - flatK p.train b0 gq0 gη0 x) =
        B_flat.apply (bε - b0) gq_diff gη_diff x +
          (ϑ.ϑ x : ℂ) • (gε x - flatK p.train bε (gq_diff + gq0) (gη_diff + gη0) x) := by
    intro x
    rw [hB_apply (bε - b0) gq_diff gη_diff x]
    exact localInteraction_split p.train ϑ.ϑ gε bε b0 gq_diff gη_diff gq0 gη0 x
  have h19_le : C_19 * ((C_B + 46) * Γ ^ max k_B 2) ^ k_19 * p.ε ^ (2 / 539 : ℝ) ≤
      (C_19 * (C_B + 46) ^ k_19) * Γ ^ (max k_B 2 * k_19 + k_rem) * p.ε ^ (2 / 539 : ℝ) := by
    rw [mul_pow, ← pow_mul]
    have hpow : Γ ^ (max k_B 2 * k_19) ≤ Γ ^ (max k_B 2 * k_19 + k_rem) :=
      pow_le_pow_right₀ hΓ1 (Nat.le_add_right (max k_B 2 * k_19) k_rem)
    have h1 : C_19 * ((C_B + 46) ^ k_19 * Γ ^ (max k_B 2 * k_19)) ≤
        (C_19 * (C_B + 46) ^ k_19) * Γ ^ (max k_B 2 * k_19 + k_rem) := by
      calc C_19 * ((C_B + 46) ^ k_19 * Γ ^ (max k_B 2 * k_19))
          = (C_19 * (C_B + 46) ^ k_19) * Γ ^ (max k_B 2 * k_19) := by ring
        _ ≤ (C_19 * (C_B + 46) ^ k_19) * Γ ^ (max k_B 2 * k_19 + k_rem) := by gcongr
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg p.ε_pos.le _)
  have hrem_le : C_rem * Γ ^ k_rem * p.ε ≤
      C_rem * Γ ^ (max k_B 2 * k_19 + k_rem) * p.ε ^ (2 / 539 : ℝ) := by
    have hpow : Γ ^ k_rem ≤ Γ ^ (max k_B 2 * k_19 + k_rem) :=
      pow_le_pow_right₀ hΓ1 (Nat.le_add_left k_rem (max k_B 2 * k_19))
    have heps : p.ε ≤ p.ε ^ (2 / 539 : ℝ) := eps_le_rpow_539 p.ε_pos.le hε1
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hCrem0.le) heps p.ε_pos.le (by positivity)
  have hε0 : 0 < p.ε := p.ε_pos
  have hcomb := hNorm_add_bound hw_pt hB_meas hrem_meas
    hbd_19 hbd_rem (by positivity) (by positivity) h19_le hrem_le
  convert hcomb using 3
  ring

end UnforcedLeray.Short.IIb

end
