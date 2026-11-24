import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_2_3_2
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.FluxDuhamel.CellInt
import UnforcedLeray.Lib.Kernels.PlanarBS.P.Infra.ConvMinkowski.Minkowski

/-!
# `PartIII-a:T19/2/3/2/3`: decomposition of `CoreDuhamelFromClock` (SP 3481-3496)

`CoreDuhamelFromClock` is split into two analytic leaves and a measure-theoretic assembly
(`coreDuhamelFromClock_of`, compiled here):

* (i) `CoreDuhamelRep` (SP 3481-3491, "define using only forward propagation"): for a.e. age `s`
  the perturbation vorticity is the forward Duhamel superposition
  `ω(s) = ∫_0^s k_t dt`, `k_t = (t/s)^μ (g(t)/g(s)) U(s,t) f(t)`, each piece in `X_{9,c}` with
  zero circulation and the weak-forward clock bound extended (by density) to the weak source
  `f(t) = -curl a(t) ∈ Z^{-1}_{9,c}`:
  `‖k_t‖_{X_9} ≤ |C| ν^{-M} (t/s)^{Re μ} (1 + (s-t)^{-1/2}) ‖f(t)‖_{Z^{-1}_9}`.
  This is the Duhamel identification (uniqueness of the zero-entrance weak solution of
  `CoreVortWeakEqAt`) plus the density extension of `ClockBoundAt`.
* (ii) `CoreSourceFinite` (SP 3481-3488, the Hardy inequality `eq:short-causal-hardy` with the free
  energy bounds of `freeCausalExistsUnique`): the right side of the bound is finite for a.e. `s`.
* Assembly: Minkowski's integral inequality in `X_{9,c}` (`PlanarBS.Conv.eLpNorm_integral_le`),
  the embedding `X_{9,c} ⊂ L¹(cell)` (`∫_cell ⟨x⟩^{-18} < ∞`) and Fubini for the circulation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The kernel `|C| ν^{-M} (t/s)^{Re μ} (1 + (s-t)^{-1/2})` of `CoreVortConclusionAt`. -/
def vortKernel (C_clock : ℝ) (P : PlanarData) (ν : ℝ) (μ : ℂ) (s t : ℝ) : ℝ :=
  |C_clock| * ν ^ (-(weakDegree 9 P.kappa : ℝ)) * (t / s) ^ μ.re * (1 + (s - t) ^ (-1 / 2 : ℝ))

/-- **Leaf (i) `CoreDuhamelRep`** (SP 3481-3491): forward Duhamel representation of the
perturbation vorticity, with the weak-forward clock bound for each propagated source. -/
def CoreDuhamelRep : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ K : Set ℂ, IsAdmissibleK K →
    ∀ b : ℝ, 1 ≤ b → ∃ ν₁ : ℝ, 0 < ν₁ ∧
      ∀ ν ∈ Ioc 0 ν₁, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        ∀ μ : ℂ, ∀ A_m C_clock : ℝ, ClockBoundAt P 9 b C_clock ν tr →
          ∀ F b₀ G₀ b_sol G_sol, VortData P K b ν tr μ A_m F b₀ G₀ b_sol G_sol →
            CoreVortWeakEqAt P b ν tr μ b₀ G₀ b_sol G_sol →
            ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) (coreEnd ν b) →
              ∃ k : ℝ → ℝ × ℝ → ℂ, Measurable (Function.uncurry k) ∧
                (∀ᵐ t ∂volume, t ∈ Ioo 0 s →
                  MemLp (k t) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9) ∧
                  HasZeroCirculation (ν ^ (-2 : ℝ)) (k t) ∧
                  xNorm (ν ^ (-2 : ℝ)) 9 (k t) ≤
                    ENNReal.ofReal (vortKernel C_clock P ν μ s t) *
                      coreSrcNorm (ν ^ (-2 : ℝ)) 9 (coreAdvSlice P.eigenvalue.re tr b₀ G₀ t)) ∧
                corePerturbVort P.eigenvalue.re ν G₀ G_sol s
                  =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
                    fun x => ∫ t in Ioo 0 s, k t x

/-- **Leaf (ii) `CoreSourceFinite`** (SP 3481-3488): the Duhamel bound is finite for a.e. age
(Hardy inequality with the free bounds `‖g⁻¹b₀‖_𝓗, ‖∇(g⁻¹b₀)‖_𝒯 < ∞`). -/
def CoreSourceFinite : Prop :=
  ∀ C_dual : ℝ, 0 ≤ C_dual →
  ∀ P : PlanarData, IsPlanarReference P → ∀ K : Set ℂ, IsAdmissibleK K →
    ∀ b : ℝ, 1 ≤ b → ∃ ν₂ : ℝ, 0 < ν₂ ∧
      ∀ ν ∈ Ioc 0 ν₂, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        ∀ μ : ℂ, ∀ A_m C_clock : ℝ,
          ∀ F b₀ G₀ b_sol G_sol, VortData P K b ν tr μ A_m F b₀ G₀ b_sol G_sol →
            ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) (coreEnd ν b) →
              ∫⁻ t in Ioo (0 : ℝ) s,
                ENNReal.ofReal (vortKernel C_clock P ν μ s t) *
                  (ENNReal.ofReal (C_dual * A_m) *
                    (unnormSliceVel (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b₀) t +
                      unnormSliceGrad (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G₀) t)) < ⊤

namespace V3

instance sigmaFinite_cellMeasure' (c m : ℝ) : SigmaFinite (B0579.cellMeasure c m) := by
  unfold B0579.cellMeasure; infer_instance

/-- `X_{9,c} ⊂ L¹(cell)`: `∫_cell |f| ≤ ‖f‖_{X_9} (∫_cell ⟨x⟩^{-18})^{1/2}`. -/
theorem lint_cell_le {c : ℝ} {f : ℝ × ℝ → ℂ} (hf : AEMeasurable f (B0579.cellMeasure c 9)) :
    ∫⁻ x in B0579.cell c, ‖f x‖ₑ ≤
      xNorm c 9 f * (∫⁻ x in B0579.cell c, ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ))) ^ (1 / 2 : ℝ) := by
  have hd : Measurable fun x => (B0579.density 9 x : ℝ≥0∞) :=
    (B0579.measurable_density 9).coe_nnreal_ennreal
  have hw : Measurable fun x : ℝ × ℝ => ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ)) :=
    ENNReal.measurable_ofReal.comp ((B0579.continuous_jb_rpow _).measurable)
  have hjb : ∀ x : ℝ × ℝ, B0579.jb x ^ (9 : ℝ) * B0579.jb x ^ (-9 : ℝ) = 1 := fun x => by
    rw [B0579.jb_rpow_mul]; simp
  have h1 : ∫⁻ x in B0579.cell c, ‖f x‖ₑ =
      ∫⁻ x, ‖f x‖ₑ * ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ)) ∂(B0579.cellMeasure c 9) := by
    unfold B0579.cellMeasure
    rw [lintegral_withDensity_eq_lintegral_mul₀
      (g := fun x => ‖f x‖ₑ * ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ))) hd.aemeasurable
      ((hf.mono_ac (B0579.ac_cellMeasure c 9)).enorm.mul hw.aemeasurable)]
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply]
    have : (B0579.density 9 x : ℝ≥0∞) = ENNReal.ofReal (B0579.jb x ^ (9 : ℝ)) := rfl
    rw [this, mul_comm (‖f x‖ₑ), ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (B0579.jb_pos x).le _), hjb,
      ENNReal.ofReal_one, one_mul]
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq (B0579.cellMeasure c 9) Real.HolderConjugate.two_two
    hf.enorm hw.aemeasurable
  have h3 : ∫⁻ x, ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ)) ^ (2 : ℝ) ∂(B0579.cellMeasure c 9) =
      ∫⁻ x in B0579.cell c, ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ)) := by
    unfold B0579.cellMeasure
    rw [lintegral_withDensity_eq_lintegral_mul _ hd (hw.pow_const _)]
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply]
    have : (B0579.density 9 x : ℝ≥0∞) = ENNReal.ofReal (B0579.jb x ^ (9 : ℝ)) := rfl
    rw [this, ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (by norm_num),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (B0579.jb_pos x).le _)]
    congr 1
    rw [← Real.rpow_mul (B0579.jb_pos x).le, B0579.jb_rpow_mul]
    norm_num
  have h4 : xNorm c 9 f = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure c 9)) ^ (1 / 2 : ℝ) := by
    rw [xNorm, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    norm_num
  rw [h1, h4, ← h3]
  exact h2

theorem lint_jb_cell_lt_top (c : ℝ) :
    ∫⁻ x in B0579.cell c, ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ)) < ⊤ :=
  (UnforcedLeray.Short.IIIa.Exist.integrableOn_jb_rpow_neg_cell (c := c) 9 (by norm_num)).lintegral_lt_top

end V3

/-- **Assembly**: the two leaves give `CoreDuhamelFromClock` (SP 3481-3496). -/
theorem coreDuhamelFromClock_of (hA : CoreDuhamelRep) (hB : CoreSourceFinite) :
    CoreDuhamelFromClock := by
  intro C_dual hC P hP K hK b hb
  obtain ⟨ν₁, hν₁, hA'⟩ := hA P hP K hK b hb
  obtain ⟨ν₂, hν₂, hB'⟩ := hB C_dual hC P hP K hK b hb
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun ν hν tr μ A_m C_clock hclock F b₀ G₀ b_sol G_sol hd
    hweak hsrc => ?_⟩
  have hA'' := hA' ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩ tr μ A_m C_clock hclock F b₀ G₀ b_sol
    G_sol hd hweak
  have hB'' := hB' ν ⟨hν.1, hν.2.trans (min_le_right _ _)⟩ tr μ A_m C_clock F b₀ G₀ b_sol G_sol hd
  set H := coreEnd ν b with hH
  set μ9 := B0579.cellMeasure (ν ^ (-2 : ℝ)) 9 with hμ9
  set RHS : ℝ → ℝ≥0∞ := fun s => ∫⁻ t in Ioo (0 : ℝ) s,
    ENNReal.ofReal (vortKernel C_clock P ν μ s t) *
      (ENNReal.ofReal (C_dual * A_m) *
        (unnormSliceVel (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b₀) t +
          unnormSliceGrad (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G₀) t)) with hRHS
  have hmeasG : ∀ i j, Measurable fun p => corePerturbGrad P.eigenvalue.re ν G₀ G_sol p i j :=
    measurable_corePerturbGrad _ _ hd.2.2.2.2.2.2.2.1.gradMeasurable
      hd.2.2.2.2.2.2.2.2.gradMeasurable
  filter_upwards [hA'', hB''] with s hsA hsB hsT
  obtain ⟨k, hkm, hkb, hrep⟩ := hsA hsT
  have hfin : RHS s < ⊤ := hsB hsT
  have hs : 0 < s := hsT.1
  set om := corePerturbVort P.eigenvalue.re ν G₀ G_sol s with hom
  have homm : Measurable om := by
    simp only [hom]
    unfold corePerturbVort
    exact ((hmeasG 1 0).comp measurable_prodMk_left).sub ((hmeasG 0 1).comp measurable_prodMk_left)
  -- the bound for each piece, integrated
  have hX : ∫⁻ t in Ioo (0 : ℝ) s, xNorm (ν ^ (-2 : ℝ)) 9 (k t) ≤ RHS s := by
    refine setLIntegral_mono_ae' measurableSet_Ioo ?_
    have hsrc' : ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) s →
        coreSrcNorm (ν ^ (-2 : ℝ)) 9 (coreAdvSlice P.eigenvalue.re tr b₀ G₀ t) ≤
          ENNReal.ofReal (C_dual * A_m) *
            (unnormSliceVel (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b₀) t +
              unnormSliceGrad (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G₀) t) := by
      filter_upwards [hsrc] with t ht hts
      exact ht ⟨hts.1, hts.2.trans hsT.2⟩
    filter_upwards [hkb, hsrc'] with t h1 h2 hts
    exact (h1 hts).2.2.trans (mul_le_mul' le_rfl (h2 hts))
  -- Minkowski
  have hkm' : AEStronglyMeasurable (Function.uncurry fun (x : ℝ × ℝ) (t : ℝ) => k t x)
      (μ9.prod (volume.restrict (Ioo (0 : ℝ) s))) :=
    (hkm.comp measurable_swap).aestronglyMeasurable
  have hmink := UnforcedLeray.PlanarBS.Conv.eLpNorm_integral_le (μ := μ9)
    (ν := volume.restrict (Ioo (0 : ℝ) s)) hkm' (p := 2) (by norm_num) (by norm_num)
  have hrep9 : om =ᵐ[μ9] fun x => ∫ t in Ioo 0 s, k t x := (B0579.cellMeasure_ac (ν ^ (-2 : ℝ)) 9).ae_le hrep
  have hbound : xNorm (ν ^ (-2 : ℝ)) 9 om ≤ RHS s := by
    calc xNorm (ν ^ (-2 : ℝ)) 9 om = eLpNorm (fun x => ∫ t in Ioo 0 s, k t x) 2 μ9 := by
          rw [xNorm]; exact eLpNorm_congr_ae hrep9
      _ ≤ ∫⁻ t in Ioo (0 : ℝ) s, eLpNorm (k t) 2 μ9 := hmink
      _ = ∫⁻ t in Ioo (0 : ℝ) s, xNorm (ν ^ (-2 : ℝ)) 9 (k t) := rfl
      _ ≤ RHS s := hX
  have hmem : MemLp om 2 μ9 := ⟨homm.aestronglyMeasurable, lt_of_le_of_lt hbound hfin⟩
  -- zero circulation
  have hL1 : ∫⁻ t in Ioo (0 : ℝ) s, ∫⁻ x in B0579.cell (ν ^ (-2 : ℝ)), ‖k t x‖ₑ < ⊤ := by
    have hk_t : ∀ t, AEMeasurable (k t) μ9 := fun t =>
      (hkm.comp (measurable_const.prodMk measurable_id)).aemeasurable
    calc ∫⁻ t in Ioo (0 : ℝ) s, ∫⁻ x in B0579.cell (ν ^ (-2 : ℝ)), ‖k t x‖ₑ
        ≤ ∫⁻ t in Ioo (0 : ℝ) s, xNorm (ν ^ (-2 : ℝ)) 9 (k t) *
            (∫⁻ x in B0579.cell (ν ^ (-2 : ℝ)), ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ))) ^ (1 / 2 : ℝ) :=
          lintegral_mono fun t => V3.lint_cell_le (hk_t t)
      _ = (∫⁻ t in Ioo (0 : ℝ) s, xNorm (ν ^ (-2 : ℝ)) 9 (k t)) *
            (∫⁻ x in B0579.cell (ν ^ (-2 : ℝ)), ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ))) ^ (1 / 2 : ℝ) :=
          lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
            (V3.lint_jb_cell_lt_top (ν ^ (-2 : ℝ))).ne)
      _ < ⊤ := ENNReal.mul_lt_top (lt_of_le_of_lt hX hfin)
          (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (V3.lint_jb_cell_lt_top (ν ^ (-2 : ℝ))).ne)
  have hint : Integrable (Function.uncurry k)
      ((volume.restrict (Ioo (0 : ℝ) s)).prod (volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))) := by
    refine ⟨hkm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod _ hkm.enorm.aemeasurable]
    exact hL1
  have homint : IntegrableOn om (B0579.cell (ν ^ (-2 : ℝ))) := by
    refine Integrable.congr hint.integral_prod_right ?_
    exact hrep.symm
  have homzero : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), om x = 0 := by
    rw [integral_congr_ae hrep, integral_integral_swap (f := fun x t => k t x) hint.swap]
    · refine (integral_congr_ae ?_).trans (integral_zero _ _)
      rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hkb] with t ht hts
      exact (ht hts).2.1.2
  exact ⟨hmem, ⟨homint, homzero⟩, hbound⟩

end UnforcedLeray.Short.IIIa

end
