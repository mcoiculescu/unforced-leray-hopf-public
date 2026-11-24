import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity3.Leaves
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity1
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity2
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FluxPath.TrainBoundsSmall
import UnforcedLeray.Short.PartIIIa.Sub.T23_4_6_Uniform
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrTrainClose
import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCirc.CellIntegrable
import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCirc.CutoffTest
import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCirc.ChiDeriv
import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCirc.BandL2
import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCirc.CauchySchwarz
import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCirc.CutoffLimit
import UnforcedLeray.Short.PartIIIa.T20_2_BiotSavartUnique

/-!
# `PartIII-a:T19/2/3/2/3/1`: decomposition of `CoreDuhamelRep` (SP 3427-3440, 3481-3496, 3541-3545)

Source of record: `the November 2 reference manuscript` (SP), lines 3427-3440,
3481-3496, 3518-3527, and 3541-3545.

`CoreDuhamelRep` (`Vorticity3/Leaves.lean:41`) is split per spec into two leaves, assembled here by
`coreDuhamelRep_of`:

* (i) `CoreDuhamelNice` (`PartIII-a:T19/2/3/2/3/1/1`, SP 3427-3440, 3481-3491, 3541-3545):
  for a nice force `NiceForce (ν ^ (-2 : ℝ)) F`, the weak advection-stretching source
  `coreSrcFun (coreAdvSlice ... b₀ G₀ t)` is represented for a.e. `t ∈ (0, H)` by an `X_{9,c}^0`
  density `f t`, and for a.e. `s ∈ (0, H)` the gain-conjugated perturbation vorticity
  `corePerturbVort ... G₀ G_sol s` equals the forward Duhamel integral `∫_0^s k t x dt` of a
  jointly measurable kernel `k` whose `t`-slices agree a.e. on `B0579.cell c` with
  `(t/s)^μ (g(t)/g(s)) w_t(s)` for a weak linearised flow `(w_t, u_t)` starting from `f t`.
* (ii) `CoreDuhamelDensity` (`PartIII-a:T19/2/3/2/3/1/2`, SP 3427-3440, 3481-3496, 3518-3527):
  passage to the `Z^{-1}_{9,c}` density limit along a geometrically converging (`≤ 2^{-n}`)
  sequence of nice forces, given both single-`n` and pairwise Cauchy `X_{9,c}` bounds on the
  approximating Duhamel kernels.

Proved unconditionally in `CoreDuhamelRepSub`:
* `fullFlowExists_core`: existence of `FullFlowExists ν (ν ^ (-2 : ℝ)) 9 tr` for small `ν` and BUC
  trains (`Exist.fullFlowExistsSmall`, `Exist.trainBoundsSmall_of`, `trainTransverseTailsUniform_of`);
* `hasZeroCirculation_of_isLinearisedFlow` and `isLinearisedFlow_sub`: preservation of zero
  circulation and linearity of `IsLinearisedFlow` under subtraction;
* `negNorm_eq_coreSrcNorm`, `negNorm_sub_eq_coreSrcNorm`, and `duhamelPiece_bounds`: deduction of
  both single-`n` and pairwise `(n, m)` `X_{9,c}` bounds from `ClockBoundAt`;
* `niceApproxSeq_exists` and `coreDuhamelRep_of`: geometric `NiceForceApprox` extraction, nice/train
  solution pairing, and complete assembly of `CoreDuhamelRep`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace CoreDuhamelRepSub

/-! ## 1. Existence of `FullFlowExists` for BUC trains at small `ν` -/

theorem fullFlowExists_core :
    ∃ ν_flow : ℝ, 0 < ν_flow ∧ ∀ ν ∈ Ioc 0 ν_flow,
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        FullFlowExists ν (ν ^ (-2 : ℝ)) 9 tr := by
  have hTails : UnforcedLeray.Short.PartI.TrainTransverseTails :=
    trainTransverseTails_of_parts
      UnforcedLeray.Short.PartI.overlap_fluctuation_decay
      UnforcedLeray.Short.PartI.overlap_mean_primitive
      UnforcedLeray.Short.PartI.overlap_mean_decay
      UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail
      UnforcedLeray.Short.PartI.train_stream_velocity_pressure_tails
  obtain ⟨ν_tb, hν_tb, hTB⟩ :=
    Exist.trainBoundsSmall_of (trainTransverseTailsUniform_of hTails) 9 (by norm_num)
  refine ⟨min ν_tb 1, lt_min hν_tb one_pos, fun ν hν tr htr => ?_⟩
  exact Exist.fullFlowExistsSmall 9 (by norm_num) ν hν.1 (hν.2.trans (min_le_right _ _)) tr
    (hTB ν hν.1 (hν.2.trans (min_le_left _ _)) tr htr)

/-! ## 2. Zero circulation and subtraction of `IsLinearisedFlow` -/

theorem hasZeroCirculation_of_isLinearisedFlow {ν c : ℝ} (hc : 0 < c)
    {tr : UnforcedLeray.B0140.TrainSol ν c} {t s : ℝ} (hts : t ≤ s)
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν c 9 tr t f w u) :
    HasZeroCirculation c (w s) := by
  have hint := zcCellIntegrable c 9 (by norm_num) (w s) (hw.memX s hts)
  exact ⟨hint, integral_cell_eq_zero_of_isBiotSavart_of zcCutoffTest zcChiDeriv zcBandL2
    zcCauchySchwarz zcCutoffLimit hc hint (hw.biotSavart s hts)⟩

theorem memLp_unweighted_of_memX {c : ℝ} {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (B0579.cellMeasure c 9)) :
    MemLp f 2 (volume.restrict (B0579.cell c)) := by
  refine ⟨hf.1.mono_ac (B0579.ac_cellMeasure c 9), ?_⟩
  have hlt := hf.2
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top] at hlt ⊢
  have hd : Measurable fun x => (B0579.density 9 x : ℝ≥0∞) :=
    (B0579.measurable_density 9).coe_nnreal_ennreal
  have hfm : AEMeasurable (fun x => ‖f x‖ₑ ^ ENNReal.toReal 2)
      (volume.restrict (B0579.cell c)) :=
    ((hf.1.mono_ac (B0579.ac_cellMeasure c 9)).enorm.pow_const _)
  unfold B0579.cellMeasure at hlt
  rw [lintegral_withDensity_eq_lintegral_mul₀ hd.aemeasurable hfm] at hlt
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hlt
  have hjb1 : 1 ≤ B0579.jb x := by
    unfold B0579.jb
    nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  have hd1 : (1 : ℝ≥0∞) ≤ (B0579.density 9 x : ℝ≥0∞) := by
    change (1 : ℝ≥0∞) ≤ ENNReal.ofReal (B0579.jb x ^ (9 : ℝ))
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow hjb1 (by norm_num))
  simpa only [Pi.mul_apply, one_mul] using
    mul_le_mul_of_nonneg_right hd1 (bot_le : (0 : ℝ≥0∞) ≤ ‖f x‖ₑ ^ ENNReal.toReal 2)

theorem integrableOn_cylTest_mul {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ)
    {g : ℝ × ℝ → ℂ} (hg : MemLp g 2 (volume.restrict (B0579.cell c))) :
    IntegrableOn (fun x => g x * (φ x : ℂ)) (B0579.cell c) := by
  have hg' : MemLp g 2 (UnforcedLeray.Cyl.cellμ c) := by
    rwa [CTE.T20_2.cellμ_eq_B0579]
  have h := CTE.T20_2.integrableOn_test_mul_C (CTE.T20_2.sob_of_B0579 hφ) hg'
  rwa [← CTE.T20_2.cell_eq] at h

theorem isBiotSavart_sub {c : ℝ} {ω₁ ω₂ : ℝ × ℝ → ℂ}
    {u₁ u₂ : ℝ × ℝ → Fin 2 → ℂ}
    (hω₁ : MemLp ω₁ 2 (B0579.cellMeasure c 9))
    (hω₂ : MemLp ω₂ 2 (B0579.cellMeasure c 9))
    (h₁ : IsBiotSavart c ω₁ u₁) (h₂ : IsBiotSavart c ω₂ u₂) :
    IsBiotSavart c (fun x => ω₁ x - ω₂ x) (fun x j => u₁ x j - u₂ x j) := by
  refine ⟨fun j => (h₁.1 j).sub (h₂.1 j), fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · have I0 := integrableOn_cylTest_mul (hψ.pd 0) (h₁.1 0)
    have I1 := integrableOn_cylTest_mul (hψ.pd 1) (h₁.1 1)
    have J0 := integrableOn_cylTest_mul (hψ.pd 0) (h₂.1 0)
    have J1 := integrableOn_cylTest_mul (hψ.pd 1) (h₂.1 1)
    have I01 : IntegrableOn
        (fun x => u₁ x 0 * (B0579.pd 0 ψ x : ℂ) + u₁ x 1 * (B0579.pd 1 ψ x : ℂ))
        (B0579.cell c) := I0.add I1
    have J01 : IntegrableOn
        (fun x => u₂ x 0 * (B0579.pd 0 ψ x : ℂ) + u₂ x 1 * (B0579.pd 1 ψ x : ℂ))
        (B0579.cell c) := J0.add J1
    have heq : (fun x => (u₁ x 0 - u₂ x 0) * (B0579.pd 0 ψ x : ℂ) +
          (u₁ x 1 - u₂ x 1) * (B0579.pd 1 ψ x : ℂ)) =
        fun x => (u₁ x 0 * (B0579.pd 0 ψ x : ℂ) + u₁ x 1 * (B0579.pd 1 ψ x : ℂ)) -
          (u₂ x 0 * (B0579.pd 0 ψ x : ℂ) + u₂ x 1 * (B0579.pd 1 ψ x : ℂ)) := by
      funext x; ring
    rw [heq, integral_sub I01 J01, h₁.2.1 ψ hψ, h₂.2.1 ψ hψ, sub_self]
  · have Iω := integrableOn_cylTest_mul hψ (memLp_unweighted_of_memX hω₁)
    have Jω := integrableOn_cylTest_mul hψ (memLp_unweighted_of_memX hω₂)
    have I0 := integrableOn_cylTest_mul (hψ.pd 1) (h₁.1 0)
    have I1 := integrableOn_cylTest_mul (hψ.pd 0) (h₁.1 1)
    have J0 := integrableOn_cylTest_mul (hψ.pd 1) (h₂.1 0)
    have J1 := integrableOn_cylTest_mul (hψ.pd 0) (h₂.1 1)
    have I01 : IntegrableOn
        (fun x => u₁ x 0 * (B0579.pd 1 ψ x : ℂ) - u₁ x 1 * (B0579.pd 0 ψ x : ℂ))
        (B0579.cell c) := I0.sub I1
    have J01 : IntegrableOn
        (fun x => u₂ x 0 * (B0579.pd 1 ψ x : ℂ) - u₂ x 1 * (B0579.pd 0 ψ x : ℂ))
        (B0579.cell c) := J0.sub J1
    have heqL : (fun x => (ω₁ x - ω₂ x) * (ψ x : ℂ)) =
        fun x => ω₁ x * (ψ x : ℂ) - ω₂ x * (ψ x : ℂ) := by
      funext x; ring
    have heqR : (fun x => (u₁ x 0 - u₂ x 0) * (B0579.pd 1 ψ x : ℂ) -
          (u₁ x 1 - u₂ x 1) * (B0579.pd 0 ψ x : ℂ)) =
        fun x => (u₁ x 0 * (B0579.pd 1 ψ x : ℂ) - u₁ x 1 * (B0579.pd 0 ψ x : ℂ)) -
          (u₂ x 0 * (B0579.pd 1 ψ x : ℂ) - u₂ x 1 * (B0579.pd 0 ψ x : ℂ)) := by
      funext x; ring
    rw [heqL, integral_sub Iω Jω, h₁.2.2 ψ hψ, h₂.2.2 ψ hψ, heqR, integral_sub I01 J01]

theorem isLinearisedFlow_sub {ν c : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {t : ℝ}
    {f₁ f₂ : ℝ × ℝ → ℂ} {w₁ w₂ : ℝ → ℝ × ℝ → ℂ} {u₁ u₂ : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hf₁ : MemLp f₁ 2 (B0579.cellMeasure c 9))
    (hf₂ : MemLp f₂ 2 (B0579.cellMeasure c 9))
    (hw₁ : IsLinearisedFlow ν c 9 tr t f₁ w₁ u₁)
    (hw₂ : IsLinearisedFlow ν c 9 tr t f₂ w₂ u₂) :
    IsLinearisedFlow ν c 9 tr t (fun x => f₁ x - f₂ x)
      (fun s x => w₁ s x - w₂ s x) (fun s x j => u₁ s x j - u₂ s x j) where
  initial := hw₁.initial.sub hw₂.initial
  memX s hs := (hw₁.memX s hs).sub (hw₂.memX s hs)
  strongCont s hs := by
    have hlim : Tendsto (fun s' => xNorm c 9 (w₁ s' - w₁ s) + xNorm c 9 (w₂ s' - w₂ s))
        (𝓝[Ici t] s) (𝓝 0) := by
      simpa using (hw₁.strongCont s hs).add (hw₂.strongCont s hs)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [self_mem_nhdsWithin] with s' hs'
    have heq : ((fun x => w₁ s' x - w₂ s' x) - (fun x => w₁ s x - w₂ s x)) =
        (w₁ s' - w₁ s) - (w₂ s' - w₂ s) := by
      funext x; simp only [Pi.sub_apply]; ring
    unfold xNorm
    rw [heq]
    exact eLpNorm_sub_le ((hw₁.memX s' hs').1.sub (hw₁.memX s hs).1)
      ((hw₂.memX s' hs').1.sub (hw₂.memX s hs).1) one_le_two
  biotSavart s hs :=
    isBiotSavart_sub (hw₁.memX s hs) (hw₂.memX s hs) (hw₁.biotSavart s hs) (hw₂.biotSavart s hs)
  integrable φ hφ r hr := by
    have heq : flowIntegrand tr (fun x => w₁ r x - w₂ r x) (fun x j => u₁ r x j - u₂ r x j) r φ =
        fun x => flowIntegrand tr (w₁ r) (u₁ r) r φ x - flowIntegrand tr (w₂ r) (u₂ r) r φ x := by
      funext x; unfold flowIntegrand; ring
    rw [heq]
    exact (hw₁.integrable φ hφ r hr).sub (hw₂.integrable φ hφ r hr)
  timeIntegrable φ hφ s hs := by
    have hsub := (hw₁.timeIntegrable φ hφ s hs).sub (hw₂.timeIntegrable φ hφ s hs)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs] at hsub ⊢
    refine hsub.congr_fun (fun r hr => ?_) measurableSet_Ioc
    have heq : flowIntegrand tr (fun x => w₁ r x - w₂ r x) (fun x j => u₁ r x j - u₂ r x j) r φ =
        fun x => flowIntegrand tr (w₁ r) (u₁ r) r φ x - flowIntegrand tr (w₂ r) (u₂ r) r φ x := by
      funext x; unfold flowIntegrand; ring
    simp only [heq]
    exact (integral_sub (hw₁.integrable φ hφ r hr.1.le) (hw₂.integrable φ hφ r hr.1.le)).symm
  weak φ hφ s hs := by
    have Iw₁ := integrableOn_cylTest_mul hφ (memLp_unweighted_of_memX (hw₁.memX s hs))
    have Iw₂ := integrableOn_cylTest_mul hφ (memLp_unweighted_of_memX (hw₂.memX s hs))
    have If₁ := integrableOn_cylTest_mul hφ (memLp_unweighted_of_memX hf₁)
    have If₂ := integrableOn_cylTest_mul hφ (memLp_unweighted_of_memX hf₂)
    have heqL : (fun x => (w₁ s x - w₂ s x) * (φ x : ℂ)) =
        fun x => w₁ s x * (φ x : ℂ) - w₂ s x * (φ x : ℂ) := by funext x; ring
    have heqf : (fun x => (f₁ x - f₂ x) * (φ x : ℂ)) =
        fun x => f₁ x * (φ x : ℂ) - f₂ x * (φ x : ℂ) := by funext x; ring
    have hcongr : ∀ r ∈ uIoc t s,
        (∫ x in B0579.cell c, flowIntegrand tr (fun x => w₁ r x - w₂ r x)
          (fun x j => u₁ r x j - u₂ r x j) r φ x) =
        (∫ x in B0579.cell c, flowIntegrand tr (w₁ r) (u₁ r) r φ x) -
          (∫ x in B0579.cell c, flowIntegrand tr (w₂ r) (u₂ r) r φ x) := by
      intro r hr
      rw [uIoc_of_le hs] at hr
      have heq : flowIntegrand tr (fun x => w₁ r x - w₂ r x) (fun x j => u₁ r x j - u₂ r x j) r φ =
          fun x => flowIntegrand tr (w₁ r) (u₁ r) r φ x - flowIntegrand tr (w₂ r) (u₂ r) r φ x := by
        funext x; unfold flowIntegrand; ring
      rw [heq, integral_sub (hw₁.integrable φ hφ r hr.1.le) (hw₂.integrable φ hφ r hr.1.le)]
    rw [heqL, integral_sub Iw₁ Iw₂, hw₁.weak φ hφ s hs, hw₂.weak φ hφ s hs,
      heqf, integral_sub If₁ If₂,
      intervalIntegral.integral_congr_ae (ae_of_all _ hcongr),
      intervalIntegral.integral_sub (hw₁.timeIntegrable φ hφ s hs) (hw₂.timeIntegrable φ hφ s hs)]
    ring

/-! ## 3. Source functional linearity and `negNorm = coreSrcNorm` -/

theorem xNorm_sq_eq {c m : ℝ} (f : ℝ × ℝ → ℂ) :
    xNorm c m f ^ 2 = ∫⁻ x in B0579.cell c, ENNReal.ofReal (B0579.jb x ^ m * ‖f x‖ ^ 2) := by
  have hd : Measurable fun x => (B0579.density m x : ℝ≥0∞) :=
    (B0579.measurable_density m).coe_nnreal_ennreal
  unfold xNorm B0579.cellMeasure
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  have hpow : ((∫⁻ x, ‖f x‖ₑ ^ ENNReal.toReal 2
      ∂(volume.restrict (B0579.cell c)).withDensity (fun x => ↑(B0579.density m x))) ^
      (1 / ENNReal.toReal 2)) ^ 2 =
      ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)
        ∂(volume.restrict (B0579.cell c)).withDensity (fun x => ↑(B0579.density m x)) := by
    rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
  rw [hpow, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hd
    (Filter.Eventually.of_forall fun _ => ENNReal.coe_lt_top) _]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  have h1 : (B0579.density m x : ℝ≥0∞) = ENNReal.ofReal (B0579.jb x ^ m) := rfl
  rw [h1, ENNReal.rpow_two, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (B0579.jb_pos x).le _)]

theorem aestronglyMeasurable_val_of_hasWeakCellDerivC {c : ℝ} {φ g : ℝ × ℝ → ℂ}
    (hg : HasWeakCellDerivC c 1 φ g) :
    AEStronglyMeasurable φ (volume.restrict (B0579.cell c)) := by
  let b : ℕ → ContDiffBump (0 : ℝ) := fun n =>
    ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩
  let ψ : ℕ → B0579.Plane → ℝ := fun n x => x.2 * b n x.2
  have hψ : ∀ n, B0579.IsCylTest c (ψ n) := fun n =>
    ⟨contDiff_snd.mul ((b n).contDiff.comp contDiff_snd), fun _ => rfl,
      ⟨(n : ℝ) + 2, fun x hx => by
        simp [ψ, (b n).zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hx.le)]⟩⟩
  have hm : ∀ n, AEStronglyMeasurable (fun x => φ x * (B0579.pd 1 (ψ n) x : ℂ))
      (volume.restrict (B0579.cell c)) :=
    fun n => ((hg.1 (ψ n) (hψ n)).1).aestronglyMeasurable
  refine aestronglyMeasurable_of_tendsto_ae atTop hm (Eventually.of_forall fun x => ?_)
  refine tendsto_atTop_of_eventually_const (i₀ := ⌈|x.2|⌉₊ + 1) fun n hn => ?_
  have hlt : |x.2| < (n : ℝ) + 1 := by
    have : (⌈|x.2|⌉₊ + 1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith [Nat.le_ceil |x.2|]
  have hU : IsOpen {y : B0579.Plane | |y.2| < (n : ℝ) + 1} :=
    isOpen_lt continuous_snd.abs continuous_const
  have hev : ψ n =ᶠ[𝓝 x] Prod.snd := by
    refine Filter.eventually_of_mem (hU.mem_nhds hlt) fun y hy => ?_
    have hone : b n y.2 = 1 := (b n).one_of_mem_closedBall (by
      simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      exact le_of_lt hy)
    simp [ψ, hone]
  have hpd : B0579.pd 1 (ψ n) x = 1 := by
    simp only [B0579.pd, hev.fderiv_eq]
    rw [(hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := x)).fderiv]
    simp [B0579.dir]
  simp [hpd]

theorem integrableOn_mul_of_memLp_h1 {c : ℝ} {f φ : ℝ × ℝ → ℂ} {g : Fin 2 → ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (B0579.cellMeasure c 9))
    (hg : ∀ j, HasWeakCellDerivC c j φ (g j)) (hh1 : h1Norm c 9 φ g ≤ 1) :
    IntegrableOn (fun x => f x * φ x) (B0579.cell c) := by
  have hfm : AEStronglyMeasurable f (volume.restrict (B0579.cell c)) :=
    hf.1.mono_ac (B0579.ac_cellMeasure c 9)
  have hφm : AEStronglyMeasurable φ (volume.restrict (B0579.cell c)) :=
    aestronglyMeasurable_val_of_hasWeakCellDerivC (hg 1)
  refine ⟨hfm.mul hφm, ?_⟩
  rw [HasFiniteIntegral]
  set F₁ : ℝ × ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (B0579.jb x ^ (9 / 2 : ℝ)) * ‖f x‖ₑ
  set F₂ : ℝ × ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (B0579.jb x ^ (-9 / 2 : ℝ)) * ‖φ x‖ₑ
  have hF₁ : AEMeasurable F₁ (volume.restrict (B0579.cell c)) :=
    ((B0579.continuous_jb_rpow _).measurable.ennreal_ofReal.aemeasurable).mul hfm.enorm
  have hF₂ : AEMeasurable F₂ (volume.restrict (B0579.cell c)) :=
    ((B0579.continuous_jb_rpow _).measurable.ennreal_ofReal.aemeasurable).mul hφm.enorm
  have hpt : ∀ x : ℝ × ℝ, ‖f x * φ x‖ₑ = F₁ x * F₂ x := by
    intro x
    have hjb : B0579.jb x ^ (9 / 2 : ℝ) * B0579.jb x ^ (-9 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add (B0579.jb_pos x)]; norm_num
    dsimp [F₁, F₂]
    calc ‖f x * φ x‖ₑ
        = 1 * (‖f x‖ₑ * ‖φ x‖ₑ) := by rw [enorm_mul, one_mul]
      _ = (ENNReal.ofReal (B0579.jb x ^ (9 / 2 : ℝ)) *
            ENNReal.ofReal (B0579.jb x ^ (-9 / 2 : ℝ))) * (‖f x‖ₑ * ‖φ x‖ₑ) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (B0579.jb_pos x).le _), hjb, ENNReal.ofReal_one]
      _ = _ := by ring
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (B0579.cell c))
    Real.HolderConjugate.two_two hF₁ hF₂
  have hsq₁ : ∫⁻ x in B0579.cell c, F₁ x ^ (2 : ℝ) = xNorm c 9 f ^ 2 := by
    rw [xNorm_sq_eq]
    refine lintegral_congr fun x => ?_
    dsimp [F₁]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.rpow_two, ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (Real.rpow_nonneg (B0579.jb_pos x).le _),
      ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (pow_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) _),
      ← Real.rpow_natCast (B0579.jb x ^ (9 / 2 : ℝ)) 2, ← Real.rpow_mul (B0579.jb_pos x).le]
    norm_num
  have hsq₂ : ∫⁻ x in B0579.cell c, F₂ x ^ (2 : ℝ) = xNorm c (-9) φ ^ 2 := by
    rw [xNorm_sq_eq]
    refine lintegral_congr fun x => ?_
    dsimp [F₂]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.rpow_two, ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (Real.rpow_nonneg (B0579.jb_pos x).le _),
      ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (pow_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) _),
      ← Real.rpow_natCast (B0579.jb x ^ (-9 / 2 : ℝ)) 2, ← Real.rpow_mul (B0579.jb_pos x).le]
    norm_num
  have hxφ : (xNorm c (-9) φ ^ 2) ^ (1 / 2 : ℝ) ≤ 1 := by
    calc (xNorm c (-9) φ ^ 2) ^ (1 / 2 : ℝ)
        ≤ (xNorm c (-9) φ ^ 2 + ∑ j, xNorm c (-9) (g j) ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow le_self_add (by norm_num)
      _ = h1Norm c 9 φ g := rfl
      _ ≤ 1 := hh1
  have hxf : (xNorm c 9 f ^ 2) ^ (1 / 2 : ℝ) < ⊤ := by
    rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
    exact hf.2
  rw [lintegral_congr hpt]
  exact hCS.trans_lt (by
    rw [hsq₁, hsq₂]
    exact ENNReal.mul_lt_top hxf (hxφ.trans_lt ENNReal.one_lt_top))

theorem lintegral_vnorm2_sq_lt_top {c : ℝ} {u : ℝ × ℝ → Fin 2 → ℂ}
    (hu : ∀ i, MemLp (fun x => u x i) 2 (volume.restrict (B0579.cell c))) :
    ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2) < ⊤ := by
  have hm0 : AEMeasurable (fun x => ENNReal.ofReal (‖u x 0‖ ^ 2))
      (volume.restrict (B0579.cell c)) :=
    ((hu 0).1.norm.aemeasurable.pow_const 2).ennreal_ofReal
  have heq : ∀ x, ENNReal.ofReal (vnorm2 (u x) ^ 2) =
      ENNReal.ofReal (‖u x 0‖ ^ 2) + ENNReal.ofReal (‖u x 1‖ ^ 2) := by
    intro x
    rw [causalLin_vnorm2_sq, Fin.sum_univ_two, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  have hfin : ∀ i : Fin 2, ∫⁻ x in B0579.cell c, ENNReal.ofReal (‖u x i‖ ^ 2) < ⊤ := by
    intro i
    have hlt := (hu i).2
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top] at hlt
    refine lt_of_eq_of_lt ?_ hlt
    refine lintegral_congr fun x => ?_
    have h2 : ENNReal.toReal 2 = 2 := by norm_num
    rw [h2, ENNReal.rpow_two, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  simp_rw [heq]
  rw [lintegral_add_left' hm0]
  exact ENNReal.add_lt_top.2 ⟨hfin 0, hfin 1⟩

theorem lintegral_tnorm2_sq_lt_top {c : ℝ} {G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ}
    (hG : ∀ i j, MemLp (fun x => G x i j) 2 (volume.restrict (B0579.cell c))) :
    ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2) < ⊤ := by
  have hfin : ∀ i j : Fin 2, ∫⁻ x in B0579.cell c, ENNReal.ofReal (‖G x i j‖ ^ 2) < ⊤ := by
    intro i j
    have hlt := (hG i j).2
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top] at hlt
    refine lt_of_eq_of_lt ?_ hlt
    refine lintegral_congr fun x => ?_
    have h2 : ENNReal.toReal 2 = 2 := by norm_num
    rw [h2, ENNReal.rpow_two, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hm : ∀ i j : Fin 2, AEMeasurable (fun x => ENNReal.ofReal (‖G x i j‖ ^ 2))
      (volume.restrict (B0579.cell c)) :=
    fun i j => ((hG i j).1.norm.aemeasurable.pow_const 2).ennreal_ofReal
  have heq : ∀ x, ENNReal.ofReal (tnorm2 (G x) ^ 2) =
      (ENNReal.ofReal (‖G x 0 0‖ ^ 2) + ENNReal.ofReal (‖G x 0 1‖ ^ 2)) +
        (ENNReal.ofReal (‖G x 1 0‖ ^ 2) + ENNReal.ofReal (‖G x 1 1‖ ^ 2)) := by
    intro x
    rw [causalLin_tnorm2_sq, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two,
      ENNReal.ofReal_add (add_nonneg (sq_nonneg _) (sq_nonneg _))
        (add_nonneg (sq_nonneg _) (sq_nonneg _)),
      ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
      ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  simp_rw [heq]
  have hm01 : AEMeasurable
      (fun x => ENNReal.ofReal (‖G x 0 0‖ ^ 2) + ENNReal.ofReal (‖G x 0 1‖ ^ 2))
      (volume.restrict (B0579.cell c)) := (hm 0 0).add (hm 0 1)
  rw [lintegral_add_left' hm01, lintegral_add_left' (hm 0 0),
    lintegral_add_left' (hm 1 0)]
  exact ENNReal.add_lt_top.2
    ⟨ENNReal.add_lt_top.2 ⟨hfin 0 0, hfin 0 1⟩, ENNReal.add_lt_top.2 ⟨hfin 1 0, hfin 1 1⟩⟩

theorem integrableOn_coreSrc_of_slice {c A_m : ℝ} (hc : 0 < c) (hAm : 0 ≤ A_m)
    {v : ℝ × ℝ → Fin 2 → ℝ} (hv : ContDiff ℝ 1 v)
    (hv_bd : ∀ x ∈ B0579.cell c, B0579.bracket x ^ (9 : ℝ) * (‖v x‖ + ‖fderiv ℝ v x‖) ≤ A_m)
    {u : ℝ × ℝ → Fin 2 → ℂ} {G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ}
    (hu : ∀ i, Measurable fun x => u x i) (hG : ∀ i j, Measurable fun x => G x i j)
    (hu_lp : ∀ i, MemLp (fun x => u x i) 2 (volume.restrict (B0579.cell c)))
    (hG_lp : ∀ i j, MemLp (fun x => G x i j) 2 (volume.restrict (B0579.cell c)))
    {φ : ℝ × ℝ → ℂ} {g : Fin 2 → ℝ × ℝ → ℂ}
    (hg : ∀ j, HasWeakCellDerivC c j φ (g j)) (hh1 : h1Norm c 9 φ g ≤ 1) :
    IntegrableOn (fun x => advStretch v u G x 1 * g 0 x - advStretch v u G x 0 * g 1 x)
      (B0579.cell c) := by
  have hgm : ∀ j : Fin 2, AEStronglyMeasurable (g j) (volume.restrict (B0579.cell c)) :=
    fun j => CurlDualityAux.aestronglyMeasurable_of_hasWeakCellDerivC (hg j)
  have hadvm : ∀ i : Fin 2, Measurable fun x => advStretch v u G x i :=
    CurlDualityAux.measurable_advStretch hv hu hG
  refine ⟨((hadvm 1).aestronglyMeasurable.mul (hgm 0)).sub
    ((hadvm 0).aestronglyMeasurable.mul (hgm 1)), ?_⟩
  rw [HasFiniteIntegral]
  set F₁ : ℝ × ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (B0579.bracket x ^ (9 : ℝ) * vnorm2 (advStretch v u G x))
  set F₂ : ℝ × ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (B0579.bracket x ^ (-9 : ℝ) * vnorm2 (fun j => g j x))
  have hF₁ : AEMeasurable F₁ (volume.restrict (B0579.cell c)) := by
    have hm_br : Measurable fun x : ℝ × ℝ => B0579.bracket x ^ (9 : ℝ) :=
      ((B0579.continuous_jb.sqrt).rpow_const (fun _ => Or.inr (by norm_num))).measurable
    exact (hm_br.mul (causalLin_measurable_vnorm2 hadvm)).ennreal_ofReal.aemeasurable
  have hF₂ : AEMeasurable F₂ (volume.restrict (B0579.cell c)) := by
    have hm_br : AEMeasurable (fun x : ℝ × ℝ => B0579.bracket x ^ (-9 : ℝ))
        (volume.restrict (B0579.cell c)) := by
      have heq : (fun x : ℝ × ℝ => B0579.bracket x ^ (-9 : ℝ)) =
          fun x => B0579.jb x ^ (-9 / 2 : ℝ) := funext (B0579.bracket_rpow (-9))
      rw [heq]
      exact (B0579.continuous_jb_rpow (-9 / 2)).measurable.aemeasurable
    have hm_g : AEMeasurable (fun x : ℝ × ℝ => vnorm2 (fun j => g j x))
        (volume.restrict (B0579.cell c)) := by
      unfold vnorm2
      refine Real.continuous_sqrt.measurable.comp_aemeasurable ?_
      rw [show (fun x : ℝ × ℝ => ∑ i : Fin 2, ‖g i x‖ ^ 2) =
          fun x => ‖g 0 x‖ ^ 2 + ‖g 1 x‖ ^ 2 from funext fun _ => Fin.sum_univ_two _]
      exact ((hgm 0).norm.aemeasurable.pow_const 2).add ((hgm 1).norm.aemeasurable.pow_const 2)
    exact (hm_br.mul hm_g).ennreal_ofReal
  have hpt : ∀ x, ‖advStretch v u G x 1 * g 0 x - advStretch v u G x 0 * g 1 x‖ₑ ≤ F₁ x * F₂ x := by
    intro x
    rw [← ofReal_norm]
    have hcs := coreSrc_cs (advStretch v u G x 0) (advStretch v u G x 1) (g 0 x) (g 1 x)
    have e1 : (![advStretch v u G x 0, advStretch v u G x 1] : Fin 2 → ℂ) = advStretch v u G x := by
      ext i; fin_cases i <;> rfl
    have e2 : (![g 0 x, g 1 x] : Fin 2 → ℂ) = fun j => g j x := by
      ext i; fin_cases i <;> rfl
    rw [e1, e2] at hcs
    have hbr_pos : 0 < B0579.bracket x := Real.sqrt_pos.2 (B0579.jb_pos x)
    have hbr_mul : B0579.bracket x ^ (9 : ℝ) * B0579.bracket x ^ (-9 : ℝ) = 1 := by
      rw [← Real.rpow_add hbr_pos, add_neg_cancel, Real.rpow_zero]
    dsimp [F₁, F₂]
    rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hbr_pos.le _) (vnorm2_nonneg _))]
    refine ENNReal.ofReal_le_ofReal (hcs.trans_eq ?_)
    calc vnorm2 (advStretch v u G x) * vnorm2 (fun j => g j x)
        = (B0579.bracket x ^ (9 : ℝ) * B0579.bracket x ^ (-9 : ℝ)) *
            (vnorm2 (advStretch v u G x) * vnorm2 (fun j => g j x)) := by
          rw [hbr_mul, one_mul]
      _ = _ := by ring
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (B0579.cell c))
    Real.HolderConjugate.two_two hF₁ hF₂
  have hF₁_sq : ∀ x, F₁ x ^ (2 : ℝ) =
      ENNReal.ofReal (B0579.bracket x ^ (18 : ℝ) * vnorm2 (advStretch v u G x) ^ 2) := by
    intro x
    have hbr_pos : 0 < B0579.bracket x := Real.sqrt_pos.2 (B0579.jb_pos x)
    have hbr18 : B0579.bracket x ^ (18 : ℝ) = (B0579.bracket x ^ (9 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast (B0579.bracket x ^ (9 : ℝ)) 2, ← Real.rpow_mul hbr_pos.le]
      norm_num
    dsimp [F₁]
    rw [ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (mul_nonneg (Real.rpow_nonneg hbr_pos.le _) (vnorm2_nonneg _)),
      mul_pow, hbr18]
  have hF₂_sq : ∀ x, F₂ x ^ (2 : ℝ) =
      ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ) * ‖g 0 x‖ ^ 2) +
        ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ) * ‖g 1 x‖ ^ 2) := by
    intro x
    have hbr_pos : 0 < B0579.bracket x := Real.sqrt_pos.2 (B0579.jb_pos x)
    have hbr_neg18 : (B0579.bracket x ^ (-9 : ℝ)) ^ 2 = B0579.jb x ^ (-9 : ℝ) := by
      rw [B0579.bracket_rpow (-9), ← Real.rpow_natCast _ 2,
        ← Real.rpow_mul (B0579.jb_pos x).le]
      congr 1; norm_num
    have hv_sq : vnorm2 (fun j => g j x) ^ 2 = ‖g 0 x‖ ^ 2 + ‖g 1 x‖ ^ 2 := by
      unfold vnorm2
      rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fin.sum_univ_two]
    dsimp [F₂]
    rw [ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (mul_nonneg (Real.rpow_nonneg hbr_pos.le _) (vnorm2_nonneg _)),
      mul_pow, hbr_neg18, hv_sq, mul_add,
      ENNReal.ofReal_add
        (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _))
        (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _))]
  have hF₂_int : (∫⁻ x in B0579.cell c, F₂ x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ 1 := by
    have hm0 : AEMeasurable
        (fun x : ℝ × ℝ => ENNReal.ofReal (B0579.jb x ^ (-9 : ℝ) * ‖g 0 x‖ ^ 2))
        (volume.restrict (B0579.cell c)) :=
      ((B0579.continuous_jb_rpow (-9)).measurable.aemeasurable.mul
        ((hgm 0).norm.aemeasurable.pow_const 2)).ennreal_ofReal
    have hint_eq : ∫⁻ x in B0579.cell c, F₂ x ^ (2 : ℝ) =
        ∑ j : Fin 2, xNorm c (-9) (g j) ^ 2 := by
      simp_rw [hF₂_sq]
      rw [lintegral_add_left' hm0, ← CurlDualityAux.xNorm_neg_nine_sq_eq c (g 0),
        ← CurlDualityAux.xNorm_neg_nine_sq_eq c (g 1), Fin.sum_univ_two]
    rw [hint_eq]
    calc (∑ j : Fin 2, xNorm c (-9) (g j) ^ 2) ^ (1 / 2 : ℝ)
        ≤ (xNorm c (-9) φ ^ 2 + ∑ j : Fin 2, xNorm c (-9) (g j) ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow le_add_self (by norm_num)
      _ = h1Norm c 9 φ g := rfl
      _ ≤ 1 := hh1
  have hF₁_fin : (∫⁻ x in B0579.cell c, F₁ x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) < ⊤ := by
    simp_rw [hF₁_sq]
    have hbd := advStretch_weighted_l2_bound hc hAm hv hv_bd hu hG
    refine hbd.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨?_, ?_⟩))
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (lintegral_vnorm2_sq_lt_top hu_lp).ne
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (lintegral_tnorm2_sq_lt_top hG_lp).ne
  exact (lintegral_mono hpt).trans_lt
    (hCS.trans_lt (ENNReal.mul_lt_top hF₁_fin (hF₂_int.trans_lt ENNReal.one_lt_top)))

theorem negNorm_eq_coreSrcNorm {c : ℝ} {f : ℝ × ℝ → ℂ} {a : ℝ × ℝ → Fin 2 → ℂ}
    (hpair : ∀ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ),
      (∀ j, HasWeakCellDerivC c j φ (g j)) → h1Norm c 9 φ g ≤ 1 →
      ∫ x in B0579.cell c, f x * φ x = coreSrcFun c a g) :
    negNorm c 9 f = coreSrcNorm c 9 a := by
  unfold negNorm coreSrcNorm
  refine iSup_congr fun φ => iSup_congr fun g => iSup_congr fun hg => iSup_congr fun hh1 => ?_
  rw [hpair φ g hg hh1]

theorem coreAdvSlice_sub {ν c : ℝ} (γ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (b₁ b₂ : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G₁ G₂ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (t : ℝ) (x : ℝ × ℝ) (i : Fin 2) :
    coreAdvSlice γ tr (fun p k => b₁ p k - b₂ p k) (fun p k l => G₁ p k l - G₂ p k l) t x i =
      coreAdvSlice γ tr b₁ G₁ t x i - coreAdvSlice γ tr b₂ G₂ t x i := by
  unfold coreAdvSlice advStretch gainConj
  simp only [Fin.sum_univ_two, Pi.smul_apply, Complex.real_smul]
  ring

theorem trainVel_weighted_bound {ν b A_m : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hbd : ∀ s ∈ Ioc (0 : ℝ) (coreEnd ν b), ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      B0579.bracket x ^ (9 : ℝ) * (‖tr.v s x‖ + ‖fderiv ℝ (tr.v s) x‖) ≤ A_m)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) (coreEnd ν b)) :
    ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      B0579.bracket x ^ (9 : ℝ) * (‖trainVel tr t x‖ + ‖fderiv ℝ (trainVel tr t) x‖) ≤ A_m := by
  intro x hx
  have hb := hbd t ht x hx
  have hfd : fderiv ℝ (trainVel tr t) x =
      (evE : EuclideanSpace ℝ (Fin 2) →L[ℝ] (Fin 2 → ℝ)).comp (fderiv ℝ (tr.v t) x) := by
    rw [trainVel_eq tr ht.1]
    exact evE.comp_fderiv (f := tr.v t) (x := x)
  have hop : ‖(evE : EuclideanSpace ℝ (Fin 2) →L[ℝ] (Fin 2 → ℝ)).comp (fderiv ℝ (tr.v t) x)‖
      ≤ ‖fderiv ℝ (tr.v t) x‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
    calc ‖(evE : EuclideanSpace ℝ (Fin 2) →L[ℝ] (Fin 2 → ℝ)) (fderiv ℝ (tr.v t) x y)‖
        ≤ ‖fderiv ℝ (tr.v t) x y‖ := norm_evE_le _
      _ ≤ ‖fderiv ℝ (tr.v t) x‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
  have hn : ‖trainVel tr t x‖ ≤ ‖tr.v t x‖ := by
    rw [trainVel_eq tr ht.1]; exact norm_evE_le _
  rw [hfd]
  exact le_trans
    (mul_le_mul_of_nonneg_left (add_le_add hn hop) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)) hb

theorem negNorm_sub_eq_coreSrcNorm {ν b A_m γ : ℝ} (hν : 0 < ν) (hAm : 0 ≤ A_m)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hbd : ∀ s ∈ Ioc (0 : ℝ) (coreEnd ν b), ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      B0579.bracket x ^ (9 : ℝ) * (‖tr.v s x‖ + ‖fderiv ℝ (tr.v s) x‖) ≤ A_m)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (coreEnd ν b))
    {f₁ f₂ : ℝ × ℝ → ℂ}
    {b₁ b₂ : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G₁ G₂ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hb₁m : ∀ i, Measurable fun p => b₁ p i) (hG₁m : ∀ i j, Measurable fun p => G₁ p i j)
    (hb₂m : ∀ i, Measurable fun p => b₂ p i) (hG₂m : ∀ i j, Measurable fun p => G₂ p i j)
    (hb₁_lp : ∀ i, MemLp (fun x => gainConj γ ν b₁ (t, x) i) 2
      (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))))
    (hG₁_lp : ∀ i j, MemLp (fun x => gainConj γ ν G₁ (t, x) i j) 2
      (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))))
    (hb₂_lp : ∀ i, MemLp (fun x => gainConj γ ν b₂ (t, x) i) 2
      (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))))
    (hG₂_lp : ∀ i j, MemLp (fun x => gainConj γ ν G₂ (t, x) i j) 2
      (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))))
    (hf₁ : MemLp f₁ 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9))
    (hf₂ : MemLp f₂ 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9))
    (hp₁ : ∀ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ),
      (∀ j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j φ (g j)) → h1Norm (ν ^ (-2 : ℝ)) 9 φ g ≤ 1 →
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f₁ x * φ x =
        coreSrcFun (ν ^ (-2 : ℝ)) (coreAdvSlice γ tr b₁ G₁ t) g)
    (hp₂ : ∀ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ),
      (∀ j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j φ (g j)) → h1Norm (ν ^ (-2 : ℝ)) 9 φ g ≤ 1 →
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f₂ x * φ x =
        coreSrcFun (ν ^ (-2 : ℝ)) (coreAdvSlice γ tr b₂ G₂ t) g) :
    negNorm (ν ^ (-2 : ℝ)) 9 (fun x => f₁ x - f₂ x) =
      coreSrcNorm (ν ^ (-2 : ℝ)) 9
        (coreAdvSlice γ tr (fun p i => b₁ p i - b₂ p i) (fun p i j => G₁ p i j - G₂ p i j) t) := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  refine negNorm_eq_coreSrcNorm fun φ g hg hh1 => ?_
  have If₁ := integrableOn_mul_of_memLp_h1 hf₁ hg hh1
  have If₂ := integrableOn_mul_of_memLp_h1 hf₂ hg hh1
  have hv := contDiff_trainVel tr ht.1
  have hv_bd := trainVel_weighted_bound hbd ⟨ht.1, ht.2.le⟩
  have hu₁ : ∀ i, Measurable fun x : ℝ × ℝ => gainConj γ ν b₁ (t, x) i := by
    intro i; simp only [gainConj, Pi.smul_apply]
    exact ((hb₁m i).comp measurable_prodMk_left).const_smul _
  have hG₁ : ∀ i j, Measurable fun x : ℝ × ℝ => gainConj γ ν G₁ (t, x) i j := by
    intro i j; simp only [gainConj, Pi.smul_apply]
    exact ((hG₁m i j).comp measurable_prodMk_left).const_smul _
  have hu₂ : ∀ i, Measurable fun x : ℝ × ℝ => gainConj γ ν b₂ (t, x) i := by
    intro i; simp only [gainConj, Pi.smul_apply]
    exact ((hb₂m i).comp measurable_prodMk_left).const_smul _
  have hG₂ : ∀ i j, Measurable fun x : ℝ × ℝ => gainConj γ ν G₂ (t, x) i j := by
    intro i j; simp only [gainConj, Pi.smul_apply]
    exact ((hG₂m i j).comp measurable_prodMk_left).const_smul _
  have Ia₁ : IntegrableOn
      (fun x => coreAdvSlice γ tr b₁ G₁ t x 1 * g 0 x - coreAdvSlice γ tr b₁ G₁ t x 0 * g 1 x)
      (B0579.cell c) :=
    integrableOn_coreSrc_of_slice hc hAm hv hv_bd hu₁ hG₁ hb₁_lp hG₁_lp hg hh1
  have Ia₂ : IntegrableOn
      (fun x => coreAdvSlice γ tr b₂ G₂ t x 1 * g 0 x - coreAdvSlice γ tr b₂ G₂ t x 0 * g 1 x)
      (B0579.cell c) :=
    integrableOn_coreSrc_of_slice hc hAm hv hv_bd hu₂ hG₂ hb₂_lp hG₂_lp hg hh1
  have heqL : (fun x => (f₁ x - f₂ x) * φ x) = fun x => f₁ x * φ x - f₂ x * φ x := by
    funext x; ring
  have heqR : (fun x =>
      coreAdvSlice γ tr (fun p i => b₁ p i - b₂ p i) (fun p i j => G₁ p i j - G₂ p i j) t x 1 *
        g 0 x -
      coreAdvSlice γ tr (fun p i => b₁ p i - b₂ p i) (fun p i j => G₁ p i j - G₂ p i j) t x 0 *
        g 1 x) =
      fun x => (coreAdvSlice γ tr b₁ G₁ t x 1 * g 0 x - coreAdvSlice γ tr b₁ G₁ t x 0 * g 1 x) -
        (coreAdvSlice γ tr b₂ G₂ t x 1 * g 0 x - coreAdvSlice γ tr b₂ G₂ t x 0 * g 1 x) := by
    funext x
    rw [coreAdvSlice_sub, coreAdvSlice_sub]
    ring
  rw [heqL, integral_sub If₁ If₂, hp₁ φ g hg hh1, hp₂ φ g hg hh1]
  unfold coreSrcFun
  rw [heqR, integral_sub Ia₁ Ia₂]

/-! ## 4. Clock bound for each Duhamel piece (single and difference) -/

theorem duhamelPiece_bounds {P : PlanarData} {b C_clock ν : ℝ} {μ : ℂ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hν : 0 < ν) (hclock : ClockBoundAt P 9 b C_clock ν tr)
    {t s : ℝ} (ht : 0 < t) (hts : t < s) (hsH : s ≤ coreEnd ν b)
    {f kt : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hf : MemLp f 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9))
    (hz : HasZeroCirculation (ν ^ (-2 : ℝ)) f)
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) 9 tr t f w u)
    (hkae : kt =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
      fun x => ((t / s : ℝ) : ℂ) ^ μ *
        ((gainG P.eigenvalue.re ν t / gainG P.eigenvalue.re ν s : ℝ) : ℂ) * w s x) :
    MemLp kt 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9) ∧
    HasZeroCirculation (ν ^ (-2 : ℝ)) kt ∧
    xNorm (ν ^ (-2 : ℝ)) 9 kt ≤
      ENNReal.ofReal (vortKernel C_clock P ν μ s t) * negNorm (ν ^ (-2 : ℝ)) 9 f := by
  set c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  set γ : ℝ := P.eigenvalue.re
  set α : ℂ := ((t / s : ℝ) : ℂ) ^ μ * ((gainG γ ν t / gainG γ ν s : ℝ) : ℂ)
  have hkae9 : kt =ᵐ[B0579.cellMeasure c 9] fun x => α * w s x :=
    (B0579.cellMeasure_ac c 9).ae_le hkae
  have hmem : MemLp kt 2 (B0579.cellMeasure c 9) :=
    ((hw.memX s hts.le).const_mul α).ae_eq hkae9.symm
  obtain ⟨hw_int, hw_zero⟩ := hasZeroCirculation_of_isLinearisedFlow hc hts.le hw
  have hzc : HasZeroCirculation c kt := by
    refine ⟨(hw_int.const_mul α).congr hkae.symm, ?_⟩
    rw [integral_congr_ae hkae, integral_const_mul, hw_zero, mul_zero]
  have hs0 : 0 < s := ht.trans hts
  have hdiv_pos : 0 < t / s := div_pos ht hs0
  have hgain_pos : 0 < gainG γ ν t / gainG γ ν s :=
    div_pos (Real.exp_pos _) (Real.exp_pos _)
  have hnorm_α : ‖α‖ₑ =
      ENNReal.ofReal ((t / s) ^ μ.re) * ENNReal.ofReal (gainG γ ν t / gainG γ ν s) := by
    rw [← ofReal_norm]
    dsimp [α]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hdiv_pos μ, Complex.norm_real,
      Real.norm_of_nonneg hgain_pos.le,
      ENNReal.ofReal_mul (Real.rpow_nonneg hdiv_pos.le _)]
  have hx_eq : xNorm c 9 kt = ‖α‖ₑ * xNorm c 9 (w s) := by
    unfold xNorm
    rw [eLpNorm_congr_ae hkae9]
    have hsm := eLpNorm_const_smul (p := 2) (μ := B0579.cellMeasure c 9) α (w s)
    simpa [Pi.smul_def, smul_eq_mul] using hsm
  have hcb := hclock t s ht hts hsH f hf hz w u hw
  have hC_le : ENNReal.ofReal (C_clock * ν ^ (-(weakDegree 9 P.kappa : ℝ)) *
        (1 + (s - t) ^ (-1 / 2 : ℝ))) ≤
      ENNReal.ofReal (|C_clock| * ν ^ (-(weakDegree 9 P.kappa : ℝ)) *
        (1 + (s - t) ^ (-1 / 2 : ℝ))) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have hfac_nn : 0 ≤ ν ^ (-(weakDegree 9 P.kappa : ℝ)) * (1 + (s - t) ^ (-1 / 2 : ℝ)) :=
      mul_nonneg (Real.rpow_nonneg hν.le _)
        (add_nonneg zero_le_one (Real.rpow_nonneg (sub_nonneg.2 hts.le) _))
    calc C_clock * ν ^ (-(weakDegree 9 P.kappa : ℝ)) * (1 + (s - t) ^ (-1 / 2 : ℝ))
        = C_clock * (ν ^ (-(weakDegree 9 P.kappa : ℝ)) * (1 + (s - t) ^ (-1 / 2 : ℝ))) := by ring
      _ ≤ |C_clock| * (ν ^ (-(weakDegree 9 P.kappa : ℝ)) * (1 + (s - t) ^ (-1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_abs_self C_clock) hfac_nn
      _ = |C_clock| * ν ^ (-(weakDegree 9 P.kappa : ℝ)) * (1 + (s - t) ^ (-1 / 2 : ℝ)) := by ring
  refine ⟨hmem, hzc, ?_⟩
  calc xNorm c 9 kt
      = ENNReal.ofReal ((t / s) ^ μ.re) *
          (ENNReal.ofReal (gainG γ ν t / gainG γ ν s) * xNorm c 9 (w s)) := by
        rw [hx_eq, hnorm_α, mul_assoc]
    _ ≤ ENNReal.ofReal ((t / s) ^ μ.re) *
          (ENNReal.ofReal (C_clock * ν ^ (-(weakDegree 9 P.kappa : ℝ)) *
            (1 + (s - t) ^ (-1 / 2 : ℝ))) * negNorm c 9 f) :=
        mul_le_mul_of_nonneg_left hcb bot_le
    _ ≤ ENNReal.ofReal ((t / s) ^ μ.re) *
          (ENNReal.ofReal (|C_clock| * ν ^ (-(weakDegree 9 P.kappa : ℝ)) *
            (1 + (s - t) ^ (-1 / 2 : ℝ))) * negNorm c 9 f) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC_le bot_le) bot_le
    _ = ENNReal.ofReal (vortKernel C_clock P ν μ s t) * negNorm c 9 f := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hdiv_pos.le _)]
        congr 2
        unfold vortKernel
        ring

/-! ## 5. Approximation bundle and geometric `NiceForceApprox` sequence -/

/-- Bundle of Duhamel approximation data for a sequence of nice forces `(Fn, b₀n, G₀n, b_sol_n, G_sol_n)`
converging geometrically (`≤ 2^{-n}`) in the gain-conjugated `𝒯` norm to `F` (SP 3427-3440,
3481-3496). -/
def NiceDuhamelApprox (P : PlanarData) (K : Set ℂ) (b ν : ℝ)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ) (A_m C_clock : ℝ)
    (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (Fn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b₀n : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G₀n : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b_sol_n : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G_sol_n : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : Prop :=
  (∀ n, VortData P K b ν tr μ A_m (Fn n) (b₀n n) (G₀n n) (b_sol_n n) (G_sol_n n)) ∧
  (∀ n, tCalNorm (ν ^ (-2 : ℝ))
      (gainConj P.eigenvalue.re ν (fun p i j => Fn n p i j - F p i j)) ≤
    ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) ∧
  ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) (coreEnd ν b) →
    ∃ ks : ℕ → ℝ → ℝ × ℝ → ℂ,
      (∀ n, Measurable (Function.uncurry (ks n))) ∧
      (∀ n, corePerturbVort P.eigenvalue.re ν (G₀n n) (G_sol_n n) s
        =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
          fun x => ∫ t in Ioo 0 s, ks n t x) ∧
      ∀ᵐ t ∂volume, t ∈ Ioo 0 s →
        (∀ n,
          MemLp (ks n t) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9) ∧
          HasZeroCirculation (ν ^ (-2 : ℝ)) (ks n t) ∧
          xNorm (ν ^ (-2 : ℝ)) 9 (ks n t) ≤
            ENNReal.ofReal (vortKernel C_clock P ν μ s t) *
              coreSrcNorm (ν ^ (-2 : ℝ)) 9
                (coreAdvSlice P.eigenvalue.re tr (b₀n n) (G₀n n) t)) ∧
        (∀ n m,
          xNorm (ν ^ (-2 : ℝ)) 9 (fun x => ks n t x - ks m t x) ≤
            ENNReal.ofReal (vortKernel C_clock P ν μ s t) *
              coreSrcNorm (ν ^ (-2 : ℝ)) 9
                (coreAdvSlice P.eigenvalue.re tr
                  (fun p i => b₀n n p i - b₀n m p i)
                  (fun p i j => G₀n n p i j - G₀n m p i j) t))

theorem niceApproxSeq_exists {P : PlanarData} (hP : IsPlanarReference P)
    {K : Set ℂ} (hK : IsAdmissibleK K) {b ν_ex ν : ℝ} (hb : 1 ≤ b) (hν : ν ∈ Ioc 0 ν_ex)
    (hTrEx : ∀ ν ∈ Ioc 0 ν_ex, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ μ ∈ K,
      ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, (∀ p i j, F p i j = F p j i) →
        (∀ i j, Measurable fun p => F p i j) →
        tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) < ⊤ →
        ∃ b_sol G_sol,
          IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (trainVel tr) F b_sol G_sol)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {μ : ℂ} {A_m : ℝ}
    {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b₀ G₀ b_sol G_sol}
    (hd : VortData P K b ν tr μ A_m F b₀ G₀ b_sol G_sol) :
    ∃ (Fn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
      (b₀n : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
      (G₀n : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
      (b_sol_n : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
      (G_sol_n : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
      (∀ n, NiceForce (ν ^ (-2 : ℝ)) (Fn n)) ∧
      (∀ n, VortData P K b ν tr μ A_m (Fn n) (b₀n n) (G₀n n) (b_sol_n n) (G_sol_n n)) ∧
      (∀ n, CoreVortWeakEqAt P b ν tr μ (b₀n n) (G₀n n) (b_sol_n n) (G_sol_n n)) ∧
      (∀ n, tCalNorm (ν ^ (-2 : ℝ))
          (gainConj P.eigenvalue.re ν (fun p i j => Fn n p i j - F p i j)) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) := by
  obtain ⟨hbuc, hμ, hAm, hbd, hFsym, hFmeas, hFtc, _, _⟩ := hd
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν.1 _
  let γ : ℝ := P.eigenvalue.re
  obtain ⟨Fk, hFk_nice, hFk_lim⟩ := niceForceApprox c ν γ hc hν.1 F hFsym hFmeas hFtc
  have hex_idx : ∀ n : ℕ, ∃ k : ℕ,
      tCalNorm c (gainConj γ ν (fun p i j => Fk k p i j - F p i j)) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
    intro n
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal ((1 / 2 : ℝ) ^ n) :=
      ENNReal.ofReal_pos.2 (by positivity)
    exact (hFk_lim.eventually (Iic_mem_nhds hpos)).exists
  let Fn : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun n => Fk (Classical.choose (hex_idx n))
  have hFn_nice : ∀ n, NiceForce c (Fn n) := fun n => hFk_nice _
  have hFn_err : ∀ n, tCalNorm c (gainConj γ ν (fun p i j => Fn n p i j - F p i j)) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ n) :=
    fun n => Classical.choose_spec (hex_idx n)
  have hFn_sym : ∀ n p i j, Fn n p i j = Fn n p j i := fun n => (hFn_nice n).1
  have hFn_meas : ∀ n i j, Measurable fun p => Fn n p i j :=
    fun n i j => ((hFn_nice n).2.1 i j).continuous.measurable
  have hFn_tc : ∀ n, tCalNorm c (gainConj γ ν (Fn n)) < ⊤ := by
    intro n
    have htri := tCalNormTriangle c ν γ (Fn n) F (fun _ _ _ => 0)
      (hFn_meas n) hFmeas (fun _ _ => measurable_const)
    have hcomm := GlobalExistenceAux.tCalNorm_sub_comm c ν γ (fun _ _ _ => 0) F
    simp only [sub_zero] at htri hcomm
    rw [hcomm] at htri
    exact lt_of_le_of_lt htri
      (ENNReal.add_lt_top.2 ⟨(hFn_err n).trans_lt ENNReal.ofReal_lt_top, hFtc⟩)
  have hFree_ex : ∀ n, ∃ b₀' G₀', IsCausalEnergySolution c ν μ (fun _ _ _ => 0) (Fn n) b₀' G₀' :=
    fun n => niceForceSolution c ν μ hc hν.1 (Fn n) (hFn_nice n)
  have hSol_ex : ∀ n, ∃ bs Gs, IsCausalEnergySolution c ν μ (trainVel tr) (Fn n) bs Gs :=
    fun n => hTrEx ν hν tr hbuc μ hμ (Fn n) (hFn_sym n) (hFn_meas n) (hFn_tc n)
  let b₀n : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun n => Classical.choose (hFree_ex n)
  let G₀n : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ :=
    fun n => Classical.choose (Classical.choose_spec (hFree_ex n))
  let b_sol_n : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun n => Classical.choose (hSol_ex n)
  let G_sol_n : ℕ → ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ :=
    fun n => Classical.choose (Classical.choose_spec (hSol_ex n))
  have hhd_n : ∀ n, VortData P K b ν tr μ A_m (Fn n) (b₀n n) (G₀n n) (b_sol_n n) (G_sol_n n) :=
    fun n => ⟨hbuc, hμ, hAm, hbd, hFn_sym n, hFn_meas n, hFn_tc n,
      Classical.choose_spec (Classical.choose_spec (hFree_ex n)),
      Classical.choose_spec (Classical.choose_spec (hSol_ex n))⟩
  have hwk_n : ∀ n, CoreVortWeakEqAt P b ν tr μ (b₀n n) (G₀n n) (b_sol_n n) (G_sol_n n) :=
    fun n => coreVortWeakEq P hP K hK b hb ν hν.1 tr μ A_m (Fn n) (b₀n n) (G₀n n)
      (b_sol_n n) (G_sol_n n) (hhd_n n)
  exact ⟨Fn, b₀n, G₀n, b_sol_n, G_sol_n, hFn_nice, hhd_n, hwk_n, hFn_err⟩

theorem ae_freeSlice_memLp {c ν γ H : ℝ} (hν : 0 < ν) (hH : 0 < H) {μ : ℂ}
    {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b₀ : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G₀ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hfree : IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F b₀ G₀) :
    ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) H →
      (∀ i, MemLp (fun x => gainConj γ ν b₀ (t, x) i) 2 (volume.restrict (B0579.cell c))) ∧
      (∀ i j, MemLp (fun x => gainConj γ ν G₀ (t, x) i j) 2 (volume.restrict (B0579.cell c))) := by
  have h0_raw := causalSolSub c ν μ (fun _ _ _ => 0) F F b₀ b₀ G₀ G₀ hfree hfree
  have heqF : (fun (p : ℝ × (ℝ × ℝ)) (i j : Fin 2) => F p i j - F p i j) =
      fun _ _ _ => (0 : ℂ) := by funext p i j; exact sub_self _
  have heqb : (fun (p : ℝ × (ℝ × ℝ)) (i : Fin 2) => b₀ p i - b₀ p i) =
      fun _ _ => (0 : ℂ) := by funext p i; exact sub_self _
  have heqG : (fun (p : ℝ × (ℝ × ℝ)) (i j : Fin 2) => G₀ p i j - G₀ p i j) =
      fun _ _ _ => (0 : ℂ) := by funext p i j; exact sub_self _
  rw [heqF, heqb, heqG] at h0_raw
  have hae := corePerturb_memLp_ae (γ := γ) hν hH h0_raw hfree
  filter_upwards [hae] with t ht htH
  obtain ⟨hu, hG⟩ := ht htH
  have eu : ∀ i, (fun x => corePerturbVel γ ν (fun _ _ => 0) b₀ (t, x) i) =
      fun x => gainConj γ ν b₀ (t, x) i := by
    intro i; funext x; simp [corePerturbVel, gainConj]
  have eG : ∀ i j, (fun x => corePerturbGrad γ ν (fun _ _ _ => 0) G₀ (t, x) i j) =
      fun x => gainConj γ ν G₀ (t, x) i j := by
    intro i j; funext x; simp [corePerturbGrad, gainConj]
  exact ⟨fun i => eu i ▸ hu i, fun i j => eG i j ▸ hG i j⟩

end CoreDuhamelRepSub

/-- **Leaf (i) `CoreDuhamelNice`** (`PartIII-a:T19/2/3/2/3/1/1`, SP 3427-3440, 3481-3491,
3541-3545): Duhamel representation of `corePerturbVort` for nice forces `NiceForce (ν ^ (-2 : ℝ)) F`.
For small `ν` and a nice force `F`, the weak advection-stretching source functional
`coreSrcFun (coreAdvSlice ... b₀ G₀ t)` is represented for a.e. `t ∈ (0, H)` by an `X_{9,c}^0`
function `f t` (`-(v·∇ω₀ + u₀·∇E)`, smooth Gaussian-decaying `ω₀ = curl(g⁻¹b₀)` via
`heatCellClassical` / `duhamelDecay` and weighted `∇E` bound via `TrainTransverseTailsUniform`),
and for a.e. `s ∈ (0, H)` the gain-conjugated perturbation vorticity equals `∫_0^s k t x dt` for a
jointly measurable kernel `k` whose `t`-slices agree a.e. on `B0579.cell c` with
`(t/s)^μ (g(t)/g(s)) w_t(s)` for a weak linearised flow `(w_t, u_t)` starting from `f t`. -/
def CoreDuhamelNice : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ K : Set ℂ, IsAdmissibleK K →
    ∀ b : ℝ, 1 ≤ b → ∃ ν_nice : ℝ, 0 < ν_nice ∧
      ∀ ν ∈ Ioc 0 ν_nice, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        FullFlowExists ν (ν ^ (-2 : ℝ)) 9 tr →
        ∀ μ : ℂ, ∀ A_m C_clock : ℝ, ClockBoundAt P 9 b C_clock ν tr →
          ∀ F b₀ G₀ b_sol G_sol,
            NiceForce (ν ^ (-2 : ℝ)) F →
            VortData P K b ν tr μ A_m F b₀ G₀ b_sol G_sol →
            CoreVortWeakEqAt P b ν tr μ b₀ G₀ b_sol G_sol →
            ∃ f : ℝ → ℝ × ℝ → ℂ,
              (∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) (coreEnd ν b) →
                MemLp (f t) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9) ∧
                HasZeroCirculation (ν ^ (-2 : ℝ)) (f t) ∧
                ∀ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ),
                  (∀ j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j φ (g j)) →
                  h1Norm (ν ^ (-2 : ℝ)) 9 φ g ≤ 1 →
                  ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f t x * φ x =
                    coreSrcFun (ν ^ (-2 : ℝ))
                      (coreAdvSlice P.eigenvalue.re tr b₀ G₀ t) g) ∧
              ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) (coreEnd ν b) →
                ∃ k : ℝ → ℝ × ℝ → ℂ, Measurable (Function.uncurry k) ∧
                  (∀ᵐ t ∂volume, t ∈ Ioo 0 s →
                    ∃ (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ),
                      IsLinearisedFlow ν (ν ^ (-2 : ℝ)) 9 tr t (f t) w u ∧
                      k t =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
                        fun x => ((t / s : ℝ) : ℂ) ^ μ *
                          ((gainG P.eigenvalue.re ν t / gainG P.eigenvalue.re ν s : ℝ) : ℂ) *
                          w s x) ∧
                  corePerturbVort P.eigenvalue.re ν G₀ G_sol s
                    =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
                      fun x => ∫ t in Ioo 0 s, k t x

/-- **Leaf (ii) `CoreDuhamelDensity`** (`PartIII-a:T19/2/3/2/3/1/2`, SP 3427-3440, 3481-3496,
3518-3527): passage to the `Z^{-1}_{9,c}` density limit along a geometrically converging sequence of
nice forces (`NiceDuhamelApprox`). Using `freeCausalEnergyBound` and `coreSourceNegBound`
(`C_dual = 8`) with the Hardy Tonelli estimate of `LeafB.lean` (`coreSourceFinite_proof`), the
successive differences `ks (n + 1) t - ks n t` are summable in `L¹(0, s; X_{9,c})` for a.e.
`s ∈ (0, H)`, yielding a jointly measurable telescoping limit `k` in `X_{9,c}^0` satisfying the
weak-source clock bound, while `trainAdvectionEnergyIdentity` on `(0, H)` gives
`tCalNormOn c H (gainConj γ ν (G_sol_n n - G_sol)) → 0` to pass the Duhamel identity to `(G₀, G_sol)`. -/
def CoreDuhamelDensity : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ K : Set ℂ, IsAdmissibleK K →
    ∀ b : ℝ, 1 ≤ b → ∃ ν_lim : ℝ, 0 < ν_lim ∧
      ∀ ν ∈ Ioc 0 ν_lim, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        ∀ μ : ℂ, ∀ A_m C_clock : ℝ, ClockBoundAt P 9 b C_clock ν tr →
          ∀ F b₀ G₀ b_sol G_sol, VortData P K b ν tr μ A_m F b₀ G₀ b_sol G_sol →
            CoreVortWeakEqAt P b ν tr μ b₀ G₀ b_sol G_sol →
            ∀ Fn b₀n G₀n b_sol_n G_sol_n,
              CoreDuhamelRepSub.NiceDuhamelApprox P K b ν tr μ A_m C_clock F
                Fn b₀n G₀n b_sol_n G_sol_n →
              ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) (coreEnd ν b) →
                ∃ k : ℝ → ℝ × ℝ → ℂ, Measurable (Function.uncurry k) ∧
                  (∀ᵐ t ∂volume, t ∈ Ioo 0 s →
                    MemLp (k t) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9) ∧
                    HasZeroCirculation (ν ^ (-2 : ℝ)) (k t) ∧
                    xNorm (ν ^ (-2 : ℝ)) 9 (k t) ≤
                      ENNReal.ofReal (vortKernel C_clock P ν μ s t) *
                        coreSrcNorm (ν ^ (-2 : ℝ)) 9
                          (coreAdvSlice P.eigenvalue.re tr b₀ G₀ t)) ∧
                  corePerturbVort P.eigenvalue.re ν G₀ G_sol s
                    =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
                      fun x => ∫ t in Ioo 0 s, k t x

/-- **Assembly of `CoreDuhamelRep`** (`PartIII-a:T19/2/3/2/3/1`, SP 3481-3491) from
`CoreDuhamelNice` and `CoreDuhamelDensity`. -/
theorem coreDuhamelRep_of (hNice : CoreDuhamelNice) (hLim : CoreDuhamelDensity) :
    CoreDuhamelRep := by
  intro P hP K hK b hb
  obtain ⟨ν_flow, hν_flow, hFlow⟩ := CoreDuhamelRepSub.fullFlowExists_core
  obtain ⟨ν_ex, hν_ex, hTrEx⟩ := trainCausalExistence P hP K hK
  obtain ⟨ν_nice, hν_nice, hN⟩ := hNice P hP K hK b hb
  obtain ⟨ν_lim, hν_lim, hL⟩ := hLim P hP K hK b hb
  set ν₁ : ℝ := min (min ν_flow ν_ex) (min ν_nice ν_lim)
  have hν₁ : 0 < ν₁ := lt_min (lt_min hν_flow hν_ex) (lt_min hν_nice hν_lim)
  refine ⟨ν₁, hν₁, fun ν hν tr μ A_m C_clock hclock F b₀ G₀ b_sol G_sol hd hweak => ?_⟩
  by_cases hH : coreEnd ν b ≤ 0
  · exact Eventually.of_forall fun s hs => absurd (hs.1.trans hs.2) (not_lt.2 hH)
  push Not at hH
  have hν_f : ν ∈ Ioc 0 ν_flow := ⟨hν.1, hν.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hν_e : ν ∈ Ioc 0 ν_ex := ⟨hν.1, hν.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hν_n : ν ∈ Ioc 0 ν_nice := ⟨hν.1, hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hν_l : ν ∈ Ioc 0 ν_lim := ⟨hν.1, hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨Fn, b₀n, G₀n, b_sol_n, G_sol_n, hFn_nice, hhd_n, hwk_n, hFn_err⟩ :=
    CoreDuhamelRepSub.niceApproxSeq_exists hP hK hb hν_e hTrEx hd
  have hflow_tr : FullFlowExists ν (ν ^ (-2 : ℝ)) 9 tr := hFlow ν hν_f tr hd.1
  have hnice_n : ∀ n, ∃ f : ℝ → ℝ × ℝ → ℂ, _ := fun n =>
    hN ν hν_n tr hflow_tr μ A_m C_clock hclock (Fn n) (b₀n n) (G₀n n) (b_sol_n n) (G_sol_n n)
      (hFn_nice n) (hhd_n n) (hwk_n n)
  let fn : ℕ → ℝ → ℝ × ℝ → ℂ := fun n => Classical.choose (hnice_n n)
  have hfn_t : ∀ n, ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) (coreEnd ν b) →
      MemLp (fn n t) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9) ∧
      HasZeroCirculation (ν ^ (-2 : ℝ)) (fn n t) ∧
      ∀ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ),
        (∀ j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j φ (g j)) →
        h1Norm (ν ^ (-2 : ℝ)) 9 φ g ≤ 1 →
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), fn n t x * φ x =
          coreSrcFun (ν ^ (-2 : ℝ)) (coreAdvSlice P.eigenvalue.re tr (b₀n n) (G₀n n) t) g :=
    fun n => (Classical.choose_spec (hnice_n n)).1
  have hfn_s : ∀ n, ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) (coreEnd ν b) →
      ∃ k : ℝ → ℝ × ℝ → ℂ, Measurable (Function.uncurry k) ∧
        (∀ᵐ t ∂volume, t ∈ Ioo 0 s →
          ∃ (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ),
            IsLinearisedFlow ν (ν ^ (-2 : ℝ)) 9 tr t (fn n t) w u ∧
            k t =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
              fun x => ((t / s : ℝ) : ℂ) ^ μ *
                ((gainG P.eigenvalue.re ν t / gainG P.eigenvalue.re ν s : ℝ) : ℂ) * w s x) ∧
        corePerturbVort P.eigenvalue.re ν (G₀n n) (G_sol_n n) s
          =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
            fun x => ∫ t in Ioo 0 s, k t x :=
    fun n => (Classical.choose_spec (hnice_n n)).2
  have hslice_n : ∀ n, ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) (coreEnd ν b) →
      (∀ i, MemLp (fun x => gainConj P.eigenvalue.re ν (b₀n n) (t, x) i) 2
        (volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))) ∧
      (∀ i j, MemLp (fun x => gainConj P.eigenvalue.re ν (G₀n n) (t, x) i j) 2
        (volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))) :=
    fun n => CoreDuhamelRepSub.ae_freeSlice_memLp hν.1 hH (hhd_n n).2.2.2.2.2.2.2.1
  have ht_all := (ae_all_iff.2 hfn_t).and (ae_all_iff.2 hslice_n)
  have hs_all := ae_all_iff.2 hfn_s
  refine hL ν hν_l tr μ A_m C_clock hclock F b₀ G₀ b_sol G_sol hd hweak
    Fn b₀n G₀n b_sol_n G_sol_n ⟨hhd_n, hFn_err, ?_⟩
  filter_upwards [hs_all] with s hs_ex hsH
  have hex_n : ∀ n, ∃ k : ℝ → ℝ × ℝ → ℂ, _ := fun n => hs_ex n hsH
  let ks : ℕ → ℝ → ℝ × ℝ → ℂ := fun n => Classical.choose (hex_n n)
  have hks_m : ∀ n, Measurable (Function.uncurry (ks n)) :=
    fun n => (Classical.choose_spec (hex_n n)).1
  have hks_flow : ∀ n, ∀ᵐ t ∂volume, t ∈ Ioo 0 s →
      ∃ (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ),
        IsLinearisedFlow ν (ν ^ (-2 : ℝ)) 9 tr t (fn n t) w u ∧
        ks n t =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
          fun x => ((t / s : ℝ) : ℂ) ^ μ *
            ((gainG P.eigenvalue.re ν t / gainG P.eigenvalue.re ν s : ℝ) : ℂ) * w s x :=
    fun n => (Classical.choose_spec (hex_n n)).2.1
  have hks_rep : ∀ n, corePerturbVort P.eigenvalue.re ν (G₀n n) (G_sol_n n) s
      =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
        fun x => ∫ t in Ioo 0 s, ks n t x :=
    fun n => (Classical.choose_spec (hex_n n)).2.2
  refine ⟨ks, hks_m, hks_rep, ?_⟩
  filter_upwards [ht_all, ae_all_iff.2 hks_flow] with t ht_good ht_fl hts
  have htH : t ∈ Ioo (0 : ℝ) (coreEnd ν b) := ⟨hts.1, hts.2.trans hsH.2⟩
  refine ⟨fun n => ?_, fun n m => ?_⟩
  · obtain ⟨hmem_f, hzc_f, hpair_f⟩ := ht_good.1 n htH
    obtain ⟨w, u, hw, hkae⟩ := ht_fl n hts
    obtain ⟨hmem_k, hzc_k, hbd_k⟩ :=
      CoreDuhamelRepSub.duhamelPiece_bounds hν.1 hclock hts.1 hts.2 hsH.2.le hmem_f hzc_f hw hkae
    rw [CoreDuhamelRepSub.negNorm_eq_coreSrcNorm hpair_f] at hbd_k
    exact ⟨hmem_k, hzc_k, hbd_k⟩
  · obtain ⟨hmem_n, hzc_n, hpair_n⟩ := ht_good.1 n htH
    obtain ⟨hmem_m, hzc_m, hpair_m⟩ := ht_good.1 m htH
    obtain ⟨wn, un, hwn, hkae_n⟩ := ht_fl n hts
    obtain ⟨wm, um, hwm, hkae_m⟩ := ht_fl m hts
    have hmem_sub : MemLp (fun x => fn n t x - fn m t x) 2
        (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9) := hmem_n.sub hmem_m
    have hzc_sub : HasZeroCirculation (ν ^ (-2 : ℝ)) (fun x => fn n t x - fn m t x) := by
      refine ⟨hzc_n.1.sub hzc_m.1, ?_⟩
      rw [integral_sub hzc_n.1 hzc_m.1, hzc_n.2, hzc_m.2, sub_self]
    have hw_sub := CoreDuhamelRepSub.isLinearisedFlow_sub hmem_n hmem_m hwn hwm
    have hkae_sub : (fun x => ks n t x - ks m t x)
        =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
          fun x => ((t / s : ℝ) : ℂ) ^ μ *
            ((gainG P.eigenvalue.re ν t / gainG P.eigenvalue.re ν s : ℝ) : ℂ) *
            (wn s x - wm s x) := by
      filter_upwards [hkae_n, hkae_m] with x hxn hxm
      rw [hxn, hxm]
      ring
    obtain ⟨_, _, hbd_sub⟩ :=
      CoreDuhamelRepSub.duhamelPiece_bounds hν.1 hclock hts.1 hts.2 hsH.2.le
        hmem_sub hzc_sub hw_sub hkae_sub
    have hneg_eq := CoreDuhamelRepSub.negNorm_sub_eq_coreSrcNorm hν.1 hd.2.2.1 hd.2.2.2.1 htH
      (hhd_n n).2.2.2.2.2.2.2.1.measurable (hhd_n n).2.2.2.2.2.2.2.1.gradMeasurable
      (hhd_n m).2.2.2.2.2.2.2.1.measurable (hhd_n m).2.2.2.2.2.2.2.1.gradMeasurable
      (ht_good.2 n htH).1 (ht_good.2 n htH).2 (ht_good.2 m htH).1 (ht_good.2 m htH).2
      hmem_n hmem_m hpair_n hpair_m
    rwa [hneg_eq] at hbd_sub

end UnforcedLeray.Short.IIIa

end
