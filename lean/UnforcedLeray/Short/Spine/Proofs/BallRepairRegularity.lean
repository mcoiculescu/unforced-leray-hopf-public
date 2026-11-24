import UnforcedLeray.Short.Spine.Sub.SP_PII
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularityProof
import UnforcedLeray.Short.PartIIb.Tasks.WindowComparison
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQMem.Ddu
import UnforcedLeray.Lib.LerayLp.RieszLp

/-!
# `Spine:SP-PII/2`: `BallRepairRegularity`

Source of record: `the November 2 reference manuscript`, lines 2524-2562, 1219, 2556.

Proves `UnforcedLeray.Short.Spine.SPPII.ballRepairRegularity : BallRepairRegularity`:
1. Joint smoothness of `p.corr z` on `SpaceTime` from `IIb.strongRegularity_proof`,
   `PartIIIb.Concrete.rawJointSmooth`, and `PartIIIb.Concrete.inlet_contDiff_joint`.
2. `L^{11/4}(periodSlab p.period)` bound for `j = 1` (`iteratedFDeriv ℝ 1 (p.corr z ·) ·`)
   from `IIb.differentiatedEquationGraphBound_of`, `IIb.contRepFDerivLeSumGrad_proof`,
   and `IIb.corr_iterated_eLpNorm_bgp_le`, integrated over the period slab.
3. `L^{11/4}(periodSlab p.period)` bound for `j = 2` (`iteratedFDeriv ℝ 2 (p.corr z ·) ·`)
   from `B0411.nuLapD` of `B0412.XToD (p.graphX z)` and the Calderón–Zygmund `L^{11/4}`
   Riesz pair bound `RieszLp.rieszPairLp`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Spine.SPPII

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Blueprint.Planar
open UnforcedLeray.Cons.C03.Concrete (Params)

/-- Slab `L^{11/4}(periodSlab P)` bound from an a.e. slice `L^{11/4}(ℝ³)` bound on `Ioc 0 P`. -/
private lemma eLpNorm_periodSlab_le_of_slice {E : Type*} [NormedAddCommGroup E]
    {P B : ℝ} (hP : 0 < P) (hB : 0 ≤ B) {F : SpaceTime → E}
    (hF : AEStronglyMeasurable F (volume.restrict (periodSlab P)))
    (hslice : ∀ᵐ τ ∂(volume.restrict (Ioc 0 P)),
      eLpNorm (fun y : Space => F (τ, y)) (11 / 4 : ℝ≥0∞) volume ≤ ENNReal.ofReal B) :
    MemLp F (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab P)) ∧
      (eLpNorm F (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab P))).toReal ≤
        P ^ ((4 : ℝ) / 11) * B := by
  have hq_pos : (0 : ℝ) < 11 / 4 := by norm_num
  have hq_ne0 : (11 / 4 : ℝ≥0∞) ≠ 0 := by norm_num
  have hq_eq : (11 / 4 : ℝ≥0∞) = ENNReal.ofReal (11 / 4) := by
    have h11 : (11 : ℝ≥0∞) = ENNReal.ofReal 11 := by norm_num
    have h4 : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by norm_num
    rw [h11, h4, ← ENNReal.ofReal_div_of_pos (by norm_num)]
  have hq_netop : (11 / 4 : ℝ≥0∞) ≠ ⊤ := by rw [hq_eq]; exact ENNReal.ofReal_ne_top
  have hq_toReal : (11 / 4 : ℝ≥0∞).toReal = 11 / 4 := by
    rw [hq_eq, ENNReal.toReal_ofReal (by norm_num)]
  have hprod : (volume.restrict (periodSlab P) : Measure SpaceTime) =
      (volume.restrict (Ioc 0 P)).prod volume := by
    unfold periodSlab
    rw [← Measure.restrict_univ (μ := (volume : Measure Space)), Measure.prod_restrict,
      Measure.volume_eq_prod]
  have hsl_int : ∀ᵐ τ ∂(volume.restrict (Ioc 0 P)),
      ∫⁻ y : Space, ‖F (τ, y)‖ₑ ^ (11 / 4 : ℝ) ≤ ENNReal.ofReal B ^ (11 / 4 : ℝ) := by
    filter_upwards [hslice] with τ hτ
    have hτ' : (∫⁻ y : Space, ‖F (τ, y)‖ₑ ^ (11 / 4 : ℝ)) ^ (1 / (11 / 4 : ℝ)) ≤
        ENNReal.ofReal B := by
      rwa [eLpNorm_eq_lintegral_rpow_enorm_toReal hq_ne0 hq_netop, hq_toReal] at hτ
    have hr := ENNReal.rpow_le_rpow hτ' hq_pos.le
    rwa [one_div, ENNReal.rpow_inv_rpow hq_pos.ne'] at hr
  have hlint_prod : ∫⁻ x : SpaceTime, ‖F x‖ₑ ^ (11 / 4 : ℝ) ∂(volume.restrict (periodSlab P)) ≤
      ENNReal.ofReal P * ENNReal.ofReal B ^ (11 / 4 : ℝ) := by
    have hm : AEMeasurable (fun x : SpaceTime => ‖F x‖ₑ ^ (11 / 4 : ℝ))
        ((volume.restrict (Ioc 0 P)).prod volume) := by
      rw [← hprod]; exact hF.enorm.pow_const _
    rw [hprod, lintegral_prod _ hm]
    calc ∫⁻ τ : ℝ, (∫⁻ y : Space, ‖F (τ, y)‖ₑ ^ (11 / 4 : ℝ) ∂volume) ∂(volume.restrict (Ioc 0 P))
        ≤ ∫⁻ _ : ℝ, ENNReal.ofReal B ^ (11 / 4 : ℝ) ∂(volume.restrict (Ioc 0 P)) :=
          lintegral_mono_ae hsl_int
      _ = ENNReal.ofReal B ^ (11 / 4 : ℝ) * volume (Ioc 0 P) := setLIntegral_const _ _
      _ = ENNReal.ofReal P * ENNReal.ofReal B ^ (11 / 4 : ℝ) := by
          rw [Real.volume_Ioc, sub_zero, mul_comm]
  have heLp_le : eLpNorm F (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab P)) ≤
      ENNReal.ofReal (P ^ ((4 : ℝ) / 11) * B) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq_ne0 hq_netop, hq_toReal]
    calc (∫⁻ x : SpaceTime, ‖F x‖ₑ ^ (11 / 4 : ℝ) ∂(volume.restrict (periodSlab P))) ^
            (1 / (11 / 4 : ℝ))
        ≤ (ENNReal.ofReal P * ENNReal.ofReal B ^ (11 / 4 : ℝ)) ^ (1 / (11 / 4 : ℝ)) :=
          ENNReal.rpow_le_rpow hlint_prod (by positivity)
      _ = ENNReal.ofReal P ^ ((4 : ℝ) / 11) *
            (ENNReal.ofReal B ^ (11 / 4 : ℝ)) ^ (1 / (11 / 4 : ℝ)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
          norm_num
      _ = ENNReal.ofReal (P ^ ((4 : ℝ) / 11)) * ENNReal.ofReal B := by
          rw [← ENNReal.ofReal_rpow_of_pos hP, one_div, ENNReal.rpow_rpow_inv hq_pos.ne']
      _ = ENNReal.ofReal (P ^ ((4 : ℝ) / 11) * B) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
  refine ⟨⟨hF, lt_of_le_of_lt heLp_le ENNReal.ofReal_lt_top⟩, ?_⟩
  calc (eLpNorm F (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab P))).toReal
      ≤ (ENNReal.ofReal (P ^ ((4 : ℝ) / 11) * B)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top heLp_le
    _ = P ^ ((4 : ℝ) / 11) * B := ENNReal.toReal_ofReal (mul_nonneg (by positivity) hB)

/-- Joint smoothness of `p.corr z` on `SpaceTime` from `IIb.strongRegularity_proof`,
`rawJointSmooth`, and `inlet_contDiff_joint`. -/
private lemma corr_joint_smooth_aux
    (lam : ℂ) (q : Profile) (hq : IsGrowingEigenpair lam q)
    {p : Params} {d dm dp : ℝ} (hreg : IIb.BgRegime p d dm dp)
    (hν1 : p.ν ≤ 1) (hmode : p.mode = q) (z : p.Z)
    (hbg : ContDiff ℝ ∞ (fun x : ℝ × Space => IIb.bgField p z x.1 x.2))
    (hraw : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2)) :
    ContDiff ℝ ∞ (fun x : SpaceTime => p.corr z x.1 x.2) := by
  have hinlet : ContDiff ℝ ∞ (fun x : SpaceTime => ∑ i : Fin 2, p.coord z i • p.inlet i x.1 x.2) :=
    ContDiff.sum fun i _ =>
      (contDiff_const (c := p.coord z i)).smul
        (PartIIIb.Concrete.inlet_contDiff_joint lam q hq hreg hν1 hmode i)
  have heq : (fun x : SpaceTime => p.corr z x.1 x.2) =
      fun x : SpaceTime => IIb.bgField p z x.1 x.2 -
        (p.raw x.1 x.2 + ∑ i : Fin 2, p.coord z i • p.inlet i x.1 x.2) := by
    funext x
    simp only [IIb.bgField]
    abel
  rw [heq]
  exact hbg.sub (hraw.add hinlet)

/-- Joint continuity of spatial `iteratedFDeriv ℝ j (u x.1) x.2` when `u` is jointly `C^∞`. -/
private lemma continuous_spatial_iteratedFDeriv_of_contDiff {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℝ → E → F} (hu : ContDiff ℝ ∞ (fun x : ℝ × E => u x.1 x.2)) (j : ℕ) :
    Continuous (fun x : ℝ × E => iteratedFDeriv ℝ j (u x.1) x.2) := by
  have heq : (fun x : ℝ × E => iteratedFDeriv ℝ j (u x.1) x.2) =
      fun x : ℝ × E => (iteratedFDeriv ℝ j (fun p : ℝ × E => u p.1 p.2) x).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ E) := by
    funext x
    ext v
    have h1 : u x.1 = (fun p : ℝ × E => u (x.1 + p.1) p.2) ∘
        ContinuousLinearMap.inr ℝ ℝ E := by
      funext y; simp
    have h2 : (fun p : ℝ × E => u (x.1 + p.1) p.2) =
        (fun p : ℝ × E => u p.1 p.2) ∘ (fun p : ℝ × E => (x.1, (0 : E)) + p) := by
      funext p; simp
    have hf : ContDiff ℝ ∞ (fun p : ℝ × E => u (x.1 + p.1) p.2) :=
      hu.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)
    rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ hf _ (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))]
    rw [h2]
    have h3 : iteratedFDeriv ℝ j ((fun q : ℝ × E => u q.1 q.2) ∘ fun p : ℝ × E => (x.1, (0 : E)) + p)
        (ContinuousLinearMap.inr ℝ ℝ E x.2) =
        iteratedFDeriv ℝ j (fun p : ℝ × E => u p.1 p.2) x :=
      (iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := fun q : ℝ × E => u q.1 q.2) j
        (x.1, (0 : E)) (ContinuousLinearMap.inr ℝ ℝ E x.2)).trans (by simp)
    change ((iteratedFDeriv ℝ j ((fun q : ℝ × E => u q.1 q.2) ∘ fun p : ℝ × E => (x.1, (0 : E)) + p)
      (ContinuousLinearMap.inr ℝ ℝ E x.2)).compContinuousLinearMap
      (fun _ => ContinuousLinearMap.inr ℝ ℝ E)) v = _
    rw [h3]
  rw [heq]
  have hc : Continuous (fun x : ℝ × E => iteratedFDeriv ℝ j (fun p : ℝ × E => u p.1 p.2) x) :=
    hu.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin j => ContinuousLinearMap.inr ℝ ℝ E)).continuous.comp hc

/-- Slab `L^{11/4}` bound for `j = 1` (`iteratedFDeriv ℝ 1 (p.corr z ·) ·`). -/
private lemma corr_fderiv_slab_aux
    {p : Params} (hP1 : p.period ≤ 1) (z : p.Z)
    (hcorr : ContDiff ℝ ∞ (fun x : SpaceTime => p.corr z x.1 x.2))
    (g : Fin 3 → B0411.D p.period p.ν B0412.q0E)
    (hg_op : ∀ j : Fin 3,
      PhaseSpace.HasPhaseOp (fun Φ => -PhaseSpace.dy j Φ) (p.wOf z) (g j : PhaseSpace.Yq p.period B0412.q0E))
    {B : ℝ} (hB : 0 ≤ B) (hg_bd : ∀ j : Fin 3, B0411.graphNormD (g j) ≤ B) :
    MemLp (fun x : SpaceTime => iteratedFDeriv ℝ 1 (p.corr z x.1) x.2) (11 / 4 : ℝ≥0∞)
        (volume.restrict (periodSlab p.period)) ∧
      (eLpNorm (fun x : SpaceTime => iteratedFDeriv ℝ 1 (p.corr z x.1) x.2) (11 / 4 : ℝ≥0∞)
        (volume.restrict (periodSlab p.period))).toReal ≤
        p.period ^ ((4 : ℝ) / 11) * (3 * B) := by
  have hP0 : 0 < p.period := p.period_pos
  have : Fact (0 < p.period) := ⟨hP0⟩
  have hcont_fd : Continuous (fun x : SpaceTime => iteratedFDeriv ℝ 1 (p.corr z x.1) x.2) :=
    continuous_spatial_iteratedFDeriv_of_contDiff hcorr 1
  have hslice : ∀ᵐ τ ∂(volume.restrict (Ioc 0 p.period)),
      eLpNorm (fun y : Space => iteratedFDeriv ℝ 1 (p.corr z τ) y) (11 / 4 : ℝ≥0∞) volume ≤
        ENNReal.ofReal (3 * B) := by
    refine ae_of_all _ fun τ => ?_
    have hq_eq : (11 / 4 : ℝ≥0∞) = ENNReal.ofReal IIb.bgp := by
      rw [IIb.S1Sub.s1_ofReal_bgp_eq_q0E, B0412.q0E]
      have h11 : (11 : ℝ≥0∞) = ENNReal.ofReal 11 := by norm_num
      have h4 : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by norm_num
      rw [h11, h4, ← ENNReal.ofReal_div_of_pos (by norm_num)]
      unfold B0281.q0; norm_num
    rw [hq_eq]
    have hle : ∀ y : Space, ‖iteratedFDeriv ℝ 1 (p.corr z τ) y‖ ≤
        ∑ α : Fin 1 → Fin 3, ‖Cons.C03.Concrete.contRep (g (α 0) : PhaseSpace.Yq p.period B0412.q0E) τ y‖ := by
      intro y
      rw [norm_iteratedFDeriv_one,
        Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 3))
          (fun α : Fin 1 → Fin 3 => ‖Cons.C03.Concrete.contRep (g (α 0) : PhaseSpace.Yq p.period B0412.q0E) τ y‖)
          (fun j : Fin 3 => ‖Cons.C03.Concrete.contRep (g j : PhaseSpace.Yq p.period B0412.q0E) τ y‖)
          (fun _ => rfl)]
      let u := B0412.XToD (p.graphX z)
      have hu_eq : (u : PhaseSpace.Yq p.period B0412.q0E) = p.wOf z := rfl
      have hfd := IIb.contRepFDerivLeSumGrad_proof p.period hP1 p.ν p.ν_pos u g
        (fun j => by rw [hu_eq]; exact hg_op j) τ y
      exact hfd
    have hcb := IIb.corr_iterated_eLpNorm_bgp_le p hP1 z 1 (fun α => g (α 0)) τ hle
    refine hcb.trans (ENNReal.ofReal_le_ofReal ?_)
    calc ∑ α : Fin 1 → Fin 3, B0411.graphNormD (g (α 0))
        = ∑ j : Fin 3, B0411.graphNormD (g j) := Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 3)) _ _ (fun _ => rfl)
      _ ≤ ∑ _j : Fin 3, B := Finset.sum_le_sum fun j _ => hg_bd j
      _ = 3 * B := by simp [mul_comm]
  exact eLpNorm_periodSlab_le_of_slice hP0 (by positivity) hcont_fd.aestronglyMeasurable hslice

/-- Periodic lift of a smooth compactly supported scalar test on `Ioo 0 P ×ˢ univ` to a
`CVec3`-valued `IsPhaseTest P` along coordinate `b`. -/
private def periodizeTest (P : ℝ) (φ : SpaceTime → ℝ) (b : Fin 3) :
    ℝ × Space → PhaseSpace.CVec3 :=
  fun x => ((∑' k : ℤ, φ (x.1 - (k : ℝ) * P, x.2) : ℝ) : ℂ) •
    (EuclideanSpace.single b (1 : ℂ))

private lemma periodizeTest_eq_on_Ioc {P : ℝ} (hP : 0 < P) {φ : SpaceTime → ℝ}
    (hφs : tsupport φ ⊆ Ioo 0 P ×ˢ univ) (b : Fin 3) {t : ℝ} (ht : t ∈ Ioc 0 P) (y : Space) :
    periodizeTest P φ b (t, y) = ((φ (t, y) : ℝ) : ℂ) • (EuclideanSpace.single b (1 : ℂ)) := by
  unfold periodizeTest
  congr 2
  rw [tsum_eq_single (0 : ℤ)]
  · simp
  · intro k hk
    have hnot : (t - (k : ℝ) * P, y) ∉ tsupport φ := by
      intro hmem
      have hIoo := (hφs hmem).1
      rcases lt_or_gt_of_ne hk with hkneg | hkpos
      · have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hkneg
        nlinarith [ht.1, ht.2, hIoo.1, hIoo.2]
      · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
        nlinarith [ht.1, ht.2, hIoo.1, hIoo.2]
    exact image_eq_zero_of_notMem_tsupport hnot

private lemma isPhaseTest_periodizeTest {P : ℝ} (hP : 0 < P) {φ : SpaceTime → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo 0 P ×ˢ univ)
    (b : Fin 3) : PhaseSpace.IsPhaseTest P (periodizeTest P φ b) where
  smooth := by
    rw [contDiff_iff_contDiffAt]
    intro x₀
    let K : Finset ℤ := Finset.Icc (⌊x₀.1 / P⌋ - 2) (⌊x₀.1 / P⌋ + 2)
    have hev : (fun x : ℝ × Space => periodizeTest P φ b x) =ᶠ[𝓝 x₀]
        fun x : ℝ × Space => ((∑ k ∈ K, φ (x.1 - (k : ℝ) * P, x.2) : ℝ) : ℂ) •
          (EuclideanSpace.single b (1 : ℂ)) := by
      filter_upwards [Metric.ball_mem_nhds x₀ (by positivity : 0 < P / 2)] with x hx
      unfold periodizeTest
      congr 2
      refine tsum_eq_sum fun k hk => ?_
      have hnot : (x.1 - (k : ℝ) * P, x.2) ∉ tsupport φ := by
        intro hmem
        have hIoo := (hφs hmem).1
        have hdist : |x.1 - x₀.1| < P / 2 :=
          (norm_fst_le (x - x₀)).trans_lt (mem_ball_iff_norm.mp hx)
        have hx_lo : x₀.1 - P / 2 < x.1 := by linarith [abs_lt.mp hdist]
        have hx_hi : x.1 < x₀.1 + P / 2 := by linarith [abs_lt.mp hdist]
        have hfl := Int.floor_le (x₀.1 / P)
        have hfl1 := Int.lt_floor_add_one (x₀.1 / P)
        simp only [K, Finset.mem_Icc, not_and, not_le] at hk
        by_cases hle : ⌊x₀.1 / P⌋ - 2 ≤ k
        · have hgt : ⌊x₀.1 / P⌋ + 2 < k := hk hle
          have hk1 : ((⌊x₀.1 / P⌋ + 3 : ℤ) : ℝ) ≤ (k : ℝ) := by
            exact_mod_cast (by omega : ⌊x₀.1 / P⌋ + 3 ≤ k)
          push_cast at hk1
          have : (k : ℝ) * P ≥ (x₀.1 / P + 2) * P := by nlinarith
          have : (x₀.1 / P + 2) * P = x₀.1 + 2 * P := by field_simp
          linarith [hIoo.1]
        · have hlt : k < ⌊x₀.1 / P⌋ - 2 := not_le.mp hle
          have hk1 : (k : ℝ) ≤ ((⌊x₀.1 / P⌋ - 3 : ℤ) : ℝ) := by
            exact_mod_cast (by omega : k ≤ ⌊x₀.1 / P⌋ - 3)
          push_cast at hk1
          have : (k : ℝ) * P ≤ (x₀.1 / P - 3) * P := by nlinarith
          have : (x₀.1 / P - 3) * P = x₀.1 - 3 * P := by field_simp
          linarith [hIoo.2]
      exact image_eq_zero_of_notMem_tsupport hnot
    have hsm1 : ContDiff ℝ ∞ (fun x : ℝ × Space => ∑ k ∈ K, φ (x.1 - (k : ℝ) * P, x.2)) :=
      ContDiff.sum fun k _ => hφ.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
    have hsm : ContDiff ℝ ∞ (fun x : ℝ × Space =>
        ((∑ k ∈ K, φ (x.1 - (k : ℝ) * P, x.2) : ℝ) : ℂ) •
          (EuclideanSpace.single b (1 : ℂ))) :=
      (Complex.ofRealCLM.contDiff.comp hsm1).smul (contDiff_const (c := EuclideanSpace.single b (1 : ℂ)))
    exact hsm.contDiffAt.congr_of_eventuallyEq hev
  periodic x y := by
    unfold periodizeTest
    congr 2
    rw [← (Equiv.addRight (-1 : ℤ)).tsum_eq (fun k : ℤ => φ (x - (k : ℝ) * P, y))]
    congr 1; funext k
    change φ (x + P - (k : ℝ) * P, y) = φ (x - ((k + (-1 : ℤ) : ℤ) : ℝ) * P, y)
    push_cast
    ring_nf
  bounded_support := by
    obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall (0 : SpaceTime)
    refine ⟨max R 0 + 1, fun t y hy => ?_⟩
    unfold periodizeTest
    have hzero : ∀ k : ℤ, φ (t - (k : ℝ) * P, y) = 0 := by
      intro k
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have hball := hR hmem
      rw [mem_closedBall_zero_iff] at hball
      have hy2 : ‖y‖ ≤ ‖(t - (k : ℝ) * P, y)‖ := by
        simp
      linarith [le_max_left R 0]
    simp [hzero]

/-- On `Ioo 0 P ×ˢ univ`, `periodizeTest P φ b` has `nuLapT` equal to `ν * Heat.laplacian` of `φ`. -/
private lemma nuLapT_periodizeTest_eq_on_Ioo {P ν : ℝ} (hP : 0 < P) {φ : SpaceTime → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφs : tsupport φ ⊆ Ioo 0 P ×ˢ univ) (b : Fin 3)
    {t : ℝ} (ht : t ∈ Ioo 0 P) (y : Space) :
    PhaseSpace.nuLapT ν (periodizeTest P φ b) (t, y) =
      ((ν * UnforcedLeray.Heat.laplacian (fun y' => φ (t, y')) y : ℝ) : ℂ) •
        (EuclideanSpace.single b (1 : ℂ)) := by
  have hev : ∀ x : ℝ × Space, x ∈ Ioo 0 P ×ˢ univ →
      periodizeTest P φ b x = ((φ x : ℝ) : ℂ) • (EuclideanSpace.single b (1 : ℂ)) :=
    fun x hx => periodizeTest_eq_on_Ioc hP hφs b (Ioo_subset_Ioc_self hx.1) x.2
  have hev_nhds : ∀ x ∈ Ioo 0 P ×ˢ (univ : Set Space),
      periodizeTest P φ b =ᶠ[𝓝 x]
        fun p : ℝ × Space => ((φ p : ℝ) : ℂ) • (EuclideanSpace.single b (1 : ℂ)) :=
    fun x hx => Filter.Eventually.mono ((isOpen_Ioo.prod isOpen_univ).mem_nhds hx) hev
  have hdy : ∀ (j : Fin 3) (x : ℝ × Space), x ∈ Ioo 0 P ×ˢ (univ : Set Space) →
      PhaseSpace.dy j (periodizeTest P φ b) x =
        ((fderiv ℝ (fun y' => φ (x.1, y')) x.2 (EuclideanSpace.single j (1 : ℝ)) : ℝ) : ℂ) •
          (EuclideanSpace.single b (1 : ℂ)) := by
    intro j x hx
    unfold PhaseSpace.dy
    rw [(hev_nhds x hx).fderiv_eq]
    have hdiff : DifferentiableAt ℝ φ x := hφ.differentiable (by simp) x
    have hf1 : HasFDerivAt (fun p : ℝ × Space => ((φ p : ℝ) : ℂ) • (EuclideanSpace.single b (1 : ℂ)))
        ((Complex.ofRealCLM.comp (fderiv ℝ φ x)).smulRight (EuclideanSpace.single b (1 : ℂ))) x :=
      (Complex.ofRealCLM.hasFDerivAt.comp x hdiff.hasFDerivAt).smul_const
        (EuclideanSpace.single b (1 : ℂ))
    rw [hf1.fderiv]
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      Complex.ofRealCLM_apply]
    congr 2
    have hslice : (fun y' : Space => φ (x.1, y')) = φ ∘ (fun y' => (x.1, y')) := rfl
    have haff : HasFDerivAt (fun y' : Space => (x.1, y')) (ContinuousLinearMap.inr ℝ ℝ Space) x.2 :=
      (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2)
    rw [hslice, (hdiff.hasFDerivAt.comp x.2 haff).fderiv]
    rfl
  have hdy2 : ∀ j : Fin 3,
      PhaseSpace.dy j (PhaseSpace.dy j (periodizeTest P φ b)) (t, y) =
        ((fderiv ℝ (fun y' => fderiv ℝ (fun y'' => φ (t, y'')) y' (EuclideanSpace.single j (1 : ℝ)))
          y (EuclideanSpace.single j (1 : ℝ)) : ℝ) : ℂ) •
          (EuclideanSpace.single b (1 : ℂ)) := by
    intro j
    have hev2 : PhaseSpace.dy j (periodizeTest P φ b) =ᶠ[𝓝 (t, y)]
        fun p : ℝ × Space =>
          ((fderiv ℝ (fun y' => φ (p.1, y')) p.2 (EuclideanSpace.single j (1 : ℝ)) : ℝ) : ℂ) •
            (EuclideanSpace.single b (1 : ℂ)) :=
      Filter.Eventually.mono ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, trivial⟩) (hdy j)
    have hfd : fderiv ℝ (PhaseSpace.dy j (periodizeTest P φ b)) (t, y) =
        fderiv ℝ (fun p : SpaceTime =>
          ↑((fderiv ℝ (fun y' => φ (p.1, y')) p.2) (EuclideanSpace.single j 1)) •
            EuclideanSpace.single b 1) (t, y) := hev2.fderiv_eq
    change (fderiv ℝ (PhaseSpace.dy j (periodizeTest P φ b)) (t, y)) (0, coordinateVector j) = _
    rw [hfd]
    let g : ℝ × Space → ℝ :=
      fun p => fderiv ℝ (fun y' => φ (p.1, y')) p.2 (EuclideanSpace.single j (1 : ℝ))
    have hg_smooth : ContDiff ℝ ∞ g := by
      have hg_eq : g = fun p => (fderiv ℝ φ p) (0, EuclideanSpace.single j (1 : ℝ)) := by
        funext p
        have hdiff := hφ.differentiable (by simp) p
        have haff : HasFDerivAt (fun y' : Space => (p.1, y')) (ContinuousLinearMap.inr ℝ ℝ Space) p.2 :=
          (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
        have hslice : (fun y' : Space => φ (p.1, y')) = φ ∘ (fun y' => (p.1, y')) := rfl
        dsimp only [g]
        rw [hslice, (hdiff.hasFDerivAt.comp p.2 haff).fderiv]
        rfl
      rw [hg_eq]
      exact (hφ.fderiv_right (by simp)).clm_apply contDiff_const
    have hdiff : DifferentiableAt ℝ g (t, y) := hg_smooth.differentiable (by simp) (t, y)
    have hf1 : HasFDerivAt (fun p : ℝ × Space => g p • (EuclideanSpace.single b (1 : ℂ)))
        ((fderiv ℝ g (t, y)).smulRight (EuclideanSpace.single b (1 : ℂ)))
        (t, y) :=
      hdiff.hasFDerivAt.smul_const (EuclideanSpace.single b (1 : ℂ))
    change (fderiv ℝ (fun p : ℝ × Space => g p • EuclideanSpace.single b (1 : ℂ)) (t, y))
        (0, coordinateVector j) = _
    have h_eq : (fderiv ℝ g (t, y)) (0, coordinateVector j) =
        (fderiv ℝ (fun y' => (fderiv ℝ (fun y'' => φ (t, y'')) y') (EuclideanSpace.single j (1 : ℝ))) y)
          (EuclideanSpace.single j (1 : ℝ)) := by
      have hslice : (fun y' : Space => g (t, y')) = g ∘ (fun y' => (t, y')) := rfl
      have haff : HasFDerivAt (fun y' : Space => (t, y')) (ContinuousLinearMap.inr ℝ ℝ Space) y :=
        (hasFDerivAt_const t y).prodMk (hasFDerivAt_id y)
      have hcomp := (hdiff.hasFDerivAt.comp y haff).fderiv
      have hfun : (fun y' : Space => g (t, y')) =
          fun y' => (fderiv ℝ (fun y'' => φ (t, y'')) y') (EuclideanSpace.single j (1 : ℝ)) := rfl
      rw [← hfun, hslice, hcomp]
      rfl
    rw [hf1.fderiv, ContinuousLinearMap.smulRight_apply, h_eq]
    ext i
    simp
  unfold PhaseSpace.nuLapT PhaseSpace.lapT
  simp only [Pi.smul_apply, hdy2]
  ext i
  by_cases hi : i = b <;>
    simp [UnforcedLeray.Heat.laplacian, coordinateVector, Finset.mul_sum, hi]

private lemma re_dotL_smul_single (c : ℂ) (b : Fin 3) (v : PhaseSpace.CVec3) :
    (PhaseSpace.dotL (c • EuclideanSpace.single b (1 : ℂ)) v).re = (c * v b).re := by
  rw [PhaseSpace.dotL_apply]
  simp

private lemma integral_laplacian_mul_eq {f g : Space → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) :
    ∫ y, f y * UnforcedLeray.Heat.laplacian g y =
      ∫ y, UnforcedLeray.Heat.laplacian f y * g y := by
  unfold UnforcedLeray.Heat.laplacian
  have h1 : ∀ y, f y * ∑ i : Fin 3,
      (fderiv ℝ (fun y' => fderiv ℝ g y' (coordinateVector i)) y) (coordinateVector i) =
      ∑ i : Fin 3, f y *
        (fderiv ℝ (fun y' => fderiv ℝ g y' (coordinateVector i)) y) (coordinateVector i) :=
    fun y => Finset.mul_sum _ _ _
  have h2 : ∀ y, (∑ i : Fin 3,
      (fderiv ℝ (fun y' => fderiv ℝ f y' (coordinateVector i)) y) (coordinateVector i)) * g y =
      ∑ i : Fin 3,
        (fderiv ℝ (fun y' => fderiv ℝ f y' (coordinateVector i)) y) (coordinateVector i) * g y :=
    fun y => Finset.sum_mul _ _ _
  simp_rw [h1, h2]
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hg1 : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  have hintL : ∀ i : Fin 3, Integrable (fun y =>
      f y * (fderiv ℝ (fun y' => fderiv ℝ g y' (coordinateVector i)) y) (coordinateVector i))
      volume := by
    intro i
    have hcd : ContDiff ℝ ∞ (fun y' => fderiv ℝ g y' (coordinateVector i)) :=
      hg1.clm_apply contDiff_const
    have hcs : HasCompactSupport (fun y' => fderiv ℝ g y' (coordinateVector i)) :=
      hgs.fderiv_apply ℝ (coordinateVector i)
    have hcd2 : ContDiff ℝ ∞ (fun y =>
        (fderiv ℝ (fun y' => fderiv ℝ g y' (coordinateVector i)) y) (coordinateVector i)) :=
      (hcd.fderiv_right (by simp)).clm_apply contDiff_const
    have hcs2 : HasCompactSupport (fun y =>
        (fderiv ℝ (fun y' => fderiv ℝ g y' (coordinateVector i)) y) (coordinateVector i)) :=
      hcs.fderiv_apply ℝ (coordinateVector i)
    exact (hf.continuous.mul hcd2.continuous).integrable_of_hasCompactSupport hcs2.mul_left
  have hintR : ∀ i : Fin 3, Integrable (fun y =>
      (fderiv ℝ (fun y' => fderiv ℝ f y' (coordinateVector i)) y) (coordinateVector i) * g y)
      volume := by
    intro i
    have hcd : ContDiff ℝ 1 (fun y' => fderiv ℝ f y' (coordinateVector i)) :=
      hf1.clm_apply contDiff_const
    have hcd2 : ContDiff ℝ 0 (fun y =>
        (fderiv ℝ (fun y' => fderiv ℝ f y' (coordinateVector i)) y) (coordinateVector i)) :=
      (hcd.fderiv_right (by norm_num)).clm_apply contDiff_const
    exact (hcd2.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgs.mul_left
  rw [integral_finsetSum _ (fun i _ => hintL i), integral_finsetSum _ (fun i _ => hintR i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcd_gi : ContDiff ℝ ∞ (fun y' => fderiv ℝ g y' (coordinateVector i)) :=
    hg1.clm_apply contDiff_const
  have hcs_gi : HasCompactSupport (fun y' => fderiv ℝ g y' (coordinateVector i)) :=
    hgs.fderiv_apply ℝ (coordinateVector i)
  have hcd_fi : ContDiff ℝ 1 (fun y' => fderiv ℝ f y' (coordinateVector i)) :=
    hf1.clm_apply contDiff_const
  have hintM : Integrable (fun y =>
      fderiv ℝ f y (coordinateVector i) * fderiv ℝ g y (coordinateVector i)) volume :=
    (hcd_fi.continuous.mul hcd_gi.continuous).integrable_of_hasCompactSupport hcs_gi.mul_left
  have hint_fg : Integrable (fun y => f y * fderiv ℝ g y (coordinateVector i)) volume :=
    (hf.continuous.mul hcd_gi.continuous).integrable_of_hasCompactSupport hcs_gi.mul_left
  have hint_f'g : Integrable (fun y => fderiv ℝ f y (coordinateVector i) * g y) volume :=
    (hcd_fi.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgs.mul_left
  have hibp1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (v := coordinateVector i) hintM (hintL i) hint_fg
    (fun y _ => (hf.differentiable (by norm_num)) y)
    (fun y _ => (hcd_gi.differentiable (by simp)) y)
  have hibp2 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (v := coordinateVector i) (hintR i) hintM hint_f'g
    (fun y _ => (hcd_fi.differentiable (by norm_num)) y)
    (fun y _ => (hg.differentiable (by simp)) y)
  linarith

private def vecLaplacian (u : Space → Space) (y : Space) : Space :=
  WithLp.toLp 2 (fun b : Fin 3 => UnforcedLeray.Heat.laplacian (fun y' => u y' b) y)

private lemma vecLaplacian_apply (u : Space → Space) (y : Space) (b : Fin 3) :
    vecLaplacian u y b = UnforcedLeray.Heat.laplacian (fun y' => u y' b) y := rfl

private lemma locallyIntegrableOn_Ioo_of_memLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ℝ} {f : SpaceTime → E} (hf : MemLp f (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab P))) :
    LocallyIntegrableOn f (Ioo 0 P ×ˢ univ) volume := by
  intro x _
  have h1 : (1 : ℝ≥0∞) ≤ 11 / 4 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  obtain ⟨s, hs, hint⟩ := (MemLp.locallyIntegrable hf h1) x
  refine ⟨(Ioo 0 P ×ˢ univ) ∩ s, inter_mem_nhdsWithin _ hs, ?_⟩
  have hsub : (Ioo 0 P ×ˢ univ) ∩ s ⊆ periodSlab P :=
    inter_subset_left.trans (Set.prod_mono Ioo_subset_Ioc_self Subset.rfl)
  have hint2 := hint.mono_set (inter_subset_right : (Ioo 0 P ×ˢ univ) ∩ s ⊆ s)
  rw [IntegrableOn, Measure.restrict_restrict_of_subset hsub] at hint2
  exact hint2

private lemma memLp_rep_periodSlab {P : ℝ} [Fact (0 < P)] (f : PhaseSpace.Yq P B0412.q0E) :
    MemLp (fun x : SpaceTime => Cons.C03.Concrete.rep f x.1 x.2)
        (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab P)) ∧
      (eLpNorm (fun x : SpaceTime => Cons.C03.Concrete.rep f x.1 x.2)
        (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab P))).toReal ≤
        P ^ ((4 : ℝ) / 11) * ‖f‖ := by
  have hP0 : 0 < P := Fact.out
  have hq_eq : (11 / 4 : ℝ≥0∞) = B0412.q0E := by
    rw [← IIb.S1Sub.s1_ofReal_bgp_eq_q0E]
    have h11 : (11 : ℝ≥0∞) = ENNReal.ofReal 11 := by norm_num
    have h4 : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by norm_num
    rw [h11, h4, ← ENNReal.ofReal_div_of_pos (by norm_num)]
    rfl
  have hq_ne0 : B0412.q0E ≠ 0 := by rw [← hq_eq]; norm_num
  have hq_ne_top : B0412.q0E ≠ (⊤ : ℝ≥0∞) := by
    rw [← hq_eq]; exact ENNReal.div_ne_top (by norm_num) (by norm_num)
  have hq_toReal : B0412.q0E.toReal = 11 / 4 := by
    rw [← hq_eq, ENNReal.toReal_div]; norm_num
  have hsm : AEStronglyMeasurable (fun x : SpaceTime => Cons.C03.Concrete.rep f x.1 x.2)
      (volume.restrict (periodSlab P)) :=
    (Cons.C03.Concrete.stronglyMeasurable_rep f).aestronglyMeasurable.restrict
  have hlint : ∫⁻ x in periodSlab P,
      ‖Cons.C03.Concrete.rep f x.1 x.2‖ₑ ^ B0412.q0E.toReal =
      ENNReal.ofReal P * ‖f‖ₑ ^ B0412.q0E.toReal := by
    have hm : Measurable (fun x : SpaceTime =>
        ‖Cons.C03.Concrete.rep f x.1 x.2‖ₑ ^ B0412.q0E.toReal) :=
      ((Cons.C03.Concrete.stronglyMeasurable_rep f).measurable.enorm).pow_const _
    rw [periodSlab, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
      lintegral_prod _ hm.aemeasurable]
    have h_inner : ∀ t : ℝ, ∫⁻ y : Space,
        ‖Cons.C03.Concrete.rep f t y‖ₑ ^ B0412.q0E.toReal =
        ‖f (t : AddCircle P)‖ₑ ^ B0412.q0E.toReal := by
      intro t
      have h_ae : (fun y : Space => ‖Cons.C03.Concrete.rep f t y‖ₑ ^ B0412.q0E.toReal) =ᵐ[volume]
          fun y => ‖(f (t : AddCircle P) : Space → PhaseSpace.CVec3) y‖ₑ ^ B0412.q0E.toReal := by
        filter_upwards [Cons.C03.Concrete.rep_slice f t] with y hy; rw [hy]
      rw [lintegral_congr_ae h_ae]
      exact PhaseSpace.lintegral_enorm_rpow_Lp (f (t : AddCircle P)) hq_ne_top
    simp_rw [h_inner]
    have h1 := AddCircle.lintegral_preimage (T := P) (0 : ℝ)
      (fun τ : AddCircle P => ‖f τ‖ₑ ^ B0412.q0E.toReal)
    rw [zero_add] at h1
    rw [h1, AddCircle.volume_eq_smul_haarAddCircle, lintegral_smul_measure, smul_eq_mul,
      PhaseSpace.lintegral_enorm_rpow_Yq f hq_ne_top]
  have heLp : eLpNorm (fun x : SpaceTime => Cons.C03.Concrete.rep f x.1 x.2)
      (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab P)) =
      (ENNReal.ofReal P * ‖f‖ₑ ^ (11 / 4 : ℝ)) ^ (4 / 11 : ℝ) := by
    rw [hq_eq, eLpNorm_eq_eLpNorm' hq_ne0 hq_ne_top, eLpNorm'_eq_lintegral_enorm, hlint,
      hq_toReal]
    norm_num
  have hlt : eLpNorm (fun x : SpaceTime => Cons.C03.Concrete.rep f x.1 x.2)
      (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab P)) < (⊤ : ℝ≥0∞) := by
    rw [heLp]
    refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top)
  refine ⟨⟨hsm, hlt⟩, ?_⟩
  rw [heLp, ← ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hP0.le,
    ← ENNReal.toReal_rpow, Real.mul_rpow hP0.le (Real.rpow_nonneg ENNReal.toReal_nonneg _),
    ← Real.rpow_mul ENNReal.toReal_nonneg]
  norm_num

private lemma laplacian_corr_slab_aux
    {p : Params} (hP1 : p.period ≤ 1) (z : p.Z)
    (hcorr : ContDiff ℝ ∞ (fun x : SpaceTime => p.corr z x.1 x.2)) :
    MemLp (fun x : SpaceTime => vecLaplacian (p.corr z x.1) x.2)
        (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period)) ∧
      (eLpNorm (fun x : SpaceTime => vecLaplacian (p.corr z x.1) x.2)
        (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period))).toReal ≤
        p.period ^ ((4 : ℝ) / 11) * (p.ν⁻¹ * ‖z‖) := by
  have hP0 : 0 < p.period := p.period_pos
  have : Fact (0 < p.period) := ⟨hP0⟩
  have hq_eq : (11 / 4 : ℝ≥0∞) = B0412.q0E := by
    rw [← IIb.S1Sub.s1_ofReal_bgp_eq_q0E]
    have h11 : (11 : ℝ≥0∞) = ENNReal.ofReal 11 := by norm_num
    have h4 : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by norm_num
    rw [h11, h4, ← ENNReal.ofReal_div_of_pos (by norm_num)]
    rfl
  let u := B0412.XToD (p.graphX z)
  have hu_eq : (u : PhaseSpace.Yq p.period B0412.q0E) = p.wOf z := rfl
  let a : PhaseSpace.Yq p.period B0412.q0E := B0411.nuLapD u
  have ha_op : PhaseSpace.HasPhaseOp (PhaseSpace.nuLapT p.ν) (p.wOf z) a := by
    rw [← hu_eq]; exact B0411.hasPhaseOp_nuLapD u
  have ha_bd : B0411.graphNormD u ≤ ‖z‖ := IIb.S1Sub.graphNormD_graphX_le_norm p z
  have hreP : Continuous Cons.C03.Concrete.reP :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp
      (continuous_pi fun i => Complex.continuous_re.comp
        ((EuclideanSpace.proj i : PhaseSpace.CVec3 →L[ℂ] ℂ).continuous))
  obtain ⟨ha_mem_c, ha_eb_c⟩ := memLp_rep_periodSlab a
  have ha_mem : MemLp (fun x : SpaceTime =>
      Cons.C03.Concrete.reP (Cons.C03.Concrete.rep a x.1 x.2))
      (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period)) := by
    refine ⟨(hreP.measurable.comp (Cons.C03.Concrete.stronglyMeasurable_rep a).measurable).aestronglyMeasurable.restrict, ?_⟩
    refine lt_of_le_of_lt (eLpNorm_mono fun x => IIb.S1Sub.norm_realPartVector_le _) ha_mem_c.2
  have ha_eb : (eLpNorm (fun x : SpaceTime =>
      Cons.C03.Concrete.reP (Cons.C03.Concrete.rep a x.1 x.2))
      (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period))).toReal ≤
      p.period ^ ((4 : ℝ) / 11) * ‖z‖ := by
    have hmono : eLpNorm (fun x : SpaceTime =>
        Cons.C03.Concrete.reP (Cons.C03.Concrete.rep a x.1 x.2))
        (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period)) ≤
        eLpNorm (fun x : SpaceTime => Cons.C03.Concrete.rep a x.1 x.2)
        (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period)) :=
      eLpNorm_mono fun x => IIb.S1Sub.norm_realPartVector_le _
    calc (eLpNorm (fun x => Cons.C03.Concrete.reP (Cons.C03.Concrete.rep a x.1 x.2))
            (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period))).toReal
        ≤ (eLpNorm (fun x => Cons.C03.Concrete.rep a x.1 x.2)
            (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period))).toReal :=
          ENNReal.toReal_mono ha_mem_c.2.ne hmono
      _ ≤ p.period ^ ((4 : ℝ) / 11) * ‖a‖ := ha_eb_c
      _ ≤ p.period ^ ((4 : ℝ) / 11) * B0411.graphNormD u := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hP0.le _)
          unfold B0411.graphNormD
          linarith [norm_nonneg (u : PhaseSpace.Yq p.period B0412.q0E), norm_nonneg (B0411.T0D u)]
      _ ≤ p.period ^ ((4 : ℝ) / 11) * ‖z‖ :=
          mul_le_mul_of_nonneg_left ha_bd (Real.rpow_nonneg hP0.le _)
  have hF_rep : Cons.C03.Concrete.IsContRep (p.wOf z) (p.corr z) := by
    have : Fact (1 ≤ ENNReal.ofReal B0281.q0) := inferInstanceAs (Fact (1 ≤ B0412.q0E))
    let F := B0449.globalRealChartRep hP1 IIb.S1Sub.s1_q0_holder IIb.S1Sub.s1_q0_gt p.ν_pos
      (B0411.hasPhaseOp_T0D u) (B0411.hasPhaseOp_nuLapD u)
    have hF : Cons.C03.Concrete.IsContRep (p.wOf z) F :=
      Cons.C03.Concrete.graph_globalRealChartRep_isContRep hP1 IIb.S1Sub.s1_q0_holder
        IIb.S1Sub.s1_q0_gt p.ν_pos (B0411.hasPhaseOp_T0D u) (B0411.hasPhaseOp_nuLapD u)
    exact Cons.C03.Concrete.contRep_spec ⟨F, hF⟩
  have hset : (Ioo 0 p.period ×ˢ (univ : Set Space)) =ᵐ[volume] periodSlab p.period := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · have : (Ioo 0 p.period ×ˢ (univ : Set Space)) \ periodSlab p.period = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨⟨h1, h2⟩, h⟩
        exact h ⟨⟨h1.1, h1.2.le⟩, trivial⟩
      rw [this, measure_empty]
    · have hsub : periodSlab p.period \ (Ioo 0 p.period ×ˢ (univ : Set Space)) ⊆
          ({p.period} : Set ℝ) ×ˢ (univ : Set Space) := by
        rintro ⟨t, y⟩ ⟨⟨⟨ht0, htP⟩, _⟩, hnot⟩
        refine ⟨le_antisymm htP ?_, trivial⟩
        by_contra hlt
        exact hnot ⟨⟨ht0, not_le.mp hlt⟩, trivial⟩
      refine measure_mono_null hsub ?_
      rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  have hres : volume.restrict (periodSlab p.period) =
      volume.restrict (Ioo 0 p.period ×ˢ (univ : Set Space)) :=
    Measure.restrict_congr_set hset.symm
  have hcorr_lap_cont : Continuous (fun x : SpaceTime => vecLaplacian (p.corr z x.1) x.2) := by
    refine (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp (continuous_pi fun b => ?_)
    have hb : ContDiff ℝ ∞ (fun x : SpaceTime => p.corr z x.1 x.2 b) :=
      (EuclideanSpace.proj b : Space →L[ℝ] ℝ).contDiff.comp hcorr
    refine continuous_finsetSum _ fun i _ => ?_
    have h1 : ContDiff ℝ ∞ (fun x : SpaceTime =>
        (fderiv ℝ (fun x' => p.corr z x'.1 x'.2 b) x) (0, coordinateVector i)) :=
      (hb.fderiv_right (by simp)).clm_apply contDiff_const
    have h2 : ContDiff ℝ ∞ (fun x : SpaceTime =>
        (fderiv ℝ (fun x' => (fderiv ℝ (fun x'' => p.corr z x''.1 x''.2 b) x')
          (0, coordinateVector i)) x) (0, coordinateVector i)) :=
      (h1.fderiv_right (by simp)).clm_apply contDiff_const
    refine h2.continuous.congr fun x => ?_
    have haff : ∀ p0 : SpaceTime, HasFDerivAt (fun y' : Space => (p0.1, y'))
        (ContinuousLinearMap.inr ℝ ℝ Space) p0.2 :=
      fun p0 => (hasFDerivAt_const p0.1 p0.2).prodMk (hasFDerivAt_id p0.2)
    have hd1 : ∀ p0 : SpaceTime,
        fderiv ℝ (fun y' => p.corr z p0.1 y' b) p0.2 (coordinateVector i) =
          fderiv ℝ (fun x' => p.corr z x'.1 x'.2 b) p0 (0, coordinateVector i) := by
      intro p0
      have hsl : (fun y' => p.corr z p0.1 y' b) =
          (fun x' : SpaceTime => p.corr z x'.1 x'.2 b) ∘ (fun y' => (p0.1, y')) := rfl
      rw [hsl, ((hb.differentiable (by simp) p0).hasFDerivAt.comp p0.2 (haff p0)).fderiv]
      rfl
    have heq_fn : (fun y' => fderiv ℝ (fun y'' => p.corr z x.1 y'' b) y' (coordinateVector i)) =
        (fun p0 : SpaceTime => fderiv ℝ (fun x' => p.corr z x'.1 x'.2 b) p0 (0, coordinateVector i)) ∘
          (fun y' => (x.1, y')) := by
      funext y'; exact hd1 (x.1, y')
    rw [heq_fn, ((h1.differentiable (by simp) x).hasFDerivAt.comp x.2 (haff x)).fderiv]
    rfl
  have hU_open : IsOpen (Ioo 0 p.period ×ˢ (univ : Set Space)) := by
    refine Metric.isOpen_iff.mpr fun x hx => ?_
    refine ⟨min x.1 (p.period - x.1), lt_min hx.1.1 (sub_pos.mpr hx.1.2), fun y hy => ?_⟩
    have hdist : |y.1 - x.1| < min x.1 (p.period - x.1) :=
      (norm_fst_le (y - x)).trans_lt (Metric.mem_ball.mp hy)
    exact ⟨⟨by linarith [abs_lt.mp hdist, min_le_left x.1 (p.period - x.1)],
      by linarith [abs_lt.mp hdist, min_le_right x.1 (p.period - x.1)]⟩, trivial⟩
  have hae_coord : ∀ b : Fin 3,
      (fun x : SpaceTime => p.ν * UnforcedLeray.Heat.laplacian (fun y' => p.corr z x.1 y' b) x.2) =ᵐ[
        volume.restrict (Ioo 0 p.period ×ˢ univ)]
        fun x => (Cons.C03.Concrete.rep a x.1 x.2 b).re := by
    intro b
    rw [← sub_ae_eq_zero, Filter.EventuallyEq, ae_restrict_iff' hU_open.measurableSet]
    refine hU_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero ?_ ?_
    · have hloc1 : LocallyIntegrableOn
          (fun x : SpaceTime => p.ν * UnforcedLeray.Heat.laplacian (fun y' => p.corr z x.1 y' b) x.2)
          (Ioo 0 p.period ×ˢ univ) volume :=
        (continuous_const.mul ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).continuous.comp hcorr_lap_cont)).continuousOn.locallyIntegrableOn
          hU_open.measurableSet
      have ha_mem_b : MemLp (fun x : SpaceTime => (Cons.C03.Concrete.rep a x.1 x.2 b).re)
          (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period)) := by
        refine ⟨(Complex.continuous_re.measurable.comp
            ((EuclideanSpace.proj b : PhaseSpace.CVec3 →L[ℂ] ℂ).continuous.measurable.comp
              (Cons.C03.Concrete.stronglyMeasurable_rep a).measurable)).aestronglyMeasurable.restrict, ?_⟩
        refine lt_of_le_of_lt (eLpNorm_mono fun x => ?_) ha_mem.2
        simpa [Cons.C03.Concrete.reP] using PiLp.norm_apply_le (Cons.C03.Concrete.reP (Cons.C03.Concrete.rep a x.1 x.2)) b
      have hloc2 : LocallyIntegrableOn
          (fun x : SpaceTime => (Cons.C03.Concrete.rep a x.1 x.2 b).re)
          (Ioo 0 p.period ×ˢ univ) volume :=
        locallyIntegrableOn_Ioo_of_memLp ha_mem_b
      exact hloc1.sub hloc2
    · intro φ hφ hφc hφs
      have hpt := isPhaseTest_periodizeTest hP0 hφ hφc hφs b
      have hop := ha_op (periodizeTest p.period φ b) hpt
      rw [PhaseSpace.phasePair_eq_periodIntegral (B0411.isPhaseTest_nuLapT hpt p.ν) (p.wOf z),
        PhaseSpace.phasePair_eq_periodIntegral hpt a] at hop
      have hop_re := congrArg Complex.re hop
      simp only [zero_add, Complex.real_smul, Complex.re_ofReal_mul] at hop_re
      have hcancel := mul_left_cancel₀ (inv_ne_zero hP0.ne') hop_re
      have hw_mem : MemLp (fun x : SpaceTime =>
          Cons.C03.Concrete.rep (p.wOf z) x.1 x.2)
          (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period)) :=
        (memLp_rep_periodSlab (p.wOf z)).1
      -- Helper: any locally integrable function on `Ioo 0 P ×ˢ univ` times a compactly supported
      -- continuous function on `Ioo 0 P ×ˢ univ` is integrable on `Ioo 0 P ×ˢ univ`
      have h_int_L_prod : IntegrableOn (fun x : SpaceTime =>
          (p.ν * UnforcedLeray.Heat.laplacian (fun y' => φ (x.1, y')) x.2) *
            (Cons.C03.Concrete.rep (p.wOf z) x.1 x.2 b).re)
          (Ioo 0 p.period ×ˢ univ) volume := by
        have hloc_w : LocallyIntegrableOn (fun x : SpaceTime =>
            (Cons.C03.Concrete.rep (p.wOf z) x.1 x.2 b).re) (Ioo 0 p.period ×ˢ univ) volume := by
          refine locallyIntegrableOn_Ioo_of_memLp ⟨?_, ?_⟩
          · exact (Complex.continuous_re.measurable.comp (((EuclideanSpace.proj b : PhaseSpace.CVec3 →L[ℂ] ℂ).continuous.measurable).comp
              (Cons.C03.Concrete.stronglyMeasurable_rep (p.wOf z)).measurable)).aestronglyMeasurable.restrict
          · refine lt_of_le_of_lt (eLpNorm_mono fun x => ?_) hw_mem.2
            simpa using (Complex.abs_re_le_norm _).trans (PiLp.norm_apply_le _ b)
        have hlap_φ : ContDiff ℝ ∞ (fun x : SpaceTime =>
            p.ν * UnforcedLeray.Heat.laplacian (fun y' => φ (x.1, y')) x.2) := by
          refine contDiff_const.mul (ContDiff.sum fun i _ => ?_)
          have h1 : ContDiff ℝ ∞ (fun x : SpaceTime =>
              (fderiv ℝ φ x) (0, coordinateVector i)) :=
            (hφ.fderiv_right (by simp)).clm_apply contDiff_const
          have h2 : ContDiff ℝ ∞ (fun x : SpaceTime =>
              (fderiv ℝ (fun x' => (fderiv ℝ φ x') (0, coordinateVector i)) x)
                (0, coordinateVector i)) :=
            (h1.fderiv_right (by simp)).clm_apply contDiff_const
          have h2_eq : (fun x : SpaceTime =>
              fderiv ℝ (fun y' => fderiv ℝ (fun y'' => φ (x.1, y'')) y' (coordinateVector i))
                x.2 (coordinateVector i)) =
              fun x : SpaceTime =>
                (fderiv ℝ (fun x' => (fderiv ℝ φ x') (0, coordinateVector i)) x)
                  (0, coordinateVector i) := by
            funext x
            have hslice1 : ∀ p0 : SpaceTime, (fun y' => φ (p0.1, y')) = φ ∘ (fun y' => (p0.1, y')) :=
              fun _ => rfl
            have haff1 : ∀ p0 : SpaceTime, HasFDerivAt (fun y' : Space => (p0.1, y'))
                (ContinuousLinearMap.inr ℝ ℝ Space) p0.2 :=
              fun p0 => (hasFDerivAt_const p0.1 p0.2).prodMk (hasFDerivAt_id p0.2)
            have hd1 : ∀ p0 : SpaceTime,
                fderiv ℝ (fun y' => φ (p0.1, y')) p0.2 (coordinateVector i) =
                  fderiv ℝ φ p0 (0, coordinateVector i) := by
              intro p0
              rw [hslice1 p0, ((hφ.differentiable (by simp) p0).hasFDerivAt.comp p0.2 (haff1 p0)).fderiv]
              rfl
            have heq_fn : (fun y' => fderiv ℝ (fun y'' => φ (x.1, y'')) y' (coordinateVector i)) =
                (fun p0 : SpaceTime => fderiv ℝ φ p0 (0, coordinateVector i)) ∘
                  (fun y' => (x.1, y')) := by
              funext y'; exact hd1 (x.1, y')
            rw [heq_fn, ((h1.differentiable (by simp) x).hasFDerivAt.comp x.2 (haff1 x)).fderiv]
            rfl
          rw [h2_eq]; exact h2
        have hsupp_lap : Function.support (fun x : SpaceTime =>
            p.ν * UnforcedLeray.Heat.laplacian (fun y' => φ (x.1, y')) x.2) ⊆ tsupport φ := by
          intro x hx
          by_contra hx_not
          have h0 : p.ν * UnforcedLeray.Heat.laplacian (fun y' => φ (x.1, y')) x.2 = 0 := by
            simp only [UnforcedLeray.Heat.laplacian, mul_eq_zero]
            right
            refine Finset.sum_eq_zero fun i _ => ?_
            have h0_i : (fun y' => fderiv ℝ (fun y'' => φ (x.1, y'')) y' (coordinateVector i)) =ᶠ[𝓝 x.2] 0 := by
              filter_upwards [((continuous_const.prodMk continuous_id).continuousAt.tendsto.eventually
                ((isClosed_tsupport φ).isOpen_compl.mem_nhds hx_not))] with y' hy'
              have hn : (fun y'' => φ (x.1, y'')) =ᶠ[𝓝 y'] 0 :=
                (notMem_tsupport_iff_eventuallyEq.mp hy').comp_tendsto
                  (Continuous.continuousAt (continuous_const.prodMk continuous_id)).tendsto
              rw [hn.fderiv_eq]; simp
            rw [h0_i.fderiv_eq]; simp
          exact hx h0
        have hK_int : IntegrableOn (fun x : SpaceTime =>
            (Cons.C03.Concrete.rep (p.wOf z) x.1 x.2 b).re) (tsupport φ) volume :=
          hloc_w.integrableOn_compact_subset hφs hφc
        obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuousOn hlap_φ.continuous.continuousOn
        have h_int_K : IntegrableOn (fun x : SpaceTime =>
            (p.ν * UnforcedLeray.Heat.laplacian (fun y' => φ (x.1, y')) x.2) *
              (Cons.C03.Concrete.rep (p.wOf z) x.1 x.2 b).re) (tsupport φ) volume := by
          refine Integrable.mono' (hK_int.norm.const_mul M)
            (hlap_φ.continuous.aestronglyMeasurable.restrict.mul hK_int.aestronglyMeasurable) ?_
          filter_upwards [ae_restrict_mem (isClosed_tsupport φ).measurableSet] with x hx
          simpa [norm_mul, Real.norm_eq_abs] using
            mul_le_mul_of_nonneg_right (hM x hx)
              (abs_nonneg (Cons.C03.Concrete.rep (p.wOf z) x.1 x.2 b).re)
        have h_int_all : Integrable (fun x : SpaceTime =>
            (p.ν * UnforcedLeray.Heat.laplacian (fun y' => φ (x.1, y')) x.2) *
              (Cons.C03.Concrete.rep (p.wOf z) x.1 x.2 b).re) volume := by
          refine (integrableOn_iff_integrable_of_support_subset (μ := volume) (s := tsupport φ) ?_).mp h_int_K
          intro x hx
          exact hsupp_lap (fun h0 => hx (by simp [h0]))
        exact h_int_all.integrableOn
      have h_int_R_prod : IntegrableOn (fun x : SpaceTime =>
          φ x * (Cons.C03.Concrete.rep a x.1 x.2 b).re)
          (Ioo 0 p.period ×ˢ univ) volume := by
        have hloc_a : LocallyIntegrableOn (fun x : SpaceTime =>
            (Cons.C03.Concrete.rep a x.1 x.2 b).re) (Ioo 0 p.period ×ˢ univ) volume :=
          locallyIntegrableOn_Ioo_of_memLp ⟨
            (Complex.continuous_re.measurable.comp (((EuclideanSpace.proj b : PhaseSpace.CVec3 →L[ℂ] ℂ).continuous.measurable).comp
              (Cons.C03.Concrete.stronglyMeasurable_rep a).measurable)).aestronglyMeasurable.restrict,
            lt_of_le_of_lt (eLpNorm_mono fun x =>
              (Complex.abs_re_le_norm _).trans (PiLp.norm_apply_le _ b)) ha_mem_c.2⟩
        have hK_int := hloc_a.integrableOn_compact_subset hφs hφc
        obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuousOn hφ.continuous.continuousOn
        have h_int_K : IntegrableOn (fun x : SpaceTime =>
            φ x * (Cons.C03.Concrete.rep a x.1 x.2 b).re) (tsupport φ) volume := by
          refine Integrable.mono' (hK_int.norm.const_mul M)
            (hφ.continuous.aestronglyMeasurable.restrict.mul hK_int.aestronglyMeasurable) ?_
          filter_upwards [ae_restrict_mem (isClosed_tsupport φ).measurableSet] with x hx
          simpa [norm_mul, Real.norm_eq_abs] using
            mul_le_mul_of_nonneg_right (hM x hx)
              (abs_nonneg (Cons.C03.Concrete.rep a x.1 x.2 b).re)
        have h_int_all : Integrable (fun x : SpaceTime =>
            φ x * (Cons.C03.Concrete.rep a x.1 x.2 b).re) volume := by
          refine (integrableOn_iff_integrable_of_support_subset (μ := volume) (s := tsupport φ) ?_).mp h_int_K
          intro x hx
          exact subset_tsupport φ (fun h0 => hx (by simp [h0]))
        exact h_int_all.integrableOn
      have h_int_L_c : IntegrableOn (fun t => ∫ y,
          PhaseSpace.dotL (PhaseSpace.nuLapT p.ν (periodizeTest p.period φ b) (t, y))
            ((p.wOf z (t : AddCircle p.period) : Space → PhaseSpace.CVec3) y))
          (Ioc 0 p.period) volume := by
        rw [IntegrableOn, Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
        have heq_t : EqOn (fun t => ∫ y,
            PhaseSpace.dotL (PhaseSpace.nuLapT p.ν (periodizeTest p.period φ b) (t, y))
              ((p.wOf z (t : AddCircle p.period) : Space → PhaseSpace.CVec3) y))
            (fun t => ∫ y, ((p.ν * UnforcedLeray.Heat.laplacian (fun y' => φ (t, y')) y : ℝ) : ℂ) *
              Cons.C03.Concrete.rep (p.wOf z) t y b) (Ioo 0 p.period) := by
          intro t ht
          refine integral_congr_ae ?_
          filter_upwards [Cons.C03.Concrete.rep_slice (p.wOf z) t] with y hy
          rw [nuLapT_periodizeTest_eq_on_Ioo hP0 hφ hφs b ht y, PhaseSpace.dotL_apply]
          simp [← hy]
        rw [← IntegrableOn, integrableOn_congr_fun heq_t measurableSet_Ioo]
        have h_int_c : IntegrableOn (fun x : SpaceTime =>
            ((p.ν * UnforcedLeray.Heat.laplacian (fun y' => φ (x.1, y')) x.2 : ℝ) : ℂ) *
              Cons.C03.Concrete.rep (p.wOf z) x.1 x.2 b) (Ioo 0 p.period ×ˢ univ) volume := by
          have hloc_wb : LocallyIntegrableOn (fun x : SpaceTime =>
              Cons.C03.Concrete.rep (p.wOf z) x.1 x.2 b) (Ioo 0 p.period ×ˢ univ) volume :=
            locallyIntegrableOn_Ioo_of_memLp ⟨
              (((EuclideanSpace.proj b : PhaseSpace.CVec3 →L[ℂ] ℂ).continuous.measurable).comp
                (Cons.C03.Concrete.stronglyMeasurable_rep (p.wOf z)).measurable).aestronglyMeasurable.restrict,
              lt_of_le_of_lt (eLpNorm_mono fun x => PiLp.norm_apply_le _ b) hw_mem.2⟩
          have hK_int := hloc_wb.integrableOn_compact_subset hφs hφc
          have hlap_φ : ContDiff ℝ ∞ (fun x : SpaceTime =>
              p.ν * UnforcedLeray.Heat.laplacian (fun y' => φ (x.1, y')) x.2) := by
            refine contDiff_const.mul (ContDiff.sum fun i _ => ?_)
            have h1 : ContDiff ℝ ∞ (fun x : SpaceTime =>
                (fderiv ℝ φ x) (0, coordinateVector i)) :=
              (hφ.fderiv_right (by simp)).clm_apply contDiff_const
            have h2 : ContDiff ℝ ∞ (fun x : SpaceTime =>
                (fderiv ℝ (fun x' => (fderiv ℝ φ x') (0, coordinateVector i)) x)
                  (0, coordinateVector i)) :=
              (h1.fderiv_right (by simp)).clm_apply contDiff_const
            have h2_eq : (fun x : SpaceTime =>
                fderiv ℝ (fun y' => fderiv ℝ (fun y'' => φ (x.1, y'')) y' (coordinateVector i))
                  x.2 (coordinateVector i)) =
                fun x : SpaceTime =>
                  (fderiv ℝ (fun x' => (fderiv ℝ φ x') (0, coordinateVector i)) x)
                    (0, coordinateVector i) := by
              funext x
              have hslice1 : ∀ p0 : SpaceTime, (fun y' => φ (p0.1, y')) = φ ∘ (fun y' => (p0.1, y')) :=
                fun _ => rfl
              have haff1 : ∀ p0 : SpaceTime, HasFDerivAt (fun y' : Space => (p0.1, y'))
                  (ContinuousLinearMap.inr ℝ ℝ Space) p0.2 :=
                fun p0 => (hasFDerivAt_const p0.1 p0.2).prodMk (hasFDerivAt_id p0.2)
              have hd1 : ∀ p0 : SpaceTime,
                  fderiv ℝ (fun y' => φ (p0.1, y')) p0.2 (coordinateVector i) =
                    fderiv ℝ φ p0 (0, coordinateVector i) := by
                intro p0
                rw [hslice1 p0, ((hφ.differentiable (by simp) p0).hasFDerivAt.comp p0.2 (haff1 p0)).fderiv]
                rfl
              have heq_fn : (fun y' => fderiv ℝ (fun y'' => φ (x.1, y'')) y' (coordinateVector i)) =
                  (fun p0 : SpaceTime => fderiv ℝ φ p0 (0, coordinateVector i)) ∘
                    (fun y' => (x.1, y')) := by
                funext y'; exact hd1 (x.1, y')
              rw [heq_fn, ((h1.differentiable (by simp) x).hasFDerivAt.comp x.2 (haff1 x)).fderiv]
              rfl
            rw [h2_eq]; exact h2
          obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuousOn hlap_φ.continuous.continuousOn
          have h_int_K : IntegrableOn (fun x : SpaceTime =>
              ((p.ν * UnforcedLeray.Heat.laplacian (fun y' => φ (x.1, y')) x.2 : ℝ) : ℂ) *
                Cons.C03.Concrete.rep (p.wOf z) x.1 x.2 b) (tsupport φ) volume := by
            refine Integrable.mono' (hK_int.norm.const_mul M)
              ((Complex.continuous_ofReal.comp hlap_φ.continuous).aestronglyMeasurable.restrict.mul
                hK_int.aestronglyMeasurable) ?_
            filter_upwards [ae_restrict_mem (isClosed_tsupport φ).measurableSet] with x hx
            simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
              mul_le_mul_of_nonneg_right (hM x hx) (norm_nonneg _)
          have h_int_all : Integrable (fun x : SpaceTime =>
              ((p.ν * UnforcedLeray.Heat.laplacian (fun y' => φ (x.1, y')) x.2 : ℝ) : ℂ) *
                Cons.C03.Concrete.rep (p.wOf z) x.1 x.2 b) volume := by
            refine (integrableOn_iff_integrable_of_support_subset (μ := volume) (s := tsupport φ) ?_).mp h_int_K
            intro x hx
            by_contra hx_not
            have h0 : p.ν * UnforcedLeray.Heat.laplacian (fun y' => φ (x.1, y')) x.2 = 0 := by
              simp only [UnforcedLeray.Heat.laplacian, mul_eq_zero]
              right
              refine Finset.sum_eq_zero fun i _ => ?_
              have h0_i : (fun y' => fderiv ℝ (fun y'' => φ (x.1, y'')) y' (coordinateVector i)) =ᶠ[𝓝 x.2] 0 := by
                filter_upwards [((continuous_const.prodMk continuous_id).continuousAt.tendsto.eventually
                  ((isClosed_tsupport φ).isOpen_compl.mem_nhds hx_not))] with y' hy'
                have hn : (fun y'' => φ (x.1, y'')) =ᶠ[𝓝 y'] 0 :=
                  (notMem_tsupport_iff_eventuallyEq.mp hy').comp_tendsto
                    (Continuous.continuousAt (continuous_const.prodMk continuous_id)).tendsto
                rw [hn.fderiv_eq]; simp
              rw [h0_i.fderiv_eq]; simp
            exact hx (by simp [h0])
          exact h_int_all.integrableOn
        rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h_int_c
        rw [IntegrableOn]
        simpa only [Measure.restrict_univ] using h_int_c.integral_prod_left
      have h_int_R_c : IntegrableOn (fun t => ∫ y,
          PhaseSpace.dotL (periodizeTest p.period φ b (t, y))
            ((a (t : AddCircle p.period) : Space → PhaseSpace.CVec3) y))
          (Ioc 0 p.period) volume := by
        rw [IntegrableOn, Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
        have heq_t : EqOn (fun t => ∫ y,
            PhaseSpace.dotL (periodizeTest p.period φ b (t, y))
              ((a (t : AddCircle p.period) : Space → PhaseSpace.CVec3) y))
            (fun t => ∫ y, ((φ (t, y) : ℝ) : ℂ) * Cons.C03.Concrete.rep a t y b)
            (Ioo 0 p.period) := by
          intro t ht
          refine integral_congr_ae ?_
          filter_upwards [Cons.C03.Concrete.rep_slice a t] with y hy
          rw [periodizeTest_eq_on_Ioc hP0 hφs b (Ioo_subset_Ioc_self ht) y, PhaseSpace.dotL_apply]
          simp [← hy]
        rw [← IntegrableOn, integrableOn_congr_fun heq_t measurableSet_Ioo]
        have h_int_c : IntegrableOn (fun x : SpaceTime =>
            ((φ x : ℝ) : ℂ) * Cons.C03.Concrete.rep a x.1 x.2 b)
            (Ioo 0 p.period ×ˢ univ) volume := by
          have hloc_ab : LocallyIntegrableOn (fun x : SpaceTime =>
              Cons.C03.Concrete.rep a x.1 x.2 b) (Ioo 0 p.period ×ˢ univ) volume :=
            locallyIntegrableOn_Ioo_of_memLp ⟨
              (((EuclideanSpace.proj b : PhaseSpace.CVec3 →L[ℂ] ℂ).continuous.measurable).comp
                (Cons.C03.Concrete.stronglyMeasurable_rep a).measurable).aestronglyMeasurable.restrict,
              lt_of_le_of_lt (eLpNorm_mono fun x => PiLp.norm_apply_le _ b) ha_mem_c.2⟩
          have hK_int := hloc_ab.integrableOn_compact_subset hφs hφc
          obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuousOn hφ.continuous.continuousOn
          have h_int_K : IntegrableOn (fun x : SpaceTime =>
              ((φ x : ℝ) : ℂ) * Cons.C03.Concrete.rep a x.1 x.2 b) (tsupport φ) volume := by
            refine Integrable.mono' (hK_int.norm.const_mul M)
              ((Complex.continuous_ofReal.comp hφ.continuous).aestronglyMeasurable.restrict.mul
                hK_int.aestronglyMeasurable) ?_
            filter_upwards [ae_restrict_mem (isClosed_tsupport φ).measurableSet] with x hx
            simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
              mul_le_mul_of_nonneg_right (hM x hx) (norm_nonneg (Cons.C03.Concrete.rep a x.1 x.2 b))
          have h_int_all : Integrable (fun x : SpaceTime =>
              ((φ x : ℝ) : ℂ) * Cons.C03.Concrete.rep a x.1 x.2 b) volume := by
            refine (integrableOn_iff_integrable_of_support_subset (μ := volume) (s := tsupport φ) ?_).mp h_int_K
            intro x hx
            exact subset_tsupport φ (fun h0 => hx (by simp [h0]))
          exact h_int_all.integrableOn
        rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h_int_c
        rw [IntegrableOn]
        simpa only [Measure.restrict_univ] using h_int_c.integral_prod_left
      rw [← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm h_int_L_c] at hcancel
      rw [← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm h_int_R_c] at hcancel
      simp_rw [setIntegral_congr_set Ioo_ae_eq_Ioc.symm] at hcancel
      have hL_eq : ∫ t in Ioo 0 p.period, (Complex.reCLM (∫ y,
          PhaseSpace.dotL (PhaseSpace.nuLapT p.ν (periodizeTest p.period φ b) (t, y))
            ((p.wOf z (t : AddCircle p.period) : Space → PhaseSpace.CVec3) y))) =
          ∫ t in Ioo 0 p.period, ∫ y,
            (p.ν * UnforcedLeray.Heat.laplacian (fun y' => φ (t, y')) y) *
              (Cons.C03.Concrete.rep (p.wOf z) t y b).re := by
        refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
        have h_int_y : Integrable (fun y =>
            PhaseSpace.dotL (PhaseSpace.nuLapT p.ν (periodizeTest p.period φ b) (t, y))
              ((p.wOf z (t : AddCircle p.period) : Space → PhaseSpace.CVec3) y)) volume := by
          have heq_y : (fun y => PhaseSpace.dotL
              (PhaseSpace.nuLapT p.ν (periodizeTest p.period φ b) (t, y))
              ((p.wOf z (t : AddCircle p.period) : Space → PhaseSpace.CVec3) y)) =ᵐ[volume]
              fun y => ((p.ν * UnforcedLeray.Heat.laplacian (fun y' => φ (t, y')) y : ℝ) : ℂ) *
                Cons.C03.Concrete.rep (p.wOf z) t y b := by
            filter_upwards [Cons.C03.Concrete.rep_slice (p.wOf z) t] with y hy
            rw [nuLapT_periodizeTest_eq_on_Ioo hP0 hφ hφs b ht y, PhaseSpace.dotL_apply]
            simp [← hy]
          rw [integrable_congr heq_y]
          have hmem_wy : MemLp (fun y => Cons.C03.Concrete.rep (p.wOf z) t y b)
              (11 / 4 : ℝ≥0∞) volume := by
            have h_ae : (fun y => Cons.C03.Concrete.rep (p.wOf z) t y b) =ᵐ[volume]
                fun y => (p.wOf z (t : AddCircle p.period) : Space → PhaseSpace.CVec3) y b := by
              filter_upwards [Cons.C03.Concrete.rep_slice (p.wOf z) t] with y hy; rw [hy]
            rw [hq_eq]
            refine ⟨(((EuclideanSpace.proj b : PhaseSpace.CVec3 →L[ℂ] ℂ).continuous.measurable).comp
                ((Cons.C03.Concrete.stronglyMeasurable_rep (p.wOf z)).comp_measurable
                  (measurable_const.prodMk measurable_id)).measurable).aestronglyMeasurable, ?_⟩
            rw [eLpNorm_congr_ae h_ae]
            exact lt_of_le_of_lt (eLpNorm_mono fun y => PiLp.norm_apply_le _ b)
              (MeasureTheory.Lp.memLp _).2
          have hq1 : (1 : ℝ≥0∞) ≤ 11 / 4 := by
            rw [ENNReal.le_div_iff_mul_le (by left; norm_num) (by right; norm_num)]
            norm_num
          have hK_sp : IsCompact (Prod.snd '' tsupport φ) := hφc.isCompact.image continuous_snd
          have hloc_wy := hmem_wy.locallyIntegrable hq1
          have hK_int := hloc_wy.integrableOn_isCompact hK_sp
          have hlap_cont_y : Continuous (fun y : Space =>
              p.ν * UnforcedLeray.Heat.laplacian (fun y' => φ (t, y')) y) := by
            refine continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)
            have hφt : ContDiff ℝ ∞ (fun y' : Space => φ (t, y')) :=
              hφ.comp (contDiff_const.prodMk contDiff_id)
            have h1 : ContDiff ℝ ∞ (fun y' : Space =>
                fderiv ℝ (fun y'' => φ (t, y'')) y' (coordinateVector i)) :=
              (hφt.fderiv_right (by simp)).clm_apply contDiff_const
            have h2 : ContDiff ℝ ∞ (fun y' : Space =>
                fderiv ℝ (fun y'' => fderiv ℝ (fun y''' => φ (t, y''')) y'' (coordinateVector i))
                  y' (coordinateVector i)) :=
              (h1.fderiv_right (by simp)).clm_apply contDiff_const
            exact h2.continuous
          obtain ⟨M, hM⟩ := hK_sp.exists_bound_of_continuousOn hlap_cont_y.continuousOn
          have h_int_K : IntegrableOn (fun y =>
              ((p.ν * UnforcedLeray.Heat.laplacian (fun y' => φ (t, y')) y : ℝ) : ℂ) *
                Cons.C03.Concrete.rep (p.wOf z) t y b) (Prod.snd '' tsupport φ) volume := by
            refine Integrable.mono' (hK_int.norm.const_mul M)
              ((Complex.continuous_ofReal.comp hlap_cont_y).aestronglyMeasurable.restrict.mul
                hK_int.aestronglyMeasurable) ?_
            filter_upwards [ae_restrict_mem hK_sp.isClosed.measurableSet] with y hy
            simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
              mul_le_mul_of_nonneg_right (hM y hy) (norm_nonneg (Cons.C03.Concrete.rep (p.wOf z) t y b))
          refine (integrableOn_iff_integrable_of_support_subset (s := Prod.snd '' tsupport φ) ?_).mp h_int_K
          intro y hy
          by_contra hy_not
          have h0 : UnforcedLeray.Heat.laplacian (fun y' => φ (t, y')) y = 0 := by
            simp only [UnforcedLeray.Heat.laplacian]
            refine Finset.sum_eq_zero fun i _ => ?_
            have h0_i : (fun y' => fderiv ℝ (fun y'' => φ (t, y'')) y' (coordinateVector i)) =ᶠ[𝓝 y] 0 := by
              have hopen : IsOpen ((Prod.snd '' tsupport φ)ᶜ) := hK_sp.isClosed.isOpen_compl
              filter_upwards [hopen.mem_nhds hy_not] with y' hy'
              have hn : (fun y'' => φ (t, y'')) =ᶠ[𝓝 y'] 0 := by
                filter_upwards [hopen.mem_nhds hy'] with y'' hy''
                exact image_eq_zero_of_notMem_tsupport fun hmem => hy'' ⟨(t, y''), hmem, rfl⟩
              rw [hn.fderiv_eq]; simp
            rw [h0_i.fderiv_eq]; simp
          exact hy (by simp [h0])
        rw [← Complex.reCLM.integral_comp_comm h_int_y]
        refine integral_congr_ae ?_
        filter_upwards [Cons.C03.Concrete.rep_slice (p.wOf z) t] with y hy
        rw [nuLapT_periodizeTest_eq_on_Ioo hP0 hφ hφs b ht y, Complex.reCLM_apply,
          re_dotL_smul_single, ← hy, Complex.re_ofReal_mul]
      have hR_eq : ∫ t in Ioo 0 p.period, (Complex.reCLM (∫ y,
          PhaseSpace.dotL (periodizeTest p.period φ b (t, y))
            ((a (t : AddCircle p.period) : Space → PhaseSpace.CVec3) y))) =
          ∫ t in Ioo 0 p.period, ∫ y,
            φ (t, y) * (Cons.C03.Concrete.rep a t y b).re := by
        refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
        have h_int_y : Integrable (fun y =>
            PhaseSpace.dotL (periodizeTest p.period φ b (t, y))
              ((a (t : AddCircle p.period) : Space → PhaseSpace.CVec3) y)) volume := by
          have heq_y : (fun y => PhaseSpace.dotL
              (periodizeTest p.period φ b (t, y))
              ((a (t : AddCircle p.period) : Space → PhaseSpace.CVec3) y)) =ᵐ[volume]
              fun y => ((φ (t, y) : ℝ) : ℂ) * Cons.C03.Concrete.rep a t y b := by
            filter_upwards [Cons.C03.Concrete.rep_slice a t] with y hy
            rw [periodizeTest_eq_on_Ioc hP0 hφs b (Ioo_subset_Ioc_self ht) y, PhaseSpace.dotL_apply]
            simp [← hy]
          rw [integrable_congr heq_y]
          have hmem_ay : MemLp (fun y => Cons.C03.Concrete.rep a t y b)
              (11 / 4 : ℝ≥0∞) volume := by
            have h_ae : (fun y => Cons.C03.Concrete.rep a t y b) =ᵐ[volume]
                fun y => (a (t : AddCircle p.period) : Space → PhaseSpace.CVec3) y b := by
              filter_upwards [Cons.C03.Concrete.rep_slice a t] with y hy; rw [hy]
            rw [hq_eq]
            refine ⟨(((EuclideanSpace.proj b : PhaseSpace.CVec3 →L[ℂ] ℂ).continuous.measurable).comp
                ((Cons.C03.Concrete.stronglyMeasurable_rep a).comp_measurable
                  (measurable_const.prodMk measurable_id)).measurable).aestronglyMeasurable, ?_⟩
            rw [eLpNorm_congr_ae h_ae]
            exact lt_of_le_of_lt (eLpNorm_mono fun y => PiLp.norm_apply_le _ b)
              (MeasureTheory.Lp.memLp _).2
          have hq1 : (1 : ℝ≥0∞) ≤ 11 / 4 := by
            rw [ENNReal.le_div_iff_mul_le (by left; norm_num) (by right; norm_num)]
            norm_num
          have hK_sp : IsCompact (Prod.snd '' tsupport φ) := hφc.isCompact.image continuous_snd
          have hloc_ay := hmem_ay.locallyIntegrable hq1
          have hK_int := hloc_ay.integrableOn_isCompact hK_sp
          obtain ⟨M, hM⟩ := hK_sp.exists_bound_of_continuousOn
            (hφ.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
          have h_int_K : IntegrableOn (fun y =>
              ((φ (t, y) : ℝ) : ℂ) * Cons.C03.Concrete.rep a t y b)
              (Prod.snd '' tsupport φ) volume := by
            refine Integrable.mono' (hK_int.norm.const_mul M)
              ((Complex.continuous_ofReal.comp
                (hφ.continuous.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable.restrict.mul
                hK_int.aestronglyMeasurable) ?_
            filter_upwards [ae_restrict_mem hK_sp.isClosed.measurableSet] with y hy
            simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
              mul_le_mul_of_nonneg_right (hM y hy) (norm_nonneg _)
          refine (integrableOn_iff_integrable_of_support_subset (s := Prod.snd '' tsupport φ) ?_).mp h_int_K
          intro y hy
          exact ⟨(t, y), subset_tsupport φ (fun h0 => hy (by simp [h0])), rfl⟩
        rw [← Complex.reCLM.integral_comp_comm h_int_y]
        refine integral_congr_ae ?_
        filter_upwards [Cons.C03.Concrete.rep_slice a t] with y hy
        rw [periodizeTest_eq_on_Ioc hP0 hφs b (Ioo_subset_Ioc_self ht) y, Complex.reCLM_apply,
          re_dotL_smul_single, ← hy, Complex.re_ofReal_mul]
      rw [hL_eq, hR_eq] at hcancel
      simp_rw [← setIntegral_univ (μ := volume)] at hcancel
      rw [← setIntegral_prod _ h_int_L_prod, ← setIntegral_prod _ h_int_R_prod] at hcancel
      have h_corr_rep : (fun x : SpaceTime =>
          (p.ν * UnforcedLeray.Heat.laplacian (fun y' => φ (x.1, y')) x.2) *
            (Cons.C03.Concrete.rep (p.wOf z) x.1 x.2 b).re) =ᵐ[volume.restrict (Ioo 0 p.period ×ˢ univ)]
          fun x => (p.ν * UnforcedLeray.Heat.laplacian (fun y' => φ (x.1, y')) x.2) *
            p.corr z x.1 x.2 b := by
        filter_upwards [ae_restrict_of_ae hF_rep.2] with x hx
        have hxb : p.corr z x.1 x.2 b = (Cons.C03.Concrete.rep (p.wOf z) x.1 x.2 b).re := by
          have := congrArg (fun v : Space => v b) hx
          simpa [Cons.C03.Concrete.reP] using this
        rw [hxb]
      rw [← Measure.volume_eq_prod] at hcancel
      rw [integral_congr_ae h_corr_rep] at hcancel
      have h_int_sub : IntegrableOn (fun x : SpaceTime =>
          φ x * (p.ν * UnforcedLeray.Heat.laplacian (fun y' => p.corr z x.1 y' b) x.2))
          (Ioo 0 p.period ×ˢ univ) volume := by
        have hloc_c : LocallyIntegrableOn (fun x : SpaceTime =>
            p.ν * UnforcedLeray.Heat.laplacian (fun y' => p.corr z x.1 y' b) x.2)
            (Ioo 0 p.period ×ˢ univ) volume :=
          (continuous_const.mul
            ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).continuous.comp hcorr_lap_cont)).continuousOn.locallyIntegrableOn
            hU_open.measurableSet
        have hK_int := hloc_c.integrableOn_compact_subset hφs hφc
        obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuousOn
          hφ.continuous.continuousOn
        have h_int_K : IntegrableOn (fun x : SpaceTime =>
            φ x * (p.ν * UnforcedLeray.Heat.laplacian (fun y' => p.corr z x.1 y' b) x.2))
            (tsupport φ) volume := by
          refine Integrable.mono' (hK_int.norm.const_mul M)
            (hφ.continuous.aestronglyMeasurable.restrict.mul hK_int.aestronglyMeasurable) ?_
          filter_upwards [ae_restrict_mem (isClosed_tsupport φ).measurableSet] with x hx
          simpa [norm_mul, Real.norm_eq_abs] using
            mul_le_mul_of_nonneg_right (hM x hx)
              (abs_nonneg (p.ν * UnforcedLeray.Heat.laplacian (fun y' => p.corr z x.1 y' b) x.2))
        have h_int_all : Integrable (fun x : SpaceTime =>
            φ x * (p.ν * UnforcedLeray.Heat.laplacian (fun y' => p.corr z x.1 y' b) x.2)) volume := by
          refine (integrableOn_iff_integrable_of_support_subset (s := tsupport φ) ?_).mp h_int_K
          intro x hx
          exact subset_tsupport φ (fun h0 => hx (by simp [h0]))
        exact h_int_all.integrableOn
      have h_ibp : ∫ x in Ioo 0 p.period ×ˢ univ,
          (p.ν * UnforcedLeray.Heat.laplacian (fun y' => φ (x.1, y')) x.2) * p.corr z x.1 x.2 b =
          ∫ x in Ioo 0 p.period ×ˢ univ,
            φ x * (p.ν * UnforcedLeray.Heat.laplacian (fun y' => p.corr z x.1 y' b) x.2) := by
        have h_int_L2 : IntegrableOn (fun x : SpaceTime =>
            (p.ν * UnforcedLeray.Heat.laplacian (fun y' => φ (x.1, y')) x.2) *
              p.corr z x.1 x.2 b) (Ioo 0 p.period ×ˢ univ) volume :=
          h_int_L_prod.congr_fun_ae h_corr_rep
        rw [Measure.volume_eq_prod]
        rw [setIntegral_prod _ (by simpa [← Measure.volume_eq_prod] using h_int_L2),
          setIntegral_prod _ (by simpa [← Measure.volume_eq_prod] using h_int_sub)]
        simp only [setIntegral_univ]
        refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
        have hcs_y : HasCompactSupport (fun y : Space => φ (t, y)) :=
          .of_support_subset_isCompact (hφc.isCompact.image continuous_snd)
            fun y hy => ⟨(t, y), subset_tsupport φ hy, rfl⟩
        have hφt : ContDiff ℝ ∞ (fun y : Space => φ (t, y)) :=
          hφ.comp (contDiff_const.prodMk contDiff_id)
        have hct : ContDiff ℝ 2 (fun y : Space => p.corr z t y b) := by
          have hc_vec : ContDiff ℝ ∞ (fun y : Space => p.corr z t y) :=
            hcorr.comp (contDiff_const.prodMk contDiff_id)
          exact ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).contDiff.comp hc_vec).of_le (by simp)
        calc ∫ y, (p.ν * UnforcedLeray.Heat.laplacian (fun y' => φ (t, y')) y) * p.corr z t y b
            = p.ν * ∫ y, p.corr z t y b * UnforcedLeray.Heat.laplacian (fun y' => φ (t, y')) y := by
              rw [← integral_const_mul]
              congr 1; ext y; ring
          _ = p.ν * ∫ y, UnforcedLeray.Heat.laplacian (fun y' => p.corr z t y' b) y * φ (t, y) := by
              rw [integral_laplacian_mul_eq hct hφt hcs_y]
          _ = ∫ y, φ (t, y) * (p.ν * UnforcedLeray.Heat.laplacian (fun y' => p.corr z t y' b) y) := by
              rw [← integral_const_mul]
              congr 1; ext y; ring
      rw [h_ibp] at hcancel
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo 0 p.period ×ˢ univ)]
      · simp only [smul_eq_mul, Pi.sub_apply, mul_sub]
        rw [integral_sub h_int_sub h_int_R_prod, sub_eq_zero]
        exact hcancel
      · intro x hx
        simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hφs h))]
  have hae_vec : (fun x : SpaceTime => p.ν • vecLaplacian (p.corr z x.1) x.2) =ᵐ[
      volume.restrict (periodSlab p.period)]
      fun x => Cons.C03.Concrete.reP (Cons.C03.Concrete.rep a x.1 x.2) := by
    rw [hres]
    filter_upwards [ae_all_iff.mpr hae_coord] with x hx
    ext b
    simpa [Cons.C03.Concrete.reP, vecLaplacian_apply] using hx b
  have hmem_nu : MemLp (fun x : SpaceTime => p.ν • vecLaplacian (p.corr z x.1) x.2)
      (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period)) :=
    ha_mem.ae_eq hae_vec.symm
  have hmem : MemLp (fun x : SpaceTime => vecLaplacian (p.corr z x.1) x.2)
      (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period)) := by
    have heq : (fun x : SpaceTime => vecLaplacian (p.corr z x.1) x.2) =
        p.ν⁻¹ • (fun x : SpaceTime => p.ν • vecLaplacian (p.corr z x.1) x.2) := by
      funext x; exact (inv_smul_smul₀ p.ν_pos.ne' _).symm
    rw [heq]
    exact hmem_nu.const_smul p.ν⁻¹
  refine ⟨hmem, ?_⟩
  have heq : (fun x : SpaceTime => vecLaplacian (p.corr z x.1) x.2) =
      p.ν⁻¹ • (fun x : SpaceTime => p.ν • vecLaplacian (p.corr z x.1) x.2) := by
    funext x; exact (inv_smul_smul₀ p.ν_pos.ne' _).symm
  rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.mpr p.ν_pos),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_pos.mpr p.ν_pos).le, eLpNorm_congr_ae hae_vec]
  calc p.ν⁻¹ * (eLpNorm (fun x => Cons.C03.Concrete.reP (Cons.C03.Concrete.rep a x.1 x.2))
          (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period))).toReal
      ≤ p.ν⁻¹ * (p.period ^ ((4 : ℝ) / 11) * ‖z‖) :=
        mul_le_mul_of_nonneg_left ha_eb (inv_pos.mpr p.ν_pos).le
    _ = p.period ^ ((4 : ℝ) / 11) * (p.ν⁻¹ * ‖z‖) := by ring

private lemma continuous_laplacian_of_contDiff
    {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) : Continuous (Heat.laplacian f) := by
  refine continuous_finsetSum _ fun j _ => ?_
  have h1 : ContDiff ℝ ∞ (fun y => fderiv ℝ f y (coordinateVector j)) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have h2 : ContDiff ℝ ∞ (fun y => fderiv ℝ (fun y' => fderiv ℝ f y' (coordinateVector j)) y
      (coordinateVector j)) := (h1.fderiv_right (by simp)).clm_apply contDiff_const
  exact h2.continuous

private lemma rieszPairL2_laplacian_test
    {Φ : Space → ℝ} (hΦ : IsSpatialTest Φ) (i k : Fin 3) :
    RieszLp.rieszPairL2 i k
        (((PressureAnalysis.scalarTest_laplacian hΦ).memLp 2).toLp
          (Heat.laplacian Φ)) =
      -((((hΦ.derivative k).derivative i).memLp 2).toLp
        (spatialTestDerivative i
          (spatialTestDerivative k Φ))) := by
  rw [RieszLp.rieszPairL2_toLp
    (PressureAnalysis.scalarTest_laplacian hΦ) i k]
  apply Lp.ext
  filter_upwards [
    (RieszLp.memLp_rieszPairTest
      (PressureAnalysis.scalarTest_laplacian hΦ) i k).coeFn_toLp,
    (((hΦ.derivative k).derivative i).memLp 2).coeFn_toLp,
    Lp.coeFn_neg ((((hΦ.derivative k).derivative i).memLp 2).toLp
      (spatialTestDerivative i
        (spatialTestDerivative k Φ)))] with y h₁ h₂ h₃
  rw [h₁, h₃]
  change RieszLp.rieszPairTest i k (Heat.laplacian Φ) y =
    -((((hΦ.derivative k).derivative i).memLp 2).toLp
      (spatialTestDerivative i
        (spatialTestDerivative k Φ)) y)
  have hconv : RieszLp.newtonConv (Heat.laplacian Φ) =
      fun x => -Φ x :=
    funext fun x => RieszLp.newtonConv_laplacian_test hΦ x
  rw [h₂,
    RieszLp.rieszPairTest_eq_newtonConv
      (PressureAnalysis.scalarTest_laplacian hΦ) i k,
    ← RieszLp.spatialTestDerivative_newtonConv
      ((PressureAnalysis.scalarTest_laplacian hΦ).derivative k) i,
    ← RieszLp.spatialTestDerivative_newtonConv
      (PressureAnalysis.scalarTest_laplacian hΦ) k,
    hconv]
  have hneg : spatialTestDerivative k (fun x => -Φ x) =
      fun x => -spatialTestDerivative k Φ x := by
    funext x
    simp [spatialTestDerivative, fderiv_fun_neg]
  rw [hneg]
  simp only [spatialTestDerivative, fderiv_fun_neg, ContinuousLinearMap.neg_apply, neg_neg]
  rfl

private lemma riesz_hessian_slice_aux
    {u : Space → ℝ} (hu : ContDiff ℝ ∞ u)
    (hu_mem : MemLp u (11 / 4 : ℝ≥0∞) volume)
    (hgrad_mem : MemLp (fun y => fderiv ℝ u y) (11 / 4 : ℝ≥0∞) volume)
    (hΔ_mem : MemLp (Heat.laplacian u) (11 / 4 : ℝ≥0∞) volume)
    (i k : Fin 3) :
    spatialTestDerivative i
        (spatialTestDerivative k u) =ᵐ[volume]
      -(RieszLp.rieszPairLp i k (11 / 4 : ℝ≥0∞)
          (by rw [ENNReal.lt_div_iff_mul_lt (by left; norm_num) (by right; norm_num)]; norm_num)
          (by simp [ENNReal.div_eq_top]) (hΔ_mem.toLp (Heat.laplacian u)) : Space → ℝ) := by
  have hq_gt1 : (1 : ℝ≥0∞) < 11 / 4 := by
    rw [ENNReal.lt_div_iff_mul_lt (by left; norm_num) (by right; norm_num)]; norm_num
  have hq_ne_top : (11 / 4 : ℝ≥0∞) ≠ ⊤ := by simp [ENNReal.div_eq_top]
  have hq_ge1 : (1 : ℝ≥0∞) ≤ 11 / 4 := hq_gt1.le
  have : Fact ((1 : ℝ≥0∞) ≤ 11 / 4) := ⟨hq_ge1⟩
  let χ : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, one_lt_two⟩
  let χm : ℕ → Space → ℝ := fun m y => χ (((m : ℝ) + 1)⁻¹ • y)
  let um : ℕ → Space → ℝ := fun m y => χm m y * u y
  have hχ_smooth : ContDiff ℝ ∞ χ := χ.contDiff
  have hχ_cs : HasCompactSupport χ := χ.hasCompactSupport
  have hχm_smooth : ∀ m : ℕ, ContDiff ℝ ∞ (χm m) := fun m =>
    hχ_smooth.comp ((contDiff_const (c := ((m : ℝ) + 1)⁻¹)).smul contDiff_id)
  have hum_test : ∀ m : ℕ, IsSpatialTest (um m) := by
    intro m
    refine ⟨(hχm_smooth m).mul hu, ?_⟩
    have hm_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hcs_m : HasCompactSupport (χm m) := by
      refine HasCompactSupport.of_support_subset_isCompact
        (isCompact_closedBall (0 : Space) (2 * ((m : ℝ) + 1))) fun y hy => ?_
      rw [mem_closedBall_zero_iff]
      by_contra hgt
      push_neg at hgt
      apply hy
      apply χ.zero_of_le_dist
      rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hm_pos.le)]
      have : 2 ≤ ((m : ℝ) + 1)⁻¹ * ‖y‖ := by
        rw [inv_mul_eq_div, le_div_iff₀ hm_pos]
        exact hgt.le
      exact this
    exact hcs_m.mul_right
  have hgrad_χ_bd : ∃ M₁ : ℝ, 0 ≤ M₁ ∧ ∀ y : Space, ‖fderiv ℝ χ y‖ ≤ M₁ := by
    obtain ⟨M₁, hM₁⟩ := hχ_cs.isCompact.exists_bound_of_continuousOn
      (hχ_smooth.continuous_fderiv (by simp)).continuousOn
    refine ⟨max M₁ 0, le_max_right _ _, fun y => ?_⟩
    by_cases hy : y ∈ tsupport χ
    · exact (hM₁ y hy).trans (le_max_left _ _)
    · have h0 : fderiv ℝ χ y = 0 := (notMem_tsupport_iff_eventuallyEq.mp hy).fderiv_eq.trans (by simp)
      rw [h0, norm_zero]; exact le_max_right _ _
  have hlap_χ_bd : ∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ y : Space, |Heat.laplacian χ y| ≤ M₂ := by
    have hlap_cont : Continuous (Heat.laplacian χ) := by
      refine continuous_finsetSum _ fun j _ => ?_
      have h1 : ContDiff ℝ ∞ (fun y => fderiv ℝ χ y (coordinateVector j)) :=
        (hχ_smooth.fderiv_right (by simp)).clm_apply contDiff_const
      have h2 : ContDiff ℝ ∞ (fun y => fderiv ℝ (fun y' => fderiv ℝ χ y' (coordinateVector j)) y
          (coordinateVector j)) := (h1.fderiv_right (by simp)).clm_apply contDiff_const
      exact h2.continuous
    obtain ⟨M₂, hM₂⟩ := hχ_cs.isCompact.exists_bound_of_continuousOn hlap_cont.continuousOn
    refine ⟨max M₂ 0, le_max_right _ _, fun y => ?_⟩
    by_cases hy : y ∈ tsupport χ
    · simpa [Real.norm_eq_abs] using (hM₂ y hy).trans (le_max_left M₂ 0)
    · have h0 : Heat.laplacian χ y = 0 := by
        simp only [Heat.laplacian]
        refine Finset.sum_eq_zero fun j _ => ?_
        have h0_j : (fun y' => fderiv ℝ χ y' (coordinateVector j)) =ᶠ[𝓝 y] 0 := by
          filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hy] with y' hy'
          rw [(notMem_tsupport_iff_eventuallyEq.mp hy').fderiv_eq]; simp
        rw [h0_j.fderiv_eq]; simp
      rw [h0, abs_zero]; exact le_max_right _ _
  obtain ⟨M₁, hM₁_nn, hM₁⟩ := hgrad_χ_bd
  obtain ⟨M₂, hM₂_nn, hM₂⟩ := hlap_χ_bd
  have hΔum_mem : ∀ m : ℕ, MemLp (Heat.laplacian (um m)) (11 / 4 : ℝ≥0∞) volume :=
    fun m => (PressureAnalysis.scalarTest_laplacian (hum_test m)).memLp (11 / 4)
  have htend_lap : Tendsto (fun m : ℕ =>
      eLpNorm (fun y => Heat.laplacian (um m) y - Heat.laplacian u y)
        (11 / 4 : ℝ≥0∞) volume) atTop (𝓝 0) := by
    have hdiff_le : ∀ (m : ℕ) (y : Space),
        ‖Heat.laplacian (um m) y - Heat.laplacian u y‖ ≤
          |χm m y - 1| * |Heat.laplacian u y| +
            (6 * M₁ * ((m : ℝ) + 1)⁻¹) * ‖fderiv ℝ u y‖ +
            (M₂ * ((m : ℝ) + 1)⁻¹ ^ 2) * |u y| := by
      intro m y
      have hm_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hfderiv_χm : ∀ y' : Space, fderiv ℝ (χm m) y' =
          ((m : ℝ) + 1)⁻¹ • fderiv ℝ χ (((m : ℝ) + 1)⁻¹ • y') := by
        intro y'
        have hcomp : HasFDerivAt (fun z : Space => χ (((m : ℝ) + 1)⁻¹ • z))
            ((fderiv ℝ χ (((m : ℝ) + 1)⁻¹ • y')).comp
              (((m : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ Space)) y' :=
          (hχ_smooth.differentiable (by simp) _).hasFDerivAt.comp y'
            ((hasFDerivAt_id y').const_smul ((m : ℝ) + 1)⁻¹)
        rw [hcomp.fderiv]
        ext v; simp [ContinuousLinearMap.smul_apply]
      have hlap_χm : Heat.laplacian (χm m) y =
          ((m : ℝ) + 1)⁻¹ ^ 2 * Heat.laplacian χ (((m : ℝ) + 1)⁻¹ • y) := by
        simp only [Heat.laplacian, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have h1_eq : (fun y' : Space => fderiv ℝ (χm m) y' (coordinateVector j)) =
            fun y' => ((m : ℝ) + 1)⁻¹ *
              fderiv ℝ χ (((m : ℝ) + 1)⁻¹ • y') (coordinateVector j) := by
          funext y'; rw [hfderiv_χm y', ContinuousLinearMap.smul_apply, smul_eq_mul]
        rw [h1_eq]
        have h2_d : HasFDerivAt (fun y' : Space =>
            ((m : ℝ) + 1)⁻¹ * fderiv ℝ χ (((m : ℝ) + 1)⁻¹ • y') (coordinateVector j))
            (((m : ℝ) + 1)⁻¹ • ((fderiv ℝ (fun z => fderiv ℝ χ z (coordinateVector j))
              (((m : ℝ) + 1)⁻¹ • y)).comp (((m : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ Space))) y := by
          have hd : ContDiff ℝ ∞ (fun z : Space => fderiv ℝ χ z (coordinateVector j)) :=
            (hχ_smooth.fderiv_right (by simp)).clm_apply contDiff_const
          exact ((hd.differentiable (by simp) _).hasFDerivAt.comp y
            ((hasFDerivAt_id y).const_smul ((m : ℝ) + 1)⁻¹)).const_mul ((m : ℝ) + 1)⁻¹
        rw [h2_d.fderiv]
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply, smul_eq_mul, map_smul]
        ring
      have hprod_lap : Heat.laplacian (um m) y =
          χm m y * Heat.laplacian u y +
            2 * (∑ j : Fin 3, fderiv ℝ (χm m) y (coordinateVector j) *
              fderiv ℝ u y (coordinateVector j)) +
            Heat.laplacian (χm m) y * u y := by
        simp only [Heat.laplacian, Finset.mul_sum]
        have hterm : ∀ j : Fin 3,
            fderiv ℝ (fun y' => fderiv ℝ (um m) y' (coordinateVector j)) y (coordinateVector j) =
              χm m y * fderiv ℝ (fun y' => fderiv ℝ u y' (coordinateVector j)) y (coordinateVector j) +
                2 * (fderiv ℝ (χm m) y (coordinateVector j) * fderiv ℝ u y (coordinateVector j)) +
                fderiv ℝ (fun y' => fderiv ℝ (χm m) y' (coordinateVector j)) y (coordinateVector j) * u y := by
          intro j
          have hfd_um : (fun y' : Space => fderiv ℝ (um m) y' (coordinateVector j)) =
              fun y' => χm m y' * fderiv ℝ u y' (coordinateVector j) +
                fderiv ℝ (χm m) y' (coordinateVector j) * u y' := by
            funext y'
            have h1 := ((hχm_smooth m).differentiable (by simp) y').hasFDerivAt.mul
              (hu.differentiable (by simp) y').hasFDerivAt
            change fderiv ℝ (χm m * u) y' (coordinateVector j) = _
            rw [h1.fderiv]
            simp [smul_eq_mul, mul_comm]
          rw [hfd_um]
          have hdu : ContDiff ℝ ∞ (fun y' : Space => fderiv ℝ u y' (coordinateVector j)) :=
            (hu.fderiv_right (by simp)).clm_apply contDiff_const
          have hA : HasFDerivAt (fun y' => χm m y' * fderiv ℝ u y' (coordinateVector j))
              (χm m y • fderiv ℝ (fun y' => fderiv ℝ u y' (coordinateVector j)) y +
                fderiv ℝ u y (coordinateVector j) • fderiv ℝ (χm m) y) y :=
            ((hχm_smooth m).differentiable (by simp) y).hasFDerivAt.mul
              (hdu.differentiable (by simp) y).hasFDerivAt
          have hdχ : ContDiff ℝ ∞ (fun y' : Space => fderiv ℝ (χm m) y' (coordinateVector j)) :=
            ((hχm_smooth m).fderiv_right (by simp)).clm_apply contDiff_const
          have hB : HasFDerivAt (fun y' => fderiv ℝ (χm m) y' (coordinateVector j) * u y')
              (fderiv ℝ (χm m) y (coordinateVector j) • fderiv ℝ u y +
                u y • fderiv ℝ (fun y' => fderiv ℝ (χm m) y' (coordinateVector j)) y) y :=
            (hdχ.differentiable (by simp) y).hasFDerivAt.mul (hu.differentiable (by simp) y).hasFDerivAt
          have hAB : fderiv ℝ (fun y' => χm m y' * fderiv ℝ u y' (coordinateVector j) +
              fderiv ℝ (χm m) y' (coordinateVector j) * u y') y =
              (χm m y • fderiv ℝ (fun y' => fderiv ℝ u y' (coordinateVector j)) y +
                fderiv ℝ u y (coordinateVector j) • fderiv ℝ (χm m) y) +
              (fderiv ℝ (χm m) y (coordinateVector j) • fderiv ℝ u y +
                u y • fderiv ℝ (fun y' => fderiv ℝ (χm m) y' (coordinateVector j)) y) :=
            (hA.add hB).fderiv
          rw [hAB]
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
          ring
        simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [hprod_lap]
      have hrew : χm m y * Heat.laplacian u y +
          2 * ∑ j : Fin 3, fderiv ℝ (χm m) y (coordinateVector j) * fderiv ℝ u y (coordinateVector j) +
          Heat.laplacian (χm m) y * u y - Heat.laplacian u y =
          (χm m y - 1) * Heat.laplacian u y +
            2 * ∑ j : Fin 3, fderiv ℝ (χm m) y (coordinateVector j) * fderiv ℝ u y (coordinateVector j) +
            Heat.laplacian (χm m) y * u y := by ring
      rw [hrew, Real.norm_eq_abs]
      refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
      · rw [abs_mul]
      · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have hsum_le : |∑ j : Fin 3, fderiv ℝ (χm m) y (coordinateVector j) *
            fderiv ℝ u y (coordinateVector j)| ≤
            3 * (M₁ * ((m : ℝ) + 1)⁻¹ * ‖fderiv ℝ u y‖) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          have hterm_le : ∀ j : Fin 3,
              |fderiv ℝ (χm m) y (coordinateVector j) * fderiv ℝ u y (coordinateVector j)| ≤
                M₁ * ((m : ℝ) + 1)⁻¹ * ‖fderiv ℝ u y‖ := by
            intro j
            rw [abs_mul]
            have h1 : |fderiv ℝ (χm m) y (coordinateVector j)| ≤ M₁ * ((m : ℝ) + 1)⁻¹ := by
              rw [hfderiv_χm y, ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul,
                abs_of_nonneg (inv_nonneg.mpr hm_pos.le)]
              have := (ContinuousLinearMap.le_opNorm (fderiv ℝ χ (((m : ℝ) + 1)⁻¹ • y))
                (coordinateVector j)).trans (by simp [coordinateVector]; exact hM₁ _)
              rw [Real.norm_eq_abs] at this
              nlinarith [inv_nonneg.mpr hm_pos.le]
            have h2 : |fderiv ℝ u y (coordinateVector j)| ≤ ‖fderiv ℝ u y‖ := by
              simpa [Real.norm_eq_abs, coordinateVector] using
                ContinuousLinearMap.le_opNorm (fderiv ℝ u y) (coordinateVector j)
            exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
          calc ∑ j : Fin 3, |fderiv ℝ (χm m) y (coordinateVector j) * fderiv ℝ u y (coordinateVector j)|
              ≤ ∑ _j : Fin 3, (M₁ * ((m : ℝ) + 1)⁻¹ * ‖fderiv ℝ u y‖) :=
                Finset.sum_le_sum fun j _ => hterm_le j
            _ = 3 * (M₁ * ((m : ℝ) + 1)⁻¹ * ‖fderiv ℝ u y‖) := by simp [mul_comm]
        nlinarith
      · rw [abs_mul, hlap_χm, abs_mul, abs_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hM₂ _) (sq_nonneg _) |>.trans_eq (mul_comm _ _)) (abs_nonneg _)
    have hpiece1 : Tendsto (fun m : ℕ =>
        eLpNorm (fun y => (χm m y - 1) * Heat.laplacian u y) (11 / 4 : ℝ≥0∞) volume)
        atTop (𝓝 0) := by
      have hlint_tend : Tendsto (fun m : ℕ =>
          ∫⁻ y : Space, ‖(χm m y - 1) * Heat.laplacian u y‖ₑ ^ ((11 : ℝ) / 4))
          atTop (𝓝 0) := by
        have hdom : ∫⁻ y : Space, ‖Heat.laplacian u y‖ₑ ^ ((11 : ℝ) / 4) ≠ ⊤ := by
          have h := hΔ_mem.2
          rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) hq_ne_top] at h
          simpa using h.ne
        have h0_eq : (0 : ℝ≥0∞) = ∫⁻ _ : Space, (0 : ℝ≥0∞) := by simp
        rw [h0_eq]
        refine tendsto_lintegral_of_dominated_convergence _ (fun m => ?_) (fun m => ?_) hdom ?_
        · exact (Continuous.enorm (((hχm_smooth m).continuous.sub continuous_const).mul
            (continuous_laplacian_of_contDiff hu))).measurable.pow_const _
        · filter_upwards with y
          have hχ_bd : |χm m y - 1| ≤ 1 := by
            have h0 : 0 ≤ χm m y := χ.nonneg
            have h1 : χm m y ≤ 1 := χ.le_one
            rw [abs_le]; constructor <;> linarith
          have hnorm_le : ‖(χm m y - 1) * Heat.laplacian u y‖ₑ ≤
              ‖Heat.laplacian u y‖ₑ := by
            rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_mul]
            exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (abs_nonneg _) hχ_bd)
          exact ENNReal.rpow_le_rpow hnorm_le (by norm_num)
        · filter_upwards with y
          have hev : ∀ᶠ m : ℕ in atTop,
              ‖(χm m y - 1) * Heat.laplacian u y‖ₑ ^ ((11 : ℝ) / 4) = 0 := by
            obtain ⟨N, hN⟩ := exists_nat_gt ‖y‖
            rw [eventually_atTop]
            refine ⟨N, fun m hm => ?_⟩
            have hm1 : ‖y‖ ≤ (m : ℝ) + 1 := by
              have : (N : ℝ) ≤ m := by exact_mod_cast hm
              linarith
            have h1 : χm m y = 1 := by
              apply χ.one_of_mem_closedBall
              rw [mem_closedBall_zero_iff, norm_smul,
                Real.norm_of_nonneg (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1))]
              rw [inv_mul_eq_div, div_le_one (by positivity)]
              exact hm1
            simp [h1]
          exact tendsto_const_nhds.congr' (hev.mono fun m hm => hm.symm)
      have hrpow_cont : Continuous (fun t : ℝ≥0∞ => t ^ ((4 : ℝ) / 11)) :=
        ENNReal.continuous_rpow_const
      have ht2 := (hrpow_cont.tendsto 0).comp hlint_tend
      simp only [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 4 / 11)] at ht2
      refine ht2.congr fun m => ?_
      rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) hq_ne_top]
      simp
    have hpiece2 : Tendsto (fun m : ℕ =>
        eLpNorm (fun y => (6 * M₁ * ((m : ℝ) + 1)⁻¹) * ‖fderiv ℝ u y‖) (11 / 4 : ℝ≥0∞) volume)
        atTop (𝓝 0) := by
      have ht_sc : Tendsto (fun m : ℕ => ENNReal.ofReal (6 * M₁ * ((m : ℝ) + 1)⁻¹) *
          eLpNorm (fun y => fderiv ℝ u y) (11 / 4 : ℝ≥0∞) volume) atTop (𝓝 0) := by
        have h0_sc : Tendsto (fun m : ℕ => (6 * M₁ * ((m : ℝ) + 1)⁻¹ : ℝ)) atTop (𝓝 0) := by
          simpa using ((tendsto_const_nhds (x := 6 * M₁)).mul (tendsto_inv_atTop_zero.comp
            (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))))
        have h1_sc := (ENNReal.continuous_ofReal.tendsto 0).comp h0_sc
        simp only [ENNReal.ofReal_zero] at h1_sc
        simpa using ENNReal.Tendsto.mul_const h1_sc (Or.inr hgrad_mem.2.ne)
      refine ht_sc.congr fun m => ?_
      have heq_s : (fun y : Space => (6 * M₁ * ((m : ℝ) + 1)⁻¹) * ‖fderiv ℝ u y‖) =
          (6 * M₁ * ((m : ℝ) + 1)⁻¹) • (fun y => ‖fderiv ℝ u y‖) := rfl
      rw [heq_s, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs,
        abs_of_nonneg (by positivity), eLpNorm_norm]
    have hpiece3 : Tendsto (fun m : ℕ =>
        eLpNorm (fun y => (M₂ * ((m : ℝ) + 1)⁻¹ ^ 2) * |u y|) (11 / 4 : ℝ≥0∞) volume)
        atTop (𝓝 0) := by
      have ht_sc : Tendsto (fun m : ℕ => ENNReal.ofReal (M₂ * ((m : ℝ) + 1)⁻¹ ^ 2) *
          eLpNorm u (11 / 4 : ℝ≥0∞) volume) atTop (𝓝 0) := by
        have h0_sc : Tendsto (fun m : ℕ => (M₂ * ((m : ℝ) + 1)⁻¹ ^ 2 : ℝ)) atTop (𝓝 0) := by
          have hinv := tendsto_inv_atTop_zero.comp
            (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
          simpa using (tendsto_const_nhds (x := M₂)).mul (hinv.pow 2)
        have h1_sc := (ENNReal.continuous_ofReal.tendsto 0).comp h0_sc
        simp only [ENNReal.ofReal_zero] at h1_sc
        simpa using ENNReal.Tendsto.mul_const h1_sc (Or.inr hu_mem.2.ne)
      refine ht_sc.congr fun m => ?_
      have heq_s : (fun y : Space => (M₂ * ((m : ℝ) + 1)⁻¹ ^ 2) * |u y|) =
          (M₂ * ((m : ℝ) + 1)⁻¹ ^ 2) • (fun y => ‖u y‖) := by
        funext y; simp [Real.norm_eq_abs, smul_eq_mul]
      rw [heq_s, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs,
        abs_of_nonneg (by positivity), eLpNorm_norm]
    have hsum_tend : Tendsto (fun m : ℕ =>
        eLpNorm (fun y => (χm m y - 1) * Heat.laplacian u y) (11 / 4 : ℝ≥0∞) volume +
        eLpNorm (fun y => (6 * M₁ * ((m : ℝ) + 1)⁻¹) * ‖fderiv ℝ u y‖) (11 / 4 : ℝ≥0∞) volume +
        eLpNorm (fun y => (M₂ * ((m : ℝ) + 1)⁻¹ ^ 2) * |u y|) (11 / 4 : ℝ≥0∞) volume)
        atTop (𝓝 0) := by
      simpa using (hpiece1.add hpiece2).add hpiece3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum_tend
      (fun _ => bot_le) (fun m => ?_)
    have h_eLp_le : eLpNorm (fun y => Heat.laplacian (um m) y -
        Heat.laplacian u y) (11 / 4 : ℝ≥0∞) volume ≤
        eLpNorm (fun y => |χm m y - 1| * |Heat.laplacian u y| +
          (6 * M₁ * ((m : ℝ) + 1)⁻¹) * ‖fderiv ℝ u y‖ +
          (M₂ * ((m : ℝ) + 1)⁻¹ ^ 2) * |u y|) (11 / 4 : ℝ≥0∞) volume := by
      refine eLpNorm_mono fun y => ?_
      exact (hdiff_le m y).trans (le_abs_self _) |>.trans_eq (Real.norm_eq_abs _).symm
    refine h_eLp_le.trans ?_
    have hsm1 : AEStronglyMeasurable (fun y => |χm m y - 1| * |Heat.laplacian u y|) volume :=
      (((hχm_smooth m).continuous.sub continuous_const).abs.mul
        (continuous_laplacian_of_contDiff hu).abs).aestronglyMeasurable
    have hsm2 : AEStronglyMeasurable (fun y => (6 * M₁ * ((m : ℝ) + 1)⁻¹) * ‖fderiv ℝ u y‖) volume :=
      (continuous_const.mul (hu.continuous_fderiv (by simp)).norm).aestronglyMeasurable
    have hsm3 : AEStronglyMeasurable (fun y => (M₂ * ((m : ℝ) + 1)⁻¹ ^ 2) * |u y|) volume :=
      (continuous_const.mul hu.continuous.abs).aestronglyMeasurable
    refine (eLpNorm_add_le (hsm1.add hsm2) hsm3 hq_ge1).trans ?_
    refine add_le_add ((eLpNorm_add_le hsm1 hsm2 hq_ge1).trans (add_le_add ?_ le_rfl)) le_rfl
    refine eLpNorm_mono fun y => ?_
    simp [Real.norm_eq_abs, abs_mul]
  let Rop := RieszLp.rieszPairLp i k (11 / 4 : ℝ≥0∞) hq_gt1 hq_ne_top
  have htend_Rop : Tendsto (fun m : ℕ =>
      Rop ((hΔum_mem m).toLp (Heat.laplacian (um m))))
      atTop (𝓝 (Rop (hΔ_mem.toLp (Heat.laplacian u)))) := by
    refine (Rop.continuous.tendsto _).comp ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have ht_real : Tendsto (fun m : ℕ =>
        (eLpNorm (fun y => Heat.laplacian (um m) y -
          Heat.laplacian u y) (11 / 4 : ℝ≥0∞) volume).toReal)
        atTop (𝓝 0) :=
      ((ENNReal.continuousAt_toReal (by simp)).tendsto.comp htend_lap).congr (fun _ => rfl)
    refine ht_real.congr fun m => ?_
    rw [Lp.norm_def]
    congr 1
    exact eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans
      ((hΔum_mem m).coeFn_toLp.sub hΔ_mem.coeFn_toLp)).symm
  have h_d2_smooth : ContDiff ℝ ∞ (spatialTestDerivative i (spatialTestDerivative k u)) := by
    have h1 : ContDiff ℝ ∞ (spatialTestDerivative k u) :=
      (hu.fderiv_right (by simp)).clm_apply contDiff_const
    exact (h1.fderiv_right (by simp)).clm_apply contDiff_const
  have h_ae_zero : spatialTestDerivative i (spatialTestDerivative k u) +
      (Rop (hΔ_mem.toLp (Heat.laplacian u)) : Space → ℝ) =ᵐ[volume] 0 :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (h_d2_smooth.continuous.locallyIntegrable.add
        ((MeasureTheory.Lp.memLp _).locallyIntegrable hq_ge1)) fun φ hφ hφc => by {
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨M, hM⟩ := exists_nat_gt (max R 0)
  have hM_eq : ∀ m : ℕ, M ≤ m →
      ∫ y : Space, φ y *
        spatialTestDerivative i
          (spatialTestDerivative k u) y =
        -(∫ y : Space, φ y *
          (Rop ((hΔum_mem m).toLp (Heat.laplacian (um m))) : Space → ℝ) y) := by
    intro m hm
    have hagree : EqOn (um m) u (Metric.ball 0 ((m : ℝ) + 1)) := by
      intro y hy
      have h1 : χm m y = 1 := by
        apply χ.one_of_mem_closedBall
        rw [mem_closedBall_zero_iff, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1))]
        rw [inv_mul_eq_div, div_le_one (by positivity)]
        exact (mem_ball_zero_iff.mp hy).le
      simp [um, h1]
    have hagree_d2 : ∀ y ∈ tsupport φ,
        spatialTestDerivative i
          (spatialTestDerivative k u) y =
        spatialTestDerivative i
          (spatialTestDerivative k (um m)) y := by
      intro y hy
      have hy_ball : y ∈ Metric.ball (0 : Space) ((m : ℝ) + 1) := by
        have hR_lt : R < (m : ℝ) + 1 := by
          have : (M : ℝ) ≤ m := by exact_mod_cast hm
          linarith [le_max_left R 0]
        exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp (hR hy)).trans_lt hR_lt)
      have hev1 : um m =ᶠ[𝓝 y] u :=
        Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hy_ball) hagree
      have hev2 : spatialTestDerivative k (um m) =ᶠ[𝓝 y]
          spatialTestDerivative k u := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hy_ball] with y' hy'
        have hloc : um m =ᶠ[𝓝 y'] u :=
          Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hy') hagree
        simp [spatialTestDerivative, hloc.fderiv_eq]
      simp [spatialTestDerivative, hev2.fderiv_eq]
    have hL_eq : ∫ y : Space, φ y *
        spatialTestDerivative i
          (spatialTestDerivative k u) y =
        ∫ y : Space, φ y *
          spatialTestDerivative i
            (spatialTestDerivative k (um m)) y := by
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      by_cases hy : y ∈ tsupport φ
      · dsimp only
        rw [hagree_d2 y hy]
      · simp [image_eq_zero_of_notMem_tsupport hy]
    have hR_ae : (Rop ((hΔum_mem m).toLp (Heat.laplacian (um m))) : Space → ℝ) =ᵐ[volume]
        fun y => -spatialTestDerivative i
          (spatialTestDerivative k (um m)) y := by
      have h2 := RieszLp.rieszPairLp_toLp_ae i k hq_gt1 hq_ne_top
        (hΔum_mem m) ((PressureAnalysis.scalarTest_laplacian (hum_test m)).memLp 2)
      have h3 := rieszPairL2_laplacian_test (hum_test m) i k
      filter_upwards [h2, Lp.coeFn_neg
        ((((hum_test m).derivative k).derivative i).memLp 2 |>.toLp
          (spatialTestDerivative i (spatialTestDerivative k (um m)))),
        (((hum_test m).derivative k).derivative i).memLp 2 |>.coeFn_toLp] with y hy1 hy2 hy3
      rw [hy1, h3, hy2, Pi.neg_apply, hy3]
    rw [hL_eq]
    have hR_eq : ∫ y : Space, φ y *
        (Rop ((hΔum_mem m).toLp (Heat.laplacian (um m))) : Space → ℝ) y =
        -(∫ y : Space, φ y *
          spatialTestDerivative i
            (spatialTestDerivative k (um m)) y) := by
      calc ∫ y : Space, φ y *
            (Rop ((hΔum_mem m).toLp (Heat.laplacian (um m))) : Space → ℝ) y
          = ∫ y : Space, φ y *
              (-spatialTestDerivative i
                (spatialTestDerivative k (um m)) y) :=
            integral_congr_ae (hR_ae.mono fun y hy => by dsimp only; rw [hy])
        _ = -(∫ y : Space, φ y *
              spatialTestDerivative i
                (spatialTestDerivative k (um m)) y) := by
            rw [← integral_neg]; congr 1; ext y; ring
    rw [hR_eq, neg_neg]
  have hφ_conj : MemLp φ (11 / 7 : ℝ≥0∞) volume :=
    hφ.continuous.memLp_of_hasCompactSupport hφc
  haveI : ENNReal.HolderTriple (11 / 7 : ℝ≥0∞) (11 / 4 : ℝ≥0∞) 1 := by
    apply ENNReal.HolderTriple.of_toReal
    norm_num [Real.holderTriple_iff, ENNReal.toReal_div]
  have htend_int : Tendsto (fun m : ℕ =>
      ∫ y : Space, φ y *
        (Rop ((hΔum_mem m).toLp (Heat.laplacian (um m))) : Space → ℝ) y)
      atTop (𝓝 (∫ y : Space, φ y *
        (Rop (hΔ_mem.toLp (Heat.laplacian u)) : Space → ℝ) y)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have ht_norm : Tendsto (fun m : ℕ =>
        ‖Rop ((hΔum_mem m).toLp (Heat.laplacian (um m))) -
          Rop (hΔ_mem.toLp (Heat.laplacian u))‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp htend_Rop
    have h_bdd : 0 ≤ (eLpNorm φ (11 / 7 : ℝ≥0∞) volume).toReal := ENNReal.toReal_nonneg
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht_norm
      (ε / ((eLpNorm φ (11 / 7 : ℝ≥0∞) volume).toReal + 1)) (by positivity)
    refine ⟨N, fun m hm => ?_⟩
    have hm_int : Integrable (fun y => φ y *
        (Rop ((hΔum_mem m).toLp (Heat.laplacian (um m))) : Space → ℝ) y) volume :=
      hφ_conj.integrable_mul (MeasureTheory.Lp.memLp _)
    have h_int : Integrable (fun y => φ y *
        (Rop (hΔ_mem.toLp (Heat.laplacian u)) : Space → ℝ) y) volume :=
      hφ_conj.integrable_mul (MeasureTheory.Lp.memLp _)
    rw [Real.dist_eq, ← integral_sub hm_int h_int]
    let dLp := Rop ((hΔum_mem m).toLp (Heat.laplacian (um m))) -
      Rop (hΔ_mem.toLp (Heat.laplacian u))
    have hsub_eq : (fun y => φ y *
        (Rop ((hΔum_mem m).toLp (Heat.laplacian (um m))) : Space → ℝ) y -
        φ y * (Rop (hΔ_mem.toLp (Heat.laplacian u)) : Space → ℝ) y) =ᵐ[volume]
        fun y => φ y * (dLp : Space → ℝ) y := by
      filter_upwards [Lp.coeFn_sub
        (Rop ((hΔum_mem m).toLp (Heat.laplacian (um m))))
        (Rop (hΔ_mem.toLp (Heat.laplacian u)))] with y hy
      have hy' : (dLp : Space → ℝ) y =
          (Rop ((hΔum_mem m).toLp (Heat.laplacian (um m))) : Space → ℝ) y -
          (Rop (hΔ_mem.toLp (Heat.laplacian u)) : Space → ℝ) y := hy
      rw [hy']; ring
    rw [integral_congr_ae hsub_eq]
    have hm_sub : Integrable (fun y => φ y * (dLp : Space → ℝ) y) volume :=
      hφ_conj.integrable_mul (MeasureTheory.Lp.memLp dLp)
    have hh := eLpNorm_smul_le_mul_eLpNorm (p := (11 / 7 : ℝ≥0∞)) (q := (11 / 4 : ℝ≥0∞))
      (r := 1) (MeasureTheory.Lp.memLp dLp).1 hφ_conj.1
    have hn := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hφ_conj.2.ne (MeasureTheory.Lp.memLp dLp).2.ne) hh
    rw [ENNReal.toReal_mul] at hn
    have h_abs_le : |∫ y, φ y * (dLp : Space → ℝ) y| ≤
        (eLpNorm φ (11 / 7 : ℝ≥0∞) volume).toReal * ‖dLp‖ := by
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_integral_norm _).trans ?_
      have heq_lp : ∫ y, ‖φ y * (dLp : Space → ℝ) y‖ =
          (eLpNorm (fun y => φ y * (dLp : Space → ℝ) y) 1 volume).toReal := by
        rw [← ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _),
          ofReal_integral_norm_eq_lintegral_enorm hm_sub,
          ← eLpNorm_one_eq_lintegral_enorm]
      rw [heq_lp]
      simpa [Lp.norm_def, Pi.mul_def] using hn
    have hlt := hN m hm
    rw [dist_eq_norm] at hlt
    simp only [sub_zero, norm_norm] at hlt
    calc |∫ y, φ y * (dLp : Space → ℝ) y|
        ≤ (eLpNorm φ (11 / 7 : ℝ≥0∞) volume).toReal * ‖dLp‖ := h_abs_le
      _ ≤ (eLpNorm φ (11 / 7 : ℝ≥0∞) volume).toReal *
            (ε / ((eLpNorm φ (11 / 7 : ℝ≥0∞) volume).toReal + 1)) :=
          mul_le_mul_of_nonneg_left hlt.le h_bdd
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith [hε]
  have hconst_tend : Tendsto (fun _ : ℕ =>
      ∫ y : Space, φ y *
        spatialTestDerivative i
          (spatialTestDerivative k u) y)
      atTop (𝓝 (-(∫ y : Space, φ y *
        (Rop (hΔ_mem.toLp (Heat.laplacian u)) : Space → ℝ) y))) :=
    (htend_int.neg).congr' (eventually_atTop.mpr ⟨M, fun m hm => (hM_eq m hm).symm⟩)
  have heq_int : ∫ y : Space, φ y *
      spatialTestDerivative i
        (spatialTestDerivative k u) y =
      -(∫ y : Space, φ y *
        (Rop (hΔ_mem.toLp (Heat.laplacian u)) : Space → ℝ) y) :=
    tendsto_nhds_unique tendsto_const_nhds hconst_tend
  have h_int_L : Integrable (fun y : Space => φ y *
      spatialTestDerivative i (spatialTestDerivative k u) y) volume :=
    (hφ.continuous.mul h_d2_smooth.continuous).integrable_of_hasCompactSupport
      hφc.mul_right
  have h_int_R : Integrable (fun y : Space => φ y *
      (Rop (hΔ_mem.toLp (Heat.laplacian u)) : Space → ℝ) y) volume :=
    hφ_conj.integrable_mul (MeasureTheory.Lp.memLp _)
  have hfun_eq : (fun y : Space => φ y *
      (spatialTestDerivative i (spatialTestDerivative k u) y +
        (Rop (hΔ_mem.toLp (Heat.laplacian u)) : Space → ℝ) y)) =
      fun y => φ y * spatialTestDerivative i (spatialTestDerivative k u) y +
        φ y * (Rop (hΔ_mem.toLp (Heat.laplacian u)) : Space → ℝ) y := by
    funext y; ring
  simp only [smul_eq_mul, Pi.add_apply]
  rw [hfun_eq, integral_add h_int_L h_int_R, heq_int, neg_add_cancel]
  }
  filter_upwards [h_ae_zero] with y hy
  exact eq_neg_of_add_eq_zero_left hy

private lemma ae_slice_memLp_of_periodSlab
    {E : Type*} [NormedAddCommGroup E] {P : ℝ} (hP : 0 < P) {f : ℝ → Space → E}
    (hf_cont : Continuous (fun x : SpaceTime => f x.1 x.2))
    (hf_mem : MemLp (fun x : SpaceTime => f x.1 x.2) (11 / 4 : ℝ≥0∞)
      (volume.restrict (periodSlab P))) :
    ∀ᵐ τ ∂(volume.restrict (Ioc 0 P)), MemLp (f τ) (11 / 4 : ℝ≥0∞) volume := by
  have hq_ne_top : (11 / 4 : ℝ≥0∞) ≠ ⊤ := by simp [ENNReal.div_eq_top]
  have hlt : ∫⁻ x : SpaceTime in periodSlab P, ‖f x.1 x.2‖ₑ ^ (11 / 4 : ℝ≥0∞).toReal < ⊤ := by
    have h := hf_mem.2
    rwa [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) hq_ne_top] at h
  have hmeas : Measurable (fun x : SpaceTime => ‖f x.1 x.2‖ₑ ^ (11 / 4 : ℝ≥0∞).toReal) :=
    (Continuous.enorm hf_cont).measurable.pow_const _
  have hprod : ∫⁻ τ in Ioc 0 P, ∫⁻ y : Space, ‖f τ y‖ₑ ^ (11 / 4 : ℝ≥0∞).toReal < ⊤ := by
    rwa [periodSlab, Measure.volume_eq_prod, ← Measure.prod_restrict,
      Measure.restrict_univ, lintegral_prod _ hmeas.aemeasurable] at hlt
  have hmeas_τ : AEMeasurable (fun τ : ℝ => ∫⁻ y : Space, ‖f τ y‖ₑ ^ (11 / 4 : ℝ≥0∞).toReal)
      (volume.restrict (Ioc 0 P)) := hmeas.lintegral_prod_right'.aemeasurable
  filter_upwards [ae_lt_top' hmeas_τ hprod.ne] with τ hτ
  refine ⟨(hf_cont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) hq_ne_top]
  exact hτ

private lemma iteratedFDeriv_two_norm_le
    {u : Space → Space} (hu : ContDiff ℝ ∞ u) (y : Space) :
    ‖iteratedFDeriv ℝ 2 u y‖ ≤ ∑ b : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3,
      |spatialTestDerivative i (spatialTestDerivative k (fun y' => u y' b)) y| := by
  have hsum : ∀ v : Space, v = ∑ i : Fin 3, (v i) • coordinateVector i := by
    intro v; ext j
    simp [coordinateVector, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
    fin_cases j <;> simp
  have hcv_norm : ∀ b : Fin 3, ‖coordinateVector b‖ = 1 := by
    intro b; simp [coordinateVector]
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  have hm0 : m 0 = (m 0 0) • coordinateVector 0 + (m 0 1) • coordinateVector 1 +
      (m 0 2) • coordinateVector 2 := by
    simpa [Fin.sum_univ_three] using hsum (m 0)
  have hm1 : m 1 = (m 1 0) • coordinateVector 0 + (m 1 1) • coordinateVector 1 +
      (m 1 2) • coordinateVector 2 := by
    simpa [Fin.sum_univ_three] using hsum (m 1)
  have hm_eq : m = fun idx : Fin 2 => Fin.cases (m 0) (fun _ => m 1) idx := by
    ext idx j; fin_cases idx <;> rfl
  have hlin : (iteratedFDeriv ℝ 2 u y) m =
      ∑ i : Fin 3, ∑ k : Fin 3, ((m 0 i) * (m 1 k)) •
        (iteratedFDeriv ℝ 2 u y) ![coordinateVector i, coordinateVector k] := by
    have h0 : (iteratedFDeriv ℝ 2 u y) m =
        ∑ i : Fin 3, (m 0 i) • (iteratedFDeriv ℝ 2 u y)
          (Function.update m 0 (coordinateVector i)) := by
      have hm_upd : m = Function.update m 0
          ((m 0 0) • coordinateVector 0 + (m 0 1) • coordinateVector 1 +
            (m 0 2) • coordinateVector 2) := by
        ext idx j; fin_cases idx
        · simp [← hm0]
        · simp
      conv_lhs => rw [hm_upd]
      rw [ContinuousMultilinearMap.map_update_add, ContinuousMultilinearMap.map_update_add,
        ContinuousMultilinearMap.map_update_smul, ContinuousMultilinearMap.map_update_smul,
        ContinuousMultilinearMap.map_update_smul, Fin.sum_univ_three]
    rw [h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (iteratedFDeriv ℝ 2 u y) (Function.update m 0 (coordinateVector i)) =
        ∑ k : Fin 3, (m 1 k) • (iteratedFDeriv ℝ 2 u y)
          ![coordinateVector i, coordinateVector k] := by
      have hm_upd1 : Function.update m 0 (coordinateVector i) =
          Function.update (Function.update m 0 (coordinateVector i)) 1
            ((m 1 0) • coordinateVector 0 + (m 1 1) • coordinateVector 1 +
              (m 1 2) • coordinateVector 2) := by
        ext idx j; fin_cases idx
        · simp
        · simp [← hm1]
      conv_lhs => rw [hm_upd1]
      rw [ContinuousMultilinearMap.map_update_add, ContinuousMultilinearMap.map_update_add,
        ContinuousMultilinearMap.map_update_smul, ContinuousMultilinearMap.map_update_smul,
        ContinuousMultilinearMap.map_update_smul, Fin.sum_univ_three]
      have hu_eq : ∀ k : Fin 3, Function.update (Function.update m 0 (coordinateVector i)) 1
          (coordinateVector k) = ![coordinateVector i, coordinateVector k] := by
        intro k; ext idx j; fin_cases idx <;> simp
      simp only [hu_eq, add_assoc]
    rw [h1, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul]
  have hterm_eq : ∀ i k : Fin 3,
      ‖(iteratedFDeriv ℝ 2 u y) ![coordinateVector i, coordinateVector k]‖ ≤
        ∑ b : Fin 3, |spatialTestDerivative i (spatialTestDerivative k (fun y' => u y' b)) y| := by
    intro i k
    have hvec : (iteratedFDeriv ℝ 2 u y) ![coordinateVector i, coordinateVector k] =
        ∑ b : Fin 3, (((iteratedFDeriv ℝ 2 u y) ![coordinateVector i, coordinateVector k]) b) •
          coordinateVector b := hsum _
    conv_lhs => rw [hvec]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, hcv_norm b, mul_one]
    have hcoord : ((iteratedFDeriv ℝ 2 u y) ![coordinateVector i, coordinateVector k]) b =
        spatialTestDerivative i (spatialTestDerivative k (fun y' => u y' b)) y := by
      have hb_eq : (fun y' => u y' b) = (EuclideanSpace.proj b : Space →L[ℝ] ℝ) ∘ u := rfl
      have hfd1 : ∀ y' : Space,
          fderiv ℝ (fun y'' => u y'' b) y' =
            (EuclideanSpace.proj b : Space →L[ℝ] ℝ).comp (fderiv ℝ u y') := by
        intro y'
        rw [hb_eq]
        exact ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).hasFDerivAt.comp y'
          (hu.differentiable (by simp) y').hasFDerivAt).fderiv
      have hfd2 : (fun y' => spatialTestDerivative k (fun y'' => u y'' b) y') =
          fun y' => ((fderiv ℝ u y' (coordinateVector k)) b) := by
        funext y'
        simp [spatialTestDerivative, hfd1 y']
      simp only [spatialTestDerivative, hfd2]
      have hproj_fd : fderiv ℝ (fun y' => (fderiv ℝ u y' (coordinateVector k)) b) y =
          (EuclideanSpace.proj b : Space →L[ℝ] ℝ).comp
            (fderiv ℝ (fun y' => fderiv ℝ u y' (coordinateVector k)) y) := by
        have hdu : ContDiff ℝ ∞ (fun y' : Space => fderiv ℝ u y' (coordinateVector k)) :=
          (hu.fderiv_right (by simp)).clm_apply contDiff_const
        exact ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).hasFDerivAt.comp y
          (hdu.differentiable (by simp) y).hasFDerivAt).fderiv
      rw [hproj_fd]
      simp only [ContinuousLinearMap.comp_apply, iteratedFDeriv_two_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      have hsymm : (fderiv ℝ (fun y' => fderiv ℝ u y') y) (coordinateVector i) (coordinateVector k) =
          (fderiv ℝ (fun y' => fderiv ℝ u y' (coordinateVector k)) y) (coordinateVector i) := by
        have hdu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
        have hev : HasFDerivAt (fun y' => fderiv ℝ u y' (coordinateVector k))
            ((ContinuousLinearMap.apply ℝ Space (coordinateVector k)).comp
              (fderiv ℝ (fderiv ℝ u) y)) y :=
          (ContinuousLinearMap.apply ℝ Space (coordinateVector k)).hasFDerivAt.comp y
            (hdu.differentiable (by simp) y).hasFDerivAt
        rw [hev.fderiv]
        rfl
      rw [hsymm]
      rfl
    rw [hcoord]
  rw [hlin]
  have hnorm_sum : ‖∑ i : Fin 3, ∑ k : Fin 3, ((m 0 i) * (m 1 k)) •
      (iteratedFDeriv ℝ 2 u y) ![coordinateVector i, coordinateVector k]‖ ≤
      ∑ i : Fin 3, ∑ k : Fin 3, |m 0 i| * |m 1 k| *
        ‖(iteratedFDeriv ℝ 2 u y) ![coordinateVector i, coordinateVector k]‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_))
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
  refine hnorm_sum.trans ?_
  have hprod_le : ∀ i k : Fin 3,
      |m 0 i| * |m 1 k| * ‖(iteratedFDeriv ℝ 2 u y) ![coordinateVector i, coordinateVector k]‖ ≤
        (∏ idx : Fin 2, ‖m idx‖) *
          ∑ b : Fin 3, |spatialTestDerivative i (spatialTestDerivative k (fun y' => u y' b)) y| := by
    intro i k
    have hi : |m 0 i| ≤ ‖m 0‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (m 0) i
    have hk : |m 1 k| ≤ ‖m 1‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (m 1) k
    have hmk : |m 0 i| * |m 1 k| ≤ ∏ idx : Fin 2, ‖m idx‖ := by
      rw [Fin.prod_univ_two]
      exact mul_le_mul hi hk (abs_nonneg _) (norm_nonneg _)
    exact mul_le_mul hmk (hterm_eq i k) (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  calc ∑ i : Fin 3, ∑ k : Fin 3, |m 0 i| * |m 1 k| *
          ‖(iteratedFDeriv ℝ 2 u y) ![coordinateVector i, coordinateVector k]‖
      ≤ ∑ i : Fin 3, ∑ k : Fin 3, (∏ idx : Fin 2, ‖m idx‖) *
          ∑ b : Fin 3, |spatialTestDerivative i (spatialTestDerivative k (fun y' => u y' b)) y| :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hprod_le i k
    _ = (∑ b : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3,
          |spatialTestDerivative i (spatialTestDerivative k (fun y' => u y' b)) y|) *
          ∏ idx : Fin 2, ‖m idx‖ := by
        simp only [Fin.sum_univ_three]
        ring

private noncomputable def rieszHessianConst : ℝ :=
  3 * (∑ i : Fin 3, ∑ k : Fin 3,
    ‖RieszLp.rieszPairLp i k (11 / 4 : ℝ≥0∞)
      (by rw [ENNReal.lt_div_iff_mul_lt (by left; norm_num) (by right; norm_num)]; norm_num)
      (by simp [ENNReal.div_eq_top])‖) + 1

private lemma rieszHessianConst_pos : 0 < rieszHessianConst := by
  unfold rieszHessianConst
  have : 0 ≤ ∑ i : Fin 3, ∑ k : Fin 3,
      ‖RieszLp.rieszPairLp i k (11 / 4 : ℝ≥0∞)
        (by rw [ENNReal.lt_div_iff_mul_lt (by left; norm_num) (by right; norm_num)]; norm_num)
        (by simp [ENNReal.div_eq_top])‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  linarith

private lemma eLpNorm_fin3_le {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Fin 3 → Space → ℝ)
    (hf : ∀ i, AEStronglyMeasurable (f i) volume) :
    eLpNorm (fun y : Space => ∑ i : Fin 3, f i y) q volume ≤
      ∑ i : Fin 3, eLpNorm (f i) q volume := by
  simp only [Fin.sum_univ_three]
  exact (eLpNorm_add_le ((hf 0).add (hf 1)) (hf 2) hq).trans
    (add_le_add (eLpNorm_add_le (hf 0) (hf 1) hq) le_rfl)

private lemma eLpNorm_sum3_le {q : ℝ≥0∞} (hq : 1 ≤ q)
    (F : Fin 3 → Fin 3 → Fin 3 → Space → ℝ)
    (hF : ∀ b i k, AEStronglyMeasurable (F b i k) volume) :
    eLpNorm (fun y : Space => ∑ b : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3, F b i k y) q volume ≤
      ∑ b : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3, eLpNorm (F b i k) q volume := by
  have hF2 : ∀ b i, AEStronglyMeasurable (fun y => ∑ k : Fin 3, F b i k y) volume := by
    intro b i
    simp only [Fin.sum_univ_three]
    exact ((hF b i 0).add (hF b i 1)).add (hF b i 2)
  have hF1 : ∀ b, AEStronglyMeasurable (fun y => ∑ i : Fin 3, ∑ k : Fin 3, F b i k y) volume := by
    intro b
    rw [show (fun y => ∑ i : Fin 3, ∑ k : Fin 3, F b i k y) =
        (fun y => ∑ k : Fin 3, F b 0 k y) + (fun y => ∑ k : Fin 3, F b 1 k y) +
          (fun y => ∑ k : Fin 3, F b 2 k y) by
      funext y; simp only [Fin.sum_univ_three, Pi.add_apply]]
    exact ((hF2 b 0).add (hF2 b 1)).add (hF2 b 2)
  refine (eLpNorm_fin3_le hq (fun b y => ∑ i : Fin 3, ∑ k : Fin 3, F b i k y) hF1).trans
    (Finset.sum_le_sum fun b _ => ?_)
  refine (eLpNorm_fin3_le hq (fun i y => ∑ k : Fin 3, F b i k y) (hF2 b)).trans
    (Finset.sum_le_sum fun i _ => ?_)
  exact eLpNorm_fin3_le hq (F b i) (hF b i)

private lemma corr_hessian_slab_aux
    {p : Params} (hP1 : p.period ≤ 1) (z : p.Z)
    (hcorr : ContDiff ℝ ∞ (fun x : SpaceTime => p.corr z x.1 x.2))
    (hfd_slab : MemLp (fun x : SpaceTime => iteratedFDeriv ℝ 1 (p.corr z x.1) x.2)
      (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period)))
    (hΔ_slab : MemLp (fun x : SpaceTime => vecLaplacian (p.corr z x.1) x.2)
      (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period)))
    (hΔ_eb : (eLpNorm (fun x : SpaceTime => vecLaplacian (p.corr z x.1) x.2)
        (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period))).toReal ≤
      p.period ^ ((4 : ℝ) / 11) * (p.ν⁻¹ * ‖z‖)) :
    MemLp (fun x : SpaceTime => iteratedFDeriv ℝ 2 (p.corr z x.1) x.2) (11 / 4 : ℝ≥0∞)
        (volume.restrict (periodSlab p.period)) ∧
      (eLpNorm (fun x : SpaceTime => iteratedFDeriv ℝ 2 (p.corr z x.1) x.2) (11 / 4 : ℝ≥0∞)
        (volume.restrict (periodSlab p.period))).toReal ≤
        p.period ^ ((4 : ℝ) / 11) * (rieszHessianConst * p.ν⁻¹ * ‖z‖) := by
  have hP0 : 0 < p.period := p.period_pos
  have : Fact (0 < p.period) := ⟨hP0⟩
  have hq_gt1 : (1 : ℝ≥0∞) < 11 / 4 := by
    rw [ENNReal.lt_div_iff_mul_lt (by left; norm_num) (by right; norm_num)]; norm_num
  have hq_ne_top : (11 / 4 : ℝ≥0∞) ≠ ⊤ := by simp [ENNReal.div_eq_top]
  have hq_ge1 : (1 : ℝ≥0∞) ≤ 11 / 4 := hq_gt1.le
  have : Fact ((1 : ℝ≥0∞) ≤ 11 / 4) := ⟨hq_ge1⟩
  have hu_slab : MemLp (fun x : SpaceTime => p.corr z x.1 x.2)
      (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period)) := by
    obtain ⟨hm_rep, _⟩ := memLp_rep_periodSlab (p.wOf z)
    have hF_rep : Cons.C03.Concrete.IsContRep (p.wOf z) (p.corr z) := by
      let u := B0412.XToD (p.graphX z)
      have : Fact (1 ≤ ENNReal.ofReal B0281.q0) := inferInstanceAs (Fact (1 ≤ B0412.q0E))
      let F := B0449.globalRealChartRep hP1 IIb.S1Sub.s1_q0_holder IIb.S1Sub.s1_q0_gt p.ν_pos
        (B0411.hasPhaseOp_T0D u) (B0411.hasPhaseOp_nuLapD u)
      have hF : Cons.C03.Concrete.IsContRep (p.wOf z) F :=
        Cons.C03.Concrete.graph_globalRealChartRep_isContRep hP1 IIb.S1Sub.s1_q0_holder
          IIb.S1Sub.s1_q0_gt p.ν_pos (B0411.hasPhaseOp_T0D u) (B0411.hasPhaseOp_nuLapD u)
      exact Cons.C03.Concrete.contRep_spec ⟨F, hF⟩
    have hreP : Continuous Cons.C03.Concrete.reP :=
      (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp
        (continuous_pi fun i => Complex.continuous_re.comp
          ((EuclideanSpace.proj i : PhaseSpace.CVec3 →L[ℂ] ℂ).continuous))
    have hm_re : MemLp (fun x : SpaceTime => Cons.C03.Concrete.reP
        (Cons.C03.Concrete.rep (p.wOf z) x.1 x.2)) (11 / 4 : ℝ≥0∞)
        (volume.restrict (periodSlab p.period)) := by
      refine ⟨(hreP.measurable.comp
        (Cons.C03.Concrete.stronglyMeasurable_rep (p.wOf z)).measurable).aestronglyMeasurable.restrict, ?_⟩
      exact lt_of_le_of_lt (eLpNorm_mono fun x => IIb.S1Sub.norm_realPartVector_le _) hm_rep.2
    exact hm_re.ae_eq (ae_restrict_of_ae hF_rep.2.symm)
  have hgrad_cont : Continuous (fun x : SpaceTime => fderiv ℝ (p.corr z x.1) x.2) := by
    have heq : (fun x : SpaceTime => fderiv ℝ (p.corr z x.1) x.2) =
        fun x : SpaceTime => continuousMultilinearCurryFin1 ℝ Space Space
          (iteratedFDeriv ℝ 1 (p.corr z x.1) x.2) := by
      funext x; ext v; simp
    rw [heq]
    exact (continuousMultilinearCurryFin1 ℝ Space Space).continuous.comp
      (continuous_spatial_iteratedFDeriv_of_contDiff hcorr 1)
  have hgrad_slab : MemLp (fun x : SpaceTime => fderiv ℝ (p.corr z x.1) x.2)
      (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period)) := by
    refine ⟨hgrad_cont.aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt (eLpNorm_mono fun x => by
      rw [← norm_iteratedFDeriv_one]) hfd_slab.2
  have hcorr_lap_cont : Continuous (fun x : SpaceTime => vecLaplacian (p.corr z x.1) x.2) := by
    refine (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp (continuous_pi fun b => ?_)
    refine continuous_finsetSum _ fun i _ => ?_
    have h1 : ContDiff ℝ ∞ (fun x : SpaceTime =>
        fderiv ℝ (fun y' => p.corr z x.1 y' b) x.2 (coordinateVector i)) := by
      have heq : (fun x : SpaceTime =>
          fderiv ℝ (fun y' => p.corr z x.1 y' b) x.2 (coordinateVector i)) =
          fun x : SpaceTime => (fderiv ℝ (fun p0 : SpaceTime => p.corr z p0.1 p0.2 b) x)
            (0, coordinateVector i) := by
        funext x
        have hb : ContDiff ℝ ∞ (fun p0 : SpaceTime => p.corr z p0.1 p0.2 b) :=
          (EuclideanSpace.proj b : Space →L[ℝ] ℝ).contDiff.comp hcorr
        have haff : HasFDerivAt (fun y' : Space => (x.1, y'))
            (ContinuousLinearMap.inr ℝ ℝ Space) x.2 :=
          (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2)
        have hdx : HasFDerivAt (fun p0 : SpaceTime => p.corr z p0.1 p0.2 b)
            (fderiv ℝ (fun p0 : SpaceTime => p.corr z p0.1 p0.2 b) x) (x.1, x.2) :=
          (hb.differentiable (n := ∞) (by simp) x).hasFDerivAt
        have hd : HasFDerivAt (fun y' => p.corr z x.1 y' b)
            ((fderiv ℝ (fun p0 : SpaceTime => p.corr z p0.1 p0.2 b) x).comp
              (ContinuousLinearMap.inr ℝ ℝ Space)) x.2 :=
          hdx.comp x.2 haff
        rw [hd.fderiv]
        rfl
      rw [heq]
      have hb : ContDiff ℝ ∞ (fun p0 : SpaceTime => p.corr z p0.1 p0.2 b) :=
        (EuclideanSpace.proj b : Space →L[ℝ] ℝ).contDiff.comp hcorr
      exact (hb.fderiv_right (by simp)).clm_apply contDiff_const
    have h2 : ContDiff ℝ ∞ (fun x : SpaceTime =>
        (fderiv ℝ (fun x' : SpaceTime =>
          fderiv ℝ (fun y' => p.corr z x'.1 y' b) x'.2 (coordinateVector i)) x)
          (0, coordinateVector i)) :=
      (h1.fderiv_right (by simp)).clm_apply contDiff_const
    have heq2 : (fun x : SpaceTime =>
        fderiv ℝ (fun y' => fderiv ℝ (fun y'' => p.corr z x.1 y'' b) y' (coordinateVector i))
          x.2 (coordinateVector i)) =
        fun x : SpaceTime =>
          (fderiv ℝ (fun x' : SpaceTime =>
            fderiv ℝ (fun y' => p.corr z x'.1 y' b) x'.2 (coordinateVector i)) x)
            (0, coordinateVector i) := by
      funext x
      have haff : HasFDerivAt (fun y' : Space => (x.1, y'))
          (ContinuousLinearMap.inr ℝ ℝ Space) x.2 :=
        (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2)
      rw [show (fun y' => fderiv ℝ (fun y'' => p.corr z x.1 y'' b) y' (coordinateVector i)) =
          (fun x' : SpaceTime => fderiv ℝ (fun y' => p.corr z x'.1 y' b) x'.2 (coordinateVector i)) ∘
            (fun y' => (x.1, y')) from rfl,
        ((h1.differentiable (by simp) x).hasFDerivAt.comp x.2 haff).fderiv]
      rfl
    rw [heq2]
    exact h2.continuous
  have hu_slice := ae_slice_memLp_of_periodSlab (f := fun τ y => p.corr z τ y) hP0 hcorr.continuous hu_slab
  have hgrad_slice := ae_slice_memLp_of_periodSlab (f := fun τ y => fderiv ℝ (p.corr z τ) y) hP0 hgrad_cont hgrad_slab
  have hΔ_slice := ae_slice_memLp_of_periodSlab (f := fun τ y => vecLaplacian (p.corr z τ) y) hP0 hcorr_lap_cont hΔ_slab
  have hslice_bound : ∀ᵐ τ ∂(volume.restrict (Ioc 0 p.period)),
      eLpNorm (fun y : Space => iteratedFDeriv ℝ 2 (p.corr z τ) y) (11 / 4 : ℝ≥0∞) volume ≤
        ENNReal.ofReal rieszHessianConst *
          eLpNorm (fun y : Space => vecLaplacian (p.corr z τ) y) (11 / 4 : ℝ≥0∞) volume := by
    filter_upwards [hu_slice, hgrad_slice, hΔ_slice] with τ hτ_u hτ_grad hτ_Δ
    have hτ_smooth : ContDiff ℝ ∞ (p.corr z τ) := hcorr.comp (contDiff_const.prodMk contDiff_id)
    have hcoord_bound : ∀ (b i k : Fin 3),
        eLpNorm (spatialTestDerivative i (spatialTestDerivative k (fun y => p.corr z τ y b)))
          (11 / 4 : ℝ≥0∞) volume ≤
          ENNReal.ofReal ‖RieszLp.rieszPairLp i k (11 / 4 : ℝ≥0∞) hq_gt1 hq_ne_top‖ *
            eLpNorm (fun y => vecLaplacian (p.corr z τ) y) (11 / 4 : ℝ≥0∞) volume := by
      intro b i k
      have hb_smooth : ContDiff ℝ ∞ (fun y => p.corr z τ y b) :=
        (EuclideanSpace.proj b : Space →L[ℝ] ℝ).contDiff.comp hτ_smooth
      have hb_u : MemLp (fun y => p.corr z τ y b) (11 / 4 : ℝ≥0∞) volume := by
        refine ⟨((EuclideanSpace.proj b : Space →L[ℝ] ℝ).continuous.comp
          hτ_smooth.continuous).aestronglyMeasurable, ?_⟩
        exact lt_of_le_of_lt (eLpNorm_mono fun y => PiLp.norm_apply_le _ b) hτ_u.2
      have hb_grad : MemLp (fun y => fderiv ℝ (fun y' => p.corr z τ y' b) y)
          (11 / 4 : ℝ≥0∞) volume := by
        refine ⟨(hb_smooth.continuous_fderiv (by simp)).aestronglyMeasurable, ?_⟩
        refine lt_of_le_of_lt (eLpNorm_mono fun y => ?_) hτ_grad.2
        have hfd : fderiv ℝ (fun y' => p.corr z τ y' b) y =
            (EuclideanSpace.proj b : Space →L[ℝ] ℝ).comp (fderiv ℝ (p.corr z τ) y) :=
          ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).hasFDerivAt.comp y
            (hτ_smooth.differentiable (by simp) y).hasFDerivAt).fderiv
        rw [hfd]
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_of_le_one_left (norm_nonneg _)
            (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
              simpa [one_mul] using PiLp.norm_apply_le v b))
      have hb_Δ : MemLp (Heat.laplacian (fun y' => p.corr z τ y' b)) (11 / 4 : ℝ≥0∞) volume := by
        refine ⟨(continuous_laplacian_of_contDiff hb_smooth).aestronglyMeasurable, ?_⟩
        exact lt_of_le_of_lt (eLpNorm_mono fun y => by
          simpa [vecLaplacian_apply] using PiLp.norm_apply_le (vecLaplacian (p.corr z τ) y) b) hτ_Δ.2
      have h_ae := riesz_hessian_slice_aux hb_smooth hb_u hb_grad hb_Δ i k
      rw [eLpNorm_congr_ae h_ae, eLpNorm_neg]
      have h_op := ContinuousLinearMap.le_opNorm
        (RieszLp.rieszPairLp i k (11 / 4 : ℝ≥0∞) hq_gt1 hq_ne_top)
        (hb_Δ.toLp (Heat.laplacian (fun y' => p.corr z τ y' b)))
      have h_eLp_le : eLpNorm (RieszLp.rieszPairLp i k (11 / 4 : ℝ≥0∞) hq_gt1 hq_ne_top
          (hb_Δ.toLp (Heat.laplacian (fun y' => p.corr z τ y' b))) : Space → ℝ)
          (11 / 4 : ℝ≥0∞) volume ≤
          ENNReal.ofReal ‖RieszLp.rieszPairLp i k (11 / 4 : ℝ≥0∞) hq_gt1 hq_ne_top‖ *
            eLpNorm (Heat.laplacian (fun y' => p.corr z τ y' b)) (11 / 4 : ℝ≥0∞) volume := by
        rw [← ENNReal.ofReal_toReal (MeasureTheory.Lp.memLp _).2.ne,
          ← ENNReal.ofReal_toReal hb_Δ.2.ne,
          ← ENNReal.ofReal_mul (norm_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        simpa [Lp.norm_def, eLpNorm_congr_ae hb_Δ.coeFn_toLp] using h_op
      refine h_eLp_le.trans (mul_le_mul_of_nonneg_left (eLpNorm_mono fun y => ?_) (by positivity))
      simpa [vecLaplacian_apply] using PiLp.norm_apply_le (vecLaplacian (p.corr z τ) y) b
    have hsm_d2 : ∀ (b i k : Fin 3), AEStronglyMeasurable
        (spatialTestDerivative i (spatialTestDerivative k (fun y => p.corr z τ y b))) volume := by
      intro b i k
      have hb_smooth : ContDiff ℝ ∞ (fun y => p.corr z τ y b) :=
        (EuclideanSpace.proj b : Space →L[ℝ] ℝ).contDiff.comp hτ_smooth
      have h1 : ContDiff ℝ ∞ (spatialTestDerivative k (fun y => p.corr z τ y b)) :=
        (hb_smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      exact ((h1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous.aestronglyMeasurable
    have h_eLp_sum : eLpNorm (fun y : Space => iteratedFDeriv ℝ 2 (p.corr z τ) y)
        (11 / 4 : ℝ≥0∞) volume ≤
        ∑ b : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3,
          eLpNorm (spatialTestDerivative i (spatialTestDerivative k (fun y => p.corr z τ y b)))
            (11 / 4 : ℝ≥0∞) volume := by
      let F : Fin 3 → Fin 3 → Fin 3 → Space → ℝ := fun b i k y =>
        |spatialTestDerivative i (spatialTestDerivative k (fun y' => p.corr z τ y' b)) y|
      have hF_asm : ∀ b i k, AEStronglyMeasurable (F b i k) volume :=
        fun b i k => (hsm_d2 b i k).norm
      have hle1 : eLpNorm (fun y : Space => iteratedFDeriv ℝ 2 (p.corr z τ) y)
          (11 / 4 : ℝ≥0∞) volume ≤
          eLpNorm (fun y : Space => ∑ b : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3, F b i k y)
            (11 / 4 : ℝ≥0∞) volume := by
        refine eLpNorm_mono fun y => ?_
        exact (iteratedFDeriv_two_norm_le hτ_smooth y).trans (le_abs_self _) |>.trans_eq
          (Real.norm_eq_abs _).symm
      refine hle1.trans ?_
      refine (eLpNorm_sum3_le hq_ge1 F hF_asm).trans ?_
      refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun k _ => ?_
      exact eLpNorm_mono fun y => by simp [F]
    refine h_eLp_sum.trans ?_
    calc ∑ b : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3,
            eLpNorm (spatialTestDerivative i (spatialTestDerivative k (fun y => p.corr z τ y b)))
              (11 / 4 : ℝ≥0∞) volume
        ≤ ∑ _b : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3,
            ENNReal.ofReal ‖RieszLp.rieszPairLp i k (11 / 4 : ℝ≥0∞) hq_gt1 hq_ne_top‖ *
              eLpNorm (fun y => vecLaplacian (p.corr z τ) y) (11 / 4 : ℝ≥0∞) volume :=
          Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ =>
            hcoord_bound b i k
      _ = ENNReal.ofReal (3 * ∑ i : Fin 3, ∑ k : Fin 3,
            ‖RieszLp.rieszPairLp i k (11 / 4 : ℝ≥0∞) hq_gt1 hq_ne_top‖) *
            eLpNorm (fun y => vecLaplacian (p.corr z τ) y) (11 / 4 : ℝ≥0∞) volume := by
          simp_rw [← Finset.sum_mul, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
          simp_rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
          rw [ENNReal.ofReal_mul (by positivity),
            show (↑(3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num,
            ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)]
      _ ≤ ENNReal.ofReal rieszHessianConst *
            eLpNorm (fun y => vecLaplacian (p.corr z τ) y) (11 / 4 : ℝ≥0∞) volume := by
          refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
          unfold rieszHessianConst; linarith
  have hcont_d2 : Continuous (fun x : SpaceTime => iteratedFDeriv ℝ 2 (p.corr z x.1) x.2) :=
    continuous_spatial_iteratedFDeriv_of_contDiff hcorr 2
  have hmeas_d2 : Measurable (fun x : SpaceTime =>
      ‖iteratedFDeriv ℝ 2 (p.corr z x.1) x.2‖ₑ ^ ((11 : ℝ) / 4)) :=
    (Continuous.enorm hcont_d2).measurable.pow_const _
  have hmeas_Δ : Measurable (fun x : SpaceTime =>
      ‖vecLaplacian (p.corr z x.1) x.2‖ₑ ^ ((11 : ℝ) / 4)) :=
    (Continuous.enorm hcorr_lap_cont).measurable.pow_const _
  have hlint_d2_le : ∫⁻ x : SpaceTime in periodSlab p.period,
      ‖iteratedFDeriv ℝ 2 (p.corr z x.1) x.2‖ₑ ^ ((11 : ℝ) / 4) ≤
      (ENNReal.ofReal rieszHessianConst) ^ ((11 : ℝ) / 4) *
        ∫⁻ x : SpaceTime in periodSlab p.period,
          ‖vecLaplacian (p.corr z x.1) x.2‖ₑ ^ ((11 : ℝ) / 4) := by
    rw [periodSlab, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
      lintegral_prod _ hmeas_d2.aemeasurable, lintegral_prod _ hmeas_Δ.aemeasurable,
      ← lintegral_const_mul _ (hmeas_Δ.lintegral_prod_right')]
    refine lintegral_mono_ae ?_
    filter_upwards [hslice_bound] with τ hτ
    have hτ_rpow : (eLpNorm (fun y : Space => iteratedFDeriv ℝ 2 (p.corr z τ) y)
        (11 / 4 : ℝ≥0∞) volume) ^ ((11 : ℝ) / 4) ≤
        (ENNReal.ofReal rieszHessianConst *
          eLpNorm (fun y : Space => vecLaplacian (p.corr z τ) y) (11 / 4 : ℝ≥0∞) volume) ^
            ((11 : ℝ) / 4) :=
      ENNReal.rpow_le_rpow hτ (by norm_num)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at hτ_rpow
    have heLp_lhs : (eLpNorm (fun y : Space => iteratedFDeriv ℝ 2 (p.corr z τ) y)
        (11 / 4 : ℝ≥0∞) volume) ^ ((11 : ℝ) / 4) =
        ∫⁻ y : Space, ‖iteratedFDeriv ℝ 2 (p.corr z τ) y‖ₑ ^ ((11 : ℝ) / 4) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) hq_ne_top]
      have htoReal : (11 / 4 : ℝ≥0∞).toReal = (11 : ℝ) / 4 := by
        rw [ENNReal.toReal_div]; norm_num
      rw [htoReal, ← ENNReal.rpow_mul]
      norm_num
    have heLp_rhs : (eLpNorm (fun y : Space => vecLaplacian (p.corr z τ) y)
        (11 / 4 : ℝ≥0∞) volume) ^ ((11 : ℝ) / 4) =
        ∫⁻ y : Space, ‖vecLaplacian (p.corr z τ) y‖ₑ ^ ((11 : ℝ) / 4) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) hq_ne_top]
      have htoReal : (11 / 4 : ℝ≥0∞).toReal = (11 : ℝ) / 4 := by
        rw [ENNReal.toReal_div]; norm_num
      rw [htoReal, ← ENNReal.rpow_mul]
      norm_num
    rwa [heLp_lhs, heLp_rhs] at hτ_rpow
  have heLp_d2_le : eLpNorm (fun x : SpaceTime => iteratedFDeriv ℝ 2 (p.corr z x.1) x.2)
      (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period)) ≤
      ENNReal.ofReal rieszHessianConst *
        eLpNorm (fun x : SpaceTime => vecLaplacian (p.corr z x.1) x.2)
          (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period)) := by
    have htoReal : (11 / 4 : ℝ≥0∞).toReal = (11 : ℝ) / 4 := by
      rw [ENNReal.toReal_div]; norm_num
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) hq_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) hq_ne_top, htoReal]
    have h1 := ENNReal.rpow_le_rpow hlint_d2_le (by norm_num : (0 : ℝ) ≤ 4 / 11)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul] at h1
    simpa [one_mul] using h1
  have hmem_d2 : MemLp (fun x : SpaceTime => iteratedFDeriv ℝ 2 (p.corr z x.1) x.2)
      (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period)) := by
    refine ⟨hcont_d2.aestronglyMeasurable.restrict, ?_⟩
    exact lt_of_le_of_lt heLp_d2_le
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hΔ_slab.2)
  refine ⟨hmem_d2, ?_⟩
  have htoReal_le : (eLpNorm (fun x : SpaceTime => iteratedFDeriv ℝ 2 (p.corr z x.1) x.2)
      (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period))).toReal ≤
      rieszHessianConst *
        (eLpNorm (fun x : SpaceTime => vecLaplacian (p.corr z x.1) x.2)
          (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period))).toReal := by
    have hfin := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := rieszHessianConst)) hΔ_slab.2.ne
    have h_tr := ENNReal.toReal_mono hfin heLp_d2_le
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal rieszHessianConst_pos.le] at h_tr
  calc (eLpNorm (fun x : SpaceTime => iteratedFDeriv ℝ 2 (p.corr z x.1) x.2)
          (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period))).toReal
      ≤ rieszHessianConst *
          (eLpNorm (fun x : SpaceTime => vecLaplacian (p.corr z x.1) x.2)
            (11 / 4 : ℝ≥0∞) (volume.restrict (periodSlab p.period))).toReal := htoReal_le
    _ ≤ rieszHessianConst * (p.period ^ ((4 : ℝ) / 11) * (p.ν⁻¹ * ‖z‖)) :=
          mul_le_mul_of_nonneg_left hΔ_eb rieszHessianConst_pos.le
    _ = p.period ^ ((4 : ℝ) / 11) * (rieszHessianConst * p.ν⁻¹ * ‖z‖) := by ring

theorem ballRepairRegularity : UnforcedLeray.Short.Spine.SPPII.BallRepairRegularity := by
  intro Sig lam q hSig hlam m hm dm dp hdm hm_bd C₁ k₁ hC₁
  obtain ⟨C_sr, k_sr, ν_sr, hC_sr, hν_sr, hSR⟩ :=
    IIb.strongRegularity_proof Sig lam q hSig hlam m hm dm dp hdm hm_bd C₁ k₁ hC₁
  let h4 := IIb.affineInletFacts_proof
  let hQ1 := IIb.quadBound_of h4
  obtain ⟨C_de, k_de, ν_de, hC_de, hν_de, hDE⟩ :=
    IIb.differentiatedEquationGraphBound_of h4 hQ1 Sig lam q hSig hlam m hm dm dp hdm hm_bd C₁ k₁ hC₁
  obtain ⟨ν_per, hν_per, hPer⟩ := IIb.window_period_le_one_exists hdm
  obtain ⟨ν_raw, hν_raw, hRaw⟩ := IIb.rawJointSmooth Sig lam q hSig hlam dm dp hdm
  refine ⟨max (3 * C_de) (rieszHessianConst * C₁), max k_de (k₁ + 1),
    min ν_sr (min ν_de (min ν_per (min ν_raw 1))),
    lt_of_lt_of_le (by positivity) (le_max_left _ _),
    lt_min hν_sr (lt_min hν_de (lt_min hν_per (lt_min hν_raw one_pos))), ?_⟩
  intro p d hreg hν hage hmode z heq hz
  have hP1 : p.period ≤ 1 := hPer p d hreg (hν.trans (min_le_right _ _ |>.trans (min_le_right _ _) |>.trans (min_le_left _ _)))
  have hν_raw_le : p.ν ≤ ν_raw := hν.trans (min_le_right _ _ |>.trans (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans (min_le_left _ _))
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _ |>.trans (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans (min_le_right _ _))
  have hν_pos : 0 < p.ν := p.ν_pos
  have hε_nn : 0 ≤ p.ε := p.ε_pos.le
  have hSR_z := hSR p d hreg (hν.trans (min_le_left _ _)) hage hmode z heq hz
  have hcorr : ContDiff ℝ ∞ (fun x : SpaceTime => p.corr z x.1 x.2) :=
    corr_joint_smooth_aux lam q hlam hreg hν1 hmode z hSR_z.1 (hRaw p d hreg hν_raw_le hage hmode 0)
  refine ⟨hcorr, ?_⟩
  intro j hj1 hj2
  have hj_cases : j = 1 ∨ j = 2 := by omega
  rcases hj_cases with rfl | rfl
  · obtain ⟨g, hg_op, hg_bd⟩ :=
      hDE p d hreg (hν.trans (min_le_right _ _ |>.trans (min_le_left _ _))) hage hmode z heq hz
    have hB_nn : 0 ≤ C_de * (p.ν ^ k_de)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) := by
      positivity
    obtain ⟨hmem1, heb1⟩ := corr_fderiv_slab_aux hP1 z hcorr g hg_op hB_nn hg_bd
    refine ⟨hmem1, heb1.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg p.period_pos.le _))⟩
    have hpow : (p.ν ^ k_de)⁻¹ ≤ (p.ν ^ max k_de (k₁ + 1))⁻¹ :=
      inv_anti₀ (pow_pos hν_pos _) (pow_le_pow_of_le_one hν_pos.le hν1 (le_max_left _ _))
    have hexp_nn : 0 ≤ Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) := by positivity
    calc 3 * (C_de * (p.ν ^ k_de)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ))
        = (3 * C_de) * (p.ν ^ k_de)⁻¹ * (Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) := by ring
      _ ≤ max (3 * C_de) (rieszHessianConst * C₁) * (p.ν ^ max k_de (k₁ + 1))⁻¹ *
            (Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (le_max_left _ _) hpow (inv_nonneg.2 (pow_pos hν_pos _).le) (by positivity))
            hexp_nn
      _ = max (3 * C_de) (rieszHessianConst * C₁) * (p.ν ^ max k_de (k₁ + 1))⁻¹ *
            Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) := by ring
  · obtain ⟨g, hg_op, hg_bd⟩ :=
      hDE p d hreg (hν.trans (min_le_right _ _ |>.trans (min_le_left _ _))) hage hmode z heq hz
    have hB_nn : 0 ≤ C_de * (p.ν ^ k_de)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) := by
      positivity
    obtain ⟨hmem1, _⟩ := corr_fderiv_slab_aux hP1 z hcorr g hg_op hB_nn hg_bd
    obtain ⟨hmemΔ, hebΔ⟩ := laplacian_corr_slab_aux hP1 z hcorr
    obtain ⟨hmem2, heb2⟩ := corr_hessian_slab_aux hP1 z hcorr hmem1 hmemΔ hebΔ
    refine ⟨hmem2, heb2.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg p.period_pos.le _))⟩
    have hpow : (p.ν ^ (k₁ + 1))⁻¹ ≤ (p.ν ^ max k_de (k₁ + 1))⁻¹ :=
      inv_anti₀ (pow_pos hν_pos _) (pow_le_pow_of_le_one hν_pos.le hν1 (le_max_right _ _))
    have hexp_nn : 0 ≤ Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) := by positivity
    calc rieszHessianConst * p.ν⁻¹ * ‖z‖
        ≤ rieszHessianConst * p.ν⁻¹ *
            (C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) :=
          mul_le_mul_of_nonneg_left hz (mul_nonneg rieszHessianConst_pos.le (inv_nonneg.2 hν_pos.le))
      _ = (rieszHessianConst * C₁) * (p.ν ^ (k₁ + 1))⁻¹ *
            (Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) := by
          rw [pow_succ, mul_inv]; ring
      _ ≤ max (3 * C_de) (rieszHessianConst * C₁) * (p.ν ^ max k_de (k₁ + 1))⁻¹ *
            (Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (le_max_right _ _) hpow (inv_nonneg.2 (pow_pos hν_pos _).le) (by positivity))
            hexp_nn
      _ = max (3 * C_de) (rieszHessianConst * C₁) * (p.ν ^ max k_de (k₁ + 1))⁻¹ *
            Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) := by ring

end UnforcedLeray.Short.Spine.SPPII
