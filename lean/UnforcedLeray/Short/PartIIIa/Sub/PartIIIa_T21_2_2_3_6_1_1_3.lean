import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6_1_1_3.BandInt0
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6_1_1_3.AdjFubini0
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_6_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6_1_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.DivPointwiseParts.RegSmooth
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.DivPointwiseParts.RegDeriv
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.DivPointwiseParts.LatticeNull
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.CurlPointwiseParts.GradIBP

/-!
# `KerVelCurl0` from the Laplacian leaves of the regularised stream function

Source: `the November 2 reference manuscript` lines 2081-2084, 3052-3057, 3121.
The `d ≥ 1` chain `kerVelCurl_of` / `kerCurlPointwise_of_parts` / `kerApproxId_of` carries over
verbatim to every `d > 0` (constants may depend on `d`): near/far bound `kerNearFar0`,
`KerBandInt0`, `KerAdjFubini0` (sibling files), and the assembly below.  The remaining inputs are
the four analytic leaves `KerLapFormula`, `KerLapInt`, `KerLapMass`, `KerLapFar`, already stated
for `0 < d`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

def KerApproxId0 : Prop :=
  ∀ d : ℝ, 0 < d → ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest d φ → ∀ y : ℝ × ℝ,
    Tendsto (fun ε : ℝ => ∫ x in B0579.cell d,
      (B0579.pd 0 (B0579.pd 0 (fun x : ℝ × ℝ => kerReg d ε (x - y))) x +
        B0579.pd 1 (B0579.pd 1 (fun x : ℝ × ℝ => kerReg d ε (x - y))) x) * φ x)
      (𝓝[>] 0) (𝓝 (φ y))

def KerCurlPointwise0 : Prop :=
  ∀ d : ℝ, 0 < d → ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest d φ → ∀ y : ℝ × ℝ,
    ∫ x in B0579.cell d,
      (kerD d (x - y) 0 * B0579.pd 1 φ x - kerD d (x - y) 1 * B0579.pd 0 φ x) = φ y

theorem kerApproxId0_of (hF : KerLapFormula) (hI : KerLapInt) (hM : KerLapMass)
    (hFar : KerLapFar) : KerApproxId0 := by
  intro d hd0 φ hφ y
  obtain ⟨M, hM0, hMb⟩ := UnforcedLeray.Short.IIIa.Exist.cylTest_exists_bound hd0 hφ
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro e he
  -- continuity at y
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.1 (hφ.continuous.continuousAt (x := y))
    (e / 2) (by linarith)
  obtain ⟨C, hC⟩ := hFar d δ hd0 hδ
  set K : ℝ := 2 * M * |C| + 1 with hK
  have hKpos : 0 < K := by positivity
  refine ⟨min 1 (e / (2 * K)), lt_min one_pos (by positivity), fun ε hε hεd => ?_⟩
  have hε0 : 0 < ε := hε
  have hh : |ε| < 1 ∧ |ε| < e / (2 * K) := by simpa [Real.dist_eq, lt_min_iff] using hεd
  have hε1 : ε < 1 := lt_of_le_of_lt (le_abs_self ε) hh.1
  have hε2 : ε < e / (2 * K) := lt_of_le_of_lt (le_abs_self ε) hh.2
  rw [pairing_eq hF d hd0 φ hφ y ε hε0]
  have hLi := hI d ε hd0 hε0
  have hLnn := lapForm_nonneg d ε hd0 hε0
  have hmass := hM d ε hd0 hε0
  set far : Set (ℝ × ℝ) := {x | δ ≤ ‖x‖} with hfar
  have hfarm : MeasurableSet far := (isClosed_le continuous_const continuous_norm).measurableSet
  have hφc : Continuous fun z : ℝ × ℝ => φ (z + y) :=
    hφ.continuous.comp (continuous_id.add continuous_const)
  have hFi : IntegrableOn (fun z : ℝ × ℝ => lapForm d ε z * φ (z + y)) (B0579.cell d) :=
    hLi.mul_bdd hφc.aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hMb (z + y))
  have hGi : IntegrableOn (fun z : ℝ × ℝ => lapForm d ε z * φ y) (B0579.cell d) := hLi.mul_const _
  have hdiff : (∫ z in B0579.cell d, lapForm d ε z * φ (z + y)) - φ y =
      ∫ z in B0579.cell d, lapForm d ε z * (φ (z + y) - φ y) := by
    have : ∫ z in B0579.cell d, lapForm d ε z * (φ (z + y) - φ y) =
        (∫ z in B0579.cell d, lapForm d ε z * φ (z + y)) -
          ∫ z in B0579.cell d, lapForm d ε z * φ y := by
      rw [← integral_sub hFi hGi]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [mul_sub]
    rw [this, integral_mul_const, hmass, one_mul]
  have hfari : IntegrableOn (lapForm d ε) (B0579.cell d ∩ far) := hLi.mono_set inter_subset_left
  have hLr : Integrable (lapForm d ε) ((volume.restrict (B0579.cell d)).restrict far) :=
    Integrable.restrict (show Integrable (lapForm d ε) (volume.restrict (B0579.cell d)) from hLi)
  have hg_int : Integrable (fun z : ℝ × ℝ => lapForm d ε z * (e / 2) +
      far.indicator (fun z => 2 * M * lapForm d ε z) z) (volume.restrict (B0579.cell d)) := by
    refine (hLi.mul_const _).add ?_
    refine (integrable_indicator_iff hfarm).2 ?_
    exact hLr.const_mul (2 * M)
  have hbound : ‖∫ z in B0579.cell d, lapForm d ε z * (φ (z + y) - φ y)‖ ≤
      ∫ z in B0579.cell d, (lapForm d ε z * (e / 2) +
        far.indicator (fun z => 2 * M * lapForm d ε z) z) := by
    refine norm_integral_le_of_norm_le hg_int (Eventually.of_forall fun z => ?_)
    rw [norm_mul, Real.norm_of_nonneg (hLnn z)]
    by_cases hz : z ∈ far
    · have h2 : ‖φ (z + y) - φ y‖ ≤ 2 * M := by
        rw [Real.norm_eq_abs]
        calc |φ (z + y) - φ y| ≤ |φ (z + y)| + |φ y| := abs_sub _ _
          _ ≤ M + M := add_le_add (hMb _) (hMb _)
          _ = 2 * M := by ring
      rw [Set.indicator_of_mem hz]
      have : 0 ≤ lapForm d ε z * (e / 2) := mul_nonneg (hLnn z) (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left h2 (hLnn z)]
    · have hz' : ‖z‖ < δ := by simpa [hfar] using hz
      have h2 : dist (φ (z + y)) (φ y) < e / 2 := hcont (by
        rw [dist_eq_norm]; simpa using hz')
      rw [Set.indicator_of_notMem hz, add_zero]
      exact mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs, ← Real.dist_eq]; exact h2.le)
        (hLnn z)
  have hint : ∫ z in B0579.cell d, (lapForm d ε z * (e / 2) +
      far.indicator (fun z => 2 * M * lapForm d ε z) z) =
      e / 2 + 2 * M * ∫ z in B0579.cell d ∩ far, lapForm d ε z := by
    rw [integral_add (hLi.mul_const _) ((integrable_indicator_iff hfarm).2
      (hLr.const_mul (2 * M))),
      integral_mul_const, hmass, one_mul, setIntegral_indicator hfarm, integral_const_mul]
  have hfarb : ∫ z in B0579.cell d ∩ far, lapForm d ε z ≤ C * ε := hC ε hε0 hε1.le
  have hfin : 2 * M * ∫ z in B0579.cell d ∩ far, lapForm d ε z < e / 2 := by
    have h1 : 2 * M * ∫ z in B0579.cell d ∩ far, lapForm d ε z ≤ 2 * M * (C * ε) :=
      mul_le_mul_of_nonneg_left hfarb (by linarith)
    have h2 : 2 * M * (C * ε) ≤ 2 * M * |C| * ε := by
      have := le_abs_self C
      nlinarith [mul_nonneg hM0 hε0.le, mul_le_mul_of_nonneg_left this (mul_nonneg hM0 hε0.le)]
    have h3 : 2 * M * |C| * ε < K * ε := by
      rw [hK]; nlinarith
    have h4 : K * ε < e / 2 := by
      have := (lt_div_iff₀ (by positivity : (0:ℝ) < 2 * K)).1 hε2
      linarith
    linarith
  rw [Real.dist_eq, hdiff]
  calc |∫ z in B0579.cell d, lapForm d ε z * (φ (z + y) - φ y)|
      = ‖∫ z in B0579.cell d, lapForm d ε z * (φ (z + y) - φ y)‖ := (Real.norm_eq_abs _).symm
    _ ≤ _ := hbound
    _ = _ := hint
    _ < e := by linarith


theorem kerCurlPointwise0_of_parts (hS : KerRegSmooth) (hD : KerRegDeriv) (hI : KerGradIBP)
    (hA : KerApproxId0) (hB : KerBandInt0) (hN : KerLatticeNull) : KerCurlPointwise0 := by
  intro d hd0 φ hφ y
  set F : ℝ × ℝ → ℝ := fun x =>
    kerD d (x - y) 0 * B0579.pd 1 φ x - kerD d (x - y) 1 * B0579.pd 0 φ x with hF
  set dn : ℝ × ℝ → ℝ := fun x => UnforcedLeray.B0592.den d (x - y) with hdn
  have hFint : IntegrableOn F (B0579.cell d) :=
    (hB d hd0 _ (hφ.pd 1) y 0).sub (hB d hd0 _ (hφ.pd 0) y 1)
  have hdn_cont : Continuous dn := (continuous_den d).comp (continuous_id.sub continuous_const)
  have hdn_nn : ∀ x, 0 ≤ dn x := fun x => den_nonneg d _
  have hnull : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), dn x ≠ 0 := by
    rw [ae_iff]
    have : {x : ℝ × ℝ | ¬ dn x ≠ 0} =
        (fun h : ℝ × ℝ => h + -y) ⁻¹' {z : ℝ × ℝ | UnforcedLeray.B0592.den d z = 0} := by
      ext x; simp [hdn, sub_eq_add_neg]
    rw [this, measure_preimage_add_right]
    exact hN d hd0
  have hnull' : ∀ᵐ x ∂(volume.restrict (B0579.cell d)), dn x ≠ 0 := ae_restrict_of_ae hnull
  -- the regularised pairing equals the Laplacian pairing
  have hreg : ∀ ε : ℝ, 0 < ε → ∫ x in B0579.cell d, dn x / (dn x + ε) * F x =
      ∫ x in B0579.cell d,
      (B0579.pd 0 (B0579.pd 0 (fun x : ℝ × ℝ => kerReg d ε (x - y))) x +
        B0579.pd 1 (B0579.pd 1 (fun x : ℝ × ℝ => kerReg d ε (x - y))) x) * φ x := by
    intro ε hε
    obtain ⟨hsm, hper⟩ := hS d ε hd0 hε
    have hGsm : ContDiff ℝ ∞ (fun x : ℝ × ℝ => kerReg d ε (x - y)) :=
      hsm.comp (contDiff_id.sub contDiff_const)
    have hGper : ∀ z : ℝ × ℝ, (fun x : ℝ × ℝ => kerReg d ε (x - y)) (z.1 + d, z.2) =
        (fun x : ℝ × ℝ => kerReg d ε (x - y)) z := by
      intro z
      have : ((z.1 + d, z.2) - y : ℝ × ℝ) = ((z - y).1 + d, (z - y).2) := by
        ext <;> simp <;> ring
      simp only [this, hper]
    have h0 := hI d hd0 _ hGsm hGper φ hφ
    have h1 : ∫ x in B0579.cell d, dn x / (dn x + ε) * F x =
        -∫ x in B0579.cell d,
          (B0579.pd 0 (fun x : ℝ × ℝ => kerReg d ε (x - y)) x * B0579.pd 0 φ x +
            B0579.pd 1 (fun x : ℝ × ℝ => kerReg d ε (x - y)) x * B0579.pd 1 φ x) := by
      rw [← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [hnull'] with x hx
      have hx' : UnforcedLeray.B0592.den d (x - y) ≠ 0 := hx
      obtain ⟨e0, e1⟩ := hD d ε hd0 hε (x - y) hx'
      rw [pd_shift, pd_shift, e0, e1]
      simp only [hF, hdn]
      ring
    rw [h1, h0, neg_neg]
  have hlim : Tendsto (fun ε : ℝ => ∫ x in B0579.cell d, dn x / (dn x + ε) * F x) (𝓝[>] 0)
      (𝓝 (∫ x in B0579.cell d, F x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖F x‖) ?_ ?_ hFint.norm ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      have hc : Continuous fun x => dn x / (dn x + ε) :=
        hdn_cont.div (hdn_cont.add continuous_const) (fun x => by linarith [hdn_nn x])
      exact hc.aestronglyMeasurable.mul hFint.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      refine Eventually.of_forall fun x => ?_
      have h1 : 0 ≤ dn x / (dn x + ε) := div_nonneg (hdn_nn x) (by linarith [hdn_nn x])
      have h2 : dn x / (dn x + ε) ≤ 1 := by
        rw [div_le_one (by linarith [hdn_nn x])]; linarith
      rw [norm_mul, Real.norm_of_nonneg h1]
      exact mul_le_of_le_one_left (norm_nonneg _) h2
    · filter_upwards [hnull'] with x hx
      have hpos : 0 < dn x := lt_of_le_of_ne (hdn_nn x) (Ne.symm hx)
      have h1 : Tendsto (fun ε : ℝ => dn x / (dn x + ε)) (𝓝 0) (𝓝 (dn x / (dn x + 0))) :=
        tendsto_const_nhds.div (tendsto_const_nhds.add tendsto_id) (by simpa using hpos.ne')
      rw [add_zero, div_self hpos.ne'] at h1
      simpa using (h1.mono_left nhdsWithin_le_nhds).mul_const (F x)
  have hlim2 : Tendsto (fun ε : ℝ => ∫ x in B0579.cell d, dn x / (dn x + ε) * F x) (𝓝[>] 0)
      (𝓝 (φ y)) := by
    refine (hA d hd0 φ hφ y).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hreg ε hε).symm
  exact tendsto_nhds_unique hlim hlim2


theorem kerVelCurl0_of_pointwise (hF : KerAdjFubini0) (hP : KerCurlPointwise0) :
    AdjE1.KerVelCurl0 := by
  intro d hd ψ hψ φ hφ
  let F : Fin 2 → ℝ × ℝ → ℂ :=
    ![fun x => ((B0579.pd 1 φ x : ℝ) : ℂ), fun x => ((-B0579.pd 0 φ x : ℝ) : ℂ)]
  have hF0 : ∀ x, F 0 x = ((B0579.pd 1 φ x : ℝ) : ℂ) := fun x => by simp [F]
  have hF1 : ∀ x, F 1 x = ((-B0579.pd 0 φ x : ℝ) : ℂ) := fun x => by simp [F]
  have hint0 : IntegrableOn (F 0) (B0579.cell d) := by
    have hfun : F 0 = fun x => ((B0579.pd 1 φ x : ℝ) : ℂ) := funext hF0
    rw [hfun]
    exact Integrable.ofReal (hφ.pd 1).integrableOn
  have hint1 : IntegrableOn (F 1) (B0579.cell d) := by
    have hfun : F 1 = fun x => ((-B0579.pd 0 φ x : ℝ) : ℂ) := funext hF1
    rw [hfun]
    exact Integrable.ofReal (hφ.pd 0).integrableOn.neg
  have hint : ∀ j, IntegrableOn (F j) (B0579.cell d) := Fin.forall_fin_two.2 ⟨hint0, hint1⟩
  -- the adjoint of `F` is `φ`
  have hA : ∀ y, kerAdj d F y = ((φ y : ℝ) : ℂ) := by
    intro y
    have h1 : ∀ x, ∑ j, F j x * ((kerD d (x - y) j : ℝ) : ℂ) =
        ((kerD d (x - y) 0 * B0579.pd 1 φ x - kerD d (x - y) 1 * B0579.pd 0 φ x : ℝ) : ℂ) := by
      intro x
      rw [Fin.sum_univ_two, hF0, hF1]
      push_cast
      ring
    unfold kerAdj
    simp only [h1]
    rw [integral_complex_ofReal, hP d hd φ hφ y]
  obtain ⟨_, hEq⟩ := hF d hd F hint ψ hψ
  simp only [hA] at hEq
  have h2 : ∀ x, ∑ j, F j x * ((kerVel d ψ x j : ℝ) : ℂ) =
      ((kerVel d ψ x 0 * B0579.pd 1 φ x - kerVel d ψ x 1 * B0579.pd 0 φ x : ℝ) : ℂ) := by
    intro x
    rw [Fin.sum_univ_two, hF0, hF1]
    push_cast
    ring
  have h3 : ∫ y in B0579.cell d, ((φ y : ℝ) : ℂ) * (ψ y : ℂ) =
      ((∫ y in B0579.cell d, ψ y * φ y : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext y
    push_cast
    ring
  have h4 : ∫ x in B0579.cell d, ∑ j, F j x * ((kerVel d ψ x j : ℝ) : ℂ) =
      ((∫ x in B0579.cell d,
        (kerVel d ψ x 0 * B0579.pd 1 φ x - kerVel d ψ x 1 * B0579.pd 0 φ x) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    exact h2 x
  rw [h3, h4] at hEq
  exact Complex.ofReal_injective hEq


theorem kerVelCurl0_of_leaves (hF : KerLapFormula) (hI : KerLapInt) (hM : KerLapMass)
    (hFar : KerLapFar) : AdjE1.KerVelCurl0 :=
  kerVelCurl0_of_pointwise kerAdjFubini0
    (kerCurlPointwise0_of_parts kerRegSmooth kerRegDeriv kerGradIBP
      (kerApproxId0_of hF hI hM hFar) kerBandInt0 kerLatticeNull)

end UnforcedLeray.Short.IIIa

#print axioms UnforcedLeray.Short.IIIa.kerVelCurl0_of_leaves
