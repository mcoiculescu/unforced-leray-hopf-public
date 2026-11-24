import UnforcedLeray.Lib.Parabolic.L2Bound
import UnforcedLeray.Lib.CZCore.Norming

/-!
# The operator `ν ∂_i∂_j (∂_t - νΔ)^{-1}` on `L²(ℝ × ℝ^d)` (INF02 T6)


step 2 ("prove the `L²` bound by BP-A, then extend `T_{ij}` to `L²`") and §5 target T6
(`secondDerivOp`, `norm_secondDerivOp_le`). Manuscript: eq:free-stress-11 at `q = 2`
(`paper/main.tex` lines 7447–7477, blueprint unit B0423).

* `eLpNorm_secondDerivTest_le`: for a test `f`, `‖∂_i∂_j (H_ν ⋆ f)‖₂ ≤ ν⁻¹ ‖f‖₂`; in particular
  `∂_i∂_j (H_ν ⋆ f) ∈ L²` (`memLp_secondDerivTest`). Proof: the pairing bound of `L2Bound`
  against smooth cutoffs `χ_n F`, the norming lemma of the CZ core (`CZ.eLpNorm_le_of_forall_
  test_pairing`, `p = 2`), and Fatou along `χ_n → 1`.
* `testSpace`: tests as a submodule of `ℝ × ℝ^d → ℝ`; `toL2` is injective and has dense range.
* `secondDerivOp ν i j : L² →L[ℝ] L²`, the continuous extension; `secondDerivOp_toL2`: it is
  `∂_i∂_j (H_ν ⋆ f)` on tests; `norm_secondDerivOp_le`: `‖secondDerivOp ν i j‖ ≤ ν⁻¹`, i.e.
  `‖ν ∂_i∂_j u‖₂ ≤ ‖f‖₂` with constant `1` (BP-A).
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Parabolic

open MeasureTheory Real Set Filter
open scoped ENNReal NNReal ContDiff Topology

open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {d : ℕ}

section Linearity

theorem dirD_add {f g : PS d → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (v : PS d) : dirD v (f + g) = dirD v f + dirD v g := by
  funext X
  simp only [dirD, Pi.add_apply]
  rw [fderiv_add (hf X) (hg X)]
  rfl

theorem dirD_smul (c : ℝ) {f : PS d → ℝ} (hf : Differentiable ℝ f) (v : PS d) :
    dirD v (c • f) = c • dirD v f := by
  funext X
  simp only [dirD, Pi.smul_apply]
  rw [fderiv_const_smul (hf X) c]
  rfl

theorem sD2_add {f g : PS d → ℝ} (hf : IsSTTest f) (hg : IsSTTest g) (i j : Fin d) :
    sD2 i j (f + g) = sD2 i j f + sD2 i j g := by
  unfold sD2 sD
  rw [dirD_add hf.differentiable hg.differentiable,
    dirD_add (hf.dirD _).differentiable (hg.dirD _).differentiable]

theorem sD2_smul (c : ℝ) {f : PS d → ℝ} (hf : IsSTTest f) (i j : Fin d) :
    sD2 i j (c • f) = c • sD2 i j f := by
  unfold sD2 sD
  rw [dirD_smul c hf.differentiable, dirD_smul c (hf.dirD _).differentiable]

theorem secondDerivTest_add {ν : ℝ} (hν : 0 < ν) {f g : PS d → ℝ} (hf : IsSTTest f)
    (hg : IsSTTest g) (i j : Fin d) :
    secondDerivTest ν i j (f + g) = secondDerivTest ν i j f + secondDerivTest ν i j g := by
  unfold secondDerivTest
  rw [sD2_add hf hg, duhamel_add hν (hf.sD2 i j) (hg.sD2 i j)]

theorem secondDerivTest_smul (ν c : ℝ) {f : PS d → ℝ} (hf : IsSTTest f) (i j : Fin d) :
    secondDerivTest ν i j (c • f) = c • secondDerivTest ν i j f := by
  unfold secondDerivTest
  rw [sD2_smul c hf, duhamel_smul]

end Linearity

section L2Membership

/-- The cutoff `χ_n`, equal to `1` on the ball of radius `n + 1`. -/
def cutoff (d : ℕ) (n : ℕ) : ContDiffBump (0 : PS d) :=
  ⟨n + 1, n + 2, by positivity, by linarith⟩

theorem cutoff_isSTTest (n : ℕ) : IsSTTest (cutoff d n : PS d → ℝ) :=
  ⟨(cutoff d n).contDiff, (cutoff d n).hasCompactSupport⟩

theorem tendsto_cutoff (X : PS d) : Tendsto (fun n => (cutoff d n : PS d → ℝ) X) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_ge ‖X‖
  filter_upwards [eventually_ge_atTop N] with n hn
  refine ((cutoff d n).one_of_mem_closedBall ?_).symm
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖X‖ ≤ (n : ℝ) + 1
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- **`L²` bound on tests.** `‖∂_i∂_j (H_ν ⋆ f)‖₂ ≤ ν⁻¹ ‖f‖₂`. -/
theorem eLpNorm_secondDerivTest_le {ν : ℝ} (hν : 0 < ν) {f : PS d → ℝ} (hf : IsSTTest f)
    (i j : Fin d) :
    eLpNorm (secondDerivTest ν i j f) 2 volume ≤ ENNReal.ofReal ν⁻¹ * eLpNorm f 2 volume := by
  set F := secondDerivTest ν i j f with hFdef
  have hFc : Continuous F := continuous_secondDerivTest hν hf i j
  have hfin : eLpNorm f 2 volume ≠ ⊤ := (hf.memLp 2).2.ne
  set C : ℝ := ν⁻¹ * (eLpNorm f 2 volume).toReal with hC
  have hcut : ∀ n, eLpNorm (fun X => (cutoff d n : PS d → ℝ) X * F X) 2 volume ≤
      ENNReal.ofReal C := by
    intro n
    have hχ := cutoff_isSTTest (d := d) n
    have hmem : MemLp (fun X => (cutoff d n : PS d → ℝ) X * F X) (ENNReal.ofReal 2) volume :=
      (hχ.continuous.mul hFc).memLp_of_hasCompactSupport hχ.2.mul_right
    have h := UnforcedLeray.CZ.eLpNorm_le_of_forall_test_pairing (μ := volume) (p := 2)
      one_lt_two hmem (C := C) (fun ψ hψ hψc => ?_)
    · simpa using h
    have hg : IsSTTest (fun X => (cutoff d n : PS d → ℝ) X * ψ X) :=
      ⟨hχ.1.mul hψ, hψc.mul_left⟩
    have hb := enorm_pairing_secondDerivTest_le hν hf hg i j
    have hψ2 : eLpNorm (fun X => (cutoff d n : PS d → ℝ) X * ψ X) 2 volume ≤
        eLpNorm ψ 2 volume := by
      refine eLpNorm_mono fun X => ?_
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      refine mul_le_of_le_one_left (abs_nonneg _) ?_
      rw [abs_of_nonneg (cutoff d n).nonneg]; exact (cutoff d n).le_one
    have hψfin : eLpNorm ψ 2 volume ≠ ⊤ :=
      (hψ.continuous.memLp_of_hasCompactSupport (p := 2) hψc).2.ne
    have heq : ∫ X, (cutoff d n : PS d → ℝ) X * F X * ψ X =
        ∫ X, (fun X => (cutoff d n : PS d → ℝ) X * ψ X) X * F X := by
      congr 1; funext X; ring
    have hconj : (ENNReal.ofReal (2 : ℝ).conjExponent) = 2 := by
      norm_num [Real.conjExponent]
    rw [hconj, heq, ← Real.norm_eq_abs, ← toReal_enorm]
    have hrhs : ENNReal.ofReal ν⁻¹ * eLpNorm f 2 volume *
        eLpNorm (fun X => (cutoff d n : PS d → ℝ) X * ψ X) 2 volume ≤
        ENNReal.ofReal ν⁻¹ * eLpNorm f 2 volume * eLpNorm ψ 2 volume := by gcongr
    have hne : ENNReal.ofReal ν⁻¹ * eLpNorm f 2 volume * eLpNorm ψ 2 volume ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hψfin
    refine (ENNReal.toReal_mono hne (hb.trans hrhs)).trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hC]
  have hlim := Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (p := 2) (μ := volume)
    (f := fun n X => (cutoff d n : PS d → ℝ) X * F X) (g := F) (Eventually.of_forall hcut)
    (fun n => ((cutoff_isSTTest (d := d) n).continuous.mul hFc).aestronglyMeasurable)
    (Eventually.of_forall fun X => by
      simpa using (tendsto_cutoff X).mul_const (F X))
  refine hlim.trans (le_of_eq ?_)
  rw [hC, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hfin]

theorem memLp_secondDerivTest {ν : ℝ} (hν : 0 < ν) {f : PS d → ℝ} (hf : IsSTTest f)
    (i j : Fin d) : MemLp (secondDerivTest ν i j f) 2 volume :=
  ⟨(continuous_secondDerivTest hν hf i j).aestronglyMeasurable,
    (eLpNorm_secondDerivTest_le hν hf i j).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hf.memLp 2).2)⟩

end L2Membership

section Extension

/-- The test functions as a submodule of `ℝ × ℝ^d → ℝ`. -/
def testSpace (d : ℕ) : Submodule ℝ (PS d → ℝ) where
  carrier := {f | IsSTTest f}
  add_mem' hf hg := IsSTTest.add hf hg
  zero_mem' := IsSTTest.zero
  smul_mem' c _ hf := IsSTTest.smul hf c

/-- The inclusion of tests in `L²`. -/
def toL2 (d : ℕ) : testSpace d →ₗ[ℝ] Lp ℝ 2 (volume : Measure (PS d)) where
  toFun f := (f.2.memLp 2).toLp f
  map_add' f g := MemLp.toLp_add (f.2.memLp 2) (g.2.memLp 2)
  map_smul' c f := MemLp.toLp_const_smul c (f.2.memLp 2)

theorem coeFn_toL2 (f : testSpace d) : ⇑(toL2 d f) =ᵐ[volume] (f : PS d → ℝ) :=
  (f.2.memLp 2).coeFn_toLp

theorem toL2_injective : Function.Injective (toL2 d) := by
  intro f g h
  have h1 : (f : PS d → ℝ) =ᵐ[volume] g := by
    have := (MemLp.toLp_eq_toLp_iff (f.2.memLp 2) (g.2.memLp 2)).1 h
    exact this
  exact Subtype.ext ((Continuous.ae_eq_iff_eq volume f.2.continuous g.2.continuous).1 h1)

theorem denseRange_toL2 : DenseRange (toL2 d) := by
  rw [Metric.denseRange_iff]
  intro F r hr
  obtain ⟨g, hgc, hgs, hle⟩ := (Lp.memLp F).exist_eLpNorm_sub_le (μ := volume) (p := 2)
    (by norm_num) (by norm_num) (half_pos hr)
  refine ⟨⟨g, hgs, hgc⟩, ?_⟩
  rw [dist_eq_norm, Lp.norm_def]
  have hae : ⇑(F - toL2 d ⟨g, hgs, hgc⟩) =ᵐ[volume] ⇑F - g := by
    filter_upwards [Lp.coeFn_sub F (toL2 d ⟨g, hgs, hgc⟩), coeFn_toL2 (d := d) ⟨g, hgs, hgc⟩]
      with X h1 h2
    rw [h1, Pi.sub_apply, h2]; rfl
  rw [eLpNorm_congr_ae hae]
  have hfin : eLpNorm (⇑F - g) 2 volume ≠ ⊤ := (hle.trans_lt ENNReal.ofReal_lt_top).ne
  calc (eLpNorm (⇑F - g) 2 volume).toReal ≤ (ENNReal.ofReal (r / 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = r / 2 := ENNReal.toReal_ofReal (by positivity)
    _ < r := half_lt_self hr

/-- The `L²` operator on tests, `f ↦ ∂_i∂_j(H_ν ⋆ f)`. -/
def secondDerivTestL2 {ν : ℝ} (hν : 0 < ν) (i j : Fin d) :
    testSpace d →ₗ[ℝ] Lp ℝ 2 (volume : Measure (PS d)) where
  toFun f := (memLp_secondDerivTest hν f.2 i j).toLp _
  map_add' f g := by
    have h := secondDerivTest_add hν f.2 g.2 i j
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun X => by
      simp only [Submodule.coe_add]; rw [h])
  map_smul' c f := by
    have h := secondDerivTest_smul ν c f.2 i j
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun X => by
      simp only [Submodule.coe_smul]; rw [h])

/-- The test subspace of `L²`. -/
abbrev testL2 (d : ℕ) : Submodule ℝ (Lp ℝ 2 (volume : Measure (PS d))) := LinearMap.range (toL2 d)

/-- The linear equivalence between tests and their `L²` classes. -/
def testEquiv (d : ℕ) : testSpace d ≃ₗ[ℝ] testL2 d :=
  LinearEquiv.ofInjective (toL2 d) toL2_injective

theorem testEquiv_coe (f : testSpace d) : ((testEquiv d f : testL2 d) : Lp ℝ 2 volume) = toL2 d f :=
  rfl

/-- The operator on the test subspace of `L²`. -/
def secondDerivOnTests {ν : ℝ} (hν : 0 < ν) (i j : Fin d) :
    testL2 d →L[ℝ] Lp ℝ 2 (volume : Measure (PS d)) :=
  LinearMap.mkContinuous ((secondDerivTestL2 hν i j).comp (testEquiv d).symm.toLinearMap) ν⁻¹
    (fun F => by
      obtain ⟨f, rfl⟩ := (testEquiv d).surjective F
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      rw [Submodule.coe_norm, testEquiv_coe, Lp.norm_def, Lp.norm_def]
      change (eLpNorm (⇑((memLp_secondDerivTest hν f.2 i j).toLp _)) 2 volume).toReal ≤
        ν⁻¹ * (eLpNorm (⇑((f.2.memLp 2).toLp (f : PS d → ℝ))) 2 volume).toReal
      rw [eLpNorm_congr_ae (MemLp.coeFn_toLp _), eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
      have h := eLpNorm_secondDerivTest_le hν f.2 i j
      have hfin : eLpNorm (f : PS d → ℝ) 2 volume ≠ ⊤ := (f.2.memLp 2).2.ne
      refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h).trans
        (le_of_eq ?_)
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)])

theorem denseRange_testL2_subtype : DenseRange ((testL2 d).subtypeL) := by
  have h := denseRange_toL2 (d := d)
  intro F
  have := h F
  refine closure_mono ?_ this
  rintro _ ⟨f, rfl⟩
  exact ⟨⟨toL2 d f, f, rfl⟩, rfl⟩

theorem isUniformInducing_testL2_subtype : IsUniformInducing ((testL2 d).subtypeL) :=
  isUniformEmbedding_subtype_val.isUniformInducing

/-- **INF02 T6.** The bounded operator `∂_i∂_j (∂_t - νΔ)^{-1}` on `L²(ℝ × ℝ^d)`: the
continuous extension of `f ↦ ∂_i∂_j (H_ν ⋆ f)` from tests. -/
def secondDerivOp {ν : ℝ} (hν : 0 < ν) (i j : Fin d) :
    Lp ℝ 2 (volume : Measure (PS d)) →L[ℝ] Lp ℝ 2 (volume : Measure (PS d)) :=
  (secondDerivOnTests hν i j).extend (testL2 d).subtypeL

/-- On tests, `secondDerivOp` is the classical `∂_i∂_j (H_ν ⋆ f)`. -/
theorem secondDerivOp_toL2 {ν : ℝ} (hν : 0 < ν) (i j : Fin d) (f : testSpace d) :
    secondDerivOp hν i j (toL2 d f) = (memLp_secondDerivTest hν f.2 i j).toLp _ := by
  have h := ContinuousLinearMap.extend_eq (secondDerivOnTests hν i j)
    denseRange_testL2_subtype isUniformInducing_testL2_subtype (testEquiv d f)
  change secondDerivOp hν i j (testEquiv d f : Lp ℝ 2 volume) = _
  rw [secondDerivOp]
  refine h.trans ?_
  simp [secondDerivOnTests, secondDerivTestL2]

/-- The same, for a test function given as a function. -/
theorem secondDerivOp_toLp {ν : ℝ} (hν : 0 < ν) (i j : Fin d) {f : PS d → ℝ} (hf : IsSTTest f) :
    secondDerivOp hν i j ((hf.memLp 2).toLp f) = (memLp_secondDerivTest hν hf i j).toLp _ :=
  secondDerivOp_toL2 hν i j ⟨f, hf⟩

/-- **INF02 T6 (BP-A): `‖secondDerivOp ν i j‖ ≤ ν⁻¹`**, that is `‖ν ∂_i∂_j u‖₂ ≤ ‖f‖₂`, with
constant `1`, independent of `ν` and `d`. -/
theorem norm_secondDerivOp_le {ν : ℝ} (hν : 0 < ν) (i j : Fin d) :
    ‖secondDerivOp hν i j‖ ≤ ν⁻¹ := by
  have h := ContinuousLinearMap.opNorm_extend_le (secondDerivOnTests hν i j) (N := 1)
    denseRange_testL2_subtype (fun x => by simp)
  refine h.trans ?_
  rw [NNReal.coe_one, one_mul]
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- **INF02 T10 (operator form).** `‖ν • secondDerivOp ν i j‖ ≤ 1`. -/
theorem norm_smul_secondDerivOp_le {ν : ℝ} (hν : 0 < ν) (i j : Fin d) :
    ‖ν • secondDerivOp hν i j‖ ≤ 1 := by
  rw [norm_smul, Real.norm_of_nonneg hν.le]
  calc ν * ‖secondDerivOp hν i j‖ ≤ ν * ν⁻¹ := by gcongr; exact norm_secondDerivOp_le hν i j
    _ = 1 := mul_inv_cancel₀ hν.ne'

end Extension

end UnforcedLeray.Parabolic
