import UnforcedLeray.Short.PartIIa.StatementsFree
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressEpsLocalH14.StressEpsCommutingFlowShiftQ.HalfDrift
import UnforcedLeray.Units.B0220.Chart
import UnforcedLeray.Units.B0428.Slice
import UnforcedLeray.Lib.FreeStressCouplings.ProdLp
import UnforcedLeray.Lib.LerayC.Complex
import UnforcedLeray.Analysis.SpatialScaling
import UnforcedLeray.Analysis.SobolevEmbedding.Density
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Spatial `H¹` slice estimates from `HasGrad` on `Yq P 2`

For `v : Yq P 2` and `g_diss : Fin 3 → Yq P 2` satisfying `HasGrad v g_diss`:
1. Almost every phase slice `v τ` has real and imaginary parts with weak spatial derivatives
   `reV (g_diss j τ)` and `imV (g_diss j τ)`.
2. Via smooth mollification (`SobolevEmbedding.mollification`) and Fatou's lemma:
   - Radial scaling difference `V₀ (τ, α • y) - V₀ (τ, y)` on `univ ×ˢ S` (`S ⊆ closedBall 0 R`),
     used for the spatial scaling flow in `PartII-a:N05/3/2`.
   - Cylindrical vertical shear difference `V₀ (τ, y + (k * radius y) • e_2) - V₀ (τ, y)` on
     `univ ×ˢ S` (`|k * radius y| ≤ Δ`), used for `shiftEta` in `PartII-a:N05/3/1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.N05FlowAux

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0428
open UnforcedLeray.FreeStress UnforcedLeray.RieszLp
open MeasureTheory.Measure (QuasiMeasurePreserving)

/-! ### 1. Complex `ℂ³` vs real/imaginary `ℝ³` norms -/

theorem norm_cvec3_sq_eq_re_im (z : CVec3) :
    ‖z‖ ^ 2 = ‖reV z‖ ^ 2 + ‖imV z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, reV_apply, imV_apply,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  ring

theorem enorm_cvec3_sq_eq_re_im (z : CVec3) :
    ‖z‖ₑ ^ (2 : ℝ) = ‖reV z‖ₑ ^ (2 : ℝ) + ‖imV z‖ₑ ^ (2 : ℝ) := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    Real.rpow_two, Real.rpow_two, Real.rpow_two,
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), norm_cvec3_sq_eq_re_im]

theorem memLp_reV_comp {u : Lp CVec3 2 (volume : Measure Space)} :
    MemLp (fun y => reV ((u : Space → CVec3) y)) 2 volume := by
  refine (Lp.memLp u).of_le
    (reV.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)) ?_
  exact Eventually.of_forall fun y =>
    (reV.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) norm_reV_le)

theorem memLp_imV_comp {u : Lp CVec3 2 (volume : Measure Space)} :
    MemLp (fun y => imV ((u : Space → CVec3) y)) 2 volume := by
  refine (Lp.memLp u).of_le
    (imV.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)) ?_
  exact Eventually.of_forall fun y =>
    (imV.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) norm_imV_le)

/-! ### 2. Slicing `HasGrad` into `HasWeakSpatialDerivative` on a.e. phase -/

theorem isSpatialTest_neg_sd {ψ : Space → ℝ} (hψ : IsSpatialTest ψ) (j : Fin 3) :
    IsSpatialTest (fun y => -sd j ψ y) :=
  ⟨(isSpatialTest_sd hψ j).smooth.neg, (isSpatialTest_sd hψ j).compact.neg⟩

theorem neg_dy_prodTest {P : ℝ} (n : ℤ) {ψ : Space → ℝ} (hψ : IsSpatialTest ψ) (i j : Fin 3) :
    (fun Φ => -dy j Φ) (prodTest P n ψ i) = prodTest P n (fun y => -sd j ψ y) i := by
  funext p
  obtain ⟨t, y⟩ := p
  change -dy j (prodTest P n ψ i) (t, y) = prodTest P n (fun z => -sd j ψ z) i (t, y)
  rw [dy_prodTest n hψ i j, prodTest_apply_eq, prodTest_apply_eq, neg_smul]

theorem ae_slice_pair_neg_dy {P : ℝ} [Fact (0 < P)] {w gj : Yq P 2} (j : Fin 3)
    (h : HasPhaseOp (fun Φ => -dy j Φ) w gj) {ψ : Space → ℝ} (hψ : IsSpatialTest ψ) (i : Fin 3) :
    ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
      innerPair 2 (sT 2 (isSpatialTest_neg_sd hψ j) i) (w τ) =
        innerPair 2 (sT 2 hψ i) (gj τ) := by
  set a := sT 2 (isSpatialTest_neg_sd hψ j) i
  set b := sT 2 hψ i
  have hint : Integrable (fun τ => innerPair 2 a (w τ) - innerPair 2 b (gj τ))
      (AddCircle.haarAddCircle (T := P)) :=
    ((innerPair 2 a).integrable_comp (integrable_Yq w)).sub
      ((innerPair 2 b).integrable_comp (integrable_Yq gj))
  have hF : ∀ n : ℤ, ∫ τ, fourier n τ * (innerPair 2 a (w τ) - innerPair 2 b (gj τ))
      ∂AddCircle.haarAddCircle = 0 := by
    intro n
    have i1 := (innerPair 2 a).integrable_comp (integrable_fourier_smul w n)
    have i2 := (innerPair 2 b).integrable_comp (integrable_fourier_smul gj n)
    simp only [map_smul, smul_eq_mul] at i1 i2
    have e1 : ∫ τ, fourier n τ * innerPair 2 a (w τ) ∂AddCircle.haarAddCircle =
        innerPair 2 a (∫ τ, fourier n τ • w τ ∂AddCircle.haarAddCircle) := by
      rw [← (innerPair 2 a).integral_comp_comm (integrable_fourier_smul w n)]
      simp only [map_smul, smul_eq_mul]
    have e2 : ∫ τ, fourier n τ * innerPair 2 b (gj τ) ∂AddCircle.haarAddCircle =
        innerPair 2 b (∫ τ, fourier n τ • gj τ ∂AddCircle.haarAddCircle) := by
      rw [← (innerPair 2 b).integral_comp_comm (integrable_fourier_smul gj n)]
      simp only [map_smul, smul_eq_mul]
    have hp := h _ (isPhaseTest_prodTest n hψ.smooth hψ.compact i)
    rw [neg_dy_prodTest n hψ i j,
      phasePair_prodTest w n (isSpatialTest_neg_sd hψ j).smooth
        (isSpatialTest_neg_sd hψ j).compact i,
      phasePair_prodTest gj n hψ.smooth hψ.compact i] at hp
    simp only [mul_sub]
    rw [integral_sub i1 i2, e1, e2]
    exact sub_eq_zero.2 hp
  filter_upwards [ae_eq_zero_of_fourier hint hF] with τ hτ
  exact sub_eq_zero.1 hτ

private def testEmbNegDy (j : Fin 3) (ψ : {ψ : Space → ℝ // IsSpatialTest ψ}) :
    Fin 3 → Lp CVec3 (conjExp 2) (volume : Measure Space) ×
      Lp CVec3 (conjExp 2) (volume : Measure Space) :=
  fun i => (sT 2 ψ.2 i, sT 2 (isSpatialTest_neg_sd ψ.2 j) i)

theorem ae_forall_pair_neg_dy {P : ℝ} [Fact (0 < P)] {w gj : Yq P 2} (j : Fin 3)
    (h : HasPhaseOp (fun Φ => -dy j Φ) w gj) :
    ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), ∀ ψ : Space → ℝ, ∀ hψ : IsSpatialTest ψ,
      ∀ i : Fin 3, innerPair 2 (sT 2 (isSpatialTest_neg_sd hψ j) i) (w τ) =
        innerPair 2 (sT 2 hψ i) (gj τ) := by
  have : Fact (conjExp (2 : ℝ≥0∞) ≠ ⊤) := ⟨B0428.conjExp_ne_top ENNReal.one_lt_two⟩
  have h1 : SecondCountableTopology (Lp CVec3 (conjExp 2) (volume : Measure Space)) :=
    inferInstance
  have h2 : SecondCountableTopology (Lp CVec3 (conjExp 2) (volume : Measure Space) ×
      Lp CVec3 (conjExp 2) (volume : Measure Space)) := inferInstance
  have h3 : SecondCountableTopology (Fin 3 → Lp CVec3 (conjExp 2) (volume : Measure Space) ×
      Lp CVec3 (conjExp 2) (volume : Measure Space)) := inferInstance
  set s := range (testEmbNegDy j)
  have hsep : TopologicalSpace.IsSeparable s := TopologicalSpace.IsSeparable.of_separableSpace s
  have := hsep.separableSpace
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense s
  have hsub : s ⊆ closure (Subtype.val '' D) := Subtype.dense_iff.1 hDd
  have : Countable D := hDc.to_subtype
  have hgood : ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), ∀ d : D,
      PairCond 2 (w τ) (gj τ) (d : s) := by
    rw [ae_all_iff]
    intro d
    obtain ⟨ψ, hψ⟩ := (d : s).2
    rw [← hψ]
    have hi : ∀ i : Fin 3, ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
        innerPair 2 (sT 2 (isSpatialTest_neg_sd ψ.2 j) i) (w τ) =
          innerPair 2 (sT 2 ψ.2 i) (gj τ) := fun i => ae_slice_pair_neg_dy j h ψ.2 i
    filter_upwards [ae_all_iff.2 hi] with τ hτ
    exact hτ
  filter_upwards [hgood] with τ hτ
  intro ψ hψ i
  have hcl : closure (Subtype.val '' D) ⊆ {x | PairCond 2 (w τ) (gj τ) x} := by
    refine closure_minimal ?_ (isClosed_pairCond _ _)
    rintro _ ⟨d, hd, rfl⟩
    exact hτ ⟨d, hd⟩
  exact hcl (hsub ⟨⟨ψ, hψ⟩, rfl⟩) i

theorem hasWeakSpatialDerivative_re_im_of_pair {j : Fin 3}
    {u gj : Lp CVec3 2 (volume : Measure Space)}
    (h : ∀ ψ : Space → ℝ, ∀ hψ : IsSpatialTest ψ, ∀ i : Fin 3,
      innerPair 2 (sT 2 (isSpatialTest_neg_sd hψ j) i) u = innerPair 2 (sT 2 hψ i) gj) :
    HasWeakSpatialDerivative j (fun y => reV ((u : Space → CVec3) y))
        (fun y => reV ((gj : Space → CVec3) y)) ∧
      HasWeakSpatialDerivative j (fun y => imV ((u : Space → CVec3) y))
        (fun y => imV ((gj : Space → CVec3) y)) := by
  have hu : LocallyIntegrable (u : Space → CVec3) volume :=
    (Lp.memLp u).locallyIntegrable one_le_two
  have hgj : LocallyIntegrable (gj : Space → CVec3) volume :=
    (Lp.memLp gj).locallyIntegrable one_le_two
  have huR := (memLp_reV_comp (u := u)).locallyIntegrable one_le_two
  have huI := (memLp_imV_comp (u := u)).locallyIntegrable one_le_two
  have hgR := (memLp_reV_comp (u := gj)).locallyIntegrable one_le_two
  have hgI := (memLp_imV_comp (u := gj)).locallyIntegrable one_le_two
  have hcoord : ∀ (φ : Space → ℝ) (hφ : IsSpatialTest φ) (i : Fin 3),
      ∫ x, ((-spatialTestDerivative j φ x : ℝ) : ℂ) * ((u : Space → CVec3) x) i =
        ∫ x, (φ x : ℂ) * ((gj : Space → CVec3) x) i := by
    intro φ hφ i
    have h1 := h φ hφ i
    have hnsd := isSpatialTest_neg_sd hφ j
    rw [sT, sT, innerPair_spatialTest hnsd.smooth hnsd.compact i u,
      innerPair_spatialTest hφ.smooth hφ.compact i gj] at h1
    exact h1
  constructor
  · refine ⟨fun φ hφ => huR.integrable_smul_left_of_hasCompactSupport
        (hφ.derivative j).smooth.continuous (hφ.derivative j).compact,
      fun φ hφ => hgR.integrable_smul_left_of_hasCompactSupport
        hφ.smooth.continuous hφ.compact, fun φ hφ => ?_⟩
    have hL := huR.integrable_smul_left_of_hasCompactSupport
      (hφ.derivative j).smooth.continuous (hφ.derivative j).compact
    have hR := hgR.integrable_smul_left_of_hasCompactSupport
      hφ.smooth.continuous hφ.compact
    have hLC : ∀ i : Fin 3, Integrable (fun x => ((-spatialTestDerivative j φ x : ℝ) : ℂ) *
        ((u : Space → CVec3) x) i) volume := fun i => by
      have hi := ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).integrable_comp
        (hu.integrable_smul_left_of_hasCompactSupport
          (isSpatialTest_neg_sd hφ j).smooth.continuous (isSpatialTest_neg_sd hφ j).compact))
      simpa [Complex.real_smul, sd, spatialTestDerivative] using hi
    have hRC : ∀ i : Fin 3, Integrable (fun x => (φ x : ℂ) *
        ((gj : Space → CVec3) x) i) volume := fun i => by
      have hi := ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).integrable_comp
        (hgj.integrable_smul_left_of_hasCompactSupport hφ.smooth.continuous hφ.compact))
      simpa [Complex.real_smul] using hi
    ext i
    rw [PiLp.neg_apply]
    have eL : (∫ x, spatialTestDerivative j φ x • reV ((u : Space → CVec3) x)) i =
        ∫ x, spatialTestDerivative j φ x * (((u : Space → CVec3) x) i).re := by
      have hp := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integral_comp_comm hL
      change EuclideanSpace.proj i (∫ x, spatialTestDerivative j φ x •
        reV ((u : Space → CVec3) x)) = _
      rw [← hp]
      simp [reV_apply]
    have eR : (∫ x, φ x • reV ((gj : Space → CVec3) x)) i =
        ∫ x, φ x * (((gj : Space → CVec3) x) i).re := by
      have hp := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integral_comp_comm hR
      change EuclideanSpace.proj i (∫ x, φ x • reV ((gj : Space → CVec3) x)) = _
      rw [← hp]
      simp [reV_apply]
    have hre := congrArg Complex.re (hcoord φ hφ i)
    rw [← Complex.reCLM_apply, ← Complex.reCLM_apply,
      ← Complex.reCLM.integral_comp_comm (hLC i),
      ← Complex.reCLM.integral_comp_comm (hRC i)] at hre
    simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, neg_mul] at hre
    rw [integral_neg] at hre
    rw [eL, eR]
    linarith
  · refine ⟨fun φ hφ => huI.integrable_smul_left_of_hasCompactSupport
        (hφ.derivative j).smooth.continuous (hφ.derivative j).compact,
      fun φ hφ => hgI.integrable_smul_left_of_hasCompactSupport
        hφ.smooth.continuous hφ.compact, fun φ hφ => ?_⟩
    have hL := huI.integrable_smul_left_of_hasCompactSupport
      (hφ.derivative j).smooth.continuous (hφ.derivative j).compact
    have hR := hgI.integrable_smul_left_of_hasCompactSupport
      hφ.smooth.continuous hφ.compact
    have hLC : ∀ i : Fin 3, Integrable (fun x => ((-spatialTestDerivative j φ x : ℝ) : ℂ) *
        ((u : Space → CVec3) x) i) volume := fun i => by
      have hi := ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).integrable_comp
        (hu.integrable_smul_left_of_hasCompactSupport
          (isSpatialTest_neg_sd hφ j).smooth.continuous (isSpatialTest_neg_sd hφ j).compact))
      simpa [Complex.real_smul, sd, spatialTestDerivative] using hi
    have hRC : ∀ i : Fin 3, Integrable (fun x => (φ x : ℂ) *
        ((gj : Space → CVec3) x) i) volume := fun i => by
      have hi := ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).integrable_comp
        (hgj.integrable_smul_left_of_hasCompactSupport hφ.smooth.continuous hφ.compact))
      simpa [Complex.real_smul] using hi
    ext i
    rw [PiLp.neg_apply]
    have eL : (∫ x, spatialTestDerivative j φ x • imV ((u : Space → CVec3) x)) i =
        ∫ x, spatialTestDerivative j φ x * (((u : Space → CVec3) x) i).im := by
      have hp := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integral_comp_comm hL
      change EuclideanSpace.proj i (∫ x, spatialTestDerivative j φ x •
        imV ((u : Space → CVec3) x)) = _
      rw [← hp]
      simp [imV_apply]
    have eR : (∫ x, φ x • imV ((gj : Space → CVec3) x)) i =
        ∫ x, φ x * (((gj : Space → CVec3) x) i).im := by
      have hp := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integral_comp_comm hR
      change EuclideanSpace.proj i (∫ x, φ x • imV ((gj : Space → CVec3) x)) = _
      rw [← hp]
      simp [imV_apply]
    have him := congrArg Complex.im (hcoord φ hφ i)
    rw [← Complex.imCLM_apply, ← Complex.imCLM_apply,
      ← Complex.imCLM.integral_comp_comm (hLC i),
      ← Complex.imCLM.integral_comp_comm (hRC i)] at him
    simp only [Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, neg_mul] at him
    rw [integral_neg] at him
    rw [eL, eR]
    linarith

theorem ae_slice_weakSpatialDeriv {P : ℝ} [Fact (0 < P)] {v : Yq P 2}
    {g_diss : Fin 3 → Yq P 2} (hg : HasGrad v g_diss) :
    ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), ∀ j : Fin 3,
      HasWeakSpatialDerivative j (fun y => reV ((v τ : Space → CVec3) y))
          (fun y => reV ((g_diss j τ : Space → CVec3) y)) ∧
        HasWeakSpatialDerivative j (fun y => imV ((v τ : Space → CVec3) y))
          (fun y => imV ((g_diss j τ : Space → CVec3) y)) := by
  have hall : ∀ j : Fin 3, ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), _ :=
    fun j => ae_forall_pair_neg_dy j (hg j)
  filter_upwards [ae_all_iff.2 hall] with τ hτ j
  exact hasWeakSpatialDerivative_re_im_of_pair (hτ j)

/-! ### 3. Elementary Cauchy-Schwarz on `uIoc` and `Space` decomposition -/

private theorem sq_setIntegral_uIoc_le {a b : ℝ} {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    (∫ r in uIoc a b, ψ r) ^ 2 ≤ |b - a| * ∫ r in uIoc a b, ψ r ^ 2 := by
  rcases eq_or_ne a b with rfl | hab
  · simp
  · set L : ℝ := |b - a|
    have hL : 0 < L := abs_sub_pos.2 hab.symm
    have hvol : (volume : Measure ℝ).real (uIoc a b) = L := by
      rw [measureReal_def, Real.volume_uIoc, ENNReal.toReal_ofReal hL.le]
    have hint1 : IntegrableOn ψ (uIoc a b) := hψ.integrableOn_uIoc
    have hint2 : IntegrableOn (fun r => ψ r ^ 2) (uIoc a b) := (hψ.pow 2).integrableOn_uIoc
    set I1 : ℝ := ∫ r in uIoc a b, ψ r
    set I2 : ℝ := ∫ r in uIoc a b, ψ r ^ 2
    set m : ℝ := I1 / L
    have hint_diff : IntegrableOn (fun r => ψ r ^ 2 - 2 * m * ψ r) (uIoc a b) :=
      hint2.sub (hint1.const_mul (2 * m))
    have hint_c : IntegrableOn (fun _ : ℝ => m ^ 2) (uIoc a b) :=
      integrableOn_const (hs := by simp [Real.volume_uIoc])
    have h0 : 0 ≤ ∫ r in uIoc a b, (ψ r - m) ^ 2 :=
      setIntegral_nonneg measurableSet_uIoc fun r _ => sq_nonneg _
    have heq : (fun r => (ψ r - m) ^ 2) = fun r => (ψ r ^ 2 - 2 * m * ψ r) + m ^ 2 := by
      funext r; ring
    rw [heq, integral_add hint_diff hint_c,
      integral_sub hint2 (hint1.const_mul (2 * m)),
      MeasureTheory.integral_const_mul, setIntegral_const, smul_eq_mul, hvol] at h0
    change 0 ≤ I2 - 2 * m * I1 + L * m ^ 2 at h0
    have hmul : 0 ≤ L * (I2 - 2 * m * I1 + L * m ^ 2) := mul_nonneg hL.le h0
    have hid : L * (I2 - 2 * m * I1 + L * m ^ 2) = L * I2 - I1 ^ 2 := by
      dsimp [m]
      field_simp
      ring
    linarith

private theorem space_eq_sum_coord (y : Space) :
    y = ∑ j : Fin 3, y j • coordinateVector j := by
  ext i
  simp [coordinateVector, Pi.single_apply]

private theorem abs_coord_le_norm (y : Space) (j : Fin 3) : |y j| ≤ ‖y‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y j

/-! ### 4. Radial scaling `H¹` bound on `Metric.closedBall 0 R` -/

theorem smooth_lintegral_closedBall_smul_sub_sq_le {f : SpatialField} (hf : ContDiff ℝ ∞ f)
    {R α : ℝ} (_hR : 0 ≤ R) (hα1 : Real.exp (-1) ≤ α) (hα2 : α ≤ Real.exp 1) :
    ∫⁻ y in Metric.closedBall (0 : Space) R, ‖f (α • y) - f y‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (3 * Real.exp 3 * (R * |α - 1|) ^ 2) *
        ∑ j : Fin 3, ∫⁻ y : Space, ‖fderiv ℝ f y (coordinateVector j)‖ₑ ^ (2 : ℝ) := by
  set Df : Fin 3 → SpatialField := fun j y => fderiv ℝ f y (coordinateVector j)
  have hDf_cont : ∀ j : Fin 3, Continuous (Df j) := fun j =>
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpt : ∀ y ∈ Metric.closedBall (0 : Space) R,
      ‖f (α • y) - f y‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (3 * R ^ 2 * |α - 1|) *
          ∑ j : Fin 3, ∫⁻ r in uIoc (1 : ℝ) α, ‖Df j (r • y)‖ₑ ^ (2 : ℝ) := by
    intro y hy
    have hyR : ‖y‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hy
    have hderiv : ∀ r : ℝ, HasDerivAt (fun r : ℝ => f (r • y)) (fderiv ℝ f (r • y) y) r := by
      intro r
      have hr : HasDerivAt (fun r : ℝ => r • y) y r := by
        simpa using (hasDerivAt_id r).smul_const y
      exact (hf.differentiable (by simp) (r • y)).hasFDerivAt.comp_hasDerivAt r hr
    have hcont_r : Continuous (fun r : ℝ => fderiv ℝ f (r • y) y) :=
      ((hf.continuous_fderiv (by simp)).comp (continuous_id.smul continuous_const)).clm_apply
        continuous_const
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hderiv r)
      (hcont_r.intervalIntegrable 1 α)
    rw [one_smul] at hftc
    set ψ : ℝ → ℝ := fun r => R * ∑ j : Fin 3, ‖Df j (r • y)‖
    have hψ_cont : Continuous ψ :=
      continuous_const.mul (continuous_finsetSum _ fun j _ =>
        ((hDf_cont j).comp (continuous_id.smul continuous_const)).norm)
    have hnorm_le : ‖f (α • y) - f y‖ ≤ ∫ r in uIoc (1 : ℝ) α, ψ r := by
      rw [← hftc]
      refine intervalIntegral.norm_integral_le_integral_norm_uIoc.trans ?_
      refine setIntegral_mono hcont_r.norm.integrableOn_uIoc
        hψ_cont.integrableOn_uIoc fun r => ?_
      have hmap : (fderiv ℝ f (r • y)) y =
          ∑ j : Fin 3, (fderiv ℝ f (r • y)) (y j • coordinateVector j) := by
        conv_lhs => arg 2; rw [space_eq_sum_coord y]
        exact map_sum (fderiv ℝ f (r • y)) _ _
      rw [hmap]
      calc ‖∑ j : Fin 3, (fderiv ℝ f (r • y)) (y j • coordinateVector j)‖
          ≤ ∑ j : Fin 3, ‖(fderiv ℝ f (r • y)) (y j • coordinateVector j)‖ := norm_sum_le _ _
        _ = ∑ j : Fin 3, |y j| * ‖Df j (r • y)‖ := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_smul, norm_smul, Real.norm_eq_abs]
        _ ≤ ∑ j : Fin 3, R * ‖Df j (r • y)‖ := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact mul_le_mul_of_nonneg_right ((abs_coord_le_norm y j).trans hyR) (norm_nonneg _)
        _ = ψ r := (Finset.mul_sum _ _ _).symm
    have hcs := sq_setIntegral_uIoc_le (a := 1) (b := α) hψ_cont
    have hsq_ψ : ∀ r : ℝ, ψ r ^ 2 ≤ 3 * R ^ 2 * ∑ j : Fin 3, ‖Df j (r • y)‖ ^ 2 := by
      intro r
      dsimp [ψ]
      rw [Fin.sum_univ_three, Fin.sum_univ_three]
      set a0 := ‖Df 0 (r • y)‖
      set a1 := ‖Df 1 (r • y)‖
      set a2 := ‖Df 2 (r • y)‖
      have h3 : (a0 + a1 + a2) ^ 2 ≤ 3 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2) := by
        nlinarith [sq_nonneg (a0 - a1), sq_nonneg (a1 - a2), sq_nonneg (a2 - a0)]
      calc (R * (a0 + a1 + a2)) ^ 2
          = R ^ 2 * (a0 + a1 + a2) ^ 2 := by ring
        _ ≤ R ^ 2 * (3 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2)) :=
            mul_le_mul_of_nonneg_left h3 (sq_nonneg R)
        _ = 3 * R ^ 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2) := by ring
    have hDf_sq_int : ∀ j : Fin 3, IntegrableOn (fun r : ℝ => ‖Df j (r • y)‖ ^ 2) (uIoc 1 α) :=
      fun j => (((hDf_cont j).comp
        (continuous_id.smul continuous_const)).norm.pow 2).integrableOn_uIoc
    have hint_sum : IntegrableOn (fun r => ∑ j : Fin 3, ‖Df j (r • y)‖ ^ 2) (uIoc 1 α) :=
      (continuous_finsetSum _ fun j _ =>
        (((hDf_cont j).comp (continuous_id.smul continuous_const)).norm.pow 2)).integrableOn_uIoc
    have hnorm_sq : ‖f (α • y) - f y‖ ^ 2 ≤
        3 * R ^ 2 * |α - 1| * ∑ j : Fin 3, ∫ r in uIoc (1 : ℝ) α, ‖Df j (r • y)‖ ^ 2 := by
      calc ‖f (α • y) - f y‖ ^ 2
          ≤ (∫ r in uIoc (1 : ℝ) α, ψ r) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2
        _ ≤ |α - 1| * ∫ r in uIoc (1 : ℝ) α, ψ r ^ 2 := hcs
        _ ≤ |α - 1| * ∫ r in uIoc (1 : ℝ) α, (3 * R ^ 2 * ∑ j : Fin 3, ‖Df j (r • y)‖ ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact setIntegral_mono (hψ_cont.pow 2).integrableOn_uIoc
              (hint_sum.const_mul _) hsq_ψ
        _ = 3 * R ^ 2 * |α - 1| * ∑ j : Fin 3, ∫ r in uIoc (1 : ℝ) α, ‖Df j (r • y)‖ ^ 2 := by
            rw [MeasureTheory.integral_const_mul,
              integral_finsetSum _ fun j _ => hDf_sq_int j]
            ring
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
    calc ENNReal.ofReal (‖f (α • y) - f y‖ ^ 2)
        ≤ ENNReal.ofReal (3 * R ^ 2 * |α - 1| *
            ∑ j : Fin 3, ∫ r in uIoc (1 : ℝ) α, ‖Df j (r • y)‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal hnorm_sq
      _ = ENNReal.ofReal (3 * R ^ 2 * |α - 1|) *
            ∑ j : Fin 3, ∫⁻ r in uIoc (1 : ℝ) α, ‖Df j (r • y)‖ₑ ^ (2 : ℝ) := by
          rw [ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_sum_of_nonneg fun j _ =>
              setIntegral_nonneg measurableSet_uIoc fun _ _ => sq_nonneg _]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [ofReal_integral_eq_lintegral_ofReal (hDf_sq_int j)
            (Eventually.of_forall fun _ => sq_nonneg _)]
          refine lintegral_congr fun r => ?_
          rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
            Real.rpow_two]
  calc ∫⁻ y in Metric.closedBall (0 : Space) R, ‖f (α • y) - f y‖ₑ ^ (2 : ℝ)
      ≤ ∫⁻ y in Metric.closedBall (0 : Space) R,
          ENNReal.ofReal (3 * R ^ 2 * |α - 1|) *
            ∑ j : Fin 3, ∫⁻ r in uIoc (1 : ℝ) α, ‖Df j (r • y)‖ₑ ^ (2 : ℝ) :=
        setLIntegral_mono' Metric.isClosed_closedBall.measurableSet hpt
    _ ≤ ∫⁻ y : Space,
          ENNReal.ofReal (3 * R ^ 2 * |α - 1|) *
            ∑ j : Fin 3, ∫⁻ r in uIoc (1 : ℝ) α, ‖Df j (r • y)‖ₑ ^ (2 : ℝ) :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (3 * R ^ 2 * |α - 1|) *
          ∑ j : Fin 3, ∫⁻ r in uIoc (1 : ℝ) α, ∫⁻ y : Space, ‖Df j (r • y)‖ₑ ^ (2 : ℝ) := by
        have hm_j : ∀ j : Fin 3, Measurable fun y : Space =>
            ∫⁻ r in uIoc (1 : ℝ) α, ‖Df j (r • y)‖ₑ ^ (2 : ℝ) := fun j => by
          have hm2 : Measurable fun p : Space × ℝ => ‖Df j (p.2 • p.1)‖ₑ ^ (2 : ℝ) :=
            (((hDf_cont j).comp (continuous_snd.smul continuous_fst)).measurable).enorm.pow_const _
          exact hm2.lintegral_prod_right'
        rw [lintegral_const_mul _ (Finset.measurable_sum _ fun j _ => hm_j j),
          lintegral_finsetSum _ fun j _ => hm_j j]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        have hm2 : AEMeasurable (fun p : Space × ℝ => ‖Df j (p.2 • p.1)‖ₑ ^ (2 : ℝ))
            ((volume : Measure Space).prod ((volume : Measure ℝ).restrict (uIoc 1 α))) :=
          ((((hDf_cont j).comp (continuous_snd.smul continuous_fst)).measurable).enorm.pow_const _).aemeasurable
        exact lintegral_lintegral_swap hm2
    _ ≤ ENNReal.ofReal (3 * R ^ 2 * |α - 1|) *
          ∑ j : Fin 3, ENNReal.ofReal (|α - 1| * Real.exp 3) *
            ∫⁻ x : Space, ‖Df j x‖ₑ ^ (2 : ℝ) := by
        gcongr with j _
        have hr_bd : ∀ r ∈ uIoc (1 : ℝ) α,
            ∫⁻ y : Space, ‖Df j (r • y)‖ₑ ^ (2 : ℝ) ≤
              ENNReal.ofReal (Real.exp 3) * ∫⁻ x : Space, ‖Df j x‖ₑ ^ (2 : ℝ) := by
          intro r hr
          have hr_mem : r ∈ Icc (Real.exp (-1)) (Real.exp 1) := by
            have hu : uIoc (1 : ℝ) α ⊆ uIcc 1 α := uIoc_subset_uIcc
            have h1e : (1 : ℝ) ∈ Icc (Real.exp (-1)) (Real.exp 1) :=
              ⟨Real.exp_le_one_iff.2 (by norm_num), Real.one_le_exp (by norm_num)⟩
            exact (uIcc_subset_Icc h1e ⟨hα1, hα2⟩) (hu hr)
          have hr_pos : 0 < r := (Real.exp_pos (-1)).trans_le hr_mem.1
          have hmap := SpatialScaling.map_dilation hr_pos.ne'
          have hchg : ∫⁻ y : Space, ‖Df j (r • y)‖ₑ ^ (2 : ℝ) =
              ENNReal.ofReal |(r ^ 3)⁻¹| * ∫⁻ x : Space, ‖Df j x‖ₑ ^ (2 : ℝ) := by
            have hm_g : Measurable fun x : Space => ‖Df j x‖ₑ ^ (2 : ℝ) :=
              (hDf_cont j).measurable.enorm.pow_const _
            have := lintegral_map hm_g (measurable_const_smul r) (μ := (volume : Measure Space))
            rw [hmap, lintegral_smul_measure] at this
            exact this.symm
          rw [hchg]
          gcongr
          rw [abs_of_pos (by positivity)]
          have hrinv : r⁻¹ ≤ Real.exp 1 := by
            rw [inv_le_comm₀ hr_pos (Real.exp_pos 1), ← Real.exp_neg]
            exact hr_mem.1
          calc (r ^ 3)⁻¹
              = (r⁻¹) ^ 3 := (inv_pow r 3).symm
            _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by positivity) hrinv 3
            _ = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
        calc ∫⁻ r in uIoc (1 : ℝ) α, ∫⁻ y : Space, ‖Df j (r • y)‖ₑ ^ (2 : ℝ)
            ≤ ∫⁻ _r in uIoc (1 : ℝ) α,
                ENNReal.ofReal (Real.exp 3) * ∫⁻ x : Space, ‖Df j x‖ₑ ^ (2 : ℝ) :=
              setLIntegral_mono' measurableSet_uIoc hr_bd
          _ = (ENNReal.ofReal (Real.exp 3) * ∫⁻ x : Space, ‖Df j x‖ₑ ^ (2 : ℝ)) *
                volume (uIoc (1 : ℝ) α) := by simp
          _ = ENNReal.ofReal (|α - 1| * Real.exp 3) * ∫⁻ x : Space, ‖Df j x‖ₑ ^ (2 : ℝ) := by
              rw [Real.volume_uIoc, mul_comm, ← mul_assoc,
                ← ENNReal.ofReal_mul (abs_nonneg _)]
    _ = ENNReal.ofReal (3 * Real.exp 3 * (R * |α - 1|) ^ 2) *
          ∑ j : Fin 3, ∫⁻ x : Space, ‖Df j x‖ₑ ^ (2 : ℝ) := by
        rw [← Finset.mul_sum, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

private theorem lintegral_mollification_enorm_sq_le (φ : ContDiffBump (0 : Space))
    {h : SpatialField} (hh : MemLp h 2 volume) :
    ∫⁻ y : Space, ‖SobolevEmbedding.mollification φ h y‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ y : Space, ‖h y‖ₑ ^ (2 : ℝ) := by
  have hmoll := SobolevEmbedding.mollification_eLpNorm_le φ h hh
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat] at hmoll
  have hpow := ENNReal.rpow_le_rpow hmoll (by norm_num : (0 : ℝ) ≤ 2)
  rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_one] at hpow

theorem quasiMeasurePreserving_smul_space {α : ℝ} (hα : α ≠ 0) :
    QuasiMeasurePreserving (fun y : Space => α • y) volume volume := by
  refine ⟨measurable_const_smul α, ?_⟩
  rw [SpatialScaling.map_dilation hα]
  exact Measure.smul_absolutelyContinuous

theorem lintegral_closedBall_smul_sub_sq_le {f : SpatialField} {g : Fin 3 → SpatialField}
    (hf : MemLp f 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (hd : ∀ j, HasWeakSpatialDerivative j f (g j))
    {R α : ℝ} (hR : 0 ≤ R) (hα1 : Real.exp (-1) ≤ α) (hα2 : α ≤ Real.exp 1) :
    ∫⁻ y in Metric.closedBall (0 : Space) R, ‖f (α • y) - f y‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (3 * Real.exp 3 * (R * |α - 1|) ^ 2) *
        ∑ j : Fin 3, ∫⁻ y : Space, ‖g j y‖ₑ ^ (2 : ℝ) := by
  obtain ⟨fn, hfn⟩ : ∃ fn : ℕ → SpatialField,
      ∀ n, fn n = SobolevEmbedding.mollification (SobolevEmbedding.shrinkingMollifier n) f :=
    ⟨_, fun _ => rfl⟩
  have hfn_smooth : ∀ n, ContDiff ℝ ∞ (fn n) := fun n => by
    rw [hfn n]
    exact SobolevEmbedding.mollification_smooth (SobolevEmbedding.shrinkingMollifier n) f hf
  have hα_pos : 0 < α := (Real.exp_pos (-1)).trans_le hα1
  have hlim1 : ∀ᵐ y ∂(volume : Measure Space), Tendsto (fun n => fn n y) atTop (𝓝 (f y)) := by
    simpa only [hfn] using SobolevEmbedding.mollification_ae_tendsto f hf
  have hlim2 : ∀ᵐ y ∂(volume : Measure Space),
      Tendsto (fun n => fn n (α • y)) atTop (𝓝 (f (α • y))) :=
    (quasiMeasurePreserving_smul_space hα_pos.ne').ae hlim1
  let B := Metric.closedBall (0 : Space) R
  have hae_B : ∀ᵐ y ∂((volume : Measure Space).restrict B),
      ‖f (α • y) - f y‖ₑ ^ (2 : ℝ) =
        liminf (fun n => ‖fn n (α • y) - fn n y‖ₑ ^ (2 : ℝ)) atTop := by
    filter_upwards [ae_restrict_of_ae (hlim2.and hlim1)] with y ⟨h2, h1⟩
    have ht : Tendsto (fun n => ‖fn n (α • y) - fn n y‖ₑ ^ (2 : ℝ)) atTop
        (𝓝 (‖f (α • y) - f y‖ₑ ^ (2 : ℝ))) :=
      ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto _).comp
        ((continuous_enorm.tendsto _).comp (h2.sub h1))
    exact ht.liminf_eq.symm
  have hm_n : ∀ n, Measurable (fun y : Space => ‖fn n (α • y) - fn n y‖ₑ ^ (2 : ℝ)) := fun n =>
    ((((hfn_smooth n).continuous.comp (continuous_const_smul α)).sub
      (hfn_smooth n).continuous).measurable).enorm.pow_const _
  have hbound_n : ∀ n,
      ∫⁻ y in B, ‖fn n (α • y) - fn n y‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (3 * Real.exp 3 * (R * |α - 1|) ^ 2) *
          ∑ j : Fin 3, ∫⁻ y : Space, ‖g j y‖ₑ ^ (2 : ℝ) := by
    intro n
    refine (smooth_lintegral_closedBall_smul_sub_sq_le (hfn_smooth n) hR hα1 hα2).trans ?_
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) zero_le
    have hcongr : ∫⁻ y : Space, ‖fderiv ℝ (fn n) y (coordinateVector j)‖ₑ ^ (2 : ℝ) =
        ∫⁻ y : Space, ‖SobolevEmbedding.mollification
          (SobolevEmbedding.shrinkingMollifier n) (g j) y‖ₑ ^ (2 : ℝ) := by
      refine lintegral_congr fun y => ?_
      rw [hfn n, SobolevEmbedding.mollification_derivative (hd j) hf
        (SobolevEmbedding.shrinkingMollifier n) y]
    rw [hcongr]
    exact lintegral_mollification_enorm_sq_le (SobolevEmbedding.shrinkingMollifier n) (hg j)
  calc ∫⁻ y in B, ‖f (α • y) - f y‖ₑ ^ (2 : ℝ)
      = ∫⁻ y in B, liminf (fun n => ‖fn n (α • y) - fn n y‖ₑ ^ (2 : ℝ)) atTop :=
        lintegral_congr_ae hae_B
    _ ≤ liminf (fun n => ∫⁻ y in B, ‖fn n (α • y) - fn n y‖ₑ ^ (2 : ℝ)) atTop :=
        lintegral_liminf_le hm_n
    _ ≤ ENNReal.ofReal (3 * Real.exp 3 * (R * |α - 1|) ^ 2) *
          ∑ j : Fin 3, ∫⁻ y : Space, ‖g j y‖ₑ ^ (2 : ℝ) :=
        liminf_le_of_frequently_le (Eventually.of_forall hbound_n).frequently

/-! ### 5. Cylindrical vertical shear `shearZ` and `H¹` bound -/

/-- Vertical shear `y ↦ y + (k * radius y) • e_2` preserving `(y 0, y 1)` and shifting `y 2`. -/
def shearZ (k : ℝ) (y : Space) : Space :=
  y + (k * B0220.radius y) • coordinateVector 2

@[simp] theorem shearZ_apply_zero (k : ℝ) (y : Space) : shearZ k y 0 = y 0 := by
  simp [shearZ, coordinateVector]

@[simp] theorem shearZ_apply_one (k : ℝ) (y : Space) : shearZ k y 1 = y 1 := by
  simp [shearZ, coordinateVector]

@[simp] theorem shearZ_apply_two (k : ℝ) (y : Space) :
    shearZ k y 2 = y 2 + k * B0220.radius y := by
  simp [shearZ, coordinateVector]

@[simp] theorem radius_shearZ (k : ℝ) (y : Space) :
    B0220.radius (shearZ k y) = B0220.radius y := by
  simp [B0220.radius]

theorem continuous_shearZ (k : ℝ) : Continuous (shearZ k) := by
  unfold shearZ
  exact continuous_id.add ((continuous_const.mul B0220.continuous_radius).smul continuous_const)

theorem measurePreserving_shearZ (k : ℝ) :
    MeasurePreserving (shearZ k) (volume : Measure Space) (volume : Measure Space) := by
  have hm : Measurable (shearZ k) := (continuous_shearZ k).measurable
  refine ⟨hm, Measure.ext fun A hA => ?_⟩
  rw [Measure.map_apply hm hA, ← lintegral_indicator_one hA,
    ← lintegral_indicator_one (hm hA)]
  have hcomp : ∀ y : Space,
      (shearZ k ⁻¹' A).indicator (1 : Space → ℝ≥0∞) y =
        A.indicator (1 : Space → ℝ≥0∞) (shearZ k y) := fun _ => rfl
  rw [lintegral_congr hcomp]
  set F : Space → ℝ≥0∞ := A.indicator 1
  have hF : Measurable F := measurable_one.indicator hA
  set g1 : (Fin 3 → ℝ) → ℝ≥0∞ := fun v => F (shearZ k (WithLp.toLp 2 v))
  set g0 : (Fin 3 → ℝ) → ℝ≥0∞ := fun v => F (WithLp.toLp 2 v)
  have htoLp : Measurable (WithLp.toLp 2 : (Fin 3 → ℝ) → Space) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable
  have hg1 : Measurable g1 := hF.comp (hm.comp htoLp)
  have hg0 : Measurable g0 := hF.comp htoLp
  have hmp_of := PiLp.volume_preserving_ofLp (Fin 3)
  have eL : ∫⁻ y : Space, F (shearZ k y) = ∫⁻ v : Fin 3 → ℝ, g1 v :=
    hmp_of.lintegral_comp hg1
  have eR : ∫⁻ y : Space, F y = ∫⁻ v : Fin 3 → ℝ, g0 v :=
    hmp_of.lintegral_comp hg0
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)
  have he : MeasurePreserving e.symm volume volume :=
    MeasurePreserving.symm e (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2))
  rw [eL, eR, ← he.lintegral_comp hg1, ← he.lintegral_comp hg0]
  have he0 : ∀ (a : ℝ) (b : Fin 2 → ℝ), e.symm (a, b) 0 = b 0 := fun _ _ => rfl
  have he1 : ∀ (a : ℝ) (b : Fin 2 → ℝ), e.symm (a, b) 1 = b 1 := fun _ _ => rfl
  have he2 : ∀ (a : ℝ) (b : Fin 2 → ℝ), e.symm (a, b) 2 = a := fun _ _ => rfl
  have hsheareq : ∀ u : ℝ × (Fin 2 → ℝ),
      shearZ k (WithLp.toLp 2 (e.symm u)) =
        WithLp.toLp 2 (e.symm (u.1 + k * √(u.2 0 ^ 2 + u.2 1 ^ 2), u.2)) := by
    rintro ⟨z, w⟩
    ext i
    fin_cases i <;> simp [B0220.radius, he0, he1, he2]
  have hcongr : (fun u : ℝ × (Fin 2 → ℝ) => g1 (e.symm u)) =
      fun u => g0 (e.symm (u.1 + k * √(u.2 0 ^ 2 + u.2 1 ^ 2), u.2)) := by
    funext u
    dsimp [g1, g0]
    rw [hsheareq u]
  have hm_sh_prod : AEMeasurable
      (fun u : ℝ × (Fin 2 → ℝ) => g0 (e.symm (u.1 + k * √(u.2 0 ^ 2 + u.2 1 ^ 2), u.2)))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) :=
    ((hg0.comp e.symm.measurable).comp
      ((measurable_fst.add (measurable_const.mul
        ((by fun_prop : Continuous fun u : ℝ × (Fin 2 → ℝ) =>
          √(u.2 0 ^ 2 + u.2 1 ^ 2)).measurable))).prodMk measurable_snd)).aemeasurable
  have hm_id_prod : AEMeasurable (fun u : ℝ × (Fin 2 → ℝ) => g0 (e.symm u))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) :=
    (hg0.comp e.symm.measurable).aemeasurable
  rw [hcongr, Measure.volume_eq_prod,
    lintegral_prod_symm
      (fun u : ℝ × (Fin 2 → ℝ) => g0 (e.symm (u.1 + k * √(u.2 0 ^ 2 + u.2 1 ^ 2), u.2)))
      hm_sh_prod,
    lintegral_prod_symm (fun u : ℝ × (Fin 2 → ℝ) => g0 (e.symm u)) hm_id_prod]
  refine lintegral_congr fun w => ?_
  exact lintegral_add_right_eq_self (fun z : ℝ => g0 (e.symm (z, w)))
    (k * √(w 0 ^ 2 + w 1 ^ 2))

theorem smooth_lintegral_shearZ_sub_sq_le {f : SpatialField} (hf : ContDiff ℝ ∞ f)
    {S : Set Space} (hS : MeasurableSet S) {k Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hk : ∀ y ∈ S, |k * B0220.radius y| ≤ Δ) :
    ∫⁻ y in S, ‖f (shearZ k y) - f y‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (2 * Δ ^ 2) *
        ∫⁻ y : Space, ‖fderiv ℝ f y (coordinateVector 2)‖ₑ ^ (2 : ℝ) := by
  set D2 : SpatialField := fun y => fderiv ℝ f y (coordinateVector 2)
  have hD2_cont : Continuous D2 :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpt : ∀ y ∈ S,
      ‖f (shearZ k y) - f y‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal Δ * ∫⁻ r in Icc (-Δ) Δ, ‖D2 (y + r • coordinateVector 2)‖ₑ ^ (2 : ℝ) := by
    intro y hy
    set d : ℝ := k * B0220.radius y
    have hdΔ : |d| ≤ Δ := hk y hy
    have hderiv : ∀ r : ℝ, HasDerivAt (fun r : ℝ => f (y + r • coordinateVector 2))
        (D2 (y + r • coordinateVector 2)) r := by
      intro r
      have hr : HasDerivAt (fun r : ℝ => y + r • coordinateVector 2) (coordinateVector 2) r := by
        simpa using ((hasDerivAt_id r).smul_const (coordinateVector 2)).const_add y
      exact (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt r hr
    have hcont_r : Continuous (fun r : ℝ => D2 (y + r • coordinateVector 2)) :=
      hD2_cont.comp (continuous_const.add (continuous_id.smul continuous_const))
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hderiv r)
      (hcont_r.intervalIntegrable 0 d)
    rw [zero_smul, add_zero] at hftc
    have hnorm_le : ‖f (shearZ k y) - f y‖ ≤
        ∫ r in uIoc (0 : ℝ) d, ‖D2 (y + r • coordinateVector 2)‖ := by
      change ‖f (y + d • coordinateVector 2) - f y‖ ≤ _
      rw [← hftc]
      exact intervalIntegral.norm_integral_le_integral_norm_uIoc
    have hcs := sq_setIntegral_uIoc_le (a := 0) (b := d) hcont_r.norm
    rw [sub_zero] at hcs
    have hsub_Icc : uIoc (0 : ℝ) d ⊆ Icc (-Δ) Δ := by
      have h0Δ : (0 : ℝ) ∈ Icc (-Δ) Δ := ⟨by linarith, hΔ⟩
      have hd_mem : d ∈ Icc (-Δ) Δ := abs_le.1 hdΔ
      exact uIoc_subset_uIcc.trans (uIcc_subset_Icc h0Δ hd_mem)
    have hnorm_sq : ‖f (shearZ k y) - f y‖ ^ 2 ≤
        Δ * ∫ r in uIoc (0 : ℝ) d, ‖D2 (y + r • coordinateVector 2)‖ ^ 2 := by
      calc ‖f (shearZ k y) - f y‖ ^ 2
          ≤ (∫ r in uIoc (0 : ℝ) d, ‖D2 (y + r • coordinateVector 2)‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2
        _ ≤ |d| * ∫ r in uIoc (0 : ℝ) d, ‖D2 (y + r • coordinateVector 2)‖ ^ 2 := hcs
        _ ≤ Δ * ∫ r in uIoc (0 : ℝ) d, ‖D2 (y + r • coordinateVector 2)‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hdΔ
              (setIntegral_nonneg measurableSet_uIoc fun _ _ => sq_nonneg _)
    have hD2_sq_int : IntegrableOn (fun r : ℝ => ‖D2 (y + r • coordinateVector 2)‖ ^ 2)
        (uIoc 0 d) := (hcont_r.norm.pow 2).integrableOn_uIoc
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
    calc ENNReal.ofReal (‖f (shearZ k y) - f y‖ ^ 2)
        ≤ ENNReal.ofReal (Δ * ∫ r in uIoc (0 : ℝ) d, ‖D2 (y + r • coordinateVector 2)‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal hnorm_sq
      _ = ENNReal.ofReal Δ *
            ∫⁻ r in uIoc (0 : ℝ) d, ‖D2 (y + r • coordinateVector 2)‖ₑ ^ (2 : ℝ) := by
          rw [ENNReal.ofReal_mul hΔ,
            ofReal_integral_eq_lintegral_ofReal hD2_sq_int
              (Eventually.of_forall fun _ => sq_nonneg _)]
          congr 1
          refine lintegral_congr fun r => ?_
          rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
            Real.rpow_two]
      _ ≤ ENNReal.ofReal Δ *
            ∫⁻ r in Icc (-Δ) Δ, ‖D2 (y + r • coordinateVector 2)‖ₑ ^ (2 : ℝ) :=
          mul_le_mul_of_nonneg_left (lintegral_mono_set hsub_Icc) zero_le
  have hm_prod : AEMeasurable
      (fun p : Space × ℝ => ‖D2 (p.1 + p.2 • coordinateVector 2)‖ₑ ^ (2 : ℝ))
      ((volume : Measure Space).prod ((volume : Measure ℝ).restrict (Icc (-Δ) Δ))) :=
    (((hD2_cont.comp (continuous_fst.add
      (continuous_snd.smul continuous_const))).measurable).enorm.pow_const _).aemeasurable
  calc ∫⁻ y in S, ‖f (shearZ k y) - f y‖ₑ ^ (2 : ℝ)
      ≤ ∫⁻ y in S, ENNReal.ofReal Δ *
          ∫⁻ r in Icc (-Δ) Δ, ‖D2 (y + r • coordinateVector 2)‖ₑ ^ (2 : ℝ) :=
        setLIntegral_mono' hS hpt
    _ ≤ ∫⁻ y : Space, ENNReal.ofReal Δ *
          ∫⁻ r in Icc (-Δ) Δ, ‖D2 (y + r • coordinateVector 2)‖ₑ ^ (2 : ℝ) :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal Δ *
          ∫⁻ r in Icc (-Δ) Δ, ∫⁻ y : Space, ‖D2 (y + r • coordinateVector 2)‖ₑ ^ (2 : ℝ) := by
        have hm_y : Measurable fun y : Space =>
            ∫⁻ r in Icc (-Δ) Δ, ‖D2 (y + r • coordinateVector 2)‖ₑ ^ (2 : ℝ) :=
          (((hD2_cont.comp (continuous_fst.add
            (continuous_snd.smul continuous_const))).measurable).enorm.pow_const _).lintegral_prod_right'
        rw [lintegral_const_mul _ hm_y, lintegral_lintegral_swap hm_prod]
    _ = ENNReal.ofReal Δ *
          ∫⁻ _r in Icc (-Δ) Δ, ∫⁻ x : Space, ‖D2 x‖ₑ ^ (2 : ℝ) := by
        congr 1
        refine lintegral_congr fun r => ?_
        exact lintegral_add_right_eq_self (fun x : Space => ‖D2 x‖ₑ ^ (2 : ℝ))
          (r • coordinateVector 2)
    _ = ENNReal.ofReal (2 * Δ ^ 2) * ∫⁻ x : Space, ‖D2 x‖ₑ ^ (2 : ℝ) := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_neg_eq_add,
          ← two_mul, mul_comm (∫⁻ x : Space, ‖D2 x‖ₑ ^ (2 : ℝ)), ← mul_assoc,
          ← ENNReal.ofReal_mul hΔ]
        congr 2
        ring

theorem lintegral_shearZ_sub_sq_le {f g2 : SpatialField}
    (hf : MemLp f 2 volume) (hg2 : MemLp g2 2 volume)
    (hd2 : HasWeakSpatialDerivative 2 f g2)
    {S : Set Space} (hS : MeasurableSet S) {k Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hk : ∀ y ∈ S, |k * B0220.radius y| ≤ Δ) :
    ∫⁻ y in S, ‖f (shearZ k y) - f y‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (2 * Δ ^ 2) * ∫⁻ y : Space, ‖g2 y‖ₑ ^ (2 : ℝ) := by
  let fn : ℕ → SpatialField := fun n =>
    SobolevEmbedding.mollification (SobolevEmbedding.shrinkingMollifier n) f
  have hfn_smooth : ∀ n, ContDiff ℝ ∞ (fn n) := fun n =>
    SobolevEmbedding.mollification_smooth (SobolevEmbedding.shrinkingMollifier n) f hf
  have hlim1 : ∀ᵐ y ∂(volume : Measure Space), Tendsto (fun n => fn n y) atTop (𝓝 (f y)) :=
    SobolevEmbedding.mollification_ae_tendsto f hf
  have hlim2 : ∀ᵐ y ∂(volume : Measure Space),
      Tendsto (fun n => fn n (shearZ k y)) atTop (𝓝 (f (shearZ k y))) :=
    (measurePreserving_shearZ k).quasiMeasurePreserving.ae hlim1
  have hae_S : ∀ᵐ y ∂((volume : Measure Space).restrict S),
      ‖f (shearZ k y) - f y‖ₑ ^ (2 : ℝ) =
        liminf (fun n => ‖fn n (shearZ k y) - fn n y‖ₑ ^ (2 : ℝ)) atTop := by
    filter_upwards [ae_restrict_of_ae (hlim2.and hlim1)] with y ⟨h2, h1⟩
    have ht : Tendsto (fun n => ‖fn n (shearZ k y) - fn n y‖ₑ ^ (2 : ℝ)) atTop
        (𝓝 (‖f (shearZ k y) - f y‖ₑ ^ (2 : ℝ))) :=
      ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto _).comp
        ((continuous_enorm.tendsto _).comp (h2.sub h1))
    exact ht.liminf_eq.symm
  have hm_n : ∀ n, Measurable (fun y : Space => ‖fn n (shearZ k y) - fn n y‖ₑ ^ (2 : ℝ)) :=
    fun n => ((((hfn_smooth n).continuous.comp (continuous_shearZ k)).sub
      (hfn_smooth n).continuous).measurable).enorm.pow_const _
  have hbound_n : ∀ n,
      ∫⁻ y in S, ‖fn n (shearZ k y) - fn n y‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (2 * Δ ^ 2) * ∫⁻ y : Space, ‖g2 y‖ₑ ^ (2 : ℝ) := by
    intro n
    refine (smooth_lintegral_shearZ_sub_sq_le (hfn_smooth n) hS hΔ hk).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    have hcongr : ∫⁻ y : Space, ‖fderiv ℝ (fn n) y (coordinateVector 2)‖ₑ ^ (2 : ℝ) =
        ∫⁻ y : Space, ‖SobolevEmbedding.mollification
          (SobolevEmbedding.shrinkingMollifier n) g2 y‖ₑ ^ (2 : ℝ) := by
      refine lintegral_congr fun y => ?_
      rw [SobolevEmbedding.mollification_derivative hd2 hf
        (SobolevEmbedding.shrinkingMollifier n) y]
    rw [hcongr]
    exact lintegral_mollification_enorm_sq_le (SobolevEmbedding.shrinkingMollifier n) hg2
  calc ∫⁻ y in S, ‖f (shearZ k y) - f y‖ₑ ^ (2 : ℝ)
      = ∫⁻ y in S, liminf (fun n => ‖fn n (shearZ k y) - fn n y‖ₑ ^ (2 : ℝ)) atTop :=
        lintegral_congr_ae hae_S
    _ ≤ liminf (fun n => ∫⁻ y in S, ‖fn n (shearZ k y) - fn n y‖ₑ ^ (2 : ℝ)) atTop :=
        lintegral_liminf_le hm_n
    _ ≤ ENNReal.ofReal (2 * Δ ^ 2) * ∫⁻ y : Space, ‖g2 y‖ₑ ^ (2 : ℝ) :=
        liminf_le_of_frequently_le (Eventually.of_forall hbound_n).frequently

/-! ### 6. Integrated `phaseVol P` corollaries for `prodLpEquiv.symm v` -/

theorem lintegral_Yq_slice_enorm_sq {P : ℝ} [Fact (0 < P)] (u : Yq P 2) :
    ∫⁻ τ, (∫⁻ y : Space, ‖(u τ : Space → CVec3) y‖ₑ ^ (2 : ℝ))
        ∂(AddCircle.haarAddCircle (T := P)) = ENNReal.ofReal (‖u‖ ^ 2) := by
  have h1 : ∀ τ : AddCircle P,
      ∫⁻ y : Space, ‖(u τ : Space → CVec3) y‖ₑ ^ (2 : ℝ) = ‖u τ‖ₑ ^ (2 : ℝ) := by
    intro τ
    rw [lintegral_enorm_sq_eq_ofReal_norm_sq (u τ), ← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  simp_rw [h1]
  exact lintegral_enorm_sq_eq_ofReal_norm_sq u

theorem lintegral_phaseVol_smul_sub_sq_le {P : ℝ} [Fact (0 < P)] {v : Yq P 2}
    {g_diss : Fin 3 → Yq P 2} (hg : HasGrad v g_diss)
    {S : Set Space} (hS : MeasurableSet S) {R α : ℝ} (hR : 0 ≤ R)
    (hSR : S ⊆ Metric.closedBall (0 : Space) R)
    (hα1 : Real.exp (-1) ≤ α) (hα2 : α ≤ Real.exp 1) :
    ∫⁻ z in univ ×ˢ S,
        ‖(prodLpEquiv.symm v : AddCircle P × Space → CVec3) (z.1, α • z.2) -
          (prodLpEquiv.symm v : AddCircle P × Space → CVec3) z‖ₑ ^ (2 : ℝ) ∂(phaseVol P) ≤
      ENNReal.ofReal (3 * Real.exp 3 * (R * |α - 1|) ^ 2 * ∑ j : Fin 3, ‖g_diss j‖ ^ 2) := by
  let V₀ : AddCircle P × Space → CVec3 := ⇑(prodLpEquiv.symm v)
  have hα_pos : 0 < α := (Real.exp_pos (-1)).trans_le hα1
  have hmV : AEStronglyMeasurable V₀ (phaseVol P) := Lp.aestronglyMeasurable (prodLpEquiv.symm v)
  have hq_α : QuasiMeasurePreserving (fun y : Space => α • y) volume volume :=
    quasiMeasurePreserving_smul_space hα_pos.ne'
  have hmp_α : QuasiMeasurePreserving (fun z : AddCircle P × Space => (z.1, α • z.2))
      (phaseVol P) (phaseVol P) :=
    MeasureTheory.QuasiMeasurePreserving.prodMap
      (QuasiMeasurePreserving.id (AddCircle.haarAddCircle (T := P))) hq_α
  have hm_int : AEMeasurable (fun z : AddCircle P × Space =>
      ‖V₀ (z.1, α • z.2) - V₀ z‖ₑ ^ (2 : ℝ)) ((phaseVol P).restrict (univ ×ˢ S)) :=
    (((hmV.comp_quasiMeasurePreserving hmp_α).sub hmV).enorm.pow_const (2 : ℝ)).restrict
  have hprod_eq : (phaseVol P).restrict (univ ×ˢ S) =
      (AddCircle.haarAddCircle (T := P)).prod ((volume : Measure Space).restrict S) := by
    rw [phaseVol, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [hprod_eq, lintegral_prod _ (hprod_eq ▸ hm_int)]
  have hae : ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
      ∫⁻ y in S, ‖V₀ (τ, α • y) - V₀ (τ, y)‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (3 * Real.exp 3 * (R * |α - 1|) ^ 2) *
          ∑ j : Fin 3, ∫⁻ y : Space, ‖(g_diss j τ : Space → CVec3) y‖ₑ ^ (2 : ℝ) := by
    filter_upwards [prodLpEquiv_symm_ae v, ae_slice_weakSpatialDeriv hg] with τ hV hslice
    have hVα : (fun y : Space => V₀ (τ, α • y)) =ᵐ[volume]
        fun y => (v τ : Space → CVec3) (α • y) :=
      hq_α.ae_eq_comp hV
    have hcongr : ∫⁻ y in S, ‖V₀ (τ, α • y) - V₀ (τ, y)‖ₑ ^ (2 : ℝ) =
        ∫⁻ y in S, ‖(v τ : Space → CVec3) (α • y) - (v τ : Space → CVec3) y‖ₑ ^ (2 : ℝ) := by
      refine setLIntegral_congr_fun_ae hS ?_
      filter_upwards [hVα, hV] with y h1 h2 _
      dsimp only [V₀] at h1 ⊢
      rw [h1, h2]
    rw [hcongr]
    let B := Metric.closedBall (0 : Space) R
    have hleB : ∫⁻ y in S, ‖(v τ : Space → CVec3) (α • y) - (v τ : Space → CVec3) y‖ₑ ^ (2 : ℝ) ≤
        ∫⁻ y in B, ‖(v τ : Space → CVec3) (α • y) - (v τ : Space → CVec3) y‖ₑ ^ (2 : ℝ) :=
      lintegral_mono_set hSR
    refine hleB.trans ?_
    have hsplit : ∀ y : Space,
        ‖(v τ : Space → CVec3) (α • y) - (v τ : Space → CVec3) y‖ₑ ^ (2 : ℝ) =
          ‖reV ((v τ : Space → CVec3) (α • y)) - reV ((v τ : Space → CVec3) y)‖ₑ ^ (2 : ℝ) +
            ‖imV ((v τ : Space → CVec3) (α • y)) - imV ((v τ : Space → CVec3) y)‖ₑ ^ (2 : ℝ) := by
      intro y
      rw [enorm_cvec3_sq_eq_re_im, map_sub, map_sub]
    simp_rw [hsplit]
    have hmR : AEMeasurable (fun y : Space =>
        ‖reV ((v τ : Space → CVec3) (α • y)) - reV ((v τ : Space → CVec3) y)‖ₑ ^ (2 : ℝ))
        ((volume : Measure Space).restrict B) :=
      ((((memLp_reV_comp (u := v τ)).1.comp_quasiMeasurePreserving hq_α).sub
        (memLp_reV_comp (u := v τ)).1).enorm.pow_const _).restrict
    rw [lintegral_add_left' hmR]
    have hbR := lintegral_closedBall_smul_sub_sq_le (memLp_reV_comp (u := v τ))
      (fun j => memLp_reV_comp (u := g_diss j τ)) (fun j => (hslice j).1) hR hα1 hα2
    have hbI := lintegral_closedBall_smul_sub_sq_le (memLp_imV_comp (u := v τ))
      (fun j => memLp_imV_comp (u := g_diss j τ)) (fun j => (hslice j).2) hR hα1 hα2
    calc (∫⁻ y in B, ‖reV ((v τ : Space → CVec3) (α • y)) -
              reV ((v τ : Space → CVec3) y)‖ₑ ^ (2 : ℝ)) +
            ∫⁻ y in B, ‖imV ((v τ : Space → CVec3) (α • y)) -
              imV ((v τ : Space → CVec3) y)‖ₑ ^ (2 : ℝ)
        ≤ ENNReal.ofReal (3 * Real.exp 3 * (R * |α - 1|) ^ 2) *
            (∑ j : Fin 3, ∫⁻ y : Space, ‖reV ((g_diss j τ : Space → CVec3) y)‖ₑ ^ (2 : ℝ)) +
          ENNReal.ofReal (3 * Real.exp 3 * (R * |α - 1|) ^ 2) *
            (∑ j : Fin 3, ∫⁻ y : Space, ‖imV ((g_diss j τ : Space → CVec3) y)‖ₑ ^ (2 : ℝ)) :=
          add_le_add hbR hbI
      _ = ENNReal.ofReal (3 * Real.exp 3 * (R * |α - 1|) ^ 2) *
            ∑ j : Fin 3, ∫⁻ y : Space, ‖(g_diss j τ : Space → CVec3) y‖ₑ ^ (2 : ℝ) := by
          rw [← mul_add, ← Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← lintegral_add_left'
            ((memLp_reV_comp (u := g_diss j τ)).1.enorm.pow_const _)]
          refine lintegral_congr fun y => (enorm_cvec3_sq_eq_re_im _).symm
  have hm_g : ∀ j : Fin 3, AEMeasurable (fun τ : AddCircle P =>
      ∫⁻ y : Space, ‖(g_diss j τ : Space → CVec3) y‖ₑ ^ (2 : ℝ))
      (AddCircle.haarAddCircle (T := P)) := fun j => by
    have h1 : (fun τ : AddCircle P => ∫⁻ y : Space, ‖(g_diss j τ : Space → CVec3) y‖ₑ ^ (2 : ℝ)) =
        fun τ => ‖g_diss j τ‖ₑ ^ (2 : ℝ) := by
      funext τ
      rw [lintegral_enorm_sq_eq_ofReal_norm_sq (g_diss j τ), ← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
    rw [h1]
    exact (Lp.aestronglyMeasurable (g_diss j)).enorm.pow_const _
  calc ∫⁻ τ, (∫⁻ y in S, ‖V₀ (τ, α • y) - V₀ (τ, y)‖ₑ ^ (2 : ℝ))
          ∂(AddCircle.haarAddCircle (T := P))
      ≤ ∫⁻ τ, ENNReal.ofReal (3 * Real.exp 3 * (R * |α - 1|) ^ 2) *
          (∑ j : Fin 3, ∫⁻ y : Space, ‖(g_diss j τ : Space → CVec3) y‖ₑ ^ (2 : ℝ))
          ∂(AddCircle.haarAddCircle (T := P)) := lintegral_mono_ae hae
    _ = ENNReal.ofReal (3 * Real.exp 3 * (R * |α - 1|) ^ 2) *
          ∑ j : Fin 3, ∫⁻ τ, (∫⁻ y : Space, ‖(g_diss j τ : Space → CVec3) y‖ₑ ^ (2 : ℝ))
            ∂(AddCircle.haarAddCircle (T := P)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum' _ fun j _ => hm_g j]
    _ = ENNReal.ofReal (3 * Real.exp 3 * (R * |α - 1|) ^ 2 * ∑ j : Fin 3, ‖g_diss j‖ ^ 2) := by
        simp_rw [lintegral_Yq_slice_enorm_sq]
        rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _,
          ← ENNReal.ofReal_mul (by positivity)]

theorem lintegral_phaseVol_shearZ_sub_sq_le {P : ℝ} [Fact (0 < P)] {v : Yq P 2}
    {g_diss : Fin 3 → Yq P 2} (hg : HasGrad v g_diss)
    {S : Set Space} (hS : MeasurableSet S) {k Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hk : ∀ y ∈ S, |k * B0220.radius y| ≤ Δ) :
    ∫⁻ z in univ ×ˢ S,
        ‖(prodLpEquiv.symm v : AddCircle P × Space → CVec3) (z.1, shearZ k z.2) -
          (prodLpEquiv.symm v : AddCircle P × Space → CVec3) z‖ₑ ^ (2 : ℝ) ∂(phaseVol P) ≤
      ENNReal.ofReal (2 * Δ ^ 2 * ‖g_diss 2‖ ^ 2) := by
  let V₀ : AddCircle P × Space → CVec3 := ⇑(prodLpEquiv.symm v)
  have hmV : AEStronglyMeasurable V₀ (phaseVol P) := Lp.aestronglyMeasurable (prodLpEquiv.symm v)
  have hmp_sh : QuasiMeasurePreserving (fun z : AddCircle P × Space => (z.1, shearZ k z.2))
      (phaseVol P) (phaseVol P) :=
    MeasureTheory.QuasiMeasurePreserving.prodMap
      (QuasiMeasurePreserving.id (AddCircle.haarAddCircle (T := P)))
      (measurePreserving_shearZ k).quasiMeasurePreserving
  have hm_int : AEMeasurable (fun z : AddCircle P × Space =>
      ‖V₀ (z.1, shearZ k z.2) - V₀ z‖ₑ ^ (2 : ℝ)) ((phaseVol P).restrict (univ ×ˢ S)) :=
    (((hmV.comp_quasiMeasurePreserving hmp_sh).sub hmV).enorm.pow_const (2 : ℝ)).restrict
  have hprod_eq : (phaseVol P).restrict (univ ×ˢ S) =
      (AddCircle.haarAddCircle (T := P)).prod ((volume : Measure Space).restrict S) := by
    rw [phaseVol, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [hprod_eq, lintegral_prod _ (hprod_eq ▸ hm_int)]
  have hae : ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
      ∫⁻ y in S, ‖V₀ (τ, shearZ k y) - V₀ (τ, y)‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (2 * Δ ^ 2) *
          ∫⁻ y : Space, ‖(g_diss 2 τ : Space → CVec3) y‖ₑ ^ (2 : ℝ) := by
    filter_upwards [prodLpEquiv_symm_ae v, ae_slice_weakSpatialDeriv hg] with τ hV hslice
    have hVsh : (fun y : Space => V₀ (τ, shearZ k y)) =ᵐ[volume]
        fun y => (v τ : Space → CVec3) (shearZ k y) :=
      (measurePreserving_shearZ k).quasiMeasurePreserving.ae_eq_comp hV
    have hcongr : ∫⁻ y in S, ‖V₀ (τ, shearZ k y) - V₀ (τ, y)‖ₑ ^ (2 : ℝ) =
        ∫⁻ y in S, ‖(v τ : Space → CVec3) (shearZ k y) - (v τ : Space → CVec3) y‖ₑ ^ (2 : ℝ) := by
      refine setLIntegral_congr_fun_ae hS ?_
      filter_upwards [hVsh, hV] with y h1 h2 _
      dsimp only [V₀] at h1 ⊢
      rw [h1, h2]
    rw [hcongr]
    have hsplit : ∀ y : Space,
        ‖(v τ : Space → CVec3) (shearZ k y) - (v τ : Space → CVec3) y‖ₑ ^ (2 : ℝ) =
          ‖reV ((v τ : Space → CVec3) (shearZ k y)) - reV ((v τ : Space → CVec3) y)‖ₑ ^ (2 : ℝ) +
            ‖imV ((v τ : Space → CVec3) (shearZ k y)) -
              imV ((v τ : Space → CVec3) y)‖ₑ ^ (2 : ℝ) := by
      intro y
      rw [enorm_cvec3_sq_eq_re_im, map_sub, map_sub]
    simp_rw [hsplit]
    have hmR : AEMeasurable (fun y : Space =>
        ‖reV ((v τ : Space → CVec3) (shearZ k y)) - reV ((v τ : Space → CVec3) y)‖ₑ ^ (2 : ℝ))
        ((volume : Measure Space).restrict S) :=
      ((((memLp_reV_comp (u := v τ)).1.comp_quasiMeasurePreserving
        (measurePreserving_shearZ k).quasiMeasurePreserving).sub
        (memLp_reV_comp (u := v τ)).1).enorm.pow_const _).restrict
    rw [lintegral_add_left' hmR]
    have hbR := lintegral_shearZ_sub_sq_le (memLp_reV_comp (u := v τ))
      (memLp_reV_comp (u := g_diss 2 τ)) (hslice 2).1 hS hΔ hk
    have hbI := lintegral_shearZ_sub_sq_le (memLp_imV_comp (u := v τ))
      (memLp_imV_comp (u := g_diss 2 τ)) (hslice 2).2 hS hΔ hk
    calc (∫⁻ y in S, ‖reV ((v τ : Space → CVec3) (shearZ k y)) -
              reV ((v τ : Space → CVec3) y)‖ₑ ^ (2 : ℝ)) +
            ∫⁻ y in S, ‖imV ((v τ : Space → CVec3) (shearZ k y)) -
              imV ((v τ : Space → CVec3) y)‖ₑ ^ (2 : ℝ)
        ≤ ENNReal.ofReal (2 * Δ ^ 2) *
            (∫⁻ y : Space, ‖reV ((g_diss 2 τ : Space → CVec3) y)‖ₑ ^ (2 : ℝ)) +
          ENNReal.ofReal (2 * Δ ^ 2) *
            (∫⁻ y : Space, ‖imV ((g_diss 2 τ : Space → CVec3) y)‖ₑ ^ (2 : ℝ)) :=
          add_le_add hbR hbI
      _ = ENNReal.ofReal (2 * Δ ^ 2) *
            ∫⁻ y : Space, ‖(g_diss 2 τ : Space → CVec3) y‖ₑ ^ (2 : ℝ) := by
          rw [← mul_add, ← lintegral_add_left'
            ((memLp_reV_comp (u := g_diss 2 τ)).1.enorm.pow_const _)]
          congr 1
          refine lintegral_congr fun y => (enorm_cvec3_sq_eq_re_im _).symm
  calc ∫⁻ τ, (∫⁻ y in S, ‖V₀ (τ, shearZ k y) - V₀ (τ, y)‖ₑ ^ (2 : ℝ))
          ∂(AddCircle.haarAddCircle (T := P))
      ≤ ∫⁻ τ, ENNReal.ofReal (2 * Δ ^ 2) *
          (∫⁻ y : Space, ‖(g_diss 2 τ : Space → CVec3) y‖ₑ ^ (2 : ℝ))
          ∂(AddCircle.haarAddCircle (T := P)) := lintegral_mono_ae hae
    _ = ENNReal.ofReal (2 * Δ ^ 2) *
          ∫⁻ τ, (∫⁻ y : Space, ‖(g_diss 2 τ : Space → CVec3) y‖ₑ ^ (2 : ℝ))
            ∂(AddCircle.haarAddCircle (T := P)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (2 * Δ ^ 2 * ‖g_diss 2‖ ^ 2) := by
        rw [lintegral_Yq_slice_enorm_sq, ← ENNReal.ofReal_mul (by positivity)]

end UnforcedLeray.Short.PartIIa.N05FlowAux
