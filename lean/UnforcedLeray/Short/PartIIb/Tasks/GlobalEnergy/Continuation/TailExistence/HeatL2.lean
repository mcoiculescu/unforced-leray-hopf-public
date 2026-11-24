import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.Continuation.LinearGlue
import UnforcedLeray.Infra.VolterraEvolution.Kernel
import UnforcedLeray.Lib.HeatCylinder.HeatVecCenteredSelfAdjoint
import UnforcedLeray.Lib.HeatCylinder.HeatL2StrongContinuity
import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeMajorant
import UnforcedLeray.Lib.HeatCylinder.KernelTimeContinuity
import UnforcedLeray.Lib.HeatCylinder.BochnerPath
import UnforcedLeray.Lib.TrainB.P0W1Rough
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Real cylinder heat, Gaussian-gradient, and `H¹_σ(C_c)` operators for `TailExistence`

Self-contained helper submodule for `PartII-b:F7/2/1` (`MeridionalTailExistence`).
Constructs the real cylinder `L²`/`H¹_σ` Banach space `H1Sol c`, translation-average heat and
Gaussian-gradient operators (`centeredHeatVecL2CLM`, `DHeatCLM`, `freeH1CLM`, `duhH1CLM`),
age differentiation of heat inner products (`hasDerivAt_inner_centeredHeatVecL2CLM`), bounded
scalar multiplication operators on `L2v c`, and bridges between `H1Sol c` and `IsCylH1Slice c`.

All declarations live in `namespace UnforcedLeray.Short.IIb.TailExistenceAux`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIb.TailExistenceAux

open UnforcedLeray.Short.IIb
open UnforcedLeray.Cyl (L2v cellμ divFree P0 Vec2)
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.HeatCylinder
open UnforcedLeray.B0284 (heatKernel2)

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-! ## 1. Real / complex slice embeddings and real cylinder predicates -/

/-- Embed a real cylinder slice `Plane → Fin 2 → ℝ` into `Plane → CMerid`. -/
def ofRealSlice (w : B0579.Plane → Fin 2 → ℝ) : B0579.Plane → CMerid :=
  fun y => WithLp.toLp 2 fun i => (w y i : ℂ)

/-- Embed a real profile `Coord → Fin 2 → ℝ` into `CProf`. -/
def ofRealProf (w : Coord → Fin 2 → ℝ) : CProf :=
  fun x => WithLp.toLp 2 fun i => (w x i : ℂ)

/-- Embed a real cylinder slice `Plane → Fin 2 → ℝ` into `Plane → Vec2`. -/
def toVecSlice (w : B0579.Plane → Fin 2 → ℝ) : Plane → Vec2 :=
  fun y => WithLp.toLp 2 (w y)

def eR0 : Vec2 := EuclideanSpace.single 0 (1 : ℝ)
def eR1 : Vec2 := EuclideanSpace.single 1 (1 : ℝ)
def πR (i : Fin 2) : Vec2 →L[ℝ] ℝ := EuclideanSpace.proj i

/-- Real weak `∂_j` derivative on `B0579.cell c` against `B0579.IsCylTest c`. -/
def HasWeakCellDerivR (c : ℝ) (j : Fin 2) (φ g : Plane → ℝ) : Prop :=
  (∀ ψ, B0579.IsCylTest c ψ →
    IntegrableOn (fun y => φ y * B0579.pd j ψ y) (B0579.cell c) ∧
      IntegrableOn (fun y => g y * ψ y) (B0579.cell c)) ∧
  ∀ ψ, B0579.IsCylTest c ψ →
    ∫ y in B0579.cell c, φ y * B0579.pd j ψ y = -∫ y in B0579.cell c, g y * ψ y

/-- Real weak divergence-free condition on `B0579.cell c`. -/
def IsRealCellSolenoidal (c : ℝ) (f : Plane → Vec2) : Prop :=
  ∀ ψ, B0579.IsCylTest c ψ →
    IntegrableOn (fun y => f y 0 * B0579.pd 0 ψ y + f y 1 * B0579.pd 1 ψ y) (B0579.cell c) ∧
      ∫ y in B0579.cell c, (f y 0 * B0579.pd 0 ψ y + f y 1 * B0579.pd 1 ψ y) = 0

/-- Smooth `c`-periodic solenoidal real vector test field on `C_c`. -/
structure IsRealSolCylTest (c : ℝ) (Φ : Plane → Vec2) : Prop where
  cyl_test : ∀ k : Fin 2, B0579.IsCylTest c (fun y => Φ y k)
  div_free : ∀ y : Plane, B0579.pd 0 (fun z => Φ z 0) y + B0579.pd 1 (fun z => Φ z 1) y = 0

lemma b0579_cell_eq_cyl_cell (c : ℝ) : B0579.cell c = UnforcedLeray.Cyl.cell c := by
  simp [B0579.cell, UnforcedLeray.Cyl.cell, neg_div]

lemma restrict_b0579_cell_eq_cellμ (c : ℝ) :
    (volume.restrict (B0579.cell c) : Measure Plane) = cellμ c := by
  unfold cellμ
  rw [b0579_cell_eq_cyl_cell]

lemma integrableOn_innerR_cell {c : ℝ} {f g : Plane → Vec2}
    (hf : MemLp f 2 (cellμ c)) (hg : MemLp g 2 (cellμ c)) :
    IntegrableOn (fun z => ⟪f z, g z⟫_ℝ) (B0579.cell c) volume := by
  change Integrable (fun z => ⟪f z, g z⟫_ℝ) (volume.restrict (B0579.cell c))
  rw [restrict_b0579_cell_eq_cellμ]
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with z hfz hgz
  change ⟪(hf.toLp f : Plane → Vec2) z, (hg.toLp g : Plane → Vec2) z⟫_ℝ = ⟪f z, g z⟫_ℝ
  rw [hfz, hgz]

/-! ## 2. Cylinder test and `L²(cell)` bridges -/

lemma memLp_cellμ_of_test {c : ℝ} {ψ : Plane → ℝ} (hψ : B0579.IsCylTest c ψ) :
    MemLp ψ 2 (cellμ c) := by
  rw [← restrict_b0579_cell_eq_cellμ c]
  obtain ⟨R, hR⟩ := hψ.vanish
  exact B0579.memLp_cell_of_continuous hψ.continuous (B0579.isCompact_box c R) hR

lemma isCylTest_sob_iff (c : ℝ) (φ : Plane → ℝ) :
    UnforcedLeray.Sob.IsCylTest c φ ↔ B0579.IsCylTest c φ := by
  constructor
  · intro h
    refine ⟨h.smooth, fun x => ?_, h.bounded⟩
    have hx : (x.1 + c, x.2) = x + (c, 0) := by ext <;> simp
    rw [hx]
    exact h.periodic x
  · intro h
    refine ⟨h.smooth, fun x => ?_, h.band⟩
    have hx : x + (c, 0) = (x.1 + c, x.2) := by ext <;> simp
    rw [hx]
    exact h.periodic x

lemma isCylSmooth_vec_of_tests {c : ℝ} {Φ : Plane → Vec2}
    (h0 : B0579.IsCylTest c (fun y => Φ y 0))
    (h1 : B0579.IsCylTest c (fun y => Φ y 1)) :
    UnforcedLeray.Sob.IsCylSmooth c Φ := by
  have heq : Φ = fun y => Φ y 0 • eR0 + Φ y 1 • eR1 := by
    funext y
    ext k
    fin_cases k <;> simp [eR0, eR1]
  rw [heq]
  have hs0 : ContDiff ℝ ∞ (fun y => Φ y 0 • eR0) := h0.smooth.smul contDiff_const
  have hs1 : ContDiff ℝ ∞ (fun y => Φ y 1 • eR1) := h1.smooth.smul contDiff_const
  refine ⟨hs0.add hs1, fun z => ?_, ?_⟩
  · have hz : z + (c, 0) = (z.1 + c, z.2) := by ext <;> simp
    simp only [hz, h0.periodic, h1.periodic]
  · obtain ⟨R0, hR0⟩ := h0.band
    obtain ⟨R1, hR1⟩ := h1.band
    refine ⟨max R0 R1, fun z hz => ?_⟩
    rw [hR0 z (lt_of_le_of_lt (le_max_left _ _) hz),
      hR1 z (lt_of_le_of_lt (le_max_right _ _) hz), zero_smul, zero_smul, add_zero]

lemma isCylSmooth_of_solTest {c : ℝ} {Φ : Plane → Vec2}
    (hΦ : IsRealSolCylTest c Φ) :
    UnforcedLeray.Sob.IsCylSmooth c Φ :=
  isCylSmooth_vec_of_tests (hΦ.cyl_test 0) (hΦ.cyl_test 1)

lemma memLp_of_cylSmooth {c : ℝ} {Φ : Plane → Vec2}
    (hΦ : UnforcedLeray.Sob.IsCylSmooth c Φ) :
    MemLp Φ 2 (cellμ c) := by
  rw [← UnforcedLeray.TrainB.vecH1_measure_eq_cell c]
  exact hΦ.memLp (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) 2

def cylSmoothToL2 {c : ℝ} {Φ : Plane → Vec2}
    (hΦ : UnforcedLeray.Sob.IsCylSmooth c Φ) : L2v c :=
  (memLp_of_cylSmooth hΦ).toLp Φ

lemma pd_coord_cylSmooth {c : ℝ} {Φ : Plane → Vec2}
    (hΦ : UnforcedLeray.Sob.IsCylSmooth c Φ) (j k : Fin 2) (y : Plane) :
    fderiv ℝ Φ y (B0579.dir j) k = B0579.pd j (fun z => Φ z k) y := by
  have hd : DifferentiableAt ℝ Φ y := (hΦ.smooth.differentiable (by simp)) y
  have hcomp : HasFDerivAt (fun z => Φ z k)
      ((EuclideanSpace.proj k : Vec2 →L[ℝ] ℝ).comp (fderiv ℝ Φ y)) y :=
    (EuclideanSpace.proj k : Vec2 →L[ℝ] ℝ).hasFDerivAt.comp y hd.hasFDerivAt
  unfold B0579.pd
  rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]
  rfl

lemma inner_cylSmoothToL2_right {c : ℝ} {Φ : Plane → Vec2}
    (hΦ : UnforcedLeray.Sob.IsCylSmooth c Φ) (f : L2v c) :
    ⟪cylSmoothToL2 hΦ, f⟫_ℝ = ∫ y in B0579.cell c, ⟪Φ y, (f : Plane → Vec2) y⟫_ℝ := by
  rw [b0579_cell_eq_cyl_cell]
  exact UnforcedLeray.Cyl.inner_toLp_left (memLp_of_cylSmooth hΦ) f

lemma isCylSmooth_single {c : ℝ} {ψ : Plane → ℝ} (hψ : B0579.IsCylTest c ψ) (k : Fin 2) :
    UnforcedLeray.Sob.IsCylSmooth c (fun y => ψ y • EuclideanSpace.single k (1 : ℝ)) where
  smooth := hψ.smooth.smul contDiff_const
  periodic z := by
    have hz : z + (c, 0) = (z.1 + c, z.2) := by ext <;> simp
    rw [hz, hψ.periodic]
  bounded := by
    obtain ⟨R, hR⟩ := hψ.band
    exact ⟨R, fun z hz => by rw [hR z hz, zero_smul]⟩

lemma inner_cylSmooth_single {c : ℝ} {ψ : Plane → ℝ} (hψ : B0579.IsCylTest c ψ)
    (k : Fin 2) (f : L2v c) :
    ⟪f, cylSmoothToL2 (isCylSmooth_single hψ k)⟫_ℝ =
      ∫ y in B0579.cell c, (f : Plane → Vec2) y k * ψ y := by
  rw [real_inner_comm, inner_cylSmoothToL2_right]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  fin_cases k <;> simp [mul_comm]

/-- Almost-everywhere uniqueness of weak cell derivatives in `L²(cell)`. -/
lemma ae_eq_of_hasWeakCellDerivR {c : ℝ} (_hc : 0 < c) {j : Fin 2}
    {u g₁ g₂ : Plane → Vec2}
    (hg₁ : MemLp g₁ 2 (cellμ c)) (hg₂ : MemLp g₂ 2 (cellμ c))
    (h1 : ∀ k : Fin 2, HasWeakCellDerivR c j (fun y => u y k) (fun y => g₁ y k))
    (h2 : ∀ k : Fin 2, HasWeakCellDerivR c j (fun y => u y k) (fun y => g₂ y k)) :
    g₁ =ᵐ[cellμ c] g₂ := by
  have hcoord : ∀ k : Fin 2,
      (fun y => g₁ y k - g₂ y k) =ᵐ[(UnforcedLeray.Sob.cylinder c).μ] 0 := by
    intro k
    let hpk : Vec2 →L[ℝ] ℝ := EuclideanSpace.proj k
    have hm1 : MemLp (fun y => g₁ y k) 2 (UnforcedLeray.Sob.cylinder c).μ := by
      rw [UnforcedLeray.Cyl.cylinder_μ_eq]
      have heq : (fun y => g₁ y k) = hpk ∘ g₁ := by funext y; simp [hpk]
      rw [heq]
      exact hpk.comp_memLp' hg₁
    have hm2 : MemLp (fun y => g₂ y k) 2 (UnforcedLeray.Sob.cylinder c).μ := by
      rw [UnforcedLeray.Cyl.cylinder_μ_eq]
      have heq : (fun y => g₂ y k) = hpk ∘ g₂ := by funext y; simp [hpk]
      rw [heq]
      exact hpk.comp_memLp' hg₂
    have hloc : LocallyIntegrable (fun y => g₁ y k - g₂ y k) (UnforcedLeray.Sob.cylinder c).μ :=
      (hm1.sub hm2).locallyIntegrable (by norm_num)
    refine (UnforcedLeray.Sob.cylinder c).ae_zero _ hloc fun φ hφ => ?_
    have hφb : B0579.IsCylTest c φ := (isCylTest_sob_iff c φ).1 hφ
    have hi1 : IntegrableOn (fun y => g₁ y k * φ y) (B0579.cell c) := ((h1 k).1 φ hφb).2
    have hi2 : IntegrableOn (fun y => g₂ y k * φ y) (B0579.cell c) := ((h2 k).1 φ hφb).2
    have hsub0 : ∫ y in B0579.cell c, (g₁ y k - g₂ y k) * φ y = 0 := by
      have hfn : (fun y => (g₁ y k - g₂ y k) * φ y) =
          fun y => g₁ y k * φ y - g₂ y k * φ y := by funext y; ring
      rw [hfn, integral_sub hi1 hi2]
      have a1 := (h1 k).2 φ hφb
      have a2 := (h2 k).2 φ hφb
      linarith
    rw [UnforcedLeray.Cyl.cylinder_μ_eq]
    change ∫ y in UnforcedLeray.Cyl.cell c, φ y * (g₁ y k - g₂ y k) = 0
    rw [← b0579_cell_eq_cyl_cell]
    have hcomm : (fun y => φ y * (g₁ y k - g₂ y k)) = fun y => (g₁ y k - g₂ y k) * φ y := by
      funext y; ring
    rwa [hcomm]
  have h0 := hcoord 0
  have h1' := hcoord 1
  rw [UnforcedLeray.Cyl.cylinder_μ_eq] at h0 h1'
  filter_upwards [h0, h1'] with y hy0 hy1
  ext k
  fin_cases k
  · exact sub_eq_zero.mp hy0
  · exact sub_eq_zero.mp hy1

lemma eq_of_hasWeakCellDerivR {c : ℝ} (hc : 0 < c) {j : Fin 2}
    {u : Plane → Vec2} {g₁ g₂ : L2v c}
    (h1 : ∀ k : Fin 2, HasWeakCellDerivR c j (fun y => u y k) (fun y => g₁ y k))
    (h2 : ∀ k : Fin 2, HasWeakCellDerivR c j (fun y => u y k) (fun y => g₂ y k)) :
    g₁ = g₂ :=
  Lp.ext (ae_eq_of_hasWeakCellDerivR hc (Lp.memLp g₁) (Lp.memLp g₂) h1 h2)

lemma mem_divFree_iff_solenoidal {c : ℝ} (f : L2v c) :
    f ∈ divFree c ↔ IsRealCellSolenoidal c (f : Plane → Vec2) := by
  rw [UnforcedLeray.Cyl.mem_divFree]
  constructor
  · intro hf ψ hψ
    have hψs : UnforcedLeray.Sob.IsCylTest c ψ := (isCylTest_sob_iff c ψ).2 hψ
    have h0 := hf ψ hψs
    rw [UnforcedLeray.Cyl.gradL, UnforcedLeray.Cyl.inner_toLp_left,
      ← b0579_cell_eq_cyl_cell] at h0
    have hd : Differentiable ℝ ψ := hψ.differentiable
    have hfun : (fun z => ⟪UnforcedLeray.Cyl.gradT ψ z, (f : Plane → Vec2) z⟫_ℝ) =
        fun y => f y 0 * B0579.pd 0 ψ y + f y 1 * B0579.pd 1 ψ y := by
      funext y
      rw [real_inner_comm, UnforcedLeray.Cyl.gradT, UnforcedLeray.Cyl.inner_vec,
        UnforcedLeray.Cyl.partialQ_eq_fderiv hd, UnforcedLeray.Cyl.partialEta_eq_fderiv hd]
      rfl
    have hint : IntegrableOn (fun z => ⟪UnforcedLeray.Cyl.gradT ψ z, (f : Plane → Vec2) z⟫_ℝ)
        (B0579.cell c) :=
      integrableOn_innerR_cell (UnforcedLeray.Cyl.memLp_gradT hψs) (Lp.memLp f)
    rw [hfun] at hint h0
    exact ⟨hint, h0⟩
  · intro hf φ hφ
    have hφb : B0579.IsCylTest c φ := (isCylTest_sob_iff c φ).1 hφ
    obtain ⟨_, h0⟩ := hf φ hφb
    rw [UnforcedLeray.Cyl.gradL, UnforcedLeray.Cyl.inner_toLp_left, ← b0579_cell_eq_cyl_cell]
    have hd : Differentiable ℝ φ := hφb.differentiable
    have hfun : (fun z => ⟪UnforcedLeray.Cyl.gradT φ z, (f : Plane → Vec2) z⟫_ℝ) =
        fun y => f y 0 * B0579.pd 0 φ y + f y 1 * B0579.pd 1 φ y := by
      funext y
      rw [real_inner_comm, UnforcedLeray.Cyl.gradT, UnforcedLeray.Cyl.inner_vec,
        UnforcedLeray.Cyl.partialQ_eq_fderiv hd, UnforcedLeray.Cyl.partialEta_eq_fderiv hd]
      rfl
    rw [hfun]
    exact h0

lemma cylSmoothToL2_mem_divFree_of_solTest {c : ℝ} (hc : 0 < c) {Φ : Plane → Vec2}
    (hΦ : IsRealSolCylTest c Φ) :
    cylSmoothToL2 (isCylSmooth_of_solTest hΦ) ∈ divFree c := by
  rw [UnforcedLeray.Cyl.mem_divFree]
  intro ψ hψ
  rw [UnforcedLeray.Cyl.gradL, cylSmoothToL2, UnforcedLeray.Cyl.inner_toLp_eq]
  have hdψ : Differentiable ℝ ψ := hψ.differentiable
  have hΦ0 : UnforcedLeray.Sob.IsCylTest c (fun z => Φ z 0) :=
    (isCylTest_sob_iff c _).2 (hΦ.cyl_test 0)
  have hΦ1 : UnforcedLeray.Sob.IsCylTest c (fun z => Φ z 1) :=
    (isCylTest_sob_iff c _).2 (hΦ.cyl_test 1)
  have e : (fun z => ⟪UnforcedLeray.Cyl.gradT ψ z, Φ z⟫_ℝ) =
      fun z => fderiv ℝ ψ z ((1 : ℝ), (0 : ℝ)) * Φ z 0 +
        fderiv ℝ ψ z ((0 : ℝ), (1 : ℝ)) * Φ z 1 := by
    funext z
    rw [real_inner_comm, UnforcedLeray.Cyl.gradT, UnforcedLeray.Cyl.inner_vec,
      UnforcedLeray.Cyl.partialQ_eq_fderiv hdψ, UnforcedLeray.Cyl.partialEta_eq_fderiv hdψ]
    ring
  rw [e, integral_add ((hψ.dirDeriv _).integrableOn_mul hΦ0.continuous)
    ((hψ.dirDeriv _).integrableOn_mul hΦ1.continuous),
    UnforcedLeray.Cyl.integral_fderiv_mul_test hc hψ hΦ0,
    UnforcedLeray.Cyl.integral_fderiv_mul_test hc hψ hΦ1,
    ← neg_add, ← integral_add (hψ.integrableOn_mul (hΦ0.dirDeriv _).continuous)
      (hψ.integrableOn_mul (hΦ1.dirDeriv _).continuous)]
  have hzero : (fun z : Plane => ψ z * fderiv ℝ (fun y => Φ y 0) z ((1 : ℝ), (0 : ℝ)) +
      ψ z * fderiv ℝ (fun y => Φ y 1) z ((0 : ℝ), (1 : ℝ))) = fun _ => 0 := by
    funext z
    rw [← mul_add]
    have hdz : fderiv ℝ (fun y => Φ y 0) z ((1 : ℝ), (0 : ℝ)) +
        fderiv ℝ (fun y => Φ y 1) z ((0 : ℝ), (1 : ℝ)) = 0 := hΦ.div_free z
    rw [hdz, mul_zero]
  rw [hzero, integral_zero, neg_zero]

lemma isRealSolCylTest_dir {c : ℝ} {Φ : Plane → Vec2}
    (hΦ : IsRealSolCylTest c Φ) (j : Fin 2) :
    IsRealSolCylTest c (fun y => fderiv ℝ Φ y (B0579.dir j)) where
  cyl_test k := by
    have hEq : (fun y => fderiv ℝ Φ y (B0579.dir j) k) = B0579.pd j (fun z => Φ z k) :=
      funext (pd_coord_cylSmooth (isCylSmooth_of_solTest hΦ) j k)
    rw [hEq]
    exact (hΦ.cyl_test k).pd j
  div_free y := by
    have hsm : UnforcedLeray.Sob.IsCylSmooth c Φ := isCylSmooth_of_solTest hΦ
    have h0 := hΦ.cyl_test 0
    have h1 := hΦ.cyl_test 1
    have hc0 : (fun z => fderiv ℝ Φ z (B0579.dir j) 0) = B0579.pd j (fun z => Φ z 0) :=
      funext (pd_coord_cylSmooth hsm j 0)
    have hc1 : (fun z => fderiv ℝ Φ z (B0579.dir j) 1) = B0579.pd j (fun z => Φ z 1) :=
      funext (pd_coord_cylSmooth hsm j 1)
    rw [hc0, hc1]
    unfold B0579.pd
    have hd0 : B0579.dir 0 = ((1 : ℝ), (0 : ℝ)) := rfl
    have hd1 : B0579.dir 1 = ((0 : ℝ), (1 : ℝ)) := rfl
    rw [hd0, hd1]
    have hcomm0 : fderiv ℝ (fun w => fderiv ℝ (fun z => Φ z 0) w (B0579.dir j)) y ((1 : ℝ), (0 : ℝ)) =
        fderiv ℝ (fun w => fderiv ℝ (fun z => Φ z 0) w ((1 : ℝ), (0 : ℝ))) y (B0579.dir j) := by
      have hp := UnforcedLeray.Sob.iterDirDeriv_perm
        (List.Perm.swap ((1 : ℝ), (0 : ℝ)) (B0579.dir j) []) h0.smooth
      exact (congrFun hp y).symm
    have hcomm1 : fderiv ℝ (fun w => fderiv ℝ (fun z => Φ z 1) w (B0579.dir j)) y ((0 : ℝ), (1 : ℝ)) =
        fderiv ℝ (fun w => fderiv ℝ (fun z => Φ z 1) w ((0 : ℝ), (1 : ℝ))) y (B0579.dir j) := by
      have hp := UnforcedLeray.Sob.iterDirDeriv_perm
        (List.Perm.swap ((0 : ℝ), (1 : ℝ)) (B0579.dir j) []) h1.smooth
      exact (congrFun hp y).symm
    rw [hcomm0, hcomm1]
    have hd0' : Differentiable ℝ (fun w => fderiv ℝ (fun z => Φ z 0) w ((1 : ℝ), (0 : ℝ))) :=
      (h0.pd 0).differentiable
    have hd1' : Differentiable ℝ (fun w => fderiv ℝ (fun z => Φ z 1) w ((0 : ℝ), (1 : ℝ))) :=
      (h1.pd 1).differentiable
    have hsum : (fun w => fderiv ℝ (fun z => Φ z 0) w ((1 : ℝ), (0 : ℝ))) +
        (fun w => fderiv ℝ (fun z => Φ z 1) w ((0 : ℝ), (1 : ℝ))) = fun _ => (0 : ℝ) :=
      funext hΦ.div_free
    have hfadd := fderiv_add (hd0' y) (hd1' y)
    have hval := congrArg (fun L : Plane →L[ℝ] ℝ => L (B0579.dir j)) hfadd
    dsimp at hval
    rw [hsum, (hasFDerivAt_const (0 : ℝ) y).fderiv, zero_apply, add_apply] at hval
    exact hval.symm

/-! ## 3. General `L¹(Plane)` translation-average operators on `L2v c` -/

lemma norm_planeShiftL2CLM {c : ℝ} (hc : 0 < c) (w : Plane) (x : L2v c) :
    ‖planeShiftL2CLM hc w x‖ = ‖x‖ := by
  change ‖UnforcedLeray.TrainB.qShiftL2Isometry hc (-w.1)
    (UnforcedLeray.TrainB.etaShiftL2 c (-w.2) x)‖ = ‖x‖
  rw [(UnforcedLeray.TrainB.qShiftL2Isometry hc (-w.1)).norm_map,
    (UnforcedLeray.TrainB.etaShiftL2 c (-w.2)).norm_map]

lemma inner_planeShiftL2CLM_adj {c : ℝ} (hc : 0 < c) (w : Plane) (x y : L2v c) :
    ⟪planeShiftL2CLM hc w x, y⟫_ℝ = ⟪x, planeShiftL2CLM hc (-w) y⟫_ℝ := by
  change inner ℝ
      (UnforcedLeray.TrainB.qShiftL2 hc (-w.1)
        (UnforcedLeray.TrainB.etaShiftL2 c (-w.2) x)) y = _
  have hinvq : UnforcedLeray.TrainB.qShiftL2 hc (-w.1)
      (UnforcedLeray.TrainB.qShiftL2 hc w.1 y) = y :=
    UnforcedLeray.TrainB.qShiftL2_neg_comp hc y
  have hinve : UnforcedLeray.TrainB.etaShiftL2 c (-w.2)
      (UnforcedLeray.TrainB.etaShiftL2 c w.2
        (UnforcedLeray.TrainB.qShiftL2 hc w.1 y)) =
      UnforcedLeray.TrainB.qShiftL2 hc w.1 y :=
    UnforcedLeray.TrainB.etaShiftL2_neg_comp
      (c := c) (a := w.2) (UnforcedLeray.TrainB.qShiftL2 hc w.1 y)
  have hq := (UnforcedLeray.TrainB.qShiftL2Isometry hc (-w.1)).inner_map_map
    (UnforcedLeray.TrainB.etaShiftL2 c (-w.2) x)
    (UnforcedLeray.TrainB.qShiftL2 hc w.1 y)
  have heta := (UnforcedLeray.TrainB.etaShiftL2 c (-w.2)).inner_map_map x
    (UnforcedLeray.TrainB.etaShiftL2 c w.2
      (UnforcedLeray.TrainB.qShiftL2 hc w.1 y))
  have hcomm := UnforcedLeray.HeatCylinder.qShiftL2_etaShiftL2_comm hc
    (a := w.1) (b := w.2) y
  calc
    inner ℝ (UnforcedLeray.TrainB.qShiftL2 hc (-w.1)
        (UnforcedLeray.TrainB.etaShiftL2 c (-w.2) x)) y =
      inner ℝ (UnforcedLeray.TrainB.qShiftL2 hc (-w.1)
        (UnforcedLeray.TrainB.etaShiftL2 c (-w.2) x))
        (UnforcedLeray.TrainB.qShiftL2 hc (-w.1)
          (UnforcedLeray.TrainB.qShiftL2 hc w.1 y)) := by rw [hinvq]
    _ = inner ℝ (UnforcedLeray.TrainB.etaShiftL2 c (-w.2) x)
        (UnforcedLeray.TrainB.qShiftL2 hc w.1 y) := hq
    _ = inner ℝ (UnforcedLeray.TrainB.etaShiftL2 c (-w.2) x)
        (UnforcedLeray.TrainB.etaShiftL2 c (-w.2)
          (UnforcedLeray.TrainB.etaShiftL2 c w.2
            (UnforcedLeray.TrainB.qShiftL2 hc w.1 y))) := by rw [hinve]
    _ = inner ℝ x (UnforcedLeray.TrainB.etaShiftL2 c w.2
        (UnforcedLeray.TrainB.qShiftL2 hc w.1 y)) := heta
    _ = inner ℝ x (UnforcedLeray.TrainB.qShiftL2 hc w.1
        (UnforcedLeray.TrainB.etaShiftL2 c w.2 y)) := by rw [← hcomm]
    _ = inner ℝ x (planeShiftL2CLM hc (-w) y) := by
      rw [planeShiftL2CLM_apply]
      simp [planeShiftL2]

lemma integrable_kernel_smul_planeShift {c : ℝ} (hc : 0 < c) {K : Plane → ℝ}
    (hK : Integrable K volume) (x : L2v c) :
    Integrable (fun w : Plane => K w • planeShiftL2CLM hc w x) volume := by
  have hcont := continuous_planeShiftL2_orbit hc x
  have hmeas : AEStronglyMeasurable (fun w : Plane => K w • planeShiftL2CLM hc w x) volume :=
    hK.aestronglyMeasurable.smul hcont.stronglyMeasurable.aestronglyMeasurable
  rw [← integrable_norm_iff hmeas]
  have hnorm : (fun w : Plane => ‖K w • planeShiftL2CLM hc w x‖) =
      fun w => ‖K w‖ * ‖x‖ := by
    funext w
    rw [norm_smul, norm_planeShiftL2CLM hc w x]
  rw [hnorm]
  exact hK.norm.mul_const ‖x‖

def shiftAvg {c : ℝ} (hc : 0 < c) (K : Plane → ℝ) (x : L2v c) : L2v c :=
  ∫ w : Plane, K w • planeShiftL2CLM hc w x

lemma norm_shiftAvg_le {c : ℝ} (hc : 0 < c) {K : Plane → ℝ} (_hK : Integrable K volume)
    (x : L2v c) :
    ‖shiftAvg hc K x‖ ≤ (∫ w : Plane, ‖K w‖) * ‖x‖ := by
  unfold shiftAvg
  calc
    ‖∫ w : Plane, K w • planeShiftL2CLM hc w x‖
        ≤ ∫ w : Plane, ‖K w • planeShiftL2CLM hc w x‖ := norm_integral_le_integral_norm _
    _ = ∫ w : Plane, ‖K w‖ * ‖x‖ := by
        congr 1; funext w; rw [norm_smul, norm_planeShiftL2CLM hc w x]
    _ = (∫ w : Plane, ‖K w‖) * ‖x‖ := integral_mul_const _ _

def shiftAvgCLM {c : ℝ} (hc : 0 < c) (K : Plane → ℝ) (hK : Integrable K volume) :
    L2v c →L[ℝ] L2v c :=
  LinearMap.mkContinuous
    { toFun := shiftAvg hc K
      map_add' := fun x y => by
        unfold shiftAvg
        have hp : (fun w : Plane => K w • planeShiftL2CLM hc w (x + y)) =
            fun w => K w • planeShiftL2CLM hc w x + K w • planeShiftL2CLM hc w y := by
          funext w; rw [map_add, smul_add]
        rw [hp, integral_add (integrable_kernel_smul_planeShift hc hK x)
          (integrable_kernel_smul_planeShift hc hK y)]
      map_smul' := fun r x => by
        unfold shiftAvg
        have hp : (fun w : Plane => K w • planeShiftL2CLM hc w (r • x)) =
            fun w => r • (K w • planeShiftL2CLM hc w x) := by
          funext w; rw [map_smul, smul_comm]
        simp only [RingHom.id_apply, hp, integral_smul] }
    (∫ w : Plane, ‖K w‖)
    (norm_shiftAvg_le hc hK)

@[simp] lemma shiftAvgCLM_apply {c : ℝ} (hc : 0 < c) {K : Plane → ℝ}
    (hK : Integrable K volume) (x : L2v c) :
    shiftAvgCLM hc K hK x = shiftAvg hc K x := rfl

lemma norm_shiftAvgCLM_le {c : ℝ} (hc : 0 < c) {K : Plane → ℝ}
    (hK : Integrable K volume) :
    ‖shiftAvgCLM hc K hK‖ ≤ ∫ w : Plane, ‖K w‖ :=
  LinearMap.mkContinuous_norm_le _ (integral_nonneg fun _ => norm_nonneg _) _

lemma norm_shiftAvgCLM_sub_le {c : ℝ} (hc : 0 < c) {K₁ K₂ : Plane → ℝ}
    (hK₁ : Integrable K₁ volume) (hK₂ : Integrable K₂ volume) :
    ‖shiftAvgCLM hc K₁ hK₁ - shiftAvgCLM hc K₂ hK₂‖ ≤
      ∫ w : Plane, ‖K₁ w - K₂ w‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _) fun x => ?_
  have hsub : (shiftAvgCLM hc K₁ hK₁ - shiftAvgCLM hc K₂ hK₂) x =
      shiftAvg hc (fun w => K₁ w - K₂ w) x := by
    simp only [sub_apply, shiftAvgCLM_apply, shiftAvg]
    rw [← integral_sub (integrable_kernel_smul_planeShift hc hK₁ x)
      (integrable_kernel_smul_planeShift hc hK₂ x)]
    congr 1; funext w; rw [sub_smul]
  rw [hsub]
  exact norm_shiftAvg_le hc (hK₁.sub hK₂) x

lemma shiftAvgCLM_P0_comm {c : ℝ} (hc : 0 < c) {K : Plane → ℝ}
    (hK : Integrable K volume) (x : L2v c) :
    shiftAvgCLM hc K hK (P0 c x) = P0 c (shiftAvgCLM hc K hK x) := by
  simp only [shiftAvgCLM_apply, shiftAvg]
  calc
    (∫ w : Plane, K w • planeShiftL2CLM hc w (P0 c x)) =
        ∫ w : Plane, P0 c (K w • planeShiftL2CLM hc w x) := by
      congr 1; funext w
      rw [map_smul, planeShiftL2CLM_apply, planeShiftL2_P0_comm hc w x, planeShiftL2CLM_apply]
    _ = P0 c (∫ w : Plane, K w • planeShiftL2CLM hc w x) :=
      (P0 c).integral_comp_comm (integrable_kernel_smul_planeShift hc hK x)

lemma inner_shiftAvgCLM {c : ℝ} (hc : 0 < c) {K : Plane → ℝ}
    (hK : Integrable K volume) (x y : L2v c) :
    ⟪shiftAvgCLM hc K hK x, y⟫_ℝ =
      ∫ w : Plane, K w * ⟪planeShiftL2CLM hc w x, y⟫_ℝ := by
  simp only [shiftAvgCLM_apply, shiftAvg]
  have hint := integrable_kernel_smul_planeShift hc hK x
  calc
    ⟪∫ w : Plane, K w • planeShiftL2CLM hc w x, y⟫_ℝ =
        ⟪y, ∫ w : Plane, K w • planeShiftL2CLM hc w x⟫_ℝ := real_inner_comm _ _
    _ = ∫ w : Plane, ⟪y, K w • planeShiftL2CLM hc w x⟫_ℝ := (integral_inner hint y).symm
    _ = ∫ w : Plane, K w * ⟪planeShiftL2CLM hc w x, y⟫_ℝ := by
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        dsimp only
        rw [inner_smul_right, real_inner_comm]

/-! ## 4. Product-kernel 1D integration by parts on translation pairings -/

lemma tendsto_qDiffQuot_cylSmooth {c : ℝ} (hc : 0 < c) {Ψ : Plane → Vec2}
    (hΨ : UnforcedLeray.Sob.IsCylSmooth c Ψ) :
    Tendsto (fun h : ℝ =>
      UnforcedLeray.TrainB.qDifferenceQuotientCLM hc h (cylSmoothToL2 hΨ))
      (𝓝[≠] 0) (𝓝 (cylSmoothToL2 (hΨ.dir ((1 : ℝ), (0 : ℝ))))) := by
  let y : UnforcedLeray.TrainB.VecH1 c :=
    UnforcedLeray.Sob.W.ofCylSmooth (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc Ψ hΨ
  have h0ae : (UnforcedLeray.TrainB.vecH1ValueCellCLM_MP y : Plane → Vec2) =ᵐ[cellμ c] Ψ :=
    UnforcedLeray.TrainB.vecH1ValueCellCLM_MP_ofCylSmooth_ae hc hΨ
  have hqae : (UnforcedLeray.TrainB.vecH1DqCellCLM_MP y : Plane → Vec2) =ᵐ[cellμ c]
      fun z => UnforcedLeray.Cyl.partialQ Ψ z :=
    UnforcedLeray.TrainB.vecH1DqCellCLM_MP_ofCylSmooth_ae hc hΨ
  have h0eq : UnforcedLeray.TrainB.vecH1ValueCellCLM_MP y = cylSmoothToL2 hΨ := by
    apply Lp.ext
    filter_upwards [h0ae, (memLp_of_cylSmooth hΨ).coeFn_toLp] with z h1 h2
    exact h1.trans h2.symm
  have hqeq : UnforcedLeray.TrainB.vecH1DqCellCLM_MP y =
      cylSmoothToL2 (hΨ.dir ((1 : ℝ), (0 : ℝ))) := by
    apply Lp.ext
    filter_upwards [hqae, (memLp_of_cylSmooth (hΨ.dir ((1 : ℝ), (0 : ℝ)))).coeFn_toLp] with z h1 h2
    rw [h1, UnforcedLeray.Cyl.partialQ_eq_fderiv (hΨ.smooth.differentiable (by simp))]
    exact h2.symm
  rw [tendsto_iff_norm_sub_tendsto_zero, ← h0eq, ← hqeq]
  exact UnforcedLeray.TrainB.tendsto_qDifferenceQuotientCLM_error_zero_ofCylSmooth hc hΨ

lemma tendsto_etaDiffQuot_cylSmooth {c : ℝ} (hc : 0 < c) {Ψ : Plane → Vec2}
    (hΨ : UnforcedLeray.Sob.IsCylSmooth c Ψ) :
    Tendsto (fun h : ℝ =>
      UnforcedLeray.TrainB.etaDifferenceQuotientCLM h (cylSmoothToL2 hΨ))
      (𝓝[≠] 0) (𝓝 (cylSmoothToL2 (hΨ.dir ((0 : ℝ), (1 : ℝ))))) := by
  let y : UnforcedLeray.TrainB.VecH1 c :=
    UnforcedLeray.Sob.W.ofCylSmooth (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc Ψ hΨ
  have h0ae : (UnforcedLeray.TrainB.vecH1ValueCellCLM_MP y : Plane → Vec2) =ᵐ[cellμ c] Ψ :=
    UnforcedLeray.TrainB.vecH1ValueCellCLM_MP_ofCylSmooth_ae hc hΨ
  have heae : (UnforcedLeray.TrainB.vecH1DetaCellCLM_MP y : Plane → Vec2) =ᵐ[cellμ c]
      fun z => UnforcedLeray.Cyl.partialEta Ψ z :=
    UnforcedLeray.TrainB.vecH1DetaCellCLM_MP_ofCylSmooth_ae hc hΨ
  have h0eq : UnforcedLeray.TrainB.vecH1ValueCellCLM_MP y = cylSmoothToL2 hΨ := by
    apply Lp.ext
    filter_upwards [h0ae, (memLp_of_cylSmooth hΨ).coeFn_toLp] with z h1 h2
    exact h1.trans h2.symm
  have heeq : UnforcedLeray.TrainB.vecH1DetaCellCLM_MP y =
      cylSmoothToL2 (hΨ.dir ((0 : ℝ), (1 : ℝ))) := by
    apply Lp.ext
    filter_upwards [heae, (memLp_of_cylSmooth (hΨ.dir ((0 : ℝ), (1 : ℝ)))).coeFn_toLp] with z h1 h2
    rw [h1, UnforcedLeray.Cyl.partialEta_eq_fderiv (hΨ.smooth.differentiable (by simp))]
    exact h2.symm
  rw [tendsto_iff_norm_sub_tendsto_zero, ← h0eq, ← heeq]
  exact UnforcedLeray.TrainB.tendsto_etaDifferenceQuotientCLM_error_zero_ofCylSmooth hc hΨ

lemma hasDerivAt_inner_planeShift_fst {c : ℝ} (hc : 0 < c) {Ψ : Plane → Vec2}
    (hΨ : UnforcedLeray.Sob.IsCylSmooth c Ψ) (x : L2v c) (q η : ℝ) :
    HasDerivAt (fun s : ℝ => ⟪planeShiftL2CLM hc (s, η) x, cylSmoothToL2 hΨ⟫_ℝ)
      ⟪planeShiftL2CLM hc (q, η) x, cylSmoothToL2 (hΨ.dir ((1 : ℝ), (0 : ℝ)))⟫_ℝ q := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  set ψ₀ := cylSmoothToL2 hΨ
  set ψq := cylSmoothToL2 (hΨ.dir ((1 : ℝ), (0 : ℝ)))
  let L : L2v c →L[ℝ] ℝ := (innerSL ℝ x).comp (planeShiftL2CLM hc (-q, -η))
  have hlim := (L.continuous.tendsto ψq).comp (tendsto_qDiffQuot_cylSmooth hc hΨ)
  have htarget : L ψq = ⟪planeShiftL2CLM hc (q, η) x, ψq⟫_ℝ := by
    change ⟪x, planeShiftL2CLM hc (-q, -η) ψq⟫_ℝ = _
    simpa using (inner_planeShiftL2CLM_adj hc (q, η) x ψq).symm
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h _
  change ⟪x, planeShiftL2CLM hc (-q, -η)
    (UnforcedLeray.TrainB.qDifferenceQuotientCLM hc h ψ₀)⟫_ℝ =
    h⁻¹ • (⟪planeShiftL2CLM hc (q + h, η) x, ψ₀⟫_ℝ - ⟪planeShiftL2CLM hc (q, η) x, ψ₀⟫_ℝ)
  have hshift : planeShiftL2CLM hc (-q, -η) (UnforcedLeray.TrainB.qShiftL2 hc h ψ₀) =
      planeShiftL2CLM hc (-(q + h), -η) ψ₀ := by
    have hq0 : UnforcedLeray.TrainB.qShiftL2 hc h ψ₀ = planeShiftL2CLM hc (-h, 0) ψ₀ := by
      have he0 : UnforcedLeray.TrainB.etaShiftL2 c 0 ψ₀ = ψ₀ := by
        have h1 := etaShiftL2_add_comp (c := c) (a := 0) (b := 0) ψ₀
        have h2 := UnforcedLeray.TrainB.etaShiftL2_neg_comp (c := c) (a := 0) ψ₀
        simp only [add_zero, neg_zero] at h1 h2
        exact h1.symm.trans h2
      rw [planeShiftL2CLM_apply]
      unfold planeShiftL2
      simp [he0]
    rw [hq0, planeShiftL2CLM_apply, planeShiftL2CLM_apply, planeShiftL2_add_comp hc]
    rw [planeShiftL2CLM_apply]
    congr 1; apply Prod.ext <;> simp [add_comm]
  change ⟪x, planeShiftL2CLM hc (-q, -η) (h⁻¹ • (UnforcedLeray.TrainB.qShiftL2 hc h ψ₀ - ψ₀))⟫_ℝ = _
  rw [map_smul, map_sub, hshift, inner_smul_right, inner_sub_right,
    inner_planeShiftL2CLM_adj hc (q + h, η) x ψ₀, inner_planeShiftL2CLM_adj hc (q, η) x ψ₀]
  simp [Prod.neg_mk, smul_eq_mul]

lemma hasDerivAt_inner_planeShift_snd {c : ℝ} (hc : 0 < c) {Ψ : Plane → Vec2}
    (hΨ : UnforcedLeray.Sob.IsCylSmooth c Ψ) (x : L2v c) (q η : ℝ) :
    HasDerivAt (fun s : ℝ => ⟪planeShiftL2CLM hc (q, s) x, cylSmoothToL2 hΨ⟫_ℝ)
      ⟪planeShiftL2CLM hc (q, η) x, cylSmoothToL2 (hΨ.dir ((0 : ℝ), (1 : ℝ)))⟫_ℝ η := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  set ψ₀ := cylSmoothToL2 hΨ
  set ψη := cylSmoothToL2 (hΨ.dir ((0 : ℝ), (1 : ℝ)))
  let L : L2v c →L[ℝ] ℝ := (innerSL ℝ x).comp (planeShiftL2CLM hc (-q, -η))
  have hlim := (L.continuous.tendsto ψη).comp (tendsto_etaDiffQuot_cylSmooth hc hΨ)
  have htarget : L ψη = ⟪planeShiftL2CLM hc (q, η) x, ψη⟫_ℝ := by
    change ⟪x, planeShiftL2CLM hc (-q, -η) ψη⟫_ℝ = _
    simpa using (inner_planeShiftL2CLM_adj hc (q, η) x ψη).symm
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h _
  change ⟪x, planeShiftL2CLM hc (-q, -η)
    (UnforcedLeray.TrainB.etaDifferenceQuotientCLM h ψ₀)⟫_ℝ =
    h⁻¹ • (⟪planeShiftL2CLM hc (q, η + h) x, ψ₀⟫_ℝ - ⟪planeShiftL2CLM hc (q, η) x, ψ₀⟫_ℝ)
  have hshift : planeShiftL2CLM hc (-q, -η) (UnforcedLeray.TrainB.etaShiftL2 c h ψ₀) =
      planeShiftL2CLM hc (-q, -(η + h)) ψ₀ := by
    have he0 : UnforcedLeray.TrainB.etaShiftL2 c h ψ₀ = planeShiftL2CLM hc (0, -h) ψ₀ := by
      have hq0 : UnforcedLeray.TrainB.qShiftL2 hc 0 (UnforcedLeray.TrainB.etaShiftL2 c h ψ₀) =
          UnforcedLeray.TrainB.etaShiftL2 c h ψ₀ := by
        have h1 := qShiftL2_add_comp hc (a := 0) (b := 0) (UnforcedLeray.TrainB.etaShiftL2 c h ψ₀)
        have h2 := UnforcedLeray.TrainB.qShiftL2_neg_comp (a := 0) hc
          (UnforcedLeray.TrainB.etaShiftL2 c h ψ₀)
        simp only [add_zero, neg_zero] at h1 h2
        exact h1.symm.trans h2
      rw [planeShiftL2CLM_apply]
      unfold planeShiftL2
      simp [hq0]
    rw [he0, planeShiftL2CLM_apply, planeShiftL2CLM_apply, planeShiftL2_add_comp hc]
    rw [planeShiftL2CLM_apply]
    congr 1; apply Prod.ext <;> simp [add_comm]
  change ⟪x, planeShiftL2CLM hc (-q, -η) (h⁻¹ • (UnforcedLeray.TrainB.etaShiftL2 c h ψ₀ - ψ₀))⟫_ℝ = _
  rw [map_smul, map_sub, hshift, inner_smul_right, inner_sub_right,
    inner_planeShiftL2CLM_adj hc (q, η + h) x ψ₀, inner_planeShiftL2CLM_adj hc (q, η) x ψ₀]
  simp [Prod.neg_mk, smul_eq_mul]

lemma integrable_prod_plane {K₁ K₂ : ℝ → ℝ}
    (hK₁ : Integrable K₁ volume) (hK₂ : Integrable K₂ volume) :
    Integrable (fun w : Plane => K₁ w.1 * K₂ w.2) volume := by
  change Integrable (fun w : ℝ × ℝ => K₁ w.1 * K₂ w.2) (volume : Measure (ℝ × ℝ))
  rw [Measure.volume_eq_prod]
  exact hK₁.mul_prod hK₂

private lemma integrable_mul_bounded_plane {G H : Plane → ℝ}
    (hG : Integrable G volume) (hH : Continuous H) {M : ℝ} (hb : ∀ w, ‖H w‖ ≤ M) :
    Integrable (fun w => G w * H w) volume := by
  refine (hG.norm.mul_const (max M 0)).mono'
    (hG.aestronglyMeasurable.mul hH.aestronglyMeasurable) (Eventually.of_forall fun w => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left ((hb w).trans (le_max_left _ _)) (norm_nonneg _)

private lemma integrable_mul_bounded_1d {G H : ℝ → ℝ}
    (hG : Integrable G volume) (hH : Continuous H) {M : ℝ} (hb : ∀ s, ‖H s‖ ≤ M) :
    Integrable (G * H) volume := by
  refine (hG.norm.mul_const (max M 0)).mono'
    (hG.aestronglyMeasurable.mul hH.aestronglyMeasurable) (Eventually.of_forall fun s => ?_)
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_left ((hb s).trans (le_max_left _ _)) (norm_nonneg _)

lemma inner_shiftAvg_prod_ibp_q {c : ℝ} (hc : 0 < c)
    {K₁ K₁' K₂ : ℝ → ℝ}
    (hK₁ : Integrable K₁ volume) (hK₁' : Integrable K₁' volume) (hK₂ : Integrable K₂ volume)
    (hderiv : ∀ q : ℝ, HasDerivAt K₁ (K₁' q) q)
    {Ψ : Plane → Vec2} (hΨ : UnforcedLeray.Sob.IsCylSmooth c Ψ) (x : L2v c) :
    ⟪shiftAvgCLM hc (fun w : Plane => K₁ w.1 * K₂ w.2) (integrable_prod_plane hK₁ hK₂) x,
      cylSmoothToL2 (hΨ.dir ((1 : ℝ), (0 : ℝ)))⟫_ℝ =
    -⟪shiftAvgCLM hc (fun w : Plane => K₁' w.1 * K₂ w.2) (integrable_prod_plane hK₁' hK₂) x,
      cylSmoothToL2 hΨ⟫_ℝ := by
  set ψ₀ := cylSmoothToL2 hΨ
  set ψq := cylSmoothToL2 (hΨ.dir ((1 : ℝ), (0 : ℝ)))
  rw [inner_shiftAvgCLM hc (integrable_prod_plane hK₁ hK₂) x ψq,
    inner_shiftAvgCLM hc (integrable_prod_plane hK₁' hK₂) x ψ₀]
  have hb0 : ∀ w : Plane, ‖⟪planeShiftL2CLM hc w x, ψ₀⟫_ℝ‖ ≤ ‖x‖ * ‖ψ₀‖ := fun w =>
    (abs_real_inner_le_norm _ _).trans (by rw [norm_planeShiftL2CLM hc w x])
  have hbq : ∀ w : Plane, ‖⟪planeShiftL2CLM hc w x, ψq⟫_ℝ‖ ≤ ‖x‖ * ‖ψq‖ := fun w =>
    (abs_real_inner_le_norm _ _).trans (by rw [norm_planeShiftL2CLM hc w x])
  have hc0 : Continuous (fun w : Plane => ⟪planeShiftL2CLM hc w x, ψ₀⟫_ℝ) :=
    continuous_inner.comp ((continuous_planeShiftL2_orbit hc x).prodMk continuous_const)
  have hcq : Continuous (fun w : Plane => ⟪planeShiftL2CLM hc w x, ψq⟫_ℝ) :=
    continuous_inner.comp ((continuous_planeShiftL2_orbit hc x).prodMk continuous_const)
  have hintL : Integrable (fun w : ℝ × ℝ => (K₁ w.1 * K₂ w.2) * ⟪planeShiftL2CLM hc w x, ψq⟫_ℝ)
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact integrable_mul_bounded_plane (integrable_prod_plane hK₁ hK₂) hcq hbq
  have hintR : Integrable (fun w : ℝ × ℝ => (K₁' w.1 * K₂ w.2) * ⟪planeShiftL2CLM hc w x, ψ₀⟫_ℝ)
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact integrable_mul_bounded_plane (integrable_prod_plane hK₁' hK₂) hc0 hb0
  change (∫ w : ℝ × ℝ, (K₁ w.1 * K₂ w.2) * ⟪planeShiftL2CLM hc w x, ψq⟫_ℝ
      ∂(volume : Measure (ℝ × ℝ))) =
    -(∫ w : ℝ × ℝ, (K₁' w.1 * K₂ w.2) * ⟪planeShiftL2CLM hc w x, ψ₀⟫_ℝ
      ∂(volume : Measure (ℝ × ℝ)))
  rw [Measure.volume_eq_prod, MeasureTheory.integral_prod_symm _ hintL,
    MeasureTheory.integral_prod_symm _ hintR, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  have hslice : ∀ q : ℝ, (K₁ q * K₂ η) * ⟪planeShiftL2CLM hc (q, η) x, ψq⟫_ℝ =
      K₂ η * (K₁ q * ⟪planeShiftL2CLM hc (q, η) x, ψq⟫_ℝ) := fun q => by ring
  have hslice' : ∀ q : ℝ, (K₁' q * K₂ η) * ⟪planeShiftL2CLM hc (q, η) x, ψ₀⟫_ℝ =
      K₂ η * (K₁' q * ⟪planeShiftL2CLM hc (q, η) x, ψ₀⟫_ℝ) := fun q => by ring
  simp_rw [hslice, hslice', integral_const_mul]
  have hi_uv' : Integrable (K₁ * fun q => ⟪planeShiftL2CLM hc (q, η) x, ψq⟫_ℝ) :=
    integrable_mul_bounded_1d hK₁ (hcq.comp (continuous_id.prodMk continuous_const))
      (fun q => hbq (q, η))
  have hi_u'v : Integrable (K₁' * fun q => ⟪planeShiftL2CLM hc (q, η) x, ψ₀⟫_ℝ) :=
    integrable_mul_bounded_1d hK₁' (hc0.comp (continuous_id.prodMk continuous_const))
      (fun q => hb0 (q, η))
  have hi_uv : Integrable (K₁ * fun q => ⟪planeShiftL2CLM hc (q, η) x, ψ₀⟫_ℝ) :=
    integrable_mul_bounded_1d hK₁ (hc0.comp (continuous_id.prodMk continuous_const))
      (fun q => hb0 (q, η))
  have hibp := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun q _ => hderiv q) (fun q _ => hasDerivAt_inner_planeShift_fst hc hΨ x q η)
    hi_uv' hi_u'v hi_uv
  rw [hibp]
  ring

lemma inner_shiftAvg_prod_ibp_eta {c : ℝ} (hc : 0 < c)
    {K₁ K₂ K₂' : ℝ → ℝ}
    (hK₁ : Integrable K₁ volume) (hK₂ : Integrable K₂ volume) (hK₂' : Integrable K₂' volume)
    (hderiv : ∀ η : ℝ, HasDerivAt K₂ (K₂' η) η)
    {Ψ : Plane → Vec2} (hΨ : UnforcedLeray.Sob.IsCylSmooth c Ψ) (x : L2v c) :
    ⟪shiftAvgCLM hc (fun w : Plane => K₁ w.1 * K₂ w.2) (integrable_prod_plane hK₁ hK₂) x,
      cylSmoothToL2 (hΨ.dir ((0 : ℝ), (1 : ℝ)))⟫_ℝ =
    -⟪shiftAvgCLM hc (fun w : Plane => K₁ w.1 * K₂' w.2) (integrable_prod_plane hK₁ hK₂') x,
      cylSmoothToL2 hΨ⟫_ℝ := by
  set ψ₀ := cylSmoothToL2 hΨ
  set ψη := cylSmoothToL2 (hΨ.dir ((0 : ℝ), (1 : ℝ)))
  rw [inner_shiftAvgCLM hc (integrable_prod_plane hK₁ hK₂) x ψη,
    inner_shiftAvgCLM hc (integrable_prod_plane hK₁ hK₂') x ψ₀]
  have hb0 : ∀ w : Plane, ‖⟪planeShiftL2CLM hc w x, ψ₀⟫_ℝ‖ ≤ ‖x‖ * ‖ψ₀‖ := fun w =>
    (abs_real_inner_le_norm _ _).trans (by rw [norm_planeShiftL2CLM hc w x])
  have hbe : ∀ w : Plane, ‖⟪planeShiftL2CLM hc w x, ψη⟫_ℝ‖ ≤ ‖x‖ * ‖ψη‖ := fun w =>
    (abs_real_inner_le_norm _ _).trans (by rw [norm_planeShiftL2CLM hc w x])
  have hc0 : Continuous (fun w : Plane => ⟪planeShiftL2CLM hc w x, ψ₀⟫_ℝ) :=
    continuous_inner.comp ((continuous_planeShiftL2_orbit hc x).prodMk continuous_const)
  have hce : Continuous (fun w : Plane => ⟪planeShiftL2CLM hc w x, ψη⟫_ℝ) :=
    continuous_inner.comp ((continuous_planeShiftL2_orbit hc x).prodMk continuous_const)
  have hintL : Integrable (fun w : ℝ × ℝ => (K₁ w.1 * K₂ w.2) * ⟪planeShiftL2CLM hc w x, ψη⟫_ℝ)
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact integrable_mul_bounded_plane (integrable_prod_plane hK₁ hK₂) hce hbe
  have hintR : Integrable (fun w : ℝ × ℝ => (K₁ w.1 * K₂' w.2) * ⟪planeShiftL2CLM hc w x, ψ₀⟫_ℝ)
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact integrable_mul_bounded_plane (integrable_prod_plane hK₁ hK₂') hc0 hb0
  change (∫ w : ℝ × ℝ, (K₁ w.1 * K₂ w.2) * ⟪planeShiftL2CLM hc w x, ψη⟫_ℝ
      ∂(volume : Measure (ℝ × ℝ))) =
    -(∫ w : ℝ × ℝ, (K₁ w.1 * K₂' w.2) * ⟪planeShiftL2CLM hc w x, ψ₀⟫_ℝ
      ∂(volume : Measure (ℝ × ℝ)))
  rw [Measure.volume_eq_prod, MeasureTheory.integral_prod _ hintL,
    MeasureTheory.integral_prod _ hintR, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  have hslice : ∀ η : ℝ, (K₁ q * K₂ η) * ⟪planeShiftL2CLM hc (q, η) x, ψη⟫_ℝ =
      K₁ q * (K₂ η * ⟪planeShiftL2CLM hc (q, η) x, ψη⟫_ℝ) := fun η => by ring
  have hslice' : ∀ η : ℝ, (K₁ q * K₂' η) * ⟪planeShiftL2CLM hc (q, η) x, ψ₀⟫_ℝ =
      K₁ q * (K₂' η * ⟪planeShiftL2CLM hc (q, η) x, ψ₀⟫_ℝ) := fun η => by ring
  simp_rw [hslice, hslice', integral_const_mul]
  have hi_uv' : Integrable (K₂ * fun η => ⟪planeShiftL2CLM hc (q, η) x, ψη⟫_ℝ) :=
    integrable_mul_bounded_1d hK₂ (hce.comp (continuous_const.prodMk continuous_id))
      (fun η => hbe (q, η))
  have hi_u'v : Integrable (K₂' * fun η => ⟪planeShiftL2CLM hc (q, η) x, ψ₀⟫_ℝ) :=
    integrable_mul_bounded_1d hK₂' (hc0.comp (continuous_const.prodMk continuous_id))
      (fun η => hb0 (q, η))
  have hi_uv : Integrable (K₂ * fun η => ⟪planeShiftL2CLM hc (q, η) x, ψ₀⟫_ℝ) :=
    integrable_mul_bounded_1d hK₂ (hc0.comp (continuous_const.prodMk continuous_id))
      (fun η => hb0 (q, η))
  have hibp := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun η _ => hderiv η) (fun η _ => hasDerivAt_inner_planeShift_snd hc hΨ x q η)
    hi_uv' hi_u'v hi_uv
  rw [hibp]
  ring

/-! ## 5. Concrete Gaussian heat `H_θ` and Gaussian-gradient `DHeatCLM` on `L2v c` -/

lemma norm_centeredHeatVecL2CLM_le_one_all {c : ℝ} (hc : 0 < c) (θ : ℝ) :
    ‖centeredHeatVecL2CLM hc θ‖ ≤ 1 := by
  by_cases hθ : 0 < θ
  · exact norm_centeredHeatVecL2CLM_le_one hc hθ
  · rw [centeredHeatVecL2CLM_eq_id_of_nonpos hc (not_lt.mp hθ)]
    exact ContinuousLinearMap.norm_id_le

lemma continuous_centeredHeatVecL2CLM_apply {c : ℝ} (hc : 0 < c) (x : L2v c) :
    Continuous (fun θ : ℝ => centeredHeatVecL2CLM hc θ x) := by
  let xN := centeredVecToNormalizedCLM hc x
  let xP := ((UnforcedLeray.Train.toVecL.symm : Vec2 →L[ℝ] Plane).compLpL 2
    (UnforcedLeray.B0284.cellMeasure c)) xN
  have hp : Continuous (fun θ : ℝ => heatL2CLM hc θ xP) :=
    continuous_heatL2CLM_apply hc xP
  have hv : Continuous (fun θ : ℝ => heatVecL2CLM hc θ xN) :=
    (((UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec2).compLpL 2
      (UnforcedLeray.B0284.cellMeasure c)).continuous).comp hp
  exact (normalizedVecToCenteredCLM hc).continuous.comp hv

lemma centeredHeat_eq_shiftAvgCLM {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) (x : L2v c) :
    centeredHeatVecL2CLM hc θ x =
      shiftAvgCLM hc (heatKernel2 θ)
        (integrable_prod_plane (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
          (UnforcedLeray.B0296.integrable_heatKernel1 hθ)) x := by
  rw [centeredHeatVecL2CLM_eq_centeredGaussianShiftAverageCLM hc hθ x,
    centeredGaussianShiftAverageCLM_apply, centeredGaussianShiftAverage]
  rfl

lemma centeredHeatVecL2CLM_P0_comm {c : ℝ} (hc : 0 < c) (θ : ℝ) (x : L2v c) :
    centeredHeatVecL2CLM hc θ (P0 c x) = P0 c (centeredHeatVecL2CLM hc θ x) := by
  by_cases hθ : 0 < θ
  · rw [centeredHeat_eq_shiftAvgCLM hc hθ, centeredHeat_eq_shiftAvgCLM hc hθ]
    exact shiftAvgCLM_P0_comm hc _ x
  · simp [centeredHeatVecL2CLM_eq_id_of_nonpos hc (not_lt.mp hθ)]

def gradKernelCoord (j : Fin 2) (θ : ℝ) (w : Plane) : ℝ :=
  match j with
  | ⟨0, _⟩ => UnforcedLeray.B0296.dHeatKernel θ w.1 * UnforcedLeray.B0191.heatKernel 1 θ w.2
  | ⟨1, _⟩ => UnforcedLeray.B0191.heatKernel 1 θ w.1 * UnforcedLeray.B0296.dHeatKernel θ w.2

lemma integrable_gradKernelCoord (j : Fin 2) {θ : ℝ} (hθ : 0 < θ) :
    Integrable (gradKernelCoord j θ) volume := by
  fin_cases j
  · exact integrable_prod_plane (UnforcedLeray.B0296.integrable_dHeatKernel hθ)
      (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
  · exact integrable_prod_plane (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
      (UnforcedLeray.B0296.integrable_dHeatKernel hθ)

lemma integral_norm_gradKernelCoord_le (j : Fin 2) {θ : ℝ} (hθ : 0 < θ) :
    ∫ w : Plane, ‖gradKernelCoord j θ w‖ ≤ heatDivL2Coeff θ := by
  have habs : ∀ w : Plane, ‖gradKernelCoord j θ w‖ ≤
      (UnforcedLeray.B0296.gradKernelAbs θ w).toReal := by
    intro w
    rw [UnforcedLeray.B0296.gradKernelAbs, ENNReal.toReal_add enorm_ne_top enorm_ne_top,
      toReal_enorm, toReal_enorm]
    fin_cases j
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  have hint_abs := integrable_gradKernelAbs_toReal hθ
  have hle : ∫ w : Plane, ‖gradKernelCoord j θ w‖ ≤
      ∫ w : Plane, (UnforcedLeray.B0296.gradKernelAbs θ w).toReal :=
    integral_mono (integrable_gradKernelCoord j hθ).norm hint_abs habs
  have hmass : ∫ w : Plane, (UnforcedLeray.B0296.gradKernelAbs θ w).toReal = heatDivL2Coeff θ := by
    have hnn : 0 ≤ ∫ w : Plane, (UnforcedLeray.B0296.gradKernelAbs θ w).toReal :=
      integral_nonneg fun _ => ENNReal.toReal_nonneg
    have h1 := ofReal_integral_norm_eq_lintegral_enorm hint_abs
    have hnorm_eq : (fun w : Plane => ‖(UnforcedLeray.B0296.gradKernelAbs θ w).toReal‖) =
        fun w => (UnforcedLeray.B0296.gradKernelAbs θ w).toReal := by
      funext w; exact Real.norm_of_nonneg ENNReal.toReal_nonneg
    have henorm_eq : (fun w : Plane => ‖(UnforcedLeray.B0296.gradKernelAbs θ w).toReal‖ₑ) =
        UnforcedLeray.B0296.gradKernelAbs θ := by
      funext w
      rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (UnforcedLeray.B0296.gradKernelAbs_ne_top θ w)]
    rw [hnorm_eq, henorm_eq, UnforcedLeray.B0296.lintegral_gradKernelAbs hθ] at h1
    have hcoeff_nn : 0 ≤ heatDivL2Coeff θ := by unfold heatDivL2Coeff; positivity
    exact (ENNReal.ofReal_eq_ofReal_iff hnn hcoeff_nn).1 h1
  exact hle.trans hmass.le

/-- Gaussian-gradient operator `D_j H_θ` on `L2v c` (`0` for `θ ≤ 0`). -/
def DHeatCLM {c : ℝ} (hc : 0 < c) (j : Fin 2) (θ : ℝ) : L2v c →L[ℝ] L2v c :=
  if hθ : 0 < θ then shiftAvgCLM hc (gradKernelCoord j θ) (integrable_gradKernelCoord j hθ)
  else 0

lemma DHeatCLM_of_pos {c : ℝ} (hc : 0 < c) (j : Fin 2) {θ : ℝ} (hθ : 0 < θ) :
    DHeatCLM hc j θ = shiftAvgCLM hc (gradKernelCoord j θ) (integrable_gradKernelCoord j hθ) := by
  simp [DHeatCLM, hθ]

lemma norm_DHeatCLM_le {c : ℝ} (hc : 0 < c) (j : Fin 2) {θ : ℝ} (hθ : 0 < θ) :
    ‖DHeatCLM hc j θ‖ ≤ heatDivL2Coeff θ := by
  rw [DHeatCLM_of_pos hc j hθ]
  exact (norm_shiftAvgCLM_le hc _).trans (integral_norm_gradKernelCoord_le j hθ)

lemma DHeatCLM_P0_comm {c : ℝ} (hc : 0 < c) (j : Fin 2) (θ : ℝ) (x : L2v c) :
    DHeatCLM hc j θ (P0 c x) = P0 c (DHeatCLM hc j θ x) := by
  by_cases hθ : 0 < θ
  · rw [DHeatCLM_of_pos hc j hθ]
    exact shiftAvgCLM_P0_comm hc _ x
  · simp [DHeatCLM, hθ]

lemma continuousOn_DHeatCLM_apply {c : ℝ} (hc : 0 < c) (j : Fin 2) (x : L2v c) :
    ContinuousOn (fun θ : ℝ => DHeatCLM hc j θ x) (Ioi 0) := by
  intro θ₀ hθ₀
  apply ContinuousWithinAt.mono _ (subset_univ _)
  rw [continuousWithinAt_univ]
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hdiv := tendsto_integral_norm_divKernelCLM_sub hθ₀
  have htop : Tendsto (fun θ : ℝ => (∫ w : Plane, ‖divKernelCLM θ w - divKernelCLM θ₀ w‖) * ‖x‖)
      (𝓝 θ₀) (𝓝 0) := by simpa using hdiv.mul_const ‖x‖
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop
    (Eventually.of_forall fun _ => dist_nonneg) ?_
  filter_upwards [Ioi_mem_nhds hθ₀] with θ hθ
  rw [dist_eq_norm, DHeatCLM_of_pos hc j hθ, DHeatCLM_of_pos hc j hθ₀, ← sub_apply]
  calc
    ‖(shiftAvgCLM hc _ _ - shiftAvgCLM hc _ _) x‖
        ≤ ‖shiftAvgCLM hc _ (integrable_gradKernelCoord j hθ) -
            shiftAvgCLM hc _ (integrable_gradKernelCoord j hθ₀)‖ * ‖x‖ :=
          ContinuousLinearMap.le_opNorm _ _
    _ ≤ (∫ w : Plane, ‖gradKernelCoord j θ w - gradKernelCoord j θ₀ w‖) * ‖x‖ :=
          mul_le_mul_of_nonneg_right (norm_shiftAvgCLM_sub_le hc _ _) (norm_nonneg _)
    _ ≤ (∫ w : Plane, ‖divKernelCLM θ w - divKernelCLM θ₀ w‖) * ‖x‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have hint_diff : Integrable (fun w : Plane => ‖divKernelCLM θ w - divKernelCLM θ₀ w‖) := by
          have hb : ∀ w : Plane, ‖divKernelCLM θ w - divKernelCLM θ₀ w‖ ≤
              (UnforcedLeray.B0296.gradKernelAbs θ w).toReal +
                (UnforcedLeray.B0296.gradKernelAbs θ₀ w).toReal := fun w =>
            (norm_sub_le _ _).trans (add_le_add (divKernelCLM_norm_le θ w)
              (divKernelCLM_norm_le θ₀ w))
          have hmeas : AEStronglyMeasurable
              (fun w : Plane => ‖divKernelCLM θ w - divKernelCLM θ₀ w‖) volume := by
            have hc1 : Continuous (fun w : Plane => divKernelCLM θ w) := by
              unfold divKernelCLM UnforcedLeray.B0296.gradHeatKernel2
              exact (((UnforcedLeray.B0296.continuous_dHeatKernel θ).comp continuous_fst).mul
                ((UnforcedLeray.B0296.continuous_heatKernel1 θ).comp continuous_snd)).smul
                continuous_const |>.add
                ((((UnforcedLeray.B0296.continuous_heatKernel1 θ).comp continuous_fst).mul
                  ((UnforcedLeray.B0296.continuous_dHeatKernel θ).comp continuous_snd)).smul
                  continuous_const)
            have hc2 : Continuous (fun w : Plane => divKernelCLM θ₀ w) := by
              unfold divKernelCLM UnforcedLeray.B0296.gradHeatKernel2
              exact (((UnforcedLeray.B0296.continuous_dHeatKernel θ₀).comp continuous_fst).mul
                ((UnforcedLeray.B0296.continuous_heatKernel1 θ₀).comp continuous_snd)).smul
                continuous_const |>.add
                ((((UnforcedLeray.B0296.continuous_heatKernel1 θ₀).comp continuous_fst).mul
                  ((UnforcedLeray.B0296.continuous_dHeatKernel θ₀).comp continuous_snd)).smul
                  continuous_const)
            exact (hc1.sub hc2).norm.aestronglyMeasurable
          exact ((integrable_gradKernelAbs_toReal hθ).add
            (integrable_gradKernelAbs_toReal hθ₀)).mono' hmeas
            (Eventually.of_forall fun w => by
              rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hb w)
        refine integral_mono ((integrable_gradKernelCoord j hθ).sub
          (integrable_gradKernelCoord j hθ₀)).norm hint_diff fun w => ?_
        fin_cases j
        · let v0 : Plane × Plane := ((1, 0), (0, 0))
          have hv0 : ‖v0‖ ≤ 1 := by simp [v0, Prod.norm_def]
          have happ : ((divKernelCLM θ w - divKernelCLM θ₀ w) v0).1 =
              gradKernelCoord 0 θ w - gradKernelCoord 0 θ₀ w := by
            simp [divKernelCLM, UnforcedLeray.B0296.gradHeatKernel2, gradKernelCoord, v0]
          calc
            ‖gradKernelCoord 0 θ w - gradKernelCoord 0 θ₀ w‖
                = ‖((divKernelCLM θ w - divKernelCLM θ₀ w) v0).1‖ := by rw [happ]
            _ ≤ ‖(divKernelCLM θ w - divKernelCLM θ₀ w) v0‖ := norm_fst_le _
            _ ≤ ‖divKernelCLM θ w - divKernelCLM θ₀ w‖ * ‖v0‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ ‖divKernelCLM θ w - divKernelCLM θ₀ w‖ :=
                mul_le_of_le_one_right (norm_nonneg _) hv0
        · let v1 : Plane × Plane := ((0, 0), (1, 0))
          have hv1 : ‖v1‖ ≤ 1 := by simp [v1, Prod.norm_def]
          have happ : ((divKernelCLM θ w - divKernelCLM θ₀ w) v1).1 =
              gradKernelCoord 1 θ w - gradKernelCoord 1 θ₀ w := by
            simp [divKernelCLM, UnforcedLeray.B0296.gradHeatKernel2, gradKernelCoord, v1]
          calc
            ‖gradKernelCoord 1 θ w - gradKernelCoord 1 θ₀ w‖
                = ‖((divKernelCLM θ w - divKernelCLM θ₀ w) v1).1‖ := by rw [happ]
            _ ≤ ‖(divKernelCLM θ w - divKernelCLM θ₀ w) v1‖ := norm_fst_le _
            _ ≤ ‖divKernelCLM θ w - divKernelCLM θ₀ w‖ * ‖v1‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ ‖divKernelCLM θ w - divKernelCLM θ₀ w‖ :=
                mul_le_of_le_one_right (norm_nonneg _) hv1

lemma hasWeakCellDerivR_DHeatCLM {c : ℝ} (hc : 0 < c) (j : Fin 2) {θ : ℝ} (hθ : 0 < θ)
    (x : L2v c) (k : Fin 2) :
    HasWeakCellDerivR c j (fun y => (centeredHeatVecL2CLM hc θ x : Plane → Vec2) y k)
      (fun y => (DHeatCLM hc j θ x : Plane → Vec2) y k) := by
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · have hmψ : MemLp ψ 2 (cellμ c) := memLp_cellμ_of_test hψ
    have hmpd : MemLp (B0579.pd j ψ) 2 (cellμ c) := memLp_cellμ_of_test (hψ.pd j)
    rw [b0579_cell_eq_cyl_cell]
    exact ⟨(UnforcedLeray.Cyl.memLp_component (centeredHeatVecL2CLM hc θ x) k).integrable_mul hmpd,
      (UnforcedLeray.Cyl.memLp_component (DHeatCLM hc j θ x) k).integrable_mul hmψ⟩
  · have hΨ := isCylSmooth_single hψ k
    have hdir : (fun y => fderiv ℝ (fun z => ψ z • EuclideanSpace.single k (1 : ℝ)) y
        (B0579.dir j)) = fun y => B0579.pd j ψ y • EuclideanSpace.single k (1 : ℝ) := by
      funext y
      rw [fderiv_smul_const (hψ.differentiable y)]
      rfl
    have htoLp_dir : cylSmoothToL2 (hΨ.dir (B0579.dir j)) =
        cylSmoothToL2 (isCylSmooth_single (hψ.pd j) k) := by
      apply Lp.ext
      filter_upwards [(memLp_of_cylSmooth (hΨ.dir (B0579.dir j))).coeFn_toLp,
        (memLp_of_cylSmooth (isCylSmooth_single (hψ.pd j) k)).coeFn_toLp] with y h1 h2
      exact h1.trans ((congrFun hdir y).trans h2.symm)
    rw [← inner_cylSmooth_single (hψ.pd j) k (centeredHeatVecL2CLM hc θ x),
      ← inner_cylSmooth_single hψ k (DHeatCLM hc j θ x), ← htoLp_dir,
      centeredHeat_eq_shiftAvgCLM hc hθ x, DHeatCLM_of_pos hc j hθ]
    fin_cases j
    · exact inner_shiftAvg_prod_ibp_q hc
        (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
        (UnforcedLeray.B0296.integrable_dHeatKernel hθ)
        (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
        (UnforcedLeray.B0296.hasDerivAt_heatKernel hθ.ne') hΨ x
    · exact inner_shiftAvg_prod_ibp_eta hc
        (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
        (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
        (UnforcedLeray.B0296.integrable_dHeatKernel hθ)
        (UnforcedLeray.B0296.hasDerivAt_heatKernel hθ.ne') hΨ x

/-! ## 6. Commutation of `shiftAvgCLM` and `P0` with weak cell derivatives -/

lemma hasWeakCellDerivR_of_vecH1 {c : ℝ} (x dx : L2v c) (j : Fin 2) :
    (∀ k : Fin 2, HasWeakCellDerivR c j (fun y => x y k) (fun y => dx y k)) ↔
      UnforcedLeray.Sob.HasWeakDeriv (UnforcedLeray.Sob.cylinder c) [B0579.dir j]
        (x : Plane → Vec2) (dx : Plane → Vec2) := by
  have hxm : MemLp (x : Plane → Vec2) 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [UnforcedLeray.TrainB.vecH1_measure_eq_cell c]; exact Lp.memLp x
  have hdxm : MemLp (dx : Plane → Vec2) 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [UnforcedLeray.TrainB.vecH1_measure_eq_cell c]; exact Lp.memLp dx
  constructor
  · intro h
    refine ⟨fun φ hφ => UnforcedLeray.Sob.integrable_smul_of_memLp
        (UnforcedLeray.Sob.CompactlyBounded.of_adm
          ((UnforcedLeray.Sob.cylinder c).adm_iterDirDeriv hφ [B0579.dir j])) hxm,
      fun φ hφ => UnforcedLeray.Sob.integrable_smul_of_memLp
        (UnforcedLeray.Sob.CompactlyBounded.of_adm hφ) hdxm, ?_⟩
    intro φ hφ
    have hφb : B0579.IsCylTest c φ := (isCylTest_sob_iff c φ).1 hφ
    have hiL := UnforcedLeray.Sob.integrable_smul_of_memLp
      (UnforcedLeray.Sob.CompactlyBounded.of_adm
        ((UnforcedLeray.Sob.cylinder c).adm_iterDirDeriv hφ [B0579.dir j])) hxm
    have hiR := UnforcedLeray.Sob.integrable_smul_of_memLp
      (UnforcedLeray.Sob.CompactlyBounded.of_adm hφ) hdxm
    ext k
    have hpL := (EuclideanSpace.proj k : Vec2 →L[ℝ] ℝ).integral_comp_comm hiL
    have hpR := (EuclideanSpace.proj k : Vec2 →L[ℝ] ℝ).integral_comp_comm hiR
    simp only [UnforcedLeray.Sob.iterDirDeriv_singleton, List.length_singleton, pow_one,
      neg_one_smul, UnforcedLeray.Cyl.cylinder_μ_eq] at hpL hpR ⊢
    rw [PiLp.neg_apply]
    change (EuclideanSpace.proj k : Vec2 →L[ℝ] ℝ)
        (∫ y : Plane, fderiv ℝ φ y (B0579.dir j) • (x : Plane → Vec2) y ∂(cellμ c)) =
      -(EuclideanSpace.proj k : Vec2 →L[ℝ] ℝ)
        (∫ y : Plane, φ y • (dx : Plane → Vec2) y ∂(cellμ c))
    rw [← hpL, ← hpR]
    have hL : (∫ y : Plane, (EuclideanSpace.proj k : Vec2 →L[ℝ] ℝ)
        (fderiv ℝ φ y (B0579.dir j) • (x : Plane → Vec2) y) ∂(cellμ c)) =
        ∫ y in B0579.cell c, x y k * B0579.pd j φ y := by
      rw [b0579_cell_eq_cyl_cell]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp [B0579.pd, mul_comm]
    have hR : (∫ y : Plane, (EuclideanSpace.proj k : Vec2 →L[ℝ] ℝ)
        (φ y • (dx : Plane → Vec2) y) ∂(cellμ c)) =
        ∫ y in B0579.cell c, dx y k * φ y := by
      rw [b0579_cell_eq_cyl_cell]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp [mul_comm]
    rw [hL, hR, (h k).2 φ hφb]
  · intro h k
    refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
    · have hmψ : MemLp ψ 2 (cellμ c) := memLp_cellμ_of_test hψ
      have hmpd : MemLp (B0579.pd j ψ) 2 (cellμ c) := memLp_cellμ_of_test (hψ.pd j)
      rw [b0579_cell_eq_cyl_cell]
      exact ⟨(UnforcedLeray.Cyl.memLp_component x k).integrable_mul hmpd,
        (UnforcedLeray.Cyl.memLp_component dx k).integrable_mul hmψ⟩
    · have hψs : UnforcedLeray.Sob.IsCylTest c ψ := (isCylTest_sob_iff c ψ).2 hψ
      have hid := congrArg (fun v : Vec2 => (EuclideanSpace.proj k : Vec2 →L[ℝ] ℝ) v)
        (h.identity ψ hψs)
      have hiL := h.int_left ψ hψs
      have hiR := h.int_right ψ hψs
      have hpL := (EuclideanSpace.proj k : Vec2 →L[ℝ] ℝ).integral_comp_comm hiL
      have hpR := (EuclideanSpace.proj k : Vec2 →L[ℝ] ℝ).integral_comp_comm hiR
      simp only [UnforcedLeray.Sob.iterDirDeriv_singleton, List.length_singleton, pow_one,
        neg_one_smul, UnforcedLeray.Cyl.cylinder_μ_eq, map_neg] at hid hpL hpR
      rw [← hpL, ← hpR] at hid
      have hL : (∫ y : Plane, (EuclideanSpace.proj k : Vec2 →L[ℝ] ℝ)
          (fderiv ℝ ψ y (B0579.dir j) • (x : Plane → Vec2) y) ∂(cellμ c)) =
          ∫ y in B0579.cell c, x y k * B0579.pd j ψ y := by
        rw [b0579_cell_eq_cyl_cell]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp [B0579.pd, mul_comm]
      have hR : (∫ y : Plane, (EuclideanSpace.proj k : Vec2 →L[ℝ] ℝ)
          (ψ y • (dx : Plane → Vec2) y) ∂(cellμ c)) =
          ∫ y in B0579.cell c, dx y k * ψ y := by
        rw [b0579_cell_eq_cyl_cell]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp [mul_comm]
      rwa [hL, hR] at hid

lemma hasWeakCellDerivR_shiftAvgCLM {c : ℝ} (hc : 0 < c) {K : Plane → ℝ}
    (hK : Integrable K volume) {x dx : L2v c} {j : Fin 2}
    (h : ∀ k : Fin 2, HasWeakCellDerivR c j (fun y => x y k) (fun y => dx y k)) :
    ∀ k : Fin 2, HasWeakCellDerivR c j
      (fun y => (shiftAvgCLM hc K hK x : Plane → Vec2) y k)
      (fun y => (shiftAvgCLM hc K hK dx : Plane → Vec2) y k) := by
  intro k
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · have hmψ : MemLp ψ 2 (cellμ c) := memLp_cellμ_of_test hψ
    have hmpd : MemLp (B0579.pd j ψ) 2 (cellμ c) := memLp_cellμ_of_test (hψ.pd j)
    rw [b0579_cell_eq_cyl_cell]
    exact ⟨(UnforcedLeray.Cyl.memLp_component (shiftAvgCLM hc K hK x) k).integrable_mul hmpd,
      (UnforcedLeray.Cyl.memLp_component (shiftAvgCLM hc K hK dx) k).integrable_mul hmψ⟩
  · have hΨ := isCylSmooth_single hψ k
    have hdir : (fun y => fderiv ℝ (fun z => ψ z • EuclideanSpace.single k (1 : ℝ)) y
        (B0579.dir j)) = fun y => B0579.pd j ψ y • EuclideanSpace.single k (1 : ℝ) := by
      funext y
      rw [fderiv_smul_const (hψ.differentiable y)]
      rfl
    have htoLp_dir : cylSmoothToL2 (hΨ.dir (B0579.dir j)) =
        cylSmoothToL2 (isCylSmooth_single (hψ.pd j) k) := by
      apply Lp.ext
      filter_upwards [(memLp_of_cylSmooth (hΨ.dir (B0579.dir j))).coeFn_toLp,
        (memLp_of_cylSmooth (isCylSmooth_single (hψ.pd j) k)).coeFn_toLp] with y h1 h2
      exact h1.trans ((congrFun hdir y).trans h2.symm)
    rw [← inner_cylSmooth_single (hψ.pd j) k (shiftAvgCLM hc K hK x),
      ← inner_cylSmooth_single hψ k (shiftAvgCLM hc K hK dx), ← htoLp_dir,
      inner_shiftAvgCLM hc hK, inner_shiftAvgCLM hc hK]
    have hpt : ∀ w : Plane,
        ⟪planeShiftL2CLM hc w x, cylSmoothToL2 (hΨ.dir (B0579.dir j))⟫_ℝ =
          -⟪planeShiftL2CLM hc w dx, cylSmoothToL2 hΨ⟫_ℝ := by
      intro w
      let ψw : B0579.Plane → ℝ := fun z => ψ (z - (-w))
      have hψw : B0579.IsCylTest c ψw := by
        refine ⟨hψ.smooth.comp (contDiff_id.sub contDiff_const), fun z => ?_, ?_⟩
        · dsimp [ψw]
          have hz : (z.1 + c, z.2) - (-w) = ((z - (-w)).1 + c, (z - (-w)).2) := by
            apply Prod.ext
            · simp; ring
            · simp
          rw [hz, hψ.periodic]
        · obtain ⟨R, hR⟩ := hψ.band
          refine ⟨R + |w.2|, fun z hz => ?_⟩
          dsimp [ψw]
          apply hR
          have htri : |z.2| ≤ |(z - (-w)).2| + |w.2| := by
            have heq : z.2 = (z - (-w)).2 - w.2 := by simp
            calc |z.2| = |(z - (-w)).2 - w.2| := by rw [heq]
              _ ≤ |(z - (-w)).2| + |w.2| := abs_sub _ _
          linarith
      have hpd_w : B0579.pd j ψw = fun z => B0579.pd j ψ (z - (-w)) := by
        funext z
        have hψw_eq : ψw = fun y => ψ (y + w) := by funext y; simp [ψw]
        unfold B0579.pd
        rw [hψw_eq, fderiv_comp_add_right (𝕜 := ℝ) (f := ψ) (x := z) w, sub_neg_eq_add]
      have hshift0 : planeShiftL2CLM hc (-w) (cylSmoothToL2 hΨ) =
          cylSmoothToL2 (isCylSmooth_single hψw k) := by
        apply Lp.ext
        have hae := planeShiftL2_ae_sub_of_cylSmooth hc hΨ (memLp_of_cylSmooth hΨ) (-w)
        filter_upwards [hae, (memLp_of_cylSmooth (isCylSmooth_single hψw k)).coeFn_toLp]
          with z h1 h2
        exact h1.trans h2.symm
      have hshift1 : planeShiftL2CLM hc (-w) (cylSmoothToL2 (hΨ.dir (B0579.dir j))) =
          cylSmoothToL2 (isCylSmooth_single (hψw.pd j) k) := by
        rw [htoLp_dir]
        apply Lp.ext
        have hae := planeShiftL2_ae_sub_of_cylSmooth hc (isCylSmooth_single (hψ.pd j) k)
          (memLp_of_cylSmooth (isCylSmooth_single (hψ.pd j) k)) (-w)
        filter_upwards [hae, (memLp_of_cylSmooth (isCylSmooth_single (hψw.pd j) k)).coeFn_toLp]
          with z h1 h2
        have hm : B0579.pd j ψ (z - (-w)) • EuclideanSpace.single k (1 : ℝ) =
            B0579.pd j ψw z • EuclideanSpace.single k (1 : ℝ) := by
          rw [hpd_w]
        exact h1.trans (hm.trans h2.symm)
      rw [inner_planeShiftL2CLM_adj hc w x, inner_planeShiftL2CLM_adj hc w dx,
        hshift0, hshift1, inner_cylSmooth_single (hψw.pd j) k x,
        inner_cylSmooth_single hψw k dx, (h k).2 ψw hψw]
    have hfun : (fun w : Plane => K w * ⟪planeShiftL2CLM hc w x,
        cylSmoothToL2 (hΨ.dir (B0579.dir j))⟫_ℝ) =
        fun w => -(K w * ⟪planeShiftL2CLM hc w dx, cylSmoothToL2 hΨ⟫_ℝ) := by
      funext w; rw [hpt w]; ring
    rw [hfun, integral_neg]

lemma DHeatCLM_eq_centeredHeat_of_weakDeriv {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {x dx : L2v c} {j : Fin 2}
    (h : ∀ k : Fin 2, HasWeakCellDerivR c j (fun y => x y k) (fun y => dx y k)) :
    DHeatCLM hc j θ x = centeredHeatVecL2CLM hc θ dx := by
  refine eq_of_hasWeakCellDerivR hc (hasWeakCellDerivR_DHeatCLM hc j hθ x) ?_
  intro k
  have havg := hasWeakCellDerivR_shiftAvgCLM hc
    (integrable_prod_plane (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
      (UnforcedLeray.B0296.integrable_heatKernel1 hθ)) h k
  have hx := centeredHeat_eq_shiftAvgCLM hc hθ x
  have hdx := centeredHeat_eq_shiftAvgCLM hc hθ dx
  change HasWeakCellDerivR c j
    (fun y => (shiftAvgCLM hc (heatKernel2 θ) _ x : Plane → Vec2) y k)
    (fun y => (shiftAvgCLM hc (heatKernel2 θ) _ dx : Plane → Vec2) y k) at havg
  rwa [← hx, ← hdx] at havg

lemma hasWeakCellDerivR_centeredHeatVecL2CLM {c : ℝ} (hc : 0 < c) (θ : ℝ)
    {x dx : L2v c} {j : Fin 2}
    (h : ∀ k : Fin 2, HasWeakCellDerivR c j (fun y => x y k) (fun y => dx y k)) :
    ∀ k : Fin 2, HasWeakCellDerivR c j
      (fun y => (centeredHeatVecL2CLM hc θ x : Plane → Vec2) y k)
      (fun y => (centeredHeatVecL2CLM hc θ dx : Plane → Vec2) y k) := by
  by_cases hθ : 0 < θ
  · intro k
    have havg := hasWeakCellDerivR_shiftAvgCLM hc
      (integrable_prod_plane (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
        (UnforcedLeray.B0296.integrable_heatKernel1 hθ)) h k
    have hx := centeredHeat_eq_shiftAvgCLM hc hθ x
    have hdx := centeredHeat_eq_shiftAvgCLM hc hθ dx
    change HasWeakCellDerivR c j
      (fun y => (shiftAvgCLM hc (heatKernel2 θ) _ x : Plane → Vec2) y k)
      (fun y => (shiftAvgCLM hc (heatKernel2 θ) _ dx : Plane → Vec2) y k) at havg
    rwa [← hx, ← hdx] at havg
  · rw [centeredHeatVecL2CLM_eq_id_of_nonpos hc (not_lt.mp hθ)]
    exact h

private lemma weightedToCell_of_toLp {c : ℝ} (u : L2v c)
    {F : Plane → Vec2} (hF : MemLp F 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))))
    (hFae : (u : Plane → Vec2) =ᵐ[cellμ c] F) :
    UnforcedLeray.TrainB.weightedToCellL2Isometry c (hF.toLp F) = u := by
  apply Lp.ext
  let hMP : MeasurePreserving id (cellμ c)
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← UnforcedLeray.TrainB.vecH1_measure_eq_cell c]
    exact MeasurePreserving.id _
  have hcomp := Lp.coeFn_compMeasurePreserving (hF.toLp F) hMP
  have hFcell := hMP.quasiMeasurePreserving.ae hF.coeFn_toLp
  filter_upwards [hcomp, hFcell, hFae] with z hzComp hzF hzU
  calc
    ((Lp.compMeasurePreserving id hMP (hF.toLp F) : L2v c) : Plane → Vec2) z =
        (hF.toLp F : Lp Vec2 2
          (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
            (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)))) z := by
            simpa [Function.comp_id] using hzComp
    _ = F z := hzF
    _ = (u : Plane → Vec2) z := hzU.symm

lemma hasWeakCellDerivR_P0 {c : ℝ} (hc : 0 < c)
    {u duq duη : L2v c}
    (hq : ∀ k : Fin 2, HasWeakCellDerivR c 0 (fun y => u y k) (fun y => duq y k))
    (hη : ∀ k : Fin 2, HasWeakCellDerivR c 1 (fun y => u y k) (fun y => duη y k)) :
    (∀ k : Fin 2, HasWeakCellDerivR c 0 (fun y => (P0 c u) y k) (fun y => (P0 c duq) y k)) ∧
    (∀ k : Fin 2, HasWeakCellDerivR c 1 (fun y => (P0 c u) y k) (fun y => (P0 c duη) y k)) := by
  let g : UnforcedLeray.Sob.Idx 2 1 → Plane → Vec2 := fun α =>
    if α = UnforcedLeray.Sob.Idx.zero then (u : Plane → Vec2)
    else if α = UnforcedLeray.Cyl.iQ then (duq : Plane → Vec2)
    else (duη : Plane → Vec2)
  have hmem : ∀ α, MemLp (g α) 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) := by
    intro α
    dsimp [g]
    split_ifs <;> exact UnforcedLeray.TrainB.memLp_cell_to_weighted _
  have h0 : g UnforcedLeray.Sob.Idx.zero = (u : Plane → Vec2) := by simp [g]
  have hQ : g UnforcedLeray.Cyl.iQ = (duq : Plane → Vec2) := by
    simp [g, UnforcedLeray.Cyl.idx_ne.1.symm]
  have hE : g UnforcedLeray.Cyl.iEta = (duη : Plane → Vec2) := by
    simp [g, UnforcedLeray.Cyl.idx_ne.2.1.symm, UnforcedLeray.Cyl.idx_ne.2.2.symm]
  have hweak : ∀ α : UnforcedLeray.Sob.Idx 2 1,
      UnforcedLeray.Sob.HasWeakDeriv (UnforcedLeray.Sob.cylinder c)
        ((UnforcedLeray.Sob.cylinder c).word α) (g UnforcedLeray.Sob.Idx.zero) (g α) := by
    intro α
    have hm : α ∈ (Finset.univ : Finset (UnforcedLeray.Sob.Idx 2 1)) := Finset.mem_univ α
    rw [UnforcedLeray.Cyl.univ_idx_two_one] at hm
    rcases (by simpa using hm : α = UnforcedLeray.Sob.Idx.zero ∨
        α = UnforcedLeray.Cyl.iQ ∨ α = UnforcedLeray.Cyl.iEta) with rfl | rfl | rfl
    · rw [UnforcedLeray.Cyl.word_zero]
      exact UnforcedLeray.Sob.HasWeakDeriv.nil fun φ hφ =>
        UnforcedLeray.Sob.integrable_smul_of_memLp
          (UnforcedLeray.Sob.CompactlyBounded.of_adm hφ) (hmem _)
    · rw [UnforcedLeray.Cyl.word_iQ, h0, hQ]
      exact (hasWeakCellDerivR_of_vecH1 u duq 0).1 hq
    · rw [UnforcedLeray.Cyl.word_iEta, h0, hE]
      exact (hasWeakCellDerivR_of_vecH1 u duη 1).1 hη
  let x : UnforcedLeray.TrainB.VecH1 c :=
    UnforcedLeray.Sob.W.ofFields (D := UnforcedLeray.Sob.cylinder c)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2)
      g hmem hweak
  have hx0 : UnforcedLeray.TrainB.vecH1ValueCellCLM_MP x = u := by
    change UnforcedLeray.TrainB.weightedToCellL2Isometry c
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 1 2 x) = u
    rw [UnforcedLeray.Sob.W.value_ofFields]
    exact weightedToCell_of_toLp u (hmem UnforcedLeray.Sob.Idx.zero) (by rw [h0])
  have hxq : UnforcedLeray.TrainB.vecH1DqCellCLM_MP x = duq := by
    change UnforcedLeray.TrainB.weightedToCellL2Isometry c
      (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 1 2 UnforcedLeray.Cyl.iQ x) = duq
    rw [UnforcedLeray.Sob.W.deriv_ofFields]
    exact weightedToCell_of_toLp duq (hmem UnforcedLeray.Cyl.iQ) (by rw [hQ])
  have hxe : UnforcedLeray.TrainB.vecH1DetaCellCLM_MP x = duη := by
    change UnforcedLeray.TrainB.weightedToCellL2Isometry c
      (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 1 2 UnforcedLeray.Cyl.iEta x) = duη
    rw [UnforcedLeray.Sob.W.deriv_ofFields]
    exact weightedToCell_of_toLp duη (hmem UnforcedLeray.Cyl.iEta) (by rw [hE])
  have hpq := UnforcedLeray.TrainB.hasWeakDeriv_P0_q_of_vecH1 hc x
  have hpe := UnforcedLeray.TrainB.hasWeakDeriv_P0_eta_of_vecH1 hc x
  rw [hx0, hxq] at hpq
  rw [hx0, hxe] at hpe
  exact ⟨(hasWeakCellDerivR_of_vecH1 _ _ 0).2 hpq, (hasWeakCellDerivR_of_vecH1 _ _ 1).2 hpe⟩

/-! ## 7. Heat generator / age derivative of inner products -/

private def d2HeatKernel1 (θ x : ℝ) : ℝ :=
  UnforcedLeray.B0191.heatKernel 1 θ x * (x ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ))

private lemma hasDerivAt_dHeatKernel_one {θ x : ℝ} (hθ : 0 < θ) :
    HasDerivAt (UnforcedLeray.B0296.dHeatKernel θ) (d2HeatKernel1 θ x) x := by
  have hlin : HasDerivAt (fun y : ℝ => -(y / (2 * θ))) (-(1 / (2 * θ))) x := by
    refine (((hasDerivAt_id x).div_const (2 * θ)).neg).congr_deriv ?_
    ring
  have hg := UnforcedLeray.B0296.hasDerivAt_heatKernel hθ.ne' x
  have hp := hlin.mul hg
  refine hp.congr_deriv ?_
  unfold d2HeatKernel1 UnforcedLeray.B0296.dHeatKernel
  field_simp [hθ.ne']
  ring

private lemma integrable_d2HeatKernel1 {θ : ℝ} (hθ : 0 < θ) :
    Integrable (d2HeatKernel1 θ) volume := by
  have h0 := UnforcedLeray.B0296.integrable_heatKernel1 hθ
  have h2 := integrable_sq_mul_heatKernel1 hθ
  have hsub := (h2.div_const (4 * θ ^ 2)).sub (h0.div_const (2 * θ))
  refine hsub.congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply, d2HeatKernel1]
  ring

private lemma heatKernel2AgeDeriv_eq_sum {θ : ℝ} (hθ : 0 < θ) (w : Plane) :
    heatKernel2AgeDerivative θ w =
      d2HeatKernel1 θ w.1 * UnforcedLeray.B0191.heatKernel 1 θ w.2 +
        UnforcedLeray.B0191.heatKernel 1 θ w.1 * d2HeatKernel1 θ w.2 := by
  unfold heatKernel2AgeDerivative d2HeatKernel1 heatKernel2
  field_simp [hθ.ne']
  ring

/-- Age derivative of `θ ↦ ⟪cylSmoothToL2 hΦ, centeredHeatVecL2CLM hc θ x⟫` at `θ > 0`. -/
lemma hasDerivAt_inner_centeredHeatVecL2CLM {c : ℝ} (hc : 0 < c) {θ : ℝ} (hθ : 0 < θ)
    {Φ : Plane → Vec2} (hΦ : UnforcedLeray.Sob.IsCylSmooth c Φ) (x : L2v c) :
    HasDerivAt (fun s : ℝ => ⟪cylSmoothToL2 hΦ, centeredHeatVecL2CLM hc s x⟫_ℝ)
      (-⟪cylSmoothToL2 (hΦ.dir ((1 : ℝ), (0 : ℝ))), DHeatCLM hc 0 θ x⟫_ℝ -
        ⟪cylSmoothToL2 (hΦ.dir ((0 : ℝ), (1 : ℝ))), DHeatCLM hc 1 θ x⟫_ℝ) θ := by
  set φ₀ := cylSmoothToL2 hΦ
  set h : Plane → ℝ := fun w => ⟪planeShiftL2CLM hc w x, φ₀⟫_ℝ
  have hcont : Continuous h :=
    continuous_inner.comp ((continuous_planeShiftL2_orbit hc x).prodMk continuous_const)
  let M : ℝ := ‖x‖ * ‖φ₀‖
  have hM : 0 ≤ M := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hbound : ∀ w : Plane, ‖h w‖ ≤ M := fun w =>
    (abs_real_inner_le_norm _ _).trans (by rw [norm_planeShiftL2CLM hc w x])
  let F : ℝ → Plane → ℝ := fun s w => heatKernel2 s w * h w
  let F' : ℝ → Plane → ℝ := fun s w => heatKernel2AgeDerivative s w * h w
  have hball : Ioo (θ / 2) (2 * θ) ∈ 𝓝 θ := Ioo_mem_nhds (by linarith) (by linarith)
  have hwide : Integrable (fun w : Plane => (1 + w.1 ^ 2 + w.2 ^ 2) * heatKernel2 (2 * θ) w) :=
    integrable_one_add_sq_mul_heatKernel2 (by positivity)
  let A : ℝ := 4 * (θ⁻¹ ^ 2 + 2 / θ)
  have hdomInt : Integrable
      (fun w : Plane => A * M * ((1 + w.1 ^ 2 + w.2 ^ 2) * heatKernel2 (2 * θ) w)) :=
    hwide.const_mul (A * M)
  have hFmeas : ∀ᶠ s : ℝ in 𝓝 θ, AEStronglyMeasurable (F s) volume := by
    filter_upwards [] with s
    have hk : Continuous (heatKernel2 s) := by
      unfold UnforcedLeray.B0284.heatKernel2 UnforcedLeray.B0191.heatKernel; fun_prop
    exact (hk.mul hcont).aestronglyMeasurable
  have hFint : Integrable (F θ) volume :=
    integrable_mul_bounded_plane (UnforcedLeray.B0284.integrable_heatKernel2 hθ) hcont hbound
  have hFprimeMeas : AEStronglyMeasurable (F' θ) volume := by
    have hk : Measurable (heatKernel2AgeDerivative θ) := by
      unfold heatKernel2AgeDerivative UnforcedLeray.B0284.heatKernel2
        UnforcedLeray.B0191.heatKernel; fun_prop
    exact (hk.mul hcont.measurable).aestronglyMeasurable
  have hFprimeBound : ∀ᵐ w ∂(volume : Measure Plane), ∀ s ∈ Ioo (θ / 2) (2 * θ),
      ‖F' s w‖ ≤ A * M * ((1 + w.1 ^ 2 + w.2 ^ 2) * heatKernel2 (2 * θ) w) := by
    filter_upwards [] with w s hs
    have hloc := abs_heatKernel2AgeDerivative_le_local (θ₀ := θ) hθ hs.1 hs.2 w
    rw [Real.norm_eq_abs]
    dsimp only [F', A]
    rw [abs_mul]
    calc
      |heatKernel2AgeDerivative s w| * |h w|
          ≤ |heatKernel2AgeDerivative s w| * M :=
            mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hbound w) (abs_nonneg _)
      _ ≤ (4 * (θ⁻¹ ^ 2 + 2 / θ) * ((1 + w.1 ^ 2 + w.2 ^ 2) * heatKernel2 (2 * θ) w)) * M :=
            mul_le_mul_of_nonneg_right hloc hM
      _ = 4 * (θ⁻¹ ^ 2 + 2 / θ) * M * ((1 + w.1 ^ 2 + w.2 ^ 2) * heatKernel2 (2 * θ) w) := by ring
  have hdiff : ∀ᵐ w ∂(volume : Measure Plane), ∀ s ∈ Ioo (θ / 2) (2 * θ),
      HasDerivAt (F · w) (F' s w) s := by
    filter_upwards [] with w s hs
    have hpos : 0 < s := lt_trans (by positivity) hs.1
    exact (hasDerivAt_heatKernel2_age hpos w).mul_const (h w)
  have hparam := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure Plane)) (F := F) (F' := F')
    (bound := fun w => A * M * ((1 + w.1 ^ 2 + w.2 ^ 2) * heatKernel2 (2 * θ) w))
    hball hFmeas hFint hFprimeMeas hFprimeBound hdomInt hdiff).2
  have hev : (fun s : ℝ => ∫ w : Plane, F s w) =ᶠ[𝓝 θ]
      fun s => ⟪φ₀, centeredHeatVecL2CLM hc s x⟫_ℝ := by
    filter_upwards [Ioi_mem_nhds hθ] with s hs
    have hs' : 0 < s := hs
    have h1 : ⟪φ₀, centeredHeatVecL2CLM hc s x⟫_ℝ =
        ⟪shiftAvgCLM hc (heatKernel2 s)
          (integrable_prod_plane (UnforcedLeray.B0296.integrable_heatKernel1 hs')
            (UnforcedLeray.B0296.integrable_heatKernel1 hs')) x, φ₀⟫_ℝ := by
      rw [real_inner_comm, centeredHeat_eq_shiftAvgCLM hc hs' x]
    exact (inner_shiftAvgCLM hc
      (integrable_prod_plane (UnforcedLeray.B0296.integrable_heatKernel1 hs')
        (UnforcedLeray.B0296.integrable_heatKernel1 hs')) x φ₀).symm.trans h1.symm
  have hd_eq : ∫ w : Plane, F' θ w =
      -⟪cylSmoothToL2 (hΦ.dir ((1 : ℝ), (0 : ℝ))), DHeatCLM hc 0 θ x⟫_ℝ -
        ⟪cylSmoothToL2 (hΦ.dir ((0 : ℝ), (1 : ℝ))), DHeatCLM hc 1 θ x⟫_ℝ := by
    have hsplit : (fun w : Plane => F' θ w) =
        fun w => (d2HeatKernel1 θ w.1 * UnforcedLeray.B0191.heatKernel 1 θ w.2) * h w +
          (UnforcedLeray.B0191.heatKernel 1 θ w.1 * d2HeatKernel1 θ w.2) * h w := by
      funext w; dsimp [F']; rw [heatKernel2AgeDeriv_eq_sum hθ w]; ring
    have hi1 : Integrable (fun w : Plane =>
        (d2HeatKernel1 θ w.1 * UnforcedLeray.B0191.heatKernel 1 θ w.2) * h w) :=
      integrable_mul_bounded_plane (integrable_prod_plane (integrable_d2HeatKernel1 hθ)
        (UnforcedLeray.B0296.integrable_heatKernel1 hθ)) hcont hbound
    have hi2 : Integrable (fun w : Plane =>
        (UnforcedLeray.B0191.heatKernel 1 θ w.1 * d2HeatKernel1 θ w.2) * h w) :=
      integrable_mul_bounded_plane (integrable_prod_plane
        (UnforcedLeray.B0296.integrable_heatKernel1 hθ) (integrable_d2HeatKernel1 hθ)) hcont hbound
    rw [hsplit, integral_add hi1 hi2,
      ← inner_shiftAvgCLM hc (integrable_prod_plane (integrable_d2HeatKernel1 hθ)
        (UnforcedLeray.B0296.integrable_heatKernel1 hθ)) x φ₀,
      ← inner_shiftAvgCLM hc (integrable_prod_plane
        (UnforcedLeray.B0296.integrable_heatKernel1 hθ) (integrable_d2HeatKernel1 hθ)) x φ₀]
    have hibpq := inner_shiftAvg_prod_ibp_q hc
      (UnforcedLeray.B0296.integrable_dHeatKernel hθ) (integrable_d2HeatKernel1 hθ)
      (UnforcedLeray.B0296.integrable_heatKernel1 hθ) (fun _ => hasDerivAt_dHeatKernel_one hθ) hΦ x
    have hibpe := inner_shiftAvg_prod_ibp_eta hc
      (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
      (UnforcedLeray.B0296.integrable_dHeatKernel hθ) (integrable_d2HeatKernel1 hθ)
      (fun _ => hasDerivAt_dHeatKernel_one hθ) hΦ x
    have hc0 : ⟪cylSmoothToL2 (hΦ.dir ((1 : ℝ), (0 : ℝ))), DHeatCLM hc 0 θ x⟫_ℝ =
        ⟪DHeatCLM hc 0 θ x, cylSmoothToL2 (hΦ.dir ((1 : ℝ), (0 : ℝ)))⟫_ℝ := real_inner_comm _ _
    have hc1 : ⟪cylSmoothToL2 (hΦ.dir ((0 : ℝ), (1 : ℝ))), DHeatCLM hc 1 θ x⟫_ℝ =
        ⟪DHeatCLM hc 1 θ x, cylSmoothToL2 (hΦ.dir ((0 : ℝ), (1 : ℝ)))⟫_ℝ := real_inner_comm _ _
    have heq0 : shiftAvgCLM hc (gradKernelCoord 0 θ) (integrable_gradKernelCoord 0 hθ) x =
        shiftAvgCLM hc (fun w => UnforcedLeray.B0296.dHeatKernel θ w.1 *
          UnforcedLeray.B0191.heatKernel 1 θ w.2)
          (integrable_prod_plane (UnforcedLeray.B0296.integrable_dHeatKernel hθ)
            (UnforcedLeray.B0296.integrable_heatKernel1 hθ)) x := rfl
    have heq1 : shiftAvgCLM hc (gradKernelCoord 1 θ) (integrable_gradKernelCoord 1 hθ) x =
        shiftAvgCLM hc (fun w => UnforcedLeray.B0191.heatKernel 1 θ w.1 *
          UnforcedLeray.B0296.dHeatKernel θ w.2)
          (integrable_prod_plane (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
            (UnforcedLeray.B0296.integrable_dHeatKernel hθ)) x := rfl
    rw [hc0, hc1, DHeatCLM_of_pos hc 0 hθ, DHeatCLM_of_pos hc 1 hθ, heq0, heq1]
    dsimp only [φ₀] at hibpq hibpe ⊢
    linarith [hibpq, hibpe]
  rw [← hd_eq]
  exact hparam.congr_of_eventuallyEq hev.symm

/-! ## 8. Solenoidal `H¹_σ(C_c)` Banach space `H1Sol c`, `freeH1CLM`, `duhH1CLM`, `scalarMultCLM` -/

abbrev TripleL2 (c : ℝ) : Type := L2v c × L2v c × L2v c

lemma hasWeakCellDerivR_l2_iff {c : ℝ} (x dx : L2v c) (j : Fin 2) :
    (∀ k : Fin 2, HasWeakCellDerivR c j (fun y => x y k) (fun y => dx y k)) ↔
      ∀ (ψ : Plane → ℝ) (hψ : B0579.IsCylTest c ψ) (k : Fin 2),
        ⟪x, cylSmoothToL2 (isCylSmooth_single (hψ.pd j) k)⟫_ℝ +
          ⟪dx, cylSmoothToL2 (isCylSmooth_single hψ k)⟫_ℝ = 0 := by
  constructor
  · intro h ψ hψ k
    rw [inner_cylSmooth_single (hψ.pd j) k x, inner_cylSmooth_single hψ k dx, (h k).2 ψ hψ]
    ring
  · intro h k
    refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
    · have hmψ : MemLp ψ 2 (cellμ c) := memLp_cellμ_of_test hψ
      have hmpd : MemLp (B0579.pd j ψ) 2 (cellμ c) := memLp_cellμ_of_test (hψ.pd j)
      rw [b0579_cell_eq_cyl_cell]
      exact ⟨(UnforcedLeray.Cyl.memLp_component x k).integrable_mul hmpd,
        (UnforcedLeray.Cyl.memLp_component dx k).integrable_mul hmψ⟩
    · have hk := h ψ hψ k
      rw [inner_cylSmooth_single (hψ.pd j) k x, inner_cylSmooth_single hψ k dx] at hk
      linarith

def H1Sol (c : ℝ) : Submodule ℝ (TripleL2 c) where
  carrier := {p | p.1 ∈ divFree c ∧
    (∀ (ψ : Plane → ℝ) (hψ : B0579.IsCylTest c ψ) (k : Fin 2),
      ⟪p.1, cylSmoothToL2 (isCylSmooth_single (hψ.pd 0) k)⟫_ℝ +
        ⟪p.2.1, cylSmoothToL2 (isCylSmooth_single hψ k)⟫_ℝ = 0) ∧
    (∀ (ψ : Plane → ℝ) (hψ : B0579.IsCylTest c ψ) (k : Fin 2),
      ⟪p.1, cylSmoothToL2 (isCylSmooth_single (hψ.pd 1) k)⟫_ℝ +
        ⟪p.2.2, cylSmoothToL2 (isCylSmooth_single hψ k)⟫_ℝ = 0)}
  zero_mem' := ⟨(divFree c).zero_mem, fun _ _ _ => by simp, fun _ _ _ => by simp⟩
  add_mem' {p q} hp hq := ⟨(divFree c).add_mem hp.1 hq.1,
    fun ψ hψ k => by
      simp only [Prod.fst_add, Prod.snd_add, inner_add_left]
      linarith [hp.2.1 ψ hψ k, hq.2.1 ψ hψ k],
    fun ψ hψ k => by
      simp only [Prod.fst_add, Prod.snd_add, inner_add_left]
      linarith [hp.2.2 ψ hψ k, hq.2.2 ψ hψ k]⟩
  smul_mem' r {p} hp := ⟨(divFree c).smul_mem r hp.1,
    fun ψ hψ k => by
      simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_left, RCLike.conj_to_real]
      linear_combination r * hp.2.1 ψ hψ k,
    fun ψ hψ k => by
      simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_left, RCLike.conj_to_real]
      linear_combination r * hp.2.2 ψ hψ k⟩

lemma isClosed_H1Sol (c : ℝ) : IsClosed (H1Sol c : Set (TripleL2 c)) := by
  have heq : (H1Sol c : Set (TripleL2 c)) =
      (Prod.fst ⁻¹' (divFree c : Set (L2v c))) ∩
      ((⋂ (ψ : Plane → ℝ) (hψ : B0579.IsCylTest c ψ) (k : Fin 2),
        {p : TripleL2 c |
          ⟪p.1, cylSmoothToL2 (isCylSmooth_single (hψ.pd 0) k)⟫_ℝ +
            ⟪p.2.1, cylSmoothToL2 (isCylSmooth_single hψ k)⟫_ℝ = 0}) ∩
       (⋂ (ψ : Plane → ℝ) (hψ : B0579.IsCylTest c ψ) (k : Fin 2),
        {p : TripleL2 c |
          ⟪p.1, cylSmoothToL2 (isCylSmooth_single (hψ.pd 1) k)⟫_ℝ +
            ⟪p.2.2, cylSmoothToL2 (isCylSmooth_single hψ k)⟫_ℝ = 0})) := by
    ext p
    simp [H1Sol]
  rw [heq]
  refine ((UnforcedLeray.Cyl.isClosed_divFree c).preimage continuous_fst).inter (IsClosed.inter ?_ ?_)
  · refine isClosed_iInter fun ψ => isClosed_iInter fun hψ => isClosed_iInter fun k => ?_
    exact isClosed_eq
      ((continuous_fst.inner continuous_const).add
        ((continuous_fst.comp continuous_snd).inner continuous_const))
      continuous_const
  · refine isClosed_iInter fun ψ => isClosed_iInter fun hψ => isClosed_iInter fun k => ?_
    exact isClosed_eq
      ((continuous_fst.inner continuous_const).add
        ((continuous_snd.comp continuous_snd).inner continuous_const))
      continuous_const

instance completeSpace_H1Sol (c : ℝ) : CompleteSpace (H1Sol c) :=
  (isClosed_H1Sol c).completeSpace_coe

def val0CLM (c : ℝ) : H1Sol c →L[ℝ] L2v c :=
  (ContinuousLinearMap.fst ℝ (L2v c) (L2v c × L2v c)).comp (H1Sol c).subtypeL

def dqCLM (c : ℝ) : H1Sol c →L[ℝ] L2v c :=
  ((ContinuousLinearMap.fst ℝ (L2v c) (L2v c)).comp
    (ContinuousLinearMap.snd ℝ (L2v c) (L2v c × L2v c))).comp (H1Sol c).subtypeL

def detaCLM (c : ℝ) : H1Sol c →L[ℝ] L2v c :=
  ((ContinuousLinearMap.snd ℝ (L2v c) (L2v c)).comp
    (ContinuousLinearMap.snd ℝ (L2v c) (L2v c × L2v c))).comp (H1Sol c).subtypeL

@[simp] lemma val0CLM_apply {c : ℝ} (p : H1Sol c) : val0CLM c p = p.1.1 := rfl
@[simp] lemma dqCLM_apply {c : ℝ} (p : H1Sol c) : dqCLM c p = p.1.2.1 := rfl
@[simp] lemma detaCLM_apply {c : ℝ} (p : H1Sol c) : detaCLM c p = p.1.2.2 := rfl

lemma norm_val0CLM_le {c : ℝ} (p : H1Sol c) : ‖val0CLM c p‖ ≤ ‖p‖ :=
  norm_fst_le p.1

lemma norm_dqCLM_le {c : ℝ} (p : H1Sol c) : ‖dqCLM c p‖ ≤ ‖p‖ :=
  (norm_fst_le p.1.2).trans (norm_snd_le p.1)

lemma norm_detaCLM_le {c : ℝ} (p : H1Sol c) : ‖detaCLM c p‖ ≤ ‖p‖ :=
  (norm_snd_le p.1.2).trans (norm_snd_le p.1)

lemma H1Sol.mem_divFree {c : ℝ} (p : H1Sol c) : val0CLM c p ∈ divFree c := p.2.1

lemma H1Sol.weak_q {c : ℝ} (p : H1Sol c) :
    ∀ k : Fin 2, HasWeakCellDerivR c 0
      (fun y => (val0CLM c p : Plane → Vec2) y k)
      (fun y => (dqCLM c p : Plane → Vec2) y k) :=
  (hasWeakCellDerivR_l2_iff (val0CLM c p) (dqCLM c p) 0).2 p.2.2.1

lemma H1Sol.weak_eta {c : ℝ} (p : H1Sol c) :
    ∀ k : Fin 2, HasWeakCellDerivR c 1
      (fun y => (val0CLM c p : Plane → Vec2) y k)
      (fun y => (detaCLM c p : Plane → Vec2) y k) :=
  (hasWeakCellDerivR_l2_iff (val0CLM c p) (detaCLM c p) 1).2 p.2.2.2

def H1Sol.mkOfWeak {c : ℝ} (u uq uη : L2v c) (hdiv : u ∈ divFree c)
    (hq : ∀ k : Fin 2, HasWeakCellDerivR c 0 (fun y => u y k) (fun y => uq y k))
    (hη : ∀ k : Fin 2, HasWeakCellDerivR c 1 (fun y => u y k) (fun y => uη y k)) :
    H1Sol c :=
  ⟨(u, uq, uη), hdiv, (hasWeakCellDerivR_l2_iff u uq 0).1 hq,
    (hasWeakCellDerivR_l2_iff u uη 1).1 hη⟩

lemma H1Sol.ext_val0 {c : ℝ} (hc : 0 < c) {p q : H1Sol c}
    (h : val0CLM c p = val0CLM c q) : p = q := by
  apply Subtype.ext
  refine Prod.ext h (Prod.ext ?_ ?_)
  · refine eq_of_hasWeakCellDerivR hc (H1Sol.weak_q p) (fun k => ?_)
    have hqk := H1Sol.weak_q q k
    rwa [← h] at hqk
  · refine eq_of_hasWeakCellDerivR hc (H1Sol.weak_eta p) (fun k => ?_)
    have hηk := H1Sol.weak_eta q k
    rwa [← h] at hηk

lemma hasWeakCellDerivR_congr_ae {c : ℝ} {j : Fin 2} {φ₁ φ₂ g₁ g₂ : Plane → ℝ}
    (hφ : φ₁ =ᵐ[cellμ c] φ₂) (hg : g₁ =ᵐ[cellμ c] g₂)
    (h1 : HasWeakCellDerivR c j φ₁ g₁) :
    HasWeakCellDerivR c j φ₂ g₂ := by
  rw [← restrict_b0579_cell_eq_cellμ] at hφ hg
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · obtain ⟨i1, i2⟩ := h1.1 ψ hψ
    refine ⟨i1.congr ?_, i2.congr ?_⟩
    · filter_upwards [hφ] with y hy; rw [hy]
    · filter_upwards [hg] with y hy; rw [hy]
  · have e1 : ∫ y in B0579.cell c, φ₂ y * B0579.pd j ψ y =
        ∫ y in B0579.cell c, φ₁ y * B0579.pd j ψ y := by
      refine integral_congr_ae ?_
      filter_upwards [hφ] with y hy; rw [hy]
    have e2 : ∫ y in B0579.cell c, g₂ y * ψ y = ∫ y in B0579.cell c, g₁ y * ψ y := by
      refine integral_congr_ae ?_
      filter_upwards [hg] with y hy; rw [hy]
    rw [e1, e2, h1.2 ψ hψ]

lemma isRealCellSolenoidal_congr_ae {c : ℝ} {f₁ f₂ : Plane → Vec2}
    (hf : f₁ =ᵐ[cellμ c] f₂) (h1 : IsRealCellSolenoidal c f₁) :
    IsRealCellSolenoidal c f₂ := by
  rw [← restrict_b0579_cell_eq_cellμ] at hf
  intro ψ hψ
  obtain ⟨hi, hz⟩ := h1 ψ hψ
  have hae : (fun y => f₁ y 0 * B0579.pd 0 ψ y + f₁ y 1 * B0579.pd 1 ψ y) =ᵐ[volume.restrict (B0579.cell c)]
      fun y => f₂ y 0 * B0579.pd 0 ψ y + f₂ y 1 * B0579.pd 1 ψ y := by
    filter_upwards [hf] with y hy; rw [hy]
  exact ⟨hi.congr hae, (integral_congr_ae hae.symm).trans hz⟩

def freeH1Fun {c : ℝ} (hc : 0 < c) (θ : ℝ) (p : H1Sol c) : H1Sol c :=
  H1Sol.mkOfWeak
    (centeredHeatVecL2CLM hc θ (val0CLM c p))
    (centeredHeatVecL2CLM hc θ (dqCLM c p))
    (centeredHeatVecL2CLM hc θ (detaCLM c p))
    (by
      have hp0 : P0 c (val0CLM c p) = val0CLM c p :=
        UnforcedLeray.Cyl.P0_eq_self (H1Sol.mem_divFree p)
      have hc0 := centeredHeatVecL2CLM_P0_comm hc θ (val0CLM c p)
      rw [hp0] at hc0
      rw [hc0]
      exact UnforcedLeray.Cyl.P0_mem _)
    (hasWeakCellDerivR_centeredHeatVecL2CLM hc θ (H1Sol.weak_q p))
    (hasWeakCellDerivR_centeredHeatVecL2CLM hc θ (H1Sol.weak_eta p))

lemma norm_freeH1Fun_le {c : ℝ} (hc : 0 < c) (θ : ℝ) (p : H1Sol c) :
    ‖freeH1Fun hc θ p‖ ≤ 1 * ‖p‖ := by
  rw [one_mul]
  change max ‖centeredHeatVecL2CLM hc θ (val0CLM c p)‖
    (max ‖centeredHeatVecL2CLM hc θ (dqCLM c p)‖
      ‖centeredHeatVecL2CLM hc θ (detaCLM c p)‖) ≤ ‖p‖
  have b0 : ‖centeredHeatVecL2CLM hc θ (val0CLM c p)‖ ≤ ‖p‖ :=
    ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_centeredHeatVecL2CLM_le_one_all hc θ))).trans
      (norm_val0CLM_le p)
  have bq : ‖centeredHeatVecL2CLM hc θ (dqCLM c p)‖ ≤ ‖p‖ :=
    ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_centeredHeatVecL2CLM_le_one_all hc θ))).trans
      (norm_dqCLM_le p)
  have bη : ‖centeredHeatVecL2CLM hc θ (detaCLM c p)‖ ≤ ‖p‖ :=
    ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_centeredHeatVecL2CLM_le_one_all hc θ))).trans
      (norm_detaCLM_le p)
  exact max_le b0 (max_le bq bη)

def freeH1CLM {c : ℝ} (hc : 0 < c) (θ : ℝ) : H1Sol c →L[ℝ] H1Sol c :=
  LinearMap.mkContinuous
    { toFun := freeH1Fun hc θ
      map_add' := fun p q => by
        apply Subtype.ext
        dsimp [freeH1Fun, H1Sol.mkOfWeak]
        simp only [map_add]
      map_smul' := fun r p => by
        apply Subtype.ext
        dsimp [freeH1Fun, H1Sol.mkOfWeak]
        simp only [map_smul] }
    1 (norm_freeH1Fun_le hc θ)

@[simp] lemma val0_freeH1CLM {c : ℝ} (hc : 0 < c) (θ : ℝ) (p : H1Sol c) :
    val0CLM c (freeH1CLM hc θ p) = centeredHeatVecL2CLM hc θ (val0CLM c p) := rfl
@[simp] lemma dq_freeH1CLM {c : ℝ} (hc : 0 < c) (θ : ℝ) (p : H1Sol c) :
    dqCLM c (freeH1CLM hc θ p) = centeredHeatVecL2CLM hc θ (dqCLM c p) := rfl
@[simp] lemma deta_freeH1CLM {c : ℝ} (hc : 0 < c) (θ : ℝ) (p : H1Sol c) :
    detaCLM c (freeH1CLM hc θ p) = centeredHeatVecL2CLM hc θ (detaCLM c p) := rfl

lemma freeH1CLM_of_nonpos {c : ℝ} (hc : 0 < c) {θ : ℝ} (hθ : θ ≤ 0) :
    freeH1CLM hc θ = ContinuousLinearMap.id ℝ (H1Sol c) := by
  apply ContinuousLinearMap.ext
  intro p
  apply H1Sol.ext_val0 hc
  change val0CLM c (freeH1CLM hc θ p) = val0CLM c p
  rw [val0_freeH1CLM, centeredHeatVecL2CLM_eq_id_of_nonpos hc hθ]
  rfl

lemma norm_freeH1CLM_le {c : ℝ} (hc : 0 < c) (θ : ℝ) :
    ‖freeH1CLM hc θ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

lemma continuous_freeH1CLM_apply {c : ℝ} (hc : 0 < c) (p : H1Sol c) :
    Continuous (fun θ : ℝ => freeH1CLM hc θ p) := by
  rw [continuous_induced_rng]
  exact (continuous_centeredHeatVecL2CLM_apply hc (val0CLM c p)).prodMk
    ((continuous_centeredHeatVecL2CLM_apply hc (dqCLM c p)).prodMk
      (continuous_centeredHeatVecL2CLM_apply hc (detaCLM c p)))

def duhH1FunPos {c : ℝ} (hc : 0 < c) {θ : ℝ} (hθ : 0 < θ) (f : L2v c) : H1Sol c :=
  let hw := hasWeakCellDerivR_P0 hc
    (hasWeakCellDerivR_DHeatCLM hc 0 hθ f) (hasWeakCellDerivR_DHeatCLM hc 1 hθ f)
  H1Sol.mkOfWeak
    (P0 c (centeredHeatVecL2CLM hc θ f))
    (P0 c (DHeatCLM hc 0 θ f))
    (P0 c (DHeatCLM hc 1 θ f))
    (UnforcedLeray.Cyl.P0_mem _) hw.1 hw.2

lemma norm_duhH1FunPos_le {c : ℝ} (hc : 0 < c) {θ : ℝ} (hθ : 0 < θ) (f : L2v c) :
    ‖duhH1FunPos hc hθ f‖ ≤ max 1 (heatDivL2Coeff θ) * ‖f‖ := by
  change max ‖P0 c (centeredHeatVecL2CLM hc θ f)‖
    (max ‖P0 c (DHeatCLM hc 0 θ f)‖ ‖P0 c (DHeatCLM hc 1 θ f)‖) ≤ _
  have hP0 : ∀ z : L2v c, ‖P0 c z‖ ≤ ‖z‖ := fun z =>
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) UnforcedLeray.Cyl.norm_P0_le)
  have b0 : ‖P0 c (centeredHeatVecL2CLM hc θ f)‖ ≤ max 1 (heatDivL2Coeff θ) * ‖f‖ := by
    calc ‖P0 c (centeredHeatVecL2CLM hc θ f)‖
        ≤ ‖centeredHeatVecL2CLM hc θ f‖ := hP0 _
      _ ≤ 1 * ‖f‖ := (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (norm_centeredHeatVecL2CLM_le_one_all hc θ) (norm_nonneg _))
      _ ≤ max 1 (heatDivL2Coeff θ) * ‖f‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have bj : ∀ j : Fin 2, ‖P0 c (DHeatCLM hc j θ f)‖ ≤ max 1 (heatDivL2Coeff θ) * ‖f‖ := by
    intro j
    calc ‖P0 c (DHeatCLM hc j θ f)‖
        ≤ ‖DHeatCLM hc j θ f‖ := hP0 _
      _ ≤ heatDivL2Coeff θ * ‖f‖ := (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (norm_DHeatCLM_le hc j hθ) (norm_nonneg _))
      _ ≤ max 1 (heatDivL2Coeff θ) * ‖f‖ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  exact max_le b0 (max_le (bj 0) (bj 1))

def duhH1CLM {c : ℝ} (hc : 0 < c) (θ : ℝ) : L2v c →L[ℝ] H1Sol c :=
  if hθ : 0 < θ then
    LinearMap.mkContinuous
      { toFun := duhH1FunPos hc hθ
        map_add' := fun f g => by
          apply Subtype.ext
          dsimp [duhH1FunPos, H1Sol.mkOfWeak]
          simp only [map_add]
        map_smul' := fun r f => by
          apply Subtype.ext
          dsimp [duhH1FunPos, H1Sol.mkOfWeak]
          simp only [map_smul] }
      (max 1 (heatDivL2Coeff θ))
      (norm_duhH1FunPos_le hc hθ)
  else 0

lemma val0_duhH1CLM_of_pos {c : ℝ} (hc : 0 < c) {θ : ℝ} (hθ : 0 < θ) (f : L2v c) :
    val0CLM c (duhH1CLM hc θ f) = P0 c (centeredHeatVecL2CLM hc θ f) := by
  simp [duhH1CLM, hθ, duhH1FunPos, H1Sol.mkOfWeak]

lemma dq_duhH1CLM_of_pos {c : ℝ} (hc : 0 < c) {θ : ℝ} (hθ : 0 < θ) (f : L2v c) :
    dqCLM c (duhH1CLM hc θ f) = P0 c (DHeatCLM hc 0 θ f) := by
  simp [duhH1CLM, hθ, duhH1FunPos, H1Sol.mkOfWeak]

lemma deta_duhH1CLM_of_pos {c : ℝ} (hc : 0 < c) {θ : ℝ} (hθ : 0 < θ) (f : L2v c) :
    detaCLM c (duhH1CLM hc θ f) = P0 c (DHeatCLM hc 1 θ f) := by
  simp [duhH1CLM, hθ, duhH1FunPos, H1Sol.mkOfWeak]

lemma norm_duhH1CLM_le {c : ℝ} (hc : 0 < c) {θ : ℝ} (hθ : 0 < θ) :
    ‖duhH1CLM hc θ‖ ≤ max 1 (heatDivL2Coeff θ) := by
  simp only [duhH1CLM, hθ, ↓reduceDIte]
  exact LinearMap.mkContinuous_norm_le _ (le_trans zero_le_one (le_max_left _ _)) _

lemma continuousOn_duhH1CLM_apply {c : ℝ} (hc : 0 < c) (f : L2v c) :
    ContinuousOn (fun θ : ℝ => duhH1CLM hc θ f) (Ioi 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  rw [continuous_induced_rng]
  have h0 : Continuous (fun θ : Ioi (0 : ℝ) => P0 c (centeredHeatVecL2CLM hc θ.1 f)) :=
    (P0 c).continuous.comp ((continuous_centeredHeatVecL2CLM_apply hc f).comp continuous_subtype_val)
  have hq : Continuous (fun θ : Ioi (0 : ℝ) => P0 c (DHeatCLM hc 0 θ.1 f)) :=
    (P0 c).continuous.comp (continuousOn_iff_continuous_domRestrict.1 (continuousOn_DHeatCLM_apply hc 0 f))
  have hη : Continuous (fun θ : Ioi (0 : ℝ) => P0 c (DHeatCLM hc 1 θ.1 f)) :=
    (P0 c).continuous.comp (continuousOn_iff_continuous_domRestrict.1 (continuousOn_DHeatCLM_apply hc 1 f))
  refine (h0.prodMk (hq.prodMk hη)).congr fun θ => ?_
  have hpos : 0 < θ.1 := θ.2
  simp [duhH1CLM, hpos, duhH1FunPos, H1Sol.mkOfWeak]

/-! ## 9. Bounded scalar multiplication and rank-1 coordinate operators on `L2v c` -/

lemma memLp_scalarMult_cellμ {c : ℝ} {a : Plane → ℝ} (ha : Continuous a)
    {M : ℝ} (hb : ∀ y, |a y| ≤ M) (f : L2v c) :
    MemLp (fun y => a y • (f : Plane → Vec2) y) 2 (cellμ c) := by
  have hmeas : AEStronglyMeasurable (fun y => a y • (f : Plane → Vec2) y) (cellμ c) :=
    ha.aestronglyMeasurable.smul (Lp.aestronglyMeasurable f)
  refine ⟨hmeas, ?_⟩
  have hle : eLpNorm (fun y => a y • (f : Plane → Vec2) y) 2 (cellμ c) ≤
      eLpNorm (fun y => max M 0 • (f : Plane → Vec2) y) 2 (cellμ c) := by
    refine eLpNorm_mono_enorm fun y => ?_
    rw [enorm_smul, enorm_smul]
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_of_nonneg (le_max_right M 0)]
    exact ENNReal.ofReal_le_ofReal ((hb y).trans (le_max_left M 0))
  exact hle.trans_lt ((Lp.memLp f).const_smul (max M 0)).eLpNorm_lt_top

lemma norm_scalarMult_le {c : ℝ} {a : Plane → ℝ} (ha : Continuous a)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ y, |a y| ≤ M) (f : L2v c) :
    ‖(memLp_scalarMult_cellμ ha hb f).toLp (fun y => a y • (f : Plane → Vec2) y)‖ ≤ M * ‖f‖ := by
  let hm := memLp_scalarMult_cellμ ha hb f
  let g : L2v c := hm.toLp (fun y => a y • (f : Plane → Vec2) y)
  have hinner_le : ⟪g, g⟫_ℝ ≤ M ^ 2 * ⟪f, f⟫_ℝ := by
    rw [L2.inner_def, L2.inner_def, ← integral_const_mul]
    have hif := L2.integrable_inner (𝕜 := ℝ) f f
    have hig := L2.integrable_inner (𝕜 := ℝ) g g
    refine integral_mono_ae hig (hif.const_mul (M ^ 2)) ?_
    filter_upwards [hm.coeFn_toLp] with y hy
    change ⟪g y, g y⟫_ℝ ≤ M ^ 2 * ⟪(f : Plane → Vec2) y, (f : Plane → Vec2) y⟫_ℝ
    rw [hy, real_inner_smul_left, real_inner_smul_right, ← mul_assoc]
    have hsq : a y * a y ≤ M ^ 2 := by
      have h1 : |a y| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hb y) 2
      simpa [sq_abs, sq] using h1
    exact mul_le_mul_of_nonneg_right hsq real_inner_self_nonneg
  rw [norm_eq_sqrt_real_inner g, norm_eq_sqrt_real_inner f]
  calc Real.sqrt ⟪g, g⟫_ℝ
      ≤ Real.sqrt (M ^ 2 * ⟪f, f⟫_ℝ) := Real.sqrt_le_sqrt hinner_le
    _ = M * Real.sqrt ⟪f, f⟫_ℝ := by
        rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM]

def scalarMultCLM {c : ℝ} (a : Plane → ℝ) (ha : Continuous a)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ y, |a y| ≤ M) : L2v c →L[ℝ] L2v c :=
  LinearMap.mkContinuous
    { toFun := fun f =>
        (memLp_scalarMult_cellμ ha hb f).toLp (fun y => a y • (f : Plane → Vec2) y)
      map_add' := fun f₁ f₂ => by
        apply Lp.ext
        let hm1 := memLp_scalarMult_cellμ ha hb f₁
        let hm2 := memLp_scalarMult_cellμ ha hb f₂
        let hm12 := memLp_scalarMult_cellμ ha hb (f₁ + f₂)
        filter_upwards [hm12.coeFn_toLp, Lp.coeFn_add (hm1.toLp _) (hm2.toLp _),
          hm1.coeFn_toLp, hm2.coeFn_toLp, Lp.coeFn_add f₁ f₂] with y h12 hadd h1 h2 hfadd
        rw [h12, hfadd, Pi.add_apply, smul_add, hadd, Pi.add_apply, h1, h2]
      map_smul' := fun r f => by
        apply Lp.ext
        let hm := memLp_scalarMult_cellμ ha hb f
        let hmr := memLp_scalarMult_cellμ ha hb (r • f)
        simp only [RingHom.id_apply]
        filter_upwards [hmr.coeFn_toLp, Lp.coeFn_smul r (hm.toLp _),
          hm.coeFn_toLp, Lp.coeFn_smul r f] with y hr1 hr2 h1 hf
        rw [hr1, hf, Pi.smul_apply, smul_comm, hr2, Pi.smul_apply, h1] }
    M (norm_scalarMult_le ha hM hb)

lemma coeFn_scalarMultCLM {c : ℝ} {a : Plane → ℝ} (ha : Continuous a)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ y, |a y| ≤ M) (f : L2v c) :
    (scalarMultCLM a ha hM hb f : Plane → Vec2) =ᵐ[cellμ c] fun y => a y • (f : Plane → Vec2) y :=
  (memLp_scalarMult_cellμ ha hb f).coeFn_toLp

lemma norm_scalarMultCLM_le {c : ℝ} {a : Plane → ℝ} (ha : Continuous a)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ y, |a y| ≤ M) :
    ‖scalarMultCLM (c := c) a ha hM hb‖ ≤ M :=
  LinearMap.mkContinuous_norm_le _ hM _

lemma continuous_scalarMultCLM_apply {c : ℝ} {a : ℝ → Plane → ℝ}
    (ha : Continuous (Function.uncurry a))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ r y, |a r y| ≤ M) (f : L2v c) :
    Continuous (fun r : ℝ =>
      scalarMultCLM (a r) (ha.comp (continuous_const.prodMk continuous_id)) hM (hb r) f) := by
  have ha_r : ∀ r : ℝ, Continuous (a r) :=
    fun r => ha.comp (continuous_const.prodMk continuous_id)
  rw [continuous_iff_continuousAt]
  intro r₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  let F : ℝ → L2v c := fun r => scalarMultCLM (a r) (ha_r r) hM (hb r) f
  change Tendsto (fun r => ‖F r - F r₀‖) (𝓝 r₀) (𝓝 0)
  have hnorm_eq : ∀ r : ℝ, ‖F r - F r₀‖ =
      Real.sqrt (∫ y : Plane, (a r y - a r₀ y) ^ 2 * ⟪(f : Plane → Vec2) y, (f : Plane → Vec2) y⟫_ℝ
        ∂(cellμ c)) := by
    intro r
    rw [norm_eq_sqrt_real_inner (F r - F r₀)]
    congr 1
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    have hr := coeFn_scalarMultCLM (ha_r r) hM (hb r) f
    have hr₀ := coeFn_scalarMultCLM (ha_r r₀) hM (hb r₀) f
    filter_upwards [Lp.coeFn_sub (F r) (F r₀), hr, hr₀] with y hsub h1 h2
    change ⟪((F r - F r₀ : L2v c) : Plane → Vec2) y, ((F r - F r₀ : L2v c) : Plane → Vec2) y⟫_ℝ = _
    rw [hsub, Pi.sub_apply, h1, h2, ← sub_smul, real_inner_smul_left, real_inner_smul_right,
      ← mul_assoc, sq]
  simp_rw [hnorm_eq]
  have hsqrt0 : Real.sqrt 0 = 0 := Real.sqrt_zero
  rw [← hsqrt0]
  refine (Real.continuous_sqrt.tendsto 0).comp ?_
  have hint_dom : Integrable
      (fun y : Plane => (2 * M) ^ 2 * ⟪(f : Plane → Vec2) y, (f : Plane → Vec2) y⟫_ℝ) (cellμ c) :=
    (L2.integrable_inner (𝕜 := ℝ) f f).const_mul ((2 * M) ^ 2)
  have hlim := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := cellμ c)
    (F := fun r y => (a r y - a r₀ y) ^ 2 * ⟪(f : Plane → Vec2) y, (f : Plane → Vec2) y⟫_ℝ)
    (bound := fun y => (2 * M) ^ 2 * ⟪(f : Plane → Vec2) y, (f : Plane → Vec2) y⟫_ℝ)
    (f := fun _ => 0)
    (Eventually.of_forall fun r => by
      have hc1 : Continuous (fun y : Plane => (a r y - a r₀ y) ^ 2) :=
        ((ha_r r).sub (ha_r r₀)).pow 2
      exact hc1.aestronglyMeasurable.mul
        (L2.integrable_inner (𝕜 := ℝ) f f).aestronglyMeasurable)
    (Eventually.of_forall fun r => Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) real_inner_self_nonneg)]
      have hab : |a r y - a r₀ y| ≤ 2 * M := by
        calc |a r y - a r₀ y| ≤ |a r y| + |a r₀ y| := abs_sub _ _
          _ ≤ M + M := add_le_add (hb r y) (hb r₀ y)
          _ = 2 * M := by ring
      have hsq : (a r y - a r₀ y) ^ 2 ≤ (2 * M) ^ 2 := by
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hab 2
      exact mul_le_mul_of_nonneg_right hsq real_inner_self_nonneg)
    hint_dom
    (Eventually.of_forall fun y => by
      have hcy : Continuous (fun r : ℝ => (a r y - a r₀ y) ^ 2 *
          ⟪(f : Plane → Vec2) y, (f : Plane → Vec2) y⟫_ℝ) :=
        (((ha.comp (continuous_id.prodMk continuous_const)).sub continuous_const).pow 2).mul
          continuous_const
      simpa using hcy.tendsto r₀)
  simpa using hlim

def rank1VecCLM (j i : Fin 2) : Vec2 →L[ℝ] Vec2 :=
  (πR j).smulRight (EuclideanSpace.single i (1 : ℝ))

lemma norm_rank1VecCLM_le (j i : Fin 2) : ‖rank1VecCLM j i‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul, rank1VecCLM, ContinuousLinearMap.smulRight_apply, norm_smul, Real.norm_eq_abs]
  have h1 : ‖(EuclideanSpace.single i (1 : ℝ) : Vec2)‖ = 1 := by
    fin_cases i <;> simp
  rw [h1, mul_one]
  exact PiLp.norm_apply_le v j

/-! ## 10. Bridges between `IsCylH1Slice` (`CMerid`) and `H1Sol c` (`Vec2`) -/

lemma norm_ofRealSlice_eq (w : B0579.Plane → Fin 2 → ℝ) (y : B0579.Plane) :
    ‖ofRealSlice w y‖ = ‖toVecSlice w y‖ := by
  have hsq : ‖ofRealSlice w y‖ ^ 2 = ‖toVecSlice w y‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [ofRealSlice, toVecSlice, Complex.norm_real]
  nlinarith [norm_nonneg (ofRealSlice w y), norm_nonneg (toVecSlice w y)]

lemma cylSliceL2_ofRealSlice_eq_eLpNorm (c : ℝ) (w : B0579.Plane → Fin 2 → ℝ) :
    cylSliceL2 c (ofRealSlice w) = eLpNorm (toVecSlice w) 2 (cellμ c) := by
  unfold cylSliceL2
  rw [restrict_b0579_cell_eq_cellμ]
  exact eLpNorm_congr_norm_ae (Eventually.of_forall (norm_ofRealSlice_eq w))

lemma stronglyMeasurable_toVecSlice {w : B0579.Plane → Fin 2 → ℝ}
    (hw : StronglyMeasurable w) : StronglyMeasurable (toVecSlice w) := by
  refine ((PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ fun i => ?_)).stronglyMeasurable
  exact ((continuous_apply i).comp_stronglyMeasurable hw).measurable

lemma stronglyMeasurable_toVecSlice_of_ofReal {w : B0579.Plane → Fin 2 → ℝ}
    (hw : StronglyMeasurable (ofRealSlice w)) : StronglyMeasurable (toVecSlice w) := by
  refine ((PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ fun i => ?_)).stronglyMeasurable
  have hre : (fun y => w y i) = fun y => (ofRealSlice w y i).re := by
    funext y; simp [ofRealSlice]
  rw [hre]
  exact Complex.continuous_re.measurable.comp
    (((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp_stronglyMeasurable hw).measurable)

lemma stronglyMeasurable_ofRealSlice_aux {w : B0579.Plane → Fin 2 → ℝ}
    (hw : StronglyMeasurable w) : StronglyMeasurable (ofRealSlice w) := by
  refine ((PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ fun i => ?_)).stronglyMeasurable
  exact Complex.measurable_ofReal.comp (((continuous_apply i).comp_stronglyMeasurable hw).measurable)

lemma memLp_toVecSlice_of_ofRealSlice {c : ℝ} {w : B0579.Plane → Fin 2 → ℝ}
    (hsm : StronglyMeasurable (ofRealSlice w))
    (hm : MemLp (ofRealSlice w) 2 (volume.restrict (B0579.cell c))) :
    MemLp (toVecSlice w) 2 (cellμ c) :=
  ⟨(stronglyMeasurable_toVecSlice_of_ofReal hsm).aestronglyMeasurable,
    (cylSliceL2_ofRealSlice_eq_eLpNorm c w).symm.trans_lt hm.eLpNorm_lt_top⟩

lemma hasWeakCellDerivC_ofReal_iff (c : ℝ) (j : Fin 2) (φ g : Plane → ℝ) :
    IIIa.HasWeakCellDerivC c j (fun y => (φ y : ℂ)) (fun y => (g y : ℂ)) ↔
      HasWeakCellDerivR c j φ g := by
  have hmul1 : ∀ ψ : Plane → ℝ,
      (fun y => (φ y : ℂ) * (B0579.pd j ψ y : ℂ)) =
        fun y => Complex.ofRealCLM (φ y * B0579.pd j ψ y) := by
    intro ψ; funext y; simp
  have hmul2 : ∀ ψ : Plane → ℝ,
      (fun y => (g y : ℂ) * (ψ y : ℂ)) =
        fun y => Complex.ofRealCLM (g y * ψ y) := by
    intro ψ; funext y; simp
  constructor
  · intro h
    refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
    · obtain ⟨i1, i2⟩ := h.1 ψ hψ
      have r1 : (fun y => φ y * B0579.pd j ψ y) =
          fun y => Complex.reCLM ((φ y : ℂ) * (B0579.pd j ψ y : ℂ)) := by
        funext y; simp
      have r2 : (fun y => g y * ψ y) =
          fun y => Complex.reCLM ((g y : ℂ) * (ψ y : ℂ)) := by
        funext y; simp
      rw [r1, r2]
      exact ⟨Complex.reCLM.integrable_comp i1, Complex.reCLM.integrable_comp i2⟩
    · obtain ⟨i1, i2⟩ := h.1 ψ hψ
      have hi1 : IntegrableOn (fun y => φ y * B0579.pd j ψ y) (B0579.cell c) := by
        have r1 : (fun y => φ y * B0579.pd j ψ y) =
            fun y => Complex.reCLM ((φ y : ℂ) * (B0579.pd j ψ y : ℂ)) := by funext y; simp
        rw [r1]; exact Complex.reCLM.integrable_comp i1
      have hi2 : IntegrableOn (fun y => g y * ψ y) (B0579.cell c) := by
        have r2 : (fun y => g y * ψ y) =
            fun y => Complex.reCLM ((g y : ℂ) * (ψ y : ℂ)) := by funext y; simp
        rw [r2]; exact Complex.reCLM.integrable_comp i2
      have heq := h.2 ψ hψ
      rw [hmul1 ψ, hmul2 ψ, Complex.ofRealCLM.integral_comp_comm hi1,
        Complex.ofRealCLM.integral_comp_comm hi2] at heq
      exact Complex.ofReal_inj.mp (by simpa using heq)
  · intro h
    refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
    · obtain ⟨i1, i2⟩ := h.1 ψ hψ
      rw [hmul1 ψ, hmul2 ψ]
      exact ⟨Complex.ofRealCLM.integrable_comp i1, Complex.ofRealCLM.integrable_comp i2⟩
    · obtain ⟨i1, i2⟩ := h.1 ψ hψ
      rw [hmul1 ψ, hmul2 ψ, Complex.ofRealCLM.integral_comp_comm i1,
        Complex.ofRealCLM.integral_comp_comm i2, h.2 ψ hψ]
      simp

lemma isCylSolenoidalSlice_ofReal_iff (c : ℝ) (u : B0579.Plane → Fin 2 → ℝ) :
    IsCylSolenoidalSlice c (ofRealSlice u) ↔ IsRealCellSolenoidal c (toVecSlice u) := by
  have hfun : ∀ ψ : Plane → ℝ,
      (fun y => ofRealSlice u y 0 * (B0579.pd 0 ψ y : ℂ) +
          ofRealSlice u y 1 * (B0579.pd 1 ψ y : ℂ)) =
        fun y => Complex.ofRealCLM
          (toVecSlice u y 0 * B0579.pd 0 ψ y + toVecSlice u y 1 * B0579.pd 1 ψ y) := by
    intro ψ; funext y; simp [ofRealSlice, toVecSlice]
  constructor
  · intro h ψ hψ
    obtain ⟨hi, hz⟩ := h ψ hψ
    have hre : (fun y => toVecSlice u y 0 * B0579.pd 0 ψ y + toVecSlice u y 1 * B0579.pd 1 ψ y) =
        fun y => Complex.reCLM (ofRealSlice u y 0 * (B0579.pd 0 ψ y : ℂ) +
          ofRealSlice u y 1 * (B0579.pd 1 ψ y : ℂ)) := by
      funext y; simp [ofRealSlice, toVecSlice]
    have hiR : IntegrableOn
        (fun y => toVecSlice u y 0 * B0579.pd 0 ψ y + toVecSlice u y 1 * B0579.pd 1 ψ y)
        (B0579.cell c) := by
      rw [hre]; exact Complex.reCLM.integrable_comp hi
    rw [hfun ψ, Complex.ofRealCLM.integral_comp_comm hiR] at hz
    exact ⟨hiR, Complex.ofReal_eq_zero.mp (by simpa using hz)⟩
  · intro h ψ hψ
    obtain ⟨hiR, hzR⟩ := h ψ hψ
    rw [hfun ψ]
    refine ⟨Complex.ofRealCLM.integrable_comp hiR, ?_⟩
    rw [Complex.ofRealCLM.integral_comp_comm hiR, hzR]
    simp

def h1SolOfCylSlice {c : ℝ} {u uq uη : B0579.Plane → Fin 2 → ℝ}
    (h : IsCylH1Slice c (ofRealSlice u) (ofRealSlice uq) (ofRealSlice uη)) : H1Sol c :=
  let hu := memLp_toVecSlice_of_ofRealSlice h.sm_u h.memL2_u
  let huq := memLp_toVecSlice_of_ofRealSlice h.sm_uq h.memL2_uq
  let huη := memLp_toVecSlice_of_ofRealSlice h.sm_uη h.memL2_uη
  H1Sol.mkOfWeak
    (hu.toLp (toVecSlice u))
    (huq.toLp (toVecSlice uq))
    (huη.toLp (toVecSlice uη))
    ((mem_divFree_iff_solenoidal _).2
      (isRealCellSolenoidal_congr_ae hu.coeFn_toLp.symm
        ((isCylSolenoidalSlice_ofReal_iff c u).1 h.solenoidal)))
    (fun k =>
      hasWeakCellDerivR_congr_ae
        (hu.coeFn_toLp.symm.mono fun _ hy => congrArg (fun v : Vec2 => v k) hy)
        (huq.coeFn_toLp.symm.mono fun _ hy => congrArg (fun v : Vec2 => v k) hy)
        ((hasWeakCellDerivC_ofReal_iff c 0 (fun y => u y k) (fun y => uq y k)).1 (h.weak_q k)))
    (fun k =>
      hasWeakCellDerivR_congr_ae
        (hu.coeFn_toLp.symm.mono fun _ hy => congrArg (fun v : Vec2 => v k) hy)
        (huη.coeFn_toLp.symm.mono fun _ hy => congrArg (fun v : Vec2 => v k) hy)
        ((hasWeakCellDerivC_ofReal_iff c 1 (fun y => u y k) (fun y => uη y k)).1 (h.weak_eta k)))

lemma h1SolOfCylSlice_ae {c : ℝ} {u uq uη : B0579.Plane → Fin 2 → ℝ}
    (h : IsCylH1Slice c (ofRealSlice u) (ofRealSlice uq) (ofRealSlice uη)) :
    ((val0CLM c (h1SolOfCylSlice h) : Plane → Vec2) =ᵐ[cellμ c] toVecSlice u) ∧
    ((dqCLM c (h1SolOfCylSlice h) : Plane → Vec2) =ᵐ[cellμ c] toVecSlice uq) ∧
    ((detaCLM c (h1SolOfCylSlice h) : Plane → Vec2) =ᵐ[cellμ c] toVecSlice uη) :=
  ⟨(memLp_toVecSlice_of_ofRealSlice h.sm_u h.memL2_u).coeFn_toLp,
   (memLp_toVecSlice_of_ofRealSlice h.sm_uq h.memL2_uq).coeFn_toLp,
   (memLp_toVecSlice_of_ofRealSlice h.sm_uη h.memL2_uη).coeFn_toLp⟩

lemma cylSliceL2_ofRealSlice_eq_ofReal_norm {c : ℝ} {w : B0579.Plane → Fin 2 → ℝ}
    {x : L2v c} (hx : (x : Plane → Vec2) =ᵐ[cellμ c] toVecSlice w) :
    cylSliceL2 c (ofRealSlice w) = ENNReal.ofReal ‖x‖ := by
  rw [cylSliceL2_ofRealSlice_eq_eLpNorm, ← eLpNorm_congr_ae hx, Lp.norm_def,
    ENNReal.ofReal_toReal (Lp.eLpNorm_lt_top x).ne]

lemma cylSliceL2_sub_ofRealSlice_eq_ofReal_norm {c : ℝ}
    {w₁ w₂ : B0579.Plane → Fin 2 → ℝ} {x₁ x₂ : L2v c}
    (hx₁ : (x₁ : Plane → Vec2) =ᵐ[cellμ c] toVecSlice w₁)
    (hx₂ : (x₂ : Plane → Vec2) =ᵐ[cellμ c] toVecSlice w₂) :
    cylSliceL2 c (fun y => ofRealSlice w₁ y - ofRealSlice w₂ y) = ENNReal.ofReal ‖x₁ - x₂‖ := by
  have hsub : (fun y => ofRealSlice w₁ y - ofRealSlice w₂ y) =
      ofRealSlice (fun y i => w₁ y i - w₂ y i) := by
    ext y i; simp [ofRealSlice]
  rw [hsub]
  refine cylSliceL2_ofRealSlice_eq_ofReal_norm ?_
  filter_upwards [Lp.coeFn_sub x₁ x₂, hx₁, hx₂] with y h12 h1 h2
  ext i
  change ((x₁ - x₂ : L2v c) : Plane → Vec2) y i = w₁ y i - w₂ y i
  rw [h12, Pi.sub_apply, h1, h2]
  rfl

lemma enorm_h1SolOfCylSlice_le {c : ℝ} {u uq uη : B0579.Plane → Fin 2 → ℝ}
    (h : IsCylH1Slice c (ofRealSlice u) (ofRealSlice uq) (ofRealSlice uη)) :
    ‖h1SolOfCylSlice h‖ₑ ≤ cylSliceH1 c (ofRealSlice u) (ofRealSlice uq) (ofRealSlice uη) := by
  obtain ⟨h0, hq, hη⟩ := h1SolOfCylSlice_ae h
  unfold cylSliceH1
  rw [cylSliceL2_ofRealSlice_eq_ofReal_norm h0,
    cylSliceL2_ofRealSlice_eq_ofReal_norm hq,
    cylSliceL2_ofRealSlice_eq_ofReal_norm hη, ← ofReal_norm]
  have hle : ‖h1SolOfCylSlice h‖ ≤
      ‖val0CLM c (h1SolOfCylSlice h)‖ + ‖dqCLM c (h1SolOfCylSlice h)‖ +
        ‖detaCLM c (h1SolOfCylSlice h)‖ := by
    change max ‖val0CLM c (h1SolOfCylSlice h)‖
      (max ‖dqCLM c (h1SolOfCylSlice h)‖ ‖detaCLM c (h1SolOfCylSlice h)‖) ≤ _
    have n0 := norm_nonneg (val0CLM c (h1SolOfCylSlice h))
    have nq := norm_nonneg (dqCLM c (h1SolOfCylSlice h))
    have nη := norm_nonneg (detaCLM c (h1SolOfCylSlice h))
    exact max_le (by linarith) (max_le (by linarith) (by linarith))
  calc ENNReal.ofReal ‖h1SolOfCylSlice h‖
      ≤ ENNReal.ofReal (‖val0CLM c (h1SolOfCylSlice h)‖ + ‖dqCLM c (h1SolOfCylSlice h)‖ +
          ‖detaCLM c (h1SolOfCylSlice h)‖) := ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal ‖val0CLM c (h1SolOfCylSlice h)‖ +
        ENNReal.ofReal ‖dqCLM c (h1SolOfCylSlice h)‖ +
        ENNReal.ofReal ‖detaCLM c (h1SolOfCylSlice h)‖ := by
        rw [ENNReal.ofReal_add (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _),
          ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]

lemma isCylH1Slice_of_h1Sol_ae {c : ℝ} (p : H1Sol c)
    {w wq wη : B0579.Plane → Fin 2 → ℝ}
    (hsm : StronglyMeasurable w) (hsmq : StronglyMeasurable wq) (hsmη : StronglyMeasurable wη)
    (hw : (val0CLM c p : Plane → Vec2) =ᵐ[cellμ c] toVecSlice w)
    (hwq : (dqCLM c p : Plane → Vec2) =ᵐ[cellμ c] toVecSlice wq)
    (hwη : (detaCLM c p : Plane → Vec2) =ᵐ[cellμ c] toVecSlice wη) :
    IsCylH1Slice c (ofRealSlice w) (ofRealSlice wq) (ofRealSlice wη) where
  sm_u := stronglyMeasurable_ofRealSlice_aux hsm
  sm_uq := stronglyMeasurable_ofRealSlice_aux hsmq
  sm_uη := stronglyMeasurable_ofRealSlice_aux hsmη
  weak_q k :=
    (hasWeakCellDerivC_ofReal_iff c 0 (fun y => w y k) (fun y => wq y k)).2
      (hasWeakCellDerivR_congr_ae
        (hw.mono fun _ hy => congrArg (fun v : Vec2 => v k) hy)
        (hwq.mono fun _ hy => congrArg (fun v : Vec2 => v k) hy)
        (H1Sol.weak_q p k))
  weak_eta k :=
    (hasWeakCellDerivC_ofReal_iff c 1 (fun y => w y k) (fun y => wη y k)).2
      (hasWeakCellDerivR_congr_ae
        (hw.mono fun _ hy => congrArg (fun v : Vec2 => v k) hy)
        (hwη.mono fun _ hy => congrArg (fun v : Vec2 => v k) hy)
        (H1Sol.weak_eta p k))
  solenoidal :=
    (isCylSolenoidalSlice_ofReal_iff c w).2
      (isRealCellSolenoidal_congr_ae hw
        ((mem_divFree_iff_solenoidal (val0CLM c p)).1 (H1Sol.mem_divFree p)))
  memL2_u :=
    ⟨(stronglyMeasurable_ofRealSlice_aux hsm).aestronglyMeasurable,
      (cylSliceL2_ofRealSlice_eq_eLpNorm c w).trans_lt
        ((eLpNorm_congr_ae hw.symm).trans_lt (Lp.memLp (val0CLM c p)).eLpNorm_lt_top)⟩
  memL2_uq :=
    ⟨(stronglyMeasurable_ofRealSlice_aux hsmq).aestronglyMeasurable,
      (cylSliceL2_ofRealSlice_eq_eLpNorm c wq).trans_lt
        ((eLpNorm_congr_ae hwq.symm).trans_lt (Lp.memLp (dqCLM c p)).eLpNorm_lt_top)⟩
  memL2_uη :=
    ⟨(stronglyMeasurable_ofRealSlice_aux hsmη).aestronglyMeasurable,
      (cylSliceL2_ofRealSlice_eq_eLpNorm c wη).trans_lt
        ((eLpNorm_congr_ae hwη.symm).trans_lt (Lp.memLp (detaCLM c p)).eLpNorm_lt_top)⟩

end UnforcedLeray.Short.IIb.TailExistenceAux

