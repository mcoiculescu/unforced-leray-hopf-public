import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2
import UnforcedLeray.Lib.HeatCylinder.HeatVecCenteredSelfAdjoint
import UnforcedLeray.Lib.HeatCylinder.HeatL2StrongContinuity
import UnforcedLeray.Lib.HeatCylinder.BochnerPath
import UnforcedLeray.Lib.HeatCylinder.P0PlaneShift
import UnforcedLeray.Lib.HeatCylinder.HeatVecGaussianShiftPairing
import UnforcedLeray.Lib.TrainB.P0W1Rough
import UnforcedLeray.Lib.CylinderB.Liouville
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# `UnitWeakUnique.HeatMollifier`: Self-contained cylinder Gaussian translation-average and
Gaussian-gradient mollifier calculus on `Cyl.L2v c`

Helper module for `PartII-b:F8/1/org/3/2` (`CylUnitWeakHomogeneousUnique`).
Imports only frozen specification and library modules (no sibling leaf drafts).
All declarations live inside `UnforcedLeray.Short.IIb.UnitWeakUniqueAux` (R6).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIb.UnitWeakUniqueAux

open UnforcedLeray.Short.IIb
open UnforcedLeray.Cyl (L2v cellμ divFree P0 Vec2)
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.HeatCylinder
open UnforcedLeray.B0284 (heatKernel2)

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-! ## 1. Cylinder test, `rotT`, and `L2v c` bridges -/

lemma b0579_cell_eq_cyl_cell (c : ℝ) : B0579.cell c = UnforcedLeray.Cyl.cell c := by
  simp [B0579.cell, UnforcedLeray.Cyl.cell, neg_div]

lemma cellMeas_eq_cellμ (c : ℝ) : F8Ex.cellMeas c = cellμ c := by
  unfold F8Ex.cellMeas cellμ
  rw [b0579_cell_eq_cyl_cell]

lemma memLp_cellμ_of_test {c : ℝ} {ψ : Plane → ℝ} (hψ : B0579.IsCylTest c ψ) :
    MemLp ψ 2 (cellμ c) := by
  rw [← cellMeas_eq_cellμ c]
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

lemma isRealSolCylTest_rotT {c : ℝ} {φ : Plane → ℝ} (hφ : UnforcedLeray.Sob.IsCylTest c φ) :
    F8Ex.IsRealSolCylTest c (UnforcedLeray.Cyl.rotT φ) := by
  have hdφ : Differentiable ℝ φ := hφ.differentiable
  have hq : UnforcedLeray.Sob.IsCylTest c (UnforcedLeray.Cyl.partialQ φ) := by
    rw [funext (UnforcedLeray.Cyl.partialQ_eq_fderiv hdφ)]
    exact hφ.dirDeriv ((1 : ℝ), (0 : ℝ))
  have hη : UnforcedLeray.Sob.IsCylTest c (UnforcedLeray.Cyl.partialEta φ) := by
    rw [funext (UnforcedLeray.Cyl.partialEta_eq_fderiv hdφ)]
    exact hφ.dirDeriv ((0 : ℝ), (1 : ℝ))
  refine ⟨fun k => ?_, fun y => ?_⟩
  · fin_cases k
    ·exact (isCylTest_sob_iff c _).1 hη
    · have hqb := (isCylTest_sob_iff c _).1 hq
      obtain ⟨R, hR⟩ := hqb.band
      exact ⟨hqb.smooth.neg,
        fun x => by simp [UnforcedLeray.Cyl.rotT, hqb.periodic x],
        R, fun x hx => by simp [UnforcedLeray.Cyl.rotT, hR x hx]⟩
  · have hfunη : UnforcedLeray.Cyl.partialEta φ = fun z => fderiv ℝ φ z ((0 : ℝ), (1 : ℝ)) :=
      funext (UnforcedLeray.Cyl.partialEta_eq_fderiv hdφ)
    have h1 : UnforcedLeray.Cyl.partialQ (fun w => UnforcedLeray.Cyl.rotT φ w 0) y =
        UnforcedLeray.Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))] φ y := by
      change UnforcedLeray.Cyl.partialQ (UnforcedLeray.Cyl.partialEta φ) y = _
      rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hη.differentiable y, hfunη]
      rfl
    have h2 : UnforcedLeray.Cyl.partialEta (fun w => UnforcedLeray.Cyl.rotT φ w 1) y =
        -UnforcedLeray.Sob.iterDirDeriv [((0 : ℝ), (1 : ℝ)), ((1 : ℝ), (0 : ℝ))] φ y := by
      change UnforcedLeray.Cyl.partialEta (fun w => -UnforcedLeray.Cyl.partialQ φ w) y = _
      rw [UnforcedLeray.Cyl.partialEta_eq_fderiv hq.differentiable.fun_neg y, fderiv_fun_neg,
        neg_apply]
      congr 1
      rw [funext (UnforcedLeray.Cyl.partialQ_eq_fderiv hdφ)]
      rfl
    have hsymm : UnforcedLeray.Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))] φ =
        UnforcedLeray.Sob.iterDirDeriv [((0 : ℝ), (1 : ℝ)), ((1 : ℝ), (0 : ℝ))] φ :=
      UnforcedLeray.Sob.iterDirDeriv_perm
        (List.Perm.swap ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ)) []) hφ.smooth
    unfold UnforcedLeray.Cyl.divergence
    rw [h1, h2, congrFun hsymm y, add_neg_cancel]

lemma isCylSmooth_vec_of_tests {c : ℝ} {Φ : Plane → F8Ex.RMerid}
    (h0 : B0579.IsCylTest c (fun y => Φ y 0))
    (h1 : B0579.IsCylTest c (fun y => Φ y 1)) :
    UnforcedLeray.Sob.IsCylSmooth c Φ := by
  have heq : Φ = fun y => Φ y 0 • F8Ex.eR0 + Φ y 1 • F8Ex.eR1 := by
    funext y; ext k; fin_cases k <;> simp [F8Ex.eR0, F8Ex.eR1]
  rw [heq]
  have hs0 : ContDiff ℝ ∞ (fun y => Φ y 0 • F8Ex.eR0) := h0.smooth.smul contDiff_const
  have hs1 : ContDiff ℝ ∞ (fun y => Φ y 1 • F8Ex.eR1) := h1.smooth.smul contDiff_const
  refine ⟨hs0.add hs1, fun z => ?_, ?_⟩
  · have hz : z + (c, 0) = (z.1 + c, z.2) := by ext <;> simp
    simp only [hz, h0.periodic, h1.periodic]
  · obtain ⟨R0, hR0⟩ := h0.band
    obtain ⟨R1, hR1⟩ := h1.band
    refine ⟨max R0 R1, fun z hz => ?_⟩
    rw [hR0 z (lt_of_le_of_lt (le_max_left _ _) hz),
      hR1 z (lt_of_le_of_lt (le_max_right _ _) hz), zero_smul, zero_smul, add_zero]

lemma isCylSmooth_of_solTest {c : ℝ} {Φ : Plane → F8Ex.RMerid}
    (hΦ : F8Ex.IsRealSolCylTest c Φ) :
    UnforcedLeray.Sob.IsCylSmooth c Φ :=
  isCylSmooth_vec_of_tests (hΦ.cyl_test 0) (hΦ.cyl_test 1)

lemma memLp_of_cylSmooth {c : ℝ} {Φ : Plane → F8Ex.RMerid}
    (hΦ : UnforcedLeray.Sob.IsCylSmooth c Φ) :
    MemLp Φ 2 (cellμ c) := by
  rw [← UnforcedLeray.TrainB.vecH1_measure_eq_cell c]
  exact hΦ.memLp (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) 2

def cylSmoothToL2 {c : ℝ} {Φ : Plane → F8Ex.RMerid}
    (hΦ : UnforcedLeray.Sob.IsCylSmooth c Φ) : L2v c :=
  (memLp_of_cylSmooth hΦ).toLp Φ

lemma pd_coord_cylSmooth {c : ℝ} {Φ : Plane → F8Ex.RMerid}
    (hΦ : UnforcedLeray.Sob.IsCylSmooth c Φ) (j k : Fin 2) (y : Plane) :
    fderiv ℝ Φ y (B0579.dir j) k = B0579.pd j (fun z => Φ z k) y := by
  have hd : DifferentiableAt ℝ Φ y := (hΦ.smooth.differentiable (by simp)) y
  have hcomp : HasFDerivAt (fun z => Φ z k)
      ((EuclideanSpace.proj k : F8Ex.RMerid →L[ℝ] ℝ).comp (fderiv ℝ Φ y)) y :=
    (EuclideanSpace.proj k : F8Ex.RMerid →L[ℝ] ℝ).hasFDerivAt.comp y hd.hasFDerivAt
  unfold B0579.pd
  rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]
  rfl

lemma inner_cylSmoothToL2_right {c : ℝ} {Φ : Plane → F8Ex.RMerid}
    (hΦ : UnforcedLeray.Sob.IsCylSmooth c Φ) (f : L2v c) :
    ⟪cylSmoothToL2 hΦ, f⟫_ℝ = ∫ y in B0579.cell c, ⟪Φ y, (f : Plane → F8Ex.RMerid) y⟫_ℝ := by
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
      ∫ y in B0579.cell c, (f : Plane → F8Ex.RMerid) y k * ψ y := by
  rw [real_inner_comm, inner_cylSmoothToL2_right]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  fin_cases k <;> simp [mul_comm]

lemma mem_divFree_iff_solenoidal {c : ℝ} (f : L2v c) :
    f ∈ divFree c ↔ F8Ex.IsRealCellSolenoidal c (f : Plane → F8Ex.RMerid) := by
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
    have hm_grad : MemLp (UnforcedLeray.Cyl.gradT ψ) 2 (F8Ex.cellMeas c) := by
      rw [cellMeas_eq_cellμ]; exact UnforcedLeray.Cyl.memLp_gradT hψs
    have hm_f : MemLp (f : Plane → Vec2) 2 (F8Ex.cellMeas c) := by
      rw [cellMeas_eq_cellμ]; exact Lp.memLp f
    have hint : IntegrableOn (fun z => ⟪UnforcedLeray.Cyl.gradT ψ z, (f : Plane → Vec2) z⟫_ℝ)
        (B0579.cell c) := F8Ex.integrableOn_innerR_cell hm_grad hm_f
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

lemma cylSmoothToL2_mem_divFree_of_solTest {c : ℝ} (hc : 0 < c) {Φ : Plane → F8Ex.RMerid}
    (hΦ : F8Ex.IsRealSolCylTest c Φ) :
    cylSmoothToL2 (isCylSmooth_of_solTest hΦ) ∈ divFree c := by
  rw [UnforcedLeray.Cyl.mem_divFree]
  intro ψ hψ
  rw [UnforcedLeray.Cyl.gradL, cylSmoothToL2, UnforcedLeray.Cyl.inner_toLp_eq]
  have hdψ : Differentiable ℝ ψ := hψ.differentiable
  have hΦ0 : UnforcedLeray.Sob.IsCylTest c (fun z => Φ z 0) :=
    (isCylTest_sob_iff c _).2 (hΦ.cyl_test 0)
  have hΦ1 : UnforcedLeray.Sob.IsCylTest c (fun z => Φ z 1) :=
    (isCylTest_sob_iff c _).2 (hΦ.cyl_test 1)
  have hdΦ0 : Differentiable ℝ (fun z => Φ z 0) := (hΦ.cyl_test 0).differentiable
  have hdΦ1 : Differentiable ℝ (fun z => Φ z 1) := (hΦ.cyl_test 1).differentiable
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
  have hdiv : ∀ z : Plane,
      fderiv ℝ (fun y => Φ y 0) z ((1 : ℝ), (0 : ℝ)) +
        fderiv ℝ (fun y => Φ y 1) z ((0 : ℝ), (1 : ℝ)) = 0 := by
    intro z
    have hdz := hΦ.div_free z
    unfold UnforcedLeray.Cyl.divergence at hdz
    rwa [UnforcedLeray.Cyl.partialQ_eq_fderiv hdΦ0,
      UnforcedLeray.Cyl.partialEta_eq_fderiv hdΦ1] at hdz
  have hzero : (fun z : Plane => ψ z * fderiv ℝ (fun y => Φ y 0) z ((1 : ℝ), (0 : ℝ)) +
      ψ z * fderiv ℝ (fun y => Φ y 1) z ((0 : ℝ), (1 : ℝ))) = fun _ => 0 := by
    funext z; rw [← mul_add, hdiv z, mul_zero]
  rw [hzero, integral_zero, neg_zero]

/-! ## 2. Completeness of stream-function tests `rotT φ` on `divFree c` -/

private noncomputable def pairH10 {c : ℝ} {h : B0579.Plane → ℝ}
    (hh0 : MemLp h 2 (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρ0 c))) :
    UnforcedLeray.Cyl.Hneg c 0 1 :=
  (innerSL ℝ (hh0.toLp h)).comp
    (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c) (UnforcedLeray.Cyl.ρ0 c) ℝ ℝ 1 2)

private lemma pairH10_testH {c : ℝ} (hc : 0 < c) {h : B0579.Plane → ℝ}
    (hh0 : MemLp h 2 (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρ0 c)))
    {ψ : B0579.Plane → ℝ} (hψ : UnforcedLeray.Sob.IsCylTest c ψ) :
    pairH10 hh0 (UnforcedLeray.Cyl.testH hc hψ (UnforcedLeray.Cyl.ρ0 c) 1) =
      ∫ z in UnforcedLeray.Cyl.cell c, h z * ψ z := by
  simp only [pairH10, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  rw [L2.inner_def]
  have hcoe1 : (hh0.toLp h : UnforcedLeray.Cyl.Plane → ℝ) =ᵐ[cellμ c] h := by
    rw [← UnforcedLeray.Cyl.wμ_ρwW_zero_inv c]
    exact hh0.coeFn_toLp
  have hcoe2 : (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρ0 c) ℝ ℝ 1 2
      (UnforcedLeray.Cyl.testH hc hψ (UnforcedLeray.Cyl.ρ0 c) 1) :
      UnforcedLeray.Cyl.Plane → ℝ) =ᵐ[cellμ c] ψ := by
    have hv := UnforcedLeray.Cyl.ae_cell_of_cylinder
      (UnforcedLeray.Cyl.coeFn_deriv_testH hc hψ (UnforcedLeray.Cyl.ρ0 c) 1
        UnforcedLeray.Sob.Idx.zero)
    have h1 := UnforcedLeray.Sob.W.deriv_zero (D := UnforcedLeray.Sob.cylinder c)
      (ρ := UnforcedLeray.Cyl.ρ0 c) (𝕜 := ℝ) (F := ℝ) (k := 1) (p := 2)
      (UnforcedLeray.Cyl.testH hc hψ (UnforcedLeray.Cyl.ρ0 c) 1)
    have h2 : UnforcedLeray.Sob.iterDirDeriv
        ((UnforcedLeray.Sob.cylinder c).word (UnforcedLeray.Sob.Idx.zero : UnforcedLeray.Sob.Idx 2 1))
        ψ = ψ := by
      rw [UnforcedLeray.Cyl.word_zero, UnforcedLeray.Sob.iterDirDeriv_nil]
    rwa [h1, h2] at hv
  rw [UnforcedLeray.Cyl.integral_wμ0]
  refine integral_congr_ae ?_
  filter_upwards [hcoe1, hcoe2] with z hz1 hz2
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hz1, hz2, mul_comm]

lemma eq_zero_of_divFree_and_ortho_rotT {c : ℝ} (hc : 0 < c) (g : L2v c)
    (hg : g ∈ divFree c)
    (horth : ∀ (φ : B0579.Plane → ℝ) (hφ : UnforcedLeray.Sob.IsCylTest c φ),
      ⟪cylSmoothToL2 (isCylSmooth_of_solTest (isRealSolCylTest_rotT hφ)), g⟫_ℝ = 0) :
    g = 0 := by
  let g0 : B0579.Plane → ℝ := fun z => (g : B0579.Plane → Vec2) z 0
  let g1 : B0579.Plane → ℝ := fun z => (g : B0579.Plane → Vec2) z 1
  have hg0 : MemLp g0 2 (cellμ c) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec2 →L[ℝ] ℝ).comp_memLp' (Lp.memLp g)
  have hg1 : MemLp g1 2 (cellμ c) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec2 →L[ℝ] ℝ).comp_memLp' (Lp.memLp g)
  have hg0w : MemLp g0 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ (UnforcedLeray.Cyl.ρ0 c)) :=
    (UnforcedLeray.Cyl.wμ_ρwW_zero_inv c).symm ▸ hg0
  have hg1w : MemLp g1 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ (UnforcedLeray.Cyl.ρ0 c)) :=
    (UnforcedLeray.Cyl.wμ_ρwW_zero_inv c).symm ▸ hg1
  let D : UnforcedLeray.Cyl.Hneg c 0 1 × UnforcedLeray.Cyl.Hneg c 0 1 :=
    (pairH10 hg0w, pairH10 hg1w)
  have hcurl : ∀ (φ : B0579.Plane → ℝ) (hφ : UnforcedLeray.Sob.IsCylTest c φ),
      D.1 (UnforcedLeray.Cyl.testH hc (hφ.dirDeriv ((0 : ℝ), (1 : ℝ)))
          (UnforcedLeray.Cyl.ρ0 c) 1) -
        D.2 (UnforcedLeray.Cyl.testH hc (hφ.dirDeriv ((1 : ℝ), (0 : ℝ)))
          (UnforcedLeray.Cyl.ρ0 c) 1) = 0 := by
    intro φ hφ
    have hdφ := hφ.differentiable
    change pairH10 hg0w _ - pairH10 hg1w _ = 0
    rw [pairH10_testH hc hg0w (hφ.dirDeriv ((0 : ℝ), (1 : ℝ))),
      pairH10_testH hc hg1w (hφ.dirDeriv ((1 : ℝ), (0 : ℝ)))]
    have hi0 : IntegrableOn (fun z => g0 z * fderiv ℝ φ z ((0 : ℝ), (1 : ℝ)))
        (UnforcedLeray.Cyl.cell c) :=
      (UnforcedLeray.Cyl.integrableOn_test_mul (hφ.dirDeriv ((0 : ℝ), (1 : ℝ))) hg0).congr_fun
        (fun _ _ => by ring) (UnforcedLeray.Cyl.measurableSet_cell c)
    have hi1 : IntegrableOn (fun z => g1 z * fderiv ℝ φ z ((1 : ℝ), (0 : ℝ)))
        (UnforcedLeray.Cyl.cell c) :=
      (UnforcedLeray.Cyl.integrableOn_test_mul (hφ.dirDeriv ((1 : ℝ), (0 : ℝ))) hg1).congr_fun
        (fun _ _ => by ring) (UnforcedLeray.Cyl.measurableSet_cell c)
    rw [← integral_sub hi0 hi1]
    have hrot := horth φ hφ
    rw [inner_cylSmoothToL2_right, b0579_cell_eq_cyl_cell] at hrot
    refine Eq.trans ?_ hrot
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp only
    rw [real_inner_comm, UnforcedLeray.Cyl.rotT, UnforcedLeray.Cyl.inner_vec,
      UnforcedLeray.Cyl.partialEta_eq_fderiv hdφ z, UnforcedLeray.Cyl.partialQ_eq_fderiv hdφ z]
    simp only [g0, g1]
    ring
  have hdiv : ∀ (φ : B0579.Plane → ℝ) (hφ : UnforcedLeray.Sob.IsCylTest c φ),
      D.1 (UnforcedLeray.Cyl.testH hc (hφ.dirDeriv ((1 : ℝ), (0 : ℝ)))
          (UnforcedLeray.Cyl.ρ0 c) 1) +
        D.2 (UnforcedLeray.Cyl.testH hc (hφ.dirDeriv ((0 : ℝ), (1 : ℝ)))
          (UnforcedLeray.Cyl.ρ0 c) 1) = 0 := by
    intro φ hφ
    have hdφ := hφ.differentiable
    change pairH10 hg0w _ + pairH10 hg1w _ = 0
    rw [pairH10_testH hc hg0w (hφ.dirDeriv ((1 : ℝ), (0 : ℝ))),
      pairH10_testH hc hg1w (hφ.dirDeriv ((0 : ℝ), (1 : ℝ)))]
    have hi0 : IntegrableOn (fun z => g0 z * fderiv ℝ φ z ((1 : ℝ), (0 : ℝ)))
        (UnforcedLeray.Cyl.cell c) :=
      (UnforcedLeray.Cyl.integrableOn_test_mul (hφ.dirDeriv ((1 : ℝ), (0 : ℝ))) hg0).congr_fun
        (fun _ _ => by ring) (UnforcedLeray.Cyl.measurableSet_cell c)
    have hi1 : IntegrableOn (fun z => g1 z * fderiv ℝ φ z ((0 : ℝ), (1 : ℝ)))
        (UnforcedLeray.Cyl.cell c) :=
      (UnforcedLeray.Cyl.integrableOn_test_mul (hφ.dirDeriv ((0 : ℝ), (1 : ℝ))) hg1).congr_fun
        (fun _ _ => by ring) (UnforcedLeray.Cyl.measurableSet_cell c)
    rw [← integral_add hi0 hi1]
    have hgr := UnforcedLeray.Cyl.mem_divFree.mp hg φ hφ
    rw [UnforcedLeray.Cyl.gradL, UnforcedLeray.Cyl.inner_toLp_left] at hgr
    refine Eq.trans ?_ hgr
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp only
    rw [real_inner_comm, UnforcedLeray.Cyl.gradT, UnforcedLeray.Cyl.inner_vec,
      UnforcedLeray.Cyl.partialQ_eq_fderiv hdφ z, UnforcedLeray.Cyl.partialEta_eq_fderiv hdφ z]
  have hD0 := UnforcedLeray.Cyl.eq_zero_of_curl_div hc D hcurl hdiv
  have hD1 : pairH10 hg0w = 0 := congrArg Prod.fst hD0
  have hD2 : pairH10 hg1w = 0 := congrArg Prod.snd hD0
  have hae_comp : ∀ (hi : B0579.Plane → ℝ) (hmi : MemLp hi 2 (cellμ c))
      (hmiw : MemLp hi 2
        (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ (UnforcedLeray.Cyl.ρ0 c))),
      pairH10 hmiw = 0 → hi =ᵐ[cellμ c] 0 := by
    intro hi hmi hmiw hp0
    have hmi' : MemLp hi 2 (UnforcedLeray.Sob.cylinder c).μ :=
      (UnforcedLeray.Cyl.cylinder_μ_eq c).symm ▸ hmi
    have hae_cyl : hi =ᵐ[(UnforcedLeray.Sob.cylinder c).μ] 0 := by
      refine (UnforcedLeray.Sob.cylinder c).ae_zero hi (hmi'.locallyIntegrable (by norm_num))
        fun ψ hψ => ?_
      have hp := congrArg
        (fun L : UnforcedLeray.Cyl.Hneg c 0 1 =>
          L (UnforcedLeray.Cyl.testH hc hψ (UnforcedLeray.Cyl.ρ0 c) 1)) hp0
      simp only [zero_apply] at hp
      rw [pairH10_testH hc hmiw hψ] at hp
      rw [UnforcedLeray.Cyl.cylinder_μ_eq c]; unfold cellμ
      simpa only [smul_eq_mul, mul_comm (ψ _)] using hp
    rwa [UnforcedLeray.Cyl.cylinder_μ_eq c] at hae_cyl
  apply Lp.ext
  filter_upwards [hae_comp g0 hg0 hg0w hD1, hae_comp g1 hg1 hg1w hD2,
    Lp.coeFn_zero Vec2 2 (cellμ c)] with z hz0 hz1 hzZ
  rw [hzZ]
  ext i
  fin_cases i
  · exact hz0
  · exact hz1

/-! ## 3. Uniqueness of weak cell derivatives in `L2v c` -/

lemma eq_of_hasWeakCellDerivR {c : ℝ} (_hc : 0 < c) {j : Fin 2}
    {u : Plane → F8Ex.RMerid} {g₁ g₂ : L2v c}
    (h1 : ∀ k : Fin 2, F8Ex.HasWeakCellDerivR c j (fun y => u y k) (fun y => g₁ y k))
    (h2 : ∀ k : Fin 2, F8Ex.HasWeakCellDerivR c j (fun y => u y k) (fun y => g₂ y k)) :
    g₁ = g₂ := by
  have hcoord : ∀ k : Fin 2,
      (fun y => (g₁ : Plane → Vec2) y k - (g₂ : Plane → Vec2) y k) =ᵐ[cellμ c] 0 := by
    intro k
    let hpk : Vec2 →L[ℝ] ℝ := EuclideanSpace.proj k
    have hm1 : MemLp (fun y => (g₁ : Plane → Vec2) y k) 2 (UnforcedLeray.Sob.cylinder c).μ := by
      rw [UnforcedLeray.Cyl.cylinder_μ_eq]
      exact hpk.comp_memLp' (Lp.memLp g₁)
    have hm2 : MemLp (fun y => (g₂ : Plane → Vec2) y k) 2 (UnforcedLeray.Sob.cylinder c).μ := by
      rw [UnforcedLeray.Cyl.cylinder_μ_eq]
      exact hpk.comp_memLp' (Lp.memLp g₂)
    have hloc : LocallyIntegrable
        (fun y => (g₁ : Plane → Vec2) y k - (g₂ : Plane → Vec2) y k)
        (UnforcedLeray.Sob.cylinder c).μ :=
      (hm1.sub hm2).locallyIntegrable (by norm_num)
    have hae := (UnforcedLeray.Sob.cylinder c).ae_zero _ hloc fun φ hφ => by
      have hφb : B0579.IsCylTest c φ := (isCylTest_sob_iff c φ).1 hφ
      have hi1 := ((h1 k).1 φ hφb).2
      have hi2 := ((h2 k).1 φ hφb).2
      have hsub0 : ∫ y in B0579.cell c,
          ((g₁ : Plane → Vec2) y k - (g₂ : Plane → Vec2) y k) * φ y = 0 := by
        have hfn : (fun y => ((g₁ : Plane → Vec2) y k - (g₂ : Plane → Vec2) y k) * φ y) =
            fun y => (g₁ : Plane → Vec2) y k * φ y - (g₂ : Plane → Vec2) y k * φ y := by
          funext y; ring
        rw [hfn, integral_sub hi1 hi2]
        linarith [(h1 k).2 φ hφb, (h2 k).2 φ hφb]
      rw [UnforcedLeray.Cyl.cylinder_μ_eq]
      change ∫ y in UnforcedLeray.Cyl.cell c,
        φ y * ((g₁ : Plane → Vec2) y k - (g₂ : Plane → Vec2) y k) = 0
      rw [← b0579_cell_eq_cyl_cell]
      have hcomm : (fun y => φ y * ((g₁ : Plane → Vec2) y k - (g₂ : Plane → Vec2) y k)) =
          fun y => ((g₁ : Plane → Vec2) y k - (g₂ : Plane → Vec2) y k) * φ y := by
        funext y; ring
      rwa [hcomm]
    rwa [UnforcedLeray.Cyl.cylinder_μ_eq] at hae
  apply Lp.ext
  filter_upwards [hcoord 0, hcoord 1] with y hy0 hy1
  ext k
  fin_cases k
  · exact sub_eq_zero.mp hy0
  · exact sub_eq_zero.mp hy1

/-! ## 4. Translation-average operators `shiftAvgCLM`, `centeredHeatVecL2CLM`, and `DHeatCLM` -/

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
    funext w; rw [norm_smul, norm_planeShiftL2CLM hc w x]
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

lemma integrable_prod_plane {K₁ K₂ : ℝ → ℝ}
    (hK₁ : Integrable K₁ volume) (hK₂ : Integrable K₂ volume) :
    Integrable (fun w : Plane => K₁ w.1 * K₂ w.2) volume := by
  change Integrable (fun w : ℝ × ℝ => K₁ w.1 * K₂ w.2) (volume : Measure (ℝ × ℝ))
  rw [Measure.volume_eq_prod]
  exact hK₁.mul_prod hK₂

lemma norm_centeredHeatVecL2CLM_le_one_all {c : ℝ} (hc : 0 < c) (θ : ℝ) :
    ‖centeredHeatVecL2CLM hc θ‖ ≤ 1 := by
  by_cases hθ : 0 < θ
  · exact norm_centeredHeatVecL2CLM_le_one hc hθ
  · rw [centeredHeatVecL2CLM_eq_id_of_nonpos hc (not_lt.mp hθ)]
    exact ContinuousLinearMap.norm_id_le

lemma continuous_centeredHeatVecL2CLM_apply {c : ℝ} (hc : 0 < c) (x : L2v c) :
    Continuous (fun θ : ℝ => centeredHeatVecL2CLM hc θ x) := by
  let xN := centeredVecToNormalizedCLM hc x
  let xP := ((UnforcedLeray.Train.toVecL.symm : F8Ex.RMerid →L[ℝ] Plane).compLpL 2
    (UnforcedLeray.B0284.cellMeasure c)) xN
  have hp : Continuous (fun θ : ℝ => heatL2CLM hc θ xP) :=
    continuous_heatL2CLM_apply hc xP
  have hv : Continuous (fun θ : ℝ => heatVecL2CLM hc θ xN) :=
    (((UnforcedLeray.Train.toVecL : Plane →L[ℝ] F8Ex.RMerid).compLpL 2
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

/-! ## 5. Product-kernel 1D integration by parts and `DHeatCLM` -/

private lemma tendsto_qDiffQuot_cylSmooth {c : ℝ} (hc : 0 < c) {Ψ : Plane → F8Ex.RMerid}
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

private lemma tendsto_etaDiffQuot_cylSmooth {c : ℝ} (hc : 0 < c) {Ψ : Plane → F8Ex.RMerid}
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

private lemma hasDerivAt_inner_planeShift_fst {c : ℝ} (hc : 0 < c) {Ψ : Plane → F8Ex.RMerid}
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
      rw [planeShiftL2CLM_apply]; unfold planeShiftL2; simp [he0]
    rw [hq0, planeShiftL2CLM_apply, planeShiftL2CLM_apply, planeShiftL2_add_comp hc,
      planeShiftL2CLM_apply]
    congr 1; apply Prod.ext <;> simp [add_comm]
  change ⟪x, planeShiftL2CLM hc (-q, -η) (h⁻¹ • (UnforcedLeray.TrainB.qShiftL2 hc h ψ₀ - ψ₀))⟫_ℝ = _
  rw [map_smul, map_sub, hshift, inner_smul_right, inner_sub_right,
    inner_planeShiftL2CLM_adj hc (q + h, η) x ψ₀, inner_planeShiftL2CLM_adj hc (q, η) x ψ₀]
  simp [Prod.neg_mk, smul_eq_mul]

private lemma hasDerivAt_inner_planeShift_snd {c : ℝ} (hc : 0 < c) {Ψ : Plane → F8Ex.RMerid}
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
      rw [planeShiftL2CLM_apply]; unfold planeShiftL2; simp [hq0]
    rw [he0, planeShiftL2CLM_apply, planeShiftL2CLM_apply, planeShiftL2_add_comp hc,
      planeShiftL2CLM_apply]
    congr 1; apply Prod.ext <;> simp [add_comm]
  change ⟪x, planeShiftL2CLM hc (-q, -η) (h⁻¹ • (UnforcedLeray.TrainB.etaShiftL2 c h ψ₀ - ψ₀))⟫_ℝ = _
  rw [map_smul, map_sub, hshift, inner_smul_right, inner_sub_right,
    inner_planeShiftL2CLM_adj hc (q, η + h) x ψ₀, inner_planeShiftL2CLM_adj hc (q, η) x ψ₀]
  simp [Prod.neg_mk, smul_eq_mul]

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

private lemma inner_shiftAvg_prod_ibp_q {c : ℝ} (hc : 0 < c)
    {K₁ K₁' K₂ : ℝ → ℝ}
    (hK₁ : Integrable K₁ volume) (hK₁' : Integrable K₁' volume) (hK₂ : Integrable K₂ volume)
    (hderiv : ∀ q : ℝ, HasDerivAt K₁ (K₁' q) q)
    {Ψ : Plane → F8Ex.RMerid} (hΨ : UnforcedLeray.Sob.IsCylSmooth c Ψ) (x : L2v c) :
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
      K₂ η * (K₁ q * ⟪planeShiftL2CLM hc (q, η) x, ψq⟫_ℝ) := fun _ => by ring
  have hslice' : ∀ q : ℝ, (K₁' q * K₂ η) * ⟪planeShiftL2CLM hc (q, η) x, ψ₀⟫_ℝ =
      K₂ η * (K₁' q * ⟪planeShiftL2CLM hc (q, η) x, ψ₀⟫_ℝ) := fun _ => by ring
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
  rw [MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun q _ => hderiv q) (fun q _ => hasDerivAt_inner_planeShift_fst hc hΨ x q η)
    hi_uv' hi_u'v hi_uv]
  ring

private lemma inner_shiftAvg_prod_ibp_eta {c : ℝ} (hc : 0 < c)
    {K₁ K₂ K₂' : ℝ → ℝ}
    (hK₁ : Integrable K₁ volume) (hK₂ : Integrable K₂ volume) (hK₂' : Integrable K₂' volume)
    (hderiv : ∀ η : ℝ, HasDerivAt K₂ (K₂' η) η)
    {Ψ : Plane → F8Ex.RMerid} (hΨ : UnforcedLeray.Sob.IsCylSmooth c Ψ) (x : L2v c) :
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
      K₁ q * (K₂ η * ⟪planeShiftL2CLM hc (q, η) x, ψη⟫_ℝ) := fun _ => by ring
  have hslice' : ∀ η : ℝ, (K₁ q * K₂' η) * ⟪planeShiftL2CLM hc (q, η) x, ψ₀⟫_ℝ =
      K₁ q * (K₂' η * ⟪planeShiftL2CLM hc (q, η) x, ψ₀⟫_ℝ) := fun _ => by ring
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
  rw [MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun η _ => hderiv η) (fun η _ => hasDerivAt_inner_planeShift_snd hc hΨ x q η)
    hi_uv' hi_u'v hi_uv]
  ring

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

def DHeatCLM {c : ℝ} (hc : 0 < c) (j : Fin 2) (θ : ℝ) : L2v c →L[ℝ] L2v c :=
  if hθ : 0 < θ then shiftAvgCLM hc (gradKernelCoord j θ) (integrable_gradKernelCoord j hθ)
  else 0

lemma DHeatCLM_of_pos {c : ℝ} (hc : 0 < c) (j : Fin 2) {θ : ℝ} (hθ : 0 < θ) :
    DHeatCLM hc j θ = shiftAvgCLM hc (gradKernelCoord j θ) (integrable_gradKernelCoord j hθ) := by
  simp [DHeatCLM, hθ]

lemma hasWeakCellDerivR_DHeatCLM {c : ℝ} (hc : 0 < c) (j : Fin 2) {θ : ℝ} (hθ : 0 < θ)
    (x : L2v c) (k : Fin 2) :
    F8Ex.HasWeakCellDerivR c j (fun y => (centeredHeatVecL2CLM hc θ x : Plane → F8Ex.RMerid) y k)
      (fun y => (DHeatCLM hc j θ x : Plane → F8Ex.RMerid) y k) := by
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · have hmψ : MemLp ψ 2 (cellμ c) := memLp_cellμ_of_test hψ
    have hmpd : MemLp (B0579.pd j ψ) 2 (cellμ c) := memLp_cellμ_of_test (hψ.pd j)
    rw [b0579_cell_eq_cyl_cell]
    exact ⟨(UnforcedLeray.Cyl.memLp_component (centeredHeatVecL2CLM hc θ x) k).integrable_mul hmpd,
      (UnforcedLeray.Cyl.memLp_component (DHeatCLM hc j θ x) k).integrable_mul hmψ⟩
  · have hΨ := isCylSmooth_single hψ k
    have hdir : (fun y => fderiv ℝ (fun z => ψ z • EuclideanSpace.single k (1 : ℝ)) y
        (B0579.dir j)) = fun y => B0579.pd j ψ y • EuclideanSpace.single k (1 : ℝ) := by
      funext y; rw [fderiv_smul_const (hψ.differentiable y)]; rfl
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

lemma hasWeakCellDerivR_shiftAvgCLM {c : ℝ} (hc : 0 < c) {K : Plane → ℝ}
    (hK : Integrable K volume) {x dx : L2v c} {j : Fin 2}
    (h : ∀ k : Fin 2, F8Ex.HasWeakCellDerivR c j (fun y => x y k) (fun y => dx y k)) :
    ∀ k : Fin 2, F8Ex.HasWeakCellDerivR c j
      (fun y => (shiftAvgCLM hc K hK x : Plane → F8Ex.RMerid) y k)
      (fun y => (shiftAvgCLM hc K hK dx : Plane → F8Ex.RMerid) y k) := by
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
      funext y; rw [fderiv_smul_const (hψ.differentiable y)]; rfl
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
            B0579.pd j ψw z • EuclideanSpace.single k (1 : ℝ) := by rw [hpd_w]
        exact h1.trans (hm.trans h2.symm)
      rw [inner_planeShiftL2CLM_adj hc w x, inner_planeShiftL2CLM_adj hc w dx,
        hshift0, hshift1, inner_cylSmooth_single (hψw.pd j) k x,
        inner_cylSmooth_single hψw k dx, (h k).2 ψw hψw]
    have hfun : (fun w : Plane => K w * ⟪planeShiftL2CLM hc w x,
        cylSmoothToL2 (hΨ.dir (B0579.dir j))⟫_ℝ) =
        fun w => -(K w * ⟪planeShiftL2CLM hc w dx, cylSmoothToL2 hΨ⟫_ℝ) := by
      funext w; rw [hpt w]; ring
    rw [hfun, integral_neg]

lemma hasWeakCellDerivR_centeredHeatVecL2CLM {c : ℝ} (hc : 0 < c) (θ : ℝ)
    {x dx : L2v c} {j : Fin 2}
    (h : ∀ k : Fin 2, F8Ex.HasWeakCellDerivR c j (fun y => x y k) (fun y => dx y k)) :
    ∀ k : Fin 2, F8Ex.HasWeakCellDerivR c j
      (fun y => (centeredHeatVecL2CLM hc θ x : Plane → F8Ex.RMerid) y k)
      (fun y => (centeredHeatVecL2CLM hc θ dx : Plane → F8Ex.RMerid) y k) := by
  by_cases hθ : 0 < θ
  · intro k
    have havg := hasWeakCellDerivR_shiftAvgCLM hc
      (integrable_prod_plane (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
        (UnforcedLeray.B0296.integrable_heatKernel1 hθ)) h k
    have hx := centeredHeat_eq_shiftAvgCLM hc hθ x
    have hdx := centeredHeat_eq_shiftAvgCLM hc hθ dx
    change F8Ex.HasWeakCellDerivR c j
      (fun y => (shiftAvgCLM hc (heatKernel2 θ) _ x : Plane → F8Ex.RMerid) y k)
      (fun y => (shiftAvgCLM hc (heatKernel2 θ) _ dx : Plane → F8Ex.RMerid) y k) at havg
    rwa [← hx, ← hdx] at havg
  · rw [centeredHeatVecL2CLM_eq_id_of_nonpos hc (not_lt.mp hθ)]
    exact h

lemma DHeatCLM_eq_centeredHeat_of_weakDeriv {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {x dx : L2v c} {j : Fin 2}
    (h : ∀ k : Fin 2, F8Ex.HasWeakCellDerivR c j (fun y => x y k) (fun y => dx y k)) :
    DHeatCLM hc j θ x = centeredHeatVecL2CLM hc θ dx :=
  eq_of_hasWeakCellDerivR hc (hasWeakCellDerivR_DHeatCLM hc j hθ x)
    (hasWeakCellDerivR_centeredHeatVecL2CLM hc θ h)

/-! ## 6. Skew-adjointness of `DHeatCLM` and dissipation identity -/

private lemma gradKernelCoord_neg (j : Fin 2) (θ : ℝ) (w : Plane) :
    gradKernelCoord j θ (-w) = -gradKernelCoord j θ w := by
  fin_cases j <;>
    simp [gradKernelCoord, UnforcedLeray.B0296.dHeatKernel,
      UnforcedLeray.B0191.heatKernel, neg_div]

lemma inner_DHeatCLM_skew {c θ : ℝ} (hc : 0 < c) (j : Fin 2) (hθ : 0 < θ) (x y : L2v c) :
    ⟪DHeatCLM hc j θ x, y⟫_ℝ = -⟪x, DHeatCLM hc j θ y⟫_ℝ := by
  have hi_K := integrable_gradKernelCoord j hθ
  rw [DHeatCLM_of_pos hc j hθ, inner_shiftAvgCLM hc hi_K x y,
    real_inner_comm _ x, inner_shiftAvgCLM hc hi_K y x]
  have h1 : (fun w : Plane =>
      gradKernelCoord j θ w * ⟪planeShiftL2CLM hc w x, y⟫_ℝ) =
      fun w => -((fun v : Plane =>
        gradKernelCoord j θ v * ⟪planeShiftL2CLM hc v y, x⟫_ℝ) (-w)) := by
    funext w
    dsimp only
    rw [inner_planeShiftL2CLM_adj hc w x y, gradKernelCoord_neg j θ w, real_inner_comm]
    ring
  rw [h1, integral_neg]
  exact congrArg Neg.neg (integral_neg_eq_self
    (fun v : Plane => gradKernelCoord j θ v * ⟪planeShiftL2CLM hc v y, x⟫_ℝ) volume)

lemma inner_DHeatCLM_heat_weak {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {x dx : L2v c} {j : Fin 2}
    (h : ∀ k : Fin 2, F8Ex.HasWeakCellDerivR c j (fun y => x y k) (fun y => dx y k)) :
    ⟪DHeatCLM hc j θ dx, centeredHeatVecL2CLM hc θ x⟫_ℝ =
      -‖centeredHeatVecL2CLM hc θ dx‖ ^ 2 := by
  rw [inner_DHeatCLM_skew hc j hθ,
    DHeatCLM_eq_centeredHeat_of_weakDeriv hc hθ (hasWeakCellDerivR_centeredHeatVecL2CLM hc θ h),
    ← inner_centeredHeatVecL2CLM_symm hc hθ.le, real_inner_self_eq_norm_sq]

lemma inner_dir_cylSmooth_centeredHeat {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {Φ : Plane → F8Ex.RMerid} (hΦ : UnforcedLeray.Sob.IsCylSmooth c Φ)
    (j : Fin 2) (x : L2v c) :
    ⟪cylSmoothToL2 (hΦ.dir (B0579.dir j)), centeredHeatVecL2CLM hc θ x⟫_ℝ =
      -⟪cylSmoothToL2 hΦ, DHeatCLM hc j θ x⟫_ℝ := by
  rw [real_inner_comm (centeredHeatVecL2CLM hc θ x) _,
    real_inner_comm (DHeatCLM hc j θ x) (cylSmoothToL2 hΦ),
    centeredHeat_eq_shiftAvgCLM hc hθ x, DHeatCLM_of_pos hc j hθ]
  fin_cases j
  · exact inner_shiftAvg_prod_ibp_q hc
      (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
      (UnforcedLeray.B0296.integrable_dHeatKernel hθ)
      (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
      (UnforcedLeray.B0296.hasDerivAt_heatKernel hθ.ne') hΦ x
  · exact inner_shiftAvg_prod_ibp_eta hc
      (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
      (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
      (UnforcedLeray.B0296.integrable_dHeatKernel hθ)
      (UnforcedLeray.B0296.hasDerivAt_heatKernel hθ.ne') hΦ x

end UnforcedLeray.Short.IIb.UnitWeakUniqueAux
