import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_3
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org.OrbitSmoothing
import UnforcedLeray.Infra.JointMeasurableRep
import UnforcedLeray.Lib.BochnerTime.Slices
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# `UnitDuhamelStep.Propagator`: Non-autonomous Oseen propagator `S_0(t, τ)`, Chapman–Kolmogorov,
linearity, continuity, right-continuity in `τ`, and joint strong measurability on the unit triangle

Helper module 1 for `PartII-b:F8/1/org/3/1` (`CylUnitDuhamelStep`, SP 2296–2305).
All declarations live inside `UnforcedLeray.Short.IIb.UnitDuhamelStepAux` (R6).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIb.UnitDuhamelStepAux

open UnforcedLeray.Short.IIb
open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-! ## 1. `L2Cell`, `X3`, `H1Set`, test-pairing CLMs, and Bochner closure -/

abbrev L2Cell (c : ℝ) : Type := Lp CMerid 2 (F8Sm.cellMeas c)

abbrev X3 (c : ℝ) : Type := L2Cell c × L2Cell c × L2Cell c

def h1RealNorm {c : ℝ} (x : X3 c) : ℝ :=
  ‖x.1‖ + ‖x.2.1‖ + ‖x.2.2‖

def h1ENN {c : ℝ} (x : X3 c) : ℝ≥0∞ :=
  F8U.cylH1 c x.1 x.2.1 x.2.2

def H1Set (c : ℝ) : Set (X3 c) :=
  {x : X3 c | F8U.IsCylH1Datum c x.1 x.2.1 x.2.2}

lemma h1RealNorm_nonneg {c : ℝ} (x : X3 c) : 0 ≤ h1RealNorm x := by
  unfold h1RealNorm
  positivity

@[simp]
lemma h1RealNorm_zero (c : ℝ) : h1RealNorm (0 : X3 c) = 0 := by
  simp [h1RealNorm]

lemma h1RealNorm_neg {c : ℝ} (x : X3 c) : h1RealNorm (-x) = h1RealNorm x := by
  simp [h1RealNorm]

lemma h1RealNorm_smul {c : ℝ} (a : ℝ) (x : X3 c) :
    h1RealNorm (a • x) = |a| * h1RealNorm x := by
  unfold h1RealNorm
  simp only [Prod.smul_fst, Prod.smul_snd, norm_smul, Real.norm_eq_abs]
  ring

lemma h1RealNorm_add_le {c : ℝ} (x y : X3 c) :
    h1RealNorm (x + y) ≤ h1RealNorm x + h1RealNorm y := by
  unfold h1RealNorm
  have b1 : ‖(x + y).1‖ ≤ ‖x.1‖ + ‖y.1‖ := norm_add_le x.1 y.1
  have b2 : ‖(x + y).2.1‖ ≤ ‖x.2.1‖ + ‖y.2.1‖ := norm_add_le x.2.1 y.2.1
  have b3 : ‖(x + y).2.2‖ ≤ ‖x.2.2‖ + ‖y.2.2‖ := norm_add_le x.2.2 y.2.2
  linarith

lemma h1RealNorm_sub_le {c : ℝ} (x y : X3 c) :
    h1RealNorm (x - y) ≤ h1RealNorm x + h1RealNorm y := by
  simpa [sub_eq_add_neg, h1RealNorm_neg] using h1RealNorm_add_le x (-y)

lemma norm_le_h1RealNorm {c : ℝ} (x : X3 c) : ‖x‖ ≤ h1RealNorm x := by
  rw [Prod.norm_def, Prod.norm_def]
  unfold h1RealNorm
  refine max_le (by linarith [norm_nonneg x.2.1, norm_nonneg x.2.2]) ?_
  exact max_le (by linarith [norm_nonneg x.1, norm_nonneg x.2.2])
    (by linarith [norm_nonneg x.1, norm_nonneg x.2.1])

lemma h1RealNorm_le_three_norm {c : ℝ} (x : X3 c) : h1RealNorm x ≤ 3 * ‖x‖ := by
  have b1 : ‖x.1‖ ≤ ‖x‖ := norm_fst_le x
  have b2 : ‖x.2.1‖ ≤ ‖x‖ := (norm_fst_le x.2).trans (norm_snd_le x)
  have b3 : ‖x.2.2‖ ≤ ‖x‖ := (norm_snd_le x.2).trans (norm_snd_le x)
  unfold h1RealNorm
  linarith

lemma cellL2_coe_eq_ofReal_norm {c : ℝ} (u : L2Cell c) :
    F8U.cellL2 c u = ENNReal.ofReal ‖u‖ := by
  rw [Lp.norm_def]
  exact (ENNReal.ofReal_toReal (Lp.memLp u).eLpNorm_ne_top).symm

lemma h1ENN_eq_ofReal {c : ℝ} (x : X3 c) :
    h1ENN x = ENNReal.ofReal (h1RealNorm x) := by
  unfold h1ENN F8U.cylH1 h1RealNorm
  rw [cellL2_coe_eq_ofReal_norm, cellL2_coe_eq_ofReal_norm, cellL2_coe_eq_ofReal_norm,
    ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
    ← ENNReal.ofReal_add (by positivity) (norm_nonneg _)]

lemma toReal_h1ENN {c : ℝ} (x : X3 c) : (h1ENN x).toReal = h1RealNorm x := by
  rw [h1ENN_eq_ofReal, ENNReal.toReal_ofReal (h1RealNorm_nonneg x)]

/-- Single-coordinate meridional lift of a real cylinder test `ψ`. -/
def singleCylVec (k : Fin 2) (ψ : B0579.Plane → ℝ) (y : B0579.Plane) : CMerid :=
  WithLp.toLp 2 fun i : Fin 2 => if i = k then (ψ y : ℂ) else 0

lemma memLp_singleCylVec {c : ℝ} (hc : 0 < c) (k : Fin 2) {ψ : B0579.Plane → ℝ}
    (hψ : B0579.IsCylTest c ψ) :
    MemLp (singleCylVec k ψ) 2 (F8Sm.cellMeas c) := by
  have hc_vec : Continuous (singleCylVec k ψ) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    by_cases hik : i = k
    · simp only [hik, ↓reduceIte]
      exact Complex.continuous_ofReal.comp hψ.continuous
    · simp only [hik, ↓reduceIte]
      exact continuous_const
  have hsq : IntegrableOn (fun y => ‖singleCylVec k ψ y‖ ^ 2) (B0579.cell c) volume := by
    have heq : (fun y : B0579.Plane => ‖singleCylVec k ψ y‖ ^ 2) =
        fun y => ‖((ψ y : ℂ) * (ψ y : ℂ))‖ := by
      funext y
      rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
      fin_cases k <;> simp [singleCylVec, sq]
    rw [heq]
    exact (F8Sm.integrableOn_cont_mul_cylTest hc
      (Complex.continuous_ofReal.comp hψ.continuous) hψ).norm
  exact (memLp_two_iff_integrable_sq_norm hc_vec.aestronglyMeasurable).2 hsq

/-- Continuous `ℝ`-linear functional `u ↦ ∫_{cell c} u(y)_k * ψ(y) dy` on `L2Cell c`. -/
def pairTestCLM {c : ℝ} (hc : 0 < c) {ψ : B0579.Plane → ℝ} (hψ : B0579.IsCylTest c ψ)
    (k : Fin 2) : L2Cell c →L[ℝ] ℂ :=
  (innerSL ℂ ((memLp_singleCylVec hc k hψ).toLp (singleCylVec k ψ))).restrictScalars ℝ

lemma pairTestCLM_apply {c : ℝ} (hc : 0 < c) {ψ : B0579.Plane → ℝ}
    (hψ : B0579.IsCylTest c ψ) (k : Fin 2) (u : L2Cell c) :
    pairTestCLM hc hψ k u = ∫ y in B0579.cell c, u y k * (ψ y : ℂ) := by
  unfold pairTestCLM
  change inner ℂ ((memLp_singleCylVec hc k hψ).toLp (singleCylVec k ψ)) u = _
  rw [L2.inner_def (𝕜 := ℂ)]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_singleCylVec hc k hψ).coeFn_toLp] with y hy
  rw [hy, PiLp.inner_apply, Fin.sum_univ_two]
  fin_cases k <;> simp [singleCylVec, RCLike.inner_apply, mul_comm]

lemma integrableOn_coe_mul_cylTest {c : ℝ} (hc : 0 < c) (u : L2Cell c) (k : Fin 2)
    {ψ : B0579.Plane → ℝ} (hψ : B0579.IsCylTest c ψ) :
    IntegrableOn (fun y => u y k * (ψ y : ℂ)) (B0579.cell c) volume := by
  have hm1 : MemLp (fun y => u y k) 2 (F8Sm.cellMeas c) :=
    F8Sm.memLp_coord_cmerid (Lp.memLp u) k
  have hm2 : MemLp (fun y => (ψ y : ℂ)) 2 (F8Sm.cellMeas c) := by
    have := F8Sm.memLp_coord_cmerid (memLp_singleCylVec hc k hψ) k
    simpa [singleCylVec] using this
  exact hm1.integrable_mul hm2

lemma hasWeakCellDerivC_congr {c : ℝ} {j : Fin 2} {f f' g g' : B0579.Plane → ℂ}
    (hf : f =ᵐ[F8Sm.cellMeas c] f') (hg : g =ᵐ[F8Sm.cellMeas c] g')
    (h : IIIa.HasWeakCellDerivC c j f g) :
    IIIa.HasWeakCellDerivC c j f' g' := by
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · refine (h.1 ψ hψ).1.congr_fun_ae ?_
    filter_upwards [hf] with y hy; rw [hy]
  · refine (h.1 ψ hψ).2.congr_fun_ae ?_
    filter_upwards [hg] with y hy; rw [hy]
  · have e1 : ∫ y in B0579.cell c, f' y * (B0579.pd j ψ y : ℂ) =
        ∫ y in B0579.cell c, f y * (B0579.pd j ψ y : ℂ) := by
      refine integral_congr_ae ?_
      filter_upwards [hf] with y hy; rw [hy]
    have e2 : ∫ y in B0579.cell c, g' y * (ψ y : ℂ) =
        ∫ y in B0579.cell c, g y * (ψ y : ℂ) := by
      refine integral_congr_ae ?_
      filter_upwards [hg] with y hy; rw [hy]
    rw [e1, e2, h.2 ψ hψ]

lemma isCellSolenoidal_congr {c : ℝ} {f f' : B0579.Plane → CMerid}
    (hf : f =ᵐ[F8Sm.cellMeas c] f') (h : F8U.IsCellSolenoidal c f) :
    F8U.IsCellSolenoidal c f' := by
  intro ψ hψ
  obtain ⟨hi, hz⟩ := h ψ hψ
  have hae : (fun y => f' y 0 * (B0579.pd 0 ψ y : ℂ) + f' y 1 * (B0579.pd 1 ψ y : ℂ))
      =ᵐ[F8Sm.cellMeas c]
      (fun y => f y 0 * (B0579.pd 0 ψ y : ℂ) + f y 1 * (B0579.pd 1 ψ y : ℂ)) := by
    filter_upwards [hf] with y hy; rw [hy]
  exact ⟨hi.congr_fun_ae hae.symm, (integral_congr_ae hae).trans hz⟩

lemma isCylH1Datum_congr {c : ℝ} {u uq uη u' uq' uη' : B0579.Plane → CMerid}
    (hu : u =ᵐ[F8Sm.cellMeas c] u') (huq : uq =ᵐ[F8Sm.cellMeas c] uq')
    (huη : uη =ᵐ[F8Sm.cellMeas c] uη')
    (h : F8U.IsCylH1Datum c u uq uη) :
    F8U.IsCylH1Datum c u' uq' uη' where
  weak_q k := hasWeakCellDerivC_congr (hu.mono fun _ hx => congrArg (· k) hx)
    (huq.mono fun _ hx => congrArg (· k) hx) (h.weak_q k)
  weak_eta k := hasWeakCellDerivC_congr (hu.mono fun _ hx => congrArg (· k) hx)
    (huη.mono fun _ hx => congrArg (· k) hx) (h.weak_eta k)
  solenoidal := isCellSolenoidal_congr hu h.solenoidal
  memL2 := ⟨h.memL2.1.ae_eq hu, h.memL2.2.1.ae_eq huq, h.memL2.2.2.ae_eq huη⟩

/-- Canonical `X3 c` element built from an `IsCylH1Datum` triple. -/
def datumToX3 {c : ℝ} {u uq uη : B0579.Plane → CMerid}
    (h : F8U.IsCylH1Datum c u uq uη) : X3 c :=
  (h.memL2.1.toLp u, h.memL2.2.1.toLp uq, h.memL2.2.2.toLp uη)

lemma datumToX3_mem_H1Set {c : ℝ} {u uq uη : B0579.Plane → CMerid}
    (h : F8U.IsCylH1Datum c u uq uη) :
    datumToX3 h ∈ H1Set c :=
  isCylH1Datum_congr h.memL2.1.coeFn_toLp.symm h.memL2.2.1.coeFn_toLp.symm
    h.memL2.2.2.coeFn_toLp.symm h

lemma h1ENN_datumToX3 {c : ℝ} {u uq uη : B0579.Plane → CMerid}
    (h : F8U.IsCylH1Datum c u uq uη) :
    h1ENN (datumToX3 h) = F8U.cylH1 c u uq uη := by
  unfold h1ENN datumToX3 F8U.cylH1 F8U.cellL2
  rw [eLpNorm_congr_ae h.memL2.1.coeFn_toLp,
    eLpNorm_congr_ae h.memL2.2.1.coeFn_toLp,
    eLpNorm_congr_ae h.memL2.2.2.coeFn_toLp]

lemma zero_mem_H1Set (c : ℝ) : (0 : X3 c) ∈ H1Set c := by
  have hz : (0 : B0579.Plane → CMerid) =ᵐ[F8Sm.cellMeas c] ((0 : L2Cell c) : B0579.Plane → CMerid) :=
    (Lp.coeFn_zero CMerid 2 (F8Sm.cellMeas c)).symm
  refine isCylH1Datum_congr hz hz hz ?_
  refine ⟨fun _ => ⟨fun _ _ => ⟨by simp, by simp⟩, fun _ _ => by simp⟩,
    fun _ => ⟨fun _ _ => ⟨by simp, by simp⟩, fun _ _ => by simp⟩,
    fun _ _ => ⟨by simp, by simp⟩,
    ⟨MemLp.zero, MemLp.zero, MemLp.zero⟩⟩

lemma add_mem_H1Set {c : ℝ} {x y : X3 c} (hx : x ∈ H1Set c) (hy : y ∈ H1Set c) :
    x + y ∈ H1Set c := by
  have h1 : (fun z => x.1 z + y.1 z) =ᵐ[F8Sm.cellMeas c] (x + y).1 :=
    (Lp.coeFn_add x.1 y.1).symm
  have h2 : (fun z => x.2.1 z + y.2.1 z) =ᵐ[F8Sm.cellMeas c] (x + y).2.1 :=
    (Lp.coeFn_add x.2.1 y.2.1).symm
  have h3 : (fun z => x.2.2 z + y.2.2 z) =ᵐ[F8Sm.cellMeas c] (x + y).2.2 :=
    (Lp.coeFn_add x.2.2 y.2.2).symm
  refine isCylH1Datum_congr h1 h2 h3 ?_
  have hwAdd : ∀ {j : Fin 2} {f₁ g₁ f₂ g₂ : B0579.Plane → ℂ},
      IIIa.HasWeakCellDerivC c j f₁ g₁ → IIIa.HasWeakCellDerivC c j f₂ g₂ →
      IIIa.HasWeakCellDerivC c j (fun z => f₁ z + f₂ z) (fun z => g₁ z + g₂ z) := by
    intro j f₁ g₁ f₂ g₂ a b
    refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
    · exact ((a.1 ψ hψ).1.add (b.1 ψ hψ).1).congr_fun
        (fun z _ => by simp only [Pi.add_apply]; ring) (B0579.measurableSet_cell c)
    · exact ((a.1 ψ hψ).2.add (b.1 ψ hψ).2).congr_fun
        (fun z _ => by simp only [Pi.add_apply]; ring) (B0579.measurableSet_cell c)
    · have eL : (fun z => (f₁ z + f₂ z) * (B0579.pd j ψ z : ℂ)) =
          fun z => f₁ z * (B0579.pd j ψ z : ℂ) + f₂ z * (B0579.pd j ψ z : ℂ) := by
        funext z; ring
      have eR : (fun z => (g₁ z + g₂ z) * (ψ z : ℂ)) =
          fun z => g₁ z * (ψ z : ℂ) + g₂ z * (ψ z : ℂ) := by
        funext z; ring
      rw [eL, eR, integral_add (a.1 ψ hψ).1 (b.1 ψ hψ).1,
        integral_add (a.1 ψ hψ).2 (b.1 ψ hψ).2, a.2 ψ hψ, b.2 ψ hψ]
      ring
  refine ⟨fun k => hwAdd (hx.weak_q k) (hy.weak_q k),
    fun k => hwAdd (hx.weak_eta k) (hy.weak_eta k),
    fun ψ hψ => ?_,
    ⟨hx.memL2.1.add hy.memL2.1, hx.memL2.2.1.add hy.memL2.2.1, hx.memL2.2.2.add hy.memL2.2.2⟩⟩
  have heq : (fun z => (x.1 z + y.1 z) 0 * (B0579.pd 0 ψ z : ℂ) +
        (x.1 z + y.1 z) 1 * (B0579.pd 1 ψ z : ℂ)) =
      fun z => (x.1 z 0 * (B0579.pd 0 ψ z : ℂ) + x.1 z 1 * (B0579.pd 1 ψ z : ℂ)) +
        (y.1 z 0 * (B0579.pd 0 ψ z : ℂ) + y.1 z 1 * (B0579.pd 1 ψ z : ℂ)) := by
    funext z; simp only [PiLp.add_apply]; ring
  rw [heq]
  exact ⟨(hx.solenoidal ψ hψ).1.add (hy.solenoidal ψ hψ).1,
    by rw [integral_add (hx.solenoidal ψ hψ).1 (hy.solenoidal ψ hψ).1,
      (hx.solenoidal ψ hψ).2, (hy.solenoidal ψ hψ).2, add_zero]⟩

lemma smul_mem_H1Set {c : ℝ} (a : ℝ) {x : X3 c} (hx : x ∈ H1Set c) :
    a • x ∈ H1Set c := by
  have h1 : (fun z => a • x.1 z) =ᵐ[F8Sm.cellMeas c] (a • x).1 :=
    (Lp.coeFn_smul a x.1).symm
  have h2 : (fun z => a • x.2.1 z) =ᵐ[F8Sm.cellMeas c] (a • x).2.1 :=
    (Lp.coeFn_smul a x.2.1).symm
  have h3 : (fun z => a • x.2.2 z) =ᵐ[F8Sm.cellMeas c] (a • x).2.2 :=
    (Lp.coeFn_smul a x.2.2).symm
  refine isCylH1Datum_congr h1 h2 h3 ?_
  have hwSmul : ∀ {j : Fin 2} {f g : B0579.Plane → ℂ},
      IIIa.HasWeakCellDerivC c j f g →
      IIIa.HasWeakCellDerivC c j (fun z => (a : ℂ) * f z) (fun z => (a : ℂ) * g z) := by
    intro j f g hfg
    refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
    · exact IntegrableOn.congr_fun ((hfg.1 ψ hψ).1.const_mul (a : ℂ))
        (fun z _ => by simp only [mul_assoc]) (B0579.measurableSet_cell c)
    · exact IntegrableOn.congr_fun ((hfg.1 ψ hψ).2.const_mul (a : ℂ))
        (fun z _ => by simp only [mul_assoc]) (B0579.measurableSet_cell c)
    · have eL : (fun z => (a : ℂ) * f z * (B0579.pd j ψ z : ℂ)) =
          fun z => (a : ℂ) * (f z * (B0579.pd j ψ z : ℂ)) := by funext z; ring
      have eR : (fun z => (a : ℂ) * g z * (ψ z : ℂ)) =
          fun z => (a : ℂ) * (g z * (ψ z : ℂ)) := by funext z; ring
      rw [eL, eR, integral_const_mul, integral_const_mul, hfg.2 ψ hψ, mul_neg]
  have hsm : ∀ (u : L2Cell c) (k : Fin 2),
      (fun z => (a • u z) k) = fun z => (a : ℂ) * u z k := by
    intro u k; funext z; simp [Complex.real_smul]
  refine ⟨fun k => by rw [hsm, hsm]; exact hwSmul (hx.weak_q k),
    fun k => by rw [hsm, hsm]; exact hwSmul (hx.weak_eta k),
    fun ψ hψ => ?_,
    ⟨hx.memL2.1.const_smul a, hx.memL2.2.1.const_smul a, hx.memL2.2.2.const_smul a⟩⟩
  have heq : (fun z => (a • x.1 z) 0 * (B0579.pd 0 ψ z : ℂ) +
        (a • x.1 z) 1 * (B0579.pd 1 ψ z : ℂ)) =
      fun z => (a : ℂ) * (x.1 z 0 * (B0579.pd 0 ψ z : ℂ) + x.1 z 1 * (B0579.pd 1 ψ z : ℂ)) := by
    funext z; simp only [PiLp.smul_apply, Complex.real_smul]; ring
  rw [heq]
  exact ⟨(hx.solenoidal ψ hψ).1.const_mul (a : ℂ),
    by rw [integral_const_mul, (hx.solenoidal ψ hψ).2, mul_zero]⟩

lemma sub_mem_H1Set {c : ℝ} {x y : X3 c} (hx : x ∈ H1Set c) (hy : y ∈ H1Set c) :
    x - y ∈ H1Set c := by
  rw [sub_eq_add_neg]
  have hny : -y = (-1 : ℝ) • y := by simp
  rw [hny]
  exact add_mem_H1Set hx (smul_mem_H1Set (-1) hy)

lemma integral_fst_X3 {α : Type*} [MeasurableSpace α] {μ : Measure α} {c : ℝ}
    {F : α → X3 c} (hF : Integrable F μ) :
    (∫ a, F a ∂μ).1 = ∫ a, (F a).1 ∂μ :=
  ((ContinuousLinearMap.fst ℝ (L2Cell c) (L2Cell c × L2Cell c)).integral_comp_comm hF).symm

lemma integral_snd_fst_X3 {α : Type*} [MeasurableSpace α] {μ : Measure α} {c : ℝ}
    {F : α → X3 c} (hF : Integrable F μ) :
    (∫ a, F a ∂μ).2.1 = ∫ a, (F a).2.1 ∂μ :=
  (((ContinuousLinearMap.fst ℝ (L2Cell c) (L2Cell c)).comp
    (ContinuousLinearMap.snd ℝ (L2Cell c) (L2Cell c × L2Cell c))).integral_comp_comm hF).symm

lemma integral_snd_snd_X3 {α : Type*} [MeasurableSpace α] {μ : Measure α} {c : ℝ}
    {F : α → X3 c} (hF : Integrable F μ) :
    (∫ a, F a ∂μ).2.2 = ∫ a, (F a).2.2 ∂μ :=
  (((ContinuousLinearMap.snd ℝ (L2Cell c) (L2Cell c)).comp
    (ContinuousLinearMap.snd ℝ (L2Cell c) (L2Cell c × L2Cell c))).integral_comp_comm hF).symm

/-- Exact componentwise Bochner triangle inequality in `h1RealNorm` (no factor of `3` loss). -/
lemma h1RealNorm_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {c : ℝ}
    {F : α → X3 c} (hF : Integrable F μ) :
    h1RealNorm (∫ a, F a ∂μ) ≤ ∫ a, h1RealNorm (F a) ∂μ := by
  have h1 : Integrable (fun a => (F a).1) μ :=
    (ContinuousLinearMap.fst ℝ (L2Cell c) (L2Cell c × L2Cell c)).integrable_comp hF
  have h2 : Integrable (fun a => (F a).2.1) μ :=
    ((ContinuousLinearMap.fst ℝ (L2Cell c) (L2Cell c)).comp
      (ContinuousLinearMap.snd ℝ (L2Cell c) (L2Cell c × L2Cell c))).integrable_comp hF
  have h3 : Integrable (fun a => (F a).2.2) μ :=
    ((ContinuousLinearMap.snd ℝ (L2Cell c) (L2Cell c)).comp
      (ContinuousLinearMap.snd ℝ (L2Cell c) (L2Cell c × L2Cell c))).integrable_comp hF
  have hsum : ∫ a, h1RealNorm (F a) ∂μ =
      (∫ a, ‖(F a).1‖ ∂μ) + (∫ a, ‖(F a).2.1‖ ∂μ) + (∫ a, ‖(F a).2.2‖ ∂μ) := by
    unfold h1RealNorm
    have ha1 := integral_add (h1.norm.add h2.norm) h3.norm
    have ha2 := integral_add h1.norm h2.norm
    dsimp only [Pi.add_apply] at ha1 ha2
    rw [ha1, ha2]
  rw [hsum]
  unfold h1RealNorm
  rw [integral_fst_X3 hF, integral_snd_fst_X3 hF, integral_snd_snd_X3 hF]
  exact add_le_add (add_le_add (norm_integral_le_integral_norm _)
    (norm_integral_le_integral_norm _)) (norm_integral_le_integral_norm _)

/-- `H1Set c` is closed under Bochner integration on any measure space. -/
lemma integral_mem_H1Set {α : Type*} [MeasurableSpace α] {μ : Measure α} {c : ℝ}
    (hc : 0 < c) {F : α → X3 c} (hF : Integrable F μ) (hmem : ∀ᵐ a ∂μ, F a ∈ H1Set c) :
    (∫ a, F a ∂μ) ∈ H1Set c := by
  set X : X3 c := ∫ a, F a ∂μ
  have h1 : Integrable (fun a => (F a).1) μ :=
    (ContinuousLinearMap.fst ℝ (L2Cell c) (L2Cell c × L2Cell c)).integrable_comp hF
  have h2 : Integrable (fun a => (F a).2.1) μ :=
    ((ContinuousLinearMap.fst ℝ (L2Cell c) (L2Cell c)).comp
      (ContinuousLinearMap.snd ℝ (L2Cell c) (L2Cell c × L2Cell c))).integrable_comp hF
  have h3 : Integrable (fun a => (F a).2.2) μ :=
    ((ContinuousLinearMap.snd ℝ (L2Cell c) (L2Cell c)).comp
      (ContinuousLinearMap.snd ℝ (L2Cell c) (L2Cell c × L2Cell c))).integrable_comp hF
  have hX1 : X.1 = ∫ a, (F a).1 ∂μ := integral_fst_X3 hF
  have hX2 : X.2.1 = ∫ a, (F a).2.1 ∂μ := integral_snd_fst_X3 hF
  have hX3 : X.2.2 = ∫ a, (F a).2.2 ∂μ := integral_snd_snd_X3 hF
  refine ⟨fun k => ⟨fun ψ hψ => ⟨integrableOn_coe_mul_cylTest hc X.1 k (hψ.pd 0),
      integrableOn_coe_mul_cylTest hc X.2.1 k hψ⟩, fun ψ hψ => ?_⟩,
    fun k => ⟨fun ψ hψ => ⟨integrableOn_coe_mul_cylTest hc X.1 k (hψ.pd 1),
      integrableOn_coe_mul_cylTest hc X.2.2 k hψ⟩, fun ψ hψ => ?_⟩,
    fun ψ hψ => ⟨(integrableOn_coe_mul_cylTest hc X.1 0 (hψ.pd 0)).add
      (integrableOn_coe_mul_cylTest hc X.1 1 (hψ.pd 1)), ?_⟩,
    ⟨Lp.memLp X.1, Lp.memLp X.2.1, Lp.memLp X.2.2⟩⟩
  · rw [← pairTestCLM_apply hc (hψ.pd 0) k X.1, ← pairTestCLM_apply hc hψ k X.2.1,
      hX1, hX2, ← (pairTestCLM hc (hψ.pd 0) k).integral_comp_comm h1,
      ← (pairTestCLM hc hψ k).integral_comp_comm h2, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hmem] with a ha
    change pairTestCLM hc (hψ.pd 0) k (F a).1 = -pairTestCLM hc hψ k (F a).2.1
    rw [pairTestCLM_apply, pairTestCLM_apply]
    exact (ha.weak_q k).2 ψ hψ
  · rw [← pairTestCLM_apply hc (hψ.pd 1) k X.1, ← pairTestCLM_apply hc hψ k X.2.2,
      hX1, hX3, ← (pairTestCLM hc (hψ.pd 1) k).integral_comp_comm h1,
      ← (pairTestCLM hc hψ k).integral_comp_comm h3, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hmem] with a ha
    change pairTestCLM hc (hψ.pd 1) k (F a).1 = -pairTestCLM hc hψ k (F a).2.2
    rw [pairTestCLM_apply, pairTestCLM_apply]
    exact (ha.weak_eta k).2 ψ hψ
  · rw [integral_add (integrableOn_coe_mul_cylTest hc X.1 0 (hψ.pd 0))
      (integrableOn_coe_mul_cylTest hc X.1 1 (hψ.pd 1)),
      ← pairTestCLM_apply hc (hψ.pd 0) 0 X.1, ← pairTestCLM_apply hc (hψ.pd 1) 1 X.1]
    let L := pairTestCLM hc (hψ.pd 0) 0 + pairTestCLM hc (hψ.pd 1) 1
    change L X.1 = 0
    rw [hX1, ← L.integral_comp_comm h1]
    refine (integral_congr_ae (g := fun _ => (0 : ℂ)) ?_).trans (by simp)
    filter_upwards [hmem] with a ha
    dsimp [L]
    rw [add_apply, pairTestCLM_apply, pairTestCLM_apply,
      ← integral_add (integrableOn_coe_mul_cylTest hc (F a).1 0 (hψ.pd 0))
        (integrableOn_coe_mul_cylTest hc (F a).1 1 (hψ.pd 1))]
    exact (ha.solenoidal ψ hψ).2

/-! ## 2. Smooth periodic slice weak derivatives and orbit slice `IsCylH1Datum` -/

lemma hasWeakCellDerivC_pdir {c : ℝ} (hc : 0 < c) (j : Fin 2)
    {F : B0579.Plane → CMerid} (hF : ContDiff ℝ ∞ F)
    (hFp : UnforcedLeray.Cyl.IsPeriodic c F)
    (hmF : MemLp F 2 (F8Sm.cellMeas c)) (hmdF : MemLp (F8Sm.pdir j F) 2 (F8Sm.cellMeas c))
    (k : Fin 2) :
    IIIa.HasWeakCellDerivC c j (fun y => F y k) (fun y => F8Sm.pdir j F y k) := by
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · let πk : CMerid →L[ℝ] ℂ := (EuclideanSpace.proj k : CMerid →L[ℂ] ℂ).restrictScalars ℝ
    exact ⟨F8Sm.integrableOn_cont_mul_cylTest hc (πk.continuous.comp hF.continuous) (hψ.pd j),
      F8Sm.integrableOn_cont_mul_cylTest hc
        (πk.continuous.comp (F8Sm.contDiff_pdir hF j).continuous) hψ⟩
  · let Ψk : B0579.Plane → CMerid := singleCylVec k ψ
    have hΨk_sm : ContDiff ℝ ∞ Ψk := by
      let ek : CMerid := WithLp.toLp 2 fun i : Fin 2 => if i = k then (1 : ℂ) else 0
      have hΨk_eq : Ψk = fun y => ψ y • ek := by
        funext y; ext i
        by_cases hik : i = k <;> simp [Ψk, singleCylVec, ek, hik, Complex.real_smul]
      rw [hΨk_eq]
      exact hψ.smooth.smul contDiff_const
    have hΨk_per : UnforcedLeray.Cyl.IsPeriodic c Ψk := fun y => by
      ext i
      by_cases hik : i = k
      · simp [Ψk, singleCylVec, hik, hψ.periodic y]
      · simp [Ψk, singleCylVec, hik]
    have hdΨk : F8Sm.pdir j Ψk = singleCylVec k (B0579.pd j ψ) := by
      funext y; ext i
      let πi : CMerid →L[ℝ] ℂ := (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ
      have hc1 := (πi.hasFDerivAt.comp y
        (hΨk_sm.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
      change πi (fderiv ℝ Ψk y (B0579.dir j)) = _
      rw [← ContinuousLinearMap.comp_apply, ← hc1]
      by_cases hik : i = k
      · subst hik
        have hfn : πi ∘ Ψk = fun z => (ψ z : ℂ) := by funext z; simp [πi, Ψk, singleCylVec]
        rw [hfn]
        have hc2 := (Complex.ofRealCLM.hasFDerivAt.comp y (hψ.differentiable y).hasFDerivAt).fderiv
        change fderiv ℝ (Complex.ofRealCLM ∘ ψ) y (B0579.dir j) = _
        rw [hc2, ContinuousLinearMap.comp_apply]
        simp [singleCylVec, B0579.pd]
      · have hfn : πi ∘ Ψk = fun _ => (0 : ℂ) := by funext z; simp [πi, Ψk, singleCylVec, hik]
        rw [hfn]
        simp [singleCylVec, hik]
    have hmΨ : MemLp Ψk 2 (F8Sm.cellMeas c) := memLp_singleCylVec hc k hψ
    have hmdΨ : MemLp (F8Sm.pdir j Ψk) 2 (F8Sm.cellMeas c) := by
      rw [hdΨk]; exact memLp_singleCylVec hc k (hψ.pd j)
    let conjMerid : CMerid → CMerid := fun v => WithLp.toLp 2 fun i => starRingEnd ℂ (v i)
    have hconj_sm : ContDiff ℝ ∞ (conjMerid ∘ F) := by
      refine ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℂ)).comp_contDiff_iff).1
        (contDiff_pi.2 fun i => ?_)
      let πi : CMerid →L[ℝ] ℂ := (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ
      exact Complex.conjCLE.toContinuousLinearMap.contDiff.comp (πi.contDiff.comp hF)
    have hconj_per : UnforcedLeray.Cyl.IsPeriodic c (conjMerid ∘ F) := fun y => by
      simp [Function.comp, hFp y]
    have hconj_d : F8Sm.pdir j (conjMerid ∘ F) = conjMerid ∘ F8Sm.pdir j F := by
      funext y; ext i
      let πi : CMerid →L[ℝ] ℂ := (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ
      let cj : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap
      have hc1 := (πi.hasFDerivAt.comp y
        (hconj_sm.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
      change πi (fderiv ℝ (conjMerid ∘ F) y (B0579.dir j)) =
        cj (πi (fderiv ℝ F y (B0579.dir j)))
      rw [← ContinuousLinearMap.comp_apply, ← hc1]
      have hfn : πi ∘ (conjMerid ∘ F) = cj ∘ (πi ∘ F) := by funext z; rfl
      rw [hfn]
      have hc2 := ((cj.comp πi).hasFDerivAt.comp y
        (hF.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
      change fderiv ℝ ((cj.comp πi) ∘ F) y (B0579.dir j) = _
      rw [hc2]
      rfl
    have hm_cF : MemLp (conjMerid ∘ F) 2 (F8Sm.cellMeas c) := by
      refine ⟨hconj_sm.continuous.aestronglyMeasurable, ?_⟩
      have heq : eLpNorm (conjMerid ∘ F) 2 (F8Sm.cellMeas c) = eLpNorm F 2 (F8Sm.cellMeas c) :=
        eLpNorm_congr_norm_ae (Eventually.of_forall fun y => by
          simp [conjMerid, PiLp.norm_eq_of_L2])
      rw [heq]; exact hmF.2
    have hmd_cF : MemLp (F8Sm.pdir j (conjMerid ∘ F)) 2 (F8Sm.cellMeas c) := by
      have hcs : Continuous (F8Sm.pdir j (conjMerid ∘ F)) :=
        (F8Sm.contDiff_pdir hconj_sm j).continuous
      refine ⟨hcs.aestronglyMeasurable, ?_⟩
      rw [hconj_d]
      have heq : eLpNorm (conjMerid ∘ F8Sm.pdir j F) 2 (F8Sm.cellMeas c) =
          eLpNorm (F8Sm.pdir j F) 2 (F8Sm.cellMeas c) :=
        eLpNorm_congr_norm_ae (Eventually.of_forall fun y => by
          simp [conjMerid, PiLp.norm_eq_of_L2])
      rw [heq]; exact hmdF.2
    have hibp := F8Sm.cell_ibp_pdir hc j hconj_sm hΨk_sm hconj_per hΨk_per hm_cF hmd_cF hmΨ hmdΨ
    rw [hconj_d, hdΨk] at hibp
    have eL : (fun y : B0579.Plane => (inner ℂ ((conjMerid ∘ F8Sm.pdir j F) y) (Ψk y) : ℂ)) =
        fun y => F8Sm.pdir j F y k * (ψ y : ℂ) := by
      funext y
      rw [PiLp.inner_apply, Fin.sum_univ_two]
      fin_cases k <;> simp [Ψk, singleCylVec, conjMerid, RCLike.inner_apply, mul_comm]
    have eR : (fun y : B0579.Plane =>
          (inner ℂ ((conjMerid ∘ F) y) (singleCylVec k (B0579.pd j ψ) y) : ℂ)) =
        fun y => F y k * (B0579.pd j ψ y : ℂ) := by
      funext y
      rw [PiLp.inner_apply, Fin.sum_univ_two]
      fin_cases k <;> simp [singleCylVec, conjMerid, RCLike.inner_apply, mul_comm]
    rw [eL, eR] at hibp
    rw [← neg_inj, neg_neg]
    exact hibp.symm

lemma orbit_slice_isCylH1Datum {p : Params} (hc : 0 < p.c) {σ : ℝ} {W : CProf}
    {u uq uη : B0579.Plane → CMerid} (hW : F8U.IsCylOseenOrbit p σ W u uq uη)
    {t : ℝ} (ht : t ∈ Ioo σ (σ + 2)) :
    F8U.IsCylH1Datum p.c (F8U.slice W t) (F8U.slice (F8U.pd 0 W) t)
      (F8U.slice (F8U.pd 1 W) t) := by
  have hsm : ContDiff ℝ ∞ (F8U.slice W t) := F8Sm.contDiff_slice hW.smooth ht
  have hper : UnforcedLeray.Cyl.IsPeriodic p.c (F8U.slice W t) := fun y =>
    hW.periodic (t, y) ht
  have hm0 : MemLp (F8U.slice W t) 2 (F8Sm.cellMeas p.c) :=
    hW.memL2 t ht 0 (by decide) ![]
  have hm10 : MemLp (F8U.slice (F8U.pd 0 W) t) 2 (F8Sm.cellMeas p.c) :=
    hW.memL2 t ht 1 (by decide) ![0]
  have hm11 : MemLp (F8U.slice (F8U.pd 1 W) t) 2 (F8Sm.cellMeas p.c) :=
    hW.memL2 t ht 1 (by decide) ![1]
  have hp0 : F8Sm.pdir 0 (F8U.slice W t) = F8U.slice (F8U.pd 0 W) t :=
    F8Sm.pdir_slice_eq hW.smooth ht 0
  have hp1 : F8Sm.pdir 1 (F8U.slice W t) = F8U.slice (F8U.pd 1 W) t :=
    F8Sm.pdir_slice_eq hW.smooth ht 1
  refine ⟨fun k => hp0 ▸ hasWeakCellDerivC_pdir hc 0 hsm hper hm0 (hp0.symm ▸ hm10) k,
    fun k => hp1 ▸ hasWeakCellDerivC_pdir hc 1 hsm hper hm0 (hp1.symm ▸ hm11) k,
    F8Sm.isCellSolenoidal_of_div_free hc hsm hper fun y => ?_,
    ⟨hm0, hm10, hm11⟩⟩
  rw [hp0, hp1]
  exact hW.div_free (t, y) ht

lemma orbit_pd_hasWeakCellDerivC {p : Params} (hc : 0 < p.c) {σ : ℝ} {W : CProf}
    {u uq uη : B0579.Plane → CMerid} (hW : F8U.IsCylOseenOrbit p σ W u uq uη)
    {t : ℝ} (ht : t ∈ Ioo σ (σ + 2)) (i j k : Fin 2) :
    IIIa.HasWeakCellDerivC p.c j (fun y => F8U.pd i W (t, y) k)
      (fun y => F8U.pd i (F8U.pd j W) (t, y) k) := by
  have hpd_sm : ContDiffOn ℝ ∞ (F8U.pd i W) (F8Sm.stripSet σ) :=
    F8Sm.contDiffOn_pd hW.smooth i
  have hsm : ContDiff ℝ ∞ (F8U.slice (F8U.pd i W) t) := F8Sm.contDiff_slice hpd_sm ht
  have hper : UnforcedLeray.Cyl.IsPeriodic p.c (F8U.slice (F8U.pd i W) t) := fun y =>
    F8Sm.periodic_fderiv_dir hW.periodic (F8U.sdir i) (t, y) ht
  have hm1 : MemLp (F8U.slice (F8U.pd i W) t) 2 (F8Sm.cellMeas p.c) :=
    hW.memL2 t ht 1 (by decide) ![i]
  have hm2ji : MemLp (F8U.slice (F8U.pd j (F8U.pd i W)) t) 2 (F8Sm.cellMeas p.c) :=
    hW.memL2 t ht 2 (by decide) ![j, i]
  have hpj : F8Sm.pdir j (F8U.slice (F8U.pd i W) t) = F8U.slice (F8U.pd j (F8U.pd i W)) t :=
    F8Sm.pdir_slice_eq hpd_sm ht j
  have hwk := hasWeakCellDerivC_pdir hc j hsm hper hm1 (hpj.symm ▸ hm2ji) k
  rw [hpj] at hwk
  change IIIa.HasWeakCellDerivC p.c j (fun y => F8U.pd i W (t, y) k)
    (fun y => F8U.pd j (F8U.pd i W) (t, y) k) at hwk
  have hcomm : (fun y => F8U.pd j (F8U.pd i W) (t, y) k) =
      (fun y => F8U.pd i (F8U.pd j W) (t, y) k) := by
    funext y
    rw [F8Sm.pd_comm hW.smooth (F8Sm.mem_stripSet ht y) j i]
  rwa [hcomm] at hwk

/-! ## 3. Train slice `L²` bounds, linearity of `IsCylOseenOrbit`, and classical uniqueness -/

/-- Uniform spatial `C^1` bound for `p.train.v` on `[0, T]` (`0 ≤ T`). -/
lemma uniform_train_C1 {dm dp : ℝ} {p : Params} {d : ℝ} (hreg : BgRegime p d dm dp)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ s ∈ Icc (0 : ℝ) T, ContDiff ℝ ∞ (p.train.v s)) ∧
      (∀ s ∈ Icc (0 : ℝ) T, UnforcedLeray.Cyl.IsPeriodic p.c (p.train.v s)) ∧
      (∀ s ∈ Icc (0 : ℝ) T, ∀ k : Fin 2, ∀ y : B0579.Plane, |p.train.v s y k| ≤ M) ∧
      (∀ s ∈ Icc (0 : ℝ) T, ∀ j k : Fin 2, ∀ y : B0579.Plane,
        |fderiv ℝ (fun z => p.train.v s z k) y (B0579.dir j)| ≤ M) := by
  obtain ⟨M0, hM0⟩ := hreg.train_buc.deriv_bound (hS := hT) 0
  obtain ⟨M1, hM1⟩ := hreg.train_buc.deriv_bound (hS := hT) 1
  let M : ℝ := max 0 (max M0 M1)
  have hM_nn : 0 ≤ M := le_max_left _ _
  have hsm_fn : ∀ s ∈ Icc (0 : ℝ) T, ContDiff ℝ ∞ (p.train.v s) := by
    intro s hs
    have hc := p.train.isTrain.smooth_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (s := univ) (fun y _ => ⟨mem_Ici.2 hs.1, mem_univ y⟩)
    exact contDiffOn_univ.1 hc
  refine ⟨M, hM_nn, hsm_fn,
    fun s hs => p.train.isTrain.periodic_v s hs.1,
    fun s hs k y => ?_,
    fun s hs j k y => ?_⟩
  · calc |p.train.v s y k| = ‖p.train.v s y k‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖p.train.v s y‖ := PiLp.norm_apply_le (p.train.v s y) k
      _ = ‖iteratedFDeriv ℝ 0 (p.train.v s) y‖ := (norm_iteratedFDeriv_zero).symm
      _ ≤ M0 := hM0 s hs y
      _ ≤ M := (le_max_left M0 M1).trans (le_max_right _ _)
  · have hVs := hsm_fn s hs
    let πk : UnforcedLeray.Train.Vec →L[ℝ] ℝ := EuclideanSpace.proj k
    have hc := (πk.hasFDerivAt.comp y (hVs.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
    have hproj : fderiv ℝ (fun z => p.train.v s z k) y (B0579.dir j) =
        fderiv ℝ (p.train.v s) y (B0579.dir j) k := by
      change fderiv ℝ (πk ∘ p.train.v s) y (B0579.dir j) = _
      rw [hc, ContinuousLinearMap.comp_apply]; rfl
    rw [hproj]
    calc |fderiv ℝ (p.train.v s) y (B0579.dir j) k|
        = ‖fderiv ℝ (p.train.v s) y (B0579.dir j) k‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (p.train.v s) y (B0579.dir j)‖ := PiLp.norm_apply_le _ k
      _ = ‖iteratedFDeriv ℝ 1 (p.train.v s) y ![B0579.dir j]‖ := by
          rw [iteratedFDeriv_one_apply, Matrix.cons_val_zero]
      _ ≤ ‖iteratedFDeriv ℝ 1 (p.train.v s) y‖ *
          ∏ l : Fin 1, ‖(![B0579.dir j] : Fin 1 → B0579.Plane) l‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ 1 (p.train.v s) y‖ := by simp [F8Sm.norm_b0579_dir]
      _ ≤ M1 := hM1 s hs y
      _ ≤ M := (le_max_right M0 M1).trans (le_max_right _ _)

/-- Slice convective-stretching operator on triples `(u, uq, uη)`. -/
def bvTripleSlice (V : B0579.Plane → UnforcedLeray.Train.Vec)
    (u uq uη : B0579.Plane → CMerid) (y : B0579.Plane) : CMerid :=
  WithLp.toLp 2 fun i : Fin 2 =>
    ((V y 0 : ℝ) : ℂ) * uq y i + ((V y 1 : ℝ) : ℂ) * uη y i +
      u y 0 * ((fderiv ℝ (fun z => V z i) y ((1 : ℝ), (0 : ℝ)) : ℝ) : ℂ) +
      u y 1 * ((fderiv ℝ (fun z => V z i) y ((0 : ℝ), (1 : ℝ)) : ℝ) : ℂ)

lemma flatBv_eq_bvTripleSlice {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (w wq wη : CProf) (s : ℝ) :
    (fun y => flatBv tr w wq wη (s, y)) =
      bvTripleSlice (tr.v s) (F8U.slice w s) (F8U.slice wq s) (F8U.slice wη s) :=
  rfl

lemma memLp_and_cellL2_bvTripleSlice {c M : ℝ} (hM : 0 ≤ M)
    {V : B0579.Plane → UnforcedLeray.Train.Vec} (hV : ContDiff ℝ ∞ V)
    (hb0 : ∀ k : Fin 2, ∀ y : B0579.Plane, |V y k| ≤ M)
    (hb1 : ∀ j k : Fin 2, ∀ y : B0579.Plane,
      |fderiv ℝ (fun z => V z k) y (B0579.dir j)| ≤ M)
    {u uq uη : B0579.Plane → CMerid}
    (hu : MemLp u 2 (F8Sm.cellMeas c))
    (huq : MemLp uq 2 (F8Sm.cellMeas c))
    (huη : MemLp uη 2 (F8Sm.cellMeas c)) :
    MemLp (bvTripleSlice V u uq uη) 2 (F8Sm.cellMeas c) ∧
      (F8U.cellL2 c (bvTripleSlice V u uq uη)).toReal ≤
        M * (F8U.cellL2 c uq).toReal + M * (F8U.cellL2 c uη).toReal +
          4 * M * (F8U.cellL2 c u).toReal := by
  let mulR (a : B0579.Plane → ℝ) (G : B0579.Plane → CMerid) : B0579.Plane → CMerid :=
    fun y => a y • G y
  have hmul : ∀ {a : B0579.Plane → ℝ} {G : B0579.Plane → CMerid},
      Continuous a → (∀ y, |a y| ≤ M) → MemLp G 2 (F8Sm.cellMeas c) →
      MemLp (mulR a G) 2 (F8Sm.cellMeas c) ∧
        (F8U.cellL2 c (mulR a G)).toReal ≤ M * (F8U.cellL2 c G).toReal := by
    intro a G ha hbd hG
    have ha_sm : AEStronglyMeasurable a (F8Sm.cellMeas c) := ha.aestronglyMeasurable
    have hm : MemLp (mulR a G) 2 (F8Sm.cellMeas c) := by
      refine ⟨ha_sm.smul hG.aestronglyMeasurable, ?_⟩
      calc eLpNorm (mulR a G) 2 (F8Sm.cellMeas c)
          ≤ eLpNorm (M • G) 2 (F8Sm.cellMeas c) := eLpNorm_mono fun y => by
            simp only [mulR, Pi.smul_apply, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg hM]
            exact mul_le_mul_of_nonneg_right (hbd y) (norm_nonneg _)
        _ = ‖M‖ₑ * eLpNorm G 2 (F8Sm.cellMeas c) := eLpNorm_const_smul M G 2 _
        _ < ⊤ := ENNReal.mul_lt_top enorm_lt_top hG.2
    refine ⟨hm, ?_⟩
    have hle : F8U.cellL2 c (mulR a G) ≤ ENNReal.ofReal M * F8U.cellL2 c G := by
      calc F8U.cellL2 c (mulR a G)
          ≤ eLpNorm (M • G) 2 (F8Sm.cellMeas c) := eLpNorm_mono fun y => by
            simp only [mulR, Pi.smul_apply, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg hM]
            exact mul_le_mul_of_nonneg_right (hbd y) (norm_nonneg _)
        _ = ‖M‖ₑ * F8U.cellL2 c G := eLpNorm_const_smul M G 2 _
        _ = ENNReal.ofReal M * F8U.cellL2 c G := by rw [← ofReal_norm, Real.norm_of_nonneg hM]
    have htr := (ENNReal.toReal_le_toReal hm.eLpNorm_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG.eLpNorm_ne_top)).2 hle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM] at htr
  have hcv : ∀ k : Fin 2, Continuous (fun y => V y k) :=
    fun k => (EuclideanSpace.proj k : UnforcedLeray.Train.Vec →L[ℝ] ℝ).continuous.comp hV.continuous
  have hcdv : ∀ j k : Fin 2, Continuous (fun y => fderiv ℝ (fun z => V z k) y (B0579.dir j)) := by
    intro j k
    have hc_vk : ContDiff ℝ ∞ (fun z => V z k) :=
      (EuclideanSpace.proj k : UnforcedLeray.Train.Vec →L[ℝ] ℝ).contDiff.comp hV
    exact (((contDiff_infty_iff_fderiv.1 hc_vk).2).clm_apply contDiff_const).continuous
  obtain ⟨mt0, bt0⟩ := hmul (hcv 0) (hb0 0) huq
  obtain ⟨mt1, bt1⟩ := hmul (hcv 1) (hb0 1) huη
  have hs_term : ∀ m k : Fin 2,
      MemLp (mulR (fun y => fderiv ℝ (fun z => V z k) y (B0579.dir m))
        (fun y => F8Sm.compCLM m k (u y))) 2 (F8Sm.cellMeas c) ∧
      (F8U.cellL2 c (mulR (fun y => fderiv ℝ (fun z => V z k) y (B0579.dir m))
        (fun y => F8Sm.compCLM m k (u y)))).toReal ≤ M * (F8U.cellL2 c u).toReal := by
    intro m k
    obtain ⟨mm, bm⟩ := hmul (hcdv m k) (hb1 m k) (F8Sm.memLp_compCLM hu m k)
    exact ⟨mm, bm.trans (mul_le_mul_of_nonneg_left (F8Sm.cellL2_compCLM_le hu m k) hM)⟩
  have htri : ∀ {A B : B0579.Plane → CMerid},
      MemLp A 2 (F8Sm.cellMeas c) → MemLp B 2 (F8Sm.cellMeas c) →
      (F8U.cellL2 c (fun y => A y + B y)).toReal ≤
        (F8U.cellL2 c A).toReal + (F8U.cellL2 c B).toReal := by
    intro A B hmA hmB
    have hle : F8U.cellL2 c (fun y => A y + B y) ≤ F8U.cellL2 c A + F8U.cellL2 c B :=
      eLpNorm_add_le hmA.aestronglyMeasurable hmB.aestronglyMeasurable one_le_two
    have htr := (ENNReal.toReal_le_toReal (hmA.add hmB).eLpNorm_ne_top
      (ENNReal.add_ne_top.2 ⟨hmA.eLpNorm_ne_top, hmB.eLpNorm_ne_top⟩)).2 hle
    rwa [ENNReal.toReal_add hmA.eLpNorm_ne_top hmB.eLpNorm_ne_top] at htr
  let S00 := mulR (fun y => fderiv ℝ (fun z => V z 0) y (B0579.dir 0))
    (fun y => F8Sm.compCLM 0 0 (u y))
  let S01 := mulR (fun y => fderiv ℝ (fun z => V z 1) y (B0579.dir 0))
    (fun y => F8Sm.compCLM 0 1 (u y))
  let S10 := mulR (fun y => fderiv ℝ (fun z => V z 0) y (B0579.dir 1))
    (fun y => F8Sm.compCLM 1 0 (u y))
  let S11 := mulR (fun y => fderiv ℝ (fun z => V z 1) y (B0579.dir 1))
    (fun y => F8Sm.compCLM 1 1 (u y))
  have hm_tr : MemLp (fun y => mulR (fun z => V z 0) uq y + mulR (fun z => V z 1) uη y)
      2 (F8Sm.cellMeas c) := mt0.add mt1
  have hm_s0 : MemLp (fun y => S00 y + S01 y) 2 (F8Sm.cellMeas c) :=
    (hs_term 0 0).1.add (hs_term 0 1).1
  have hm_s1 : MemLp (fun y => S10 y + S11 y) 2 (F8Sm.cellMeas c) :=
    (hs_term 1 0).1.add (hs_term 1 1).1
  have hm_s : MemLp (fun y => (S00 y + S01 y) + (S10 y + S11 y)) 2 (F8Sm.cellMeas c) :=
    hm_s0.add hm_s1
  have heq : bvTripleSlice V u uq uη =
      fun y => (mulR (fun z => V z 0) uq y + mulR (fun z => V z 1) uη y) +
        ((S00 y + S01 y) + (S10 y + S11 y)) := by
    funext y; ext i
    dsimp [bvTripleSlice, mulR, S00, S01, S10, S11]
    fin_cases i <;> simp [B0579.dir] <;> ring
  rw [heq]
  refine ⟨hm_tr.add hm_s, ?_⟩
  have t1 := htri hm_tr hm_s
  have t2 := htri mt0 mt1
  have t3 := htri hm_s0 hm_s1
  have t4 := htri (hs_term 0 0).1 (hs_term 0 1).1
  have t5 := htri (hs_term 1 0).1 (hs_term 1 1).1
  linarith [bt0, bt1, (hs_term 0 0).2, (hs_term 0 1).2, (hs_term 1 0).2, (hs_term 1 1).2]

lemma pdIter_comb_on_strip {σ : ℝ} {w₁ w₂ : CProf}
    (hw₁ : ContDiffOn ℝ ∞ w₁ (F8Sm.stripSet σ))
    (hw₂ : ContDiffOn ℝ ∞ w₂ (F8Sm.stripSet σ)) (a b : ℝ) :
    ∀ {n : ℕ} (α : Fin n → Fin 2) {x : Coord}, x ∈ F8Sm.stripSet σ →
      F8U.pdIter α (fun z => a • w₁ z + b • w₂ z) x =
        a • F8U.pdIter α w₁ x + b • F8U.pdIter α w₂ x
  | 0, _, _, _ => rfl
  | _ + 1, α, x, hx => by
    have ih_ev : F8U.pdIter (Fin.tail α) (fun z => a • w₁ z + b • w₂ z) =ᶠ[𝓝 x]
        fun z => a • F8U.pdIter (Fin.tail α) w₁ z + b • F8U.pdIter (Fin.tail α) w₂ z := by
      filter_upwards [(F8Sm.isOpen_stripSet σ).mem_nhds hx] with z hz
      exact pdIter_comb_on_strip hw₁ hw₂ a b (Fin.tail α) hz
    have hd₁ : DifferentiableAt ℝ (F8U.pdIter (Fin.tail α) w₁) x :=
      ((F8Sm.contDiffOn_pdIter hw₁ (Fin.tail α)).contDiffAt
        ((F8Sm.isOpen_stripSet σ).mem_nhds hx)).differentiableAt (by simp)
    have hd₂ : DifferentiableAt ℝ (F8U.pdIter (Fin.tail α) w₂) x :=
      ((F8Sm.contDiffOn_pdIter hw₂ (Fin.tail α)).contDiffAt
        ((F8Sm.isOpen_stripSet σ).mem_nhds hx)).differentiableAt (by simp)
    change fderiv ℝ (F8U.pdIter (Fin.tail α) (fun z => a • w₁ z + b • w₂ z)) x (F8U.sdir (α 0)) = _
    rw [ih_ev.fderiv_eq]
    have hcomb := ((hd₁.hasFDerivAt.const_smul a).add (hd₂.hasFDerivAt.const_smul b)).fderiv
    change fderiv ℝ (a • F8U.pdIter (Fin.tail α) w₁ + b • F8U.pdIter (Fin.tail α) w₂) x
        (F8U.sdir (α 0)) = _
    rw [hcomb]
    simp [F8U.pdIter, F8U.pd]

lemma ps_pdIter_comb_on_strip {σ : ℝ} {w₁ w₂ : CProf}
    (hw₁ : ContDiffOn ℝ ∞ w₁ (F8Sm.stripSet σ))
    (hw₂ : ContDiffOn ℝ ∞ w₂ (F8Sm.stripSet σ)) (a b : ℝ)
    {n : ℕ} (α : Fin n → Fin 2) {x : Coord} (hx : x ∈ F8Sm.stripSet σ) :
    F8U.ps (F8U.pdIter α (fun z => a • w₁ z + b • w₂ z)) x =
      a • F8U.ps (F8U.pdIter α w₁) x + b • F8U.ps (F8U.pdIter α w₂) x := by
  have ih_ev : F8U.pdIter α (fun z => a • w₁ z + b • w₂ z) =ᶠ[𝓝 x]
      fun z => a • F8U.pdIter α w₁ z + b • F8U.pdIter α w₂ z := by
    filter_upwards [(F8Sm.isOpen_stripSet σ).mem_nhds hx] with z hz
    exact pdIter_comb_on_strip hw₁ hw₂ a b α hz
  have hd₁ : DifferentiableAt ℝ (F8U.pdIter α w₁) x :=
    ((F8Sm.contDiffOn_pdIter hw₁ α).contDiffAt
      ((F8Sm.isOpen_stripSet σ).mem_nhds hx)).differentiableAt (by simp)
  have hd₂ : DifferentiableAt ℝ (F8U.pdIter α w₂) x :=
    ((F8Sm.contDiffOn_pdIter hw₂ α).contDiffAt
      ((F8Sm.isOpen_stripSet σ).mem_nhds hx)).differentiableAt (by simp)
  unfold F8U.ps
  rw [ih_ev.fderiv_eq]
  have hcomb := ((hd₁.hasFDerivAt.const_smul a).add (hd₂.hasFDerivAt.const_smul b)).fderiv
  change fderiv ℝ (a • F8U.pdIter α w₁ + b • F8U.pdIter α w₂) x (1, (0, 0)) = _
  rw [hcomb]
  simp

lemma isCylOseenOrbit_congr_datum {p : Params} {σ : ℝ} {W : CProf}
    {u uq uη u' uq' uη' : B0579.Plane → CMerid}
    (hu : u =ᵐ[F8Sm.cellMeas p.c] u') (huq : uq =ᵐ[F8Sm.cellMeas p.c] uq')
    (huη : uη =ᵐ[F8Sm.cellMeas p.c] uη')
    (hW : F8U.IsCylOseenOrbit p σ W u uq uη) :
    F8U.IsCylOseenOrbit p σ W u' uq' uη' := by
  refine ⟨hW.smooth, hW.periodic, hW.div_free, hW.memL2, hW.memL2_s, hW.cont, hW.cont_s,
    hW.projected, ?_⟩
  refine hW.initial.congr fun t => ?_
  unfold F8U.cylH1 F8U.cellL2
  have e0 : eLpNorm (fun y => W (t, y) - u y) 2 (F8Sm.cellMeas p.c) =
      eLpNorm (fun y => W (t, y) - u' y) 2 (F8Sm.cellMeas p.c) :=
    eLpNorm_congr_ae (hu.mono fun y hy => by dsimp only; rw [hy])
  have e1 : eLpNorm (fun y => F8U.pd 0 W (t, y) - uq y) 2 (F8Sm.cellMeas p.c) =
      eLpNorm (fun y => F8U.pd 0 W (t, y) - uq' y) 2 (F8Sm.cellMeas p.c) :=
    eLpNorm_congr_ae (huq.mono fun y hy => by dsimp only; rw [hy])
  have e2 : eLpNorm (fun y => F8U.pd 1 W (t, y) - uη y) 2 (F8Sm.cellMeas p.c) =
      eLpNorm (fun y => F8U.pd 1 W (t, y) - uη' y) 2 (F8Sm.cellMeas p.c) :=
    eLpNorm_congr_ae (huη.mono fun y hy => by dsimp only; rw [hy])
  rw [e0, e1, e2]

private lemma pd_zero_prof (i : Fin 2) : F8U.pd i (0 : CProf) = 0 := by
  funext z; change fderiv ℝ (fun _ : Coord => (0 : CMerid)) z (F8U.sdir i) = 0; simp

private lemma ps_zero_prof : F8U.ps (0 : CProf) = 0 := by
  funext z; change fderiv ℝ (fun _ : Coord => (0 : CMerid)) z (1, (0, 0)) = 0; simp

private lemma pdIter_zero_prof : ∀ {n : ℕ} (α : Fin n → Fin 2), F8U.pdIter α (0 : CProf) = 0
  | 0, _ => rfl
  | _ + 1, α => by rw [F8U.pdIter, pdIter_zero_prof (Fin.tail α), pd_zero_prof]

lemma isCylOseenOrbit_zero (p : Params) (σ : ℝ) :
    F8U.IsCylOseenOrbit p σ 0 0 0 0 where
  smooth := contDiffOn_const
  periodic _ _ := rfl
  div_free x _ := by rw [pd_zero_prof, pd_zero_prof]; simp
  memL2 τ _ _ _ α := by
    rw [pdIter_zero_prof]; exact MemLp.zero
  memL2_s τ _ _ _ α := by
    rw [pdIter_zero_prof, ps_zero_prof]; exact MemLp.zero
  cont τ _ _ _ α := by
    rw [pdIter_zero_prof]; simp [F8U.cellL2]
  cont_s τ _ _ _ α := by
    rw [pdIter_zero_prof, ps_zero_prof]; simp [F8U.cellL2]
  projected τ _ φ _ _ := by
    have hz : ∀ y, F8U.homResidual p 0 (τ, y) = 0 := fun y => by
      simp only [F8U.homResidual, ps_zero_prof, pd_zero_prof, flatBv]
      ext i; simp
    simp [hz]
  initial := by
    rw [pd_zero_prof, pd_zero_prof]
    simp [F8U.cylH1, F8U.cellL2]

lemma isCylOseenOrbit_comb {dm dp : ℝ} {p : Params} {d : ℝ} (hreg : BgRegime p d dm dp)
    {σ : ℝ} (hσ : 0 ≤ σ) {w₁ w₂ : CProf}
    {u₁ uq₁ uη₁ u₂ uq₂ uη₂ : B0579.Plane → CMerid}
    (hu₁ : F8U.IsCylH1Datum p.c u₁ uq₁ uη₁)
    (hu₂ : F8U.IsCylH1Datum p.c u₂ uq₂ uη₂)
    (h₁ : F8U.IsCylOseenOrbit p σ w₁ u₁ uq₁ uη₁)
    (h₂ : F8U.IsCylOseenOrbit p σ w₂ u₂ uq₂ uη₂) (a b : ℝ) :
    F8U.IsCylOseenOrbit p σ (fun x => a • w₁ x + b • w₂ x)
      (fun y => a • u₁ y + b • u₂ y) (fun y => a • uq₁ y + b • uq₂ y)
      (fun y => a • uη₁ y + b • uη₂ y) := by
  let w : CProf := fun x => a • w₁ x + b • w₂ x
  obtain ⟨M, hM, hV_sm, _, hb0, hb1⟩ := uniform_train_C1 hreg (T := σ + 2) (by linarith)
  have hpd1 : ∀ i : Fin 2, ∀ x ∈ F8Sm.stripSet σ,
      F8U.pd i w x = a • F8U.pd i w₁ x + b • F8U.pd i w₂ x :=
    fun i x hx => pdIter_comb_on_strip h₁.smooth h₂.smooth a b ![i] hx
  have hpd2 : ∀ i j : Fin 2, ∀ x ∈ F8Sm.stripSet σ,
      F8U.pd i (F8U.pd j w) x = a • F8U.pd i (F8U.pd j w₁) x + b • F8U.pd i (F8U.pd j w₂) x :=
    fun i j x hx => pdIter_comb_on_strip h₁.smooth h₂.smooth a b ![i, j] hx
  refine ⟨(h₁.smooth.const_smul a).add (h₂.smooth.const_smul b),
    fun x hx => by simp only [h₁.periodic x hx, h₂.periodic x hx],
    fun x hx => ?_,
    fun τ hτ n hn α => ?_,
    fun τ hτ n hn α => ?_,
    fun τ hτ n hn α => ?_,
    fun τ hτ n hn α => ?_,
    fun τ hτ φ hφ_L2 hφ_sol => ?_,
    ?_⟩
  · have hx' : x ∈ F8Sm.stripSet σ := ⟨hx, trivial⟩
    rw [hpd1 0 x hx', hpd1 1 x hx']
    simp only [PiLp.add_apply, PiLp.smul_apply, Complex.real_smul]
    calc (a : ℂ) * F8U.pd 0 w₁ x 0 + (b : ℂ) * F8U.pd 0 w₂ x 0 +
          ((a : ℂ) * F8U.pd 1 w₁ x 1 + (b : ℂ) * F8U.pd 1 w₂ x 1)
        = (a : ℂ) * (F8U.pd 0 w₁ x 0 + F8U.pd 1 w₁ x 1) +
            (b : ℂ) * (F8U.pd 0 w₂ x 0 + F8U.pd 1 w₂ x 1) := by ring
      _ = 0 := by rw [h₁.div_free x hx, h₂.div_free x hx]; simp
  · have heq : F8U.slice (F8U.pdIter α w) τ =
        fun y => a • F8U.slice (F8U.pdIter α w₁) τ y + b • F8U.slice (F8U.pdIter α w₂) τ y :=
      funext fun y => pdIter_comb_on_strip h₁.smooth h₂.smooth a b α ⟨hτ, trivial⟩
    rw [heq]
    exact ((h₁.memL2 τ hτ n hn α).const_smul a).add ((h₂.memL2 τ hτ n hn α).const_smul b)
  · have heq : F8U.slice (F8U.ps (F8U.pdIter α w)) τ =
        fun y => a • F8U.slice (F8U.ps (F8U.pdIter α w₁)) τ y +
          b • F8U.slice (F8U.ps (F8U.pdIter α w₂)) τ y :=
      funext fun y => ps_pdIter_comb_on_strip h₁.smooth h₂.smooth a b α ⟨hτ, trivial⟩
    rw [heq]
    exact ((h₁.memL2_s τ hτ n hn α).const_smul a).add ((h₂.memL2_s τ hτ n hn α).const_smul b)
  · have h_upper : Tendsto (fun t =>
        ‖a‖ₑ * F8U.cellL2 p.c (fun y => F8U.pdIter α w₁ (t, y) - F8U.pdIter α w₁ (τ, y)) +
        ‖b‖ₑ * F8U.cellL2 p.c (fun y => F8U.pdIter α w₂ (t, y) - F8U.pdIter α w₂ (τ, y)))
        (𝓝 τ) (𝓝 0) := by
      simpa using (ENNReal.Tendsto.const_mul (h₁.cont τ hτ n hn α) (Or.inr enorm_ne_top)).add
        (ENNReal.Tendsto.const_mul (h₂.cont τ hτ n hn α) (Or.inr enorm_ne_top))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [isOpen_Ioo.mem_nhds hτ] with t ht
    have hfn : (fun y => F8U.pdIter α w (t, y) - F8U.pdIter α w (τ, y)) =
        fun y => a • (F8U.pdIter α w₁ (t, y) - F8U.pdIter α w₁ (τ, y)) +
          b • (F8U.pdIter α w₂ (t, y) - F8U.pdIter α w₂ (τ, y)) := by
      funext y
      rw [pdIter_comb_on_strip h₁.smooth h₂.smooth a b α ⟨ht, trivial⟩,
        pdIter_comb_on_strip h₁.smooth h₂.smooth a b α ⟨hτ, trivial⟩]
      ext k; simp [Complex.real_smul]; ring
    unfold F8U.cellL2
    rw [hfn]
    have hm1 := ((h₁.memL2 t ht n hn α).sub (h₁.memL2 τ hτ n hn α)).const_smul a
    have hm2 := ((h₂.memL2 t ht n hn α).sub (h₂.memL2 τ hτ n hn α)).const_smul b
    refine (eLpNorm_add_le hm1.aestronglyMeasurable hm2.aestronglyMeasurable one_le_two).trans ?_
    rw [eLpNorm_const_smul a, eLpNorm_const_smul b]
    exact le_rfl
  · have h_upper : Tendsto (fun t =>
        ‖a‖ₑ * F8U.cellL2 p.c (fun y => F8U.ps (F8U.pdIter α w₁) (t, y) -
            F8U.ps (F8U.pdIter α w₁) (τ, y)) +
        ‖b‖ₑ * F8U.cellL2 p.c (fun y => F8U.ps (F8U.pdIter α w₂) (t, y) -
            F8U.ps (F8U.pdIter α w₂) (τ, y)))
        (𝓝 τ) (𝓝 0) := by
      simpa using (ENNReal.Tendsto.const_mul (h₁.cont_s τ hτ n hn α) (Or.inr enorm_ne_top)).add
        (ENNReal.Tendsto.const_mul (h₂.cont_s τ hτ n hn α) (Or.inr enorm_ne_top))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [isOpen_Ioo.mem_nhds hτ] with t ht
    have hfn : (fun y => F8U.ps (F8U.pdIter α w) (t, y) - F8U.ps (F8U.pdIter α w) (τ, y)) =
        fun y => a • (F8U.ps (F8U.pdIter α w₁) (t, y) - F8U.ps (F8U.pdIter α w₁) (τ, y)) +
          b • (F8U.ps (F8U.pdIter α w₂) (t, y) - F8U.ps (F8U.pdIter α w₂) (τ, y)) := by
      funext y
      rw [ps_pdIter_comb_on_strip h₁.smooth h₂.smooth a b α ⟨ht, trivial⟩,
        ps_pdIter_comb_on_strip h₁.smooth h₂.smooth a b α ⟨hτ, trivial⟩]
      ext k; simp [Complex.real_smul]; ring
    unfold F8U.cellL2
    rw [hfn]
    have hm1 := ((h₁.memL2_s t ht n hn α).sub (h₁.memL2_s τ hτ n hn α)).const_smul a
    have hm2 := ((h₂.memL2_s t ht n hn α).sub (h₂.memL2_s τ hτ n hn α)).const_smul b
    refine (eLpNorm_add_le hm1.aestronglyMeasurable hm2.aestronglyMeasurable one_le_two).trans ?_
    rw [eLpNorm_const_smul a, eLpNorm_const_smul b]
    exact le_rfl
  · have hτ_icc : τ ∈ Icc (0 : ℝ) (σ + 2) := ⟨by linarith [hτ.1], hτ.2.le⟩
    have hres_eq : ∀ y : B0579.Plane,
        F8U.homResidual p w (τ, y) =
          (a : ℂ) • F8U.homResidual p w₁ (τ, y) + (b : ℂ) • F8U.homResidual p w₂ (τ, y) := by
      intro y
      have hx : (τ, y) ∈ F8Sm.stripSet σ := ⟨hτ, trivial⟩
      have hps : F8U.ps w (τ, y) = a • F8U.ps w₁ (τ, y) + b • F8U.ps w₂ (τ, y) :=
        ps_pdIter_comb_on_strip h₁.smooth h₂.smooth a b ![] hx
      unfold F8U.homResidual
      rw [hps, hpd2 0 0 (τ, y) hx, hpd2 1 1 (τ, y) hx]
      ext i
      have hq0 := hpd1 0 (τ, y) hx
      have hq1 := hpd1 1 (τ, y) hx
      simp only [flatBv, hq0, hq1, w, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        Complex.real_smul, smul_eq_mul]
      ring
    have hmR : ∀ {W : CProf} {u uq uη}, F8U.IsCylOseenOrbit p σ W u uq uη →
        MemLp (fun y => F8U.homResidual p W (τ, y)) 2 (F8Sm.cellMeas p.c) := by
      intro W u uq uη hW
      have hm_ps := hW.memL2_s τ hτ 0 (by decide) ![]
      have hm_lap := ((hW.memL2 τ hτ 2 (by decide) ![0, 0]).add
        (hW.memL2 τ hτ 2 (by decide) ![1, 1])).const_smul p.ν
      have hm_bv := (memLp_and_cellL2_bvTripleSlice hM (hV_sm τ hτ_icc)
        (hb0 τ hτ_icc) (hb1 τ hτ_icc) (hW.memL2 τ hτ 0 (by decide) ![])
        (hW.memL2 τ hτ 1 (by decide) ![0]) (hW.memL2 τ hτ 1 (by decide) ![1])).1
      exact (hm_ps.sub hm_lap).add hm_bv
    have hi1 := F8Sm.integrableOn_inner_cell hφ_L2 (hmR h₁)
    have hi2 := F8Sm.integrableOn_inner_cell hφ_L2 (hmR h₂)
    have hpt : (fun y => inner ℂ (φ y) (F8U.homResidual p w (τ, y))) =
        fun y => (a : ℂ) * inner ℂ (φ y) (F8U.homResidual p w₁ (τ, y)) +
          (b : ℂ) * inner ℂ (φ y) (F8U.homResidual p w₂ (τ, y)) := by
      funext y
      rw [hres_eq y, inner_add_right, inner_smul_right, inner_smul_right]
    rw [hpt, integral_add (hi1.const_mul _) (hi2.const_mul _),
      integral_const_mul, integral_const_mul,
      h₁.projected τ hτ φ hφ_L2 hφ_sol, h₂.projected τ hτ φ hφ_L2 hφ_sol]
    simp
  · have h_upper : Tendsto (fun t =>
        ‖a‖ₑ * F8U.cylH1 p.c (fun y => w₁ (t, y) - u₁ y)
            (fun y => F8U.pd 0 w₁ (t, y) - uq₁ y) (fun y => F8U.pd 1 w₁ (t, y) - uη₁ y) +
        ‖b‖ₑ * F8U.cylH1 p.c (fun y => w₂ (t, y) - u₂ y)
            (fun y => F8U.pd 0 w₂ (t, y) - uq₂ y) (fun y => F8U.pd 1 w₂ (t, y) - uη₂ y))
        (𝓝[>] σ) (𝓝 0) := by
      simpa using (ENNReal.Tendsto.const_mul h₁.initial (Or.inr enorm_ne_top)).add
        (ENNReal.Tendsto.const_mul h₂.initial (Or.inr enorm_ne_top))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [Ioo_mem_nhdsGT (by linarith : σ < σ + 2)] with t ht
    have htri_comp : ∀ {f₁ g₁ f₂ g₂ : B0579.Plane → CMerid},
        AEStronglyMeasurable (fun y => f₁ y - g₁ y) (F8Sm.cellMeas p.c) →
        AEStronglyMeasurable (fun y => f₂ y - g₂ y) (F8Sm.cellMeas p.c) →
        F8U.cellL2 p.c (fun y => (a • f₁ y + b • f₂ y) - (a • g₁ y + b • g₂ y)) ≤
          ‖a‖ₑ * F8U.cellL2 p.c (fun y => f₁ y - g₁ y) +
          ‖b‖ₑ * F8U.cellL2 p.c (fun y => f₂ y - g₂ y) := by
      intro f₁ g₁ f₂ g₂ hm1 hm2
      have hfn : (fun y => (a • f₁ y + b • f₂ y) - (a • g₁ y + b • g₂ y)) =
          (a • fun y => f₁ y - g₁ y) + (b • fun y => f₂ y - g₂ y) := by
        funext y; ext k; simp [Complex.real_smul]; ring
      unfold F8U.cellL2
      rw [hfn]
      refine (eLpNorm_add_le (hm1.const_smul a) (hm2.const_smul b) one_le_two).trans ?_
      rw [eLpNorm_const_smul a, eLpNorm_const_smul b]
    have b0 := htri_comp ((h₁.memL2 t ht 0 (by decide) ![]).sub hu₁.memL2.1).aestronglyMeasurable
      ((h₂.memL2 t ht 0 (by decide) ![]).sub hu₂.memL2.1).aestronglyMeasurable
    have b1 := htri_comp ((h₁.memL2 t ht 1 (by decide) ![0]).sub hu₁.memL2.2.1).aestronglyMeasurable
      ((h₂.memL2 t ht 1 (by decide) ![0]).sub hu₂.memL2.2.1).aestronglyMeasurable
    have b2 := htri_comp ((h₁.memL2 t ht 1 (by decide) ![1]).sub hu₁.memL2.2.2).aestronglyMeasurable
      ((h₂.memL2 t ht 1 (by decide) ![1]).sub hu₂.memL2.2.2).aestronglyMeasurable
    dsimp only [F8U.slice, F8U.pdIter] at b0 b1 b2
    have e1 : (fun y => F8U.pd 0 w (t, y) - (a • uq₁ y + b • uq₂ y)) =
        fun y => (a • F8U.pd 0 w₁ (t, y) + b • F8U.pd 0 w₂ (t, y)) - (a • uq₁ y + b • uq₂ y) :=
      funext fun y => by rw [hpd1 0 (t, y) ⟨ht, trivial⟩]
    have e2 : (fun y => F8U.pd 1 w (t, y) - (a • uη₁ y + b • uη₂ y)) =
        fun y => (a • F8U.pd 1 w₁ (t, y) + b • F8U.pd 1 w₂ (t, y)) - (a • uη₁ y + b • uη₂ y) :=
      funext fun y => by rw [hpd1 1 (t, y) ⟨ht, trivial⟩]
    unfold F8U.cylH1
    rw [e1, e2]
    calc F8U.cellL2 p.c (fun y => (a • w₁ (t, y) + b • w₂ (t, y)) - (a • u₁ y + b • u₂ y)) +
          F8U.cellL2 p.c (fun y => (a • F8U.pd 0 w₁ (t, y) + b • F8U.pd 0 w₂ (t, y)) -
            (a • uq₁ y + b • uq₂ y)) +
          F8U.cellL2 p.c (fun y => (a • F8U.pd 1 w₁ (t, y) + b • F8U.pd 1 w₂ (t, y)) -
            (a • uη₁ y + b • uη₂ y))
        ≤ (‖a‖ₑ * F8U.cellL2 p.c (fun y => w₁ (t, y) - u₁ y) +
            ‖b‖ₑ * F8U.cellL2 p.c (fun y => w₂ (t, y) - u₂ y)) +
          (‖a‖ₑ * F8U.cellL2 p.c (fun y => F8U.pd 0 w₁ (t, y) - uq₁ y) +
            ‖b‖ₑ * F8U.cellL2 p.c (fun y => F8U.pd 0 w₂ (t, y) - uq₂ y)) +
          (‖a‖ₑ * F8U.cellL2 p.c (fun y => F8U.pd 1 w₁ (t, y) - uη₁ y) +
            ‖b‖ₑ * F8U.cellL2 p.c (fun y => F8U.pd 1 w₂ (t, y) - uη₂ y)) :=
          add_le_add (add_le_add b0 b1) b2
      _ = ‖a‖ₑ * (F8U.cellL2 p.c (fun y => w₁ (t, y) - u₁ y) +
            F8U.cellL2 p.c (fun y => F8U.pd 0 w₁ (t, y) - uq₁ y) +
            F8U.cellL2 p.c (fun y => F8U.pd 1 w₁ (t, y) - uη₁ y)) +
          ‖b‖ₑ * (F8U.cellL2 p.c (fun y => w₂ (t, y) - u₂ y) +
            F8U.cellL2 p.c (fun y => F8U.pd 0 w₂ (t, y) - uq₂ y) +
            F8U.cellL2 p.c (fun y => F8U.pd 1 w₂ (t, y) - uη₂ y)) := by
          ring

/-! ## 4. `L2Cell` time differentiability, classical uniqueness, Chapman–Kolmogorov, and `S0Val` -/

open Classical in
/-- `L2Cell c` slice path of a profile `f` on `Ioo τ T` (extended by `0` outside `Ioo τ T`). -/
def sliceLpOn {c τ T : ℝ} (f : CProf)
    (_hm : ∀ s ∈ Ioo τ T, MemLp (F8U.slice f s) 2 (F8Sm.cellMeas c)) (s : ℝ) : L2Cell c :=
  if s ∈ Ioo τ T then UnforcedLeray.BochnerTime.toPathLq 2 (F8Sm.cellMeas c) f s else 0

lemma sliceLpOn_of_mem {c τ T : ℝ} {f : CProf}
    (hm : ∀ s ∈ Ioo τ T, MemLp (F8U.slice f s) 2 (F8Sm.cellMeas c)) {s : ℝ} (hs : s ∈ Ioo τ T) :
    sliceLpOn f hm s = (hm s hs).toLp (F8U.slice f s) := by
  have hm' : MemLp (fun y => f (s, y)) 2 (F8Sm.cellMeas c) := hm s hs
  simp only [sliceLpOn, hs, ↓reduceIte]
  rw [UnforcedLeray.BochnerTime.toPathLq_of_memLp hm']
  rfl

/-- Rescaled difference-quotient convergence in `L²(cell)` on any open age interval `Ioo τ T`. -/
lemma tendsto_diffQuot_slice_L2_Ioo {c τ T s₀ : ℝ} {f : CProf}
    (hf : ContDiffOn ℝ ∞ f (Ioo τ T ×ˢ univ))
    (hfs_cont : Tendsto (fun t => F8U.cellL2 c (fun y => F8U.ps f (t, y) - F8U.ps f (s₀, y)))
      (𝓝 s₀) (𝓝 0))
    (hs₀ : s₀ ∈ Ioo τ T) :
    Tendsto (fun h : ℝ =>
      F8U.cellL2 c (fun y => h⁻¹ • (f (s₀ + h, y) - f (s₀, y)) - F8U.ps f (s₀, y)))
      (𝓝[≠] 0) (𝓝 0) := by
  have hτT : τ < T := hs₀.1.trans hs₀.2
  let lam : ℝ := (T - τ) / 2
  have hlam : 0 < lam := by dsimp [lam]; linarith
  let aff : Coord → Coord := fun x => (τ + lam * x.1, x.2)
  have haff_sm : ContDiff ℝ ∞ aff :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  have hmaps : MapsTo aff (F8Sm.stripSet 0) (Ioo τ T ×ˢ univ) := by
    intro x hx
    have hx1 : 0 < x.1 ∧ x.1 < 2 := by simpa using hx.1
    refine ⟨⟨by dsimp [aff, lam]; nlinarith, by dsimp [aff, lam]; nlinarith⟩, trivial⟩
  let g : CProf := f ∘ aff
  have hg_sm : ContDiffOn ℝ ∞ g (F8Sm.stripSet 0) := hf.comp haff_sm.contDiffOn hmaps
  have hps_g : ∀ u ∈ Ioo (0 : ℝ) 2, ∀ y : B0579.Plane,
      F8U.ps g (u, y) = lam • F8U.ps f (τ + lam * u, y) := by
    intro u hu y
    have hmem : aff (u, y) ∈ Ioo τ T ×ˢ univ := hmaps ⟨by simpa using hu, trivial⟩
    have hdf : DifferentiableAt ℝ f (aff (u, y)) :=
      (hf.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hmem)).differentiableAt (by simp)
    have hdaff : HasFDerivAt aff
        (((ContinuousLinearMap.fst ℝ ℝ B0579.Plane).smulRight (lam : ℝ)).prod
          (ContinuousLinearMap.snd ℝ ℝ B0579.Plane)) (u, y) := by
      have h1 : HasFDerivAt (fun x : Coord => τ + lam * x.1)
          ((ContinuousLinearMap.fst ℝ ℝ B0579.Plane).smulRight (lam : ℝ)) (u, y) := by
        simpa [mul_comm] using
          ((ContinuousLinearMap.fst ℝ ℝ B0579.Plane).hasFDerivAt.smul_const lam).const_add τ
      exact h1.prodMk (ContinuousLinearMap.snd ℝ ℝ B0579.Plane).hasFDerivAt
    have hcomp := (hdf.hasFDerivAt.comp (u, y) hdaff).fderiv
    unfold F8U.ps
    rw [hcomp, ContinuousLinearMap.comp_apply]
    have hvec : (((ContinuousLinearMap.fst ℝ ℝ B0579.Plane).smulRight (lam : ℝ)).prod
        (ContinuousLinearMap.snd ℝ ℝ B0579.Plane)) (1, (0, 0)) = lam • ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) := by
      ext <;> simp
    rw [hvec, map_smul]
  let u₀ : ℝ := (s₀ - τ) / lam
  have hu₀ : u₀ ∈ Ioo (0 : ℝ) 2 := by
    refine ⟨div_pos (sub_pos.2 hs₀.1) hlam, ?_⟩
    rw [div_lt_iff₀ hlam]
    dsimp [lam]; linarith [hs₀.2]
  have haff_u₀ : τ + lam * u₀ = s₀ := by
    dsimp [u₀]; rw [mul_div_cancel₀ _ hlam.ne']; ring
  have hg_cont : Tendsto (fun u => F8U.cellL2 c (fun y => F8U.ps g (u, y) - F8U.ps g (u₀, y)))
      (𝓝 u₀) (𝓝 0) := by
    have hcomp_t : Tendsto (fun u => τ + lam * u) (𝓝 u₀) (𝓝 s₀) := by
      rw [← haff_u₀]
      exact (continuous_const.add (continuous_const.mul continuous_id)).tendsto u₀
    have hlim' := ENNReal.Tendsto.const_mul (hfs_cont.comp hcomp_t)
      (Or.inr (enorm_ne_top (x := lam)))
    rw [mul_zero] at hlim'
    refine hlim'.congr' ?_
    filter_upwards [isOpen_Ioo.mem_nhds hu₀] with u hu
    have hfn : (fun y => F8U.ps g (u, y) - F8U.ps g (u₀, y)) =
        lam • fun y => F8U.ps f (τ + lam * u, y) - F8U.ps f (s₀, y) := by
      funext y
      dsimp only [Pi.smul_apply]
      rw [hps_g u hu y, hps_g u₀ hu₀ y, haff_u₀, smul_sub]
    unfold F8U.cellL2
    rw [hfn, eLpNorm_const_smul]
    rfl
  have hu₀' : u₀ ∈ Ioo (0 : ℝ) (0 + 2) := by simpa using hu₀
  have hdq_g := F8Sm.tendsto_diffQuot_slice_L2 hg_sm hg_cont hu₀'
  have hscale_nhds : Tendsto (fun h : ℝ => lam⁻¹ * h) (𝓝[≠] 0) (𝓝[≠] 0) := by
    have h0 : Tendsto (fun h : ℝ => lam⁻¹ * h) (𝓝 0) (𝓝 0) :=
      (continuous_const_mul lam⁻¹).tendsto' 0 0 (mul_zero _)
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (h0.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [eventually_mem_nhdsWithin] with h hh
    exact mul_ne_zero (inv_ne_zero hlam.ne') hh
  have hcomp_dq := ENNReal.Tendsto.const_mul (hdq_g.comp hscale_nhds)
    (Or.inr (enorm_ne_top (x := lam⁻¹)))
  rw [mul_zero] at hcomp_dq
  refine hcomp_dq.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with h _hh
  have hfn : (fun y => h⁻¹ • (f (s₀ + h, y) - f (s₀, y)) - F8U.ps f (s₀, y)) =
      lam⁻¹ • fun y => (lam⁻¹ * h)⁻¹ • (g (u₀ + lam⁻¹ * h, y) - g (u₀, y)) - F8U.ps g (u₀, y) := by
    funext y
    have h1 : τ + lam * (u₀ + lam⁻¹ * h) = s₀ + h := by
      rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul, ← add_assoc, haff_u₀]
    have h2 : (lam⁻¹ * h)⁻¹ = lam * h⁻¹ := by rw [mul_inv_rev, inv_inv, mul_comm]
    dsimp only [g, aff, Function.comp_apply, Pi.smul_apply]
    rw [h1, haff_u₀, hps_g u₀ hu₀ y, haff_u₀, h2, smul_sub (lam⁻¹),
      smul_smul, ← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul,
      smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
  unfold F8U.cellL2
  rw [hfn, eLpNorm_const_smul]
  rfl

/-- `HasDerivAt` of the `L2Cell c` slice path on `Ioo τ T`. -/
lemma hasDerivAt_sliceLpOn {c τ T s₀ : ℝ} {f : CProf}
    (hf : ContDiffOn ℝ ∞ f (Ioo τ T ×ˢ univ))
    (hm : ∀ s ∈ Ioo τ T, MemLp (F8U.slice f s) 2 (F8Sm.cellMeas c))
    (hms : MemLp (F8U.slice (F8U.ps f) s₀) 2 (F8Sm.cellMeas c))
    (hfs_cont : Tendsto (fun t => F8U.cellL2 c (fun y => F8U.ps f (t, y) - F8U.ps f (s₀, y)))
      (𝓝 s₀) (𝓝 0))
    (hs₀ : s₀ ∈ Ioo τ T) :
    HasDerivAt (sliceLpOn f hm) (hms.toLp (F8U.slice (F8U.ps f) s₀)) s₀ := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hdq := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_diffQuot_slice_L2_Ioo hf hfs_cont hs₀)
  rw [ENNReal.toReal_zero] at hdq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine hdq.congr' ?_
  have hev_in : ∀ᶠ h : ℝ in 𝓝[≠] 0, s₀ + h ∈ Ioo τ T := by
    have hc_add : Continuous (fun h : ℝ => s₀ + h) := continuous_const.add continuous_id
    exact eventually_nhdsWithin_of_eventually_nhds
      (hc_add.tendsto' 0 s₀ (add_zero s₀) (isOpen_Ioo.mem_nhds hs₀))
  filter_upwards [hev_in] with h hh
  dsimp only [Function.comp_def, F8U.cellL2]
  rw [sliceLpOn_of_mem hm hh, sliceLpOn_of_mem hm hs₀, Lp.norm_def]
  refine congrArg ENNReal.toReal (eLpNorm_congr_ae ?_)
  have hae1 := (hm (s₀ + h) hh).coeFn_toLp
  have hae0 := (hm s₀ hs₀).coeFn_toLp
  have haes := hms.coeFn_toLp
  have hsub := Lp.coeFn_sub ((hm (s₀ + h) hh).toLp (F8U.slice f (s₀ + h)))
    ((hm s₀ hs₀).toLp (F8U.slice f s₀))
  have hsmul := Lp.coeFn_smul h⁻¹ (((hm (s₀ + h) hh).toLp (F8U.slice f (s₀ + h))) -
    ((hm s₀ hs₀).toLp (F8U.slice f s₀)))
  have hdiff := Lp.coeFn_sub
    (h⁻¹ • (((hm (s₀ + h) hh).toLp (F8U.slice f (s₀ + h))) -
      ((hm s₀ hs₀).toLp (F8U.slice f s₀))))
    (hms.toLp (F8U.slice (F8U.ps f) s₀))
  filter_upwards [hae1, hae0, haes, hsub, hsmul, hdiff] with y hy1 hy0 hys hsb hsm hdf
  simp only [Pi.sub_apply, Pi.smul_apply] at hdf hsm hsb ⊢
  rw [hdf, hsm, hsb, hy1, hy0, hys]
  rfl

lemma pdir_slice_on_Ioo {τ T : ℝ} {f : CProf}
    (hf : ContDiffOn ℝ ∞ f (Ioo τ T ×ˢ univ)) {s : ℝ} (hs : s ∈ Ioo τ T) (i : Fin 2) :
    F8Sm.pdir i (F8U.slice f s) = F8U.slice (F8U.pd i f) s := by
  funext y
  have hdf : DifferentiableAt ℝ f (s, y) :=
    (hf.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs, trivial⟩)).differentiableAt
      (by simp)
  have hd_emb : HasFDerivAt (fun z : B0579.Plane => (s, z))
      ((0 : B0579.Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ B0579.Plane)) y :=
    (hasFDerivAt_const s y).prodMk (hasFDerivAt_id y)
  have hcomp := (hdf.hasFDerivAt.comp y hd_emb).fderiv
  change fderiv ℝ (f ∘ fun z : B0579.Plane => (s, z)) y (B0579.dir i) =
    fderiv ℝ f (s, y) (F8U.sdir i)
  rw [hcomp, ContinuousLinearMap.comp_apply]
  congr 1
  fin_cases i <;> rfl

lemma contDiffOn_pd_Ioo {τ T : ℝ} {f : CProf}
    (hf : ContDiffOn ℝ ∞ f (Ioo τ T ×ˢ univ)) (i : Fin 2) :
    ContDiffOn ℝ ∞ (F8U.pd i f) (Ioo τ T ×ˢ univ) :=
  (hf.fderiv_of_isOpen (isOpen_Ioo.prod isOpen_univ) (by simp)).clm_apply contDiffOn_const

lemma periodic_slice_eq_zero_of_ae_zero {c : ℝ} (hc : 0 < c) {g : B0579.Plane → CMerid}
    (hg_cont : Continuous g) (hg_per : UnforcedLeray.Cyl.IsPeriodic c g)
    (h_ae : g =ᵐ[F8Sm.cellMeas c] 0) :
    ∀ y : B0579.Plane, g y = 0 := by
  have hper_int : ∀ (m : ℤ) (y : B0579.Plane), g (y.1 + (m : ℝ) * c, y.2) = g y := by
    intro m
    induction m using Int.induction_on with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      have h1 : y.1 + (((n : ℤ) + 1 : ℤ) : ℝ) * c = (y.1 + (n : ℝ) * c) + c := by push_cast; ring
      have ih' : g (y.1 + (n : ℝ) * c, y.2) = g y := by simpa using ih y
      rw [h1, hg_per (y.1 + (n : ℝ) * c, y.2), ih']
    | pred n ih =>
      intro y
      have h2 : (y.1 + ((-(n : ℤ) - 1 : ℤ) : ℝ) * c) + c = y.1 + (-(n : ℝ)) * c := by
        push_cast; ring
      have hp := hg_per (y.1 + ((-(n : ℤ) - 1 : ℤ) : ℝ) * c, y.2)
      dsimp only at hp
      have ih' : g (y.1 + (-(n : ℝ)) * c, y.2) = g y := by simpa using ih y
      rw [h2, ih'] at hp
      exact hp.symm
  intro y₀
  by_contra hne
  let m : ℤ := ⌊(y₀.1 + c / 2) / c⌋
  let q₁ : ℝ := y₀.1 - (m : ℝ) * c
  have hq₁_ge : -(c / 2) ≤ q₁ := by
    dsimp [q₁]
    have := (le_div_iff₀ hc).1 (Int.floor_le ((y₀.1 + c / 2) / c))
    linarith
  have hq₁_lt : q₁ < c / 2 := by
    dsimp [q₁]
    have := (div_lt_iff₀ hc).1 (Int.lt_floor_add_one ((y₀.1 + c / 2) / c))
    linarith
  have hg_q₁ : g (q₁, y₀.2) ≠ 0 := by
    have heq : (q₁ + (m : ℝ) * c, y₀.2) = y₀ := by ext <;> simp [q₁]
    rw [← hper_int m (q₁, y₀.2), heq]
    exact hne
  obtain ⟨r, hr_pos, hr_ball⟩ := Metric.isOpen_iff.1 (isOpen_ne.preimage hg_cont) (q₁, y₀.2) hg_q₁
  let ε : ℝ := min (r / 2) ((c / 2 - q₁) / 2)
  have hε_pos : 0 < ε := lt_min (half_pos hr_pos) (half_pos (sub_pos.2 hq₁_lt))
  let B : Set B0579.Plane := Ioo q₁ (q₁ + ε) ×ˢ Ioo (y₀.2 - ε) (y₀.2 + ε)
  have hB_cell : B ⊆ B0579.cell c := by
    intro z hz
    have hε_c : ε ≤ (c / 2 - q₁) / 2 := min_le_right _ _
    rw [F8Sm.cell_eq_cylCell]
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, trivial⟩
  have hB_nz : ∀ z ∈ B, g z ≠ 0 := by
    intro z hz
    apply hr_ball
    have hε_r : ε ≤ r / 2 := min_le_left _ _
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    refine max_lt ?_ ?_
    · rw [abs_lt]; exact ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
    · rw [abs_lt]; exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hnull : (F8Sm.cellMeas c) {z | g z ≠ 0} = 0 := ae_iff.1 h_ae
  have hB_zero : (F8Sm.cellMeas c) B = 0 :=
    le_antisymm ((measure_mono hB_nz).trans (le_of_eq hnull)) bot_le
  rw [F8Sm.cellMeas, Measure.restrict_apply ( measurableSet_Ioo.prod measurableSet_Ioo ),
    inter_eq_self_of_subset_left hB_cell, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Ioo, Real.volume_Ioo] at hB_zero
  have h1 : q₁ + ε - q₁ = ε := by ring
  have h2 : y₀.2 + ε - (y₀.2 - ε) = 2 * ε := by ring
  rw [h1, h2] at hB_zero
  have hpos : 0 < ENNReal.ofReal ε * ENNReal.ofReal (2 * ε) :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.2 hε_pos).ne'
      (ENNReal.ofReal_pos.2 (by linarith)).ne'
  exact hpos.ne' hB_zero

/-- Classical `L²(cell)` energy Grönwall uniqueness on any open age strip `Ioo τ T ×ˢ univ`
(`0 ≤ τ < T`), yielding identical vanishing of `δ`, `pd i δ`, and `pd i (pd j δ)`. -/
lemma classical_oseen_zero_on_Ioo {dm dp : ℝ} {p : Params} {d : ℝ} (hreg : BgRegime p d dm dp)
    {τ T : ℝ} (hτ : 0 ≤ τ) {δ : CProf}
    (hsm : ContDiffOn ℝ ∞ δ (Ioo τ T ×ˢ univ))
    (hper : ∀ x : Coord, x.1 ∈ Ioo τ T → δ (qShift p.c x) = δ x)
    (hdiv : ∀ x : Coord, x.1 ∈ Ioo τ T → F8U.pd 0 δ x 0 + F8U.pd 1 δ x 1 = 0)
    (hm0 : ∀ s ∈ Ioo τ T, MemLp (F8U.slice δ s) 2 (F8Sm.cellMeas p.c))
    (hm1 : ∀ s ∈ Ioo τ T, ∀ i : Fin 2, MemLp (F8U.slice (F8U.pd i δ) s) 2 (F8Sm.cellMeas p.c))
    (hm2 : ∀ s ∈ Ioo τ T, ∀ i j : Fin 2,
      MemLp (F8U.slice (F8U.pd i (F8U.pd j δ)) s) 2 (F8Sm.cellMeas p.c))
    (hms : ∀ s ∈ Ioo τ T, MemLp (F8U.slice (F8U.ps δ) s) 2 (F8Sm.cellMeas p.c))
    (hcs : ∀ s ∈ Ioo τ T,
      Tendsto (fun t => F8U.cellL2 p.c (fun y => F8U.ps δ (t, y) - F8U.ps δ (s, y))) (𝓝 s) (𝓝 0))
    (hproj : ∀ s ∈ Ioo τ T, ∀ φ : B0579.Plane → CMerid,
      MemLp φ 2 (F8Sm.cellMeas p.c) → F8U.IsCellSolenoidal p.c φ →
        ∫ y in B0579.cell p.c, inner ℂ (φ y) (F8U.homResidual p δ (s, y)) = 0)
    (hinit : Tendsto (fun s => F8U.cellL2 p.c (F8U.slice δ s)) (𝓝[>] τ) (𝓝 0)) :
    ∀ x ∈ Ioo τ T ×ˢ (univ : Set B0579.Plane),
      δ x = 0 ∧ (∀ i : Fin 2, F8U.pd i δ x = 0) ∧ (∀ i j : Fin 2, F8U.pd i (F8U.pd j δ) x = 0) := by
  by_cases hτT : τ < T
  · obtain ⟨M, hM, hV_sm, _, hb0, hb1⟩ := uniform_train_C1 hreg (T := T) (by linarith)
    let L : ℝ → L2Cell p.c := sliceLpOn δ hm0
    let E : ℝ → ℝ := fun s => ‖L s‖ ^ 2
    let K : ℝ := M ^ 2 / p.ν + 8 * M
    have hK_nn : 0 ≤ K := by dsimp [K]; have := p.ν_pos; positivity
    have hE_deriv : ∀ s ∈ Ioo τ T, ∃ E' : ℝ, HasDerivAt E E' s ∧ E' ≤ K * E s := by
      intro s hs
      let Ls' : L2Cell p.c := (hms s hs).toLp (F8U.slice (F8U.ps δ) s)
      have hdL : HasDerivAt L Ls' s :=
        hasDerivAt_sliceLpOn hsm hm0 (hms s hs) (hcs s hs) hs
      have hd_inn := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s (hdL.inner ℂ hdL)
      have hfn_E : (fun r => Complex.reCLM (inner ℂ (L r) (L r))) = E := by
        funext r
        change (inner ℂ (L r) (L r)).re = ‖L r‖ ^ 2
        simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) (L r)
      have hd_inn' : HasDerivAt E (Complex.reCLM (inner ℂ (L s) Ls' + inner ℂ Ls' (L s))) s := by
        rw [← hfn_E]
        exact hd_inn
      have hre_symm : Complex.reCLM (inner ℂ (L s) Ls' + inner ℂ Ls' (L s)) =
          2 * (inner ℂ (L s) Ls').re := by
        change (inner ℂ (L s) Ls' + inner ℂ Ls' (L s)).re = _
        rw [Complex.add_re, ← inner_conj_symm (L s) Ls', Complex.conj_re]
        ring
      rw [hre_symm] at hd_inn'
      refine ⟨2 * (inner ℂ (L s) Ls').re, hd_inn', ?_⟩
      have hLs_eq : L s = (hm0 s hs).toLp (F8U.slice δ s) := sliceLpOn_of_mem hm0 hs
      have hinn_int : inner ℂ (L s) Ls' =
          ∫ y in B0579.cell p.c, inner ℂ (δ (s, y)) (F8U.ps δ (s, y)) := by
        rw [hLs_eq, L2.inner_def (𝕜 := ℂ)]
        refine integral_congr_ae ?_
        filter_upwards [(hm0 s hs).coeFn_toLp, (hms s hs).coeFn_toLp] with y hy0 hys
        rw [hy0, hys]; rfl
      have hφ_sm : ContDiff ℝ ∞ (F8U.slice δ s) :=
        contDiffOn_univ.1 (hsm.comp (contDiff_const.prodMk contDiff_id).contDiffOn
          (fun y _ => ⟨hs, trivial⟩))
      have hφ_per : UnforcedLeray.Cyl.IsPeriodic p.c (F8U.slice δ s) :=
        fun y => hper (s, y) hs
      have hpdir1 : ∀ i : Fin 2, F8Sm.pdir i (F8U.slice δ s) = F8U.slice (F8U.pd i δ) s :=
        fun i => pdir_slice_on_Ioo hsm hs i
      have hpdir2 : ∀ i : Fin 2,
          F8Sm.pdir i (F8Sm.pdir i (F8U.slice δ s)) = F8U.slice (F8U.pd i (F8U.pd i δ)) s := by
        intro i
        rw [hpdir1 i]
        exact pdir_slice_on_Ioo (contDiffOn_pd_Ioo hsm i) hs i
      have hφ_sol : F8U.IsCellSolenoidal p.c (F8U.slice δ s) :=
        F8Sm.isCellSolenoidal_of_div_free p.c_pos hφ_sm hφ_per fun y => by
          rw [hpdir1 0, hpdir1 1]; exact hdiv (s, y) hs
      have hres0 := hproj s hs (F8U.slice δ s) (hm0 s hs) hφ_sol
      have hs_icc : s ∈ Icc (0 : ℝ) T := ⟨by linarith [hs.1], hs.2.le⟩
      obtain ⟨hm_bv, hbd_bv⟩ := memLp_and_cellL2_bvTripleSlice hM (hV_sm s hs_icc)
        (hb0 s hs_icc) (hb1 s hs_icc) (hm0 s hs) (hm1 s hs 0) (hm1 s hs 1)
      have hm_lap := ((hm2 s hs 0 0).add (hm2 s hs 1 1)).const_smul p.ν
      have hi_ps := F8Sm.integrableOn_inner_cell (hm0 s hs) (hms s hs)
      have hi_lap := F8Sm.integrableOn_inner_cell (hm0 s hs) hm_lap
      have hi_bv := F8Sm.integrableOn_inner_cell (hm0 s hs) hm_bv
      have hi_00 := F8Sm.integrableOn_inner_cell (hm0 s hs) (hm2 s hs 0 0)
      have hi_11 := F8Sm.integrableOn_inner_cell (hm0 s hs) (hm2 s hs 1 1)
      have hsplit : (∫ y in B0579.cell p.c, inner ℂ (F8U.slice δ s y) (F8U.homResidual p δ (s, y))) =
          (∫ y in B0579.cell p.c, inner ℂ (δ (s, y)) (F8U.ps δ (s, y))) -
          (p.ν : ℂ) * ((∫ y in B0579.cell p.c, inner ℂ (δ (s, y)) (F8U.pd 0 (F8U.pd 0 δ) (s, y))) +
            (∫ y in B0579.cell p.c, inner ℂ (δ (s, y)) (F8U.pd 1 (F8U.pd 1 δ) (s, y)))) +
          (∫ y in B0579.cell p.c, inner ℂ (δ (s, y))
            (bvTripleSlice (p.train.v s) (F8U.slice δ s)
              (F8U.slice (F8U.pd 0 δ) s) (F8U.slice (F8U.pd 1 δ) s) y)) := by
        have hpt : (fun y => inner ℂ (F8U.slice δ s y) (F8U.homResidual p δ (s, y))) =
            fun y => (inner ℂ (F8U.slice δ s y) (F8U.slice (F8U.ps δ) s y) -
              inner ℂ (F8U.slice δ s y) ((p.ν • (F8U.slice (F8U.pd 0 (F8U.pd 0 δ)) s +
                F8U.slice (F8U.pd 1 (F8U.pd 1 δ)) s)) y)) +
              inner ℂ (F8U.slice δ s y) (bvTripleSlice (p.train.v s) (F8U.slice δ s)
                (F8U.slice (F8U.pd 0 δ) s) (F8U.slice (F8U.pd 1 δ) s) y) := by
          funext y
          unfold F8U.homResidual
          rw [inner_add_right, inner_sub_right]; rfl
        have hi_sub : IntegrableOn
            (fun y => inner ℂ (F8U.slice δ s y) (F8U.slice (F8U.ps δ) s y) -
              inner ℂ (F8U.slice δ s y) ((p.ν • (F8U.slice (F8U.pd 0 (F8U.pd 0 δ)) s +
                F8U.slice (F8U.pd 1 (F8U.pd 1 δ)) s)) y))
            (B0579.cell p.c) volume := hi_ps.sub hi_lap
        rw [hpt, integral_add hi_sub hi_bv, integral_sub hi_ps hi_lap]
        congr 2
        have hpt2 : (fun y => inner ℂ (F8U.slice δ s y)
              ((p.ν • (F8U.slice (F8U.pd 0 (F8U.pd 0 δ)) s +
                F8U.slice (F8U.pd 1 (F8U.pd 1 δ)) s)) y)) =
            fun y => (p.ν : ℂ) * ((fun z => inner ℂ (F8U.slice δ s z)
                (F8U.slice (F8U.pd 0 (F8U.pd 0 δ)) s z)) y +
              (fun z => inner ℂ (F8U.slice δ s z)
                (F8U.slice (F8U.pd 1 (F8U.pd 1 δ)) s z)) y) := by
          funext y
          change inner ℂ (δ (s, y)) ((p.ν : ℂ) • (F8U.pd 0 (F8U.pd 0 δ) (s, y) +
            F8U.pd 1 (F8U.pd 1 δ) (s, y))) = _
          rw [inner_smul_right, inner_add_right]; rfl
        rw [hpt2, integral_const_mul, integral_add hi_00 hi_11]; rfl
      rw [hsplit] at hres0
      let G0 : L2Cell p.c := (hm1 s hs 0).toLp (F8U.slice (F8U.pd 0 δ) s)
      let G1 : L2Cell p.c := (hm1 s hs 1).toLp (F8U.slice (F8U.pd 1 δ) s)
      let Bv : L2Cell p.c := hm_bv.toLp (bvTripleSlice (p.train.v s) (F8U.slice δ s)
        (F8U.slice (F8U.pd 0 δ) s) (F8U.slice (F8U.pd 1 δ) s))
      have hibp : ∀ i : Fin 2,
          (∫ y in B0579.cell p.c, inner ℂ (δ (s, y)) (F8U.pd i (F8U.pd i δ) (s, y))).re =
            - ‖(hm1 s hs i).toLp (F8U.slice (F8U.pd i δ) s)‖ ^ 2 := by
        intro i
        have hper_di : UnforcedLeray.Cyl.IsPeriodic p.c (F8Sm.pdir i (F8U.slice δ s)) := by
          intro y
          let v₀ : B0579.Plane := (p.c, 0)
          have hfn : (fun z : B0579.Plane => F8U.slice δ s (z + v₀)) = F8U.slice δ s := by
            funext z
            have hz : z + v₀ = (z.1 + p.c, z.2) := Prod.ext rfl (add_zero z.2)
            rw [hz]
            exact hφ_per z
          have hd_sh : HasFDerivAt (fun z : B0579.Plane => z + v₀)
              (ContinuousLinearMap.id ℝ B0579.Plane) y :=
            (hasFDerivAt_id y).add_const v₀
          have hd_g : HasFDerivAt (F8U.slice δ s)
              (fderiv ℝ (F8U.slice δ s) (y + v₀)) (y + v₀) :=
            (hφ_sm.contDiffAt.differentiableAt (by simp)).hasFDerivAt
          have hcomp := (hd_g.comp y hd_sh).fderiv
          change fderiv ℝ (F8U.slice δ s) (y.1 + p.c, y.2) (B0579.dir i) =
            fderiv ℝ (F8U.slice δ s) y (B0579.dir i)
          have hy : y + v₀ = (y.1 + p.c, y.2) := Prod.ext rfl (add_zero y.2)
          rw [← hy]
          change (fderiv ℝ (F8U.slice δ s) (y + v₀)).comp
            (ContinuousLinearMap.id ℝ B0579.Plane) (B0579.dir i) = _
          rw [← hcomp]
          change fderiv ℝ (fun z : B0579.Plane => F8U.slice δ s (z + v₀)) y (B0579.dir i) = _
          rw [hfn]
        have hi_eq := F8Sm.cell_ibp_pdir p.c_pos i hφ_sm
          (F8Sm.contDiff_pdir hφ_sm i) hφ_per hper_di
          (hm0 s hs) (by rw [hpdir1 i]; exact hm1 s hs i)
          (by rw [hpdir1 i]; exact hm1 s hs i) (by rw [hpdir2 i]; exact hm2 s hs i i)
        rw [hpdir2 i, hpdir1 i] at hi_eq
        have hnorm_gi : (∫ y in B0579.cell p.c,
              inner ℂ (F8U.pd i δ (s, y)) (F8U.pd i δ (s, y))).re =
            ‖(hm1 s hs i).toLp (F8U.slice (F8U.pd i δ) s)‖ ^ 2 := by
          have hL2 : inner ℂ ((hm1 s hs i).toLp (F8U.slice (F8U.pd i δ) s))
              ((hm1 s hs i).toLp (F8U.slice (F8U.pd i δ) s)) =
              ∫ y in B0579.cell p.c, inner ℂ (F8U.pd i δ (s, y)) (F8U.pd i δ (s, y)) := by
            rw [L2.inner_def (𝕜 := ℂ)]
            refine integral_congr_ae ?_
            filter_upwards [(hm1 s hs i).coeFn_toLp] with y hy
            rw [hy]; rfl
          rw [← hL2]
          simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) _
        have hneg := congrArg Complex.re hi_eq
        dsimp only [F8U.slice] at hneg
        rw [Complex.neg_re, hnorm_gi] at hneg
        linarith
      have hbv_re : -(∫ y in B0579.cell p.c, inner ℂ (δ (s, y))
            (bvTripleSlice (p.train.v s) (F8U.slice δ s)
              (F8U.slice (F8U.pd 0 δ) s) (F8U.slice (F8U.pd 1 δ) s) y)).re ≤
          ‖L s‖ * (M * ‖G0‖ + M * ‖G1‖ + 4 * M * ‖L s‖) := by
        have hL2_bv : ∫ y in B0579.cell p.c, inner ℂ (δ (s, y))
            (bvTripleSlice (p.train.v s) (F8U.slice δ s)
              (F8U.slice (F8U.pd 0 δ) s) (F8U.slice (F8U.pd 1 δ) s) y) =
            inner ℂ (L s) Bv := by
          rw [hLs_eq, L2.inner_def (𝕜 := ℂ)]
          refine (integral_congr_ae ?_).symm
          filter_upwards [(hm0 s hs).coeFn_toLp, hm_bv.coeFn_toLp] with y hy0 hyb
          rw [hy0, hyb]; rfl
        rw [hL2_bv]
        have habs : -(inner ℂ (L s) Bv).re ≤ ‖inner ℂ (L s) Bv‖ :=
          (neg_le_abs _).trans (Complex.abs_re_le_norm _)
        have hcs_in : ‖inner ℂ (L s) Bv‖ ≤ ‖L s‖ * ‖Bv‖ := norm_inner_le_norm (L s) Bv
        have hBv_n : ‖Bv‖ ≤ M * ‖G0‖ + M * ‖G1‖ + 4 * M * ‖L s‖ := by
          have nB : ‖Bv‖ = (F8U.cellL2 p.c (bvTripleSlice (p.train.v s) (F8U.slice δ s)
              (F8U.slice (F8U.pd 0 δ) s) (F8U.slice (F8U.pd 1 δ) s))).toReal :=
            F8Sm.norm_toLp_eq_cellL2 hm_bv
          have n0 : ‖L s‖ = (F8U.cellL2 p.c (F8U.slice δ s)).toReal := by
            rw [hLs_eq]; exact F8Sm.norm_toLp_eq_cellL2 (hm0 s hs)
          have ng0 : ‖G0‖ = (F8U.cellL2 p.c (F8U.slice (F8U.pd 0 δ) s)).toReal :=
            F8Sm.norm_toLp_eq_cellL2 (hm1 s hs 0)
          have ng1 : ‖G1‖ = (F8U.cellL2 p.c (F8U.slice (F8U.pd 1 δ) s)).toReal :=
            F8Sm.norm_toLp_eq_cellL2 (hm1 s hs 1)
          rw [nB, n0, ng0, ng1]
          exact hbd_bv
        exact habs.trans (hcs_in.trans (mul_le_mul_of_nonneg_left hBv_n (norm_nonneg _)))
      have hre0 := congrArg Complex.re hres0
      simp only [Complex.zero_re, Complex.add_re, Complex.sub_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre0
      rw [hibp 0, hibp 1] at hre0
      have hps_re : (inner ℂ (L s) Ls').re ≤
          -p.ν * (‖G0‖ ^ 2 + ‖G1‖ ^ 2) + ‖L s‖ * (M * ‖G0‖ + M * ‖G1‖ + 4 * M * ‖L s‖) := by
        rw [hinn_int]
        linarith [hbv_re]
      have hyoung : ∀ g : ℝ, M * ‖L s‖ * g - p.ν * g ^ 2 ≤ (M ^ 2 / (4 * p.ν)) * ‖L s‖ ^ 2 := by
        intro g
        have hν_pos : 0 < p.ν := p.ν_pos
        have hsq : 0 ≤ p.ν * (g - M * ‖L s‖ / (2 * p.ν)) ^ 2 :=
          mul_nonneg hν_pos.le (sq_nonneg _)
        have hid : (M ^ 2 / (4 * p.ν)) * ‖L s‖ ^ 2 - (M * ‖L s‖ * g - p.ν * g ^ 2) =
            p.ν * (g - M * ‖L s‖ / (2 * p.ν)) ^ 2 := by
          field_simp [hν_pos.ne']
          ring
        linarith
      have hy0 := hyoung ‖G0‖
      have hy1 := hyoung ‖G1‖
      have hexp1 : -p.ν * (‖G0‖ ^ 2 + ‖G1‖ ^ 2) + ‖L s‖ * (M * ‖G0‖ + M * ‖G1‖ + 4 * M * ‖L s‖) =
          (M * ‖L s‖ * ‖G0‖ - p.ν * ‖G0‖ ^ 2) + (M * ‖L s‖ * ‖G1‖ - p.ν * ‖G1‖ ^ 2) +
            4 * M * ‖L s‖ ^ 2 := by ring
      have hexp2 : 2 * ((M ^ 2 / (4 * p.ν)) * ‖L s‖ ^ 2 + (M ^ 2 / (4 * p.ν)) * ‖L s‖ ^ 2 +
            4 * M * ‖L s‖ ^ 2) = (M ^ 2 / p.ν + 8 * M) * ‖L s‖ ^ 2 := by
        have hν_pos : 0 < p.ν := p.ν_pos
        field_simp [hν_pos.ne']
        ring
      dsimp [K, E]
      linarith [hps_re, hy0, hy1, hexp1, hexp2]
    have hE_zero : ∀ t ∈ Ioo τ T, E t = 0 := by
      intro t ht
      let G : ℝ → ℝ := fun s => Real.exp (-K * s) * E s
      have hG_deriv : ∀ s ∈ Ioo τ T, DifferentiableAt ℝ G s ∧ deriv G s ≤ 0 := by
        intro s hs
        obtain ⟨E', hdE, hbdE⟩ := hE_deriv s hs
        have hd_exp : HasDerivAt (fun r => Real.exp (-K * r))
            (Real.exp (-K * s) * (-K)) s := by
          simpa using ((hasDerivAt_id s).const_mul (-K)).exp
        have hdG : HasDerivAt G (Real.exp (-K * s) * (-K) * E s + Real.exp (-K * s) * E') s :=
          hd_exp.mul hdE
        refine ⟨hdG.differentiableAt, ?_⟩
        rw [hdG.deriv]
        have hpos : 0 < Real.exp (-K * s) := Real.exp_pos _
        have hle : Real.exp (-K * s) * (-K) * E s + Real.exp (-K * s) * E' =
            Real.exp (-K * s) * (E' - K * E s) := by ring
        rw [hle]
        exact mul_nonpos_of_nonneg_of_nonpos hpos.le (by linarith)
      have hG_lim : Tendsto G (𝓝[>] τ) (𝓝 0) := by
        have hE_lim : Tendsto E (𝓝[>] τ) (𝓝 0) := by
          have htr := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hinit).pow 2
          simp only [ENNReal.toReal_zero, zero_pow (by decide : 2 ≠ 0)] at htr
          refine htr.congr' ?_
          filter_upwards [Ioo_mem_nhdsGT hτT] with r hr
          dsimp [E, L]
          rw [sliceLpOn_of_mem hm0 hr, F8Sm.norm_toLp_eq_cellL2 (hm0 r hr)]
        have hexp_lim : Tendsto (fun r => Real.exp (-K * r)) (𝓝[>] τ) (𝓝 (Real.exp (-K * τ))) :=
          tendsto_nhdsWithin_of_tendsto_nhds
            ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).tendsto τ)
        have h0 : Real.exp (-K * τ) * 0 = 0 := mul_zero _
        rw [← h0]
        exact hexp_lim.mul hE_lim
      have hGt_le : G t ≤ 0 := by
        refine ge_of_tendsto hG_lim ?_
        filter_upwards [Ioo_mem_nhdsGT ht.1] with r hr
        have hsub : Icc r t ⊆ Ioo τ T := fun u hu => ⟨hr.1.trans_le hu.1, hu.2.trans_lt ht.2⟩
        have hanti : AntitoneOn G (Icc r t) := by
          refine antitoneOn_of_deriv_nonpos (convex_Icc r t) ?_ ?_ ?_
          · exact fun u hu => (hG_deriv u (hsub hu)).1.continuousAt.continuousWithinAt
          · intro u hu
            rw [interior_Icc] at hu
            exact (hG_deriv u (hsub ⟨hu.1.le, hu.2.le⟩)).1.differentiableWithinAt
          · intro u hu
            rw [interior_Icc] at hu
            exact (hG_deriv u (hsub ⟨hu.1.le, hu.2.le⟩)).2
        exact hanti ⟨le_rfl, hr.2.le⟩ ⟨hr.2.le, le_rfl⟩ hr.2.le
      have hGt_nn : 0 ≤ G t := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
      have hGt0 : Real.exp (-K * t) * E t = 0 := le_antisymm hGt_le hGt_nn
      exact (mul_eq_zero.1 hGt0).resolve_left (Real.exp_pos _).ne'
    have hδ_zero : ∀ x ∈ Ioo τ T ×ˢ (univ : Set B0579.Plane), δ x = 0 := by
      rintro ⟨t, y⟩ ⟨ht, -⟩
      have hEt := hE_zero t ht
      have hLt : L t = 0 := norm_eq_zero.1 (sq_eq_zero_iff.1 hEt)
      dsimp only [L] at hLt
      rw [sliceLpOn_of_mem hm0 ht] at hLt
      have hae : F8U.slice δ t =ᵐ[F8Sm.cellMeas p.c] 0 := by
        filter_upwards [(hm0 t ht).coeFn_toLp,
          Lp.coeFn_zero CMerid 2 (F8Sm.cellMeas p.c)] with z hz1 hz0
        rw [← hz1, hLt, hz0]
      have hsm_t : ContDiff ℝ ∞ (F8U.slice δ t) :=
        contDiffOn_univ.1 (hsm.comp (contDiff_const.prodMk contDiff_id).contDiffOn
          (fun z _ => ⟨ht, trivial⟩))
      exact periodic_slice_eq_zero_of_ae_zero p.c_pos hsm_t.continuous
        (fun z => hper (t, z) ht) hae y
    have hpd_zero : ∀ i : Fin 2, ∀ x ∈ Ioo τ T ×ˢ (univ : Set B0579.Plane), F8U.pd i δ x = 0 := by
      intro i x hx
      have hev : δ =ᶠ[𝓝 x] 0 := by
        filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hx] with z hz
        exact hδ_zero z hz
      change fderiv ℝ δ x (F8U.sdir i) = 0
      rw [hev.fderiv_eq]
      simp
    refine fun x hx => ⟨hδ_zero x hx, fun i => hpd_zero i x hx, fun i j => ?_⟩
    have hev : F8U.pd j δ =ᶠ[𝓝 x] 0 := by
      filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hx] with z hz
      exact hpd_zero j z hz
    change fderiv ℝ (F8U.pd j δ) x (F8U.sdir i) = 0
    rw [hev.fderiv_eq]
    simp
  · rintro ⟨s, y⟩ ⟨hs, -⟩
    exact False.elim (hτT (hs.1.trans hs.2))

/-- Same-age orbit uniqueness on `stripSet σ`: two orbits from `cellMeas`-a.e. equal `IsCylH1Datum`
coincide identically on `(σ, σ + 2) × ℝ²` together with `pd i` and `pd i (pd j)`. -/
lemma isCylOseenOrbit_unique {dm dp : ℝ} {p : Params} {d : ℝ} (hreg : BgRegime p d dm dp)
    {σ : ℝ} (hσ : 0 ≤ σ) {w₁ w₂ : CProf}
    {u₁ uq₁ uη₁ u₂ uq₂ uη₂ : B0579.Plane → CMerid}
    (hu₁ : F8U.IsCylH1Datum p.c u₁ uq₁ uη₁)
    (hu_ae : u₁ =ᵐ[F8Sm.cellMeas p.c] u₂)
    (huq_ae : uq₁ =ᵐ[F8Sm.cellMeas p.c] uq₂)
    (huη_ae : uη₁ =ᵐ[F8Sm.cellMeas p.c] uη₂)
    (h₁ : F8U.IsCylOseenOrbit p σ w₁ u₁ uq₁ uη₁)
    (h₂ : F8U.IsCylOseenOrbit p σ w₂ u₂ uq₂ uη₂) :
    ∀ x ∈ F8Sm.stripSet σ,
      w₁ x = w₂ x ∧ (∀ i : Fin 2, F8U.pd i w₁ x = F8U.pd i w₂ x) ∧
        (∀ i j : Fin 2, F8U.pd i (F8U.pd j w₁) x = F8U.pd i (F8U.pd j w₂) x) := by
  have h₂' : F8U.IsCylOseenOrbit p σ w₂ u₁ uq₁ uη₁ :=
    isCylOseenOrbit_congr_datum hu_ae.symm huq_ae.symm huη_ae.symm h₂
  have hdiff := isCylOseenOrbit_comb hreg hσ hu₁ hu₁ h₁ h₂' 1 (-1)
  have hinit0 : Tendsto (fun s => F8U.cellL2 p.c
      (F8U.slice (fun z => (1 : ℝ) • w₁ z + (-1 : ℝ) • w₂ z) s)) (𝓝[>] σ) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiff.initial
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards with s
    have h0 : (fun y => ((1 : ℝ) • w₁ (s, y) + (-1 : ℝ) • w₂ (s, y)) -
        ((1 : ℝ) • u₁ y + (-1 : ℝ) • u₁ y)) =
        F8U.slice (fun z => (1 : ℝ) • w₁ z + (-1 : ℝ) • w₂ z) s := by
      funext y; simp [F8U.slice]
    unfold F8U.cylH1
    rw [h0]
    exact le_self_add.trans le_self_add
  have hz := classical_oseen_zero_on_Ioo hreg hσ hdiff.smooth hdiff.periodic hdiff.div_free
    (fun s hs => hdiff.memL2 s hs 0 (by decide) ![])
    (fun s hs i => hdiff.memL2 s hs 1 (by decide) ![i])
    (fun s hs i j => hdiff.memL2 s hs 2 (by decide) ![i, j])
    (fun s hs => hdiff.memL2_s s hs 0 (by decide) ![])
    (fun s hs => hdiff.cont_s s hs 0 (by decide) ![])
    hdiff.projected hinit0
  intro x hx
  obtain ⟨z0, z1, z2⟩ := hz x hx
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · simp only [one_smul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at z0
    exact z0
  · have := pdIter_comb_on_strip h₁.smooth h₂.smooth 1 (-1) ![i] hx
    change F8U.pd i (fun z => (1 : ℝ) • w₁ z + (-1 : ℝ) • w₂ z) x = _ at this
    rw [z1 i] at this
    simp only [one_smul, neg_one_smul, ← sub_eq_add_neg] at this
    exact sub_eq_zero.1 this.symm
  · have := pdIter_comb_on_strip h₁.smooth h₂.smooth 1 (-1) ![i, j] hx
    change F8U.pd i (F8U.pd j (fun z => (1 : ℝ) • w₁ z + (-1 : ℝ) • w₂ z)) x = _ at this
    rw [z2 i j] at this
    simp only [one_smul, neg_one_smul, ← sub_eq_add_neg] at this
    exact sub_eq_zero.1 this.symm

/-- Chapman–Kolmogorov identity for classical Oseen orbits: if `W₀` starts at `τ₀ ≥ 0` and `W₁`
starts at `τ ∈ (τ₀, τ₀ + 2)` from the slice of `W₀` at `τ`, then `W₁ = W₀` (with `pd i` and
`pd i (pd j)`) identically on `(τ, τ₀ + 2) × ℝ²`. -/
lemma chapman_kolmogorov_orbit {dm dp : ℝ} {p : Params} {d : ℝ} (hreg : BgRegime p d dm dp)
    {τ₀ τ : ℝ} (hτ₀ : 0 ≤ τ₀) (hτ : τ ∈ Ioo τ₀ (τ₀ + 2))
    {W₀ W₁ : CProf} {u₀ uq₀ uη₀ : B0579.Plane → CMerid}
    (hW₀ : F8U.IsCylOseenOrbit p τ₀ W₀ u₀ uq₀ uη₀)
    (hW₁ : F8U.IsCylOseenOrbit p τ W₁ (F8U.slice W₀ τ) (F8U.slice (F8U.pd 0 W₀) τ)
      (F8U.slice (F8U.pd 1 W₀) τ)) :
    ∀ x ∈ Ioo τ (τ₀ + 2) ×ˢ (univ : Set B0579.Plane),
      W₁ x = W₀ x ∧ (∀ i : Fin 2, F8U.pd i W₁ x = F8U.pd i W₀ x) ∧
        (∀ i j : Fin 2, F8U.pd i (F8U.pd j W₁) x = F8U.pd i (F8U.pd j W₀) x) := by
  let δ : CProf := fun x => (1 : ℝ) • W₁ x + (-1 : ℝ) • W₀ x
  have hsub₀ : Ioo τ (τ₀ + 2) ⊆ Ioo τ₀ (τ₀ + 2) := fun s hs => ⟨hτ.1.trans hs.1, hs.2⟩
  have hsub₁ : Ioo τ (τ₀ + 2) ⊆ Ioo τ (τ + 2) := fun s hs => ⟨hs.1, by linarith [hτ.1, hs.2]⟩
  have hsm : ContDiffOn ℝ ∞ δ (Ioo τ (τ₀ + 2) ×ˢ univ) :=
    ((hW₁.smooth.mono (prod_mono_left hsub₁)).const_smul 1).add
      ((hW₀.smooth.mono (prod_mono_left hsub₀)).const_smul (-1))
  have hpd_comb : ∀ {n : ℕ} (α : Fin n → Fin 2) {x : Coord},
      x ∈ Ioo τ (τ₀ + 2) ×ˢ (univ : Set B0579.Plane) →
      F8U.pdIter α δ x = F8U.pdIter α W₁ x - F8U.pdIter α W₀ x := by
    intro n
    induction n with
    | zero => intro α x _; simp [δ, F8U.pdIter, sub_eq_add_neg]
    | succ n ih =>
      intro α x hx
      have hev : F8U.pdIter (Fin.tail α) δ =ᶠ[𝓝 x]
          fun z => F8U.pdIter (Fin.tail α) W₁ z - F8U.pdIter (Fin.tail α) W₀ z := by
        filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hx] with z hz
        exact ih (Fin.tail α) hz
      have hd1 : DifferentiableAt ℝ (F8U.pdIter (Fin.tail α) W₁) x :=
        ((F8Sm.contDiffOn_pdIter hW₁.smooth (Fin.tail α)).contDiffAt
          ((F8Sm.isOpen_stripSet τ).mem_nhds ⟨hsub₁ hx.1, trivial⟩)).differentiableAt (by simp)
      have hd0 : DifferentiableAt ℝ (F8U.pdIter (Fin.tail α) W₀) x :=
        ((F8Sm.contDiffOn_pdIter hW₀.smooth (Fin.tail α)).contDiffAt
          ((F8Sm.isOpen_stripSet τ₀).mem_nhds ⟨hsub₀ hx.1, trivial⟩)).differentiableAt (by simp)
      change fderiv ℝ (F8U.pdIter (Fin.tail α) δ) x (F8U.sdir (α 0)) = _
      rw [hev.fderiv_eq]
      change fderiv ℝ (F8U.pdIter (Fin.tail α) W₁ - F8U.pdIter (Fin.tail α) W₀) x
        (F8U.sdir (α 0)) = _
      rw [(hd1.hasFDerivAt.sub hd0.hasFDerivAt).fderiv]
      rfl
  have hps_comb : ∀ {x : Coord}, x ∈ Ioo τ (τ₀ + 2) ×ˢ (univ : Set B0579.Plane) →
      F8U.ps δ x = F8U.ps W₁ x - F8U.ps W₀ x := by
    intro x hx
    have hev : δ =ᶠ[𝓝 x] fun z => W₁ z - W₀ z := by
      filter_upwards with z; simp [δ, sub_eq_add_neg]
    have hd1 : DifferentiableAt ℝ W₁ x :=
      (hW₁.smooth.contDiffAt ((F8Sm.isOpen_stripSet τ).mem_nhds ⟨hsub₁ hx.1, trivial⟩)).differentiableAt
        (by simp)
    have hd0 : DifferentiableAt ℝ W₀ x :=
      (hW₀.smooth.contDiffAt ((F8Sm.isOpen_stripSet τ₀).mem_nhds ⟨hsub₀ hx.1, trivial⟩)).differentiableAt
        (by simp)
    unfold F8U.ps
    rw [hev.fderiv_eq]
    change fderiv ℝ (W₁ - W₀) x (1, (0, 0)) = _
    rw [(hd1.hasFDerivAt.sub hd0.hasFDerivAt).fderiv]
    rfl
  obtain ⟨M, hM, hV_sm, _, hb0, hb1⟩ := uniform_train_C1 hreg (T := τ₀ + 2) (by linarith)
  have hz := classical_oseen_zero_on_Ioo hreg (by linarith [hτ.1] : 0 ≤ τ) hsm
    (fun x hx => by dsimp only [δ]; rw [hW₁.periodic x (hsub₁ hx), hW₀.periodic x (hsub₀ hx)])
    (fun x hx => by
      have h1 := hpd_comb ![0] (x := x) ⟨hx, trivial⟩
      have h2 := hpd_comb ![1] (x := x) ⟨hx, trivial⟩
      change F8U.pd 0 δ x = _ at h1
      change F8U.pd 1 δ x = _ at h2
      rw [h1, h2]
      simp only [PiLp.sub_apply]
      calc (F8U.pd 0 W₁ x 0 - F8U.pd 0 W₀ x 0) + (F8U.pd 1 W₁ x 1 - F8U.pd 1 W₀ x 1)
          = (F8U.pd 0 W₁ x 0 + F8U.pd 1 W₁ x 1) - (F8U.pd 0 W₀ x 0 + F8U.pd 1 W₀ x 1) := by ring
        _ = 0 := by rw [hW₁.div_free x (hsub₁ hx), hW₀.div_free x (hsub₀ hx), sub_zero])
    (fun s hs => by
      have heq : F8U.slice δ s = fun y => W₁ (s, y) - W₀ (s, y) := by
        funext y; simp [F8U.slice, δ, sub_eq_add_neg]
      rw [heq]
      exact (hW₁.memL2 s (hsub₁ hs) 0 (by decide) ![]).sub
        (hW₀.memL2 s (hsub₀ hs) 0 (by decide) ![]))
    (fun s hs i => by
      have heq : F8U.slice (F8U.pd i δ) s = fun y => F8U.pd i W₁ (s, y) - F8U.pd i W₀ (s, y) :=
        funext fun y => hpd_comb ![i] ⟨hs, trivial⟩
      rw [heq]
      exact (hW₁.memL2 s (hsub₁ hs) 1 (by decide) ![i]).sub
        (hW₀.memL2 s (hsub₀ hs) 1 (by decide) ![i]))
    (fun s hs i j => by
      have heq : F8U.slice (F8U.pd i (F8U.pd j δ)) s =
          fun y => F8U.pd i (F8U.pd j W₁) (s, y) - F8U.pd i (F8U.pd j W₀) (s, y) :=
        funext fun y => hpd_comb ![i, j] ⟨hs, trivial⟩
      rw [heq]
      exact (hW₁.memL2 s (hsub₁ hs) 2 (by decide) ![i, j]).sub
        (hW₀.memL2 s (hsub₀ hs) 2 (by decide) ![i, j]))
    (fun s hs => by
      have heq : F8U.slice (F8U.ps δ) s = fun y => F8U.ps W₁ (s, y) - F8U.ps W₀ (s, y) :=
        funext fun y => hps_comb ⟨hs, trivial⟩
      rw [heq]
      exact (hW₁.memL2_s s (hsub₁ hs) 0 (by decide) ![]).sub
        (hW₀.memL2_s s (hsub₀ hs) 0 (by decide) ![]))
    (fun s hs => by
      have h_up : Tendsto (fun t =>
          F8U.cellL2 p.c (fun y => F8U.ps W₁ (t, y) - F8U.ps W₁ (s, y)) +
          F8U.cellL2 p.c (fun y => F8U.ps W₀ (t, y) - F8U.ps W₀ (s, y))) (𝓝 s) (𝓝 0) := by
        have c1 := hW₁.cont_s s (hsub₁ hs) 0 (by decide) ![]
        have c0 := hW₀.cont_s s (hsub₀ hs) 0 (by decide) ![]
        dsimp only [F8U.pdIter] at c1 c0
        simpa using c1.add c0
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_up
        (Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
      have hfn : (fun y => F8U.ps δ (t, y) - F8U.ps δ (s, y)) =
          fun y => (F8U.ps W₁ (t, y) - F8U.ps W₁ (s, y)) -
            (F8U.ps W₀ (t, y) - F8U.ps W₀ (s, y)) := by
        funext y
        rw [hps_comb ⟨ht, trivial⟩, hps_comb ⟨hs, trivial⟩]
        abel
      unfold F8U.cellL2
      rw [hfn]
      exact eLpNorm_sub_le
        ((hW₁.memL2_s t (hsub₁ ht) 0 (by decide) ![]).sub
          (hW₁.memL2_s s (hsub₁ hs) 0 (by decide) ![])).aestronglyMeasurable
        ((hW₀.memL2_s t (hsub₀ ht) 0 (by decide) ![]).sub
          (hW₀.memL2_s s (hsub₀ hs) 0 (by decide) ![])).aestronglyMeasurable one_le_two)
    (fun s hs φ hφ_L2 hφ_sol => by
      have hs_icc : s ∈ Icc (0 : ℝ) (τ₀ + 2) := ⟨by linarith [hτ.1, hs.1], hs.2.le⟩
      have hres_eq : ∀ y, F8U.homResidual p δ (s, y) =
          F8U.homResidual p W₁ (s, y) - F8U.homResidual p W₀ (s, y) := by
        intro y
        have hps := hps_comb (x := (s, y)) ⟨hs, trivial⟩
        have h00 := hpd_comb ![0, 0] (x := (s, y)) ⟨hs, trivial⟩
        have h11 := hpd_comb ![1, 1] (x := (s, y)) ⟨hs, trivial⟩
        have h10 := hpd_comb ![0] (x := (s, y)) ⟨hs, trivial⟩
        have h01 := hpd_comb ![1] (x := (s, y)) ⟨hs, trivial⟩
        change F8U.pd 0 (F8U.pd 0 δ) (s, y) =
          F8U.pd 0 (F8U.pd 0 W₁) (s, y) - F8U.pd 0 (F8U.pd 0 W₀) (s, y) at h00
        change F8U.pd 1 (F8U.pd 1 δ) (s, y) =
          F8U.pd 1 (F8U.pd 1 W₁) (s, y) - F8U.pd 1 (F8U.pd 1 W₀) (s, y) at h11
        change F8U.pd 0 δ (s, y) = F8U.pd 0 W₁ (s, y) - F8U.pd 0 W₀ (s, y) at h10
        change F8U.pd 1 δ (s, y) = F8U.pd 1 W₁ (s, y) - F8U.pd 1 W₀ (s, y) at h01
        unfold F8U.homResidual
        rw [hps, h00, h11]
        ext i
        simp only [flatBv, h10, h01, δ, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
          Complex.real_smul, Complex.ofReal_one, Complex.ofReal_neg, one_mul, neg_one_mul]
        ring
      have hmR1 : MemLp (fun y => F8U.homResidual p W₁ (s, y)) 2 (F8Sm.cellMeas p.c) := by
        have hm_bv := (memLp_and_cellL2_bvTripleSlice hM (hV_sm s hs_icc)
          (hb0 s hs_icc) (hb1 s hs_icc) (hW₁.memL2 s (hsub₁ hs) 0 (by decide) ![])
          (hW₁.memL2 s (hsub₁ hs) 1 (by decide) ![0])
          (hW₁.memL2 s (hsub₁ hs) 1 (by decide) ![1])).1
        exact ((hW₁.memL2_s s (hsub₁ hs) 0 (by decide) ![]).sub
          (((hW₁.memL2 s (hsub₁ hs) 2 (by decide) ![0, 0]).add
            (hW₁.memL2 s (hsub₁ hs) 2 (by decide) ![1, 1])).const_smul p.ν)).add hm_bv
      have hmR0 : MemLp (fun y => F8U.homResidual p W₀ (s, y)) 2 (F8Sm.cellMeas p.c) := by
        have hm_bv := (memLp_and_cellL2_bvTripleSlice hM (hV_sm s hs_icc)
          (hb0 s hs_icc) (hb1 s hs_icc) (hW₀.memL2 s (hsub₀ hs) 0 (by decide) ![])
          (hW₀.memL2 s (hsub₀ hs) 1 (by decide) ![0])
          (hW₀.memL2 s (hsub₀ hs) 1 (by decide) ![1])).1
        exact ((hW₀.memL2_s s (hsub₀ hs) 0 (by decide) ![]).sub
          (((hW₀.memL2 s (hsub₀ hs) 2 (by decide) ![0, 0]).add
            (hW₀.memL2 s (hsub₀ hs) 2 (by decide) ![1, 1])).const_smul p.ν)).add hm_bv
      have hpt : (fun y => inner ℂ (φ y) (F8U.homResidual p δ (s, y))) =
          fun y => inner ℂ (φ y) (F8U.homResidual p W₁ (s, y)) -
            inner ℂ (φ y) (F8U.homResidual p W₀ (s, y)) := by
        funext y; rw [hres_eq y, inner_sub_right]
      rw [hpt, integral_sub (F8Sm.integrableOn_inner_cell hφ_L2 hmR1)
          (F8Sm.integrableOn_inner_cell hφ_L2 hmR0),
        hW₁.projected s (hsub₁ hs) φ hφ_L2 hφ_sol,
        hW₀.projected s (hsub₀ hs) φ hφ_L2 hφ_sol, sub_zero])
    (by
      have h1 : Tendsto (fun s => F8U.cellL2 p.c (fun y => W₁ (s, y) - W₀ (τ, y)))
          (𝓝[>] τ) (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hW₁.initial
          (Eventually.of_forall fun _ => bot_le) ?_
        filter_upwards with s
        exact le_self_add.trans le_self_add
      have h2 : Tendsto (fun s => F8U.cellL2 p.c (fun y => W₀ (s, y) - W₀ (τ, y)))
          (𝓝[>] τ) (𝓝 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds (hW₀.cont τ hτ 0 (by decide) ![])
      have hsum : Tendsto (fun s => F8U.cellL2 p.c (fun y => W₁ (s, y) - W₀ (τ, y)) +
          F8U.cellL2 p.c (fun y => W₀ (s, y) - W₀ (τ, y))) (𝓝[>] τ) (𝓝 0) := by
        simpa using h1.add h2
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
        (Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards [Ioo_mem_nhdsGT hτ.2] with s hs
      have hfn : F8U.slice δ s =
          fun y => (W₁ (s, y) - W₀ (τ, y)) - (W₀ (s, y) - W₀ (τ, y)) := by
        funext y; simp [F8U.slice, δ, sub_eq_add_neg]
      unfold F8U.cellL2
      rw [hfn]
      exact eLpNorm_sub_le
        ((hW₁.memL2 s (hsub₁ hs) 0 (by decide) ![]).sub
          (hW₀.memL2 τ hτ 0 (by decide) ![])).aestronglyMeasurable
        ((hW₀.memL2 s (hsub₀ hs) 0 (by decide) ![]).sub
          (hW₀.memL2 τ hτ 0 (by decide) ![])).aestronglyMeasurable one_le_two)
  intro x hx
  obtain ⟨z0, z1, z2⟩ := hz x hx
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · simp only [δ, one_smul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at z0
    exact z0
  · have := hpd_comb ![i] hx
    change F8U.pd i δ x = _ at this
    rw [z1 i] at this
    exact sub_eq_zero.1 this.symm
  · have := hpd_comb ![i, j] hx
    change F8U.pd i (F8U.pd j δ) x = _ at this
    rw [z2 i j] at this
    exact sub_eq_zero.1 this.symm

lemma orbit_memLp_0 {p : Params} {σ : ℝ} {W : CProf} {u uq uη : B0579.Plane → CMerid}
    (hW : F8U.IsCylOseenOrbit p σ W u uq uη) {t : ℝ} (ht : t ∈ Ioo σ (σ + 2)) :
    MemLp (F8U.slice W t) 2 (F8Sm.cellMeas p.c) :=
  hW.memL2 t ht 0 (by decide) ![]

lemma orbit_memLp_1 {p : Params} {σ : ℝ} {W : CProf} {u uq uη : B0579.Plane → CMerid}
    (hW : F8U.IsCylOseenOrbit p σ W u uq uη) {t : ℝ} (ht : t ∈ Ioo σ (σ + 2)) (i : Fin 2) :
    MemLp (F8U.slice (F8U.pd i W) t) 2 (F8Sm.cellMeas p.c) :=
  hW.memL2 t ht 1 (by decide) ![i]

lemma orbit_memLp_2 {p : Params} {σ : ℝ} {W : CProf} {u uq uη : B0579.Plane → CMerid}
    (hW : F8U.IsCylOseenOrbit p σ W u uq uη) {t : ℝ} (ht : t ∈ Ioo σ (σ + 2)) (i j : Fin 2) :
    MemLp (F8U.slice (F8U.pd i (F8U.pd j W)) t) 2 (F8Sm.cellMeas p.c) :=
  hW.memL2 t ht 2 (by decide) ![i, j]

private lemma fin2_double_le_sum (F : Fin 2 → Fin 2 → ℝ)
    (hF : ∀ a b, 0 ≤ F a b) (i j : Fin 2) :
    F i j ≤ ∑ a : Fin 2, ∑ b : Fin 2, F a b := by
  simp only [Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> dsimp <;> linarith [hF 0 0, hF 0 1, hF 1 0, hF 1 1]

open Classical in
/-- Chosen classical Oseen orbit starting at age `τ` from `v : X3 p.c` (`0` outside domain). -/
def orbitOf {A : ℝ} {p : Params} (hflow : F8U.CylOseenFlowBound A p)
    (τ : ℝ) (v : X3 p.c) : CProf :=
  if h : 0 ≤ τ ∧ v ∈ H1Set p.c then (hflow τ h.1 v.1 v.2.1 v.2.2 h.2).1.choose else 0

lemma isCylOseenOrbit_orbitOf {A : ℝ} {p : Params} (hflow : F8U.CylOseenFlowBound A p)
    {τ : ℝ} (hτ : 0 ≤ τ) {v : X3 p.c} (hv : v ∈ H1Set p.c) :
    F8U.IsCylOseenOrbit p τ (orbitOf hflow τ v) v.1 v.2.1 v.2.2 := by
  have h : 0 ≤ τ ∧ v ∈ H1Set p.c := ⟨hτ, hv⟩
  rw [orbitOf, dite_eq_left_of_eq_true (eq_true h)]
  exact (hflow τ hτ v.1 v.2.1 v.2.2 hv).1.choose_spec

open Classical in
/-- Non-autonomous propagator `S_0(t, τ) v` in `X3 p.c` (`0` outside `0 ≤ τ < t < τ + 2` or
`v ∉ H1Set p.c`). -/
def S0Val {A : ℝ} {p : Params} (hflow : F8U.CylOseenFlowBound A p)
    (t τ : ℝ) (v : X3 p.c) : X3 p.c :=
  if 0 ≤ τ ∧ t ∈ Ioo τ (τ + 2) ∧ v ∈ H1Set p.c then
    (UnforcedLeray.BochnerTime.toPathLq 2 (F8Sm.cellMeas p.c) (orbitOf hflow τ v) t,
     UnforcedLeray.BochnerTime.toPathLq 2 (F8Sm.cellMeas p.c) (F8U.pd 0 (orbitOf hflow τ v)) t,
     UnforcedLeray.BochnerTime.toPathLq 2 (F8Sm.cellMeas p.c) (F8U.pd 1 (orbitOf hflow τ v)) t)
  else 0

open Classical in
/-- Second spatial derivative propagator `∂_i ∂_j S_0(t, τ) v` in `L2Cell p.c`. -/
def SD2Val {A : ℝ} {p : Params} (hflow : F8U.CylOseenFlowBound A p)
    (i j : Fin 2) (t τ : ℝ) (v : X3 p.c) : L2Cell p.c :=
  if 0 ≤ τ ∧ t ∈ Ioo τ (τ + 2) ∧ v ∈ H1Set p.c then
    UnforcedLeray.BochnerTime.toPathLq 2 (F8Sm.cellMeas p.c)
      (F8U.pd i (F8U.pd j (orbitOf hflow τ v))) t
  else 0

lemma S0Val_of_cond {A : ℝ} {p : Params} (hflow : F8U.CylOseenFlowBound A p)
    {t τ : ℝ} {v : X3 p.c} (hτ : 0 ≤ τ) (ht : t ∈ Ioo τ (τ + 2)) (hv : v ∈ H1Set p.c) :
    S0Val hflow t τ v =
      ((orbit_memLp_0 (isCylOseenOrbit_orbitOf hflow hτ hv) ht).toLp
          (F8U.slice (orbitOf hflow τ v) t),
       (orbit_memLp_1 (isCylOseenOrbit_orbitOf hflow hτ hv) ht 0).toLp
          (F8U.slice (F8U.pd 0 (orbitOf hflow τ v)) t),
       (orbit_memLp_1 (isCylOseenOrbit_orbitOf hflow hτ hv) ht 1).toLp
          (F8U.slice (F8U.pd 1 (orbitOf hflow τ v)) t)) := by
  have hc : 0 ≤ τ ∧ t ∈ Ioo τ (τ + 2) ∧ v ∈ H1Set p.c := ⟨hτ, ht, hv⟩
  have hw := isCylOseenOrbit_orbitOf hflow hτ hv
  have m0 : MemLp (fun y => orbitOf hflow τ v (t, y)) 2 (F8Sm.cellMeas p.c) :=
    orbit_memLp_0 hw ht
  have m10 : MemLp (fun y => F8U.pd 0 (orbitOf hflow τ v) (t, y)) 2 (F8Sm.cellMeas p.c) :=
    orbit_memLp_1 hw ht 0
  have m11 : MemLp (fun y => F8U.pd 1 (orbitOf hflow τ v) (t, y)) 2 (F8Sm.cellMeas p.c) :=
    orbit_memLp_1 hw ht 1
  simp only [S0Val, hc, and_self, ↓reduceIte]
  rw [UnforcedLeray.BochnerTime.toPathLq_of_memLp m0,
    UnforcedLeray.BochnerTime.toPathLq_of_memLp m10,
    UnforcedLeray.BochnerTime.toPathLq_of_memLp m11]
  rfl

lemma SD2Val_of_cond {A : ℝ} {p : Params} (hflow : F8U.CylOseenFlowBound A p)
    (i j : Fin 2) {t τ : ℝ} {v : X3 p.c}
    (hτ : 0 ≤ τ) (ht : t ∈ Ioo τ (τ + 2)) (hv : v ∈ H1Set p.c) :
    SD2Val hflow i j t τ v =
      (orbit_memLp_2 (isCylOseenOrbit_orbitOf hflow hτ hv) ht i j).toLp
        (F8U.slice (F8U.pd i (F8U.pd j (orbitOf hflow τ v))) t) := by
  have hc : 0 ≤ τ ∧ t ∈ Ioo τ (τ + 2) ∧ v ∈ H1Set p.c := ⟨hτ, ht, hv⟩
  have m2 : MemLp (fun y => F8U.pd i (F8U.pd j (orbitOf hflow τ v)) (t, y)) 2
      (F8Sm.cellMeas p.c) := orbit_memLp_2 (isCylOseenOrbit_orbitOf hflow hτ hv) ht i j
  simp only [SD2Val, hc, and_self, ↓reduceIte]
  rw [UnforcedLeray.BochnerTime.toPathLq_of_memLp m2]
  rfl

/-- Representation of `S0Val` and `SD2Val` by *any* `IsCylOseenOrbit` from `v`. -/
lemma S0Val_and_SD2Val_eq_of_orbit {dm dp : ℝ} {p : Params} {d A : ℝ}
    (hreg : BgRegime p d dm dp) (hflow : F8U.CylOseenFlowBound A p)
    {τ t : ℝ} (hτ : 0 ≤ τ) (ht : t ∈ Ioo τ (τ + 2))
    {v : X3 p.c} (hv : v ∈ H1Set p.c)
    {W : CProf} {u uq uη : B0579.Plane → CMerid}
    (hu : v.1 =ᵐ[F8Sm.cellMeas p.c] u)
    (huq : v.2.1 =ᵐ[F8Sm.cellMeas p.c] uq)
    (huη : v.2.2 =ᵐ[F8Sm.cellMeas p.c] uη)
    (hW : F8U.IsCylOseenOrbit p τ W u uq uη) :
    S0Val hflow t τ v =
      ((orbit_memLp_0 hW ht).toLp (F8U.slice W t),
       (orbit_memLp_1 hW ht 0).toLp (F8U.slice (F8U.pd 0 W) t),
       (orbit_memLp_1 hW ht 1).toLp (F8U.slice (F8U.pd 1 W) t)) ∧
    ∀ i j : Fin 2, SD2Val hflow i j t τ v =
      (orbit_memLp_2 hW ht i j).toLp (F8U.slice (F8U.pd i (F8U.pd j W)) t) := by
  have hw := isCylOseenOrbit_orbitOf hflow hτ hv
  have huniq := isCylOseenOrbit_unique hreg hτ hv hu huq huη hw hW
  refine ⟨?_, fun i j => ?_⟩
  · rw [S0Val_of_cond hflow hτ ht hv]
    ext1
    · apply Lp.ext_iff.2
      filter_upwards [(orbit_memLp_0 hw ht).coeFn_toLp, (orbit_memLp_0 hW ht).coeFn_toLp]
        with y hy1 hy2
      rw [hy1, hy2]
      exact (huniq (t, y) ⟨ht, trivial⟩).1
    · ext1
      · apply Lp.ext_iff.2
        filter_upwards [(orbit_memLp_1 hw ht 0).coeFn_toLp, (orbit_memLp_1 hW ht 0).coeFn_toLp]
          with y hy1 hy2
        rw [hy1, hy2]
        exact (huniq (t, y) ⟨ht, trivial⟩).2.1 0
      · apply Lp.ext_iff.2
        filter_upwards [(orbit_memLp_1 hw ht 1).coeFn_toLp, (orbit_memLp_1 hW ht 1).coeFn_toLp]
          with y hy1 hy2
        rw [hy1, hy2]
        exact (huniq (t, y) ⟨ht, trivial⟩).2.1 1
  · rw [SD2Val_of_cond hflow i j hτ ht hv]
    apply Lp.ext_iff.2
    filter_upwards [(orbit_memLp_2 hw ht i j).coeFn_toLp, (orbit_memLp_2 hW ht i j).coeFn_toLp]
      with y hy1 hy2
    rw [hy1, hy2]
    exact (huniq (t, y) ⟨ht, trivial⟩).2.2 i j

@[simp]
lemma S0Val_zero {dm dp : ℝ} {p : Params} {d A : ℝ}
    (hreg : BgRegime p d dm dp) (hflow : F8U.CylOseenFlowBound A p) (t τ : ℝ) :
    S0Val hflow t τ 0 = 0 := by
  by_cases h : 0 ≤ τ ∧ t ∈ Ioo τ (τ + 2)
  · have hz := isCylOseenOrbit_zero p τ
    obtain ⟨h0, _⟩ := S0Val_and_SD2Val_eq_of_orbit hreg hflow h.1 h.2 (zero_mem_H1Set p.c)
      (Lp.coeFn_zero CMerid 2 (F8Sm.cellMeas p.c))
      (Lp.coeFn_zero CMerid 2 (F8Sm.cellMeas p.c))
      (Lp.coeFn_zero CMerid 2 (F8Sm.cellMeas p.c)) hz
    rw [h0]
    ext1
    · apply Lp.ext_iff.2
      filter_upwards [(orbit_memLp_0 hz h.2).coeFn_toLp,
        Lp.coeFn_zero CMerid 2 (F8Sm.cellMeas p.c)] with y hy1 hy0
      simp only [Prod.fst_zero]
      rw [hy1, hy0]; rfl
    · ext1
      · apply Lp.ext_iff.2
        filter_upwards [(orbit_memLp_1 hz h.2 0).coeFn_toLp,
          Lp.coeFn_zero CMerid 2 (F8Sm.cellMeas p.c)] with y hy1 hy0
        simp only [Prod.snd_zero, Prod.fst_zero]
        rw [hy1, hy0]; simp [F8U.slice, pd_zero_prof]
      · apply Lp.ext_iff.2
        filter_upwards [(orbit_memLp_1 hz h.2 1).coeFn_toLp,
          Lp.coeFn_zero CMerid 2 (F8Sm.cellMeas p.c)] with y hy1 hy0
        simp only [Prod.snd_zero]
        rw [hy1, hy0]; simp [F8U.slice, pd_zero_prof]
  · have hn : ¬(0 ≤ τ ∧ t ∈ Ioo τ (τ + 2) ∧ (0 : X3 p.c) ∈ H1Set p.c) :=
      fun hc => h ⟨hc.1, hc.2.1⟩
    simp only [S0Val, hn, ↓reduceIte]

@[simp]
lemma SD2Val_zero {dm dp : ℝ} {p : Params} {d A : ℝ}
    (hreg : BgRegime p d dm dp) (hflow : F8U.CylOseenFlowBound A p) (i j : Fin 2) (t τ : ℝ) :
    SD2Val hflow i j t τ 0 = 0 := by
  by_cases h : 0 ≤ τ ∧ t ∈ Ioo τ (τ + 2)
  · have hz := isCylOseenOrbit_zero p τ
    obtain ⟨_, hd2⟩ := S0Val_and_SD2Val_eq_of_orbit hreg hflow h.1 h.2 (zero_mem_H1Set p.c)
      (Lp.coeFn_zero CMerid 2 (F8Sm.cellMeas p.c))
      (Lp.coeFn_zero CMerid 2 (F8Sm.cellMeas p.c))
      (Lp.coeFn_zero CMerid 2 (F8Sm.cellMeas p.c)) hz
    rw [hd2 i j]
    apply Lp.ext_iff.2
    filter_upwards [(orbit_memLp_2 hz h.2 i j).coeFn_toLp,
      Lp.coeFn_zero CMerid 2 (F8Sm.cellMeas p.c)] with y hy1 hy0
    rw [hy1, hy0]; simp [F8U.slice, pd_zero_prof]
  · have hn : ¬(0 ≤ τ ∧ t ∈ Ioo τ (τ + 2) ∧ (0 : X3 p.c) ∈ H1Set p.c) :=
      fun hc => h ⟨hc.1, hc.2.1⟩
    simp only [SD2Val, hn, ↓reduceIte]

lemma S0Val_mem_H1Set {A : ℝ} {p : Params} (hc : 0 < p.c) (hflow : F8U.CylOseenFlowBound A p)
    (t τ : ℝ) (v : X3 p.c) :
    S0Val hflow t τ v ∈ H1Set p.c := by
  by_cases h : 0 ≤ τ ∧ t ∈ Ioo τ (τ + 2) ∧ v ∈ H1Set p.c
  · rw [S0Val_of_cond hflow h.1 h.2.1 h.2.2]
    exact datumToX3_mem_H1Set
      (orbit_slice_isCylH1Datum hc (isCylOseenOrbit_orbitOf hflow h.1 h.2.2) h.2.1)
  · simp only [S0Val, h, ↓reduceIte]
    exact zero_mem_H1Set p.c

lemma S0Val_and_SD2Val_comb {dm dp : ℝ} {p : Params} {d A : ℝ}
    (hreg : BgRegime p d dm dp) (hflow : F8U.CylOseenFlowBound A p)
    (t τ : ℝ) {u v : X3 p.c} (hu : u ∈ H1Set p.c) (hv : v ∈ H1Set p.c) (a b : ℝ) :
    S0Val hflow t τ (a • u + b • v) = a • S0Val hflow t τ u + b • S0Val hflow t τ v ∧
    ∀ i j : Fin 2,
      SD2Val hflow i j t τ (a • u + b • v) =
        a • SD2Val hflow i j t τ u + b • SD2Val hflow i j t τ v := by
  have huv : a • u + b • v ∈ H1Set p.c :=
    add_mem_H1Set (smul_mem_H1Set a hu) (smul_mem_H1Set b hv)
  by_cases h : 0 ≤ τ ∧ t ∈ Ioo τ (τ + 2)
  · have hWu := isCylOseenOrbit_orbitOf hflow h.1 hu
    have hWv := isCylOseenOrbit_orbitOf hflow h.1 hv
    have hcomb := isCylOseenOrbit_comb hreg h.1 hu hv hWu hWv a b
    have hae_c : ∀ (x y : L2Cell p.c),
        ((a • x + b • y : L2Cell p.c) : B0579.Plane → CMerid) =ᵐ[F8Sm.cellMeas p.c]
          fun z => a • x z + b • y z := by
      intro x y
      filter_upwards [Lp.coeFn_add (a • x) (b • y), Lp.coeFn_smul a x, Lp.coeFn_smul b y]
        with z hadd hsa hsb
      simp only [Pi.add_apply, Pi.smul_apply] at hadd hsa hsb ⊢
      rw [hadd, hsa, hsb]
    obtain ⟨hs0, hsd2⟩ := S0Val_and_SD2Val_eq_of_orbit hreg hflow h.1 h.2 huv
      (hae_c u.1 v.1) (hae_c u.2.1 v.2.1) (hae_c u.2.2 v.2.2) hcomb
    have toLp_comb : ∀ {f g k : B0579.Plane → CMerid}
        (hf : MemLp f 2 (F8Sm.cellMeas p.c)) (hg : MemLp g 2 (F8Sm.cellMeas p.c))
        (hk : MemLp k 2 (F8Sm.cellMeas p.c)),
        (∀ y, k y = a • f y + b • g y) →
        hk.toLp k = a • hf.toLp f + b • hg.toLp g := by
      intro f g k hf hg hk hpt
      apply Lp.ext_iff.2
      filter_upwards [hk.coeFn_toLp, Lp.coeFn_add (a • hf.toLp f) (b • hg.toLp g),
        Lp.coeFn_smul a (hf.toLp f), Lp.coeFn_smul b (hg.toLp g),
        hf.coeFn_toLp, hg.coeFn_toLp] with y hyk hadd hsa hsb hyf hyg
      simp only [Pi.add_apply, Pi.smul_apply] at hadd hsa hsb ⊢
      rw [hyk, hadd, hsa, hsb, hyf, hyg, hpt y]
    refine ⟨?_, fun i j => ?_⟩
    · rw [hs0, S0Val_of_cond hflow h.1 h.2 hu, S0Val_of_cond hflow h.1 h.2 hv]
      ext1
      · exact toLp_comb (orbit_memLp_0 hWu h.2) (orbit_memLp_0 hWv h.2)
          (orbit_memLp_0 hcomb h.2) fun y => rfl
      · ext1
        · exact toLp_comb (orbit_memLp_1 hWu h.2 0) (orbit_memLp_1 hWv h.2 0)
            (orbit_memLp_1 hcomb h.2 0) fun y =>
              pdIter_comb_on_strip hWu.smooth hWv.smooth a b ![0] ⟨h.2, trivial⟩
        · exact toLp_comb (orbit_memLp_1 hWu h.2 1) (orbit_memLp_1 hWv h.2 1)
            (orbit_memLp_1 hcomb h.2 1) fun y =>
              pdIter_comb_on_strip hWu.smooth hWv.smooth a b ![1] ⟨h.2, trivial⟩
    · rw [hsd2 i j, SD2Val_of_cond hflow i j h.1 h.2 hu, SD2Val_of_cond hflow i j h.1 h.2 hv]
      exact toLp_comb (orbit_memLp_2 hWu h.2 i j) (orbit_memLp_2 hWv h.2 i j)
        (orbit_memLp_2 hcomb h.2 i j) fun y =>
          pdIter_comb_on_strip hWu.smooth hWv.smooth a b ![i, j] ⟨h.2, trivial⟩
  · have n1 : ¬(0 ≤ τ ∧ t ∈ Ioo τ (τ + 2) ∧ a • u + b • v ∈ H1Set p.c) :=
      fun hc => h ⟨hc.1, hc.2.1⟩
    have n2 : ¬(0 ≤ τ ∧ t ∈ Ioo τ (τ + 2) ∧ u ∈ H1Set p.c) := fun hc => h ⟨hc.1, hc.2.1⟩
    have n3 : ¬(0 ≤ τ ∧ t ∈ Ioo τ (τ + 2) ∧ v ∈ H1Set p.c) := fun hc => h ⟨hc.1, hc.2.1⟩
    refine ⟨?_, fun i j => ?_⟩
    · rw [S0Val, S0Val, S0Val]
      simp only [n1, n2, n3, ↓reduceIte, smul_zero, add_zero]
    · rw [SD2Val, SD2Val, SD2Val]
      simp only [n1, n2, n3, ↓reduceIte, smul_zero, add_zero]

lemma S0Val_sub {dm dp : ℝ} {p : Params} {d A : ℝ}
    (hreg : BgRegime p d dm dp) (hflow : F8U.CylOseenFlowBound A p)
    (t τ : ℝ) {u v : X3 p.c} (hu : u ∈ H1Set p.c) (hv : v ∈ H1Set p.c) :
    S0Val hflow t τ (u - v) = S0Val hflow t τ u - S0Val hflow t τ v := by
  have := (S0Val_and_SD2Val_comb hreg hflow t τ hu hv 1 (-1)).1
  simpa [sub_eq_add_neg] using this

lemma SD2Val_sub {dm dp : ℝ} {p : Params} {d A : ℝ}
    (hreg : BgRegime p d dm dp) (hflow : F8U.CylOseenFlowBound A p)
    (i j : Fin 2) (t τ : ℝ) {u v : X3 p.c} (hu : u ∈ H1Set p.c) (hv : v ∈ H1Set p.c) :
    SD2Val hflow i j t τ (u - v) = SD2Val hflow i j t τ u - SD2Val hflow i j t τ v := by
  have := (S0Val_and_SD2Val_comb hreg hflow t τ hu hv 1 (-1)).2 i j
  simpa [sub_eq_add_neg] using this

/-- Unit-window `H¹ → H¹` and `H¹ → H²` flow bounds in both `ENNReal` and `Real` forms. -/
lemma S0Val_and_SD2Val_bounds {A : ℝ} (hA : 0 < A) {p : Params} (hν : 0 < p.ν)
    (hflow : F8U.CylOseenFlowBound A p)
    {τ t : ℝ} (hτ : 0 ≤ τ) (ht : t ∈ Ioc τ (τ + 1)) {v : X3 p.c} (hv : v ∈ H1Set p.c) :
    h1ENN (S0Val hflow t τ v) ≤ ENNReal.ofReal A * h1ENN v ∧
    h1RealNorm (S0Val hflow t τ v) ≤ A * h1RealNorm v ∧
    ∑ i : Fin 2, ∑ j : Fin 2, ENNReal.ofReal ‖SD2Val hflow i j t τ v‖ ≤
      ENNReal.ofReal (A * p.ν ^ (-1 / 2 : ℝ) * (t - τ) ^ (-1 / 2 : ℝ)) * h1ENN v ∧
    ∑ i : Fin 2, ∑ j : Fin 2, ‖SD2Val hflow i j t τ v‖ ≤
      A * p.ν ^ (-1 / 2 : ℝ) * (t - τ) ^ (-1 / 2 : ℝ) * h1RealNorm v := by
  have ht2 : t ∈ Ioo τ (τ + 2) := ⟨ht.1, by linarith [ht.2]⟩
  have hW := isCylOseenOrbit_orbitOf hflow hτ hv
  obtain ⟨hb1, hb2⟩ := (hflow τ hτ v.1 v.2.1 v.2.2 hv).2 (orbitOf hflow τ v) hW t ht
  have heq_h1 : h1ENN (S0Val hflow t τ v) =
      F8U.cylH1 p.c (F8U.slice (orbitOf hflow τ v) t)
        (F8U.slice (F8U.pd 0 (orbitOf hflow τ v)) t)
        (F8U.slice (F8U.pd 1 (orbitOf hflow τ v)) t) := by
    rw [S0Val_of_cond hflow hτ ht2 hv]
    unfold h1ENN F8U.cylH1 F8U.cellL2
    rw [eLpNorm_congr_ae (orbit_memLp_0 hW ht2).coeFn_toLp,
      eLpNorm_congr_ae (orbit_memLp_1 hW ht2 0).coeFn_toLp,
      eLpNorm_congr_ae (orbit_memLp_1 hW ht2 1).coeFn_toLp]
  have heq_d2 : ∀ i j : Fin 2,
      ENNReal.ofReal ‖SD2Val hflow i j t τ v‖ =
        F8U.cellL2 p.c (F8U.slice (F8U.pd i (F8U.pd j (orbitOf hflow τ v))) t) := by
    intro i j
    rw [← cellL2_coe_eq_ofReal_norm, SD2Val_of_cond hflow i j hτ ht2 hv]
    exact eLpNorm_congr_ae (orbit_memLp_2 hW ht2 i j).coeFn_toLp
  rw [← heq_h1] at hb1
  change _ ≤ ENNReal.ofReal A * h1ENN v at hb1
  have hb2' : ∑ i : Fin 2, ∑ j : Fin 2, ENNReal.ofReal ‖SD2Val hflow i j t τ v‖ ≤
      ENNReal.ofReal (A * p.ν ^ (-1 / 2 : ℝ) * (t - τ) ^ (-1 / 2 : ℝ)) * h1ENN v := by
    simp_rw [heq_d2]
    exact hb2
  have hb1_real : h1RealNorm (S0Val hflow t τ v) ≤ A * h1RealNorm v := by
    rw [h1ENN_eq_ofReal, h1ENN_eq_ofReal, ← ENNReal.ofReal_mul hA.le] at hb1
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA.le (h1RealNorm_nonneg v))).1 hb1
  have hC_nn : 0 ≤ A * p.ν ^ (-1 / 2 : ℝ) * (t - τ) ^ (-1 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg hA.le (Real.rpow_nonneg hν.le _))
      (Real.rpow_nonneg (sub_pos.2 ht.1).le _)
  have hb2_real : ∑ i : Fin 2, ∑ j : Fin 2, ‖SD2Val hflow i j t τ v‖ ≤
      A * p.ν ^ (-1 / 2 : ℝ) * (t - τ) ^ (-1 / 2 : ℝ) * h1RealNorm v := by
    have hlhs : ∑ i : Fin 2, ∑ j : Fin 2, ENNReal.ofReal ‖SD2Val hflow i j t τ v‖ =
        ENNReal.ofReal (∑ i : Fin 2, ∑ j : Fin 2, ‖SD2Val hflow i j t τ v‖) := by
      simp only [Fin.sum_univ_two]
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
        ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    have h2 := hb2'
    rw [hlhs, h1ENN_eq_ofReal, ← ENNReal.ofReal_mul hC_nn] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC_nn (h1RealNorm_nonneg v))).1 h2
  exact ⟨hb1, hb1_real, hb2', hb2_real⟩

/-- Propagator Chapman–Kolmogorov identities on `0 ≤ τ₀ < τ < t < τ₀ + 2`. -/
lemma chapman_kolmogorov_S0Val_and_SD2Val {dm dp : ℝ} {p : Params} {d A : ℝ}
    (hreg : BgRegime p d dm dp) (hflow : F8U.CylOseenFlowBound A p)
    {τ₀ τ t : ℝ} (hτ₀ : 0 ≤ τ₀) (hτ : τ ∈ Ioo τ₀ (τ₀ + 2)) (ht : t ∈ Ioo τ (τ₀ + 2))
    {v : X3 p.c} (hv : v ∈ H1Set p.c) :
    S0Val hflow t τ (S0Val hflow τ τ₀ v) = S0Val hflow t τ₀ v ∧
    ∀ i j : Fin 2, SD2Val hflow i j t τ (S0Val hflow τ τ₀ v) = SD2Val hflow i j t τ₀ v := by
  have ht0 : t ∈ Ioo τ₀ (τ₀ + 2) := ⟨hτ.1.trans ht.1, ht.2⟩
  have ht1 : t ∈ Ioo τ (τ + 2) := ⟨ht.1, by linarith [hτ.1, ht.2]⟩
  have hτ_nn : 0 ≤ τ := by linarith [hτ.1]
  have hSτ_mem : S0Val hflow τ τ₀ v ∈ H1Set p.c := S0Val_mem_H1Set p.c_pos hflow τ τ₀ v
  have hW0 := isCylOseenOrbit_orbitOf hflow hτ₀ hv
  have hW1_raw := isCylOseenOrbit_orbitOf hflow hτ_nn hSτ_mem
  have hae0 : (S0Val hflow τ τ₀ v).1 =ᵐ[F8Sm.cellMeas p.c] F8U.slice (orbitOf hflow τ₀ v) τ := by
    rw [S0Val_of_cond hflow hτ₀ hτ hv]
    exact (orbit_memLp_0 hW0 hτ).coeFn_toLp
  have hae1 : (S0Val hflow τ τ₀ v).2.1 =ᵐ[F8Sm.cellMeas p.c]
      F8U.slice (F8U.pd 0 (orbitOf hflow τ₀ v)) τ := by
    rw [S0Val_of_cond hflow hτ₀ hτ hv]
    exact (orbit_memLp_1 hW0 hτ 0).coeFn_toLp
  have hae2 : (S0Val hflow τ τ₀ v).2.2 =ᵐ[F8Sm.cellMeas p.c]
      F8U.slice (F8U.pd 1 (orbitOf hflow τ₀ v)) τ := by
    rw [S0Val_of_cond hflow hτ₀ hτ hv]
    exact (orbit_memLp_1 hW0 hτ 1).coeFn_toLp
  have hW1 := isCylOseenOrbit_congr_datum hae0 hae1 hae2 hW1_raw
  have hck := chapman_kolmogorov_orbit hreg hτ₀ hτ hW0 hW1
  refine ⟨?_, fun i j => ?_⟩
  · rw [S0Val_of_cond hflow hτ_nn ht1 hSτ_mem, S0Val_of_cond hflow hτ₀ ht0 hv]
    ext1
    · apply Lp.ext_iff.2
      filter_upwards [(orbit_memLp_0 hW1_raw ht1).coeFn_toLp,
        (orbit_memLp_0 hW0 ht0).coeFn_toLp] with y hy1 hy0
      rw [hy1, hy0]
      exact (hck (t, y) ⟨ht, trivial⟩).1
    · ext1
      · apply Lp.ext_iff.2
        filter_upwards [(orbit_memLp_1 hW1_raw ht1 0).coeFn_toLp,
          (orbit_memLp_1 hW0 ht0 0).coeFn_toLp] with y hy1 hy0
        rw [hy1, hy0]
        exact (hck (t, y) ⟨ht, trivial⟩).2.1 0
      · apply Lp.ext_iff.2
        filter_upwards [(orbit_memLp_1 hW1_raw ht1 1).coeFn_toLp,
          (orbit_memLp_1 hW0 ht0 1).coeFn_toLp] with y hy1 hy0
        rw [hy1, hy0]
        exact (hck (t, y) ⟨ht, trivial⟩).2.1 1
  · rw [SD2Val_of_cond hflow i j hτ_nn ht1 hSτ_mem, SD2Val_of_cond hflow i j hτ₀ ht0 hv]
    apply Lp.ext_iff.2
    filter_upwards [(orbit_memLp_2 hW1_raw ht1 i j).coeFn_toLp,
      (orbit_memLp_2 hW0 ht0 i j).coeFn_toLp] with y hy1 hy0
    rw [hy1, hy0]
    exact (hck (t, y) ⟨ht, trivial⟩).2.2 i j

/-- Continuity of `t ↦ S0Val hflow t τ v` and `t ↦ SD2Val hflow i j t τ v` on `Ioo τ (τ + 2)`. -/
lemma continuousOn_S0Val_and_SD2Val_left {A : ℝ} {p : Params} (hflow : F8U.CylOseenFlowBound A p)
    {τ : ℝ} (hτ : 0 ≤ τ) {v : X3 p.c} (hv : v ∈ H1Set p.c) :
    ContinuousOn (fun t => S0Val hflow t τ v) (Ioo τ (τ + 2)) ∧
    ∀ i j : Fin 2, ContinuousOn (fun t => SD2Val hflow i j t τ v) (Ioo τ (τ + 2)) := by
  have hW := isCylOseenOrbit_orbitOf hflow hτ hv
  have hcont_iter : ∀ {n : ℕ} (hn : n ≤ 4) (α : Fin n → Fin 2),
      ContinuousOn (fun t =>
        if t ∈ Ioo τ (τ + 2) then
          UnforcedLeray.BochnerTime.toPathLq 2 (F8Sm.cellMeas p.c)
            (F8U.pdIter α (orbitOf hflow τ v)) t
        else 0) (Ioo τ (τ + 2)) := by
    intro n hn α t₀ ht₀
    refine ContinuousAt.continuousWithinAt ?_
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have htr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hW.cont t₀ ht₀ n hn α)
    rw [ENNReal.toReal_zero] at htr
    refine htr.congr' ?_
    filter_upwards [isOpen_Ioo.mem_nhds ht₀] with t ht
    have hm_t : MemLp (fun y => F8U.pdIter α (orbitOf hflow τ v) (t, y)) 2 (F8Sm.cellMeas p.c) :=
      hW.memL2 t ht n hn α
    have hm_t0 : MemLp (fun y => F8U.pdIter α (orbitOf hflow τ v) (t₀, y)) 2 (F8Sm.cellMeas p.c) :=
      hW.memL2 t₀ ht₀ n hn α
    dsimp only [Function.comp_def, F8U.cellL2]
    simp only [ht, ht₀, ↓reduceIte]
    rw [UnforcedLeray.BochnerTime.toPathLq_of_memLp hm_t,
      UnforcedLeray.BochnerTime.toPathLq_of_memLp hm_t0,
      Lp.norm_def]
    refine congrArg ENNReal.toReal (eLpNorm_congr_ae ?_)
    filter_upwards [Lp.coeFn_sub
        (hm_t.toLp (fun y => F8U.pdIter α (orbitOf hflow τ v) (t, y)))
        (hm_t0.toLp (fun y => F8U.pdIter α (orbitOf hflow τ v) (t₀, y))),
      hm_t.coeFn_toLp, hm_t0.coeFn_toLp]
      with y hsub hyt hyt0
    simp only [Pi.sub_apply] at hsub ⊢
    rw [hsub, hyt, hyt0]
  refine ⟨?_, fun i j => ?_⟩
  · refine ((hcont_iter (n := 0) (by decide) ![]).prodMk
      ((hcont_iter (n := 1) (by decide) ![0]).prodMk
        (hcont_iter (n := 1) (by decide) ![1]))).congr fun t ht => ?_
    simp only [S0Val, hτ, ht, hv, and_self, ↓reduceIte]
    rfl
  · refine (hcont_iter (n := 2) (by decide) ![i, j]).congr fun t ht => ?_
    simp only [SD2Val, hτ, ht, hv, and_self, ↓reduceIte]
    rfl

/-- Right-hand initial continuity `S0Val hflow t τ v → v` as `t → τ⁺` in `h1RealNorm` and `X3`. -/
lemma tendsto_S0Val_initial {A : ℝ} {p : Params} (hflow : F8U.CylOseenFlowBound A p)
    {τ : ℝ} (hτ : 0 ≤ τ) {v : X3 p.c} (hv : v ∈ H1Set p.c) :
    Tendsto (fun t => h1RealNorm (S0Val hflow t τ v - v)) (𝓝[>] τ) (𝓝 0) ∧
    Tendsto (fun t => S0Val hflow t τ v) (𝓝[>] τ) (𝓝 v) := by
  have hW := isCylOseenOrbit_orbitOf hflow hτ hv
  have htr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hW.initial
  rw [ENNReal.toReal_zero] at htr
  have hh1 : Tendsto (fun t => h1RealNorm (S0Val hflow t τ v - v)) (𝓝[>] τ) (𝓝 0) := by
    refine htr.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (by linarith : τ < τ + 2)] with t ht
    dsimp only [Function.comp_def]
    rw [← toReal_h1ENN]
    refine congrArg ENNReal.toReal ?_
    rw [S0Val_of_cond hflow hτ ht hv]
    unfold h1ENN F8U.cylH1
    have c1 : ∀ {f : B0579.Plane → CMerid} (hm : MemLp f 2 (F8Sm.cellMeas p.c)) (g : L2Cell p.c),
        F8U.cellL2 p.c (fun y => f y - g y) =
          F8U.cellL2 p.c (((hm.toLp f - g : L2Cell p.c) : B0579.Plane → CMerid)) := by
      intro f hm g
      refine eLpNorm_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (hm.toLp f) g, hm.coeFn_toLp] with y hsub hyf
      simp only [Pi.sub_apply] at hsub ⊢
      rw [hsub, hyf]
    exact congrArg₂ (· + ·)
      (congrArg₂ (· + ·) (c1 (orbit_memLp_0 hW ht) v.1) (c1 (orbit_memLp_1 hW ht 0) v.2.1))
      (c1 (orbit_memLp_1 hW ht 1) v.2.2)
  refine ⟨hh1, tendsto_iff_norm_sub_tendsto_zero.2 ?_⟩
  exact squeeze_zero (fun _ => norm_nonneg _) (fun t => norm_le_h1RealNorm _) hh1

/-- Right-continuity `τ → τ₀⁺` of `S0Val` and `SD2Val` on the unit triangle. -/
lemma tendsto_S0Val_and_SD2Val_right {dm dp : ℝ} {p : Params} {d A : ℝ}
    (hA : 0 < A) (hreg : BgRegime p d dm dp) (hflow : F8U.CylOseenFlowBound A p)
    {σ t τ₀ : ℝ} (hσ : 0 ≤ σ) (h1 : σ < τ₀) (h2 : τ₀ < t) (h3 : t < σ + 1)
    {v : X3 p.c} (hv : v ∈ H1Set p.c) :
    Tendsto (fun τ => S0Val hflow t τ v) (𝓝[>] τ₀) (𝓝 (S0Val hflow t τ₀ v)) ∧
    ∀ i j : Fin 2, Tendsto (fun τ => SD2Val hflow i j t τ v) (𝓝[>] τ₀)
      (𝓝 (SD2Val hflow i j t τ₀ v)) := by
  have hτ₀_nn : 0 ≤ τ₀ := by linarith
  have hinit := (tendsto_S0Val_initial hflow hτ₀_nn hv).1
  have hmid : τ₀ < (τ₀ + t) / 2 := by linarith
  refine ⟨tendsto_iff_norm_sub_tendsto_zero.2 ?_, fun i j => tendsto_iff_norm_sub_tendsto_zero.2 ?_⟩
  · have h_up : Tendsto (fun τ => A * h1RealNorm (S0Val hflow τ τ₀ v - v)) (𝓝[>] τ₀) (𝓝 0) := by
      simpa using hinit.const_mul A
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_up
      (Eventually.of_forall fun _ => norm_nonneg _) ?_
    filter_upwards [Ioo_mem_nhdsGT hmid] with τ hτ_in
    have hτ_nn : 0 ≤ τ := by linarith [hτ_in.1]
    have hτ_ioo : τ ∈ Ioo τ₀ (τ₀ + 2) := ⟨hτ_in.1, by linarith [hτ_in.2, h3, h1]⟩
    have ht_ioo : t ∈ Ioo τ (τ₀ + 2) := ⟨by linarith [hτ_in.2], by linarith [h3, h1]⟩
    have ht_ioc : t ∈ Ioc τ (τ + 1) := ⟨by linarith [hτ_in.2], by linarith [hτ_in.1, h3, h1]⟩
    have hS_mem : S0Val hflow τ τ₀ v ∈ H1Set p.c := S0Val_mem_H1Set p.c_pos hflow τ τ₀ v
    have hdiff_mem : v - S0Val hflow τ τ₀ v ∈ H1Set p.c := sub_mem_H1Set hv hS_mem
    have hck := (chapman_kolmogorov_S0Val_and_SD2Val hreg hflow hτ₀_nn hτ_ioo ht_ioo hv).1
    rw [← hck, ← S0Val_sub hreg hflow t τ hv hS_mem]
    calc ‖S0Val hflow t τ (v - S0Val hflow τ τ₀ v)‖
        ≤ h1RealNorm (S0Val hflow t τ (v - S0Val hflow τ τ₀ v)) := norm_le_h1RealNorm _
      _ ≤ A * h1RealNorm (v - S0Val hflow τ τ₀ v) :=
          (S0Val_and_SD2Val_bounds hA p.ν_pos hflow hτ_nn ht_ioc hdiff_mem).2.1
      _ = A * h1RealNorm (S0Val hflow τ τ₀ v - v) := by
          rw [← h1RealNorm_neg (v - _), neg_sub]
  · let C₀ : ℝ := A * p.ν ^ (-1 / 2 : ℝ) * ((t - τ₀) / 2) ^ (-1 / 2 : ℝ)
    have h_up : Tendsto (fun τ => C₀ * h1RealNorm (S0Val hflow τ τ₀ v - v)) (𝓝[>] τ₀) (𝓝 0) := by
      simpa using hinit.const_mul C₀
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_up
      (Eventually.of_forall fun _ => norm_nonneg _) ?_
    filter_upwards [Ioo_mem_nhdsGT hmid] with τ hτ_in
    have hτ_nn : 0 ≤ τ := by linarith [hτ_in.1]
    have hτ_ioo : τ ∈ Ioo τ₀ (τ₀ + 2) := ⟨hτ_in.1, by linarith [hτ_in.2, h3, h1]⟩
    have ht_ioo : t ∈ Ioo τ (τ₀ + 2) := ⟨by linarith [hτ_in.2], by linarith [h3, h1]⟩
    have ht_ioc : t ∈ Ioc τ (τ + 1) := ⟨by linarith [hτ_in.2], by linarith [hτ_in.1, h3, h1]⟩
    have hS_mem : S0Val hflow τ τ₀ v ∈ H1Set p.c := S0Val_mem_H1Set p.c_pos hflow τ τ₀ v
    have hdiff_mem : v - S0Val hflow τ τ₀ v ∈ H1Set p.c := sub_mem_H1Set hv hS_mem
    have hck := (chapman_kolmogorov_S0Val_and_SD2Val hreg hflow hτ₀_nn hτ_ioo ht_ioo hv).2 i j
    rw [← hck, ← SD2Val_sub hreg hflow i j t τ hv hS_mem]
    have hsum_bd := (S0Val_and_SD2Val_bounds hA p.ν_pos hflow hτ_nn ht_ioc hdiff_mem).2.2.2
    have hterm_le : ‖SD2Val hflow i j t τ (v - S0Val hflow τ τ₀ v)‖ ≤
        ∑ a : Fin 2, ∑ b : Fin 2, ‖SD2Val hflow a b t τ (v - S0Val hflow τ τ₀ v)‖ :=
      fin2_double_le_sum (fun a b => ‖SD2Val hflow a b t τ (v - S0Val hflow τ τ₀ v)‖)
        (fun _ _ => norm_nonneg _) i j
    have hrpow_le : (t - τ) ^ (-1 / 2 : ℝ) ≤ ((t - τ₀) / 2) ^ (-1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (half_pos (sub_pos.2 h2)) (by linarith [hτ_in.2]) (by norm_num)
    have hC_le : A * p.ν ^ (-1 / 2 : ℝ) * (t - τ) ^ (-1 / 2 : ℝ) ≤ C₀ :=
      mul_le_mul_of_nonneg_left hrpow_le (mul_nonneg hA.le (Real.rpow_nonneg p.ν_pos.le _))
    calc ‖SD2Val hflow i j t τ (v - S0Val hflow τ τ₀ v)‖
        ≤ A * p.ν ^ (-1 / 2 : ℝ) * (t - τ) ^ (-1 / 2 : ℝ) *
            h1RealNorm (v - S0Val hflow τ τ₀ v) := hterm_le.trans hsum_bd
      _ ≤ C₀ * h1RealNorm (v - S0Val hflow τ τ₀ v) :=
          mul_le_mul_of_nonneg_right hC_le (h1RealNorm_nonneg _)
      _ = C₀ * h1RealNorm (S0Val hflow τ τ₀ v - v) := by
          rw [← h1RealNorm_neg (v - _), neg_sub]

/-! ## 5. Joint strong measurability on `unitTriangle σ` and `forcingPath` -/

/-- Open unit Duhamel triangle `Δ σ = {(t, τ) : ℝ × ℝ | σ < τ < t < σ + 1}`. -/
def unitTriangle (σ : ℝ) : Set (ℝ × ℝ) :=
  {q : ℝ × ℝ | σ < q.2 ∧ q.2 < q.1 ∧ q.1 < σ + 1}

lemma isOpen_unitTriangle (σ : ℝ) : IsOpen (unitTriangle σ) :=
  (isOpen_lt continuous_const continuous_snd).inter
    ((isOpen_lt continuous_snd continuous_fst).inter
      (isOpen_lt continuous_fst continuous_const))

lemma measurableSet_unitTriangle (σ : ℝ) : MeasurableSet (unitTriangle σ) :=
  (isOpen_unitTriangle σ).measurableSet

private lemma stronglyMeasurable_finset_sum {α E ι : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] (s : Finset ι) {f : ι → α → E}
    (hf : ∀ i ∈ s, StronglyMeasurable (f i)) :
    StronglyMeasurable (fun a => ∑ i ∈ s, f i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using stronglyMeasurable_const
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Joint strong measurability on `ℝ × ℝ` of `(unitTriangle σ).indicator (fun q => Φ q.1 q.2)`
for any Banach-space-valued kernel `Φ` that is continuous in `t` on `(τ, σ + 1)` and
right-continuous in `τ` on `(σ, t)`. -/
lemma stronglyMeasurable_triangle_of_cont_left_rightCont_right {E : Type*}
    [NormedAddCommGroup E] {σ : ℝ} {Φ : ℝ → ℝ → E}
    (hcont_left : ∀ τ ∈ Ioo σ (σ + 1), ContinuousOn (fun t => Φ t τ) (Ioo τ (σ + 1)))
    (hright : ∀ t τ₀, σ < τ₀ → τ₀ < t → t < σ + 1 →
      Tendsto (fun τ => Φ t τ) (𝓝[>] τ₀) (𝓝 (Φ t τ₀))) :
    StronglyMeasurable ((unitTriangle σ).indicator fun q : ℝ × ℝ => Φ q.1 q.2) := by
  let g (k m : ℕ) : ℝ := σ + (m : ℝ) / ((k : ℝ) + 1)
  let S (k m : ℕ) : Set (ℝ × ℝ) :=
    {q : ℝ × ℝ | σ < q.2 ∧ g k m ≤ q.2 ∧ q.2 < g k (m + 1) ∧ g k (m + 1) < q.1 ∧ q.1 < σ + 1}
  let Ψ (k : ℕ) (q : ℝ × ℝ) : E :=
    ∑ m ∈ Finset.range k, (S k m).indicator (fun p : ℝ × ℝ => Φ p.1 (g k (m + 1))) q
  have hS_meas : ∀ k m, MeasurableSet (S k m) := by
    intro k m
    exact (measurableSet_lt measurable_const measurable_snd).inter
      ((measurableSet_le measurable_const measurable_snd).inter
        ((measurableSet_lt measurable_snd measurable_const).inter
          ((measurableSet_lt measurable_const measurable_fst).inter
            (measurableSet_lt measurable_fst measurable_const))))
  have hΨ_sm : ∀ k, StronglyMeasurable (Ψ k) := by
    intro k
    dsimp only [Ψ]
    refine stronglyMeasurable_finset_sum (Finset.range k) fun m hm => ?_
    have hm_lt : m < k := Finset.mem_range.1 hm
    have hpos_den : 0 < (k : ℝ) + 1 := by positivity
    have hgm_ioo : g k (m + 1) ∈ Ioo σ (σ + 1) := by
      dsimp [g]
      have hdiv_pos : 0 < ((m + 1 : ℕ) : ℝ) / ((k : ℝ) + 1) := div_pos (by positivity) hpos_den
      have hdiv_lt : ((m + 1 : ℕ) : ℝ) / ((k : ℝ) + 1) < 1 := by
        rw [div_lt_one hpos_den]
        exact_mod_cast Nat.succ_lt_succ hm_lt
      exact ⟨by linarith, by linarith⟩
    have hc_on : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 (g k (m + 1))) (S k m) :=
      (hcont_left (g k (m + 1)) hgm_ioo).comp continuousOn_fst
        (fun p hp => ⟨hp.2.2.2.1, hp.2.2.2.2⟩)
    exact UnforcedLeray.Infra.JointMeasurableRep.stronglyMeasurable_indicator_of_continuousOn
      hc_on (hS_meas k m)
  have hS_disj : ∀ k {m₁ m₂ : ℕ}, m₁ ≠ m₂ → ∀ q, q ∈ S k m₁ → q ∉ S k m₂ := by
    intro k m₁ m₂ hne q h1 h2
    have hpos_den : 0 < (k : ℝ) + 1 := by positivity
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : g k (m₁ + 1) ≤ g k m₂ := by
        dsimp [g]
        have : ((m₁ + 1 : ℕ) : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hlt
        exact add_le_add_right (div_le_div_of_nonneg_right this hpos_den.le) _
      linarith [h1.2.2.1, h2.2.1]
    · have hle : g k (m₂ + 1) ≤ g k m₁ := by
        dsimp [g]
        have : ((m₂ + 1 : ℕ) : ℝ) ≤ (m₁ : ℝ) := by exact_mod_cast hgt
        exact add_le_add_right (div_le_div_of_nonneg_right this hpos_den.le) _
      linarith [h2.2.2.1, h1.2.1]
  have hΨ_lim : ∀ q : ℝ × ℝ,
      Tendsto (fun k => Ψ k q) atTop
        (𝓝 ((unitTriangle σ).indicator (fun p : ℝ × ℝ => Φ p.1 p.2) q)) := by
    intro q
    by_cases hq : q ∈ unitTriangle σ
    · rw [indicator_of_mem hq]
      rcases q with ⟨t, τ⟩
      obtain ⟨hστ, hτt, ht1⟩ := hq
      rw [tendsto_nhds]
      intro U hU_open hU_mem
      have hev := (hright t τ hστ hτt ht1).eventually (hU_open.mem_nhds hU_mem)
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
      obtain ⟨δ, hδ_pos, hδ_ball⟩ := hev
      obtain ⟨K, hK⟩ := exists_nat_one_div_lt (lt_min hδ_pos (sub_pos.2 hτt))
      rw [Filter.mem_atTop_sets]
      refine ⟨K, fun k hk => ?_⟩
      change Ψ k (t, τ) ∈ U
      have hpos_den : 0 < (k : ℝ) + 1 := by positivity
      have hstep_lt : 1 / ((k : ℝ) + 1) < min δ (t - τ) := by
        refine lt_of_le_of_lt ?_ hK
        refine one_div_le_one_div_of_le (by positivity) ?_
        exact_mod_cast Nat.succ_le_succ hk
      let m₀ : ℕ := ⌊(τ - σ) * ((k : ℝ) + 1)⌋₊
      have hgm_le : g k m₀ ≤ τ := by
        dsimp [g, m₀]
        have hfl := Nat.floor_le (mul_nonneg (sub_pos.2 hστ).le hpos_den.le)
        have hdiv := (div_le_iff₀ hpos_den).2 hfl
        linarith
      have hτ_lt_gm1 : τ < g k (m₀ + 1) := by
        dsimp [g, m₀]
        have hfl := Nat.lt_floor_add_one ((τ - σ) * ((k : ℝ) + 1))
        have hdiv := (lt_div_iff₀ hpos_den).2 hfl
        push_cast
        linarith
      have hgm1_le : g k (m₀ + 1) ≤ τ + 1 / ((k : ℝ) + 1) := by
        have hsplit : g k (m₀ + 1) = g k m₀ + 1 / ((k : ℝ) + 1) := by
          dsimp [g]; push_cast; ring
        linarith
      have hgm1_lt_t : g k (m₀ + 1) < t := by
        have := lt_of_lt_of_le hstep_lt (min_le_right _ _)
        linarith
      have hm₀_mem : m₀ ∈ Finset.range k := by
        rw [Finset.mem_range]
        have hlt1 : ((m₀ + 1 : ℕ) : ℝ) < (k : ℝ) + 1 := by
          have : g k (m₀ + 1) < σ + 1 := hgm1_lt_t.trans ht1
          dsimp [g] at this
          have hdiv : ((m₀ + 1 : ℕ) : ℝ) / ((k : ℝ) + 1) < 1 := by linarith
          exact (div_lt_one hpos_den).1 hdiv
        have hlt_nat : m₀ + 1 < k + 1 := by exact_mod_cast hlt1
        omega
      have hq_mem_S : (t, τ) ∈ S k m₀ := ⟨hστ, hgm_le, hτ_lt_gm1, hgm1_lt_t, ht1⟩
      have hΨ_val : Ψ k (t, τ) = Φ t (g k (m₀ + 1)) := by
        dsimp [Ψ]
        rw [Finset.sum_eq_single m₀]
        · exact indicator_of_mem hq_mem_S _
        · intro m _ hne
          exact indicator_of_notMem (hS_disj k hne.symm (t, τ) hq_mem_S) _
        · intro hnot; exact False.elim (hnot hm₀_mem)
      rw [hΨ_val]
      have hdist : dist (g k (m₀ + 1)) τ < δ := by
        rw [Real.dist_eq, abs_of_pos (sub_pos.2 hτ_lt_gm1)]
        have := lt_of_lt_of_le hstep_lt (min_le_left _ _)
        linarith
      exact hδ_ball hdist hτ_lt_gm1
    · rw [indicator_of_notMem hq]
      have hz : ∀ k, Ψ k q = 0 := by
        intro k
        dsimp [Ψ]
        refine Finset.sum_eq_zero fun m _ => indicator_of_notMem (fun hm => hq ?_) _
        exact ⟨hm.1, hm.2.2.1.trans hm.2.2.2.1, hm.2.2.2.2⟩
      simp [hz]
  exact stronglyMeasurable_of_tendsto atTop hΨ_sm (tendsto_pi_nhds.2 hΨ_lim)

/-- Composition of a jointly strongly measurable triangle kernel with a `StronglyMeasurable`
`H1Set`-valued forcing path via `SimpleFunc.approxOn`. -/
lemma stronglyMeasurable_triangle_comp_H1 {E : Type*} [NormedAddCommGroup E]
    {c σ : ℝ} {B : ℝ → ℝ → X3 c → E}
    (hB_triangle : ∀ v ∈ H1Set c,
      StronglyMeasurable ((unitTriangle σ).indicator fun q : ℝ × ℝ => B q.1 q.2 v))
    (hB_lip : ∀ q ∈ unitTriangle σ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u ∈ H1Set c, ∀ v ∈ H1Set c, ‖B q.1 q.2 u - B q.1 q.2 v‖ ≤ C * h1RealNorm (u - v))
    {f : ℝ → X3 c} (hf : StronglyMeasurable f) (hf_mem : ∀ τ, f τ ∈ H1Set c) :
    StronglyMeasurable ((unitTriangle σ).indicator fun q : ℝ × ℝ => B q.1 q.2 (f q.2)) := by
  classical
  borelize (X3 c)
  let S₀ : Set (X3 c) := range f ∪ {0}
  have h0_mem : (0 : X3 c) ∈ S₀ := mem_union_right _ rfl
  have hS₀_sub : S₀ ⊆ H1Set c := by
    rintro x (⟨τ, rfl⟩ | rfl)
    · exact hf_mem τ
    · exact zero_mem_H1Set c
  have : TopologicalSpace.SeparableSpace S₀ :=
    (hf.isSeparable_range.union (Set.finite_singleton (0 : X3 c)).isSeparable).separableSpace
  let sf : ℕ → MeasureTheory.SimpleFunc ℝ (X3 c) :=
    fun n => SimpleFunc.approxOn f hf.measurable S₀ 0 h0_mem n
  have hsf_mem : ∀ n τ, sf n τ ∈ H1Set c :=
    fun n τ => hS₀_sub (SimpleFunc.approxOn_mem hf.measurable h0_mem n τ)
  let G (n : ℕ) : ℝ × ℝ → E :=
    (unitTriangle σ).indicator fun q : ℝ × ℝ => B q.1 q.2 (sf n q.2)
  have hG_sm : ∀ n, StronglyMeasurable (G n) := by
    intro n
    have heq : G n = fun q : ℝ × ℝ =>
        ∑ v ∈ (sf n).range,
          (Prod.snd ⁻¹' ((sf n) ⁻¹' {v})).indicator
            ((unitTriangle σ).indicator fun p : ℝ × ℝ => B p.1 p.2 v) q := by
      funext q
      rw [Finset.sum_eq_single (sf n q.2)]
      · by_cases hq : q ∈ unitTriangle σ <;> simp [G, hq]
      · intro v _ hne
        exact indicator_of_notMem (fun h => hne h.symm) _
      · intro hnot
        exact False.elim (hnot (SimpleFunc.mem_range_self (sf n) q.2))
    rw [heq]
    refine stronglyMeasurable_finset_sum (sf n).range fun v hv => ?_
    obtain ⟨τ₀, rfl⟩ := SimpleFunc.mem_range.1 hv
    have hm_set : MeasurableSet (Prod.snd ⁻¹' ((sf n) ⁻¹' {sf n τ₀}) : Set (ℝ × ℝ)) :=
      ((sf n).measurableSet_fiber (sf n τ₀)).preimage measurable_snd
    exact (hB_triangle (sf n τ₀) (hsf_mem n τ₀)).indicator hm_set
  have hG_lim : ∀ q : ℝ × ℝ,
      Tendsto (fun n => G n q) atTop
        (𝓝 ((unitTriangle σ).indicator (fun p : ℝ × ℝ => B p.1 p.2 (f p.2)) q)) := by
    intro q
    by_cases hq : q ∈ unitTriangle σ
    · obtain ⟨C, hC_nn, hlip⟩ := hB_lip q hq
      have hf_cl : f q.2 ∈ closure S₀ := subset_closure (mem_union_left _ (mem_range_self q.2))
      have happ := tendsto_iff_norm_sub_tendsto_zero.1
        (SimpleFunc.tendsto_approxOn hf.measurable h0_mem hf_cl)
      have hup : Tendsto (fun n => C * (3 * ‖sf n q.2 - f q.2‖)) atTop (𝓝 0) := by
        simpa using (happ.const_mul 3).const_mul C
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hup
      dsimp [G]
      rw [indicator_of_mem hq, indicator_of_mem hq]
      calc ‖B q.1 q.2 (sf n q.2) - B q.1 q.2 (f q.2)‖
          ≤ C * h1RealNorm (sf n q.2 - f q.2) := hlip _ (hsf_mem n q.2) _ (hf_mem q.2)
        _ ≤ C * (3 * ‖sf n q.2 - f q.2‖) :=
            mul_le_mul_of_nonneg_left (h1RealNorm_le_three_norm _) hC_nn
    · simp [G, hq]
  exact stronglyMeasurable_of_tendsto atTop hG_sm (tendsto_pi_nhds.2 hG_lim)

/-- Raw `X3 c` slice path extracted from `(g₁, gq₁, gη₁)` via `BochnerTime.toPathLq`. -/
def rawForcingPath (c : ℝ) (g₁ gq₁ gη₁ : CProf) (τ : ℝ) : X3 c :=
  (UnforcedLeray.BochnerTime.toPathLq 2 (F8Sm.cellMeas c) g₁ τ,
   UnforcedLeray.BochnerTime.toPathLq 2 (F8Sm.cellMeas c) gq₁ τ,
   UnforcedLeray.BochnerTime.toPathLq 2 (F8Sm.cellMeas c) gη₁ τ)

lemma stronglyMeasurable_rawForcingPath {c : ℝ} {g₁ gq₁ gη₁ : CProf}
    (hg₁ : StronglyMeasurable g₁) (hgq₁ : StronglyMeasurable gq₁)
    (hgη₁ : StronglyMeasurable gη₁) :
    StronglyMeasurable (rawForcingPath c g₁ gq₁ gη₁) :=
  (UnforcedLeray.BochnerTime.stronglyMeasurable_toPathLq hg₁).prodMk
    ((UnforcedLeray.BochnerTime.stronglyMeasurable_toPathLq hgq₁).prodMk
      (UnforcedLeray.BochnerTime.stronglyMeasurable_toPathLq hgη₁))

/-- Construction of a Borel-measurable `H1Set`-valued modification `forcingPath : ℝ → X3 c`
on `Ioc σ (σ + 1)` from the a.e. `IsCylH1Datum` hypothesis. -/
lemma exists_clean_forcingPath {c σ : ℝ} {g₁ gq₁ gη₁ : CProf}
    (hg₁ : StronglyMeasurable g₁) (hgq₁ : StronglyMeasurable gq₁)
    (hgη₁ : StronglyMeasurable gη₁)
    (hae : ∀ᵐ τ ∂volume, τ ∈ Ioc σ (σ + 1) →
      F8U.IsCylH1Datum c (F8U.slice g₁ τ) (F8U.slice gq₁ τ) (F8U.slice gη₁ τ)) :
    ∃ fp : ℝ → X3 c,
      StronglyMeasurable fp ∧
      (∀ τ, fp τ ∈ H1Set c) ∧
      (∀ τ ∉ Ioc σ (σ + 1), fp τ = 0) ∧
      (∀ τ, h1ENN (fp τ) ≤ sliceH1Norm c g₁ gq₁ gη₁ τ) ∧
      (∀ᵐ τ ∂volume, τ ∈ Ioc σ (σ + 1) →
        (fp τ).1 =ᵐ[F8Sm.cellMeas c] F8U.slice g₁ τ ∧
        (fp τ).2.1 =ᵐ[F8Sm.cellMeas c] F8U.slice gq₁ τ ∧
        (fp τ).2.2 =ᵐ[F8Sm.cellMeas c] F8U.slice gη₁ τ ∧
        h1ENN (fp τ) = sliceH1Norm c g₁ gq₁ gη₁ τ) := by
  let Bad : Set ℝ :=
    {τ : ℝ | τ ∈ Ioc σ (σ + 1) ∧
      ¬F8U.IsCylH1Datum c (F8U.slice g₁ τ) (F8U.slice gq₁ τ) (F8U.slice gη₁ τ)}
  have hBad_null : volume Bad = 0 := by
    have : Bad = {τ : ℝ | ¬(τ ∈ Ioc σ (σ + 1) →
        F8U.IsCylH1Datum c (F8U.slice g₁ τ) (F8U.slice gq₁ τ) (F8U.slice gη₁ τ))} := by
      ext τ; simp [Bad, and_assoc]
    rw [this]
    exact ae_iff.1 hae
  obtain ⟨N, hBad_sub, hN_meas, hN_null⟩ := exists_measurable_superset_of_null hBad_null
  let G : Set ℝ := Ioc σ (σ + 1) \ N
  have hG_meas : MeasurableSet G := measurableSet_Ioc.diff hN_meas
  let fp : ℝ → X3 c := G.indicator (rawForcingPath c g₁ gq₁ gη₁)
  have hG_dat : ∀ {τ}, τ ∈ G →
      F8U.IsCylH1Datum c (F8U.slice g₁ τ) (F8U.slice gq₁ τ) (F8U.slice gη₁ τ) := by
    intro τ hτ
    by_contra hnot
    exact hτ.2 (hBad_sub ⟨hτ.1, hnot⟩)
  have hfp_eq : ∀ {τ} (hτ : τ ∈ G), fp τ = datumToX3 (hG_dat hτ) := by
    intro τ hτ
    have hd := hG_dat hτ
    have hm1 : MemLp (fun y => g₁ (τ, y)) 2 (F8Sm.cellMeas c) := hd.memL2.1
    have hm2 : MemLp (fun y => gq₁ (τ, y)) 2 (F8Sm.cellMeas c) := hd.memL2.2.1
    have hm3 : MemLp (fun y => gη₁ (τ, y)) 2 (F8Sm.cellMeas c) := hd.memL2.2.2
    dsimp only [fp]
    rw [indicator_of_mem hτ]
    unfold rawForcingPath datumToX3
    rw [UnforcedLeray.BochnerTime.toPathLq_of_memLp hm1,
      UnforcedLeray.BochnerTime.toPathLq_of_memLp hm2,
      UnforcedLeray.BochnerTime.toPathLq_of_memLp hm3]
    rfl
  refine ⟨fp, (stronglyMeasurable_rawForcingPath hg₁ hgq₁ hgη₁).indicator hG_meas,
    fun τ => ?_, fun τ hτ => indicator_of_notMem (fun hg => hτ hg.1) _,
    fun τ => ?_, ?_⟩
  · by_cases hτ : τ ∈ G
    · rw [hfp_eq hτ]; exact datumToX3_mem_H1Set (hG_dat hτ)
    · dsimp [fp]; rw [indicator_of_notMem hτ]; exact zero_mem_H1Set c
  · by_cases hτ : τ ∈ G
    · rw [hfp_eq hτ, h1ENN_datumToX3]
      rfl
    · dsimp [fp]; rw [indicator_of_notMem hτ, h1ENN_eq_ofReal, h1RealNorm_zero, ENNReal.ofReal_zero]
      exact bot_le
  · filter_upwards [compl_mem_ae_iff.2 hN_null] with τ hτN hτ_ioc
    have hτG : τ ∈ G := ⟨hτ_ioc, hτN⟩
    have hd := hG_dat hτG
    rw [hfp_eq hτG]
    exact ⟨hd.memL2.1.coeFn_toLp, hd.memL2.2.1.coeFn_toLp, hd.memL2.2.2.coeFn_toLp,
      h1ENN_datumToX3 hd⟩

/-- Duhamel `X3`-kernel `K0` and second-derivative `L2Cell`-kernels `KD2 i j` on `ℝ × ℝ`. -/
def K0 {A : ℝ} {p : Params} (hflow : F8U.CylOseenFlowBound A p)
    (σ : ℝ) (fp : ℝ → X3 p.c) : ℝ × ℝ → X3 p.c :=
  (unitTriangle σ).indicator fun q : ℝ × ℝ => S0Val hflow q.1 q.2 (fp q.2)

def KD2 {A : ℝ} {p : Params} (hflow : F8U.CylOseenFlowBound A p)
    (σ : ℝ) (fp : ℝ → X3 p.c) (i j : Fin 2) : ℝ × ℝ → L2Cell p.c :=
  (unitTriangle σ).indicator fun q : ℝ × ℝ => SD2Val hflow i j q.1 q.2 (fp q.2)

lemma stronglyMeasurable_K0_and_KD2 {dm dp : ℝ} {p : Params} {d A σ : ℝ}
    (hA : 0 < A) (hreg : BgRegime p d dm dp) (hflow : F8U.CylOseenFlowBound A p) (hσ : 0 ≤ σ)
    {fp : ℝ → X3 p.c} (hfp : StronglyMeasurable fp) (hfp_mem : ∀ τ, fp τ ∈ H1Set p.c) :
    StronglyMeasurable (K0 hflow σ fp) ∧
    ∀ i j : Fin 2, StronglyMeasurable (KD2 hflow σ fp i j) := by
  refine ⟨?_, fun i j => ?_⟩
  · refine stronglyMeasurable_triangle_comp_H1
      (fun v hv => stronglyMeasurable_triangle_of_cont_left_rightCont_right
        (fun τ hτ => (continuousOn_S0Val_and_SD2Val_left hflow (by linarith [hτ.1]) hv).1.mono
          (fun t ht => ⟨ht.1, by linarith [ht.2, hτ.1]⟩))
        (fun t τ₀ h1 h2 h3 =>
          (tendsto_S0Val_and_SD2Val_right hA hreg hflow hσ h1 h2 h3 hv).1))
      (fun q hq => ⟨A, hA.le, fun u hu v hv => by
        rw [← S0Val_sub hreg hflow q.1 q.2 hu hv]
        exact (norm_le_h1RealNorm _).trans
          (S0Val_and_SD2Val_bounds hA p.ν_pos hflow (by linarith [hq.1])
            ⟨hq.2.1, by linarith [hq.1, hq.2.2]⟩ (sub_mem_H1Set hu hv)).2.1⟩)
      hfp hfp_mem
  · refine stronglyMeasurable_triangle_comp_H1
      (fun v hv => stronglyMeasurable_triangle_of_cont_left_rightCont_right
        (fun τ hτ => (continuousOn_S0Val_and_SD2Val_left hflow (by linarith [hτ.1]) hv).2 i j |>.mono
          (fun t ht => ⟨ht.1, by linarith [ht.2, hτ.1]⟩))
        (fun t τ₀ h1 h2 h3 =>
          (tendsto_S0Val_and_SD2Val_right hA hreg hflow hσ h1 h2 h3 hv).2 i j))
      (fun q hq => by
        let Cq : ℝ := A * p.ν ^ (-1 / 2 : ℝ) * (q.1 - q.2) ^ (-1 / 2 : ℝ)
        have hCq_nn : 0 ≤ Cq :=
          mul_nonneg (mul_nonneg hA.le (Real.rpow_nonneg p.ν_pos.le _))
            (Real.rpow_nonneg (sub_pos.2 hq.2.1).le _)
        refine ⟨Cq, hCq_nn, fun u hu v hv => ?_⟩
        rw [← SD2Val_sub hreg hflow i j q.1 q.2 hu hv]
        have hsum := (S0Val_and_SD2Val_bounds hA p.ν_pos hflow (by linarith [hq.1])
          ⟨hq.2.1, by linarith [hq.1, hq.2.2]⟩ (sub_mem_H1Set hu hv)).2.2.2
        have hle : ‖SD2Val hflow i j q.1 q.2 (u - v)‖ ≤
            ∑ a : Fin 2, ∑ b : Fin 2, ‖SD2Val hflow a b q.1 q.2 (u - v)‖ :=
          fin2_double_le_sum (fun a b => ‖SD2Val hflow a b q.1 q.2 (u - v)‖)
            (fun _ _ => norm_nonneg _) i j
        exact hle.trans hsum)
      hfp hfp_mem

end UnforcedLeray.Short.IIb.UnitDuhamelStepAux
