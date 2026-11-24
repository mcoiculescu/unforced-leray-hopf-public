import UnforcedLeray.Short.PartI.Sub.T02_1_4_6

/-!
# Part I, task `PartI:T02/1/4/6`, leaf R1: a solenoidal test has a divergence-free `L²` class

Source of record: `the November 2 reference manuscript`, lines 261-288
(test fields for the Leray form of the mild equation).

Target: `divFreeTestClass : DivFreeTestClass` (leaf R1 of `Sub/T02_1_4_6.lean`).

Route.
* `φ` is continuous and vanishes for `|η|` large, so `φ ∈ L²(cell)` (`Cyl.memLp_of_vanishes`);
  its class `φL = hMem.toLp φ` is a.e. equal to `φ`.
* `φL ∈ Cyl.divFree c` means `⟪gradL χ, φL⟫ = 0` for every cylinder test `χ`
  (`Cyl.mem_divFree`). By `Cyl.inner_toLp_eq` this is `∫_cell ⟨∇χ, φ⟩ = 0`.
* The components `φ₀ = φ · e₁`, `φ₁ = φ · e₂` are scalar cylinder tests, so componentwise
  integration by parts (`Cyl.integral_fderiv_mul_test`) gives
  `∫ ∂_qχ φ₀ = -∫ χ ∂_qφ₀` and `∫ ∂_ηχ φ₁ = -∫ χ ∂_ηφ₁`. Since `∂_qφ₀ + ∂_ηφ₁ = div φ = 0`
  pointwise, the two right-hand integrals cancel.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-- **Leaf R1** (`DivFreeTestClass`): a smooth periodic solenoidal field with `η`-compact support
has an `L²(cell)` class lying in the weakly solenoidal space `Cyl.divFree c`. -/
theorem divFreeTestClass : DivFreeTestClass := by
  intro c hc φ hφ
  obtain ⟨⟨hsm, hper, hbd⟩, hdiv⟩ := hφ
  obtain ⟨R, hR⟩ := hbd
  have hp : ∀ x : Plane, φ (x.1 + c, x.2) = φ x := hper
  have hφc : Continuous φ := hsm.continuous
  have hMem : MemLp φ 2 (Cyl.cellμ c) := Cyl.memLp_of_vanishes hφc hR 2
  refine ⟨hMem.toLp φ, hMem.coeFn_toLp, ?_⟩
  rw [Cyl.mem_divFree]
  intro χ hχ
  -- The scalar components of `φ` are cylinder tests.
  have hcomp : ∀ i : Fin 2, Sob.IsCylTest c (fun z => φ z i) := by
    intro i
    refine ⟨?_, ?_, ?_⟩
    · exact (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).contDiff.comp hsm
    · intro x
      have e : x + ((c : ℝ), (0 : ℝ)) = (x.1 + c, x.2) := by ext <;> simp
      show φ (x + ((c : ℝ), (0 : ℝ))) i = φ x i
      rw [e, hp x]
    · exact ⟨R, fun x hx => by simp [hR x hx]⟩
  have hT0 := hcomp 0
  have hT1 := hcomp 1
  -- Pointwise: the integrand `⟨∇χ, φ⟩` splits into the two components.
  have hint : ∀ z : Plane, inner ℝ (Cyl.gradT χ z) (φ z) =
      fderiv ℝ χ z ((1 : ℝ), (0 : ℝ)) * φ z 0 + fderiv ℝ χ z ((0 : ℝ), (1 : ℝ)) * φ z 1 := by
    intro z
    simp only [Cyl.gradT]
    rw [Cyl.partialQ_eq_fderiv hχ.differentiable z, Cyl.partialEta_eq_fderiv hχ.differentiable z,
      real_inner_comm, Cyl.inner_vec]
    ring
  -- Pointwise: the two partial divergences of `φ` cancel, since `div φ = 0`.
  have hb : ∀ z : Plane, χ z * fderiv ℝ (fun w => φ w 1) z ((0 : ℝ), (1 : ℝ)) =
      -(χ z * fderiv ℝ (fun w => φ w 0) z ((1 : ℝ), (0 : ℝ))) := by
    intro z
    have hz : Cyl.partialQ (fun w => φ w 0) z + Cyl.partialEta (fun w => φ w 1) z = 0 := hdiv z
    rw [Cyl.partialQ_eq_fderiv hT0.differentiable z,
      Cyl.partialEta_eq_fderiv hT1.differentiable z] at hz
    have h' : fderiv ℝ (fun w => φ w 1) z ((0 : ℝ), (1 : ℝ)) =
        -fderiv ℝ (fun w => φ w 0) z ((1 : ℝ), (0 : ℝ)) := by linarith
    rw [h']
    ring
  -- Componentwise integration by parts.
  have e1 : ∫ z in Cyl.cell c, fderiv ℝ χ z ((1 : ℝ), (0 : ℝ)) * φ z 0 =
      -∫ z in Cyl.cell c, χ z * fderiv ℝ (fun w => φ w 0) z ((1 : ℝ), (0 : ℝ)) :=
    Cyl.integral_fderiv_mul_test hc hχ hT0 ((1 : ℝ), (0 : ℝ))
  have e2 : ∫ z in Cyl.cell c, fderiv ℝ χ z ((0 : ℝ), (1 : ℝ)) * φ z 1 =
      -∫ z in Cyl.cell c, χ z * fderiv ℝ (fun w => φ w 1) z ((0 : ℝ), (1 : ℝ)) :=
    Cyl.integral_fderiv_mul_test hc hχ hT1 ((0 : ℝ), (1 : ℝ))
  have e3 : ∫ z in Cyl.cell c, χ z * fderiv ℝ (fun w => φ w 1) z ((0 : ℝ), (1 : ℝ)) =
      -∫ z in Cyl.cell c, χ z * fderiv ℝ (fun w => φ w 0) z ((1 : ℝ), (0 : ℝ)) := by
    simp only [hb, integral_neg]
  have h1 : IntegrableOn (fun z => fderiv ℝ χ z ((1 : ℝ), (0 : ℝ)) * φ z 0) (Cyl.cell c) :=
    (hχ.dirDeriv ((1 : ℝ), (0 : ℝ))).integrableOn_mul hT0.continuous
  have h2 : IntegrableOn (fun z => fderiv ℝ χ z ((0 : ℝ), (1 : ℝ)) * φ z 1) (Cyl.cell c) :=
    (hχ.dirDeriv ((0 : ℝ), (1 : ℝ))).integrableOn_mul hT1.continuous
  rw [Cyl.gradL, Cyl.inner_toLp_eq]
  simp only [hint]
  rw [integral_add h1 h2, e1, e2, e3]
  ring

end UnforcedLeray.Short.PartI
