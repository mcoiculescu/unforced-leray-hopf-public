import UnforcedLeray.Lib.PhaseSpace.Leibniz
import UnforcedLeray.Units.B0411
import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators

/-!
# Solenoidality of `L₀ᵗΦ + μΦ` (helper for `PairFunctionalDual`)

For a solenoidal phase test `Φ` (`IsSolTest P Φ`), the test `L₀ᵗΦ + μΦ` is again a solenoidal
phase test. Phase-testness is `isPhaseTest_L0T`. Solenoidality is proved by the scheme

* `∂ⱼ (L₀ᵗΦ + μΦ) = L₀ᵗ(∂ⱼΦ) + μ ∂ⱼΦ` (CVec3 level, `dy_driftT`, `dy_lapT`),
* taking the `j`-th coordinate, the `j`-th coordinate of `L₀ᵗ(∂ⱼΦ)` is the scalar operator
  applied to `∂ⱼ φⱼ` with `φⱼ = (Φ)ⱼ` (`driftT_cproj`, `lapT_cproj`),
* the three scalar functions `fⱼ = ∂ⱼ φⱼ` sum to zero (the divergence condition), and the
  scalar operators are additive (`driftT_add_pt`, `lapT_add_pt`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.PairDualAux

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Cons.C03.Concrete

/-! ### Generic calculus for scalar-valued phase functions -/

section Generic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_dy_g {f : ℝ × Space → F} (hf : ContDiff ℝ ∞ f) (j : Fin 3) :
    ContDiff ℝ ∞ (dy j f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem dy_add_g {f g : ℝ × Space → F} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (j : Fin 3) : dy j (fun y => f y + g y) = fun y => dy j f y + dy j g y := by
  funext p
  simp only [dy]
  rw [show (fun y => f y + g y) = f + g from rfl, fderiv_add (hf p) (hg p)]
  simp

theorem dτ_add_g {f g : ℝ × Space → F} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    dτ (fun y => f y + g y) = fun y => dτ f y + dτ g y := by
  funext p
  simp only [dτ]
  rw [show (fun y => f y + g y) = f + g from rfl, fderiv_add (hf p) (hg p)]
  simp

theorem radialT_add_g {f g : ℝ × Space → F} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    radialT (fun y => f y + g y) = fun y => radialT f y + radialT g y := by
  funext p
  simp only [radialT, dy_add_g hf hg, smul_add, Finset.sum_add_distrib]

theorem driftT_add_pt {f g : ℝ × Space → F} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (p : ℝ × Space) :
    driftT (fun y => f y + g y) p = driftT f p + driftT g p := by
  simp only [driftT, dτ_add_g hf hg, radialT_add_g hf hg]
  module

theorem lapT_add_pt {f g : ℝ × Space → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (p : ℝ × Space) :
    lapT (fun y => f y + g y) p = lapT f p + lapT g p := by
  have hfD : Differentiable ℝ f := hf.differentiable (by simp)
  have hgD : Differentiable ℝ g := hg.differentiable (by simp)
  have hfd : ∀ k, Differentiable ℝ (dy k f) := fun k => (contDiff_dy_g hf k).differentiable (by simp)
  have hgd : ∀ k, Differentiable ℝ (dy k g) := fun k => (contDiff_dy_g hg k).differentiable (by simp)
  have h1 : ∀ k, dy k (fun y => f y + g y) = fun y => dy k f y + dy k g y :=
    fun k => dy_add_g hfD hgD k
  have h2 : ∀ k, dy k (fun y => dy k f y + dy k g y) =
      fun y => dy k (dy k f) y + dy k (dy k g) y :=
    fun k => dy_add_g (hfd k) (hgd k) k
  simp only [lapT, h1, h2, Finset.sum_add_distrib]

theorem dy_zero_fun (j : Fin 3) : dy j (fun _ : ℝ × Space => (0 : F)) = fun _ => 0 := by
  funext p
  simp [dy]

theorem driftT_zero_pt (x : ℝ × Space) : driftT (fun _ : ℝ × Space => (0 : F)) x = 0 := by
  simp [driftT, radialT, dτ, dy_zero_fun]

theorem lapT_zero_pt (x : ℝ × Space) : lapT (fun _ : ℝ × Space => (0 : F)) x = 0 := by
  simp [lapT, dy_zero_fun]

end Generic

/-! ### Coordinates on `CVec3` -/

/-- The `j`-th coordinate, as a complex-linear functional on `CVec3`. -/
def cprojC (j : Fin 3) : CVec3 →L[ℂ] ℂ := EuclideanSpace.proj j

/-- The `j`-th coordinate, as a real-linear functional on `CVec3`. -/
def cproj (j : Fin 3) : CVec3 →L[ℝ] ℂ := (cprojC j).restrictScalars ℝ

theorem cproj_apply (j : Fin 3) (v : CVec3) : cproj j v = v j := rfl

theorem cproj_smul_C (j : Fin 3) (c : ℂ) (v : CVec3) :
    cproj j (c • v) = c * cproj j v := by
  show cprojC j (c • v) = c * cprojC j v
  rw [map_smul, smul_eq_mul]

theorem fderiv_cproj {Ψ : ℝ × Space → CVec3} (hΨ : Differentiable ℝ Ψ) (j : Fin 3)
    (p v : ℝ × Space) :
    fderiv ℝ (fun y => cproj j (Ψ y)) p v = cproj j (fderiv ℝ Ψ p v) := by
  have h : HasFDerivAt (fun y => cproj j (Ψ y)) ((cproj j).comp (fderiv ℝ Ψ p)) p :=
    HasFDerivAt.comp p (cproj j).hasFDerivAt (hΨ p).hasFDerivAt
  rw [h.fderiv]
  rfl

theorem dy_cproj_fun {Ψ : ℝ × Space → CVec3} (hΨ : Differentiable ℝ Ψ) (j k : Fin 3) :
    (fun y => cproj j (dy k Ψ y)) = dy k (fun y => cproj j (Ψ y)) := by
  funext p
  simp only [dy]
  rw [fderiv_cproj hΨ j]

theorem dτ_cproj {Ψ : ℝ × Space → CVec3} (hΨ : Differentiable ℝ Ψ) (j : Fin 3) (p : ℝ × Space) :
    cproj j (dτ Ψ p) = dτ (fun y => cproj j (Ψ y)) p := by
  simp only [dτ]
  rw [fderiv_cproj hΨ j]

theorem radialT_cproj {Ψ : ℝ × Space → CVec3} (hΨ : ContDiff ℝ ∞ Ψ) (j : Fin 3)
    (p : ℝ × Space) :
    cproj j (radialT Ψ p) = radialT (fun y => cproj j (Ψ y)) p := by
  have hD : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  have e : ∀ k, cproj j (dy k Ψ p) = dy k (fun y => cproj j (Ψ y)) p :=
    fun k => congrFun (dy_cproj_fun hD j k) p
  simp only [radialT, map_sum, map_smul, e]

theorem driftT_cproj {Ψ : ℝ × Space → CVec3} (hΨ : ContDiff ℝ ∞ Ψ) (j : Fin 3)
    (p : ℝ × Space) :
    cproj j (driftT Ψ p) = driftT (fun y => cproj j (Ψ y)) p := by
  have hD : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  simp only [driftT, map_add, map_neg, map_smul, dτ_cproj hD, radialT_cproj hΨ]

theorem lapT_cproj {Ψ : ℝ × Space → CVec3} (hΨ : ContDiff ℝ ∞ Ψ) (j : Fin 3)
    (p : ℝ × Space) :
    cproj j (lapT Ψ p) = lapT (fun y => cproj j (Ψ y)) p := by
  have hD : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  have hDk : ∀ k, Differentiable ℝ (dy k Ψ) := fun k => (contDiff_dy hΨ k).differentiable (by simp)
  simp only [lapT, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← dy_cproj_fun hD j k, ← dy_cproj_fun (hDk k) j k]

/-! ### The `j`-th coordinate of `∂ⱼ (L₀ᵗΦ + μΦ)` -/

theorem diffR_smul {G : ℝ × Space → CVec3} (hG : Differentiable ℝ G) (c : ℝ) :
    Differentiable ℝ (c • G) := fun p => (hG p).const_smul c

theorem diffC_smul {G : ℝ × Space → CVec3} (hG : Differentiable ℝ G) (c : ℂ) :
    Differentiable ℝ (c • G) := fun p => (hG p).const_smul c

theorem dy_smulC {G : ℝ × Space → CVec3} (hG : Differentiable ℝ G) (c : ℂ) (j : Fin 3) :
    dy j (c • G) = c • dy j G := by
  funext p
  simp [dy, fderiv_const_smul (hG p) c]

theorem dy_L0T_add {ν μ : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ) (j : Fin 3) :
    dy j (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) =
      fun x => driftT (dy j Φ) x - (ν : ℝ) • lapT (dy j Φ) x + (μ : ℂ) • dy j Φ x := by
  have hD : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hdr : ContDiff ℝ ∞ (driftT Φ) := by
    have h1 := (contDiff_dτ hΦ).neg
    have h2 := (contDiff_radialT hΦ).const_smul (1 / 2 : ℝ)
    have h3 := hΦ.const_smul (3 / 2 : ℝ)
    exact (h1.add h2).add h3
  have hlap : ContDiff ℝ ∞ (lapT Φ) := contDiff_lapT hΦ
  have hdrD : Differentiable ℝ (driftT Φ) := hdr.differentiable (by simp)
  have hlapD : Differentiable ℝ (lapT Φ) := hlap.differentiable (by simp)
  have hGeq : (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) =
      (driftT Φ + (-(ν : ℝ)) • lapT Φ) + ((-(1 / 2 : ℝ)) • Φ + (μ : ℂ) • Φ) := by
    funext x
    simp only [L0T, nuLapT, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
      sub_eq_add_neg, neg_smul]
    abel
  have hA : Differentiable ℝ (driftT Φ + (-(ν : ℝ)) • lapT Φ) :=
    hdrD.add (diffR_smul hlapD _)
  have hB : Differentiable ℝ ((-(1 / 2 : ℝ)) • Φ + (μ : ℂ) • Φ) :=
    (diffR_smul hD _).add (diffC_smul hD _)
  rw [hGeq, dy_add hA hB j, dy_add hdrD (diffR_smul hlapD _) j,
    dy_smul hlapD (-(ν : ℝ)) j, dy_add (diffR_smul hD _) (diffC_smul hD _) j,
    dy_smul hD (-(1 / 2 : ℝ)) j, dy_smulC hD (μ : ℂ) j, dy_driftT hΦ j, dy_lapT hΦ j]
  funext x
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, sub_eq_add_neg, neg_smul, smul_neg]
  abel

/-! ### Solenoidality of the scalar sum -/

theorem sum3_zero {ν μ : ℝ} {f0 f1 f2 : ℝ × Space → ℂ} (h0 : ContDiff ℝ ∞ f0)
    (h1 : ContDiff ℝ ∞ f1) (h2 : ContDiff ℝ ∞ f2) (hz : ∀ y, f0 y + f1 y + f2 y = 0)
    (x : ℝ × Space) :
    (driftT f0 x - (ν : ℝ) • lapT f0 x + (μ : ℂ) * f0 x) +
      (driftT f1 x - (ν : ℝ) • lapT f1 x + (μ : ℂ) * f1 x) +
      (driftT f2 x - (ν : ℝ) • lapT f2 x + (μ : ℂ) * f2 x) = 0 := by
  have hS : (fun y => f0 y + f1 y + f2 y) = fun _ => (0 : ℂ) := funext hz
  have h01 : ContDiff ℝ ∞ (fun y => f0 y + f1 y) := h0.add h1
  have eD : driftT (fun y => f0 y + f1 y + f2 y) x = driftT f0 x + driftT f1 x + driftT f2 x := by
    rw [driftT_add_pt (h01.differentiable (by simp)) (h2.differentiable (by simp)) x,
      driftT_add_pt (h0.differentiable (by simp)) (h1.differentiable (by simp)) x]
  have eL : lapT (fun y => f0 y + f1 y + f2 y) x = lapT f0 x + lapT f1 x + lapT f2 x := by
    rw [lapT_add_pt h01 h2 x, lapT_add_pt h0 h1 x]
  have z1 : driftT (fun y => f0 y + f1 y + f2 y) x = 0 := by
    rw [hS]; exact driftT_zero_pt x
  have z2 : lapT (fun y => f0 y + f1 y + f2 y) x = 0 := by
    rw [hS]; exact lapT_zero_pt x
  rw [eD] at z1
  rw [eL] at z2
  have hsum : f0 x + f1 x + f2 x = 0 := hz x
  simp only [Complex.real_smul]
  linear_combination z1 - (ν : ℂ) * z2 + (μ : ℂ) * hsum

/-! ### Solenoidality of `L₀ᵗΦ + μΦ` -/

/-- **Solenoidal phase test for the transposed free operator.** If `Φ` is a solenoidal phase
test, so is `L₀ᵗΦ + μΦ`. -/
theorem isSolTest_L0T_add {P ν μ : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsSolTest P Φ) :
    IsSolTest P (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) := by
  have hC : ContDiff ℝ ∞ Φ := hΦ.1.smooth
  refine ⟨(isPhaseTest_L0T hΦ.1 ν).add (hΦ.1.const_smul (μ : ℂ)), fun x => ?_⟩
  have hcomp : ∀ j : Fin 3, cproj j (dy j (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) x) =
      driftT (fun y => cproj j (dy j Φ y)) x - (ν : ℝ) • lapT (fun y => cproj j (dy j Φ y)) x +
        (μ : ℂ) * cproj j (dy j Φ x) := by
    intro j
    rw [congrFun (dy_L0T_add (ν := ν) (μ := μ) hC j) x]
    simp only [map_add, map_sub, map_smul, cproj_smul_C, driftT_cproj (contDiff_dy hC j),
      lapT_cproj (contDiff_dy hC j)]
  have hz : ∀ y, cproj 0 (dy 0 Φ y) + cproj 1 (dy 1 Φ y) + cproj 2 (dy 2 Φ y) = 0 := by
    intro y
    have h := hΦ.2 y
    rw [Fin.sum_univ_three] at h
    exact h
  have key := sum3_zero (ν := ν) (μ := μ)
    (f0 := fun y => cproj 0 (dy 0 Φ y)) (f1 := fun y => cproj 1 (dy 1 Φ y))
    (f2 := fun y => cproj 2 (dy 2 Φ y))
    ((cproj 0).contDiff.comp (contDiff_dy hC 0))
    ((cproj 1).contDiff.comp (contDiff_dy hC 1))
    ((cproj 2).contDiff.comp (contDiff_dy hC 2)) hz x
  rw [show (∑ j : Fin 3, dy j (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) x j) =
      ∑ j : Fin 3, cproj j (dy j (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) x) from rfl]
  rw [Fin.sum_univ_three, hcomp 0, hcomp 1, hcomp 2]
  exact key

end UnforcedLeray.Short.PartIIIb.NearInst.PairDualAux
