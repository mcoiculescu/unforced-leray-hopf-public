import UnforcedLeray.Short.PartIIa.Sub.F05_1
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.ParamIntegralSmooth

/-!
# Part II-a, task `PartII-a:F05a`: phase-space operators pass under the integral

Target: `OpsUnderIntegral` (defined in `Short/PartII-a/Sub/F05_1.lean`). For a parameter family
`G x : ℝ × Space → ℂ³` satisfying `ParamFamilyHyp`, the pointwise values `G_x(p)`, `∂_τ G_x(p)`,
`∂_{y_j} G_x(p)`, `(y·∇)G_x(p)`, `Δ G_x(p)` are integrable in `x`, and the operators `∂_τ`,
`∂_{y_j}`, `y·∇`, `Δ` commute with `∫ G_x dm`.

Source of record: `the November 2 reference manuscript`. The operators are those of
line 139 (`𝒯₀ = ∂_τ - ½ y·∇`) and line 1344 (`𝒯 = ∂_τ - y·∇/2`). The Prop is an analysis lemma
with no single source step, so no other tex lines are cited.

Proof outline (the smoothness and derivative formula come from `paramIntegralSmooth_proof`):
* `integrable_iterCMM`, `integrable_iter`: `x ↦ D^k G_x(p)` and `x ↦ D^k G_x(p) v` are integrable,
  from the bound `b_k` and a.e.-measurability, through `ContinuousLinearMap.integrable_comp`.
* `iter_integral_eval`: `D^k Ψ(p) v = ∫ D^k G_x(p) v dm`, through `ContinuousLinearMap.integral_comp_comm`
  for the evaluation map `ContinuousMultilinearMap.apply`.
* `fderiv_fderiv_apply`, `dy_dy_eq`: second derivatives of a smooth function in coordinate directions.
* `fderiv_integral_eq`, `integrable_fderiv`: first derivatives in a direction, from the `k = 1` case.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace

namespace UnforcedLeray.Short.PartIIa

namespace OpsUnderIntegralAux

variable {X : Type} [MeasurableSpace X]

/-- The `k`-th derivative of the family at `p` is integrable in `x`, as a multilinear map. -/
theorem integrable_iterCMM {m : Measure X} {G : X → ℝ × Space → CVec3}
    (hG : ParamFamilyHyp m G) (k : ℕ) (p : ℝ × Space) :
    Integrable (fun x => iteratedFDeriv ℝ k (G x) p) m := by
  obtain ⟨b, hb, hbd⟩ := hG.2.2 k
  exact Integrable.mono' hb (hG.2.1 k p) (hbd.mono fun x hx => hx p)

/-- The `k`-th derivative of the family at `p`, evaluated on a tuple of vectors, is integrable. -/
theorem integrable_iter {m : Measure X} {G : X → ℝ × Space → CVec3}
    (hG : ParamFamilyHyp m G) (k : ℕ) (p : ℝ × Space) (v : Fin k → ℝ × Space) :
    Integrable (fun x => iteratedFDeriv ℝ k (G x) p v) m :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => ℝ × Space) CVec3 v).integrable_comp
    (integrable_iterCMM hG k p)

/-- Evaluating the `k`-th derivative of the parameter integral on a tuple of vectors commutes with
the integral. -/
theorem iter_integral_eval {m : Measure X} {G : X → ℝ × Space → CVec3}
    (hG : ParamFamilyHyp m G) (k : ℕ) (p : ℝ × Space) (v : Fin k → ℝ × Space) :
    iteratedFDeriv ℝ k (fun q => ∫ x, G x q ∂m) p v = ∫ x, iteratedFDeriv ℝ k (G x) p v ∂m := by
  rw [(paramIntegralSmooth_proof (ℝ × Space) X m G hG).2 k p]
  exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => ℝ × Space) CVec3 v).integral_comp_comm
    (integrable_iterCMM hG k p)).symm

/-- For a smooth `g`, the derivative of `q ↦ ∂_w g(q)` in the direction `v` is `D²g(p)(v, w)`. -/
theorem fderiv_fderiv_apply {g : ℝ × Space → CVec3} (hg : ContDiff ℝ ∞ g) (v w : ℝ × Space)
    (p : ℝ × Space) :
    fderiv ℝ (fun q => fderiv ℝ g q w) p v = iteratedFDeriv ℝ 2 g p ![v, w] := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) p :=
    ((hg.fderiv_right (m := 1) (by norm_cast)).differentiable one_ne_zero) p
  have hu : DifferentiableAt ℝ (fun _ : ℝ × Space => w) p := differentiableAt_const w
  have h1 := fderiv_clm_apply hd hu
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add] at h1
  rw [iteratedFDeriv_two_apply, h1]
  rfl

/-- The second derivative of a smooth function in two phase-space coordinate directions. -/
theorem dy_dy_eq {g : ℝ × Space → CVec3} (hg : ContDiff ℝ ∞ g) (j : Fin 3) (p : ℝ × Space) :
    dy j (dy j g) p
      = iteratedFDeriv ℝ 2 g p ![(0, coordinateVector j), (0, coordinateVector j)] :=
  fderiv_fderiv_apply hg (0, coordinateVector j) (0, coordinateVector j) p

/-- The first derivative of the parameter integral in a direction `v`. -/
theorem fderiv_integral_eq {m : Measure X} {G : X → ℝ × Space → CVec3}
    (hG : ParamFamilyHyp m G) (p : ℝ × Space) (v : ℝ × Space) :
    fderiv ℝ (fun q => ∫ x, G x q ∂m) p v = ∫ x, fderiv ℝ (G x) p v ∂m := by
  have h := iter_integral_eval hG 1 p ![v]
  simpa only [iteratedFDeriv_one_apply, Matrix.cons_val_zero] using h

/-- The directional derivative of the family at `p` is integrable in `x`. -/
theorem integrable_fderiv {m : Measure X} {G : X → ℝ × Space → CVec3}
    (hG : ParamFamilyHyp m G) (p : ℝ × Space) (v : ℝ × Space) :
    Integrable (fun x => fderiv ℝ (G x) p v) m := by
  have h := integrable_iter hG 1 p ![v]
  simpa only [iteratedFDeriv_one_apply, Matrix.cons_val_zero] using h

end OpsUnderIntegralAux

open OpsUnderIntegralAux in
/-- **Phase-space operators pass under the integral** (`OpsUnderIntegral`). -/
theorem opsUnderIntegral_proof : UnforcedLeray.Short.PartIIa.OpsUnderIntegral := by
  intro X _ m G hG p
  have hPsi := paramIntegralSmooth_proof (ℝ × Space) X m G hG
  have hint0 : Integrable (fun x => G x p) m := by
    have h := integrable_iter hG 0 p ![]
    simpa only [iteratedFDeriv_zero_apply] using h
  have hdτ : Integrable (fun x => dτ (G x) p) m := integrable_fderiv hG p (1, 0)
  have hdy : ∀ j : Fin 3, Integrable (fun x => dy j (G x) p) m :=
    fun j => integrable_fderiv hG p (0, coordinateVector j)
  have hdy_eq : ∀ j : Fin 3, dy j (fun q => ∫ x, G x q ∂m) p = ∫ x, dy j (G x) p ∂m :=
    fun j => fderiv_integral_eq hG p (0, coordinateVector j)
  have hsmul : ∀ j : Fin 3, Integrable (fun x => (p.2 j) • dy j (G x) p) m :=
    fun j => (hdy j).smul (p.2 j)
  have hrad : Integrable (fun x => radialT (G x) p) m := by
    have h := integrable_finsetSum (Finset.univ : Finset (Fin 3))
      (f := fun j x => (p.2 j) • dy j (G x) p) (fun j _ => hsmul j)
    exact h
  have hdd : ∀ j : Fin 3, Integrable (fun x => dy j (dy j (G x)) p) m := by
    intro j
    refine (integrable_iter hG 2 p ![(0, coordinateVector j), (0, coordinateVector j)]).congr ?_
    filter_upwards [hG.1] with x hx
    exact (dy_dy_eq hx j p).symm
  have hlap : Integrable (fun x => lapT (G x) p) m := by
    have h := integrable_finsetSum (Finset.univ : Finset (Fin 3))
      (f := fun j x => dy j (dy j (G x)) p) (fun j _ => hdd j)
    exact h
  have hdyy : ∀ j : Fin 3,
      dy j (dy j (fun q => ∫ x, G x q ∂m)) p = ∫ x, dy j (dy j (G x)) p ∂m := by
    intro j
    rw [dy_dy_eq hPsi.1 j p,
      iter_integral_eval hG 2 p ![(0, coordinateVector j), (0, coordinateVector j)]]
    apply integral_congr_ae
    filter_upwards [hG.1] with x hx
    exact (dy_dy_eq hx j p).symm
  refine ⟨hint0, hdτ, hdy, hrad, hlap, fderiv_integral_eq hG p (1, 0), hdy_eq, ?_, ?_⟩
  · show ∑ j : Fin 3, (p.2 j) • dy j (fun q => ∫ x, G x q ∂m) p
        = ∫ x, ∑ j : Fin 3, (p.2 j) • dy j (G x) p ∂m
    rw [integral_finsetSum (Finset.univ : Finset (Fin 3))
      (f := fun j x => (p.2 j) • dy j (G x) p) (fun j _ => hsmul j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hdy_eq j, integral_smul]
  · show ∑ j : Fin 3, dy j (dy j (fun q => ∫ x, G x q ∂m)) p
        = ∫ x, ∑ j : Fin 3, dy j (dy j (G x)) p ∂m
    rw [integral_finsetSum (Finset.univ : Finset (Fin 3))
      (f := fun j x => dy j (dy j (G x)) p) (fun j _ => hdd j)]
    exact Finset.sum_congr rfl fun j _ => hdyy j

end UnforcedLeray.Short.PartIIa
