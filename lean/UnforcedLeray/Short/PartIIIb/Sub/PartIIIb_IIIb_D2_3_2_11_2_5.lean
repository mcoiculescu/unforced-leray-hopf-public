import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2

/-!
# `OutPrimSmoothInf` decomposed (`PartIII-b:IIIb-D2/3/2/11/2/5`, source 4177-4179)

Source of record: `the November 2 reference manuscript`.
`outPrimSmoothInf_of` derives `OutPrimSmoothInf` from

* `WardX0SmoothInf` (joint `C^∞` of `X₀` on the young region, 3604-3621; in the
  parent Sub file),
* `WardX0IntegrandDecay` (all-order decay of the integrand `ρ X₀,z(τ,ρ,0,z)` on the half plane,
  source 4177-4179),
* `ParamIntSmooth` (generic analysis: smooth dependence of `-∫_{Ioi r} G` on `(τ,r,z)`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **Source fact (all-order decay of the primitive's integrand)** (source 4177-4179, from the
bounds `|∂^α X₀(τ,y)| ≤ C_α|y|^{-4}` for `|y|` large of the separated kernel estimates
`IIIa.SepKernelBounds`, old data supported in `ϱ ≤ R√(5ν/6)`; the factor `ρ` and the embedding
`(τ,ρ,z) ↦ (τ,(ρ,0,z))` only lose `ρ`, giving `ρ^{-3} ≤ ρ^{-2}`): for every order `n` and compact
set `K` of `(τ,z)` there are `ρ₀ > max(1, R√(5ν/6))` and `C` with
`‖D^n (ρ X₀,z)(τ,ρ,z)‖ ≤ C ρ^{-2}` for `(τ,z) ∈ K`, `ρ ≥ ρ₀`. -/
def WardX0IntegrandDecay : Prop :=
  ∀ (ν μ R c : ℝ) (g : Chart → Ten3), 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ → IsSmoothOld c ν g →
    ∀ (n : ℕ) (K : Set (ℝ × ℝ)), IsCompact K →
      ∃ ρ₀ C : ℝ, 1 ≤ ρ₀ ∧ R * Real.sqrt (5 * ν / 6) < ρ₀ ∧
        ∀ τ z : ℝ, (τ, z) ∈ K → ∀ ρ : ℝ, ρ₀ ≤ ρ →
          ‖iteratedFDeriv ℝ n
              (fun x : ℝ × ℝ × ℝ => x.2.1 * wardX0 ν μ R c g x.1 !₂[x.2.1, 0, x.2.2] 2)
              (τ, ρ, z)‖ ≤ C / ρ ^ 2

/-- **Generic analysis (differentiation under the integral to all orders plus FTC for the lower
limit)**: if `G(τ,ρ,z)` is `C^∞` on `ρ > r₀` and every derivative is bounded by `C ρ^{-2}` for
`ρ ≥ ρ₀` uniformly for `(τ,z)` in a compact set, then `(τ,r,z) ↦ -∫_{Ioi r} G(τ,ρ,z) dρ` is `C^∞`
on `r > r₀`. (`hasFDerivAt_integral_of_dominated_of_fderiv_le`, induction on the order; reduce the
lower limit via `∫_{Ioi r} = ∫_{Ioi r₁} + ∫_{Ioc r r₁}`-type splitting, `r₀ < r₁ < r`.) -/
def ParamIntSmooth : Prop :=
  ∀ (G : ℝ × ℝ × ℝ → ℝ) (r₀ : ℝ),
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G {x | r₀ < x.2.1} →
    (∀ (n : ℕ) (K : Set (ℝ × ℝ)), IsCompact K →
      ∃ ρ₀ C : ℝ, 1 ≤ ρ₀ ∧ r₀ < ρ₀ ∧
        ∀ τ z : ℝ, (τ, z) ∈ K → ∀ ρ : ℝ, ρ₀ ≤ ρ →
          ‖iteratedFDeriv ℝ n G (τ, ρ, z)‖ ≤ C / ρ ^ 2) →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × ℝ × ℝ => -∫ ρ in Ioi x.2.1, G (x.1, ρ, x.2.2)) {x | r₀ < x.2.1}

theorem outPrimSmoothInf_of (h1 : WardX0SmoothInf) (h2 : WardX0IntegrandDecay)
    (h3 : ParamIntSmooth) : OutPrimSmoothInf := by
  intro ν μ R c g hν hR hc hμ hg
  have hS := h1 ν μ R c g hν hR hc hμ hg
  set r₀ := R * Real.sqrt (5 * ν / 6) with hr₀
  have hr₀' : 0 ≤ r₀ := by positivity
  let e : ℝ × ℝ × ℝ → ℝ × Space := fun x => (x.1, !₂[x.2.1, 0, x.2.2])
  have he : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) e := by
    refine contDiff_fst.prodMk ?_
    have h3' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ × ℝ × ℝ => (![x.2.1, 0, x.2.2] : Fin 3 → ℝ)) := by
      refine contDiff_pi.2 fun i => ?_
      fin_cases i
      · exact contDiff_fst.comp contDiff_snd
      · exact contDiff_const
      · exact contDiff_snd.comp contDiff_snd
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp h3'
  have hmaps : Set.MapsTo e {x : ℝ × ℝ × ℝ | r₀ < x.2.1} {x : ℝ × Space | x.2 ∈ youngOpen ν R} := by
    intro x hx
    have hx' : r₀ < x.2.1 := hx
    show r₀ < ϱ (!₂[x.2.1, 0, x.2.2] : Space)
    have : ϱ (!₂[x.2.1, 0, x.2.2] : Space) = x.2.1 := by
      unfold ϱ
      simp [Real.sqrt_sq (hr₀'.trans hx'.le)]
    rw [this]; exact hx'
  have hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × ℝ × ℝ => x.2.1 * wardX0 ν μ R c g x.1 !₂[x.2.1, 0, x.2.2] 2)
      {x | r₀ < x.2.1} := by
    generalize wardX0 ν μ R c g = W at hS ⊢
    have hw : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ × ℝ × ℝ => W x.1 !₂[x.2.1, 0, x.2.2]) {x | r₀ < x.2.1} :=
      hS.comp he.contDiffOn hmaps
    have hp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : Space => v 2) :=
      (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff
    exact (contDiff_fst.comp contDiff_snd).contDiffOn.mul (hp.comp_contDiffOn hw)
  have := h3 _ r₀ hG (fun n K hK => h2 ν μ R c g hν hR hc hμ hg n K hK)
  simpa [outPrim] using this

end UnforcedLeray.Short.PartIIIb.Concrete
