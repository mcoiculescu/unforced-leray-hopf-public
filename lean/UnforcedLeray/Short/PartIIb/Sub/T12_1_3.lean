import UnforcedLeray.Short.PartIIb.Sub.T12_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.CylDivCurlFreeZero

/-!
# Part II-b, task `PartII-b:T12/1/3` (`CylHelmholtzUnique`): decomposition into leaves

Source: `the November 2 reference manuscript` lines 1670, 1923-1926.
Mollify `D`; the mollified fields are smooth, periodic, bounded, in `L^r`, satisfy the same weak
identities (`CylMollApprox`); smooth fields with the weak identities satisfy the identities
pointwise (`CylSmoothWeakToPointwise`); `cylDivCurlFreeZero` kills each mollification, and the
a.e. limit gives `D = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Weak divergence-free identity for a field on the cylinder (the first hypothesis of
`CylHelmholtzUnique`). -/
def CylWeakDiv (c : ℝ) (D : ℝ × ℝ → CMerid) : Prop :=
  ∀ φ : ℝ × ℝ → ℝ, CylTest c φ →
      ∫ z, (D z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + D z 1 * (fderiv ℝ φ z (0, 1) : ℂ))
        ∂(UnforcedLeray.Cyl.avgμ c) = 0

/-- Orthogonality to solenoidal tests (the second hypothesis of `CylHelmholtzUnique`). -/
def CylWeakSol (c : ℝ) (D : ℝ × ℝ → CMerid) : Prop :=
  ∀ Ψ : ℝ × ℝ → Fin 2 → ℝ, CylSolTest c Ψ →
      ∫ z, ∑ i : Fin 2, D z i * (Ψ z i : ℂ) ∂(UnforcedLeray.Cyl.avgμ c) = 0

/-- A smooth bounded `c`-periodic field in `L^r(avgμ c)`. -/
def CylSmoothField (c r : ℝ) (E : ℝ × ℝ → CMerid) : Prop :=
  CylLp c r E ∧ (∀ i : Fin 2, ContDiff ℝ ∞ (fun z => E z i)) ∧
    (∃ M : ℝ, ∀ z i, ‖E z i‖ ≤ M) ∧
    ∀ i : Fin 2, MemLp (fun z => E z i) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)

/-- **Leaf `PartII-b:T12/1/3/1`** (SP 1923-1926, mollification `E_n = D * ρ_{ε_n}`, `ε_n → 0`,
`2ε_n < c`): `E_n` is smooth, periodic, bounded (Hölder on at most two cells), in `L^r(avgμ c)`;
the identities pass to `E_n` since `φ * ρ̌_ε` is a `CylTest` and `Ψ * ρ̌_ε` a `CylSolTest`
(Fubini + cell unfolding); `E_n → D` a.e. (Lebesgue differentiation, `D` locally integrable by
periodicity + `L^r(avgμ)`). -/
def CylMollApprox : Prop :=
  ∀ c r : ℝ, 0 < c → 1 < r → ∀ D : ℝ × ℝ → CMerid, CylLp c r D → CylWeakDiv c D → CylWeakSol c D →
    ∃ E : ℕ → ℝ × ℝ → CMerid, (∀ n, CylSmoothField c r (E n)) ∧
      (∀ n, CylWeakDiv c (E n)) ∧ (∀ n, CylWeakSol c (E n)) ∧
      ∀ᵐ z ∂(UnforcedLeray.Cyl.avgμ c), Tendsto (fun n => E n z) atTop (𝓝 (D z))

/-- **Leaf `PartII-b:T12/1/3/2`** (integration by parts, `Lib/Cylinder/IBP.lean`): a smooth
bounded `c`-periodic field with `∫ E·∇φ = 0` (all `CylTest φ`) and `∫ E·∇^⊥φ = 0` has
`div E = 0` and `curl E = 0` pointwise (a continuous function orthogonal to all tests, using
periodized bumps as tests). Complex-valued derivative form. -/
def CylSmoothWeakToPointwise : Prop :=
  ∀ c r : ℝ, 0 < c → ∀ E : ℝ × ℝ → CMerid, CylSmoothField c r E → CylWeakDiv c E → CylWeakSol c E →
    (∀ z : ℝ × ℝ, fderiv ℝ (fun y => E y 0) z (1, 0) + fderiv ℝ (fun y => E y 1) z (0, 1) = 0) ∧
    (∀ z : ℝ × ℝ, fderiv ℝ (fun y => E y 1) z (1, 0) - fderiv ℝ (fun y => E y 0) z (0, 1) = 0)

private lemma fderiv_comp_clm (L : ℂ →L[ℝ] ℝ) {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (z d : ℝ × ℝ) :
    fderiv ℝ (fun y => L (f y)) z d = L (fderiv ℝ f z d) := by
  have hd : DifferentiableAt ℝ f z := (hf.differentiable (by simp)).differentiableAt
  rw [show (fun y => L (f y)) = L ∘ f from rfl, fderiv_comp z L.differentiableAt hd]
  simp

theorem cylHelmholtzUnique_of (h1 : CylMollApprox) (h2 : CylSmoothWeakToPointwise) :
    CylHelmholtzUnique := by
  intro c r hc hr D hD hdiv hsol
  obtain ⟨E, hE, hEd, hEs, hlim⟩ := h1 c r hc hr D hD hdiv hsol
  have key : ∀ n i, ∀ z, E n z i = 0 := by
    intro n
    obtain ⟨⟨hper, hL⟩, hsm, ⟨M, hM⟩, hcoord⟩ := hE n
    obtain ⟨hpd, hpc⟩ := h2 c r hc (E n) (hE n) (hEd n) (hEs n)
    have hr1 : (1 : ℝ) ≤ r := hr.le
    have hmem : ∀ (L : ℂ →L[ℝ] ℝ), (∀ w, ‖L w‖ ≤ ‖w‖) → ∀ i : Fin 2,
        MemLp (fun z => L (E n z i)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) := by
      intro L hLn i
      have := hcoord i
      exact this.of_le_mul (L.continuous.comp_aestronglyMeasurable this.1) (by
        refine Eventually.of_forall fun z => ?_
        simpa using hLn _ :
          ∀ᵐ x ∂(UnforcedLeray.Cyl.avgμ c), ‖L (E n x i)‖ ≤ 1 * ‖E n x i‖)
    have hz : ∀ (L : ℂ →L[ℝ] ℝ), (∀ w, ‖L w‖ ≤ ‖w‖) →
        (∀ i : Fin 2, ∀ z, L (E n z i) = 0) := by
      intro L hLn
      have := cylDivCurlFreeZero c r (fun z => L (E n z 0)) (fun z => L (E n z 1)) hc hr1
        (L.contDiff.comp (hsm 0)) (L.contDiff.comp (hsm 1))
        (fun z => by simp [hper z]) (fun z => by simp [hper z])
        ⟨M, fun z => ⟨(hLn _).trans (hM z 0) |> fun h => by simpa using h,
          (hLn _).trans (hM z 1) |> fun h => by simpa using h⟩⟩
        (hmem L hLn 0) (hmem L hLn 1)
        (fun z => by
          rw [fderiv_comp_clm L (hsm 0) z, fderiv_comp_clm L (hsm 1) z, ← map_add, hpd z, map_zero])
        (fun z => by
          rw [fderiv_comp_clm L (hsm 1) z, fderiv_comp_clm L (hsm 0) z, ← map_sub, hpc z, map_zero])
      intro i z
      fin_cases i
      · exact (this z).1
      · exact (this z).2
    intro i z
    have h1 := hz Complex.reCLM (fun w => Complex.abs_re_le_norm w) i z
    have h2 := hz Complex.imCLM (fun w => Complex.abs_im_le_norm w) i z
    exact Complex.ext (by simpa using h1) (by simpa using h2)
  filter_upwards [hlim] with z hz
  have : D z = 0 := by
    have h0 : (fun n => E n z) = fun _ => (0 : CMerid) := by
      funext n; ext i; exact key n i z
    rw [h0] at hz
    exact tendsto_nhds_unique hz tendsto_const_nhds
  simpa using this

end UnforcedLeray.Short.IIb
