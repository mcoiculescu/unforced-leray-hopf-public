import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Defs
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2

/-!
# `PDX0Rep` from two leaves (decomposition of `PartIII-b:C/rep/5/1/2/4/1/2/7`)

Source `the November 2 reference manuscript` 3611-3617 (`sep:resolvent`), 3708,
4171.  `wardX0` is the real part of `sepW μ - sepW (μ+1)`; `sepW_eq_integral` turns each into an
integral over `sepRho = vol|_{(0,1)} ⊗ vol`; the leaves are integrability and the change of
variables `l = e^{-(τ-σ)/2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Leaf 1 (integrability).**  Under the hypotheses of `PDX0Rep` (the finite `σ`-form moment),
the `l`-form integrands `sepPhi` (at `μ` and `μ+1`, every component) are `sepRho`-integrable, and
the phase-lag integrand `xKer` is volume-integrable.  Source 3604-3617: kernel bound
`IIIa.sepKernelBounds` (`j = 0`), `x - lz ≠ 0` from `ϱ(x - lz) ≥ ϱ x - l ϱ z > 0` on the support,
`PDSigmaToLambda` for the transfer from the `σ`-form, `measurable_oldPhys_entry`. -/
def PDX0RepIntegrable : Prop :=
  ∀ (ν μ R c : ℝ) (g : Chart → Ten3), 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ → μ ≤ 1 →
    Measurable g →
    ∀ (τ : ℝ) (x : Space), (∀ σ z, oldPhys R c g σ z ≠ 0 → ϱ z < ϱ x) →
      ∫⁻ e : ℝ × Space, (if e.1 < τ then ENNReal.ofReal (pdLam (τ - e.1) ^ (2 * μ + 3) *
          (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) else 0) *
        IIIa.srcNorm (oldPhys R c g) e.1 e.2 < ⊤ →
      (∀ i : Fin 3,
        Integrable (fun p => sepPhi ν (μ : ℂ) (oldPhys R c g) τ i p x) sepRho ∧
        Integrable (fun p => sepPhi ν ((μ : ℂ) + 1) (oldPhys R c g) τ i p x) sepRho) ∧
      Integrable (fun e : ℝ × Space =>
        if e.1 < τ then xKer ν μ (τ - e.1) (x - pdLam (τ - e.1) • e.2) (oldPhys R c g e.1 e.2)
        else 0) volume

/-- **Leaf 2 (change of variables).**  Same hypotheses: componentwise,
`∫_{sepRho} Re(sepPhi μ - sepPhi (μ+1)) = ∫_{σ<τ,z} (xKer(τ-σ, x - λz) : T)_i`.  Source 3611-3617:
`l = pdLam (τ - σ)`, `dl = (l/2) dσ` (`integral_image_eq_integral_abs_deriv_smul`), so
`-2 l^{2μ+2}(1-l²) dl = -(λ^{2μ+3} - λ^{2μ+5}) dσ`; `(l:ℂ)^(2μ+2) = (l^(2μ+2):ℝ)` for `l > 0`
(`Complex.ofReal_cpow`); `integral_prod` on `volume`; `T(τ+2 log l, z)` with `σ = τ + 2 log l`;
`ν(1-l²)` is the heat time of `xKer`. -/
def PDX0RepCoV : Prop :=
  ∀ (ν μ R c : ℝ) (g : Chart → Ten3), 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ → μ ≤ 1 →
    Measurable g →
    ∀ (τ : ℝ) (x : Space), (∀ σ z, oldPhys R c g σ z ≠ 0 → ϱ z < ϱ x) →
      ∫⁻ e : ℝ × Space, (if e.1 < τ then ENNReal.ofReal (pdLam (τ - e.1) ^ (2 * μ + 3) *
          (‖x - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) else 0) *
        IIIa.srcNorm (oldPhys R c g) e.1 e.2 < ⊤ →
      ∀ i : Fin 3,
        ∫ p, (sepPhi ν (μ : ℂ) (oldPhys R c g) τ i p x -
            sepPhi ν ((μ : ℂ) + 1) (oldPhys R c g) τ i p x).re ∂sepRho =
        ∫ e : ℝ × Space, (if e.1 < τ then
          (xKer ν μ (τ - e.1) (x - pdLam (τ - e.1) • e.2) (oldPhys R c g e.1 e.2)) i else 0)

theorem pdX0Rep_of (h1 : PDX0RepIntegrable) (h2 : PDX0RepCoV) : PDX0Rep := by
  intro ν μ R c g hν hR hc hμ1 hμ2 hg τ x hsupp hfin
  obtain ⟨hA, hB⟩ := h1 ν μ R c g hν hR hc hμ1 hμ2 hg τ x hsupp hfin
  have h2' := h2 ν μ R c g hν hR hc hμ1 hμ2 hg τ x hsupp hfin
  ext i
  have hcomp : (∫ e : ℝ × Space, if e.1 < τ then
        xKer ν μ (τ - e.1) (x - pdLam (τ - e.1) • e.2) (oldPhys R c g e.1 e.2) else 0) i =
      ∫ e : ℝ × Space, (if e.1 < τ then
        (xKer ν μ (τ - e.1) (x - pdLam (τ - e.1) • e.2) (oldPhys R c g e.1 e.2)) i else 0) := by
    have := ContinuousLinearMap.integral_comp_comm
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i) hB
    refine Eq.trans this.symm ?_
    congr 1
    funext e
    by_cases h : e.1 < τ <;> simp [h]
  rw [hcomp, ← h2' i]
  unfold wardX0
  simp only []
  rw [sepW_eq_integral ν (μ : ℂ) (oldPhys R c g) τ i x (hA i).1,
    sepW_eq_integral ν ((μ : ℂ) + 1) (oldPhys R c g) τ i x (hA i).2,
    ← integral_sub (hA i).1 (hA i).2]
  exact (integral_re ((hA i).1.sub (hA i).2)).symm

end UnforcedLeray.Short.PartIIIb.Concrete

end
