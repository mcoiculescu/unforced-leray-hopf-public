import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2_2_3
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Joint smoothness of the `sep:resolvent` integrand (`PartIII-b:IIIb-D2/3/2/11/2/2/2/3/3`)

Source of record: `the November 2 reference manuscript`
3611-3617.  The integrand `-2 l^{2μ+2} Σ_{jk} ∂_k(K_{ν(1-l²)})_{ij}(y - l z) T_{jk}(τ + 2 log l, z)`
(`sepPhi`) is jointly `C^∞` in `((l,z),(τ,y))` for `l ∈ (0,1)`: the power `l^{2μ+2} = exp(log l (2μ+2))`
(`l > 0`), `log l` and `τ + 2 log l` are smooth, and the two factors are smooth by hypothesis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **Target** `PartIII-b:IIIb-D2/3/2/11/2/2/2/3/3`: joint smoothness of the `sep:resolvent`
integrand `sepPhiJ` on `l ∈ (0,1)`. -/
theorem sepPhiJointSmoothTop_of (h : SepKernelFactorJointSmooth) : SepPhiJointSmoothTop := by
  intro ν μ T hν hT i p x hp
  have hpos : (0 : ℝ) < p.1 := hp.1
  have hne : p.1 ≠ 0 := hpos.ne'
  -- the logarithm of the level `l = p.1`, as a function of the joint parameter
  have hl : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × Space) × (ℝ × Space) => Real.log q.1.1) (p, x) :=
    ContDiffAt.log contDiffAt_fst.fst hne
  -- the power factor `l^{2μ+2}` (for `l > 0`, `l^{c} = exp(log l · c)`)
  have hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × Space) × (ℝ × Space) => Complex.exp (((Real.log q.1.1 : ℝ) : ℂ) * (2 * μ + 2)))
      (p, x) := by
    have hc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : (ℝ × Space) × (ℝ × Space) => ((Real.log q.1.1 : ℝ) : ℂ) * (2 * μ + 2)) (p, x) :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp _ hl).mul contDiffAt_const
    exact hc.cexp
  have hopen : IsOpen {q : (ℝ × Space) × (ℝ × Space) | 0 < q.1.1} :=
    isOpen_lt continuous_const (continuous_fst.fst)
  have hC : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × Space) × (ℝ × Space) => ((q.1.1 : ℝ) : ℂ) ^ (2 * μ + 2)) (p, x) := by
    have hEv : (fun q : (ℝ × Space) × (ℝ × Space) => ((q.1.1 : ℝ) : ℂ) ^ (2 * μ + 2)) =ᶠ[𝓝 (p, x)]
        (fun q : (ℝ × Space) × (ℝ × Space) => Complex.exp (((Real.log q.1.1 : ℝ) : ℂ) * (2 * μ + 2))) := by
      filter_upwards [hopen.mem_nhds (show (0 : ℝ) < (p, x).1.1 from hpos)] with q hq
      have hq' : (0 : ℝ) < q.1.1 := hq
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hq'.ne'),
        Complex.ofReal_log hq'.le]
    exact hG.congr_of_eventuallyEq hEv
  -- the kernel factors (from `SepKernelFactorJointSmooth`), in `ℂ`
  have hK : ∀ j k : Fin 3, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × Space) × (ℝ × Space) =>
        ((fderiv ℝ (fun w => IIIa.heatLerayK (ν * (1 - q.1.1 ^ 2)) i j w) (q.2.2 - q.1.1 • q.1.2)
          (coordinateVector k) : ℝ) : ℂ)) (p, x) :=
    fun j k => Complex.ofRealCLM.contDiff.contDiffAt.comp _ (h ν hν i j k p x hp)
  -- the matrix entries `T(τ + 2 log l, z)`, in `ℂ`
  have hTpt : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × Space) × (ℝ × Space) => (q.2.1 + 2 * Real.log q.1.1, q.1.2)) (p, x) := by
    have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : (ℝ × Space) × (ℝ × Space) => 2 * Real.log q.1.1) (p, x) :=
      contDiffAt_const.mul hl
    exact (contDiffAt_snd.fst.add h2).prodMk contDiffAt_fst.snd
  have hT' : ∀ j k : Fin 3, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × Space) × (ℝ × Space) =>
        ((T (q.2.1 + 2 * Real.log q.1.1) q.1.2 j k : ℝ) : ℂ)) (p, x) :=
    fun j k => Complex.ofRealCLM.contDiff.contDiffAt.comp _
      (((hT j k).contDiffAt).comp _ hTpt)
  have hA : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × Space) × (ℝ × Space) => -2 * ((q.1.1 : ℝ) : ℂ) ^ (2 * μ + 2)) (p, x) :=
    contDiffAt_const.mul hC
  have hS : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × Space) × (ℝ × Space) => ∑ j : Fin 3, ∑ k : Fin 3,
        ((fderiv ℝ (fun w => IIIa.heatLerayK (ν * (1 - q.1.1 ^ 2)) i j w) (q.2.2 - q.1.1 • q.1.2)
          (coordinateVector k) : ℝ) : ℂ) * ((T (q.2.1 + 2 * Real.log q.1.1) q.1.2 j k : ℝ) : ℂ))
      (p, x) :=
    ContDiffAt.sum fun j _ => ContDiffAt.sum fun k _ => (hK j k).mul (hT' j k)
  unfold sepPhiJ sepPhi
  exact hA.mul hS

end UnforcedLeray.Short.PartIIIb.Concrete
