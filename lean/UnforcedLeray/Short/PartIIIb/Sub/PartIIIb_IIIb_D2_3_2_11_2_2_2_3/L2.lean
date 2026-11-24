import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2_2_3
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Joint smoothness of the separated kernel factor (`PartIII-b:IIIb-D2/3/2/11/2/2/2/3/2`)

Source of record: `the November 2 reference manuscript`
3604-3617.  For `ν > 0` and `p.1 ∈ (0,1)` the time `ν(1-p.1²)` is positive, so the parametric
derivative `∂_k K_{ν(1-l²)}(y - l z)` is `C^∞` jointly in `((l,z),(τ,y))`: it is the `fderiv` in the
space variable of the jointly `C^∞` map `(t,x) ↦ K_t(x)` (`HeatLerayKJointSmoothTop`), composed
with the smooth maps `q ↦ ν(1-q₁₁²)` and `q ↦ y - l z`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **Target** `PartIII-b:IIIb-D2/3/2/11/2/2/2/3/2`: joint smoothness of the kernel factor
`∂_k K_{ν(1-l²)}(y - l z)` on `l ∈ (0,1)`. -/
theorem sepKernelFactorJointSmooth_of (h : HeatLerayKJointSmoothTop) : SepKernelFactorJointSmooth := by
  intro ν hν i j k p x hp
  have ht : 0 < ν * (1 - p.1 ^ 2) := by
    have h1 := hp.1
    have h2 := hp.2
    have h3 : p.1 ^ 2 < 1 := by nlinarith
    exact mul_pos hν (sub_pos.2 h3)
  have hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × Space) × (ℝ × Space) => q.2.2 - q.1.1 • q.1.2) (p, x) :=
    contDiffAt_snd.snd.sub (contDiffAt_fst.fst.smul contDiffAt_fst.snd)
  have hmap : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun r : ((ℝ × Space) × (ℝ × Space)) × Space => (ν * (1 - r.1.1.1 ^ 2), r.2))
      ((p, x), x.2 - p.1 • p.2) := by
    have hc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun r : ((ℝ × Space) × (ℝ × Space)) × Space => ν * (1 - r.1.1.1 ^ 2)) ((p, x), x.2 - p.1 • p.2) :=
      contDiffAt_const.mul (contDiffAt_const.sub (contDiffAt_fst.fst.fst.pow 2))
    exact hc.prodMk contDiffAt_snd
  have hinner : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun r : ℝ × Space => IIIa.heatLerayK r.1 i j r.2) (ν * (1 - p.1 ^ 2), x.2 - p.1 • p.2) :=
    h i j _ ht
  have hfu : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (fun (q : (ℝ × Space) × (ℝ × Space)) (w : Space) =>
        IIIa.heatLerayK (ν * (1 - q.1.1 ^ 2)) i j w)) ((p, x), x.2 - p.1 • p.2) := by
    have heq : Function.uncurry (fun (q : (ℝ × Space) × (ℝ × Space)) (w : Space) =>
        IIIa.heatLerayK (ν * (1 - q.1.1 ^ 2)) i j w) =
        (fun r : ℝ × Space => IIIa.heatLerayK r.1 i j r.2) ∘
          (fun r : ((ℝ × Space) × (ℝ × Space)) × Space => (ν * (1 - r.1.1.1 ^ 2), r.2)) := by
      funext r
      rfl
    rw [heq]
    exact ContDiffAt.comp (((p, x), x.2 - p.1 • p.2)) hinner hmap
  have key := ContDiffAt.fderiv
    (f := fun (q : (ℝ × Space) × (ℝ × Space)) (w : Space) =>
      IIIa.heatLerayK (ν * (1 - q.1.1 ^ 2)) i j w)
    (g := fun q : (ℝ × Space) × (ℝ × Space) => q.2.2 - q.1.1 • q.1.2)
    hfu hg sepTop_add_one_le
  exact key.clm_apply contDiffAt_const

end UnforcedLeray.Short.PartIIIb.Concrete
