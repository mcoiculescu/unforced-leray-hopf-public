import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T08_1_2

/-!
# Part II-b, task `PartII-b:T09/1/2` (`DivSmoothPt`): three leaves

Source of record: `the November 2 reference manuscript`, lines 1639-1668
(`div(√s b) = s[(∂_q - εK) b_r + ∂_η b_z]`, `∂_q - εK = Q_ε + ε`) and 1912-1916.

For nice `b`, `u = N_v b` is a phase test (leaf `NvCNicePhaseTest`, already proved in
`Tasks/DriftNvC/Smooth/SmoothPt/NicePhaseTest.lean` as `nvCNicePhaseTest_proof`).  The identity
splits as a spatial integration by parts valid for every pair of phase tests (`DivIBP`) and a
pointwise divergence identity for the ring lift (`NvCDivOffAxis`, `NvCDivOnAxis`).

Proved here: `divSmoothPt_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-- **Leaf `T09/1/2/1`**: spatial integration by parts, `⟪∇φ, u⟫ = -⟪φ, div u⟫`, for a scalar phase
test `φ` and a `ℂ³`-valued phase test `u` (both smooth, `P`-periodic in `τ`, bounded `y`-support).
Proof: for each `τ` and each coordinate `j`, `∫ ∂_j(φ u_j) dy = 0` (compact support;
`MeasureTheory.integral_fderiv...`/divergence theorem on `ℝ³`, or Fubini + 1-D FTC), the product
rule `∂_j(φ u_j) = ∂_jφ u_j + φ ∂_j u_j`, then sum over `j` and integrate over `τ ∈ (0,P]`. -/
def DivIBP : Prop :=
  ∀ (P : ℝ) (φ : ℝ × Space → ℂ) (u : ℝ × Space → CVec3), 0 < P → IsPhaseTest P φ →
    IsPhaseTest P u →
    pairF P (gradT φ) u = -phaseInt P (fun p => φ p * ∑ j : Fin 3, dy j u p j)

/-- **Leaf `T09/1/2/2`** (SP 1658-1660, 1912-1916): pointwise divergence identity off the axis,
`div_y N_v b = sLift (s[(Q_ε b)_r + ε b_r + (∂_η b)_z])` with the classical `Q_ε b`, `∂_η b`
(`classOp (vQ ε) (dQ ε) b`, `classOp vEta dZero b`).  Chain rule in the chart
`(τ,y) ↦ (age, phase, trans)` of `Axi.chart` (`Lib/Axisymmetric/RingChart.lean`,
`Lib/AxisymmetricB/Lift.lean`): `∂_ρ(√s F) = s Q_ε F`, `∂_z(√s F) = s ∂_η F`, with
`Q_ε = ∂_q - ε(2s∂_s + η∂_η + 1)` (SP 1651-1653); pattern
`Tasks/DriftNvC/Smooth/SmoothPt/DriftOffAxis.lean`. -/
def NvCDivOffAxis : Prop :=
  ∀ (c ε : ℝ) (b : CProf), 0 < c → 0 < ε → NiceProf c b → ∀ p : ℝ × Space,
    p.2 ∉ Axi.axis →
    ∑ j : Fin 3, dy j (NvC ε⁻¹ b) p j =
      sLift ε⁻¹ (gDiv ε b (classOp (vQ ε) (dQ ε) b) (classOp vEta dZero b)) p

/-- **Leaf `T09/1/2/3`**: on the axis (a closed set) both sides vanish: `NiceProf` forces
`s ∈ [s₀, s₁]` so `N_v b` vanishes on a neighbourhood of the axis (hence all its derivatives),
and `sLift (gDiv ..)` is `0` there since `gDiv` carries the factor `s` and `age = 0` on the axis
(pattern `Tasks/DriftNvC/Smooth/SmoothPt/DriftOnAxis.lean`). -/
def NvCDivOnAxis : Prop :=
  ∀ (c ε : ℝ) (b : CProf), 0 < c → 0 < ε → NiceProf c b → ∀ p : ℝ × Space,
    p.2 ∈ Axi.axis →
    ∑ j : Fin 3, dy j (NvC ε⁻¹ b) p j =
      sLift ε⁻¹ (gDiv ε b (classOp (vQ ε) (dQ ε) b) (classOp vEta dZero b)) p

theorem divSmoothPt_of (h0 : NvCNicePhaseTest) (h1 : DivIBP) (h2 : NvCDivOffAxis)
    (h3 : NvCDivOnAxis) : DivSmoothPt := by
  intro c ε b hc hε hb φ hφ
  have hP : 0 < 2 * ε * c := by positivity
  rw [h1 _ φ _ hP hφ (h0 c ε b hc hε hb)]
  congr 2
  funext p
  congr 1
  by_cases hp : p.2 ∈ Axi.axis
  · exact h3 c ε b hc hε hb p hp
  · exact h2 c ε b hc hε hb p hp

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.divSmoothPt_of
