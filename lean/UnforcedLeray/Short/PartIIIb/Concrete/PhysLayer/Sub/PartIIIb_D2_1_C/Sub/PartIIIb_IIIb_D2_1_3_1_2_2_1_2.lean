import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLocInt

/-!
# Decomposition of `MollDivKernel` (divergence of `ρ ⋆ Φ` via the periodised reflected kernel)

Source: `the November 2 reference manuscript`
lines 1351-1362.  With `κ_x(w) = ρ_norm(x - w)` and its periodisation
`φ_x(w) = ∑_{k∈ℤ} κ_x(w + (kP, 0))` (a finite sum on compacts), the identity is
`∑_j ∂_{y_j}(ρ ⋆ Φ)_j(x) = -P ⟪∇φ_x, Φ⟫`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The reflected kernel `κ_x(w) = ρ_norm(x - w)` as a complex scalar field. -/
def reflK (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space) : ℝ × Space → ℂ :=
  fun w => ((ρ.normed volume (x - w) : ℝ) : ℂ)

/-- The periodised reflected kernel `φ_x(w) = ∑_k κ_x(w + (kP, 0))`. -/
def perK (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space) (P : ℝ) : ℝ × Space → ℂ :=
  fun w => ∑' k : ℤ, reflK ρ x (w + ((k : ℝ) * P, (0 : Space)))

/-- **S1** (lines 1351-1362): `φ_x` is a phase test (smooth: locally finite sum; periodic: reindex
`k ↦ k+1`; `y`-compact support from the support of `ρ`). -/
def PerKPhaseTest : Prop :=
  ∀ (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space) {P : ℝ}, 0 < P → IsPhaseTest P (perK ρ x P)

/-- **S2** (lines 1351-1362; differentiation under the convolution integral): for locally integrable
`Φ`, `∂_{y_j}(ρ ⋆ Φ)_j(x) = ∫ -(∂_{y_j} κ_x)(w) Φ_j(w) dw`. -/
def DyMollP : Prop :=
  ∀ (ρ : ContDiffBump (0 : ℝ × Space)) (Φ : ℝ × Space → CVec3), LocallyIntegrable Φ volume →
    ∀ (x : ℝ × Space) (j : Fin 3),
      dy j (mollP ρ Φ) x j = ∫ w, -(dy j (reflK ρ x) w) * Φ w j

/-- **S3** (lines 1351-1362; fold `ℝ` into the cell `(0,P]`): for integrable `G`,
`∫ G = ∫_{cellBase P} ∑_k G(w + (kP,0))`. -/
def FoldCell : Prop :=
  ∀ {P : ℝ}, 0 < P → ∀ {G : ℝ × Space → ℂ}, Integrable G volume →
    ∫ w, G w = ∫ w in cellBase P, ∑' k : ℤ, G (w + ((k : ℝ) * P, (0 : Space)))

/-- **S4** (lines 1351-1362; differentiation of the locally finite periodisation):
`∂_{y_j} φ_x(w) = ∑_k ∂_{y_j} κ_x (w + (kP,0))`. -/
def DyPerK : Prop :=
  ∀ (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space) {P : ℝ}, 0 < P → ∀ (j : Fin 3) (w : ℝ × Space),
    dy j (perK ρ x P) w = ∑' k : ℤ, dy j (reflK ρ x) (w + ((k : ℝ) * P, (0 : Space)))

/-- **S5** (lines 1351-1362): `phaseInt` is `P⁻¹` times the cell integral, for integrable `G` on the cell. -/
def PhaseIntCell : Prop :=
  ∀ {P : ℝ}, 0 < P → ∀ (G : ℝ × Space → ℂ), IntegrableOn G (cellBase P) volume →
    phaseInt P G = P⁻¹ • ∫ w in cellBase P, G w

/-- The divergence identity with the periodised kernel (assembly of S2-S5; needs `Φ` a.e. periodic,
locally integrable and `y`-compactly supported so that all the integrals converge absolutely). -/
def DivIdentity : Prop :=
  ∀ (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space) {P : ℝ}, 0 < P →
    ∀ Φ : ℝ × Space → CVec3, LocallyIntegrable Φ volume → YCompactSupp Φ →
      (∀ᵐ z : ℝ × Space, Φ (z.1 + P, z.2) = Φ z) →
        ∑ j : Fin 3, dy j (mollP ρ Φ) x j = (-(P : ℂ)) * pairF P (gradT (perK ρ x P)) Φ

/-- Reduction of `MollDivKernel` to the phase-test property of `φ_x` and the divergence identity. -/
theorem mollDivKernel_of (h1 : PerKPhaseTest) (h2 : DivIdentity) : MollDivKernel := by
  intro P ν μ hP hP1 hν hμ Φ g hdom hsupp ρ x
  have hli : LocallyIntegrable Φ volume := mollLocInt P ν μ hP hP1 hν hμ Φ g hdom hsupp
  have hper : ∀ᵐ z : ℝ × Space, Φ (z.1 + P, z.2) = Φ z := hdom.mem.periodic
  exact ⟨perK ρ x P, -(P : ℂ), h1 ρ x hP, h2 ρ x hP Φ hli hsupp hper⟩

end UnforcedLeray.Short.PartIIIb.Concrete
