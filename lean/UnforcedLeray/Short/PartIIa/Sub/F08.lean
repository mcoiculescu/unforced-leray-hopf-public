import UnforcedLeray.Short.PartIIa.StatementsFree
import UnforcedLeray.Short.PartIIa.Tasks.F01BodyResolvent
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation
import UnforcedLeray.Short.PartIIa.Tasks.F04MaximalDomain
import UnforcedLeray.Units.B0411
import UnforcedLeray.Units.B0421.Phase
import UnforcedLeray.Lib.LerayC.PhaseSol

/-!
# Part II-a, task `PartII-a:F08`: projected inverse, reduced to three leaf lemmas

Source `the November 2 reference manuscript` lines 1358-1359, 1498-1500
("Leray commutes with heat, dilation and phase translation, so projection preserves all
identities"). With `Rm = R_μ` from F01 and `f' = 𝐏 f`, put `w = R_μ f'`. The Leray projection
commutes with the Laplace integral of `𝒯_ν(t)` (leaves 1-3), so `w = 𝐏 R_μ f` is solenoidal
(`lerayY_isPhaseSolenoidal`); membership in `D_r` and the equation are as in F07.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **Leaf 1** (source 1498-1500): the complex Leray projection commutes with the free similarity
semigroup `S_ν(r)` on `L^p(ℝ³;ℂ³)` (it is `e^{r/2}` times heat time `ν(e^r-1)` composed with
dilation; use `lerayC_heat`, `lerayC_dilate`, and the definition of `B0421.freeC` as the
complexification of `B0418.freeSemigroupLp`). -/
def LerayCFreeComm : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤) (ν r : ℝ),
    (lerayC p hp1 hp).comp (B0421.freeC hp ν r) = (B0421.freeC hp ν r).comp (lerayC p hp1 hp)

/-- **Leaf 2** (source 1498-1500): the Leray projection commutes with the phase operator
`𝒯_ν(r) = (S_ν(r) slice-wise) ∘ (phase shift by -r)` on `Y_q`. -/
def LerayYPhaseTComm : Prop :=
  ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq1 : 1 < q) (hq : q ≠ ⊤) (P : ℝ) [Fact (0 < P)] (ν r : ℝ)
    (g : Yq P q),
    lerayY P q hq1 hq (B0421.phaseT hq ν r g) = B0421.phaseT hq ν r (lerayY P q hq1 hq g)

/-- **Leaf 3** (source 1498-1500): `𝐏` commutes with the Laplace integral `R_μ` of `𝒯_ν`
(a bounded linear map commutes with the Bochner integral; integrability as in F01). -/
def LerayYResolventComm : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)] (h1 : 1 < r) (h3 : r < 3) (P : ℝ) [Fact (0 < P)] (ν : ℝ),
    0 < ν → ∀ (μ : ℂ), 0 < μ.re + gammaR r → ∀ (Rm : Yq P r →L[ℂ] Yq P r),
      (∀ f, Rm f = ∫ t in Set.Ioi (0 : ℝ),
        Complex.exp (-(μ * t)) • B0421.phaseT (ne_top_of_lt h3) ν t f) →
      ∀ f, lerayY P r h1 (ne_top_of_lt h3) (Rm f) = Rm (lerayY P r h1 (ne_top_of_lt h3) f)

/-- **`PartII-a:F08` from the leaf lemmas.** -/
theorem commonBodyProjected_of (h3 : LerayYResolventComm) : CommonBodyProjected := by
  intro r hr h1 h3' P hP hPle ν hν μ hμ f
  obtain ⟨Rm, -, hRm⟩ := bodyResolvent_exists r h1 h3' P ν hν μ hμ
  set g : Yq P r := lerayY P r h1 (ne_top_of_lt h3') f with hg
  have hsol : HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) (Rm g) g :=
    bodyResolvent_solves r h1 h3' P ν hν μ hμ Rm hRm g
  have hmem : Rm g ∈ D P ν r :=
    commonBodyMaximalDomain r h1 h3' P hPle ν hν μ hμ (Rm g) g hsol
  have hL0 : HasPhaseOp (L0T ν) (Rm g) (g - μ • Rm g) := by
    intro Φ hΦ
    have h := hsol Φ hΦ
    simp only at h
    rw [phasePair_add (hΦ.const_smul μ) (isPhaseTest_L0T hΦ ν),
      phasePair_const_smul hΦ] at h
    rw [map_sub, map_smul, smul_eq_mul]
    linear_combination h
  refine ⟨⟨Rm g, hmem⟩, ?_, ?_⟩
  · show Rm g ∈ Ysigma P r
    rw [hg, ← h3 r h1 h3' P ν hν μ hμ Rm hRm f]
    exact mem_Ysigma.2 (lerayY_isPhaseSolenoidal h1 (ne_top_of_lt h3') (Rm f))
  · have hw : L0D (⟨Rm g, hmem⟩ : D P ν r) = g - μ • Rm g := L0D_eq hL0
    simp only [bodyOp, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_subtype,
      L0L_apply]
    rw [hw]
    abel

end UnforcedLeray.Short.PartIIa
