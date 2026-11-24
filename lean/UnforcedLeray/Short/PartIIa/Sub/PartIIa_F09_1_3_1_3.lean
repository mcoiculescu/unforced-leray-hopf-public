import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_1_3_1
import UnforcedLeray.Short.PartIIa.Tasks.F12bPhaseInnerEqPairing

/-!
# Part II-a, audit decomposition of `PartII-a:F09/1/3/1/3` (`phaseDualityAdjT`)

Source `the November 2 reference manuscript` lines 1403-1413, 1426-1428.
`adjT P ν s` is the Hilbert adjoint of `𝒯(s) = phaseT` on `Y_2`. The bilinear pairing against a
phase test equals the Hilbert inner product against its conjugate (`phaseInnerEqPairing`); the
adjoint moves `𝒯(s)` across; `𝒯(s)` commutes with conjugation (`PhaseTConj`, the one analytic
leaf: `S_ν(s)` is real); and a Hilbert pairing against a pointwise conjugate is a bilinear pairing
(`hilbert_eq_pairing`, proved here).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **`𝒯(s)` commutes with conjugation on tests** (`S_ν(s)` is real, `B0421.coeFn_freeC`;
`B0421.coeFn_phaseT`; slices of tests via `MemLp.coeFn_toLp`): for a.e. phase `τ`, the `y`-a.e.
function `(𝒯(s) Φ̄)(τ)` (in `Y_2`) is the pointwise conjugate of `(𝒯(s) Φ)(τ)` (in `Y_{2'}`). -/
def PhaseTConj : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν s : ℝ) (Φ : ℝ × Space → CVec3), IsPhaseTest P Φ →
    ∀ᵐ τ ∂(AddCircle.haarAddCircle : Measure (AddCircle P)),
      ⇑((B0421.phaseT (P := P) (q := 2) ENNReal.ofNat_ne_top ν s (testElem P 2 (conjF Φ))) τ)
        =ᵐ[volume]
      fun y => (WithLp.toLp 2 fun k => star
        (((B0421.phaseT (P := P) (q := conjExp 2) (conjExp_ne_top (by norm_num)) ν s
          (testElem P (conjExp 2) Φ)) τ) y k) : CVec3)

/-- A Hilbert pairing in `Y_2` against a pointwise conjugate is the bilinear phase pairing. -/
theorem hilbert_eq_pairing {P : ℝ} [Fact (0 < P)] (u x : Yq P 2) (ψ : Yq P (conjExp 2))
    (h : ∀ᵐ τ ∂(AddCircle.haarAddCircle : Measure (AddCircle P)),
      ⇑(u τ) =ᵐ[volume] fun y => (WithLp.toLp 2 fun k => star ((ψ τ) y k) : CVec3)) :
    inner ℂ u x = phasePairing P 2 ψ x := by
  rw [L2.inner_def, phasePairing_apply]
  refine integral_congr_ae ?_
  filter_upwards [h] with τ hτ
  rw [L2.inner_def, innerPair_apply]
  refine integral_congr_ae ?_
  filter_upwards [hτ] with y hy
  rw [hy, inner_eq_dotL_conj]
  simp only [star_star]

theorem conjF_conjF' (Φ : ℝ × Space → CVec3) : conjF (conjF Φ) = Φ := by
  funext p
  ext k
  simp [conjF]

/-- **`PhaseDualityAdjT` from the conjugation-commutation of `𝒯(s)`.** -/
theorem phaseDualityAdjT_of (h : PhaseTConj) : PhaseDualityAdjT := by
  intro P _ ν hν Φ hΦ s hs x
  have e1 : phasePair P 2 Φ (adjT P ν s x) =
      inner ℂ (testElem P 2 (conjF Φ)) (adjT P ν s x) := by
    have := ((phaseInnerEqPairing P (conjF Φ) (conjF_isPhaseTest hΦ)).2 (adjT P ν s x)).symm
    rwa [conjF_conjF'] at this
  rw [e1, adjT, ContinuousLinearMap.adjoint_inner_right]
  exact hilbert_eq_pairing _ x _ (h P ν s Φ hΦ)

end UnforcedLeray.Short.PartIIa
