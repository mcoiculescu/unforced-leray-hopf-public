import UnforcedLeray.Short.PartIIa.Sub.F14_1
import UnforcedLeray.Short.PartIIa.Tasks.F12bPhaseInnerEqPairing

/-!
# Part II-a, `PartII-a:F14/1/4`: `Re ⟨div G, w⟩ ≤ ‖G‖ ‖∇w‖`

Source `the November 2 reference manuscript` line 1497.  For a smooth symmetric
phase tensor `G` and `w ∈ Y_2` with gradient `g`, testing `∂_j w = g_j` against the conjugate
`Φ_j = conj(G_j)` and summing over `j` gives, by the symmetry `G_ij = G_ji`,
`⟨div G, w⟩ = - ∑_j ⟨G_j, g_j⟩_{Y_2}`; then Cauchy-Schwarz.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- Coordinatewise conjugation on `ℂ³` as a real continuous linear map. -/
def conjM : CVec3 →L[ℝ] CVec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 fun k => star (v k)
      map_add' := fun v w => by ext k; simp
      map_smul' := fun c v => by ext k; simp }

theorem conjM_apply (v : CVec3) : conjM v = WithLp.toLp 2 fun k => star (v k) := rfl

theorem conjF_eq (Φ : ℝ × Space → CVec3) : conjF Φ = fun p => conjM (Φ p) := rfl

theorem dy_conjF {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (j : Fin 3) :
    dy j (conjF Φ) = conjF (dy j Φ) := by
  funext p
  have h := conjM.hasFDerivAt.comp p
    ((hΦ.smooth.differentiable (by simp)) p).hasFDerivAt
  have h2 : fderiv ℝ (fun p => conjM (Φ p)) p = conjM ∘SL fderiv ℝ Φ p := h.fderiv
  simp only [dy, conjF_eq]
  rw [h2]
  rfl

theorem dy_apply_coord {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (j : Fin 3)
    (p : ℝ × Space) (k : Fin 3) :
    dy j Φ p k = fderiv ℝ (fun q => Φ q k) p (0, coordinateVector j) := by
  have h : HasFDerivAt (fun q => Φ q k)
      (((EuclideanSpace.proj k : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).comp (fderiv ℝ Φ p)) p :=
    ((EuclideanSpace.proj k : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.comp p
      ((hΦ.smooth.differentiable (by simp)) p).hasFDerivAt
  rw [h.fderiv]
  rfl

theorem tensorDiv_eq {P : ℝ} {G : Fin 3 → ℝ × Space → CVec3} (hG : ∀ i, IsPhaseTest P (G i))
    (hs : IsSymRows G) : tensorDiv G = ∑ j, dy j (G j) := by
  funext p
  ext i
  have h1 : (∑ c, dy c (G c) p).ofLp i = ∑ c, (dy c (G c) p).ofLp i := by
    simp [WithLp.ofLp_sum]
  simp only [tensorDiv, WithLp.ofLp_toLp, Finset.sum_apply]
  rw [h1]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e1 := dy_apply_coord (hG i) c p c
  have e2 := dy_apply_coord (hG c) c p i
  have e3 : (fun q => G c q i) = (fun q => G i q c) := funext fun q => hs c i q
  show (dy c (G i) p) c = (dy c (G c) p) i
  rw [e1, e2, e3]

theorem tensorDivPairingLe : TensorDivPairingLe := by
  intro P _ G hG hs w g hgw
  have hbr := phaseInnerEqPairing
  have hdiv : IsPhaseTest P (tensorDiv G) := by
    rw [tensorDiv_eq hG hs]
    exact IsPhaseTest.sum _ fun j _ => (hG j).dy j
  have hconj : ∀ j, IsPhaseTest P (conjF (G j)) := fun j => (hbr P (G j) (hG j)).1
  have hdyj : ∀ j, IsPhaseTest P (conjF (dy j (G j))) := fun j => (hbr P _ ((hG j).dy j)).1
  have h2 : ∀ j, phasePair P 2 (conjF (dy j (G j))) w =
      -inner ℂ (testElem P 2 (G j)) (g j) := by
    intro j
    have h := hgw j (conjF (G j)) (hconj j)
    simp only at h
    rw [dy_conjF (hG j) j, phasePair_neg (hdyj j), ← (hbr P _ (hG j)).2 (g j)] at h
    linear_combination -h
  have hid : inner ℂ (testElem P 2 (tensorDiv G)) w =
      -∑ j, inner ℂ (testElem P 2 (G j)) (g j) := by
    rw [(hbr P _ hdiv).2 w]
    have h1 : conjF (tensorDiv G) = ∑ j, conjF (dy j (G j)) := by
      rw [tensorDiv_eq hG hs]
      funext p
      ext k
      simp [conjF, WithLp.ofLp_sum]
    rw [h1, phasePair_sum _ (fun j _ => hdyj j)]
    simp_rw [h2]
    rw [Finset.sum_neg_distrib]
  rw [hid]
  have hnorm : ‖smoothTensor P G‖ = Real.sqrt (∑ j, ‖testElem P 2 (G j)‖ ^ 2) := by
    rw [smoothTensor, PiLp.norm_eq_of_L2]
  rw [hnorm]
  calc (-∑ j, inner ℂ (testElem P 2 (G j)) (g j)).re
      ≤ ‖-∑ j, inner ℂ (testElem P 2 (G j)) (g j)‖ := Complex.re_le_norm _
    _ = ‖∑ j, inner ℂ (testElem P 2 (G j)) (g j)‖ := norm_neg _
    _ ≤ ∑ j, ‖inner ℂ (testElem P 2 (G j)) (g j)‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖testElem P 2 (G j)‖ * ‖g j‖ :=
        Finset.sum_le_sum fun j _ => norm_inner_le_norm _ _
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

end UnforcedLeray.Short.PartIIa
