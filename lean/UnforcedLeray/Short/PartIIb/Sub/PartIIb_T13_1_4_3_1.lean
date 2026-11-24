import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_3
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Convolution

/-!
# Part II-b, task `PartII-b:T13/1/4/3/1` (`chmMollNice`): decomposition

Source: `the November 2 reference manuscript` (SP) lines 1933-1935.

Proved here: the convolution calculus (`chm_cdvConv`: `∂_j (ρ ⋆ u) = (∂_j ρ) ⋆ u` for smooth compactly
supported `ρ` and locally integrable `u`), the `q`-periodicity of `ρ ⋆ u` and the properties of the
mollifier `chmRho n`.  Remaining source facts (Props): local integrability of a `q`-periodic
`L^r(cylMeas c)` function (`ChmLocInt`) and the Young inequality in `L^r(cylMeas c)`
(`ChmYoungCyl`).  `chmMollNice_of` assembles `ChmMollNice`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology Convolution

theorem chmConv_eq_convolution (ρ : Coord → ℝ) (u : Coord → ℂ) :
    chmConv ρ u = convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext x
  simp [chmConv, convolution, Complex.real_smul]

theorem chmRho_contDiff (n : ℕ) : ContDiff ℝ ∞ (chmRho n) :=
  ContDiffBump.contDiff_normed _ (n := ⊤)

theorem chmRho_compact (n : ℕ) : HasCompactSupport (chmRho n) :=
  ContDiffBump.hasCompactSupport_normed _

/-- Derivative of a convolution with a smooth compactly supported real kernel. -/
theorem chm_cdvConv_aux {ρ : Coord → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ)
    {u : Coord → ℂ} (hu : LocallyIntegrable u volume) (j : Fin 3) (x : Coord) :
    cdv j (chmConv ρ u) x = chmConv (cpd j ρ) u x := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by exact_mod_cast le_top)
  have hfd : ContDiff ℝ 0 (fderiv ℝ ρ) := by
    have := hρ.fderiv_right (m := 0) (by simp)
    exact this
  have hfdc : Continuous (fderiv ℝ ρ) := hfd.continuous
  have hfdcs : HasCompactSupport (fderiv ℝ ρ) := hc.fderiv ℝ
  set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ with hL
  have h1 : HasFDerivAt (convolution u ρ L.flip volume)
      ((u ⋆[L.flip.precompR Coord, volume] fderiv ℝ ρ) x) x :=
    hc.hasFDerivAt_convolution_right L.flip hu hρ1 x
  have h2 : chmConv ρ u = convolution u ρ L.flip volume := by
    rw [chmConv_eq_convolution, convolution_flip]
  rw [cdv, h2, h1.fderiv, convolution_precompR_apply L.flip hu hfdcs hfdc x (cdir j)]
  rw [convolution_flip]
  simp [chmConv, cpd, convolution, L, Complex.real_smul]


theorem cpd_contDiff {ρ : Coord → ℝ} (hρ : ContDiff ℝ ∞ ρ) (j : Fin 3) : ContDiff ℝ ∞ (cpd j ρ) := by
  have h : ContDiff ℝ ∞ (fderiv ℝ ρ) := hρ.fderiv_right (m := ∞) (by simp)
  exact h.clm_apply contDiff_const

theorem cpd_compact {ρ : Coord → ℝ} (hc : HasCompactSupport ρ) (j : Fin 3) :
    HasCompactSupport (cpd j ρ) :=
  (hc.fderiv ℝ).comp_left (g := fun L : Coord →L[ℝ] ℝ => L (cdir j)) (by simp)

theorem cpd_integrable {ρ : Coord → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ)
    (j : Fin 3) : Integrable (cpd j ρ) volume :=
  (cpd_contDiff hρ j).continuous.integrable_of_hasCompactSupport (cpd_compact hc j)

theorem chm_periodic {c : ℝ} {u : Coord → ℂ} (hu : QPeriodicS c u) (K : Coord → ℝ) (x : Coord) :
    chmConv K u (qShift c x) = chmConv K u x := by
  unfold chmConv
  have h1 : ∀ᵐ y : Coord ∂volume, u (qShift c (x - y)) = u (x - y) :=
    (Measure.measurePreserving_sub_left (volume : Measure Coord) x).quasiMeasurePreserving.ae hu
  refine integral_congr_ae (h1.mono fun y hy => ?_)
  have : qShift c x - y = qShift c (x - y) := by
    simp [qShift, Prod.ext_iff]; ring
  simp only [this, hy]

/-- Translation invariance of the cylinder integral of an a.e. `q`-periodic function:
`cylMeas c = ds ⊗ (dq/c on [-c/2,c/2) ⊗ dη)`, translations in `s, η` preserve Lebesgue measure and a
`q`-translation by `t` moves the strip `[-c/2,c/2)` to `[-c/2-t, c/2-t)`, which carries the same
integral of a function with `G ∘ qShift c = G` a.e. (compare the two strips through their common
part and the shift by exactly `c`). -/
def ChmCylTransInv : Prop :=
  ∀ c : ℝ, 0 < c → ∀ G : Coord → ℝ≥0∞, Measurable G → (∀ᵐ x : Coord, G (qShift c x) = G x) →
    ∀ y : Coord, ∫⁻ x, G (x - y) ∂(cylMeas c) = ∫⁻ x, G x ∂(cylMeas c)

/-- Local integrability of a `q`-periodic measurable function in `L^r(cylMeas c)` (SP 1933-1935:
finitely many cells cover a compact set and `L^r ⊆ L^1` on finite measure). -/
def ChmLocInt : Prop :=
  ∀ c : ℝ, 0 < c → ∀ r : ℝ, 1 < r → ∀ u : Coord → ℂ, QPeriodicS c u →
    AEStronglyMeasurable u volume → cylNorm c r u < ⊤ → LocallyIntegrable u volume

/-- Young inequality for a `q`-periodic function in `L^r(cylMeas c)` and an integrable kernel on
`Coord` (Minkowski; `cylMeas c` is invariant under translation of a periodic function). -/
def ChmYoungCyl : Prop :=
  ∀ c : ℝ, 0 < c → ∀ r : ℝ, 1 < r → ∀ (K : Coord → ℝ) (u : Coord → ℂ), Integrable K volume →
    QPeriodicS c u → AEStronglyMeasurable u volume → cylNorm c r u < ⊤ →
    cylNorm c r (chmConv K u) ≤ eLpNorm K 1 volume * cylNorm c r u

theorem chmMollNice_of (hL : ChmLocInt) (hY : ChmYoungCyl) : ChmMollNice := by
  intro r hr c hc u hup hum hun n
  have hloc := hL c hc r hr u hup hum hun
  have hρ := chmRho_contDiff n
  have hcs := chmRho_compact n
  have hfin : ∀ K : Coord → ℝ, Integrable K volume → cylNorm c r (chmConv K u) < ⊤ := fun K hK =>
    lt_of_le_of_lt (hY c hc r hr K u hK hup hum hun)
      (ENNReal.mul_lt_top (memLp_one_iff_integrable.2 hK).eLpNorm_lt_top hun)
  have hd1 : ∀ j : Fin 3, cdv j (chmConv (chmRho n) u) = chmConv (cpd j (chmRho n)) u :=
    fun j => funext fun x => chm_cdvConv_aux hρ hcs hloc j x
  refine ⟨?_, chm_periodic hup _, ?_, ?_, ?_⟩
  · rw [chmConv_eq_convolution]
    exact hcs.contDiff_convolution_left _ (n := ⊤) hρ hloc
  · exact hfin _ (hρ.continuous.integrable_of_hasCompactSupport hcs)
  · intro j
    rw [hd1 j]
    exact hfin _ (cpd_integrable hρ hcs j)
  · intro j k
    rw [hd1 k, funext fun x => chm_cdvConv_aux (cpd_contDiff hρ k) (cpd_compact hcs k) hloc j x]
    exact hfin _ (cpd_integrable (cpd_contDiff hρ k) (cpd_compact hcs k) j)

end UnforcedLeray.Short.IIb
