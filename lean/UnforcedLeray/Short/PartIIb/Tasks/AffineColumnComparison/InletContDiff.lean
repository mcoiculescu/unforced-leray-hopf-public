import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth.SmoothPt.NicePhaseTest

/-!
# Part II-b, task `PartII-b:G4/5/1` (`InletContDiff`)

Source of record: `the November 2 reference manuscript`, lines 2347-2369.
The frozen inlet `p.inlet i τ` is the ring lift `Nv p.R (p.inletProfile i) τ` of the profile
`ringStreamProfile p.R (p.cutStream i)`, where `cutStream i = χ(s) · frozenStream i` and the
frozen streams are built from the periodized eigenstream `periodicStream p.mode p.c`.
The periodized eigenstream is `C^∞` (`frozenStreamBounds`, `c ≥ 1`), the age cutoff is `C^∞`
and vanishes for `s ≥ H/2`, so the ring-lift smoothness lemma `contDiff_Nv` applies.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.Axi

/-- Partial derivatives of a `C^∞` function on the chart space are `C^∞`. -/
theorem inletCD_fderiv_apply {φ : ℝ × (ℝ × ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (v : ℝ × (ℝ × ℝ)) : ContDiff ℝ ∞ (fun m => fderiv ℝ φ m v) :=
  (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The normalized components `ringStreamProfile R φ` of a `C^∞` profile are `C^∞`. -/
theorem inletCD_ringStreamProfile {R : ℝ} {φ : ℝ × (ℝ × ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun m => ringStreamProfile R φ m) := by
  have hS : ContDiff ℝ ∞ (fun m => fderiv ℝ φ m (1, (0, 0))) := inletCD_fderiv_apply hφ _
  have hQ : ContDiff ℝ ∞ (fun m => fderiv ℝ φ m (0, (1, 0))) := inletCD_fderiv_apply hφ _
  have hE : ContDiff ℝ ∞ (fun m => fderiv ℝ φ m (0, (0, 1))) := inletCD_fderiv_apply hφ _
  simp only [ringStreamProfile, Axi.dS, Axi.dQ, Axi.dEta]
  fun_prop

/-- The frozen streams are `C^∞` once the periodized eigenstream is. -/
theorem inletCD_frozenStream {p : Params} {q : Planar.Profile}
    (hP : ContDiff ℝ ∞ (periodicStream q p.c)) (hmode : p.mode = q) (i : Fin 2) :
    ContDiff ℝ ∞ (p.frozenStream i) := by
  have hP' : ContDiff ℝ ∞ (periodicStream p.mode p.c) := by rw [hmode]; exact hP
  have hre : ContDiff ℝ ∞ (fun x => (periodicStream p.mode p.c x).re) :=
    Complex.reCLM.contDiff.comp hP'
  have him : ContDiff ℝ ∞ (fun x => (periodicStream p.mode p.c x).im) :=
    Complex.imCLM.contDiff.comp hP'
  fin_cases i
  · exact contDiff_const.mul hre
  · exact contDiff_const.mul him

/-- **Smoothness of each frozen inlet slice** (through the axis). -/
theorem inletContDiff : InletContDiff := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨C, κ, N, -, -, hper⟩ := frozenStreamBounds lam q hq 0
  refine ⟨1, one_pos, ?_⟩
  intro p d hreg hν hSig' hmode i τ
  have hνpos : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hP : ContDiff ℝ ∞ (periodicStream q p.c) := (hper p.c hc1).1
  have hfro : ∀ k : Fin 2, ContDiff ℝ ∞ (p.frozenStream k) :=
    fun k => inletCD_frozenStream hP hmode k
  have hH : 0 < p.H := div_pos p.ageCut_pos p.ν_pos
  have hcut : ContDiff ℝ ∞ (p.cutStream i) := by
    unfold Params.cutStream
    exact ((contDiff_ageCutoff p.H).comp contDiff_fst).mul ((hfro i).comp contDiff_snd)
  have hB : ContDiff ℝ ∞ (p.inletProfile i) := by
    unfold Params.inletProfile
    exact inletCD_ringStreamProfile hcut
  have hvan : ∀ x : ℝ × (ℝ × ℝ), p.H / 2 < x.1 → p.inletProfile i x = 0 := by
    intro x hx
    have hcut0 : p.cutStream i x = 0 := by
      unfold Params.cutStream
      simp [ageCutoff_eq_zero hH hx.le]
    have hev : ∀ᶠ y in 𝓝 x, p.H / 2 < y.1 :=
      (continuous_fst.tendsto x).eventually (lt_mem_nhds hx)
    have hfun : p.cutStream i =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hev] with y hy
      unfold Params.cutStream
      simp [ageCutoff_eq_zero hH hy.le]
    have hfd : fderiv ℝ (p.cutStream i) x = 0 := by
      rw [hfun.fderiv_eq]
      simp
    have hdS : Axi.dS (p.cutStream i) x = 0 := by
      unfold Axi.dS
      rw [hfd]
      simp
    have hdQ : Axi.dQ (p.cutStream i) x = 0 := by
      unfold Axi.dQ
      rw [hfd]
      simp
    have hdE : Axi.dEta (p.cutStream i) x = 0 := by
      unfold Axi.dEta
      rw [hfd]
      simp
    simp [Params.inletProfile, Axi.ringStreamProfile, hdS, hdQ, hdE, hcut0]
  have hN := NicePT.contDiff_Nv p.R_pos hB (s1 := p.H / 2) hvan
  have hcomp := hN.comp (contDiff_const.prodMk contDiff_id :
    ContDiff ℝ ∞ (fun y => ((τ, y) : ℝ × _)))
  exact hcomp

end UnforcedLeray.Short.IIb
