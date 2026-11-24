import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_Fields
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletContDiff

/-!
# Part II-b, task `PartII-b:G4/4/1/1/1` (`InletJointSmooth`)

Source of record: `the November 2 reference manuscript`, lines 2355-2383 and
2347-2369. The inlet `p.inlet i τ = Nv p.R (p.inletProfile i) τ` is the ring lift of the
smooth cutoff profile. `NicePT.contDiff_Nv` is already a joint statement in `(τ, y)`, so the
joint smoothness is the slice argument of `inletContDiff` without the composition with `y ↦ (τ, y)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.Axi

/-- **Joint smoothness of the inlet** `(τ, y) ↦ E_i(τ, y)`. -/
theorem inletJointSmooth : UnforcedLeray.Short.IIb.InletJointSmooth := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨C, κ, N, -, -, hper⟩ := frozenStreamBounds lam q hq 0
  refine ⟨1, one_pos, ?_⟩
  intro p d hreg hν hSig' hmode i
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
  exact hN

end UnforcedLeray.Short.IIb
