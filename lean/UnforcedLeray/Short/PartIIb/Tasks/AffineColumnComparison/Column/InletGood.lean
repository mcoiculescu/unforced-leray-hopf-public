import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletContDiff

/-!
# Part II-b, task `PartII-b:G4/3/1/1` (`InletGoodAll`)

Source of record: `the November 2 reference manuscript`, lines 2347-2348, 2360-2374.
With `ν₀ = 1`: the affine inlet `E_εα = Σ α_i Efun i` is jointly `C^∞` (ring lift `contDiff_Nv`),
`P`-periodic in `τ` (`Nv_add_period_of_not_mem_axis`, `P = 2c/R`), and vanishes on `ϱ < R/(H/2+1)`
(there the age `R²/ϱ²` exceeds `H/2`, where the age cutoff vanishes).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.Axi
open UnforcedLeray.B0412 (realC)

theorem inletGoodAll : UnforcedLeray.Short.IIb.InletGoodAll := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨C, κ, N, -, -, hper⟩ := frozenStreamBounds lam q hq 0
  refine ⟨1, one_pos, ?_⟩
  intro p d hreg hν hSig' hmode α
  have hνpos : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hP : ContDiff ℝ ∞ (periodicStream q p.c) := (hper p.c hc1).1
  have hfro : ∀ k : Fin 2, ContDiff ℝ ∞ (p.frozenStream k) :=
    fun k => inletCD_frozenStream hP hmode k
  have hH : 0 < p.H := div_pos p.ageCut_pos p.ν_pos
  have key : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2) ∧
      (∀ x : ℝ × (ℝ × ℝ), p.H / 2 < x.1 → p.inletProfile i x = 0) := by
    intro i
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
    exact ⟨NicePT.contDiff_Nv p.R_pos hB (s1 := p.H / 2) hvan, hvan⟩
  have hJ : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2) :=
    fun i => (key i).1
  -- Vanishing of each inlet on the thin tube `ϱ < R/(H/2+1)`.
  have hH2 : 0 < p.H / 2 + 1 := by linarith
  have hNv0 : ∀ (i : Fin 2) (τ : ℝ) (y : Space), Axi.ϱ y < p.R / (p.H / 2 + 1) →
      p.inlet i τ y = 0 := by
    intro i τ y hy
    by_cases h0 : Axi.ϱ y = 0
    · simp [Params.inlet, Axi.Nv, Axi.age, h0]
    · have hϱpos : 0 < Axi.ϱ y := lt_of_le_of_ne (Axi.ϱ_nonneg y) (Ne.symm h0)
      have h1 : Axi.ϱ y * (p.H / 2 + 1) < p.R := (lt_div_iff₀ hH2).1 hy
      have h2 : (Axi.ϱ y * (p.H / 2 + 1)) ^ 2 < p.R ^ 2 :=
        pow_lt_pow_left₀ h1 (by positivity) two_ne_zero
      have hbig : p.H / 2 < (Axi.chart p.R τ y).1 := by
        show p.H / 2 < Axi.age p.R y
        unfold Axi.age
        rw [lt_div_iff₀ (pow_pos hϱpos 2)]
        nlinarith [mul_nonneg (sq_nonneg (Axi.ϱ y))
          (by positivity : (0 : ℝ) ≤ (p.H / 2) ^ 2 + p.H / 2 + 1)]
      have hg : p.inletProfile i (Axi.chart p.R τ y) = 0 := (key i).2 _ hbig
      simp [Params.inlet, Axi.Nv, hg]
  -- Periodicity of each inlet in `τ`.
  have hinletP : ∀ (i : Fin 2) (τ : ℝ) (y : Space),
      p.inlet i (τ + p.period) y = p.inlet i τ y := by
    intro i τ y
    by_cases h0 : Axi.ϱ y = 0
    · simp [Params.inlet, Axi.Nv, Axi.age, h0]
    · have hy : y ∉ Axi.axis := fun h => h0 ((Axi.mem_axis_iff y).1 h)
      unfold Params.inlet
      exact UnforcedLeray.Cons.C03.Nv_add_period_of_not_mem_axis p.R_pos.ne' p.period_eq
        (fun s _ ξ η => p.inletProfile_periodic i s ξ η) τ hy
  refine ⟨?_, ?_, ⟨p.R / (p.H / 2 + 1), div_pos p.R_pos hH2, ?_⟩⟩
  · have hc : inletC p α = fun x : ℝ × Space =>
        ∑ i : Fin 2, ((α i : ℝ) : ℂ) • realC (p.inlet i x.1 x.2) := rfl
    rw [hc]
    exact ContDiff.sum fun i _ => ((NicePT.contDiff_realC.comp (hJ i))).const_smul ((α i : ℝ) : ℂ)
  · intro τ y
    simp [inletC, Params.Efun, hinletP]
  · intro τ y hy
    have hz : ∀ i : Fin 2, realC (p.inlet i τ y) = 0 := by
      intro i
      rw [hNv0 i τ y hy]
      simp [realC]
    simp [inletC, Params.Efun, hz]

end UnforcedLeray.Short.IIb
