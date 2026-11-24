import UnforcedLeray.Short.PartIIa.Sub.N02_3
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.Cutoff
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.PrimSmooth

/-!


Source of record: `the November 2 reference manuscript`, lines 1728-1730.
Prop: `ZeroCutTest` (`Sub/N02_3.lean`).

Plan. With `g_i = f(·, i)` (a complex band test), `Φ = zPrimC g_i` is smooth (`zeroPrimSmooth`),
`q`-periodic (the integrand is), and its `s`-support is that of `g_i` (an integral over a
vanishing integrand is zero). The cut-off `zCut L Φ = χ(η/L) Φ` is smooth, periodic, has the same
`s`-support, and its `η`-support lies in `|η| ≤ 2L` because `χ(t) = 0` for `|t| ≥ 2`. The negated
primitive is handled by the same lemma.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace ZeroCutTestAux

/-- A coordinate component of a meridional test is a complex band test. -/
lemma comp_isCTest {c : ℝ} {f : Profile → MeridC} (hf : IsMeridTest c f) (i : Fin 2) :
    IsCTest c (fun p => f p i) := by
  obtain ⟨s0, s1, L, hs0, hb⟩ := hf.band
  refine ⟨?_, ?_, s0, s1, L, hs0, ?_⟩
  · exact ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hf.smooth
  · intro p
    exact congrArg (fun v : MeridC => v i) (hf.periodic p)
  · intro p hp
    exact hb p (fun h => hp (by simp [h]))

/-- The primitive of a `q`-periodic function is `q`-periodic. -/
lemma zPrim_periodic {c : ℝ} {g : Profile → ℂ} (hP : QPeriodic c g) :
    QPeriodic c (zPrimC g) := by
  intro p
  show (∫ t in (0 : ℝ)..p.2.2, g (p.1, p.2.1 + c, t))
    = ∫ t in (0 : ℝ)..p.2.2, g (p.1, p.2.1, t)
  exact intervalIntegral.integral_congr fun t _ => hP (p.1, p.2.1, t)

/-- The negated primitive of a `q`-periodic function is `q`-periodic. -/
lemma zPrim_neg_periodic {c : ℝ} {g : Profile → ℂ} (hP : QPeriodic c (zPrimC g)) :
    QPeriodic c (fun p => -zPrimC g p) := by
  intro p
  show -zPrimC g (p.1, p.2.1 + c, p.2.2) = -zPrimC g p
  rw [hP p]

/-- The primitive vanishes unless the `s`-variable lies in the support interval of `g`. -/
lemma zPrim_support {g : Profile → ℂ} {s0 s1 : ℝ}
    (hsup : ∀ p : Profile, g p ≠ 0 → p.1 ∈ Icc s0 s1) (p : Profile) (hp : zPrimC g p ≠ 0) :
    p.1 ∈ Icc s0 s1 := by
  by_contra hn
  apply hp
  show (∫ t in (0 : ℝ)..p.2.2, g (p.1, p.2.1, t)) = 0
  have hz : ∀ t : ℝ, g (p.1, p.2.1, t) = 0 := fun t => by
    by_contra h
    exact hn (hsup (p.1, p.2.1, t) h)
  simp [hz]

/-- The cut-off `χ_L Φ` of a smooth, `q`-periodic `Φ` whose `s`-support lies in `[s0, s1]` is a
complex band test (its `η`-support lies in `|η| ≤ 2L`). -/
lemma cut_isCTest {c L : ℝ} {Φ : Profile → ℂ} (hL : 0 < L) (hS : ContDiff ℝ ∞ Φ)
    (hP : QPeriodic c Φ) {s0 s1 : ℝ} (hs0 : 0 < s0)
    (hsup : ∀ p : Profile, Φ p ≠ 0 → p.1 ∈ Icc s0 s1) :
    IsCTest c (zCut L Φ) := by
  have hC := zeroCutoff
  have hzero : ∀ t : ℝ, 2 ≤ |t| → zChi t = 0 := hC.2.2.2.1
  have hchi : ContDiff ℝ ∞ (fun p : Profile => ((zChi (p.2.2 / L) : ℝ) : ℂ)) := by
    have h1 : ContDiff ℝ ∞ (fun p : Profile => p.2.2 / L) := by fun_prop
    exact Complex.ofRealCLM.contDiff.comp (hC.1.comp h1)
  refine ⟨hchi.mul hS, ?_, s0, s1, 2 * L, hs0, ?_⟩
  · intro p
    show ((zChi ((p.1, p.2.1 + c, p.2.2).2.2 / L) : ℝ) : ℂ) * Φ (p.1, p.2.1 + c, p.2.2)
      = ((zChi (p.2.2 / L) : ℝ) : ℂ) * Φ p
    rw [hP p]
  · intro p hp
    have hΦ : Φ p ≠ 0 := fun h => hp (by simp [zCut, h])
    have hχ : zChi (p.2.2 / L) ≠ 0 := fun h => hp (by simp [zCut, h])
    refine ⟨hsup p hΦ, ?_⟩
    have h2 : |p.2.2 / L| < 2 := by
      by_contra hc
      exact hχ (hzero _ (not_lt.mp hc))
    have hη : |p.2.2| = |p.2.2 / L| * L := by
      rw [abs_div, abs_of_pos hL, div_mul_cancel₀ _ hL.ne']
    rw [hη]
    exact mul_le_mul_of_nonneg_right h2.le hL.le

end ZeroCutTestAux

/-- **L2 (cut-off primitives are complex band potentials), proved.** For a smooth periodic band test
`f` and `L > 0`, both `χ_L Φ_i` and `-χ_L Φ_i` (with `Φ_i = ∫_0^η f_i`) are `IsCTest`s. -/
theorem zeroCutTest : ZeroCutTest := by
  intro c L f hc hL hf i
  have hg := ZeroCutTestAux.comp_isCTest hf i
  obtain ⟨s0, s1, _, hs0, hb⟩ := hg.band
  have hsup : ∀ p : Profile, (fun p => f p i) p ≠ 0 → p.1 ∈ Icc s0 s1 := fun p h => (hb p h).1
  have hΦs : ContDiff ℝ ∞ (zPrimC (fun p => f p i)) :=
    (zeroPrimSmooth _ hg.smooth hg.band).1
  have hΦp : QPeriodic c (zPrimC (fun p => f p i)) := ZeroCutTestAux.zPrim_periodic hg.periodic
  refine ⟨ZeroCutTestAux.cut_isCTest hL hΦs hΦp hs0
    (fun p h => ZeroCutTestAux.zPrim_support hsup p h), ?_⟩
  exact ZeroCutTestAux.cut_isCTest hL hΦs.neg
    (ZeroCutTestAux.zPrim_neg_periodic hΦp) hs0
    (fun p h => ZeroCutTestAux.zPrim_support hsup p (neg_ne_zero.mp h))

end UnforcedLeray.Short.PartIIa
