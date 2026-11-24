import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1
import UnforcedLeray.Lib.Gaussian.Kernel
import UnforcedLeray.Units.B0224.PlaneHeat

/-!
# Decomposition of `T0gSmooth`

Source `the November 2 reference manuscript`
1640-1656: `Ψ(s,q,η) = e^{-t/2} e^{ν s (e^t-1) Δ_{q,η}} Φ(e^t s, ·)(q,η)` is jointly smooth.
Reduction: `Ψ` vanishes for `s < s0'` (band), equals a dilation of `Φ` where the heat time
`ν s (e^t-1) ≤ 0`, and on `s > 0` with `ν (e^t-1) > 0` is a Gaussian average with smooth
parameter `r = √(ν s (e^t-1))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile QPeriodic)
open UnforcedLeray.B0226 (ProfileTest IsProfileTest)

/-- A profile test is smooth with all iterated derivatives bounded (derivatives are periodic in
`q` and supported in the compact band; source 1640-1650). -/
def T0gBdd : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (Φ : Profile → ℝ), IsProfileTest c Φ → ∀ k : ℕ, ∃ C : ℝ, ∀ p : Profile,
    ‖iteratedFDeriv ℝ k Φ p‖ ≤ C

/-- Joint smoothness of the Gaussian average in the scale `r`, the parameter `s` and the point `z`
for `F` smooth with all derivatives bounded (differentiation under the integral; the Gaussian has
all moments). -/
def T0gGaussParam : Prop :=
  ∀ (F : Profile → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
    (∀ k : ℕ, ∃ C : ℝ, ∀ p : Profile, ‖iteratedFDeriv ℝ k F p‖ ≤ C) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × ℝ × (ℝ × ℝ) =>
      ∫ w : UnforcedLeray.Gaussian.Euc 2,
        UnforcedLeray.Gaussian.gaussKernel 2 1 w *
          F (x.2.1, x.2.2 - UnforcedLeray.B0224.planeι (x.1 • w)))

/-- Scaling form of the planar heat (substitute `y = √θ w` in `planeHeat_of_pos`). -/
def T0gHeatSub : Prop :=
  ∀ (θ : ℝ), 0 < θ → ∀ (u : ℝ × ℝ → ℝ) (x : ℝ × ℝ),
    UnforcedLeray.B0224.planeHeat θ u x =
      ∫ w : UnforcedLeray.Gaussian.Euc 2, UnforcedLeray.Gaussian.gaussKernel 2 1 w *
        u (x - UnforcedLeray.B0224.planeι (Real.sqrt θ • w))

/-- Gaussian region: `Ψ` is smooth on `{s > 0}` when `ν (e^t - 1) > 0`. -/
def T0gHeatPos : Prop :=
  ∀ (c ν t : ℝ), 0 < c → ∀ (Φ : Profile → ℝ), IsProfileTest c Φ → 0 < ν * (Real.exp t - 1) →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (t0gPsi ν t Φ) {p : Profile | 0 < p.1}

theorem t0gSmooth_of (hB : T0gBand) (hA : T0gHeatPos) : T0gSmooth := by
  intro c ν t hc Φ hΦ
  obtain ⟨s0, s1, hs0, hband⟩ := hB c ν t Φ hΦ
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.1 < s0
  · have hev : t0gPsi ν t Φ =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
      have : {q : Profile | q.1 < s0} ∈ 𝓝 p :=
        (isOpen_lt continuous_fst continuous_const).mem_nhds hp
      filter_upwards [this] with q hq
      by_contra hne
      exact absurd (hband q hne).1 (not_le.2 hq)
    exact (contDiffAt_const).congr_of_eventuallyEq hev
  · have hp0 : 0 < p.1 := lt_of_lt_of_le hs0 (not_lt.1 hp)
    have hopen : IsOpen {q : Profile | 0 < q.1} := isOpen_lt continuous_const continuous_fst
    by_cases hν : 0 < ν * (Real.exp t - 1)
    · exact (hA c ν t hc Φ hΦ hν).contDiffAt (hopen.mem_nhds hp0)
    · have hev : t0gPsi ν t Φ =ᶠ[𝓝 p]
          fun q : Profile => Real.exp (-t / 2) * Φ (Real.exp t * q.1, q.2) := by
        filter_upwards [hopen.mem_nhds hp0] with q hq
        have hq' : (0 : ℝ) < q.1 := hq
        have hθ : ν * q.1 * (Real.exp t - 1) ≤ 0 := by
          have : ν * q.1 * (Real.exp t - 1) = q.1 * (ν * (Real.exp t - 1)) := by ring
          rw [this]
          exact mul_nonpos_of_nonneg_of_nonpos hq'.le (not_lt.1 hν)
        simp only [t0gPsi, UnforcedLeray.B0224.planeHeat_of_nonpos hθ]
      refine ContDiffAt.congr_of_eventuallyEq ?_ hev
      have hcomp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : Profile => Φ (Real.exp t * q.1, q.2)) :=
        hΦ.smooth.comp (by fun_prop)
      exact (contDiff_const.mul hcomp).contDiffAt

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
