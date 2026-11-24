import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2
import UnforcedLeray.Short.PartIIb.Sub.B1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1.ProjSmooth

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1` (decomposition): `L0TSolExtension`

Source `the November 2 reference manuscript`
lines 119-120 (Cartesian Leray projection `𝔓 = ℙ`), 1356-1366 (`bg:common-body-graph`: the
projected inverse is obtained by applying Cartesian Leray projection to `f`) and 1446-1455
(uniqueness by testing against radial cutoffs: the drift cutoff is bounded, the diffusion cutoffs
cost `N⁻¹, N⁻²`).  With `𝔓Φ` the slice-wise Leray projection of a phase test `Φ`, represented by
the smooth field `projSmooth Φ = Φ + ∇π` (`…_8_2_1/ProjSmooth.lean`: `contDiff_projSmooth`,
`projSmooth_slice_ae`; `…_8_2_1/Smooth.lean`: `isSliceTest_projSmooth`,
`phasePair_projSmooth_eq_of_phaseSolenoidal`):
(A) `⟪L₀ᵗΦ, v⟫ = ⟪L₀ᵗ𝔓Φ, v⟫` for solenoidal `v`;
(B) there are solenoidal tests `Ψₙ` with `⟪L₀ᵗΨₙ, d⟫ → ⟪L₀ᵗ𝔓Φ, d⟫` (graph-sense approximation).
The assembly `l0TSolExtension_of` is proved here.

Both Props were first stated with `IIb.projTest P Φ` in place of `projSmooth Φ`; that field is
only the `L^{q₀'}` representative `(lerayC … (sliceMap …)) x.2`, fixed only a.e. in `y`, so the
pointwise `fderiv`-based `L0T` of it was junk.  `L0TProjCommute` below has literally the same body
as `L0TProjSmoothCommute` (`…_8_2_1/ProjCommuteProps.lean`), so `l0TProjSmoothCommute` proves it
by unfolding.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (IsSolTest)

/-- **(A) Commutation of `L₀ᵗ` with the Leray projection on solenoidal pairings.**  For a phase
test `Φ` and `v ∈ Y_{q₀,σ}`: `⟪L₀ᵗΦ, v⟫ = ⟪L₀ᵗ(projSmooth Φ), v⟫` (source lines 1356-1366,
119-120).  Sketch: `ℙ` is a degree-0 Fourier multiplier, so it commutes exactly with `∂_τ`, `Δ`,
constants and the dilation generator `y·∇`; hence `L₀ᵗ(projSmooth Φ) = projSmooth (L₀ᵗΦ)`, and
`phasePair_projSmooth_eq_of_phaseSolenoidal` applied to the phase test `L₀ᵗΦ` gives (A).  (The
compiled decomposition in `…_8_2_1/ProjCommuteProps.lean` instead writes `L₀ᵗ(Φ + ∇π) - L₀ᵗΦ` as
a gradient and shows it pairs to zero with `v`.) -/
def L0TProjCommute : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν → ∀ v : Yq P UnforcedLeray.B0412.q0E,
    v ∈ Ysigma P UnforcedLeray.B0412.q0E →
    ∀ Φ : ℝ × UnforcedLeray.Space → CVec3, IsPhaseTest P Φ →
      phasePair P UnforcedLeray.B0412.q0E (L0T ν Φ) v =
        phasePair P UnforcedLeray.B0412.q0E (L0T ν (projSmooth Φ)) v

/-- **(B) Graph-sense solenoidal approximation of `𝔓Φ`.**  There are solenoidal tests `Ψₙ`
with `⟪L₀ᵗΨₙ, d⟫ → ⟪L₀ᵗ(projSmooth Φ), d⟫` for every `d ∈ Y_{q₀}` (strengthens
`IIb.SolTestApprox`, which controls only `⟪Ψₙ, d⟫`; source lines 1446-1455: cutoff at radius `N`,
the drift cutoff is bounded and the diffusion cutoffs cost `N⁻¹, N⁻²`).  Sketch: `Ψₙ` are the curl
cutoffs `curl(χ_{n+1} B)` of the Newton curl potential `B = curl(N * Φ)` of the real and imaginary
parts (`isSolTest_projectedTestNewtonVectorPotentialCurlCutoff`, as in `IIb.realSolTestApprox_of`
and `IIb.solTestApprox_of_real`); `L₀ᵗΨₙ → L₀ᵗ(projSmooth Φ)` in `L^{q₀'}` slice-wise, uniformly in
`τ ∈ [0, P]` (the cutoff commutator terms carry `∇χ_R = O(R⁻¹)`, `Δχ_R = O(R⁻²)`,
`y·∇χ_R = O(1)` on the shell `R ≤ |y| ≤ 2R`, against `B = O(|y|⁻¹)` and tails of `L^{q₀'}` fields;
`3/q₀' = 21/11 < 2`), then `IIb.phasePairLimit_of IIb.testElemLimit`. -/
def L0TSolApprox : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν →
    ∀ Φ : ℝ × UnforcedLeray.Space → CVec3, IsPhaseTest P Φ →
      ∃ Ψ : ℕ → ℝ × UnforcedLeray.Space → CVec3, (∀ n, IsSolTest P (Ψ n)) ∧
        ∀ d : Yq P UnforcedLeray.B0412.q0E,
          Tendsto (fun n => phasePair P UnforcedLeray.B0412.q0E (L0T ν (Ψ n)) d) atTop
            (𝓝 (phasePair P UnforcedLeray.B0412.q0E (L0T ν (projSmooth Φ)) d))

theorem l0TSolExtension_of (hA : L0TProjCommute) (hB : L0TSolApprox) : L0TSolExtension := by
  intro P _ ν hν v hvσ hsol Φ hΦ
  obtain ⟨Ψ, hΨ, hlim⟩ := hB P ν hν Φ hΦ
  have h0 : Tendsto (fun n => phasePair P UnforcedLeray.B0412.q0E (L0T ν (Ψ n)) v) atTop
      (𝓝 (0 : ℂ)) := by
    have : (fun n => phasePair P UnforcedLeray.B0412.q0E (L0T ν (Ψ n)) v) = fun _ => 0 :=
      funext fun n => hsol (Ψ n) (hΨ n)
    rw [this]; exact tendsto_const_nhds
  rw [hA P ν hν v hvσ Φ hΦ]
  exact tendsto_nhds_unique (hlim v) h0

end UnforcedLeray.Short.PartIIIb.Concrete
