import UnforcedLeray.Short.PartI.Sub.S11

/-!
# Part I, task `PartI:S11/1`: `secProfAE` reduced to a dense subclass (conditional)

Source of record: `the November 2 reference manuscript`, lines 841-889
(sector decomposition of the Euler generator, `K = ∇^⊥Δ⁻¹`).

Target: `SecProfAE` (`Short/PartI/Sub/S11.lean`): the sector-`n` profile of `A_E f = (Kf)·∇E₀` is
`-couplingSec hM n` applied to the sector-`n` profile of `f`, for every `f ∈ H^0_M`.

Both sides are bounded linear (continuous) in `f`, so it suffices to check the identity on a dense
subclass: the finite sums of sector functions `w(r) e^{imϑ}` with `w` smooth, compactly supported
in `(0,∞)`.  Two precise leaves:

* `SecAEOnSmoothSums`: the identity on that subclass (the pointwise Biot-Savart computation of
  `Lib/PlanarSectorsB/BiotSavartSector.lean` plus `PartI:S04`, `biotSavart_eq_perpGrad`);
* `SmoothSectorSumsDense`: density of that subclass in `H^0_M` (density of smooth compactly
  supported profiles in `ProfL2 M` and the sector decomposition `Planar.norm_sq_eq_tsum`).

`secProfAE_of` proves `SecProfAE` from them.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- A radial profile that is (a.e. equal to) a smooth function with compact support in `(0,∞)`. -/
def IsSmoothCptProfile (M : ℝ) (h : Planar.ProfL2 M) : Prop :=
  ∃ φ : ℝ → ℂ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioi 0 ∧
    (h : ℝ → ℂ) =ᵐ[Planar.profileMeasure M] φ

/-- Finite sums `∑_{m ∈ F} w_m(r) e^{imϑ}` of sector functions with smooth compactly supported
profiles in `(0,∞)` (dense in `L²_M`, source lines 841-889). -/
def SmoothSectorSums (M : ℝ) : Set (Planar.L2w M) :=
  {g | ∃ (F : Finset ℤ) (w : ℤ → Planar.ProfL2 M),
    (∀ m ∈ F, IsSmoothCptProfile M (w m)) ∧ g = ∑ m ∈ F, Planar.secEmb M m (w m)}

/-- **Leaf 1** (identity on the dense subclass; source lines 841-889, `K = ∇^⊥Δ⁻¹`,
`∇E₀(y) = k(|y|)y`): for `f ∈ H^0_M` whose value is a finite sum of smooth compactly supported
sector functions, `secProf n (A_E f) = -couplingSec n (secProf n f)`.  Proof: for
`f = ofProfile m w` the stream function is `ofProfile m (greenN |m| w)`, smooth with
`Δ Ψ = f` and `∇Ψ → 0`; `PartI:S04` gives `Kf = ∇^⊥Ψ`, and
`BiotSavartSector.velocity_dot_gradE0_sector` gives `(Kf)·∇E₀ = -i m k Ψ`, a pure sector-`m`
function with profile `-couplingSec w` (compare `Planar.coeFn_couplingSec`); the case `m = 0`
is `(Kf)·y = 0`; sum over `m`. -/
def SecAEOnSmoothSums : Prop :=
  ∀ {M : ℝ} (hM : 1 < M) (n : ℤ) (f : B0008.HjM 0 M), f.value ∈ SmoothSectorSums M →
    Planar.secProf M n (B0061.AEj 0 hM f).value =
      -Planar.couplingSec hM n (Planar.secProf M n f.value)

/-- **Leaf 2** (density; source lines 841-889): the elements of `H^0_M` whose value is a finite
sum of smooth compactly supported sector functions are dense in `H^0_M`.  Proof: `H^0_M ≅ L²_M`
(`norm_eq_value_zero`, `ofL2`, in `Short/PartI/Tasks/TransportGroupHjM/Zero.lean`); the sector
decomposition `Planar.norm_sq_eq_tsum`/`Planar.hasSum_secEmb_secProf` reduces to finitely many
sectors, and `C_c^∞((0,∞))` is dense in `ProfL2 M` (the measure `profileMeasure M` is a
`σ`-finite regular measure on `(0,∞)` with finite mass on compacts). -/
def SmoothSectorSumsDense : Prop :=
  ∀ {M : ℝ}, 1 < M →
    Dense {f : B0008.HjM 0 M | f.value ∈ SmoothSectorSums M}

theorem secProfAE_of (h1 : SecAEOnSmoothSums) (h2 : SmoothSectorSumsDense) : SecProfAE := by
  intro M hM n f
  have hd := h2 hM
  have hc : Continuous fun g : B0008.HjM 0 M =>
      Planar.secProf M n (B0061.AEj 0 hM g).value +
        Planar.couplingSec hM n (Planar.secProf M n g.value) := by
    have hv : Continuous fun g : B0008.HjM 0 M => g.value := (B0008.HjM.valueCLM 0 M).continuous
    have hA : Continuous fun g : B0008.HjM 0 M => (B0061.AEj 0 hM g).value :=
      (B0008.HjM.valueCLM 0 M).continuous.comp (B0061.AEj 0 hM).continuous
    exact ((Planar.secProf M n).continuous.comp hA).add
      ((Planar.couplingSec hM n).continuous.comp ((Planar.secProf M n).continuous.comp hv))
  have hclosed : IsClosed {g : B0008.HjM 0 M |
      Planar.secProf M n (B0061.AEj 0 hM g).value +
        Planar.couplingSec hM n (Planar.secProf M n g.value) = 0} :=
    isClosed_eq hc continuous_const
  have hsub : {g : B0008.HjM 0 M | g.value ∈ SmoothSectorSums M} ⊆ {g : B0008.HjM 0 M |
      Planar.secProf M n (B0061.AEj 0 hM g).value +
        Planar.couplingSec hM n (Planar.secProf M n g.value) = 0} := by
    intro g hg
    have := h1 hM n g hg
    show _ + _ = 0
    rw [this]
    simp
  have := closure_minimal hsub hclosed (hd.closure_eq ▸ Set.mem_univ f)
  have h0 : Planar.secProf M n (B0061.AEj 0 hM f).value +
      Planar.couplingSec hM n (Planar.secProf M n f.value) = 0 := this
  exact eq_neg_of_add_eq_zero_left h0

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.secProfAE_of
