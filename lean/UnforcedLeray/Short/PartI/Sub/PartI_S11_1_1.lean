import UnforcedLeray.Short.PartI.Sub.PartI_S11_1
import UnforcedLeray.Short.PartI.Tasks.BiotSavartPerpGrad
import UnforcedLeray.Short.PartI.Tasks.TransportGroupHjM.Zero
import UnforcedLeray.Lib.PlanarSectorsB.BiotSavartSector

/-!
# Part I, task `PartI:S11/1/1` (decomposition): `SecAEOnSmoothSums`

Source of record: `the November 2 reference manuscript`,
lines 841-889 (sector decomposition of `A_E f = (Kf)·∇E₀`, `K = ∇^⊥Δ⁻¹`, `∇E₀(y) = k(|y|) y`).

For `φ` smooth with compact support in `(0,∞)` and `m ∈ ℤ` put `q = φ(|y|)(y/|y|)^m` and
`Ψ = (Δ_{|m|}⁻¹φ)(|y|)(y/|y|)^m`.  The leaves are

* `SecStreamQ` (`PartI:S11/1/1/1`): `q` is smooth with Gaussian-class derivative bounds;
* `SecStreamPsi` (`PartI:S11/1/1/2`): `Ψ` is smooth, `ΔΨ = q`, `∇Ψ → 0` (`m ≠ 0`);
* `SecPertZero` (`PartI:S11/1/1/3`): sector `0`, `(K q)·∇E₀ = 0` (`K q` tangential, `∇E₀` radial);
* `SecAEBridge` (`PartI:S11/1/1/4`): from the pointwise identity
  `A_E q = -(i m k(|y|) Ψ)` to the identity in `L²_M` for `H^0_M` elements.

Proved here: `secPert_of` (pointwise identity for `m ≠ 0` from the leaves, `PartI:S04`
`biotSavart_eq_perpGrad` and `Planar.velocity_dot_gradE0_sector`), `secAESingle_of` (single sector
function) and `secAEOnSmoothSums_of` (finite sums).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.Planar.NUE

/-- A smooth function with compact support inside `(0,∞)`. -/
def SmoothCptFun (φ : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioi 0

/-- **Leaf `PartI:S11/1/1/1`** (lines 841-889): the sector function `φ(|y|)(y/|y|)^m` of a smooth
compactly supported profile is smooth (compactly supported away from `0`) and has Gaussian-class
derivative bounds `‖D^k q(y)‖ ≤ C (1+|y|)^N e^{-|y|²/4}`. -/
def SecStreamQ : Prop :=
  ∀ (m : ℤ) (φ : ℝ → ℂ), SmoothCptFun φ →
    ContDiff ℝ ∞ (Ang.ofProfile m φ) ∧ ∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ y,
      ‖iteratedFDeriv ℝ k (Ang.ofProfile m φ) y‖ ≤
        C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4)

/-- **Leaf `PartI:S11/1/1/2`** (lines 841-889): for `m ≠ 0` the stream function
`Ψ = ofProfile m (greenN |m| φ)` is smooth, satisfies `ΔΨ = q` (`= ofProfile m φ`) and
`∇Ψ → 0` at infinity.  Proof idea: `greenN |m| φ` solves the radial Poisson equation
(`Planar.isRadialPoissonSol_greenN`), vanishes like `r^{|m|}` at `0` and equals
`c r^{-|m|}` outside the support of `φ`; smoothness near `0` from `Ψ = r^{|m|} · (smooth)`;
decay from `r^{-|m|-1}`. -/
def SecStreamPsi : Prop :=
  ∀ (m : ℤ) (φ : ℝ → ℂ), SmoothCptFun φ → m ≠ 0 →
    ContDiff ℝ ∞ (Ang.ofProfile m (Planar.greenN m.natAbs φ)) ∧
    (∀ y, iteratedFDeriv ℝ 2 (Ang.ofProfile m (Planar.greenN m.natAbs φ)) y ![1, 1] +
      iteratedFDeriv ℝ 2 (Ang.ofProfile m (Planar.greenN m.natAbs φ)) y ![Complex.I, Complex.I] =
        Ang.ofProfile m φ y) ∧
    Tendsto (fderiv ℝ (Ang.ofProfile m (Planar.greenN m.natAbs φ))) (cocompact ℂ) (𝓝 0)

/-- **Leaf `PartI:S11/1/1/3`** (lines 841-889): sector `0`.  For radial `q = φ(|y|)` the Biot-Savart
velocity is tangential, so `(K q)·∇E₀ = 0` (a.e., or everywhere).  Proof idea: `K q = ∇^⊥Ψ₀`
with `Ψ₀` radial (`PartI:S04` applies with `Ψ₀(y) = ∫_0^{|y|} (1/s)∫_0^s tφ(t)dt ds`, whose
gradient is `(c(|y|)/|y|) y`, c the enclosed mass, and tends to `0` only if the mass is `0`;
otherwise use the explicit tangential formula of `B0009.biotSavart`). -/
def SecPertZero : Prop :=
  ∀ φ : ℝ → ℂ, SmoothCptFun φ →
    ∀ᵐ y ∂(volume : Measure ℂ), B0009.perturbation (Ang.ofProfile 0 φ) y = 0

/-- **Leaf `PartI:S11/1/1/4`** (lines 841-889): the bridge from a pointwise sector identity to the
`L²_M` identity.  If `f ∈ H^0_M` has value `secEmb M m w` with `w =ᵐ φ`, `φ` smooth with compact
support in `(0,∞)`, and the perturbation of `q = ofProfile m φ` is a.e. `-(i m k(|y|) Ψ)`,
`Ψ = ofProfile m (greenN |m| φ)`, then `(A_E f).value = secEmb M m (-couplingSec hM m w)`.
Proof idea: `AEj_value_ae`, `perturbation_congr_ae` (value `=ᵐ` `ofProfile m φ`),
`Planar.coeFn_couplingSec`, `Planar.greenN_congr`, `Planar.coeFn_secEmb`, and `wMeasure ≪ volume`;
conclude by `Lp.ext`. -/
def SecAEBridge : Prop :=
  ∀ {M : ℝ} (hM : 1 < M) (m : ℤ) (w : Planar.ProfL2 M) (φ : ℝ → ℂ), SmoothCptFun φ →
    (w : ℝ → ℂ) =ᵐ[Planar.profileMeasure M] φ → ∀ f : B0008.HjM 0 M, f.value = Planar.secEmb M m w →
    (∀ᵐ y ∂(volume : Measure ℂ), B0009.perturbation (Ang.ofProfile m φ) y =
      -(Complex.I * (m : ℂ) * (GaussianVortex.radialK ‖y‖ : ℂ) *
        Ang.ofProfile m (Planar.greenN m.natAbs φ) y)) →
    (B0061.AEj 0 hM f).value = Planar.secEmb M m (-(Planar.couplingSec hM m w))

/-- The pointwise identity `A_E q = -(i m k Ψ)` for `m ≠ 0`, from the two stream leaves. -/
theorem secPert_of (hQ : SecStreamQ) (hP : SecStreamPsi) (m : ℤ) (hm : m ≠ 0) (φ : ℝ → ℂ)
    (hφ : SmoothCptFun φ) (y : ℂ) :
    B0009.perturbation (Ang.ofProfile m φ) y =
      -(Complex.I * (m : ℂ) * (GaussianVortex.radialK ‖y‖ : ℂ) *
        Ang.ofProfile m (Planar.greenN m.natAbs φ) y) := by
  unfold SecStreamQ at hQ
  unfold SecStreamPsi at hP
  obtain ⟨hq, hqb⟩ := hQ m φ hφ
  obtain ⟨hΨ, hlap, hdec⟩ := hP m φ hφ hm
  have hS := biotSavart_eq_perpGrad hq hqb (Planar.integral_ofProfile_eq_zero hm φ) hΨ hlap hdec y
  have hd : HasFDerivAt (Ang.ofProfile m (Planar.greenN m.natAbs φ))
      (fderiv ℝ (Ang.ofProfile m (Planar.greenN m.natAbs φ)) y) y :=
    ((hΨ.differentiable (by simp)) y).hasFDerivAt
  have hv := Planar.velocity_dot_gradE0_sector hd
  have hg := B0009.gradE0_eq y
  unfold B0009.perturbation
  rw [hS.1, hS.2, hg]
  simp only []
  push_cast at hv ⊢
  linear_combination hv

/-- Single sector function: `SecAEOnSmoothSums` for `f` with `f.value = secEmb M m w`. -/
theorem secAESingle_of (hQ : SecStreamQ) (hP : SecStreamPsi) (hZ : SecPertZero)
    (hB : SecAEBridge) {M : ℝ} (hM : 1 < M) (m n : ℤ) (w : Planar.ProfL2 M)
    (hw : IsSmoothCptProfile M w) (f : B0008.HjM 0 M) (hf : f.value = Planar.secEmb M m w) :
    Planar.secProf M n (B0061.AEj 0 hM f).value =
      -Planar.couplingSec hM n (Planar.secProf M n f.value) := by
  obtain ⟨φ, hs, hc, hts, hae⟩ := hw
  have hφ : SmoothCptFun φ := ⟨hs, hc, hts⟩
  have hpert : ∀ᵐ y ∂(volume : Measure ℂ), B0009.perturbation (Ang.ofProfile m φ) y =
      -(Complex.I * (m : ℂ) * (GaussianVortex.radialK ‖y‖ : ℂ) *
        Ang.ofProfile m (Planar.greenN m.natAbs φ) y) := by
    by_cases hm : m = 0
    · subst hm
      filter_upwards [hZ φ hφ] with y hy
      rw [hy]
      simp
    · exact Eventually.of_forall fun y => secPert_of hQ hP m hm φ hφ y
  rw [hB hM m w φ hφ hae f hf hpert, hf, Planar.secProf_secEmb, Planar.secProf_secEmb]
  by_cases h : m = n
  · subst h
    simp
  · simp [h]

/-- `SecAEOnSmoothSums` from the four leaves: finite sums of single sector functions. -/
theorem secAEOnSmoothSums_of (hQ : SecStreamQ) (hP : SecStreamPsi) (hZ : SecPertZero)
    (hB : SecAEBridge) : SecAEOnSmoothSums := by
  intro M hM n f hf
  obtain ⟨F, w, hw, hfs⟩ := hf
  set g : ℤ → B0008.HjM 0 M := fun m => TransportGroupHjMZero.ofL2 M (Planar.secEmb M m (w m)) with hg
  have hsum : f = ∑ m ∈ F, g m := by
    apply B0008.HjM.ext
    have := map_sum (B0008.HjM.valueCLM 0 M) g F
    simp only [B0008.HjM.valueCLM_apply] at this
    rw [this, hfs]
    exact Finset.sum_congr rfl fun m _ => (TransportGroupHjMZero.value_ofL2 _).symm
  have key : ∀ m ∈ F, Planar.secProf M n (B0061.AEj 0 hM (g m)).value =
      -Planar.couplingSec hM n (Planar.secProf M n (g m).value) := fun m hm =>
    secAESingle_of hQ hP hZ hB hM m n (w m) (hw m hm) (g m) (TransportGroupHjMZero.value_ofL2 _)
  have e1 : (B0061.AEj 0 hM f).value = ∑ m ∈ F, (B0061.AEj 0 hM (g m)).value := by
    rw [hsum, map_sum]
    exact (map_sum (B0008.HjM.valueCLM 0 M) (fun m => B0061.AEj 0 hM (g m)) F)
  have e2 : f.value = ∑ m ∈ F, (g m).value := by
    rw [hsum]
    exact (map_sum (B0008.HjM.valueCLM 0 M) g F)
  have s1 : Planar.secProf M n (B0061.AEj 0 hM f).value =
      ∑ m ∈ F, Planar.secProf M n (B0061.AEj 0 hM (g m)).value := by
    rw [e1]
    exact map_sum (Planar.secProf M n) (fun m => (B0061.AEj 0 hM (g m)).value) F
  have s2 : Planar.secProf M n f.value = ∑ m ∈ F, Planar.secProf M n (g m).value := by
    rw [e2]
    exact map_sum (Planar.secProf M n) (fun m => (g m).value) F
  have s3 : Planar.couplingSec hM n (Planar.secProf M n f.value) =
      ∑ m ∈ F, Planar.couplingSec hM n (Planar.secProf M n (g m).value) := by
    rw [s2]
    exact map_sum (Planar.couplingSec hM n) (fun m => Planar.secProf M n (g m).value) F
  rw [s1, s3, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl key

end UnforcedLeray.Short.PartI
