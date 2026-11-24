import UnforcedLeray.Short.PartI.Sub.PartI_S11_1_1

/-!
# Part I, task `PartI:S11/1/1/4`: from the pointwise sector identity to the `L²_M` identity

Target: `secAEBridge : SecAEBridge` (`Sub/PartI_S11_1_1.lean`, lines 841-889). If `f ∈ H⁰_M` has
value `secEmb M m w` with `w =ᵐ φ` (profile measure), and the perturbation of `ofProfile m φ` is a.e.
`-(i m k(|y|) Ψ)` with `Ψ = ofProfile m (greenN |m| φ)`, then
`(A_E f).value = secEmb M m (-couplingSec hM m w)`.

Method. Transport the a.e. identities between `volume`, `wMeasure` and `profileMeasure` using the
equivalences `volume ≪ wMeasure`, `wMeasure ≪ volume` and `volume.restrict (Ioi 0) ≪ profileMeasure`.
`AEj_value_ae` and `perturbation_congr_ae` reduce `(A_E f).value` to the perturbation of
`ofProfile m φ`. The right-hand side is identified through `coeFn_secEmb`, `coeFn_couplingSec` and
`greenN_congr`. Conclude by `Lp.ext`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.Planar.NUE

/-- **Target `PartI:S11/1/1/4`**: `SecAEBridge` (see `Sub/PartI_S11_1_1.lean`, lines 841-889). -/
theorem secAEBridge : UnforcedLeray.Short.PartI.SecAEBridge := by
  unfold SecAEBridge
  intro M hM m w φ _hφ hwφ f hf hpert
  -- Step 1: the value of `f` agrees with `ofProfile m φ` almost everywhere on `ℂ`.
  have hA : ⇑(f.value) =ᵐ[Planar.wMeasure M] Ang.ofProfile m (w : ℝ → ℂ) := by
    rw [hf]
    exact Planar.coeFn_secEmb M m w
  have hA' : ⇑(f.value) =ᵐ[volume] Ang.ofProfile m (w : ℝ → ℂ) :=
    (Planar.volume_ac M).ae_le hA
  have hw : (w : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] φ :=
    (Planar.ac_profileMeasure M).ae_le hwφ
  have hW : Ang.ofProfile m (w : ℝ → ℂ) =ᵐ[volume] Ang.ofProfile m φ :=
    Planar.ofProfile_congr_ae m hw
  have hAφ : (⇑(f.value) : ℂ → ℂ) =ᵐ[volume] Ang.ofProfile m φ := hA'.trans hW
  have hpertEq : B0009.perturbation (⇑(f.value)) = B0009.perturbation (Ang.ofProfile m φ) :=
    B0009.perturbation_congr_ae hAφ
  -- Step 2: the value of `A_E f` is the stated sector function, volume-a.e.
  have h6 : ∀ᵐ y ∂(volume : Measure ℂ), (B0061.AEj 0 hM f).value y =
      -(Complex.I * (m : ℂ) * (GaussianVortex.radialK ‖y‖ : ℂ) *
        Ang.ofProfile m (Planar.greenN m.natAbs φ) y) := by
    filter_upwards [B0061.AEj_value_ae hM f, hpert] with y h1 h2
    rw [h1, hpertEq]
    exact h2
  -- Step 3: the right-hand side, pointwise on `ℂ` almost everywhere on `wMeasure`.
  have hcs : ⇑(-(Planar.couplingSec hM m w)) =ᵐ[Planar.profileMeasure M]
      fun r => -(Complex.I * (m : ℂ) * (GaussianVortex.radialK r : ℂ) *
        Planar.greenN m.natAbs (w : ℝ → ℂ) r) := by
    filter_upwards [Lp.coeFn_neg (Planar.couplingSec hM m w),
      Planar.coeFn_couplingSec hM m w] with r h1 h2
    rw [h1, Pi.neg_apply, h2]
  have h9 : Ang.ofProfile m ⇑(-(Planar.couplingSec hM m w)) =ᵐ[Planar.wMeasure M]
      Ang.ofProfile m (fun r => -(Complex.I * (m : ℂ) * (GaussianVortex.radialK r : ℂ) *
        Planar.greenN m.natAbs (w : ℝ → ℂ) r)) :=
    Planar.ofProfile_congr_ae' M m hcs
  have hpt : ∀ y : ℂ, Ang.ofProfile m (fun r => -(Complex.I * (m : ℂ) *
        (GaussianVortex.radialK r : ℂ) * Planar.greenN m.natAbs (w : ℝ → ℂ) r)) y =
      -(Complex.I * (m : ℂ) * (GaussianVortex.radialK ‖y‖ : ℂ) *
        Ang.ofProfile m (Planar.greenN m.natAbs φ) y) := by
    intro y
    have hg := Planar.greenN_congr (M := M) m.natAbs hwφ ‖y‖
    simp only [Ang.ofProfile]
    rw [hg]
    ring
  -- Step 4: conclude in `L²(wMeasure)`.
  apply Lp.ext
  have h7 : ⇑((B0061.AEj 0 hM f).value) =ᵐ[Planar.wMeasure M]
      fun y => -(Complex.I * (m : ℂ) * (GaussianVortex.radialK ‖y‖ : ℂ) *
        Ang.ofProfile m (Planar.greenN m.natAbs φ) y) :=
    (Planar.wMeasure_ac M).ae_le h6
  have h8 : ⇑(Planar.secEmb M m (-(Planar.couplingSec hM m w))) =ᵐ[Planar.wMeasure M]
      Ang.ofProfile m ⇑(-(Planar.couplingSec hM m w)) :=
    Planar.coeFn_secEmb M m _
  filter_upwards [h7, h8, h9] with y e7 e8 e9
  exact e7.trans (e8.trans (e9.trans (hpt y))).symm

end UnforcedLeray.Short.PartI
