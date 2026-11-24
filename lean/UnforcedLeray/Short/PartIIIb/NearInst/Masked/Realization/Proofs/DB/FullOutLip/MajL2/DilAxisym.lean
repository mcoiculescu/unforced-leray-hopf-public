import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_2_4
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.RotExists

/-!
# `FmDilAxisym` (source 2666-2668, 3996-4011)

`fmKer ν l` depends on its argument only through its norm, so the substitution `z ↦ Q z` for a
linear isometry `Q` fixing `hRad` and the third coordinate (`rotExists_holds`) leaves each fixed-`l`
integral of `dilMajG` unchanged, using `AxisymProf` of the profile.  This follows `dilMajAxisym_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem fmDilAxisym : UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.FmDilAxisym := by
  intro ν μ g hg τ y y' h1 h2
  obtain ⟨Q, hQy, hQ⟩ := rotExists_holds y y' h1 h2
  subst hQy
  have hemb : MeasurableEmbedding (Q : UnforcedLeray.Space → UnforcedLeray.Space) :=
    (LinearIsometryEquiv.toHomeomorph Q).measurableEmbedding
  have hpt : ∀ (l : ℝ) (z : UnforcedLeray.Space),
      fmKer ν l (Q y - l • Q z) * g (τ + 2 * Real.log l) (Q z) =
        fmKer ν l (y - l • z) * g (τ + 2 * Real.log l) z := by
    intro l z
    have hsub : Q y - l • Q z = Q (y - l • z) := by rw [map_sub, map_smul]
    rw [hsub, hg (τ + 2 * Real.log l) (Q z) z (hQ z).1 (hQ z).2]
    unfold fmKer
    rw [LinearIsometryEquiv.norm_map]
  have key : ∀ l : ℝ,
      ∫⁻ z : UnforcedLeray.Space, fmKer ν l (Q y - l • z) * g (τ + 2 * Real.log l) z =
        ∫⁻ z : UnforcedLeray.Space, fmKer ν l (y - l • z) * g (τ + 2 * Real.log l) z := by
    intro l
    calc ∫⁻ z : UnforcedLeray.Space, fmKer ν l (Q y - l • z) * g (τ + 2 * Real.log l) z
        = ∫⁻ z : UnforcedLeray.Space,
            fmKer ν l (Q y - l • Q z) * g (τ + 2 * Real.log l) (Q z) :=
          ((Q.measurePreserving).lintegral_comp_emb hemb _).symm
      _ = ∫⁻ z : UnforcedLeray.Space, fmKer ν l (y - l • z) * g (τ + 2 * Real.log l) z :=
          lintegral_congr fun z => hpt l z
  unfold dilMajG
  exact lintegral_congr fun l => by rw [key l]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
