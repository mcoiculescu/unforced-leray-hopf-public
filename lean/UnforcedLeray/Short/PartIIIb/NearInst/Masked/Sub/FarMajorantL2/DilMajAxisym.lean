import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs

/-!
# Axisymmetry of `dilMaj` in the output point (source 2666-2668)

Given `y, y'` with the same `hRad` and the same third coordinate, a linear isometry `Q` of `ℝ³`
(`RotExists`) carries `y` to `y'` and fixes `hRad` and the third coordinate of every point.
Substituting `z ↦ Q z` in each fixed-`l` integral (measure preservation, no measurability needed)
and using `‖Q w‖ = ‖w‖` together with `AxisymProf` of the source gives the identity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem dilMajAxisym_of (hR : RotExists) : DilMajAxisym := by
  intro μ d g hg τ y y' h1 h2
  obtain ⟨Q, hQy, hQ⟩ := hR y y' h1 h2
  subst hQy
  have hemb : MeasurableEmbedding (Q : UnforcedLeray.Space → UnforcedLeray.Space) :=
    (LinearIsometryEquiv.toHomeomorph Q).measurableEmbedding
  have hpt : ∀ (l : ℝ) (z : UnforcedLeray.Space),
      farKern d (Q y - l • Q z) * g (τ + 2 * Real.log l) (Q z) =
        farKern d (y - l • z) * g (τ + 2 * Real.log l) z := by
    intro l z
    have hsub : Q y - l • Q z = Q (y - l • z) := by rw [map_sub, map_smul]
    rw [hsub, hg (τ + 2 * Real.log l) (Q z) z (hQ z).1 (hQ z).2]
    unfold farKern
    rw [LinearIsometryEquiv.norm_map]
  have key : ∀ l : ℝ,
      ∫⁻ z : UnforcedLeray.Space, farKern d (Q y - l • z) * g (τ + 2 * Real.log l) z =
        ∫⁻ z : UnforcedLeray.Space, farKern d (y - l • z) * g (τ + 2 * Real.log l) z := by
    intro l
    calc ∫⁻ z : UnforcedLeray.Space, farKern d (Q y - l • z) * g (τ + 2 * Real.log l) z
        = ∫⁻ z : UnforcedLeray.Space,
            farKern d (Q y - l • Q z) * g (τ + 2 * Real.log l) (Q z) :=
          ((Q.measurePreserving).lintegral_comp_emb hemb _).symm
      _ = ∫⁻ z : UnforcedLeray.Space, farKern d (y - l • z) * g (τ + 2 * Real.log l) z :=
          lintegral_congr fun z => hpt l z
  unfold dilMaj
  exact lintegral_congr fun l => by rw [key l]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
