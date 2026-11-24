import UnforcedLeray.Short.PartI.Sub.T02_4
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.LocalVorticityEquation.Vorticity

/-!
# Part I, `LocalVorticityEquation`: the scalar vorticity equation on `(0, T) × ℝ²`

Source of record: `the November 2 reference manuscript`, lines 276-288 ("the scalar
vorticity equation preserves zero circulation and its `L¹, L^∞` bounds"). The target
`LocalVorticityEquation` (`Short/PartI/Sub/T02_4.lean`) asserts that the vorticity residual vanishes
for `s ∈ (0, T)` along a classical solution on `[0, T]`.

Proof: the open-set form `LV.lvVorticityResidual_eq_zero` (`LocalVorticityEquation/Vorticity.lean`)
applied on `O = Ioo 0 T ×ˢ univ`. The hypotheses are restrictions of `IsClassicalOn`: smoothness on
`Icc 0 T ×ˢ univ` restricts to `O`, the solenoidal condition on `Icc 0 T` contains `Ioo 0 T`, and the
momentum equation on `Ioo 0 T` is exactly the one on `O`.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- **Local-time vorticity equation** (`LocalVorticityEquation`, source lines 276-288): for a
classical solution on `[0, T]`, the vorticity `ω = curl v` satisfies `ω_s + v·∇ω - νΔω = 0` on
`(0, T)`. -/
theorem localVorticityEquation : LocalVorticityEquation := by
  intro ν c T v p _hν _hc hT hcl s hs z
  have hO : IsOpen (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set Plane)) :=
    isOpen_Ioo.prod isOpen_univ
  have hslab : ∀ (s : ℝ) (z z' : Plane), (s, z) ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set Plane) →
      (s, z') ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set Plane) :=
    fun _ _ z' h => ⟨h.1, Set.mem_univ z'⟩
  have hu : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2)
      (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set Plane)) :=
    hcl.smooth_v.mono (Set.prod_mono Set.Ioo_subset_Icc_self Subset.rfl)
  have hp : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => p x.1 x.2)
      (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set Plane)) :=
    hcl.smooth_p.mono (Set.prod_mono Set.Ioo_subset_Icc_self Subset.rfl)
  have hdiv : ∀ (s : ℝ) (z : Plane), (s, z) ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set Plane) →
      Cyl.divergence (v s) z = 0 :=
    fun s z h => hcl.solenoidal s (Set.Ioo_subset_Icc_self h.1) z
  have hmom : ∀ (s : ℝ) (z : Plane), (s, z) ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set Plane) →
      Train.momentumResidual ν v p s z = 0 :=
    fun s z h => hcl.momentum s h.1 z
  exact LV.lvVorticityResidual_eq_zero hO hslab hu hp hdiv hmom
    (show (s, z) ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set Plane) from ⟨hs, Set.mem_univ z⟩)

end UnforcedLeray.Short.PartI
