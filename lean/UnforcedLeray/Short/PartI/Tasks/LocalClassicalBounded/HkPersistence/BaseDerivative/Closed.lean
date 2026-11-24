import UnforcedLeray.Short.PartI.Sub.T02_1_2_4

/-!
# Part I, task `PartI:T02/1/2/4/4`: `derivClosed` (closedness of derivative paths)

Source of record: `the November 2 reference manuscript`, lines 261-288.

The target `derivClosed : DerivClosed` says: if `a m` has the derivative path `a' m` for every `m`,
and `a m → x`, `a' m → d` in `C([0,T], H³)`, then `d` is a derivative path of `x`.

Route (no PDE, only functional analysis on the cylinder test domain):

1. For fixed `t`, evaluation at `t` is continuous for the sup-norm topology, and the field map
   `Cyl.H.val` (`Sob.W.value`) is a continuous linear map into `L²`. So `Cyl.H.val (a m t) → Cyl.H.val (x t)`
   and `Cyl.H.val (a' m t) → Cyl.H.val (d t)` in `L²`.
2. For an admissible test `φ`, the pairing `f ↦ ∫ ψ • f dμ` with `ψ` compactly bounded is the
   continuous linear functional `Sob.testPair` on `L²` (`Sob.testPair_apply` identifies it with the
   integral). So the weak identity `∫ (∂_j φ) • f_m = -∫ φ • g_m` passes to the limit by
   `tendsto_nhds_unique`.
3. Integrability of the pairings of the limit comes from `Sob.integrable_smul_of_memLp` and
   `Lp.memLp`.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-- The test pairing `f ↦ ∫ ψ • f dμ` is continuous along `L²`-convergent sequences of fields on
the cylinder: an `L²`-limit of the fields has the limit pairing. -/
theorem derivClosed_pairTendsto {c : ℝ} (ψ : ℝ × ℝ → ℝ)
    (hψ : Sob.CompactlyBounded (Sob.cylinder c).μ ψ)
    {u : ℕ → VectorH3 c} {v : VectorH3 c}
    (hu : Tendsto (fun m => Cyl.H.val (u m)) atTop (𝓝 (Cyl.H.val v))) :
    Tendsto (fun m => ∫ q, ψ q • Cyl.H.val (u m) q ∂(Sob.cylinder c).μ) atTop
      (𝓝 (∫ q, ψ q • Cyl.H.val v q ∂(Sob.cylinder c).μ)) := by
  have hT := (Sob.testPair (F := Vec) (𝕜 := ℝ) (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)) 2 ψ hψ).continuous.tendsto
    (Cyl.H.val v)
  have hc := hT.comp hu
  simpa only [Function.comp_def, Sob.testPair_apply] using hc

/-- Closedness of a single time slice: a pointwise `L²`-limit of weak `∂_j`-derivatives is a weak
`∂_j`-derivative of the limit. -/
theorem derivClosed_slice {c : ℝ} (j : Fin 2) (y y' : ℕ → VectorH3 c) (z z' : VectorH3 c)
    (hw : ∀ m, Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (y m) : Plane → Vec) (Cyl.H.val (y' m) : Plane → Vec))
    (hy : Tendsto (fun m => Cyl.H.val (y m)) atTop (𝓝 (Cyl.H.val z)))
    (hy' : Tendsto (fun m => Cyl.H.val (y' m)) atTop (𝓝 (Cyl.H.val z'))) :
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val z : Plane → Vec) (Cyl.H.val z' : Plane → Vec) := by
  refine ⟨fun φ hφ => Sob.integrable_smul_of_memLp
      (Sob.CompactlyBounded.of_adm ((Sob.cylinder c).adm_iterDirDeriv hφ [(Sob.cylinder c).dir j]))
      (Lp.memLp _),
    fun φ hφ => Sob.integrable_smul_of_memLp (Sob.CompactlyBounded.of_adm hφ) (Lp.memLp _), ?_⟩
  intro φ hφ
  have hψ := Sob.CompactlyBounded.of_adm
    ((Sob.cylinder c).adm_iterDirDeriv hφ [(Sob.cylinder c).dir j])
  have hφ' := Sob.CompactlyBounded.of_adm hφ
  have hL := (derivClosed_pairTendsto (Sob.iterDirDeriv [(Sob.cylinder c).dir j] φ) hψ hy).congr
    (fun m => (hw m).identity φ hφ)
  have hR := (derivClosed_pairTendsto φ hφ' hy').const_smul
    ((-1 : ℝ) ^ [(Sob.cylinder c).dir j].length)
  exact tendsto_nhds_unique hL hR

/-- **Closedness of derivative paths** (task `PartI:T02/1/2/4/4`, source lines 261-288). -/
theorem derivClosed : DerivClosed := by
  intro c T j a a' x d hA ha ha' t
  have hpt : ∀ (y : ℕ → MPath c T) (z : MPath c T), Tendsto y atTop (𝓝 z) →
      Tendsto (fun m => Cyl.H.val (y m t)) atTop (𝓝 (Cyl.H.val (z t))) := by
    intro y z hyz
    have h1 : Tendsto (fun m => y m t) atTop (𝓝 (z t)) :=
      ((continuous_eval_const t).tendsto z).comp hyz
    exact ((Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2).continuous.tendsto
      (z t)).comp h1
  exact derivClosed_slice j (fun m => a m t) (fun m => a' m t) (x t) (d t)
    (fun m => hA m t) (hpt a x ha) (hpt a' d ha')

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.derivClosed
