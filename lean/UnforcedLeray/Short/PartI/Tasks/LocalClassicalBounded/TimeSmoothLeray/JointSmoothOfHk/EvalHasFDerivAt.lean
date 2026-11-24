import UnforcedLeray.Short.PartI.Sub.T02_1_4_5

/-!
# Part I, task `PartI:T02/1/4/5/1`: Fréchet differentiability of the evaluation map

Source of record: `the November 2 reference manuscript`, lines 261-288 (the Sobolev
embedding on the cell, applied to the linear family `h ↦ g h` of `C¹` functions on the plane).

Target: `EvalHasFDerivAt` (`Short/PartI/Sub/T02_1_4_5.lean`), proved here as `evalHasFDerivAt`.

Proof.  Put `A h := g h z`.  By the bound for `j = 0`, `A` is a continuous linear map `E →L F`
with norm at most `|C|`.  Put `L (h, v) := A h + D(g x) z v`, a continuous linear map on
`E × Plane`; the identity `L (h, v) = g h z + D(g x) z v` holds by definition.  For the Fréchet
derivative, the remainder at `(x, z)` in direction `(h, v)` splits as
`(g h (z + v) - g h z) + (g x (z + v) - g x z - D(g x) z v)`:
* the first summand has norm at most `C ‖h‖ ‖v‖` by the mean value inequality on `Plane`, using
  the derivative bound `‖D(g h) y‖ ≤ C ‖h‖` (the bound for `j = 1`), hence it is `o(‖(h, v)‖)`;
* the second summand is `o(‖v‖)` because `g x` is differentiable at `z`, hence `o(‖(h, v)‖)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

theorem evalHasFDerivAt : EvalHasFDerivAt := by
  intro E iE iE' F iF iF' g C hd hb x z
  -- pointwise bounds from the derivative bounds at orders `0` and `1`
  have hb0 : ∀ h : E, ‖g h z‖ ≤ C * ‖h‖ := fun h => by
    have h0 := hb h 0 (by norm_num) z
    rwa [norm_iteratedFDeriv_zero] at h0
  have hbd : ∀ (h : E) (y : Plane), ‖fderiv ℝ (g h) y‖ ≤ C * ‖h‖ := fun h y => by
    have h1 := hb h 1 le_rfl y
    rwa [norm_iteratedFDeriv_one] at h1
  -- the continuous linear map `h ↦ g h z`
  let A₀ : E →ₗ[ℝ] F := (LinearMap.proj z).comp g
  have hA₀ : ∀ h : E, A₀ h = g h z := fun h => rfl
  let A : E →L[ℝ] F := A₀.mkContinuous |C| (fun h => by
    rw [hA₀]
    exact (hb0 h).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg h)))
  have hA : ∀ h : E, A h = g h z := fun h => rfl
  -- the candidate derivative on `E × Plane`
  obtain ⟨L, hLdef⟩ : ∃ L : E × Plane →L[ℝ] F,
      L = A.comp (ContinuousLinearMap.fst ℝ E Plane)
        + (fderiv ℝ (g x) z).comp (ContinuousLinearMap.snd ℝ E Plane) := ⟨_, rfl⟩
  have hLf : ∀ (h : E) (v : Plane), L (h, v) = g h z + fderiv ℝ (g x) z v := by
    intro h v
    rw [hLdef]
    simp [hA]
  have hLp : ∀ p : E × Plane, L p = g p.1 z + fderiv ℝ (g x) z p.2 :=
    fun p => hLf p.1 p.2
  refine ⟨L, ?_, hLf⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  -- the first summand `g h (z + v) - g h z` is `o(‖(h, v)‖)` (mean value inequality)
  have hT1 : (fun p : E × Plane => g p.1 (z + p.2) - g p.1 z)
      =o[𝓝 0] (fun p : E × Plane => p) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hcont : Continuous (fun p : E × Plane => |C| * ‖p‖) :=
      continuous_const.mul continuous_norm
    have ht : Tendsto (fun p : E × Plane => |C| * ‖p‖) (𝓝 0)
        (𝓝 (|C| * ‖(0 : E × Plane)‖)) :=
      hcont.tendsto 0
    rw [norm_zero, mul_zero] at ht
    have hlt : ∀ᶠ y in 𝓝 (0 : ℝ), y ≤ c := Iic_mem_nhds hc
    have hK : ∀ᶠ p : E × Plane in 𝓝 0, |C| * ‖p‖ ≤ c := ht.eventually hlt
    filter_upwards [hK] with p hp
    show ‖g p.1 (z + p.2) - g p.1 z‖ ≤ c * ‖p‖
    have hm : ‖g p.1 (z + p.2) - g p.1 z‖ ≤ C * ‖p.1‖ * ‖z + p.2 - z‖ :=
      Convex.norm_image_sub_le_of_norm_fderiv_le (fun y _ => (hd p.1).differentiable_one y)
        (fun y _ => hbd p.1 y) convex_univ (mem_univ z) (mem_univ (z + p.2))
    have e : z + p.2 - z = p.2 := by abel
    rw [e] at hm
    have hp1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
    have hp2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
    calc ‖g p.1 (z + p.2) - g p.1 z‖ ≤ C * ‖p.1‖ * ‖p.2‖ := hm
      _ ≤ |C| * ‖p.1‖ * ‖p.2‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)) (norm_nonneg _)
      _ ≤ |C| * ‖p‖ * ‖p‖ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hp1 (abs_nonneg C)) hp2 (norm_nonneg _)
            (mul_nonneg (abs_nonneg C) (norm_nonneg _))
      _ ≤ c * ‖p‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg p)
  -- the second summand `g x (z + v) - g x z - D(g x) z v` is `o(‖v‖)`, hence `o(‖(h, v)‖)`
  have hdiff : HasFDerivAt (g x) (fderiv ℝ (g x) z) z :=
    ((hd x).differentiable_one z).hasFDerivAt
  have hφ := hasFDerivAt_iff_isLittleO_nhds_zero.mp hdiff
  have hsnd : Tendsto (fun p : E × Plane => p.2) (𝓝 0) (𝓝 0) :=
    continuous_snd.tendsto' (0 : E × Plane) (0 : Plane) (by simp)
  have h2 : (fun p : E × Plane => p.2) =O[𝓝 (0 : E × Plane)] (fun p : E × Plane => p) :=
    Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun p => by simpa using norm_snd_le p)
  have hT2 : (fun p : E × Plane => g x (z + p.2) - g x z - fderiv ℝ (g x) z p.2)
      =o[𝓝 0] (fun p : E × Plane => p) :=
    (hφ.comp_tendsto hsnd).trans_isBigO h2
  -- assemble: the remainder equals `T1 + T2`
  refine (hT1.add hT2).congr_left ?_
  intro p
  show (g p.1 (z + p.2) - g p.1 z) + (g x (z + p.2) - g x z - fderiv ℝ (g x) z p.2)
      = g (x + p.1) (z + p.2) - g x z - L p
  rw [hLp p, map_add, Pi.add_apply]
  abel

end UnforcedLeray.Short.PartI
