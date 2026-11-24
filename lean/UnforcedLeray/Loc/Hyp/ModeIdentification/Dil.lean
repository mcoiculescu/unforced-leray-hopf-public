import UnforcedLeray.Loc.L13PhysicalRemainder
import UnforcedLeray.Loc.L04ModeRegularity
import UnforcedLeray.Lib.BochnerTime

/-!
# H-ModeId helpers: the similarity dilation `D(s)` on `L²`

Support for `Loc/Hyp/ModeIdentification.lean` (target `ModeIdentificationHyp`,
`paper/main.tex` lines 308–318, blueprint units B1009, B1010).

`D(s)F = e^{s/2} F(e^{s/2}·)` is `Loc.L02.dil`. Proved here: the group law
`D(a)D(b) = D(a+b)`, `D(0) = 1`, the scaling `⟨D(s)A, D(s)B⟩ = e^{-s/2}⟨A,B⟩`, and the joint
continuity of `s ↦ D(k(s)) g(s)` along continuous paths (the compiled
`L13.continuousOn_dil_apply` covers only `s ≥ 0`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.Blueprint.ModeId

open SobolevGraph
open UnforcedLeray.Loc.L02 (dil coeFn_dil norm_dil_apply_le)

theorem dil_dil (a b : ℝ) (F : L2Space) : dil a (dil b F) = dil (a + b) F := by
  apply Lp.ext
  refine (coeFn_dil a _).trans ?_
  refine (SpatialScaling.ae_eq_spatialScale (coeFn_dil b F) _ (Real.exp_pos _).ne').trans ?_
  refine Filter.EventuallyEq.trans ?_ (coeFn_dil (a + b) F).symm
  refine Filter.Eventually.of_forall (fun x => ?_)
  simp only [SpatialScaling.spatialScale, smul_smul, ← Real.exp_add]
  rw [show a / 2 + b / 2 = (a + b) / 2 by ring, show b / 2 + a / 2 = (a + b) / 2 by ring]

theorem dil_zero (F : L2Space) : dil 0 F = F := by
  apply Lp.ext
  refine (coeFn_dil 0 F).trans (Filter.Eventually.of_forall (fun x => ?_))
  simp [SpatialScaling.spatialScale]

theorem dil_neg_dil (s : ℝ) (F : L2Space) : dil (-s) (dil s F) = F := by
  rw [dil_dil, neg_add_cancel, dil_zero]

theorem dil_injective (s : ℝ) : Function.Injective (dil s) := fun A B h => by
  rw [← dil_neg_dil s A, h, dil_neg_dil]

/-- `⟨D(s)A, D(s)B⟩ = e^{-s/2} ⟨A, B⟩`. -/
theorem inner_dil_dil (s : ℝ) (A B : L2Space) :
    inner ℝ (dil s A) (dil s B) = Real.exp (-s / 2) * inner ℝ A B := by
  rw [L13.dil_adjoint, dil_neg_dil]

theorem norm_dil_sq (s : ℝ) (A : L2Space) :
    ‖dil s A‖ ^ 2 = Real.exp (-s / 2) * ‖A‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_dil_dil]

/-- `s ↦ D(s)F` is continuous on `ℝ`. -/
theorem continuous_dil_apply (F : L2Space) : Continuous (fun s => dil s F) := by
  rw [continuous_iff_continuousAt]
  intro s₀
  have hc : ContinuousOn (fun s => dil s (dil (s₀ - 1) F)) (Ici 0) :=
    Loc.L02.continuousOn_freeL2 le_rfl (dil (s₀ - 1) F)
  have h1 : ContinuousAt (fun s => dil s (dil (s₀ - 1) F)) 1 :=
    hc.continuousAt (Ici_mem_nhds (by norm_num))
  have h2 : ContinuousAt (fun s : ℝ => s - (s₀ - 1)) s₀ := by fun_prop
  have h3 : ContinuousAt (fun s => dil (s - (s₀ - 1)) (dil (s₀ - 1) F)) s₀ := by
    have : (s₀ - (s₀ - 1)) = 1 := by ring
    refine ContinuousAt.comp (g := fun s => dil s (dil (s₀ - 1) F)) ?_ h2
    rw [this]
    exact h1
  refine h3.congr (Filter.Eventually.of_forall (fun s => ?_))
  simp only [dil_dil, sub_add_cancel]

/-- `s ↦ D(k(s)) g(s)` is continuous on `S` for continuous `k` and `g` continuous on `S`. -/
theorem continuousOn_dil_path {S : Set ℝ} {k : ℝ → ℝ} (hk : Continuous k) {g : ℝ → L2Space}
    (hg : ContinuousOn g S) : ContinuousOn (fun s => dil (k s) (g s)) S := by
  intro s₀ hs₀
  have hstrong : Tendsto (fun s => dil (k s) (g s₀)) (𝓝[S] s₀) (𝓝 (dil (k s₀) (g s₀))) :=
    (((continuous_dil_apply (g s₀)).comp hk).tendsto s₀).mono_left nhdsWithin_le_nhds
  have hg0 : Tendsto (fun s => ‖g s - g s₀‖) (𝓝[S] s₀) (𝓝 0) := by
    have := ((hg s₀ hs₀).tendsto.sub_const (g s₀)).norm
    simpa using this
  have hexp : Continuous (fun s => Real.exp (-(k s / 4))) := by fun_prop
  have hbd : ∀ᶠ s in 𝓝[S] s₀, Real.exp (-(k s / 4)) < Real.exp (-(k s₀ / 4)) + 1 :=
    ((hexp.tendsto s₀).eventually (gt_mem_nhds (lt_add_one _))).filter_mono
      nhdsWithin_le_nhds
  have hsmall : Tendsto (fun s => dil (k s) (g s) - dil (k s) (g s₀)) (𝓝[S] s₀) (𝓝 0) := by
    have hlim : Tendsto (fun s => (Real.exp (-(k s₀ / 4)) + 1) * ‖g s - g s₀‖) (𝓝[S] s₀)
        (𝓝 0) := by
      simpa using hg0.const_mul (Real.exp (-(k s₀ / 4)) + 1)
    apply squeeze_zero_norm' _ hlim
    filter_upwards [hbd] with s hs
    rw [← map_sub]
    calc ‖dil (k s) (g s - g s₀)‖ ≤ Real.exp (-(k s / 4)) * ‖g s - g s₀‖ :=
          norm_dil_apply_le _ _
      _ ≤ (Real.exp (-(k s₀ / 4)) + 1) * ‖g s - g s₀‖ := by
          gcongr
  have := hsmall.add hstrong
  simp only [sub_add_cancel, zero_add] at this
  exact this

end UnforcedLeray.Blueprint.ModeId
