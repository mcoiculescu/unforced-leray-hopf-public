import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5

/-!
# Leaf `DilLap`: the Laplacian commutes with the potential dilation

Source: `the November 2 reference manuscript` lines 1351-1362, 1470-1480.
Proves `dilLap : DilLap`. With `c = s⁻¹` and `L(τ,y) = (τ, c • y)`, the field
`liftS (dilU u₀ s)` equals `c · (liftS u₀ ∘ L)`. Each `∂ⱼ` contributes a factor `c` by the chain
rule, so `Δ_y (liftS (dilU u₀ s)) = c³ · (Δ_y (liftS u₀) ∘ L)`, which is `dilK b₀ s` on the
hypothesis `Δ u₀ = b₀`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Chain rule for `∂ⱼ` along the scaling `(τ,y) ↦ (τ, c • y)`. -/
theorem dilLap_dy_scale (c : ℝ) (j : Fin 3) {G : ℝ × Space → ℂ} (hG : Differentiable ℝ G)
    (k : ℂ) :
    UnforcedLeray.PhaseSpace.dy j (fun q => k * G (q.1, c • q.2)) =
      fun p => (k * (c : ℂ)) * UnforcedLeray.PhaseSpace.dy j G (p.1, c • p.2) := by
  funext p
  let L : ℝ × Space →L[ℝ] ℝ × Space :=
    ContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ ℝ) (c • ContinuousLinearMap.id ℝ Space)
  have hL : ∀ q : ℝ × Space, L q = (q.1, c • q.2) := fun q => rfl
  have hcomp : HasFDerivAt (fun q => k * G (L q)) (k • (fderiv ℝ G (L p)).comp L) p :=
    ((hG (L p)).hasFDerivAt.comp p L.hasFDerivAt).const_mul k
  have hfun : (fun q : ℝ × Space => k * G (q.1, c • q.2)) = fun q => k * G (L q) := by
    funext q
    rw [hL]
  have hv : ∀ v : Space, ((0 : ℝ), c • v) = c • ((0 : ℝ), v) := fun v => by simp
  unfold UnforcedLeray.PhaseSpace.dy
  rw [hfun, hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, hL, smul_eq_mul]
  rw [hv, map_smul, Complex.real_smul]
  ring

/-- `∂ⱼ G` is differentiable for smooth `G`. -/
theorem dilLap_dy_diff {G : ℝ × Space → ℂ} (hG : ContDiff ℝ ∞ G) (j : Fin 3) :
    Differentiable ℝ (UnforcedLeray.PhaseSpace.dy j G) := by
  have hd : Differentiable ℝ (fderiv ℝ G) :=
    (hG.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  intro p
  unfold UnforcedLeray.PhaseSpace.dy
  exact (hd p).clm_apply (differentiableAt_const _)

/-- Laplacian of a dilated field along `(τ,y) ↦ (τ, c • y)`. -/
theorem dilLap_lapT_scale (c : ℝ) {G : ℝ × Space → ℂ} (hG : ContDiff ℝ ∞ G) (k : ℂ)
    (p : ℝ × Space) :
    UnforcedLeray.PhaseSpace.lapT (fun q => k * G (q.1, c • q.2)) p =
      (k * (c : ℂ) * (c : ℂ)) * UnforcedLeray.PhaseSpace.lapT G (p.1, c • p.2) := by
  have h1 : ∀ j : Fin 3, UnforcedLeray.PhaseSpace.dy j (fun q => k * G (q.1, c • q.2)) =
      fun p => (k * (c : ℂ)) * UnforcedLeray.PhaseSpace.dy j G (p.1, c • p.2) :=
    fun j => dilLap_dy_scale c j (hG.differentiable (by simp)) k
  have h2 : ∀ j : Fin 3,
      UnforcedLeray.PhaseSpace.dy j (UnforcedLeray.PhaseSpace.dy j (fun q => k * G (q.1, c • q.2))) =
        fun p => ((k * (c : ℂ)) * (c : ℂ)) *
          UnforcedLeray.PhaseSpace.dy j (UnforcedLeray.PhaseSpace.dy j G) (p.1, c • p.2) := by
    intro j
    rw [h1 j]
    exact dilLap_dy_scale c j (dilLap_dy_diff hG j) (k * (c : ℂ))
  unfold UnforcedLeray.PhaseSpace.lapT
  simp only [h2, Finset.mul_sum]

theorem dilLap : DilLap := by
  intro u₀ b₀ s hu hs hb x
  have hG : ContDiff ℝ ∞ (liftS u₀) :=
    Complex.ofRealCLM.contDiff.comp (hu.1.comp contDiff_snd)
  have hΦ : liftS (dilU u₀ s) =
      fun q : ℝ × Space => (((s⁻¹ : ℝ) : ℂ)) * liftS u₀ (q.1, s⁻¹ • q.2) := by
    funext q
    simp [liftS, dilU, Complex.ofReal_mul]
  rw [hΦ, dilLap_lapT_scale s⁻¹ hG _ x, hb]
  simp only [dilK]
  push_cast
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
