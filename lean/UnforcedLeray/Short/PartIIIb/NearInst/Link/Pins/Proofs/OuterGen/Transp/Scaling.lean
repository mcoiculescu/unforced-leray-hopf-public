import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2_3_2

/-!
# Scaling identity for the transposed outer generator (task `PartIII-b:C/near/pins/3/4/2/3/2/5`)

Source `the November 2 reference manuscript`
lines 1339-1362 and 4139-4146. With `ψ(τ, x) = Φ(τ, x/ε)` and `h = νε²` the transposed outer
generator satisfies `Gᵗψ = (-L₀ᵗΦ)(τ, x/ε)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The linear map `(τ, y) ↦ (τ, c • y)`. -/
def outerScaleLin (c : ℝ) : ℝ × UnforcedLeray.Space →L[ℝ] ℝ × UnforcedLeray.Space :=
  (ContinuousLinearMap.fst ℝ ℝ UnforcedLeray.Space).prod
    (c • ContinuousLinearMap.snd ℝ ℝ UnforcedLeray.Space)

theorem outerScaleLin_apply (c : ℝ) (r : ℝ × UnforcedLeray.Space) :
    outerScaleLin c r = (r.1, c • r.2) := by
  simp [outerScaleLin]

theorem outerScaleLin_fun (c : ℝ) :
    (fun r : ℝ × UnforcedLeray.Space => (r.1, c • r.2)) = outerScaleLin c := by
  funext r
  simp [outerScaleLin_apply]

theorem outerDiff_scale {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : ℝ × UnforcedLeray.Space → F} (hG : Differentiable ℝ G) (c : ℝ) :
    Differentiable ℝ (fun r : ℝ × UnforcedLeray.Space => G (r.1, c • r.2)) := by
  have h : Differentiable ℝ (G ∘ outerScaleLin c) := hG.comp (outerScaleLin c).differentiable
  have hfun : (G ∘ outerScaleLin c) = fun r : ℝ × UnforcedLeray.Space => G (r.1, c • r.2) := by
    funext r
    simp [outerScaleLin_apply]
  rw [← hfun]
  exact h

theorem outerFderiv_scale {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : ℝ × UnforcedLeray.Space → F) (hG : Differentiable ℝ G) (c : ℝ)
    (q v : ℝ × UnforcedLeray.Space) :
    fderiv ℝ (fun r : ℝ × UnforcedLeray.Space => G (r.1, c • r.2)) q v
      = fderiv ℝ G (q.1, c • q.2) (v.1, c • v.2) := by
  have hL : HasFDerivAt (fun r : ℝ × UnforcedLeray.Space => (r.1, c • r.2))
      (outerScaleLin c) q := by
    rw [outerScaleLin_fun]
    exact (outerScaleLin c).hasFDerivAt
  have h2 := (hG (q.1, c • q.2)).hasFDerivAt.comp q hL
  have h3 : fderiv ℝ (fun r : ℝ × UnforcedLeray.Space => G (r.1, c • r.2)) q
      = (fderiv ℝ G (q.1, c • q.2)).comp (outerScaleLin c) := h2.fderiv
  rw [h3, ContinuousLinearMap.comp_apply, outerScaleLin_apply]

theorem outerDtau_scale {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : ℝ × UnforcedLeray.Space → F) (hG : Differentiable ℝ G) (c : ℝ) (q : ℝ × UnforcedLeray.Space) :
    dτ (fun r : ℝ × UnforcedLeray.Space => G (r.1, c • r.2)) q = dτ G (q.1, c • q.2) := by
  unfold dτ
  rw [outerFderiv_scale G hG c q (1, 0)]
  simp

theorem outerDy_scale {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : ℝ × UnforcedLeray.Space → F) (hG : Differentiable ℝ G) (c : ℝ) (j : Fin 3)
    (q : ℝ × UnforcedLeray.Space) :
    dy j (fun r : ℝ × UnforcedLeray.Space => G (r.1, c • r.2)) q
      = c • dy j G (q.1, c • q.2) := by
  unfold dy
  rw [outerFderiv_scale G hG c q (0, UnforcedLeray.coordinateVector j)]
  have h : ((0 : ℝ), c • UnforcedLeray.coordinateVector j)
      = c • ((0 : ℝ), UnforcedLeray.coordinateVector j) := by
    simp
  simp only [h, map_smul]

theorem outerDy_const_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : ℝ × UnforcedLeray.Space → F) (hK : Differentiable ℝ K) (c : ℝ) (j : Fin 3)
    (q : ℝ × UnforcedLeray.Space) :
    dy j (fun r => c • K r) q = c • dy j K q := by
  have e : (fun r : ℝ × UnforcedLeray.Space => c • K r) = c • K := rfl
  have hfd : fderiv ℝ (fun r : ℝ × UnforcedLeray.Space => c • K r) q
      = c • fderiv ℝ K q := by
    rw [e]
    exact fderiv_const_smul (hK q) c
  unfold dy
  rw [hfd, smul_apply]

theorem outerScaling : OuterScaling := by
  intro p Φ hΦ
  have hΦd : Differentiable ℝ Φ := hΦ.smooth.differentiable (by simp)
  have hdy : ∀ j : Fin 3, Differentiable ℝ (dy j Φ) := fun j =>
    (hΦ.dy j).smooth.differentiable (by simp)
  have hε : p.ε ≠ 0 := p.ε_pos.ne'
  have hdy1 : ∀ j : Fin 3,
      dy j (fun r : ℝ × UnforcedLeray.Space => Φ (r.1, p.ε⁻¹ • r.2))
        = fun r : ℝ × UnforcedLeray.Space => p.ε⁻¹ • dy j Φ (r.1, p.ε⁻¹ • r.2) := by
    intro j
    funext r
    exact outerDy_scale Φ hΦd p.ε⁻¹ j r
  have hyy : ∀ j : Fin 3,
      dy j (dy j (fun r : ℝ × UnforcedLeray.Space => Φ (r.1, p.ε⁻¹ • r.2)))
        = fun r : ℝ × UnforcedLeray.Space => p.ε⁻¹ • p.ε⁻¹ • dy j (dy j Φ) (r.1, p.ε⁻¹ • r.2) := by
    intro j
    rw [hdy1 j]
    funext r
    rw [outerDy_const_smul (fun r : ℝ × UnforcedLeray.Space => dy j Φ (r.1, p.ε⁻¹ • r.2))
      (outerDiff_scale (hdy j) p.ε⁻¹) p.ε⁻¹ j r]
    rw [outerDy_scale (dy j Φ) (hdy j) p.ε⁻¹ j r]
  have hlap : ∀ q : ℝ × UnforcedLeray.Space,
      lapT (fun r : ℝ × UnforcedLeray.Space => Φ (r.1, p.ε⁻¹ • r.2)) q
        = p.ε⁻¹ • p.ε⁻¹ • lapT Φ (q.1, p.ε⁻¹ • q.2) := by
    intro q
    simp only [lapT, hyy, Finset.smul_sum]
  have hrad : ∀ q : ℝ × UnforcedLeray.Space,
      radialT (fun r : ℝ × UnforcedLeray.Space => Φ (r.1, p.ε⁻¹ • r.2)) q
        = radialT Φ (q.1, p.ε⁻¹ • q.2) := by
    intro q
    simp only [radialT, hdy1]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [smul_smul]
    congr 1
    ring
  have hdτ : ∀ q : ℝ × UnforcedLeray.Space,
      dτ (fun r : ℝ × UnforcedLeray.Space => Φ (r.1, p.ε⁻¹ • r.2)) q
        = dτ Φ (q.1, p.ε⁻¹ • q.2) := fun q =>
    outerDtau_scale Φ hΦd p.ε⁻¹ q
  have hk : ∀ X : CVec3, (p.ν * p.ε ^ 2) • (p.ε⁻¹ • p.ε⁻¹ • X) = p.ν • X := by
    intro X
    rw [smul_smul, smul_smul]
    congr 1
    field_simp
  funext q
  show (p.ν * p.ε ^ 2) • lapT (fun r : ℝ × UnforcedLeray.Space => Φ (r.1, p.ε⁻¹ • r.2)) q
      - (1 / 2 : ℝ) • radialT (fun r : ℝ × UnforcedLeray.Space => Φ (r.1, p.ε⁻¹ • r.2)) q
      - Φ (q.1, p.ε⁻¹ • q.2)
      + dτ (fun r : ℝ × UnforcedLeray.Space => Φ (r.1, p.ε⁻¹ • r.2)) q
    = -(driftT Φ (q.1, p.ε⁻¹ • q.2) - p.ν • lapT Φ (q.1, p.ε⁻¹ • q.2)
        - (1 / 2 : ℝ) • Φ (q.1, p.ε⁻¹ • q.2))
  rw [hlap q, hrad q, hdτ q, hk]
  simp only [driftT]
  module

end UnforcedLeray.Short.PartIIIb.NearInst
