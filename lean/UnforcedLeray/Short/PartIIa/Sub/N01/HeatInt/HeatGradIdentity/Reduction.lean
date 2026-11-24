import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_6

/-!
# `PartII-a:N01/9/1/2/4/6` (heat integral): reduction of `HeatGradIdentity`

Source `the November 2 reference manuscript`
lines 1684-1689, 3379-3383.  The heat integral `smoothHeatInt` of a smooth force is differentiated
in `(q,η)` by the analytic core `HeatIntDiffCore` (differentiation under the `σ`-integral and the
Gaussian average).  This file proves the algebraic part: the coordinate-wise derivative of a
`MeridC`-valued map, the slice identity `periodize (σ⁻¹ F) = σ⁻¹ F` for `c`-periodic `F`, the
identification of the slice derivative with `derivForce`, and hence `HeatGradIdentity` from
`HeatIntDiffCore` and `DerivForceSmooth`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.B0223 (MeridC)

/-- The analytic core of `HeatGradIdentity`: `z ↦ smoothHeatInt c ν μ F (s,z)` is differentiable
and its derivative in direction `dir j` is the heat integral of the slice derivatives,
`∫₀^s (σ/s)^μ planeHeat(ν(s-σ)) (∂_{dir j} (periodized σ⁻¹F(σ,·))) dσ`.  (Dominated
differentiation under the `σ`-integral; `planeHeat` derivative `PlaneHeatFderiv`.) -/
def HeatIntDiffCore : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν → ∀ μ : ℂ, ∀ F : Profile → MeridC, IsSmoothForceFn c F →
    ∀ s : ℝ, 0 < s → ∀ (j : Fin 2) (z : ℝ × ℝ),
      DifferentiableAt ℝ (fun z' : ℝ × ℝ => smoothHeatInt c ν μ F (s, z')) z ∧
      fderiv ℝ (fun z' : ℝ × ℝ => smoothHeatInt c ν μ F (s, z')) z (UnforcedLeray.B0579.dir j)
        = ∫ σ in (0 : ℝ)..s, ((σ / s : ℝ) : ℂ) ^ μ •
            UnforcedLeray.B0224.planeHeat (ν * (s - σ))
              (fun w : ℝ × ℝ => fderiv ℝ (fun w' : ℝ × ℝ =>
                UnforcedLeray.B0220.periodize c (fun q : Profile => (q.1)⁻¹ • F q) (σ, w')) w
                  (UnforcedLeray.B0579.dir j)) z

/-- Coordinates commute with the derivative of a differentiable `MeridC`-valued map. -/
theorem fderiv_apply_coord (Φ : ℝ × ℝ → MeridC) (w : ℝ × ℝ) (hΦ : DifferentiableAt ℝ Φ w)
    (v : ℝ × ℝ) (i : Fin 2) :
    fderiv ℝ Φ w v i = fderiv ℝ (fun z : ℝ × ℝ => Φ z i) w v := by
  have hB := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (Φ w) i
  have h := hB.comp w hΦ.hasFDerivAt
  have h2 : fderiv ℝ (fun z : ℝ × ℝ => Φ z i) w
      = (PiLp.proj 2 (fun _ : Fin 2 => ℂ) i).comp (fderiv ℝ Φ w) := h.fderiv
  rw [h2]
  simp

/-- The periodized slice of a `c`-periodic force is `σ⁻¹` times the force. -/
theorem periodize_slice (c : ℝ) (F : Profile → MeridC)
    (hper : ∀ p : Profile, F (p.1, p.2.1 + c, p.2.2) = F p) (σ : ℝ) (w : ℝ × ℝ) :
    UnforcedLeray.B0220.periodize c (fun q : Profile => (q.1)⁻¹ • F q) (σ, w)
      = σ⁻¹ • F (σ, w) := by
  unfold UnforcedLeray.B0220.periodize
  dsimp only
  rw [UnforcedLeray.B0220.periodic_reduceIoc_eq F hper σ w.1 w.2]

/-- The heat integral of a `c`-periodic force, written with the slices `σ⁻¹ G(σ,·)`. -/
theorem smoothHeatInt_eq_slice (c ν : ℝ) (μ : ℂ) (G : Profile → MeridC)
    (hG : ∀ p : Profile, G (p.1, p.2.1 + c, p.2.2) = G p) (s : ℝ) (z : ℝ × ℝ) :
    smoothHeatInt c ν μ G (s, z) = ∫ σ in (0 : ℝ)..s, ((σ / s : ℝ) : ℂ) ^ μ •
      UnforcedLeray.B0224.planeHeat (ν * (s - σ)) (fun w : ℝ × ℝ => σ⁻¹ • G (σ, w)) z := by
  unfold smoothHeatInt
  apply intervalIntegral.integral_congr
  intro σ _
  dsimp only
  have hfun : (fun w : ℝ × ℝ => UnforcedLeray.B0220.periodize c
      (fun q : Profile => (q.1)⁻¹ • G q) (σ, w)) = fun w => σ⁻¹ • G (σ, w) :=
    funext fun w => periodize_slice c G hG σ w
  rw [hfun]

/-- The `j`-th cell derivative of a force is the `dir j`-derivative of the force slice. -/
theorem derivForce_eq_fderiv (F : Profile → MeridC) (hF : ContDiff ℝ ∞ F) (j : Fin 2)
    (σ : ℝ) (w : ℝ × ℝ) :
    derivForce j F (σ, w) = fderiv ℝ (fun z : ℝ × ℝ => F (σ, z)) w (UnforcedLeray.B0579.dir j) := by
  have hdiff2 : Differentiable ℝ (fun z : ℝ × ℝ => ((σ, z) : ℝ × (ℝ × ℝ))) :=
    (differentiable_const σ).prodMk differentiable_id
  have hd : Differentiable ℝ (fun z : ℝ × ℝ => F (σ, z)) :=
    (hF.differentiable (by simp)).comp hdiff2
  ext i
  rw [fderiv_apply_coord _ w (hd w)]
  simp [derivForce]

/-- **Reduction of `HeatGradIdentity`** to the analytic core `HeatIntDiffCore`, given the smoothness
of the cell derivative `DerivForceSmooth`. -/
theorem heatGradIdentity_of (hD1 : DerivForceSmooth) (hCore : HeatIntDiffCore) :
    HeatGradIdentity := by
  intro c ν hc hν μ F hF s hs i j y
  have hFc : ContDiff ℝ ∞ F := hF.1
  have hDF : IsSmoothForceFn c (derivForce j F) := hD1 c F hF j
  obtain ⟨hdiff, hfd⟩ := hCore c ν hc hν μ F hF s hs j y
  refine Eq.trans (fderiv_apply_coord _ y hdiff (UnforcedLeray.B0579.dir j) i).symm ?_
  rw [hfd, smoothHeatInt_eq_slice c ν μ (derivForce j F) hDF.2.1 s y]
  refine congrArg (fun v : MeridC => v i) ?_
  refine intervalIntegral.integral_congr (fun σ _ => ?_)
  show _ = _
  have hslice : (fun w' : ℝ × ℝ => UnforcedLeray.B0220.periodize c
      (fun q : Profile => (q.1)⁻¹ • F q) (σ, w')) = fun w' => σ⁻¹ • F (σ, w') :=
    funext fun w' => periodize_slice c F hF.2.1 σ w'
  have hfun : (fun w : ℝ × ℝ => fderiv ℝ (fun w' : ℝ × ℝ => UnforcedLeray.B0220.periodize c
      (fun q : Profile => (q.1)⁻¹ • F q) (σ, w')) w (UnforcedLeray.B0579.dir j))
      = fun w => σ⁻¹ • derivForce j F (σ, w) := by
    funext w
    have hdFw : DifferentiableAt ℝ (fun z : ℝ × ℝ => F (σ, z)) w := by
      have hdiff2 : Differentiable ℝ (fun z : ℝ × ℝ => ((σ, z) : ℝ × (ℝ × ℝ))) :=
        (differentiable_const σ).prodMk differentiable_id
      exact ((hFc.differentiable (by simp)).comp hdiff2) w
    have hsm : fderiv ℝ (fun w' : ℝ × ℝ => σ⁻¹ • F (σ, w')) w
        = σ⁻¹ • fderiv ℝ (fun z : ℝ × ℝ => F (σ, z)) w :=
      fderiv_const_smul hdFw σ⁻¹
    rw [hslice, hsm, smul_apply, derivForce_eq_fderiv F hFc j σ w]
  rw [hfun]

end UnforcedLeray.Short.PartIIa.N01
