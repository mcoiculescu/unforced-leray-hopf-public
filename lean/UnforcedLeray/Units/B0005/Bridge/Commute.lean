import UnforcedLeray.Units.B0005.Bridge.Solenoidal

/-!
# B0005 bridge, part 6: `hΔf` and `𝒯₀f` of a solenoidal `f` are solenoidal

Blueprint unit B0005 (tex 141–142) defines `𝒱_q = {f ∈ 𝒴_{q,div} : hΔf, 𝒯₀f ∈ 𝒴_q}`;
`loc:eq:graph` (tex 173–179) and the interface `Blueprint.InPeriodicGraph` ask for
`hΔf, 𝒯₀f ∈ 𝒴_{q,div}`. The two agree because the divergence commutes with the operators:
`div Δ = Δ div` and `div 𝒯₀ = (𝒯₀ - ½) div`. On tests (transposes):

  `Δ(∇φ) = ∇(Δφ)`,   `𝒯₀ᵗ(∇φ) = ∇(𝒯₀ᵗφ - ½φ)`        (`lapT_gradT`, `driftT_gradT`),

derived from the vector identities `dy_lapT`, `dy_driftT` of `Lib/PhaseSpace/Leibniz.lean`
applied to `φ eⱼ`. Consequences: `IsPhaseSolenoidal.of_hasHLap`, `IsPhaseSolenoidal.of_hasT0`.

Status: proved. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0005

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace

/-- `c ↦ c eⱼ`, `ℂ → ℂ³`. -/
def embedJ (j : Fin 3) : ℂ →L[ℝ] CVec3 :=
  (ContinuousLinearMap.id ℝ ℂ).smulRight (EuclideanSpace.single j (1 : ℂ))

/-- The `i`-th coordinate `ℂ³ → ℂ`, real-linear. -/
def projC (i : Fin 3) : CVec3 →L[ℝ] ℂ :=
  (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ

@[simp] theorem projC_apply (i : Fin 3) (x : CVec3) : projC i x = x i := rfl

theorem projC_embedJ (i : Fin 3) (c : ℂ) : projC i (embedJ i c) = c := by
  simp [embedJ]

theorem projC_gradT (φ : ℝ × Space → ℂ) (p : ℝ × Space) (i : Fin 3) :
    projC i (gradT φ p) = dy i φ p := by
  simp [gradT]

section Smooth

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_dτ' {G : ℝ × Space → F} (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (dτ G) :=
  (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_radialT' {G : ℝ × Space → F} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (radialT G) :=
  ContDiff.sum fun k _ => ((contDiff_coord k).comp contDiff_snd).smul (contDiff_dy' hG k)

theorem contDiff_driftT' {G : ℝ × Space → F} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (driftT G) := by
  show ContDiff ℝ ∞ (fun p => -dτ G p + (1 / 2 : ℝ) • radialT G p + (3 / 2 : ℝ) • G p)
  exact ((contDiff_dτ' hG).neg.add ((contDiff_radialT' hG).const_smul _)).add (hG.const_smul _)

end Smooth

section Scalar

variable {φ : ℝ × Space → ℂ}

theorem diff_of_smooth {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : ℝ × Space → F} (hG : ContDiff ℝ ∞ G) : Differentiable ℝ G :=
  hG.differentiable (by simp)

theorem contDiff_embed (hφ : ContDiff ℝ ∞ φ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun p => embedJ i (φ p)) :=
  (embedJ i).contDiff.comp hφ

theorem proj_embed (i : Fin 3) : (fun p => projC i (embedJ i (φ p))) = φ := by
  funext p; exact projC_embedJ i (φ p)

/-- `∂ᵢ (𝒯₀ᵗφ) = 𝒯₀ᵗ(∂ᵢφ) + ½ ∂ᵢφ` for a scalar test. -/
theorem dy_driftT_scalar (hφ : ContDiff ℝ ∞ φ) (i : Fin 3) :
    dy i (driftT φ) = driftT (dy i φ) + (1 / 2 : ℝ) • dy i φ := by
  have hΦ := contDiff_embed hφ i
  have h := congrArg (fun H : ℝ × Space → CVec3 => fun p => projC i (H p)) (dy_driftT hΦ i)
  have hdr : Differentiable ℝ (driftT (fun p => embedJ i (φ p))) :=
    diff_of_smooth (contDiff_driftT' hΦ)
  have hdy : Differentiable ℝ (dy i (fun p => embedJ i (φ p))) :=
    diff_of_smooth (contDiff_dy' hΦ i)
  rw [← dy_clm (projC i) hdr, ← driftT_clm (projC i) (diff_of_smooth hΦ), proj_embed] at h
  rw [h]
  funext p
  simp only [Pi.add_apply, Pi.smul_apply, map_add, map_smul]
  have e1 : (fun p => projC i (driftT (dy i fun p => embedJ i (φ p)) p)) = driftT (dy i φ) := by
    rw [← driftT_clm (projC i) hdy, ← dy_clm (projC i) (diff_of_smooth hΦ), proj_embed]
  have e2 : projC i (dy i (fun p => embedJ i (φ p)) p) = dy i φ p := by
    have := congrFun (dy_clm (projC i) (diff_of_smooth hΦ) i) p
    rw [proj_embed] at this
    exact this.symm
  rw [show projC i (driftT (dy i fun p => embedJ i (φ p)) p) = driftT (dy i φ) p from
    congrFun e1 p, e2]

/-- `∂ᵢ (Δφ) = Δ(∂ᵢφ)` for a scalar test. -/
theorem dy_lapT_scalar (hφ : ContDiff ℝ ∞ φ) (i : Fin 3) :
    dy i (lapT φ) = lapT (dy i φ) := by
  have hΦ := contDiff_embed hφ i
  have h := congrArg (fun H : ℝ × Space → CVec3 => fun p => projC i (H p)) (dy_lapT hΦ i)
  rw [← dy_clm (projC i) (diff_of_smooth (contDiff_lapT hΦ)), ← lapT_clm (projC i) hΦ,
    proj_embed, ← lapT_clm (projC i) (contDiff_dy' hΦ i),
    ← dy_clm (projC i) (diff_of_smooth hΦ), proj_embed] at h
  exact h

theorem contDiff_gradT (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (gradT φ) :=
  ContDiff.sum fun j _ => (contDiff_dy' hφ j).smul contDiff_const

/-- `Δ(∇φ) = ∇(Δφ)`. -/
theorem lapT_gradT (hφ : ContDiff ℝ ∞ φ) : lapT (gradT φ) = gradT (lapT φ) := by
  funext p
  ext i
  have h1 := congrFun (lapT_clm (projC i) (contDiff_gradT hφ)) p
  simp only [projC_gradT] at h1
  rw [show (lapT (gradT φ) p) i = projC i (lapT (gradT φ) p) from rfl, ← h1,
    show (gradT (lapT φ) p) i = projC i (gradT (lapT φ) p) from rfl, projC_gradT,
    dy_lapT_scalar hφ i]

/-- `𝒯₀ᵗ(∇φ) = ∇(𝒯₀ᵗφ - ½φ)`. -/
theorem driftT_gradT (hφ : ContDiff ℝ ∞ φ) :
    driftT (gradT φ) = gradT (driftT φ - (1 / 2 : ℝ) • φ) := by
  have hdrift : ContDiff ℝ ∞ (driftT φ) := contDiff_driftT' hφ
  funext p
  ext i
  have h1 := congrFun (driftT_clm (projC i) (diff_of_smooth (contDiff_gradT hφ))) p
  simp only [projC_gradT] at h1
  rw [show (driftT (gradT φ) p) i = projC i (driftT (gradT φ) p) from rfl, ← h1,
    show (gradT (driftT φ - (1 / 2 : ℝ) • φ) p) i =
      projC i (gradT (driftT φ - (1 / 2 : ℝ) • φ) p) from rfl, projC_gradT]
  have hsub : dy i (driftT φ - (1 / 2 : ℝ) • φ) p = dy i (driftT φ) p - (1 / 2 : ℝ) • dy i φ p := by
    simp only [dy]
    rw [fderiv_sub (diff_of_smooth hdrift p) ((diff_of_smooth hφ p).const_smul _),
      fderiv_const_smul (diff_of_smooth hφ p)]
    rfl
  rw [hsub, dy_driftT_scalar hφ i]
  simp

end Scalar

section Graph

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- `div f = 0` and `Δf = a` give `div a = 0`. -/
theorem IsPhaseSolenoidal.of_hasPhaseOp_lapT {f a : Yq P q} (hf : IsPhaseSolenoidal f)
    (ha : HasPhaseOp lapT f a) : IsPhaseSolenoidal a := by
  intro φ hφ
  rw [← ha (gradT φ) hφ.gradT, lapT_gradT hφ.smooth]
  exact hf _ hφ.lapT

/-- `div f = 0` and `hΔf = a` give `div a = 0`. -/
theorem IsPhaseSolenoidal.of_hasHLap {h : ℝ} {f a : Yq P q} (hf : IsPhaseSolenoidal f)
    (ha : HasPhaseOp (nuLapT h) f a) : IsPhaseSolenoidal a := by
  intro φ hφ
  rw [← ha (gradT φ) hφ.gradT, nuLapT, lapT_gradT hφ.smooth,
    phasePair_real_smul hφ.lapT.gradT, hf _ hφ.lapT, mul_zero]

/-- `div f = 0` and `𝒯₀f = b` give `div b = 0`. -/
theorem IsPhaseSolenoidal.of_hasT0 {f b : Yq P q} (hf : IsPhaseSolenoidal f)
    (hb : HasPhaseOp driftT f b) : IsPhaseSolenoidal b := by
  intro φ hφ
  rw [← hb (gradT φ) hφ.gradT, driftT_gradT hφ.smooth]
  exact hf _ (hφ.driftT.sub (hφ.const_smul _))

end Graph

end UnforcedLeray.B0005
