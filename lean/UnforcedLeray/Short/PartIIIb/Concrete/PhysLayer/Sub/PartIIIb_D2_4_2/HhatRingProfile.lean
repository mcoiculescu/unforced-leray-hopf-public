import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Defs

/-!
# Pointwise ring-chart identity (source 4993-4996, 5036-5039)

For `s > 0`, `s^{-1/2} ĥ_A = (h^p_{A,r}, h^p_{A,z} + ε(ψ - 𝒦ψ))` with `h^p = J∇ψ`, which is
the normalized ring profile `ringStreamProfile ε⁻¹ ψ` at `(s, (q, η))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Partial derivative of a joint function in its last two variables: the slice at fixed `s`. -/
theorem hrp_fderiv_slice_x (f : ℝ × (ℝ × ℝ) → ℝ) (s : ℝ) (x : ℝ × ℝ)
    (hf : DifferentiableAt ℝ f (s, x)) (v : ℝ × ℝ) :
    fderiv ℝ (fun y => f (s, y)) x v = fderiv ℝ f (s, x) (0, v) := by
  have hg : HasFDerivAt (fun y : ℝ × ℝ => ((s, y) : ℝ × (ℝ × ℝ)))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) x :=
    (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x)
  have h := hf.hasFDerivAt.comp x hg
  have h' : (fun y => f (s, y)) = f ∘ (fun y : ℝ × ℝ => ((s, y) : ℝ × (ℝ × ℝ))) := rfl
  rw [h', h.fderiv]
  simp

/-- Derivative in the first variable at fixed `x`: the slice at fixed `x`. -/
theorem hrp_deriv_slice_s (f : ℝ × (ℝ × ℝ) → ℝ) (s : ℝ) (x : ℝ × ℝ)
    (hf : DifferentiableAt ℝ f (s, x)) :
    deriv (fun s' => f (s', x)) s = fderiv ℝ f (s, x) (1, (0, 0)) := by
  have hg : HasDerivAt (fun s' : ℝ => ((s', x) : ℝ × (ℝ × ℝ))) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  have h := hf.hasFDerivAt.comp_hasDerivAt s hg
  exact h.deriv

/-- **Pointwise ring-chart identity** (source 4993-4996, 5036-5039). -/
theorem hhatRingProfile_proof (ν ε : ℝ) (χf : ℝ → ℝ) : HhatRingProfile ν ε χf := by
  intro A hJ p hp hd
  obtain ⟨hν, hpsi⟩ := hJ
  obtain ⟨s, x⟩ := p
  have hs0 : 0 < s := hp
  have hsq : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs0).ne'
  have hJx := hpsi s hs0 x
  set φ := psiRing ν χf A with hφdef
  have hval : psipA ν χf A s x = φ (s, x) := rfl
  have hA : fderiv ℝ (psipA ν χf A s) x (ei 0) = fderiv ℝ φ (s, x) (0, (1, 0)) :=
    hrp_fderiv_slice_x φ s x hd (ei 0)
  have hB : fderiv ℝ (psipA ν χf A s) x (ei 1) = fderiv ℝ φ (s, x) (0, (0, 1)) :=
    hrp_fderiv_slice_x φ s x hd (ei 1)
  have hC : deriv (fun s' => psipA ν χf A s' x) s = fderiv ℝ φ (s, x) (1, (0, 0)) :=
    hrp_deriv_slice_s φ s x hd
  unfold hhatChart
  unfold hhatA
  dsimp only
  rw [inv_smul_smul₀ hsq, hJx]
  unfold Kop
  unfold ringStreamProfile UnforcedLeray.Axi.dEta UnforcedLeray.Axi.dQ UnforcedLeray.Axi.dS
  simp only [mgrad, Jrot, inv_inv]
  rw [hval, hA, hB, hC]
  ext i
  fin_cases i
  · simp [merOf, emb, m0, m1]
  · simp [merOf, emb, m0, m1]
    left
    ring

end UnforcedLeray.Short.PartIIIb.Concrete
