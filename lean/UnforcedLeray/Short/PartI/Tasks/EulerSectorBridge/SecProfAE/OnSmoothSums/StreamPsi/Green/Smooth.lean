import UnforcedLeray.Short.PartI.Sub.PartI_S11_1_1_2

/-!
# Part I, task `PartI:S11/1/1/2/1`: `SecGreenSmooth`

For `n ≥ 1` and a smooth compactly supported profile `φ` in `(0,∞)`, the Green function
`ψ = greenN n φ` is smooth on `(0,∞)`.

Proof: `ψ` solves the integrated radial Poisson equation (`B0079.IsDeltaNSol`) with a derivative
`ψ'` that is continuous.  Pointwise, `ψ' = deriv ψ` on `(0,∞)` and
`ψ'' = φ - ψ'/r + n²ψ/r²` there (`B0079.IsDeltaNSol.deltaN_eq`).  An induction on the order
then gives `ψ, ψ' ∈ C^k` for every `k`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.Planar.NUE

theorem smoothCpt_contDiff_aux {φ : ℝ → ℂ} (h : SmoothCptFun φ) : ContDiff ℝ ∞ φ :=
  h.1

theorem smoothCpt_wprof_aux {φ : ℝ → ℂ} (h : SmoothCptFun φ) : UnforcedLeray.B0011.WProf φ := by
  obtain ⟨hc, hK, -⟩ := h
  have hcont : Continuous φ := hc.continuous
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  have hf : Continuous (fun ρ : ℝ => ρ * ‖φ ρ‖) := continuous_id.mul hcont.norm
  have hcs : HasCompactSupport (fun ρ : ℝ => ρ * ‖φ ρ‖) := hK.norm.mul_left
  exact (hf.integrable_of_hasCompactSupport hcs).restrict

theorem greenN_smooth_aux (n : ℕ) (hn : 1 ≤ n) (φ : ℝ → ℂ) (hφ : SmoothCptFun φ) :
    ContDiffOn ℝ ∞ (Planar.greenN n φ) (Ioi 0) := by
  have hφc : ContDiff ℝ ∞ φ := smoothCpt_contDiff_aux hφ
  have hφC : ContinuousOn φ (Ioi 0) := hφc.continuous.continuousOn
  have hsol : B0079.IsDeltaNSol n φ (Planar.greenN n φ) :=
    Planar.isRadialPoissonSol_greenN hn (smoothCpt_wprof_aux hφ)
  have hDN : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ (deriv (Planar.greenN n φ)) r ∧
      B0079.DeltaN n (Planar.greenN n φ) r = φ r := fun r hr =>
    ⟨(B0079.IsDeltaNSol.deltaN_eq hsol hφC hr).2.1, (B0079.IsDeltaNSol.deltaN_eq hsol hφC hr).2.2⟩
  obtain ⟨ψ', hd, hc, -⟩ := hsol
  set ψ := Planar.greenN n φ with hψdef
  have hdψ : ∀ r : ℝ, 0 < r → deriv ψ r = ψ' r := fun r hr => (hd r hr).deriv
  have hev : ∀ r : ℝ, 0 < r → deriv ψ =ᶠ[𝓝 r] ψ' := fun r hr => by
    filter_upwards [Ioi_mem_nhds hr] with s hs using hdψ s hs
  have hdiff' : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ ψ' r := fun r hr =>
    (hDN r hr).1.congr_of_eventuallyEq (hev r hr).symm
  have hF : ∀ r : ℝ, 0 < r → deriv ψ' r =
      φ r - ψ' r * (r : ℂ)⁻¹ + (n : ℂ) ^ 2 * ψ r * ((r : ℂ) ^ 2)⁻¹ := by
    intro r hr
    have h1 : deriv (deriv ψ) r = deriv ψ' r := (hev r hr).deriv_eq
    have h2 := (hDN r hr).2
    unfold B0079.DeltaN at h2
    rw [h1, hdψ r hr] at h2
    linear_combination h2
  have hψd : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ ψ r := fun r hr => (hd r hr).differentiableAt
  have key : ∀ k : ℕ, ContDiffOn ℝ k ψ (Ioi 0) ∧ ContDiffOn ℝ k ψ' (Ioi 0) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · exact contDiffOn_zero.2 fun r hr => (hψd r hr).continuousAt.continuousWithinAt
      · exact contDiffOn_zero.2 hc
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [Nat.cast_succ]
      have hφk : ContDiffOn ℝ k φ (Ioi 0) :=
        (contDiffOn_infty.1 hφc.contDiffOn k).mono (subset_univ _)
      have hrC : ContDiffOn ℝ k (fun r : ℝ => (r : ℂ)) (Ioi 0) :=
        (Complex.ofRealCLM.contDiff).contDiffOn
      have hr0 : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) ≠ 0 := fun r hr => by
        exact_mod_cast (ne_of_gt hr)
      have hinv1 : ContDiffOn ℝ k (fun r : ℝ => (r : ℂ)⁻¹) (Ioi 0) := hrC.inv hr0
      have hinv2 : ContDiffOn ℝ k (fun r : ℝ => ((r : ℂ) ^ 2)⁻¹) (Ioi 0) :=
        (hrC.pow 2).inv (fun r hr => pow_ne_zero 2 (hr0 r hr))
      have hFk : ContDiffOn ℝ k
          (fun r : ℝ => φ r - ψ' r * (r : ℂ)⁻¹ + (n : ℂ) ^ 2 * ψ r * ((r : ℂ) ^ 2)⁻¹)
          (Ioi 0) :=
        (hφk.sub (h2.mul hinv1)).add ((contDiffOn_const.mul h1).mul hinv2)
      have hdψ'k : ContDiffOn ℝ k (deriv ψ') (Ioi 0) :=
        hFk.congr fun r hr => hF r hr
      have hdψk : ContDiffOn ℝ k (deriv ψ) (Ioi 0) :=
        h2.congr fun r hr => hdψ r hr
      constructor
      · exact (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).2
          ⟨fun r hr => (hψd r hr).differentiableWithinAt, fun h => absurd h (by simp), hdψk⟩
      · exact (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).2
          ⟨fun r hr => (hdiff' r hr).differentiableWithinAt, fun h => absurd h (by simp), hdψ'k⟩
  exact contDiffOn_infty.2 fun k => (key k).1

/-- **Leaf `PartI:S11/1/1/2/1`** (lines 841-889 of the shorter proof): `greenN n φ` is smooth on
`(0,∞)` for `n ≥ 1` and `φ` smooth with compact support in `(0,∞)`. -/
theorem secGreenSmooth_proof : UnforcedLeray.Short.PartI.SecGreenSmooth := by
  intro n hn φ hφ
  exact greenN_smooth_aux n hn φ hφ

end UnforcedLeray.Short.PartI
