import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineFields
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.PsipADiff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.HpPsiLinear

/-!
# `PartIII-b:C/inst/8`: linearity of `b = s^{-1/2} ĥ_A` in `A` (source 4973-4985)

`ĥ_A = √s [(h^p_A)_r e_r + ((h^p_A)_z + ε(1 - 𝒦)ψ^p_A) e_z]` (source 4980), and `𝒦` is linear
in `ψ` (it is a sum of a derivative in `η` and of `2s ∂_s`).  Linearity of `h^p_A, ψ^p_A` in `A`
at `s > 0` is `hpPsiLinear`; the differentiability needed to split the derivatives is
`psipADiff`.  Source lines 4973-4980 and 4985.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Pointwise additivity of `h^p_A, ψ^p_A` at `s > 0` (from `hpPsiLinear`). -/
theorem hpPsi_split_add (ν : ℝ) (χ : ℝ → ℝ) (A A' : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ)
    (hν : 0 < ν) (hs : 0 < s) :
    hpA ν χ (A + A') s x = hpA ν χ A s x + hpA ν χ A' s x ∧
      psipA ν χ (A + A') s x = psipA ν χ A s x + psipA ν χ A' s x := by
  obtain ⟨h1, h3⟩ := hpPsiTermSummable ν χ A s x hν hs
  obtain ⟨h2, h4⟩ := hpPsiTermSummable ν χ A' s x hν hs
  obtain ⟨⟨a, _⟩, ⟨b, _⟩⟩ := hpPsiLinear ν χ A A' 0 s x h1 h2 h3 h4
  exact ⟨a, b⟩

/-- Pointwise homogeneity of `h^p_A, ψ^p_A` at `s > 0` (from `hpPsiLinear`). -/
theorem hpPsi_split_smul (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (r s : ℝ) (x : ℝ × ℝ)
    (hν : 0 < ν) (hs : 0 < s) :
    hpA ν χ (r • A) s x = r • hpA ν χ A s x ∧
      psipA ν χ (r • A) s x = r • psipA ν χ A s x := by
  obtain ⟨h1, h3⟩ := hpPsiTermSummable ν χ A s x hν hs
  obtain ⟨⟨_, a⟩, ⟨_, b⟩⟩ := hpPsiLinear ν χ A A r s x h1 h1 h3 h3
  exact ⟨a, b⟩

/-- `Kop` is additive in `ψ`, given the splitting on `s' > 0` and the differentiability at `s`. -/
theorem kop_add_gen (ψ ψ1 ψ2 : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ) (hs : 0 < s)
    (hf : ∀ s' : ℝ, 0 < s' → ∀ y : ℝ × ℝ, ψ s' y = ψ1 s' y + ψ2 s' y)
    (h1 : DifferentiableAt ℝ (ψ1 s) x) (h2 : DifferentiableAt ℝ (ψ2 s) x)
    (h1' : DifferentiableAt ℝ (fun s' => ψ1 s' x) s)
    (h2' : DifferentiableAt ℝ (fun s' => ψ2 s' x) s) :
    Kop ψ s x = Kop ψ1 s x + Kop ψ2 s x := by
  have hS : ψ s = fun y => ψ1 s y + ψ2 s y := funext fun y => hf s hs y
  have hT : (fun s' => ψ s' x) =ᶠ[𝓝 s] fun s' => ψ1 s' x + ψ2 s' x :=
    Filter.eventually_of_mem (Ioi_mem_nhds hs) fun s' hs' => hf s' (Set.mem_Ioi.mp hs') x
  have hF : fderiv ℝ (fun y => ψ1 s y + ψ2 s y) x = fderiv ℝ (ψ1 s) x + fderiv ℝ (ψ2 s) x :=
    fderiv_add h1 h2
  have hG : deriv (fun s' => ψ1 s' x + ψ2 s' x) s = deriv (fun s' => ψ1 s' x) s + deriv (fun s' => ψ2 s' x) s :=
    deriv_add h1' h2'
  unfold Kop
  rw [hS, hT.deriv_eq, hF, hG]
  simp only [add_apply]
  ring

/-- `Kop` is homogeneous in `ψ`. -/
theorem kop_smul_gen (ψ ψ1 : ℝ → ℝ × ℝ → ℝ) (r s : ℝ) (x : ℝ × ℝ) (hs : 0 < s)
    (hf : ∀ s' : ℝ, 0 < s' → ∀ y : ℝ × ℝ, ψ s' y = r * ψ1 s' y)
    (h1 : DifferentiableAt ℝ (ψ1 s) x) :
    Kop ψ s x = r * Kop ψ1 s x := by
  have hS : ψ s = fun y => r * ψ1 s y := funext fun y => hf s hs y
  have hT : (fun s' => ψ s' x) =ᶠ[𝓝 s] fun s' => r * ψ1 s' x :=
    Filter.eventually_of_mem (Ioi_mem_nhds hs) fun s' hs' => hf s' (Set.mem_Ioi.mp hs') x
  unfold Kop
  rw [hS, hT.deriv_eq, fderiv_const_mul h1 r, deriv_const_mul_field]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- `ĥ_A` is additive in `A` at `s > 0`. -/
theorem hhatA_add_pt (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν ε : ℝ) (hν : 0 < ν)
    (A A' : ℝ → Mat3) (hA : IsAffElem as A) (hA' : IsAffElem as A')
    (s : ℝ) (x : ℝ × ℝ) (hs : 0 < s) :
    hhatA ν ε χf (A + A') s x = hhatA ν ε χf A s x + hhatA ν ε χf A' s x := by
  have hD := psipADiff as χf hχ
  obtain ⟨hp, hψ⟩ := hpPsi_split_add ν χf A A' s x hν hs
  have hK := kop_add_gen (fun s' y => psipA ν χf (A + A') s' y)
    (fun s' y => psipA ν χf A s' y) (fun s' y => psipA ν χf A' s' y) s x hs
    (fun s' hs' y => (hpPsi_split_add ν χf A A' s' y hν hs').2)
    (hD ν hν A hA s hs x).1 (hD ν hν A' hA' s hs x).1
    (hD ν hν A hA s hs x).2 (hD ν hν A' hA' s hs x).2
  unfold hhatA
  rw [hp, hψ, hK, ← smul_add]
  congr 1
  ext i
  fin_cases i <;> (simp [emb]; try ring)

/-- `ĥ_A` is homogeneous in `A` at `s > 0`. -/
theorem hhatA_smul_pt (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν ε : ℝ) (hν : 0 < ν)
    (A : ℝ → Mat3) (hA : IsAffElem as A) (r : ℝ)
    (s : ℝ) (x : ℝ × ℝ) (hs : 0 < s) :
    hhatA ν ε χf (r • A) s x = r • hhatA ν ε χf A s x := by
  have hD := psipADiff as χf hχ
  obtain ⟨hp, hψ⟩ := hpPsi_split_smul ν χf A r s x hν hs
  have hK := kop_smul_gen (fun s' y => psipA ν χf (r • A) s' y)
    (fun s' y => psipA ν χf A s' y) r s x hs
    (fun s' hs' y => by
      simpa [smul_eq_mul] using (hpPsi_split_smul ν χf A r s' y hν hs').2)
    (hD ν hν A hA s hs x).1
  unfold hhatA
  rw [hp, hψ, hK]
  ext i
  fin_cases i <;> simp [emb, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-- Additivity of the coefficient `b = s^{-1/2} ĥ_A` at a chart point (source 4980, 4985). -/
theorem hhatCoef_add_pt (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν ε : ℝ) (hν : 0 < ν)
    (A A' : ℝ → Mat3) (hA : IsAffElem as A) (hA' : IsAffElem as A')
    (p : Chart) (hp : 0 < p.1) :
    hAcoef ν ε χf (A + A') p = hAcoef ν ε χf A p + hAcoef ν ε χf A' p := by
  unfold hAcoef
  rw [hhatA_add_pt as χf hχ ν ε hν A A' hA hA' p.1 p.2 hp, smul_add, affMerOf_add]

/-- Homogeneity of the coefficient `b = s^{-1/2} ĥ_A` at a chart point (source 4985). -/
theorem hhatCoef_smul_pt (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν ε : ℝ) (hν : 0 < ν)
    (A : ℝ → Mat3) (hA : IsAffElem as A) (r : ℝ) (p : Chart) (hp : 0 < p.1) :
    hAcoef ν ε χf (r • A) p = r • hAcoef ν ε χf A p := by
  unfold hAcoef
  rw [hhatA_smul_pt as χf hχ ν ε hν A hA r p.1 p.2 hp]
  have key : ∀ v : Vec3, (Real.sqrt p.1)⁻¹ • (r • v) = r • ((Real.sqrt p.1)⁻¹ • v) := by
    intro v
    module
  rw [key, affMerOf_smul]

theorem hhatCoefLinear (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) : HhatCoefLinear as χf := by
  intro ν ε hν A A' r hA hA' p hp
  exact ⟨hhatCoef_add_pt as χf hχ ν ε hν A A' hA hA' p hp,
    hhatCoef_smul_pt as χf hχ ν ε hν A hA r p hp⟩

end UnforcedLeray.Short.PartIIIb.Concrete
