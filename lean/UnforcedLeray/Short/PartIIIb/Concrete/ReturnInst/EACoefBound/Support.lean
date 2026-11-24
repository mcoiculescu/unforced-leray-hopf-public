import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_10

/-!
# `PartIII-b:C/inst/10/1`: support of `E_A` for `s > 1.1/ν`

Source `the November 2 reference manuscript` 4953-4963 (cutoff `χ_f(s) = χ̂_f(νs)`
vanishes for `νs ≥ 1.1`) and 5063-5079. On `s > 1.1/ν` the cutoff vanishes on a neighbourhood,
so `A^y = χ_f A ≡ 0` there, `B = 0`, `A^y(s) = 0`, and `e_A = 0`, hence `E_A = 0` and its
coefficient is `0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem eac_bmat_zero (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν μ : ℝ) (hν : 0 < ν)
    (A : ℝ → Mat3) (s : ℝ) (hs : (11 / 10) / ν < s) :
    Bmat ν μ χf A s = 0 ∧ Ay ν χf A s = 0 := by
  have hcut : ∀ t : ℝ, (11 / 10) / ν < t → χf (ν * t) = 0 := by
    intro t ht
    apply hχ.zero
    rw [div_lt_iff₀ hν] at ht
    nlinarith
  have hev : Ay ν χf A =ᶠ[𝓝 s] (fun _ => (0 : Mat3)) := by
    have hopen : ∀ᶠ t in 𝓝 s, (11 / 10) / ν < t := Ioi_mem_nhds hs
    filter_upwards [hopen] with t ht
    unfold Ay
    rw [hcut t ht, zero_smul]
  have hd : deriv (Ay ν χf A) s = 0 := by
    rw [hev.deriv_eq]
    exact deriv_const _ _
  have hA0 : Ay ν χf A s = 0 := by
    unfold Ay
    rw [hcut s hs, zero_smul]
  refine ⟨?_, hA0⟩
  unfold Bmat
  rw [hd, hA0, smul_zero, add_zero]

theorem eac_eA_zero_of (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ)
    (hB : Bmat ν μ χ A s = 0) (hC : Ay ν χ A s = 0) : eA ν μ χ A s x = 0 := by
  have he : emb 0 = 0 := by
    funext i
    fin_cases i <;> simp [emb]
  have hh : ∀ V : ℝ × ℝ → ℝ × ℝ, hessContr (0 : Mat3) V x = 0 := by
    intro V
    unfold hessContr
    simp [he]
  have hm0 : ∀ v : Vec3, mv (0 : Mat3) v = 0 := fun v => by
    funext i
    simp [mv]
  have hm1 : ∀ v : Vec3, mv (fun _ _ => (0 : ℝ)) v = 0 := fun v => by
    funext i
    simp [mv]
  unfold eA
  rw [hB, hC]
  simp [hm0, hm1, hh]

theorem eaCSupport (χf : ℝ → ℝ) : EAcSupport χf := by
  unfold EAcSupport
  intro hχ ν μ hν A s hs x
  obtain ⟨hB, hC⟩ := eac_bmat_zero χf hχ ν μ hν A s hs
  have he := eac_eA_zero_of ν μ χf A s x hB hC
  have hm0 : merOf (0 : Vec3) = 0 := by
    ext i
    fin_cases i <;> simp [merOf]
  unfold EAcoef EA
  rw [he]
  simp only [smul_zero]
  exact hm0

end UnforcedLeray.Short.PartIIIb.Concrete
