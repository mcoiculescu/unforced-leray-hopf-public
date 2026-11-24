import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9

/-!
# `PartIII-b:C/inst/9/1`: support of `F_A` for `s > 1.1/ν`

Source `the November 2 reference manuscript` 4953-4955 (cutoff `χ_f(s) = χ̂_f(νs)`
vanishes for `νs ≥ 1.1`) and 5063-5079. On `s > 1.1/ν` the cutoff vanishes on a neighbourhood,
so `A^y = χ_f A ≡ 0` there, `B = 0`, and `f_A = 0`, hence `F_A = 0` and its coefficient is `0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem fac_bmat_zero (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν μ : ℝ) (hν : 0 < ν)
    (A : ℝ → Mat3) (s : ℝ) (hs : (11 / 10) / ν < s) :
    Bmat ν μ χf A s = 0 := by
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
  unfold Bmat
  rw [hd, hA0, smul_zero, add_zero]

theorem fac_fA_zero_of_bmat (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ)
    (h : Bmat ν μ χ A s = 0) : fA ν μ χ A s x = 0 := by
  have hm : ∀ y : ℝ × ℝ, merApply (0 : Mat3) y = 0 := by
    intro y
    ext <;> simp [merApply]
  have he : emb 0 = 0 := by
    funext i
    fin_cases i <;> simp [emb]
  have hv : ∀ v : Vec3, mv 0 v = 0 := by
    intro v
    funext i
    simp [mv]
  unfold fA
  rw [h]
  simp only [hm, map_zero, he, hv, zero_add, tsum_zero, neg_zero]

theorem fAcSupport (χf : ℝ → ℝ) : FAcSupport χf := by
  unfold FAcSupport
  intro hχ ν μ hν A s hs x
  have hB := fac_bmat_zero χf hχ ν μ hν A s hs
  have hf := fac_fA_zero_of_bmat ν μ χf A s x hB
  have hm0 : merOf (0 : Vec3) = 0 := by
    ext i
    fin_cases i <;> simp [merOf]
  unfold FAcoef FA
  rw [hf]
  simp only [smul_zero]
  exact hm0

end UnforcedLeray.Short.PartIIIb.Concrete
