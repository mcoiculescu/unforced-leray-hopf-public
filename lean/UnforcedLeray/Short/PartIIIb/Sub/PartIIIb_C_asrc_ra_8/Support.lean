import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8

/-!
# `PartIII-b:C/asrc/ra/8/4` : `RPerSupport`

For `s > (11/10)/ν` the source cutoff `χ_f(ν s') = 0` on a neighbourhood of `s`, so `A^y = 0`
there, hence `h^p_A`, `f_A`, `e_A`, `Ψ_A`, `Bmat` vanish and `r_per = 0` (source 4953-4958).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem merApply_zero_mat (v : ℝ × ℝ) : merApply (0 : Mat3) v = 0 := by
  ext <;> simp [merApply]

theorem mv_zero_mat (v : Vec3) : mv (0 : Mat3) v = 0 := by
  ext i; simp [mv]

theorem emb_zero_pair : emb (0 : ℝ × ℝ) = 0 := by
  ext i; fin_cases i <;> simp [emb]

theorem mv_zero_lam (v : Vec3) : mv (fun _ _ => (0 : ℝ)) v = 0 := mv_zero_mat v

theorem hessContr_zero_mat (V : ℝ × ℝ → ℝ × ℝ) (x : ℝ × ℝ) : hessContr (0 : Mat3) V x = 0 := by
  simp [hessContr, emb_zero_pair]

theorem rPerSupport (as : ℝ) (χf : ℝ → ℝ) : RPerSupport as χf := by
  intro hχ p d dm dp _hreg μ A _hA s hs x
  have hνp : 0 < p.ν := p.ν_pos
  -- A^y vanishes on the open set s' > (11/10)/ν
  have key : ∀ s', (11 / 10 : ℝ) / p.ν < s' → Ay p.ν χf A s' = 0 := by
    intro s' hs'
    have h2 : (11 / 10 : ℝ) ≤ p.ν * s' := by
      have := (div_lt_iff₀ hνp).1 hs'
      linarith [mul_comm s' p.ν]
    funext i j
    simp only [Ay, hχ.zero _ h2, zero_smul, Pi.zero_apply]
  have hAyfun : Ay p.ν χf A s = 0 := key s hs
  have hE : Ay p.ν χf A =ᶠ[nhds s] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds hs] with s' hs'
    exact key s' hs'
  have hBy : deriv (Ay p.ν χf A) s = 0 := by
    rw [hE.deriv_eq]; simp
  have hB : Bmat p.ν μ χf A s = 0 := by
    simp [Bmat, hBy, hAyfun]
  have hpAx : ∀ᶠ s' in nhds s, hpA p.ν χf A s' x = 0 := by
    filter_upwards [Ioi_mem_nhds hs] with s' hs'
    simp [hpA, key s' hs', merApply_zero_mat]
  have hd : deriv (fun s' => hpA p.ν χf A s' x) s = 0 := by
    have hE2 : (fun s' => hpA p.ν χf A s' x) =ᶠ[nhds s] fun _ => 0 := hpAx
    rw [hE2.deriv_eq]; simp
  have hH : hpA p.ν χf A s = fun _ => 0 := by
    funext y; simp [hpA, hAyfun, merApply_zero_mat]
  have hPsi : PsiA p.ν χf A s = fun _ => 0 := by
    funext y; simp [PsiA, hAyfun, merApply_zero_mat]
  have hf : fA p.ν μ χf A s x = 0 := by
    simp [fA, hB, merApply_zero_mat, mv_zero_mat, emb_zero_pair]
  have he : eA p.ν μ χf A s x = 0 := by
    simp [eA, hB, hAyfun, mv_zero_mat, mv_zero_lam, hessContr_zero_mat]
  simp [rPer, merPl, hd, hH, hPsi, hf, he, lapPl, mgrad]

end UnforcedLeray.Short.PartIIIb.Concrete
