import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4.Defs

/-!
# `PartIII-b:C/asrc/ra/9/4/org/3` : the pointwise norm identity for `gradRem`

Source of record: `the November 2 reference manuscript`, lines 5039-5043.
With `F = sΨ_A`, the product rule gives `dS F = Ψ + s ∂_sΨ` and `dEta F = s ∂_ηΨ` on `s > 0`, so
`2s dS F + η dEta F = s (𝒦Ψ + 2Ψ)` with `𝒦Ψ = η∂_ηΨ + 2s∂_sΨ = Kop Ψ`, and
`‖gradRem‖ = ε s |𝒦Ψ + 2Ψ|`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gradRemNorm (as : ℝ) (χf : ℝ → ℝ) : GradRemNorm as χf := by
  intro h hχ p μ A hA q hq
  have hν : 0 < p.ν := p.ν_pos
  have hε : 0 < p.ε := p.ε_pos
  obtain ⟨P, hPdef⟩ : ∃ P : Chart → ℝ, P = fun z => PsiA p.ν χf A z.1 z.2 := ⟨_, rfl⟩
  have hPq : ∀ z : Chart, P z = PsiA p.ν χf A z.1 z.2 := fun z => by rw [hPdef]
  have hFeq : sPsiChart p χf A = fun z => z.1 * P z := by
    funext z
    simp only [sPsiChart, hPq]
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hmem : q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hq, mem_univ _⟩
  have hF : ContDiffOn ℝ 1 (sPsiChart p χf A) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    h hχ p.ν hν A hA
  have hFd : DifferentiableAt ℝ (sPsiChart p χf A) q :=
    (hF.differentiableOn one_ne_zero).differentiableAt (hopen.mem_nhds hmem)
  have hPd : DifferentiableAt ℝ P q := by
    have hdiv : DifferentiableAt ℝ (fun z : Chart => sPsiChart p χf A z * (z.1)⁻¹) q :=
      hFd.mul (differentiableAt_fst.inv hq.ne')
    refine hdiv.congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have hz1 : z.1 ≠ 0 := (show (0 : ℝ) < z.1 from hz.1).ne'
    rw [hPq z]
    simp only [sPsiChart]
    rw [mul_comm (z.1), mul_assoc, mul_inv_cancel₀ hz1, mul_one]
  have hFP : HasFDerivAt (sPsiChart p χf A)
      (q.1 • fderiv ℝ P q + P q • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) q := by
    rw [hFeq]
    exact hasFDerivAt_fst.mul hPd.hasFDerivAt
  have hFdv : ∀ v : Chart, fderiv ℝ (sPsiChart p χf A) q v =
      q.1 * fderiv ℝ P q v + P q * v.1 := by
    intro v
    rw [hFP.fderiv]
    simp
  have hline : HasDerivAt (fun t : ℝ => ((t, q.2) : Chart)) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) q.1 :=
    (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
  have hds : deriv (fun s' => PsiA p.ν χf A s' q.2) q.1 =
      fderiv ℝ P q (1, ((0 : ℝ), (0 : ℝ))) := by
    have hc := hPd.hasFDerivAt.comp_hasDerivAt q.1 hline
    have hfun : (P ∘ fun t : ℝ => ((t, q.2) : Chart)) = fun s' => PsiA p.ν χf A s' q.2 :=
      funext fun t => hPq _
    rw [hfun] at hc
    exact hc.deriv
  have hyl : HasFDerivAt (fun y : ℝ × ℝ => ((q.1, y) : Chart))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) q.2 :=
    (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
  have hde : ∀ v : ℝ × ℝ, fderiv ℝ P q (0, v) =
      fderiv ℝ (fun y => PsiA p.ν χf A q.1 y) q.2 v := by
    intro v
    have hc := hPd.hasFDerivAt.comp q.2 hyl
    have hfun : (P ∘ fun y : ℝ × ℝ => ((q.1, y) : Chart)) = fun y => PsiA p.ν χf A q.1 y :=
      funext fun y => hPq _
    rw [hfun] at hc
    rw [hc.fderiv]
    simp
  have hei : ei 1 = ((0 : ℝ), (1 : ℝ)) := by
    simp [ei]
  have hKop : Kop (fun s' y => PsiA p.ν χf A s' y) q.1 q.2 =
      q.2.2 * fderiv ℝ P q (0, ((0 : ℝ), (1 : ℝ))) +
        2 * q.1 * fderiv ℝ P q (1, ((0 : ℝ), (0 : ℝ))) := by
    show q.2.2 * fderiv ℝ (fun y => PsiA p.ν χf A q.1 y) q.2 (ei 1) +
      2 * q.1 * deriv (fun s' => PsiA p.ν χf A s' q.2) q.1 = _
    rw [hds, ← hde (ei 1), hei]
  have hS : UnforcedLeray.Axi.dS (sPsiChart p χf A) q =
      q.1 * fderiv ℝ P q (1, ((0 : ℝ), (0 : ℝ))) + P q := by
    unfold UnforcedLeray.Axi.dS
    rw [hFdv]
    simp
  have hE : UnforcedLeray.Axi.dEta (sPsiChart p χf A) q =
      q.1 * fderiv ℝ P q (0, ((0 : ℝ), (1 : ℝ))) := by
    unfold UnforcedLeray.Axi.dEta
    rw [hFdv]
    simp
  have hkey : 2 * q.1 * UnforcedLeray.Axi.dS (sPsiChart p χf A) q +
      q.2.2 * UnforcedLeray.Axi.dEta (sPsiChart p χf A) q =
      q.1 * (Kop (fun s' y => PsiA p.ν χf A s' y) q.1 q.2 + 2 * PsiA p.ν χf A q.1 q.2) := by
    rw [hS, hE, hKop, ← hPq q]
    ring
  have hn : ∀ a : ℝ, ‖(!₂[a, (0 : ℝ)] : EuclideanSpace ℝ (Fin 2))‖ = |a| := by
    intro a
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, Real.sqrt_sq_eq_abs, sq_abs]
  unfold gradRem
  rw [hkey, hn, abs_neg, abs_mul, abs_mul, abs_of_pos hε, abs_of_pos hq]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
