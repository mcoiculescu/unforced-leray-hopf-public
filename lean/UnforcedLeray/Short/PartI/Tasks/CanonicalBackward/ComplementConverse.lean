import UnforcedLeray.Short.PartI.Sub.PartI_C08_1_3

/-!
# `PartI:C08/1/3/4`: proof of `ComplementConverse`

Converse of `complementFreeDuhamel` (source lines 1094-1125, "uniqueness follows from the bounded
coupling maps and Gronwall"): on the forward block `[-s₀,-b]` the backward Duhamel form of `r`
is the mild form relative to the free family with the bounded perturbation `canonicalCplPert`,
so `Evolution.mild_unique` (Gronwall inside) identifies it with the Dyson evolution, which is
`U` by `cplMildIsDyson`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray MeasureTheory Set

theorem complementConverse_proof : UnforcedLeray.Short.PartI.ComplementConverse := by
  intro lam κ l q Rf b hb U hU y A r hAc hrc hbwd θ s₀ hθ hθs
  have hθ0 : 0 < θ := hb.trans_le hθ
  have he : -b < 0 := neg_lt_zero.mpr hb
  have hid := cplMildIsDyson lam κ l q Rf hb hU (-s₀)
  have hsrc : ContinuousOn (fun σ : ℝ => (A σ / (σ : ℂ)) • y) (Ici b) := by
    refine (hAc.div Complex.continuous_ofReal.continuousOn fun σ hσ => ?_).smul
      continuousOn_const
    exact Complex.ofReal_ne_zero.mpr (hb.trans_le hσ).ne'
  have hρc : ContinuousOn (fun u : ℝ => (A (-u) / ((-u : ℝ) : ℂ)) • y) (Icc (-s₀) (-b)) :=
    hsrc.comp continuous_neg.continuousOn fun u hu => by
      simp only [mem_Ici]
      linarith [hu.2]
  have hρi : IntegrableOn (fun u : ℝ => (A (-u) / ((-u : ℝ) : ℂ)) • y) (Ioc (-s₀) (-b)) :=
    hρc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hzc : ContinuousOn (fun t : ℝ => r (-t)) (Icc (-s₀) (-b)) :=
    hrc.comp continuous_neg.continuousOn fun u hu => by
      simp only [mem_Ici]
      linarith [hu.2]
  have hz : ∀ t ∈ Icc (-s₀) (-b), r (-t) =
      (Cons.G3b.freeFam (-s₀) (-b) he).U t (-s₀) (r (-(-s₀))) +
        ∫ u in (-s₀)..t, (Cons.G3b.freeFam (-s₀) (-b) he).U t u
          ((canonicalCplPert lam κ l q Rf hb (-s₀) (-b)).A u (r (-u)) +
            (A (-u) / ((-u : ℝ) : ℂ)) • y) := by
    intro t ht
    have h2 := (hbwd (-t) s₀ (by linarith [ht.2]) (by linarith [ht.1])).2
    rw [neg_neg]
    rw [h2]
    congr 1
    · show _ = Cons.G3b.freeU t (-s₀) (r s₀)
      simp only [Cons.G3b.freeU, neg_neg]
    have hc := intervalIntegral.integral_comp_neg (a := -t) (b := s₀)
      (f := fun u : ℝ => Cons.G3b.freeU t u
        (canonicalCplGen lam κ l q Rf b u (r (-u)) + (A (-u) / ((-u : ℝ) : ℂ)) • y))
    simp only [neg_neg] at hc
    show _ = ∫ u in (-s₀)..t, Cons.G3b.freeU t u
      (canonicalCplGen lam κ l q Rf b u (r (-u)) + (A (-u) / ((-u : ℝ) : ℂ)) • y)
    rw [← hc]
    refine intervalIntegral.integral_congr fun σ _ => ?_
    simp only [Cons.G3b.freeU, neg_neg]
  have hmu := Evolution.mild_unique (Cons.G3b.freeFam (-s₀) (-b) he)
    (canonicalCplPert lam κ l q Rf hb (-s₀) (-b)) (le_refl (-s₀)) hzc hρi hz (-θ)
    ⟨by linarith, by linarith⟩
  have hm : r (- -s₀) = r s₀ := by rw [neg_neg]
  have hm' : r (- -θ) = r θ := by rw [neg_neg]
  rw [hm, hm'] at hmu
  rw [hmu]
  have hS : ∀ s, θ ≤ s → s ≤ s₀ → canonicalS U θ s = (Evolution.dyson
      (Cons.G3b.freeFam (-s₀) (-b) he) (canonicalCplPert lam κ l q Rf hb (-s₀) (-b))).U (-θ) (-s) := by
    intro s h1 h2
    simp only [canonicalS]
    exact hid (-s) (-θ) (by linarith) (by linarith) (by linarith)
  have hS0 : canonicalS U θ s₀ = (Evolution.dyson
      (Cons.G3b.freeFam (-s₀) (-b) he) (canonicalCplPert lam κ l q Rf hb (-s₀) (-b))).U (-θ) (-s₀) :=
    hS s₀ hθs le_rfl
  rw [hS0]
  congr 1
  have hc := intervalIntegral.integral_comp_neg (a := θ) (b := s₀)
    (f := fun u : ℝ => (A (-u) / ((-u : ℝ) : ℂ)) • (Evolution.dyson
      (Cons.G3b.freeFam (-s₀) (-b) he) (canonicalCplPert lam κ l q Rf hb (-s₀) (-b))).U (-θ) u y)
  simp only [neg_neg] at hc
  simp only [map_smul]
  refine Eq.trans hc.symm ?_
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le hθs] at hs
  rw [hS s hs.1 hs.2]

end UnforcedLeray.Short.PartI
