import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Defs

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18`: `AdjMollEnergy` from its leaves

Source of record: `the November 2 reference manuscript` lines 3060-3071, 3052-3058.
For each `r ∈ [a, b]` the order `-1` bound (`KTOrderMinusOneUnif`, with `B = ∇E(r)` from
`TrainGradBdd`) gives `χ(r)` with level-`(k+1)` jets bounded by a multiple of `M`; the dynamics leaf
`MollRateDeriv` gives continuity and the derivative of `N_j`; the static leaf `StaticMollEnergy`
(with the slice data of `TrainSliceVel`) gives the inequality.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem adjMollEnergy_of (m : ℝ) (hm : 8 < m) (hB : MollRateDeriv m) (hD : StaticMollEnergy m)
    (hV : TrainSliceVel) (hE : TrainGradBdd) (hK : KTOrderMinusOneUnif m) : AdjMollEnergy m := by
  intro ν hν hν1 tr hTB hTJ t s ht hts g φ hφ hTD k a b hta hab hbs D M hDj hDM
  have hc1 : (1 : ℝ) ≤ ν ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  have hs0 : 0 ≤ s := ht.trans hts.le
  have hsub : ∀ r ∈ Icc a b, r ∈ Icc (0 : ℝ) s := fun r hr =>
    ⟨ht.trans (hta.trans hr.1), hr.2.trans hbs.le⟩
  obtain ⟨Av, hAv⟩ := hV ν _ tr m s hs0 (hTJ s hs0)
  obtain ⟨A, hA⟩ := hE ν _ tr m s hs0 (hTJ s hs0) k
  obtain ⟨Cχ, hCχ0, hCχ⟩ := hK (by linarith) _ hc1 k A
  obtain ⟨C, β, hC0, hβ, hS⟩ := hD ν hν hν1 k Av (Cχ * ((wordsLE k).card : ℝ))
  have hex : ∀ r ∈ Icc a b, ∃ (χ : ℝ × ℝ → ℂ) (Dχ : List (Fin 2) → ℝ × ℝ → ℂ),
      IsCellJet (ν ^ (-2 : ℝ)) m (k + 1) χ Dχ ∧
        (∀ w : List (Fin 2), w.length ≤ k + 1 →
          xNorm (ν ^ (-2 : ℝ)) (-m) (Dχ w) ≤
            ENNReal.ofReal Cχ * jetNorm (ν ^ (-2 : ℝ)) m k (D r)) ∧
        ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ), B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ →
          IsKernelBiotSavart (ν ^ (-2 : ℝ)) ψ uψ →
          IntegrableOn (fun x => φ r x *
              ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
                uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ))
            (B0579.cell (ν ^ (-2 : ℝ))) ∧
          ∫ x in B0579.cell (ν ^ (-2 : ℝ)), χ x * (ψ x : ℂ) =
            ∫ x in B0579.cell (ν ^ (-2 : ℝ)), φ r x *
              ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
                uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) := by
    intro r hr
    obtain ⟨h1, h2, h3⟩ := hA r (hsub r hr)
    exact hCχ (fun l => B0579.pd l (UnforcedLeray.B0238.Ec tr r)) h1 h2
      (fun l i hi x => h3 l i hi x) (φ r) (D r) (hDj r hr)
  choose! χ Dχ hχ using hex
  have hjn : ∀ r ∈ Icc a b,
      jetNorm (ν ^ (-2 : ℝ)) m k (D r) ≤ ENNReal.ofReal (((wordsLE k).card : ℝ) * M) := by
    intro r hr
    unfold jetNorm
    calc ∑ w ∈ wordsLE k, xNorm (ν ^ (-2 : ℝ)) (-m) (D r w)
        ≤ ∑ _w ∈ wordsLE k, ENNReal.ofReal M :=
          Finset.sum_le_sum fun w hw => hDM r hr w (mem_wordsLE.1 hw)
      _ = ENNReal.ofReal (((wordsLE k).card : ℝ) * M) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
  have hχb : ∀ r ∈ Icc a b, ∀ w : List (Fin 2), w.length ≤ k + 1 →
      xNorm (ν ^ (-2 : ℝ)) (-m) (Dχ r w) ≤
        ENNReal.ofReal (Cχ * ((wordsLE k).card : ℝ) * M) := by
    intro r hr w hw
    calc xNorm (ν ^ (-2 : ℝ)) (-m) (Dχ r w)
        ≤ ENNReal.ofReal Cχ * jetNorm (ν ^ (-2 : ℝ)) m k (D r) := (hχ r hr).2.1 w hw
      _ ≤ ENNReal.ofReal Cχ * ENNReal.ofReal (((wordsLE k).card : ℝ) * M) := by
          gcongr; exact hjn r hr
      _ = ENNReal.ofReal (Cχ * ((wordsLE k).card : ℝ) * M) := by
          rw [← ENNReal.ofReal_mul hCχ0, mul_assoc]
  refine ⟨C, β, hC0, hβ, fun n j hj => ?_⟩
  have hB' := hB ν hν hν1 tr hTB t s ht hts g φ hφ hTD a b hta hab hbs χ
    (fun r hr => ⟨(hχ r hr).1.periodic [] (Nat.zero_le _) |> fun h => by
        simpa [(hχ r hr).1.base] using h,
      by simpa [(hχ r hr).1.base] using (hχ r hr).1.memX [] (Nat.zero_le _),
      (hχ r hr).2.2⟩) n j
  refine ⟨hB'.1, fun r hr => ⟨_, hB'.2 r hr, ?_⟩⟩
  have hr' : r ∈ Icc a b := Ioo_subset_Icc_self hr
  exact hS (tr.v r) (hAv r (hsub r hr')) (φ r) (χ r) (D r) (Dχ r) M (hDj r hr') (hDM r hr')
    (hχ r hr').1 (hχb r hr') n j hj

end UnforcedLeray.Short.IIIa
