import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2_Smooth
import UnforcedLeray.Lib.EvolutionFamilies.Fubini

/-!
# Part III-a, `PartIII-a:T21/3/2/2/3/3`: assembly of the Duhamel identity `UnitHeatDuhamel`

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
From `FluxPairHeatDuhamel` (pointwise in the flux) and `FluxPairHeatContinuous` (joint continuity
of `(r, θ) ↦ ⟨F(r), ∇P_θ g⟩`), the Duhamel identity of the smoothed tests follows by substituting
`η = u - r` and swapping the triangle `∫_a^t dr ∫_r^t du = ∫_a^t du ∫_a^u dr`
(`UnforcedLeray.Evolution.integral_triangle_swap`, applied in `ℂ` to real-valued integrands).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- Clamp a real number into `[a, b]`. -/
def clampI (a b x : ℝ) : ℝ := max a (min b x)

theorem clampI_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : clampI a b x ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

theorem clampI_eq {a b x : ℝ} (hx : x ∈ Icc a b) : clampI a b x = x := by
  unfold clampI
  rw [min_eq_right hx.2, max_eq_right hx.1]

theorem unitHeatDuhamel_of (h1 : FluxPairHeatDuhamel) (h2 : FluxPairHeatContinuous) :
    UnitHeatDuhamel cylHeatSmooth := by
  intro c m _ hm F a b hab hb hF φ hφ t ht
  have hc : 0 < c := Fact.out
  have hL : UnforcedLeray.B0579.IsCylTest c (lapP φ) := cylTest_lapP hφ
  have hΦ := h2 c m hm F a b hF (lapP φ) hL
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hΦ
  obtain ⟨Gc, hGc_def⟩ : ∃ Gc : ℝ × ℝ → ℝ, Gc = fun p => fluxPair hm (F (clampI a b p.1))
      (cylHeatSmooth c (clampI (-1) 1 p.2) (lapP φ)) := ⟨_, rfl⟩
  have hGcapp : ∀ p : ℝ × ℝ, Gc p = fluxPair hm (F (clampI a b p.1))
      (cylHeatSmooth c (clampI (-1) 1 p.2) (lapP φ)) := fun p => by rw [hGc_def]
  have hmem : ∀ p : ℝ × ℝ, (clampI a b p.1, clampI (-1) 1 p.2) ∈ Icc a b ×ˢ Icc (-1 : ℝ) 1 :=
    fun p => ⟨clampI_mem hab p.1, clampI_mem (by norm_num) p.2⟩
  have hcl : Continuous (fun p : ℝ × ℝ => (clampI a b p.1, clampI (-1) 1 p.2)) := by
    unfold clampI
    exact (continuous_const.max (continuous_const.min continuous_id)).comp continuous_fst |>.prodMk
      ((continuous_const.max (continuous_const.min continuous_id)).comp continuous_snd)
  have hGcont : Continuous Gc := by
    have hGeq : Gc = (fun p : ℝ × ℝ => fluxPair hm (F p.1) (cylHeatSmooth c p.2 (lapP φ))) ∘
        (fun p : ℝ × ℝ => (clampI a b p.1, clampI (-1) 1 p.2)) :=
      funext fun p => hGcapp p
    rw [hGeq]
    exact hΦ.comp_continuous hcl hmem
  have hGbd : ∀ p, ‖Gc p‖ ≤ C := fun p => by
    rw [hGcapp p]
    exact hC _ (hmem p)
  have hΦ' : ∀ r η : ℝ, r ∈ Icc a b → η ∈ Icc (-1 : ℝ) 1 →
      Gc (r, η) = fluxPair hm (F r) (cylHeatSmooth c η (lapP φ)) := by
    intro r η hr hη
    have := hGcapp (r, η)
    simp only at this
    rw [this, clampI_eq hr, clampI_eq hη]
  -- the flux pairing against `φ` is continuous on `[a, t]`
  have hA0 := (h2 c m hm F a b hF φ hφ).comp
    (continuousOn_id.prodMk (continuousOn_const (c := (0 : ℝ))))
    (fun x hx => ⟨hx, ⟨by norm_num, by norm_num⟩⟩)
  have hA : ContinuousOn (fun r => fluxPair hm (F r) φ) (Icc a b) := by
    refine hA0.congr ?_
    intro r _
    simp [cylHeatSmooth_zero]
  have hAint : IntervalIntegrable (fun r => fluxPair hm (F r) φ) volume a t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 (hA.mono (Icc_subset_Icc le_rfl ht.2))
  have hBc : Continuous (fun r : ℝ => ∫ η in (0 : ℝ)..(t - r), Gc (r, η)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun r η => Gc (r, η)) hGcont (continuous_const.sub continuous_id)
  have hBint : IntervalIntegrable (fun r : ℝ => ∫ η in (0 : ℝ)..(t - r), Gc (r, η)) volume a t :=
    hBc.intervalIntegrable _ _
  -- pointwise identity on `[a, t]`
  have hint1 : ∀ r ∈ uIcc a t, fluxPair hm (F r) (cylHeatSmooth c (t - r) φ) =
      fluxPair hm (F r) φ + ∫ η in (0 : ℝ)..(t - r), Gc (r, η) := by
    intro r hr
    rw [uIcc_of_le ht.1] at hr
    have hθ : t - r ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hr.2], by linarith [hr.1, ht.2, hb]⟩
    rw [h1 c m hm (F r) φ hφ (t - r) hθ]
    congr 1
    refine intervalIntegral.integral_congr (fun η hη => ?_)
    rw [uIcc_of_le (by linarith [hr.2] : (0 : ℝ) ≤ t - r)] at hη
    show fluxPair hm (F r) (cylHeatSmooth c η (lapP φ)) = Gc (r, η)
    rw [hΦ' r η ⟨hr.1, hr.2.trans ht.2⟩ ⟨by linarith [hη.1], by linarith [hη.2, hθ.2]⟩]
  have e : (∫ r in a..t, fluxPair hm (F r) (cylHeatSmooth c (t - r) φ)) =
      ∫ r in a..t, (fluxPair hm (F r) φ + ∫ η in (0 : ℝ)..(t - r), Gc (r, η)) :=
    intervalIntegral.integral_congr hint1
  -- triangle swap, in `ℂ`
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun (q r : ℝ) => ((Gc (r, q - r) : ℝ) : ℂ))
      (UnforcedLeray.Evolution.triMeasure a t) :=
    (Complex.continuous_ofReal.comp
      (hGcont.comp (continuous_snd.prodMk (continuous_fst.sub continuous_snd)))).aestronglyMeasurable
  have hK : ∀ q r : ℝ, a < r → r < q → q ≤ t → ‖((Gc (r, q - r) : ℝ) : ℂ)‖ ≤ C :=
    fun q r _ _ _ => by
      rw [Complex.norm_real]
      exact hGbd _
  have tri := UnforcedLeray.Evolution.integral_triangle_swap (X := ℂ) ht.1
    (G := fun q r => ((Gc (r, q - r) : ℝ) : ℂ)) hmeas hK
  simp only [intervalIntegral.integral_ofReal] at tri
  have triR : (∫ q in a..t, ∫ r in a..q, Gc (r, q - r)) =
      ∫ r in a..t, ∫ q in r..t, Gc (r, q - r) := by
    exact_mod_cast tri
  have hcomp : ∀ r : ℝ, (∫ q in r..t, Gc (r, q - r)) = ∫ η in (0 : ℝ)..(t - r), Gc (r, η) := by
    intro r
    have h : (∫ q in r..t, Gc (r, q - r)) = ∫ x in r - r..t - r, Gc (r, x) :=
      intervalIntegral.integral_comp_sub_right (fun η => Gc (r, η)) r
    rw [h, sub_self]
  have hBsum : (∫ r in a..t, ∫ η in (0 : ℝ)..(t - r), Gc (r, η)) =
      ∫ u in a..t, ∫ r in a..u, fluxPair hm (F r) (cylHeatSmooth c (u - r) (lapP φ)) := by
    have e1 : (∫ r in a..t, ∫ η in (0 : ℝ)..(t - r), Gc (r, η)) =
        ∫ r in a..t, ∫ q in r..t, Gc (r, q - r) :=
      intervalIntegral.integral_congr (fun r _ => (hcomp r).symm)
    rw [e1, ← triR]
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [uIcc_of_le ht.1] at hu
    refine intervalIntegral.integral_congr (fun r hr => ?_)
    rw [uIcc_of_le hu.1] at hr
    show Gc (r, u - r) = fluxPair hm (F r) (cylHeatSmooth c (u - r) (lapP φ))
    rw [hΦ' r (u - r) ⟨hr.1, hr.2.trans (hu.2.trans ht.2)⟩
      ⟨by linarith [hr.2], by linarith [hr.1, hu.2, ht.2, hb]⟩]
  rw [e, intervalIntegral.integral_add hAint hBint, hBsum]

end UnforcedLeray.Short.IIIa.Exist
