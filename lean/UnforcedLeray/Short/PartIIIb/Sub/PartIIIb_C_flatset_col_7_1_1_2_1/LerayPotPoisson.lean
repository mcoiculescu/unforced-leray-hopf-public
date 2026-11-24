import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayPotSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayKerGreen
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayForceDeriv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayKerWindow
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayPotPoisson.Chain

/-!
# Poisson equation for the flat potential (`LerayPotPoisson`)

Source `the November 2 reference manuscript` 1676: `Δu = div F` for
`u = Σ_i K_i ⊛ F_i`.  Route: `∂_v u = lerayPot (∂_v F)` (`LerayPotSmooth`), so `Δu` is the
convolution of `K_i` with `lap` of `F_i`; each summand is the fundamental-solution identity
`CylKerGreen` applied to the test `h(y) = F_i(p + (0,-y))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Integrability of `y ↦ K_i(y) G_i(p.1, p.2 - y)` on the cell for a force field `G`. -/
lemma pp_integrable (c : ℝ) (hc : 0 < c) (G : Chart → Fin 2 → ℝ) (hG : IsForceField c G)
    (i : Fin 2) (p : Chart) :
    Integrable (fun y : ℝ × ℝ => cylKer c i y * G (p.1, p.2 - y) i)
      (volume.restrict (cellC c)) := by
  obtain ⟨hGs, hGper, s0, s1, LG, hs0, hsupp⟩ := hG
  have hFi : ContDiff ℝ ∞ (fun q => G q i) := hGs i
  have hperi : ∀ s q η, (fun q => G q i) (s, (q + c, η)) = (fun q => G q i) (s, (q, η)) :=
    fun s q η => congrFun (hGper s q η) i
  have hLF : ∀ q : Chart, LG < |q.2.2| → G q i = 0 := by
    intro q hq
    by_contra hne
    have hG0 : G q ≠ 0 := fun h0 => hne (by simp [h0])
    exact absurd (hsupp q hG0).2 (not_le.2 hq)
  obtain ⟨M, hM⟩ := boundedDerivBand c hc (fun q => G q i) hFi hperi
    ⟨s0, s1, LG, fun q hq => hsupp q (fun h0 => hq (by simp [h0]))⟩ 0
  have hMM : ∀ q : Chart, ‖iteratedFDeriv ℝ 0 (fun q => G q i) q‖ ≤ max M 0 :=
    fun q => (hM q).trans (le_max_left _ _)
  have hcont : Continuous (fun y : ℝ × ℝ => G (p.1, p.2 - y) i) :=
    hFi.continuous.comp (continuous_const.prodMk (continuous_const.sub continuous_id))
  have hmeas : AEStronglyMeasurable (fun y : ℝ × ℝ => cylKer c i y * G (p.1, p.2 - y) i)
      (volume.restrict (cellC c)) :=
    (cylKW_meas c i).aestronglyMeasurable.mul hcont.aestronglyMeasurable
  refine Integrable.mono' (lps_ind_int c hc i p.2.2 LG (max M 0)) hmeas ?_
  refine ae_restrict_of_forall_mem (MeasurableSet.prod measurableSet_Ioc MeasurableSet.univ)
    (fun y hy => ?_)
  have h := lps_pointwise c G i LG hLF hFi (max M 0) 0 hMM y hy p
  rw [norm_iteratedFDeriv_zero] at h
  exact h

/-- A force field vanishes for `|η|` large. -/
lemma pp_zero (c : ℝ) (F : Chart → Fin 2 → ℝ) (hF : IsForceField c F) :
    ∃ LF : ℝ, ∀ q : Chart, LF < |q.2.2| → F q = 0 := by
  obtain ⟨_, _, _, _, LF, _, hsupp⟩ := hF
  refine ⟨LF, fun q hq => ?_⟩
  by_contra hne
  exact absurd (hsupp q hne).2 (not_le.2 hq)

/-- The reflected component `y ↦ F_i(p + (0,-y))` is a cylinder test function. -/
lemma pp_test (c : ℝ) (hc : 0 < c) (F : Chart → Fin 2 → ℝ) (hF : IsForceField c F)
    (p : Chart) (i : Fin 2) : IsCylTest2 c (fun y => F (p + ((0 : ℝ), -y)) i) := by
  obtain ⟨LF, hLF⟩ := pp_zero c F hF
  refine ⟨?_, ?_, ?_⟩
  · exact (hF.1 i).comp (contDiff_const.add (contDiff_const.prodMk contDiff_id.neg))
  · intro y
    obtain ⟨s, q, η⟩ := p
    have e1 : ((s, (q, η)) + ((0 : ℝ), -((y.1 + c), y.2))) =
        (s, (q + -y.1 + -c, η + -y.2)) := by
      ext <;> simp <;> ring
    have e2 : ((s, (q, η)) + ((0 : ℝ), -y)) = (s, (q + -y.1, η + -y.2)) := by
      ext <;> simp
    show F ((s, (q, η)) + ((0 : ℝ), -((y.1 + c), y.2))) i = F ((s, (q, η)) + ((0 : ℝ), -y)) i
    rw [e1, e2]
    have h := congrFun (hF.2.1 s (q + -y.1 + -c) (η + -y.2)) i
    rw [show q + -y.1 + -c + c = q + -y.1 by ring] at h
    exact h.symm
  · obtain ⟨LF', hLF'⟩ := pp_zero c F hF
    refine ⟨LF' + |p.2.2|, fun y hy => ?_⟩
    have hz : LF' < |(p + ((0 : ℝ), -y)).2.2| := by
      have e : (p + ((0 : ℝ), -y)).2.2 = p.2.2 - y.2 := by simp [sub_eq_add_neg]
      rw [e]
      rcases abs_cases p.2.2 with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
        rcases abs_cases y.2 with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
        rcases abs_cases (p.2.2 - y.2) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> linarith
    have := hLF' _ hz
    exact congrFun this i

lemma pp_dv_isForce (c : ℝ) (F : Chart → Fin 2 → ℝ) (hF : IsForceField c F) (v : Chart) :
    IsForceField c (ppDv F v) :=
  forceFieldDeriv c F hF v

/-- **Poisson equation**: `Δ_{q,η} u = div F` for `u = lerayPot c F` (source 1676). -/
theorem lerayPotPoisson : LerayPotPoisson := by
  intro c hc F hF p
  have hdlu : ∀ (G : Chart → Fin 2 → ℝ), IsForceField c G → ∀ (v p' : Chart),
      fderiv ℝ (lerayPot c G) p' v = lerayPot c (ppDv G v) p' :=
    fun G hG v p' => (lerayPotSmooth c hc G hG).2.2 p' v
  have hA : ∀ (G : Chart → Fin 2 → ℝ), IsForceField c G → ∀ (v w p' : Chart),
      fderiv ℝ (fun q => fderiv ℝ (lerayPot c G) q v) p' w =
        lerayPot c (ppDv (ppDv G v) w) p' := by
    intro G hG v w p'
    have hfun : (fun q => fderiv ℝ (lerayPot c G) q v) = lerayPot c (ppDv G v) :=
      funext fun q => hdlu G hG v q
    rw [hfun]
    exact hdlu (ppDv G v) (pp_dv_isForce c G hG v) w p'
  have hL : UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ (lerayPot c F)) p +
      UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta (lerayPot c F)) p =
      lerayPot c (ppDv (ppDv F ((0 : ℝ), dir2 0)) ((0 : ℝ), dir2 0)) p +
        lerayPot c (ppDv (ppDv F ((0 : ℝ), dir2 1)) ((0 : ℝ), dir2 1)) p := by
    have h0 := hA F hF ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) p
    have h1 := hA F hF ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) p
    have hd0 : dir2 0 = ((1 : ℝ), (0 : ℝ)) := by simp [dir2]
    have hd1 : dir2 1 = ((0 : ℝ), (1 : ℝ)) := by simp [dir2]
    rw [hd0, hd1]
    exact congrArg₂ (· + ·) h0 h1
  have hsum : lerayPot c (ppDv (ppDv F ((0 : ℝ), dir2 0)) ((0 : ℝ), dir2 0)) p +
      lerayPot c (ppDv (ppDv F ((0 : ℝ), dir2 1)) ((0 : ℝ), dir2 1)) p =
      ∑ i : Fin 2, ∫ y in cellC c, cylKer c i y *
        (ppDv (ppDv F ((0 : ℝ), dir2 0)) ((0 : ℝ), dir2 0) (p.1, p.2 - y) i +
          ppDv (ppDv F ((0 : ℝ), dir2 1)) ((0 : ℝ), dir2 1) (p.1, p.2 - y) i) := by
    unfold lerayPot
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_add
      (pp_integrable c hc _ (pp_dv_isForce c _ (pp_dv_isForce c F hF _) _) i p)
      (pp_integrable c hc _ (pp_dv_isForce c _ (pp_dv_isForce c F hF _) _) i p)]
    congr 1
    funext y
    ring
  have key : ∀ i : Fin 2, ∫ y in cellC c, cylKer c i y *
      (ppDv (ppDv F ((0 : ℝ), dir2 0)) ((0 : ℝ), dir2 0) (p.1, p.2 - y) i +
        ppDv (ppDv F ((0 : ℝ), dir2 1)) ((0 : ℝ), dir2 1) (p.1, p.2 - y) i) =
      fderiv ℝ (fun z => F z i) p (0, dir2 i) := by
    intro i
    have hgs : ContDiff ℝ ∞ (fun z => F z i) := hF.1 i
    have hshift : ∀ y : ℝ × ℝ, (p.1, p.2 - y) = p + ((0 : ℝ), -y) := fun y => lps_shift p y
    have hp : ∀ j : Fin 2, pd2 j (fun y => F (p + ((0 : ℝ), -y)) i) =
        fun y' => -fderiv ℝ (fun z => F z i) (p + ((0 : ℝ), -y')) ((0 : ℝ), dir2 j) := by
      intro j
      funext y'
      exact pp_chain1 _ hgs p y' (dir2 j)
    have hpp : ∀ (j : Fin 2) (y : ℝ × ℝ), pd2 j (pd2 j (fun y => F (p + ((0 : ℝ), -y)) i)) y =
        ppDv (ppDv F ((0 : ℝ), dir2 j)) ((0 : ℝ), dir2 j) (p + ((0 : ℝ), -y)) i := by
      intro j y
      show fderiv ℝ (pd2 j (fun y => F (p + ((0 : ℝ), -y)) i)) y (dir2 j) = _
      rw [hp j, fderiv_fun_neg, ContinuousLinearMap.neg_apply, pp_chain2 _ hgs p _ y (dir2 j),
        neg_neg]
      rfl
    have hlap : ∀ y : ℝ × ℝ, lap2 (fun y => F (p + ((0 : ℝ), -y)) i) y =
        ppDv (ppDv F ((0 : ℝ), dir2 0)) ((0 : ℝ), dir2 0) (p.1, p.2 - y) i +
          ppDv (ppDv F ((0 : ℝ), dir2 1)) ((0 : ℝ), dir2 1) (p.1, p.2 - y) i := by
      intro y
      rw [hshift y]
      unfold lap2
      rw [hpp 0 y, hpp 1 y]
    have hG := cylKerGreen c hc (fun y => F (p + ((0 : ℝ), -y)) i) (pp_test c hc F hF p i) i
    simp_rw [← hlap]
    rw [hG]
    unfold pd2
    have h0 : p + ((0 : ℝ), -(0 : ℝ × ℝ)) = p := by ext <;> simp
    rw [pp_chain1 _ hgs p 0 (dir2 i), h0]
    simp
  rw [hL, hsum, Fin.sum_univ_two, key 0, key 1]
  unfold flatDiv UnforcedLeray.Axi.dQ UnforcedLeray.Axi.dEta
  simp [dir2]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
