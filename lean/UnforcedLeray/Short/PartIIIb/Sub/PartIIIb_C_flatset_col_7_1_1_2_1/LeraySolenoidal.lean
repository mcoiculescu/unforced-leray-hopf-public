import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayDefs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayCellIBP
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.IntegralMeasureHCell
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CellFubiniEta
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Smooth divergence-free fields are solenoidal (`SmoothSolenoidal`)

Source `the November 2 reference manuscript` 1676-1677.  For a smooth, `c`-periodic,
divergence-free `W` in `H`, the pairing with every generator `cgrad 0 Φ` of `solenoidalHC 0 c`
vanishes: the weighted cell integral `∫ s^{-3/2}(∂_qΦ W₀ + ∂_ηΦ W₁)` is split into two
integrations by parts (`cellIBP` on each `s`-slice, Fubini on the cell) and `flatDiv W = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open UnforcedLeray.Short.PartIIa

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

lemma sol_dQ_slice (A : Chart → ℝ) (hA : Differentiable ℝ A) (s : ℝ) (y : ℝ × ℝ) :
    pd2 0 (fun z => A (s, z)) y = UnforcedLeray.Axi.dQ A (s, y) := by
  have hι : HasFDerivAt (fun z : ℝ × ℝ => ((s, z) : ℝ × (ℝ × ℝ)))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) y :=
    (hasFDerivAt_const s y).prodMk (hasFDerivAt_id y)
  have hA' : HasFDerivAt A (fderiv ℝ A (s, y)) (s, y) := (hA (s, y)).hasFDerivAt
  have h := (hA'.comp y hι).fderiv
  unfold pd2 UnforcedLeray.Axi.dQ
  rw [show (fun z : ℝ × ℝ => A (s, z)) = A ∘ (fun z => (s, z)) from rfl, h]
  simp [dir2]

lemma sol_dEta_slice (A : Chart → ℝ) (hA : Differentiable ℝ A) (s : ℝ) (y : ℝ × ℝ) :
    pd2 1 (fun z => A (s, z)) y = UnforcedLeray.Axi.dEta A (s, y) := by
  have hι : HasFDerivAt (fun z : ℝ × ℝ => ((s, z) : ℝ × (ℝ × ℝ)))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) y :=
    (hasFDerivAt_const s y).prodMk (hasFDerivAt_id y)
  have hA' : HasFDerivAt A (fderiv ℝ A (s, y)) (s, y) := (hA (s, y)).hasFDerivAt
  have h := (hA'.comp y hι).fderiv
  unfold pd2 UnforcedLeray.Axi.dEta
  rw [show (fun z : ℝ × ℝ => A (s, z)) = A ∘ (fun z => (s, z)) from rfl, h]
  simp [dir2]

lemma sol_dQ_cont (A : Chart → ℝ) (hA : ContDiff ℝ ∞ A) :
    Continuous (UnforcedLeray.Axi.dQ A) := by
  unfold UnforcedLeray.Axi.dQ
  exact (hA.continuous_fderiv (by simp)).clm_apply continuous_const

lemma sol_dEta_cont (A : Chart → ℝ) (hA : ContDiff ℝ ∞ A) :
    Continuous (UnforcedLeray.Axi.dEta A) := by
  unfold UnforcedLeray.Axi.dEta
  exact (hA.continuous_fderiv (by simp)).clm_apply continuous_const

/-- The derivative of a band-supported function vanishes outside the band. -/
lemma sol_fderiv_zero (Φ : Chart → ℝ) (s0 s1 L : ℝ)
    (hband : ∀ p : Chart, Φ p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L)
    (p : Chart) (hp : ¬(p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L)) (v : Chart) :
    fderiv ℝ Φ p v = 0 := by
  have hS : IsClosed {p : Chart | p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L} :=
    (isClosed_Icc.preimage continuous_fst).inter
      (isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd)) continuous_const)
  have hev : Φ =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
    filter_upwards [hS.isOpen_compl.mem_nhds hp] with z hz
    by_contra hne
    exact hz (hband z hne)
  rw [hev.fderiv_eq]
  simp

lemma sol_integrableOn_cell (c : ℝ) (F : Chart → ℝ) (K : Set Chart) (hK : IsCompact K)
    (hFc : ContinuousOn F K) (hz : ∀ p ∈ cell c, p ∉ K → F p = 0) :
    IntegrableOn F (cell c) := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hind : Integrable (K.indicator F) :=
    (integrable_indicator_iff hKm).2 (hFc.integrableOn_compact hK)
  refine (hind.integrableOn).congr_fun ?_ (measurableSet_cell c)
  intro p hp
  by_cases hpK : p ∈ K
  · rw [indicator_of_mem hpK]
  · rw [indicator_of_notMem hpK]
    exact (hz p hp hpK).symm

lemma sol_integ (c s0 s1 L : ℝ) (g h : Chart → ℝ) (hg : Continuous g) (hh : Continuous h)
    (hs0 : 0 < s0) (hz : ∀ p : Chart, ¬(p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) → h p = 0) :
    IntegrableOn (fun p : Chart => p.1 ^ (-(3 / 2 : ℝ)) * (g p * h p)) (cell c) := by
  apply sol_integrableOn_cell c _ (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L))
  · exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  · apply ContinuousOn.mul
    · apply ContinuousOn.rpow_const continuous_fst.continuousOn
      intro p hp
      exact Or.inl (lt_of_lt_of_le hs0 hp.1.1).ne'
    · exact (hg.mul hh).continuousOn
  · intro p hp hpK
    have hnb : ¬(p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) := by
      rintro ⟨h1, h2⟩
      exact hpK ⟨h1, ⟨⟨hp.2.1.1.le, hp.2.1.2⟩, abs_le.1 h2⟩⟩
    simp only [hz p hnb, mul_zero]

lemma sol_fubini (c : ℝ) (F : Chart → ℝ) (hF : IntegrableOn F (cell c)) :
    ∫ p in cell c, F p = ∫ s in Ioi (0 : ℝ), ∫ q in Ioc (0 : ℝ) c, ∫ η : ℝ, F (s, q, η) := by
  have hC : IntegrableOn (fun p => ((F p : ℝ) : ℂ)) (cell c) := Integrable.ofReal hF
  have h := cellFubiniEta c (fun p => ((F p : ℝ) : ℂ)) hC
  simp only [integral_complex_ofReal] at h
  exact_mod_cast h

/-- The cell integration by parts with the weight `s^{-3/2}`, slice by slice in `s`. -/
lemma sol_main (c : ℝ) (hc : 0 < c) (A Φ : Chart → ℝ) (D : (Chart → ℝ) → Chart → ℝ) (k : Fin 2)
    (hD : ∀ G : Chart → ℝ, ContDiff ℝ ∞ G → ∀ s y, pd2 k (fun z => G (s, z)) y = D G (s, y))
    (hDc : ∀ G : Chart → ℝ, ContDiff ℝ ∞ G → Continuous (D G))
    (hA : ContDiff ℝ ∞ A) (hAper : ∀ s q η, A (s, (q + c, η)) = A (s, (q, η)))
    (hΦ : ContDiff ℝ ∞ Φ) (hΦper : ∀ s q η, Φ (s, (q + c, η)) = Φ (s, (q, η)))
    (s0 s1 L : ℝ) (hs0 : 0 < s0)
    (hband : ∀ p : Chart, Φ p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L)
    (hz0 : ∀ p : Chart, ¬(p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) → D Φ p = 0) :
    ∫ p in cell c, p.1 ^ (-(3 / 2 : ℝ)) * (A p * D Φ p) =
      -∫ p in cell c, p.1 ^ (-(3 / 2 : ℝ)) * (D A p * Φ p) := by
  have hI1 : IntegrableOn (fun p : Chart => p.1 ^ (-(3 / 2 : ℝ)) * (A p * D Φ p)) (cell c) :=
    sol_integ c s0 s1 L A (D Φ) hA.continuous (hDc Φ hΦ) hs0 hz0
  have hI2 : IntegrableOn (fun p : Chart => p.1 ^ (-(3 / 2 : ℝ)) * (D A p * Φ p)) (cell c) :=
    sol_integ c s0 s1 L (D A) Φ (hDc A hA) hΦ.continuous hs0 (fun p hp => by
      by_contra hne
      exact hp (hband p hne))
  rw [sol_fubini c _ hI1, sol_fubini c _ hI2, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  dsimp only
  have hB : ContDiff ℝ 1 (fun z : ℝ × ℝ => Φ (s, z)) :=
    (hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hAs : ContDiff ℝ 1 (fun z : ℝ × ℝ => A (s, z)) :=
    (hA.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hAper' : ∀ y : ℝ × ℝ, (fun z : ℝ × ℝ => A (s, z)) (y.1 + c, y.2) =
      (fun z : ℝ × ℝ => A (s, z)) y := fun y => hAper s y.1 y.2
  have hΦper' : ∀ y : ℝ × ℝ, (fun z : ℝ × ℝ => Φ (s, z)) (y.1 + c, y.2) =
      (fun z : ℝ × ℝ => Φ (s, z)) y := fun y => hΦper s y.1 y.2
  have hLb : ∃ L' : ℝ, ∀ y : ℝ × ℝ, L' < |y.2| → (fun z : ℝ × ℝ => Φ (s, z)) y = 0 :=
    ⟨L, fun y hy => by
      by_contra hne
      exact (not_le.2 hy) (hband (s, y) hne).2⟩
  have hfA : Continuous (fun y : ℝ × ℝ => A (s, y) * D Φ (s, y)) :=
    (hA.continuous.comp (continuous_const.prodMk continuous_id)).mul
      ((hDc Φ hΦ).comp (continuous_const.prodMk continuous_id))
  have hfB : Continuous (fun y : ℝ × ℝ => D A (s, y) * Φ (s, y)) :=
    ((hDc A hA).comp (continuous_const.prodMk continuous_id)).mul
      (hΦ.continuous.comp (continuous_const.prodMk continuous_id))
  have hzA : ∀ y : ℝ × ℝ, L < |y.2| → A (s, y) * D Φ (s, y) = 0 := by
    intro y hy
    rw [hz0 (s, y) (fun h => (not_le.2 hy) h.2), mul_zero]
  have hzB : ∀ y : ℝ × ℝ, L < |y.2| → D A (s, y) * Φ (s, y) = 0 := by
    intro y hy
    have : Φ (s, y) = 0 := by
      by_contra hne
      exact (not_le.2 hy) (hband (s, y) hne).2
    rw [this, mul_zero]
  have hint1 := integrableOn_cellS _ hfA 0 c L hzA
  have hint2 := integrableOn_cellS _ hfB 0 c L hzB
  have E1 := cellS_eq_iter_q (fun y : ℝ × ℝ => A (s, y) * D Φ (s, y)) 0 c hint1
  have E2 := cellS_eq_iter_q (fun y : ℝ × ℝ => D A (s, y) * Φ (s, y)) 0 c hint2
  simp only [zero_add] at E1 E2
  have hS := cellIBP c hc 0 (fun z => A (s, z)) (fun z => Φ (s, z)) hAs hB hAper' hΦper' hLb k
  simp only [zero_add, hD Φ hΦ s, hD A hA s] at hS
  simp only [integral_const_mul]
  rw [← E1, ← E2, hS]
  ring

lemma sol_cell_zero (c : ℝ) (hc : 0 < c) (W : Chart → Fin 2 → ℝ)
    (hWsm : ∀ i, ContDiff ℝ ∞ fun p => W p i)
    (hWper : ∀ s q η, W (s, (q + c, η)) = W (s, (q, η)))
    (hdiv : ∀ p, flatDiv W p = 0)
    (Φ : Chart → ℝ) (hΦsm : ContDiff ℝ ∞ Φ) (hΦper : ∀ s q η, Φ (s, (q + c, η)) = Φ (s, (q, η)))
    (s0 s1 L : ℝ) (hs0 : 0 < s0)
    (hband : ∀ p : Chart, Φ p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) :
    ∫ p in cell c, p.1 ^ (-(3 / 2 : ℝ)) *
      (UnforcedLeray.Axi.dQ Φ p * W p 0 + UnforcedLeray.Axi.dEta Φ p * W p 1) = 0 := by
  have hz0Q : ∀ p : Chart, ¬(p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) → UnforcedLeray.Axi.dQ Φ p = 0 :=
    fun p hp => sol_fderiv_zero Φ s0 s1 L hband p hp _
  have hz0E : ∀ p : Chart, ¬(p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) → UnforcedLeray.Axi.dEta Φ p = 0 :=
    fun p hp => sol_fderiv_zero Φ s0 s1 L hband p hp _
  have hA0 : ContDiff ℝ ∞ (fun p : Chart => W p 0) := hWsm 0
  have hA1 : ContDiff ℝ ∞ (fun p : Chart => W p 1) := hWsm 1
  have hAper0 : ∀ s q η, (fun p : Chart => W p 0) (s, (q + c, η)) =
      (fun p : Chart => W p 0) (s, (q, η)) := fun s q η => by
    simp only [hWper s q η]
  have hAper1 : ∀ s q η, (fun p : Chart => W p 1) (s, (q + c, η)) =
      (fun p : Chart => W p 1) (s, (q, η)) := fun s q η => by
    simp only [hWper s q η]
  have hDQ : ∀ G : Chart → ℝ, ContDiff ℝ ∞ G → ∀ s y,
      pd2 0 (fun z => G (s, z)) y = UnforcedLeray.Axi.dQ G (s, y) :=
    fun G hG s y => sol_dQ_slice G (hG.differentiable (by simp)) s y
  have hDE : ∀ G : Chart → ℝ, ContDiff ℝ ∞ G → ∀ s y,
      pd2 1 (fun z => G (s, z)) y = UnforcedLeray.Axi.dEta G (s, y) :=
    fun G hG s y => sol_dEta_slice G (hG.differentiable (by simp)) s y
  have e0 : ∫ p in cell c, p.1 ^ (-(3 / 2 : ℝ)) * (W p 0 * UnforcedLeray.Axi.dQ Φ p) =
      -∫ p in cell c, p.1 ^ (-(3 / 2 : ℝ)) *
        (UnforcedLeray.Axi.dQ (fun p => W p 0) p * Φ p) :=
    sol_main c hc (fun p => W p 0) Φ UnforcedLeray.Axi.dQ 0 hDQ
      (fun G hG => sol_dQ_cont G hG) hA0 hAper0 hΦsm hΦper s0 s1 L hs0 hband hz0Q
  have e1 : ∫ p in cell c, p.1 ^ (-(3 / 2 : ℝ)) * (W p 1 * UnforcedLeray.Axi.dEta Φ p) =
      -∫ p in cell c, p.1 ^ (-(3 / 2 : ℝ)) *
        (UnforcedLeray.Axi.dEta (fun p => W p 1) p * Φ p) :=
    sol_main c hc (fun p => W p 1) Φ UnforcedLeray.Axi.dEta 1 hDE
      (fun G hG => sol_dEta_cont G hG) hA1 hAper1 hΦsm hΦper s0 s1 L hs0 hband hz0E
  have I0 : IntegrableOn (fun p : Chart => p.1 ^ (-(3 / 2 : ℝ)) *
      (W p 0 * UnforcedLeray.Axi.dQ Φ p)) (cell c) :=
    sol_integ c s0 s1 L (fun p => W p 0) (UnforcedLeray.Axi.dQ Φ) (hWsm 0).continuous
      (sol_dQ_cont Φ hΦsm) hs0 hz0Q
  have I1 : IntegrableOn (fun p : Chart => p.1 ^ (-(3 / 2 : ℝ)) *
      (W p 1 * UnforcedLeray.Axi.dEta Φ p)) (cell c) :=
    sol_integ c s0 s1 L (fun p => W p 1) (UnforcedLeray.Axi.dEta Φ) (hWsm 1).continuous
      (sol_dEta_cont Φ hΦsm) hs0 hz0E
  have J0 : IntegrableOn (fun p : Chart => p.1 ^ (-(3 / 2 : ℝ)) *
      (UnforcedLeray.Axi.dQ (fun p => W p 0) p * Φ p)) (cell c) :=
    sol_integ c s0 s1 L (UnforcedLeray.Axi.dQ (fun p => W p 0)) Φ (sol_dQ_cont _ hA0)
      hΦsm.continuous hs0 (fun p hp => by
        by_contra hne
        exact hp (hband p hne))
  have J1 : IntegrableOn (fun p : Chart => p.1 ^ (-(3 / 2 : ℝ)) *
      (UnforcedLeray.Axi.dEta (fun p => W p 1) p * Φ p)) (cell c) :=
    sol_integ c s0 s1 L (UnforcedLeray.Axi.dEta (fun p => W p 1)) Φ (sol_dEta_cont _ hA1)
      hΦsm.continuous hs0 (fun p hp => by
        by_contra hne
        exact hp (hband p hne))
  have hpt : ∀ p : Chart, p.1 ^ (-(3 / 2 : ℝ)) *
      (UnforcedLeray.Axi.dQ Φ p * W p 0 + UnforcedLeray.Axi.dEta Φ p * W p 1) =
      p.1 ^ (-(3 / 2 : ℝ)) * (W p 0 * UnforcedLeray.Axi.dQ Φ p) +
        p.1 ^ (-(3 / 2 : ℝ)) * (W p 1 * UnforcedLeray.Axi.dEta Φ p) := fun p => by ring
  have hzero : ∀ p : Chart, p.1 ^ (-(3 / 2 : ℝ)) *
      (UnforcedLeray.Axi.dQ (fun p => W p 0) p * Φ p) +
        p.1 ^ (-(3 / 2 : ℝ)) * (UnforcedLeray.Axi.dEta (fun p => W p 1) p * Φ p) = 0 := by
    intro p
    have h := hdiv p
    unfold flatDiv at h
    linear_combination (p.1 ^ (-(3 / 2 : ℝ)) * Φ p) * h
  simp only [hpt]
  rw [integral_add I0 I1, e0, e1]
  have key : (∫ p in cell c, p.1 ^ (-(3 / 2 : ℝ)) *
        (UnforcedLeray.Axi.dQ (fun p => W p 0) p * Φ p)) +
      (∫ p in cell c, p.1 ^ (-(3 / 2 : ℝ)) *
        (UnforcedLeray.Axi.dEta (fun p => W p 1) p * Φ p)) = 0 := by
    rw [← integral_add J0 J1]
    simp only [hzero, integral_zero]
  linarith [key]

lemma sol_pair (c : ℝ) (hc : 0 < c) (W : Chart → Fin 2 → ℝ)
    (hWsm : ∀ i, ContDiff ℝ ∞ fun p => W p i)
    (hWper : ∀ s q η, W (s, (q + c, η)) = W (s, (q, η)))
    (hdiv : ∀ p, flatDiv W p = 0)
    (hW : MemLp (fun p => cvec (W p)) 2 (UnforcedLeray.B0220.measureH c))
    (Φ : ProfileTest c) (hΦ : MemLp (cgrad 0 Φ.1) 2 (UnforcedLeray.B0220.measureH c)) :
    ⟪hΦ.toLp (cgrad 0 Φ.1), hW.toLp _⟫_ℂ = 0 := by
  have hpt : ∀ p : Chart, ⟪cgrad 0 Φ.1 p, cvec (W p)⟫_ℂ =
      ((UnforcedLeray.Axi.dQ Φ.1 p : ℝ) : ℂ) * ((W p 0 : ℝ) : ℂ) +
        ((UnforcedLeray.Axi.dEta Φ.1 p : ℝ) : ℂ) * ((W p 1 : ℝ) : ℂ) := by
    intro p
    simp [cgrad, cvec, Deps_zero, PiLp.inner_apply, Fin.sum_univ_two]
    try ring
  have hint : ∫ a, ⟪hΦ.toLp (cgrad 0 Φ.1) a, hW.toLp _ a⟫_ℂ ∂(UnforcedLeray.B0220.measureH c) =
      ∫ a, ((UnforcedLeray.Axi.dQ Φ.1 a : ℝ) : ℂ) * ((W a 0 : ℝ) : ℂ) +
        ((UnforcedLeray.Axi.dEta Φ.1 a : ℝ) : ℂ) * ((W a 1 : ℝ) : ℂ)
        ∂(UnforcedLeray.B0220.measureH c) := by
    apply integral_congr_ae
    filter_upwards [hΦ.coeFn_toLp, hW.coeFn_toLp] with a h1 h2
    simp only [h1, h2, hpt]
  rw [L2.inner_def, hint]
  have hI := integralMeasureHCell c (fun a : Chart =>
    ((UnforcedLeray.Axi.dQ Φ.1 a : ℝ) : ℂ) * ((W a 0 : ℝ) : ℂ) +
      ((UnforcedLeray.Axi.dEta Φ.1 a : ℝ) : ℂ) * ((W a 1 : ℝ) : ℂ))
  rw [hI]
  have hR : ∀ p : Chart, ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
      (((UnforcedLeray.Axi.dQ Φ.1 p : ℝ) : ℂ) * ((W p 0 : ℝ) : ℂ) +
        ((UnforcedLeray.Axi.dEta Φ.1 p : ℝ) : ℂ) * ((W p 1 : ℝ) : ℂ)) =
      (((p.1 ^ (-(3 / 2 : ℝ))) * (UnforcedLeray.Axi.dQ Φ.1 p * W p 0 +
        UnforcedLeray.Axi.dEta Φ.1 p * W p 1) : ℝ) : ℂ) := fun p => by
    push_cast
    ring
  simp only [hR]
  obtain ⟨s0, s1, L, hs0, hb⟩ := Φ.2.band
  rw [integral_complex_ofReal, sol_cell_zero c hc W hWsm hWper hdiv Φ.1 Φ.2.smooth
    (fun s q η => Φ.2.periodic (s, q, η)) s0 s1 L hs0 hb]
  simp

theorem smoothSolenoidal : SmoothSolenoidal := by
  intro c hc W hWsm hWper hdiv hW
  unfold UnforcedLeray.Short.PartIIa.solenoidalHC
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Φ, hΦmem, rfl⟩ := hx
    exact sol_pair c hc W hWsm hWper hdiv hW Φ hΦmem
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
