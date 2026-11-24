import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_1_7
import UnforcedLeray.Lib.Gaussian.Periodization
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutLimit

/-!
# `PartIII-a:T21/2/7/1/7/1`: fundamental lemma on the cylinder (`locCylUniq`)

An element `f` of `X_{-m,c}` (= `AdjX c m`) whose pairing with every cylinder test vanishes is
zero. Route: `f` is locally integrable on the open interior `U = (-c/2, c/2) × ℝ` of the cell
(`CutLimitAux.integrable_complex` against a band indicator), so the Mathlib fundamental lemma
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` applies once every smooth compactly
supported `g` with `tsupport g ⊆ U` is replaced by its `c`-periodization, which is a cylinder
test equal to `g` on the cell (`Gaussian.periodize`, `contDiff_periodize`). The boundary line
`q = -c/2` is Lebesgue-null.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace LocCylUniqAux

/-- Derivatives of a smooth compactly supported function are bounded by a translate-decay
envelope `C (1 + |q|)^{-2}`. -/
theorem hD_bound {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hcs : HasCompactSupport g) (k : ℕ) :
    ∃ C : ℝ, ∀ z : ℝ × ℝ, ‖iteratedFDeriv ℝ k g z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  have hcont : Continuous (iteratedFDeriv ℝ k g) := hg.continuous_iteratedFDeriv (by simp)
  have hK : HasCompactSupport (iteratedFDeriv ℝ k g) := hcs.iteratedFDeriv k
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support hK
  obtain ⟨R, hR⟩ := hK.isCompact.exists_bound_of_continuousOn continuous_fst.continuousOn
  refine ⟨max M 0 * (1 + |R|) ^ 2, fun z => ?_⟩
  by_cases hz : z ∈ tsupport (iteratedFDeriv ℝ k g)
  · have h1 : |z.1| ≤ R := by
      have := hR z hz
      rw [Real.norm_eq_abs] at this
      exact this
    have hpos : 0 < 1 + |z.1| := by positivity
    rw [Real.rpow_neg hpos.le, Real.rpow_two]
    have hMle : ‖iteratedFDeriv ℝ k g z‖ ≤ max M 0 := (hM z).trans (le_max_left _ _)
    have h2 : (1 : ℝ) ≤ (1 + |R|) ^ 2 * ((1 + |z.1|) ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      have hR' : |z.1| ≤ |R| := h1.trans (le_abs_self R)
      nlinarith [abs_nonneg z.1, abs_nonneg R]
    calc ‖iteratedFDeriv ℝ k g z‖ ≤ max M 0 := hMle
      _ ≤ max M 0 * ((1 + |R|) ^ 2 * ((1 + |z.1|) ^ 2)⁻¹) :=
          le_mul_of_one_le_right (le_max_right _ _) h2
      _ = max M 0 * (1 + |R|) ^ 2 * ((1 + |z.1|) ^ 2)⁻¹ := by ring
  · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
    exact mul_nonneg (mul_nonneg (le_max_right _ _) (by positivity)) (by positivity)

/-- The `c`-periodization of a smooth compactly supported bump in the open strip is a cylinder
test. -/
theorem periodize_isCylTest {c : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hcs : HasCompactSupport g) :
    B0579.IsCylTest c (UnforcedLeray.Gaussian.periodize c g) := by
  refine ⟨?_, ?_, ?_⟩
  · exact UnforcedLeray.Gaussian.contDiff_periodize (s := 2) (by norm_num) hc.ne' hg
      (fun k _ => hD_bound hg hcs k)
  · intro x
    exact UnforcedLeray.Gaussian.periodize_add_period c g x.1 x.2
  · obtain ⟨Rη, hRη⟩ := hcs.isCompact.exists_bound_of_continuousOn continuous_snd.continuousOn
    refine ⟨Rη, fun x hx => ?_⟩
    have hterm : ∀ n : ℤ, g (x.1 - n * c, x.2) = 0 := fun n =>
      image_eq_zero_of_notMem_tsupport (fun h => by
        have h' : ‖x.2‖ ≤ Rη := by
          have := hRη _ h
          exact this
        rw [Real.norm_eq_abs] at h'
        linarith)
    simp only [UnforcedLeray.Gaussian.periodize, hterm, tsum_zero]

/-- On the cell the periodization agrees with the bump `g` whose support lies in the open
strip. -/
theorem periodize_eqOn_cell {c : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℝ}
    (hU : tsupport g ⊆ Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)) :
    EqOn (UnforcedLeray.Gaussian.periodize c g) g (UnforcedLeray.B0579.cell c) := by
  intro x hx
  have hterm : ∀ n : ℤ, n ≠ 0 → g (x.1 - n * c, x.2) = 0 := by
    intro n hn
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have h1 : x.1 - n * c ∈ Ioo (-(c / 2)) (c / 2) := (hU h).1
    obtain ⟨h1a, h1b⟩ := h1
    obtain ⟨hx1, hx2⟩ := hx.1
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ -1 - n by linarith) hc.le]
    · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ n - 1 by linarith) hc.le]
  simp only [UnforcedLeray.Gaussian.periodize]
  rw [tsum_eq_single 0 (fun n hn => hterm n hn)]
  simp

end LocCylUniqAux

open LocCylUniqAux

/-- **(L3) Fundamental lemma on the cylinder** (SP 3052-3058): an element of `X_{-m,c}` whose
pairing with every cylinder test vanishes is zero. -/
theorem locCylUniq : LocCylUniq := by
  intro c m hc f hf
  have hUo : IsOpen (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  -- local integrability of `f` on the open interior of the cell
  have hloc : LocallyIntegrableOn (⇑f) (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)) volume := by
    refine (locallyIntegrableOn_iff hUo.isLocallyClosed).2 ?_
    intro k hkU hk
    obtain ⟨R, hR⟩ := hk.exists_bound_of_continuousOn continuous_snd.continuousOn
    have hG : MemLp (fun x : ℝ × ℝ => (((UnforcedLeray.B0579.band R).indicator
        (fun _ => (1 : ℝ)) x : ℝ) : ℂ)) 2 (UnforcedLeray.B0579.cellMeasure c (-(-m))) := by
      rw [neg_neg]
      exact (UnforcedLeray.B0579.memLp_indicator_band c m R).ofReal
    have hint := CutLimitAux.integrable_complex (Lp.memLp f) hG
    have hsub : k ⊆ UnforcedLeray.B0579.cell c := fun x hx =>
      ⟨Ioo_subset_Ico_self (hkU hx).1, mem_univ _⟩
    refine (IntegrableOn.mono_set hint hsub).congr_fun ?_ hk.isClosed.measurableSet
    intro x hx
    have hxb : x ∈ UnforcedLeray.B0579.band R := by
      have := hR x hx
      rw [Real.norm_eq_abs] at this
      exact this
    simp only [Set.indicator_of_mem hxb, Complex.ofReal_one, mul_one]
  -- the test-function identity for smooth compactly supported bumps
  have hint : ∀ g : ℝ × ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ) →
      ∫ x, g x • (⇑f) x = 0 := by
    intro g hg hcs hgU
    have h1 := hf _ (periodize_isCylTest hc hg hcs)
    have e1 : ∫ x in UnforcedLeray.B0579.cell c,
        (⇑f) x * (((UnforcedLeray.Gaussian.periodize c g x : ℝ)) : ℂ) =
        ∫ x in UnforcedLeray.B0579.cell c, ((g x : ℝ) : ℂ) * (⇑f) x := by
      refine setIntegral_congr_fun (UnforcedLeray.B0579.measurableSet_cell c) (fun x hx => ?_)
      rw [periodize_eqOn_cell hc hgU hx]
      ring
    have hzero : ∀ x, x ∉ UnforcedLeray.B0579.cell c → g x • (⇑f) x = 0 := by
      intro x hx
      have hg0 : g x = 0 := image_eq_zero_of_notMem_tsupport (fun h =>
        hx ⟨Ioo_subset_Ico_self (hgU h).1, mem_univ _⟩)
      simp [hg0]
    have e2 : ∫ x in UnforcedLeray.B0579.cell c, g x • (⇑f) x = ∫ x, g x • (⇑f) x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero
    have e3 : ∫ x in UnforcedLeray.B0579.cell c, ((g x : ℝ) : ℂ) * (⇑f) x =
        ∫ x in UnforcedLeray.B0579.cell c, g x • (⇑f) x := by
      refine setIntegral_congr_fun (UnforcedLeray.B0579.measurableSet_cell c) (fun x _ => ?_)
      rw [Complex.real_smul]
    rw [← e2, ← e3, ← e1]
    exact h1
  -- almost everywhere on the open interior
  have hae : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)),
      x ∈ Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ) → (⇑f) x = 0 :=
    hUo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc hint
  -- the boundary line `q = -c/2` is null
  have hnull : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), x ∉ ({-(c / 2)} ×ˢ (univ : Set ℝ)) := by
    rw [← measure_eq_zero_iff_ae_notMem]
    rw [Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, zero_mul]
  have h1 : ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)), (⇑f) x = 0 := by
    rw [ae_restrict_iff' (UnforcedLeray.B0579.measurableSet_cell c)]
    filter_upwards [hae, hnull] with x hx1 hx2 hxc
    by_cases hxU : x ∈ Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)
    · exact hx1 hxU
    · exfalso
      apply hx2
      have hx1' : x.1 = -(c / 2) := by
        by_contra hne
        exact hxU ⟨⟨lt_of_le_of_ne hxc.1.1 (Ne.symm hne), hxc.1.2⟩, mem_univ _⟩
      exact ⟨Set.mem_singleton_iff.2 hx1', mem_univ _⟩
  have hF : ∀ᵐ x ∂(UnforcedLeray.B0579.cellMeasure c (-m)), (⇑f) x = 0 :=
    (UnforcedLeray.B0579.cellMeasure_ac c (-m)).ae_le h1
  have h0 : ⇑(0 : Lp ℂ 2 (UnforcedLeray.B0579.cellMeasure c (-m))) =ᵐ[
      UnforcedLeray.B0579.cellMeasure c (-m)] 0 := Lp.coeFn_zero ℂ 2 _
  apply Lp.ext
  filter_upwards [hF, h0] with x hx1 hx2
  rw [hx2]
  exact hx1

end UnforcedLeray.Short.IIIa
