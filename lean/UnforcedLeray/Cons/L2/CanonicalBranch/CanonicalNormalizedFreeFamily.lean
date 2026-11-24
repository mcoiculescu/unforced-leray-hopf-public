import UnforcedLeray.Cons.L2.CanonicalBranch.CanonicalNormalizedEvolutionMild

/-!
# Evolution family and uniqueness for the normalized Gaussian free clock

Package the gauge-conjugated Gaussian diffusion as an evolution family, then use the existing
mild uniqueness theorem to identify the actual normalized transition with its bounded-`L₀`
Dyson evolution on a finite turnover block.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.B0123 UnforcedLeray.Evolution

/-- The gauge-conjugated Gaussian diffusion as an evolution family on a finite turnover block. -/
def normalizedTurnoverFreeFamily (lam κ : ℂ) (R b₀ : ℝ)
    (hb₀ : 0 < b₀) (hR : b₀ ≤ R) :
    EvolutionFamily XG 0 (R - b₀) where
  U := fun t s => normalizedTurnoverFree lam κ R t s
  U_diag t ht := by
    have hθ : 0 < R - t := by linarith [ht.2, hb₀]
    ext x
    simp [normalizedTurnoverFree, freeU, expD_zero,
      gauge_mul_gaugeInv (lam := lam) (κ := κ) hθ]
  U_comp s r t hs hsr hrt ht := by
    have hrθ : 0 < R - r := by linarith [hrt, ht, hb₀]
    have hγ :
        (gauge lam κ (R - t) * gaugeInv lam κ (R - r)) *
          (gauge lam κ (R - r) * gaugeInv lam κ (R - s)) =
        gauge lam κ (R - t) * gaugeInv lam κ (R - s) := by
      calc
        _ = gauge lam κ (R - t) *
              (gaugeInv lam κ (R - r) * gauge lam κ (R - r)) *
              gaugeInv lam κ (R - s) := by ring
        _ = gauge lam κ (R - t) * 1 * gaugeInv lam κ (R - s) := by
              rw [gaugeInv_mul_gauge (lam := lam) (κ := κ) hrθ]
        _ = _ := by ring
    have hfree := (freeFam (-R) (-b₀) (by linarith)).U_comp
      (s := s - R) (r := r - R) (t := t - R)
      (by linarith) (by linarith) (by linarith) (by linarith)
    have hfree' : freeU (t - R) (r - R) ∘L freeU (r - R) (s - R) =
        freeU (t - R) (s - R) := by simpa [freeFam] using hfree
    calc
      ((gauge lam κ (R - t) * gaugeInv lam κ (R - r)) •
          freeU (t - R) (r - R)) ∘L
        ((gauge lam κ (R - r) * gaugeInv lam κ (R - s)) •
          freeU (r - R) (s - R)) =
          ((gauge lam κ (R - t) * gaugeInv lam κ (R - r)) *
            (gauge lam κ (R - r) * gaugeInv lam κ (R - s))) •
              (freeU (t - R) (r - R) ∘L freeU (r - R) (s - R)) := by
                rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]
      _ = (gauge lam κ (R - t) * gaugeInv lam κ (R - s)) •
            freeU (t - R) (s - R) := by rw [hγ, hfree']
  U_cont x := by
    let K := freeFam (-R) (-b₀) (by linarith [hb₀])
    have hgamma : ContinuousOn
        (fun p : ℝ × ℝ => gauge lam κ (R - p.2) * gaugeInv lam κ (R - p.1))
        {p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ R - b₀} := by
      have h1 : ContinuousOn (fun p : ℝ × ℝ => gauge lam κ (R - p.2))
          {p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ R - b₀} := by
        apply (continuousOn_gauge lam κ).comp
          (continuousOn_const.sub continuous_snd.continuousOn)
        intro p hp
        have hp' : b₀ ≤ R - p.2 := by linarith [hp.2.2]
        exact mem_Ioi.mpr (lt_of_lt_of_le hb₀ hp')
      have h2 : ContinuousOn (fun p : ℝ × ℝ => gaugeInv lam κ (R - p.1))
          {p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ R - b₀} := by
        unfold gaugeInv
        refine ContinuousOn.mul ?_ ?_
        · have harg : Continuous (fun p : ℝ × ℝ => -(lam * ((R - p.1 : ℝ) : ℂ))) := by
            fun_prop
          exact (Complex.continuous_exp.comp harg).continuousOn
        · have hbase : Continuous (fun p : ℝ × ℝ => ((R - p.1 : ℝ) : ℂ)) := by fun_prop
          exact ContinuousOn.cpow hbase.continuousOn continuousOn_const
            (fun p hp => Complex.ofReal_mem_slitPlane.mpr (by
              have hp' : b₀ ≤ R - p.1 := by linarith [hp.2.1, hp.2.2]
              exact lt_of_lt_of_le hb₀ hp'))
      exact h1.mul h2
    have hfree : ContinuousOn
        (fun p : ℝ × ℝ => freeU (p.2 - R) (p.1 - R) x)
        {p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ R - b₀} := by
      let tri : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ R - b₀}
      have hlog : ContinuousOn
          (fun p : ℝ × ℝ => Real.log (-(p.1 - R)) - Real.log (-(p.2 - R))) tri := by
        have hleft : ContinuousOn (fun p : ℝ × ℝ => -(p.1 - R)) tri :=
          (continuous_fst.sub continuous_const).neg.continuousOn
        have hright : ContinuousOn (fun p : ℝ × ℝ => -(p.2 - R)) tri :=
          (continuous_snd.sub continuous_const).neg.continuousOn
        have hleftpos : ∀ p ∈ tri, 0 < -(p.1 - R) := by
          intro p hp
          have hp' : b₀ ≤ R - p.1 := by linarith [hp.2.1, hp.2.2]
          have hpos : 0 < R - p.1 := lt_of_lt_of_le hb₀ hp'
          convert hpos using 1 <;> ring
        have hrightpos : ∀ p ∈ tri, 0 < -(p.2 - R) := by
          intro p hp
          have hp' : b₀ ≤ R - p.2 := by linarith [hp.2.2]
          have hpos : 0 < R - p.2 := lt_of_lt_of_le hb₀ hp'
          convert hpos using 1 <;> ring
        exact (ContinuousOn.log hleft fun p hp => (hleftpos p hp).ne' ).sub
          (ContinuousOn.log hright fun p hp => (hrightpos p hp).ne')
      change ContinuousOn (fun p : ℝ × ℝ =>
        expD (Real.log (-(p.1 - R)) - Real.log (-(p.2 - R))) x) tri
      exact (continuous_expD_apply x).comp_continuousOn hlog
    have hprod := hgamma.smul hfree
    have hpoint :
        (fun p : ℝ × ℝ => normalizedTurnoverFree lam κ R p.2 p.1 x) =
          (fun p : ℝ × ℝ => (gauge lam κ (R - p.2) * gaugeInv lam κ (R - p.1)) •
            (freeU (p.2 - R) (p.1 - R) x)) := by
      funext p
      simp [normalizedTurnoverFree]
    rw [hpoint]
    change ContinuousOn
      (fun p : ℝ × ℝ =>
        (gauge lam κ (R - p.2) * gaugeInv lam κ (R - p.1)) •
          (freeU (p.2 - R) (p.1 - R) x))
      {p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ R - b₀}
    exact hprod
  U_bdd := by
    let Kset : Set (ℝ × ℝ) := Set.Icc 0 (R - b₀) ×ˢ Set.Icc 0 (R - b₀)
    have hgamma : ContinuousOn
        (fun p : ℝ × ℝ => gauge lam κ (R - p.2) * gaugeInv lam κ (R - p.1)) Kset := by
      have h1 : ContinuousOn (fun p : ℝ × ℝ => gauge lam κ (R - p.2)) Kset := by
        apply (continuousOn_gauge lam κ).comp
          (continuousOn_const.sub continuous_snd.continuousOn)
        intro p hp
        have hp' : b₀ ≤ R - p.2 := by linarith [hp.2.2]
        exact mem_Ioi.mpr (lt_of_lt_of_le hb₀ hp')
      have h2 : ContinuousOn (fun p : ℝ × ℝ => gaugeInv lam κ (R - p.1)) Kset := by
        unfold gaugeInv
        refine ContinuousOn.mul ?_ ?_
        · have harg : Continuous (fun p : ℝ × ℝ => -(lam * ((R - p.1 : ℝ) : ℂ))) := by
            fun_prop
          exact (Complex.continuous_exp.comp harg).continuousOn
        · have hbase : Continuous (fun p : ℝ × ℝ => ((R - p.1 : ℝ) : ℂ)) := by fun_prop
          exact ContinuousOn.cpow hbase.continuousOn continuousOn_const
            (fun p hp => Complex.ofReal_mem_slitPlane.mpr (by
              have hp' : b₀ ≤ R - p.1 := by linarith [hp.1.2]
              exact lt_of_lt_of_le hb₀ hp'))
      exact h1.mul h2
    have hcomp : IsCompact Kset := isCompact_Icc.prod isCompact_Icc
    obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hgamma.norm
    refine ⟨M, fun s t hs hst ht => ?_⟩
    have hT : 0 ≤ R - b₀ := by linarith [hR]
    have hp : (s, t) ∈ Kset := ⟨⟨hs, hst.trans ht⟩, ⟨le_trans hs hst, ht⟩⟩
    have hfree := norm_freeU_le (t - R) (s - R)
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (0, 0)
      ⟨⟨le_rfl, hT⟩, ⟨le_rfl, hT⟩⟩)
    have hMpoint : ‖gauge lam κ (R - t) * gaugeInv lam κ (R - s)‖ ≤ M := by
      simpa using hM (s, t) hp
    calc
      ‖normalizedTurnoverFree lam κ R t s‖ =
          ‖gauge lam κ (R - t) * gaugeInv lam κ (R - s)‖ *
            ‖freeU (t - R) (s - R)‖ := by simp [normalizedTurnoverFree, norm_smul]
      _ ≤ M * 1 := mul_le_mul hMpoint hfree (norm_nonneg _) hM0
      _ = M := by ring

/-- Duhamel uniqueness identifies the actual normalized transition with the bounded-`L₀` Dyson
family over the gauge-conjugated Gaussian free evolution. -/
theorem actualNormalizedTurnoverEvolution_eq_dyson
    {lam κ : ℂ} {R b₀ s t : ℝ} (hb₀ : 0 < b₀)
    (hs : 0 ≤ s) (hst : s ≤ t) (htt : t ≤ R - b₀) (x : XG) :
    actualNormalizedTurnoverEvolution lam κ R t s x =
      (dyson (normalizedTurnoverFreeFamily lam κ R b₀ hb₀ (by linarith [htt, hs]))
        (pertL0 0 (R - b₀))).U t s x := by
  have hR : b₀ ≤ R := by linarith [htt, hs]
  let V := normalizedTurnoverFreeFamily lam κ R b₀ hb₀ hR
  let A := pertL0 (0 : ℝ) (R - b₀)
  let z : ℝ → XG := fun r => actualNormalizedTurnoverEvolution lam κ R r s x
  have hScont : ContinuousOn (fun r => S (R - r) (R - s) x)
      (Icc s (R - b₀)) := by
    have htheta : 0 < b₀ := hb₀
    have hmap : ContinuousOn (fun r : ℝ => R - r) (Icc s (R - b₀)) :=
      (continuous_const.sub continuous_id).continuousOn
    have hmaps : MapsTo (fun r : ℝ => R - r) (Icc s (R - b₀))
        (Icc b₀ (R - s)) := by
      intro r hr
      constructor <;> linarith [hr.1, hr.2, hb₀]
    exact (continuousOn_S_left (θ₁ := R - s) hb₀ x).comp hmap hmaps
  have hgamma : ContinuousOn (fun r =>
      gauge lam κ (R - r) * gaugeInv lam κ (R - s)) (Icc s (R - b₀)) := by
    have hmap : MapsTo (fun r : ℝ => R - r) (Icc s (R - b₀)) (Ioi 0) := by
      intro r hr
      exact mem_Ioi.mpr (by linarith [hr.2, hb₀])
    have h := (continuousOn_gauge lam κ).comp
      ((continuous_const.sub continuous_id).continuousOn) hmap
    exact h.mul continuousOn_const
  have hzc : ContinuousOn z (Icc s (R - b₀)) := by
    exact hgamma.smul hScont
  have hdiag : z s = x := by
    dsimp [z, actualNormalizedTurnoverEvolution]
    have htheta : 0 < R - s := by linarith [htt, hst, hb₀]
    rw [S_self htheta]
    simp [gauge_mul_gaugeInv (lam := lam) (κ := κ) htheta]
  have hmild : ∀ r ∈ Icc s (R - b₀),
      z r = V.U r s (z s) + ∫ u in s..r, V.U r u (A.A u (z u)) := by
    intro r hr
    have hactual := actualNormalizedTurnoverEvolution_mild (lam := lam) (κ := κ) hb₀ hs hr.1 hr.2 x
    rw [hdiag]
    simpa [V, normalizedTurnoverFreeFamily, A, pertL0] using hactual
  have hmild' : ∀ r ∈ Icc s (R - b₀),
      z r = V.U r s (z s) + ∫ u in s..r, V.U r u (A.A u (z u) + 0) := by
    intro r hr
    simpa using hmild r hr
  have hunique := Evolution.mild_unique (F := V) (A := A) hs hzc integrableOn_zero hmild'
  have htmem : t ∈ Icc s (R - b₀) := ⟨hst, htt⟩
  simpa [z, V, A, hdiag] using hunique t htmem

end UnforcedLeray.Cons.G3b
