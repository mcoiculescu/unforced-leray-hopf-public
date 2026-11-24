import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.Reg

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/2`: Friedrichs' lemma at every level (`StFriedJet`)

Source of record: `the November 2 reference manuscript` lines 3060-3071 (the
transport term of the regularized adjoint; the remainder of the regularization is of order zero
uniformly in `n`).

`R_n = stFriedRem v n φ = stFried n v φ` (`(∂_lρ_n) ⋆ φ = ∂_l(ρ_n ⋆ φ)`, `CellConvDeriv`); the
derivation rule `StFriedDeriv` and `st_word_leibniz` give
`∂^u R_n = Σ_{p ∈ stSplits u} stFried n (∂^{p.1} v) (D p.2)` for `|u| ≤ k`, and each term is bounded
by `StFriedZero` with the Lipschitz constant `Av (|p.1| + 1)` of `∂^{p.1} v` (`StVelWords`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The triangle inequality for a finite sum in `X_{-m,c}`. -/
theorem st_list_sum_memLp_le {c m : ℝ} {ι : Type*} (L : List ι) (B : ι → ℝ × ℝ → ℂ)
    (b : ι → ℝ)
    (hB : ∀ i ∈ L, MemLp (B i) 2 (B0579.cellMeasure c (-m)) ∧ (xNorm c (-m) (B i)).toReal ≤ b i) :
    MemLp (fun x => (L.map fun i => B i x).sum) 2 (B0579.cellMeasure c (-m)) ∧
      (xNorm c (-m) (fun x => (L.map fun i => B i x).sum)).toReal ≤ (L.map b).sum := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact ⟨MemLp.zero', by simp [xNorm]⟩
  | cons i L ih =>
    obtain ⟨hm1, hb1⟩ := hB i (by simp)
    obtain ⟨hm2, hb2⟩ := ih fun j hj => hB j (by simp [hj])
    simp only [List.map_cons, List.sum_cons]
    refine ⟨hm1.add hm2, ?_⟩
    have h := eLpNorm_add_le hm1.1 hm2.1 (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hne1 := hm1.eLpNorm_lt_top.ne
    have hne2 := hm2.eLpNorm_lt_top.ne
    calc (xNorm c (-m) (fun x => B i x + (L.map fun i => B i x).sum)).toReal
        ≤ (xNorm c (-m) (B i) +
            xNorm c (-m) (fun x => (L.map fun i => B i x).sum)).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hne1, hne2⟩) h
      _ = (xNorm c (-m) (B i)).toReal +
            (xNorm c (-m) (fun x => (L.map fun i => B i x).sum)).toReal :=
          ENNReal.toReal_add hne1 hne2
      _ ≤ b i + (L.map b).sum := add_le_add hb1 hb2

/-- `R_n = stFried n v φ`. -/
theorem st_friedRem_eq (hCD : CellConvDeriv) {c m : ℝ} (hc : 0 < c)
    (v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) {φ : ℝ × ℝ → ℂ}
    (hφp : ∀ x : ℝ × ℝ, φ (x.1 + c, x.2) = φ x) (hφm : MemLp φ 2 (B0579.cellMeasure c (-m)))
    (n : ℕ) : stFriedRem v n φ = stFried n (stVel v) φ := by
  have h := (hCD c m (molKer n) φ hc (st_molKer_contDiff n) (st_molKer_hasCompactSupport n)
    hφp hφm).2.2
  funext x
  unfold stFriedRem stFried stTrans stGrad
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hl : pdCx l (cellMoll n φ) x = cellConv (B0579.pd l (molKer n)) φ x := congrFun (h [l]) x
  rw [hl]
  rfl

/-- **`StFriedJet` from its leaves**. -/
theorem stFriedJet_of (hCD : CellConvDeriv) (hZ : StFriedZero) (hD : StFriedDeriv)
    (hVW : StVelWords) : StFriedJet := by
  intro c m k Av hc
  obtain ⟨C₀, hC₀0, hC₀⟩ := hZ c m hc
  have hL0 : 0 ≤ ∑ i ∈ Finset.range (k + 2), |Av i| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨2 ^ k * (C₀ * ∑ i ∈ Finset.range (k + 2), |Av i|), by positivity, ?_⟩
  intro v hv φ D M hM hJ hDM n u hu
  have hφp := st_jet_periodic hJ
  have hφm := st_jet_memX hJ
  -- the coefficients `∂^{u'} v`
  have hcoef : ∀ u' : List (Fin 2),
      (∀ l, ContDiff ℝ ∞ (stCoefWord u' (stVel v) l)) ∧
      (∀ l (x : ℝ × ℝ), stCoefWord u' (stVel v) l (x.1 + c, x.2) = stCoefWord u' (stVel v) l x) ∧
      (∃ A : ℝ, ∀ l (x : ℝ × ℝ), |stCoefWord u' (stVel v) l x| ≤ A ∧
        ∀ j : Fin 2, |B0579.pd j (stCoefWord u' (stVel v) l) x| ≤ A) := by
    intro u'
    refine ⟨fun l => (hVW c v Av hv u' l).1, fun l x => (hVW c v Av hv u' l).2.1 x,
      |Av u'.length| + |Av (u'.length + 1)|, fun l x => ⟨?_, fun j => ?_⟩⟩
    · exact ((hVW c v Av hv u' l).2.2.1 x).trans
        ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _)))
    · exact ((hVW c v Av hv (j :: u') l).2.2.1 x).trans
        ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _)))
  -- the word Leibniz expansion
  have hexp := st_word_leibniz (stFried n) (stVel v) D k
    (fun u' u'' hu'' => (hD c m n (stCoefWord u' (stVel v)) (D u'') hc (hcoef u').1 (hcoef u').2.1
      (hcoef u').2.2 (hJ.periodic u'' hu'') (hJ.memX u'' hu'')).1)
    (fun j u' u'' hu'' => (hD c m n (stCoefWord u' (stVel v)) (D u'') hc (hcoef u').1
      (hcoef u').2.1 (hcoef u').2.2 (hJ.periodic u'' hu''.le) (hJ.memX u'' hu''.le)).2 j
      (D (j :: u'')) (hJ.periodic (j :: u'') (by simpa using hu''))
      (hJ.memX (j :: u'') (by simpa using hu'')) (hJ.deriv j u'' hu'')) u hu
  have hR : stFriedRem v n φ = stFried n (stVel v) (D []) := by
    rw [hJ.base]
    exact st_friedRem_eq hCD hc v hφp hφm n
  rw [hR, hexp]
  -- the bound of each term
  have hterm : ∀ p ∈ stSplits u, MemLp (stFried n (stCoefWord p.1 (stVel v)) (D p.2)) 2
      (B0579.cellMeasure c (-m)) ∧
      (xNorm c (-m) (stFried n (stCoefWord p.1 (stVel v)) (D p.2))).toReal ≤
        C₀ * (∑ i ∈ Finset.range (k + 2), |Av i|) * M := by
    intro p hp
    have hp1 := (st_splits_length_le hp).1
    have hp2 : p.2.length ≤ k := (st_splits_length_le hp).2.trans hu
    obtain ⟨hm, hb⟩ := hC₀ n (stCoefWord p.1 (stVel v)) (Av p.1.length) (Av (p.1.length + 1))
      (D p.2) (fun l => (hVW c v Av hv p.1 l).1.continuous)
      (fun l x => (hVW c v Av hv p.1 l).2.2.1 x) (fun l x y => (hVW c v Av hv p.1 l).2.2.2 x y)
      (hJ.periodic p.2 hp2) (hJ.memX p.2 hp2)
    refine ⟨hm, hb.trans ?_⟩
    have hDp : (xNorm c (-m) (D p.2)).toReal ≤ M := ENNReal.toReal_le_of_le_ofReal hM (hDM p.2 hp2)
    have hAv : Av (p.1.length + 1) ≤ ∑ i ∈ Finset.range (k + 2), |Av i| :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |Av i|)
        (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (by omega)))
    have hD0 : 0 ≤ (xNorm c (-m) (D p.2)).toReal := ENNReal.toReal_nonneg
    calc C₀ * Av (p.1.length + 1) * (xNorm c (-m) (D p.2)).toReal
        ≤ C₀ * (∑ i ∈ Finset.range (k + 2), |Av i|) * (xNorm c (-m) (D p.2)).toReal :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAv hC₀0) hD0
      _ ≤ C₀ * (∑ i ∈ Finset.range (k + 2), |Av i|) * M :=
          mul_le_mul_of_nonneg_left hDp (mul_nonneg hC₀0 hL0)
  obtain ⟨hm, hb⟩ := st_list_sum_memLp_le (stSplits u)
    (fun p => stFried n (stCoefWord p.1 (stVel v)) (D p.2))
    (fun _ => C₀ * (∑ i ∈ Finset.range (k + 2), |Av i|) * M) hterm
  refine ⟨hm, hb.trans ?_⟩
  rw [List.map_const', List.sum_replicate, st_splits_card, nsmul_eq_mul]
  have h2 : ((2 ^ u.length : ℕ) : ℝ) ≤ 2 ^ k := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) hu
  have h3 : 0 ≤ C₀ * (∑ i ∈ Finset.range (k + 2), |Av i|) * M := by positivity
  calc ((2 ^ u.length : ℕ) : ℝ) * (C₀ * (∑ i ∈ Finset.range (k + 2), |Av i|) * M)
      ≤ 2 ^ k * (C₀ * (∑ i ∈ Finset.range (k + 2), |Av i|) * M) :=
        mul_le_mul_of_nonneg_right h2 h3
    _ = 2 ^ k * (C₀ * ∑ i ∈ Finset.range (k + 2), |Av i|) * M := by ring

end UnforcedLeray.Short.IIIa
