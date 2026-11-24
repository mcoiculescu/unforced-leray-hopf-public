import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Abstract

/-!
# `PartIII-a:T21/2/7/2/1/1/6`: `AdjTimeJetsOf` from its leaves

Source: `the November 2 reference manuscript` (SP) lines 3060-3061 (the
reverse-time adjoint and its equation), 3052-3058 (the adjoint localized interaction), 270-288 and
2866-2870 (the train and its weighted jets).

* `adjTimeJetsOf_of`: the jets are `tjSeq` for the operator family `adjLop tr`
  (`tjSeq_spec`, `Abstract.lean`), from `AdjHkAllOf`, `XDerivUpgrade`, `AdjTimeDerivBase`,
  `AdjLopSmooth`, `AdjLopDeriv`, `AdjHkAllLinear`, `HasXDerivOnLinear`;
* `xDerivUpgrade_of`: from `XDerivOfTested` and `TestedOfXDeriv`, by induction on the word
  (`∫ D(j :: w) ψ = -∫ D w ∂_jψ`);
* `adjTimeDerivBase_of`: from `XDerivOfTested`, `KerVelIsBS`, `AdjLopTested` (with
  `AdjTestedDeriv`) and `AdjLopSmooth` (continuity of `L^{(0)}φ` in `X_{-m,c}`);
* `adjHkAll_shift` (proved): the fields `D (w ++ u)` of `∂^u f`;
* `adjLopSmooth_of`, `adjLopDeriv_of`: from the coefficient leaves (`AdjHkAllCoeffMul`,
  `CoeffMulDeriv`, `TrainVCoeff`), the kernel leaves (`AdjHkAllKerMul`, `KerMulDeriv`,
  `TrainECoeff`) and linearity.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## The top assembly -/

/-- **`AdjTimeJetsOf` from its leaves.** -/
theorem adjTimeJetsOf_of (m : ℝ) (hJ : AdjHkAllOf) (hU : XDerivUpgrade)
    (hB : AdjTimeDerivBase m) (hS : AdjLopSmooth m) (hD : AdjLopDeriv m)
    (hL : AdjHkAllLinear) (hX : HasXDerivOnLinear) : AdjTimeJetsOf m := by
  intro ν hν hν1 tr hBdd hJets t s ht hts g φ hφ hTD hk
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  refine ⟨tjSeq (jetOf (ν ^ (-2 : ℝ)) m (Ioo t s)) (adjLop tr) φ, tjSeq_zero _ _ _, ?_⟩
  exact tjSeq_spec (adjLop tr) φ hL hX (hJ _ m _ φ hc hk)
    (fun i f D hfD => hS ν hν hν1 tr hBdd hJets t s ht i f D hfD)
    (fun i f f' D D' h1 h2 h3 => hD ν hν hν1 tr hBdd hJets t s ht i f f' D D' h1 h2 h3)
    (fun D hDφ => hB ν hν hν1 tr hBdd hJets t s ht hts g φ hφ hTD D hDφ)
    (fun f f' D D' h1 h2 h3 => hU _ m t s f f' D D' hc h1 h2 h3)

/-! ## The upgrade -/

/-- **`XDerivUpgrade` from the two tested-derivative leaves.** -/
theorem xDerivUpgrade_of (hP : XDerivOfTested) (hT : TestedOfXDeriv) : XDerivUpgrade := by
  intro c m a b f f' D D' hc hD hD' hff' w
  have hmD : ∀ u : List (Fin 2), ∀ r ∈ Ioo a b, MemLp (D r u) 2 (B0579.cellMeasure c (-m)) :=
    fun u r hr => (hD.1 r hr u.length).memX u le_rfl
  have hmD' : ∀ u : List (Fin 2), ∀ r ∈ Ioo a b, MemLp (D' r u) 2 (B0579.cellMeasure c (-m)) :=
    fun u r hr => (hD'.1 r hr u.length).memX u le_rfl
  induction w with
  | nil =>
    exact hasXDerivOn_congr hff' (fun r hr => ((hD.1 r hr 0).base).symm)
      (fun r hr => ((hD'.1 r hr 0).base).symm)
  | cons j w ih =>
    refine hP c m a b (fun r => D r (j :: w)) (fun r => D' r (j :: w)) hc (hmD _) (hmD' _)
      (fun r hr => hD'.2 (j :: w) r hr) (fun ψ hψ r hr => ?_)
    have hw := hT c m a b (fun r => D r w) (fun r => D' r w) hc (hmD w) (hmD' w) ih
      (B0579.pd j ψ) (hψ.pd j) r hr
    have hibp : ∀ r' ∈ Ioo a b, ∫ x in B0579.cell c, D r' (j :: w) x * (ψ x : ℂ) =
        -∫ x in B0579.cell c, D r' w x * (B0579.pd j ψ x : ℂ) := by
      intro r' hr'
      have hd := (hD.1 r' hr' (w.length + 1)).deriv j w (Nat.lt_succ_self _)
      rw [hd.2 ψ hψ, neg_neg]
    have hibp' : ∫ x in B0579.cell c, D' r (j :: w) x * (ψ x : ℂ) =
        -∫ x in B0579.cell c, D' r w x * (B0579.pd j ψ x : ℂ) := by
      have hd := (hD'.1 r hr (w.length + 1)).deriv j w (Nat.lt_succ_self _)
      rw [hd.2 ψ hψ, neg_neg]
    show HasDerivAt (fun r' => ∫ x in B0579.cell c, D r' (j :: w) x * (ψ x : ℂ))
      (∫ x in B0579.cell c, D' r (j :: w) x * (ψ x : ℂ)) r
    rw [hibp']
    refine hw.neg.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hr] with r' hr'
    exact hibp r' hr'

/-! ## The first age derivative -/

/-- **`AdjTimeDerivBase` from its leaves.** -/
theorem adjTimeDerivBase_of (m : ℝ) (hP : XDerivOfTested) (hK : KerVelIsBS)
    (hT : AdjLopTested m) (hS : AdjLopSmooth m) : AdjTimeDerivBase m := by
  intro ν hν hν1 tr hBdd hJets t s ht hts g φ hφ hTD D hD
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hc1 : (1 : ℝ) ≤ ν ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  obtain ⟨D', hD'⟩ := hS ν hν hν1 tr hBdd hJets t s ht 0 φ D hD
  refine hP _ m t s φ (fun r => adjLop tr 0 r (D r)) hc (fun r hr => hD.memLp hr)
    (fun r hr => hD'.memLp hr) (fun r hr => ?_) (fun ψ hψ r hr => ?_)
  · have h := hD'.2 [] r hr
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r' hr'
    rw [(hD'.1 r' hr' 0).base, (hD'.1 r hr 0).base]
  · obtain ⟨-, hder⟩ := hTD ψ (kerVel (ν ^ (-2 : ℝ)) ψ) hψ (hK _ hc1 ψ hψ)
    have h2 := (hder r ⟨hr.1.le, hr.2.le⟩).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
    have h3 := hT ν hν hν1 tr hBdd r (lt_of_le_of_lt ht hr.1) (φ r) (D r) (hD.1 r hr 2) ψ hψ
    show HasDerivAt (fun r' => ∫ x in B0579.cell (ν ^ (-2 : ℝ)), φ r' x * (ψ x : ℂ))
      (∫ x in B0579.cell (ν ^ (-2 : ℝ)), adjLop tr 0 r (D r) x * (ψ x : ℂ)) r
    rw [h3]
    exact h2

/-! ## The operators -/

/-- The fields `D (w ++ u)` of `∂^u f`. -/
theorem adjHkAll_shift {c m : ℝ} {I : Set ℝ} {f : ℝ → ℝ × ℝ → ℂ}
    {D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ} (h : AdjHkAll c m I f D) (u : List (Fin 2)) :
    AdjHkAll c m I (fun r => D r u) (fun r w => D r (w ++ u)) := by
  refine ⟨fun r hr k => ?_, fun w r hr => h.2 (w ++ u) r hr⟩
  exact { base := rfl
          periodic := fun w _ x => (h.1 r hr (w ++ u).length).periodic (w ++ u) le_rfl x
          memX := fun w _ => (h.1 r hr (w ++ u).length).memX (w ++ u) le_rfl
          deriv := fun j w _ =>
            (h.1 r hr ((w ++ u).length + 1)).deriv j (w ++ u) (Nat.lt_succ_self _) }

theorem memLp_lin {μ : Measure (ℝ × ℝ)} {u v : ℝ × ℝ → ℂ} (α β : ℂ) (hu : MemLp u 2 μ)
    (hv : MemLp v 2 μ) : MemLp (fun x => α * u x + β * v x) 2 μ :=
  (hu.const_mul α).add (hv.const_mul β)

theorem memLp_ite_zero {μ : Measure (ℝ × ℝ)} (p : Prop) [Decidable p] {u : ℝ × ℝ → ℂ}
    (hu : MemLp u 2 μ) : MemLp (fun x => if p then u x else 0) 2 μ := by
  by_cases h : p
  · simpa [h] using hu
  · simp [h]

/-- **`AdjLopSmooth` from its leaves.** -/
theorem adjLopSmooth_of (m : ℝ) (hL : AdjHkAllLinear) (hC : AdjHkAllCoeffMul)
    (hK : AdjHkAllKerMul m) (hV : TrainVCoeff m) (hE : TrainECoeff m) : AdjLopSmooth m := by
  intro ν hν hν1 tr hBdd hJets a b ha i f D hD
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hc1 : (1 : ℝ) ≤ ν ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  have hlin := (hL (ν ^ (-2 : ℝ)) m (Ioo a b)).2
  have hzero := (hL (ν ^ (-2 : ℝ)) m (Ioo a b)).1
  have hdiff := hlin _ _ _ _ 1 1 (adjHkAll_shift hD [0, 0]) (adjHkAll_shift hD [1, 1])
  have htr : ∀ l : Fin 2, AdjHkAll (ν ^ (-2 : ℝ)) m (Ioo a b)
      (fun r x => ((vJet tr i r x l : ℝ) : ℂ) * D r [l] x)
      (fun r => leib (fun x => vJet tr i r x l) (fun w => D r (w ++ [l]))) := fun l =>
    hC _ m (Ioo a b) (fun r x => vJet tr i r x l) (fun r => D r [l]) (fun r w => D r (w ++ [l]))
      hc (hV ν hν hν1 tr hJets a b ha i l).1 (adjHkAll_shift hD [l])
  have hD0 : AdjHkAll (ν ^ (-2 : ℝ)) m (Ioo a b) (fun r => D r []) D :=
    adjHkAll_congr hD (fun r hr => ((hD.1 r hr 0).base).symm)
  have hker := hK _ (Ioo a b) (fun r l x => eJet tr i r l x) (fun r => D r []) D hc1
    (hE ν hν hν1 tr hJets a b ha i).1 hD0
  obtain ⟨DQ, hQ⟩ : ∃ DQ, AdjHkAll (ν ^ (-2 : ℝ)) m (Ioo a b)
      (fun r x => if i = 0 then (ν : ℂ) * (D r [0, 0] x + D r [1, 1] x) else 0) DQ := by
    by_cases hi : i = 0
    · refine ⟨_, adjHkAll_congr (hlin _ _ _ _ (ν : ℂ) 0 hdiff hzero) (fun r _ => ?_)⟩
      funext x
      simp [hi]
    · refine ⟨_, adjHkAll_congr hzero (fun r _ => ?_)⟩
      funext x
      simp [hi]
  have hT := hlin _ _ _ _ 1 1 (htr 0) (htr 1)
  have hQT := hlin _ _ _ _ 1 1 hQ hT
  have hall := hlin _ _ _ _ (-1) 1 hQT hker
  refine ⟨_, adjHkAll_congr hall (fun r _ => ?_)⟩
  funext x
  simp only [adjLop, Fin.sum_univ_two]
  ring

/-- The diffusion part `[i = 0] ν (E [0,0] + E [1,1])` of `adjLop`. -/
def lopQ (ν : ℝ) (i : ℕ) (E : ℝ → List (Fin 2) → ℝ × ℝ → ℂ) (r : ℝ) (x : ℝ × ℝ) : ℂ :=
  if i = 0 then (ν : ℂ) * (E r [0, 0] x + E r [1, 1] x) else 0

/-- The transport part `∂_r^n v_l · E [l]` of `adjLop`. -/
def lopT {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (n : ℕ) (l : Fin 2)
    (E : ℝ → List (Fin 2) → ℝ × ℝ → ℂ) (r : ℝ) (x : ℝ × ℝ) : ℂ :=
  ((vJet tr n r x l : ℝ) : ℂ) * E r [l] x

/-- The kernel part `K_c^T(∂_r^n∇E · E [])` of `adjLop`. -/
def lopK {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (n : ℕ)
    (E : ℝ → List (Fin 2) → ℝ × ℝ → ℂ) (r : ℝ) : ℝ × ℝ → ℂ :=
  kerAdj c (fun l y => ((eJet tr n r l y : ℝ) : ℂ) * E r [] y)

theorem adjLop_eq_parts {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (n : ℕ)
    (E : ℝ → List (Fin 2) → ℝ × ℝ → ℂ) (r : ℝ) (x : ℝ × ℝ) :
    adjLop tr n r (E r) x = -1 * (1 * lopQ ν n E r x +
      1 * (1 * lopT tr n 0 E r x + 1 * lopT tr n 1 E r x)) + 1 * lopK tr n E r x := by
  simp only [adjLop, lopQ, lopT, lopK, Fin.sum_univ_two]
  ring

/-- **`AdjLopDeriv` from its leaves.** -/
theorem adjLopDeriv_of (m : ℝ) (hX : HasXDerivOnLinear)
    (hC : AdjHkAllCoeffMul) (hK : AdjHkAllKerMul m) (hCD : CoeffMulDeriv) (hKD : KerMulDeriv m)
    (hV : TrainVCoeff m) (hE : TrainECoeff m) : AdjLopDeriv m := by
  intro ν hν hν1 tr hBdd hJets a b ha i f f' D D' hD hD' hDD'
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hc1 : (1 : ℝ) ≤ ν ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  have hmD : ∀ u : List (Fin 2), ∀ r ∈ Ioo a b,
      MemLp (D r u) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    fun u r hr => (hD.1 r hr u.length).memX u le_rfl
  have hmD' : ∀ u : List (Fin 2), ∀ r ∈ Ioo a b,
      MemLp (D' r u) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    fun u r hr => (hD'.1 r hr u.length).memX u le_rfl
  -- memberships of the parts
  have hTm : ∀ (n : ℕ) (E : ℝ → List (Fin 2) → ℝ × ℝ → ℂ) (g : ℝ → ℝ × ℝ → ℂ),
      AdjHkAll (ν ^ (-2 : ℝ)) m (Ioo a b) g E → ∀ l : Fin 2, ∀ r ∈ Ioo a b,
      MemLp (lopT tr n l E r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
    intro n E g hg l r hr
    exact (hC _ m (Ioo a b) (fun r x => vJet tr n r x l) (fun r => E r [l])
      (fun r w => E r (w ++ [l])) hc (hV ν hν hν1 tr hJets a b ha n l).1
      (adjHkAll_shift hg [l])).memLp hr
  have hKm : ∀ (n : ℕ) (E : ℝ → List (Fin 2) → ℝ × ℝ → ℂ) (g : ℝ → ℝ × ℝ → ℂ),
      AdjHkAll (ν ^ (-2 : ℝ)) m (Ioo a b) g E → ∀ r ∈ Ioo a b,
      MemLp (lopK tr n E r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
    intro n E g hg r hr
    have hE0 : AdjHkAll (ν ^ (-2 : ℝ)) m (Ioo a b) (fun r => E r []) E :=
      adjHkAll_congr hg (fun r hr => ((hg.1 r hr 0).base).symm)
    exact (hK _ (Ioo a b) (fun r l x => eJet tr n r l x) (fun r => E r []) E hc1
      (hE ν hν hν1 tr hJets a b ha n).1 hE0).memLp hr
  have hQm : ∀ (E : ℝ → List (Fin 2) → ℝ × ℝ → ℂ), (∀ u, ∀ r ∈ Ioo a b,
      MemLp (E r u) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) → ∀ r ∈ Ioo a b,
      MemLp (lopQ ν i E r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
    intro E hEm r hr
    unfold lopQ
    refine memLp_ite_zero _ ?_
    exact ((hEm [0, 0] r hr).add (hEm [1, 1] r hr)).const_mul (ν : ℂ)
  -- the derivatives of the parts
  have hXl := (hX (ν ^ (-2 : ℝ)) m (Ioo a b)).2
  have hX0 := (hX (ν ^ (-2 : ℝ)) m (Ioo a b)).1
  have hQ : HasXDerivOn (ν ^ (-2 : ℝ)) m (Ioo a b) (lopQ ν i D) (lopQ ν i D') := by
    by_cases hi : i = 0
    · have h1 := hXl (fun r => D r [0, 0]) (fun r => D' r [0, 0]) (fun r => D r [1, 1])
        (fun r => D' r [1, 1]) 1 1
        (fun r hr => ⟨hmD _ r hr, hmD' _ r hr, hmD _ r hr, hmD' _ r hr⟩) (hDD' [0, 0])
        (hDD' [1, 1])
      have h2 := hXl (fun r x => 1 * D r [0, 0] x + 1 * D r [1, 1] x)
        (fun r x => 1 * D' r [0, 0] x + 1 * D' r [1, 1] x) (fun _ _ => 0) (fun _ _ => 0)
        (ν : ℂ) 0
        (fun r hr => ⟨memLp_lin 1 1 (hmD _ r hr) (hmD _ r hr),
          memLp_lin 1 1 (hmD' _ r hr) (hmD' _ r hr), MemLp.zero', MemLp.zero'⟩) h1 hX0
      refine hasXDerivOn_congr h2 (fun r _ => ?_) (fun r _ => ?_)
      · funext x
        simp [lopQ, hi]
      · funext x
        simp [lopQ, hi]
    · refine hasXDerivOn_congr hX0 (fun r _ => ?_) (fun r _ => ?_)
      · funext x
        simp [lopQ, hi]
      · funext x
        simp [lopQ, hi]
  have htr : ∀ l : Fin 2, HasXDerivOn (ν ^ (-2 : ℝ)) m (Ioo a b) (lopT tr i l D)
      (fun r x => lopT tr (i + 1) l D r x + lopT tr i l D' r x) := fun l =>
    hCD _ m a b (fun r x => vJet tr i r x l) (fun r x => vJet tr (i + 1) r x l)
      (fun r => D r [l]) (fun r => D' r [l]) hc (hV ν hν hν1 tr hJets a b ha i l).1
      (hV ν hν hν1 tr hJets a b ha (i + 1) l).1 (hV ν hν hν1 tr hJets a b ha i l).2
      (hmD [l]) (hmD' [l]) (hDD' [l])
  have hker : HasXDerivOn (ν ^ (-2 : ℝ)) m (Ioo a b) (lopK tr i D)
      (fun r x => lopK tr (i + 1) D r x + lopK tr i D' r x) :=
    hKD _ a b (fun r l x => eJet tr i r l x) (fun r l x => eJet tr (i + 1) r l x)
      (fun r => D r []) (fun r => D' r []) hc1 (hE ν hν hν1 tr hJets a b ha i).1
      (hE ν hν hν1 tr hJets a b ha (i + 1)).1 (hE ν hν hν1 tr hJets a b ha i).2
      (hmD []) (hmD' []) (hDD' [])
  -- combine
  have mT' : ∀ l : Fin 2, ∀ r ∈ Ioo a b, MemLp (fun x => lopT tr (i + 1) l D r x +
      lopT tr i l D' r x) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    fun l r hr => (hTm (i + 1) D f hD l r hr).add (hTm i D' f' hD' l r hr)
  have hT := hXl (lopT tr i 0 D) (fun r x => lopT tr (i + 1) 0 D r x + lopT tr i 0 D' r x)
    (lopT tr i 1 D) (fun r x => lopT tr (i + 1) 1 D r x + lopT tr i 1 D' r x) 1 1
    (fun r hr => ⟨hTm i D f hD 0 r hr, mT' 0 r hr, hTm i D f hD 1 r hr, mT' 1 r hr⟩)
    (htr 0) (htr 1)
  have hQT := hXl (lopQ ν i D) (lopQ ν i D')
    (fun r x => 1 * lopT tr i 0 D r x + 1 * lopT tr i 1 D r x)
    (fun r x => 1 * (lopT tr (i + 1) 0 D r x + lopT tr i 0 D' r x) +
      1 * (lopT tr (i + 1) 1 D r x + lopT tr i 1 D' r x)) 1 1
    (fun r hr => ⟨hQm D hmD r hr, hQm D' hmD' r hr,
      memLp_lin 1 1 (hTm i D f hD 0 r hr) (hTm i D f hD 1 r hr),
      memLp_lin 1 1 (mT' 0 r hr) (mT' 1 r hr)⟩) hQ hT
  have hall := hXl
    (fun r x => 1 * lopQ ν i D r x + 1 * (1 * lopT tr i 0 D r x + 1 * lopT tr i 1 D r x))
    (fun r x => 1 * lopQ ν i D' r x + 1 * (1 * (lopT tr (i + 1) 0 D r x + lopT tr i 0 D' r x) +
      1 * (lopT tr (i + 1) 1 D r x + lopT tr i 1 D' r x)))
    (lopK tr i D) (fun r x => lopK tr (i + 1) D r x + lopK tr i D' r x) (-1) 1
    (fun r hr => ⟨memLp_lin 1 1 (hQm D hmD r hr)
        (memLp_lin 1 1 (hTm i D f hD 0 r hr) (hTm i D f hD 1 r hr)),
      memLp_lin 1 1 (hQm D' hmD' r hr) (memLp_lin 1 1 (mT' 0 r hr) (mT' 1 r hr)),
      hKm i D f hD r hr, (hKm (i + 1) D f hD r hr).add (hKm i D' f' hD' r hr)⟩) hQT hker
  refine hasXDerivOn_congr hall (fun r _ => ?_) (fun r _ => ?_)
  · funext x
    simp only [adjLop_eq_parts]
  · funext x
    simp only [adjLop_eq_parts, lopQ, Nat.add_one_ne_zero, ↓reduceIte]
    ring

/-! ## All the leaves at once -/

/-- **`AdjTimeJetsOf` from the leaves** (the target task `PartIII-a:T21/2/7/2/1/1/6` applies it to the
proved leaves; `AdjHkAllKerMul`, `KerMulDeriv` are proved for `m > 1`). -/
theorem adjTimeJetsOf_of_leaves (m : ℝ) (h1 : AdjHkAllOf) (h2 : XDerivOfTested)
    (h3 : TestedOfXDeriv) (h4 : AdjHkAllLinear) (h5 : HasXDerivOnLinear) (h6 : KerVelIsBS)
    (h7 : AdjLopTested m) (h10 : AdjHkAllCoeffMul) (h11 : CoeffMulDeriv)
    (h19 : AdjHkAllKerMul m) (h20 : KerMulDeriv m) (h22 : TrainVCoeff m) (h23 : TrainECoeff m) :
    AdjTimeJetsOf m :=
  have hS := adjLopSmooth_of m h4 h10 h19 h22 h23
  adjTimeJetsOf_of m h1 (xDerivUpgrade_of h2 h3) (adjTimeDerivBase_of m h2 h6 h7 hS) hS
    (adjLopDeriv_of m h5 h10 h19 h11 h20 h22 h23) h4 h5

end UnforcedLeray.Short.IIIa

#print axioms UnforcedLeray.Short.IIIa.adjTimeJetsOf_of
#print axioms UnforcedLeray.Short.IIIa.adjTimeDerivBase_of
#print axioms UnforcedLeray.Short.IIIa.xDerivUpgrade_of
#print axioms UnforcedLeray.Short.IIIa.adjLopSmooth_of
#print axioms UnforcedLeray.Short.IIIa.adjLopDeriv_of
#print axioms UnforcedLeray.Short.IIIa.adjTimeJetsOf_of_leaves
