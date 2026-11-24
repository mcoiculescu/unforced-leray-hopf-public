import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.KernelDeriv.Duality.KernelIntegrable.Tiling

/-!
# Part III-a, `PartIII-a:T21/3/2/1/2/1/1`: mass transport (lemma A, unfolding on the cylinder)

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
Strategy: `F1 = 1_{cell × ℝ²} K` and `F2 = 1_{ℝ² × cell} K` on `ℝ⁴` are unfolded along the
diagonal translations `W_k = (k c e₁, k c e₁)`; the cell translates tile `ℝ⁴`, so
`∫ F2 = ∑_k ∫ 1_D(q) K(q) 1_cell(q₂ - k c e₁) = ∫ F1`. Fubini identifies the two sides.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Function
open scoped ENNReal
open scoped Classical

namespace UnforcedLeray.Short.IIIa.Exist

instance mt_inv4 : Measure.IsAddRightInvariant (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- Sum over the cell translates of an indicator, plus convention. -/
lemma mt_tsum_plus {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [T2Space M]
    (c : ℝ) (hc : 0 < c) (a : ℝ × ℝ) (x : M) :
    ∑' k : ℤ, (if a + ((k : ℝ) * c, (0 : ℝ)) ∈ UnforcedLeray.B0579.cell c then x else 0) = x := by
  have hex : ∃ k0 : ℤ, a + ((k0 : ℝ) * c, (0 : ℝ)) ∈ UnforcedLeray.B0579.cell c := by
    have ha : a ∈ ⋃ k : ℤ, {b : ℝ × ℝ | b + ((k : ℝ) * c, (0 : ℝ)) ∈ UnforcedLeray.B0579.cell c} := by
      rw [KI.tile_iUnion c hc]; exact mem_univ a
    simpa using ha
  obtain ⟨k0, hk0⟩ := hex
  rw [tsum_eq_single k0]
  · simp [hk0]
  · intro k hk
    have hnot : a + ((k : ℝ) * c, (0 : ℝ)) ∉ UnforcedLeray.B0579.cell c := by
      intro hk'
      exact Set.disjoint_left.1 (KI.tile_disjoint c hc hk) hk' hk0
    simp [hnot]

/-- Sum over the cell translates of an indicator, minus convention. -/
lemma mt_tsum_minus {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [T2Space M]
    (c : ℝ) (hc : 0 < c) (a : ℝ × ℝ) (x : M) :
    ∑' k : ℤ, (if a - ((k : ℝ) * c, (0 : ℝ)) ∈ UnforcedLeray.B0579.cell c then x else 0) = x := by
  rw [← (Equiv.neg ℤ).tsum_eq]
  have e : ∀ k : ℤ, a - (((-k : ℤ) : ℝ) * c, (0 : ℝ)) = a + ((k : ℝ) * c, (0 : ℝ)) := by
    intro k
    ext <;> simp [sub_neg_eq_add]
  simp only [Equiv.neg_apply, e]
  exact mt_tsum_plus c hc a x

/-- The diagonal shift of the kernel: `K` is invariant under `(z, y) ↦ (z + kc e₁, y + kc e₁)`. -/
lemma mt_kper (c : ℝ) (K : ℝ × ℝ → ℝ × ℝ → ℝ)
    (hK : ∀ z y : ℝ × ℝ, K (z.1 + c, z.2) (y.1 + c, y.2) = K z y) (k : ℤ) (z y : ℝ × ℝ) :
    K (z + ((k : ℝ) * c, (0 : ℝ))) (y + ((k : ℝ) * c, (0 : ℝ))) = K z y := by
  let G2 : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p => K p.1 p.2
  have hP : Function.Periodic G2 ((c, (0 : ℝ)), (c, (0 : ℝ))) := by
    intro p
    show K (p.1 + (c, (0 : ℝ))) (p.2 + (c, (0 : ℝ))) = K p.1 p.2
    have e1 : p.1 + (c, (0 : ℝ)) = (p.1.1 + c, p.1.2) := by ext <;> simp
    have e2 : p.2 + (c, (0 : ℝ)) = (p.2.1 + c, p.2.2) := by ext <;> simp
    rw [e1, e2]
    exact hK p.1 p.2
  have h := hP.zsmul k (z, y)
  have e : (z, y) + k • ((c, (0 : ℝ)), (c, (0 : ℝ))) =
      (z + ((k : ℝ) * c, (0 : ℝ)), y + ((k : ℝ) * c, (0 : ℝ))) := by
    ext <;> simp [zsmul_eq_mul]
  rw [e] at h
  exact h

lemma mt_kper_minus (c : ℝ) (K : ℝ × ℝ → ℝ × ℝ → ℝ)
    (hK : ∀ z y : ℝ × ℝ, K (z.1 + c, z.2) (y.1 + c, y.2) = K z y) (k : ℤ) (z y : ℝ × ℝ) :
    K (z - ((k : ℝ) * c, (0 : ℝ))) (y - ((k : ℝ) * c, (0 : ℝ))) = K z y := by
  have h := mt_kper c K hK (-k) z y
  have e1 : z + (((-k : ℤ) : ℝ) * c, (0 : ℝ)) = z - ((k : ℝ) * c, (0 : ℝ)) := by
    ext <;> simp [sub_eq_add_neg]
  have e2 : y + (((-k : ℤ) : ℝ) * c, (0 : ℝ)) = y - ((k : ℝ) * c, (0 : ℝ)) := by
    ext <;> simp [sub_eq_add_neg]
  rw [e1, e2] at h
  exact h

/-- The domain `cell × ℝ²` in `ℝ⁴`. -/
def Dset (c : ℝ) : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {p | p.1 ∈ UnforcedLeray.B0579.cell c}

/-- The second-coordinate domain `ℝ² × cell`. -/
def E2set (c : ℝ) : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {p | p.2 ∈ UnforcedLeray.B0579.cell c}

/-- The `k`-th diagonal shift in `ℝ⁴`. -/
def Wsh (c : ℝ) (k : ℤ) : (ℝ × ℝ) × (ℝ × ℝ) := (((k : ℝ) * c, (0 : ℝ)), ((k : ℝ) * c, (0 : ℝ)))

/-- The tiles `E_k = {p | p + W_k ∈ cell × ℝ²}` in `ℝ⁴`. -/
def Eset (c : ℝ) (k : ℤ) : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  {p | p.1 + ((k : ℝ) * c, (0 : ℝ)) ∈ UnforcedLeray.B0579.cell c}

/-- The kernel as a function on `ℝ⁴`. -/
def Kp (K : ℝ × ℝ → ℝ × ℝ → ℝ) : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p => K p.1 p.2

lemma mt_D_meas (c : ℝ) : MeasurableSet (Dset c) :=
  (KI.cell_measurable c).preimage measurable_fst

lemma mt_E2_meas (c : ℝ) : MeasurableSet (E2set c) :=
  (KI.cell_measurable c).preimage measurable_snd

lemma mt_E_meas (c : ℝ) (k : ℤ) : MeasurableSet (Eset c k) :=
  (KI.cell_measurable c).preimage (measurable_fst.add_const _)

lemma mt_E_cover (c : ℝ) (hc : 0 < c) : (⋃ k : ℤ, Eset c k) = univ := by
  ext p
  simp only [mem_iUnion, mem_univ, iff_true]
  have hp : p.1 ∈ (⋃ k : ℤ, {b : ℝ × ℝ | b + ((k : ℝ) * c, (0 : ℝ)) ∈ UnforcedLeray.B0579.cell c}) := by
    rw [KI.tile_iUnion c hc]; exact mem_univ _
  obtain ⟨k, hk⟩ := mem_iUnion.1 hp
  exact ⟨k, hk⟩

lemma mt_E_disj (c : ℝ) (hc : 0 < c) : Pairwise (Disjoint on fun k : ℤ => Eset c k) := by
  intro j k hjk
  rw [Function.onFun, Set.disjoint_left]
  intro p hp hq
  exact Set.disjoint_left.1 (KI.tile_disjoint c hc hjk) hp hq

/-- Unfolding of an integrable function along the diagonal shifts. -/
lemma mt_unfold (c : ℝ) (hc : 0 < c) (f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ) (hf : Integrable f) :
    ∫ p, f p = ∑' k : ℤ, ∫ q, (Dset c).indicator (fun q => f (q - Wsh c k)) q := by
  calc ∫ p, f p = ∫ p in ⋃ k : ℤ, Eset c k, f p := by
        rw [mt_E_cover c hc, Measure.restrict_univ]
    _ = ∑' k : ℤ, ∫ p in Eset c k, f p :=
        integral_iUnion (fun k => mt_E_meas c k) (mt_E_disj c hc) hf.integrableOn
    _ = ∑' k : ℤ, ∫ q, (Dset c).indicator (fun q => f (q - Wsh c k)) q := by
        refine tsum_congr fun k => ?_
        have hfun : (Eset c k).indicator f =
            fun p => (Dset c).indicator (fun q => f (q - Wsh c k)) (p + Wsh c k) := by
          funext p
          by_cases h : p ∈ Eset c k
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show p + Wsh c k ∈ Dset c from h)]
            simp
          · rw [Set.indicator_of_notMem h,
              Set.indicator_of_notMem (show p + Wsh c k ∉ Dset c from h)]
        rw [← integral_indicator (mt_E_meas c k), hfun]
        exact integral_add_right_eq_self
          (fun q => (Dset c).indicator (fun q => f (q - Wsh c k)) q) (Wsh c k)

/-- Lebesgue (nonnegative) version of the unfolding. -/
lemma mt_lunfold (c : ℝ) (hc : 0 < c) (f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ≥0∞) :
    ∫⁻ p, f p = ∑' k : ℤ, ∫⁻ q, (Dset c).indicator (fun q => f (q - Wsh c k)) q := by
  calc ∫⁻ p, f p = ∫⁻ p in ⋃ k : ℤ, Eset c k, f p := by
        rw [mt_E_cover c hc, Measure.restrict_univ]
    _ = ∑' k : ℤ, ∫⁻ p in Eset c k, f p :=
        lintegral_iUnion (fun k => mt_E_meas c k) (mt_E_disj c hc) f
    _ = ∑' k : ℤ, ∫⁻ q, (Dset c).indicator (fun q => f (q - Wsh c k)) q := by
        refine tsum_congr fun k => ?_
        have hfun : (Eset c k).indicator f =
            fun p => (Dset c).indicator (fun q => f (q - Wsh c k)) (p + Wsh c k) := by
          funext p
          by_cases h : p ∈ Eset c k
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show p + Wsh c k ∈ Dset c from h)]
            simp
          · rw [Set.indicator_of_notMem h,
              Set.indicator_of_notMem (show p + Wsh c k ∉ Dset c from h)]
        rw [← lintegral_indicator (mt_E_meas c k), hfun]
        exact lintegral_add_right_eq_self
          (fun q => (Dset c).indicator (fun q => f (q - Wsh c k)) q) (Wsh c k)

theorem massTransport : UnforcedLeray.Short.IIIa.Exist.MassTransport := by
  intro c hc K hI hK
  have hKW : ∀ (k : ℤ) (p : (ℝ × ℝ) × (ℝ × ℝ)), Kp K (p - Wsh c k) = Kp K p :=
    fun k p => mt_kper_minus c K hK k p.1 p.2
  have hKW' : ∀ (k : ℤ) (p : (ℝ × ℝ) × (ℝ × ℝ)), Kp K (p + Wsh c k) = Kp K p :=
    fun k p => mt_kper c K hK k p.1 p.2
  have hmeasD : (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))).restrict (Dset c) =
      (volume.restrict (UnforcedLeray.B0579.cell c)).prod volume := by
    have hDset : Dset c = UnforcedLeray.B0579.cell c ×ˢ univ := by
      ext p; simp [Dset]
    have h1 : (volume.restrict (UnforcedLeray.B0579.cell c)).prod
        (volume.restrict (univ : Set (ℝ × ℝ))) =
        ((volume : Measure (ℝ × ℝ)).prod volume).restrict
          (UnforcedLeray.B0579.cell c ×ˢ univ) := Measure.prod_restrict _ _
    rw [Measure.restrict_univ] at h1
    rw [hDset]
    exact h1.symm
  have hF1 : Integrable ((Dset c).indicator (Kp K)) := by
    rw [integrable_indicator_iff (mt_D_meas c), IntegrableOn, hmeasD]
    exact hI
  -- the kernel is a.e. strongly measurable on ℝ⁴: on the tile `E_k` it is a translate of `F1`
  have hKae : AEStronglyMeasurable (Kp K) volume := by
    have hpiece : ∀ k : ℤ, AEStronglyMeasurable (Kp K) (volume.restrict (Eset c k)) := by
      intro k
      have hT : AEStronglyMeasurable (fun p => (Dset c).indicator (Kp K) (p + Wsh c k)) volume :=
        hF1.aestronglyMeasurable.comp_measurePreserving
          (measurePreserving_add_right volume (Wsh c k))
      refine hT.restrict.congr ?_
      refine ae_restrict_of_forall_mem (mt_E_meas c k) (fun p hp => ?_)
      have hpD : p + Wsh c k ∈ Dset c := hp
      simp only [Set.indicator_apply, if_pos hpD]
      exact hKW' k p
    have key : AEStronglyMeasurable (Kp K) (volume.restrict (⋃ k : ℤ, Eset c k)) :=
      aestronglyMeasurable_iUnion_iff.2 hpiece
    rwa [mt_E_cover c hc, Measure.restrict_univ] at key
  have hF2ae : AEStronglyMeasurable ((E2set c).indicator (Kp K)) volume :=
    hKae.indicator (mt_E2_meas c)
  -- the shifted second truncation
  have hterm : ∀ (q : (ℝ × ℝ) × (ℝ × ℝ)) (k : ℤ),
      (E2set c).indicator (Kp K) (q - Wsh c k) =
        if q.2 - ((k : ℝ) * c, (0 : ℝ)) ∈ UnforcedLeray.B0579.cell c then Kp K q else 0 := by
    intro q k
    by_cases h : q.2 - ((k : ℝ) * c, (0 : ℝ)) ∈ UnforcedLeray.B0579.cell c
    · have h' : (q - Wsh c k) ∈ E2set c := by
        show (q - Wsh c k).2 ∈ UnforcedLeray.B0579.cell c
        simpa [Wsh] using h
      rw [Set.indicator_of_mem h', if_pos h, hKW k q]
    · have h' : (q - Wsh c k) ∉ E2set c := by
        show ¬ (q - Wsh c k).2 ∈ UnforcedLeray.B0579.cell c
        simpa [Wsh] using h
      rw [Set.indicator_of_notMem h', if_neg h]
  have hnorm_ind : ∀ (g : (ℝ × ℝ) × (ℝ × ℝ) → ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ)),
      ‖(Dset c).indicator g q‖ₑ = (Dset c).indicator (fun q => ‖g q‖ₑ) q := by
    intro g q
    by_cases hq : q ∈ Dset c
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
    · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq, enorm_zero]
  have hsumF1 : ∀ q : (ℝ × ℝ) × (ℝ × ℝ),
      ∑' k : ℤ, (Dset c).indicator (fun q => (E2set c).indicator (Kp K) (q - Wsh c k)) q =
        (Dset c).indicator (Kp K) q := by
    intro q
    by_cases hq : q ∈ Dset c
    · simp only [Set.indicator_of_mem hq, hterm]
      exact mt_tsum_minus c hc q.2 (Kp K q)
    · simp only [Set.indicator_apply, hq, if_false, tsum_zero]
  have hgae : ∀ k : ℤ, AEStronglyMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      (Dset c).indicator (fun q => (E2set c).indicator (Kp K) (q - Wsh c k)) q) volume :=
    fun k => (hF2ae.comp_measurePreserving
      (measurePreserving_sub_right volume (Wsh c k))).indicator (mt_D_meas c)
  have hsumN : ∀ q : (ℝ × ℝ) × (ℝ × ℝ),
      ∑' k : ℤ, (Dset c).indicator (fun q => ‖(E2set c).indicator (Kp K) (q - Wsh c k)‖ₑ) q =
        ‖(Dset c).indicator (Kp K) q‖ₑ := by
    intro q
    by_cases hq : q ∈ Dset c
    · simp only [Set.indicator_of_mem hq, hterm]
      have hite : ∀ k : ℤ, ‖(if q.2 - ((k : ℝ) * c, (0 : ℝ)) ∈ UnforcedLeray.B0579.cell c
          then Kp K q else 0)‖ₑ =
          if q.2 - ((k : ℝ) * c, (0 : ℝ)) ∈ UnforcedLeray.B0579.cell c then ‖Kp K q‖ₑ else 0 := by
        intro k
        split_ifs <;> simp
      simp only [hite]
      exact mt_tsum_minus c hc q.2 ‖Kp K q‖ₑ
    · simp [Set.indicator_apply, hq]
  have haeG : ∀ k : ℤ, AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      (Dset c).indicator (fun q => ‖(E2set c).indicator (Kp K) (q - Wsh c k)‖ₑ) q) volume := by
    intro k
    have h1 : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        ‖(E2set c).indicator (Kp K) (q - Wsh c k)‖ₑ) volume :=
      (hF2ae.comp_measurePreserving (measurePreserving_sub_right volume (Wsh c k))).enorm
    exact h1.indicator (mt_D_meas c)
  have hF2 : Integrable ((E2set c).indicator (Kp K)) := by
    refine ⟨hF2ae, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ p, ‖(E2set c).indicator (Kp K) p‖ₑ
        = ∑' k : ℤ, ∫⁻ q, (Dset c).indicator
            (fun q => ‖(E2set c).indicator (Kp K) (q - Wsh c k)‖ₑ) q :=
          mt_lunfold c hc (fun p => ‖(E2set c).indicator (Kp K) p‖ₑ)
      _ = ∫⁻ q, ∑' k : ℤ, (Dset c).indicator
            (fun q => ‖(E2set c).indicator (Kp K) (q - Wsh c k)‖ₑ) q :=
          (lintegral_tsum haeG).symm
      _ = ∫⁻ q, ‖(Dset c).indicator (Kp K) q‖ₑ := lintegral_congr hsumN
      _ < ⊤ := hF1.2
  have hsummable : ∑' k : ℤ, ∫⁻ q, ‖(Dset c).indicator
      (fun q => (E2set c).indicator (Kp K) (q - Wsh c k)) q‖ₑ ≠ ⊤ := by
    have e1 : ∑' k : ℤ, ∫⁻ q, ‖(Dset c).indicator
        (fun q => (E2set c).indicator (Kp K) (q - Wsh c k)) q‖ₑ =
        ∫⁻ q, ∑' k : ℤ, (Dset c).indicator
          (fun q => ‖(E2set c).indicator (Kp K) (q - Wsh c k)‖ₑ) q := by
      rw [lintegral_tsum haeG]
      exact tsum_congr fun k => lintegral_congr fun q => hnorm_ind _ q
    rw [e1, lintegral_congr hsumN]
    exact hF1.2.ne
  have hkey : ∫ p, (E2set c).indicator (Kp K) p = ∫ p, (Dset c).indicator (Kp K) p := by
    calc ∫ p, (E2set c).indicator (Kp K) p
        = ∑' k : ℤ, ∫ q, (Dset c).indicator
            (fun q => (E2set c).indicator (Kp K) (q - Wsh c k)) q :=
          mt_unfold c hc _ hF2
      _ = ∫ q, ∑' k : ℤ, (Dset c).indicator
            (fun q => (E2set c).indicator (Kp K) (q - Wsh c k)) q :=
          (integral_tsum hgae hsummable).symm
      _ = ∫ p, (Dset c).indicator (Kp K) p := integral_congr_ae (ae_of_all _ hsumF1)
  have hF1' : Integrable ((Dset c).indicator (Kp K)) ((volume : Measure (ℝ × ℝ)).prod volume) := hF1
  have hF2' : Integrable ((E2set c).indicator (Kp K)) ((volume : Measure (ℝ × ℝ)).prod volume) := hF2
  have hLHS : ∫ z in UnforcedLeray.B0579.cell c, ∫ y, K z y =
      ∫ p, (Dset c).indicator (Kp K) p := by
    have hfub : ∫ p, (Dset c).indicator (Kp K) p =
        ∫ x, ∫ y, (Dset c).indicator (Kp K) (x, y) := integral_prod _ hF1'
    rw [hfub, ← integral_indicator (KI.cell_measurable c)]
    congr 1
    funext z
    by_cases hz : z ∈ UnforcedLeray.B0579.cell c
    · simp only [Set.indicator_of_mem hz]
      congr 1
      funext y
      simp [Set.indicator_apply, Dset, hz, Kp]
    · simp [Set.indicator_apply, Dset, hz]
  have hRHS : ∫ y in UnforcedLeray.B0579.cell c, ∫ z, K z y =
      ∫ p, (E2set c).indicator (Kp K) p := by
    have hfub : ∫ p, (E2set c).indicator (Kp K) p =
        ∫ y, ∫ x, (E2set c).indicator (Kp K) (x, y) := integral_prod_symm _ hF2'
    rw [hfub, ← integral_indicator (KI.cell_measurable c)]
    congr 1
    funext y
    by_cases hy : y ∈ UnforcedLeray.B0579.cell c
    · simp only [Set.indicator_of_mem hy]
      congr 1
      funext z
      simp [Set.indicator_apply, E2set, hy, Kp]
    · simp [Set.indicator_apply, E2set, hy]
  exact hLHS.trans (hkey.symm.trans hRHS.symm)

end UnforcedLeray.Short.IIIa.Exist
